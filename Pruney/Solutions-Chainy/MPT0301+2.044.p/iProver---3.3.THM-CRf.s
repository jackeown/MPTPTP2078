%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:37:02 EST 2020

% Result     : Theorem 7.25s
% Output     : CNFRefutation 7.25s
% Verified   : 
% Statistics : Number of formulae       :  117 (1592 expanded)
%              Number of clauses        :   64 ( 626 expanded)
%              Number of leaves         :   14 ( 322 expanded)
%              Depth                    :   27
%              Number of atoms          :  340 (4087 expanded)
%              Number of equality atoms :  176 (1606 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :   11 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f19])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f23,plain,(
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
    inference(rectify,[],[f22])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK1(X0,X1,X2),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X0)
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(sK1(X0,X1,X2),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK1(X0,X1,X2),X1)
            | ~ r2_hidden(sK1(X0,X1,X2),X0)
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
              & r2_hidden(sK1(X0,X1,X2),X0) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f23,f24])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X0)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | r2_hidden(sK1(X0,X1,X2),X0)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f39,f43])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK1(X0,X1,X2),X1)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | ~ r2_hidden(sK1(X0,X1,X2),X1)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f40,f43])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f5,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ~ ( ! [X5,X6] :
            ~ ( r2_hidden(X6,k3_xboole_0(X2,X4))
              & r2_hidden(X5,k3_xboole_0(X1,X3))
              & k4_tarski(X5,X6) = X0 )
        & r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ? [X5,X6] :
          ( r2_hidden(X6,k3_xboole_0(X2,X4))
          & r2_hidden(X5,k3_xboole_0(X1,X3))
          & k4_tarski(X5,X6) = X0 )
      | ~ r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f26,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5,X6] :
          ( r2_hidden(X6,k3_xboole_0(X2,X4))
          & r2_hidden(X5,k3_xboole_0(X1,X3))
          & k4_tarski(X5,X6) = X0 )
     => ( r2_hidden(sK3(X0,X1,X2,X3,X4),k3_xboole_0(X2,X4))
        & r2_hidden(sK2(X0,X1,X2,X3,X4),k3_xboole_0(X1,X3))
        & k4_tarski(sK2(X0,X1,X2,X3,X4),sK3(X0,X1,X2,X3,X4)) = X0 ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( r2_hidden(sK3(X0,X1,X2,X3,X4),k3_xboole_0(X2,X4))
        & r2_hidden(sK2(X0,X1,X2,X3,X4),k3_xboole_0(X1,X3))
        & k4_tarski(sK2(X0,X1,X2,X3,X4),sK3(X0,X1,X2,X3,X4)) = X0 )
      | ~ r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f17,f26])).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(sK2(X0,X1,X2,X3,X4),k3_xboole_0(X1,X3))
      | ~ r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f37,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f60,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f37,f43])).

fof(f63,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f60])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      <=> ( k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f18,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <~> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f30,plain,(
    ? [X0,X1] :
      ( ( ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f31,plain,(
    ? [X0,X1] :
      ( ( ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f30])).

fof(f32,plain,
    ( ? [X0,X1] :
        ( ( ( k1_xboole_0 != X1
            & k1_xboole_0 != X0 )
          | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
        & ( k1_xboole_0 = X1
          | k1_xboole_0 = X0
          | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) )
   => ( ( ( k1_xboole_0 != sK5
          & k1_xboole_0 != sK4 )
        | k1_xboole_0 != k2_zfmisc_1(sK4,sK5) )
      & ( k1_xboole_0 = sK5
        | k1_xboole_0 = sK4
        | k1_xboole_0 = k2_zfmisc_1(sK4,sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ( ( k1_xboole_0 != sK5
        & k1_xboole_0 != sK4 )
      | k1_xboole_0 != k2_zfmisc_1(sK4,sK5) )
    & ( k1_xboole_0 = sK5
      | k1_xboole_0 = sK4
      | k1_xboole_0 = k2_zfmisc_1(sK4,sK5) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f31,f32])).

fof(f53,plain,
    ( k1_xboole_0 = sK5
    | k1_xboole_0 = sK4
    | k1_xboole_0 = k2_zfmisc_1(sK4,sK5) ),
    inference(cnf_transformation,[],[f33])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f28])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f54,plain,
    ( k1_xboole_0 != sK4
    | k1_xboole_0 != k2_zfmisc_1(sK4,sK5) ),
    inference(cnf_transformation,[],[f33])).

fof(f55,plain,
    ( k1_xboole_0 != sK5
    | k1_xboole_0 != k2_zfmisc_1(sK4,sK5) ),
    inference(cnf_transformation,[],[f33])).

fof(f49,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(sK3(X0,X1,X2,X3,X4),k3_xboole_0(X2,X4))
      | ~ r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))) ) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_211,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_1,c_10])).

cnf(c_568,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r2_hidden(sK0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_211])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_222,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_0,c_10])).

cnf(c_567,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r2_hidden(sK0(X0,X1),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_222])).

cnf(c_3319,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_568,c_567])).

cnf(c_4,plain,
    ( r2_hidden(sK1(X0,X1,X2),X0)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_578,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
    | r2_hidden(sK1(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3,plain,
    ( ~ r2_hidden(sK1(X0,X1,X2),X1)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_579,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
    | r2_hidden(sK1(X0,X1,X2),X1) != iProver_top
    | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3275,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = X1
    | r2_hidden(sK1(X0,X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_578,c_579])).

cnf(c_11,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_4097,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X1,X1,X0),X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3275,c_11,c_3319])).

cnf(c_8,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_9,plain,
    ( r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_204,plain,
    ( k5_xboole_0(X0,X1) != X2
    | k3_xboole_0(X0,X1) != X3
    | k3_xboole_0(X3,X2) = k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_9])).

cnf(c_205,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_204])).

cnf(c_717,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X0),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_11,c_205])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)))
    | r2_hidden(sK2(X0,X1,X2,X3,X4),k3_xboole_0(X1,X3)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_573,plain,
    ( r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))) != iProver_top
    | r2_hidden(sK2(X0,X1,X2,X3,X4),k3_xboole_0(X1,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2513,plain,
    ( r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(k3_xboole_0(X1,X1),X2),k2_zfmisc_1(k1_xboole_0,X3))) != iProver_top
    | r2_hidden(sK2(X0,k3_xboole_0(X1,X1),X2,k1_xboole_0,X3),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_717,c_573])).

cnf(c_7616,plain,
    ( r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k1_xboole_0,X3))) != iProver_top
    | r2_hidden(sK2(X0,X1,X2,k1_xboole_0,X3),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2513,c_3319])).

cnf(c_7624,plain,
    ( k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(k1_xboole_0,X2)) = k1_xboole_0
    | r2_hidden(sK2(sK1(X3,X3,k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(k1_xboole_0,X2))),X0,X1,k1_xboole_0,X2),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4097,c_7616])).

cnf(c_721,plain,
    ( k3_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(X0,X0),k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_717,c_205])).

cnf(c_793,plain,
    ( k3_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(X0,X0),k1_xboole_0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_721,c_205])).

cnf(c_718,plain,
    ( k3_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_205,c_205])).

cnf(c_1116,plain,
    ( k3_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(X0,X0),k1_xboole_0))))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_793,c_718])).

cnf(c_800,plain,
    ( k3_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_718,c_718])).

cnf(c_1553,plain,
    ( k3_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(X0,X0),k1_xboole_0))))))))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1116,c_800])).

cnf(c_5425,plain,
    ( k3_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0))))))))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1553,c_1553,c_3319])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_576,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_5449,plain,
    ( r2_hidden(X0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k1_xboole_0))))))))) != iProver_top
    | r2_hidden(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5425,c_576])).

cnf(c_5452,plain,
    ( r2_hidden(X0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k1_xboole_0))))))))) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5449,c_11])).

cnf(c_5500,plain,
    ( r2_hidden(X0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_xboole_0)))))))) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_5452])).

cnf(c_5501,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5500,c_11])).

cnf(c_9740,plain,
    ( k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(k1_xboole_0,X2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7624,c_5501])).

cnf(c_12640,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3319,c_9740])).

cnf(c_20,negated_conjecture,
    ( k1_xboole_0 = k2_zfmisc_1(sK4,sK5)
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK5 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_571,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1565,plain,
    ( sK4 = k1_xboole_0
    | sK5 = k1_xboole_0
    | r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(X1,sK5) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_20,c_571])).

cnf(c_5660,plain,
    ( sK4 = k1_xboole_0
    | sK5 = k1_xboole_0
    | r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(X1,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1565,c_5501])).

cnf(c_5858,plain,
    ( sK4 = k1_xboole_0
    | sK5 = k1_xboole_0
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4097,c_5660])).

cnf(c_6299,plain,
    ( sK4 = k1_xboole_0
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4097,c_5858])).

cnf(c_19,negated_conjecture,
    ( k1_xboole_0 != k2_zfmisc_1(sK4,sK5)
    | k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_6303,plain,
    ( k2_zfmisc_1(k1_xboole_0,sK5) != k1_xboole_0
    | sK4 != k1_xboole_0
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6299,c_19])).

cnf(c_6397,plain,
    ( k2_zfmisc_1(k1_xboole_0,sK5) != k1_xboole_0
    | sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6303,c_6299])).

cnf(c_13212,plain,
    ( sK5 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_12640,c_6397])).

cnf(c_13213,plain,
    ( sK5 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_13212])).

cnf(c_18,negated_conjecture,
    ( k1_xboole_0 != k2_zfmisc_1(sK4,sK5)
    | k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_13538,plain,
    ( k2_zfmisc_1(sK4,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_13213,c_18])).

cnf(c_13539,plain,
    ( k2_zfmisc_1(sK4,k1_xboole_0) != k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_13538])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)))
    | r2_hidden(sK3(X0,X1,X2,X3,X4),k3_xboole_0(X2,X4)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_574,plain,
    ( r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))) != iProver_top
    | r2_hidden(sK3(X0,X1,X2,X3,X4),k3_xboole_0(X2,X4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2974,plain,
    ( r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,k3_xboole_0(X2,X2)),k2_zfmisc_1(X3,k1_xboole_0))) != iProver_top
    | r2_hidden(sK3(X0,X1,k3_xboole_0(X2,X2),X3,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_717,c_574])).

cnf(c_7832,plain,
    ( r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,k1_xboole_0))) != iProver_top
    | r2_hidden(sK3(X0,X1,X2,X3,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2974,c_3319])).

cnf(c_7840,plain,
    ( k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,k1_xboole_0)) = k1_xboole_0
    | r2_hidden(sK3(sK1(X3,X3,k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,k1_xboole_0))),X0,X1,X2,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4097,c_7832])).

cnf(c_10223,plain,
    ( k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7840,c_5501])).

cnf(c_12643,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3319,c_10223])).

cnf(c_13540,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_13539,c_12643])).

cnf(c_13541,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_13540])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:10:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.25/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.25/1.49  
% 7.25/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.25/1.49  
% 7.25/1.49  ------  iProver source info
% 7.25/1.49  
% 7.25/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.25/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.25/1.49  git: non_committed_changes: false
% 7.25/1.49  git: last_make_outside_of_git: false
% 7.25/1.49  
% 7.25/1.49  ------ 
% 7.25/1.49  
% 7.25/1.49  ------ Input Options
% 7.25/1.49  
% 7.25/1.49  --out_options                           all
% 7.25/1.49  --tptp_safe_out                         true
% 7.25/1.49  --problem_path                          ""
% 7.25/1.49  --include_path                          ""
% 7.25/1.49  --clausifier                            res/vclausify_rel
% 7.25/1.49  --clausifier_options                    ""
% 7.25/1.49  --stdin                                 false
% 7.25/1.49  --stats_out                             all
% 7.25/1.49  
% 7.25/1.49  ------ General Options
% 7.25/1.49  
% 7.25/1.49  --fof                                   false
% 7.25/1.49  --time_out_real                         305.
% 7.25/1.49  --time_out_virtual                      -1.
% 7.25/1.49  --symbol_type_check                     false
% 7.25/1.49  --clausify_out                          false
% 7.25/1.49  --sig_cnt_out                           false
% 7.25/1.49  --trig_cnt_out                          false
% 7.25/1.49  --trig_cnt_out_tolerance                1.
% 7.25/1.49  --trig_cnt_out_sk_spl                   false
% 7.25/1.49  --abstr_cl_out                          false
% 7.25/1.49  
% 7.25/1.49  ------ Global Options
% 7.25/1.49  
% 7.25/1.49  --schedule                              default
% 7.25/1.49  --add_important_lit                     false
% 7.25/1.49  --prop_solver_per_cl                    1000
% 7.25/1.49  --min_unsat_core                        false
% 7.25/1.49  --soft_assumptions                      false
% 7.25/1.49  --soft_lemma_size                       3
% 7.25/1.49  --prop_impl_unit_size                   0
% 7.25/1.49  --prop_impl_unit                        []
% 7.25/1.49  --share_sel_clauses                     true
% 7.25/1.49  --reset_solvers                         false
% 7.25/1.49  --bc_imp_inh                            [conj_cone]
% 7.25/1.49  --conj_cone_tolerance                   3.
% 7.25/1.49  --extra_neg_conj                        none
% 7.25/1.49  --large_theory_mode                     true
% 7.25/1.49  --prolific_symb_bound                   200
% 7.25/1.49  --lt_threshold                          2000
% 7.25/1.49  --clause_weak_htbl                      true
% 7.25/1.49  --gc_record_bc_elim                     false
% 7.25/1.49  
% 7.25/1.49  ------ Preprocessing Options
% 7.25/1.49  
% 7.25/1.49  --preprocessing_flag                    true
% 7.25/1.49  --time_out_prep_mult                    0.1
% 7.25/1.49  --splitting_mode                        input
% 7.25/1.49  --splitting_grd                         true
% 7.25/1.49  --splitting_cvd                         false
% 7.25/1.49  --splitting_cvd_svl                     false
% 7.25/1.49  --splitting_nvd                         32
% 7.25/1.49  --sub_typing                            true
% 7.25/1.49  --prep_gs_sim                           true
% 7.25/1.49  --prep_unflatten                        true
% 7.25/1.49  --prep_res_sim                          true
% 7.25/1.49  --prep_upred                            true
% 7.25/1.49  --prep_sem_filter                       exhaustive
% 7.25/1.49  --prep_sem_filter_out                   false
% 7.25/1.49  --pred_elim                             true
% 7.25/1.49  --res_sim_input                         true
% 7.25/1.49  --eq_ax_congr_red                       true
% 7.25/1.49  --pure_diseq_elim                       true
% 7.25/1.49  --brand_transform                       false
% 7.25/1.49  --non_eq_to_eq                          false
% 7.25/1.49  --prep_def_merge                        true
% 7.25/1.49  --prep_def_merge_prop_impl              false
% 7.25/1.49  --prep_def_merge_mbd                    true
% 7.25/1.49  --prep_def_merge_tr_red                 false
% 7.25/1.49  --prep_def_merge_tr_cl                  false
% 7.25/1.49  --smt_preprocessing                     true
% 7.25/1.49  --smt_ac_axioms                         fast
% 7.25/1.49  --preprocessed_out                      false
% 7.25/1.49  --preprocessed_stats                    false
% 7.25/1.49  
% 7.25/1.49  ------ Abstraction refinement Options
% 7.25/1.49  
% 7.25/1.49  --abstr_ref                             []
% 7.25/1.49  --abstr_ref_prep                        false
% 7.25/1.49  --abstr_ref_until_sat                   false
% 7.25/1.49  --abstr_ref_sig_restrict                funpre
% 7.25/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.25/1.49  --abstr_ref_under                       []
% 7.25/1.49  
% 7.25/1.49  ------ SAT Options
% 7.25/1.49  
% 7.25/1.49  --sat_mode                              false
% 7.25/1.49  --sat_fm_restart_options                ""
% 7.25/1.49  --sat_gr_def                            false
% 7.25/1.49  --sat_epr_types                         true
% 7.25/1.49  --sat_non_cyclic_types                  false
% 7.25/1.49  --sat_finite_models                     false
% 7.25/1.49  --sat_fm_lemmas                         false
% 7.25/1.49  --sat_fm_prep                           false
% 7.25/1.49  --sat_fm_uc_incr                        true
% 7.25/1.49  --sat_out_model                         small
% 7.25/1.49  --sat_out_clauses                       false
% 7.25/1.49  
% 7.25/1.49  ------ QBF Options
% 7.25/1.49  
% 7.25/1.49  --qbf_mode                              false
% 7.25/1.49  --qbf_elim_univ                         false
% 7.25/1.49  --qbf_dom_inst                          none
% 7.25/1.49  --qbf_dom_pre_inst                      false
% 7.25/1.49  --qbf_sk_in                             false
% 7.25/1.49  --qbf_pred_elim                         true
% 7.25/1.49  --qbf_split                             512
% 7.25/1.49  
% 7.25/1.49  ------ BMC1 Options
% 7.25/1.49  
% 7.25/1.49  --bmc1_incremental                      false
% 7.25/1.49  --bmc1_axioms                           reachable_all
% 7.25/1.49  --bmc1_min_bound                        0
% 7.25/1.49  --bmc1_max_bound                        -1
% 7.25/1.49  --bmc1_max_bound_default                -1
% 7.25/1.49  --bmc1_symbol_reachability              true
% 7.25/1.49  --bmc1_property_lemmas                  false
% 7.25/1.49  --bmc1_k_induction                      false
% 7.25/1.49  --bmc1_non_equiv_states                 false
% 7.25/1.49  --bmc1_deadlock                         false
% 7.25/1.49  --bmc1_ucm                              false
% 7.25/1.49  --bmc1_add_unsat_core                   none
% 7.25/1.49  --bmc1_unsat_core_children              false
% 7.25/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.25/1.49  --bmc1_out_stat                         full
% 7.25/1.49  --bmc1_ground_init                      false
% 7.25/1.49  --bmc1_pre_inst_next_state              false
% 7.25/1.49  --bmc1_pre_inst_state                   false
% 7.25/1.49  --bmc1_pre_inst_reach_state             false
% 7.25/1.49  --bmc1_out_unsat_core                   false
% 7.25/1.49  --bmc1_aig_witness_out                  false
% 7.25/1.49  --bmc1_verbose                          false
% 7.25/1.49  --bmc1_dump_clauses_tptp                false
% 7.25/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.25/1.49  --bmc1_dump_file                        -
% 7.25/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.25/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.25/1.49  --bmc1_ucm_extend_mode                  1
% 7.25/1.49  --bmc1_ucm_init_mode                    2
% 7.25/1.49  --bmc1_ucm_cone_mode                    none
% 7.25/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.25/1.49  --bmc1_ucm_relax_model                  4
% 7.25/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.25/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.25/1.49  --bmc1_ucm_layered_model                none
% 7.25/1.49  --bmc1_ucm_max_lemma_size               10
% 7.25/1.49  
% 7.25/1.49  ------ AIG Options
% 7.25/1.49  
% 7.25/1.49  --aig_mode                              false
% 7.25/1.49  
% 7.25/1.49  ------ Instantiation Options
% 7.25/1.49  
% 7.25/1.49  --instantiation_flag                    true
% 7.25/1.49  --inst_sos_flag                         true
% 7.25/1.49  --inst_sos_phase                        true
% 7.25/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.25/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.25/1.49  --inst_lit_sel_side                     num_symb
% 7.25/1.49  --inst_solver_per_active                1400
% 7.25/1.49  --inst_solver_calls_frac                1.
% 7.25/1.49  --inst_passive_queue_type               priority_queues
% 7.25/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.25/1.49  --inst_passive_queues_freq              [25;2]
% 7.25/1.49  --inst_dismatching                      true
% 7.25/1.49  --inst_eager_unprocessed_to_passive     true
% 7.25/1.49  --inst_prop_sim_given                   true
% 7.25/1.49  --inst_prop_sim_new                     false
% 7.25/1.49  --inst_subs_new                         false
% 7.25/1.49  --inst_eq_res_simp                      false
% 7.25/1.49  --inst_subs_given                       false
% 7.25/1.49  --inst_orphan_elimination               true
% 7.25/1.49  --inst_learning_loop_flag               true
% 7.25/1.49  --inst_learning_start                   3000
% 7.25/1.49  --inst_learning_factor                  2
% 7.25/1.49  --inst_start_prop_sim_after_learn       3
% 7.25/1.49  --inst_sel_renew                        solver
% 7.25/1.49  --inst_lit_activity_flag                true
% 7.25/1.49  --inst_restr_to_given                   false
% 7.25/1.49  --inst_activity_threshold               500
% 7.25/1.49  --inst_out_proof                        true
% 7.25/1.49  
% 7.25/1.49  ------ Resolution Options
% 7.25/1.49  
% 7.25/1.49  --resolution_flag                       true
% 7.25/1.49  --res_lit_sel                           adaptive
% 7.25/1.49  --res_lit_sel_side                      none
% 7.25/1.49  --res_ordering                          kbo
% 7.25/1.49  --res_to_prop_solver                    active
% 7.25/1.49  --res_prop_simpl_new                    false
% 7.25/1.49  --res_prop_simpl_given                  true
% 7.25/1.49  --res_passive_queue_type                priority_queues
% 7.25/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.25/1.49  --res_passive_queues_freq               [15;5]
% 7.25/1.49  --res_forward_subs                      full
% 7.25/1.49  --res_backward_subs                     full
% 7.25/1.49  --res_forward_subs_resolution           true
% 7.25/1.49  --res_backward_subs_resolution          true
% 7.25/1.49  --res_orphan_elimination                true
% 7.25/1.49  --res_time_limit                        2.
% 7.25/1.49  --res_out_proof                         true
% 7.25/1.49  
% 7.25/1.49  ------ Superposition Options
% 7.25/1.49  
% 7.25/1.49  --superposition_flag                    true
% 7.25/1.49  --sup_passive_queue_type                priority_queues
% 7.25/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.25/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.25/1.49  --demod_completeness_check              fast
% 7.25/1.49  --demod_use_ground                      true
% 7.25/1.49  --sup_to_prop_solver                    passive
% 7.25/1.49  --sup_prop_simpl_new                    true
% 7.25/1.49  --sup_prop_simpl_given                  true
% 7.25/1.49  --sup_fun_splitting                     true
% 7.25/1.49  --sup_smt_interval                      50000
% 7.25/1.49  
% 7.25/1.49  ------ Superposition Simplification Setup
% 7.25/1.49  
% 7.25/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.25/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.25/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.25/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.25/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.25/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.25/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.25/1.49  --sup_immed_triv                        [TrivRules]
% 7.25/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.25/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.25/1.49  --sup_immed_bw_main                     []
% 7.25/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.25/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.25/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.25/1.49  --sup_input_bw                          []
% 7.25/1.49  
% 7.25/1.49  ------ Combination Options
% 7.25/1.49  
% 7.25/1.49  --comb_res_mult                         3
% 7.25/1.49  --comb_sup_mult                         2
% 7.25/1.49  --comb_inst_mult                        10
% 7.25/1.49  
% 7.25/1.49  ------ Debug Options
% 7.25/1.49  
% 7.25/1.49  --dbg_backtrace                         false
% 7.25/1.49  --dbg_dump_prop_clauses                 false
% 7.25/1.49  --dbg_dump_prop_clauses_file            -
% 7.25/1.49  --dbg_out_stat                          false
% 7.25/1.49  ------ Parsing...
% 7.25/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.25/1.49  
% 7.25/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.25/1.49  
% 7.25/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.25/1.49  
% 7.25/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.25/1.49  ------ Proving...
% 7.25/1.49  ------ Problem Properties 
% 7.25/1.49  
% 7.25/1.49  
% 7.25/1.49  clauses                                 19
% 7.25/1.49  conjectures                             3
% 7.25/1.49  EPR                                     0
% 7.25/1.49  Horn                                    13
% 7.25/1.49  unary                                   2
% 7.25/1.49  binary                                  11
% 7.25/1.49  lits                                    43
% 7.25/1.49  lits eq                                 15
% 7.25/1.49  fd_pure                                 0
% 7.25/1.49  fd_pseudo                               0
% 7.25/1.49  fd_cond                                 0
% 7.25/1.49  fd_pseudo_cond                          3
% 7.25/1.49  AC symbols                              0
% 7.25/1.49  
% 7.25/1.49  ------ Schedule dynamic 5 is on 
% 7.25/1.49  
% 7.25/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.25/1.49  
% 7.25/1.49  
% 7.25/1.49  ------ 
% 7.25/1.49  Current options:
% 7.25/1.49  ------ 
% 7.25/1.49  
% 7.25/1.49  ------ Input Options
% 7.25/1.49  
% 7.25/1.49  --out_options                           all
% 7.25/1.49  --tptp_safe_out                         true
% 7.25/1.49  --problem_path                          ""
% 7.25/1.49  --include_path                          ""
% 7.25/1.49  --clausifier                            res/vclausify_rel
% 7.25/1.49  --clausifier_options                    ""
% 7.25/1.49  --stdin                                 false
% 7.25/1.49  --stats_out                             all
% 7.25/1.49  
% 7.25/1.49  ------ General Options
% 7.25/1.49  
% 7.25/1.49  --fof                                   false
% 7.25/1.49  --time_out_real                         305.
% 7.25/1.49  --time_out_virtual                      -1.
% 7.25/1.49  --symbol_type_check                     false
% 7.25/1.49  --clausify_out                          false
% 7.25/1.49  --sig_cnt_out                           false
% 7.25/1.49  --trig_cnt_out                          false
% 7.25/1.49  --trig_cnt_out_tolerance                1.
% 7.25/1.49  --trig_cnt_out_sk_spl                   false
% 7.25/1.49  --abstr_cl_out                          false
% 7.25/1.49  
% 7.25/1.49  ------ Global Options
% 7.25/1.49  
% 7.25/1.49  --schedule                              default
% 7.25/1.49  --add_important_lit                     false
% 7.25/1.49  --prop_solver_per_cl                    1000
% 7.25/1.49  --min_unsat_core                        false
% 7.25/1.49  --soft_assumptions                      false
% 7.25/1.49  --soft_lemma_size                       3
% 7.25/1.49  --prop_impl_unit_size                   0
% 7.25/1.49  --prop_impl_unit                        []
% 7.25/1.49  --share_sel_clauses                     true
% 7.25/1.49  --reset_solvers                         false
% 7.25/1.49  --bc_imp_inh                            [conj_cone]
% 7.25/1.49  --conj_cone_tolerance                   3.
% 7.25/1.49  --extra_neg_conj                        none
% 7.25/1.49  --large_theory_mode                     true
% 7.25/1.49  --prolific_symb_bound                   200
% 7.25/1.49  --lt_threshold                          2000
% 7.25/1.49  --clause_weak_htbl                      true
% 7.25/1.49  --gc_record_bc_elim                     false
% 7.25/1.49  
% 7.25/1.49  ------ Preprocessing Options
% 7.25/1.49  
% 7.25/1.49  --preprocessing_flag                    true
% 7.25/1.49  --time_out_prep_mult                    0.1
% 7.25/1.49  --splitting_mode                        input
% 7.25/1.49  --splitting_grd                         true
% 7.25/1.49  --splitting_cvd                         false
% 7.25/1.49  --splitting_cvd_svl                     false
% 7.25/1.49  --splitting_nvd                         32
% 7.25/1.49  --sub_typing                            true
% 7.25/1.49  --prep_gs_sim                           true
% 7.25/1.49  --prep_unflatten                        true
% 7.25/1.49  --prep_res_sim                          true
% 7.25/1.49  --prep_upred                            true
% 7.25/1.49  --prep_sem_filter                       exhaustive
% 7.25/1.49  --prep_sem_filter_out                   false
% 7.25/1.49  --pred_elim                             true
% 7.25/1.49  --res_sim_input                         true
% 7.25/1.49  --eq_ax_congr_red                       true
% 7.25/1.49  --pure_diseq_elim                       true
% 7.25/1.49  --brand_transform                       false
% 7.25/1.49  --non_eq_to_eq                          false
% 7.25/1.49  --prep_def_merge                        true
% 7.25/1.49  --prep_def_merge_prop_impl              false
% 7.25/1.49  --prep_def_merge_mbd                    true
% 7.25/1.49  --prep_def_merge_tr_red                 false
% 7.25/1.49  --prep_def_merge_tr_cl                  false
% 7.25/1.49  --smt_preprocessing                     true
% 7.25/1.49  --smt_ac_axioms                         fast
% 7.25/1.49  --preprocessed_out                      false
% 7.25/1.49  --preprocessed_stats                    false
% 7.25/1.49  
% 7.25/1.49  ------ Abstraction refinement Options
% 7.25/1.49  
% 7.25/1.49  --abstr_ref                             []
% 7.25/1.49  --abstr_ref_prep                        false
% 7.25/1.49  --abstr_ref_until_sat                   false
% 7.25/1.49  --abstr_ref_sig_restrict                funpre
% 7.25/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.25/1.49  --abstr_ref_under                       []
% 7.25/1.49  
% 7.25/1.49  ------ SAT Options
% 7.25/1.49  
% 7.25/1.49  --sat_mode                              false
% 7.25/1.49  --sat_fm_restart_options                ""
% 7.25/1.49  --sat_gr_def                            false
% 7.25/1.49  --sat_epr_types                         true
% 7.25/1.49  --sat_non_cyclic_types                  false
% 7.25/1.49  --sat_finite_models                     false
% 7.25/1.49  --sat_fm_lemmas                         false
% 7.25/1.49  --sat_fm_prep                           false
% 7.25/1.49  --sat_fm_uc_incr                        true
% 7.25/1.49  --sat_out_model                         small
% 7.25/1.49  --sat_out_clauses                       false
% 7.25/1.49  
% 7.25/1.49  ------ QBF Options
% 7.25/1.49  
% 7.25/1.49  --qbf_mode                              false
% 7.25/1.49  --qbf_elim_univ                         false
% 7.25/1.49  --qbf_dom_inst                          none
% 7.25/1.49  --qbf_dom_pre_inst                      false
% 7.25/1.49  --qbf_sk_in                             false
% 7.25/1.49  --qbf_pred_elim                         true
% 7.25/1.49  --qbf_split                             512
% 7.25/1.49  
% 7.25/1.49  ------ BMC1 Options
% 7.25/1.49  
% 7.25/1.49  --bmc1_incremental                      false
% 7.25/1.49  --bmc1_axioms                           reachable_all
% 7.25/1.49  --bmc1_min_bound                        0
% 7.25/1.49  --bmc1_max_bound                        -1
% 7.25/1.49  --bmc1_max_bound_default                -1
% 7.25/1.49  --bmc1_symbol_reachability              true
% 7.25/1.49  --bmc1_property_lemmas                  false
% 7.25/1.49  --bmc1_k_induction                      false
% 7.25/1.49  --bmc1_non_equiv_states                 false
% 7.25/1.49  --bmc1_deadlock                         false
% 7.25/1.49  --bmc1_ucm                              false
% 7.25/1.49  --bmc1_add_unsat_core                   none
% 7.25/1.49  --bmc1_unsat_core_children              false
% 7.25/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.25/1.49  --bmc1_out_stat                         full
% 7.25/1.49  --bmc1_ground_init                      false
% 7.25/1.49  --bmc1_pre_inst_next_state              false
% 7.25/1.49  --bmc1_pre_inst_state                   false
% 7.25/1.49  --bmc1_pre_inst_reach_state             false
% 7.25/1.49  --bmc1_out_unsat_core                   false
% 7.25/1.49  --bmc1_aig_witness_out                  false
% 7.25/1.49  --bmc1_verbose                          false
% 7.25/1.49  --bmc1_dump_clauses_tptp                false
% 7.25/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.25/1.49  --bmc1_dump_file                        -
% 7.25/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.25/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.25/1.49  --bmc1_ucm_extend_mode                  1
% 7.25/1.49  --bmc1_ucm_init_mode                    2
% 7.25/1.49  --bmc1_ucm_cone_mode                    none
% 7.25/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.25/1.49  --bmc1_ucm_relax_model                  4
% 7.25/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.25/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.25/1.49  --bmc1_ucm_layered_model                none
% 7.25/1.49  --bmc1_ucm_max_lemma_size               10
% 7.25/1.49  
% 7.25/1.49  ------ AIG Options
% 7.25/1.49  
% 7.25/1.49  --aig_mode                              false
% 7.25/1.49  
% 7.25/1.49  ------ Instantiation Options
% 7.25/1.49  
% 7.25/1.49  --instantiation_flag                    true
% 7.25/1.49  --inst_sos_flag                         true
% 7.25/1.49  --inst_sos_phase                        true
% 7.25/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.25/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.25/1.49  --inst_lit_sel_side                     none
% 7.25/1.49  --inst_solver_per_active                1400
% 7.25/1.49  --inst_solver_calls_frac                1.
% 7.25/1.49  --inst_passive_queue_type               priority_queues
% 7.25/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.25/1.49  --inst_passive_queues_freq              [25;2]
% 7.25/1.49  --inst_dismatching                      true
% 7.25/1.49  --inst_eager_unprocessed_to_passive     true
% 7.25/1.49  --inst_prop_sim_given                   true
% 7.25/1.49  --inst_prop_sim_new                     false
% 7.25/1.49  --inst_subs_new                         false
% 7.25/1.49  --inst_eq_res_simp                      false
% 7.25/1.49  --inst_subs_given                       false
% 7.25/1.49  --inst_orphan_elimination               true
% 7.25/1.49  --inst_learning_loop_flag               true
% 7.25/1.49  --inst_learning_start                   3000
% 7.25/1.49  --inst_learning_factor                  2
% 7.25/1.49  --inst_start_prop_sim_after_learn       3
% 7.25/1.49  --inst_sel_renew                        solver
% 7.25/1.49  --inst_lit_activity_flag                true
% 7.25/1.49  --inst_restr_to_given                   false
% 7.25/1.49  --inst_activity_threshold               500
% 7.25/1.49  --inst_out_proof                        true
% 7.25/1.49  
% 7.25/1.49  ------ Resolution Options
% 7.25/1.49  
% 7.25/1.49  --resolution_flag                       false
% 7.25/1.49  --res_lit_sel                           adaptive
% 7.25/1.49  --res_lit_sel_side                      none
% 7.25/1.49  --res_ordering                          kbo
% 7.25/1.49  --res_to_prop_solver                    active
% 7.25/1.49  --res_prop_simpl_new                    false
% 7.25/1.49  --res_prop_simpl_given                  true
% 7.25/1.49  --res_passive_queue_type                priority_queues
% 7.25/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.25/1.49  --res_passive_queues_freq               [15;5]
% 7.25/1.49  --res_forward_subs                      full
% 7.25/1.49  --res_backward_subs                     full
% 7.25/1.49  --res_forward_subs_resolution           true
% 7.25/1.49  --res_backward_subs_resolution          true
% 7.25/1.49  --res_orphan_elimination                true
% 7.25/1.49  --res_time_limit                        2.
% 7.25/1.49  --res_out_proof                         true
% 7.25/1.49  
% 7.25/1.49  ------ Superposition Options
% 7.25/1.49  
% 7.25/1.49  --superposition_flag                    true
% 7.25/1.49  --sup_passive_queue_type                priority_queues
% 7.25/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.25/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.25/1.49  --demod_completeness_check              fast
% 7.25/1.49  --demod_use_ground                      true
% 7.25/1.49  --sup_to_prop_solver                    passive
% 7.25/1.49  --sup_prop_simpl_new                    true
% 7.25/1.49  --sup_prop_simpl_given                  true
% 7.25/1.49  --sup_fun_splitting                     true
% 7.25/1.49  --sup_smt_interval                      50000
% 7.25/1.49  
% 7.25/1.49  ------ Superposition Simplification Setup
% 7.25/1.49  
% 7.25/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.25/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.25/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.25/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.25/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.25/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.25/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.25/1.49  --sup_immed_triv                        [TrivRules]
% 7.25/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.25/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.25/1.49  --sup_immed_bw_main                     []
% 7.25/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.25/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.25/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.25/1.49  --sup_input_bw                          []
% 7.25/1.49  
% 7.25/1.49  ------ Combination Options
% 7.25/1.49  
% 7.25/1.49  --comb_res_mult                         3
% 7.25/1.49  --comb_sup_mult                         2
% 7.25/1.49  --comb_inst_mult                        10
% 7.25/1.49  
% 7.25/1.49  ------ Debug Options
% 7.25/1.49  
% 7.25/1.49  --dbg_backtrace                         false
% 7.25/1.49  --dbg_dump_prop_clauses                 false
% 7.25/1.49  --dbg_dump_prop_clauses_file            -
% 7.25/1.49  --dbg_out_stat                          false
% 7.25/1.49  
% 7.25/1.49  
% 7.25/1.49  
% 7.25/1.49  
% 7.25/1.49  ------ Proving...
% 7.25/1.49  
% 7.25/1.49  
% 7.25/1.49  % SZS status Theorem for theBenchmark.p
% 7.25/1.49  
% 7.25/1.49   Resolution empty clause
% 7.25/1.49  
% 7.25/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.25/1.49  
% 7.25/1.49  fof(f1,axiom,(
% 7.25/1.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.25/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.25/1.49  
% 7.25/1.49  fof(f13,plain,(
% 7.25/1.49    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 7.25/1.49    inference(unused_predicate_definition_removal,[],[f1])).
% 7.25/1.49  
% 7.25/1.49  fof(f14,plain,(
% 7.25/1.49    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 7.25/1.49    inference(ennf_transformation,[],[f13])).
% 7.25/1.49  
% 7.25/1.49  fof(f19,plain,(
% 7.25/1.49    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.25/1.49    introduced(choice_axiom,[])).
% 7.25/1.49  
% 7.25/1.49  fof(f20,plain,(
% 7.25/1.49    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.25/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f19])).
% 7.25/1.49  
% 7.25/1.49  fof(f34,plain,(
% 7.25/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 7.25/1.49    inference(cnf_transformation,[],[f20])).
% 7.25/1.49  
% 7.25/1.49  fof(f6,axiom,(
% 7.25/1.49    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 7.25/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.25/1.49  
% 7.25/1.49  fof(f16,plain,(
% 7.25/1.49    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 7.25/1.49    inference(ennf_transformation,[],[f6])).
% 7.25/1.49  
% 7.25/1.49  fof(f45,plain,(
% 7.25/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 7.25/1.49    inference(cnf_transformation,[],[f16])).
% 7.25/1.49  
% 7.25/1.49  fof(f35,plain,(
% 7.25/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 7.25/1.49    inference(cnf_transformation,[],[f20])).
% 7.25/1.49  
% 7.25/1.49  fof(f2,axiom,(
% 7.25/1.49    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 7.25/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.25/1.49  
% 7.25/1.49  fof(f21,plain,(
% 7.25/1.49    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.25/1.49    inference(nnf_transformation,[],[f2])).
% 7.25/1.49  
% 7.25/1.49  fof(f22,plain,(
% 7.25/1.49    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.25/1.49    inference(flattening,[],[f21])).
% 7.25/1.49  
% 7.25/1.49  fof(f23,plain,(
% 7.25/1.49    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.25/1.49    inference(rectify,[],[f22])).
% 7.25/1.49  
% 7.25/1.49  fof(f24,plain,(
% 7.25/1.49    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 7.25/1.49    introduced(choice_axiom,[])).
% 7.25/1.49  
% 7.25/1.49  fof(f25,plain,(
% 7.25/1.49    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.25/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f23,f24])).
% 7.25/1.49  
% 7.25/1.49  fof(f39,plain,(
% 7.25/1.49    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 7.25/1.49    inference(cnf_transformation,[],[f25])).
% 7.25/1.49  
% 7.25/1.49  fof(f4,axiom,(
% 7.25/1.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.25/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.25/1.49  
% 7.25/1.49  fof(f43,plain,(
% 7.25/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.25/1.49    inference(cnf_transformation,[],[f4])).
% 7.25/1.49  
% 7.25/1.49  fof(f58,plain,(
% 7.25/1.49    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 7.25/1.49    inference(definition_unfolding,[],[f39,f43])).
% 7.25/1.49  
% 7.25/1.49  fof(f40,plain,(
% 7.25/1.49    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 7.25/1.49    inference(cnf_transformation,[],[f25])).
% 7.25/1.49  
% 7.25/1.49  fof(f57,plain,(
% 7.25/1.49    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | ~r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 7.25/1.49    inference(definition_unfolding,[],[f40,f43])).
% 7.25/1.49  
% 7.25/1.49  fof(f7,axiom,(
% 7.25/1.49    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 7.25/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.25/1.49  
% 7.25/1.49  fof(f46,plain,(
% 7.25/1.49    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 7.25/1.49    inference(cnf_transformation,[],[f7])).
% 7.25/1.49  
% 7.25/1.49  fof(f3,axiom,(
% 7.25/1.49    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 7.25/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.25/1.49  
% 7.25/1.49  fof(f12,plain,(
% 7.25/1.49    ! [X0,X1] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,X1) = k1_xboole_0)),
% 7.25/1.49    inference(unused_predicate_definition_removal,[],[f3])).
% 7.25/1.49  
% 7.25/1.49  fof(f15,plain,(
% 7.25/1.49    ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 7.25/1.49    inference(ennf_transformation,[],[f12])).
% 7.25/1.49  
% 7.25/1.49  fof(f42,plain,(
% 7.25/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 7.25/1.49    inference(cnf_transformation,[],[f15])).
% 7.25/1.49  
% 7.25/1.49  fof(f5,axiom,(
% 7.25/1.49    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 7.25/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.25/1.49  
% 7.25/1.49  fof(f44,plain,(
% 7.25/1.49    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 7.25/1.49    inference(cnf_transformation,[],[f5])).
% 7.25/1.49  
% 7.25/1.49  fof(f8,axiom,(
% 7.25/1.49    ! [X0,X1,X2,X3,X4] : ~(! [X5,X6] : ~(r2_hidden(X6,k3_xboole_0(X2,X4)) & r2_hidden(X5,k3_xboole_0(X1,X3)) & k4_tarski(X5,X6) = X0) & r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))))),
% 7.25/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.25/1.49  
% 7.25/1.49  fof(f17,plain,(
% 7.25/1.49    ! [X0,X1,X2,X3,X4] : (? [X5,X6] : (r2_hidden(X6,k3_xboole_0(X2,X4)) & r2_hidden(X5,k3_xboole_0(X1,X3)) & k4_tarski(X5,X6) = X0) | ~r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))))),
% 7.25/1.49    inference(ennf_transformation,[],[f8])).
% 7.25/1.49  
% 7.25/1.49  fof(f26,plain,(
% 7.25/1.49    ! [X4,X3,X2,X1,X0] : (? [X5,X6] : (r2_hidden(X6,k3_xboole_0(X2,X4)) & r2_hidden(X5,k3_xboole_0(X1,X3)) & k4_tarski(X5,X6) = X0) => (r2_hidden(sK3(X0,X1,X2,X3,X4),k3_xboole_0(X2,X4)) & r2_hidden(sK2(X0,X1,X2,X3,X4),k3_xboole_0(X1,X3)) & k4_tarski(sK2(X0,X1,X2,X3,X4),sK3(X0,X1,X2,X3,X4)) = X0))),
% 7.25/1.49    introduced(choice_axiom,[])).
% 7.25/1.49  
% 7.25/1.49  fof(f27,plain,(
% 7.25/1.49    ! [X0,X1,X2,X3,X4] : ((r2_hidden(sK3(X0,X1,X2,X3,X4),k3_xboole_0(X2,X4)) & r2_hidden(sK2(X0,X1,X2,X3,X4),k3_xboole_0(X1,X3)) & k4_tarski(sK2(X0,X1,X2,X3,X4),sK3(X0,X1,X2,X3,X4)) = X0) | ~r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))))),
% 7.25/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f17,f26])).
% 7.25/1.49  
% 7.25/1.49  fof(f48,plain,(
% 7.25/1.49    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(sK2(X0,X1,X2,X3,X4),k3_xboole_0(X1,X3)) | ~r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)))) )),
% 7.25/1.49    inference(cnf_transformation,[],[f27])).
% 7.25/1.49  
% 7.25/1.49  fof(f37,plain,(
% 7.25/1.49    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 7.25/1.49    inference(cnf_transformation,[],[f25])).
% 7.25/1.49  
% 7.25/1.49  fof(f60,plain,(
% 7.25/1.49    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 7.25/1.49    inference(definition_unfolding,[],[f37,f43])).
% 7.25/1.49  
% 7.25/1.49  fof(f63,plain,(
% 7.25/1.49    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 7.25/1.49    inference(equality_resolution,[],[f60])).
% 7.25/1.49  
% 7.25/1.49  fof(f10,conjecture,(
% 7.25/1.49    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 7.25/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.25/1.49  
% 7.25/1.49  fof(f11,negated_conjecture,(
% 7.25/1.49    ~! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 7.25/1.49    inference(negated_conjecture,[],[f10])).
% 7.25/1.49  
% 7.25/1.49  fof(f18,plain,(
% 7.25/1.49    ? [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <~> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 7.25/1.49    inference(ennf_transformation,[],[f11])).
% 7.25/1.49  
% 7.25/1.49  fof(f30,plain,(
% 7.25/1.49    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 7.25/1.49    inference(nnf_transformation,[],[f18])).
% 7.25/1.49  
% 7.25/1.49  fof(f31,plain,(
% 7.25/1.49    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 7.25/1.49    inference(flattening,[],[f30])).
% 7.25/1.49  
% 7.25/1.49  fof(f32,plain,(
% 7.25/1.49    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1))) => (((k1_xboole_0 != sK5 & k1_xboole_0 != sK4) | k1_xboole_0 != k2_zfmisc_1(sK4,sK5)) & (k1_xboole_0 = sK5 | k1_xboole_0 = sK4 | k1_xboole_0 = k2_zfmisc_1(sK4,sK5)))),
% 7.25/1.49    introduced(choice_axiom,[])).
% 7.25/1.49  
% 7.25/1.49  fof(f33,plain,(
% 7.25/1.49    ((k1_xboole_0 != sK5 & k1_xboole_0 != sK4) | k1_xboole_0 != k2_zfmisc_1(sK4,sK5)) & (k1_xboole_0 = sK5 | k1_xboole_0 = sK4 | k1_xboole_0 = k2_zfmisc_1(sK4,sK5))),
% 7.25/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f31,f32])).
% 7.25/1.49  
% 7.25/1.49  fof(f53,plain,(
% 7.25/1.49    k1_xboole_0 = sK5 | k1_xboole_0 = sK4 | k1_xboole_0 = k2_zfmisc_1(sK4,sK5)),
% 7.25/1.49    inference(cnf_transformation,[],[f33])).
% 7.25/1.49  
% 7.25/1.49  fof(f9,axiom,(
% 7.25/1.49    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 7.25/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.25/1.49  
% 7.25/1.49  fof(f28,plain,(
% 7.25/1.49    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 7.25/1.49    inference(nnf_transformation,[],[f9])).
% 7.25/1.49  
% 7.25/1.49  fof(f29,plain,(
% 7.25/1.49    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 7.25/1.49    inference(flattening,[],[f28])).
% 7.25/1.49  
% 7.25/1.49  fof(f52,plain,(
% 7.25/1.49    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 7.25/1.49    inference(cnf_transformation,[],[f29])).
% 7.25/1.49  
% 7.25/1.49  fof(f54,plain,(
% 7.25/1.49    k1_xboole_0 != sK4 | k1_xboole_0 != k2_zfmisc_1(sK4,sK5)),
% 7.25/1.49    inference(cnf_transformation,[],[f33])).
% 7.25/1.49  
% 7.25/1.49  fof(f55,plain,(
% 7.25/1.49    k1_xboole_0 != sK5 | k1_xboole_0 != k2_zfmisc_1(sK4,sK5)),
% 7.25/1.49    inference(cnf_transformation,[],[f33])).
% 7.25/1.49  
% 7.25/1.49  fof(f49,plain,(
% 7.25/1.49    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(sK3(X0,X1,X2,X3,X4),k3_xboole_0(X2,X4)) | ~r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)))) )),
% 7.25/1.49    inference(cnf_transformation,[],[f27])).
% 7.25/1.49  
% 7.25/1.49  cnf(c_1,plain,
% 7.25/1.49      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 7.25/1.49      inference(cnf_transformation,[],[f34]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_10,plain,
% 7.25/1.49      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 7.25/1.49      inference(cnf_transformation,[],[f45]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_211,plain,
% 7.25/1.49      ( r2_hidden(sK0(X0,X1),X0) | k3_xboole_0(X0,X1) = X0 ),
% 7.25/1.49      inference(resolution,[status(thm)],[c_1,c_10]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_568,plain,
% 7.25/1.49      ( k3_xboole_0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X0) = iProver_top ),
% 7.25/1.49      inference(predicate_to_equality,[status(thm)],[c_211]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_0,plain,
% 7.25/1.49      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 7.25/1.49      inference(cnf_transformation,[],[f35]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_222,plain,
% 7.25/1.49      ( ~ r2_hidden(sK0(X0,X1),X1) | k3_xboole_0(X0,X1) = X0 ),
% 7.25/1.49      inference(resolution,[status(thm)],[c_0,c_10]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_567,plain,
% 7.25/1.49      ( k3_xboole_0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1) != iProver_top ),
% 7.25/1.49      inference(predicate_to_equality,[status(thm)],[c_222]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_3319,plain,
% 7.25/1.49      ( k3_xboole_0(X0,X0) = X0 ),
% 7.25/1.49      inference(superposition,[status(thm)],[c_568,c_567]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_4,plain,
% 7.25/1.49      ( r2_hidden(sK1(X0,X1,X2),X0)
% 7.25/1.49      | r2_hidden(sK1(X0,X1,X2),X2)
% 7.25/1.49      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
% 7.25/1.49      inference(cnf_transformation,[],[f58]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_578,plain,
% 7.25/1.49      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
% 7.25/1.49      | r2_hidden(sK1(X0,X1,X2),X0) = iProver_top
% 7.25/1.49      | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
% 7.25/1.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_3,plain,
% 7.25/1.49      ( ~ r2_hidden(sK1(X0,X1,X2),X1)
% 7.25/1.49      | r2_hidden(sK1(X0,X1,X2),X2)
% 7.25/1.49      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
% 7.25/1.49      inference(cnf_transformation,[],[f57]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_579,plain,
% 7.25/1.49      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
% 7.25/1.49      | r2_hidden(sK1(X0,X1,X2),X1) != iProver_top
% 7.25/1.49      | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
% 7.25/1.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_3275,plain,
% 7.25/1.49      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = X1
% 7.25/1.49      | r2_hidden(sK1(X0,X0,X1),X1) = iProver_top ),
% 7.25/1.49      inference(superposition,[status(thm)],[c_578,c_579]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_11,plain,
% 7.25/1.49      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 7.25/1.49      inference(cnf_transformation,[],[f46]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_4097,plain,
% 7.25/1.49      ( k1_xboole_0 = X0 | r2_hidden(sK1(X1,X1,X0),X0) = iProver_top ),
% 7.25/1.49      inference(light_normalisation,[status(thm)],[c_3275,c_11,c_3319]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_8,plain,
% 7.25/1.49      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 7.25/1.49      inference(cnf_transformation,[],[f42]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_9,plain,
% 7.25/1.49      ( r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
% 7.25/1.49      inference(cnf_transformation,[],[f44]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_204,plain,
% 7.25/1.49      ( k5_xboole_0(X0,X1) != X2
% 7.25/1.49      | k3_xboole_0(X0,X1) != X3
% 7.25/1.49      | k3_xboole_0(X3,X2) = k1_xboole_0 ),
% 7.25/1.49      inference(resolution_lifted,[status(thm)],[c_8,c_9]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_205,plain,
% 7.25/1.49      ( k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) = k1_xboole_0 ),
% 7.25/1.49      inference(unflattening,[status(thm)],[c_204]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_717,plain,
% 7.25/1.49      ( k3_xboole_0(k3_xboole_0(X0,X0),k1_xboole_0) = k1_xboole_0 ),
% 7.25/1.49      inference(superposition,[status(thm)],[c_11,c_205]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_13,plain,
% 7.25/1.49      ( ~ r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)))
% 7.25/1.49      | r2_hidden(sK2(X0,X1,X2,X3,X4),k3_xboole_0(X1,X3)) ),
% 7.25/1.49      inference(cnf_transformation,[],[f48]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_573,plain,
% 7.25/1.49      ( r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))) != iProver_top
% 7.25/1.49      | r2_hidden(sK2(X0,X1,X2,X3,X4),k3_xboole_0(X1,X3)) = iProver_top ),
% 7.25/1.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_2513,plain,
% 7.25/1.49      ( r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(k3_xboole_0(X1,X1),X2),k2_zfmisc_1(k1_xboole_0,X3))) != iProver_top
% 7.25/1.49      | r2_hidden(sK2(X0,k3_xboole_0(X1,X1),X2,k1_xboole_0,X3),k1_xboole_0) = iProver_top ),
% 7.25/1.49      inference(superposition,[status(thm)],[c_717,c_573]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_7616,plain,
% 7.25/1.49      ( r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k1_xboole_0,X3))) != iProver_top
% 7.25/1.49      | r2_hidden(sK2(X0,X1,X2,k1_xboole_0,X3),k1_xboole_0) = iProver_top ),
% 7.25/1.49      inference(demodulation,[status(thm)],[c_2513,c_3319]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_7624,plain,
% 7.25/1.49      ( k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(k1_xboole_0,X2)) = k1_xboole_0
% 7.25/1.49      | r2_hidden(sK2(sK1(X3,X3,k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(k1_xboole_0,X2))),X0,X1,k1_xboole_0,X2),k1_xboole_0) = iProver_top ),
% 7.25/1.49      inference(superposition,[status(thm)],[c_4097,c_7616]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_721,plain,
% 7.25/1.49      ( k3_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(X0,X0),k1_xboole_0)) = k1_xboole_0 ),
% 7.25/1.49      inference(superposition,[status(thm)],[c_717,c_205]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_793,plain,
% 7.25/1.49      ( k3_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(X0,X0),k1_xboole_0))) = k1_xboole_0 ),
% 7.25/1.49      inference(superposition,[status(thm)],[c_721,c_205]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_718,plain,
% 7.25/1.49      ( k3_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) = k1_xboole_0 ),
% 7.25/1.49      inference(superposition,[status(thm)],[c_205,c_205]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_1116,plain,
% 7.25/1.49      ( k3_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(X0,X0),k1_xboole_0))))) = k1_xboole_0 ),
% 7.25/1.49      inference(superposition,[status(thm)],[c_793,c_718]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_800,plain,
% 7.25/1.49      ( k3_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))))) = k1_xboole_0 ),
% 7.25/1.49      inference(superposition,[status(thm)],[c_718,c_718]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_1553,plain,
% 7.25/1.49      ( k3_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(X0,X0),k1_xboole_0))))))))) = k1_xboole_0 ),
% 7.25/1.49      inference(superposition,[status(thm)],[c_1116,c_800]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_5425,plain,
% 7.25/1.49      ( k3_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0))))))))) = k1_xboole_0 ),
% 7.25/1.49      inference(light_normalisation,[status(thm)],[c_1553,c_1553,c_3319]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_6,plain,
% 7.25/1.49      ( ~ r2_hidden(X0,X1)
% 7.25/1.49      | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
% 7.25/1.49      inference(cnf_transformation,[],[f63]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_576,plain,
% 7.25/1.49      ( r2_hidden(X0,X1) != iProver_top
% 7.25/1.49      | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
% 7.25/1.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_5449,plain,
% 7.25/1.49      ( r2_hidden(X0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k1_xboole_0))))))))) != iProver_top
% 7.25/1.49      | r2_hidden(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) != iProver_top ),
% 7.25/1.49      inference(superposition,[status(thm)],[c_5425,c_576]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_5452,plain,
% 7.25/1.49      ( r2_hidden(X0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k1_xboole_0))))))))) != iProver_top
% 7.25/1.49      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.25/1.49      inference(demodulation,[status(thm)],[c_5449,c_11]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_5500,plain,
% 7.25/1.49      ( r2_hidden(X0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_xboole_0)))))))) != iProver_top
% 7.25/1.49      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.25/1.49      inference(superposition,[status(thm)],[c_11,c_5452]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_5501,plain,
% 7.25/1.49      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.25/1.49      inference(demodulation,[status(thm)],[c_5500,c_11]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_9740,plain,
% 7.25/1.49      ( k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(k1_xboole_0,X2)) = k1_xboole_0 ),
% 7.25/1.49      inference(superposition,[status(thm)],[c_7624,c_5501]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_12640,plain,
% 7.25/1.49      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.25/1.49      inference(superposition,[status(thm)],[c_3319,c_9740]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_20,negated_conjecture,
% 7.25/1.49      ( k1_xboole_0 = k2_zfmisc_1(sK4,sK5)
% 7.25/1.49      | k1_xboole_0 = sK4
% 7.25/1.49      | k1_xboole_0 = sK5 ),
% 7.25/1.49      inference(cnf_transformation,[],[f53]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_15,plain,
% 7.25/1.49      ( ~ r2_hidden(X0,X1)
% 7.25/1.49      | ~ r2_hidden(X2,X3)
% 7.25/1.49      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 7.25/1.49      inference(cnf_transformation,[],[f52]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_571,plain,
% 7.25/1.49      ( r2_hidden(X0,X1) != iProver_top
% 7.25/1.49      | r2_hidden(X2,X3) != iProver_top
% 7.25/1.49      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
% 7.25/1.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_1565,plain,
% 7.25/1.49      ( sK4 = k1_xboole_0
% 7.25/1.49      | sK5 = k1_xboole_0
% 7.25/1.49      | r2_hidden(X0,sK4) != iProver_top
% 7.25/1.49      | r2_hidden(X1,sK5) != iProver_top
% 7.25/1.49      | r2_hidden(k4_tarski(X0,X1),k1_xboole_0) = iProver_top ),
% 7.25/1.49      inference(superposition,[status(thm)],[c_20,c_571]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_5660,plain,
% 7.25/1.49      ( sK4 = k1_xboole_0
% 7.25/1.49      | sK5 = k1_xboole_0
% 7.25/1.49      | r2_hidden(X0,sK4) != iProver_top
% 7.25/1.49      | r2_hidden(X1,sK5) != iProver_top ),
% 7.25/1.49      inference(superposition,[status(thm)],[c_1565,c_5501]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_5858,plain,
% 7.25/1.49      ( sK4 = k1_xboole_0
% 7.25/1.49      | sK5 = k1_xboole_0
% 7.25/1.49      | r2_hidden(X0,sK5) != iProver_top ),
% 7.25/1.49      inference(superposition,[status(thm)],[c_4097,c_5660]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_6299,plain,
% 7.25/1.49      ( sK4 = k1_xboole_0 | sK5 = k1_xboole_0 ),
% 7.25/1.49      inference(superposition,[status(thm)],[c_4097,c_5858]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_19,negated_conjecture,
% 7.25/1.49      ( k1_xboole_0 != k2_zfmisc_1(sK4,sK5) | k1_xboole_0 != sK4 ),
% 7.25/1.49      inference(cnf_transformation,[],[f54]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_6303,plain,
% 7.25/1.49      ( k2_zfmisc_1(k1_xboole_0,sK5) != k1_xboole_0
% 7.25/1.49      | sK4 != k1_xboole_0
% 7.25/1.49      | sK5 = k1_xboole_0 ),
% 7.25/1.49      inference(superposition,[status(thm)],[c_6299,c_19]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_6397,plain,
% 7.25/1.49      ( k2_zfmisc_1(k1_xboole_0,sK5) != k1_xboole_0 | sK5 = k1_xboole_0 ),
% 7.25/1.49      inference(global_propositional_subsumption,[status(thm)],[c_6303,c_6299]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_13212,plain,
% 7.25/1.49      ( sK5 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 7.25/1.49      inference(demodulation,[status(thm)],[c_12640,c_6397]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_13213,plain,
% 7.25/1.49      ( sK5 = k1_xboole_0 ),
% 7.25/1.49      inference(equality_resolution_simp,[status(thm)],[c_13212]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_18,negated_conjecture,
% 7.25/1.49      ( k1_xboole_0 != k2_zfmisc_1(sK4,sK5) | k1_xboole_0 != sK5 ),
% 7.25/1.49      inference(cnf_transformation,[],[f55]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_13538,plain,
% 7.25/1.49      ( k2_zfmisc_1(sK4,k1_xboole_0) != k1_xboole_0
% 7.25/1.49      | k1_xboole_0 != k1_xboole_0 ),
% 7.25/1.49      inference(demodulation,[status(thm)],[c_13213,c_18]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_13539,plain,
% 7.25/1.49      ( k2_zfmisc_1(sK4,k1_xboole_0) != k1_xboole_0 ),
% 7.25/1.49      inference(equality_resolution_simp,[status(thm)],[c_13538]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_12,plain,
% 7.25/1.49      ( ~ r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)))
% 7.25/1.49      | r2_hidden(sK3(X0,X1,X2,X3,X4),k3_xboole_0(X2,X4)) ),
% 7.25/1.49      inference(cnf_transformation,[],[f49]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_574,plain,
% 7.25/1.49      ( r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))) != iProver_top
% 7.25/1.49      | r2_hidden(sK3(X0,X1,X2,X3,X4),k3_xboole_0(X2,X4)) = iProver_top ),
% 7.25/1.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_2974,plain,
% 7.25/1.49      ( r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,k3_xboole_0(X2,X2)),k2_zfmisc_1(X3,k1_xboole_0))) != iProver_top
% 7.25/1.49      | r2_hidden(sK3(X0,X1,k3_xboole_0(X2,X2),X3,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 7.25/1.49      inference(superposition,[status(thm)],[c_717,c_574]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_7832,plain,
% 7.25/1.49      ( r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,k1_xboole_0))) != iProver_top
% 7.25/1.49      | r2_hidden(sK3(X0,X1,X2,X3,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 7.25/1.49      inference(demodulation,[status(thm)],[c_2974,c_3319]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_7840,plain,
% 7.25/1.49      ( k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,k1_xboole_0)) = k1_xboole_0
% 7.25/1.49      | r2_hidden(sK3(sK1(X3,X3,k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,k1_xboole_0))),X0,X1,X2,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 7.25/1.49      inference(superposition,[status(thm)],[c_4097,c_7832]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_10223,plain,
% 7.25/1.49      ( k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,k1_xboole_0)) = k1_xboole_0 ),
% 7.25/1.49      inference(superposition,[status(thm)],[c_7840,c_5501]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_12643,plain,
% 7.25/1.49      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 7.25/1.49      inference(superposition,[status(thm)],[c_3319,c_10223]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_13540,plain,
% 7.25/1.49      ( k1_xboole_0 != k1_xboole_0 ),
% 7.25/1.49      inference(demodulation,[status(thm)],[c_13539,c_12643]) ).
% 7.25/1.49  
% 7.25/1.49  cnf(c_13541,plain,
% 7.25/1.49      ( $false ),
% 7.25/1.49      inference(equality_resolution_simp,[status(thm)],[c_13540]) ).
% 7.25/1.49  
% 7.25/1.49  
% 7.25/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.25/1.49  
% 7.25/1.49  ------                               Statistics
% 7.25/1.49  
% 7.25/1.49  ------ General
% 7.25/1.49  
% 7.25/1.49  abstr_ref_over_cycles:                  0
% 7.25/1.49  abstr_ref_under_cycles:                 0
% 7.25/1.49  gc_basic_clause_elim:                   0
% 7.25/1.49  forced_gc_time:                         0
% 7.25/1.49  parsing_time:                           0.008
% 7.25/1.49  unif_index_cands_time:                  0.
% 7.25/1.49  unif_index_add_time:                    0.
% 7.25/1.49  orderings_time:                         0.
% 7.25/1.49  out_proof_time:                         0.01
% 7.25/1.49  total_time:                             0.516
% 7.25/1.49  num_of_symbols:                         45
% 7.25/1.49  num_of_terms:                           26375
% 7.25/1.49  
% 7.25/1.49  ------ Preprocessing
% 7.25/1.49  
% 7.25/1.49  num_of_splits:                          0
% 7.25/1.49  num_of_split_atoms:                     0
% 7.25/1.49  num_of_reused_defs:                     0
% 7.25/1.49  num_eq_ax_congr_red:                    50
% 7.25/1.49  num_of_sem_filtered_clauses:            1
% 7.25/1.49  num_of_subtypes:                        0
% 7.25/1.49  monotx_restored_types:                  0
% 7.25/1.49  sat_num_of_epr_types:                   0
% 7.25/1.49  sat_num_of_non_cyclic_types:            0
% 7.25/1.49  sat_guarded_non_collapsed_types:        0
% 7.25/1.49  num_pure_diseq_elim:                    0
% 7.25/1.49  simp_replaced_by:                       0
% 7.25/1.49  res_preprocessed:                       93
% 7.25/1.49  prep_upred:                             0
% 7.25/1.49  prep_unflattend:                        2
% 7.25/1.49  smt_new_axioms:                         0
% 7.25/1.49  pred_elim_cands:                        1
% 7.25/1.49  pred_elim:                              2
% 7.25/1.49  pred_elim_cl:                           2
% 7.25/1.49  pred_elim_cycles:                       4
% 7.25/1.49  merged_defs:                            0
% 7.25/1.49  merged_defs_ncl:                        0
% 7.25/1.49  bin_hyper_res:                          0
% 7.25/1.49  prep_cycles:                            4
% 7.25/1.49  pred_elim_time:                         0.001
% 7.25/1.49  splitting_time:                         0.
% 7.25/1.49  sem_filter_time:                        0.
% 7.25/1.49  monotx_time:                            0.001
% 7.25/1.49  subtype_inf_time:                       0.
% 7.25/1.49  
% 7.25/1.49  ------ Problem properties
% 7.25/1.49  
% 7.25/1.49  clauses:                                19
% 7.25/1.49  conjectures:                            3
% 7.25/1.49  epr:                                    0
% 7.25/1.49  horn:                                   13
% 7.25/1.49  ground:                                 3
% 7.25/1.49  unary:                                  2
% 7.25/1.49  binary:                                 11
% 7.25/1.49  lits:                                   43
% 7.25/1.49  lits_eq:                                15
% 7.25/1.49  fd_pure:                                0
% 7.25/1.49  fd_pseudo:                              0
% 7.25/1.49  fd_cond:                                0
% 7.25/1.49  fd_pseudo_cond:                         3
% 7.25/1.49  ac_symbols:                             0
% 7.25/1.49  
% 7.25/1.49  ------ Propositional Solver
% 7.25/1.49  
% 7.25/1.49  prop_solver_calls:                      34
% 7.25/1.49  prop_fast_solver_calls:                 1761
% 7.25/1.49  smt_solver_calls:                       0
% 7.25/1.49  smt_fast_solver_calls:                  0
% 7.25/1.49  prop_num_of_clauses:                    6229
% 7.25/1.49  prop_preprocess_simplified:             9659
% 7.25/1.49  prop_fo_subsumed:                       343
% 7.25/1.49  prop_solver_time:                       0.
% 7.25/1.49  smt_solver_time:                        0.
% 7.25/1.49  smt_fast_solver_time:                   0.
% 7.25/1.49  prop_fast_solver_time:                  0.
% 7.25/1.49  prop_unsat_core_time:                   0.
% 7.25/1.49  
% 7.25/1.49  ------ QBF
% 7.25/1.49  
% 7.25/1.49  qbf_q_res:                              0
% 7.25/1.49  qbf_num_tautologies:                    0
% 7.25/1.49  qbf_prep_cycles:                        0
% 7.25/1.49  
% 7.25/1.49  ------ BMC1
% 7.25/1.49  
% 7.25/1.49  bmc1_current_bound:                     -1
% 7.25/1.49  bmc1_last_solved_bound:                 -1
% 7.25/1.49  bmc1_unsat_core_size:                   -1
% 7.25/1.49  bmc1_unsat_core_parents_size:           -1
% 7.25/1.49  bmc1_merge_next_fun:                    0
% 7.25/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.25/1.49  
% 7.25/1.49  ------ Instantiation
% 7.25/1.49  
% 7.25/1.49  inst_num_of_clauses:                    1323
% 7.25/1.49  inst_num_in_passive:                    95
% 7.25/1.49  inst_num_in_active:                     659
% 7.25/1.49  inst_num_in_unprocessed:                569
% 7.25/1.49  inst_num_of_loops:                      800
% 7.25/1.49  inst_num_of_learning_restarts:          0
% 7.25/1.49  inst_num_moves_active_passive:          135
% 7.25/1.49  inst_lit_activity:                      0
% 7.25/1.49  inst_lit_activity_moves:                0
% 7.25/1.49  inst_num_tautologies:                   0
% 7.25/1.49  inst_num_prop_implied:                  0
% 7.25/1.49  inst_num_existing_simplified:           0
% 7.25/1.49  inst_num_eq_res_simplified:             0
% 7.25/1.49  inst_num_child_elim:                    0
% 7.25/1.49  inst_num_of_dismatching_blockings:      1169
% 7.25/1.49  inst_num_of_non_proper_insts:           1548
% 7.25/1.49  inst_num_of_duplicates:                 0
% 7.25/1.49  inst_inst_num_from_inst_to_res:         0
% 7.25/1.49  inst_dismatching_checking_time:         0.
% 7.25/1.49  
% 7.25/1.49  ------ Resolution
% 7.25/1.49  
% 7.25/1.49  res_num_of_clauses:                     0
% 7.25/1.49  res_num_in_passive:                     0
% 7.25/1.49  res_num_in_active:                      0
% 7.25/1.49  res_num_of_loops:                       97
% 7.25/1.49  res_forward_subset_subsumed:            40
% 7.25/1.49  res_backward_subset_subsumed:           0
% 7.25/1.49  res_forward_subsumed:                   0
% 7.25/1.49  res_backward_subsumed:                  0
% 7.25/1.49  res_forward_subsumption_resolution:     0
% 7.25/1.49  res_backward_subsumption_resolution:    0
% 7.25/1.49  res_clause_to_clause_subsumption:       3396
% 7.25/1.49  res_orphan_elimination:                 0
% 7.25/1.49  res_tautology_del:                      130
% 7.25/1.49  res_num_eq_res_simplified:              0
% 7.25/1.49  res_num_sel_changes:                    0
% 7.25/1.49  res_moves_from_active_to_pass:          0
% 7.25/1.49  
% 7.25/1.49  ------ Superposition
% 7.25/1.49  
% 7.25/1.49  sup_time_total:                         0.
% 7.25/1.49  sup_time_generating:                    0.
% 7.25/1.49  sup_time_sim_full:                      0.
% 7.25/1.49  sup_time_sim_immed:                     0.
% 7.25/1.49  
% 7.25/1.49  sup_num_of_clauses:                     677
% 7.25/1.49  sup_num_in_active:                      69
% 7.25/1.49  sup_num_in_passive:                     608
% 7.25/1.49  sup_num_of_loops:                       158
% 7.25/1.49  sup_fw_superposition:                   966
% 7.25/1.49  sup_bw_superposition:                   760
% 7.25/1.49  sup_immediate_simplified:               684
% 7.25/1.49  sup_given_eliminated:                   2
% 7.25/1.49  comparisons_done:                       0
% 7.25/1.49  comparisons_avoided:                    198
% 7.25/1.49  
% 7.25/1.49  ------ Simplifications
% 7.25/1.49  
% 7.25/1.49  
% 7.25/1.49  sim_fw_subset_subsumed:                 75
% 7.25/1.49  sim_bw_subset_subsumed:                 11
% 7.25/1.49  sim_fw_subsumed:                        170
% 7.25/1.49  sim_bw_subsumed:                        66
% 7.25/1.49  sim_fw_subsumption_res:                 0
% 7.25/1.49  sim_bw_subsumption_res:                 0
% 7.25/1.49  sim_tautology_del:                      59
% 7.25/1.49  sim_eq_tautology_del:                   145
% 7.25/1.49  sim_eq_res_simp:                        3
% 7.25/1.49  sim_fw_demodulated:                     412
% 7.25/1.49  sim_bw_demodulated:                     34
% 7.25/1.49  sim_light_normalised:                   187
% 7.25/1.49  sim_joinable_taut:                      0
% 7.25/1.49  sim_joinable_simp:                      0
% 7.25/1.49  sim_ac_normalised:                      0
% 7.25/1.49  sim_smt_subsumption:                    0
% 7.25/1.49  
%------------------------------------------------------------------------------
