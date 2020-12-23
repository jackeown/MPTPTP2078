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
% DateTime   : Thu Dec  3 11:37:01 EST 2020

% Result     : Theorem 3.00s
% Output     : CNFRefutation 3.00s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 442 expanded)
%              Number of clauses        :   47 ( 138 expanded)
%              Number of leaves         :   12 ( 112 expanded)
%              Depth                    :   22
%              Number of atoms          :  315 (2252 expanded)
%              Number of equality atoms :  177 ( 909 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f14,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f14])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f12,f16])).

fof(f32,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X4,X5] :
                  ( k4_tarski(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) ) )
            & ( ? [X4,X5] :
                  ( k4_tarski(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X6,X7] :
                  ( k4_tarski(X6,X7) = X3
                  & r2_hidden(X7,X1)
                  & r2_hidden(X6,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ? [X11,X12] :
                  ( k4_tarski(X11,X12) = X8
                  & r2_hidden(X12,X1)
                  & r2_hidden(X11,X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f19])).

fof(f23,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8
        & r2_hidden(sK6(X0,X1,X8),X1)
        & r2_hidden(sK5(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X6,X7] :
          ( k4_tarski(X6,X7) = X3
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)) = X3
        & r2_hidden(sK4(X0,X1,X2),X1)
        & r2_hidden(sK3(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != X3
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X6,X7] :
                ( k4_tarski(X6,X7) = X3
                & r2_hidden(X7,X1)
                & r2_hidden(X6,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X5,X4] :
              ( k4_tarski(X4,X5) != sK2(X0,X1,X2)
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X0) )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ? [X7,X6] :
              ( k4_tarski(X6,X7) = sK2(X0,X1,X2)
              & r2_hidden(X7,X1)
              & r2_hidden(X6,X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != sK2(X0,X1,X2)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)) = sK2(X0,X1,X2)
              & r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ( k4_tarski(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8
                & r2_hidden(sK6(X0,X1,X8),X1)
                & r2_hidden(sK5(X0,X1,X8),X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f20,f23,f22,f21])).

fof(f38,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK5(X0,X1,X8),X0)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f54,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK5(X0,X1,X8),X0)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f38])).

fof(f39,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK6(X0,X1,X8),X1)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f53,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK6(X0,X1,X8),X1)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f39])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      <=> ( k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f13,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <~> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ( ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ( ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f25])).

fof(f27,plain,
    ( ? [X0,X1] :
        ( ( ( k1_xboole_0 != X1
            & k1_xboole_0 != X0 )
          | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
        & ( k1_xboole_0 = X1
          | k1_xboole_0 = X0
          | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) )
   => ( ( ( k1_xboole_0 != sK8
          & k1_xboole_0 != sK7 )
        | k1_xboole_0 != k2_zfmisc_1(sK7,sK8) )
      & ( k1_xboole_0 = sK8
        | k1_xboole_0 = sK7
        | k1_xboole_0 = k2_zfmisc_1(sK7,sK8) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ( ( k1_xboole_0 != sK8
        & k1_xboole_0 != sK7 )
      | k1_xboole_0 != k2_zfmisc_1(sK7,sK8) )
    & ( k1_xboole_0 = sK8
      | k1_xboole_0 = sK7
      | k1_xboole_0 = k2_zfmisc_1(sK7,sK8) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f26,f27])).

fof(f46,plain,
    ( k1_xboole_0 = sK8
    | k1_xboole_0 = sK7
    | k1_xboole_0 = k2_zfmisc_1(sK7,sK8) ),
    inference(cnf_transformation,[],[f28])).

fof(f41,plain,(
    ! [X2,X0,X10,X8,X1,X9] :
      ( r2_hidden(X8,X2)
      | k4_tarski(X9,X10) != X8
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f50,plain,(
    ! [X2,X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),X2)
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f41])).

fof(f51,plain,(
    ! [X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0) ) ),
    inference(equality_resolution,[],[f50])).

fof(f47,plain,
    ( k1_xboole_0 != sK7
    | k1_xboole_0 != k2_zfmisc_1(sK7,sK8) ),
    inference(cnf_transformation,[],[f28])).

fof(f48,plain,
    ( k1_xboole_0 != sK8
    | k1_xboole_0 != k2_zfmisc_1(sK7,sK8) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_5,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_6,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) != X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_636,plain,
    ( k4_xboole_0(X0,X1) != X0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_969,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_636])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_639,plain,
    ( r2_hidden(sK0(X0,X1),X1) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_638,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_640,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r1_xboole_0(X2,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2217,plain,
    ( r2_hidden(sK0(X0,X1),X2) != iProver_top
    | r1_xboole_0(X2,X0) != iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_638,c_640])).

cnf(c_4688,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_639,c_2217])).

cnf(c_4738,plain,
    ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_969,c_4688])).

cnf(c_3,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_637,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(sK5(X1,X2,X0),X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_627,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(sK5(X1,X2,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(sK6(X1,X2,X0),X2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_628,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(sK6(X1,X2,X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2220,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(sK6(X1,X2,X0),X3) != iProver_top
    | r1_xboole_0(X3,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_628,c_640])).

cnf(c_5038,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r1_xboole_0(X2,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_628,c_2220])).

cnf(c_5069,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3))) != iProver_top
    | r1_xboole_0(X3,X3) != iProver_top ),
    inference(superposition,[status(thm)],[c_628,c_5038])).

cnf(c_5367,plain,
    ( r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3)),X4)) != iProver_top
    | r1_xboole_0(X3,X3) != iProver_top ),
    inference(superposition,[status(thm)],[c_627,c_5069])).

cnf(c_6370,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2)),X3) = k1_xboole_0
    | r1_xboole_0(X2,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_637,c_5367])).

cnf(c_6474,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,k1_xboole_0)),X2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4738,c_6370])).

cnf(c_5062,plain,
    ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    | r1_xboole_0(X1,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_637,c_5038])).

cnf(c_5169,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4738,c_5062])).

cnf(c_6477,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6474,c_5169])).

cnf(c_18,negated_conjecture,
    ( k1_xboole_0 = k2_zfmisc_1(sK7,sK8)
    | k1_xboole_0 = sK7
    | k1_xboole_0 = sK8 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_630,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2129,plain,
    ( sK7 = k1_xboole_0
    | sK8 = k1_xboole_0
    | r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(X1,sK8) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_18,c_630])).

cnf(c_2733,plain,
    ( sK7 = k1_xboole_0
    | sK8 = k1_xboole_0
    | r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(X1,sK8) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),X2) != iProver_top
    | r1_xboole_0(X2,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2129,c_640])).

cnf(c_2798,plain,
    ( sK7 = k1_xboole_0
    | sK8 = k1_xboole_0
    | r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(X1,sK8) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),X2) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2733,c_969])).

cnf(c_2803,plain,
    ( sK7 = k1_xboole_0
    | sK8 = k1_xboole_0
    | r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(X1,sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_2129,c_2798])).

cnf(c_2898,plain,
    ( sK7 = k1_xboole_0
    | sK8 = k1_xboole_0
    | r2_hidden(X0,sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_637,c_2803])).

cnf(c_4008,plain,
    ( sK7 = k1_xboole_0
    | sK8 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_637,c_2898])).

cnf(c_17,negated_conjecture,
    ( k1_xboole_0 != k2_zfmisc_1(sK7,sK8)
    | k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_4115,plain,
    ( k2_zfmisc_1(k1_xboole_0,sK8) != k1_xboole_0
    | sK7 != k1_xboole_0
    | sK8 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4008,c_17])).

cnf(c_4120,plain,
    ( k2_zfmisc_1(k1_xboole_0,sK8) != k1_xboole_0
    | sK8 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4115,c_4008])).

cnf(c_6485,plain,
    ( sK8 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6477,c_4120])).

cnf(c_6488,plain,
    ( sK8 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_6485])).

cnf(c_16,negated_conjecture,
    ( k1_xboole_0 != k2_zfmisc_1(sK7,sK8)
    | k1_xboole_0 != sK8 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_6572,plain,
    ( k2_zfmisc_1(sK7,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6488,c_16])).

cnf(c_6573,plain,
    ( k2_zfmisc_1(sK7,k1_xboole_0) != k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_6572])).

cnf(c_6575,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6573,c_5169])).

cnf(c_6576,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_6575])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:14:09 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.00/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.00/0.99  
% 3.00/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.00/0.99  
% 3.00/0.99  ------  iProver source info
% 3.00/0.99  
% 3.00/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.00/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.00/0.99  git: non_committed_changes: false
% 3.00/0.99  git: last_make_outside_of_git: false
% 3.00/0.99  
% 3.00/0.99  ------ 
% 3.00/0.99  
% 3.00/0.99  ------ Input Options
% 3.00/0.99  
% 3.00/0.99  --out_options                           all
% 3.00/0.99  --tptp_safe_out                         true
% 3.00/0.99  --problem_path                          ""
% 3.00/0.99  --include_path                          ""
% 3.00/0.99  --clausifier                            res/vclausify_rel
% 3.00/0.99  --clausifier_options                    --mode clausify
% 3.00/0.99  --stdin                                 false
% 3.00/0.99  --stats_out                             all
% 3.00/0.99  
% 3.00/0.99  ------ General Options
% 3.00/0.99  
% 3.00/0.99  --fof                                   false
% 3.00/0.99  --time_out_real                         305.
% 3.00/0.99  --time_out_virtual                      -1.
% 3.00/0.99  --symbol_type_check                     false
% 3.00/0.99  --clausify_out                          false
% 3.00/0.99  --sig_cnt_out                           false
% 3.00/0.99  --trig_cnt_out                          false
% 3.00/0.99  --trig_cnt_out_tolerance                1.
% 3.00/0.99  --trig_cnt_out_sk_spl                   false
% 3.00/0.99  --abstr_cl_out                          false
% 3.00/0.99  
% 3.00/0.99  ------ Global Options
% 3.00/0.99  
% 3.00/0.99  --schedule                              default
% 3.00/0.99  --add_important_lit                     false
% 3.00/0.99  --prop_solver_per_cl                    1000
% 3.00/0.99  --min_unsat_core                        false
% 3.00/0.99  --soft_assumptions                      false
% 3.00/0.99  --soft_lemma_size                       3
% 3.00/0.99  --prop_impl_unit_size                   0
% 3.00/0.99  --prop_impl_unit                        []
% 3.00/0.99  --share_sel_clauses                     true
% 3.00/0.99  --reset_solvers                         false
% 3.00/0.99  --bc_imp_inh                            [conj_cone]
% 3.00/0.99  --conj_cone_tolerance                   3.
% 3.00/0.99  --extra_neg_conj                        none
% 3.00/0.99  --large_theory_mode                     true
% 3.00/0.99  --prolific_symb_bound                   200
% 3.00/0.99  --lt_threshold                          2000
% 3.00/0.99  --clause_weak_htbl                      true
% 3.00/0.99  --gc_record_bc_elim                     false
% 3.00/0.99  
% 3.00/0.99  ------ Preprocessing Options
% 3.00/0.99  
% 3.00/0.99  --preprocessing_flag                    true
% 3.00/0.99  --time_out_prep_mult                    0.1
% 3.00/0.99  --splitting_mode                        input
% 3.00/0.99  --splitting_grd                         true
% 3.00/0.99  --splitting_cvd                         false
% 3.00/0.99  --splitting_cvd_svl                     false
% 3.00/0.99  --splitting_nvd                         32
% 3.00/0.99  --sub_typing                            true
% 3.00/0.99  --prep_gs_sim                           true
% 3.00/0.99  --prep_unflatten                        true
% 3.00/0.99  --prep_res_sim                          true
% 3.00/0.99  --prep_upred                            true
% 3.00/0.99  --prep_sem_filter                       exhaustive
% 3.00/0.99  --prep_sem_filter_out                   false
% 3.00/0.99  --pred_elim                             true
% 3.00/0.99  --res_sim_input                         true
% 3.00/0.99  --eq_ax_congr_red                       true
% 3.00/0.99  --pure_diseq_elim                       true
% 3.00/0.99  --brand_transform                       false
% 3.00/0.99  --non_eq_to_eq                          false
% 3.00/0.99  --prep_def_merge                        true
% 3.00/0.99  --prep_def_merge_prop_impl              false
% 3.00/0.99  --prep_def_merge_mbd                    true
% 3.00/0.99  --prep_def_merge_tr_red                 false
% 3.00/0.99  --prep_def_merge_tr_cl                  false
% 3.00/0.99  --smt_preprocessing                     true
% 3.00/0.99  --smt_ac_axioms                         fast
% 3.00/0.99  --preprocessed_out                      false
% 3.00/0.99  --preprocessed_stats                    false
% 3.00/0.99  
% 3.00/0.99  ------ Abstraction refinement Options
% 3.00/0.99  
% 3.00/0.99  --abstr_ref                             []
% 3.00/0.99  --abstr_ref_prep                        false
% 3.00/0.99  --abstr_ref_until_sat                   false
% 3.00/0.99  --abstr_ref_sig_restrict                funpre
% 3.00/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.00/0.99  --abstr_ref_under                       []
% 3.00/0.99  
% 3.00/0.99  ------ SAT Options
% 3.00/0.99  
% 3.00/0.99  --sat_mode                              false
% 3.00/0.99  --sat_fm_restart_options                ""
% 3.00/0.99  --sat_gr_def                            false
% 3.00/0.99  --sat_epr_types                         true
% 3.00/0.99  --sat_non_cyclic_types                  false
% 3.00/0.99  --sat_finite_models                     false
% 3.00/0.99  --sat_fm_lemmas                         false
% 3.00/0.99  --sat_fm_prep                           false
% 3.00/0.99  --sat_fm_uc_incr                        true
% 3.00/0.99  --sat_out_model                         small
% 3.00/0.99  --sat_out_clauses                       false
% 3.00/0.99  
% 3.00/0.99  ------ QBF Options
% 3.00/0.99  
% 3.00/0.99  --qbf_mode                              false
% 3.00/0.99  --qbf_elim_univ                         false
% 3.00/0.99  --qbf_dom_inst                          none
% 3.00/0.99  --qbf_dom_pre_inst                      false
% 3.00/0.99  --qbf_sk_in                             false
% 3.00/0.99  --qbf_pred_elim                         true
% 3.00/0.99  --qbf_split                             512
% 3.00/0.99  
% 3.00/0.99  ------ BMC1 Options
% 3.00/0.99  
% 3.00/0.99  --bmc1_incremental                      false
% 3.00/0.99  --bmc1_axioms                           reachable_all
% 3.00/0.99  --bmc1_min_bound                        0
% 3.00/0.99  --bmc1_max_bound                        -1
% 3.00/0.99  --bmc1_max_bound_default                -1
% 3.00/0.99  --bmc1_symbol_reachability              true
% 3.00/0.99  --bmc1_property_lemmas                  false
% 3.00/0.99  --bmc1_k_induction                      false
% 3.00/0.99  --bmc1_non_equiv_states                 false
% 3.00/0.99  --bmc1_deadlock                         false
% 3.00/0.99  --bmc1_ucm                              false
% 3.00/0.99  --bmc1_add_unsat_core                   none
% 3.00/0.99  --bmc1_unsat_core_children              false
% 3.00/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.00/0.99  --bmc1_out_stat                         full
% 3.00/0.99  --bmc1_ground_init                      false
% 3.00/0.99  --bmc1_pre_inst_next_state              false
% 3.00/0.99  --bmc1_pre_inst_state                   false
% 3.00/0.99  --bmc1_pre_inst_reach_state             false
% 3.00/0.99  --bmc1_out_unsat_core                   false
% 3.00/0.99  --bmc1_aig_witness_out                  false
% 3.00/0.99  --bmc1_verbose                          false
% 3.00/0.99  --bmc1_dump_clauses_tptp                false
% 3.00/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.00/0.99  --bmc1_dump_file                        -
% 3.00/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.00/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.00/0.99  --bmc1_ucm_extend_mode                  1
% 3.00/0.99  --bmc1_ucm_init_mode                    2
% 3.00/0.99  --bmc1_ucm_cone_mode                    none
% 3.00/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.00/0.99  --bmc1_ucm_relax_model                  4
% 3.00/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.00/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.00/0.99  --bmc1_ucm_layered_model                none
% 3.00/0.99  --bmc1_ucm_max_lemma_size               10
% 3.00/0.99  
% 3.00/0.99  ------ AIG Options
% 3.00/0.99  
% 3.00/0.99  --aig_mode                              false
% 3.00/0.99  
% 3.00/0.99  ------ Instantiation Options
% 3.00/0.99  
% 3.00/0.99  --instantiation_flag                    true
% 3.00/0.99  --inst_sos_flag                         false
% 3.00/0.99  --inst_sos_phase                        true
% 3.00/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.00/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.00/0.99  --inst_lit_sel_side                     num_symb
% 3.00/0.99  --inst_solver_per_active                1400
% 3.00/0.99  --inst_solver_calls_frac                1.
% 3.00/0.99  --inst_passive_queue_type               priority_queues
% 3.00/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.00/0.99  --inst_passive_queues_freq              [25;2]
% 3.00/0.99  --inst_dismatching                      true
% 3.00/0.99  --inst_eager_unprocessed_to_passive     true
% 3.00/0.99  --inst_prop_sim_given                   true
% 3.00/0.99  --inst_prop_sim_new                     false
% 3.00/0.99  --inst_subs_new                         false
% 3.00/0.99  --inst_eq_res_simp                      false
% 3.00/0.99  --inst_subs_given                       false
% 3.00/0.99  --inst_orphan_elimination               true
% 3.00/0.99  --inst_learning_loop_flag               true
% 3.00/0.99  --inst_learning_start                   3000
% 3.00/0.99  --inst_learning_factor                  2
% 3.00/0.99  --inst_start_prop_sim_after_learn       3
% 3.00/0.99  --inst_sel_renew                        solver
% 3.00/0.99  --inst_lit_activity_flag                true
% 3.00/0.99  --inst_restr_to_given                   false
% 3.00/0.99  --inst_activity_threshold               500
% 3.00/0.99  --inst_out_proof                        true
% 3.00/0.99  
% 3.00/0.99  ------ Resolution Options
% 3.00/0.99  
% 3.00/0.99  --resolution_flag                       true
% 3.00/0.99  --res_lit_sel                           adaptive
% 3.00/0.99  --res_lit_sel_side                      none
% 3.00/0.99  --res_ordering                          kbo
% 3.00/0.99  --res_to_prop_solver                    active
% 3.00/0.99  --res_prop_simpl_new                    false
% 3.00/0.99  --res_prop_simpl_given                  true
% 3.00/0.99  --res_passive_queue_type                priority_queues
% 3.00/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.00/0.99  --res_passive_queues_freq               [15;5]
% 3.00/0.99  --res_forward_subs                      full
% 3.00/0.99  --res_backward_subs                     full
% 3.00/0.99  --res_forward_subs_resolution           true
% 3.00/0.99  --res_backward_subs_resolution          true
% 3.00/0.99  --res_orphan_elimination                true
% 3.00/0.99  --res_time_limit                        2.
% 3.00/0.99  --res_out_proof                         true
% 3.00/0.99  
% 3.00/0.99  ------ Superposition Options
% 3.00/0.99  
% 3.00/0.99  --superposition_flag                    true
% 3.00/0.99  --sup_passive_queue_type                priority_queues
% 3.00/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.00/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.00/0.99  --demod_completeness_check              fast
% 3.00/0.99  --demod_use_ground                      true
% 3.00/0.99  --sup_to_prop_solver                    passive
% 3.00/0.99  --sup_prop_simpl_new                    true
% 3.00/0.99  --sup_prop_simpl_given                  true
% 3.00/0.99  --sup_fun_splitting                     false
% 3.00/0.99  --sup_smt_interval                      50000
% 3.00/0.99  
% 3.00/0.99  ------ Superposition Simplification Setup
% 3.00/0.99  
% 3.00/0.99  --sup_indices_passive                   []
% 3.00/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.00/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/0.99  --sup_full_bw                           [BwDemod]
% 3.00/0.99  --sup_immed_triv                        [TrivRules]
% 3.00/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.00/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/0.99  --sup_immed_bw_main                     []
% 3.00/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.00/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/0.99  
% 3.00/0.99  ------ Combination Options
% 3.00/0.99  
% 3.00/0.99  --comb_res_mult                         3
% 3.00/0.99  --comb_sup_mult                         2
% 3.00/0.99  --comb_inst_mult                        10
% 3.00/0.99  
% 3.00/0.99  ------ Debug Options
% 3.00/0.99  
% 3.00/0.99  --dbg_backtrace                         false
% 3.00/0.99  --dbg_dump_prop_clauses                 false
% 3.00/0.99  --dbg_dump_prop_clauses_file            -
% 3.00/0.99  --dbg_out_stat                          false
% 3.00/0.99  ------ Parsing...
% 3.00/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.00/0.99  
% 3.00/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.00/0.99  
% 3.00/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.00/0.99  
% 3.00/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.00/0.99  ------ Proving...
% 3.00/0.99  ------ Problem Properties 
% 3.00/0.99  
% 3.00/0.99  
% 3.00/0.99  clauses                                 19
% 3.00/0.99  conjectures                             3
% 3.00/0.99  EPR                                     1
% 3.00/0.99  Horn                                    12
% 3.00/0.99  unary                                   2
% 3.00/0.99  binary                                  10
% 3.00/0.99  lits                                    45
% 3.00/0.99  lits eq                                 19
% 3.00/0.99  fd_pure                                 0
% 3.00/0.99  fd_pseudo                               0
% 3.00/0.99  fd_cond                                 1
% 3.00/0.99  fd_pseudo_cond                          4
% 3.00/0.99  AC symbols                              0
% 3.00/0.99  
% 3.00/0.99  ------ Schedule dynamic 5 is on 
% 3.00/0.99  
% 3.00/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.00/0.99  
% 3.00/0.99  
% 3.00/0.99  ------ 
% 3.00/0.99  Current options:
% 3.00/0.99  ------ 
% 3.00/0.99  
% 3.00/0.99  ------ Input Options
% 3.00/0.99  
% 3.00/0.99  --out_options                           all
% 3.00/0.99  --tptp_safe_out                         true
% 3.00/0.99  --problem_path                          ""
% 3.00/0.99  --include_path                          ""
% 3.00/0.99  --clausifier                            res/vclausify_rel
% 3.00/0.99  --clausifier_options                    --mode clausify
% 3.00/0.99  --stdin                                 false
% 3.00/0.99  --stats_out                             all
% 3.00/0.99  
% 3.00/0.99  ------ General Options
% 3.00/0.99  
% 3.00/0.99  --fof                                   false
% 3.00/0.99  --time_out_real                         305.
% 3.00/0.99  --time_out_virtual                      -1.
% 3.00/0.99  --symbol_type_check                     false
% 3.00/0.99  --clausify_out                          false
% 3.00/0.99  --sig_cnt_out                           false
% 3.00/0.99  --trig_cnt_out                          false
% 3.00/0.99  --trig_cnt_out_tolerance                1.
% 3.00/0.99  --trig_cnt_out_sk_spl                   false
% 3.00/0.99  --abstr_cl_out                          false
% 3.00/0.99  
% 3.00/0.99  ------ Global Options
% 3.00/0.99  
% 3.00/0.99  --schedule                              default
% 3.00/0.99  --add_important_lit                     false
% 3.00/0.99  --prop_solver_per_cl                    1000
% 3.00/0.99  --min_unsat_core                        false
% 3.00/0.99  --soft_assumptions                      false
% 3.00/0.99  --soft_lemma_size                       3
% 3.00/0.99  --prop_impl_unit_size                   0
% 3.00/0.99  --prop_impl_unit                        []
% 3.00/0.99  --share_sel_clauses                     true
% 3.00/0.99  --reset_solvers                         false
% 3.00/0.99  --bc_imp_inh                            [conj_cone]
% 3.00/0.99  --conj_cone_tolerance                   3.
% 3.00/0.99  --extra_neg_conj                        none
% 3.00/0.99  --large_theory_mode                     true
% 3.00/0.99  --prolific_symb_bound                   200
% 3.00/0.99  --lt_threshold                          2000
% 3.00/0.99  --clause_weak_htbl                      true
% 3.00/0.99  --gc_record_bc_elim                     false
% 3.00/0.99  
% 3.00/0.99  ------ Preprocessing Options
% 3.00/0.99  
% 3.00/0.99  --preprocessing_flag                    true
% 3.00/0.99  --time_out_prep_mult                    0.1
% 3.00/0.99  --splitting_mode                        input
% 3.00/0.99  --splitting_grd                         true
% 3.00/0.99  --splitting_cvd                         false
% 3.00/0.99  --splitting_cvd_svl                     false
% 3.00/0.99  --splitting_nvd                         32
% 3.00/0.99  --sub_typing                            true
% 3.00/0.99  --prep_gs_sim                           true
% 3.00/0.99  --prep_unflatten                        true
% 3.00/0.99  --prep_res_sim                          true
% 3.00/0.99  --prep_upred                            true
% 3.00/0.99  --prep_sem_filter                       exhaustive
% 3.00/0.99  --prep_sem_filter_out                   false
% 3.00/0.99  --pred_elim                             true
% 3.00/0.99  --res_sim_input                         true
% 3.00/0.99  --eq_ax_congr_red                       true
% 3.00/0.99  --pure_diseq_elim                       true
% 3.00/0.99  --brand_transform                       false
% 3.00/0.99  --non_eq_to_eq                          false
% 3.00/0.99  --prep_def_merge                        true
% 3.00/0.99  --prep_def_merge_prop_impl              false
% 3.00/0.99  --prep_def_merge_mbd                    true
% 3.00/0.99  --prep_def_merge_tr_red                 false
% 3.00/0.99  --prep_def_merge_tr_cl                  false
% 3.00/0.99  --smt_preprocessing                     true
% 3.00/0.99  --smt_ac_axioms                         fast
% 3.00/0.99  --preprocessed_out                      false
% 3.00/0.99  --preprocessed_stats                    false
% 3.00/0.99  
% 3.00/0.99  ------ Abstraction refinement Options
% 3.00/0.99  
% 3.00/0.99  --abstr_ref                             []
% 3.00/0.99  --abstr_ref_prep                        false
% 3.00/0.99  --abstr_ref_until_sat                   false
% 3.00/0.99  --abstr_ref_sig_restrict                funpre
% 3.00/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.00/0.99  --abstr_ref_under                       []
% 3.00/0.99  
% 3.00/0.99  ------ SAT Options
% 3.00/0.99  
% 3.00/0.99  --sat_mode                              false
% 3.00/0.99  --sat_fm_restart_options                ""
% 3.00/0.99  --sat_gr_def                            false
% 3.00/0.99  --sat_epr_types                         true
% 3.00/0.99  --sat_non_cyclic_types                  false
% 3.00/0.99  --sat_finite_models                     false
% 3.00/0.99  --sat_fm_lemmas                         false
% 3.00/0.99  --sat_fm_prep                           false
% 3.00/0.99  --sat_fm_uc_incr                        true
% 3.00/0.99  --sat_out_model                         small
% 3.00/0.99  --sat_out_clauses                       false
% 3.00/0.99  
% 3.00/0.99  ------ QBF Options
% 3.00/0.99  
% 3.00/0.99  --qbf_mode                              false
% 3.00/0.99  --qbf_elim_univ                         false
% 3.00/0.99  --qbf_dom_inst                          none
% 3.00/0.99  --qbf_dom_pre_inst                      false
% 3.00/0.99  --qbf_sk_in                             false
% 3.00/0.99  --qbf_pred_elim                         true
% 3.00/0.99  --qbf_split                             512
% 3.00/0.99  
% 3.00/0.99  ------ BMC1 Options
% 3.00/0.99  
% 3.00/0.99  --bmc1_incremental                      false
% 3.00/0.99  --bmc1_axioms                           reachable_all
% 3.00/0.99  --bmc1_min_bound                        0
% 3.00/0.99  --bmc1_max_bound                        -1
% 3.00/0.99  --bmc1_max_bound_default                -1
% 3.00/0.99  --bmc1_symbol_reachability              true
% 3.00/0.99  --bmc1_property_lemmas                  false
% 3.00/0.99  --bmc1_k_induction                      false
% 3.00/0.99  --bmc1_non_equiv_states                 false
% 3.00/0.99  --bmc1_deadlock                         false
% 3.00/0.99  --bmc1_ucm                              false
% 3.00/0.99  --bmc1_add_unsat_core                   none
% 3.00/0.99  --bmc1_unsat_core_children              false
% 3.00/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.00/0.99  --bmc1_out_stat                         full
% 3.00/0.99  --bmc1_ground_init                      false
% 3.00/0.99  --bmc1_pre_inst_next_state              false
% 3.00/0.99  --bmc1_pre_inst_state                   false
% 3.00/0.99  --bmc1_pre_inst_reach_state             false
% 3.00/0.99  --bmc1_out_unsat_core                   false
% 3.00/0.99  --bmc1_aig_witness_out                  false
% 3.00/0.99  --bmc1_verbose                          false
% 3.00/0.99  --bmc1_dump_clauses_tptp                false
% 3.00/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.00/0.99  --bmc1_dump_file                        -
% 3.00/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.00/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.00/0.99  --bmc1_ucm_extend_mode                  1
% 3.00/0.99  --bmc1_ucm_init_mode                    2
% 3.00/0.99  --bmc1_ucm_cone_mode                    none
% 3.00/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.00/0.99  --bmc1_ucm_relax_model                  4
% 3.00/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.00/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.00/0.99  --bmc1_ucm_layered_model                none
% 3.00/0.99  --bmc1_ucm_max_lemma_size               10
% 3.00/0.99  
% 3.00/0.99  ------ AIG Options
% 3.00/0.99  
% 3.00/0.99  --aig_mode                              false
% 3.00/0.99  
% 3.00/0.99  ------ Instantiation Options
% 3.00/0.99  
% 3.00/0.99  --instantiation_flag                    true
% 3.00/0.99  --inst_sos_flag                         false
% 3.00/0.99  --inst_sos_phase                        true
% 3.00/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.00/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.00/0.99  --inst_lit_sel_side                     none
% 3.00/0.99  --inst_solver_per_active                1400
% 3.00/0.99  --inst_solver_calls_frac                1.
% 3.00/0.99  --inst_passive_queue_type               priority_queues
% 3.00/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.00/0.99  --inst_passive_queues_freq              [25;2]
% 3.00/0.99  --inst_dismatching                      true
% 3.00/0.99  --inst_eager_unprocessed_to_passive     true
% 3.00/0.99  --inst_prop_sim_given                   true
% 3.00/0.99  --inst_prop_sim_new                     false
% 3.00/0.99  --inst_subs_new                         false
% 3.00/0.99  --inst_eq_res_simp                      false
% 3.00/0.99  --inst_subs_given                       false
% 3.00/0.99  --inst_orphan_elimination               true
% 3.00/0.99  --inst_learning_loop_flag               true
% 3.00/0.99  --inst_learning_start                   3000
% 3.00/0.99  --inst_learning_factor                  2
% 3.00/0.99  --inst_start_prop_sim_after_learn       3
% 3.00/0.99  --inst_sel_renew                        solver
% 3.00/0.99  --inst_lit_activity_flag                true
% 3.00/0.99  --inst_restr_to_given                   false
% 3.00/0.99  --inst_activity_threshold               500
% 3.00/0.99  --inst_out_proof                        true
% 3.00/0.99  
% 3.00/0.99  ------ Resolution Options
% 3.00/0.99  
% 3.00/0.99  --resolution_flag                       false
% 3.00/0.99  --res_lit_sel                           adaptive
% 3.00/0.99  --res_lit_sel_side                      none
% 3.00/0.99  --res_ordering                          kbo
% 3.00/0.99  --res_to_prop_solver                    active
% 3.00/0.99  --res_prop_simpl_new                    false
% 3.00/0.99  --res_prop_simpl_given                  true
% 3.00/0.99  --res_passive_queue_type                priority_queues
% 3.00/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.00/0.99  --res_passive_queues_freq               [15;5]
% 3.00/0.99  --res_forward_subs                      full
% 3.00/0.99  --res_backward_subs                     full
% 3.00/0.99  --res_forward_subs_resolution           true
% 3.00/0.99  --res_backward_subs_resolution          true
% 3.00/0.99  --res_orphan_elimination                true
% 3.00/0.99  --res_time_limit                        2.
% 3.00/0.99  --res_out_proof                         true
% 3.00/0.99  
% 3.00/0.99  ------ Superposition Options
% 3.00/0.99  
% 3.00/0.99  --superposition_flag                    true
% 3.00/0.99  --sup_passive_queue_type                priority_queues
% 3.00/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.00/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.00/0.99  --demod_completeness_check              fast
% 3.00/0.99  --demod_use_ground                      true
% 3.00/0.99  --sup_to_prop_solver                    passive
% 3.00/0.99  --sup_prop_simpl_new                    true
% 3.00/0.99  --sup_prop_simpl_given                  true
% 3.00/0.99  --sup_fun_splitting                     false
% 3.00/0.99  --sup_smt_interval                      50000
% 3.00/0.99  
% 3.00/0.99  ------ Superposition Simplification Setup
% 3.00/0.99  
% 3.00/0.99  --sup_indices_passive                   []
% 3.00/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.00/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/0.99  --sup_full_bw                           [BwDemod]
% 3.00/0.99  --sup_immed_triv                        [TrivRules]
% 3.00/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.00/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/0.99  --sup_immed_bw_main                     []
% 3.00/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.00/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/0.99  
% 3.00/0.99  ------ Combination Options
% 3.00/0.99  
% 3.00/0.99  --comb_res_mult                         3
% 3.00/0.99  --comb_sup_mult                         2
% 3.00/0.99  --comb_inst_mult                        10
% 3.00/0.99  
% 3.00/0.99  ------ Debug Options
% 3.00/0.99  
% 3.00/0.99  --dbg_backtrace                         false
% 3.00/0.99  --dbg_dump_prop_clauses                 false
% 3.00/0.99  --dbg_dump_prop_clauses_file            -
% 3.00/0.99  --dbg_out_stat                          false
% 3.00/0.99  
% 3.00/0.99  
% 3.00/0.99  
% 3.00/0.99  
% 3.00/0.99  ------ Proving...
% 3.00/0.99  
% 3.00/0.99  
% 3.00/0.99  % SZS status Theorem for theBenchmark.p
% 3.00/0.99  
% 3.00/0.99   Resolution empty clause
% 3.00/0.99  
% 3.00/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.00/0.99  
% 3.00/0.99  fof(f4,axiom,(
% 3.00/0.99    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.00/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/0.99  
% 3.00/0.99  fof(f34,plain,(
% 3.00/0.99    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.00/0.99    inference(cnf_transformation,[],[f4])).
% 3.00/0.99  
% 3.00/0.99  fof(f6,axiom,(
% 3.00/0.99    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 3.00/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/0.99  
% 3.00/0.99  fof(f18,plain,(
% 3.00/0.99    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 3.00/0.99    inference(nnf_transformation,[],[f6])).
% 3.00/0.99  
% 3.00/0.99  fof(f37,plain,(
% 3.00/0.99    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 3.00/0.99    inference(cnf_transformation,[],[f18])).
% 3.00/0.99  
% 3.00/0.99  fof(f1,axiom,(
% 3.00/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.00/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/0.99  
% 3.00/0.99  fof(f10,plain,(
% 3.00/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.00/0.99    inference(rectify,[],[f1])).
% 3.00/0.99  
% 3.00/0.99  fof(f11,plain,(
% 3.00/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 3.00/0.99    inference(ennf_transformation,[],[f10])).
% 3.00/0.99  
% 3.00/0.99  fof(f14,plain,(
% 3.00/0.99    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.00/0.99    introduced(choice_axiom,[])).
% 3.00/0.99  
% 3.00/0.99  fof(f15,plain,(
% 3.00/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 3.00/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f14])).
% 3.00/0.99  
% 3.00/0.99  fof(f30,plain,(
% 3.00/0.99    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 3.00/0.99    inference(cnf_transformation,[],[f15])).
% 3.00/0.99  
% 3.00/0.99  fof(f29,plain,(
% 3.00/0.99    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 3.00/0.99    inference(cnf_transformation,[],[f15])).
% 3.00/0.99  
% 3.00/0.99  fof(f31,plain,(
% 3.00/0.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 3.00/0.99    inference(cnf_transformation,[],[f15])).
% 3.00/0.99  
% 3.00/0.99  fof(f2,axiom,(
% 3.00/0.99    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 3.00/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/0.99  
% 3.00/0.99  fof(f12,plain,(
% 3.00/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 3.00/0.99    inference(ennf_transformation,[],[f2])).
% 3.00/0.99  
% 3.00/0.99  fof(f16,plain,(
% 3.00/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 3.00/0.99    introduced(choice_axiom,[])).
% 3.00/0.99  
% 3.00/0.99  fof(f17,plain,(
% 3.00/0.99    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 3.00/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f12,f16])).
% 3.00/0.99  
% 3.00/0.99  fof(f32,plain,(
% 3.00/0.99    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 3.00/0.99    inference(cnf_transformation,[],[f17])).
% 3.00/0.99  
% 3.00/0.99  fof(f7,axiom,(
% 3.00/0.99    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 3.00/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/0.99  
% 3.00/0.99  fof(f19,plain,(
% 3.00/0.99    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 3.00/0.99    inference(nnf_transformation,[],[f7])).
% 3.00/0.99  
% 3.00/0.99  fof(f20,plain,(
% 3.00/0.99    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 3.00/0.99    inference(rectify,[],[f19])).
% 3.00/0.99  
% 3.00/0.99  fof(f23,plain,(
% 3.00/0.99    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) => (k4_tarski(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8 & r2_hidden(sK6(X0,X1,X8),X1) & r2_hidden(sK5(X0,X1,X8),X0)))),
% 3.00/0.99    introduced(choice_axiom,[])).
% 3.00/0.99  
% 3.00/0.99  fof(f22,plain,(
% 3.00/0.99    ( ! [X3] : (! [X2,X1,X0] : (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) => (k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)) = X3 & r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)))) )),
% 3.00/0.99    introduced(choice_axiom,[])).
% 3.00/0.99  
% 3.00/0.99  fof(f21,plain,(
% 3.00/0.99    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK2(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK2(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 3.00/0.99    introduced(choice_axiom,[])).
% 3.00/0.99  
% 3.00/0.99  fof(f24,plain,(
% 3.00/0.99    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ((! [X4,X5] : (k4_tarski(X4,X5) != sK2(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)) = sK2(X0,X1,X2) & r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & ((k4_tarski(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8 & r2_hidden(sK6(X0,X1,X8),X1) & r2_hidden(sK5(X0,X1,X8),X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 3.00/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f20,f23,f22,f21])).
% 3.00/0.99  
% 3.00/0.99  fof(f38,plain,(
% 3.00/0.99    ( ! [X2,X0,X8,X1] : (r2_hidden(sK5(X0,X1,X8),X0) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 3.00/0.99    inference(cnf_transformation,[],[f24])).
% 3.00/0.99  
% 3.00/0.99  fof(f54,plain,(
% 3.00/0.99    ( ! [X0,X8,X1] : (r2_hidden(sK5(X0,X1,X8),X0) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 3.00/0.99    inference(equality_resolution,[],[f38])).
% 3.00/0.99  
% 3.00/0.99  fof(f39,plain,(
% 3.00/0.99    ( ! [X2,X0,X8,X1] : (r2_hidden(sK6(X0,X1,X8),X1) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 3.00/0.99    inference(cnf_transformation,[],[f24])).
% 3.00/0.99  
% 3.00/0.99  fof(f53,plain,(
% 3.00/0.99    ( ! [X0,X8,X1] : (r2_hidden(sK6(X0,X1,X8),X1) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 3.00/0.99    inference(equality_resolution,[],[f39])).
% 3.00/0.99  
% 3.00/0.99  fof(f8,conjecture,(
% 3.00/0.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.00/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/0.99  
% 3.00/0.99  fof(f9,negated_conjecture,(
% 3.00/0.99    ~! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.00/0.99    inference(negated_conjecture,[],[f8])).
% 3.00/0.99  
% 3.00/0.99  fof(f13,plain,(
% 3.00/0.99    ? [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <~> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.00/0.99    inference(ennf_transformation,[],[f9])).
% 3.00/0.99  
% 3.00/0.99  fof(f25,plain,(
% 3.00/0.99    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 3.00/0.99    inference(nnf_transformation,[],[f13])).
% 3.00/0.99  
% 3.00/0.99  fof(f26,plain,(
% 3.00/0.99    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 3.00/0.99    inference(flattening,[],[f25])).
% 3.00/0.99  
% 3.00/0.99  fof(f27,plain,(
% 3.00/0.99    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1))) => (((k1_xboole_0 != sK8 & k1_xboole_0 != sK7) | k1_xboole_0 != k2_zfmisc_1(sK7,sK8)) & (k1_xboole_0 = sK8 | k1_xboole_0 = sK7 | k1_xboole_0 = k2_zfmisc_1(sK7,sK8)))),
% 3.00/0.99    introduced(choice_axiom,[])).
% 3.00/0.99  
% 3.00/0.99  fof(f28,plain,(
% 3.00/0.99    ((k1_xboole_0 != sK8 & k1_xboole_0 != sK7) | k1_xboole_0 != k2_zfmisc_1(sK7,sK8)) & (k1_xboole_0 = sK8 | k1_xboole_0 = sK7 | k1_xboole_0 = k2_zfmisc_1(sK7,sK8))),
% 3.00/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f26,f27])).
% 3.00/0.99  
% 3.00/0.99  fof(f46,plain,(
% 3.00/0.99    k1_xboole_0 = sK8 | k1_xboole_0 = sK7 | k1_xboole_0 = k2_zfmisc_1(sK7,sK8)),
% 3.00/0.99    inference(cnf_transformation,[],[f28])).
% 3.00/0.99  
% 3.00/0.99  fof(f41,plain,(
% 3.00/0.99    ( ! [X2,X0,X10,X8,X1,X9] : (r2_hidden(X8,X2) | k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0) | k2_zfmisc_1(X0,X1) != X2) )),
% 3.00/0.99    inference(cnf_transformation,[],[f24])).
% 3.00/0.99  
% 3.00/0.99  fof(f50,plain,(
% 3.00/0.99    ( ! [X2,X0,X10,X1,X9] : (r2_hidden(k4_tarski(X9,X10),X2) | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0) | k2_zfmisc_1(X0,X1) != X2) )),
% 3.00/0.99    inference(equality_resolution,[],[f41])).
% 3.00/0.99  
% 3.00/0.99  fof(f51,plain,(
% 3.00/0.99    ( ! [X0,X10,X1,X9] : (r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1)) | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0)) )),
% 3.00/0.99    inference(equality_resolution,[],[f50])).
% 3.00/0.99  
% 3.00/0.99  fof(f47,plain,(
% 3.00/0.99    k1_xboole_0 != sK7 | k1_xboole_0 != k2_zfmisc_1(sK7,sK8)),
% 3.00/0.99    inference(cnf_transformation,[],[f28])).
% 3.00/0.99  
% 3.00/0.99  fof(f48,plain,(
% 3.00/0.99    k1_xboole_0 != sK8 | k1_xboole_0 != k2_zfmisc_1(sK7,sK8)),
% 3.00/0.99    inference(cnf_transformation,[],[f28])).
% 3.00/0.99  
% 3.00/0.99  cnf(c_5,plain,
% 3.00/0.99      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.00/0.99      inference(cnf_transformation,[],[f34]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_6,plain,
% 3.00/0.99      ( r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0 ),
% 3.00/0.99      inference(cnf_transformation,[],[f37]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_636,plain,
% 3.00/0.99      ( k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1) = iProver_top ),
% 3.00/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_969,plain,
% 3.00/0.99      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_5,c_636]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1,plain,
% 3.00/0.99      ( r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1) ),
% 3.00/0.99      inference(cnf_transformation,[],[f30]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_639,plain,
% 3.00/0.99      ( r2_hidden(sK0(X0,X1),X1) = iProver_top
% 3.00/0.99      | r1_xboole_0(X0,X1) = iProver_top ),
% 3.00/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_2,plain,
% 3.00/0.99      ( r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1) ),
% 3.00/0.99      inference(cnf_transformation,[],[f29]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_638,plain,
% 3.00/0.99      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 3.00/0.99      | r1_xboole_0(X0,X1) = iProver_top ),
% 3.00/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_0,plain,
% 3.00/0.99      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 3.00/0.99      inference(cnf_transformation,[],[f31]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_640,plain,
% 3.00/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.00/0.99      | r2_hidden(X0,X2) != iProver_top
% 3.00/0.99      | r1_xboole_0(X2,X1) != iProver_top ),
% 3.00/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_2217,plain,
% 3.00/0.99      ( r2_hidden(sK0(X0,X1),X2) != iProver_top
% 3.00/0.99      | r1_xboole_0(X2,X0) != iProver_top
% 3.00/0.99      | r1_xboole_0(X0,X1) = iProver_top ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_638,c_640]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_4688,plain,
% 3.00/0.99      ( r1_xboole_0(X0,X1) != iProver_top | r1_xboole_0(X1,X0) = iProver_top ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_639,c_2217]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_4738,plain,
% 3.00/0.99      ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_969,c_4688]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_3,plain,
% 3.00/0.99      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 3.00/0.99      inference(cnf_transformation,[],[f32]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_637,plain,
% 3.00/0.99      ( k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 3.00/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_15,plain,
% 3.00/0.99      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(sK5(X1,X2,X0),X1) ),
% 3.00/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_627,plain,
% 3.00/0.99      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.00/0.99      | r2_hidden(sK5(X1,X2,X0),X1) = iProver_top ),
% 3.00/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_14,plain,
% 3.00/0.99      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(sK6(X1,X2,X0),X2) ),
% 3.00/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_628,plain,
% 3.00/0.99      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.00/0.99      | r2_hidden(sK6(X1,X2,X0),X2) = iProver_top ),
% 3.00/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_2220,plain,
% 3.00/0.99      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.00/0.99      | r2_hidden(sK6(X1,X2,X0),X3) != iProver_top
% 3.00/0.99      | r1_xboole_0(X3,X2) != iProver_top ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_628,c_640]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_5038,plain,
% 3.00/0.99      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.00/0.99      | r1_xboole_0(X2,X2) != iProver_top ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_628,c_2220]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_5069,plain,
% 3.00/0.99      ( r2_hidden(X0,k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3))) != iProver_top
% 3.00/0.99      | r1_xboole_0(X3,X3) != iProver_top ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_628,c_5038]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_5367,plain,
% 3.00/0.99      ( r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3)),X4)) != iProver_top
% 3.00/0.99      | r1_xboole_0(X3,X3) != iProver_top ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_627,c_5069]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_6370,plain,
% 3.00/0.99      ( k2_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2)),X3) = k1_xboole_0
% 3.00/0.99      | r1_xboole_0(X2,X2) != iProver_top ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_637,c_5367]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_6474,plain,
% 3.00/0.99      ( k2_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,k1_xboole_0)),X2) = k1_xboole_0 ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_4738,c_6370]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_5062,plain,
% 3.00/0.99      ( k2_zfmisc_1(X0,X1) = k1_xboole_0 | r1_xboole_0(X1,X1) != iProver_top ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_637,c_5038]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_5169,plain,
% 3.00/0.99      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_4738,c_5062]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_6477,plain,
% 3.00/0.99      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.00/0.99      inference(demodulation,[status(thm)],[c_6474,c_5169]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_18,negated_conjecture,
% 3.00/0.99      ( k1_xboole_0 = k2_zfmisc_1(sK7,sK8)
% 3.00/0.99      | k1_xboole_0 = sK7
% 3.00/0.99      | k1_xboole_0 = sK8 ),
% 3.00/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_12,plain,
% 3.00/0.99      ( ~ r2_hidden(X0,X1)
% 3.00/0.99      | ~ r2_hidden(X2,X3)
% 3.00/0.99      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 3.00/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_630,plain,
% 3.00/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.00/0.99      | r2_hidden(X2,X3) != iProver_top
% 3.00/0.99      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
% 3.00/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_2129,plain,
% 3.00/0.99      ( sK7 = k1_xboole_0
% 3.00/0.99      | sK8 = k1_xboole_0
% 3.00/0.99      | r2_hidden(X0,sK7) != iProver_top
% 3.00/0.99      | r2_hidden(X1,sK8) != iProver_top
% 3.00/0.99      | r2_hidden(k4_tarski(X0,X1),k1_xboole_0) = iProver_top ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_18,c_630]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_2733,plain,
% 3.00/0.99      ( sK7 = k1_xboole_0
% 3.00/0.99      | sK8 = k1_xboole_0
% 3.00/0.99      | r2_hidden(X0,sK7) != iProver_top
% 3.00/0.99      | r2_hidden(X1,sK8) != iProver_top
% 3.00/0.99      | r2_hidden(k4_tarski(X0,X1),X2) != iProver_top
% 3.00/0.99      | r1_xboole_0(X2,k1_xboole_0) != iProver_top ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_2129,c_640]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_2798,plain,
% 3.00/0.99      ( sK7 = k1_xboole_0
% 3.00/0.99      | sK8 = k1_xboole_0
% 3.00/0.99      | r2_hidden(X0,sK7) != iProver_top
% 3.00/0.99      | r2_hidden(X1,sK8) != iProver_top
% 3.00/0.99      | r2_hidden(k4_tarski(X0,X1),X2) != iProver_top ),
% 3.00/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_2733,c_969]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_2803,plain,
% 3.00/0.99      ( sK7 = k1_xboole_0
% 3.00/0.99      | sK8 = k1_xboole_0
% 3.00/0.99      | r2_hidden(X0,sK7) != iProver_top
% 3.00/0.99      | r2_hidden(X1,sK8) != iProver_top ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_2129,c_2798]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_2898,plain,
% 3.00/0.99      ( sK7 = k1_xboole_0
% 3.00/0.99      | sK8 = k1_xboole_0
% 3.00/0.99      | r2_hidden(X0,sK8) != iProver_top ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_637,c_2803]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_4008,plain,
% 3.00/0.99      ( sK7 = k1_xboole_0 | sK8 = k1_xboole_0 ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_637,c_2898]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_17,negated_conjecture,
% 3.00/0.99      ( k1_xboole_0 != k2_zfmisc_1(sK7,sK8) | k1_xboole_0 != sK7 ),
% 3.00/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_4115,plain,
% 3.00/0.99      ( k2_zfmisc_1(k1_xboole_0,sK8) != k1_xboole_0
% 3.00/0.99      | sK7 != k1_xboole_0
% 3.00/0.99      | sK8 = k1_xboole_0 ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_4008,c_17]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_4120,plain,
% 3.00/0.99      ( k2_zfmisc_1(k1_xboole_0,sK8) != k1_xboole_0 | sK8 = k1_xboole_0 ),
% 3.00/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_4115,c_4008]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_6485,plain,
% 3.00/0.99      ( sK8 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 3.00/0.99      inference(demodulation,[status(thm)],[c_6477,c_4120]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_6488,plain,
% 3.00/0.99      ( sK8 = k1_xboole_0 ),
% 3.00/0.99      inference(equality_resolution_simp,[status(thm)],[c_6485]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_16,negated_conjecture,
% 3.00/0.99      ( k1_xboole_0 != k2_zfmisc_1(sK7,sK8) | k1_xboole_0 != sK8 ),
% 3.00/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_6572,plain,
% 3.00/0.99      ( k2_zfmisc_1(sK7,k1_xboole_0) != k1_xboole_0
% 3.00/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.00/0.99      inference(demodulation,[status(thm)],[c_6488,c_16]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_6573,plain,
% 3.00/0.99      ( k2_zfmisc_1(sK7,k1_xboole_0) != k1_xboole_0 ),
% 3.00/0.99      inference(equality_resolution_simp,[status(thm)],[c_6572]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_6575,plain,
% 3.00/0.99      ( k1_xboole_0 != k1_xboole_0 ),
% 3.00/0.99      inference(demodulation,[status(thm)],[c_6573,c_5169]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_6576,plain,
% 3.00/0.99      ( $false ),
% 3.00/0.99      inference(equality_resolution_simp,[status(thm)],[c_6575]) ).
% 3.00/0.99  
% 3.00/0.99  
% 3.00/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.00/0.99  
% 3.00/0.99  ------                               Statistics
% 3.00/0.99  
% 3.00/0.99  ------ General
% 3.00/0.99  
% 3.00/0.99  abstr_ref_over_cycles:                  0
% 3.00/0.99  abstr_ref_under_cycles:                 0
% 3.00/0.99  gc_basic_clause_elim:                   0
% 3.00/0.99  forced_gc_time:                         0
% 3.00/0.99  parsing_time:                           0.008
% 3.00/0.99  unif_index_cands_time:                  0.
% 3.00/0.99  unif_index_add_time:                    0.
% 3.00/0.99  orderings_time:                         0.
% 3.00/0.99  out_proof_time:                         0.006
% 3.00/0.99  total_time:                             0.19
% 3.00/0.99  num_of_symbols:                         46
% 3.00/0.99  num_of_terms:                           7954
% 3.00/0.99  
% 3.00/0.99  ------ Preprocessing
% 3.00/0.99  
% 3.00/0.99  num_of_splits:                          0
% 3.00/0.99  num_of_split_atoms:                     0
% 3.00/0.99  num_of_reused_defs:                     0
% 3.00/0.99  num_eq_ax_congr_red:                    42
% 3.00/0.99  num_of_sem_filtered_clauses:            1
% 3.00/0.99  num_of_subtypes:                        0
% 3.00/0.99  monotx_restored_types:                  0
% 3.00/0.99  sat_num_of_epr_types:                   0
% 3.00/0.99  sat_num_of_non_cyclic_types:            0
% 3.00/0.99  sat_guarded_non_collapsed_types:        0
% 3.00/0.99  num_pure_diseq_elim:                    0
% 3.00/0.99  simp_replaced_by:                       0
% 3.00/0.99  res_preprocessed:                       70
% 3.00/0.99  prep_upred:                             0
% 3.00/0.99  prep_unflattend:                        6
% 3.00/0.99  smt_new_axioms:                         0
% 3.00/0.99  pred_elim_cands:                        2
% 3.00/0.99  pred_elim:                              0
% 3.00/0.99  pred_elim_cl:                           0
% 3.00/0.99  pred_elim_cycles:                       1
% 3.00/0.99  merged_defs:                            6
% 3.00/0.99  merged_defs_ncl:                        0
% 3.00/0.99  bin_hyper_res:                          6
% 3.00/0.99  prep_cycles:                            3
% 3.00/0.99  pred_elim_time:                         0.001
% 3.00/0.99  splitting_time:                         0.
% 3.00/0.99  sem_filter_time:                        0.
% 3.00/0.99  monotx_time:                            0.001
% 3.00/0.99  subtype_inf_time:                       0.
% 3.00/0.99  
% 3.00/0.99  ------ Problem properties
% 3.00/0.99  
% 3.00/0.99  clauses:                                19
% 3.00/0.99  conjectures:                            3
% 3.00/0.99  epr:                                    1
% 3.00/0.99  horn:                                   12
% 3.00/0.99  ground:                                 3
% 3.00/0.99  unary:                                  2
% 3.00/0.99  binary:                                 10
% 3.00/0.99  lits:                                   45
% 3.00/0.99  lits_eq:                                19
% 3.00/0.99  fd_pure:                                0
% 3.00/0.99  fd_pseudo:                              0
% 3.00/0.99  fd_cond:                                1
% 3.00/0.99  fd_pseudo_cond:                         4
% 3.00/0.99  ac_symbols:                             0
% 3.00/0.99  
% 3.00/0.99  ------ Propositional Solver
% 3.00/0.99  
% 3.00/0.99  prop_solver_calls:                      23
% 3.00/0.99  prop_fast_solver_calls:                 903
% 3.00/0.99  smt_solver_calls:                       0
% 3.00/0.99  smt_fast_solver_calls:                  0
% 3.00/0.99  prop_num_of_clauses:                    2394
% 3.00/0.99  prop_preprocess_simplified:             5449
% 3.00/0.99  prop_fo_subsumed:                       151
% 3.00/0.99  prop_solver_time:                       0.
% 3.00/0.99  smt_solver_time:                        0.
% 3.00/0.99  smt_fast_solver_time:                   0.
% 3.00/0.99  prop_fast_solver_time:                  0.
% 3.00/0.99  prop_unsat_core_time:                   0.
% 3.00/0.99  
% 3.00/0.99  ------ QBF
% 3.00/0.99  
% 3.00/0.99  qbf_q_res:                              0
% 3.00/0.99  qbf_num_tautologies:                    0
% 3.00/0.99  qbf_prep_cycles:                        0
% 3.00/0.99  
% 3.00/0.99  ------ BMC1
% 3.00/0.99  
% 3.00/0.99  bmc1_current_bound:                     -1
% 3.00/0.99  bmc1_last_solved_bound:                 -1
% 3.00/0.99  bmc1_unsat_core_size:                   -1
% 3.00/0.99  bmc1_unsat_core_parents_size:           -1
% 3.00/0.99  bmc1_merge_next_fun:                    0
% 3.00/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.00/0.99  
% 3.00/0.99  ------ Instantiation
% 3.00/0.99  
% 3.00/0.99  inst_num_of_clauses:                    588
% 3.00/0.99  inst_num_in_passive:                    142
% 3.00/0.99  inst_num_in_active:                     323
% 3.00/0.99  inst_num_in_unprocessed:                123
% 3.00/0.99  inst_num_of_loops:                      380
% 3.00/0.99  inst_num_of_learning_restarts:          0
% 3.00/0.99  inst_num_moves_active_passive:          54
% 3.00/0.99  inst_lit_activity:                      0
% 3.00/0.99  inst_lit_activity_moves:                0
% 3.00/0.99  inst_num_tautologies:                   0
% 3.00/0.99  inst_num_prop_implied:                  0
% 3.00/0.99  inst_num_existing_simplified:           0
% 3.00/0.99  inst_num_eq_res_simplified:             0
% 3.00/0.99  inst_num_child_elim:                    0
% 3.00/0.99  inst_num_of_dismatching_blockings:      148
% 3.00/0.99  inst_num_of_non_proper_insts:           293
% 3.00/0.99  inst_num_of_duplicates:                 0
% 3.00/0.99  inst_inst_num_from_inst_to_res:         0
% 3.00/0.99  inst_dismatching_checking_time:         0.
% 3.00/0.99  
% 3.00/0.99  ------ Resolution
% 3.00/0.99  
% 3.00/0.99  res_num_of_clauses:                     0
% 3.00/0.99  res_num_in_passive:                     0
% 3.00/0.99  res_num_in_active:                      0
% 3.00/0.99  res_num_of_loops:                       73
% 3.00/0.99  res_forward_subset_subsumed:            2
% 3.00/0.99  res_backward_subset_subsumed:           0
% 3.00/0.99  res_forward_subsumed:                   0
% 3.00/0.99  res_backward_subsumed:                  0
% 3.00/0.99  res_forward_subsumption_resolution:     0
% 3.00/0.99  res_backward_subsumption_resolution:    0
% 3.00/0.99  res_clause_to_clause_subsumption:       748
% 3.00/0.99  res_orphan_elimination:                 0
% 3.00/0.99  res_tautology_del:                      41
% 3.00/0.99  res_num_eq_res_simplified:              0
% 3.00/0.99  res_num_sel_changes:                    0
% 3.00/0.99  res_moves_from_active_to_pass:          0
% 3.00/0.99  
% 3.00/0.99  ------ Superposition
% 3.00/0.99  
% 3.00/0.99  sup_time_total:                         0.
% 3.00/0.99  sup_time_generating:                    0.
% 3.00/0.99  sup_time_sim_full:                      0.
% 3.00/0.99  sup_time_sim_immed:                     0.
% 3.00/0.99  
% 3.00/0.99  sup_num_of_clauses:                     175
% 3.00/0.99  sup_num_in_active:                      56
% 3.00/0.99  sup_num_in_passive:                     119
% 3.00/0.99  sup_num_of_loops:                       74
% 3.00/0.99  sup_fw_superposition:                   283
% 3.00/0.99  sup_bw_superposition:                   105
% 3.00/0.99  sup_immediate_simplified:               114
% 3.00/0.99  sup_given_eliminated:                   1
% 3.00/0.99  comparisons_done:                       0
% 3.00/0.99  comparisons_avoided:                    93
% 3.00/0.99  
% 3.00/0.99  ------ Simplifications
% 3.00/0.99  
% 3.00/0.99  
% 3.00/0.99  sim_fw_subset_subsumed:                 72
% 3.00/0.99  sim_bw_subset_subsumed:                 11
% 3.00/0.99  sim_fw_subsumed:                        10
% 3.00/0.99  sim_bw_subsumed:                        20
% 3.00/0.99  sim_fw_subsumption_res:                 2
% 3.00/0.99  sim_bw_subsumption_res:                 0
% 3.00/0.99  sim_tautology_del:                      4
% 3.00/0.99  sim_eq_tautology_del:                   7
% 3.00/0.99  sim_eq_res_simp:                        2
% 3.00/0.99  sim_fw_demodulated:                     17
% 3.00/0.99  sim_bw_demodulated:                     14
% 3.00/0.99  sim_light_normalised:                   10
% 3.00/0.99  sim_joinable_taut:                      0
% 3.00/0.99  sim_joinable_simp:                      0
% 3.00/0.99  sim_ac_normalised:                      0
% 3.00/0.99  sim_smt_subsumption:                    0
% 3.00/0.99  
%------------------------------------------------------------------------------
