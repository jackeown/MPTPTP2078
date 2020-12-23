%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:31:53 EST 2020

% Result     : Theorem 15.59s
% Output     : CNFRefutation 15.59s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 348 expanded)
%              Number of clauses        :   41 (  86 expanded)
%              Number of leaves         :   11 (  91 expanded)
%              Depth                    :   16
%              Number of atoms          :  302 (1341 expanded)
%              Number of equality atoms :  170 ( 782 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f8])).

fof(f10,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK0(X0,X1) != X0
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( sK0(X0,X1) = X0
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK0(X0,X1) != X0
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( sK0(X0,X1) = X0
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f10])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK0(X0,X1) = X0
      | r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f2,axiom,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X0,X0,X0,X0) = X1
      | sK0(X0,X1) = X0
      | r2_hidden(sK0(X0,X1),X1) ) ),
    inference(definition_unfolding,[],[f24,f26])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f13,plain,(
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
    inference(rectify,[],[f12])).

fof(f16,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK4(X0,X1,X8),sK5(X0,X1,X8)) = X8
        & r2_hidden(sK5(X0,X1,X8),X1)
        & r2_hidden(sK4(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X6,X7] :
          ( k4_tarski(X6,X7) = X3
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)) = X3
        & r2_hidden(sK3(X0,X1,X2),X1)
        & r2_hidden(sK2(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
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
              ( k4_tarski(X4,X5) != sK1(X0,X1,X2)
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X0) )
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ? [X7,X6] :
              ( k4_tarski(X6,X7) = sK1(X0,X1,X2)
              & r2_hidden(X7,X1)
              & r2_hidden(X6,X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != sK1(X0,X1,X2)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)) = sK1(X0,X1,X2)
              & r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ( k4_tarski(sK4(X0,X1,X8),sK5(X0,X1,X8)) = X8
                & r2_hidden(sK5(X0,X1,X8),X1)
                & r2_hidden(sK4(X0,X1,X8),X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f13,f16,f15,f14])).

fof(f28,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK5(X0,X1,X8),X1)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f53,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK5(X0,X1,X8),X1)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f28])).

fof(f22,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f22,f26])).

fof(f49,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f42])).

fof(f5,conjecture,(
    ! [X0,X1] : k1_tarski(k4_tarski(X0,X1)) = k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] : k1_tarski(k4_tarski(X0,X1)) = k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) ),
    inference(negated_conjecture,[],[f5])).

fof(f7,plain,(
    ? [X0,X1] : k1_tarski(k4_tarski(X0,X1)) != k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) ),
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,
    ( ? [X0,X1] : k1_tarski(k4_tarski(X0,X1)) != k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1))
   => k1_tarski(k4_tarski(sK6,sK7)) != k2_zfmisc_1(k1_tarski(sK6),k1_tarski(sK7)) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    k1_tarski(k4_tarski(sK6,sK7)) != k2_zfmisc_1(k1_tarski(sK6),k1_tarski(sK7)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f7,f20])).

fof(f38,plain,(
    k1_tarski(k4_tarski(sK6,sK7)) != k2_zfmisc_1(k1_tarski(sK6),k1_tarski(sK7)) ),
    inference(cnf_transformation,[],[f21])).

fof(f46,plain,(
    k2_enumset1(k4_tarski(sK6,sK7),k4_tarski(sK6,sK7),k4_tarski(sK6,sK7),k4_tarski(sK6,sK7)) != k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7)) ),
    inference(definition_unfolding,[],[f38,f26,f26,f26])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK0(X0,X1) != X0
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X0,X0,X0,X0) = X1
      | sK0(X0,X1) != X0
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(definition_unfolding,[],[f25,f26])).

fof(f23,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f23,f26])).

fof(f47,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_enumset1(X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f41])).

fof(f48,plain,(
    ! [X3] : r2_hidden(X3,k2_enumset1(X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f47])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
    <=> ( X1 = X3
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
        | X1 != X3
        | X0 != X2 )
      & ( ( X1 = X3
          & X0 = X2 )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
        | X1 != X3
        | X0 != X2 )
      & ( ( X1 = X3
          & X0 = X2 )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) ) ) ),
    inference(flattening,[],[f18])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
      | X1 != X3
      | X0 != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),k2_enumset1(X3,X3,X3,X3)))
      | X1 != X3
      | X0 != X2 ) ),
    inference(definition_unfolding,[],[f37,f26,f26])).

fof(f55,plain,(
    ! [X2,X0,X3] :
      ( r2_hidden(k4_tarski(X0,X3),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),k2_enumset1(X3,X3,X3,X3)))
      | X0 != X2 ) ),
    inference(equality_resolution,[],[f43])).

fof(f56,plain,(
    ! [X2,X3] : r2_hidden(k4_tarski(X2,X3),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),k2_enumset1(X3,X3,X3,X3))) ),
    inference(equality_resolution,[],[f55])).

fof(f29,plain,(
    ! [X2,X0,X8,X1] :
      ( k4_tarski(sK4(X0,X1,X8),sK5(X0,X1,X8)) = X8
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f52,plain,(
    ! [X0,X8,X1] :
      ( k4_tarski(sK4(X0,X1,X8),sK5(X0,X1,X8)) = X8
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f29])).

fof(f27,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK4(X0,X1,X8),X0)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f54,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK4(X0,X1,X8),X0)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f27])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | k2_enumset1(X0,X0,X0,X0) = X1
    | sK0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_422,plain,
    ( k2_enumset1(X0,X0,X0,X0) = X1
    | sK0(X0,X1) = X0
    | r2_hidden(sK0(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(sK5(X1,X2,X0),X2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_413,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(sK5(X1,X2,X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_420,plain,
    ( X0 = X1
    | r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_862,plain,
    ( sK5(X0,k2_enumset1(X1,X1,X1,X1),X2) = X1
    | r2_hidden(X2,k2_zfmisc_1(X0,k2_enumset1(X1,X1,X1,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_413,c_420])).

cnf(c_1738,plain,
    ( sK5(X0,k2_enumset1(X1,X1,X1,X1),sK0(X2,k2_zfmisc_1(X0,k2_enumset1(X1,X1,X1,X1)))) = X1
    | k2_zfmisc_1(X0,k2_enumset1(X1,X1,X1,X1)) = k2_enumset1(X2,X2,X2,X2)
    | sK0(X2,k2_zfmisc_1(X0,k2_enumset1(X1,X1,X1,X1))) = X2 ),
    inference(superposition,[status(thm)],[c_422,c_862])).

cnf(c_15,negated_conjecture,
    ( k2_enumset1(k4_tarski(sK6,sK7),k4_tarski(sK6,sK7),k4_tarski(sK6,sK7),k4_tarski(sK6,sK7)) != k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_30027,plain,
    ( sK5(X0,k2_enumset1(X1,X1,X1,X1),sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(X0,k2_enumset1(X1,X1,X1,X1)))) = X1
    | k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7)) != k2_zfmisc_1(X0,k2_enumset1(X1,X1,X1,X1))
    | sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(X0,k2_enumset1(X1,X1,X1,X1))) = k4_tarski(sK6,sK7) ),
    inference(superposition,[status(thm)],[c_1738,c_15])).

cnf(c_30509,plain,
    ( sK5(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7),sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7)))) = sK7
    | sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7))) = k4_tarski(sK6,sK7) ),
    inference(equality_resolution,[status(thm)],[c_30027])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | k2_enumset1(X0,X0,X0,X0) = X1
    | sK0(X0,X1) != X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_439,plain,
    ( ~ r2_hidden(sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7))),k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7)))
    | k2_enumset1(k4_tarski(sK6,sK7),k4_tarski(sK6,sK7),k4_tarski(sK6,sK7),k4_tarski(sK6,sK7)) = k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7))
    | sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7))) != k4_tarski(sK6,sK7) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_443,plain,
    ( k2_enumset1(k4_tarski(sK6,sK7),k4_tarski(sK6,sK7),k4_tarski(sK6,sK7),k4_tarski(sK6,sK7)) = k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7))
    | sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7))) != k4_tarski(sK6,sK7)
    | r2_hidden(sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7))),k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_439])).

cnf(c_481,plain,
    ( ~ r2_hidden(k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7)),k2_enumset1(X0,X0,X0,X0))
    | k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7)) = X0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_676,plain,
    ( ~ r2_hidden(k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7)),k2_enumset1(k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7)),k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7)),k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7)),k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7))))
    | k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7)) = k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7)) ),
    inference(instantiation,[status(thm)],[c_481])).

cnf(c_2,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_906,plain,
    ( r2_hidden(k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7)),k2_enumset1(k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7)),k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7)),k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7)),k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7)))) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_181,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_465,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7))),k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7)))
    | k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7)) != X1
    | sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7))) != X0 ),
    inference(instantiation,[status(thm)],[c_181])).

cnf(c_543,plain,
    ( ~ r2_hidden(k4_tarski(sK6,sK7),X0)
    | r2_hidden(sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7))),k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7)))
    | k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7)) != X0
    | sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7))) != k4_tarski(sK6,sK7) ),
    inference(instantiation,[status(thm)],[c_465])).

cnf(c_647,plain,
    ( ~ r2_hidden(k4_tarski(sK6,sK7),k2_zfmisc_1(X0,X1))
    | r2_hidden(sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7))),k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7)))
    | k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7)) != k2_zfmisc_1(X0,X1)
    | sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7))) != k4_tarski(sK6,sK7) ),
    inference(instantiation,[status(thm)],[c_543])).

cnf(c_1005,plain,
    ( ~ r2_hidden(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7)))
    | r2_hidden(sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7))),k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7)))
    | k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7)) != k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7))
    | sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7))) != k4_tarski(sK6,sK7) ),
    inference(instantiation,[status(thm)],[c_647])).

cnf(c_1006,plain,
    ( k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7)) != k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7))
    | sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7))) != k4_tarski(sK6,sK7)
    | r2_hidden(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7))) != iProver_top
    | r2_hidden(sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7))),k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1005])).

cnf(c_12,plain,
    ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2077,plain,
    ( r2_hidden(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7))) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2078,plain,
    ( r2_hidden(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2077])).

cnf(c_31220,plain,
    ( sK5(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7),sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7)))) = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_30509,c_15,c_443,c_676,c_906,c_1006,c_2078])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | k4_tarski(sK4(X1,X2,X0),sK5(X1,X2,X0)) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_414,plain,
    ( k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)) = X2
    | r2_hidden(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1079,plain,
    ( k2_enumset1(X0,X0,X0,X0) = k2_zfmisc_1(X1,X2)
    | k4_tarski(sK4(X1,X2,sK0(X0,k2_zfmisc_1(X1,X2))),sK5(X1,X2,sK0(X0,k2_zfmisc_1(X1,X2)))) = sK0(X0,k2_zfmisc_1(X1,X2))
    | sK0(X0,k2_zfmisc_1(X1,X2)) = X0 ),
    inference(superposition,[status(thm)],[c_422,c_414])).

cnf(c_31260,plain,
    ( k2_enumset1(k4_tarski(sK6,sK7),k4_tarski(sK6,sK7),k4_tarski(sK6,sK7),k4_tarski(sK6,sK7)) = k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7))
    | k4_tarski(sK4(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7),sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7)))),sK7) = sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7)))
    | sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7))) = k4_tarski(sK6,sK7) ),
    inference(superposition,[status(thm)],[c_31220,c_1079])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(sK4(X1,X2,X0),X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_412,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(sK4(X1,X2,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_857,plain,
    ( sK4(k2_enumset1(X0,X0,X0,X0),X1,X2) = X0
    | r2_hidden(X2,k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_412,c_420])).

cnf(c_1384,plain,
    ( sK4(k2_enumset1(X0,X0,X0,X0),X1,sK0(X2,k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),X1))) = X0
    | k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),X1) = k2_enumset1(X2,X2,X2,X2)
    | sK0(X2,k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),X1)) = X2 ),
    inference(superposition,[status(thm)],[c_422,c_857])).

cnf(c_20305,plain,
    ( sK4(k2_enumset1(X0,X0,X0,X0),X1,sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),X1))) = X0
    | k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7)) != k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),X1)
    | sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),X1)) = k4_tarski(sK6,sK7) ),
    inference(superposition,[status(thm)],[c_1384,c_15])).

cnf(c_20633,plain,
    ( sK4(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7),sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7)))) = sK6
    | sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7))) = k4_tarski(sK6,sK7) ),
    inference(equality_resolution,[status(thm)],[c_20305])).

cnf(c_21763,plain,
    ( sK4(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7),sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7)))) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_20633,c_15,c_443,c_676,c_906,c_1006,c_2078])).

cnf(c_31261,plain,
    ( k2_enumset1(k4_tarski(sK6,sK7),k4_tarski(sK6,sK7),k4_tarski(sK6,sK7),k4_tarski(sK6,sK7)) = k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7))
    | sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7))) = k4_tarski(sK6,sK7) ),
    inference(light_normalisation,[status(thm)],[c_31260,c_21763])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_31261,c_2078,c_1006,c_906,c_676,c_443,c_15])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:03:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 15.59/2.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.59/2.50  
% 15.59/2.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.59/2.50  
% 15.59/2.50  ------  iProver source info
% 15.59/2.50  
% 15.59/2.50  git: date: 2020-06-30 10:37:57 +0100
% 15.59/2.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.59/2.50  git: non_committed_changes: false
% 15.59/2.50  git: last_make_outside_of_git: false
% 15.59/2.50  
% 15.59/2.50  ------ 
% 15.59/2.50  
% 15.59/2.50  ------ Input Options
% 15.59/2.50  
% 15.59/2.50  --out_options                           all
% 15.59/2.50  --tptp_safe_out                         true
% 15.59/2.50  --problem_path                          ""
% 15.59/2.50  --include_path                          ""
% 15.59/2.50  --clausifier                            res/vclausify_rel
% 15.59/2.50  --clausifier_options                    ""
% 15.59/2.50  --stdin                                 false
% 15.59/2.50  --stats_out                             all
% 15.59/2.50  
% 15.59/2.50  ------ General Options
% 15.59/2.50  
% 15.59/2.50  --fof                                   false
% 15.59/2.50  --time_out_real                         305.
% 15.59/2.50  --time_out_virtual                      -1.
% 15.59/2.50  --symbol_type_check                     false
% 15.59/2.50  --clausify_out                          false
% 15.59/2.50  --sig_cnt_out                           false
% 15.59/2.50  --trig_cnt_out                          false
% 15.59/2.50  --trig_cnt_out_tolerance                1.
% 15.59/2.50  --trig_cnt_out_sk_spl                   false
% 15.59/2.50  --abstr_cl_out                          false
% 15.59/2.50  
% 15.59/2.50  ------ Global Options
% 15.59/2.50  
% 15.59/2.50  --schedule                              default
% 15.59/2.50  --add_important_lit                     false
% 15.59/2.50  --prop_solver_per_cl                    1000
% 15.59/2.50  --min_unsat_core                        false
% 15.59/2.50  --soft_assumptions                      false
% 15.59/2.50  --soft_lemma_size                       3
% 15.59/2.50  --prop_impl_unit_size                   0
% 15.59/2.50  --prop_impl_unit                        []
% 15.59/2.50  --share_sel_clauses                     true
% 15.59/2.50  --reset_solvers                         false
% 15.59/2.50  --bc_imp_inh                            [conj_cone]
% 15.59/2.50  --conj_cone_tolerance                   3.
% 15.59/2.50  --extra_neg_conj                        none
% 15.59/2.50  --large_theory_mode                     true
% 15.59/2.50  --prolific_symb_bound                   200
% 15.59/2.50  --lt_threshold                          2000
% 15.59/2.50  --clause_weak_htbl                      true
% 15.59/2.50  --gc_record_bc_elim                     false
% 15.59/2.50  
% 15.59/2.50  ------ Preprocessing Options
% 15.59/2.50  
% 15.59/2.50  --preprocessing_flag                    true
% 15.59/2.50  --time_out_prep_mult                    0.1
% 15.59/2.50  --splitting_mode                        input
% 15.59/2.50  --splitting_grd                         true
% 15.59/2.50  --splitting_cvd                         false
% 15.59/2.50  --splitting_cvd_svl                     false
% 15.59/2.50  --splitting_nvd                         32
% 15.59/2.50  --sub_typing                            true
% 15.59/2.50  --prep_gs_sim                           true
% 15.59/2.50  --prep_unflatten                        true
% 15.59/2.50  --prep_res_sim                          true
% 15.59/2.50  --prep_upred                            true
% 15.59/2.50  --prep_sem_filter                       exhaustive
% 15.59/2.50  --prep_sem_filter_out                   false
% 15.59/2.50  --pred_elim                             true
% 15.59/2.50  --res_sim_input                         true
% 15.59/2.50  --eq_ax_congr_red                       true
% 15.59/2.50  --pure_diseq_elim                       true
% 15.59/2.50  --brand_transform                       false
% 15.59/2.50  --non_eq_to_eq                          false
% 15.59/2.50  --prep_def_merge                        true
% 15.59/2.50  --prep_def_merge_prop_impl              false
% 15.59/2.50  --prep_def_merge_mbd                    true
% 15.59/2.50  --prep_def_merge_tr_red                 false
% 15.59/2.50  --prep_def_merge_tr_cl                  false
% 15.59/2.50  --smt_preprocessing                     true
% 15.59/2.50  --smt_ac_axioms                         fast
% 15.59/2.50  --preprocessed_out                      false
% 15.59/2.50  --preprocessed_stats                    false
% 15.59/2.50  
% 15.59/2.50  ------ Abstraction refinement Options
% 15.59/2.50  
% 15.59/2.50  --abstr_ref                             []
% 15.59/2.50  --abstr_ref_prep                        false
% 15.59/2.50  --abstr_ref_until_sat                   false
% 15.59/2.50  --abstr_ref_sig_restrict                funpre
% 15.59/2.50  --abstr_ref_af_restrict_to_split_sk     false
% 15.59/2.50  --abstr_ref_under                       []
% 15.59/2.50  
% 15.59/2.50  ------ SAT Options
% 15.59/2.50  
% 15.59/2.50  --sat_mode                              false
% 15.59/2.50  --sat_fm_restart_options                ""
% 15.59/2.50  --sat_gr_def                            false
% 15.59/2.50  --sat_epr_types                         true
% 15.59/2.50  --sat_non_cyclic_types                  false
% 15.59/2.50  --sat_finite_models                     false
% 15.59/2.50  --sat_fm_lemmas                         false
% 15.59/2.50  --sat_fm_prep                           false
% 15.59/2.50  --sat_fm_uc_incr                        true
% 15.59/2.50  --sat_out_model                         small
% 15.59/2.50  --sat_out_clauses                       false
% 15.59/2.50  
% 15.59/2.50  ------ QBF Options
% 15.59/2.50  
% 15.59/2.50  --qbf_mode                              false
% 15.59/2.50  --qbf_elim_univ                         false
% 15.59/2.50  --qbf_dom_inst                          none
% 15.59/2.50  --qbf_dom_pre_inst                      false
% 15.59/2.50  --qbf_sk_in                             false
% 15.59/2.50  --qbf_pred_elim                         true
% 15.59/2.50  --qbf_split                             512
% 15.59/2.50  
% 15.59/2.50  ------ BMC1 Options
% 15.59/2.50  
% 15.59/2.50  --bmc1_incremental                      false
% 15.59/2.50  --bmc1_axioms                           reachable_all
% 15.59/2.50  --bmc1_min_bound                        0
% 15.59/2.50  --bmc1_max_bound                        -1
% 15.59/2.50  --bmc1_max_bound_default                -1
% 15.59/2.50  --bmc1_symbol_reachability              true
% 15.59/2.50  --bmc1_property_lemmas                  false
% 15.59/2.50  --bmc1_k_induction                      false
% 15.59/2.50  --bmc1_non_equiv_states                 false
% 15.59/2.50  --bmc1_deadlock                         false
% 15.59/2.50  --bmc1_ucm                              false
% 15.59/2.50  --bmc1_add_unsat_core                   none
% 15.59/2.50  --bmc1_unsat_core_children              false
% 15.59/2.50  --bmc1_unsat_core_extrapolate_axioms    false
% 15.59/2.50  --bmc1_out_stat                         full
% 15.59/2.50  --bmc1_ground_init                      false
% 15.59/2.50  --bmc1_pre_inst_next_state              false
% 15.59/2.50  --bmc1_pre_inst_state                   false
% 15.59/2.50  --bmc1_pre_inst_reach_state             false
% 15.59/2.50  --bmc1_out_unsat_core                   false
% 15.59/2.50  --bmc1_aig_witness_out                  false
% 15.59/2.50  --bmc1_verbose                          false
% 15.59/2.50  --bmc1_dump_clauses_tptp                false
% 15.59/2.50  --bmc1_dump_unsat_core_tptp             false
% 15.59/2.50  --bmc1_dump_file                        -
% 15.59/2.50  --bmc1_ucm_expand_uc_limit              128
% 15.59/2.50  --bmc1_ucm_n_expand_iterations          6
% 15.59/2.50  --bmc1_ucm_extend_mode                  1
% 15.59/2.50  --bmc1_ucm_init_mode                    2
% 15.59/2.50  --bmc1_ucm_cone_mode                    none
% 15.59/2.50  --bmc1_ucm_reduced_relation_type        0
% 15.59/2.50  --bmc1_ucm_relax_model                  4
% 15.59/2.50  --bmc1_ucm_full_tr_after_sat            true
% 15.59/2.50  --bmc1_ucm_expand_neg_assumptions       false
% 15.59/2.50  --bmc1_ucm_layered_model                none
% 15.59/2.50  --bmc1_ucm_max_lemma_size               10
% 15.59/2.50  
% 15.59/2.50  ------ AIG Options
% 15.59/2.50  
% 15.59/2.50  --aig_mode                              false
% 15.59/2.50  
% 15.59/2.50  ------ Instantiation Options
% 15.59/2.50  
% 15.59/2.50  --instantiation_flag                    true
% 15.59/2.50  --inst_sos_flag                         true
% 15.59/2.50  --inst_sos_phase                        true
% 15.59/2.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.59/2.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.59/2.50  --inst_lit_sel_side                     num_symb
% 15.59/2.50  --inst_solver_per_active                1400
% 15.59/2.50  --inst_solver_calls_frac                1.
% 15.59/2.50  --inst_passive_queue_type               priority_queues
% 15.59/2.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.59/2.50  --inst_passive_queues_freq              [25;2]
% 15.59/2.50  --inst_dismatching                      true
% 15.59/2.50  --inst_eager_unprocessed_to_passive     true
% 15.59/2.50  --inst_prop_sim_given                   true
% 15.59/2.50  --inst_prop_sim_new                     false
% 15.59/2.50  --inst_subs_new                         false
% 15.59/2.50  --inst_eq_res_simp                      false
% 15.59/2.50  --inst_subs_given                       false
% 15.59/2.50  --inst_orphan_elimination               true
% 15.59/2.50  --inst_learning_loop_flag               true
% 15.59/2.50  --inst_learning_start                   3000
% 15.59/2.50  --inst_learning_factor                  2
% 15.59/2.50  --inst_start_prop_sim_after_learn       3
% 15.59/2.50  --inst_sel_renew                        solver
% 15.59/2.50  --inst_lit_activity_flag                true
% 15.59/2.50  --inst_restr_to_given                   false
% 15.59/2.50  --inst_activity_threshold               500
% 15.59/2.50  --inst_out_proof                        true
% 15.59/2.50  
% 15.59/2.50  ------ Resolution Options
% 15.59/2.50  
% 15.59/2.50  --resolution_flag                       true
% 15.59/2.50  --res_lit_sel                           adaptive
% 15.59/2.50  --res_lit_sel_side                      none
% 15.59/2.50  --res_ordering                          kbo
% 15.59/2.50  --res_to_prop_solver                    active
% 15.59/2.50  --res_prop_simpl_new                    false
% 15.59/2.50  --res_prop_simpl_given                  true
% 15.59/2.50  --res_passive_queue_type                priority_queues
% 15.59/2.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.59/2.50  --res_passive_queues_freq               [15;5]
% 15.59/2.50  --res_forward_subs                      full
% 15.59/2.50  --res_backward_subs                     full
% 15.59/2.50  --res_forward_subs_resolution           true
% 15.59/2.50  --res_backward_subs_resolution          true
% 15.59/2.50  --res_orphan_elimination                true
% 15.59/2.50  --res_time_limit                        2.
% 15.59/2.50  --res_out_proof                         true
% 15.59/2.50  
% 15.59/2.50  ------ Superposition Options
% 15.59/2.50  
% 15.59/2.50  --superposition_flag                    true
% 15.59/2.50  --sup_passive_queue_type                priority_queues
% 15.59/2.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.59/2.50  --sup_passive_queues_freq               [8;1;4]
% 15.59/2.50  --demod_completeness_check              fast
% 15.59/2.50  --demod_use_ground                      true
% 15.59/2.50  --sup_to_prop_solver                    passive
% 15.59/2.50  --sup_prop_simpl_new                    true
% 15.59/2.50  --sup_prop_simpl_given                  true
% 15.59/2.50  --sup_fun_splitting                     true
% 15.59/2.50  --sup_smt_interval                      50000
% 15.59/2.50  
% 15.59/2.50  ------ Superposition Simplification Setup
% 15.59/2.50  
% 15.59/2.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.59/2.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.59/2.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.59/2.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.59/2.50  --sup_full_triv                         [TrivRules;PropSubs]
% 15.59/2.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.59/2.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.59/2.50  --sup_immed_triv                        [TrivRules]
% 15.59/2.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.59/2.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.59/2.50  --sup_immed_bw_main                     []
% 15.59/2.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.59/2.50  --sup_input_triv                        [Unflattening;TrivRules]
% 15.59/2.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.59/2.50  --sup_input_bw                          []
% 15.59/2.50  
% 15.59/2.50  ------ Combination Options
% 15.59/2.50  
% 15.59/2.50  --comb_res_mult                         3
% 15.59/2.50  --comb_sup_mult                         2
% 15.59/2.50  --comb_inst_mult                        10
% 15.59/2.50  
% 15.59/2.50  ------ Debug Options
% 15.59/2.50  
% 15.59/2.50  --dbg_backtrace                         false
% 15.59/2.50  --dbg_dump_prop_clauses                 false
% 15.59/2.50  --dbg_dump_prop_clauses_file            -
% 15.59/2.50  --dbg_out_stat                          false
% 15.59/2.50  ------ Parsing...
% 15.59/2.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.59/2.50  
% 15.59/2.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 15.59/2.50  
% 15.59/2.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.59/2.50  
% 15.59/2.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.59/2.50  ------ Proving...
% 15.59/2.50  ------ Problem Properties 
% 15.59/2.50  
% 15.59/2.50  
% 15.59/2.50  clauses                                 16
% 15.59/2.50  conjectures                             1
% 15.59/2.50  EPR                                     0
% 15.59/2.50  Horn                                    12
% 15.59/2.50  unary                                   3
% 15.59/2.50  binary                                  6
% 15.59/2.50  lits                                    38
% 15.59/2.50  lits eq                                 15
% 15.59/2.50  fd_pure                                 0
% 15.59/2.50  fd_pseudo                               0
% 15.59/2.50  fd_cond                                 0
% 15.59/2.50  fd_pseudo_cond                          8
% 15.59/2.50  AC symbols                              0
% 15.59/2.50  
% 15.59/2.50  ------ Schedule dynamic 5 is on 
% 15.59/2.50  
% 15.59/2.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 15.59/2.50  
% 15.59/2.50  
% 15.59/2.50  ------ 
% 15.59/2.50  Current options:
% 15.59/2.50  ------ 
% 15.59/2.50  
% 15.59/2.50  ------ Input Options
% 15.59/2.50  
% 15.59/2.50  --out_options                           all
% 15.59/2.50  --tptp_safe_out                         true
% 15.59/2.50  --problem_path                          ""
% 15.59/2.50  --include_path                          ""
% 15.59/2.50  --clausifier                            res/vclausify_rel
% 15.59/2.50  --clausifier_options                    ""
% 15.59/2.50  --stdin                                 false
% 15.59/2.50  --stats_out                             all
% 15.59/2.50  
% 15.59/2.50  ------ General Options
% 15.59/2.50  
% 15.59/2.50  --fof                                   false
% 15.59/2.50  --time_out_real                         305.
% 15.59/2.50  --time_out_virtual                      -1.
% 15.59/2.50  --symbol_type_check                     false
% 15.59/2.50  --clausify_out                          false
% 15.59/2.50  --sig_cnt_out                           false
% 15.59/2.50  --trig_cnt_out                          false
% 15.59/2.50  --trig_cnt_out_tolerance                1.
% 15.59/2.50  --trig_cnt_out_sk_spl                   false
% 15.59/2.50  --abstr_cl_out                          false
% 15.59/2.50  
% 15.59/2.50  ------ Global Options
% 15.59/2.50  
% 15.59/2.50  --schedule                              default
% 15.59/2.50  --add_important_lit                     false
% 15.59/2.50  --prop_solver_per_cl                    1000
% 15.59/2.50  --min_unsat_core                        false
% 15.59/2.50  --soft_assumptions                      false
% 15.59/2.50  --soft_lemma_size                       3
% 15.59/2.50  --prop_impl_unit_size                   0
% 15.59/2.50  --prop_impl_unit                        []
% 15.59/2.50  --share_sel_clauses                     true
% 15.59/2.50  --reset_solvers                         false
% 15.59/2.50  --bc_imp_inh                            [conj_cone]
% 15.59/2.50  --conj_cone_tolerance                   3.
% 15.59/2.50  --extra_neg_conj                        none
% 15.59/2.50  --large_theory_mode                     true
% 15.59/2.50  --prolific_symb_bound                   200
% 15.59/2.50  --lt_threshold                          2000
% 15.59/2.50  --clause_weak_htbl                      true
% 15.59/2.50  --gc_record_bc_elim                     false
% 15.59/2.50  
% 15.59/2.50  ------ Preprocessing Options
% 15.59/2.50  
% 15.59/2.50  --preprocessing_flag                    true
% 15.59/2.50  --time_out_prep_mult                    0.1
% 15.59/2.50  --splitting_mode                        input
% 15.59/2.50  --splitting_grd                         true
% 15.59/2.50  --splitting_cvd                         false
% 15.59/2.50  --splitting_cvd_svl                     false
% 15.59/2.50  --splitting_nvd                         32
% 15.59/2.50  --sub_typing                            true
% 15.59/2.50  --prep_gs_sim                           true
% 15.59/2.50  --prep_unflatten                        true
% 15.59/2.50  --prep_res_sim                          true
% 15.59/2.50  --prep_upred                            true
% 15.59/2.50  --prep_sem_filter                       exhaustive
% 15.59/2.50  --prep_sem_filter_out                   false
% 15.59/2.50  --pred_elim                             true
% 15.59/2.50  --res_sim_input                         true
% 15.59/2.50  --eq_ax_congr_red                       true
% 15.59/2.50  --pure_diseq_elim                       true
% 15.59/2.50  --brand_transform                       false
% 15.59/2.50  --non_eq_to_eq                          false
% 15.59/2.50  --prep_def_merge                        true
% 15.59/2.50  --prep_def_merge_prop_impl              false
% 15.59/2.50  --prep_def_merge_mbd                    true
% 15.59/2.50  --prep_def_merge_tr_red                 false
% 15.59/2.50  --prep_def_merge_tr_cl                  false
% 15.59/2.50  --smt_preprocessing                     true
% 15.59/2.50  --smt_ac_axioms                         fast
% 15.59/2.50  --preprocessed_out                      false
% 15.59/2.50  --preprocessed_stats                    false
% 15.59/2.50  
% 15.59/2.50  ------ Abstraction refinement Options
% 15.59/2.50  
% 15.59/2.50  --abstr_ref                             []
% 15.59/2.50  --abstr_ref_prep                        false
% 15.59/2.50  --abstr_ref_until_sat                   false
% 15.59/2.50  --abstr_ref_sig_restrict                funpre
% 15.59/2.50  --abstr_ref_af_restrict_to_split_sk     false
% 15.59/2.50  --abstr_ref_under                       []
% 15.59/2.50  
% 15.59/2.50  ------ SAT Options
% 15.59/2.50  
% 15.59/2.50  --sat_mode                              false
% 15.59/2.50  --sat_fm_restart_options                ""
% 15.59/2.50  --sat_gr_def                            false
% 15.59/2.50  --sat_epr_types                         true
% 15.59/2.50  --sat_non_cyclic_types                  false
% 15.59/2.50  --sat_finite_models                     false
% 15.59/2.50  --sat_fm_lemmas                         false
% 15.59/2.50  --sat_fm_prep                           false
% 15.59/2.50  --sat_fm_uc_incr                        true
% 15.59/2.50  --sat_out_model                         small
% 15.59/2.50  --sat_out_clauses                       false
% 15.59/2.50  
% 15.59/2.50  ------ QBF Options
% 15.59/2.50  
% 15.59/2.50  --qbf_mode                              false
% 15.59/2.50  --qbf_elim_univ                         false
% 15.59/2.50  --qbf_dom_inst                          none
% 15.59/2.50  --qbf_dom_pre_inst                      false
% 15.59/2.50  --qbf_sk_in                             false
% 15.59/2.50  --qbf_pred_elim                         true
% 15.59/2.50  --qbf_split                             512
% 15.59/2.50  
% 15.59/2.50  ------ BMC1 Options
% 15.59/2.50  
% 15.59/2.50  --bmc1_incremental                      false
% 15.59/2.50  --bmc1_axioms                           reachable_all
% 15.59/2.50  --bmc1_min_bound                        0
% 15.59/2.50  --bmc1_max_bound                        -1
% 15.59/2.50  --bmc1_max_bound_default                -1
% 15.59/2.50  --bmc1_symbol_reachability              true
% 15.59/2.50  --bmc1_property_lemmas                  false
% 15.59/2.50  --bmc1_k_induction                      false
% 15.59/2.50  --bmc1_non_equiv_states                 false
% 15.59/2.50  --bmc1_deadlock                         false
% 15.59/2.50  --bmc1_ucm                              false
% 15.59/2.50  --bmc1_add_unsat_core                   none
% 15.59/2.50  --bmc1_unsat_core_children              false
% 15.59/2.50  --bmc1_unsat_core_extrapolate_axioms    false
% 15.59/2.50  --bmc1_out_stat                         full
% 15.59/2.50  --bmc1_ground_init                      false
% 15.59/2.50  --bmc1_pre_inst_next_state              false
% 15.59/2.50  --bmc1_pre_inst_state                   false
% 15.59/2.50  --bmc1_pre_inst_reach_state             false
% 15.59/2.50  --bmc1_out_unsat_core                   false
% 15.59/2.50  --bmc1_aig_witness_out                  false
% 15.59/2.50  --bmc1_verbose                          false
% 15.59/2.50  --bmc1_dump_clauses_tptp                false
% 15.59/2.50  --bmc1_dump_unsat_core_tptp             false
% 15.59/2.50  --bmc1_dump_file                        -
% 15.59/2.50  --bmc1_ucm_expand_uc_limit              128
% 15.59/2.50  --bmc1_ucm_n_expand_iterations          6
% 15.59/2.50  --bmc1_ucm_extend_mode                  1
% 15.59/2.50  --bmc1_ucm_init_mode                    2
% 15.59/2.50  --bmc1_ucm_cone_mode                    none
% 15.59/2.50  --bmc1_ucm_reduced_relation_type        0
% 15.59/2.50  --bmc1_ucm_relax_model                  4
% 15.59/2.50  --bmc1_ucm_full_tr_after_sat            true
% 15.59/2.50  --bmc1_ucm_expand_neg_assumptions       false
% 15.59/2.50  --bmc1_ucm_layered_model                none
% 15.59/2.50  --bmc1_ucm_max_lemma_size               10
% 15.59/2.50  
% 15.59/2.50  ------ AIG Options
% 15.59/2.50  
% 15.59/2.50  --aig_mode                              false
% 15.59/2.50  
% 15.59/2.50  ------ Instantiation Options
% 15.59/2.50  
% 15.59/2.50  --instantiation_flag                    true
% 15.59/2.50  --inst_sos_flag                         true
% 15.59/2.50  --inst_sos_phase                        true
% 15.59/2.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.59/2.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.59/2.50  --inst_lit_sel_side                     none
% 15.59/2.50  --inst_solver_per_active                1400
% 15.59/2.50  --inst_solver_calls_frac                1.
% 15.59/2.50  --inst_passive_queue_type               priority_queues
% 15.59/2.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.59/2.50  --inst_passive_queues_freq              [25;2]
% 15.59/2.50  --inst_dismatching                      true
% 15.59/2.50  --inst_eager_unprocessed_to_passive     true
% 15.59/2.50  --inst_prop_sim_given                   true
% 15.59/2.50  --inst_prop_sim_new                     false
% 15.59/2.50  --inst_subs_new                         false
% 15.59/2.50  --inst_eq_res_simp                      false
% 15.59/2.50  --inst_subs_given                       false
% 15.59/2.50  --inst_orphan_elimination               true
% 15.59/2.50  --inst_learning_loop_flag               true
% 15.59/2.50  --inst_learning_start                   3000
% 15.59/2.50  --inst_learning_factor                  2
% 15.59/2.50  --inst_start_prop_sim_after_learn       3
% 15.59/2.50  --inst_sel_renew                        solver
% 15.59/2.50  --inst_lit_activity_flag                true
% 15.59/2.50  --inst_restr_to_given                   false
% 15.59/2.50  --inst_activity_threshold               500
% 15.59/2.50  --inst_out_proof                        true
% 15.59/2.50  
% 15.59/2.50  ------ Resolution Options
% 15.59/2.50  
% 15.59/2.50  --resolution_flag                       false
% 15.59/2.50  --res_lit_sel                           adaptive
% 15.59/2.50  --res_lit_sel_side                      none
% 15.59/2.50  --res_ordering                          kbo
% 15.59/2.50  --res_to_prop_solver                    active
% 15.59/2.50  --res_prop_simpl_new                    false
% 15.59/2.50  --res_prop_simpl_given                  true
% 15.59/2.50  --res_passive_queue_type                priority_queues
% 15.59/2.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.59/2.50  --res_passive_queues_freq               [15;5]
% 15.59/2.50  --res_forward_subs                      full
% 15.59/2.50  --res_backward_subs                     full
% 15.59/2.50  --res_forward_subs_resolution           true
% 15.59/2.50  --res_backward_subs_resolution          true
% 15.59/2.50  --res_orphan_elimination                true
% 15.59/2.50  --res_time_limit                        2.
% 15.59/2.50  --res_out_proof                         true
% 15.59/2.50  
% 15.59/2.50  ------ Superposition Options
% 15.59/2.50  
% 15.59/2.50  --superposition_flag                    true
% 15.59/2.50  --sup_passive_queue_type                priority_queues
% 15.59/2.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.59/2.50  --sup_passive_queues_freq               [8;1;4]
% 15.59/2.50  --demod_completeness_check              fast
% 15.59/2.50  --demod_use_ground                      true
% 15.59/2.50  --sup_to_prop_solver                    passive
% 15.59/2.50  --sup_prop_simpl_new                    true
% 15.59/2.50  --sup_prop_simpl_given                  true
% 15.59/2.50  --sup_fun_splitting                     true
% 15.59/2.50  --sup_smt_interval                      50000
% 15.59/2.50  
% 15.59/2.50  ------ Superposition Simplification Setup
% 15.59/2.50  
% 15.59/2.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.59/2.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.59/2.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.59/2.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.59/2.50  --sup_full_triv                         [TrivRules;PropSubs]
% 15.59/2.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.59/2.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.59/2.50  --sup_immed_triv                        [TrivRules]
% 15.59/2.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.59/2.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.59/2.50  --sup_immed_bw_main                     []
% 15.59/2.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.59/2.50  --sup_input_triv                        [Unflattening;TrivRules]
% 15.59/2.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.59/2.50  --sup_input_bw                          []
% 15.59/2.50  
% 15.59/2.50  ------ Combination Options
% 15.59/2.50  
% 15.59/2.50  --comb_res_mult                         3
% 15.59/2.50  --comb_sup_mult                         2
% 15.59/2.50  --comb_inst_mult                        10
% 15.59/2.50  
% 15.59/2.50  ------ Debug Options
% 15.59/2.50  
% 15.59/2.50  --dbg_backtrace                         false
% 15.59/2.50  --dbg_dump_prop_clauses                 false
% 15.59/2.50  --dbg_dump_prop_clauses_file            -
% 15.59/2.50  --dbg_out_stat                          false
% 15.59/2.50  
% 15.59/2.50  
% 15.59/2.50  
% 15.59/2.50  
% 15.59/2.50  ------ Proving...
% 15.59/2.50  
% 15.59/2.50  
% 15.59/2.50  % SZS status Theorem for theBenchmark.p
% 15.59/2.50  
% 15.59/2.50  % SZS output start CNFRefutation for theBenchmark.p
% 15.59/2.50  
% 15.59/2.50  fof(f1,axiom,(
% 15.59/2.50    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 15.59/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.59/2.50  
% 15.59/2.50  fof(f8,plain,(
% 15.59/2.50    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 15.59/2.50    inference(nnf_transformation,[],[f1])).
% 15.59/2.50  
% 15.59/2.50  fof(f9,plain,(
% 15.59/2.50    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 15.59/2.50    inference(rectify,[],[f8])).
% 15.59/2.50  
% 15.59/2.50  fof(f10,plain,(
% 15.59/2.50    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1))))),
% 15.59/2.50    introduced(choice_axiom,[])).
% 15.59/2.50  
% 15.59/2.50  fof(f11,plain,(
% 15.59/2.50    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 15.59/2.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f10])).
% 15.59/2.50  
% 15.59/2.50  fof(f24,plain,(
% 15.59/2.50    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1)) )),
% 15.59/2.50    inference(cnf_transformation,[],[f11])).
% 15.59/2.50  
% 15.59/2.50  fof(f2,axiom,(
% 15.59/2.50    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)),
% 15.59/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.59/2.50  
% 15.59/2.50  fof(f26,plain,(
% 15.59/2.50    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 15.59/2.50    inference(cnf_transformation,[],[f2])).
% 15.59/2.50  
% 15.59/2.50  fof(f40,plain,(
% 15.59/2.50    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X0) = X1 | sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1)) )),
% 15.59/2.50    inference(definition_unfolding,[],[f24,f26])).
% 15.59/2.50  
% 15.59/2.50  fof(f3,axiom,(
% 15.59/2.50    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 15.59/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.59/2.50  
% 15.59/2.50  fof(f12,plain,(
% 15.59/2.50    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 15.59/2.50    inference(nnf_transformation,[],[f3])).
% 15.59/2.50  
% 15.59/2.50  fof(f13,plain,(
% 15.59/2.50    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 15.59/2.50    inference(rectify,[],[f12])).
% 15.59/2.50  
% 15.59/2.50  fof(f16,plain,(
% 15.59/2.50    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) => (k4_tarski(sK4(X0,X1,X8),sK5(X0,X1,X8)) = X8 & r2_hidden(sK5(X0,X1,X8),X1) & r2_hidden(sK4(X0,X1,X8),X0)))),
% 15.59/2.50    introduced(choice_axiom,[])).
% 15.59/2.50  
% 15.59/2.50  fof(f15,plain,(
% 15.59/2.50    ( ! [X3] : (! [X2,X1,X0] : (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) => (k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)) = X3 & r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)))) )),
% 15.59/2.50    introduced(choice_axiom,[])).
% 15.59/2.50  
% 15.59/2.50  fof(f14,plain,(
% 15.59/2.50    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK1(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK1(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 15.59/2.50    introduced(choice_axiom,[])).
% 15.59/2.50  
% 15.59/2.50  fof(f17,plain,(
% 15.59/2.50    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ((! [X4,X5] : (k4_tarski(X4,X5) != sK1(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)) = sK1(X0,X1,X2) & r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & ((k4_tarski(sK4(X0,X1,X8),sK5(X0,X1,X8)) = X8 & r2_hidden(sK5(X0,X1,X8),X1) & r2_hidden(sK4(X0,X1,X8),X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 15.59/2.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f13,f16,f15,f14])).
% 15.59/2.50  
% 15.59/2.50  fof(f28,plain,(
% 15.59/2.50    ( ! [X2,X0,X8,X1] : (r2_hidden(sK5(X0,X1,X8),X1) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 15.59/2.50    inference(cnf_transformation,[],[f17])).
% 15.59/2.50  
% 15.59/2.50  fof(f53,plain,(
% 15.59/2.50    ( ! [X0,X8,X1] : (r2_hidden(sK5(X0,X1,X8),X1) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 15.59/2.50    inference(equality_resolution,[],[f28])).
% 15.59/2.50  
% 15.59/2.50  fof(f22,plain,(
% 15.59/2.50    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 15.59/2.50    inference(cnf_transformation,[],[f11])).
% 15.59/2.50  
% 15.59/2.50  fof(f42,plain,(
% 15.59/2.50    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 15.59/2.50    inference(definition_unfolding,[],[f22,f26])).
% 15.59/2.50  
% 15.59/2.50  fof(f49,plain,(
% 15.59/2.50    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))) )),
% 15.59/2.50    inference(equality_resolution,[],[f42])).
% 15.59/2.50  
% 15.59/2.50  fof(f5,conjecture,(
% 15.59/2.50    ! [X0,X1] : k1_tarski(k4_tarski(X0,X1)) = k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1))),
% 15.59/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.59/2.50  
% 15.59/2.50  fof(f6,negated_conjecture,(
% 15.59/2.50    ~! [X0,X1] : k1_tarski(k4_tarski(X0,X1)) = k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1))),
% 15.59/2.50    inference(negated_conjecture,[],[f5])).
% 15.59/2.50  
% 15.59/2.50  fof(f7,plain,(
% 15.59/2.50    ? [X0,X1] : k1_tarski(k4_tarski(X0,X1)) != k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1))),
% 15.59/2.50    inference(ennf_transformation,[],[f6])).
% 15.59/2.50  
% 15.59/2.50  fof(f20,plain,(
% 15.59/2.50    ? [X0,X1] : k1_tarski(k4_tarski(X0,X1)) != k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) => k1_tarski(k4_tarski(sK6,sK7)) != k2_zfmisc_1(k1_tarski(sK6),k1_tarski(sK7))),
% 15.59/2.50    introduced(choice_axiom,[])).
% 15.59/2.50  
% 15.59/2.50  fof(f21,plain,(
% 15.59/2.50    k1_tarski(k4_tarski(sK6,sK7)) != k2_zfmisc_1(k1_tarski(sK6),k1_tarski(sK7))),
% 15.59/2.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f7,f20])).
% 15.59/2.50  
% 15.59/2.50  fof(f38,plain,(
% 15.59/2.50    k1_tarski(k4_tarski(sK6,sK7)) != k2_zfmisc_1(k1_tarski(sK6),k1_tarski(sK7))),
% 15.59/2.50    inference(cnf_transformation,[],[f21])).
% 15.59/2.50  
% 15.59/2.50  fof(f46,plain,(
% 15.59/2.50    k2_enumset1(k4_tarski(sK6,sK7),k4_tarski(sK6,sK7),k4_tarski(sK6,sK7),k4_tarski(sK6,sK7)) != k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7))),
% 15.59/2.50    inference(definition_unfolding,[],[f38,f26,f26,f26])).
% 15.59/2.50  
% 15.59/2.50  fof(f25,plain,(
% 15.59/2.50    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) )),
% 15.59/2.50    inference(cnf_transformation,[],[f11])).
% 15.59/2.50  
% 15.59/2.50  fof(f39,plain,(
% 15.59/2.50    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X0) = X1 | sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) )),
% 15.59/2.50    inference(definition_unfolding,[],[f25,f26])).
% 15.59/2.50  
% 15.59/2.50  fof(f23,plain,(
% 15.59/2.50    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 15.59/2.50    inference(cnf_transformation,[],[f11])).
% 15.59/2.50  
% 15.59/2.50  fof(f41,plain,(
% 15.59/2.50    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 15.59/2.50    inference(definition_unfolding,[],[f23,f26])).
% 15.59/2.50  
% 15.59/2.50  fof(f47,plain,(
% 15.59/2.50    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_enumset1(X3,X3,X3,X3) != X1) )),
% 15.59/2.50    inference(equality_resolution,[],[f41])).
% 15.59/2.50  
% 15.59/2.50  fof(f48,plain,(
% 15.59/2.50    ( ! [X3] : (r2_hidden(X3,k2_enumset1(X3,X3,X3,X3))) )),
% 15.59/2.50    inference(equality_resolution,[],[f47])).
% 15.59/2.50  
% 15.59/2.50  fof(f4,axiom,(
% 15.59/2.50    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) <=> (X1 = X3 & X0 = X2))),
% 15.59/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.59/2.50  
% 15.59/2.50  fof(f18,plain,(
% 15.59/2.50    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) | (X1 != X3 | X0 != X2)) & ((X1 = X3 & X0 = X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))))),
% 15.59/2.50    inference(nnf_transformation,[],[f4])).
% 15.59/2.50  
% 15.59/2.50  fof(f19,plain,(
% 15.59/2.50    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) | X1 != X3 | X0 != X2) & ((X1 = X3 & X0 = X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))))),
% 15.59/2.50    inference(flattening,[],[f18])).
% 15.59/2.50  
% 15.59/2.50  fof(f37,plain,(
% 15.59/2.50    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) | X1 != X3 | X0 != X2) )),
% 15.59/2.50    inference(cnf_transformation,[],[f19])).
% 15.59/2.50  
% 15.59/2.50  fof(f43,plain,(
% 15.59/2.50    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),k2_enumset1(X3,X3,X3,X3))) | X1 != X3 | X0 != X2) )),
% 15.59/2.50    inference(definition_unfolding,[],[f37,f26,f26])).
% 15.59/2.50  
% 15.59/2.50  fof(f55,plain,(
% 15.59/2.50    ( ! [X2,X0,X3] : (r2_hidden(k4_tarski(X0,X3),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),k2_enumset1(X3,X3,X3,X3))) | X0 != X2) )),
% 15.59/2.50    inference(equality_resolution,[],[f43])).
% 15.59/2.50  
% 15.59/2.50  fof(f56,plain,(
% 15.59/2.50    ( ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),k2_enumset1(X3,X3,X3,X3)))) )),
% 15.59/2.50    inference(equality_resolution,[],[f55])).
% 15.59/2.50  
% 15.59/2.50  fof(f29,plain,(
% 15.59/2.50    ( ! [X2,X0,X8,X1] : (k4_tarski(sK4(X0,X1,X8),sK5(X0,X1,X8)) = X8 | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 15.59/2.50    inference(cnf_transformation,[],[f17])).
% 15.59/2.50  
% 15.59/2.50  fof(f52,plain,(
% 15.59/2.50    ( ! [X0,X8,X1] : (k4_tarski(sK4(X0,X1,X8),sK5(X0,X1,X8)) = X8 | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 15.59/2.50    inference(equality_resolution,[],[f29])).
% 15.59/2.50  
% 15.59/2.50  fof(f27,plain,(
% 15.59/2.50    ( ! [X2,X0,X8,X1] : (r2_hidden(sK4(X0,X1,X8),X0) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 15.59/2.50    inference(cnf_transformation,[],[f17])).
% 15.59/2.50  
% 15.59/2.50  fof(f54,plain,(
% 15.59/2.50    ( ! [X0,X8,X1] : (r2_hidden(sK4(X0,X1,X8),X0) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 15.59/2.50    inference(equality_resolution,[],[f27])).
% 15.59/2.50  
% 15.59/2.50  cnf(c_1,plain,
% 15.59/2.50      ( r2_hidden(sK0(X0,X1),X1)
% 15.59/2.50      | k2_enumset1(X0,X0,X0,X0) = X1
% 15.59/2.50      | sK0(X0,X1) = X0 ),
% 15.59/2.50      inference(cnf_transformation,[],[f40]) ).
% 15.59/2.50  
% 15.59/2.50  cnf(c_422,plain,
% 15.59/2.50      ( k2_enumset1(X0,X0,X0,X0) = X1
% 15.59/2.50      | sK0(X0,X1) = X0
% 15.59/2.50      | r2_hidden(sK0(X0,X1),X1) = iProver_top ),
% 15.59/2.50      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 15.59/2.50  
% 15.59/2.50  cnf(c_10,plain,
% 15.59/2.50      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 15.59/2.50      | r2_hidden(sK5(X1,X2,X0),X2) ),
% 15.59/2.50      inference(cnf_transformation,[],[f53]) ).
% 15.59/2.50  
% 15.59/2.50  cnf(c_413,plain,
% 15.59/2.50      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 15.59/2.50      | r2_hidden(sK5(X1,X2,X0),X2) = iProver_top ),
% 15.59/2.50      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 15.59/2.50  
% 15.59/2.50  cnf(c_3,plain,
% 15.59/2.50      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) | X0 = X1 ),
% 15.59/2.50      inference(cnf_transformation,[],[f49]) ).
% 15.59/2.50  
% 15.59/2.50  cnf(c_420,plain,
% 15.59/2.50      ( X0 = X1 | r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) != iProver_top ),
% 15.59/2.50      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 15.59/2.50  
% 15.59/2.50  cnf(c_862,plain,
% 15.59/2.50      ( sK5(X0,k2_enumset1(X1,X1,X1,X1),X2) = X1
% 15.59/2.50      | r2_hidden(X2,k2_zfmisc_1(X0,k2_enumset1(X1,X1,X1,X1))) != iProver_top ),
% 15.59/2.50      inference(superposition,[status(thm)],[c_413,c_420]) ).
% 15.59/2.50  
% 15.59/2.50  cnf(c_1738,plain,
% 15.59/2.50      ( sK5(X0,k2_enumset1(X1,X1,X1,X1),sK0(X2,k2_zfmisc_1(X0,k2_enumset1(X1,X1,X1,X1)))) = X1
% 15.59/2.50      | k2_zfmisc_1(X0,k2_enumset1(X1,X1,X1,X1)) = k2_enumset1(X2,X2,X2,X2)
% 15.59/2.50      | sK0(X2,k2_zfmisc_1(X0,k2_enumset1(X1,X1,X1,X1))) = X2 ),
% 15.59/2.50      inference(superposition,[status(thm)],[c_422,c_862]) ).
% 15.59/2.50  
% 15.59/2.50  cnf(c_15,negated_conjecture,
% 15.59/2.50      ( k2_enumset1(k4_tarski(sK6,sK7),k4_tarski(sK6,sK7),k4_tarski(sK6,sK7),k4_tarski(sK6,sK7)) != k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7)) ),
% 15.59/2.50      inference(cnf_transformation,[],[f46]) ).
% 15.59/2.50  
% 15.59/2.50  cnf(c_30027,plain,
% 15.59/2.50      ( sK5(X0,k2_enumset1(X1,X1,X1,X1),sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(X0,k2_enumset1(X1,X1,X1,X1)))) = X1
% 15.59/2.50      | k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7)) != k2_zfmisc_1(X0,k2_enumset1(X1,X1,X1,X1))
% 15.59/2.50      | sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(X0,k2_enumset1(X1,X1,X1,X1))) = k4_tarski(sK6,sK7) ),
% 15.59/2.50      inference(superposition,[status(thm)],[c_1738,c_15]) ).
% 15.59/2.50  
% 15.59/2.50  cnf(c_30509,plain,
% 15.59/2.50      ( sK5(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7),sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7)))) = sK7
% 15.59/2.50      | sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7))) = k4_tarski(sK6,sK7) ),
% 15.59/2.50      inference(equality_resolution,[status(thm)],[c_30027]) ).
% 15.59/2.50  
% 15.59/2.50  cnf(c_0,plain,
% 15.59/2.50      ( ~ r2_hidden(sK0(X0,X1),X1)
% 15.59/2.50      | k2_enumset1(X0,X0,X0,X0) = X1
% 15.59/2.50      | sK0(X0,X1) != X0 ),
% 15.59/2.50      inference(cnf_transformation,[],[f39]) ).
% 15.59/2.50  
% 15.59/2.50  cnf(c_439,plain,
% 15.59/2.50      ( ~ r2_hidden(sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7))),k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7)))
% 15.59/2.50      | k2_enumset1(k4_tarski(sK6,sK7),k4_tarski(sK6,sK7),k4_tarski(sK6,sK7),k4_tarski(sK6,sK7)) = k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7))
% 15.59/2.50      | sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7))) != k4_tarski(sK6,sK7) ),
% 15.59/2.50      inference(instantiation,[status(thm)],[c_0]) ).
% 15.59/2.50  
% 15.59/2.50  cnf(c_443,plain,
% 15.59/2.50      ( k2_enumset1(k4_tarski(sK6,sK7),k4_tarski(sK6,sK7),k4_tarski(sK6,sK7),k4_tarski(sK6,sK7)) = k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7))
% 15.59/2.50      | sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7))) != k4_tarski(sK6,sK7)
% 15.59/2.50      | r2_hidden(sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7))),k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7))) != iProver_top ),
% 15.59/2.50      inference(predicate_to_equality,[status(thm)],[c_439]) ).
% 15.59/2.50  
% 15.59/2.50  cnf(c_481,plain,
% 15.59/2.50      ( ~ r2_hidden(k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7)),k2_enumset1(X0,X0,X0,X0))
% 15.59/2.50      | k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7)) = X0 ),
% 15.59/2.50      inference(instantiation,[status(thm)],[c_3]) ).
% 15.59/2.50  
% 15.59/2.50  cnf(c_676,plain,
% 15.59/2.50      ( ~ r2_hidden(k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7)),k2_enumset1(k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7)),k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7)),k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7)),k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7))))
% 15.59/2.50      | k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7)) = k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7)) ),
% 15.59/2.50      inference(instantiation,[status(thm)],[c_481]) ).
% 15.59/2.50  
% 15.59/2.50  cnf(c_2,plain,
% 15.59/2.50      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) ),
% 15.59/2.50      inference(cnf_transformation,[],[f48]) ).
% 15.59/2.50  
% 15.59/2.50  cnf(c_906,plain,
% 15.59/2.50      ( r2_hidden(k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7)),k2_enumset1(k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7)),k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7)),k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7)),k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7)))) ),
% 15.59/2.50      inference(instantiation,[status(thm)],[c_2]) ).
% 15.59/2.50  
% 15.59/2.50  cnf(c_181,plain,
% 15.59/2.50      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 15.59/2.50      theory(equality) ).
% 15.59/2.50  
% 15.59/2.50  cnf(c_465,plain,
% 15.59/2.50      ( ~ r2_hidden(X0,X1)
% 15.59/2.50      | r2_hidden(sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7))),k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7)))
% 15.59/2.50      | k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7)) != X1
% 15.59/2.50      | sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7))) != X0 ),
% 15.59/2.50      inference(instantiation,[status(thm)],[c_181]) ).
% 15.59/2.50  
% 15.59/2.50  cnf(c_543,plain,
% 15.59/2.50      ( ~ r2_hidden(k4_tarski(sK6,sK7),X0)
% 15.59/2.50      | r2_hidden(sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7))),k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7)))
% 15.59/2.50      | k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7)) != X0
% 15.59/2.50      | sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7))) != k4_tarski(sK6,sK7) ),
% 15.59/2.50      inference(instantiation,[status(thm)],[c_465]) ).
% 15.59/2.50  
% 15.59/2.50  cnf(c_647,plain,
% 15.59/2.50      ( ~ r2_hidden(k4_tarski(sK6,sK7),k2_zfmisc_1(X0,X1))
% 15.59/2.50      | r2_hidden(sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7))),k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7)))
% 15.59/2.50      | k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7)) != k2_zfmisc_1(X0,X1)
% 15.59/2.50      | sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7))) != k4_tarski(sK6,sK7) ),
% 15.59/2.50      inference(instantiation,[status(thm)],[c_543]) ).
% 15.59/2.50  
% 15.59/2.50  cnf(c_1005,plain,
% 15.59/2.50      ( ~ r2_hidden(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7)))
% 15.59/2.50      | r2_hidden(sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7))),k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7)))
% 15.59/2.50      | k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7)) != k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7))
% 15.59/2.50      | sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7))) != k4_tarski(sK6,sK7) ),
% 15.59/2.50      inference(instantiation,[status(thm)],[c_647]) ).
% 15.59/2.50  
% 15.59/2.50  cnf(c_1006,plain,
% 15.59/2.50      ( k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7)) != k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7))
% 15.59/2.50      | sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7))) != k4_tarski(sK6,sK7)
% 15.59/2.50      | r2_hidden(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7))) != iProver_top
% 15.59/2.50      | r2_hidden(sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7))),k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7))) = iProver_top ),
% 15.59/2.50      inference(predicate_to_equality,[status(thm)],[c_1005]) ).
% 15.59/2.50  
% 15.59/2.50  cnf(c_12,plain,
% 15.59/2.50      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))) ),
% 15.59/2.50      inference(cnf_transformation,[],[f56]) ).
% 15.59/2.50  
% 15.59/2.50  cnf(c_2077,plain,
% 15.59/2.50      ( r2_hidden(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7))) ),
% 15.59/2.50      inference(instantiation,[status(thm)],[c_12]) ).
% 15.59/2.50  
% 15.59/2.50  cnf(c_2078,plain,
% 15.59/2.50      ( r2_hidden(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7))) = iProver_top ),
% 15.59/2.50      inference(predicate_to_equality,[status(thm)],[c_2077]) ).
% 15.59/2.50  
% 15.59/2.50  cnf(c_31220,plain,
% 15.59/2.50      ( sK5(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7),sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7)))) = sK7 ),
% 15.59/2.50      inference(global_propositional_subsumption,
% 15.59/2.50                [status(thm)],
% 15.59/2.50                [c_30509,c_15,c_443,c_676,c_906,c_1006,c_2078]) ).
% 15.59/2.50  
% 15.59/2.50  cnf(c_9,plain,
% 15.59/2.50      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 15.59/2.50      | k4_tarski(sK4(X1,X2,X0),sK5(X1,X2,X0)) = X0 ),
% 15.59/2.50      inference(cnf_transformation,[],[f52]) ).
% 15.59/2.50  
% 15.59/2.50  cnf(c_414,plain,
% 15.59/2.50      ( k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)) = X2
% 15.59/2.50      | r2_hidden(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 15.59/2.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 15.59/2.50  
% 15.59/2.50  cnf(c_1079,plain,
% 15.59/2.50      ( k2_enumset1(X0,X0,X0,X0) = k2_zfmisc_1(X1,X2)
% 15.59/2.50      | k4_tarski(sK4(X1,X2,sK0(X0,k2_zfmisc_1(X1,X2))),sK5(X1,X2,sK0(X0,k2_zfmisc_1(X1,X2)))) = sK0(X0,k2_zfmisc_1(X1,X2))
% 15.59/2.50      | sK0(X0,k2_zfmisc_1(X1,X2)) = X0 ),
% 15.59/2.50      inference(superposition,[status(thm)],[c_422,c_414]) ).
% 15.59/2.50  
% 15.59/2.50  cnf(c_31260,plain,
% 15.59/2.50      ( k2_enumset1(k4_tarski(sK6,sK7),k4_tarski(sK6,sK7),k4_tarski(sK6,sK7),k4_tarski(sK6,sK7)) = k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7))
% 15.59/2.50      | k4_tarski(sK4(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7),sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7)))),sK7) = sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7)))
% 15.59/2.50      | sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7))) = k4_tarski(sK6,sK7) ),
% 15.59/2.50      inference(superposition,[status(thm)],[c_31220,c_1079]) ).
% 15.59/2.50  
% 15.59/2.50  cnf(c_11,plain,
% 15.59/2.50      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 15.59/2.50      | r2_hidden(sK4(X1,X2,X0),X1) ),
% 15.59/2.50      inference(cnf_transformation,[],[f54]) ).
% 15.59/2.50  
% 15.59/2.50  cnf(c_412,plain,
% 15.59/2.50      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 15.59/2.50      | r2_hidden(sK4(X1,X2,X0),X1) = iProver_top ),
% 15.59/2.50      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 15.59/2.50  
% 15.59/2.50  cnf(c_857,plain,
% 15.59/2.50      ( sK4(k2_enumset1(X0,X0,X0,X0),X1,X2) = X0
% 15.59/2.50      | r2_hidden(X2,k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),X1)) != iProver_top ),
% 15.59/2.50      inference(superposition,[status(thm)],[c_412,c_420]) ).
% 15.59/2.50  
% 15.59/2.50  cnf(c_1384,plain,
% 15.59/2.50      ( sK4(k2_enumset1(X0,X0,X0,X0),X1,sK0(X2,k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),X1))) = X0
% 15.59/2.50      | k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),X1) = k2_enumset1(X2,X2,X2,X2)
% 15.59/2.50      | sK0(X2,k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),X1)) = X2 ),
% 15.59/2.50      inference(superposition,[status(thm)],[c_422,c_857]) ).
% 15.59/2.50  
% 15.59/2.50  cnf(c_20305,plain,
% 15.59/2.50      ( sK4(k2_enumset1(X0,X0,X0,X0),X1,sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),X1))) = X0
% 15.59/2.50      | k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7)) != k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),X1)
% 15.59/2.50      | sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),X1)) = k4_tarski(sK6,sK7) ),
% 15.59/2.50      inference(superposition,[status(thm)],[c_1384,c_15]) ).
% 15.59/2.50  
% 15.59/2.50  cnf(c_20633,plain,
% 15.59/2.50      ( sK4(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7),sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7)))) = sK6
% 15.59/2.50      | sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7))) = k4_tarski(sK6,sK7) ),
% 15.59/2.50      inference(equality_resolution,[status(thm)],[c_20305]) ).
% 15.59/2.50  
% 15.59/2.50  cnf(c_21763,plain,
% 15.59/2.50      ( sK4(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7),sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7)))) = sK6 ),
% 15.59/2.50      inference(global_propositional_subsumption,
% 15.59/2.50                [status(thm)],
% 15.59/2.50                [c_20633,c_15,c_443,c_676,c_906,c_1006,c_2078]) ).
% 15.59/2.50  
% 15.59/2.50  cnf(c_31261,plain,
% 15.59/2.50      ( k2_enumset1(k4_tarski(sK6,sK7),k4_tarski(sK6,sK7),k4_tarski(sK6,sK7),k4_tarski(sK6,sK7)) = k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7))
% 15.59/2.50      | sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7))) = k4_tarski(sK6,sK7) ),
% 15.59/2.50      inference(light_normalisation,[status(thm)],[c_31260,c_21763]) ).
% 15.59/2.50  
% 15.59/2.50  cnf(contradiction,plain,
% 15.59/2.50      ( $false ),
% 15.59/2.50      inference(minisat,
% 15.59/2.50                [status(thm)],
% 15.59/2.50                [c_31261,c_2078,c_1006,c_906,c_676,c_443,c_15]) ).
% 15.59/2.50  
% 15.59/2.50  
% 15.59/2.50  % SZS output end CNFRefutation for theBenchmark.p
% 15.59/2.50  
% 15.59/2.50  ------                               Statistics
% 15.59/2.50  
% 15.59/2.50  ------ General
% 15.59/2.50  
% 15.59/2.50  abstr_ref_over_cycles:                  0
% 15.59/2.50  abstr_ref_under_cycles:                 0
% 15.59/2.50  gc_basic_clause_elim:                   0
% 15.59/2.50  forced_gc_time:                         0
% 15.59/2.50  parsing_time:                           0.008
% 15.59/2.50  unif_index_cands_time:                  0.
% 15.59/2.50  unif_index_add_time:                    0.
% 15.59/2.50  orderings_time:                         0.
% 15.59/2.50  out_proof_time:                         0.011
% 15.59/2.50  total_time:                             1.697
% 15.59/2.50  num_of_symbols:                         43
% 15.59/2.50  num_of_terms:                           58230
% 15.59/2.50  
% 15.59/2.50  ------ Preprocessing
% 15.59/2.50  
% 15.59/2.50  num_of_splits:                          0
% 15.59/2.50  num_of_split_atoms:                     0
% 15.59/2.50  num_of_reused_defs:                     0
% 15.59/2.50  num_eq_ax_congr_red:                    34
% 15.59/2.50  num_of_sem_filtered_clauses:            1
% 15.59/2.50  num_of_subtypes:                        0
% 15.59/2.50  monotx_restored_types:                  0
% 15.59/2.50  sat_num_of_epr_types:                   0
% 15.59/2.50  sat_num_of_non_cyclic_types:            0
% 15.59/2.50  sat_guarded_non_collapsed_types:        0
% 15.59/2.50  num_pure_diseq_elim:                    0
% 15.59/2.50  simp_replaced_by:                       0
% 15.59/2.50  res_preprocessed:                       61
% 15.59/2.50  prep_upred:                             0
% 15.59/2.50  prep_unflattend:                        0
% 15.59/2.50  smt_new_axioms:                         0
% 15.59/2.50  pred_elim_cands:                        1
% 15.59/2.50  pred_elim:                              0
% 15.59/2.50  pred_elim_cl:                           0
% 15.59/2.50  pred_elim_cycles:                       1
% 15.59/2.50  merged_defs:                            0
% 15.59/2.50  merged_defs_ncl:                        0
% 15.59/2.50  bin_hyper_res:                          0
% 15.59/2.50  prep_cycles:                            3
% 15.59/2.50  pred_elim_time:                         0.
% 15.59/2.50  splitting_time:                         0.
% 15.59/2.50  sem_filter_time:                        0.
% 15.59/2.50  monotx_time:                            0.
% 15.59/2.50  subtype_inf_time:                       0.
% 15.59/2.50  
% 15.59/2.50  ------ Problem properties
% 15.59/2.50  
% 15.59/2.50  clauses:                                16
% 15.59/2.50  conjectures:                            1
% 15.59/2.50  epr:                                    0
% 15.59/2.50  horn:                                   12
% 15.59/2.50  ground:                                 1
% 15.59/2.50  unary:                                  3
% 15.59/2.50  binary:                                 6
% 15.59/2.50  lits:                                   38
% 15.59/2.50  lits_eq:                                15
% 15.59/2.50  fd_pure:                                0
% 15.59/2.50  fd_pseudo:                              0
% 15.59/2.50  fd_cond:                                0
% 15.59/2.50  fd_pseudo_cond:                         8
% 15.59/2.50  ac_symbols:                             0
% 15.59/2.50  
% 15.59/2.50  ------ Propositional Solver
% 15.59/2.50  
% 15.59/2.50  prop_solver_calls:                      25
% 15.59/2.50  prop_fast_solver_calls:                 1130
% 15.59/2.50  smt_solver_calls:                       0
% 15.59/2.50  smt_fast_solver_calls:                  0
% 15.59/2.50  prop_num_of_clauses:                    18214
% 15.59/2.50  prop_preprocess_simplified:             17769
% 15.59/2.50  prop_fo_subsumed:                       4
% 15.59/2.50  prop_solver_time:                       0.
% 15.59/2.50  smt_solver_time:                        0.
% 15.59/2.50  smt_fast_solver_time:                   0.
% 15.59/2.50  prop_fast_solver_time:                  0.
% 15.59/2.50  prop_unsat_core_time:                   0.001
% 15.59/2.50  
% 15.59/2.50  ------ QBF
% 15.59/2.50  
% 15.59/2.50  qbf_q_res:                              0
% 15.59/2.50  qbf_num_tautologies:                    0
% 15.59/2.50  qbf_prep_cycles:                        0
% 15.59/2.50  
% 15.59/2.50  ------ BMC1
% 15.59/2.50  
% 15.59/2.50  bmc1_current_bound:                     -1
% 15.59/2.50  bmc1_last_solved_bound:                 -1
% 15.59/2.50  bmc1_unsat_core_size:                   -1
% 15.59/2.50  bmc1_unsat_core_parents_size:           -1
% 15.59/2.50  bmc1_merge_next_fun:                    0
% 15.59/2.50  bmc1_unsat_core_clauses_time:           0.
% 15.59/2.50  
% 15.59/2.50  ------ Instantiation
% 15.59/2.50  
% 15.59/2.50  inst_num_of_clauses:                    2554
% 15.59/2.50  inst_num_in_passive:                    399
% 15.59/2.50  inst_num_in_active:                     961
% 15.59/2.50  inst_num_in_unprocessed:                1194
% 15.59/2.50  inst_num_of_loops:                      1100
% 15.59/2.50  inst_num_of_learning_restarts:          0
% 15.59/2.50  inst_num_moves_active_passive:          138
% 15.59/2.50  inst_lit_activity:                      0
% 15.59/2.50  inst_lit_activity_moves:                0
% 15.59/2.50  inst_num_tautologies:                   0
% 15.59/2.50  inst_num_prop_implied:                  0
% 15.59/2.50  inst_num_existing_simplified:           0
% 15.59/2.50  inst_num_eq_res_simplified:             0
% 15.59/2.50  inst_num_child_elim:                    0
% 15.59/2.50  inst_num_of_dismatching_blockings:      3851
% 15.59/2.50  inst_num_of_non_proper_insts:           4177
% 15.59/2.50  inst_num_of_duplicates:                 0
% 15.59/2.50  inst_inst_num_from_inst_to_res:         0
% 15.59/2.50  inst_dismatching_checking_time:         0.
% 15.59/2.50  
% 15.59/2.50  ------ Resolution
% 15.59/2.50  
% 15.59/2.50  res_num_of_clauses:                     0
% 15.59/2.50  res_num_in_passive:                     0
% 15.59/2.50  res_num_in_active:                      0
% 15.59/2.50  res_num_of_loops:                       64
% 15.59/2.50  res_forward_subset_subsumed:            373
% 15.59/2.50  res_backward_subset_subsumed:           6
% 15.59/2.50  res_forward_subsumed:                   0
% 15.59/2.50  res_backward_subsumed:                  0
% 15.59/2.50  res_forward_subsumption_resolution:     0
% 15.59/2.50  res_backward_subsumption_resolution:    0
% 15.59/2.50  res_clause_to_clause_subsumption:       21132
% 15.59/2.50  res_orphan_elimination:                 0
% 15.59/2.50  res_tautology_del:                      248
% 15.59/2.50  res_num_eq_res_simplified:              0
% 15.59/2.50  res_num_sel_changes:                    0
% 15.59/2.50  res_moves_from_active_to_pass:          0
% 15.59/2.50  
% 15.59/2.50  ------ Superposition
% 15.59/2.50  
% 15.59/2.50  sup_time_total:                         0.
% 15.59/2.50  sup_time_generating:                    0.
% 15.59/2.50  sup_time_sim_full:                      0.
% 15.59/2.50  sup_time_sim_immed:                     0.
% 15.59/2.50  
% 15.59/2.50  sup_num_of_clauses:                     4731
% 15.59/2.50  sup_num_in_active:                      220
% 15.59/2.50  sup_num_in_passive:                     4511
% 15.59/2.50  sup_num_of_loops:                       219
% 15.59/2.50  sup_fw_superposition:                   3703
% 15.59/2.50  sup_bw_superposition:                   1838
% 15.59/2.50  sup_immediate_simplified:               128
% 15.59/2.50  sup_given_eliminated:                   0
% 15.59/2.50  comparisons_done:                       0
% 15.59/2.50  comparisons_avoided:                    72
% 15.59/2.50  
% 15.59/2.50  ------ Simplifications
% 15.59/2.50  
% 15.59/2.50  
% 15.59/2.50  sim_fw_subset_subsumed:                 33
% 15.59/2.50  sim_bw_subset_subsumed:                 0
% 15.59/2.50  sim_fw_subsumed:                        59
% 15.59/2.50  sim_bw_subsumed:                        1
% 15.59/2.50  sim_fw_subsumption_res:                 0
% 15.59/2.50  sim_bw_subsumption_res:                 0
% 15.59/2.50  sim_tautology_del:                      3
% 15.59/2.50  sim_eq_tautology_del:                   8
% 15.59/2.50  sim_eq_res_simp:                        0
% 15.59/2.50  sim_fw_demodulated:                     33
% 15.59/2.50  sim_bw_demodulated:                     0
% 15.59/2.50  sim_light_normalised:                   7
% 15.59/2.50  sim_joinable_taut:                      0
% 15.59/2.50  sim_joinable_simp:                      0
% 15.59/2.50  sim_ac_normalised:                      0
% 15.59/2.50  sim_smt_subsumption:                    0
% 15.59/2.50  
%------------------------------------------------------------------------------
