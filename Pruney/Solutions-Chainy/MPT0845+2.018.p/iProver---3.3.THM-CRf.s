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
% DateTime   : Thu Dec  3 11:57:18 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 574 expanded)
%              Number of clauses        :   71 ( 216 expanded)
%              Number of leaves         :   15 ( 138 expanded)
%              Depth                    :   15
%              Number of atoms          :  346 (2344 expanded)
%              Number of equality atoms :  160 ( 554 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f8,plain,(
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

fof(f9,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f13,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f13])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ! [X3] :
                  ~ ( r2_hidden(X3,X2)
                    & r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f21,plain,(
    ! [X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
     => ( ! [X3] :
            ( ~ r2_hidden(X3,sK6(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK6(X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,sK6(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK6(X1),X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f11,f21])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X1),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

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

fof(f15,plain,(
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

fof(f16,plain,(
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
    inference(rectify,[],[f15])).

fof(f19,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK4(X0,X1,X8),sK5(X0,X1,X8)) = X8
        & r2_hidden(sK5(X0,X1,X8),X1)
        & r2_hidden(sK4(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X6,X7] :
          ( k4_tarski(X6,X7) = X3
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)) = X3
        & r2_hidden(sK3(X0,X1,X2),X1)
        & r2_hidden(sK2(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
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

fof(f20,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f16,f19,f18,f17])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k2_zfmisc_1(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f6,conjecture,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( r1_xboole_0(X1,X0)
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ~ ( ! [X1] :
              ~ ( r1_xboole_0(X1,X0)
                & r2_hidden(X1,X0) )
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f6])).

fof(f12,plain,(
    ? [X0] :
      ( ! [X1] :
          ( ~ r1_xboole_0(X1,X0)
          | ~ r2_hidden(X1,X0) )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f23,plain,
    ( ? [X0] :
        ( ! [X1] :
            ( ~ r1_xboole_0(X1,X0)
            | ~ r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 )
   => ( ! [X1] :
          ( ~ r1_xboole_0(X1,sK7)
          | ~ r2_hidden(X1,sK7) )
      & k1_xboole_0 != sK7 ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ! [X1] :
        ( ~ r1_xboole_0(X1,sK7)
        | ~ r2_hidden(X1,sK7) )
    & k1_xboole_0 != sK7 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f12,f23])).

fof(f41,plain,(
    ! [X1] :
      ( ~ r1_xboole_0(X1,sK7)
      | ~ r2_hidden(X1,sK7) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k2_zfmisc_1(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,sK6(X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f30,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK5(X0,X1,X8),X1)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f45,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK5(X0,X1,X8),X1)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f30])).

fof(f29,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK4(X0,X1,X8),X0)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f46,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK4(X0,X1,X8),X0)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f29])).

fof(f2,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( r2_hidden(X0,X2)
        & r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f40,plain,(
    k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_600,plain,
    ( r2_hidden(sK0(X0,X1),X1) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK6(X1),X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_587,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(sK6(X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1026,plain,
    ( r2_hidden(sK6(X0),X0) = iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_600,c_587])).

cnf(c_6,plain,
    ( r2_hidden(sK3(X0,X1,X2),X1)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k2_zfmisc_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_595,plain,
    ( k2_zfmisc_1(X0,X1) = X2
    | r2_hidden(sK3(X0,X1,X2),X1) = iProver_top
    | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_15,negated_conjecture,
    ( ~ r2_hidden(X0,sK7)
    | ~ r1_xboole_0(X0,sK7) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_586,plain,
    ( r2_hidden(X0,sK7) != iProver_top
    | r1_xboole_0(X0,sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2406,plain,
    ( k2_zfmisc_1(X0,sK7) = X1
    | r2_hidden(sK1(X0,sK7,X1),X1) = iProver_top
    | r1_xboole_0(sK3(X0,sK7,X1),sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_595,c_586])).

cnf(c_4939,plain,
    ( k2_zfmisc_1(X0,sK7) = X1
    | r2_hidden(sK1(X0,sK7,X1),X1) = iProver_top
    | r2_hidden(sK6(sK7),sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_1026,c_2406])).

cnf(c_310,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_319,plain,
    ( sK7 = sK7 ),
    inference(instantiation,[status(thm)],[c_310])).

cnf(c_311,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_817,plain,
    ( k2_zfmisc_1(X0,X1) != X2
    | sK7 != X2
    | sK7 = k2_zfmisc_1(X0,X1) ),
    inference(instantiation,[status(thm)],[c_311])).

cnf(c_818,plain,
    ( k2_zfmisc_1(sK7,sK7) != sK7
    | sK7 = k2_zfmisc_1(sK7,sK7)
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_817])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_1579,plain,
    ( ~ r2_hidden(sK6(X0),X0)
    | ~ r2_hidden(sK6(X0),X1)
    | ~ r1_xboole_0(X1,X0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1586,plain,
    ( r2_hidden(sK6(X0),X0) != iProver_top
    | r2_hidden(sK6(X0),X1) != iProver_top
    | r1_xboole_0(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1579])).

cnf(c_1588,plain,
    ( r2_hidden(sK6(sK7),sK7) != iProver_top
    | r1_xboole_0(sK7,sK7) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1586])).

cnf(c_312,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3720,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(k2_zfmisc_1(X2,X3),X4)
    | X1 != X4
    | X0 != k2_zfmisc_1(X2,X3) ),
    inference(instantiation,[status(thm)],[c_312])).

cnf(c_3721,plain,
    ( X0 != X1
    | X2 != k2_zfmisc_1(X3,X4)
    | r1_xboole_0(X2,X0) = iProver_top
    | r1_xboole_0(k2_zfmisc_1(X3,X4),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3720])).

cnf(c_3723,plain,
    ( sK7 != k2_zfmisc_1(sK7,sK7)
    | sK7 != sK7
    | r1_xboole_0(k2_zfmisc_1(sK7,sK7),sK7) != iProver_top
    | r1_xboole_0(sK7,sK7) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3721])).

cnf(c_7,plain,
    ( r2_hidden(sK2(X0,X1,X2),X0)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k2_zfmisc_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_594,plain,
    ( k2_zfmisc_1(X0,X1) = X2
    | r2_hidden(sK2(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2074,plain,
    ( k2_zfmisc_1(X0,X1) = sK7
    | r2_hidden(sK2(X0,X1,sK7),X0) = iProver_top
    | r1_xboole_0(sK1(X0,X1,sK7),sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_594,c_586])).

cnf(c_4936,plain,
    ( k2_zfmisc_1(X0,X1) = sK7
    | r2_hidden(sK2(X0,X1,sK7),X0) = iProver_top
    | r2_hidden(sK6(sK7),sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_1026,c_2074])).

cnf(c_8866,plain,
    ( k2_zfmisc_1(sK7,X0) = sK7
    | r2_hidden(sK6(sK7),sK7) = iProver_top
    | r1_xboole_0(sK2(sK7,X0,sK7),sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_4936,c_586])).

cnf(c_1635,plain,
    ( ~ r2_hidden(sK6(sK7),sK7)
    | ~ r1_xboole_0(sK6(sK7),sK7) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1638,plain,
    ( r2_hidden(sK6(sK7),sK7) != iProver_top
    | r1_xboole_0(sK6(sK7),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1635])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_599,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,sK6(X1)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_588,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r2_hidden(X2,sK6(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_908,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(sK0(sK6(X1),X2),X1) != iProver_top
    | r1_xboole_0(sK6(X1),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_599,c_588])).

cnf(c_9031,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_xboole_0(sK6(X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_600,c_908])).

cnf(c_9533,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r1_xboole_0(sK6(X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1026,c_9031])).

cnf(c_9641,plain,
    ( r1_xboole_0(sK6(sK7),sK7) = iProver_top
    | r1_xboole_0(sK7,sK7) = iProver_top ),
    inference(instantiation,[status(thm)],[c_9533])).

cnf(c_9689,plain,
    ( k2_zfmisc_1(sK7,X0) = sK7
    | r1_xboole_0(sK2(sK7,X0,sK7),sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8866,c_1588,c_1638,c_9641])).

cnf(c_9699,plain,
    ( k2_zfmisc_1(sK7,X0) = sK7
    | r2_hidden(sK6(sK7),sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_1026,c_9689])).

cnf(c_9718,plain,
    ( k2_zfmisc_1(sK7,X0) = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9699,c_1588,c_1638,c_9641])).

cnf(c_9720,plain,
    ( k2_zfmisc_1(sK7,sK7) = sK7 ),
    inference(instantiation,[status(thm)],[c_9718])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(sK5(X1,X2,X0),X2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_591,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(sK5(X1,X2,X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(sK4(X1,X2,X0),X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_590,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(sK4(X1,X2,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_598,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_xboole_0(k2_tarski(X0,X2),X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_589,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_xboole_0(k2_tarski(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_743,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_598,c_589])).

cnf(c_844,plain,
    ( r2_hidden(X0,k2_zfmisc_1(k1_xboole_0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_590,c_743])).

cnf(c_1551,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,k2_zfmisc_1(k1_xboole_0,X2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_591,c_844])).

cnf(c_2981,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,k2_zfmisc_1(X2,k2_zfmisc_1(k1_xboole_0,X3)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_591,c_1551])).

cnf(c_4195,plain,
    ( r1_xboole_0(k2_zfmisc_1(X0,k2_zfmisc_1(X1,k2_zfmisc_1(k1_xboole_0,X2))),X3) = iProver_top ),
    inference(superposition,[status(thm)],[c_599,c_2981])).

cnf(c_9766,plain,
    ( r1_xboole_0(k2_zfmisc_1(X0,sK7),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_9718,c_4195])).

cnf(c_9808,plain,
    ( r1_xboole_0(k2_zfmisc_1(sK7,sK7),sK7) = iProver_top ),
    inference(instantiation,[status(thm)],[c_9766])).

cnf(c_9846,plain,
    ( r2_hidden(sK1(X0,sK7,X1),X1) = iProver_top
    | k2_zfmisc_1(X0,sK7) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4939,c_1588,c_1638,c_9641])).

cnf(c_9847,plain,
    ( k2_zfmisc_1(X0,sK7) = X1
    | r2_hidden(sK1(X0,sK7,X1),X1) = iProver_top ),
    inference(renaming,[status(thm)],[c_9846])).

cnf(c_9858,plain,
    ( k2_zfmisc_1(X0,sK7) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_9847,c_743])).

cnf(c_9951,plain,
    ( k2_zfmisc_1(sK7,sK7) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_9858])).

cnf(c_730,plain,
    ( X0 != X1
    | k1_xboole_0 != X1
    | k1_xboole_0 = X0 ),
    inference(instantiation,[status(thm)],[c_311])).

cnf(c_768,plain,
    ( X0 != k2_zfmisc_1(X1,X2)
    | k1_xboole_0 = X0
    | k1_xboole_0 != k2_zfmisc_1(X1,X2) ),
    inference(instantiation,[status(thm)],[c_730])).

cnf(c_769,plain,
    ( sK7 != k2_zfmisc_1(sK7,sK7)
    | k1_xboole_0 != k2_zfmisc_1(sK7,sK7)
    | k1_xboole_0 = sK7 ),
    inference(instantiation,[status(thm)],[c_768])).

cnf(c_736,plain,
    ( X0 != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_730])).

cnf(c_747,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = k2_zfmisc_1(X0,X1)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_736])).

cnf(c_751,plain,
    ( k2_zfmisc_1(sK7,sK7) != k1_xboole_0
    | k1_xboole_0 = k2_zfmisc_1(sK7,sK7)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_747])).

cnf(c_729,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_310])).

cnf(c_16,negated_conjecture,
    ( k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f40])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9951,c_9720,c_818,c_769,c_751,c_729,c_319,c_16])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:02:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.17/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/0.98  
% 2.17/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.17/0.98  
% 2.17/0.98  ------  iProver source info
% 2.17/0.98  
% 2.17/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.17/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.17/0.98  git: non_committed_changes: false
% 2.17/0.98  git: last_make_outside_of_git: false
% 2.17/0.98  
% 2.17/0.98  ------ 
% 2.17/0.98  
% 2.17/0.98  ------ Input Options
% 2.17/0.98  
% 2.17/0.98  --out_options                           all
% 2.17/0.98  --tptp_safe_out                         true
% 2.17/0.98  --problem_path                          ""
% 2.17/0.98  --include_path                          ""
% 2.17/0.98  --clausifier                            res/vclausify_rel
% 2.17/0.98  --clausifier_options                    --mode clausify
% 2.17/0.98  --stdin                                 false
% 2.17/0.98  --stats_out                             all
% 2.17/0.98  
% 2.17/0.98  ------ General Options
% 2.17/0.98  
% 2.17/0.98  --fof                                   false
% 2.17/0.98  --time_out_real                         305.
% 2.17/0.98  --time_out_virtual                      -1.
% 2.17/0.98  --symbol_type_check                     false
% 2.17/0.98  --clausify_out                          false
% 2.17/0.98  --sig_cnt_out                           false
% 2.17/0.98  --trig_cnt_out                          false
% 2.17/0.98  --trig_cnt_out_tolerance                1.
% 2.17/0.98  --trig_cnt_out_sk_spl                   false
% 2.17/0.98  --abstr_cl_out                          false
% 2.17/0.98  
% 2.17/0.98  ------ Global Options
% 2.17/0.98  
% 2.17/0.98  --schedule                              default
% 2.17/0.98  --add_important_lit                     false
% 2.17/0.98  --prop_solver_per_cl                    1000
% 2.17/0.98  --min_unsat_core                        false
% 2.17/0.98  --soft_assumptions                      false
% 2.17/0.98  --soft_lemma_size                       3
% 2.17/0.98  --prop_impl_unit_size                   0
% 2.17/0.98  --prop_impl_unit                        []
% 2.17/0.98  --share_sel_clauses                     true
% 2.17/0.98  --reset_solvers                         false
% 2.17/0.98  --bc_imp_inh                            [conj_cone]
% 2.17/0.98  --conj_cone_tolerance                   3.
% 2.17/0.98  --extra_neg_conj                        none
% 2.17/0.98  --large_theory_mode                     true
% 2.17/0.98  --prolific_symb_bound                   200
% 2.17/0.98  --lt_threshold                          2000
% 2.17/0.98  --clause_weak_htbl                      true
% 2.17/0.98  --gc_record_bc_elim                     false
% 2.17/0.98  
% 2.17/0.98  ------ Preprocessing Options
% 2.17/0.98  
% 2.17/0.98  --preprocessing_flag                    true
% 2.17/0.98  --time_out_prep_mult                    0.1
% 2.17/0.98  --splitting_mode                        input
% 2.17/0.98  --splitting_grd                         true
% 2.17/0.98  --splitting_cvd                         false
% 2.17/0.98  --splitting_cvd_svl                     false
% 2.17/0.98  --splitting_nvd                         32
% 2.17/0.98  --sub_typing                            true
% 2.17/0.98  --prep_gs_sim                           true
% 2.17/0.98  --prep_unflatten                        true
% 2.17/0.98  --prep_res_sim                          true
% 2.17/0.98  --prep_upred                            true
% 2.17/0.98  --prep_sem_filter                       exhaustive
% 2.17/0.98  --prep_sem_filter_out                   false
% 2.17/0.98  --pred_elim                             true
% 2.17/0.98  --res_sim_input                         true
% 2.17/0.98  --eq_ax_congr_red                       true
% 2.17/0.98  --pure_diseq_elim                       true
% 2.17/0.98  --brand_transform                       false
% 2.17/0.98  --non_eq_to_eq                          false
% 2.17/0.98  --prep_def_merge                        true
% 2.17/0.98  --prep_def_merge_prop_impl              false
% 2.17/0.98  --prep_def_merge_mbd                    true
% 2.17/0.98  --prep_def_merge_tr_red                 false
% 2.17/0.98  --prep_def_merge_tr_cl                  false
% 2.17/0.98  --smt_preprocessing                     true
% 2.17/0.98  --smt_ac_axioms                         fast
% 2.17/0.98  --preprocessed_out                      false
% 2.17/0.98  --preprocessed_stats                    false
% 2.17/0.98  
% 2.17/0.98  ------ Abstraction refinement Options
% 2.17/0.98  
% 2.17/0.98  --abstr_ref                             []
% 2.17/0.98  --abstr_ref_prep                        false
% 2.17/0.98  --abstr_ref_until_sat                   false
% 2.17/0.98  --abstr_ref_sig_restrict                funpre
% 2.17/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.17/0.98  --abstr_ref_under                       []
% 2.17/0.98  
% 2.17/0.98  ------ SAT Options
% 2.17/0.98  
% 2.17/0.98  --sat_mode                              false
% 2.17/0.98  --sat_fm_restart_options                ""
% 2.17/0.98  --sat_gr_def                            false
% 2.17/0.98  --sat_epr_types                         true
% 2.17/0.98  --sat_non_cyclic_types                  false
% 2.17/0.98  --sat_finite_models                     false
% 2.17/0.98  --sat_fm_lemmas                         false
% 2.17/0.98  --sat_fm_prep                           false
% 2.17/0.98  --sat_fm_uc_incr                        true
% 2.17/0.98  --sat_out_model                         small
% 2.17/0.98  --sat_out_clauses                       false
% 2.17/0.98  
% 2.17/0.98  ------ QBF Options
% 2.17/0.98  
% 2.17/0.98  --qbf_mode                              false
% 2.17/0.98  --qbf_elim_univ                         false
% 2.17/0.98  --qbf_dom_inst                          none
% 2.17/0.98  --qbf_dom_pre_inst                      false
% 2.17/0.98  --qbf_sk_in                             false
% 2.17/0.98  --qbf_pred_elim                         true
% 2.17/0.98  --qbf_split                             512
% 2.17/0.98  
% 2.17/0.98  ------ BMC1 Options
% 2.17/0.98  
% 2.17/0.98  --bmc1_incremental                      false
% 2.17/0.98  --bmc1_axioms                           reachable_all
% 2.17/0.98  --bmc1_min_bound                        0
% 2.17/0.98  --bmc1_max_bound                        -1
% 2.17/0.98  --bmc1_max_bound_default                -1
% 2.17/0.98  --bmc1_symbol_reachability              true
% 2.17/0.98  --bmc1_property_lemmas                  false
% 2.17/0.98  --bmc1_k_induction                      false
% 2.17/0.98  --bmc1_non_equiv_states                 false
% 2.17/0.98  --bmc1_deadlock                         false
% 2.17/0.98  --bmc1_ucm                              false
% 2.17/0.98  --bmc1_add_unsat_core                   none
% 2.17/0.98  --bmc1_unsat_core_children              false
% 2.17/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.17/0.98  --bmc1_out_stat                         full
% 2.17/0.98  --bmc1_ground_init                      false
% 2.17/0.98  --bmc1_pre_inst_next_state              false
% 2.17/0.98  --bmc1_pre_inst_state                   false
% 2.17/0.98  --bmc1_pre_inst_reach_state             false
% 2.17/0.98  --bmc1_out_unsat_core                   false
% 2.17/0.98  --bmc1_aig_witness_out                  false
% 2.17/0.98  --bmc1_verbose                          false
% 2.17/0.98  --bmc1_dump_clauses_tptp                false
% 2.17/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.17/0.98  --bmc1_dump_file                        -
% 2.17/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.17/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.17/0.98  --bmc1_ucm_extend_mode                  1
% 2.17/0.98  --bmc1_ucm_init_mode                    2
% 2.17/0.98  --bmc1_ucm_cone_mode                    none
% 2.17/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.17/0.98  --bmc1_ucm_relax_model                  4
% 2.17/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.17/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.17/0.98  --bmc1_ucm_layered_model                none
% 2.17/0.98  --bmc1_ucm_max_lemma_size               10
% 2.17/0.98  
% 2.17/0.98  ------ AIG Options
% 2.17/0.98  
% 2.17/0.98  --aig_mode                              false
% 2.17/0.98  
% 2.17/0.98  ------ Instantiation Options
% 2.17/0.98  
% 2.17/0.98  --instantiation_flag                    true
% 2.17/0.98  --inst_sos_flag                         false
% 2.17/0.98  --inst_sos_phase                        true
% 2.17/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.17/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.17/0.98  --inst_lit_sel_side                     num_symb
% 2.17/0.98  --inst_solver_per_active                1400
% 2.17/0.98  --inst_solver_calls_frac                1.
% 2.17/0.98  --inst_passive_queue_type               priority_queues
% 2.17/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.17/0.98  --inst_passive_queues_freq              [25;2]
% 2.17/0.98  --inst_dismatching                      true
% 2.17/0.98  --inst_eager_unprocessed_to_passive     true
% 2.17/0.98  --inst_prop_sim_given                   true
% 2.17/0.98  --inst_prop_sim_new                     false
% 2.17/0.98  --inst_subs_new                         false
% 2.17/0.98  --inst_eq_res_simp                      false
% 2.17/0.98  --inst_subs_given                       false
% 2.17/0.98  --inst_orphan_elimination               true
% 2.17/0.98  --inst_learning_loop_flag               true
% 2.17/0.98  --inst_learning_start                   3000
% 2.17/0.98  --inst_learning_factor                  2
% 2.17/0.98  --inst_start_prop_sim_after_learn       3
% 2.17/0.98  --inst_sel_renew                        solver
% 2.17/0.98  --inst_lit_activity_flag                true
% 2.17/0.98  --inst_restr_to_given                   false
% 2.17/0.98  --inst_activity_threshold               500
% 2.17/0.98  --inst_out_proof                        true
% 2.17/0.98  
% 2.17/0.98  ------ Resolution Options
% 2.17/0.98  
% 2.17/0.98  --resolution_flag                       true
% 2.17/0.98  --res_lit_sel                           adaptive
% 2.17/0.98  --res_lit_sel_side                      none
% 2.17/0.98  --res_ordering                          kbo
% 2.17/0.98  --res_to_prop_solver                    active
% 2.17/0.98  --res_prop_simpl_new                    false
% 2.17/0.98  --res_prop_simpl_given                  true
% 2.17/0.98  --res_passive_queue_type                priority_queues
% 2.17/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.17/0.98  --res_passive_queues_freq               [15;5]
% 2.17/0.98  --res_forward_subs                      full
% 2.17/0.98  --res_backward_subs                     full
% 2.17/0.98  --res_forward_subs_resolution           true
% 2.17/0.98  --res_backward_subs_resolution          true
% 2.17/0.98  --res_orphan_elimination                true
% 2.17/0.98  --res_time_limit                        2.
% 2.17/0.98  --res_out_proof                         true
% 2.17/0.98  
% 2.17/0.98  ------ Superposition Options
% 2.17/0.98  
% 2.17/0.98  --superposition_flag                    true
% 2.17/0.98  --sup_passive_queue_type                priority_queues
% 2.17/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.17/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.17/0.98  --demod_completeness_check              fast
% 2.17/0.98  --demod_use_ground                      true
% 2.17/0.98  --sup_to_prop_solver                    passive
% 2.17/0.98  --sup_prop_simpl_new                    true
% 2.17/0.98  --sup_prop_simpl_given                  true
% 2.17/0.98  --sup_fun_splitting                     false
% 2.17/0.98  --sup_smt_interval                      50000
% 2.17/0.98  
% 2.17/0.98  ------ Superposition Simplification Setup
% 2.17/0.98  
% 2.17/0.98  --sup_indices_passive                   []
% 2.17/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.17/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.17/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.17/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.17/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.17/0.98  --sup_full_bw                           [BwDemod]
% 2.17/0.98  --sup_immed_triv                        [TrivRules]
% 2.17/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.17/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.17/0.98  --sup_immed_bw_main                     []
% 2.17/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.17/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.17/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.17/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.17/0.98  
% 2.17/0.98  ------ Combination Options
% 2.17/0.98  
% 2.17/0.98  --comb_res_mult                         3
% 2.17/0.98  --comb_sup_mult                         2
% 2.17/0.98  --comb_inst_mult                        10
% 2.17/0.98  
% 2.17/0.98  ------ Debug Options
% 2.17/0.98  
% 2.17/0.98  --dbg_backtrace                         false
% 2.17/0.98  --dbg_dump_prop_clauses                 false
% 2.17/0.98  --dbg_dump_prop_clauses_file            -
% 2.17/0.98  --dbg_out_stat                          false
% 2.17/0.98  ------ Parsing...
% 2.17/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.17/0.98  
% 2.17/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.17/0.98  
% 2.17/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.17/0.98  
% 2.17/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.17/0.98  ------ Proving...
% 2.17/0.98  ------ Problem Properties 
% 2.17/0.98  
% 2.17/0.98  
% 2.17/0.98  clauses                                 17
% 2.17/0.98  conjectures                             2
% 2.17/0.98  EPR                                     4
% 2.17/0.98  Horn                                    12
% 2.17/0.98  unary                                   2
% 2.17/0.98  binary                                  8
% 2.17/0.98  lits                                    41
% 2.17/0.98  lits eq                                 8
% 2.17/0.98  fd_pure                                 0
% 2.17/0.98  fd_pseudo                               0
% 2.17/0.98  fd_cond                                 0
% 2.17/0.98  fd_pseudo_cond                          4
% 2.17/0.98  AC symbols                              0
% 2.17/0.98  
% 2.17/0.98  ------ Schedule dynamic 5 is on 
% 2.17/0.98  
% 2.17/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.17/0.98  
% 2.17/0.98  
% 2.17/0.98  ------ 
% 2.17/0.98  Current options:
% 2.17/0.98  ------ 
% 2.17/0.98  
% 2.17/0.98  ------ Input Options
% 2.17/0.98  
% 2.17/0.98  --out_options                           all
% 2.17/0.98  --tptp_safe_out                         true
% 2.17/0.98  --problem_path                          ""
% 2.17/0.98  --include_path                          ""
% 2.17/0.98  --clausifier                            res/vclausify_rel
% 2.17/0.98  --clausifier_options                    --mode clausify
% 2.17/0.98  --stdin                                 false
% 2.17/0.98  --stats_out                             all
% 2.17/0.98  
% 2.17/0.98  ------ General Options
% 2.17/0.98  
% 2.17/0.98  --fof                                   false
% 2.17/0.98  --time_out_real                         305.
% 2.17/0.98  --time_out_virtual                      -1.
% 2.17/0.98  --symbol_type_check                     false
% 2.17/0.98  --clausify_out                          false
% 2.17/0.98  --sig_cnt_out                           false
% 2.17/0.98  --trig_cnt_out                          false
% 2.17/0.98  --trig_cnt_out_tolerance                1.
% 2.17/0.98  --trig_cnt_out_sk_spl                   false
% 2.17/0.98  --abstr_cl_out                          false
% 2.17/0.98  
% 2.17/0.98  ------ Global Options
% 2.17/0.98  
% 2.17/0.98  --schedule                              default
% 2.17/0.98  --add_important_lit                     false
% 2.17/0.98  --prop_solver_per_cl                    1000
% 2.17/0.98  --min_unsat_core                        false
% 2.17/0.98  --soft_assumptions                      false
% 2.17/0.98  --soft_lemma_size                       3
% 2.17/0.98  --prop_impl_unit_size                   0
% 2.17/0.98  --prop_impl_unit                        []
% 2.17/0.98  --share_sel_clauses                     true
% 2.17/0.98  --reset_solvers                         false
% 2.17/0.98  --bc_imp_inh                            [conj_cone]
% 2.17/0.98  --conj_cone_tolerance                   3.
% 2.17/0.98  --extra_neg_conj                        none
% 2.17/0.98  --large_theory_mode                     true
% 2.17/0.98  --prolific_symb_bound                   200
% 2.17/0.98  --lt_threshold                          2000
% 2.17/0.98  --clause_weak_htbl                      true
% 2.17/0.98  --gc_record_bc_elim                     false
% 2.17/0.98  
% 2.17/0.98  ------ Preprocessing Options
% 2.17/0.98  
% 2.17/0.98  --preprocessing_flag                    true
% 2.17/0.98  --time_out_prep_mult                    0.1
% 2.17/0.98  --splitting_mode                        input
% 2.17/0.98  --splitting_grd                         true
% 2.17/0.98  --splitting_cvd                         false
% 2.17/0.98  --splitting_cvd_svl                     false
% 2.17/0.98  --splitting_nvd                         32
% 2.17/0.98  --sub_typing                            true
% 2.17/0.98  --prep_gs_sim                           true
% 2.17/0.98  --prep_unflatten                        true
% 2.17/0.98  --prep_res_sim                          true
% 2.17/0.98  --prep_upred                            true
% 2.17/0.98  --prep_sem_filter                       exhaustive
% 2.17/0.98  --prep_sem_filter_out                   false
% 2.17/0.98  --pred_elim                             true
% 2.17/0.98  --res_sim_input                         true
% 2.17/0.98  --eq_ax_congr_red                       true
% 2.17/0.98  --pure_diseq_elim                       true
% 2.17/0.98  --brand_transform                       false
% 2.17/0.98  --non_eq_to_eq                          false
% 2.17/0.98  --prep_def_merge                        true
% 2.17/0.98  --prep_def_merge_prop_impl              false
% 2.17/0.98  --prep_def_merge_mbd                    true
% 2.17/0.98  --prep_def_merge_tr_red                 false
% 2.17/0.98  --prep_def_merge_tr_cl                  false
% 2.17/0.98  --smt_preprocessing                     true
% 2.17/0.98  --smt_ac_axioms                         fast
% 2.17/0.98  --preprocessed_out                      false
% 2.17/0.98  --preprocessed_stats                    false
% 2.17/0.98  
% 2.17/0.98  ------ Abstraction refinement Options
% 2.17/0.98  
% 2.17/0.98  --abstr_ref                             []
% 2.17/0.98  --abstr_ref_prep                        false
% 2.17/0.98  --abstr_ref_until_sat                   false
% 2.17/0.98  --abstr_ref_sig_restrict                funpre
% 2.17/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.17/0.98  --abstr_ref_under                       []
% 2.17/0.98  
% 2.17/0.98  ------ SAT Options
% 2.17/0.98  
% 2.17/0.98  --sat_mode                              false
% 2.17/0.98  --sat_fm_restart_options                ""
% 2.17/0.98  --sat_gr_def                            false
% 2.17/0.98  --sat_epr_types                         true
% 2.17/0.98  --sat_non_cyclic_types                  false
% 2.17/0.98  --sat_finite_models                     false
% 2.17/0.98  --sat_fm_lemmas                         false
% 2.17/0.98  --sat_fm_prep                           false
% 2.17/0.98  --sat_fm_uc_incr                        true
% 2.17/0.98  --sat_out_model                         small
% 2.17/0.98  --sat_out_clauses                       false
% 2.17/0.98  
% 2.17/0.98  ------ QBF Options
% 2.17/0.98  
% 2.17/0.98  --qbf_mode                              false
% 2.17/0.98  --qbf_elim_univ                         false
% 2.17/0.98  --qbf_dom_inst                          none
% 2.17/0.98  --qbf_dom_pre_inst                      false
% 2.17/0.98  --qbf_sk_in                             false
% 2.17/0.98  --qbf_pred_elim                         true
% 2.17/0.98  --qbf_split                             512
% 2.17/0.98  
% 2.17/0.98  ------ BMC1 Options
% 2.17/0.98  
% 2.17/0.98  --bmc1_incremental                      false
% 2.17/0.98  --bmc1_axioms                           reachable_all
% 2.17/0.98  --bmc1_min_bound                        0
% 2.17/0.98  --bmc1_max_bound                        -1
% 2.17/0.98  --bmc1_max_bound_default                -1
% 2.17/0.98  --bmc1_symbol_reachability              true
% 2.17/0.98  --bmc1_property_lemmas                  false
% 2.17/0.98  --bmc1_k_induction                      false
% 2.17/0.98  --bmc1_non_equiv_states                 false
% 2.17/0.98  --bmc1_deadlock                         false
% 2.17/0.98  --bmc1_ucm                              false
% 2.17/0.98  --bmc1_add_unsat_core                   none
% 2.17/0.98  --bmc1_unsat_core_children              false
% 2.17/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.17/0.98  --bmc1_out_stat                         full
% 2.17/0.98  --bmc1_ground_init                      false
% 2.17/0.98  --bmc1_pre_inst_next_state              false
% 2.17/0.98  --bmc1_pre_inst_state                   false
% 2.17/0.98  --bmc1_pre_inst_reach_state             false
% 2.17/0.98  --bmc1_out_unsat_core                   false
% 2.17/0.98  --bmc1_aig_witness_out                  false
% 2.17/0.98  --bmc1_verbose                          false
% 2.17/0.98  --bmc1_dump_clauses_tptp                false
% 2.17/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.17/0.98  --bmc1_dump_file                        -
% 2.17/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.17/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.17/0.98  --bmc1_ucm_extend_mode                  1
% 2.17/0.98  --bmc1_ucm_init_mode                    2
% 2.17/0.98  --bmc1_ucm_cone_mode                    none
% 2.17/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.17/0.98  --bmc1_ucm_relax_model                  4
% 2.17/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.17/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.17/0.98  --bmc1_ucm_layered_model                none
% 2.17/0.98  --bmc1_ucm_max_lemma_size               10
% 2.17/0.98  
% 2.17/0.98  ------ AIG Options
% 2.17/0.98  
% 2.17/0.98  --aig_mode                              false
% 2.17/0.98  
% 2.17/0.98  ------ Instantiation Options
% 2.17/0.98  
% 2.17/0.98  --instantiation_flag                    true
% 2.17/0.98  --inst_sos_flag                         false
% 2.17/0.98  --inst_sos_phase                        true
% 2.17/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.17/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.17/0.98  --inst_lit_sel_side                     none
% 2.17/0.98  --inst_solver_per_active                1400
% 2.17/0.98  --inst_solver_calls_frac                1.
% 2.17/0.98  --inst_passive_queue_type               priority_queues
% 2.17/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.17/0.98  --inst_passive_queues_freq              [25;2]
% 2.17/0.98  --inst_dismatching                      true
% 2.17/0.98  --inst_eager_unprocessed_to_passive     true
% 2.17/0.98  --inst_prop_sim_given                   true
% 2.17/0.98  --inst_prop_sim_new                     false
% 2.17/0.98  --inst_subs_new                         false
% 2.17/0.98  --inst_eq_res_simp                      false
% 2.17/0.98  --inst_subs_given                       false
% 2.17/0.98  --inst_orphan_elimination               true
% 2.17/0.98  --inst_learning_loop_flag               true
% 2.17/0.98  --inst_learning_start                   3000
% 2.17/0.98  --inst_learning_factor                  2
% 2.17/0.98  --inst_start_prop_sim_after_learn       3
% 2.17/0.98  --inst_sel_renew                        solver
% 2.17/0.98  --inst_lit_activity_flag                true
% 2.17/0.98  --inst_restr_to_given                   false
% 2.17/0.98  --inst_activity_threshold               500
% 2.17/0.98  --inst_out_proof                        true
% 2.17/0.98  
% 2.17/0.98  ------ Resolution Options
% 2.17/0.98  
% 2.17/0.98  --resolution_flag                       false
% 2.17/0.98  --res_lit_sel                           adaptive
% 2.17/0.98  --res_lit_sel_side                      none
% 2.17/0.98  --res_ordering                          kbo
% 2.17/0.98  --res_to_prop_solver                    active
% 2.17/0.98  --res_prop_simpl_new                    false
% 2.17/0.98  --res_prop_simpl_given                  true
% 2.17/0.98  --res_passive_queue_type                priority_queues
% 2.17/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.17/0.98  --res_passive_queues_freq               [15;5]
% 2.17/0.98  --res_forward_subs                      full
% 2.17/0.98  --res_backward_subs                     full
% 2.17/0.98  --res_forward_subs_resolution           true
% 2.17/0.98  --res_backward_subs_resolution          true
% 2.17/0.98  --res_orphan_elimination                true
% 2.17/0.98  --res_time_limit                        2.
% 2.17/0.98  --res_out_proof                         true
% 2.17/0.98  
% 2.17/0.98  ------ Superposition Options
% 2.17/0.98  
% 2.17/0.98  --superposition_flag                    true
% 2.17/0.98  --sup_passive_queue_type                priority_queues
% 2.17/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.17/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.17/0.98  --demod_completeness_check              fast
% 2.17/0.98  --demod_use_ground                      true
% 2.17/0.98  --sup_to_prop_solver                    passive
% 2.17/0.98  --sup_prop_simpl_new                    true
% 2.17/0.98  --sup_prop_simpl_given                  true
% 2.17/0.98  --sup_fun_splitting                     false
% 2.17/0.98  --sup_smt_interval                      50000
% 2.17/0.98  
% 2.17/0.98  ------ Superposition Simplification Setup
% 2.17/0.98  
% 2.17/0.98  --sup_indices_passive                   []
% 2.17/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.17/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.17/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.17/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.17/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.17/0.98  --sup_full_bw                           [BwDemod]
% 2.17/0.98  --sup_immed_triv                        [TrivRules]
% 2.17/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.17/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.17/0.98  --sup_immed_bw_main                     []
% 2.17/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.17/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.17/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.17/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.17/0.98  
% 2.17/0.98  ------ Combination Options
% 2.17/0.98  
% 2.17/0.98  --comb_res_mult                         3
% 2.17/0.98  --comb_sup_mult                         2
% 2.17/0.98  --comb_inst_mult                        10
% 2.17/0.98  
% 2.17/0.98  ------ Debug Options
% 2.17/0.98  
% 2.17/0.98  --dbg_backtrace                         false
% 2.17/0.98  --dbg_dump_prop_clauses                 false
% 2.17/0.98  --dbg_dump_prop_clauses_file            -
% 2.17/0.98  --dbg_out_stat                          false
% 2.17/0.98  
% 2.17/0.98  
% 2.17/0.98  
% 2.17/0.98  
% 2.17/0.98  ------ Proving...
% 2.17/0.98  
% 2.17/0.98  
% 2.17/0.98  % SZS status Theorem for theBenchmark.p
% 2.17/0.98  
% 2.17/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.17/0.98  
% 2.17/0.98  fof(f1,axiom,(
% 2.17/0.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.17/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.17/0.98  
% 2.17/0.98  fof(f8,plain,(
% 2.17/0.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.17/0.98    inference(rectify,[],[f1])).
% 2.17/0.98  
% 2.17/0.98  fof(f9,plain,(
% 2.17/0.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 2.17/0.98    inference(ennf_transformation,[],[f8])).
% 2.17/0.98  
% 2.17/0.98  fof(f13,plain,(
% 2.17/0.98    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.17/0.98    introduced(choice_axiom,[])).
% 2.17/0.98  
% 2.17/0.98  fof(f14,plain,(
% 2.17/0.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 2.17/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f13])).
% 2.17/0.98  
% 2.17/0.98  fof(f26,plain,(
% 2.17/0.98    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 2.17/0.98    inference(cnf_transformation,[],[f14])).
% 2.17/0.98  
% 2.17/0.98  fof(f5,axiom,(
% 2.17/0.98    ! [X0,X1] : ~(! [X2] : ~(! [X3] : ~(r2_hidden(X3,X2) & r2_hidden(X3,X1)) & r2_hidden(X2,X1)) & r2_hidden(X0,X1))),
% 2.17/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.17/0.98  
% 2.17/0.98  fof(f11,plain,(
% 2.17/0.98    ! [X0,X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) | ~r2_hidden(X0,X1))),
% 2.17/0.98    inference(ennf_transformation,[],[f5])).
% 2.17/0.98  
% 2.17/0.98  fof(f21,plain,(
% 2.17/0.98    ! [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) => (! [X3] : (~r2_hidden(X3,sK6(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK6(X1),X1)))),
% 2.17/0.98    introduced(choice_axiom,[])).
% 2.17/0.98  
% 2.17/0.98  fof(f22,plain,(
% 2.17/0.98    ! [X0,X1] : ((! [X3] : (~r2_hidden(X3,sK6(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK6(X1),X1)) | ~r2_hidden(X0,X1))),
% 2.17/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f11,f21])).
% 2.17/0.98  
% 2.17/0.98  fof(f38,plain,(
% 2.17/0.98    ( ! [X0,X1] : (r2_hidden(sK6(X1),X1) | ~r2_hidden(X0,X1)) )),
% 2.17/0.98    inference(cnf_transformation,[],[f22])).
% 2.17/0.98  
% 2.17/0.98  fof(f3,axiom,(
% 2.17/0.98    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 2.17/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.17/0.98  
% 2.17/0.98  fof(f15,plain,(
% 2.17/0.98    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 2.17/0.98    inference(nnf_transformation,[],[f3])).
% 2.17/0.98  
% 2.17/0.98  fof(f16,plain,(
% 2.17/0.98    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 2.17/0.98    inference(rectify,[],[f15])).
% 2.17/0.98  
% 2.17/0.98  fof(f19,plain,(
% 2.17/0.98    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) => (k4_tarski(sK4(X0,X1,X8),sK5(X0,X1,X8)) = X8 & r2_hidden(sK5(X0,X1,X8),X1) & r2_hidden(sK4(X0,X1,X8),X0)))),
% 2.17/0.98    introduced(choice_axiom,[])).
% 2.17/0.98  
% 2.17/0.98  fof(f18,plain,(
% 2.17/0.98    ( ! [X3] : (! [X2,X1,X0] : (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) => (k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)) = X3 & r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)))) )),
% 2.17/0.98    introduced(choice_axiom,[])).
% 2.17/0.98  
% 2.17/0.98  fof(f17,plain,(
% 2.17/0.98    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK1(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK1(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 2.17/0.98    introduced(choice_axiom,[])).
% 2.17/0.98  
% 2.17/0.98  fof(f20,plain,(
% 2.17/0.98    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ((! [X4,X5] : (k4_tarski(X4,X5) != sK1(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)) = sK1(X0,X1,X2) & r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & ((k4_tarski(sK4(X0,X1,X8),sK5(X0,X1,X8)) = X8 & r2_hidden(sK5(X0,X1,X8),X1) & r2_hidden(sK4(X0,X1,X8),X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 2.17/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f16,f19,f18,f17])).
% 2.17/0.98  
% 2.17/0.98  fof(f34,plain,(
% 2.17/0.98    ( ! [X2,X0,X1] : (k2_zfmisc_1(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 2.17/0.98    inference(cnf_transformation,[],[f20])).
% 2.17/0.98  
% 2.17/0.98  fof(f6,conjecture,(
% 2.17/0.98    ! [X0] : ~(! [X1] : ~(r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 2.17/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.17/0.98  
% 2.17/0.98  fof(f7,negated_conjecture,(
% 2.17/0.98    ~! [X0] : ~(! [X1] : ~(r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 2.17/0.98    inference(negated_conjecture,[],[f6])).
% 2.17/0.98  
% 2.17/0.98  fof(f12,plain,(
% 2.17/0.98    ? [X0] : (! [X1] : (~r1_xboole_0(X1,X0) | ~r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 2.17/0.98    inference(ennf_transformation,[],[f7])).
% 2.17/0.98  
% 2.17/0.98  fof(f23,plain,(
% 2.17/0.98    ? [X0] : (! [X1] : (~r1_xboole_0(X1,X0) | ~r2_hidden(X1,X0)) & k1_xboole_0 != X0) => (! [X1] : (~r1_xboole_0(X1,sK7) | ~r2_hidden(X1,sK7)) & k1_xboole_0 != sK7)),
% 2.17/0.98    introduced(choice_axiom,[])).
% 2.17/0.98  
% 2.17/0.98  fof(f24,plain,(
% 2.17/0.98    ! [X1] : (~r1_xboole_0(X1,sK7) | ~r2_hidden(X1,sK7)) & k1_xboole_0 != sK7),
% 2.17/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f12,f23])).
% 2.17/0.98  
% 2.17/0.98  fof(f41,plain,(
% 2.17/0.98    ( ! [X1] : (~r1_xboole_0(X1,sK7) | ~r2_hidden(X1,sK7)) )),
% 2.17/0.98    inference(cnf_transformation,[],[f24])).
% 2.17/0.98  
% 2.17/0.98  fof(f27,plain,(
% 2.17/0.98    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 2.17/0.98    inference(cnf_transformation,[],[f14])).
% 2.17/0.98  
% 2.17/0.98  fof(f33,plain,(
% 2.17/0.98    ( ! [X2,X0,X1] : (k2_zfmisc_1(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 2.17/0.98    inference(cnf_transformation,[],[f20])).
% 2.17/0.98  
% 2.17/0.98  fof(f25,plain,(
% 2.17/0.98    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 2.17/0.98    inference(cnf_transformation,[],[f14])).
% 2.17/0.98  
% 2.17/0.98  fof(f39,plain,(
% 2.17/0.98    ( ! [X0,X3,X1] : (~r2_hidden(X3,sK6(X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(X0,X1)) )),
% 2.17/0.98    inference(cnf_transformation,[],[f22])).
% 2.17/0.98  
% 2.17/0.98  fof(f30,plain,(
% 2.17/0.98    ( ! [X2,X0,X8,X1] : (r2_hidden(sK5(X0,X1,X8),X1) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 2.17/0.98    inference(cnf_transformation,[],[f20])).
% 2.17/0.98  
% 2.17/0.98  fof(f45,plain,(
% 2.17/0.98    ( ! [X0,X8,X1] : (r2_hidden(sK5(X0,X1,X8),X1) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 2.17/0.98    inference(equality_resolution,[],[f30])).
% 2.17/0.98  
% 2.17/0.98  fof(f29,plain,(
% 2.17/0.98    ( ! [X2,X0,X8,X1] : (r2_hidden(sK4(X0,X1,X8),X0) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 2.17/0.98    inference(cnf_transformation,[],[f20])).
% 2.17/0.98  
% 2.17/0.98  fof(f46,plain,(
% 2.17/0.98    ( ! [X0,X8,X1] : (r2_hidden(sK4(X0,X1,X8),X0) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 2.17/0.98    inference(equality_resolution,[],[f29])).
% 2.17/0.98  
% 2.17/0.98  fof(f2,axiom,(
% 2.17/0.98    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 2.17/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.17/0.98  
% 2.17/0.98  fof(f28,plain,(
% 2.17/0.98    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 2.17/0.98    inference(cnf_transformation,[],[f2])).
% 2.17/0.98  
% 2.17/0.98  fof(f4,axiom,(
% 2.17/0.98    ! [X0,X1,X2] : ~(r2_hidden(X0,X2) & r1_xboole_0(k2_tarski(X0,X1),X2))),
% 2.17/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.17/0.98  
% 2.17/0.98  fof(f10,plain,(
% 2.17/0.98    ! [X0,X1,X2] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2))),
% 2.17/0.98    inference(ennf_transformation,[],[f4])).
% 2.17/0.98  
% 2.17/0.98  fof(f37,plain,(
% 2.17/0.98    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2)) )),
% 2.17/0.98    inference(cnf_transformation,[],[f10])).
% 2.17/0.98  
% 2.17/0.98  fof(f40,plain,(
% 2.17/0.98    k1_xboole_0 != sK7),
% 2.17/0.98    inference(cnf_transformation,[],[f24])).
% 2.17/0.98  
% 2.17/0.98  cnf(c_1,plain,
% 2.17/0.98      ( r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1) ),
% 2.17/0.98      inference(cnf_transformation,[],[f26]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_600,plain,
% 2.17/0.98      ( r2_hidden(sK0(X0,X1),X1) = iProver_top
% 2.17/0.98      | r1_xboole_0(X0,X1) = iProver_top ),
% 2.17/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_14,plain,
% 2.17/0.98      ( ~ r2_hidden(X0,X1) | r2_hidden(sK6(X1),X1) ),
% 2.17/0.98      inference(cnf_transformation,[],[f38]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_587,plain,
% 2.17/0.98      ( r2_hidden(X0,X1) != iProver_top
% 2.17/0.98      | r2_hidden(sK6(X1),X1) = iProver_top ),
% 2.17/0.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_1026,plain,
% 2.17/0.98      ( r2_hidden(sK6(X0),X0) = iProver_top
% 2.17/0.98      | r1_xboole_0(X1,X0) = iProver_top ),
% 2.17/0.98      inference(superposition,[status(thm)],[c_600,c_587]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_6,plain,
% 2.17/0.98      ( r2_hidden(sK3(X0,X1,X2),X1)
% 2.17/0.98      | r2_hidden(sK1(X0,X1,X2),X2)
% 2.17/0.98      | k2_zfmisc_1(X0,X1) = X2 ),
% 2.17/0.98      inference(cnf_transformation,[],[f34]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_595,plain,
% 2.17/0.98      ( k2_zfmisc_1(X0,X1) = X2
% 2.17/0.98      | r2_hidden(sK3(X0,X1,X2),X1) = iProver_top
% 2.17/0.98      | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
% 2.17/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_15,negated_conjecture,
% 2.17/0.98      ( ~ r2_hidden(X0,sK7) | ~ r1_xboole_0(X0,sK7) ),
% 2.17/0.98      inference(cnf_transformation,[],[f41]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_586,plain,
% 2.17/0.98      ( r2_hidden(X0,sK7) != iProver_top
% 2.17/0.98      | r1_xboole_0(X0,sK7) != iProver_top ),
% 2.17/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_2406,plain,
% 2.17/0.98      ( k2_zfmisc_1(X0,sK7) = X1
% 2.17/0.98      | r2_hidden(sK1(X0,sK7,X1),X1) = iProver_top
% 2.17/0.98      | r1_xboole_0(sK3(X0,sK7,X1),sK7) != iProver_top ),
% 2.17/0.98      inference(superposition,[status(thm)],[c_595,c_586]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_4939,plain,
% 2.17/0.98      ( k2_zfmisc_1(X0,sK7) = X1
% 2.17/0.98      | r2_hidden(sK1(X0,sK7,X1),X1) = iProver_top
% 2.17/0.98      | r2_hidden(sK6(sK7),sK7) = iProver_top ),
% 2.17/0.98      inference(superposition,[status(thm)],[c_1026,c_2406]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_310,plain,( X0 = X0 ),theory(equality) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_319,plain,
% 2.17/0.98      ( sK7 = sK7 ),
% 2.17/0.98      inference(instantiation,[status(thm)],[c_310]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_311,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_817,plain,
% 2.17/0.98      ( k2_zfmisc_1(X0,X1) != X2 | sK7 != X2 | sK7 = k2_zfmisc_1(X0,X1) ),
% 2.17/0.98      inference(instantiation,[status(thm)],[c_311]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_818,plain,
% 2.17/0.98      ( k2_zfmisc_1(sK7,sK7) != sK7
% 2.17/0.98      | sK7 = k2_zfmisc_1(sK7,sK7)
% 2.17/0.98      | sK7 != sK7 ),
% 2.17/0.98      inference(instantiation,[status(thm)],[c_817]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_0,plain,
% 2.17/0.98      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 2.17/0.98      inference(cnf_transformation,[],[f27]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_1579,plain,
% 2.17/0.98      ( ~ r2_hidden(sK6(X0),X0)
% 2.17/0.98      | ~ r2_hidden(sK6(X0),X1)
% 2.17/0.98      | ~ r1_xboole_0(X1,X0) ),
% 2.17/0.98      inference(instantiation,[status(thm)],[c_0]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_1586,plain,
% 2.17/0.98      ( r2_hidden(sK6(X0),X0) != iProver_top
% 2.17/0.98      | r2_hidden(sK6(X0),X1) != iProver_top
% 2.17/0.98      | r1_xboole_0(X1,X0) != iProver_top ),
% 2.17/0.98      inference(predicate_to_equality,[status(thm)],[c_1579]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_1588,plain,
% 2.17/0.98      ( r2_hidden(sK6(sK7),sK7) != iProver_top
% 2.17/0.98      | r1_xboole_0(sK7,sK7) != iProver_top ),
% 2.17/0.98      inference(instantiation,[status(thm)],[c_1586]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_312,plain,
% 2.17/0.98      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.17/0.98      theory(equality) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_3720,plain,
% 2.17/0.98      ( r1_xboole_0(X0,X1)
% 2.17/0.98      | ~ r1_xboole_0(k2_zfmisc_1(X2,X3),X4)
% 2.17/0.98      | X1 != X4
% 2.17/0.98      | X0 != k2_zfmisc_1(X2,X3) ),
% 2.17/0.98      inference(instantiation,[status(thm)],[c_312]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_3721,plain,
% 2.17/0.98      ( X0 != X1
% 2.17/0.98      | X2 != k2_zfmisc_1(X3,X4)
% 2.17/0.98      | r1_xboole_0(X2,X0) = iProver_top
% 2.17/0.98      | r1_xboole_0(k2_zfmisc_1(X3,X4),X1) != iProver_top ),
% 2.17/0.98      inference(predicate_to_equality,[status(thm)],[c_3720]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_3723,plain,
% 2.17/0.98      ( sK7 != k2_zfmisc_1(sK7,sK7)
% 2.17/0.98      | sK7 != sK7
% 2.17/0.98      | r1_xboole_0(k2_zfmisc_1(sK7,sK7),sK7) != iProver_top
% 2.17/0.98      | r1_xboole_0(sK7,sK7) = iProver_top ),
% 2.17/0.98      inference(instantiation,[status(thm)],[c_3721]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_7,plain,
% 2.17/0.98      ( r2_hidden(sK2(X0,X1,X2),X0)
% 2.17/0.98      | r2_hidden(sK1(X0,X1,X2),X2)
% 2.17/0.98      | k2_zfmisc_1(X0,X1) = X2 ),
% 2.17/0.98      inference(cnf_transformation,[],[f33]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_594,plain,
% 2.17/0.98      ( k2_zfmisc_1(X0,X1) = X2
% 2.17/0.98      | r2_hidden(sK2(X0,X1,X2),X0) = iProver_top
% 2.17/0.98      | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
% 2.17/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_2074,plain,
% 2.17/0.98      ( k2_zfmisc_1(X0,X1) = sK7
% 2.17/0.98      | r2_hidden(sK2(X0,X1,sK7),X0) = iProver_top
% 2.17/0.98      | r1_xboole_0(sK1(X0,X1,sK7),sK7) != iProver_top ),
% 2.17/0.98      inference(superposition,[status(thm)],[c_594,c_586]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_4936,plain,
% 2.17/0.98      ( k2_zfmisc_1(X0,X1) = sK7
% 2.17/0.98      | r2_hidden(sK2(X0,X1,sK7),X0) = iProver_top
% 2.17/0.98      | r2_hidden(sK6(sK7),sK7) = iProver_top ),
% 2.17/0.98      inference(superposition,[status(thm)],[c_1026,c_2074]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_8866,plain,
% 2.17/0.98      ( k2_zfmisc_1(sK7,X0) = sK7
% 2.17/0.98      | r2_hidden(sK6(sK7),sK7) = iProver_top
% 2.17/0.98      | r1_xboole_0(sK2(sK7,X0,sK7),sK7) != iProver_top ),
% 2.17/0.98      inference(superposition,[status(thm)],[c_4936,c_586]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_1635,plain,
% 2.17/0.98      ( ~ r2_hidden(sK6(sK7),sK7) | ~ r1_xboole_0(sK6(sK7),sK7) ),
% 2.17/0.98      inference(instantiation,[status(thm)],[c_15]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_1638,plain,
% 2.17/0.98      ( r2_hidden(sK6(sK7),sK7) != iProver_top
% 2.17/0.98      | r1_xboole_0(sK6(sK7),sK7) != iProver_top ),
% 2.17/0.98      inference(predicate_to_equality,[status(thm)],[c_1635]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_2,plain,
% 2.17/0.98      ( r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1) ),
% 2.17/0.98      inference(cnf_transformation,[],[f25]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_599,plain,
% 2.17/0.98      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 2.17/0.98      | r1_xboole_0(X0,X1) = iProver_top ),
% 2.17/0.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_13,plain,
% 2.17/0.98      ( ~ r2_hidden(X0,X1)
% 2.17/0.98      | ~ r2_hidden(X2,X1)
% 2.17/0.98      | ~ r2_hidden(X2,sK6(X1)) ),
% 2.17/0.98      inference(cnf_transformation,[],[f39]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_588,plain,
% 2.17/0.98      ( r2_hidden(X0,X1) != iProver_top
% 2.17/0.98      | r2_hidden(X2,X1) != iProver_top
% 2.17/0.98      | r2_hidden(X2,sK6(X1)) != iProver_top ),
% 2.17/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_908,plain,
% 2.17/0.98      ( r2_hidden(X0,X1) != iProver_top
% 2.17/0.98      | r2_hidden(sK0(sK6(X1),X2),X1) != iProver_top
% 2.17/0.98      | r1_xboole_0(sK6(X1),X2) = iProver_top ),
% 2.17/0.98      inference(superposition,[status(thm)],[c_599,c_588]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_9031,plain,
% 2.17/0.98      ( r2_hidden(X0,X1) != iProver_top
% 2.17/0.98      | r1_xboole_0(sK6(X1),X1) = iProver_top ),
% 2.17/0.98      inference(superposition,[status(thm)],[c_600,c_908]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_9533,plain,
% 2.17/0.98      ( r1_xboole_0(X0,X1) = iProver_top
% 2.17/0.98      | r1_xboole_0(sK6(X1),X1) = iProver_top ),
% 2.17/0.98      inference(superposition,[status(thm)],[c_1026,c_9031]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_9641,plain,
% 2.17/0.98      ( r1_xboole_0(sK6(sK7),sK7) = iProver_top
% 2.17/0.98      | r1_xboole_0(sK7,sK7) = iProver_top ),
% 2.17/0.98      inference(instantiation,[status(thm)],[c_9533]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_9689,plain,
% 2.17/0.98      ( k2_zfmisc_1(sK7,X0) = sK7
% 2.17/0.98      | r1_xboole_0(sK2(sK7,X0,sK7),sK7) != iProver_top ),
% 2.17/0.98      inference(global_propositional_subsumption,
% 2.17/0.98                [status(thm)],
% 2.17/0.98                [c_8866,c_1588,c_1638,c_9641]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_9699,plain,
% 2.17/0.98      ( k2_zfmisc_1(sK7,X0) = sK7
% 2.17/0.98      | r2_hidden(sK6(sK7),sK7) = iProver_top ),
% 2.17/0.98      inference(superposition,[status(thm)],[c_1026,c_9689]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_9718,plain,
% 2.17/0.98      ( k2_zfmisc_1(sK7,X0) = sK7 ),
% 2.17/0.98      inference(global_propositional_subsumption,
% 2.17/0.98                [status(thm)],
% 2.17/0.98                [c_9699,c_1588,c_1638,c_9641]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_9720,plain,
% 2.17/0.98      ( k2_zfmisc_1(sK7,sK7) = sK7 ),
% 2.17/0.98      inference(instantiation,[status(thm)],[c_9718]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_10,plain,
% 2.17/0.98      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 2.17/0.98      | r2_hidden(sK5(X1,X2,X0),X2) ),
% 2.17/0.98      inference(cnf_transformation,[],[f45]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_591,plain,
% 2.17/0.98      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 2.17/0.98      | r2_hidden(sK5(X1,X2,X0),X2) = iProver_top ),
% 2.17/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_11,plain,
% 2.17/0.98      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 2.17/0.98      | r2_hidden(sK4(X1,X2,X0),X1) ),
% 2.17/0.98      inference(cnf_transformation,[],[f46]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_590,plain,
% 2.17/0.98      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 2.17/0.98      | r2_hidden(sK4(X1,X2,X0),X1) = iProver_top ),
% 2.17/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_3,plain,
% 2.17/0.98      ( r1_xboole_0(X0,k1_xboole_0) ),
% 2.17/0.98      inference(cnf_transformation,[],[f28]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_598,plain,
% 2.17/0.98      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 2.17/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_12,plain,
% 2.17/0.98      ( ~ r2_hidden(X0,X1) | ~ r1_xboole_0(k2_tarski(X0,X2),X1) ),
% 2.17/0.98      inference(cnf_transformation,[],[f37]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_589,plain,
% 2.17/0.98      ( r2_hidden(X0,X1) != iProver_top
% 2.17/0.98      | r1_xboole_0(k2_tarski(X0,X2),X1) != iProver_top ),
% 2.17/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_743,plain,
% 2.17/0.98      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.17/0.98      inference(superposition,[status(thm)],[c_598,c_589]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_844,plain,
% 2.17/0.98      ( r2_hidden(X0,k2_zfmisc_1(k1_xboole_0,X1)) != iProver_top ),
% 2.17/0.98      inference(superposition,[status(thm)],[c_590,c_743]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_1551,plain,
% 2.17/0.98      ( r2_hidden(X0,k2_zfmisc_1(X1,k2_zfmisc_1(k1_xboole_0,X2))) != iProver_top ),
% 2.17/0.98      inference(superposition,[status(thm)],[c_591,c_844]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_2981,plain,
% 2.17/0.98      ( r2_hidden(X0,k2_zfmisc_1(X1,k2_zfmisc_1(X2,k2_zfmisc_1(k1_xboole_0,X3)))) != iProver_top ),
% 2.17/0.98      inference(superposition,[status(thm)],[c_591,c_1551]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_4195,plain,
% 2.17/0.98      ( r1_xboole_0(k2_zfmisc_1(X0,k2_zfmisc_1(X1,k2_zfmisc_1(k1_xboole_0,X2))),X3) = iProver_top ),
% 2.17/0.98      inference(superposition,[status(thm)],[c_599,c_2981]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_9766,plain,
% 2.17/0.98      ( r1_xboole_0(k2_zfmisc_1(X0,sK7),X1) = iProver_top ),
% 2.17/0.98      inference(superposition,[status(thm)],[c_9718,c_4195]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_9808,plain,
% 2.17/0.98      ( r1_xboole_0(k2_zfmisc_1(sK7,sK7),sK7) = iProver_top ),
% 2.17/0.98      inference(instantiation,[status(thm)],[c_9766]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_9846,plain,
% 2.17/0.98      ( r2_hidden(sK1(X0,sK7,X1),X1) = iProver_top
% 2.17/0.98      | k2_zfmisc_1(X0,sK7) = X1 ),
% 2.17/0.98      inference(global_propositional_subsumption,
% 2.17/0.98                [status(thm)],
% 2.17/0.98                [c_4939,c_1588,c_1638,c_9641]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_9847,plain,
% 2.17/0.98      ( k2_zfmisc_1(X0,sK7) = X1
% 2.17/0.98      | r2_hidden(sK1(X0,sK7,X1),X1) = iProver_top ),
% 2.17/0.98      inference(renaming,[status(thm)],[c_9846]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_9858,plain,
% 2.17/0.98      ( k2_zfmisc_1(X0,sK7) = k1_xboole_0 ),
% 2.17/0.98      inference(superposition,[status(thm)],[c_9847,c_743]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_9951,plain,
% 2.17/0.98      ( k2_zfmisc_1(sK7,sK7) = k1_xboole_0 ),
% 2.17/0.98      inference(instantiation,[status(thm)],[c_9858]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_730,plain,
% 2.17/0.98      ( X0 != X1 | k1_xboole_0 != X1 | k1_xboole_0 = X0 ),
% 2.17/0.98      inference(instantiation,[status(thm)],[c_311]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_768,plain,
% 2.17/0.98      ( X0 != k2_zfmisc_1(X1,X2)
% 2.17/0.98      | k1_xboole_0 = X0
% 2.17/0.98      | k1_xboole_0 != k2_zfmisc_1(X1,X2) ),
% 2.17/0.98      inference(instantiation,[status(thm)],[c_730]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_769,plain,
% 2.17/0.98      ( sK7 != k2_zfmisc_1(sK7,sK7)
% 2.17/0.98      | k1_xboole_0 != k2_zfmisc_1(sK7,sK7)
% 2.17/0.98      | k1_xboole_0 = sK7 ),
% 2.17/0.98      inference(instantiation,[status(thm)],[c_768]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_736,plain,
% 2.17/0.98      ( X0 != k1_xboole_0
% 2.17/0.98      | k1_xboole_0 = X0
% 2.17/0.98      | k1_xboole_0 != k1_xboole_0 ),
% 2.17/0.98      inference(instantiation,[status(thm)],[c_730]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_747,plain,
% 2.17/0.98      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 2.17/0.98      | k1_xboole_0 = k2_zfmisc_1(X0,X1)
% 2.17/0.98      | k1_xboole_0 != k1_xboole_0 ),
% 2.17/0.98      inference(instantiation,[status(thm)],[c_736]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_751,plain,
% 2.17/0.98      ( k2_zfmisc_1(sK7,sK7) != k1_xboole_0
% 2.17/0.98      | k1_xboole_0 = k2_zfmisc_1(sK7,sK7)
% 2.17/0.98      | k1_xboole_0 != k1_xboole_0 ),
% 2.17/0.98      inference(instantiation,[status(thm)],[c_747]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_729,plain,
% 2.17/0.98      ( k1_xboole_0 = k1_xboole_0 ),
% 2.17/0.98      inference(instantiation,[status(thm)],[c_310]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_16,negated_conjecture,
% 2.17/0.98      ( k1_xboole_0 != sK7 ),
% 2.17/0.98      inference(cnf_transformation,[],[f40]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(contradiction,plain,
% 2.17/0.98      ( $false ),
% 2.17/0.98      inference(minisat,
% 2.17/0.98                [status(thm)],
% 2.17/0.98                [c_9951,c_9720,c_818,c_769,c_751,c_729,c_319,c_16]) ).
% 2.17/0.98  
% 2.17/0.98  
% 2.17/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.17/0.98  
% 2.17/0.98  ------                               Statistics
% 2.17/0.98  
% 2.17/0.98  ------ General
% 2.17/0.98  
% 2.17/0.98  abstr_ref_over_cycles:                  0
% 2.17/0.98  abstr_ref_under_cycles:                 0
% 2.17/0.98  gc_basic_clause_elim:                   0
% 2.17/0.98  forced_gc_time:                         0
% 2.17/0.98  parsing_time:                           0.007
% 2.17/0.98  unif_index_cands_time:                  0.
% 2.17/0.98  unif_index_add_time:                    0.
% 2.17/0.98  orderings_time:                         0.
% 2.17/0.98  out_proof_time:                         0.013
% 2.17/0.98  total_time:                             0.411
% 2.17/0.98  num_of_symbols:                         45
% 2.17/0.98  num_of_terms:                           13677
% 2.17/0.98  
% 2.17/0.98  ------ Preprocessing
% 2.17/0.98  
% 2.17/0.98  num_of_splits:                          0
% 2.17/0.98  num_of_split_atoms:                     0
% 2.17/0.98  num_of_reused_defs:                     0
% 2.17/0.98  num_eq_ax_congr_red:                    44
% 2.17/0.98  num_of_sem_filtered_clauses:            1
% 2.17/0.98  num_of_subtypes:                        0
% 2.17/0.98  monotx_restored_types:                  0
% 2.17/0.98  sat_num_of_epr_types:                   0
% 2.17/0.98  sat_num_of_non_cyclic_types:            0
% 2.17/0.98  sat_guarded_non_collapsed_types:        0
% 2.17/0.98  num_pure_diseq_elim:                    0
% 2.17/0.98  simp_replaced_by:                       0
% 2.17/0.98  res_preprocessed:                       62
% 2.17/0.98  prep_upred:                             0
% 2.17/0.98  prep_unflattend:                        17
% 2.17/0.98  smt_new_axioms:                         0
% 2.17/0.98  pred_elim_cands:                        2
% 2.17/0.98  pred_elim:                              0
% 2.17/0.98  pred_elim_cl:                           0
% 2.17/0.98  pred_elim_cycles:                       1
% 2.17/0.98  merged_defs:                            0
% 2.17/0.98  merged_defs_ncl:                        0
% 2.17/0.98  bin_hyper_res:                          0
% 2.17/0.98  prep_cycles:                            3
% 2.17/0.98  pred_elim_time:                         0.001
% 2.17/0.98  splitting_time:                         0.
% 2.17/0.98  sem_filter_time:                        0.
% 2.17/0.98  monotx_time:                            0.
% 2.17/0.98  subtype_inf_time:                       0.
% 2.17/0.98  
% 2.17/0.98  ------ Problem properties
% 2.17/0.98  
% 2.17/0.98  clauses:                                17
% 2.17/0.98  conjectures:                            2
% 2.17/0.98  epr:                                    4
% 2.17/0.98  horn:                                   12
% 2.17/0.98  ground:                                 1
% 2.17/0.98  unary:                                  2
% 2.17/0.98  binary:                                 8
% 2.17/0.98  lits:                                   41
% 2.17/0.98  lits_eq:                                8
% 2.17/0.98  fd_pure:                                0
% 2.17/0.98  fd_pseudo:                              0
% 2.17/0.98  fd_cond:                                0
% 2.17/0.98  fd_pseudo_cond:                         4
% 2.17/0.98  ac_symbols:                             0
% 2.17/0.98  
% 2.17/0.98  ------ Propositional Solver
% 2.17/0.98  
% 2.17/0.98  prop_solver_calls:                      26
% 2.17/0.98  prop_fast_solver_calls:                 485
% 2.17/0.98  smt_solver_calls:                       0
% 2.17/0.98  smt_fast_solver_calls:                  0
% 2.17/0.98  prop_num_of_clauses:                    4291
% 2.17/0.98  prop_preprocess_simplified:             9927
% 2.17/0.98  prop_fo_subsumed:                       3
% 2.17/0.98  prop_solver_time:                       0.
% 2.17/0.98  smt_solver_time:                        0.
% 2.17/0.98  smt_fast_solver_time:                   0.
% 2.17/0.98  prop_fast_solver_time:                  0.
% 2.17/0.98  prop_unsat_core_time:                   0.
% 2.17/0.98  
% 2.17/0.98  ------ QBF
% 2.17/0.98  
% 2.17/0.98  qbf_q_res:                              0
% 2.17/0.98  qbf_num_tautologies:                    0
% 2.17/0.98  qbf_prep_cycles:                        0
% 2.17/0.98  
% 2.17/0.98  ------ BMC1
% 2.17/0.98  
% 2.17/0.98  bmc1_current_bound:                     -1
% 2.17/0.98  bmc1_last_solved_bound:                 -1
% 2.17/0.98  bmc1_unsat_core_size:                   -1
% 2.17/0.98  bmc1_unsat_core_parents_size:           -1
% 2.17/0.98  bmc1_merge_next_fun:                    0
% 2.17/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.17/0.98  
% 2.17/0.98  ------ Instantiation
% 2.17/0.98  
% 2.17/0.98  inst_num_of_clauses:                    985
% 2.17/0.98  inst_num_in_passive:                    590
% 2.17/0.98  inst_num_in_active:                     331
% 2.17/0.98  inst_num_in_unprocessed:                64
% 2.17/0.98  inst_num_of_loops:                      410
% 2.17/0.98  inst_num_of_learning_restarts:          0
% 2.17/0.98  inst_num_moves_active_passive:          73
% 2.17/0.98  inst_lit_activity:                      0
% 2.17/0.98  inst_lit_activity_moves:                1
% 2.17/0.98  inst_num_tautologies:                   0
% 2.17/0.98  inst_num_prop_implied:                  0
% 2.17/0.98  inst_num_existing_simplified:           0
% 2.17/0.98  inst_num_eq_res_simplified:             0
% 2.17/0.98  inst_num_child_elim:                    0
% 2.17/0.98  inst_num_of_dismatching_blockings:      676
% 2.17/0.98  inst_num_of_non_proper_insts:           545
% 2.17/0.98  inst_num_of_duplicates:                 0
% 2.17/0.98  inst_inst_num_from_inst_to_res:         0
% 2.17/0.98  inst_dismatching_checking_time:         0.
% 2.17/0.98  
% 2.17/0.98  ------ Resolution
% 2.17/0.98  
% 2.17/0.98  res_num_of_clauses:                     0
% 2.17/0.98  res_num_in_passive:                     0
% 2.17/0.98  res_num_in_active:                      0
% 2.17/0.98  res_num_of_loops:                       65
% 2.17/0.98  res_forward_subset_subsumed:            21
% 2.17/0.98  res_backward_subset_subsumed:           0
% 2.17/0.98  res_forward_subsumed:                   0
% 2.17/0.98  res_backward_subsumed:                  1
% 2.17/0.98  res_forward_subsumption_resolution:     0
% 2.17/0.98  res_backward_subsumption_resolution:    0
% 2.17/0.98  res_clause_to_clause_subsumption:       1080
% 2.17/0.98  res_orphan_elimination:                 0
% 2.17/0.98  res_tautology_del:                      37
% 2.17/0.98  res_num_eq_res_simplified:              0
% 2.17/0.98  res_num_sel_changes:                    0
% 2.17/0.98  res_moves_from_active_to_pass:          0
% 2.17/0.98  
% 2.17/0.98  ------ Superposition
% 2.17/0.98  
% 2.17/0.98  sup_time_total:                         0.
% 2.17/0.98  sup_time_generating:                    0.
% 2.17/0.98  sup_time_sim_full:                      0.
% 2.17/0.98  sup_time_sim_immed:                     0.
% 2.17/0.98  
% 2.17/0.98  sup_num_of_clauses:                     336
% 2.17/0.98  sup_num_in_active:                      68
% 2.17/0.98  sup_num_in_passive:                     268
% 2.17/0.98  sup_num_of_loops:                       80
% 2.17/0.98  sup_fw_superposition:                   238
% 2.17/0.98  sup_bw_superposition:                   245
% 2.17/0.98  sup_immediate_simplified:               22
% 2.17/0.98  sup_given_eliminated:                   1
% 2.17/0.98  comparisons_done:                       0
% 2.17/0.98  comparisons_avoided:                    5
% 2.17/0.98  
% 2.17/0.98  ------ Simplifications
% 2.17/0.98  
% 2.17/0.98  
% 2.17/0.98  sim_fw_subset_subsumed:                 1
% 2.17/0.98  sim_bw_subset_subsumed:                 26
% 2.17/0.98  sim_fw_subsumed:                        16
% 2.17/0.98  sim_bw_subsumed:                        0
% 2.17/0.98  sim_fw_subsumption_res:                 1
% 2.17/0.98  sim_bw_subsumption_res:                 0
% 2.17/0.98  sim_tautology_del:                      0
% 2.17/0.98  sim_eq_tautology_del:                   0
% 2.17/0.98  sim_eq_res_simp:                        0
% 2.17/0.98  sim_fw_demodulated:                     5
% 2.17/0.98  sim_bw_demodulated:                     26
% 2.17/0.98  sim_light_normalised:                   2
% 2.17/0.98  sim_joinable_taut:                      0
% 2.17/0.98  sim_joinable_simp:                      0
% 2.17/0.98  sim_ac_normalised:                      0
% 2.17/0.98  sim_smt_subsumption:                    0
% 2.17/0.98  
%------------------------------------------------------------------------------
