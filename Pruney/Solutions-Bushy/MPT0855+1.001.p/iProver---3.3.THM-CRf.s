%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0855+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:16 EST 2020

% Result     : Theorem 1.14s
% Output     : CNFRefutation 1.14s
% Verified   : 
% Statistics : Number of formulae       :   40 (  70 expanded)
%              Number of clauses        :   15 (  16 expanded)
%              Number of leaves         :    8 (  20 expanded)
%              Depth                    :   11
%              Number of atoms          :  162 ( 284 expanded)
%              Number of equality atoms :   63 ( 101 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   18 (   1 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
     => ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
        | ! [X3,X4] : k4_tarski(X3,X4) != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r2_hidden(k2_mcart_1(X0),X2)
          & r2_hidden(k1_mcart_1(X0),X1) )
       => ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
          | ! [X3,X4] : k4_tarski(X3,X4) != X0 ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      & ? [X3,X4] : k4_tarski(X3,X4) = X0
      & r2_hidden(k2_mcart_1(X0),X2)
      & r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      & ? [X3,X4] : k4_tarski(X3,X4) = X0
      & r2_hidden(k2_mcart_1(X0),X2)
      & r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(flattening,[],[f6])).

fof(f15,plain,(
    ! [X0] :
      ( ? [X3,X4] : k4_tarski(X3,X4) = X0
     => k4_tarski(sK8,sK9) = X0 ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
        & ? [X3,X4] : k4_tarski(X3,X4) = X0
        & r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
   => ( ~ r2_hidden(sK5,k2_zfmisc_1(sK6,sK7))
      & ? [X4,X3] : k4_tarski(X3,X4) = sK5
      & r2_hidden(k2_mcart_1(sK5),sK7)
      & r2_hidden(k1_mcart_1(sK5),sK6) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ~ r2_hidden(sK5,k2_zfmisc_1(sK6,sK7))
    & k4_tarski(sK8,sK9) = sK5
    & r2_hidden(k2_mcart_1(sK5),sK7)
    & r2_hidden(k1_mcart_1(sK5),sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8,sK9])],[f7,f15,f14])).

fof(f28,plain,(
    k4_tarski(sK8,sK9) = sK5 ),
    inference(cnf_transformation,[],[f16])).

fof(f2,axiom,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | k4_tarski(X1,X2) != X0 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f35,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) = k4_tarski(k1_mcart_1(k4_tarski(X1,X2)),k2_mcart_1(k4_tarski(X1,X2))) ),
    inference(equality_resolution,[],[f25])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f9,plain,(
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
    inference(rectify,[],[f8])).

fof(f12,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK3(X0,X1,X8),sK4(X0,X1,X8)) = X8
        & r2_hidden(sK4(X0,X1,X8),X1)
        & r2_hidden(sK3(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X6,X7] :
          ( k4_tarski(X6,X7) = X3
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)) = X3
        & r2_hidden(sK2(X0,X1,X2),X1)
        & r2_hidden(sK1(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
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
              ( k4_tarski(X4,X5) != sK0(X0,X1,X2)
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X0) )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ? [X7,X6] :
              ( k4_tarski(X6,X7) = sK0(X0,X1,X2)
              & r2_hidden(X7,X1)
              & r2_hidden(X6,X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != sK0(X0,X1,X2)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)) = sK0(X0,X1,X2)
              & r2_hidden(sK2(X0,X1,X2),X1)
              & r2_hidden(sK1(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ( k4_tarski(sK3(X0,X1,X8),sK4(X0,X1,X8)) = X8
                & r2_hidden(sK4(X0,X1,X8),X1)
                & r2_hidden(sK3(X0,X1,X8),X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f9,f12,f11,f10])).

fof(f20,plain,(
    ! [X2,X0,X10,X8,X1,X9] :
      ( r2_hidden(X8,X2)
      | k4_tarski(X9,X10) != X8
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f30,plain,(
    ! [X2,X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),X2)
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f20])).

fof(f31,plain,(
    ! [X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0) ) ),
    inference(equality_resolution,[],[f30])).

fof(f29,plain,(
    ~ r2_hidden(sK5,k2_zfmisc_1(sK6,sK7)) ),
    inference(cnf_transformation,[],[f16])).

fof(f27,plain,(
    r2_hidden(k2_mcart_1(sK5),sK7) ),
    inference(cnf_transformation,[],[f16])).

fof(f26,plain,(
    r2_hidden(k1_mcart_1(sK5),sK6) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_10,negated_conjecture,
    ( k4_tarski(sK8,sK9) = sK5 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_8,plain,
    ( k4_tarski(k1_mcart_1(k4_tarski(X0,X1)),k2_mcart_1(k4_tarski(X0,X1))) = k4_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_624,plain,
    ( k4_tarski(k1_mcart_1(sK5),k2_mcart_1(sK5)) = k4_tarski(sK8,sK9) ),
    inference(superposition,[status(thm)],[c_10,c_8])).

cnf(c_626,plain,
    ( k4_tarski(k1_mcart_1(sK5),k2_mcart_1(sK5)) = sK5 ),
    inference(light_normalisation,[status(thm)],[c_624,c_10])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_323,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_795,plain,
    ( r2_hidden(k2_mcart_1(sK5),X0) != iProver_top
    | r2_hidden(k1_mcart_1(sK5),X1) != iProver_top
    | r2_hidden(sK5,k2_zfmisc_1(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_626,c_323])).

cnf(c_9,negated_conjecture,
    ( ~ r2_hidden(sK5,k2_zfmisc_1(sK6,sK7)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_319,plain,
    ( r2_hidden(sK5,k2_zfmisc_1(sK6,sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1560,plain,
    ( r2_hidden(k2_mcart_1(sK5),sK7) != iProver_top
    | r2_hidden(k1_mcart_1(sK5),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_795,c_319])).

cnf(c_11,negated_conjecture,
    ( r2_hidden(k2_mcart_1(sK5),sK7) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_14,plain,
    ( r2_hidden(k2_mcart_1(sK5),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_12,negated_conjecture,
    ( r2_hidden(k1_mcart_1(sK5),sK6) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_13,plain,
    ( r2_hidden(k1_mcart_1(sK5),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1560,c_14,c_13])).


%------------------------------------------------------------------------------
