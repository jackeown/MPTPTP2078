%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0912+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:24 EST 2020

% Result     : Theorem 2.15s
% Output     : CNFRefutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 143 expanded)
%              Number of clauses        :   25 (  35 expanded)
%              Number of leaves         :    8 (  43 expanded)
%              Depth                    :   13
%              Number of atoms          :  195 ( 884 expanded)
%              Number of equality atoms :   76 ( 285 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( ! [X4,X5,X6] :
            ~ ( k3_mcart_1(X4,X5,X6) = X0
              & r2_hidden(X6,X3)
              & r2_hidden(X5,X2)
              & r2_hidden(X4,X1) )
        & r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( ! [X4,X5,X6] :
              ~ ( k3_mcart_1(X4,X5,X6) = X0
                & r2_hidden(X6,X3)
                & r2_hidden(X5,X2)
                & r2_hidden(X4,X1) )
          & r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f6,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4,X5,X6] :
          ( k3_mcart_1(X4,X5,X6) != X0
          | ~ r2_hidden(X6,X3)
          | ~ r2_hidden(X5,X2)
          | ~ r2_hidden(X4,X1) )
      & r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f13,plain,
    ( ? [X0,X1,X2,X3] :
        ( ! [X4,X5,X6] :
            ( k3_mcart_1(X4,X5,X6) != X0
            | ~ r2_hidden(X6,X3)
            | ~ r2_hidden(X5,X2)
            | ~ r2_hidden(X4,X1) )
        & r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)) )
   => ( ! [X6,X5,X4] :
          ( k3_mcart_1(X4,X5,X6) != sK5
          | ~ r2_hidden(X6,sK8)
          | ~ r2_hidden(X5,sK7)
          | ~ r2_hidden(X4,sK6) )
      & r2_hidden(sK5,k3_zfmisc_1(sK6,sK7,sK8)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ! [X4,X5,X6] :
        ( k3_mcart_1(X4,X5,X6) != sK5
        | ~ r2_hidden(X6,sK8)
        | ~ r2_hidden(X5,sK7)
        | ~ r2_hidden(X4,sK6) )
    & r2_hidden(sK5,k3_zfmisc_1(sK6,sK7,sK8)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f6,f13])).

fof(f25,plain,(
    r2_hidden(sK5,k3_zfmisc_1(sK6,sK7,sK8)) ),
    inference(cnf_transformation,[],[f14])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f28,plain,(
    r2_hidden(sK5,k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8)) ),
    inference(definition_unfolding,[],[f25,f24])).

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

fof(f7,plain,(
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

fof(f8,plain,(
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
    inference(rectify,[],[f7])).

fof(f11,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK3(X0,X1,X8),sK4(X0,X1,X8)) = X8
        & r2_hidden(sK4(X0,X1,X8),X1)
        & r2_hidden(sK3(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X6,X7] :
          ( k4_tarski(X6,X7) = X3
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)) = X3
        & r2_hidden(sK2(X0,X1,X2),X1)
        & r2_hidden(sK1(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
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

fof(f12,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f8,f11,f10,f9])).

fof(f17,plain,(
    ! [X2,X0,X8,X1] :
      ( k4_tarski(sK3(X0,X1,X8),sK4(X0,X1,X8)) = X8
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f31,plain,(
    ! [X0,X8,X1] :
      ( k4_tarski(sK3(X0,X1,X8),sK4(X0,X1,X8)) = X8
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f17])).

fof(f15,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK3(X0,X1,X8),X0)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f33,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK3(X0,X1,X8),X0)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f15])).

fof(f26,plain,(
    ! [X6,X4,X5] :
      ( k3_mcart_1(X4,X5,X6) != sK5
      | ~ r2_hidden(X6,sK8)
      | ~ r2_hidden(X5,sK7)
      | ~ r2_hidden(X4,sK6) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X2,X0,X1] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f27,plain,(
    ! [X6,X4,X5] :
      ( k4_tarski(k4_tarski(X4,X5),X6) != sK5
      | ~ r2_hidden(X6,sK8)
      | ~ r2_hidden(X5,sK7)
      | ~ r2_hidden(X4,sK6) ) ),
    inference(definition_unfolding,[],[f26,f23])).

fof(f16,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK4(X0,X1,X8),X1)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f32,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK4(X0,X1,X8),X1)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f16])).

cnf(c_9,negated_conjecture,
    ( r2_hidden(sK5,k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_287,plain,
    ( r2_hidden(sK5,k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | k4_tarski(sK3(X1,X2,X0),sK4(X1,X2,X0)) = X0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_291,plain,
    ( k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)) = X2
    | r2_hidden(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_626,plain,
    ( k4_tarski(sK3(k2_zfmisc_1(sK6,sK7),sK8,sK5),sK4(k2_zfmisc_1(sK6,sK7),sK8,sK5)) = sK5 ),
    inference(superposition,[status(thm)],[c_287,c_291])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(sK3(X1,X2,X0),X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_289,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(sK3(X1,X2,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_625,plain,
    ( k4_tarski(sK3(X0,X1,sK3(k2_zfmisc_1(X0,X1),X2,X3)),sK4(X0,X1,sK3(k2_zfmisc_1(X0,X1),X2,X3))) = sK3(k2_zfmisc_1(X0,X1),X2,X3)
    | r2_hidden(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_289,c_291])).

cnf(c_1895,plain,
    ( k4_tarski(sK3(sK6,sK7,sK3(k2_zfmisc_1(sK6,sK7),sK8,sK5)),sK4(sK6,sK7,sK3(k2_zfmisc_1(sK6,sK7),sK8,sK5))) = sK3(k2_zfmisc_1(sK6,sK7),sK8,sK5) ),
    inference(superposition,[status(thm)],[c_287,c_625])).

cnf(c_8,negated_conjecture,
    ( ~ r2_hidden(X0,sK6)
    | ~ r2_hidden(X1,sK7)
    | ~ r2_hidden(X2,sK8)
    | k4_tarski(k4_tarski(X0,X1),X2) != sK5 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_288,plain,
    ( k4_tarski(k4_tarski(X0,X1),X2) != sK5
    | r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(X1,sK7) != iProver_top
    | r2_hidden(X2,sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1967,plain,
    ( k4_tarski(sK3(k2_zfmisc_1(sK6,sK7),sK8,sK5),X0) != sK5
    | r2_hidden(X0,sK8) != iProver_top
    | r2_hidden(sK4(sK6,sK7,sK3(k2_zfmisc_1(sK6,sK7),sK8,sK5)),sK7) != iProver_top
    | r2_hidden(sK3(sK6,sK7,sK3(k2_zfmisc_1(sK6,sK7),sK8,sK5)),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1895,c_288])).

cnf(c_10,plain,
    ( r2_hidden(sK5,k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_377,plain,
    ( r2_hidden(sK3(k2_zfmisc_1(sK6,sK7),sK8,sK5),k2_zfmisc_1(sK6,sK7))
    | ~ r2_hidden(sK5,k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_378,plain,
    ( r2_hidden(sK3(k2_zfmisc_1(sK6,sK7),sK8,sK5),k2_zfmisc_1(sK6,sK7)) = iProver_top
    | r2_hidden(sK5,k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_377])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(sK4(X1,X2,X0),X2) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_422,plain,
    ( r2_hidden(sK4(sK6,sK7,sK3(k2_zfmisc_1(sK6,sK7),sK8,sK5)),sK7)
    | ~ r2_hidden(sK3(k2_zfmisc_1(sK6,sK7),sK8,sK5),k2_zfmisc_1(sK6,sK7)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_423,plain,
    ( r2_hidden(sK4(sK6,sK7,sK3(k2_zfmisc_1(sK6,sK7),sK8,sK5)),sK7) = iProver_top
    | r2_hidden(sK3(k2_zfmisc_1(sK6,sK7),sK8,sK5),k2_zfmisc_1(sK6,sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_422])).

cnf(c_421,plain,
    ( ~ r2_hidden(sK3(k2_zfmisc_1(sK6,sK7),sK8,sK5),k2_zfmisc_1(sK6,sK7))
    | r2_hidden(sK3(sK6,sK7,sK3(k2_zfmisc_1(sK6,sK7),sK8,sK5)),sK6) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_425,plain,
    ( r2_hidden(sK3(k2_zfmisc_1(sK6,sK7),sK8,sK5),k2_zfmisc_1(sK6,sK7)) != iProver_top
    | r2_hidden(sK3(sK6,sK7,sK3(k2_zfmisc_1(sK6,sK7),sK8,sK5)),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_421])).

cnf(c_2425,plain,
    ( k4_tarski(sK3(k2_zfmisc_1(sK6,sK7),sK8,sK5),X0) != sK5
    | r2_hidden(X0,sK8) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1967,c_10,c_378,c_423,c_425])).

cnf(c_2433,plain,
    ( r2_hidden(sK4(k2_zfmisc_1(sK6,sK7),sK8,sK5),sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_626,c_2425])).

cnf(c_374,plain,
    ( r2_hidden(sK4(k2_zfmisc_1(sK6,sK7),sK8,sK5),sK8)
    | ~ r2_hidden(sK5,k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_375,plain,
    ( r2_hidden(sK4(k2_zfmisc_1(sK6,sK7),sK8,sK5),sK8) = iProver_top
    | r2_hidden(sK5,k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_374])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2433,c_375,c_10])).


%------------------------------------------------------------------------------
