%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0923+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:26 EST 2020

% Result     : Theorem 3.77s
% Output     : CNFRefutation 3.77s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 140 expanded)
%              Number of clauses        :   33 (  39 expanded)
%              Number of leaves         :   10 (  39 expanded)
%              Depth                    :   14
%              Number of atoms          :  253 ( 751 expanded)
%              Number of equality atoms :   91 ( 223 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ~ ( ! [X5,X6,X7,X8] :
            ~ ( k4_mcart_1(X5,X6,X7,X8) = X0
              & r2_hidden(X8,X4)
              & r2_hidden(X7,X3)
              & r2_hidden(X6,X2)
              & r2_hidden(X5,X1) )
        & r2_hidden(X0,k4_zfmisc_1(X1,X2,X3,X4)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ~ ( ! [X5,X6,X7,X8] :
              ~ ( k4_mcart_1(X5,X6,X7,X8) = X0
                & r2_hidden(X8,X4)
                & r2_hidden(X7,X3)
                & r2_hidden(X6,X2)
                & r2_hidden(X5,X1) )
          & r2_hidden(X0,k4_zfmisc_1(X1,X2,X3,X4)) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f8,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ! [X5,X6,X7,X8] :
          ( k4_mcart_1(X5,X6,X7,X8) != X0
          | ~ r2_hidden(X8,X4)
          | ~ r2_hidden(X7,X3)
          | ~ r2_hidden(X6,X2)
          | ~ r2_hidden(X5,X1) )
      & r2_hidden(X0,k4_zfmisc_1(X1,X2,X3,X4)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f17,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( ! [X5,X6,X7,X8] :
            ( k4_mcart_1(X5,X6,X7,X8) != X0
            | ~ r2_hidden(X8,X4)
            | ~ r2_hidden(X7,X3)
            | ~ r2_hidden(X6,X2)
            | ~ r2_hidden(X5,X1) )
        & r2_hidden(X0,k4_zfmisc_1(X1,X2,X3,X4)) )
   => ( ! [X8,X7,X6,X5] :
          ( k4_mcart_1(X5,X6,X7,X8) != sK8
          | ~ r2_hidden(X8,sK12)
          | ~ r2_hidden(X7,sK11)
          | ~ r2_hidden(X6,sK10)
          | ~ r2_hidden(X5,sK9) )
      & r2_hidden(sK8,k4_zfmisc_1(sK9,sK10,sK11,sK12)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ! [X5,X6,X7,X8] :
        ( k4_mcart_1(X5,X6,X7,X8) != sK8
        | ~ r2_hidden(X8,sK12)
        | ~ r2_hidden(X7,sK11)
        | ~ r2_hidden(X6,sK10)
        | ~ r2_hidden(X5,sK9) )
    & r2_hidden(sK8,k4_zfmisc_1(sK9,sK10,sK11,sK12)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10,sK11,sK12])],[f8,f17])).

fof(f33,plain,(
    r2_hidden(sK8,k4_zfmisc_1(sK9,sK10,sK11,sK12)) ),
    inference(cnf_transformation,[],[f18])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f3])).

fof(f36,plain,(
    r2_hidden(sK8,k2_zfmisc_1(k3_zfmisc_1(sK9,sK10,sK11),sK12)) ),
    inference(definition_unfolding,[],[f33,f28])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
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

fof(f10,plain,(
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
    inference(rectify,[],[f9])).

fof(f13,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK3(X0,X1,X8),sK4(X0,X1,X8)) = X8
        & r2_hidden(sK4(X0,X1,X8),X1)
        & r2_hidden(sK3(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X6,X7] :
          ( k4_tarski(X6,X7) = X3
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)) = X3
        & r2_hidden(sK2(X0,X1,X2),X1)
        & r2_hidden(sK1(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
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

fof(f14,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f10,f13,f12,f11])).

fof(f21,plain,(
    ! [X2,X0,X8,X1] :
      ( k4_tarski(sK3(X0,X1,X8),sK4(X0,X1,X8)) = X8
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f39,plain,(
    ! [X0,X8,X1] :
      ( k4_tarski(sK3(X0,X1,X8),sK4(X0,X1,X8)) = X8
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f21])).

fof(f19,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK3(X0,X1,X8),X0)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f41,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK3(X0,X1,X8),X0)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f19])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ! [X4,X5,X6] :
            ~ ( k3_mcart_1(X4,X5,X6) = X0
              & r2_hidden(X6,X3)
              & r2_hidden(X5,X2)
              & r2_hidden(X4,X1) )
        & r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1,X2,X3] :
      ( ? [X4,X5,X6] :
          ( k3_mcart_1(X4,X5,X6) = X0
          & r2_hidden(X6,X3)
          & r2_hidden(X5,X2)
          & r2_hidden(X4,X1) )
      | ~ r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f15,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4,X5,X6] :
          ( k3_mcart_1(X4,X5,X6) = X0
          & r2_hidden(X6,X3)
          & r2_hidden(X5,X2)
          & r2_hidden(X4,X1) )
     => ( k3_mcart_1(sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3),sK7(X0,X1,X2,X3)) = X0
        & r2_hidden(sK7(X0,X1,X2,X3),X3)
        & r2_hidden(sK6(X0,X1,X2,X3),X2)
        & r2_hidden(sK5(X0,X1,X2,X3),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k3_mcart_1(sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3),sK7(X0,X1,X2,X3)) = X0
        & r2_hidden(sK7(X0,X1,X2,X3),X3)
        & r2_hidden(sK6(X0,X1,X2,X3),X2)
        & r2_hidden(sK5(X0,X1,X2,X3),X1) )
      | ~ r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f7,f15])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_mcart_1(sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3),sK7(X0,X1,X2,X3)) = X0
      | ~ r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f34,plain,(
    ! [X6,X8,X7,X5] :
      ( k4_mcart_1(X5,X6,X7,X8) != sK8
      | ~ r2_hidden(X8,sK12)
      | ~ r2_hidden(X7,sK11)
      | ~ r2_hidden(X6,sK10)
      | ~ r2_hidden(X5,sK9) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k4_tarski(k3_mcart_1(X0,X1,X2),X3) = k4_mcart_1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X2,X0,X3,X1] : k4_tarski(k3_mcart_1(X0,X1,X2),X3) = k4_mcart_1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f2])).

fof(f35,plain,(
    ! [X6,X8,X7,X5] :
      ( k4_tarski(k3_mcart_1(X5,X6,X7),X8) != sK8
      | ~ r2_hidden(X8,sK12)
      | ~ r2_hidden(X7,sK11)
      | ~ r2_hidden(X6,sK10)
      | ~ r2_hidden(X5,sK9) ) ),
    inference(definition_unfolding,[],[f34,f27])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK7(X0,X1,X2,X3),X3)
      | ~ r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK6(X0,X1,X2,X3),X2)
      | ~ r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK5(X0,X1,X2,X3),X1)
      | ~ r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f20,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK4(X0,X1,X8),X1)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f40,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK4(X0,X1,X8),X1)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f20])).

cnf(c_13,negated_conjecture,
    ( r2_hidden(sK8,k2_zfmisc_1(k3_zfmisc_1(sK9,sK10,sK11),sK12)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_405,plain,
    ( r2_hidden(sK8,k2_zfmisc_1(k3_zfmisc_1(sK9,sK10,sK11),sK12)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | k4_tarski(sK3(X1,X2,X0),sK4(X1,X2,X0)) = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_413,plain,
    ( k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)) = X2
    | r2_hidden(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_879,plain,
    ( k4_tarski(sK3(k3_zfmisc_1(sK9,sK10,sK11),sK12,sK8),sK4(k3_zfmisc_1(sK9,sK10,sK11),sK12,sK8)) = sK8 ),
    inference(superposition,[status(thm)],[c_405,c_413])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(sK3(X1,X2,X0),X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_411,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(sK3(X1,X2,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k3_zfmisc_1(X1,X2,X3))
    | k3_mcart_1(sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3),sK7(X0,X1,X2,X3)) = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_410,plain,
    ( k3_mcart_1(sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3),sK7(X0,X1,X2,X3)) = X0
    | r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1151,plain,
    ( k3_mcart_1(sK5(sK3(k3_zfmisc_1(X0,X1,X2),X3,X4),X0,X1,X2),sK6(sK3(k3_zfmisc_1(X0,X1,X2),X3,X4),X0,X1,X2),sK7(sK3(k3_zfmisc_1(X0,X1,X2),X3,X4),X0,X1,X2)) = sK3(k3_zfmisc_1(X0,X1,X2),X3,X4)
    | r2_hidden(X4,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_411,c_410])).

cnf(c_9913,plain,
    ( k3_mcart_1(sK5(sK3(k3_zfmisc_1(sK9,sK10,sK11),sK12,sK8),sK9,sK10,sK11),sK6(sK3(k3_zfmisc_1(sK9,sK10,sK11),sK12,sK8),sK9,sK10,sK11),sK7(sK3(k3_zfmisc_1(sK9,sK10,sK11),sK12,sK8),sK9,sK10,sK11)) = sK3(k3_zfmisc_1(sK9,sK10,sK11),sK12,sK8) ),
    inference(superposition,[status(thm)],[c_405,c_1151])).

cnf(c_12,negated_conjecture,
    ( ~ r2_hidden(X0,sK9)
    | ~ r2_hidden(X1,sK10)
    | ~ r2_hidden(X2,sK11)
    | ~ r2_hidden(X3,sK12)
    | k4_tarski(k3_mcart_1(X0,X1,X2),X3) != sK8 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_406,plain,
    ( k4_tarski(k3_mcart_1(X0,X1,X2),X3) != sK8
    | r2_hidden(X0,sK9) != iProver_top
    | r2_hidden(X1,sK10) != iProver_top
    | r2_hidden(X2,sK11) != iProver_top
    | r2_hidden(X3,sK12) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_10036,plain,
    ( k4_tarski(sK3(k3_zfmisc_1(sK9,sK10,sK11),sK12,sK8),X0) != sK8
    | r2_hidden(X0,sK12) != iProver_top
    | r2_hidden(sK7(sK3(k3_zfmisc_1(sK9,sK10,sK11),sK12,sK8),sK9,sK10,sK11),sK11) != iProver_top
    | r2_hidden(sK6(sK3(k3_zfmisc_1(sK9,sK10,sK11),sK12,sK8),sK9,sK10,sK11),sK10) != iProver_top
    | r2_hidden(sK5(sK3(k3_zfmisc_1(sK9,sK10,sK11),sK12,sK8),sK9,sK10,sK11),sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_9913,c_406])).

cnf(c_14,plain,
    ( r2_hidden(sK8,k2_zfmisc_1(k3_zfmisc_1(sK9,sK10,sK11),sK12)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_525,plain,
    ( r2_hidden(sK3(k3_zfmisc_1(sK9,sK10,sK11),sK12,sK8),k3_zfmisc_1(sK9,sK10,sK11))
    | ~ r2_hidden(sK8,k2_zfmisc_1(k3_zfmisc_1(sK9,sK10,sK11),sK12)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_526,plain,
    ( r2_hidden(sK3(k3_zfmisc_1(sK9,sK10,sK11),sK12,sK8),k3_zfmisc_1(sK9,sK10,sK11)) = iProver_top
    | r2_hidden(sK8,k2_zfmisc_1(k3_zfmisc_1(sK9,sK10,sK11),sK12)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_525])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k3_zfmisc_1(X1,X2,X3))
    | r2_hidden(sK7(X0,X1,X2,X3),X3) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_578,plain,
    ( r2_hidden(sK7(sK3(k3_zfmisc_1(sK9,sK10,sK11),sK12,sK8),sK9,sK10,sK11),sK11)
    | ~ r2_hidden(sK3(k3_zfmisc_1(sK9,sK10,sK11),sK12,sK8),k3_zfmisc_1(sK9,sK10,sK11)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_579,plain,
    ( r2_hidden(sK7(sK3(k3_zfmisc_1(sK9,sK10,sK11),sK12,sK8),sK9,sK10,sK11),sK11) = iProver_top
    | r2_hidden(sK3(k3_zfmisc_1(sK9,sK10,sK11),sK12,sK8),k3_zfmisc_1(sK9,sK10,sK11)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_578])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k3_zfmisc_1(X1,X2,X3))
    | r2_hidden(sK6(X0,X1,X2,X3),X2) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_577,plain,
    ( r2_hidden(sK6(sK3(k3_zfmisc_1(sK9,sK10,sK11),sK12,sK8),sK9,sK10,sK11),sK10)
    | ~ r2_hidden(sK3(k3_zfmisc_1(sK9,sK10,sK11),sK12,sK8),k3_zfmisc_1(sK9,sK10,sK11)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_581,plain,
    ( r2_hidden(sK6(sK3(k3_zfmisc_1(sK9,sK10,sK11),sK12,sK8),sK9,sK10,sK11),sK10) = iProver_top
    | r2_hidden(sK3(k3_zfmisc_1(sK9,sK10,sK11),sK12,sK8),k3_zfmisc_1(sK9,sK10,sK11)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_577])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k3_zfmisc_1(X1,X2,X3))
    | r2_hidden(sK5(X0,X1,X2,X3),X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_576,plain,
    ( r2_hidden(sK5(sK3(k3_zfmisc_1(sK9,sK10,sK11),sK12,sK8),sK9,sK10,sK11),sK9)
    | ~ r2_hidden(sK3(k3_zfmisc_1(sK9,sK10,sK11),sK12,sK8),k3_zfmisc_1(sK9,sK10,sK11)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_583,plain,
    ( r2_hidden(sK5(sK3(k3_zfmisc_1(sK9,sK10,sK11),sK12,sK8),sK9,sK10,sK11),sK9) = iProver_top
    | r2_hidden(sK3(k3_zfmisc_1(sK9,sK10,sK11),sK12,sK8),k3_zfmisc_1(sK9,sK10,sK11)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_576])).

cnf(c_10652,plain,
    ( r2_hidden(X0,sK12) != iProver_top
    | k4_tarski(sK3(k3_zfmisc_1(sK9,sK10,sK11),sK12,sK8),X0) != sK8 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10036,c_14,c_526,c_579,c_581,c_583])).

cnf(c_10653,plain,
    ( k4_tarski(sK3(k3_zfmisc_1(sK9,sK10,sK11),sK12,sK8),X0) != sK8
    | r2_hidden(X0,sK12) != iProver_top ),
    inference(renaming,[status(thm)],[c_10652])).

cnf(c_10660,plain,
    ( r2_hidden(sK4(k3_zfmisc_1(sK9,sK10,sK11),sK12,sK8),sK12) != iProver_top ),
    inference(superposition,[status(thm)],[c_879,c_10653])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(sK4(X1,X2,X0),X2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_522,plain,
    ( r2_hidden(sK4(k3_zfmisc_1(sK9,sK10,sK11),sK12,sK8),sK12)
    | ~ r2_hidden(sK8,k2_zfmisc_1(k3_zfmisc_1(sK9,sK10,sK11),sK12)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_523,plain,
    ( r2_hidden(sK4(k3_zfmisc_1(sK9,sK10,sK11),sK12,sK8),sK12) = iProver_top
    | r2_hidden(sK8,k2_zfmisc_1(k3_zfmisc_1(sK9,sK10,sK11),sK12)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_522])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10660,c_523,c_14])).


%------------------------------------------------------------------------------
