%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:37:11 EST 2020

% Result     : Theorem 3.45s
% Output     : CNFRefutation 3.45s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 230 expanded)
%              Number of clauses        :   44 (  67 expanded)
%              Number of leaves         :    8 (  52 expanded)
%              Depth                    :   19
%              Number of atoms          :  267 (1012 expanded)
%              Number of equality atoms :  109 ( 214 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f8])).

fof(f10,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f10])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f3,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_tarski(X2,X3)
          & r1_tarski(X0,X1) )
       => r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f6,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f7,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f6])).

fof(f18,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(k2_zfmisc_1(sK6,sK8),k2_zfmisc_1(sK7,sK9))
      & r1_tarski(sK8,sK9)
      & r1_tarski(sK6,sK7) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK6,sK8),k2_zfmisc_1(sK7,sK9))
    & r1_tarski(sK8,sK9)
    & r1_tarski(sK6,sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f7,f18])).

fof(f31,plain,(
    r1_tarski(sK6,sK7) ),
    inference(cnf_transformation,[],[f19])).

fof(f2,axiom,(
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
    inference(nnf_transformation,[],[f2])).

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

fof(f23,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK4(X0,X1,X8),X0)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f38,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK4(X0,X1,X8),X0)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f23])).

fof(f20,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f32,plain,(
    r1_tarski(sK8,sK9) ),
    inference(cnf_transformation,[],[f19])).

fof(f24,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK5(X0,X1,X8),X1)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f37,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK5(X0,X1,X8),X1)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f24])).

fof(f25,plain,(
    ! [X2,X0,X8,X1] :
      ( k4_tarski(sK4(X0,X1,X8),sK5(X0,X1,X8)) = X8
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f36,plain,(
    ! [X0,X8,X1] :
      ( k4_tarski(sK4(X0,X1,X8),sK5(X0,X1,X8)) = X8
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f25])).

fof(f33,plain,(
    ~ r1_tarski(k2_zfmisc_1(sK6,sK8),k2_zfmisc_1(sK7,sK9)) ),
    inference(cnf_transformation,[],[f19])).

fof(f26,plain,(
    ! [X2,X0,X10,X8,X1,X9] :
      ( r2_hidden(X8,X2)
      | k4_tarski(X9,X10) != X8
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f34,plain,(
    ! [X2,X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),X2)
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f26])).

fof(f35,plain,(
    ! [X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0) ) ),
    inference(equality_resolution,[],[f34])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_496,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_497,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_893,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_496,c_497])).

cnf(c_13,negated_conjecture,
    ( r1_tarski(sK6,sK7) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_484,plain,
    ( r1_tarski(sK6,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(sK4(X1,X2,X0),X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_487,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(sK4(X1,X2,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_495,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_788,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(sK4(X1,X2,X0),X3) = iProver_top
    | r1_tarski(X1,X3) != iProver_top ),
    inference(superposition,[status(thm)],[c_487,c_495])).

cnf(c_1222,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(sK4(X1,X2,X0),X3) = iProver_top
    | r1_tarski(X1,X4) != iProver_top
    | r1_tarski(X4,X3) != iProver_top ),
    inference(superposition,[status(thm)],[c_788,c_495])).

cnf(c_6065,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(sK4(X1,X2,X0),sK7) = iProver_top
    | r1_tarski(X1,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_484,c_1222])).

cnf(c_12,negated_conjecture,
    ( r1_tarski(sK8,sK9) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_485,plain,
    ( r1_tarski(sK8,sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(sK5(X1,X2,X0),X2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_488,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(sK5(X1,X2,X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_787,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(sK5(X1,X2,X0),X3) = iProver_top
    | r1_tarski(X2,X3) != iProver_top ),
    inference(superposition,[status(thm)],[c_488,c_495])).

cnf(c_1215,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(sK5(X1,X2,X0),X3) = iProver_top
    | r1_tarski(X2,X4) != iProver_top
    | r1_tarski(X4,X3) != iProver_top ),
    inference(superposition,[status(thm)],[c_787,c_495])).

cnf(c_1465,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,sK8)) != iProver_top
    | r2_hidden(sK5(X1,sK8,X0),X2) = iProver_top
    | r1_tarski(sK9,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_485,c_1215])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | k4_tarski(sK4(X1,X2,X0),sK5(X1,X2,X0)) = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_489,plain,
    ( k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)) = X2
    | r2_hidden(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_895,plain,
    ( k4_tarski(sK4(X0,X1,sK0(k2_zfmisc_1(X0,X1),X2)),sK5(X0,X1,sK0(k2_zfmisc_1(X0,X1),X2))) = sK0(k2_zfmisc_1(X0,X1),X2)
    | r1_tarski(k2_zfmisc_1(X0,X1),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_496,c_489])).

cnf(c_11,negated_conjecture,
    ( ~ r1_tarski(k2_zfmisc_1(sK6,sK8),k2_zfmisc_1(sK7,sK9)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_486,plain,
    ( r1_tarski(k2_zfmisc_1(sK6,sK8),k2_zfmisc_1(sK7,sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4441,plain,
    ( k4_tarski(sK4(sK6,sK8,sK0(k2_zfmisc_1(sK6,sK8),k2_zfmisc_1(sK7,sK9))),sK5(sK6,sK8,sK0(k2_zfmisc_1(sK6,sK8),k2_zfmisc_1(sK7,sK9)))) = sK0(k2_zfmisc_1(sK6,sK8),k2_zfmisc_1(sK7,sK9)) ),
    inference(superposition,[status(thm)],[c_895,c_486])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_490,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4758,plain,
    ( r2_hidden(sK5(sK6,sK8,sK0(k2_zfmisc_1(sK6,sK8),k2_zfmisc_1(sK7,sK9))),X0) != iProver_top
    | r2_hidden(sK4(sK6,sK8,sK0(k2_zfmisc_1(sK6,sK8),k2_zfmisc_1(sK7,sK9))),X1) != iProver_top
    | r2_hidden(sK0(k2_zfmisc_1(sK6,sK8),k2_zfmisc_1(sK7,sK9)),k2_zfmisc_1(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4441,c_490])).

cnf(c_4825,plain,
    ( r2_hidden(sK4(sK6,sK8,sK0(k2_zfmisc_1(sK6,sK8),k2_zfmisc_1(sK7,sK9))),X0) != iProver_top
    | r2_hidden(sK0(k2_zfmisc_1(sK6,sK8),k2_zfmisc_1(sK7,sK9)),k2_zfmisc_1(X0,X1)) = iProver_top
    | r2_hidden(sK0(k2_zfmisc_1(sK6,sK8),k2_zfmisc_1(sK7,sK9)),k2_zfmisc_1(sK6,sK8)) != iProver_top
    | r1_tarski(sK9,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1465,c_4758])).

cnf(c_184,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | k2_zfmisc_1(sK7,sK9) != X1
    | k2_zfmisc_1(sK6,sK8) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_11])).

cnf(c_185,plain,
    ( r2_hidden(sK0(k2_zfmisc_1(sK6,sK8),k2_zfmisc_1(sK7,sK9)),k2_zfmisc_1(sK6,sK8)) ),
    inference(unflattening,[status(thm)],[c_184])).

cnf(c_186,plain,
    ( r2_hidden(sK0(k2_zfmisc_1(sK6,sK8),k2_zfmisc_1(sK7,sK9)),k2_zfmisc_1(sK6,sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_185])).

cnf(c_4845,plain,
    ( r2_hidden(sK0(k2_zfmisc_1(sK6,sK8),k2_zfmisc_1(sK7,sK9)),k2_zfmisc_1(X0,X1)) = iProver_top
    | r2_hidden(sK4(sK6,sK8,sK0(k2_zfmisc_1(sK6,sK8),k2_zfmisc_1(sK7,sK9))),X0) != iProver_top
    | r1_tarski(sK9,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4825,c_186])).

cnf(c_4846,plain,
    ( r2_hidden(sK4(sK6,sK8,sK0(k2_zfmisc_1(sK6,sK8),k2_zfmisc_1(sK7,sK9))),X0) != iProver_top
    | r2_hidden(sK0(k2_zfmisc_1(sK6,sK8),k2_zfmisc_1(sK7,sK9)),k2_zfmisc_1(X0,X1)) = iProver_top
    | r1_tarski(sK9,X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_4845])).

cnf(c_6237,plain,
    ( r2_hidden(sK0(k2_zfmisc_1(sK6,sK8),k2_zfmisc_1(sK7,sK9)),k2_zfmisc_1(sK7,X0)) = iProver_top
    | r2_hidden(sK0(k2_zfmisc_1(sK6,sK8),k2_zfmisc_1(sK7,sK9)),k2_zfmisc_1(sK6,sK8)) != iProver_top
    | r1_tarski(sK9,X0) != iProver_top
    | r1_tarski(sK6,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_6065,c_4846])).

cnf(c_897,plain,
    ( r1_tarski(sK6,sK6) = iProver_top ),
    inference(instantiation,[status(thm)],[c_893])).

cnf(c_7381,plain,
    ( r1_tarski(sK9,X0) != iProver_top
    | r2_hidden(sK0(k2_zfmisc_1(sK6,sK8),k2_zfmisc_1(sK7,sK9)),k2_zfmisc_1(sK7,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6237,c_186,c_897])).

cnf(c_7382,plain,
    ( r2_hidden(sK0(k2_zfmisc_1(sK6,sK8),k2_zfmisc_1(sK7,sK9)),k2_zfmisc_1(sK7,X0)) = iProver_top
    | r1_tarski(sK9,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_7381])).

cnf(c_7387,plain,
    ( r1_tarski(k2_zfmisc_1(sK6,sK8),k2_zfmisc_1(sK7,sK9)) = iProver_top
    | r1_tarski(sK9,sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_7382,c_497])).

cnf(c_16,plain,
    ( r1_tarski(k2_zfmisc_1(sK6,sK8),k2_zfmisc_1(sK7,sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_8835,plain,
    ( r1_tarski(sK9,sK9) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7387,c_16])).

cnf(c_8839,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_893,c_8835])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:39:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.45/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.45/0.98  
% 3.45/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.45/0.98  
% 3.45/0.98  ------  iProver source info
% 3.45/0.98  
% 3.45/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.45/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.45/0.98  git: non_committed_changes: false
% 3.45/0.98  git: last_make_outside_of_git: false
% 3.45/0.98  
% 3.45/0.98  ------ 
% 3.45/0.98  
% 3.45/0.98  ------ Input Options
% 3.45/0.98  
% 3.45/0.98  --out_options                           all
% 3.45/0.98  --tptp_safe_out                         true
% 3.45/0.98  --problem_path                          ""
% 3.45/0.98  --include_path                          ""
% 3.45/0.98  --clausifier                            res/vclausify_rel
% 3.45/0.98  --clausifier_options                    ""
% 3.45/0.98  --stdin                                 false
% 3.45/0.98  --stats_out                             all
% 3.45/0.98  
% 3.45/0.98  ------ General Options
% 3.45/0.98  
% 3.45/0.98  --fof                                   false
% 3.45/0.98  --time_out_real                         305.
% 3.45/0.98  --time_out_virtual                      -1.
% 3.45/0.98  --symbol_type_check                     false
% 3.45/0.98  --clausify_out                          false
% 3.45/0.98  --sig_cnt_out                           false
% 3.45/0.98  --trig_cnt_out                          false
% 3.45/0.98  --trig_cnt_out_tolerance                1.
% 3.45/0.98  --trig_cnt_out_sk_spl                   false
% 3.45/0.98  --abstr_cl_out                          false
% 3.45/0.98  
% 3.45/0.98  ------ Global Options
% 3.45/0.98  
% 3.45/0.98  --schedule                              default
% 3.45/0.98  --add_important_lit                     false
% 3.45/0.98  --prop_solver_per_cl                    1000
% 3.45/0.98  --min_unsat_core                        false
% 3.45/0.98  --soft_assumptions                      false
% 3.45/0.98  --soft_lemma_size                       3
% 3.45/0.98  --prop_impl_unit_size                   0
% 3.45/0.98  --prop_impl_unit                        []
% 3.45/0.98  --share_sel_clauses                     true
% 3.45/0.98  --reset_solvers                         false
% 3.45/0.98  --bc_imp_inh                            [conj_cone]
% 3.45/0.98  --conj_cone_tolerance                   3.
% 3.45/0.98  --extra_neg_conj                        none
% 3.45/0.98  --large_theory_mode                     true
% 3.45/0.98  --prolific_symb_bound                   200
% 3.45/0.98  --lt_threshold                          2000
% 3.45/0.98  --clause_weak_htbl                      true
% 3.45/0.98  --gc_record_bc_elim                     false
% 3.45/0.98  
% 3.45/0.98  ------ Preprocessing Options
% 3.45/0.98  
% 3.45/0.98  --preprocessing_flag                    true
% 3.45/0.98  --time_out_prep_mult                    0.1
% 3.45/0.98  --splitting_mode                        input
% 3.45/0.98  --splitting_grd                         true
% 3.45/0.98  --splitting_cvd                         false
% 3.45/0.98  --splitting_cvd_svl                     false
% 3.45/0.98  --splitting_nvd                         32
% 3.45/0.98  --sub_typing                            true
% 3.45/0.98  --prep_gs_sim                           true
% 3.45/0.98  --prep_unflatten                        true
% 3.45/0.98  --prep_res_sim                          true
% 3.45/0.98  --prep_upred                            true
% 3.45/0.98  --prep_sem_filter                       exhaustive
% 3.45/0.98  --prep_sem_filter_out                   false
% 3.45/0.98  --pred_elim                             true
% 3.45/0.98  --res_sim_input                         true
% 3.45/0.98  --eq_ax_congr_red                       true
% 3.45/0.98  --pure_diseq_elim                       true
% 3.45/0.98  --brand_transform                       false
% 3.45/0.98  --non_eq_to_eq                          false
% 3.45/0.98  --prep_def_merge                        true
% 3.45/0.98  --prep_def_merge_prop_impl              false
% 3.45/0.98  --prep_def_merge_mbd                    true
% 3.45/0.98  --prep_def_merge_tr_red                 false
% 3.45/0.98  --prep_def_merge_tr_cl                  false
% 3.45/0.98  --smt_preprocessing                     true
% 3.45/0.98  --smt_ac_axioms                         fast
% 3.45/0.98  --preprocessed_out                      false
% 3.45/0.98  --preprocessed_stats                    false
% 3.45/0.98  
% 3.45/0.98  ------ Abstraction refinement Options
% 3.45/0.98  
% 3.45/0.98  --abstr_ref                             []
% 3.45/0.98  --abstr_ref_prep                        false
% 3.45/0.98  --abstr_ref_until_sat                   false
% 3.45/0.98  --abstr_ref_sig_restrict                funpre
% 3.45/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.45/0.98  --abstr_ref_under                       []
% 3.45/0.98  
% 3.45/0.98  ------ SAT Options
% 3.45/0.98  
% 3.45/0.98  --sat_mode                              false
% 3.45/0.98  --sat_fm_restart_options                ""
% 3.45/0.98  --sat_gr_def                            false
% 3.45/0.98  --sat_epr_types                         true
% 3.45/0.98  --sat_non_cyclic_types                  false
% 3.45/0.98  --sat_finite_models                     false
% 3.45/0.98  --sat_fm_lemmas                         false
% 3.45/0.98  --sat_fm_prep                           false
% 3.45/0.98  --sat_fm_uc_incr                        true
% 3.45/0.98  --sat_out_model                         small
% 3.45/0.98  --sat_out_clauses                       false
% 3.45/0.98  
% 3.45/0.98  ------ QBF Options
% 3.45/0.98  
% 3.45/0.98  --qbf_mode                              false
% 3.45/0.98  --qbf_elim_univ                         false
% 3.45/0.98  --qbf_dom_inst                          none
% 3.45/0.98  --qbf_dom_pre_inst                      false
% 3.45/0.98  --qbf_sk_in                             false
% 3.45/0.98  --qbf_pred_elim                         true
% 3.45/0.98  --qbf_split                             512
% 3.45/0.98  
% 3.45/0.98  ------ BMC1 Options
% 3.45/0.98  
% 3.45/0.98  --bmc1_incremental                      false
% 3.45/0.98  --bmc1_axioms                           reachable_all
% 3.45/0.98  --bmc1_min_bound                        0
% 3.45/0.98  --bmc1_max_bound                        -1
% 3.45/0.98  --bmc1_max_bound_default                -1
% 3.45/0.98  --bmc1_symbol_reachability              true
% 3.45/0.98  --bmc1_property_lemmas                  false
% 3.45/0.98  --bmc1_k_induction                      false
% 3.45/0.98  --bmc1_non_equiv_states                 false
% 3.45/0.98  --bmc1_deadlock                         false
% 3.45/0.98  --bmc1_ucm                              false
% 3.45/0.98  --bmc1_add_unsat_core                   none
% 3.45/0.98  --bmc1_unsat_core_children              false
% 3.45/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.45/0.98  --bmc1_out_stat                         full
% 3.45/0.98  --bmc1_ground_init                      false
% 3.45/0.98  --bmc1_pre_inst_next_state              false
% 3.45/0.98  --bmc1_pre_inst_state                   false
% 3.45/0.98  --bmc1_pre_inst_reach_state             false
% 3.45/0.98  --bmc1_out_unsat_core                   false
% 3.45/0.98  --bmc1_aig_witness_out                  false
% 3.45/0.98  --bmc1_verbose                          false
% 3.45/0.98  --bmc1_dump_clauses_tptp                false
% 3.45/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.45/0.98  --bmc1_dump_file                        -
% 3.45/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.45/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.45/0.98  --bmc1_ucm_extend_mode                  1
% 3.45/0.98  --bmc1_ucm_init_mode                    2
% 3.45/0.98  --bmc1_ucm_cone_mode                    none
% 3.45/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.45/0.98  --bmc1_ucm_relax_model                  4
% 3.45/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.45/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.45/0.98  --bmc1_ucm_layered_model                none
% 3.45/0.98  --bmc1_ucm_max_lemma_size               10
% 3.45/0.98  
% 3.45/0.98  ------ AIG Options
% 3.45/0.98  
% 3.45/0.98  --aig_mode                              false
% 3.45/0.98  
% 3.45/0.98  ------ Instantiation Options
% 3.45/0.98  
% 3.45/0.98  --instantiation_flag                    true
% 3.45/0.98  --inst_sos_flag                         true
% 3.45/0.98  --inst_sos_phase                        true
% 3.45/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.45/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.45/0.98  --inst_lit_sel_side                     num_symb
% 3.45/0.98  --inst_solver_per_active                1400
% 3.45/0.98  --inst_solver_calls_frac                1.
% 3.45/0.98  --inst_passive_queue_type               priority_queues
% 3.45/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.45/0.98  --inst_passive_queues_freq              [25;2]
% 3.45/0.98  --inst_dismatching                      true
% 3.45/0.98  --inst_eager_unprocessed_to_passive     true
% 3.45/0.98  --inst_prop_sim_given                   true
% 3.45/0.98  --inst_prop_sim_new                     false
% 3.45/0.98  --inst_subs_new                         false
% 3.45/0.98  --inst_eq_res_simp                      false
% 3.45/0.98  --inst_subs_given                       false
% 3.45/0.98  --inst_orphan_elimination               true
% 3.45/0.98  --inst_learning_loop_flag               true
% 3.45/0.98  --inst_learning_start                   3000
% 3.45/0.98  --inst_learning_factor                  2
% 3.45/0.98  --inst_start_prop_sim_after_learn       3
% 3.45/0.98  --inst_sel_renew                        solver
% 3.45/0.98  --inst_lit_activity_flag                true
% 3.45/0.98  --inst_restr_to_given                   false
% 3.45/0.98  --inst_activity_threshold               500
% 3.45/0.98  --inst_out_proof                        true
% 3.45/0.98  
% 3.45/0.98  ------ Resolution Options
% 3.45/0.98  
% 3.45/0.98  --resolution_flag                       true
% 3.45/0.98  --res_lit_sel                           adaptive
% 3.45/0.98  --res_lit_sel_side                      none
% 3.45/0.98  --res_ordering                          kbo
% 3.45/0.98  --res_to_prop_solver                    active
% 3.45/0.98  --res_prop_simpl_new                    false
% 3.45/0.98  --res_prop_simpl_given                  true
% 3.45/0.98  --res_passive_queue_type                priority_queues
% 3.45/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.45/0.98  --res_passive_queues_freq               [15;5]
% 3.45/0.98  --res_forward_subs                      full
% 3.45/0.98  --res_backward_subs                     full
% 3.45/0.98  --res_forward_subs_resolution           true
% 3.45/0.98  --res_backward_subs_resolution          true
% 3.45/0.98  --res_orphan_elimination                true
% 3.45/0.98  --res_time_limit                        2.
% 3.45/0.98  --res_out_proof                         true
% 3.45/0.98  
% 3.45/0.98  ------ Superposition Options
% 3.45/0.98  
% 3.45/0.98  --superposition_flag                    true
% 3.45/0.98  --sup_passive_queue_type                priority_queues
% 3.45/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.45/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.45/0.98  --demod_completeness_check              fast
% 3.45/0.98  --demod_use_ground                      true
% 3.45/0.98  --sup_to_prop_solver                    passive
% 3.45/0.98  --sup_prop_simpl_new                    true
% 3.45/0.98  --sup_prop_simpl_given                  true
% 3.45/0.98  --sup_fun_splitting                     true
% 3.45/0.98  --sup_smt_interval                      50000
% 3.45/0.98  
% 3.45/0.98  ------ Superposition Simplification Setup
% 3.45/0.98  
% 3.45/0.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.45/0.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.45/0.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.45/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.45/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.45/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.45/0.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.45/0.98  --sup_immed_triv                        [TrivRules]
% 3.45/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.45/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.45/0.98  --sup_immed_bw_main                     []
% 3.45/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.45/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.45/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.45/0.98  --sup_input_bw                          []
% 3.45/0.98  
% 3.45/0.98  ------ Combination Options
% 3.45/0.98  
% 3.45/0.98  --comb_res_mult                         3
% 3.45/0.98  --comb_sup_mult                         2
% 3.45/0.98  --comb_inst_mult                        10
% 3.45/0.98  
% 3.45/0.98  ------ Debug Options
% 3.45/0.98  
% 3.45/0.98  --dbg_backtrace                         false
% 3.45/0.98  --dbg_dump_prop_clauses                 false
% 3.45/0.98  --dbg_dump_prop_clauses_file            -
% 3.45/0.98  --dbg_out_stat                          false
% 3.45/0.98  ------ Parsing...
% 3.45/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.45/0.98  
% 3.45/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.45/0.98  
% 3.45/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.45/0.98  
% 3.45/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.45/0.98  ------ Proving...
% 3.45/0.98  ------ Problem Properties 
% 3.45/0.98  
% 3.45/0.98  
% 3.45/0.98  clauses                                 14
% 3.45/0.98  conjectures                             3
% 3.45/0.98  EPR                                     3
% 3.45/0.98  Horn                                    10
% 3.45/0.98  unary                                   3
% 3.45/0.98  binary                                  5
% 3.45/0.98  lits                                    33
% 3.45/0.98  lits eq                                 7
% 3.45/0.98  fd_pure                                 0
% 3.45/0.98  fd_pseudo                               0
% 3.45/0.98  fd_cond                                 0
% 3.45/0.98  fd_pseudo_cond                          4
% 3.45/0.98  AC symbols                              0
% 3.45/0.98  
% 3.45/0.98  ------ Schedule dynamic 5 is on 
% 3.45/0.98  
% 3.45/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.45/0.98  
% 3.45/0.98  
% 3.45/0.98  ------ 
% 3.45/0.98  Current options:
% 3.45/0.98  ------ 
% 3.45/0.98  
% 3.45/0.98  ------ Input Options
% 3.45/0.98  
% 3.45/0.98  --out_options                           all
% 3.45/0.98  --tptp_safe_out                         true
% 3.45/0.98  --problem_path                          ""
% 3.45/0.98  --include_path                          ""
% 3.45/0.98  --clausifier                            res/vclausify_rel
% 3.45/0.98  --clausifier_options                    ""
% 3.45/0.98  --stdin                                 false
% 3.45/0.98  --stats_out                             all
% 3.45/0.98  
% 3.45/0.98  ------ General Options
% 3.45/0.98  
% 3.45/0.98  --fof                                   false
% 3.45/0.98  --time_out_real                         305.
% 3.45/0.98  --time_out_virtual                      -1.
% 3.45/0.98  --symbol_type_check                     false
% 3.45/0.98  --clausify_out                          false
% 3.45/0.98  --sig_cnt_out                           false
% 3.45/0.98  --trig_cnt_out                          false
% 3.45/0.98  --trig_cnt_out_tolerance                1.
% 3.45/0.98  --trig_cnt_out_sk_spl                   false
% 3.45/0.98  --abstr_cl_out                          false
% 3.45/0.98  
% 3.45/0.98  ------ Global Options
% 3.45/0.98  
% 3.45/0.98  --schedule                              default
% 3.45/0.98  --add_important_lit                     false
% 3.45/0.98  --prop_solver_per_cl                    1000
% 3.45/0.98  --min_unsat_core                        false
% 3.45/0.98  --soft_assumptions                      false
% 3.45/0.98  --soft_lemma_size                       3
% 3.45/0.98  --prop_impl_unit_size                   0
% 3.45/0.98  --prop_impl_unit                        []
% 3.45/0.98  --share_sel_clauses                     true
% 3.45/0.98  --reset_solvers                         false
% 3.45/0.98  --bc_imp_inh                            [conj_cone]
% 3.45/0.98  --conj_cone_tolerance                   3.
% 3.45/0.98  --extra_neg_conj                        none
% 3.45/0.98  --large_theory_mode                     true
% 3.45/0.98  --prolific_symb_bound                   200
% 3.45/0.98  --lt_threshold                          2000
% 3.45/0.98  --clause_weak_htbl                      true
% 3.45/0.98  --gc_record_bc_elim                     false
% 3.45/0.98  
% 3.45/0.98  ------ Preprocessing Options
% 3.45/0.98  
% 3.45/0.98  --preprocessing_flag                    true
% 3.45/0.98  --time_out_prep_mult                    0.1
% 3.45/0.98  --splitting_mode                        input
% 3.45/0.98  --splitting_grd                         true
% 3.45/0.98  --splitting_cvd                         false
% 3.45/0.98  --splitting_cvd_svl                     false
% 3.45/0.98  --splitting_nvd                         32
% 3.45/0.98  --sub_typing                            true
% 3.45/0.98  --prep_gs_sim                           true
% 3.45/0.98  --prep_unflatten                        true
% 3.45/0.98  --prep_res_sim                          true
% 3.45/0.98  --prep_upred                            true
% 3.45/0.98  --prep_sem_filter                       exhaustive
% 3.45/0.98  --prep_sem_filter_out                   false
% 3.45/0.98  --pred_elim                             true
% 3.45/0.98  --res_sim_input                         true
% 3.45/0.98  --eq_ax_congr_red                       true
% 3.45/0.98  --pure_diseq_elim                       true
% 3.45/0.98  --brand_transform                       false
% 3.45/0.98  --non_eq_to_eq                          false
% 3.45/0.98  --prep_def_merge                        true
% 3.45/0.98  --prep_def_merge_prop_impl              false
% 3.45/0.98  --prep_def_merge_mbd                    true
% 3.45/0.98  --prep_def_merge_tr_red                 false
% 3.45/0.98  --prep_def_merge_tr_cl                  false
% 3.45/0.98  --smt_preprocessing                     true
% 3.45/0.98  --smt_ac_axioms                         fast
% 3.45/0.98  --preprocessed_out                      false
% 3.45/0.98  --preprocessed_stats                    false
% 3.45/0.98  
% 3.45/0.98  ------ Abstraction refinement Options
% 3.45/0.98  
% 3.45/0.98  --abstr_ref                             []
% 3.45/0.98  --abstr_ref_prep                        false
% 3.45/0.98  --abstr_ref_until_sat                   false
% 3.45/0.98  --abstr_ref_sig_restrict                funpre
% 3.45/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.45/0.98  --abstr_ref_under                       []
% 3.45/0.98  
% 3.45/0.98  ------ SAT Options
% 3.45/0.98  
% 3.45/0.98  --sat_mode                              false
% 3.45/0.98  --sat_fm_restart_options                ""
% 3.45/0.98  --sat_gr_def                            false
% 3.45/0.98  --sat_epr_types                         true
% 3.45/0.98  --sat_non_cyclic_types                  false
% 3.45/0.98  --sat_finite_models                     false
% 3.45/0.98  --sat_fm_lemmas                         false
% 3.45/0.98  --sat_fm_prep                           false
% 3.45/0.98  --sat_fm_uc_incr                        true
% 3.45/0.98  --sat_out_model                         small
% 3.45/0.98  --sat_out_clauses                       false
% 3.45/0.98  
% 3.45/0.98  ------ QBF Options
% 3.45/0.98  
% 3.45/0.98  --qbf_mode                              false
% 3.45/0.98  --qbf_elim_univ                         false
% 3.45/0.98  --qbf_dom_inst                          none
% 3.45/0.98  --qbf_dom_pre_inst                      false
% 3.45/0.98  --qbf_sk_in                             false
% 3.45/0.98  --qbf_pred_elim                         true
% 3.45/0.98  --qbf_split                             512
% 3.45/0.98  
% 3.45/0.98  ------ BMC1 Options
% 3.45/0.98  
% 3.45/0.98  --bmc1_incremental                      false
% 3.45/0.98  --bmc1_axioms                           reachable_all
% 3.45/0.98  --bmc1_min_bound                        0
% 3.45/0.98  --bmc1_max_bound                        -1
% 3.45/0.98  --bmc1_max_bound_default                -1
% 3.45/0.98  --bmc1_symbol_reachability              true
% 3.45/0.98  --bmc1_property_lemmas                  false
% 3.45/0.98  --bmc1_k_induction                      false
% 3.45/0.98  --bmc1_non_equiv_states                 false
% 3.45/0.98  --bmc1_deadlock                         false
% 3.45/0.98  --bmc1_ucm                              false
% 3.45/0.98  --bmc1_add_unsat_core                   none
% 3.45/0.98  --bmc1_unsat_core_children              false
% 3.45/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.45/0.98  --bmc1_out_stat                         full
% 3.45/0.98  --bmc1_ground_init                      false
% 3.45/0.98  --bmc1_pre_inst_next_state              false
% 3.45/0.98  --bmc1_pre_inst_state                   false
% 3.45/0.98  --bmc1_pre_inst_reach_state             false
% 3.45/0.98  --bmc1_out_unsat_core                   false
% 3.45/0.98  --bmc1_aig_witness_out                  false
% 3.45/0.98  --bmc1_verbose                          false
% 3.45/0.98  --bmc1_dump_clauses_tptp                false
% 3.45/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.45/0.98  --bmc1_dump_file                        -
% 3.45/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.45/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.45/0.98  --bmc1_ucm_extend_mode                  1
% 3.45/0.98  --bmc1_ucm_init_mode                    2
% 3.45/0.98  --bmc1_ucm_cone_mode                    none
% 3.45/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.45/0.98  --bmc1_ucm_relax_model                  4
% 3.45/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.45/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.45/0.98  --bmc1_ucm_layered_model                none
% 3.45/0.98  --bmc1_ucm_max_lemma_size               10
% 3.45/0.98  
% 3.45/0.98  ------ AIG Options
% 3.45/0.98  
% 3.45/0.98  --aig_mode                              false
% 3.45/0.98  
% 3.45/0.98  ------ Instantiation Options
% 3.45/0.98  
% 3.45/0.98  --instantiation_flag                    true
% 3.45/0.98  --inst_sos_flag                         true
% 3.45/0.98  --inst_sos_phase                        true
% 3.45/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.45/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.45/0.98  --inst_lit_sel_side                     none
% 3.45/0.98  --inst_solver_per_active                1400
% 3.45/0.98  --inst_solver_calls_frac                1.
% 3.45/0.98  --inst_passive_queue_type               priority_queues
% 3.45/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.45/0.98  --inst_passive_queues_freq              [25;2]
% 3.45/0.98  --inst_dismatching                      true
% 3.45/0.98  --inst_eager_unprocessed_to_passive     true
% 3.45/0.98  --inst_prop_sim_given                   true
% 3.45/0.98  --inst_prop_sim_new                     false
% 3.45/0.98  --inst_subs_new                         false
% 3.45/0.98  --inst_eq_res_simp                      false
% 3.45/0.98  --inst_subs_given                       false
% 3.45/0.98  --inst_orphan_elimination               true
% 3.45/0.98  --inst_learning_loop_flag               true
% 3.45/0.98  --inst_learning_start                   3000
% 3.45/0.98  --inst_learning_factor                  2
% 3.45/0.98  --inst_start_prop_sim_after_learn       3
% 3.45/0.98  --inst_sel_renew                        solver
% 3.45/0.98  --inst_lit_activity_flag                true
% 3.45/0.98  --inst_restr_to_given                   false
% 3.45/0.98  --inst_activity_threshold               500
% 3.45/0.98  --inst_out_proof                        true
% 3.45/0.98  
% 3.45/0.98  ------ Resolution Options
% 3.45/0.98  
% 3.45/0.98  --resolution_flag                       false
% 3.45/0.98  --res_lit_sel                           adaptive
% 3.45/0.98  --res_lit_sel_side                      none
% 3.45/0.98  --res_ordering                          kbo
% 3.45/0.98  --res_to_prop_solver                    active
% 3.45/0.98  --res_prop_simpl_new                    false
% 3.45/0.98  --res_prop_simpl_given                  true
% 3.45/0.98  --res_passive_queue_type                priority_queues
% 3.45/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.45/0.98  --res_passive_queues_freq               [15;5]
% 3.45/0.98  --res_forward_subs                      full
% 3.45/0.98  --res_backward_subs                     full
% 3.45/0.98  --res_forward_subs_resolution           true
% 3.45/0.98  --res_backward_subs_resolution          true
% 3.45/0.98  --res_orphan_elimination                true
% 3.45/0.98  --res_time_limit                        2.
% 3.45/0.98  --res_out_proof                         true
% 3.45/0.98  
% 3.45/0.98  ------ Superposition Options
% 3.45/0.98  
% 3.45/0.98  --superposition_flag                    true
% 3.45/0.98  --sup_passive_queue_type                priority_queues
% 3.45/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.45/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.45/0.98  --demod_completeness_check              fast
% 3.45/0.98  --demod_use_ground                      true
% 3.45/0.98  --sup_to_prop_solver                    passive
% 3.45/0.98  --sup_prop_simpl_new                    true
% 3.45/0.98  --sup_prop_simpl_given                  true
% 3.45/0.98  --sup_fun_splitting                     true
% 3.45/0.98  --sup_smt_interval                      50000
% 3.45/0.98  
% 3.45/0.98  ------ Superposition Simplification Setup
% 3.45/0.98  
% 3.45/0.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.45/0.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.45/0.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.45/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.45/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.45/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.45/0.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.45/0.98  --sup_immed_triv                        [TrivRules]
% 3.45/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.45/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.45/0.98  --sup_immed_bw_main                     []
% 3.45/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.45/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.45/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.45/0.98  --sup_input_bw                          []
% 3.45/0.98  
% 3.45/0.98  ------ Combination Options
% 3.45/0.98  
% 3.45/0.98  --comb_res_mult                         3
% 3.45/0.98  --comb_sup_mult                         2
% 3.45/0.98  --comb_inst_mult                        10
% 3.45/0.98  
% 3.45/0.98  ------ Debug Options
% 3.45/0.98  
% 3.45/0.98  --dbg_backtrace                         false
% 3.45/0.98  --dbg_dump_prop_clauses                 false
% 3.45/0.98  --dbg_dump_prop_clauses_file            -
% 3.45/0.98  --dbg_out_stat                          false
% 3.45/0.98  
% 3.45/0.98  
% 3.45/0.98  
% 3.45/0.98  
% 3.45/0.98  ------ Proving...
% 3.45/0.98  
% 3.45/0.98  
% 3.45/0.98  % SZS status Theorem for theBenchmark.p
% 3.45/0.98  
% 3.45/0.98   Resolution empty clause
% 3.45/0.98  
% 3.45/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.45/0.98  
% 3.45/0.98  fof(f1,axiom,(
% 3.45/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.45/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/0.98  
% 3.45/0.98  fof(f5,plain,(
% 3.45/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.45/0.98    inference(ennf_transformation,[],[f1])).
% 3.45/0.98  
% 3.45/0.98  fof(f8,plain,(
% 3.45/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.45/0.98    inference(nnf_transformation,[],[f5])).
% 3.45/0.98  
% 3.45/0.98  fof(f9,plain,(
% 3.45/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.45/0.98    inference(rectify,[],[f8])).
% 3.45/0.98  
% 3.45/0.98  fof(f10,plain,(
% 3.45/0.98    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.45/0.98    introduced(choice_axiom,[])).
% 3.45/0.98  
% 3.45/0.98  fof(f11,plain,(
% 3.45/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.45/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f10])).
% 3.45/0.98  
% 3.45/0.98  fof(f21,plain,(
% 3.45/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.45/0.98    inference(cnf_transformation,[],[f11])).
% 3.45/0.98  
% 3.45/0.98  fof(f22,plain,(
% 3.45/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 3.45/0.98    inference(cnf_transformation,[],[f11])).
% 3.45/0.98  
% 3.45/0.98  fof(f3,conjecture,(
% 3.45/0.98    ! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))),
% 3.45/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/0.98  
% 3.45/0.98  fof(f4,negated_conjecture,(
% 3.45/0.98    ~! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))),
% 3.45/0.98    inference(negated_conjecture,[],[f3])).
% 3.45/0.98  
% 3.45/0.98  fof(f6,plain,(
% 3.45/0.98    ? [X0,X1,X2,X3] : (~r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) & (r1_tarski(X2,X3) & r1_tarski(X0,X1)))),
% 3.45/0.98    inference(ennf_transformation,[],[f4])).
% 3.45/0.98  
% 3.45/0.98  fof(f7,plain,(
% 3.45/0.98    ? [X0,X1,X2,X3] : (~r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) & r1_tarski(X2,X3) & r1_tarski(X0,X1))),
% 3.45/0.98    inference(flattening,[],[f6])).
% 3.45/0.98  
% 3.45/0.98  fof(f18,plain,(
% 3.45/0.98    ? [X0,X1,X2,X3] : (~r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) & r1_tarski(X2,X3) & r1_tarski(X0,X1)) => (~r1_tarski(k2_zfmisc_1(sK6,sK8),k2_zfmisc_1(sK7,sK9)) & r1_tarski(sK8,sK9) & r1_tarski(sK6,sK7))),
% 3.45/0.98    introduced(choice_axiom,[])).
% 3.45/0.98  
% 3.45/0.98  fof(f19,plain,(
% 3.45/0.98    ~r1_tarski(k2_zfmisc_1(sK6,sK8),k2_zfmisc_1(sK7,sK9)) & r1_tarski(sK8,sK9) & r1_tarski(sK6,sK7)),
% 3.45/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f7,f18])).
% 3.45/0.98  
% 3.45/0.98  fof(f31,plain,(
% 3.45/0.98    r1_tarski(sK6,sK7)),
% 3.45/0.98    inference(cnf_transformation,[],[f19])).
% 3.45/0.98  
% 3.45/0.98  fof(f2,axiom,(
% 3.45/0.98    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 3.45/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/0.98  
% 3.45/0.98  fof(f12,plain,(
% 3.45/0.98    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 3.45/0.98    inference(nnf_transformation,[],[f2])).
% 3.45/0.98  
% 3.45/0.98  fof(f13,plain,(
% 3.45/0.98    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 3.45/0.98    inference(rectify,[],[f12])).
% 3.45/0.98  
% 3.45/0.98  fof(f16,plain,(
% 3.45/0.98    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) => (k4_tarski(sK4(X0,X1,X8),sK5(X0,X1,X8)) = X8 & r2_hidden(sK5(X0,X1,X8),X1) & r2_hidden(sK4(X0,X1,X8),X0)))),
% 3.45/0.98    introduced(choice_axiom,[])).
% 3.45/0.98  
% 3.45/0.98  fof(f15,plain,(
% 3.45/0.98    ( ! [X3] : (! [X2,X1,X0] : (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) => (k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)) = X3 & r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)))) )),
% 3.45/0.98    introduced(choice_axiom,[])).
% 3.45/0.98  
% 3.45/0.98  fof(f14,plain,(
% 3.45/0.98    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK1(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK1(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 3.45/0.98    introduced(choice_axiom,[])).
% 3.45/0.98  
% 3.45/0.98  fof(f17,plain,(
% 3.45/0.98    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ((! [X4,X5] : (k4_tarski(X4,X5) != sK1(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)) = sK1(X0,X1,X2) & r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & ((k4_tarski(sK4(X0,X1,X8),sK5(X0,X1,X8)) = X8 & r2_hidden(sK5(X0,X1,X8),X1) & r2_hidden(sK4(X0,X1,X8),X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 3.45/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f13,f16,f15,f14])).
% 3.45/0.98  
% 3.45/0.98  fof(f23,plain,(
% 3.45/0.98    ( ! [X2,X0,X8,X1] : (r2_hidden(sK4(X0,X1,X8),X0) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 3.45/0.98    inference(cnf_transformation,[],[f17])).
% 3.45/0.98  
% 3.45/0.98  fof(f38,plain,(
% 3.45/0.98    ( ! [X0,X8,X1] : (r2_hidden(sK4(X0,X1,X8),X0) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 3.45/0.98    inference(equality_resolution,[],[f23])).
% 3.45/0.98  
% 3.45/0.98  fof(f20,plain,(
% 3.45/0.98    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.45/0.98    inference(cnf_transformation,[],[f11])).
% 3.45/0.98  
% 3.45/0.98  fof(f32,plain,(
% 3.45/0.98    r1_tarski(sK8,sK9)),
% 3.45/0.98    inference(cnf_transformation,[],[f19])).
% 3.45/0.98  
% 3.45/0.98  fof(f24,plain,(
% 3.45/0.98    ( ! [X2,X0,X8,X1] : (r2_hidden(sK5(X0,X1,X8),X1) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 3.45/0.98    inference(cnf_transformation,[],[f17])).
% 3.45/0.98  
% 3.45/0.98  fof(f37,plain,(
% 3.45/0.98    ( ! [X0,X8,X1] : (r2_hidden(sK5(X0,X1,X8),X1) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 3.45/0.98    inference(equality_resolution,[],[f24])).
% 3.45/0.98  
% 3.45/0.98  fof(f25,plain,(
% 3.45/0.98    ( ! [X2,X0,X8,X1] : (k4_tarski(sK4(X0,X1,X8),sK5(X0,X1,X8)) = X8 | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 3.45/0.98    inference(cnf_transformation,[],[f17])).
% 3.45/0.98  
% 3.45/0.98  fof(f36,plain,(
% 3.45/0.98    ( ! [X0,X8,X1] : (k4_tarski(sK4(X0,X1,X8),sK5(X0,X1,X8)) = X8 | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 3.45/0.98    inference(equality_resolution,[],[f25])).
% 3.45/0.98  
% 3.45/0.98  fof(f33,plain,(
% 3.45/0.98    ~r1_tarski(k2_zfmisc_1(sK6,sK8),k2_zfmisc_1(sK7,sK9))),
% 3.45/0.98    inference(cnf_transformation,[],[f19])).
% 3.45/0.98  
% 3.45/0.98  fof(f26,plain,(
% 3.45/0.98    ( ! [X2,X0,X10,X8,X1,X9] : (r2_hidden(X8,X2) | k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0) | k2_zfmisc_1(X0,X1) != X2) )),
% 3.45/0.98    inference(cnf_transformation,[],[f17])).
% 3.45/0.98  
% 3.45/0.98  fof(f34,plain,(
% 3.45/0.98    ( ! [X2,X0,X10,X1,X9] : (r2_hidden(k4_tarski(X9,X10),X2) | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0) | k2_zfmisc_1(X0,X1) != X2) )),
% 3.45/0.98    inference(equality_resolution,[],[f26])).
% 3.45/0.98  
% 3.45/0.98  fof(f35,plain,(
% 3.45/0.98    ( ! [X0,X10,X1,X9] : (r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1)) | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0)) )),
% 3.45/0.98    inference(equality_resolution,[],[f34])).
% 3.45/0.98  
% 3.45/0.98  cnf(c_1,plain,
% 3.45/0.98      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.45/0.98      inference(cnf_transformation,[],[f21]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_496,plain,
% 3.45/0.98      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 3.45/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 3.45/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_0,plain,
% 3.45/0.98      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 3.45/0.98      inference(cnf_transformation,[],[f22]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_497,plain,
% 3.45/0.98      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 3.45/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 3.45/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_893,plain,
% 3.45/0.98      ( r1_tarski(X0,X0) = iProver_top ),
% 3.45/0.98      inference(superposition,[status(thm)],[c_496,c_497]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_13,negated_conjecture,
% 3.45/0.98      ( r1_tarski(sK6,sK7) ),
% 3.45/0.98      inference(cnf_transformation,[],[f31]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_484,plain,
% 3.45/0.98      ( r1_tarski(sK6,sK7) = iProver_top ),
% 3.45/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_10,plain,
% 3.45/0.98      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(sK4(X1,X2,X0),X1) ),
% 3.45/0.98      inference(cnf_transformation,[],[f38]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_487,plain,
% 3.45/0.98      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.45/0.98      | r2_hidden(sK4(X1,X2,X0),X1) = iProver_top ),
% 3.45/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_2,plain,
% 3.45/0.98      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 3.45/0.98      inference(cnf_transformation,[],[f20]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_495,plain,
% 3.45/0.98      ( r2_hidden(X0,X1) != iProver_top
% 3.45/0.98      | r2_hidden(X0,X2) = iProver_top
% 3.45/0.98      | r1_tarski(X1,X2) != iProver_top ),
% 3.45/0.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_788,plain,
% 3.45/0.98      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.45/0.98      | r2_hidden(sK4(X1,X2,X0),X3) = iProver_top
% 3.45/0.98      | r1_tarski(X1,X3) != iProver_top ),
% 3.45/0.98      inference(superposition,[status(thm)],[c_487,c_495]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_1222,plain,
% 3.45/0.98      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.45/0.98      | r2_hidden(sK4(X1,X2,X0),X3) = iProver_top
% 3.45/0.98      | r1_tarski(X1,X4) != iProver_top
% 3.45/0.98      | r1_tarski(X4,X3) != iProver_top ),
% 3.45/0.98      inference(superposition,[status(thm)],[c_788,c_495]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_6065,plain,
% 3.45/0.98      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.45/0.98      | r2_hidden(sK4(X1,X2,X0),sK7) = iProver_top
% 3.45/0.98      | r1_tarski(X1,sK6) != iProver_top ),
% 3.45/0.98      inference(superposition,[status(thm)],[c_484,c_1222]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_12,negated_conjecture,
% 3.45/0.98      ( r1_tarski(sK8,sK9) ),
% 3.45/0.98      inference(cnf_transformation,[],[f32]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_485,plain,
% 3.45/0.98      ( r1_tarski(sK8,sK9) = iProver_top ),
% 3.45/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_9,plain,
% 3.45/0.98      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(sK5(X1,X2,X0),X2) ),
% 3.45/0.98      inference(cnf_transformation,[],[f37]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_488,plain,
% 3.45/0.98      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.45/0.98      | r2_hidden(sK5(X1,X2,X0),X2) = iProver_top ),
% 3.45/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_787,plain,
% 3.45/0.98      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.45/0.98      | r2_hidden(sK5(X1,X2,X0),X3) = iProver_top
% 3.45/0.98      | r1_tarski(X2,X3) != iProver_top ),
% 3.45/0.98      inference(superposition,[status(thm)],[c_488,c_495]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_1215,plain,
% 3.45/0.98      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.45/0.98      | r2_hidden(sK5(X1,X2,X0),X3) = iProver_top
% 3.45/0.98      | r1_tarski(X2,X4) != iProver_top
% 3.45/0.98      | r1_tarski(X4,X3) != iProver_top ),
% 3.45/0.98      inference(superposition,[status(thm)],[c_787,c_495]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_1465,plain,
% 3.45/0.98      ( r2_hidden(X0,k2_zfmisc_1(X1,sK8)) != iProver_top
% 3.45/0.98      | r2_hidden(sK5(X1,sK8,X0),X2) = iProver_top
% 3.45/0.98      | r1_tarski(sK9,X2) != iProver_top ),
% 3.45/0.98      inference(superposition,[status(thm)],[c_485,c_1215]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_8,plain,
% 3.45/0.98      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 3.45/0.98      | k4_tarski(sK4(X1,X2,X0),sK5(X1,X2,X0)) = X0 ),
% 3.45/0.98      inference(cnf_transformation,[],[f36]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_489,plain,
% 3.45/0.98      ( k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)) = X2
% 3.45/0.98      | r2_hidden(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 3.45/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_895,plain,
% 3.45/0.98      ( k4_tarski(sK4(X0,X1,sK0(k2_zfmisc_1(X0,X1),X2)),sK5(X0,X1,sK0(k2_zfmisc_1(X0,X1),X2))) = sK0(k2_zfmisc_1(X0,X1),X2)
% 3.45/0.98      | r1_tarski(k2_zfmisc_1(X0,X1),X2) = iProver_top ),
% 3.45/0.98      inference(superposition,[status(thm)],[c_496,c_489]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_11,negated_conjecture,
% 3.45/0.98      ( ~ r1_tarski(k2_zfmisc_1(sK6,sK8),k2_zfmisc_1(sK7,sK9)) ),
% 3.45/0.98      inference(cnf_transformation,[],[f33]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_486,plain,
% 3.45/0.98      ( r1_tarski(k2_zfmisc_1(sK6,sK8),k2_zfmisc_1(sK7,sK9)) != iProver_top ),
% 3.45/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_4441,plain,
% 3.45/0.98      ( k4_tarski(sK4(sK6,sK8,sK0(k2_zfmisc_1(sK6,sK8),k2_zfmisc_1(sK7,sK9))),sK5(sK6,sK8,sK0(k2_zfmisc_1(sK6,sK8),k2_zfmisc_1(sK7,sK9)))) = sK0(k2_zfmisc_1(sK6,sK8),k2_zfmisc_1(sK7,sK9)) ),
% 3.45/0.98      inference(superposition,[status(thm)],[c_895,c_486]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_7,plain,
% 3.45/0.98      ( ~ r2_hidden(X0,X1)
% 3.45/0.98      | ~ r2_hidden(X2,X3)
% 3.45/0.98      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 3.45/0.98      inference(cnf_transformation,[],[f35]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_490,plain,
% 3.45/0.98      ( r2_hidden(X0,X1) != iProver_top
% 3.45/0.98      | r2_hidden(X2,X3) != iProver_top
% 3.45/0.98      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
% 3.45/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_4758,plain,
% 3.45/0.98      ( r2_hidden(sK5(sK6,sK8,sK0(k2_zfmisc_1(sK6,sK8),k2_zfmisc_1(sK7,sK9))),X0) != iProver_top
% 3.45/0.98      | r2_hidden(sK4(sK6,sK8,sK0(k2_zfmisc_1(sK6,sK8),k2_zfmisc_1(sK7,sK9))),X1) != iProver_top
% 3.45/0.98      | r2_hidden(sK0(k2_zfmisc_1(sK6,sK8),k2_zfmisc_1(sK7,sK9)),k2_zfmisc_1(X1,X0)) = iProver_top ),
% 3.45/0.98      inference(superposition,[status(thm)],[c_4441,c_490]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_4825,plain,
% 3.45/0.98      ( r2_hidden(sK4(sK6,sK8,sK0(k2_zfmisc_1(sK6,sK8),k2_zfmisc_1(sK7,sK9))),X0) != iProver_top
% 3.45/0.98      | r2_hidden(sK0(k2_zfmisc_1(sK6,sK8),k2_zfmisc_1(sK7,sK9)),k2_zfmisc_1(X0,X1)) = iProver_top
% 3.45/0.98      | r2_hidden(sK0(k2_zfmisc_1(sK6,sK8),k2_zfmisc_1(sK7,sK9)),k2_zfmisc_1(sK6,sK8)) != iProver_top
% 3.45/0.98      | r1_tarski(sK9,X1) != iProver_top ),
% 3.45/0.98      inference(superposition,[status(thm)],[c_1465,c_4758]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_184,plain,
% 3.45/0.98      ( r2_hidden(sK0(X0,X1),X0)
% 3.45/0.98      | k2_zfmisc_1(sK7,sK9) != X1
% 3.45/0.98      | k2_zfmisc_1(sK6,sK8) != X0 ),
% 3.45/0.98      inference(resolution_lifted,[status(thm)],[c_1,c_11]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_185,plain,
% 3.45/0.98      ( r2_hidden(sK0(k2_zfmisc_1(sK6,sK8),k2_zfmisc_1(sK7,sK9)),k2_zfmisc_1(sK6,sK8)) ),
% 3.45/0.98      inference(unflattening,[status(thm)],[c_184]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_186,plain,
% 3.45/0.98      ( r2_hidden(sK0(k2_zfmisc_1(sK6,sK8),k2_zfmisc_1(sK7,sK9)),k2_zfmisc_1(sK6,sK8)) = iProver_top ),
% 3.45/0.98      inference(predicate_to_equality,[status(thm)],[c_185]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_4845,plain,
% 3.45/0.98      ( r2_hidden(sK0(k2_zfmisc_1(sK6,sK8),k2_zfmisc_1(sK7,sK9)),k2_zfmisc_1(X0,X1)) = iProver_top
% 3.45/0.98      | r2_hidden(sK4(sK6,sK8,sK0(k2_zfmisc_1(sK6,sK8),k2_zfmisc_1(sK7,sK9))),X0) != iProver_top
% 3.45/0.98      | r1_tarski(sK9,X1) != iProver_top ),
% 3.45/0.98      inference(global_propositional_subsumption,[status(thm)],[c_4825,c_186]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_4846,plain,
% 3.45/0.98      ( r2_hidden(sK4(sK6,sK8,sK0(k2_zfmisc_1(sK6,sK8),k2_zfmisc_1(sK7,sK9))),X0) != iProver_top
% 3.45/0.98      | r2_hidden(sK0(k2_zfmisc_1(sK6,sK8),k2_zfmisc_1(sK7,sK9)),k2_zfmisc_1(X0,X1)) = iProver_top
% 3.45/0.98      | r1_tarski(sK9,X1) != iProver_top ),
% 3.45/0.98      inference(renaming,[status(thm)],[c_4845]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_6237,plain,
% 3.45/0.98      ( r2_hidden(sK0(k2_zfmisc_1(sK6,sK8),k2_zfmisc_1(sK7,sK9)),k2_zfmisc_1(sK7,X0)) = iProver_top
% 3.45/0.98      | r2_hidden(sK0(k2_zfmisc_1(sK6,sK8),k2_zfmisc_1(sK7,sK9)),k2_zfmisc_1(sK6,sK8)) != iProver_top
% 3.45/0.98      | r1_tarski(sK9,X0) != iProver_top
% 3.45/0.98      | r1_tarski(sK6,sK6) != iProver_top ),
% 3.45/0.98      inference(superposition,[status(thm)],[c_6065,c_4846]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_897,plain,
% 3.45/0.98      ( r1_tarski(sK6,sK6) = iProver_top ),
% 3.45/0.98      inference(instantiation,[status(thm)],[c_893]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_7381,plain,
% 3.45/0.98      ( r1_tarski(sK9,X0) != iProver_top
% 3.45/0.98      | r2_hidden(sK0(k2_zfmisc_1(sK6,sK8),k2_zfmisc_1(sK7,sK9)),k2_zfmisc_1(sK7,X0)) = iProver_top ),
% 3.45/0.98      inference(global_propositional_subsumption,
% 3.45/0.98                [status(thm)],
% 3.45/0.98                [c_6237,c_186,c_897]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_7382,plain,
% 3.45/0.98      ( r2_hidden(sK0(k2_zfmisc_1(sK6,sK8),k2_zfmisc_1(sK7,sK9)),k2_zfmisc_1(sK7,X0)) = iProver_top
% 3.45/0.98      | r1_tarski(sK9,X0) != iProver_top ),
% 3.45/0.98      inference(renaming,[status(thm)],[c_7381]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_7387,plain,
% 3.45/0.98      ( r1_tarski(k2_zfmisc_1(sK6,sK8),k2_zfmisc_1(sK7,sK9)) = iProver_top
% 3.45/0.98      | r1_tarski(sK9,sK9) != iProver_top ),
% 3.45/0.98      inference(superposition,[status(thm)],[c_7382,c_497]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_16,plain,
% 3.45/0.98      ( r1_tarski(k2_zfmisc_1(sK6,sK8),k2_zfmisc_1(sK7,sK9)) != iProver_top ),
% 3.45/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_8835,plain,
% 3.45/0.98      ( r1_tarski(sK9,sK9) != iProver_top ),
% 3.45/0.98      inference(global_propositional_subsumption,[status(thm)],[c_7387,c_16]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_8839,plain,
% 3.45/0.98      ( $false ),
% 3.45/0.98      inference(superposition,[status(thm)],[c_893,c_8835]) ).
% 3.45/0.98  
% 3.45/0.98  
% 3.45/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.45/0.98  
% 3.45/0.98  ------                               Statistics
% 3.45/0.98  
% 3.45/0.98  ------ General
% 3.45/0.98  
% 3.45/0.98  abstr_ref_over_cycles:                  0
% 3.45/0.98  abstr_ref_under_cycles:                 0
% 3.45/0.98  gc_basic_clause_elim:                   0
% 3.45/0.98  forced_gc_time:                         0
% 3.45/0.98  parsing_time:                           0.008
% 3.45/0.98  unif_index_cands_time:                  0.
% 3.45/0.98  unif_index_add_time:                    0.
% 3.45/0.98  orderings_time:                         0.
% 3.45/0.98  out_proof_time:                         0.009
% 3.45/0.98  total_time:                             0.35
% 3.45/0.98  num_of_symbols:                         45
% 3.45/0.98  num_of_terms:                           16916
% 3.45/0.98  
% 3.45/0.98  ------ Preprocessing
% 3.45/0.98  
% 3.45/0.98  num_of_splits:                          0
% 3.45/0.98  num_of_split_atoms:                     0
% 3.45/0.98  num_of_reused_defs:                     0
% 3.45/0.98  num_eq_ax_congr_red:                    34
% 3.45/0.98  num_of_sem_filtered_clauses:            1
% 3.45/0.98  num_of_subtypes:                        0
% 3.45/0.98  monotx_restored_types:                  0
% 3.45/0.98  sat_num_of_epr_types:                   0
% 3.45/0.98  sat_num_of_non_cyclic_types:            0
% 3.45/0.98  sat_guarded_non_collapsed_types:        0
% 3.45/0.98  num_pure_diseq_elim:                    0
% 3.45/0.98  simp_replaced_by:                       0
% 3.45/0.98  res_preprocessed:                       55
% 3.45/0.98  prep_upred:                             0
% 3.45/0.98  prep_unflattend:                        12
% 3.45/0.98  smt_new_axioms:                         0
% 3.45/0.98  pred_elim_cands:                        2
% 3.45/0.98  pred_elim:                              0
% 3.45/0.98  pred_elim_cl:                           0
% 3.45/0.98  pred_elim_cycles:                       1
% 3.45/0.98  merged_defs:                            0
% 3.45/0.98  merged_defs_ncl:                        0
% 3.45/0.98  bin_hyper_res:                          0
% 3.45/0.98  prep_cycles:                            3
% 3.45/0.98  pred_elim_time:                         0.
% 3.45/0.98  splitting_time:                         0.
% 3.45/0.98  sem_filter_time:                        0.
% 3.45/0.98  monotx_time:                            0.
% 3.45/0.98  subtype_inf_time:                       0.
% 3.45/0.98  
% 3.45/0.98  ------ Problem properties
% 3.45/0.98  
% 3.45/0.98  clauses:                                14
% 3.45/0.98  conjectures:                            3
% 3.45/0.98  epr:                                    3
% 3.45/0.98  horn:                                   10
% 3.45/0.98  ground:                                 3
% 3.45/0.98  unary:                                  3
% 3.45/0.98  binary:                                 5
% 3.45/0.98  lits:                                   33
% 3.45/0.98  lits_eq:                                7
% 3.45/0.98  fd_pure:                                0
% 3.45/0.98  fd_pseudo:                              0
% 3.45/0.98  fd_cond:                                0
% 3.45/0.98  fd_pseudo_cond:                         4
% 3.45/0.98  ac_symbols:                             0
% 3.45/0.98  
% 3.45/0.98  ------ Propositional Solver
% 3.45/0.98  
% 3.45/0.98  prop_solver_calls:                      25
% 3.45/0.98  prop_fast_solver_calls:                 643
% 3.45/0.98  smt_solver_calls:                       0
% 3.45/0.98  smt_fast_solver_calls:                  0
% 3.45/0.98  prop_num_of_clauses:                    5198
% 3.45/0.98  prop_preprocess_simplified:             5268
% 3.45/0.98  prop_fo_subsumed:                       17
% 3.45/0.98  prop_solver_time:                       0.
% 3.45/0.98  smt_solver_time:                        0.
% 3.45/0.98  smt_fast_solver_time:                   0.
% 3.45/0.98  prop_fast_solver_time:                  0.
% 3.45/0.98  prop_unsat_core_time:                   0.
% 3.45/0.98  
% 3.45/0.98  ------ QBF
% 3.45/0.98  
% 3.45/0.98  qbf_q_res:                              0
% 3.45/0.98  qbf_num_tautologies:                    0
% 3.45/0.98  qbf_prep_cycles:                        0
% 3.45/0.98  
% 3.45/0.98  ------ BMC1
% 3.45/0.98  
% 3.45/0.98  bmc1_current_bound:                     -1
% 3.45/0.98  bmc1_last_solved_bound:                 -1
% 3.45/0.98  bmc1_unsat_core_size:                   -1
% 3.45/0.98  bmc1_unsat_core_parents_size:           -1
% 3.45/0.98  bmc1_merge_next_fun:                    0
% 3.45/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.45/0.98  
% 3.45/0.98  ------ Instantiation
% 3.45/0.98  
% 3.45/0.98  inst_num_of_clauses:                    779
% 3.45/0.98  inst_num_in_passive:                    55
% 3.45/0.98  inst_num_in_active:                     360
% 3.45/0.98  inst_num_in_unprocessed:                364
% 3.45/0.98  inst_num_of_loops:                      500
% 3.45/0.98  inst_num_of_learning_restarts:          0
% 3.45/0.98  inst_num_moves_active_passive:          136
% 3.45/0.98  inst_lit_activity:                      0
% 3.45/0.98  inst_lit_activity_moves:                0
% 3.45/0.98  inst_num_tautologies:                   0
% 3.45/0.98  inst_num_prop_implied:                  0
% 3.45/0.98  inst_num_existing_simplified:           0
% 3.45/0.98  inst_num_eq_res_simplified:             0
% 3.45/0.98  inst_num_child_elim:                    0
% 3.45/0.98  inst_num_of_dismatching_blockings:      409
% 3.45/0.98  inst_num_of_non_proper_insts:           958
% 3.45/0.98  inst_num_of_duplicates:                 0
% 3.45/0.98  inst_inst_num_from_inst_to_res:         0
% 3.45/0.98  inst_dismatching_checking_time:         0.
% 3.45/0.98  
% 3.45/0.98  ------ Resolution
% 3.45/0.98  
% 3.45/0.98  res_num_of_clauses:                     0
% 3.45/0.98  res_num_in_passive:                     0
% 3.45/0.98  res_num_in_active:                      0
% 3.45/0.98  res_num_of_loops:                       58
% 3.45/0.98  res_forward_subset_subsumed:            97
% 3.45/0.98  res_backward_subset_subsumed:           0
% 3.45/0.98  res_forward_subsumed:                   0
% 3.45/0.98  res_backward_subsumed:                  0
% 3.45/0.98  res_forward_subsumption_resolution:     0
% 3.45/0.98  res_backward_subsumption_resolution:    0
% 3.45/0.98  res_clause_to_clause_subsumption:       3534
% 3.45/0.98  res_orphan_elimination:                 0
% 3.45/0.98  res_tautology_del:                      105
% 3.45/0.98  res_num_eq_res_simplified:              0
% 3.45/0.98  res_num_sel_changes:                    0
% 3.45/0.98  res_moves_from_active_to_pass:          0
% 3.45/0.98  
% 3.45/0.98  ------ Superposition
% 3.45/0.98  
% 3.45/0.98  sup_time_total:                         0.
% 3.45/0.98  sup_time_generating:                    0.
% 3.45/0.98  sup_time_sim_full:                      0.
% 3.45/0.98  sup_time_sim_immed:                     0.
% 3.45/0.98  
% 3.45/0.98  sup_num_of_clauses:                     739
% 3.45/0.98  sup_num_in_active:                      96
% 3.45/0.98  sup_num_in_passive:                     643
% 3.45/0.98  sup_num_of_loops:                       99
% 3.45/0.98  sup_fw_superposition:                   442
% 3.45/0.98  sup_bw_superposition:                   321
% 3.45/0.98  sup_immediate_simplified:               18
% 3.45/0.98  sup_given_eliminated:                   0
% 3.45/0.98  comparisons_done:                       0
% 3.45/0.98  comparisons_avoided:                    6
% 3.45/0.98  
% 3.45/0.98  ------ Simplifications
% 3.45/0.98  
% 3.45/0.98  
% 3.45/0.98  sim_fw_subset_subsumed:                 16
% 3.45/0.98  sim_bw_subset_subsumed:                 0
% 3.45/0.98  sim_fw_subsumed:                        2
% 3.45/0.98  sim_bw_subsumed:                        4
% 3.45/0.98  sim_fw_subsumption_res:                 0
% 3.45/0.98  sim_bw_subsumption_res:                 0
% 3.45/0.98  sim_tautology_del:                      1
% 3.45/0.98  sim_eq_tautology_del:                   0
% 3.45/0.98  sim_eq_res_simp:                        0
% 3.45/0.98  sim_fw_demodulated:                     0
% 3.45/0.98  sim_bw_demodulated:                     0
% 3.45/0.98  sim_light_normalised:                   0
% 3.45/0.98  sim_joinable_taut:                      0
% 3.45/0.98  sim_joinable_simp:                      0
% 3.45/0.98  sim_ac_normalised:                      0
% 3.45/0.98  sim_smt_subsumption:                    0
% 3.45/0.98  
%------------------------------------------------------------------------------
