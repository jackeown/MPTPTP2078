%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:41:29 EST 2020

% Result     : Theorem 7.48s
% Output     : CNFRefutation 7.48s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 141 expanded)
%              Number of clauses        :   41 (  44 expanded)
%              Number of leaves         :   16 (  34 expanded)
%              Depth                    :   10
%              Number of atoms          :  379 ( 684 expanded)
%              Number of equality atoms :   79 ( 101 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f33,plain,(
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
    inference(rectify,[],[f32])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK2(X0,X1,X2),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X0)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(sK2(X0,X1,X2),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK2(X0,X1,X2),X1)
            | ~ r2_hidden(sK2(X0,X1,X2),X0)
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f34])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f22])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f57,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f85,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f57])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = X0
       => ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 ) )
      & ( k1_xboole_0 != X0
       => ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X3,X0)
                 => r2_hidden(X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 )
        | k1_xboole_0 != X0 )
      & ( ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X2,X3)
                  | ~ r2_hidden(X3,X0) ) ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( ( ( k1_setfam_1(X0) = X1
            | ? [X2] :
                ( ( ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r2_hidden(X3,X0) )
                  | ~ r2_hidden(X2,X1) )
                & ( ! [X3] :
                      ( r2_hidden(X2,X3)
                      | ~ r2_hidden(X3,X0) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r2_hidden(X3,X0) ) )
                & ( ! [X3] :
                      ( r2_hidden(X2,X3)
                      | ~ r2_hidden(X3,X0) )
                  | ~ r2_hidden(X2,X1) ) )
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( ( ( k1_setfam_1(X0) = X1
            | ? [X2] :
                ( ( ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r2_hidden(X3,X0) )
                  | ~ r2_hidden(X2,X1) )
                & ( ! [X4] :
                      ( r2_hidden(X2,X4)
                      | ~ r2_hidden(X4,X0) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ? [X6] :
                      ( ~ r2_hidden(X5,X6)
                      & r2_hidden(X6,X0) ) )
                & ( ! [X7] :
                      ( r2_hidden(X5,X7)
                      | ~ r2_hidden(X7,X0) )
                  | ~ r2_hidden(X5,X1) ) )
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(rectify,[],[f39])).

fof(f43,plain,(
    ! [X5,X0] :
      ( ? [X6] :
          ( ~ r2_hidden(X5,X6)
          & r2_hidden(X6,X0) )
     => ( ~ r2_hidden(X5,sK6(X0,X5))
        & r2_hidden(sK6(X0,X5),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X2,X3)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(X2,sK5(X0,X1))
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( ~ r2_hidden(X2,X3)
                & r2_hidden(X3,X0) )
            | ~ r2_hidden(X2,X1) )
          & ( ! [X4] :
                ( r2_hidden(X2,X4)
                | ~ r2_hidden(X4,X0) )
            | r2_hidden(X2,X1) ) )
     => ( ( ? [X3] :
              ( ~ r2_hidden(sK4(X0,X1),X3)
              & r2_hidden(X3,X0) )
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( ! [X4] :
              ( r2_hidden(sK4(X0,X1),X4)
              | ~ r2_hidden(X4,X0) )
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( ( ( k1_setfam_1(X0) = X1
            | ( ( ( ~ r2_hidden(sK4(X0,X1),sK5(X0,X1))
                  & r2_hidden(sK5(X0,X1),X0) )
                | ~ r2_hidden(sK4(X0,X1),X1) )
              & ( ! [X4] :
                    ( r2_hidden(sK4(X0,X1),X4)
                    | ~ r2_hidden(X4,X0) )
                | r2_hidden(sK4(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ( ~ r2_hidden(X5,sK6(X0,X5))
                    & r2_hidden(sK6(X0,X5),X0) ) )
                & ( ! [X7] :
                      ( r2_hidden(X5,X7)
                      | ~ r2_hidden(X7,X0) )
                  | ~ r2_hidden(X5,X1) ) )
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f40,f43,f42,f41])).

fof(f70,plain,(
    ! [X0,X7,X5,X1] :
      ( r2_hidden(X5,X7)
      | ~ r2_hidden(X7,X0)
      | ~ r2_hidden(X5,X1)
      | k1_setfam_1(X0) != X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f93,plain,(
    ! [X0,X7,X5] :
      ( r2_hidden(X5,X7)
      | ~ r2_hidden(X7,X0)
      | ~ r2_hidden(X5,k1_setfam_1(X0))
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f70])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ! [X3] :
                  ~ ( r2_hidden(X3,X2)
                    & r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f37,plain,(
    ! [X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
     => ( ! [X3] :
            ( ~ r2_hidden(X3,sK3(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK3(X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,sK3(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK3(X1),X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f37])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X1),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r2_hidden(X0,X1) )
     => r1_tarski(k1_setfam_1(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_tarski(X0,X2)
          & r2_hidden(X0,X1) )
       => r1_tarski(k1_setfam_1(X1),X2) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k1_setfam_1(X1),X2)
      & r1_tarski(X0,X2)
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k1_setfam_1(X1),X2)
      & r1_tarski(X0,X2)
      & r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f45,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k1_setfam_1(X1),X2)
        & r1_tarski(X0,X2)
        & r2_hidden(X0,X1) )
   => ( ~ r1_tarski(k1_setfam_1(sK8),sK9)
      & r1_tarski(sK7,sK9)
      & r2_hidden(sK7,sK8) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ~ r1_tarski(k1_setfam_1(sK8),sK9)
    & r1_tarski(sK7,sK9)
    & r2_hidden(sK7,sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f21,f45])).

fof(f80,plain,(
    ~ r1_tarski(k1_setfam_1(sK8),sK9) ),
    inference(cnf_transformation,[],[f46])).

fof(f79,plain,(
    r1_tarski(sK7,sK9) ),
    inference(cnf_transformation,[],[f46])).

fof(f78,plain,(
    r2_hidden(sK7,sK8) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_10,plain,
    ( ~ r2_hidden(sK2(X0,X1,X2),X1)
    | r2_hidden(sK2(X0,X1,X2),X2)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_35871,plain,
    ( ~ r2_hidden(sK2(k1_setfam_1(sK8),sK9,k1_xboole_0),sK9)
    | r2_hidden(sK2(k1_setfam_1(sK8),sK9,k1_xboole_0),k1_xboole_0)
    | k4_xboole_0(k1_setfam_1(sK8),sK9) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_9935,plain,
    ( r2_hidden(sK2(k1_setfam_1(sK8),sK9,k1_xboole_0),X0)
    | ~ r2_hidden(sK2(k1_setfam_1(sK8),sK9,k1_xboole_0),sK7)
    | ~ r1_tarski(sK7,X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_19420,plain,
    ( ~ r2_hidden(sK2(k1_setfam_1(sK8),sK9,k1_xboole_0),sK7)
    | r2_hidden(sK2(k1_setfam_1(sK8),sK9,k1_xboole_0),sK9)
    | ~ r1_tarski(sK7,sK9) ),
    inference(instantiation,[status(thm)],[c_9935])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_14980,plain,
    ( ~ r2_hidden(sK3(X0),X1)
    | ~ r2_hidden(sK3(X0),k4_xboole_0(X2,X1)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_14986,plain,
    ( ~ r2_hidden(sK3(k1_xboole_0),k4_xboole_0(k1_xboole_0,k1_xboole_0))
    | ~ r2_hidden(sK3(k1_xboole_0),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_14980])).

cnf(c_2846,plain,
    ( ~ r2_hidden(sK3(X0),X0)
    | r2_hidden(sK3(X0),X1)
    | ~ r1_tarski(X0,X1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_14979,plain,
    ( ~ r2_hidden(sK3(X0),X0)
    | r2_hidden(sK3(X0),k4_xboole_0(X1,X2))
    | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_2846])).

cnf(c_14982,plain,
    ( r2_hidden(sK3(k1_xboole_0),k4_xboole_0(k1_xboole_0,k1_xboole_0))
    | ~ r2_hidden(sK3(k1_xboole_0),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_14979])).

cnf(c_30,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X0)
    | ~ r2_hidden(X2,k1_setfam_1(X1))
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_2128,plain,
    ( ~ r2_hidden(X0,sK8)
    | r2_hidden(sK2(k1_setfam_1(sK8),sK9,k1_xboole_0),X0)
    | ~ r2_hidden(sK2(k1_setfam_1(sK8),sK9,k1_xboole_0),k1_setfam_1(sK8))
    | k1_xboole_0 = sK8 ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_6354,plain,
    ( ~ r2_hidden(sK2(k1_setfam_1(sK8),sK9,k1_xboole_0),k1_setfam_1(sK8))
    | r2_hidden(sK2(k1_setfam_1(sK8),sK9,k1_xboole_0),sK7)
    | ~ r2_hidden(sK7,sK8)
    | k1_xboole_0 = sK8 ),
    inference(instantiation,[status(thm)],[c_2128])).

cnf(c_691,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_18,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_5991,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,k4_xboole_0(X0,X1))
    | ~ r1_tarski(X3,k1_xboole_0)
    | X2 != X3 ),
    inference(resolution,[status(thm)],[c_691,c_18])).

cnf(c_5993,plain,
    ( r1_tarski(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0))
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5991])).

cnf(c_22,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK3(X1),X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_3875,plain,
    ( ~ r2_hidden(sK2(k1_setfam_1(sK8),sK9,k1_xboole_0),k1_xboole_0)
    | r2_hidden(sK3(k1_xboole_0),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_689,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2726,plain,
    ( sK7 = sK7 ),
    inference(instantiation,[status(thm)],[c_689])).

cnf(c_692,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1734,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK7,sK8)
    | X0 != sK7
    | X1 != sK8 ),
    inference(instantiation,[status(thm)],[c_692])).

cnf(c_2725,plain,
    ( r2_hidden(sK7,X0)
    | ~ r2_hidden(sK7,sK8)
    | X0 != sK8
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_1734])).

cnf(c_2728,plain,
    ( ~ r2_hidden(sK7,sK8)
    | r2_hidden(sK7,k1_xboole_0)
    | sK7 != sK7
    | k1_xboole_0 != sK8 ),
    inference(instantiation,[status(thm)],[c_2725])).

cnf(c_1937,plain,
    ( r2_hidden(sK3(X0),X0)
    | ~ r2_hidden(sK7,X0) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_1939,plain,
    ( r2_hidden(sK3(k1_xboole_0),k1_xboole_0)
    | ~ r2_hidden(sK7,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1937])).

cnf(c_11,plain,
    ( r2_hidden(sK2(X0,X1,X2),X0)
    | r2_hidden(sK2(X0,X1,X2),X2)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1765,plain,
    ( r2_hidden(sK2(k1_setfam_1(sK8),sK9,k1_xboole_0),k1_setfam_1(sK8))
    | r2_hidden(sK2(k1_setfam_1(sK8),sK9,k1_xboole_0),k1_xboole_0)
    | k4_xboole_0(k1_setfam_1(sK8),sK9) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1757,plain,
    ( r1_tarski(X0,X0) ),
    inference(resolution,[status(thm)],[c_0,c_1])).

cnf(c_1759,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1757])).

cnf(c_19,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1656,plain,
    ( r1_tarski(k1_setfam_1(sK8),sK9)
    | k4_xboole_0(k1_setfam_1(sK8),sK9) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_698,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_689])).

cnf(c_31,negated_conjecture,
    ( ~ r1_tarski(k1_setfam_1(sK8),sK9) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_32,negated_conjecture,
    ( r1_tarski(sK7,sK9) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_33,negated_conjecture,
    ( r2_hidden(sK7,sK8) ),
    inference(cnf_transformation,[],[f78])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_35871,c_19420,c_14986,c_14982,c_6354,c_5993,c_3875,c_2726,c_2728,c_1939,c_1765,c_1759,c_1656,c_698,c_31,c_32,c_33])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:50:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.48/1.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.48/1.48  
% 7.48/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.48/1.48  
% 7.48/1.48  ------  iProver source info
% 7.48/1.48  
% 7.48/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.48/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.48/1.48  git: non_committed_changes: false
% 7.48/1.48  git: last_make_outside_of_git: false
% 7.48/1.48  
% 7.48/1.48  ------ 
% 7.48/1.48  ------ Parsing...
% 7.48/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.48/1.48  
% 7.48/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.48/1.48  
% 7.48/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.48/1.48  
% 7.48/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.48/1.48  ------ Proving...
% 7.48/1.48  ------ Problem Properties 
% 7.48/1.48  
% 7.48/1.48  
% 7.48/1.48  clauses                                 33
% 7.48/1.48  conjectures                             3
% 7.48/1.48  EPR                                     3
% 7.48/1.48  Horn                                    20
% 7.48/1.48  unary                                   4
% 7.48/1.48  binary                                  13
% 7.48/1.48  lits                                    85
% 7.48/1.48  lits eq                                 20
% 7.48/1.48  fd_pure                                 0
% 7.48/1.48  fd_pseudo                               0
% 7.48/1.48  fd_cond                                 3
% 7.48/1.48  fd_pseudo_cond                          9
% 7.48/1.48  AC symbols                              0
% 7.48/1.48  
% 7.48/1.48  ------ Input Options Time Limit: Unbounded
% 7.48/1.48  
% 7.48/1.48  
% 7.48/1.48  ------ 
% 7.48/1.48  Current options:
% 7.48/1.48  ------ 
% 7.48/1.48  
% 7.48/1.48  
% 7.48/1.48  
% 7.48/1.48  
% 7.48/1.48  ------ Proving...
% 7.48/1.48  
% 7.48/1.48  
% 7.48/1.48  % SZS status Theorem for theBenchmark.p
% 7.48/1.48  
% 7.48/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.48/1.48  
% 7.48/1.48  fof(f3,axiom,(
% 7.48/1.48    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 7.48/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.48/1.48  
% 7.48/1.48  fof(f31,plain,(
% 7.48/1.48    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.48/1.48    inference(nnf_transformation,[],[f3])).
% 7.48/1.48  
% 7.48/1.48  fof(f32,plain,(
% 7.48/1.48    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.48/1.48    inference(flattening,[],[f31])).
% 7.48/1.48  
% 7.48/1.48  fof(f33,plain,(
% 7.48/1.48    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.48/1.48    inference(rectify,[],[f32])).
% 7.48/1.48  
% 7.48/1.48  fof(f34,plain,(
% 7.48/1.48    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 7.48/1.48    introduced(choice_axiom,[])).
% 7.48/1.48  
% 7.48/1.48  fof(f35,plain,(
% 7.48/1.48    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.48/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f34])).
% 7.48/1.48  
% 7.48/1.48  fof(f60,plain,(
% 7.48/1.48    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 7.48/1.48    inference(cnf_transformation,[],[f35])).
% 7.48/1.48  
% 7.48/1.48  fof(f1,axiom,(
% 7.48/1.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.48/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.48/1.48  
% 7.48/1.48  fof(f13,plain,(
% 7.48/1.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 7.48/1.48    inference(ennf_transformation,[],[f1])).
% 7.48/1.48  
% 7.48/1.48  fof(f22,plain,(
% 7.48/1.48    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 7.48/1.48    inference(nnf_transformation,[],[f13])).
% 7.48/1.48  
% 7.48/1.48  fof(f23,plain,(
% 7.48/1.48    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.48/1.48    inference(rectify,[],[f22])).
% 7.48/1.48  
% 7.48/1.48  fof(f24,plain,(
% 7.48/1.48    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.48/1.48    introduced(choice_axiom,[])).
% 7.48/1.48  
% 7.48/1.48  fof(f25,plain,(
% 7.48/1.48    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.48/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).
% 7.48/1.48  
% 7.48/1.48  fof(f47,plain,(
% 7.48/1.48    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 7.48/1.48    inference(cnf_transformation,[],[f25])).
% 7.48/1.48  
% 7.48/1.48  fof(f57,plain,(
% 7.48/1.48    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 7.48/1.48    inference(cnf_transformation,[],[f35])).
% 7.48/1.48  
% 7.48/1.48  fof(f85,plain,(
% 7.48/1.48    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 7.48/1.48    inference(equality_resolution,[],[f57])).
% 7.48/1.48  
% 7.48/1.48  fof(f10,axiom,(
% 7.48/1.48    ! [X0,X1] : ((k1_xboole_0 = X0 => (k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1)) & (k1_xboole_0 != X0 => (k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X3,X0) => r2_hidden(X2,X3))))))),
% 7.48/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.48/1.48  
% 7.48/1.48  fof(f19,plain,(
% 7.48/1.48    ! [X0,X1] : (((k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1) | k1_xboole_0 != X0) & ((k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)))) | k1_xboole_0 = X0))),
% 7.48/1.48    inference(ennf_transformation,[],[f10])).
% 7.48/1.48  
% 7.48/1.48  fof(f39,plain,(
% 7.48/1.48    ! [X0,X1] : ((((k1_setfam_1(X0) = X1 | k1_xboole_0 != X1) & (k1_xboole_0 = X1 | k1_setfam_1(X0) != X1)) | k1_xboole_0 != X0) & (((k1_setfam_1(X0) = X1 | ? [X2] : ((? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)) & (! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0))) & (! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)) | ~r2_hidden(X2,X1))) | k1_setfam_1(X0) != X1)) | k1_xboole_0 = X0))),
% 7.48/1.48    inference(nnf_transformation,[],[f19])).
% 7.48/1.48  
% 7.48/1.48  fof(f40,plain,(
% 7.48/1.48    ! [X0,X1] : ((((k1_setfam_1(X0) = X1 | k1_xboole_0 != X1) & (k1_xboole_0 = X1 | k1_setfam_1(X0) != X1)) | k1_xboole_0 != X0) & (((k1_setfam_1(X0) = X1 | ? [X2] : ((? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)) & (! [X4] : (r2_hidden(X2,X4) | ~r2_hidden(X4,X0)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ? [X6] : (~r2_hidden(X5,X6) & r2_hidden(X6,X0))) & (! [X7] : (r2_hidden(X5,X7) | ~r2_hidden(X7,X0)) | ~r2_hidden(X5,X1))) | k1_setfam_1(X0) != X1)) | k1_xboole_0 = X0))),
% 7.48/1.48    inference(rectify,[],[f39])).
% 7.48/1.48  
% 7.48/1.48  fof(f43,plain,(
% 7.48/1.48    ! [X5,X0] : (? [X6] : (~r2_hidden(X5,X6) & r2_hidden(X6,X0)) => (~r2_hidden(X5,sK6(X0,X5)) & r2_hidden(sK6(X0,X5),X0)))),
% 7.48/1.48    introduced(choice_axiom,[])).
% 7.48/1.48  
% 7.48/1.48  fof(f42,plain,(
% 7.48/1.48    ( ! [X2] : (! [X1,X0] : (? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) => (~r2_hidden(X2,sK5(X0,X1)) & r2_hidden(sK5(X0,X1),X0)))) )),
% 7.48/1.48    introduced(choice_axiom,[])).
% 7.48/1.48  
% 7.48/1.48  fof(f41,plain,(
% 7.48/1.48    ! [X1,X0] : (? [X2] : ((? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)) & (! [X4] : (r2_hidden(X2,X4) | ~r2_hidden(X4,X0)) | r2_hidden(X2,X1))) => ((? [X3] : (~r2_hidden(sK4(X0,X1),X3) & r2_hidden(X3,X0)) | ~r2_hidden(sK4(X0,X1),X1)) & (! [X4] : (r2_hidden(sK4(X0,X1),X4) | ~r2_hidden(X4,X0)) | r2_hidden(sK4(X0,X1),X1))))),
% 7.48/1.48    introduced(choice_axiom,[])).
% 7.48/1.48  
% 7.48/1.48  fof(f44,plain,(
% 7.48/1.48    ! [X0,X1] : ((((k1_setfam_1(X0) = X1 | k1_xboole_0 != X1) & (k1_xboole_0 = X1 | k1_setfam_1(X0) != X1)) | k1_xboole_0 != X0) & (((k1_setfam_1(X0) = X1 | (((~r2_hidden(sK4(X0,X1),sK5(X0,X1)) & r2_hidden(sK5(X0,X1),X0)) | ~r2_hidden(sK4(X0,X1),X1)) & (! [X4] : (r2_hidden(sK4(X0,X1),X4) | ~r2_hidden(X4,X0)) | r2_hidden(sK4(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | (~r2_hidden(X5,sK6(X0,X5)) & r2_hidden(sK6(X0,X5),X0))) & (! [X7] : (r2_hidden(X5,X7) | ~r2_hidden(X7,X0)) | ~r2_hidden(X5,X1))) | k1_setfam_1(X0) != X1)) | k1_xboole_0 = X0))),
% 7.48/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f40,f43,f42,f41])).
% 7.48/1.48  
% 7.48/1.48  fof(f70,plain,(
% 7.48/1.48    ( ! [X0,X7,X5,X1] : (r2_hidden(X5,X7) | ~r2_hidden(X7,X0) | ~r2_hidden(X5,X1) | k1_setfam_1(X0) != X1 | k1_xboole_0 = X0) )),
% 7.48/1.48    inference(cnf_transformation,[],[f44])).
% 7.48/1.48  
% 7.48/1.48  fof(f93,plain,(
% 7.48/1.48    ( ! [X0,X7,X5] : (r2_hidden(X5,X7) | ~r2_hidden(X7,X0) | ~r2_hidden(X5,k1_setfam_1(X0)) | k1_xboole_0 = X0) )),
% 7.48/1.48    inference(equality_resolution,[],[f70])).
% 7.48/1.48  
% 7.48/1.48  fof(f7,axiom,(
% 7.48/1.48    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 7.48/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.48/1.48  
% 7.48/1.48  fof(f36,plain,(
% 7.48/1.48    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 7.48/1.48    inference(nnf_transformation,[],[f7])).
% 7.48/1.48  
% 7.48/1.48  fof(f66,plain,(
% 7.48/1.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 7.48/1.48    inference(cnf_transformation,[],[f36])).
% 7.48/1.48  
% 7.48/1.48  fof(f9,axiom,(
% 7.48/1.48    ! [X0,X1] : ~(! [X2] : ~(! [X3] : ~(r2_hidden(X3,X2) & r2_hidden(X3,X1)) & r2_hidden(X2,X1)) & r2_hidden(X0,X1))),
% 7.48/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.48/1.48  
% 7.48/1.48  fof(f18,plain,(
% 7.48/1.48    ! [X0,X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) | ~r2_hidden(X0,X1))),
% 7.48/1.48    inference(ennf_transformation,[],[f9])).
% 7.48/1.48  
% 7.48/1.48  fof(f37,plain,(
% 7.48/1.48    ! [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) => (! [X3] : (~r2_hidden(X3,sK3(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK3(X1),X1)))),
% 7.48/1.48    introduced(choice_axiom,[])).
% 7.48/1.48  
% 7.48/1.48  fof(f38,plain,(
% 7.48/1.48    ! [X0,X1] : ((! [X3] : (~r2_hidden(X3,sK3(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK3(X1),X1)) | ~r2_hidden(X0,X1))),
% 7.48/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f37])).
% 7.48/1.48  
% 7.48/1.48  fof(f68,plain,(
% 7.48/1.48    ( ! [X0,X1] : (r2_hidden(sK3(X1),X1) | ~r2_hidden(X0,X1)) )),
% 7.48/1.48    inference(cnf_transformation,[],[f38])).
% 7.48/1.48  
% 7.48/1.48  fof(f59,plain,(
% 7.48/1.48    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 7.48/1.48    inference(cnf_transformation,[],[f35])).
% 7.48/1.48  
% 7.48/1.48  fof(f49,plain,(
% 7.48/1.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 7.48/1.48    inference(cnf_transformation,[],[f25])).
% 7.48/1.48  
% 7.48/1.48  fof(f48,plain,(
% 7.48/1.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 7.48/1.48    inference(cnf_transformation,[],[f25])).
% 7.48/1.48  
% 7.48/1.48  fof(f65,plain,(
% 7.48/1.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 7.48/1.48    inference(cnf_transformation,[],[f36])).
% 7.48/1.48  
% 7.48/1.48  fof(f11,conjecture,(
% 7.48/1.48    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r2_hidden(X0,X1)) => r1_tarski(k1_setfam_1(X1),X2))),
% 7.48/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.48/1.48  
% 7.48/1.48  fof(f12,negated_conjecture,(
% 7.48/1.48    ~! [X0,X1,X2] : ((r1_tarski(X0,X2) & r2_hidden(X0,X1)) => r1_tarski(k1_setfam_1(X1),X2))),
% 7.48/1.48    inference(negated_conjecture,[],[f11])).
% 7.48/1.48  
% 7.48/1.48  fof(f20,plain,(
% 7.48/1.48    ? [X0,X1,X2] : (~r1_tarski(k1_setfam_1(X1),X2) & (r1_tarski(X0,X2) & r2_hidden(X0,X1)))),
% 7.48/1.48    inference(ennf_transformation,[],[f12])).
% 7.48/1.48  
% 7.48/1.48  fof(f21,plain,(
% 7.48/1.48    ? [X0,X1,X2] : (~r1_tarski(k1_setfam_1(X1),X2) & r1_tarski(X0,X2) & r2_hidden(X0,X1))),
% 7.48/1.48    inference(flattening,[],[f20])).
% 7.48/1.48  
% 7.48/1.48  fof(f45,plain,(
% 7.48/1.48    ? [X0,X1,X2] : (~r1_tarski(k1_setfam_1(X1),X2) & r1_tarski(X0,X2) & r2_hidden(X0,X1)) => (~r1_tarski(k1_setfam_1(sK8),sK9) & r1_tarski(sK7,sK9) & r2_hidden(sK7,sK8))),
% 7.48/1.48    introduced(choice_axiom,[])).
% 7.48/1.48  
% 7.48/1.48  fof(f46,plain,(
% 7.48/1.48    ~r1_tarski(k1_setfam_1(sK8),sK9) & r1_tarski(sK7,sK9) & r2_hidden(sK7,sK8)),
% 7.48/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f21,f45])).
% 7.48/1.48  
% 7.48/1.48  fof(f80,plain,(
% 7.48/1.48    ~r1_tarski(k1_setfam_1(sK8),sK9)),
% 7.48/1.48    inference(cnf_transformation,[],[f46])).
% 7.48/1.48  
% 7.48/1.48  fof(f79,plain,(
% 7.48/1.48    r1_tarski(sK7,sK9)),
% 7.48/1.48    inference(cnf_transformation,[],[f46])).
% 7.48/1.48  
% 7.48/1.48  fof(f78,plain,(
% 7.48/1.48    r2_hidden(sK7,sK8)),
% 7.48/1.48    inference(cnf_transformation,[],[f46])).
% 7.48/1.48  
% 7.48/1.48  cnf(c_10,plain,
% 7.48/1.48      ( ~ r2_hidden(sK2(X0,X1,X2),X1)
% 7.48/1.48      | r2_hidden(sK2(X0,X1,X2),X2)
% 7.48/1.48      | k4_xboole_0(X0,X1) = X2 ),
% 7.48/1.48      inference(cnf_transformation,[],[f60]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_35871,plain,
% 7.48/1.48      ( ~ r2_hidden(sK2(k1_setfam_1(sK8),sK9,k1_xboole_0),sK9)
% 7.48/1.48      | r2_hidden(sK2(k1_setfam_1(sK8),sK9,k1_xboole_0),k1_xboole_0)
% 7.48/1.48      | k4_xboole_0(k1_setfam_1(sK8),sK9) = k1_xboole_0 ),
% 7.48/1.48      inference(instantiation,[status(thm)],[c_10]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_2,plain,
% 7.48/1.48      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 7.48/1.48      inference(cnf_transformation,[],[f47]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_9935,plain,
% 7.48/1.48      ( r2_hidden(sK2(k1_setfam_1(sK8),sK9,k1_xboole_0),X0)
% 7.48/1.48      | ~ r2_hidden(sK2(k1_setfam_1(sK8),sK9,k1_xboole_0),sK7)
% 7.48/1.48      | ~ r1_tarski(sK7,X0) ),
% 7.48/1.48      inference(instantiation,[status(thm)],[c_2]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_19420,plain,
% 7.48/1.48      ( ~ r2_hidden(sK2(k1_setfam_1(sK8),sK9,k1_xboole_0),sK7)
% 7.48/1.48      | r2_hidden(sK2(k1_setfam_1(sK8),sK9,k1_xboole_0),sK9)
% 7.48/1.48      | ~ r1_tarski(sK7,sK9) ),
% 7.48/1.48      inference(instantiation,[status(thm)],[c_9935]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_13,plain,
% 7.48/1.48      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 7.48/1.48      inference(cnf_transformation,[],[f85]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_14980,plain,
% 7.48/1.48      ( ~ r2_hidden(sK3(X0),X1)
% 7.48/1.48      | ~ r2_hidden(sK3(X0),k4_xboole_0(X2,X1)) ),
% 7.48/1.48      inference(instantiation,[status(thm)],[c_13]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_14986,plain,
% 7.48/1.48      ( ~ r2_hidden(sK3(k1_xboole_0),k4_xboole_0(k1_xboole_0,k1_xboole_0))
% 7.48/1.48      | ~ r2_hidden(sK3(k1_xboole_0),k1_xboole_0) ),
% 7.48/1.48      inference(instantiation,[status(thm)],[c_14980]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_2846,plain,
% 7.48/1.48      ( ~ r2_hidden(sK3(X0),X0)
% 7.48/1.48      | r2_hidden(sK3(X0),X1)
% 7.48/1.48      | ~ r1_tarski(X0,X1) ),
% 7.48/1.48      inference(instantiation,[status(thm)],[c_2]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_14979,plain,
% 7.48/1.48      ( ~ r2_hidden(sK3(X0),X0)
% 7.48/1.48      | r2_hidden(sK3(X0),k4_xboole_0(X1,X2))
% 7.48/1.48      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ),
% 7.48/1.48      inference(instantiation,[status(thm)],[c_2846]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_14982,plain,
% 7.48/1.48      ( r2_hidden(sK3(k1_xboole_0),k4_xboole_0(k1_xboole_0,k1_xboole_0))
% 7.48/1.48      | ~ r2_hidden(sK3(k1_xboole_0),k1_xboole_0)
% 7.48/1.48      | ~ r1_tarski(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) ),
% 7.48/1.48      inference(instantiation,[status(thm)],[c_14979]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_30,plain,
% 7.48/1.48      ( ~ r2_hidden(X0,X1)
% 7.48/1.48      | r2_hidden(X2,X0)
% 7.48/1.48      | ~ r2_hidden(X2,k1_setfam_1(X1))
% 7.48/1.48      | k1_xboole_0 = X1 ),
% 7.48/1.48      inference(cnf_transformation,[],[f93]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_2128,plain,
% 7.48/1.48      ( ~ r2_hidden(X0,sK8)
% 7.48/1.48      | r2_hidden(sK2(k1_setfam_1(sK8),sK9,k1_xboole_0),X0)
% 7.48/1.48      | ~ r2_hidden(sK2(k1_setfam_1(sK8),sK9,k1_xboole_0),k1_setfam_1(sK8))
% 7.48/1.48      | k1_xboole_0 = sK8 ),
% 7.48/1.48      inference(instantiation,[status(thm)],[c_30]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_6354,plain,
% 7.48/1.48      ( ~ r2_hidden(sK2(k1_setfam_1(sK8),sK9,k1_xboole_0),k1_setfam_1(sK8))
% 7.48/1.48      | r2_hidden(sK2(k1_setfam_1(sK8),sK9,k1_xboole_0),sK7)
% 7.48/1.48      | ~ r2_hidden(sK7,sK8)
% 7.48/1.48      | k1_xboole_0 = sK8 ),
% 7.48/1.48      inference(instantiation,[status(thm)],[c_2128]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_691,plain,
% 7.48/1.48      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.48/1.48      theory(equality) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_18,plain,
% 7.48/1.48      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 7.48/1.48      inference(cnf_transformation,[],[f66]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_5991,plain,
% 7.48/1.48      ( ~ r1_tarski(X0,X1)
% 7.48/1.48      | r1_tarski(X2,k4_xboole_0(X0,X1))
% 7.48/1.48      | ~ r1_tarski(X3,k1_xboole_0)
% 7.48/1.48      | X2 != X3 ),
% 7.48/1.48      inference(resolution,[status(thm)],[c_691,c_18]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_5993,plain,
% 7.48/1.48      ( r1_tarski(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0))
% 7.48/1.48      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 7.48/1.48      | k1_xboole_0 != k1_xboole_0 ),
% 7.48/1.48      inference(instantiation,[status(thm)],[c_5991]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_22,plain,
% 7.48/1.48      ( ~ r2_hidden(X0,X1) | r2_hidden(sK3(X1),X1) ),
% 7.48/1.48      inference(cnf_transformation,[],[f68]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_3875,plain,
% 7.48/1.48      ( ~ r2_hidden(sK2(k1_setfam_1(sK8),sK9,k1_xboole_0),k1_xboole_0)
% 7.48/1.48      | r2_hidden(sK3(k1_xboole_0),k1_xboole_0) ),
% 7.48/1.48      inference(instantiation,[status(thm)],[c_22]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_689,plain,( X0 = X0 ),theory(equality) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_2726,plain,
% 7.48/1.48      ( sK7 = sK7 ),
% 7.48/1.48      inference(instantiation,[status(thm)],[c_689]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_692,plain,
% 7.48/1.48      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.48/1.48      theory(equality) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_1734,plain,
% 7.48/1.48      ( r2_hidden(X0,X1) | ~ r2_hidden(sK7,sK8) | X0 != sK7 | X1 != sK8 ),
% 7.48/1.48      inference(instantiation,[status(thm)],[c_692]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_2725,plain,
% 7.48/1.48      ( r2_hidden(sK7,X0)
% 7.48/1.48      | ~ r2_hidden(sK7,sK8)
% 7.48/1.48      | X0 != sK8
% 7.48/1.48      | sK7 != sK7 ),
% 7.48/1.48      inference(instantiation,[status(thm)],[c_1734]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_2728,plain,
% 7.48/1.48      ( ~ r2_hidden(sK7,sK8)
% 7.48/1.48      | r2_hidden(sK7,k1_xboole_0)
% 7.48/1.48      | sK7 != sK7
% 7.48/1.48      | k1_xboole_0 != sK8 ),
% 7.48/1.48      inference(instantiation,[status(thm)],[c_2725]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_1937,plain,
% 7.48/1.48      ( r2_hidden(sK3(X0),X0) | ~ r2_hidden(sK7,X0) ),
% 7.48/1.48      inference(instantiation,[status(thm)],[c_22]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_1939,plain,
% 7.48/1.48      ( r2_hidden(sK3(k1_xboole_0),k1_xboole_0)
% 7.48/1.48      | ~ r2_hidden(sK7,k1_xboole_0) ),
% 7.48/1.48      inference(instantiation,[status(thm)],[c_1937]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_11,plain,
% 7.48/1.48      ( r2_hidden(sK2(X0,X1,X2),X0)
% 7.48/1.48      | r2_hidden(sK2(X0,X1,X2),X2)
% 7.48/1.48      | k4_xboole_0(X0,X1) = X2 ),
% 7.48/1.48      inference(cnf_transformation,[],[f59]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_1765,plain,
% 7.48/1.48      ( r2_hidden(sK2(k1_setfam_1(sK8),sK9,k1_xboole_0),k1_setfam_1(sK8))
% 7.48/1.48      | r2_hidden(sK2(k1_setfam_1(sK8),sK9,k1_xboole_0),k1_xboole_0)
% 7.48/1.48      | k4_xboole_0(k1_setfam_1(sK8),sK9) = k1_xboole_0 ),
% 7.48/1.48      inference(instantiation,[status(thm)],[c_11]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_0,plain,
% 7.48/1.48      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 7.48/1.48      inference(cnf_transformation,[],[f49]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_1,plain,
% 7.48/1.48      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 7.48/1.48      inference(cnf_transformation,[],[f48]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_1757,plain,
% 7.48/1.48      ( r1_tarski(X0,X0) ),
% 7.48/1.48      inference(resolution,[status(thm)],[c_0,c_1]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_1759,plain,
% 7.48/1.48      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 7.48/1.48      inference(instantiation,[status(thm)],[c_1757]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_19,plain,
% 7.48/1.48      ( r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0 ),
% 7.48/1.48      inference(cnf_transformation,[],[f65]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_1656,plain,
% 7.48/1.48      ( r1_tarski(k1_setfam_1(sK8),sK9)
% 7.48/1.48      | k4_xboole_0(k1_setfam_1(sK8),sK9) != k1_xboole_0 ),
% 7.48/1.48      inference(instantiation,[status(thm)],[c_19]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_698,plain,
% 7.48/1.48      ( k1_xboole_0 = k1_xboole_0 ),
% 7.48/1.48      inference(instantiation,[status(thm)],[c_689]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_31,negated_conjecture,
% 7.48/1.48      ( ~ r1_tarski(k1_setfam_1(sK8),sK9) ),
% 7.48/1.48      inference(cnf_transformation,[],[f80]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_32,negated_conjecture,
% 7.48/1.48      ( r1_tarski(sK7,sK9) ),
% 7.48/1.48      inference(cnf_transformation,[],[f79]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_33,negated_conjecture,
% 7.48/1.48      ( r2_hidden(sK7,sK8) ),
% 7.48/1.48      inference(cnf_transformation,[],[f78]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(contradiction,plain,
% 7.48/1.48      ( $false ),
% 7.48/1.48      inference(minisat,
% 7.48/1.48                [status(thm)],
% 7.48/1.48                [c_35871,c_19420,c_14986,c_14982,c_6354,c_5993,c_3875,
% 7.48/1.48                 c_2726,c_2728,c_1939,c_1765,c_1759,c_1656,c_698,c_31,
% 7.48/1.48                 c_32,c_33]) ).
% 7.48/1.48  
% 7.48/1.48  
% 7.48/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 7.48/1.48  
% 7.48/1.48  ------                               Statistics
% 7.48/1.48  
% 7.48/1.48  ------ Selected
% 7.48/1.48  
% 7.48/1.48  total_time:                             0.929
% 7.48/1.48  
%------------------------------------------------------------------------------
