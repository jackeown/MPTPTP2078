%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:41:36 EST 2020

% Result     : Theorem 7.84s
% Output     : CNFRefutation 7.84s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 906 expanded)
%              Number of clauses        :   46 ( 152 expanded)
%              Number of leaves         :   20 ( 283 expanded)
%              Depth                    :   19
%              Number of atoms          :  393 (3405 expanded)
%              Number of equality atoms :  224 (1778 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
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

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f31,plain,(
    ! [X5,X0] :
      ( ? [X6] :
          ( ~ r2_hidden(X5,X6)
          & r2_hidden(X6,X0) )
     => ( ~ r2_hidden(X5,sK3(X0,X5))
        & r2_hidden(sK3(X0,X5),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X2,X3)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(X2,sK2(X0,X1))
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
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
              ( ~ r2_hidden(sK1(X0,X1),X3)
              & r2_hidden(X3,X0) )
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ! [X4] :
              ( r2_hidden(sK1(X0,X1),X4)
              | ~ r2_hidden(X4,X0) )
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( ( ( k1_setfam_1(X0) = X1
            | ( ( ( ~ r2_hidden(sK1(X0,X1),sK2(X0,X1))
                  & r2_hidden(sK2(X0,X1),X0) )
                | ~ r2_hidden(sK1(X0,X1),X1) )
              & ( ! [X4] :
                    ( r2_hidden(sK1(X0,X1),X4)
                    | ~ r2_hidden(X4,X0) )
                | r2_hidden(sK1(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ( ~ r2_hidden(X5,sK3(X0,X5))
                    & r2_hidden(sK3(X0,X5),X0) ) )
                & ( ! [X7] :
                      ( r2_hidden(X5,X7)
                      | ~ r2_hidden(X7,X0) )
                  | ~ r2_hidden(X5,X1) ) )
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f28,f31,f30,f29])).

fof(f59,plain,(
    ! [X4,X0,X1] :
      ( k1_setfam_1(X0) = X1
      | r2_hidden(sK1(X0,X1),X4)
      | ~ r2_hidden(X4,X0)
      | r2_hidden(sK1(X0,X1),X1)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f11,conjecture,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(negated_conjecture,[],[f11])).

fof(f14,plain,(
    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 ),
    inference(ennf_transformation,[],[f12])).

fof(f33,plain,
    ( ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0
   => k1_setfam_1(k1_tarski(sK4)) != sK4 ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    k1_setfam_1(k1_tarski(sK4)) != sK4 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f14,f33])).

fof(f64,plain,(
    k1_setfam_1(k1_tarski(sK4)) != sK4 ),
    inference(cnf_transformation,[],[f34])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f65,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f47,f48])).

fof(f66,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f46,f65])).

fof(f80,plain,(
    k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)) != sK4 ),
    inference(definition_unfolding,[],[f64,f66])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(X0) = X1
      | r2_hidden(sK2(X0,X1),X0)
      | ~ r2_hidden(sK1(X0,X1),X1)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f55,f66])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
        | X0 = X1 )
      & ( X0 != X1
        | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f52,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f77,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)) != k2_enumset1(X0,X0,X0,X0) ) ),
    inference(definition_unfolding,[],[f52,f66,f66,f66])).

fof(f90,plain,(
    ! [X1] : k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1)) != k2_enumset1(X1,X1,X1,X1) ),
    inference(equality_resolution,[],[f77])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f18])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f19])).

fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK0(X0,X1,X2) != X1
            & sK0(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( sK0(X0,X1,X2) = X1
          | sK0(X0,X1,X2) = X0
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK0(X0,X1,X2) != X1
              & sK0(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( sK0(X0,X1,X2) = X1
            | sK0(X0,X1,X2) = X0
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f21])).

fof(f40,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f72,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f40,f65])).

fof(f87,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k2_enumset1(X0,X0,X0,X1)) ) ),
    inference(equality_resolution,[],[f72])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(X0) = X1
      | ~ r2_hidden(sK1(X0,X1),sK2(X0,X1))
      | ~ r2_hidden(sK1(X0,X1),X1)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f23])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
      | k1_xboole_0 != X0 ) ),
    inference(definition_unfolding,[],[f50,f66])).

fof(f89,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,k2_enumset1(X1,X1,X1,X1)) ),
    inference(equality_resolution,[],[f74])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) != X0 ) ),
    inference(definition_unfolding,[],[f54,f66])).

cnf(c_504,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | X6 != X7
    | k2_enumset1(X0,X2,X4,X6) = k2_enumset1(X1,X3,X5,X7) ),
    theory(equality)).

cnf(c_501,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_6227,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | X6 != X7
    | X8 != k2_enumset1(X1,X3,X5,X7)
    | k2_enumset1(X0,X2,X4,X6) = X8 ),
    inference(resolution,[status(thm)],[c_504,c_501])).

cnf(c_22,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK1(X1,X2),X2)
    | r2_hidden(sK1(X1,X2),X0)
    | k1_setfam_1(X1) = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_26,negated_conjecture,
    ( k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)) != sK4 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_5875,plain,
    ( ~ r2_hidden(X0,k2_enumset1(sK4,sK4,sK4,sK4))
    | r2_hidden(sK1(k2_enumset1(sK4,sK4,sK4,sK4),sK4),X0)
    | r2_hidden(sK1(k2_enumset1(sK4,sK4,sK4,sK4),sK4),sK4)
    | k1_xboole_0 = k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(resolution,[status(thm)],[c_22,c_26])).

cnf(c_21,plain,
    ( r2_hidden(sK2(X0,X1),X0)
    | ~ r2_hidden(sK1(X0,X1),X1)
    | k1_setfam_1(X0) = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_6251,plain,
    ( ~ r2_hidden(X0,k2_enumset1(sK4,sK4,sK4,sK4))
    | r2_hidden(sK2(k2_enumset1(sK4,sK4,sK4,sK4),sK4),k2_enumset1(sK4,sK4,sK4,sK4))
    | r2_hidden(sK1(k2_enumset1(sK4,sK4,sK4,sK4),sK4),X0)
    | k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)) = sK4
    | k1_xboole_0 = k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(resolution,[status(thm)],[c_5875,c_21])).

cnf(c_6268,plain,
    ( r2_hidden(sK1(k2_enumset1(sK4,sK4,sK4,sK4),sK4),sK4)
    | ~ r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4))
    | k1_xboole_0 = k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(factoring,[status(thm)],[c_5875])).

cnf(c_16,plain,
    ( r2_hidden(X0,X1)
    | k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X0)) = X1 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1700,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X2))
    | k4_xboole_0(k2_enumset1(X1,X1,X1,X2),k2_enumset1(X0,X0,X0,X0)) = k2_enumset1(X1,X1,X1,X2) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_2770,plain,
    ( r2_hidden(sK4,k2_enumset1(X0,X0,X0,X1))
    | k4_xboole_0(k2_enumset1(X0,X0,X0,X1),k2_enumset1(sK4,sK4,sK4,sK4)) = k2_enumset1(X0,X0,X0,X1) ),
    inference(instantiation,[status(thm)],[c_1700])).

cnf(c_3930,plain,
    ( r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4))
    | k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(sK4,sK4,sK4,sK4)) = k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_2770])).

cnf(c_15,plain,
    ( k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0)) != k2_enumset1(X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_3931,plain,
    ( k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(sK4,sK4,sK4,sK4)) != k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_6564,plain,
    ( r2_hidden(sK1(k2_enumset1(sK4,sK4,sK4,sK4),sK4),sK4)
    | k1_xboole_0 = k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6268,c_3930,c_3931])).

cnf(c_6580,plain,
    ( r2_hidden(sK2(k2_enumset1(sK4,sK4,sK4,sK4),sK4),k2_enumset1(sK4,sK4,sK4,sK4))
    | k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)) = sK4
    | k1_xboole_0 = k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(resolution,[status(thm)],[c_6564,c_21])).

cnf(c_6583,plain,
    ( r2_hidden(sK2(k2_enumset1(sK4,sK4,sK4,sK4),sK4),k2_enumset1(sK4,sK4,sK4,sK4))
    | k1_xboole_0 = k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6251,c_26,c_6580])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_6970,plain,
    ( sK2(k2_enumset1(sK4,sK4,sK4,sK4),sK4) = sK4
    | k1_xboole_0 = k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(resolution,[status(thm)],[c_6583,c_10])).

cnf(c_500,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1499,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_501,c_500])).

cnf(c_6976,plain,
    ( sK4 = sK2(k2_enumset1(sK4,sK4,sK4,sK4),sK4)
    | k1_xboole_0 = k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(resolution,[status(thm)],[c_6970,c_1499])).

cnf(c_502,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2455,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_502,c_500])).

cnf(c_7019,plain,
    ( ~ r1_tarski(sK2(k2_enumset1(sK4,sK4,sK4,sK4),sK4),X0)
    | r1_tarski(sK4,X0)
    | k1_xboole_0 = k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(resolution,[status(thm)],[c_6976,c_2455])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_2443,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,k4_xboole_0(X0,X1))
    | ~ r1_tarski(X3,k1_xboole_0)
    | X2 != X3 ),
    inference(resolution,[status(thm)],[c_502,c_3])).

cnf(c_8595,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK2(k2_enumset1(sK4,sK4,sK4,sK4),sK4),k4_xboole_0(X0,X1))
    | ~ r1_tarski(sK4,k1_xboole_0)
    | k1_xboole_0 = k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(resolution,[status(thm)],[c_2443,c_6970])).

cnf(c_10057,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK4,k4_xboole_0(X0,X1))
    | ~ r1_tarski(sK4,k1_xboole_0)
    | k1_xboole_0 = k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(resolution,[status(thm)],[c_7019,c_8595])).

cnf(c_505,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_7002,plain,
    ( r2_hidden(X0,sK2(k2_enumset1(sK4,sK4,sK4,sK4),sK4))
    | ~ r2_hidden(X1,sK4)
    | X0 != X1
    | k1_xboole_0 = k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(resolution,[status(thm)],[c_6970,c_505])).

cnf(c_9413,plain,
    ( r2_hidden(X0,sK2(k2_enumset1(sK4,sK4,sK4,sK4),sK4))
    | ~ r2_hidden(X0,sK4)
    | k1_xboole_0 = k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(resolution,[status(thm)],[c_7002,c_500])).

cnf(c_20,plain,
    ( ~ r2_hidden(sK1(X0,X1),X1)
    | ~ r2_hidden(sK1(X0,X1),sK2(X0,X1))
    | k1_setfam_1(X0) = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_12210,plain,
    ( ~ r2_hidden(sK1(k2_enumset1(sK4,sK4,sK4,sK4),sK4),sK4)
    | k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)) = sK4
    | k1_xboole_0 = k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(resolution,[status(thm)],[c_9413,c_20])).

cnf(c_12218,plain,
    ( k1_xboole_0 = k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10057,c_26,c_3930,c_3931,c_6268,c_12210])).

cnf(c_19350,plain,
    ( X0 != sK4
    | X1 != sK4
    | X2 != sK4
    | X3 != sK4
    | k2_enumset1(X0,X2,X1,X3) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6227,c_12218])).

cnf(c_12,plain,
    ( r1_tarski(k1_xboole_0,k2_enumset1(X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X0)) != X1 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1226,plain,
    ( ~ r2_hidden(X0,k1_xboole_0)
    | k4_xboole_0(k1_xboole_0,k2_enumset1(X0,X0,X0,X0)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1227,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_enumset1(X0,X0,X0,X0))
    | k4_xboole_0(k1_xboole_0,k2_enumset1(X0,X0,X0,X0)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1389,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k2_enumset1(X2,X2,X2,X3))
    | X0 != X2
    | X1 != k2_enumset1(X2,X2,X2,X3) ),
    inference(instantiation,[status(thm)],[c_505])).

cnf(c_1742,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X0,X0,X0,X1))
    | r2_hidden(X2,k1_xboole_0)
    | X2 != X0
    | k1_xboole_0 != k2_enumset1(X0,X0,X0,X1) ),
    inference(instantiation,[status(thm)],[c_1389])).

cnf(c_10754,plain,
    ( r2_hidden(X0,k1_xboole_0)
    | ~ r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4))
    | X0 != sK4
    | k1_xboole_0 != k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_1742])).

cnf(c_30586,plain,
    ( X0 != sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_19350,c_26,c_12,c_1226,c_1227,c_3930,c_3931,c_6268,c_10754,c_12210])).

cnf(c_30625,plain,
    ( $false ),
    inference(resolution,[status(thm)],[c_30586,c_500])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n016.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 14:53:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.84/1.48  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.84/1.48  
% 7.84/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.84/1.48  
% 7.84/1.48  ------  iProver source info
% 7.84/1.48  
% 7.84/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.84/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.84/1.48  git: non_committed_changes: false
% 7.84/1.48  git: last_make_outside_of_git: false
% 7.84/1.48  
% 7.84/1.48  ------ 
% 7.84/1.48  ------ Parsing...
% 7.84/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.84/1.48  
% 7.84/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.84/1.48  
% 7.84/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.84/1.48  
% 7.84/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.84/1.48  ------ Proving...
% 7.84/1.48  ------ Problem Properties 
% 7.84/1.48  
% 7.84/1.48  
% 7.84/1.48  clauses                                 25
% 7.84/1.48  conjectures                             1
% 7.84/1.48  EPR                                     2
% 7.84/1.48  Horn                                    14
% 7.84/1.48  unary                                   8
% 7.84/1.48  binary                                  5
% 7.84/1.48  lits                                    60
% 7.84/1.48  lits eq                                 30
% 7.84/1.48  fd_pure                                 0
% 7.84/1.48  fd_pseudo                               0
% 7.84/1.48  fd_cond                                 3
% 7.84/1.48  fd_pseudo_cond                          9
% 7.84/1.48  AC symbols                              0
% 7.84/1.48  
% 7.84/1.48  ------ Input Options Time Limit: Unbounded
% 7.84/1.48  
% 7.84/1.48  
% 7.84/1.48  ------ 
% 7.84/1.48  Current options:
% 7.84/1.48  ------ 
% 7.84/1.48  
% 7.84/1.48  
% 7.84/1.48  
% 7.84/1.48  
% 7.84/1.48  ------ Proving...
% 7.84/1.48  
% 7.84/1.48  
% 7.84/1.48  % SZS status Theorem for theBenchmark.p
% 7.84/1.48  
% 7.84/1.48   Resolution empty clause
% 7.84/1.48  
% 7.84/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.84/1.48  
% 7.84/1.48  fof(f10,axiom,(
% 7.84/1.48    ! [X0,X1] : ((k1_xboole_0 = X0 => (k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1)) & (k1_xboole_0 != X0 => (k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X3,X0) => r2_hidden(X2,X3))))))),
% 7.84/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.84/1.48  
% 7.84/1.48  fof(f13,plain,(
% 7.84/1.48    ! [X0,X1] : (((k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1) | k1_xboole_0 != X0) & ((k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)))) | k1_xboole_0 = X0))),
% 7.84/1.48    inference(ennf_transformation,[],[f10])).
% 7.84/1.48  
% 7.84/1.48  fof(f27,plain,(
% 7.84/1.48    ! [X0,X1] : ((((k1_setfam_1(X0) = X1 | k1_xboole_0 != X1) & (k1_xboole_0 = X1 | k1_setfam_1(X0) != X1)) | k1_xboole_0 != X0) & (((k1_setfam_1(X0) = X1 | ? [X2] : ((? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)) & (! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0))) & (! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)) | ~r2_hidden(X2,X1))) | k1_setfam_1(X0) != X1)) | k1_xboole_0 = X0))),
% 7.84/1.48    inference(nnf_transformation,[],[f13])).
% 7.84/1.48  
% 7.84/1.48  fof(f28,plain,(
% 7.84/1.48    ! [X0,X1] : ((((k1_setfam_1(X0) = X1 | k1_xboole_0 != X1) & (k1_xboole_0 = X1 | k1_setfam_1(X0) != X1)) | k1_xboole_0 != X0) & (((k1_setfam_1(X0) = X1 | ? [X2] : ((? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)) & (! [X4] : (r2_hidden(X2,X4) | ~r2_hidden(X4,X0)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ? [X6] : (~r2_hidden(X5,X6) & r2_hidden(X6,X0))) & (! [X7] : (r2_hidden(X5,X7) | ~r2_hidden(X7,X0)) | ~r2_hidden(X5,X1))) | k1_setfam_1(X0) != X1)) | k1_xboole_0 = X0))),
% 7.84/1.48    inference(rectify,[],[f27])).
% 7.84/1.48  
% 7.84/1.48  fof(f31,plain,(
% 7.84/1.48    ! [X5,X0] : (? [X6] : (~r2_hidden(X5,X6) & r2_hidden(X6,X0)) => (~r2_hidden(X5,sK3(X0,X5)) & r2_hidden(sK3(X0,X5),X0)))),
% 7.84/1.48    introduced(choice_axiom,[])).
% 7.84/1.48  
% 7.84/1.48  fof(f30,plain,(
% 7.84/1.48    ( ! [X2] : (! [X1,X0] : (? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) => (~r2_hidden(X2,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),X0)))) )),
% 7.84/1.48    introduced(choice_axiom,[])).
% 7.84/1.48  
% 7.84/1.48  fof(f29,plain,(
% 7.84/1.48    ! [X1,X0] : (? [X2] : ((? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)) & (! [X4] : (r2_hidden(X2,X4) | ~r2_hidden(X4,X0)) | r2_hidden(X2,X1))) => ((? [X3] : (~r2_hidden(sK1(X0,X1),X3) & r2_hidden(X3,X0)) | ~r2_hidden(sK1(X0,X1),X1)) & (! [X4] : (r2_hidden(sK1(X0,X1),X4) | ~r2_hidden(X4,X0)) | r2_hidden(sK1(X0,X1),X1))))),
% 7.84/1.48    introduced(choice_axiom,[])).
% 7.84/1.48  
% 7.84/1.48  fof(f32,plain,(
% 7.84/1.48    ! [X0,X1] : ((((k1_setfam_1(X0) = X1 | k1_xboole_0 != X1) & (k1_xboole_0 = X1 | k1_setfam_1(X0) != X1)) | k1_xboole_0 != X0) & (((k1_setfam_1(X0) = X1 | (((~r2_hidden(sK1(X0,X1),sK2(X0,X1)) & r2_hidden(sK2(X0,X1),X0)) | ~r2_hidden(sK1(X0,X1),X1)) & (! [X4] : (r2_hidden(sK1(X0,X1),X4) | ~r2_hidden(X4,X0)) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | (~r2_hidden(X5,sK3(X0,X5)) & r2_hidden(sK3(X0,X5),X0))) & (! [X7] : (r2_hidden(X5,X7) | ~r2_hidden(X7,X0)) | ~r2_hidden(X5,X1))) | k1_setfam_1(X0) != X1)) | k1_xboole_0 = X0))),
% 7.84/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f28,f31,f30,f29])).
% 7.84/1.48  
% 7.84/1.48  fof(f59,plain,(
% 7.84/1.48    ( ! [X4,X0,X1] : (k1_setfam_1(X0) = X1 | r2_hidden(sK1(X0,X1),X4) | ~r2_hidden(X4,X0) | r2_hidden(sK1(X0,X1),X1) | k1_xboole_0 = X0) )),
% 7.84/1.48    inference(cnf_transformation,[],[f32])).
% 7.84/1.48  
% 7.84/1.48  fof(f11,conjecture,(
% 7.84/1.48    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 7.84/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.84/1.48  
% 7.84/1.48  fof(f12,negated_conjecture,(
% 7.84/1.48    ~! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 7.84/1.48    inference(negated_conjecture,[],[f11])).
% 7.84/1.48  
% 7.84/1.48  fof(f14,plain,(
% 7.84/1.48    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0),
% 7.84/1.48    inference(ennf_transformation,[],[f12])).
% 7.84/1.48  
% 7.84/1.48  fof(f33,plain,(
% 7.84/1.48    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 => k1_setfam_1(k1_tarski(sK4)) != sK4),
% 7.84/1.48    introduced(choice_axiom,[])).
% 7.84/1.48  
% 7.84/1.48  fof(f34,plain,(
% 7.84/1.48    k1_setfam_1(k1_tarski(sK4)) != sK4),
% 7.84/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f14,f33])).
% 7.84/1.48  
% 7.84/1.48  fof(f64,plain,(
% 7.84/1.48    k1_setfam_1(k1_tarski(sK4)) != sK4),
% 7.84/1.48    inference(cnf_transformation,[],[f34])).
% 7.84/1.48  
% 7.84/1.48  fof(f4,axiom,(
% 7.84/1.48    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 7.84/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.84/1.48  
% 7.84/1.48  fof(f46,plain,(
% 7.84/1.48    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 7.84/1.48    inference(cnf_transformation,[],[f4])).
% 7.84/1.48  
% 7.84/1.48  fof(f5,axiom,(
% 7.84/1.48    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.84/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.84/1.48  
% 7.84/1.48  fof(f47,plain,(
% 7.84/1.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.84/1.48    inference(cnf_transformation,[],[f5])).
% 7.84/1.48  
% 7.84/1.48  fof(f6,axiom,(
% 7.84/1.48    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.84/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.84/1.48  
% 7.84/1.48  fof(f48,plain,(
% 7.84/1.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.84/1.48    inference(cnf_transformation,[],[f6])).
% 7.84/1.48  
% 7.84/1.48  fof(f65,plain,(
% 7.84/1.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 7.84/1.48    inference(definition_unfolding,[],[f47,f48])).
% 7.84/1.48  
% 7.84/1.48  fof(f66,plain,(
% 7.84/1.48    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 7.84/1.48    inference(definition_unfolding,[],[f46,f65])).
% 7.84/1.48  
% 7.84/1.48  fof(f80,plain,(
% 7.84/1.48    k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)) != sK4),
% 7.84/1.48    inference(definition_unfolding,[],[f64,f66])).
% 7.84/1.48  
% 7.84/1.48  fof(f60,plain,(
% 7.84/1.48    ( ! [X0,X1] : (k1_setfam_1(X0) = X1 | r2_hidden(sK2(X0,X1),X0) | ~r2_hidden(sK1(X0,X1),X1) | k1_xboole_0 = X0) )),
% 7.84/1.48    inference(cnf_transformation,[],[f32])).
% 7.84/1.48  
% 7.84/1.48  fof(f9,axiom,(
% 7.84/1.48    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 7.84/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.84/1.48  
% 7.84/1.48  fof(f26,plain,(
% 7.84/1.48    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 7.84/1.48    inference(nnf_transformation,[],[f9])).
% 7.84/1.48  
% 7.84/1.48  fof(f55,plain,(
% 7.84/1.48    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 7.84/1.48    inference(cnf_transformation,[],[f26])).
% 7.84/1.48  
% 7.84/1.48  fof(f78,plain,(
% 7.84/1.48    ( ! [X0,X1] : (k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0 | r2_hidden(X1,X0)) )),
% 7.84/1.48    inference(definition_unfolding,[],[f55,f66])).
% 7.84/1.48  
% 7.84/1.48  fof(f8,axiom,(
% 7.84/1.48    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) <=> X0 != X1)),
% 7.84/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.84/1.48  
% 7.84/1.48  fof(f25,plain,(
% 7.84/1.48    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) & (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)))),
% 7.84/1.48    inference(nnf_transformation,[],[f8])).
% 7.84/1.48  
% 7.84/1.48  fof(f52,plain,(
% 7.84/1.48    ( ! [X0,X1] : (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)) )),
% 7.84/1.48    inference(cnf_transformation,[],[f25])).
% 7.84/1.48  
% 7.84/1.48  fof(f77,plain,(
% 7.84/1.48    ( ! [X0,X1] : (X0 != X1 | k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)) != k2_enumset1(X0,X0,X0,X0)) )),
% 7.84/1.48    inference(definition_unfolding,[],[f52,f66,f66,f66])).
% 7.84/1.48  
% 7.84/1.48  fof(f90,plain,(
% 7.84/1.48    ( ! [X1] : (k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1)) != k2_enumset1(X1,X1,X1,X1)) )),
% 7.84/1.48    inference(equality_resolution,[],[f77])).
% 7.84/1.48  
% 7.84/1.48  fof(f3,axiom,(
% 7.84/1.48    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 7.84/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.84/1.48  
% 7.84/1.48  fof(f18,plain,(
% 7.84/1.48    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 7.84/1.48    inference(nnf_transformation,[],[f3])).
% 7.84/1.48  
% 7.84/1.48  fof(f19,plain,(
% 7.84/1.48    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 7.84/1.48    inference(flattening,[],[f18])).
% 7.84/1.48  
% 7.84/1.48  fof(f20,plain,(
% 7.84/1.48    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 7.84/1.48    inference(rectify,[],[f19])).
% 7.84/1.48  
% 7.84/1.48  fof(f21,plain,(
% 7.84/1.48    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2))))),
% 7.84/1.48    introduced(choice_axiom,[])).
% 7.84/1.48  
% 7.84/1.48  fof(f22,plain,(
% 7.84/1.48    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 7.84/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f21])).
% 7.84/1.48  
% 7.84/1.48  fof(f40,plain,(
% 7.84/1.48    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 7.84/1.48    inference(cnf_transformation,[],[f22])).
% 7.84/1.48  
% 7.84/1.48  fof(f72,plain,(
% 7.84/1.48    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 7.84/1.48    inference(definition_unfolding,[],[f40,f65])).
% 7.84/1.48  
% 7.84/1.48  fof(f87,plain,(
% 7.84/1.48    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k2_enumset1(X0,X0,X0,X1))) )),
% 7.84/1.48    inference(equality_resolution,[],[f72])).
% 7.84/1.48  
% 7.84/1.48  fof(f2,axiom,(
% 7.84/1.48    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 7.84/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.84/1.48  
% 7.84/1.48  fof(f17,plain,(
% 7.84/1.48    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 7.84/1.48    inference(nnf_transformation,[],[f2])).
% 7.84/1.48  
% 7.84/1.48  fof(f39,plain,(
% 7.84/1.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 7.84/1.48    inference(cnf_transformation,[],[f17])).
% 7.84/1.48  
% 7.84/1.48  fof(f61,plain,(
% 7.84/1.48    ( ! [X0,X1] : (k1_setfam_1(X0) = X1 | ~r2_hidden(sK1(X0,X1),sK2(X0,X1)) | ~r2_hidden(sK1(X0,X1),X1) | k1_xboole_0 = X0) )),
% 7.84/1.48    inference(cnf_transformation,[],[f32])).
% 7.84/1.48  
% 7.84/1.48  fof(f7,axiom,(
% 7.84/1.48    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 7.84/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.84/1.48  
% 7.84/1.48  fof(f23,plain,(
% 7.84/1.48    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 7.84/1.48    inference(nnf_transformation,[],[f7])).
% 7.84/1.48  
% 7.84/1.48  fof(f24,plain,(
% 7.84/1.48    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 7.84/1.48    inference(flattening,[],[f23])).
% 7.84/1.48  
% 7.84/1.48  fof(f50,plain,(
% 7.84/1.48    ( ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 != X0) )),
% 7.84/1.48    inference(cnf_transformation,[],[f24])).
% 7.84/1.48  
% 7.84/1.48  fof(f74,plain,(
% 7.84/1.48    ( ! [X0,X1] : (r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) | k1_xboole_0 != X0) )),
% 7.84/1.48    inference(definition_unfolding,[],[f50,f66])).
% 7.84/1.48  
% 7.84/1.48  fof(f89,plain,(
% 7.84/1.48    ( ! [X1] : (r1_tarski(k1_xboole_0,k2_enumset1(X1,X1,X1,X1))) )),
% 7.84/1.48    inference(equality_resolution,[],[f74])).
% 7.84/1.48  
% 7.84/1.48  fof(f54,plain,(
% 7.84/1.48    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) )),
% 7.84/1.48    inference(cnf_transformation,[],[f26])).
% 7.84/1.48  
% 7.84/1.48  fof(f79,plain,(
% 7.84/1.48    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) != X0) )),
% 7.84/1.48    inference(definition_unfolding,[],[f54,f66])).
% 7.84/1.48  
% 7.84/1.48  cnf(c_504,plain,
% 7.84/1.48      ( X0 != X1
% 7.84/1.48      | X2 != X3
% 7.84/1.48      | X4 != X5
% 7.84/1.48      | X6 != X7
% 7.84/1.48      | k2_enumset1(X0,X2,X4,X6) = k2_enumset1(X1,X3,X5,X7) ),
% 7.84/1.48      theory(equality) ).
% 7.84/1.48  
% 7.84/1.48  cnf(c_501,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.84/1.48  
% 7.84/1.48  cnf(c_6227,plain,
% 7.84/1.48      ( X0 != X1
% 7.84/1.48      | X2 != X3
% 7.84/1.48      | X4 != X5
% 7.84/1.48      | X6 != X7
% 7.84/1.48      | X8 != k2_enumset1(X1,X3,X5,X7)
% 7.84/1.48      | k2_enumset1(X0,X2,X4,X6) = X8 ),
% 7.84/1.48      inference(resolution,[status(thm)],[c_504,c_501]) ).
% 7.84/1.48  
% 7.84/1.48  cnf(c_22,plain,
% 7.84/1.48      ( ~ r2_hidden(X0,X1)
% 7.84/1.48      | r2_hidden(sK1(X1,X2),X2)
% 7.84/1.48      | r2_hidden(sK1(X1,X2),X0)
% 7.84/1.48      | k1_setfam_1(X1) = X2
% 7.84/1.48      | k1_xboole_0 = X1 ),
% 7.84/1.48      inference(cnf_transformation,[],[f59]) ).
% 7.84/1.48  
% 7.84/1.48  cnf(c_26,negated_conjecture,
% 7.84/1.48      ( k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)) != sK4 ),
% 7.84/1.48      inference(cnf_transformation,[],[f80]) ).
% 7.84/1.48  
% 7.84/1.48  cnf(c_5875,plain,
% 7.84/1.48      ( ~ r2_hidden(X0,k2_enumset1(sK4,sK4,sK4,sK4))
% 7.84/1.48      | r2_hidden(sK1(k2_enumset1(sK4,sK4,sK4,sK4),sK4),X0)
% 7.84/1.48      | r2_hidden(sK1(k2_enumset1(sK4,sK4,sK4,sK4),sK4),sK4)
% 7.84/1.48      | k1_xboole_0 = k2_enumset1(sK4,sK4,sK4,sK4) ),
% 7.84/1.48      inference(resolution,[status(thm)],[c_22,c_26]) ).
% 7.84/1.48  
% 7.84/1.48  cnf(c_21,plain,
% 7.84/1.48      ( r2_hidden(sK2(X0,X1),X0)
% 7.84/1.48      | ~ r2_hidden(sK1(X0,X1),X1)
% 7.84/1.48      | k1_setfam_1(X0) = X1
% 7.84/1.48      | k1_xboole_0 = X0 ),
% 7.84/1.48      inference(cnf_transformation,[],[f60]) ).
% 7.84/1.48  
% 7.84/1.48  cnf(c_6251,plain,
% 7.84/1.48      ( ~ r2_hidden(X0,k2_enumset1(sK4,sK4,sK4,sK4))
% 7.84/1.48      | r2_hidden(sK2(k2_enumset1(sK4,sK4,sK4,sK4),sK4),k2_enumset1(sK4,sK4,sK4,sK4))
% 7.84/1.48      | r2_hidden(sK1(k2_enumset1(sK4,sK4,sK4,sK4),sK4),X0)
% 7.84/1.48      | k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)) = sK4
% 7.84/1.48      | k1_xboole_0 = k2_enumset1(sK4,sK4,sK4,sK4) ),
% 7.84/1.48      inference(resolution,[status(thm)],[c_5875,c_21]) ).
% 7.84/1.48  
% 7.84/1.48  cnf(c_6268,plain,
% 7.84/1.48      ( r2_hidden(sK1(k2_enumset1(sK4,sK4,sK4,sK4),sK4),sK4)
% 7.84/1.48      | ~ r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4))
% 7.84/1.48      | k1_xboole_0 = k2_enumset1(sK4,sK4,sK4,sK4) ),
% 7.84/1.48      inference(factoring,[status(thm)],[c_5875]) ).
% 7.84/1.48  
% 7.84/1.48  cnf(c_16,plain,
% 7.84/1.48      ( r2_hidden(X0,X1) | k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X0)) = X1 ),
% 7.84/1.48      inference(cnf_transformation,[],[f78]) ).
% 7.84/1.48  
% 7.84/1.48  cnf(c_1700,plain,
% 7.84/1.48      ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X2))
% 7.84/1.48      | k4_xboole_0(k2_enumset1(X1,X1,X1,X2),k2_enumset1(X0,X0,X0,X0)) = k2_enumset1(X1,X1,X1,X2) ),
% 7.84/1.48      inference(instantiation,[status(thm)],[c_16]) ).
% 7.84/1.48  
% 7.84/1.48  cnf(c_2770,plain,
% 7.84/1.48      ( r2_hidden(sK4,k2_enumset1(X0,X0,X0,X1))
% 7.84/1.48      | k4_xboole_0(k2_enumset1(X0,X0,X0,X1),k2_enumset1(sK4,sK4,sK4,sK4)) = k2_enumset1(X0,X0,X0,X1) ),
% 7.84/1.48      inference(instantiation,[status(thm)],[c_1700]) ).
% 7.84/1.48  
% 7.84/1.48  cnf(c_3930,plain,
% 7.84/1.48      ( r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4))
% 7.84/1.48      | k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(sK4,sK4,sK4,sK4)) = k2_enumset1(sK4,sK4,sK4,sK4) ),
% 7.84/1.48      inference(instantiation,[status(thm)],[c_2770]) ).
% 7.84/1.48  
% 7.84/1.48  cnf(c_15,plain,
% 7.84/1.48      ( k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0)) != k2_enumset1(X0,X0,X0,X0) ),
% 7.84/1.48      inference(cnf_transformation,[],[f90]) ).
% 7.84/1.48  
% 7.84/1.48  cnf(c_3931,plain,
% 7.84/1.48      ( k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(sK4,sK4,sK4,sK4)) != k2_enumset1(sK4,sK4,sK4,sK4) ),
% 7.84/1.48      inference(instantiation,[status(thm)],[c_15]) ).
% 7.84/1.48  
% 7.84/1.48  cnf(c_6564,plain,
% 7.84/1.48      ( r2_hidden(sK1(k2_enumset1(sK4,sK4,sK4,sK4),sK4),sK4)
% 7.84/1.48      | k1_xboole_0 = k2_enumset1(sK4,sK4,sK4,sK4) ),
% 7.84/1.48      inference(global_propositional_subsumption,
% 7.84/1.48                [status(thm)],
% 7.84/1.48                [c_6268,c_3930,c_3931]) ).
% 7.84/1.48  
% 7.84/1.48  cnf(c_6580,plain,
% 7.84/1.48      ( r2_hidden(sK2(k2_enumset1(sK4,sK4,sK4,sK4),sK4),k2_enumset1(sK4,sK4,sK4,sK4))
% 7.84/1.48      | k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)) = sK4
% 7.84/1.48      | k1_xboole_0 = k2_enumset1(sK4,sK4,sK4,sK4) ),
% 7.84/1.48      inference(resolution,[status(thm)],[c_6564,c_21]) ).
% 7.84/1.48  
% 7.84/1.48  cnf(c_6583,plain,
% 7.84/1.48      ( r2_hidden(sK2(k2_enumset1(sK4,sK4,sK4,sK4),sK4),k2_enumset1(sK4,sK4,sK4,sK4))
% 7.84/1.48      | k1_xboole_0 = k2_enumset1(sK4,sK4,sK4,sK4) ),
% 7.84/1.48      inference(global_propositional_subsumption,
% 7.84/1.48                [status(thm)],
% 7.84/1.48                [c_6251,c_26,c_6580]) ).
% 7.84/1.48  
% 7.84/1.48  cnf(c_10,plain,
% 7.84/1.48      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X2)) | X0 = X1 | X0 = X2 ),
% 7.84/1.48      inference(cnf_transformation,[],[f87]) ).
% 7.84/1.48  
% 7.84/1.48  cnf(c_6970,plain,
% 7.84/1.48      ( sK2(k2_enumset1(sK4,sK4,sK4,sK4),sK4) = sK4
% 7.84/1.48      | k1_xboole_0 = k2_enumset1(sK4,sK4,sK4,sK4) ),
% 7.84/1.48      inference(resolution,[status(thm)],[c_6583,c_10]) ).
% 7.84/1.48  
% 7.84/1.48  cnf(c_500,plain,( X0 = X0 ),theory(equality) ).
% 7.84/1.48  
% 7.84/1.48  cnf(c_1499,plain,
% 7.84/1.48      ( X0 != X1 | X1 = X0 ),
% 7.84/1.48      inference(resolution,[status(thm)],[c_501,c_500]) ).
% 7.84/1.48  
% 7.84/1.48  cnf(c_6976,plain,
% 7.84/1.48      ( sK4 = sK2(k2_enumset1(sK4,sK4,sK4,sK4),sK4)
% 7.84/1.48      | k1_xboole_0 = k2_enumset1(sK4,sK4,sK4,sK4) ),
% 7.84/1.48      inference(resolution,[status(thm)],[c_6970,c_1499]) ).
% 7.84/1.48  
% 7.84/1.48  cnf(c_502,plain,
% 7.84/1.48      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.84/1.48      theory(equality) ).
% 7.84/1.48  
% 7.84/1.48  cnf(c_2455,plain,
% 7.84/1.48      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 7.84/1.48      inference(resolution,[status(thm)],[c_502,c_500]) ).
% 7.84/1.48  
% 7.84/1.48  cnf(c_7019,plain,
% 7.84/1.48      ( ~ r1_tarski(sK2(k2_enumset1(sK4,sK4,sK4,sK4),sK4),X0)
% 7.84/1.48      | r1_tarski(sK4,X0)
% 7.84/1.48      | k1_xboole_0 = k2_enumset1(sK4,sK4,sK4,sK4) ),
% 7.84/1.48      inference(resolution,[status(thm)],[c_6976,c_2455]) ).
% 7.84/1.48  
% 7.84/1.48  cnf(c_3,plain,
% 7.84/1.48      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 7.84/1.48      inference(cnf_transformation,[],[f39]) ).
% 7.84/1.48  
% 7.84/1.48  cnf(c_2443,plain,
% 7.84/1.48      ( ~ r1_tarski(X0,X1)
% 7.84/1.48      | r1_tarski(X2,k4_xboole_0(X0,X1))
% 7.84/1.48      | ~ r1_tarski(X3,k1_xboole_0)
% 7.84/1.48      | X2 != X3 ),
% 7.84/1.48      inference(resolution,[status(thm)],[c_502,c_3]) ).
% 7.84/1.48  
% 7.84/1.48  cnf(c_8595,plain,
% 7.84/1.48      ( ~ r1_tarski(X0,X1)
% 7.84/1.48      | r1_tarski(sK2(k2_enumset1(sK4,sK4,sK4,sK4),sK4),k4_xboole_0(X0,X1))
% 7.84/1.48      | ~ r1_tarski(sK4,k1_xboole_0)
% 7.84/1.48      | k1_xboole_0 = k2_enumset1(sK4,sK4,sK4,sK4) ),
% 7.84/1.48      inference(resolution,[status(thm)],[c_2443,c_6970]) ).
% 7.84/1.48  
% 7.84/1.48  cnf(c_10057,plain,
% 7.84/1.48      ( ~ r1_tarski(X0,X1)
% 7.84/1.48      | r1_tarski(sK4,k4_xboole_0(X0,X1))
% 7.84/1.48      | ~ r1_tarski(sK4,k1_xboole_0)
% 7.84/1.48      | k1_xboole_0 = k2_enumset1(sK4,sK4,sK4,sK4) ),
% 7.84/1.48      inference(resolution,[status(thm)],[c_7019,c_8595]) ).
% 7.84/1.48  
% 7.84/1.48  cnf(c_505,plain,
% 7.84/1.48      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.84/1.48      theory(equality) ).
% 7.84/1.48  
% 7.84/1.48  cnf(c_7002,plain,
% 7.84/1.48      ( r2_hidden(X0,sK2(k2_enumset1(sK4,sK4,sK4,sK4),sK4))
% 7.84/1.48      | ~ r2_hidden(X1,sK4)
% 7.84/1.48      | X0 != X1
% 7.84/1.48      | k1_xboole_0 = k2_enumset1(sK4,sK4,sK4,sK4) ),
% 7.84/1.48      inference(resolution,[status(thm)],[c_6970,c_505]) ).
% 7.84/1.48  
% 7.84/1.48  cnf(c_9413,plain,
% 7.84/1.48      ( r2_hidden(X0,sK2(k2_enumset1(sK4,sK4,sK4,sK4),sK4))
% 7.84/1.48      | ~ r2_hidden(X0,sK4)
% 7.84/1.48      | k1_xboole_0 = k2_enumset1(sK4,sK4,sK4,sK4) ),
% 7.84/1.48      inference(resolution,[status(thm)],[c_7002,c_500]) ).
% 7.84/1.48  
% 7.84/1.48  cnf(c_20,plain,
% 7.84/1.48      ( ~ r2_hidden(sK1(X0,X1),X1)
% 7.84/1.48      | ~ r2_hidden(sK1(X0,X1),sK2(X0,X1))
% 7.84/1.48      | k1_setfam_1(X0) = X1
% 7.84/1.48      | k1_xboole_0 = X0 ),
% 7.84/1.48      inference(cnf_transformation,[],[f61]) ).
% 7.84/1.48  
% 7.84/1.48  cnf(c_12210,plain,
% 7.84/1.48      ( ~ r2_hidden(sK1(k2_enumset1(sK4,sK4,sK4,sK4),sK4),sK4)
% 7.84/1.48      | k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)) = sK4
% 7.84/1.48      | k1_xboole_0 = k2_enumset1(sK4,sK4,sK4,sK4) ),
% 7.84/1.48      inference(resolution,[status(thm)],[c_9413,c_20]) ).
% 7.84/1.48  
% 7.84/1.48  cnf(c_12218,plain,
% 7.84/1.48      ( k1_xboole_0 = k2_enumset1(sK4,sK4,sK4,sK4) ),
% 7.84/1.48      inference(global_propositional_subsumption,
% 7.84/1.48                [status(thm)],
% 7.84/1.48                [c_10057,c_26,c_3930,c_3931,c_6268,c_12210]) ).
% 7.84/1.48  
% 7.84/1.48  cnf(c_19350,plain,
% 7.84/1.48      ( X0 != sK4
% 7.84/1.48      | X1 != sK4
% 7.84/1.48      | X2 != sK4
% 7.84/1.48      | X3 != sK4
% 7.84/1.48      | k2_enumset1(X0,X2,X1,X3) = k1_xboole_0 ),
% 7.84/1.48      inference(resolution,[status(thm)],[c_6227,c_12218]) ).
% 7.84/1.48  
% 7.84/1.48  cnf(c_12,plain,
% 7.84/1.48      ( r1_tarski(k1_xboole_0,k2_enumset1(X0,X0,X0,X0)) ),
% 7.84/1.48      inference(cnf_transformation,[],[f89]) ).
% 7.84/1.48  
% 7.84/1.48  cnf(c_17,plain,
% 7.84/1.48      ( ~ r2_hidden(X0,X1) | k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X0)) != X1 ),
% 7.84/1.48      inference(cnf_transformation,[],[f79]) ).
% 7.84/1.48  
% 7.84/1.48  cnf(c_1226,plain,
% 7.84/1.48      ( ~ r2_hidden(X0,k1_xboole_0)
% 7.84/1.48      | k4_xboole_0(k1_xboole_0,k2_enumset1(X0,X0,X0,X0)) != k1_xboole_0 ),
% 7.84/1.48      inference(instantiation,[status(thm)],[c_17]) ).
% 7.84/1.48  
% 7.84/1.48  cnf(c_1227,plain,
% 7.84/1.48      ( ~ r1_tarski(k1_xboole_0,k2_enumset1(X0,X0,X0,X0))
% 7.84/1.48      | k4_xboole_0(k1_xboole_0,k2_enumset1(X0,X0,X0,X0)) = k1_xboole_0 ),
% 7.84/1.48      inference(instantiation,[status(thm)],[c_3]) ).
% 7.84/1.48  
% 7.84/1.48  cnf(c_1389,plain,
% 7.84/1.48      ( r2_hidden(X0,X1)
% 7.84/1.48      | ~ r2_hidden(X2,k2_enumset1(X2,X2,X2,X3))
% 7.84/1.48      | X0 != X2
% 7.84/1.48      | X1 != k2_enumset1(X2,X2,X2,X3) ),
% 7.84/1.48      inference(instantiation,[status(thm)],[c_505]) ).
% 7.84/1.48  
% 7.84/1.48  cnf(c_1742,plain,
% 7.84/1.48      ( ~ r2_hidden(X0,k2_enumset1(X0,X0,X0,X1))
% 7.84/1.48      | r2_hidden(X2,k1_xboole_0)
% 7.84/1.48      | X2 != X0
% 7.84/1.48      | k1_xboole_0 != k2_enumset1(X0,X0,X0,X1) ),
% 7.84/1.48      inference(instantiation,[status(thm)],[c_1389]) ).
% 7.84/1.48  
% 7.84/1.48  cnf(c_10754,plain,
% 7.84/1.48      ( r2_hidden(X0,k1_xboole_0)
% 7.84/1.48      | ~ r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4))
% 7.84/1.48      | X0 != sK4
% 7.84/1.48      | k1_xboole_0 != k2_enumset1(sK4,sK4,sK4,sK4) ),
% 7.84/1.48      inference(instantiation,[status(thm)],[c_1742]) ).
% 7.84/1.48  
% 7.84/1.48  cnf(c_30586,plain,
% 7.84/1.48      ( X0 != sK4 ),
% 7.84/1.48      inference(global_propositional_subsumption,
% 7.84/1.48                [status(thm)],
% 7.84/1.48                [c_19350,c_26,c_12,c_1226,c_1227,c_3930,c_3931,c_6268,c_10754,
% 7.84/1.48                 c_12210]) ).
% 7.84/1.48  
% 7.84/1.48  cnf(c_30625,plain,
% 7.84/1.48      ( $false ),
% 7.84/1.48      inference(resolution,[status(thm)],[c_30586,c_500]) ).
% 7.84/1.48  
% 7.84/1.48  
% 7.84/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 7.84/1.48  
% 7.84/1.48  ------                               Statistics
% 7.84/1.48  
% 7.84/1.48  ------ Selected
% 7.84/1.48  
% 7.84/1.48  total_time:                             0.874
% 7.84/1.48  
%------------------------------------------------------------------------------
