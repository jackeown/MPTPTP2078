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

% Result     : Theorem 4.02s
% Output     : CNFRefutation 4.02s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 404 expanded)
%              Number of clauses        :   48 (  97 expanded)
%              Number of leaves         :   18 ( 116 expanded)
%              Depth                    :   19
%              Number of atoms          :  367 (1618 expanded)
%              Number of equality atoms :  179 ( 801 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
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
    inference(ennf_transformation,[],[f9])).

fof(f29,plain,(
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

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f33,plain,(
    ! [X5,X0] :
      ( ? [X6] :
          ( ~ r2_hidden(X5,X6)
          & r2_hidden(X6,X0) )
     => ( ~ r2_hidden(X5,sK4(X0,X5))
        & r2_hidden(sK4(X0,X5),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X2,X3)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(X2,sK3(X0,X1))
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
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
              ( ~ r2_hidden(sK2(X0,X1),X3)
              & r2_hidden(X3,X0) )
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( ! [X4] :
              ( r2_hidden(sK2(X0,X1),X4)
              | ~ r2_hidden(X4,X0) )
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( ( ( k1_setfam_1(X0) = X1
            | ( ( ( ~ r2_hidden(sK2(X0,X1),sK3(X0,X1))
                  & r2_hidden(sK3(X0,X1),X0) )
                | ~ r2_hidden(sK2(X0,X1),X1) )
              & ( ! [X4] :
                    ( r2_hidden(sK2(X0,X1),X4)
                    | ~ r2_hidden(X4,X0) )
                | r2_hidden(sK2(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ( ~ r2_hidden(X5,sK4(X0,X5))
                    & r2_hidden(sK4(X0,X5),X0) ) )
                & ( ! [X7] :
                      ( r2_hidden(X5,X7)
                      | ~ r2_hidden(X7,X0) )
                  | ~ r2_hidden(X5,X1) ) )
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f30,f33,f32,f31])).

fof(f59,plain,(
    ! [X4,X0,X1] :
      ( k1_setfam_1(X0) = X1
      | r2_hidden(sK2(X0,X1),X4)
      | ~ r2_hidden(X4,X0)
      | r2_hidden(sK2(X0,X1),X1)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f10,conjecture,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(negated_conjecture,[],[f10])).

fof(f14,plain,(
    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 ),
    inference(ennf_transformation,[],[f11])).

fof(f35,plain,
    ( ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0
   => k1_setfam_1(k1_tarski(sK5)) != sK5 ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    k1_setfam_1(k1_tarski(sK5)) != sK5 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f14,f35])).

fof(f64,plain,(
    k1_setfam_1(k1_tarski(sK5)) != sK5 ),
    inference(cnf_transformation,[],[f36])).

fof(f4,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f65,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f48,f49])).

fof(f66,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f47,f65])).

fof(f77,plain,(
    k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)) != sK5 ),
    inference(definition_unfolding,[],[f64,f66])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(X0) = X1
      | r2_hidden(sK3(X0,X1),X0)
      | ~ r2_hidden(sK2(X0,X1),X1)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK1(X0,X1) != X0
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( sK1(X0,X1) = X0
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK1(X0,X1) != X0
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( sK1(X0,X1) = X0
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f23])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f69,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f44,f66])).

fof(f80,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_enumset1(X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f69])).

fof(f81,plain,(
    ! [X3] : r2_hidden(X3,k2_enumset1(X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f80])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f70,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f43,f66])).

fof(f82,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f70])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_setfam_1(X0) != X1
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f88,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_setfam_1(X0)
      | k1_xboole_0 != X0 ) ),
    inference(equality_resolution,[],[f62])).

fof(f89,plain,(
    k1_xboole_0 = k1_setfam_1(k1_xboole_0) ),
    inference(equality_resolution,[],[f88])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f25])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
      | k1_xboole_0 != X0 ) ),
    inference(definition_unfolding,[],[f51,f66])).

fof(f84,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,k2_enumset1(X1,X1,X1,X1)) ),
    inference(equality_resolution,[],[f72])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f15])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f17])).

fof(f37,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(X0) = X1
      | ~ r2_hidden(sK2(X0,X1),sK3(X0,X1))
      | ~ r2_hidden(sK2(X0,X1),X1)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK2(X1,X2),X2)
    | r2_hidden(sK2(X1,X2),X0)
    | k1_setfam_1(X1) = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_24,negated_conjecture,
    ( k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)) != sK5 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_13986,plain,
    ( ~ r2_hidden(X0,k2_enumset1(sK5,sK5,sK5,sK5))
    | r2_hidden(sK2(k2_enumset1(sK5,sK5,sK5,sK5),sK5),X0)
    | r2_hidden(sK2(k2_enumset1(sK5,sK5,sK5,sK5),sK5),sK5)
    | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(resolution,[status(thm)],[c_20,c_24])).

cnf(c_19,plain,
    ( r2_hidden(sK3(X0,X1),X0)
    | ~ r2_hidden(sK2(X0,X1),X1)
    | k1_setfam_1(X0) = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_14018,plain,
    ( ~ r2_hidden(X0,k2_enumset1(sK5,sK5,sK5,sK5))
    | r2_hidden(sK3(k2_enumset1(sK5,sK5,sK5,sK5),sK5),k2_enumset1(sK5,sK5,sK5,sK5))
    | r2_hidden(sK2(k2_enumset1(sK5,sK5,sK5,sK5),sK5),X0)
    | k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)) = sK5
    | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(resolution,[status(thm)],[c_13986,c_19])).

cnf(c_14028,plain,
    ( r2_hidden(sK2(k2_enumset1(sK5,sK5,sK5,sK5),sK5),sK5)
    | ~ r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5))
    | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(factoring,[status(thm)],[c_13986])).

cnf(c_8,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_6073,plain,
    ( r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_14223,plain,
    ( r2_hidden(sK2(k2_enumset1(sK5,sK5,sK5,sK5),sK5),sK5)
    | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14028,c_6073])).

cnf(c_14239,plain,
    ( r2_hidden(sK3(k2_enumset1(sK5,sK5,sK5,sK5),sK5),k2_enumset1(sK5,sK5,sK5,sK5))
    | k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)) = sK5
    | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(resolution,[status(thm)],[c_14223,c_19])).

cnf(c_14242,plain,
    ( r2_hidden(sK3(k2_enumset1(sK5,sK5,sK5,sK5),sK5),k2_enumset1(sK5,sK5,sK5,sK5))
    | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14018,c_24,c_14239])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_14426,plain,
    ( sK3(k2_enumset1(sK5,sK5,sK5,sK5),sK5) = sK5
    | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(resolution,[status(thm)],[c_14242,c_9])).

cnf(c_300,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_14434,plain,
    ( r2_hidden(X0,sK3(k2_enumset1(sK5,sK5,sK5,sK5),sK5))
    | ~ r2_hidden(X1,sK5)
    | X0 != X1
    | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(resolution,[status(thm)],[c_14426,c_300])).

cnf(c_17,plain,
    ( k1_setfam_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_11,plain,
    ( r1_tarski(k1_xboole_0,k2_enumset1(X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_54,plain,
    ( r1_tarski(k1_xboole_0,k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_298,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2152,plain,
    ( k1_setfam_1(X0) != X1
    | sK5 != X1
    | sK5 = k1_setfam_1(X0) ),
    inference(instantiation,[status(thm)],[c_298])).

cnf(c_2153,plain,
    ( k1_setfam_1(k1_xboole_0) != k1_xboole_0
    | sK5 = k1_setfam_1(k1_xboole_0)
    | sK5 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2152])).

cnf(c_6032,plain,
    ( k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)) != X0
    | k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)) = sK5
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_298])).

cnf(c_6039,plain,
    ( k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)) != k1_setfam_1(X0)
    | k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)) = sK5
    | sK5 != k1_setfam_1(X0) ),
    inference(instantiation,[status(thm)],[c_6032])).

cnf(c_6040,plain,
    ( k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)) != k1_setfam_1(k1_xboole_0)
    | k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)) = sK5
    | sK5 != k1_setfam_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_6039])).

cnf(c_303,plain,
    ( X0 != X1
    | k1_setfam_1(X0) = k1_setfam_1(X1) ),
    theory(equality)).

cnf(c_6053,plain,
    ( k2_enumset1(sK5,sK5,sK5,sK5) != X0
    | k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)) = k1_setfam_1(X0) ),
    inference(instantiation,[status(thm)],[c_303])).

cnf(c_6054,plain,
    ( k2_enumset1(sK5,sK5,sK5,sK5) != k1_xboole_0
    | k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)) = k1_setfam_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_6053])).

cnf(c_6096,plain,
    ( X0 != X1
    | k2_enumset1(sK5,sK5,sK5,sK5) != X1
    | k2_enumset1(sK5,sK5,sK5,sK5) = X0 ),
    inference(instantiation,[status(thm)],[c_298])).

cnf(c_6202,plain,
    ( X0 != k2_enumset1(sK5,sK5,sK5,sK5)
    | k2_enumset1(sK5,sK5,sK5,sK5) = X0
    | k2_enumset1(sK5,sK5,sK5,sK5) != k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_6096])).

cnf(c_6203,plain,
    ( X0 != k2_enumset1(sK5,sK5,sK5,sK5)
    | k2_enumset1(sK5,sK5,sK5,sK5) = X0 ),
    inference(equality_resolution_simp,[status(thm)],[c_6202])).

cnf(c_6204,plain,
    ( k2_enumset1(sK5,sK5,sK5,sK5) = k1_xboole_0
    | k1_xboole_0 != k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_6203])).

cnf(c_13253,plain,
    ( ~ r2_hidden(sK5,k2_enumset1(X0,X0,X0,X0))
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_13255,plain,
    ( ~ r2_hidden(sK5,k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | sK5 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_13253])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_13262,plain,
    ( ~ r2_hidden(sK5,X0)
    | r2_hidden(sK5,k2_enumset1(X1,X1,X1,X1))
    | ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_13264,plain,
    ( r2_hidden(sK5,k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | ~ r2_hidden(sK5,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_13262])).

cnf(c_13373,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK5,X2)
    | X2 != X1
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_300])).

cnf(c_14478,plain,
    ( ~ r2_hidden(sK5,X0)
    | r2_hidden(sK5,X1)
    | X1 != X0
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_13373])).

cnf(c_14479,plain,
    ( ~ r2_hidden(sK5,X0)
    | r2_hidden(sK5,X1)
    | X1 != X0 ),
    inference(equality_resolution_simp,[status(thm)],[c_14478])).

cnf(c_14520,plain,
    ( r2_hidden(sK5,X0)
    | ~ r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5))
    | X0 != k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_14479])).

cnf(c_14522,plain,
    ( ~ r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5))
    | r2_hidden(sK5,k1_xboole_0)
    | k1_xboole_0 != k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_14520])).

cnf(c_14596,plain,
    ( X0 != X1
    | ~ r2_hidden(X1,sK5)
    | r2_hidden(X0,sK3(k2_enumset1(sK5,sK5,sK5,sK5),sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14434,c_24,c_17,c_54,c_2153,c_6040,c_6054,c_6073,c_6204,c_13255,c_13264,c_14522])).

cnf(c_14597,plain,
    ( r2_hidden(X0,sK3(k2_enumset1(sK5,sK5,sK5,sK5),sK5))
    | ~ r2_hidden(X1,sK5)
    | X0 != X1 ),
    inference(renaming,[status(thm)],[c_14596])).

cnf(c_297,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_14887,plain,
    ( r2_hidden(X0,sK3(k2_enumset1(sK5,sK5,sK5,sK5),sK5))
    | ~ r2_hidden(X0,sK5) ),
    inference(resolution,[status(thm)],[c_14597,c_297])).

cnf(c_18,plain,
    ( ~ r2_hidden(sK2(X0,X1),X1)
    | ~ r2_hidden(sK2(X0,X1),sK3(X0,X1))
    | k1_setfam_1(X0) = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_15913,plain,
    ( ~ r2_hidden(sK2(k2_enumset1(sK5,sK5,sK5,sK5),sK5),sK5)
    | k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)) = sK5
    | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(resolution,[status(thm)],[c_14887,c_18])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_15913,c_14522,c_14028,c_13264,c_13255,c_6204,c_6073,c_6054,c_6040,c_2153,c_54,c_17,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:18:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 4.02/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.02/0.97  
% 4.02/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.02/0.97  
% 4.02/0.97  ------  iProver source info
% 4.02/0.97  
% 4.02/0.97  git: date: 2020-06-30 10:37:57 +0100
% 4.02/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.02/0.97  git: non_committed_changes: false
% 4.02/0.97  git: last_make_outside_of_git: false
% 4.02/0.97  
% 4.02/0.97  ------ 
% 4.02/0.97  ------ Parsing...
% 4.02/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.02/0.97  
% 4.02/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 4.02/0.97  
% 4.02/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.02/0.97  
% 4.02/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.02/0.97  ------ Proving...
% 4.02/0.97  ------ Problem Properties 
% 4.02/0.97  
% 4.02/0.97  
% 4.02/0.97  clauses                                 23
% 4.02/0.97  conjectures                             1
% 4.02/0.97  EPR                                     3
% 4.02/0.97  Horn                                    13
% 4.02/0.97  unary                                   7
% 4.02/0.97  binary                                  4
% 4.02/0.97  lits                                    56
% 4.02/0.97  lits eq                                 20
% 4.02/0.97  fd_pure                                 0
% 4.02/0.98  fd_pseudo                               0
% 4.02/0.98  fd_cond                                 3
% 4.02/0.98  fd_pseudo_cond                          8
% 4.02/0.98  AC symbols                              0
% 4.02/0.98  
% 4.02/0.98  ------ Input Options Time Limit: Unbounded
% 4.02/0.98  
% 4.02/0.98  
% 4.02/0.98  
% 4.02/0.98  
% 4.02/0.98  ------ Preprocessing...
% 4.02/0.98  
% 4.02/0.98  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 4.02/0.98  Current options:
% 4.02/0.98  ------ 
% 4.02/0.98  
% 4.02/0.98  
% 4.02/0.98  
% 4.02/0.98  
% 4.02/0.98  ------ Proving...
% 4.02/0.98  
% 4.02/0.98  
% 4.02/0.98  ------ Preprocessing...
% 4.02/0.98  
% 4.02/0.98  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.02/0.98  
% 4.02/0.98  ------ Proving...
% 4.02/0.98  
% 4.02/0.98  
% 4.02/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.02/0.98  
% 4.02/0.98  ------ Proving...
% 4.02/0.98  
% 4.02/0.98  
% 4.02/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 4.02/0.98  
% 4.02/0.98  ------ Proving...
% 4.02/0.98  
% 4.02/0.98  
% 4.02/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 4.02/0.98  
% 4.02/0.98  ------ Proving...
% 4.02/0.98  
% 4.02/0.98  
% 4.02/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 4.02/0.98  
% 4.02/0.98  ------ Proving...
% 4.02/0.98  
% 4.02/0.98  
% 4.02/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 4.02/0.98  
% 4.02/0.98  ------ Proving...
% 4.02/0.98  
% 4.02/0.98  
% 4.02/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.02/0.98  
% 4.02/0.98  ------ Proving...
% 4.02/0.98  
% 4.02/0.98  
% 4.02/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.02/0.98  
% 4.02/0.98  ------ Proving...
% 4.02/0.98  
% 4.02/0.98  
% 4.02/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 4.02/0.98  
% 4.02/0.98  ------ Proving...
% 4.02/0.98  
% 4.02/0.98  
% 4.02/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 4.02/0.98  
% 4.02/0.98  ------ Proving...
% 4.02/0.98  
% 4.02/0.98  
% 4.02/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 4.02/0.98  
% 4.02/0.98  ------ Proving...
% 4.02/0.98  
% 4.02/0.98  
% 4.02/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 4.02/0.98  
% 4.02/0.98  ------ Proving...
% 4.02/0.98  
% 4.02/0.98  
% 4.02/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 4.02/0.98  
% 4.02/0.98  ------ Proving...
% 4.02/0.98  
% 4.02/0.98  
% 4.02/0.98  % SZS status Theorem for theBenchmark.p
% 4.02/0.98  
% 4.02/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 4.02/0.98  
% 4.02/0.98  fof(f9,axiom,(
% 4.02/0.98    ! [X0,X1] : ((k1_xboole_0 = X0 => (k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1)) & (k1_xboole_0 != X0 => (k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X3,X0) => r2_hidden(X2,X3))))))),
% 4.02/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.02/0.98  
% 4.02/0.98  fof(f13,plain,(
% 4.02/0.98    ! [X0,X1] : (((k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1) | k1_xboole_0 != X0) & ((k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)))) | k1_xboole_0 = X0))),
% 4.02/0.98    inference(ennf_transformation,[],[f9])).
% 4.02/0.98  
% 4.02/0.98  fof(f29,plain,(
% 4.02/0.98    ! [X0,X1] : ((((k1_setfam_1(X0) = X1 | k1_xboole_0 != X1) & (k1_xboole_0 = X1 | k1_setfam_1(X0) != X1)) | k1_xboole_0 != X0) & (((k1_setfam_1(X0) = X1 | ? [X2] : ((? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)) & (! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0))) & (! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)) | ~r2_hidden(X2,X1))) | k1_setfam_1(X0) != X1)) | k1_xboole_0 = X0))),
% 4.02/0.98    inference(nnf_transformation,[],[f13])).
% 4.02/0.98  
% 4.02/0.98  fof(f30,plain,(
% 4.02/0.98    ! [X0,X1] : ((((k1_setfam_1(X0) = X1 | k1_xboole_0 != X1) & (k1_xboole_0 = X1 | k1_setfam_1(X0) != X1)) | k1_xboole_0 != X0) & (((k1_setfam_1(X0) = X1 | ? [X2] : ((? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)) & (! [X4] : (r2_hidden(X2,X4) | ~r2_hidden(X4,X0)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ? [X6] : (~r2_hidden(X5,X6) & r2_hidden(X6,X0))) & (! [X7] : (r2_hidden(X5,X7) | ~r2_hidden(X7,X0)) | ~r2_hidden(X5,X1))) | k1_setfam_1(X0) != X1)) | k1_xboole_0 = X0))),
% 4.02/0.98    inference(rectify,[],[f29])).
% 4.02/0.98  
% 4.02/0.98  fof(f33,plain,(
% 4.02/0.98    ! [X5,X0] : (? [X6] : (~r2_hidden(X5,X6) & r2_hidden(X6,X0)) => (~r2_hidden(X5,sK4(X0,X5)) & r2_hidden(sK4(X0,X5),X0)))),
% 4.02/0.98    introduced(choice_axiom,[])).
% 4.02/0.98  
% 4.02/0.98  fof(f32,plain,(
% 4.02/0.98    ( ! [X2] : (! [X1,X0] : (? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) => (~r2_hidden(X2,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),X0)))) )),
% 4.02/0.98    introduced(choice_axiom,[])).
% 4.02/0.98  
% 4.02/0.98  fof(f31,plain,(
% 4.02/0.98    ! [X1,X0] : (? [X2] : ((? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)) & (! [X4] : (r2_hidden(X2,X4) | ~r2_hidden(X4,X0)) | r2_hidden(X2,X1))) => ((? [X3] : (~r2_hidden(sK2(X0,X1),X3) & r2_hidden(X3,X0)) | ~r2_hidden(sK2(X0,X1),X1)) & (! [X4] : (r2_hidden(sK2(X0,X1),X4) | ~r2_hidden(X4,X0)) | r2_hidden(sK2(X0,X1),X1))))),
% 4.02/0.98    introduced(choice_axiom,[])).
% 4.02/0.98  
% 4.02/0.98  fof(f34,plain,(
% 4.02/0.98    ! [X0,X1] : ((((k1_setfam_1(X0) = X1 | k1_xboole_0 != X1) & (k1_xboole_0 = X1 | k1_setfam_1(X0) != X1)) | k1_xboole_0 != X0) & (((k1_setfam_1(X0) = X1 | (((~r2_hidden(sK2(X0,X1),sK3(X0,X1)) & r2_hidden(sK3(X0,X1),X0)) | ~r2_hidden(sK2(X0,X1),X1)) & (! [X4] : (r2_hidden(sK2(X0,X1),X4) | ~r2_hidden(X4,X0)) | r2_hidden(sK2(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | (~r2_hidden(X5,sK4(X0,X5)) & r2_hidden(sK4(X0,X5),X0))) & (! [X7] : (r2_hidden(X5,X7) | ~r2_hidden(X7,X0)) | ~r2_hidden(X5,X1))) | k1_setfam_1(X0) != X1)) | k1_xboole_0 = X0))),
% 4.02/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f30,f33,f32,f31])).
% 4.02/0.98  
% 4.02/0.98  fof(f59,plain,(
% 4.02/0.98    ( ! [X4,X0,X1] : (k1_setfam_1(X0) = X1 | r2_hidden(sK2(X0,X1),X4) | ~r2_hidden(X4,X0) | r2_hidden(sK2(X0,X1),X1) | k1_xboole_0 = X0) )),
% 4.02/0.98    inference(cnf_transformation,[],[f34])).
% 4.02/0.98  
% 4.02/0.98  fof(f10,conjecture,(
% 4.02/0.98    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 4.02/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.02/0.98  
% 4.02/0.98  fof(f11,negated_conjecture,(
% 4.02/0.98    ~! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 4.02/0.98    inference(negated_conjecture,[],[f10])).
% 4.02/0.98  
% 4.02/0.98  fof(f14,plain,(
% 4.02/0.98    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0),
% 4.02/0.98    inference(ennf_transformation,[],[f11])).
% 4.02/0.98  
% 4.02/0.98  fof(f35,plain,(
% 4.02/0.98    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 => k1_setfam_1(k1_tarski(sK5)) != sK5),
% 4.02/0.98    introduced(choice_axiom,[])).
% 4.02/0.98  
% 4.02/0.98  fof(f36,plain,(
% 4.02/0.98    k1_setfam_1(k1_tarski(sK5)) != sK5),
% 4.02/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f14,f35])).
% 4.02/0.98  
% 4.02/0.98  fof(f64,plain,(
% 4.02/0.98    k1_setfam_1(k1_tarski(sK5)) != sK5),
% 4.02/0.98    inference(cnf_transformation,[],[f36])).
% 4.02/0.98  
% 4.02/0.98  fof(f4,axiom,(
% 4.02/0.98    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 4.02/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.02/0.98  
% 4.02/0.98  fof(f47,plain,(
% 4.02/0.98    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 4.02/0.98    inference(cnf_transformation,[],[f4])).
% 4.02/0.98  
% 4.02/0.98  fof(f5,axiom,(
% 4.02/0.98    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 4.02/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.02/0.98  
% 4.02/0.98  fof(f48,plain,(
% 4.02/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 4.02/0.98    inference(cnf_transformation,[],[f5])).
% 4.02/0.98  
% 4.02/0.98  fof(f6,axiom,(
% 4.02/0.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 4.02/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.02/0.98  
% 4.02/0.98  fof(f49,plain,(
% 4.02/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 4.02/0.98    inference(cnf_transformation,[],[f6])).
% 4.02/0.98  
% 4.02/0.98  fof(f65,plain,(
% 4.02/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 4.02/0.98    inference(definition_unfolding,[],[f48,f49])).
% 4.02/0.98  
% 4.02/0.98  fof(f66,plain,(
% 4.02/0.98    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 4.02/0.98    inference(definition_unfolding,[],[f47,f65])).
% 4.02/0.98  
% 4.02/0.98  fof(f77,plain,(
% 4.02/0.98    k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)) != sK5),
% 4.02/0.98    inference(definition_unfolding,[],[f64,f66])).
% 4.02/0.98  
% 4.02/0.98  fof(f60,plain,(
% 4.02/0.98    ( ! [X0,X1] : (k1_setfam_1(X0) = X1 | r2_hidden(sK3(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1) | k1_xboole_0 = X0) )),
% 4.02/0.98    inference(cnf_transformation,[],[f34])).
% 4.02/0.98  
% 4.02/0.98  fof(f3,axiom,(
% 4.02/0.98    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 4.02/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.02/0.98  
% 4.02/0.98  fof(f21,plain,(
% 4.02/0.98    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 4.02/0.98    inference(nnf_transformation,[],[f3])).
% 4.02/0.98  
% 4.02/0.98  fof(f22,plain,(
% 4.02/0.98    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 4.02/0.98    inference(rectify,[],[f21])).
% 4.02/0.98  
% 4.02/0.98  fof(f23,plain,(
% 4.02/0.98    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1))))),
% 4.02/0.98    introduced(choice_axiom,[])).
% 4.02/0.98  
% 4.02/0.98  fof(f24,plain,(
% 4.02/0.98    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 4.02/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f23])).
% 4.02/0.98  
% 4.02/0.98  fof(f44,plain,(
% 4.02/0.98    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 4.02/0.98    inference(cnf_transformation,[],[f24])).
% 4.02/0.98  
% 4.02/0.98  fof(f69,plain,(
% 4.02/0.98    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 4.02/0.98    inference(definition_unfolding,[],[f44,f66])).
% 4.02/0.98  
% 4.02/0.98  fof(f80,plain,(
% 4.02/0.98    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_enumset1(X3,X3,X3,X3) != X1) )),
% 4.02/0.98    inference(equality_resolution,[],[f69])).
% 4.02/0.98  
% 4.02/0.98  fof(f81,plain,(
% 4.02/0.98    ( ! [X3] : (r2_hidden(X3,k2_enumset1(X3,X3,X3,X3))) )),
% 4.02/0.98    inference(equality_resolution,[],[f80])).
% 4.02/0.98  
% 4.02/0.98  fof(f43,plain,(
% 4.02/0.98    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 4.02/0.98    inference(cnf_transformation,[],[f24])).
% 4.02/0.98  
% 4.02/0.98  fof(f70,plain,(
% 4.02/0.98    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 4.02/0.98    inference(definition_unfolding,[],[f43,f66])).
% 4.02/0.98  
% 4.02/0.98  fof(f82,plain,(
% 4.02/0.98    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))) )),
% 4.02/0.98    inference(equality_resolution,[],[f70])).
% 4.02/0.98  
% 4.02/0.98  fof(f62,plain,(
% 4.02/0.98    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_setfam_1(X0) != X1 | k1_xboole_0 != X0) )),
% 4.02/0.98    inference(cnf_transformation,[],[f34])).
% 4.02/0.98  
% 4.02/0.98  fof(f88,plain,(
% 4.02/0.98    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(X0) | k1_xboole_0 != X0) )),
% 4.02/0.98    inference(equality_resolution,[],[f62])).
% 4.02/0.98  
% 4.02/0.98  fof(f89,plain,(
% 4.02/0.98    k1_xboole_0 = k1_setfam_1(k1_xboole_0)),
% 4.02/0.98    inference(equality_resolution,[],[f88])).
% 4.02/0.98  
% 4.02/0.98  fof(f7,axiom,(
% 4.02/0.98    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 4.02/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.02/0.98  
% 4.02/0.98  fof(f25,plain,(
% 4.02/0.98    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 4.02/0.98    inference(nnf_transformation,[],[f7])).
% 4.02/0.98  
% 4.02/0.98  fof(f26,plain,(
% 4.02/0.98    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 4.02/0.98    inference(flattening,[],[f25])).
% 4.02/0.98  
% 4.02/0.98  fof(f51,plain,(
% 4.02/0.98    ( ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 != X0) )),
% 4.02/0.98    inference(cnf_transformation,[],[f26])).
% 4.02/0.98  
% 4.02/0.98  fof(f72,plain,(
% 4.02/0.98    ( ! [X0,X1] : (r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) | k1_xboole_0 != X0) )),
% 4.02/0.98    inference(definition_unfolding,[],[f51,f66])).
% 4.02/0.98  
% 4.02/0.98  fof(f84,plain,(
% 4.02/0.98    ( ! [X1] : (r1_tarski(k1_xboole_0,k2_enumset1(X1,X1,X1,X1))) )),
% 4.02/0.98    inference(equality_resolution,[],[f72])).
% 4.02/0.98  
% 4.02/0.98  fof(f1,axiom,(
% 4.02/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 4.02/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.02/0.98  
% 4.02/0.98  fof(f12,plain,(
% 4.02/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 4.02/0.98    inference(ennf_transformation,[],[f1])).
% 4.02/0.98  
% 4.02/0.98  fof(f15,plain,(
% 4.02/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 4.02/0.98    inference(nnf_transformation,[],[f12])).
% 4.02/0.98  
% 4.02/0.98  fof(f16,plain,(
% 4.02/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 4.02/0.98    inference(rectify,[],[f15])).
% 4.02/0.98  
% 4.02/0.98  fof(f17,plain,(
% 4.02/0.98    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 4.02/0.98    introduced(choice_axiom,[])).
% 4.02/0.98  
% 4.02/0.98  fof(f18,plain,(
% 4.02/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 4.02/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f17])).
% 4.02/0.98  
% 4.02/0.98  fof(f37,plain,(
% 4.02/0.98    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 4.02/0.98    inference(cnf_transformation,[],[f18])).
% 4.02/0.98  
% 4.02/0.98  fof(f61,plain,(
% 4.02/0.98    ( ! [X0,X1] : (k1_setfam_1(X0) = X1 | ~r2_hidden(sK2(X0,X1),sK3(X0,X1)) | ~r2_hidden(sK2(X0,X1),X1) | k1_xboole_0 = X0) )),
% 4.02/0.98    inference(cnf_transformation,[],[f34])).
% 4.02/0.98  
% 4.02/0.98  cnf(c_20,plain,
% 4.02/0.98      ( ~ r2_hidden(X0,X1)
% 4.02/0.98      | r2_hidden(sK2(X1,X2),X2)
% 4.02/0.98      | r2_hidden(sK2(X1,X2),X0)
% 4.02/0.98      | k1_setfam_1(X1) = X2
% 4.02/0.98      | k1_xboole_0 = X1 ),
% 4.02/0.98      inference(cnf_transformation,[],[f59]) ).
% 4.02/0.98  
% 4.02/0.98  cnf(c_24,negated_conjecture,
% 4.02/0.98      ( k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)) != sK5 ),
% 4.02/0.98      inference(cnf_transformation,[],[f77]) ).
% 4.02/0.98  
% 4.02/0.98  cnf(c_13986,plain,
% 4.02/0.98      ( ~ r2_hidden(X0,k2_enumset1(sK5,sK5,sK5,sK5))
% 4.02/0.98      | r2_hidden(sK2(k2_enumset1(sK5,sK5,sK5,sK5),sK5),X0)
% 4.02/0.98      | r2_hidden(sK2(k2_enumset1(sK5,sK5,sK5,sK5),sK5),sK5)
% 4.02/0.98      | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
% 4.02/0.98      inference(resolution,[status(thm)],[c_20,c_24]) ).
% 4.02/0.98  
% 4.02/0.98  cnf(c_19,plain,
% 4.02/0.98      ( r2_hidden(sK3(X0,X1),X0)
% 4.02/0.98      | ~ r2_hidden(sK2(X0,X1),X1)
% 4.02/0.98      | k1_setfam_1(X0) = X1
% 4.02/0.98      | k1_xboole_0 = X0 ),
% 4.02/0.98      inference(cnf_transformation,[],[f60]) ).
% 4.02/0.98  
% 4.02/0.98  cnf(c_14018,plain,
% 4.02/0.98      ( ~ r2_hidden(X0,k2_enumset1(sK5,sK5,sK5,sK5))
% 4.02/0.98      | r2_hidden(sK3(k2_enumset1(sK5,sK5,sK5,sK5),sK5),k2_enumset1(sK5,sK5,sK5,sK5))
% 4.02/0.98      | r2_hidden(sK2(k2_enumset1(sK5,sK5,sK5,sK5),sK5),X0)
% 4.02/0.98      | k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)) = sK5
% 4.02/0.98      | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
% 4.02/0.98      inference(resolution,[status(thm)],[c_13986,c_19]) ).
% 4.02/0.98  
% 4.02/0.98  cnf(c_14028,plain,
% 4.02/0.98      ( r2_hidden(sK2(k2_enumset1(sK5,sK5,sK5,sK5),sK5),sK5)
% 4.02/0.98      | ~ r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5))
% 4.02/0.98      | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
% 4.02/0.98      inference(factoring,[status(thm)],[c_13986]) ).
% 4.02/0.98  
% 4.02/0.98  cnf(c_8,plain,
% 4.02/0.98      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) ),
% 4.02/0.98      inference(cnf_transformation,[],[f81]) ).
% 4.02/0.98  
% 4.02/0.98  cnf(c_6073,plain,
% 4.02/0.98      ( r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5)) ),
% 4.02/0.98      inference(instantiation,[status(thm)],[c_8]) ).
% 4.02/0.98  
% 4.02/0.98  cnf(c_14223,plain,
% 4.02/0.98      ( r2_hidden(sK2(k2_enumset1(sK5,sK5,sK5,sK5),sK5),sK5)
% 4.02/0.98      | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
% 4.02/0.98      inference(global_propositional_subsumption,
% 4.02/0.98                [status(thm)],
% 4.02/0.98                [c_14028,c_6073]) ).
% 4.02/0.98  
% 4.02/0.98  cnf(c_14239,plain,
% 4.02/0.98      ( r2_hidden(sK3(k2_enumset1(sK5,sK5,sK5,sK5),sK5),k2_enumset1(sK5,sK5,sK5,sK5))
% 4.02/0.98      | k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)) = sK5
% 4.02/0.98      | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
% 4.02/0.98      inference(resolution,[status(thm)],[c_14223,c_19]) ).
% 4.02/0.98  
% 4.02/0.98  cnf(c_14242,plain,
% 4.02/0.98      ( r2_hidden(sK3(k2_enumset1(sK5,sK5,sK5,sK5),sK5),k2_enumset1(sK5,sK5,sK5,sK5))
% 4.02/0.98      | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
% 4.02/0.98      inference(global_propositional_subsumption,
% 4.02/0.98                [status(thm)],
% 4.02/0.98                [c_14018,c_24,c_14239]) ).
% 4.02/0.98  
% 4.02/0.98  cnf(c_9,plain,
% 4.02/0.98      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) | X0 = X1 ),
% 4.02/0.98      inference(cnf_transformation,[],[f82]) ).
% 4.02/0.98  
% 4.02/0.98  cnf(c_14426,plain,
% 4.02/0.98      ( sK3(k2_enumset1(sK5,sK5,sK5,sK5),sK5) = sK5
% 4.02/0.98      | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
% 4.02/0.98      inference(resolution,[status(thm)],[c_14242,c_9]) ).
% 4.02/0.98  
% 4.02/0.98  cnf(c_300,plain,
% 4.02/0.98      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 4.02/0.98      theory(equality) ).
% 4.02/0.98  
% 4.02/0.98  cnf(c_14434,plain,
% 4.02/0.98      ( r2_hidden(X0,sK3(k2_enumset1(sK5,sK5,sK5,sK5),sK5))
% 4.02/0.98      | ~ r2_hidden(X1,sK5)
% 4.02/0.98      | X0 != X1
% 4.02/0.98      | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
% 4.02/0.98      inference(resolution,[status(thm)],[c_14426,c_300]) ).
% 4.02/0.98  
% 4.02/0.98  cnf(c_17,plain,
% 4.02/0.98      ( k1_setfam_1(k1_xboole_0) = k1_xboole_0 ),
% 4.02/0.98      inference(cnf_transformation,[],[f89]) ).
% 4.02/0.98  
% 4.02/0.98  cnf(c_11,plain,
% 4.02/0.98      ( r1_tarski(k1_xboole_0,k2_enumset1(X0,X0,X0,X0)) ),
% 4.02/0.98      inference(cnf_transformation,[],[f84]) ).
% 4.02/0.98  
% 4.02/0.98  cnf(c_54,plain,
% 4.02/0.98      ( r1_tarski(k1_xboole_0,k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
% 4.02/0.98      inference(instantiation,[status(thm)],[c_11]) ).
% 4.02/0.98  
% 4.02/0.98  cnf(c_298,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 4.02/0.98  
% 4.02/0.98  cnf(c_2152,plain,
% 4.02/0.98      ( k1_setfam_1(X0) != X1 | sK5 != X1 | sK5 = k1_setfam_1(X0) ),
% 4.02/0.98      inference(instantiation,[status(thm)],[c_298]) ).
% 4.02/0.98  
% 4.02/0.98  cnf(c_2153,plain,
% 4.02/0.98      ( k1_setfam_1(k1_xboole_0) != k1_xboole_0
% 4.02/0.98      | sK5 = k1_setfam_1(k1_xboole_0)
% 4.02/0.98      | sK5 != k1_xboole_0 ),
% 4.02/0.98      inference(instantiation,[status(thm)],[c_2152]) ).
% 4.02/0.98  
% 4.02/0.98  cnf(c_6032,plain,
% 4.02/0.98      ( k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)) != X0
% 4.02/0.98      | k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)) = sK5
% 4.02/0.98      | sK5 != X0 ),
% 4.02/0.98      inference(instantiation,[status(thm)],[c_298]) ).
% 4.02/0.98  
% 4.02/0.98  cnf(c_6039,plain,
% 4.02/0.98      ( k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)) != k1_setfam_1(X0)
% 4.02/0.98      | k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)) = sK5
% 4.02/0.98      | sK5 != k1_setfam_1(X0) ),
% 4.02/0.98      inference(instantiation,[status(thm)],[c_6032]) ).
% 4.02/0.98  
% 4.02/0.98  cnf(c_6040,plain,
% 4.02/0.98      ( k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)) != k1_setfam_1(k1_xboole_0)
% 4.02/0.98      | k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)) = sK5
% 4.02/0.98      | sK5 != k1_setfam_1(k1_xboole_0) ),
% 4.02/0.98      inference(instantiation,[status(thm)],[c_6039]) ).
% 4.02/0.98  
% 4.02/0.98  cnf(c_303,plain,
% 4.02/0.98      ( X0 != X1 | k1_setfam_1(X0) = k1_setfam_1(X1) ),
% 4.02/0.98      theory(equality) ).
% 4.02/0.98  
% 4.02/0.98  cnf(c_6053,plain,
% 4.02/0.98      ( k2_enumset1(sK5,sK5,sK5,sK5) != X0
% 4.02/0.98      | k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)) = k1_setfam_1(X0) ),
% 4.02/0.98      inference(instantiation,[status(thm)],[c_303]) ).
% 4.02/0.98  
% 4.02/0.98  cnf(c_6054,plain,
% 4.02/0.98      ( k2_enumset1(sK5,sK5,sK5,sK5) != k1_xboole_0
% 4.02/0.98      | k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)) = k1_setfam_1(k1_xboole_0) ),
% 4.02/0.98      inference(instantiation,[status(thm)],[c_6053]) ).
% 4.02/0.98  
% 4.02/0.98  cnf(c_6096,plain,
% 4.02/0.98      ( X0 != X1
% 4.02/0.98      | k2_enumset1(sK5,sK5,sK5,sK5) != X1
% 4.02/0.98      | k2_enumset1(sK5,sK5,sK5,sK5) = X0 ),
% 4.02/0.98      inference(instantiation,[status(thm)],[c_298]) ).
% 4.02/0.98  
% 4.02/0.98  cnf(c_6202,plain,
% 4.02/0.98      ( X0 != k2_enumset1(sK5,sK5,sK5,sK5)
% 4.02/0.98      | k2_enumset1(sK5,sK5,sK5,sK5) = X0
% 4.02/0.98      | k2_enumset1(sK5,sK5,sK5,sK5) != k2_enumset1(sK5,sK5,sK5,sK5) ),
% 4.02/0.98      inference(instantiation,[status(thm)],[c_6096]) ).
% 4.02/0.98  
% 4.02/0.98  cnf(c_6203,plain,
% 4.02/0.98      ( X0 != k2_enumset1(sK5,sK5,sK5,sK5)
% 4.02/0.98      | k2_enumset1(sK5,sK5,sK5,sK5) = X0 ),
% 4.02/0.98      inference(equality_resolution_simp,[status(thm)],[c_6202]) ).
% 4.02/0.98  
% 4.02/0.98  cnf(c_6204,plain,
% 4.02/0.98      ( k2_enumset1(sK5,sK5,sK5,sK5) = k1_xboole_0
% 4.02/0.98      | k1_xboole_0 != k2_enumset1(sK5,sK5,sK5,sK5) ),
% 4.02/0.98      inference(instantiation,[status(thm)],[c_6203]) ).
% 4.02/0.98  
% 4.02/0.98  cnf(c_13253,plain,
% 4.02/0.98      ( ~ r2_hidden(sK5,k2_enumset1(X0,X0,X0,X0)) | sK5 = X0 ),
% 4.02/0.98      inference(instantiation,[status(thm)],[c_9]) ).
% 4.02/0.98  
% 4.02/0.98  cnf(c_13255,plain,
% 4.02/0.98      ( ~ r2_hidden(sK5,k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
% 4.02/0.98      | sK5 = k1_xboole_0 ),
% 4.02/0.98      inference(instantiation,[status(thm)],[c_13253]) ).
% 4.02/0.98  
% 4.02/0.98  cnf(c_2,plain,
% 4.02/0.98      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 4.02/0.98      inference(cnf_transformation,[],[f37]) ).
% 4.02/0.98  
% 4.02/0.98  cnf(c_13262,plain,
% 4.02/0.98      ( ~ r2_hidden(sK5,X0)
% 4.02/0.98      | r2_hidden(sK5,k2_enumset1(X1,X1,X1,X1))
% 4.02/0.98      | ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) ),
% 4.02/0.98      inference(instantiation,[status(thm)],[c_2]) ).
% 4.02/0.98  
% 4.02/0.98  cnf(c_13264,plain,
% 4.02/0.98      ( r2_hidden(sK5,k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
% 4.02/0.98      | ~ r2_hidden(sK5,k1_xboole_0)
% 4.02/0.98      | ~ r1_tarski(k1_xboole_0,k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
% 4.02/0.98      inference(instantiation,[status(thm)],[c_13262]) ).
% 4.02/0.98  
% 4.02/0.98  cnf(c_13373,plain,
% 4.02/0.98      ( ~ r2_hidden(X0,X1) | r2_hidden(sK5,X2) | X2 != X1 | sK5 != X0 ),
% 4.02/0.98      inference(instantiation,[status(thm)],[c_300]) ).
% 4.02/0.98  
% 4.02/0.98  cnf(c_14478,plain,
% 4.02/0.98      ( ~ r2_hidden(sK5,X0) | r2_hidden(sK5,X1) | X1 != X0 | sK5 != sK5 ),
% 4.02/0.98      inference(instantiation,[status(thm)],[c_13373]) ).
% 4.02/0.98  
% 4.02/0.98  cnf(c_14479,plain,
% 4.02/0.98      ( ~ r2_hidden(sK5,X0) | r2_hidden(sK5,X1) | X1 != X0 ),
% 4.02/0.98      inference(equality_resolution_simp,[status(thm)],[c_14478]) ).
% 4.02/0.98  
% 4.02/0.98  cnf(c_14520,plain,
% 4.02/0.98      ( r2_hidden(sK5,X0)
% 4.02/0.98      | ~ r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5))
% 4.02/0.98      | X0 != k2_enumset1(sK5,sK5,sK5,sK5) ),
% 4.02/0.98      inference(instantiation,[status(thm)],[c_14479]) ).
% 4.02/0.98  
% 4.02/0.98  cnf(c_14522,plain,
% 4.02/0.98      ( ~ r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5))
% 4.02/0.98      | r2_hidden(sK5,k1_xboole_0)
% 4.02/0.98      | k1_xboole_0 != k2_enumset1(sK5,sK5,sK5,sK5) ),
% 4.02/0.98      inference(instantiation,[status(thm)],[c_14520]) ).
% 4.02/0.98  
% 4.02/0.98  cnf(c_14596,plain,
% 4.02/0.98      ( X0 != X1
% 4.02/0.98      | ~ r2_hidden(X1,sK5)
% 4.02/0.98      | r2_hidden(X0,sK3(k2_enumset1(sK5,sK5,sK5,sK5),sK5)) ),
% 4.02/0.98      inference(global_propositional_subsumption,
% 4.02/0.98                [status(thm)],
% 4.02/0.98                [c_14434,c_24,c_17,c_54,c_2153,c_6040,c_6054,c_6073,
% 4.02/0.98                 c_6204,c_13255,c_13264,c_14522]) ).
% 4.02/0.98  
% 4.02/0.98  cnf(c_14597,plain,
% 4.02/0.98      ( r2_hidden(X0,sK3(k2_enumset1(sK5,sK5,sK5,sK5),sK5))
% 4.02/0.98      | ~ r2_hidden(X1,sK5)
% 4.02/0.98      | X0 != X1 ),
% 4.02/0.98      inference(renaming,[status(thm)],[c_14596]) ).
% 4.02/0.98  
% 4.02/0.98  cnf(c_297,plain,( X0 = X0 ),theory(equality) ).
% 4.02/0.98  
% 4.02/0.98  cnf(c_14887,plain,
% 4.02/0.98      ( r2_hidden(X0,sK3(k2_enumset1(sK5,sK5,sK5,sK5),sK5))
% 4.02/0.98      | ~ r2_hidden(X0,sK5) ),
% 4.02/0.98      inference(resolution,[status(thm)],[c_14597,c_297]) ).
% 4.02/0.98  
% 4.02/0.98  cnf(c_18,plain,
% 4.02/0.98      ( ~ r2_hidden(sK2(X0,X1),X1)
% 4.02/0.98      | ~ r2_hidden(sK2(X0,X1),sK3(X0,X1))
% 4.02/0.98      | k1_setfam_1(X0) = X1
% 4.02/0.98      | k1_xboole_0 = X0 ),
% 4.02/0.98      inference(cnf_transformation,[],[f61]) ).
% 4.02/0.98  
% 4.02/0.98  cnf(c_15913,plain,
% 4.02/0.98      ( ~ r2_hidden(sK2(k2_enumset1(sK5,sK5,sK5,sK5),sK5),sK5)
% 4.02/0.98      | k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)) = sK5
% 4.02/0.98      | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
% 4.02/0.98      inference(resolution,[status(thm)],[c_14887,c_18]) ).
% 4.02/0.98  
% 4.02/0.98  cnf(contradiction,plain,
% 4.02/0.98      ( $false ),
% 4.02/0.98      inference(minisat,
% 4.02/0.98                [status(thm)],
% 4.02/0.98                [c_15913,c_14522,c_14028,c_13264,c_13255,c_6204,c_6073,
% 4.02/0.98                 c_6054,c_6040,c_2153,c_54,c_17,c_24]) ).
% 4.02/0.98  
% 4.02/0.98  
% 4.02/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 4.02/0.98  
% 4.02/0.98  ------                               Statistics
% 4.02/0.98  
% 4.02/0.98  ------ Selected
% 4.02/0.98  
% 4.02/0.98  total_time:                             0.461
% 4.02/0.98  
%------------------------------------------------------------------------------
