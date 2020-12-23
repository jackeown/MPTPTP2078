%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:35:21 EST 2020

% Result     : Theorem 6.95s
% Output     : CNFRefutation 6.95s
% Verified   : 
% Statistics : Number of formulae       :   81 (1302 expanded)
%              Number of clauses        :   39 ( 262 expanded)
%              Number of leaves         :   12 ( 366 expanded)
%              Depth                    :   21
%              Number of atoms          :  311 (6418 expanded)
%              Number of equality atoms :  142 (3342 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f12])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f13])).

fof(f15,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f15])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f33,f42])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,X1)
     => ( k3_xboole_0(k2_tarski(X0,X2),X1) = k1_tarski(X0)
        | ( X0 != X2
          & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X0,X1)
       => ( k3_xboole_0(k2_tarski(X0,X2),X1) = k1_tarski(X0)
          | ( X0 != X2
            & r2_hidden(X2,X1) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( k3_xboole_0(k2_tarski(X0,X2),X1) != k1_tarski(X0)
      & ( X0 = X2
        | ~ r2_hidden(X2,X1) )
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( k3_xboole_0(k2_tarski(X0,X2),X1) != k1_tarski(X0)
      & ( X0 = X2
        | ~ r2_hidden(X2,X1) )
      & r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f10])).

fof(f27,plain,
    ( ? [X0,X1,X2] :
        ( k3_xboole_0(k2_tarski(X0,X2),X1) != k1_tarski(X0)
        & ( X0 = X2
          | ~ r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) )
   => ( k3_xboole_0(k2_tarski(sK3,sK5),sK4) != k1_tarski(sK3)
      & ( sK3 = sK5
        | ~ r2_hidden(sK5,sK4) )
      & r2_hidden(sK3,sK4) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( k3_xboole_0(k2_tarski(sK3,sK5),sK4) != k1_tarski(sK3)
    & ( sK3 = sK5
      | ~ r2_hidden(sK5,sK4) )
    & r2_hidden(sK3,sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f11,f27])).

fof(f53,plain,(
    k3_xboole_0(k2_tarski(sK3,sK5),sK4) != k1_tarski(sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f54,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f49,f50])).

fof(f68,plain,(
    k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK5),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK5),sK4)) != k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(definition_unfolding,[],[f53,f42,f50,f54])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f24,plain,(
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
    inference(rectify,[],[f23])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK2(X0,X1,X2) != X1
            & sK2(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( sK2(X0,X1,X2) = X1
          | sK2(X0,X1,X2) = X0
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK2(X0,X1,X2) != X1
              & sK2(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( sK2(X0,X1,X2) = X1
            | sK2(X0,X1,X2) = X0
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f25])).

fof(f43,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f67,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f43,f50])).

fof(f79,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k2_enumset1(X0,X0,X0,X1)) ) ),
    inference(equality_resolution,[],[f67])).

fof(f51,plain,(
    r2_hidden(sK3,sK4) ),
    inference(cnf_transformation,[],[f28])).

fof(f52,plain,
    ( sK3 = sK5
    | ~ r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f28])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f34,f42])).

fof(f44,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f66,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f44,f50])).

fof(f77,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_enumset1(X4,X4,X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f66])).

fof(f78,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_enumset1(X4,X4,X4,X1)) ),
    inference(equality_resolution,[],[f77])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f35,f42])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_19,negated_conjecture,
    ( k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK5),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK5),sK4)) != k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2894,plain,
    ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK5))
    | r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(resolution,[status(thm)],[c_3,c_19])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_3077,plain,
    ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3))
    | sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)) = sK5
    | sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)) = sK3 ),
    inference(resolution,[status(thm)],[c_2894,c_18])).

cnf(c_3365,plain,
    ( sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)) = sK5
    | sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)) = sK3 ),
    inference(resolution,[status(thm)],[c_3077,c_18])).

cnf(c_218,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3388,plain,
    ( X0 != sK5
    | sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)) = X0
    | sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)) = sK3 ),
    inference(resolution,[status(thm)],[c_3365,c_218])).

cnf(c_21,negated_conjecture,
    ( r2_hidden(sK3,sK4) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_20,negated_conjecture,
    ( ~ r2_hidden(sK5,sK4)
    | sK3 = sK5 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_217,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1010,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_217])).

cnf(c_1162,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_218,c_217])).

cnf(c_3387,plain,
    ( sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)) = sK3
    | sK5 = sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(resolution,[status(thm)],[c_3365,c_1162])).

cnf(c_3389,plain,
    ( sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)) = sK3
    | sK3 != sK5 ),
    inference(instantiation,[status(thm)],[c_3388])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2842,plain,
    ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3))
    | r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),sK4) ),
    inference(resolution,[status(thm)],[c_2,c_19])).

cnf(c_3069,plain,
    ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),sK4)
    | sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)) = sK3 ),
    inference(resolution,[status(thm)],[c_2842,c_18])).

cnf(c_220,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1272,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_220,c_217])).

cnf(c_3089,plain,
    ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),X0)
    | r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),sK4)
    | ~ r2_hidden(sK3,X0) ),
    inference(resolution,[status(thm)],[c_3069,c_1272])).

cnf(c_3771,plain,
    ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),sK4)
    | ~ r2_hidden(sK3,sK4) ),
    inference(factoring,[status(thm)],[c_3089])).

cnf(c_832,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),sK4)
    | X0 != sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3))
    | X1 != sK4 ),
    inference(instantiation,[status(thm)],[c_220])).

cnf(c_1435,plain,
    ( r2_hidden(X0,sK4)
    | ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),sK4)
    | X0 != sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3))
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_832])).

cnf(c_4559,plain,
    ( ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),sK4)
    | r2_hidden(sK5,sK4)
    | sK4 != sK4
    | sK5 != sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(instantiation,[status(thm)],[c_1435])).

cnf(c_4819,plain,
    ( sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3388,c_21,c_20,c_1010,c_3387,c_3389,c_3771,c_4559])).

cnf(c_4825,plain,
    ( sK3 = sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(resolution,[status(thm)],[c_4819,c_1162])).

cnf(c_5726,plain,
    ( ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),X0)
    | r2_hidden(sK3,X0) ),
    inference(resolution,[status(thm)],[c_4825,c_1272])).

cnf(c_17010,plain,
    ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3))
    | r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK5)) ),
    inference(resolution,[status(thm)],[c_5726,c_2894])).

cnf(c_17,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_28,plain,
    ( r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_4827,plain,
    ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),X0)
    | ~ r2_hidden(sK3,X0) ),
    inference(resolution,[status(thm)],[c_4819,c_1272])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | ~ r2_hidden(sK0(X0,X1,X2),X0)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_6058,plain,
    ( ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK5))
    | ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),sK4)
    | ~ r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK3))
    | k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK5),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK5),sK4)) = k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(resolution,[status(thm)],[c_4827,c_1])).

cnf(c_17024,plain,
    ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17010,c_21,c_19,c_28,c_2894,c_3771,c_6058])).

cnf(c_17036,plain,
    ( ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK5))
    | ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),sK4)
    | k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK5),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK5),sK4)) = k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(resolution,[status(thm)],[c_17024,c_1])).

cnf(c_17552,plain,
    ( ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17036,c_21,c_19,c_28,c_3771,c_6058])).

cnf(c_17567,plain,
    ( ~ r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK5)) ),
    inference(resolution,[status(thm)],[c_17552,c_4827])).

cnf(c_17905,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_17567,c_17])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:05:44 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 6.95/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.95/1.49  
% 6.95/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 6.95/1.49  
% 6.95/1.49  ------  iProver source info
% 6.95/1.49  
% 6.95/1.49  git: date: 2020-06-30 10:37:57 +0100
% 6.95/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 6.95/1.49  git: non_committed_changes: false
% 6.95/1.49  git: last_make_outside_of_git: false
% 6.95/1.49  
% 6.95/1.49  ------ 
% 6.95/1.49  ------ Parsing...
% 6.95/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 6.95/1.49  
% 6.95/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 6.95/1.49  
% 6.95/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 6.95/1.49  
% 6.95/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 6.95/1.49  ------ Proving...
% 6.95/1.49  ------ Problem Properties 
% 6.95/1.49  
% 6.95/1.49  
% 6.95/1.49  clauses                                 22
% 6.95/1.49  conjectures                             3
% 6.95/1.49  EPR                                     2
% 6.95/1.49  Horn                                    14
% 6.95/1.49  unary                                   5
% 6.95/1.49  binary                                  5
% 6.95/1.49  lits                                    54
% 6.95/1.49  lits eq                                 18
% 6.95/1.49  fd_pure                                 0
% 6.95/1.49  fd_pseudo                               0
% 6.95/1.49  fd_cond                                 0
% 6.95/1.49  fd_pseudo_cond                          9
% 6.95/1.49  AC symbols                              0
% 6.95/1.49  
% 6.95/1.49  ------ Input Options Time Limit: Unbounded
% 6.95/1.49  
% 6.95/1.49  
% 6.95/1.49  ------ 
% 6.95/1.49  Current options:
% 6.95/1.49  ------ 
% 6.95/1.49  
% 6.95/1.49  
% 6.95/1.49  
% 6.95/1.49  
% 6.95/1.49  ------ Proving...
% 6.95/1.49  
% 6.95/1.49  
% 6.95/1.49  % SZS status Theorem for theBenchmark.p
% 6.95/1.49  
% 6.95/1.49   Resolution empty clause
% 6.95/1.49  
% 6.95/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 6.95/1.49  
% 6.95/1.49  fof(f2,axiom,(
% 6.95/1.49    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 6.95/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.95/1.49  
% 6.95/1.49  fof(f12,plain,(
% 6.95/1.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 6.95/1.49    inference(nnf_transformation,[],[f2])).
% 6.95/1.49  
% 6.95/1.49  fof(f13,plain,(
% 6.95/1.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 6.95/1.49    inference(flattening,[],[f12])).
% 6.95/1.49  
% 6.95/1.49  fof(f14,plain,(
% 6.95/1.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 6.95/1.49    inference(rectify,[],[f13])).
% 6.95/1.49  
% 6.95/1.49  fof(f15,plain,(
% 6.95/1.49    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 6.95/1.49    introduced(choice_axiom,[])).
% 6.95/1.49  
% 6.95/1.49  fof(f16,plain,(
% 6.95/1.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 6.95/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f15])).
% 6.95/1.49  
% 6.95/1.49  fof(f33,plain,(
% 6.95/1.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 6.95/1.49    inference(cnf_transformation,[],[f16])).
% 6.95/1.49  
% 6.95/1.49  fof(f4,axiom,(
% 6.95/1.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 6.95/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.95/1.49  
% 6.95/1.49  fof(f42,plain,(
% 6.95/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 6.95/1.49    inference(cnf_transformation,[],[f4])).
% 6.95/1.49  
% 6.95/1.49  fof(f58,plain,(
% 6.95/1.49    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 6.95/1.49    inference(definition_unfolding,[],[f33,f42])).
% 6.95/1.49  
% 6.95/1.49  fof(f8,conjecture,(
% 6.95/1.49    ! [X0,X1,X2] : (r2_hidden(X0,X1) => (k3_xboole_0(k2_tarski(X0,X2),X1) = k1_tarski(X0) | (X0 != X2 & r2_hidden(X2,X1))))),
% 6.95/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.95/1.49  
% 6.95/1.49  fof(f9,negated_conjecture,(
% 6.95/1.49    ~! [X0,X1,X2] : (r2_hidden(X0,X1) => (k3_xboole_0(k2_tarski(X0,X2),X1) = k1_tarski(X0) | (X0 != X2 & r2_hidden(X2,X1))))),
% 6.95/1.49    inference(negated_conjecture,[],[f8])).
% 6.95/1.49  
% 6.95/1.49  fof(f10,plain,(
% 6.95/1.49    ? [X0,X1,X2] : ((k3_xboole_0(k2_tarski(X0,X2),X1) != k1_tarski(X0) & (X0 = X2 | ~r2_hidden(X2,X1))) & r2_hidden(X0,X1))),
% 6.95/1.49    inference(ennf_transformation,[],[f9])).
% 6.95/1.49  
% 6.95/1.49  fof(f11,plain,(
% 6.95/1.49    ? [X0,X1,X2] : (k3_xboole_0(k2_tarski(X0,X2),X1) != k1_tarski(X0) & (X0 = X2 | ~r2_hidden(X2,X1)) & r2_hidden(X0,X1))),
% 6.95/1.49    inference(flattening,[],[f10])).
% 6.95/1.49  
% 6.95/1.49  fof(f27,plain,(
% 6.95/1.49    ? [X0,X1,X2] : (k3_xboole_0(k2_tarski(X0,X2),X1) != k1_tarski(X0) & (X0 = X2 | ~r2_hidden(X2,X1)) & r2_hidden(X0,X1)) => (k3_xboole_0(k2_tarski(sK3,sK5),sK4) != k1_tarski(sK3) & (sK3 = sK5 | ~r2_hidden(sK5,sK4)) & r2_hidden(sK3,sK4))),
% 6.95/1.49    introduced(choice_axiom,[])).
% 6.95/1.49  
% 6.95/1.49  fof(f28,plain,(
% 6.95/1.49    k3_xboole_0(k2_tarski(sK3,sK5),sK4) != k1_tarski(sK3) & (sK3 = sK5 | ~r2_hidden(sK5,sK4)) & r2_hidden(sK3,sK4)),
% 6.95/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f11,f27])).
% 6.95/1.49  
% 6.95/1.49  fof(f53,plain,(
% 6.95/1.49    k3_xboole_0(k2_tarski(sK3,sK5),sK4) != k1_tarski(sK3)),
% 6.95/1.49    inference(cnf_transformation,[],[f28])).
% 6.95/1.49  
% 6.95/1.49  fof(f6,axiom,(
% 6.95/1.49    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 6.95/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.95/1.49  
% 6.95/1.49  fof(f49,plain,(
% 6.95/1.49    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 6.95/1.49    inference(cnf_transformation,[],[f6])).
% 6.95/1.49  
% 6.95/1.49  fof(f7,axiom,(
% 6.95/1.49    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)),
% 6.95/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.95/1.49  
% 6.95/1.49  fof(f50,plain,(
% 6.95/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 6.95/1.49    inference(cnf_transformation,[],[f7])).
% 6.95/1.49  
% 6.95/1.49  fof(f54,plain,(
% 6.95/1.49    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 6.95/1.49    inference(definition_unfolding,[],[f49,f50])).
% 6.95/1.49  
% 6.95/1.49  fof(f68,plain,(
% 6.95/1.49    k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK5),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK5),sK4)) != k2_enumset1(sK3,sK3,sK3,sK3)),
% 6.95/1.49    inference(definition_unfolding,[],[f53,f42,f50,f54])).
% 6.95/1.49  
% 6.95/1.49  fof(f5,axiom,(
% 6.95/1.49    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 6.95/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.95/1.49  
% 6.95/1.49  fof(f22,plain,(
% 6.95/1.49    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 6.95/1.49    inference(nnf_transformation,[],[f5])).
% 6.95/1.49  
% 6.95/1.49  fof(f23,plain,(
% 6.95/1.49    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 6.95/1.49    inference(flattening,[],[f22])).
% 6.95/1.49  
% 6.95/1.49  fof(f24,plain,(
% 6.95/1.49    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 6.95/1.49    inference(rectify,[],[f23])).
% 6.95/1.49  
% 6.95/1.49  fof(f25,plain,(
% 6.95/1.49    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK2(X0,X1,X2) != X1 & sK2(X0,X1,X2) != X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (sK2(X0,X1,X2) = X1 | sK2(X0,X1,X2) = X0 | r2_hidden(sK2(X0,X1,X2),X2))))),
% 6.95/1.49    introduced(choice_axiom,[])).
% 6.95/1.49  
% 6.95/1.49  fof(f26,plain,(
% 6.95/1.49    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK2(X0,X1,X2) != X1 & sK2(X0,X1,X2) != X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (sK2(X0,X1,X2) = X1 | sK2(X0,X1,X2) = X0 | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 6.95/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f25])).
% 6.95/1.49  
% 6.95/1.49  fof(f43,plain,(
% 6.95/1.49    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 6.95/1.49    inference(cnf_transformation,[],[f26])).
% 6.95/1.49  
% 6.95/1.49  fof(f67,plain,(
% 6.95/1.49    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 6.95/1.49    inference(definition_unfolding,[],[f43,f50])).
% 6.95/1.49  
% 6.95/1.49  fof(f79,plain,(
% 6.95/1.49    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k2_enumset1(X0,X0,X0,X1))) )),
% 6.95/1.49    inference(equality_resolution,[],[f67])).
% 6.95/1.49  
% 6.95/1.49  fof(f51,plain,(
% 6.95/1.49    r2_hidden(sK3,sK4)),
% 6.95/1.49    inference(cnf_transformation,[],[f28])).
% 6.95/1.49  
% 6.95/1.49  fof(f52,plain,(
% 6.95/1.49    sK3 = sK5 | ~r2_hidden(sK5,sK4)),
% 6.95/1.49    inference(cnf_transformation,[],[f28])).
% 6.95/1.49  
% 6.95/1.49  fof(f34,plain,(
% 6.95/1.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 6.95/1.49    inference(cnf_transformation,[],[f16])).
% 6.95/1.49  
% 6.95/1.49  fof(f57,plain,(
% 6.95/1.49    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 6.95/1.49    inference(definition_unfolding,[],[f34,f42])).
% 6.95/1.49  
% 6.95/1.49  fof(f44,plain,(
% 6.95/1.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 6.95/1.49    inference(cnf_transformation,[],[f26])).
% 6.95/1.49  
% 6.95/1.49  fof(f66,plain,(
% 6.95/1.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 6.95/1.49    inference(definition_unfolding,[],[f44,f50])).
% 6.95/1.49  
% 6.95/1.49  fof(f77,plain,(
% 6.95/1.49    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_enumset1(X4,X4,X4,X1) != X2) )),
% 6.95/1.49    inference(equality_resolution,[],[f66])).
% 6.95/1.49  
% 6.95/1.49  fof(f78,plain,(
% 6.95/1.49    ( ! [X4,X1] : (r2_hidden(X4,k2_enumset1(X4,X4,X4,X1))) )),
% 6.95/1.49    inference(equality_resolution,[],[f77])).
% 6.95/1.49  
% 6.95/1.49  fof(f35,plain,(
% 6.95/1.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 6.95/1.49    inference(cnf_transformation,[],[f16])).
% 6.95/1.49  
% 6.95/1.49  fof(f56,plain,(
% 6.95/1.49    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 6.95/1.49    inference(definition_unfolding,[],[f35,f42])).
% 6.95/1.49  
% 6.95/1.49  cnf(c_3,plain,
% 6.95/1.49      ( r2_hidden(sK0(X0,X1,X2),X0)
% 6.95/1.49      | r2_hidden(sK0(X0,X1,X2),X2)
% 6.95/1.49      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
% 6.95/1.49      inference(cnf_transformation,[],[f58]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_19,negated_conjecture,
% 6.95/1.49      ( k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK5),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK5),sK4)) != k2_enumset1(sK3,sK3,sK3,sK3) ),
% 6.95/1.49      inference(cnf_transformation,[],[f68]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_2894,plain,
% 6.95/1.49      ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK5))
% 6.95/1.49      | r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3)) ),
% 6.95/1.49      inference(resolution,[status(thm)],[c_3,c_19]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_18,plain,
% 6.95/1.49      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X2)) | X0 = X1 | X0 = X2 ),
% 6.95/1.49      inference(cnf_transformation,[],[f79]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_3077,plain,
% 6.95/1.49      ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3))
% 6.95/1.49      | sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)) = sK5
% 6.95/1.49      | sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)) = sK3 ),
% 6.95/1.49      inference(resolution,[status(thm)],[c_2894,c_18]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_3365,plain,
% 6.95/1.49      ( sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)) = sK5
% 6.95/1.49      | sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)) = sK3 ),
% 6.95/1.49      inference(resolution,[status(thm)],[c_3077,c_18]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_218,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_3388,plain,
% 6.95/1.49      ( X0 != sK5
% 6.95/1.49      | sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)) = X0
% 6.95/1.49      | sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)) = sK3 ),
% 6.95/1.49      inference(resolution,[status(thm)],[c_3365,c_218]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_21,negated_conjecture,
% 6.95/1.49      ( r2_hidden(sK3,sK4) ),
% 6.95/1.49      inference(cnf_transformation,[],[f51]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_20,negated_conjecture,
% 6.95/1.49      ( ~ r2_hidden(sK5,sK4) | sK3 = sK5 ),
% 6.95/1.49      inference(cnf_transformation,[],[f52]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_217,plain,( X0 = X0 ),theory(equality) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_1010,plain,
% 6.95/1.49      ( sK4 = sK4 ),
% 6.95/1.49      inference(instantiation,[status(thm)],[c_217]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_1162,plain,
% 6.95/1.49      ( X0 != X1 | X1 = X0 ),
% 6.95/1.49      inference(resolution,[status(thm)],[c_218,c_217]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_3387,plain,
% 6.95/1.49      ( sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)) = sK3
% 6.95/1.49      | sK5 = sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)) ),
% 6.95/1.49      inference(resolution,[status(thm)],[c_3365,c_1162]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_3389,plain,
% 6.95/1.49      ( sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)) = sK3
% 6.95/1.49      | sK3 != sK5 ),
% 6.95/1.49      inference(instantiation,[status(thm)],[c_3388]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_2,plain,
% 6.95/1.49      ( r2_hidden(sK0(X0,X1,X2),X1)
% 6.95/1.49      | r2_hidden(sK0(X0,X1,X2),X2)
% 6.95/1.49      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
% 6.95/1.49      inference(cnf_transformation,[],[f57]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_2842,plain,
% 6.95/1.49      ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3))
% 6.95/1.49      | r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),sK4) ),
% 6.95/1.49      inference(resolution,[status(thm)],[c_2,c_19]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_3069,plain,
% 6.95/1.49      ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),sK4)
% 6.95/1.49      | sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)) = sK3 ),
% 6.95/1.49      inference(resolution,[status(thm)],[c_2842,c_18]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_220,plain,
% 6.95/1.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 6.95/1.49      theory(equality) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_1272,plain,
% 6.95/1.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X1) | X2 != X0 ),
% 6.95/1.49      inference(resolution,[status(thm)],[c_220,c_217]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_3089,plain,
% 6.95/1.49      ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),X0)
% 6.95/1.49      | r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),sK4)
% 6.95/1.49      | ~ r2_hidden(sK3,X0) ),
% 6.95/1.49      inference(resolution,[status(thm)],[c_3069,c_1272]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_3771,plain,
% 6.95/1.49      ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),sK4)
% 6.95/1.49      | ~ r2_hidden(sK3,sK4) ),
% 6.95/1.49      inference(factoring,[status(thm)],[c_3089]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_832,plain,
% 6.95/1.49      ( r2_hidden(X0,X1)
% 6.95/1.49      | ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),sK4)
% 6.95/1.49      | X0 != sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3))
% 6.95/1.49      | X1 != sK4 ),
% 6.95/1.49      inference(instantiation,[status(thm)],[c_220]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_1435,plain,
% 6.95/1.49      ( r2_hidden(X0,sK4)
% 6.95/1.49      | ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),sK4)
% 6.95/1.49      | X0 != sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3))
% 6.95/1.49      | sK4 != sK4 ),
% 6.95/1.49      inference(instantiation,[status(thm)],[c_832]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_4559,plain,
% 6.95/1.49      ( ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),sK4)
% 6.95/1.49      | r2_hidden(sK5,sK4)
% 6.95/1.49      | sK4 != sK4
% 6.95/1.49      | sK5 != sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)) ),
% 6.95/1.49      inference(instantiation,[status(thm)],[c_1435]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_4819,plain,
% 6.95/1.49      ( sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)) = sK3 ),
% 6.95/1.49      inference(global_propositional_subsumption,
% 6.95/1.49                [status(thm)],
% 6.95/1.49                [c_3388,c_21,c_20,c_1010,c_3387,c_3389,c_3771,c_4559]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_4825,plain,
% 6.95/1.49      ( sK3 = sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)) ),
% 6.95/1.49      inference(resolution,[status(thm)],[c_4819,c_1162]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_5726,plain,
% 6.95/1.49      ( ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),X0)
% 6.95/1.49      | r2_hidden(sK3,X0) ),
% 6.95/1.49      inference(resolution,[status(thm)],[c_4825,c_1272]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_17010,plain,
% 6.95/1.49      ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3))
% 6.95/1.49      | r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK5)) ),
% 6.95/1.49      inference(resolution,[status(thm)],[c_5726,c_2894]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_17,plain,
% 6.95/1.49      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
% 6.95/1.49      inference(cnf_transformation,[],[f78]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_28,plain,
% 6.95/1.49      ( r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK3)) ),
% 6.95/1.49      inference(instantiation,[status(thm)],[c_17]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_4827,plain,
% 6.95/1.49      ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),X0)
% 6.95/1.49      | ~ r2_hidden(sK3,X0) ),
% 6.95/1.49      inference(resolution,[status(thm)],[c_4819,c_1272]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_1,plain,
% 6.95/1.49      ( ~ r2_hidden(sK0(X0,X1,X2),X1)
% 6.95/1.49      | ~ r2_hidden(sK0(X0,X1,X2),X0)
% 6.95/1.49      | ~ r2_hidden(sK0(X0,X1,X2),X2)
% 6.95/1.49      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
% 6.95/1.49      inference(cnf_transformation,[],[f56]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_6058,plain,
% 6.95/1.49      ( ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK5))
% 6.95/1.49      | ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),sK4)
% 6.95/1.49      | ~ r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK3))
% 6.95/1.49      | k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK5),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK5),sK4)) = k2_enumset1(sK3,sK3,sK3,sK3) ),
% 6.95/1.49      inference(resolution,[status(thm)],[c_4827,c_1]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_17024,plain,
% 6.95/1.49      ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3)) ),
% 6.95/1.49      inference(global_propositional_subsumption,
% 6.95/1.49                [status(thm)],
% 6.95/1.49                [c_17010,c_21,c_19,c_28,c_2894,c_3771,c_6058]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_17036,plain,
% 6.95/1.49      ( ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK5))
% 6.95/1.49      | ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),sK4)
% 6.95/1.49      | k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK5),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK5),sK4)) = k2_enumset1(sK3,sK3,sK3,sK3) ),
% 6.95/1.49      inference(resolution,[status(thm)],[c_17024,c_1]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_17552,plain,
% 6.95/1.49      ( ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK5)) ),
% 6.95/1.49      inference(global_propositional_subsumption,
% 6.95/1.49                [status(thm)],
% 6.95/1.49                [c_17036,c_21,c_19,c_28,c_3771,c_6058]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_17567,plain,
% 6.95/1.49      ( ~ r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK5)) ),
% 6.95/1.49      inference(resolution,[status(thm)],[c_17552,c_4827]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_17905,plain,
% 6.95/1.49      ( $false ),
% 6.95/1.49      inference(forward_subsumption_resolution,[status(thm)],[c_17567,c_17]) ).
% 6.95/1.49  
% 6.95/1.49  
% 6.95/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 6.95/1.49  
% 6.95/1.49  ------                               Statistics
% 6.95/1.49  
% 6.95/1.49  ------ Selected
% 6.95/1.49  
% 6.95/1.49  total_time:                             0.581
% 6.95/1.49  
%------------------------------------------------------------------------------
