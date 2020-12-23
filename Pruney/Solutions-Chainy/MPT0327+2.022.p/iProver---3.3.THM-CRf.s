%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:38:01 EST 2020

% Result     : Theorem 23.70s
% Output     : CNFRefutation 23.70s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 146 expanded)
%              Number of clauses        :   26 (  27 expanded)
%              Number of leaves         :   15 (  44 expanded)
%              Depth                    :   11
%              Number of atoms          :  229 ( 377 expanded)
%              Number of equality atoms :   98 ( 177 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f13])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f14])).

fof(f16,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & ~ r2_hidden(sK0(X0,X1,X2),X0) )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( r2_hidden(sK0(X0,X1,X2),X1)
          | r2_hidden(sK0(X0,X1,X2),X0)
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & ~ r2_hidden(sK0(X0,X1,X2),X0) )
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( r2_hidden(sK0(X0,X1,X2),X1)
            | r2_hidden(sK0(X0,X1,X2),X0)
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f33,f31])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f29,f43])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f28,f43])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
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
    inference(nnf_transformation,[],[f6])).

fof(f19,plain,(
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
    inference(rectify,[],[f18])).

fof(f20,plain,(
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

fof(f21,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f20])).

fof(f34,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f7,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f44,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f39,f40])).

fof(f45,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f38,f44])).

fof(f57,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f34,f45])).

fof(f64,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f57])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f46,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f24,f43,f43])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f53,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),X0))) ),
    inference(definition_unfolding,[],[f32,f43,f43,f31])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    inference(negated_conjecture,[],[f10])).

fof(f12,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f22,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
        & r2_hidden(X0,X1) )
   => ( k2_xboole_0(k4_xboole_0(sK3,k1_tarski(sK2)),k1_tarski(sK2)) != sK3
      & r2_hidden(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( k2_xboole_0(k4_xboole_0(sK3,k1_tarski(sK2)),k1_tarski(sK2)) != sK3
    & r2_hidden(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f12,f22])).

fof(f42,plain,(
    k2_xboole_0(k4_xboole_0(sK3,k1_tarski(sK2)),k1_tarski(sK2)) != sK3 ),
    inference(cnf_transformation,[],[f23])).

fof(f58,plain,(
    k5_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k3_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK2,sK2,sK2,sK2)))))) != sK3 ),
    inference(definition_unfolding,[],[f42,f43,f31,f45,f45])).

fof(f41,plain,(
    r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_2,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X2)
    | ~ r2_hidden(sK0(X0,X1,X2),X0)
    | k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X2 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_529,plain,
    ( ~ r2_hidden(sK0(X0,X1,sK3),X0)
    | ~ r2_hidden(sK0(X0,X1,sK3),sK3)
    | k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = sK3 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_994,plain,
    ( ~ r2_hidden(sK0(sK3,X0,sK3),sK3)
    | k5_xboole_0(sK3,k5_xboole_0(X0,k3_xboole_0(X0,sK3))) = sK3 ),
    inference(instantiation,[status(thm)],[c_529])).

cnf(c_65082,plain,
    ( ~ r2_hidden(sK0(sK3,k2_enumset1(sK2,sK2,sK2,sK2),sK3),sK3)
    | k5_xboole_0(sK3,k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k3_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK3))) = sK3 ),
    inference(instantiation,[status(thm)],[c_994])).

cnf(c_135,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_443,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK2,sK3)
    | X0 != sK2
    | X1 != sK3 ),
    inference(instantiation,[status(thm)],[c_135])).

cnf(c_563,plain,
    ( r2_hidden(X0,sK3)
    | ~ r2_hidden(sK2,sK3)
    | X0 != sK2
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_443])).

cnf(c_4016,plain,
    ( r2_hidden(sK0(X0,X1,sK3),sK3)
    | ~ r2_hidden(sK2,sK3)
    | sK0(X0,X1,sK3) != sK2
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_563])).

cnf(c_24421,plain,
    ( r2_hidden(sK0(sK3,k2_enumset1(sK2,sK2,sK2,sK2),sK3),sK3)
    | ~ r2_hidden(sK2,sK3)
    | sK0(sK3,k2_enumset1(sK2,sK2,sK2,sK2),sK3) != sK2
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_4016])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(sK0(X0,X1,X2),X0)
    | k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X2 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_528,plain,
    ( r2_hidden(sK0(X0,X1,sK3),X1)
    | r2_hidden(sK0(X0,X1,sK3),X0)
    | r2_hidden(sK0(X0,X1,sK3),sK3)
    | k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = sK3 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_992,plain,
    ( r2_hidden(sK0(sK3,X0,sK3),X0)
    | r2_hidden(sK0(sK3,X0,sK3),sK3)
    | k5_xboole_0(sK3,k5_xboole_0(X0,k3_xboole_0(X0,sK3))) = sK3 ),
    inference(instantiation,[status(thm)],[c_528])).

cnf(c_14490,plain,
    ( r2_hidden(sK0(sK3,k2_enumset1(sK2,sK2,sK2,sK2),sK3),k2_enumset1(sK2,sK2,sK2,sK2))
    | r2_hidden(sK0(sK3,k2_enumset1(sK2,sK2,sK2,sK2),sK3),sK3)
    | k5_xboole_0(sK3,k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k3_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK3))) = sK3 ),
    inference(instantiation,[status(thm)],[c_992])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_7405,plain,
    ( ~ r2_hidden(sK0(sK3,X0,X1),k2_enumset1(sK2,sK2,sK2,sK2))
    | sK0(sK3,X0,X1) = sK2 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_14489,plain,
    ( ~ r2_hidden(sK0(sK3,k2_enumset1(sK2,sK2,sK2,sK2),sK3),k2_enumset1(sK2,sK2,sK2,sK2))
    | sK0(sK3,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = sK2 ),
    inference(instantiation,[status(thm)],[c_7405])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),X0))) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_12,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k3_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK2,sK2,sK2,sK2)))))) != sK3 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_570,plain,
    ( k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k5_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k3_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k2_enumset1(sK2,sK2,sK2,sK2)))) != sK3 ),
    inference(demodulation,[status(thm)],[c_0,c_12])).

cnf(c_823,plain,
    ( k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK2,sK2,sK2,sK2)))) != sK3 ),
    inference(demodulation,[status(thm)],[c_7,c_570])).

cnf(c_861,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k3_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK3))) != sK3 ),
    inference(superposition,[status(thm)],[c_0,c_823])).

cnf(c_131,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_564,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_131])).

cnf(c_13,negated_conjecture,
    ( r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f41])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_65082,c_24421,c_14490,c_14489,c_861,c_564,c_13])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:41:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 23.70/3.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.70/3.50  
% 23.70/3.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.70/3.50  
% 23.70/3.50  ------  iProver source info
% 23.70/3.50  
% 23.70/3.50  git: date: 2020-06-30 10:37:57 +0100
% 23.70/3.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.70/3.50  git: non_committed_changes: false
% 23.70/3.50  git: last_make_outside_of_git: false
% 23.70/3.50  
% 23.70/3.50  ------ 
% 23.70/3.50  
% 23.70/3.50  ------ Input Options
% 23.70/3.50  
% 23.70/3.50  --out_options                           all
% 23.70/3.50  --tptp_safe_out                         true
% 23.70/3.50  --problem_path                          ""
% 23.70/3.50  --include_path                          ""
% 23.70/3.50  --clausifier                            res/vclausify_rel
% 23.70/3.50  --clausifier_options                    --mode clausify
% 23.70/3.50  --stdin                                 false
% 23.70/3.50  --stats_out                             all
% 23.70/3.50  
% 23.70/3.50  ------ General Options
% 23.70/3.50  
% 23.70/3.50  --fof                                   false
% 23.70/3.50  --time_out_real                         305.
% 23.70/3.50  --time_out_virtual                      -1.
% 23.70/3.50  --symbol_type_check                     false
% 23.70/3.50  --clausify_out                          false
% 23.70/3.50  --sig_cnt_out                           false
% 23.70/3.50  --trig_cnt_out                          false
% 23.70/3.50  --trig_cnt_out_tolerance                1.
% 23.70/3.50  --trig_cnt_out_sk_spl                   false
% 23.70/3.50  --abstr_cl_out                          false
% 23.70/3.50  
% 23.70/3.50  ------ Global Options
% 23.70/3.50  
% 23.70/3.50  --schedule                              default
% 23.70/3.50  --add_important_lit                     false
% 23.70/3.50  --prop_solver_per_cl                    1000
% 23.70/3.50  --min_unsat_core                        false
% 23.70/3.50  --soft_assumptions                      false
% 23.70/3.50  --soft_lemma_size                       3
% 23.70/3.50  --prop_impl_unit_size                   0
% 23.70/3.50  --prop_impl_unit                        []
% 23.70/3.50  --share_sel_clauses                     true
% 23.70/3.50  --reset_solvers                         false
% 23.70/3.50  --bc_imp_inh                            [conj_cone]
% 23.70/3.50  --conj_cone_tolerance                   3.
% 23.70/3.50  --extra_neg_conj                        none
% 23.70/3.50  --large_theory_mode                     true
% 23.70/3.50  --prolific_symb_bound                   200
% 23.70/3.50  --lt_threshold                          2000
% 23.70/3.50  --clause_weak_htbl                      true
% 23.70/3.50  --gc_record_bc_elim                     false
% 23.70/3.50  
% 23.70/3.50  ------ Preprocessing Options
% 23.70/3.50  
% 23.70/3.50  --preprocessing_flag                    true
% 23.70/3.50  --time_out_prep_mult                    0.1
% 23.70/3.50  --splitting_mode                        input
% 23.70/3.50  --splitting_grd                         true
% 23.70/3.50  --splitting_cvd                         false
% 23.70/3.50  --splitting_cvd_svl                     false
% 23.70/3.50  --splitting_nvd                         32
% 23.70/3.50  --sub_typing                            true
% 23.70/3.50  --prep_gs_sim                           true
% 23.70/3.50  --prep_unflatten                        true
% 23.70/3.50  --prep_res_sim                          true
% 23.70/3.50  --prep_upred                            true
% 23.70/3.50  --prep_sem_filter                       exhaustive
% 23.70/3.50  --prep_sem_filter_out                   false
% 23.70/3.50  --pred_elim                             true
% 23.70/3.50  --res_sim_input                         true
% 23.70/3.50  --eq_ax_congr_red                       true
% 23.70/3.50  --pure_diseq_elim                       true
% 23.70/3.50  --brand_transform                       false
% 23.70/3.50  --non_eq_to_eq                          false
% 23.70/3.50  --prep_def_merge                        true
% 23.70/3.50  --prep_def_merge_prop_impl              false
% 23.70/3.50  --prep_def_merge_mbd                    true
% 23.70/3.50  --prep_def_merge_tr_red                 false
% 23.70/3.50  --prep_def_merge_tr_cl                  false
% 23.70/3.50  --smt_preprocessing                     true
% 23.70/3.50  --smt_ac_axioms                         fast
% 23.70/3.50  --preprocessed_out                      false
% 23.70/3.50  --preprocessed_stats                    false
% 23.70/3.50  
% 23.70/3.50  ------ Abstraction refinement Options
% 23.70/3.50  
% 23.70/3.50  --abstr_ref                             []
% 23.70/3.50  --abstr_ref_prep                        false
% 23.70/3.50  --abstr_ref_until_sat                   false
% 23.70/3.50  --abstr_ref_sig_restrict                funpre
% 23.70/3.50  --abstr_ref_af_restrict_to_split_sk     false
% 23.70/3.50  --abstr_ref_under                       []
% 23.70/3.50  
% 23.70/3.50  ------ SAT Options
% 23.70/3.50  
% 23.70/3.50  --sat_mode                              false
% 23.70/3.50  --sat_fm_restart_options                ""
% 23.70/3.50  --sat_gr_def                            false
% 23.70/3.50  --sat_epr_types                         true
% 23.70/3.50  --sat_non_cyclic_types                  false
% 23.70/3.50  --sat_finite_models                     false
% 23.70/3.50  --sat_fm_lemmas                         false
% 23.70/3.50  --sat_fm_prep                           false
% 23.70/3.50  --sat_fm_uc_incr                        true
% 23.70/3.50  --sat_out_model                         small
% 23.70/3.50  --sat_out_clauses                       false
% 23.70/3.50  
% 23.70/3.50  ------ QBF Options
% 23.70/3.50  
% 23.70/3.50  --qbf_mode                              false
% 23.70/3.50  --qbf_elim_univ                         false
% 23.70/3.50  --qbf_dom_inst                          none
% 23.70/3.50  --qbf_dom_pre_inst                      false
% 23.70/3.50  --qbf_sk_in                             false
% 23.70/3.50  --qbf_pred_elim                         true
% 23.70/3.50  --qbf_split                             512
% 23.70/3.50  
% 23.70/3.50  ------ BMC1 Options
% 23.70/3.50  
% 23.70/3.50  --bmc1_incremental                      false
% 23.70/3.50  --bmc1_axioms                           reachable_all
% 23.70/3.50  --bmc1_min_bound                        0
% 23.70/3.50  --bmc1_max_bound                        -1
% 23.70/3.50  --bmc1_max_bound_default                -1
% 23.70/3.50  --bmc1_symbol_reachability              true
% 23.70/3.50  --bmc1_property_lemmas                  false
% 23.70/3.50  --bmc1_k_induction                      false
% 23.70/3.50  --bmc1_non_equiv_states                 false
% 23.70/3.50  --bmc1_deadlock                         false
% 23.70/3.50  --bmc1_ucm                              false
% 23.70/3.50  --bmc1_add_unsat_core                   none
% 23.70/3.50  --bmc1_unsat_core_children              false
% 23.70/3.50  --bmc1_unsat_core_extrapolate_axioms    false
% 23.70/3.50  --bmc1_out_stat                         full
% 23.70/3.50  --bmc1_ground_init                      false
% 23.70/3.50  --bmc1_pre_inst_next_state              false
% 23.70/3.50  --bmc1_pre_inst_state                   false
% 23.70/3.50  --bmc1_pre_inst_reach_state             false
% 23.70/3.50  --bmc1_out_unsat_core                   false
% 23.70/3.50  --bmc1_aig_witness_out                  false
% 23.70/3.50  --bmc1_verbose                          false
% 23.70/3.50  --bmc1_dump_clauses_tptp                false
% 23.70/3.50  --bmc1_dump_unsat_core_tptp             false
% 23.70/3.50  --bmc1_dump_file                        -
% 23.70/3.50  --bmc1_ucm_expand_uc_limit              128
% 23.70/3.50  --bmc1_ucm_n_expand_iterations          6
% 23.70/3.50  --bmc1_ucm_extend_mode                  1
% 23.70/3.50  --bmc1_ucm_init_mode                    2
% 23.70/3.50  --bmc1_ucm_cone_mode                    none
% 23.70/3.50  --bmc1_ucm_reduced_relation_type        0
% 23.70/3.50  --bmc1_ucm_relax_model                  4
% 23.70/3.50  --bmc1_ucm_full_tr_after_sat            true
% 23.70/3.50  --bmc1_ucm_expand_neg_assumptions       false
% 23.70/3.50  --bmc1_ucm_layered_model                none
% 23.70/3.50  --bmc1_ucm_max_lemma_size               10
% 23.70/3.50  
% 23.70/3.50  ------ AIG Options
% 23.70/3.50  
% 23.70/3.50  --aig_mode                              false
% 23.70/3.50  
% 23.70/3.50  ------ Instantiation Options
% 23.70/3.50  
% 23.70/3.50  --instantiation_flag                    true
% 23.70/3.50  --inst_sos_flag                         false
% 23.70/3.50  --inst_sos_phase                        true
% 23.70/3.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.70/3.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.70/3.50  --inst_lit_sel_side                     num_symb
% 23.70/3.50  --inst_solver_per_active                1400
% 23.70/3.50  --inst_solver_calls_frac                1.
% 23.70/3.50  --inst_passive_queue_type               priority_queues
% 23.70/3.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.70/3.50  --inst_passive_queues_freq              [25;2]
% 23.70/3.50  --inst_dismatching                      true
% 23.70/3.50  --inst_eager_unprocessed_to_passive     true
% 23.70/3.50  --inst_prop_sim_given                   true
% 23.70/3.50  --inst_prop_sim_new                     false
% 23.70/3.50  --inst_subs_new                         false
% 23.70/3.50  --inst_eq_res_simp                      false
% 23.70/3.50  --inst_subs_given                       false
% 23.70/3.50  --inst_orphan_elimination               true
% 23.70/3.50  --inst_learning_loop_flag               true
% 23.70/3.50  --inst_learning_start                   3000
% 23.70/3.50  --inst_learning_factor                  2
% 23.70/3.50  --inst_start_prop_sim_after_learn       3
% 23.70/3.50  --inst_sel_renew                        solver
% 23.70/3.50  --inst_lit_activity_flag                true
% 23.70/3.50  --inst_restr_to_given                   false
% 23.70/3.50  --inst_activity_threshold               500
% 23.70/3.50  --inst_out_proof                        true
% 23.70/3.50  
% 23.70/3.50  ------ Resolution Options
% 23.70/3.50  
% 23.70/3.50  --resolution_flag                       true
% 23.70/3.50  --res_lit_sel                           adaptive
% 23.70/3.50  --res_lit_sel_side                      none
% 23.70/3.50  --res_ordering                          kbo
% 23.70/3.50  --res_to_prop_solver                    active
% 23.70/3.50  --res_prop_simpl_new                    false
% 23.70/3.50  --res_prop_simpl_given                  true
% 23.70/3.50  --res_passive_queue_type                priority_queues
% 23.70/3.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.70/3.50  --res_passive_queues_freq               [15;5]
% 23.70/3.50  --res_forward_subs                      full
% 23.70/3.50  --res_backward_subs                     full
% 23.70/3.50  --res_forward_subs_resolution           true
% 23.70/3.50  --res_backward_subs_resolution          true
% 23.70/3.50  --res_orphan_elimination                true
% 23.70/3.50  --res_time_limit                        2.
% 23.70/3.50  --res_out_proof                         true
% 23.70/3.50  
% 23.70/3.50  ------ Superposition Options
% 23.70/3.50  
% 23.70/3.50  --superposition_flag                    true
% 23.70/3.50  --sup_passive_queue_type                priority_queues
% 23.70/3.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.70/3.50  --sup_passive_queues_freq               [8;1;4]
% 23.70/3.50  --demod_completeness_check              fast
% 23.70/3.50  --demod_use_ground                      true
% 23.70/3.50  --sup_to_prop_solver                    passive
% 23.70/3.50  --sup_prop_simpl_new                    true
% 23.70/3.50  --sup_prop_simpl_given                  true
% 23.70/3.50  --sup_fun_splitting                     false
% 23.70/3.50  --sup_smt_interval                      50000
% 23.70/3.50  
% 23.70/3.50  ------ Superposition Simplification Setup
% 23.70/3.50  
% 23.70/3.50  --sup_indices_passive                   []
% 23.70/3.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.70/3.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.70/3.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.70/3.50  --sup_full_triv                         [TrivRules;PropSubs]
% 23.70/3.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.70/3.50  --sup_full_bw                           [BwDemod]
% 23.70/3.50  --sup_immed_triv                        [TrivRules]
% 23.70/3.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.70/3.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.70/3.50  --sup_immed_bw_main                     []
% 23.70/3.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 23.70/3.50  --sup_input_triv                        [Unflattening;TrivRules]
% 23.70/3.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.70/3.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 23.70/3.50  
% 23.70/3.50  ------ Combination Options
% 23.70/3.50  
% 23.70/3.50  --comb_res_mult                         3
% 23.70/3.50  --comb_sup_mult                         2
% 23.70/3.50  --comb_inst_mult                        10
% 23.70/3.50  
% 23.70/3.50  ------ Debug Options
% 23.70/3.50  
% 23.70/3.50  --dbg_backtrace                         false
% 23.70/3.50  --dbg_dump_prop_clauses                 false
% 23.70/3.50  --dbg_dump_prop_clauses_file            -
% 23.70/3.50  --dbg_out_stat                          false
% 23.70/3.50  ------ Parsing...
% 23.70/3.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.70/3.50  
% 23.70/3.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 23.70/3.50  
% 23.70/3.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.70/3.50  
% 23.70/3.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.70/3.50  ------ Proving...
% 23.70/3.50  ------ Problem Properties 
% 23.70/3.50  
% 23.70/3.50  
% 23.70/3.50  clauses                                 14
% 23.70/3.50  conjectures                             2
% 23.70/3.50  EPR                                     1
% 23.70/3.50  Horn                                    11
% 23.70/3.50  unary                                   5
% 23.70/3.50  binary                                  3
% 23.70/3.50  lits                                    30
% 23.70/3.50  lits eq                                 11
% 23.70/3.50  fd_pure                                 0
% 23.70/3.50  fd_pseudo                               0
% 23.70/3.50  fd_cond                                 0
% 23.70/3.50  fd_pseudo_cond                          5
% 23.70/3.50  AC symbols                              0
% 23.70/3.50  
% 23.70/3.50  ------ Schedule dynamic 5 is on 
% 23.70/3.50  
% 23.70/3.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 23.70/3.50  
% 23.70/3.50  
% 23.70/3.50  ------ 
% 23.70/3.50  Current options:
% 23.70/3.50  ------ 
% 23.70/3.50  
% 23.70/3.50  ------ Input Options
% 23.70/3.50  
% 23.70/3.50  --out_options                           all
% 23.70/3.50  --tptp_safe_out                         true
% 23.70/3.50  --problem_path                          ""
% 23.70/3.50  --include_path                          ""
% 23.70/3.50  --clausifier                            res/vclausify_rel
% 23.70/3.50  --clausifier_options                    --mode clausify
% 23.70/3.50  --stdin                                 false
% 23.70/3.50  --stats_out                             all
% 23.70/3.50  
% 23.70/3.50  ------ General Options
% 23.70/3.50  
% 23.70/3.50  --fof                                   false
% 23.70/3.50  --time_out_real                         305.
% 23.70/3.50  --time_out_virtual                      -1.
% 23.70/3.50  --symbol_type_check                     false
% 23.70/3.50  --clausify_out                          false
% 23.70/3.50  --sig_cnt_out                           false
% 23.70/3.50  --trig_cnt_out                          false
% 23.70/3.50  --trig_cnt_out_tolerance                1.
% 23.70/3.50  --trig_cnt_out_sk_spl                   false
% 23.70/3.50  --abstr_cl_out                          false
% 23.70/3.50  
% 23.70/3.50  ------ Global Options
% 23.70/3.50  
% 23.70/3.50  --schedule                              default
% 23.70/3.50  --add_important_lit                     false
% 23.70/3.50  --prop_solver_per_cl                    1000
% 23.70/3.50  --min_unsat_core                        false
% 23.70/3.50  --soft_assumptions                      false
% 23.70/3.50  --soft_lemma_size                       3
% 23.70/3.50  --prop_impl_unit_size                   0
% 23.70/3.50  --prop_impl_unit                        []
% 23.70/3.50  --share_sel_clauses                     true
% 23.70/3.50  --reset_solvers                         false
% 23.70/3.50  --bc_imp_inh                            [conj_cone]
% 23.70/3.50  --conj_cone_tolerance                   3.
% 23.70/3.50  --extra_neg_conj                        none
% 23.70/3.50  --large_theory_mode                     true
% 23.70/3.50  --prolific_symb_bound                   200
% 23.70/3.50  --lt_threshold                          2000
% 23.70/3.50  --clause_weak_htbl                      true
% 23.70/3.50  --gc_record_bc_elim                     false
% 23.70/3.50  
% 23.70/3.50  ------ Preprocessing Options
% 23.70/3.50  
% 23.70/3.50  --preprocessing_flag                    true
% 23.70/3.50  --time_out_prep_mult                    0.1
% 23.70/3.50  --splitting_mode                        input
% 23.70/3.50  --splitting_grd                         true
% 23.70/3.50  --splitting_cvd                         false
% 23.70/3.50  --splitting_cvd_svl                     false
% 23.70/3.50  --splitting_nvd                         32
% 23.70/3.50  --sub_typing                            true
% 23.70/3.50  --prep_gs_sim                           true
% 23.70/3.50  --prep_unflatten                        true
% 23.70/3.50  --prep_res_sim                          true
% 23.70/3.50  --prep_upred                            true
% 23.70/3.50  --prep_sem_filter                       exhaustive
% 23.70/3.50  --prep_sem_filter_out                   false
% 23.70/3.50  --pred_elim                             true
% 23.70/3.50  --res_sim_input                         true
% 23.70/3.50  --eq_ax_congr_red                       true
% 23.70/3.50  --pure_diseq_elim                       true
% 23.70/3.50  --brand_transform                       false
% 23.70/3.50  --non_eq_to_eq                          false
% 23.70/3.50  --prep_def_merge                        true
% 23.70/3.50  --prep_def_merge_prop_impl              false
% 23.70/3.50  --prep_def_merge_mbd                    true
% 23.70/3.50  --prep_def_merge_tr_red                 false
% 23.70/3.50  --prep_def_merge_tr_cl                  false
% 23.70/3.50  --smt_preprocessing                     true
% 23.70/3.50  --smt_ac_axioms                         fast
% 23.70/3.50  --preprocessed_out                      false
% 23.70/3.50  --preprocessed_stats                    false
% 23.70/3.50  
% 23.70/3.50  ------ Abstraction refinement Options
% 23.70/3.50  
% 23.70/3.50  --abstr_ref                             []
% 23.70/3.50  --abstr_ref_prep                        false
% 23.70/3.50  --abstr_ref_until_sat                   false
% 23.70/3.50  --abstr_ref_sig_restrict                funpre
% 23.70/3.50  --abstr_ref_af_restrict_to_split_sk     false
% 23.70/3.50  --abstr_ref_under                       []
% 23.70/3.50  
% 23.70/3.50  ------ SAT Options
% 23.70/3.50  
% 23.70/3.50  --sat_mode                              false
% 23.70/3.50  --sat_fm_restart_options                ""
% 23.70/3.50  --sat_gr_def                            false
% 23.70/3.50  --sat_epr_types                         true
% 23.70/3.50  --sat_non_cyclic_types                  false
% 23.70/3.50  --sat_finite_models                     false
% 23.70/3.50  --sat_fm_lemmas                         false
% 23.70/3.50  --sat_fm_prep                           false
% 23.70/3.50  --sat_fm_uc_incr                        true
% 23.70/3.50  --sat_out_model                         small
% 23.70/3.50  --sat_out_clauses                       false
% 23.70/3.50  
% 23.70/3.50  ------ QBF Options
% 23.70/3.50  
% 23.70/3.50  --qbf_mode                              false
% 23.70/3.50  --qbf_elim_univ                         false
% 23.70/3.50  --qbf_dom_inst                          none
% 23.70/3.50  --qbf_dom_pre_inst                      false
% 23.70/3.50  --qbf_sk_in                             false
% 23.70/3.50  --qbf_pred_elim                         true
% 23.70/3.50  --qbf_split                             512
% 23.70/3.50  
% 23.70/3.50  ------ BMC1 Options
% 23.70/3.50  
% 23.70/3.50  --bmc1_incremental                      false
% 23.70/3.50  --bmc1_axioms                           reachable_all
% 23.70/3.50  --bmc1_min_bound                        0
% 23.70/3.50  --bmc1_max_bound                        -1
% 23.70/3.50  --bmc1_max_bound_default                -1
% 23.70/3.50  --bmc1_symbol_reachability              true
% 23.70/3.50  --bmc1_property_lemmas                  false
% 23.70/3.50  --bmc1_k_induction                      false
% 23.70/3.50  --bmc1_non_equiv_states                 false
% 23.70/3.50  --bmc1_deadlock                         false
% 23.70/3.50  --bmc1_ucm                              false
% 23.70/3.50  --bmc1_add_unsat_core                   none
% 23.70/3.50  --bmc1_unsat_core_children              false
% 23.70/3.50  --bmc1_unsat_core_extrapolate_axioms    false
% 23.70/3.50  --bmc1_out_stat                         full
% 23.70/3.50  --bmc1_ground_init                      false
% 23.70/3.50  --bmc1_pre_inst_next_state              false
% 23.70/3.50  --bmc1_pre_inst_state                   false
% 23.70/3.50  --bmc1_pre_inst_reach_state             false
% 23.70/3.50  --bmc1_out_unsat_core                   false
% 23.70/3.50  --bmc1_aig_witness_out                  false
% 23.70/3.50  --bmc1_verbose                          false
% 23.70/3.50  --bmc1_dump_clauses_tptp                false
% 23.70/3.50  --bmc1_dump_unsat_core_tptp             false
% 23.70/3.50  --bmc1_dump_file                        -
% 23.70/3.50  --bmc1_ucm_expand_uc_limit              128
% 23.70/3.50  --bmc1_ucm_n_expand_iterations          6
% 23.70/3.50  --bmc1_ucm_extend_mode                  1
% 23.70/3.50  --bmc1_ucm_init_mode                    2
% 23.70/3.50  --bmc1_ucm_cone_mode                    none
% 23.70/3.50  --bmc1_ucm_reduced_relation_type        0
% 23.70/3.50  --bmc1_ucm_relax_model                  4
% 23.70/3.50  --bmc1_ucm_full_tr_after_sat            true
% 23.70/3.50  --bmc1_ucm_expand_neg_assumptions       false
% 23.70/3.50  --bmc1_ucm_layered_model                none
% 23.70/3.50  --bmc1_ucm_max_lemma_size               10
% 23.70/3.50  
% 23.70/3.50  ------ AIG Options
% 23.70/3.50  
% 23.70/3.50  --aig_mode                              false
% 23.70/3.50  
% 23.70/3.50  ------ Instantiation Options
% 23.70/3.50  
% 23.70/3.50  --instantiation_flag                    true
% 23.70/3.50  --inst_sos_flag                         false
% 23.70/3.50  --inst_sos_phase                        true
% 23.70/3.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.70/3.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.70/3.50  --inst_lit_sel_side                     none
% 23.70/3.50  --inst_solver_per_active                1400
% 23.70/3.50  --inst_solver_calls_frac                1.
% 23.70/3.50  --inst_passive_queue_type               priority_queues
% 23.70/3.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.70/3.50  --inst_passive_queues_freq              [25;2]
% 23.70/3.50  --inst_dismatching                      true
% 23.70/3.50  --inst_eager_unprocessed_to_passive     true
% 23.70/3.50  --inst_prop_sim_given                   true
% 23.70/3.50  --inst_prop_sim_new                     false
% 23.70/3.50  --inst_subs_new                         false
% 23.70/3.50  --inst_eq_res_simp                      false
% 23.70/3.50  --inst_subs_given                       false
% 23.70/3.50  --inst_orphan_elimination               true
% 23.70/3.50  --inst_learning_loop_flag               true
% 23.70/3.50  --inst_learning_start                   3000
% 23.70/3.50  --inst_learning_factor                  2
% 23.70/3.50  --inst_start_prop_sim_after_learn       3
% 23.70/3.50  --inst_sel_renew                        solver
% 23.70/3.50  --inst_lit_activity_flag                true
% 23.70/3.50  --inst_restr_to_given                   false
% 23.70/3.50  --inst_activity_threshold               500
% 23.70/3.50  --inst_out_proof                        true
% 23.70/3.50  
% 23.70/3.50  ------ Resolution Options
% 23.70/3.50  
% 23.70/3.50  --resolution_flag                       false
% 23.70/3.50  --res_lit_sel                           adaptive
% 23.70/3.50  --res_lit_sel_side                      none
% 23.70/3.50  --res_ordering                          kbo
% 23.70/3.50  --res_to_prop_solver                    active
% 23.70/3.50  --res_prop_simpl_new                    false
% 23.70/3.50  --res_prop_simpl_given                  true
% 23.70/3.50  --res_passive_queue_type                priority_queues
% 23.70/3.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.70/3.50  --res_passive_queues_freq               [15;5]
% 23.70/3.50  --res_forward_subs                      full
% 23.70/3.50  --res_backward_subs                     full
% 23.70/3.50  --res_forward_subs_resolution           true
% 23.70/3.50  --res_backward_subs_resolution          true
% 23.70/3.50  --res_orphan_elimination                true
% 23.70/3.50  --res_time_limit                        2.
% 23.70/3.50  --res_out_proof                         true
% 23.70/3.50  
% 23.70/3.50  ------ Superposition Options
% 23.70/3.50  
% 23.70/3.50  --superposition_flag                    true
% 23.70/3.50  --sup_passive_queue_type                priority_queues
% 23.70/3.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.70/3.50  --sup_passive_queues_freq               [8;1;4]
% 23.70/3.50  --demod_completeness_check              fast
% 23.70/3.50  --demod_use_ground                      true
% 23.70/3.50  --sup_to_prop_solver                    passive
% 23.70/3.50  --sup_prop_simpl_new                    true
% 23.70/3.50  --sup_prop_simpl_given                  true
% 23.70/3.50  --sup_fun_splitting                     false
% 23.70/3.50  --sup_smt_interval                      50000
% 23.70/3.50  
% 23.70/3.50  ------ Superposition Simplification Setup
% 23.70/3.50  
% 23.70/3.50  --sup_indices_passive                   []
% 23.70/3.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.70/3.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.70/3.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.70/3.50  --sup_full_triv                         [TrivRules;PropSubs]
% 23.70/3.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.70/3.50  --sup_full_bw                           [BwDemod]
% 23.70/3.50  --sup_immed_triv                        [TrivRules]
% 23.70/3.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.70/3.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.70/3.50  --sup_immed_bw_main                     []
% 23.70/3.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 23.70/3.50  --sup_input_triv                        [Unflattening;TrivRules]
% 23.70/3.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.70/3.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 23.70/3.50  
% 23.70/3.50  ------ Combination Options
% 23.70/3.50  
% 23.70/3.50  --comb_res_mult                         3
% 23.70/3.50  --comb_sup_mult                         2
% 23.70/3.50  --comb_inst_mult                        10
% 23.70/3.50  
% 23.70/3.50  ------ Debug Options
% 23.70/3.50  
% 23.70/3.50  --dbg_backtrace                         false
% 23.70/3.50  --dbg_dump_prop_clauses                 false
% 23.70/3.50  --dbg_dump_prop_clauses_file            -
% 23.70/3.50  --dbg_out_stat                          false
% 23.70/3.50  
% 23.70/3.50  
% 23.70/3.50  
% 23.70/3.50  
% 23.70/3.50  ------ Proving...
% 23.70/3.50  
% 23.70/3.50  
% 23.70/3.50  % SZS status Theorem for theBenchmark.p
% 23.70/3.50  
% 23.70/3.50  % SZS output start CNFRefutation for theBenchmark.p
% 23.70/3.50  
% 23.70/3.50  fof(f2,axiom,(
% 23.70/3.50    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 23.70/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.70/3.50  
% 23.70/3.50  fof(f13,plain,(
% 23.70/3.50    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 23.70/3.50    inference(nnf_transformation,[],[f2])).
% 23.70/3.50  
% 23.70/3.50  fof(f14,plain,(
% 23.70/3.50    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 23.70/3.50    inference(flattening,[],[f13])).
% 23.70/3.50  
% 23.70/3.50  fof(f15,plain,(
% 23.70/3.50    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 23.70/3.50    inference(rectify,[],[f14])).
% 23.70/3.50  
% 23.70/3.50  fof(f16,plain,(
% 23.70/3.50    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 23.70/3.50    introduced(choice_axiom,[])).
% 23.70/3.50  
% 23.70/3.50  fof(f17,plain,(
% 23.70/3.50    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 23.70/3.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).
% 23.70/3.50  
% 23.70/3.50  fof(f29,plain,(
% 23.70/3.50    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 23.70/3.50    inference(cnf_transformation,[],[f17])).
% 23.70/3.50  
% 23.70/3.50  fof(f5,axiom,(
% 23.70/3.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 23.70/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.70/3.50  
% 23.70/3.50  fof(f33,plain,(
% 23.70/3.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 23.70/3.50    inference(cnf_transformation,[],[f5])).
% 23.70/3.50  
% 23.70/3.50  fof(f3,axiom,(
% 23.70/3.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 23.70/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.70/3.50  
% 23.70/3.50  fof(f31,plain,(
% 23.70/3.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 23.70/3.50    inference(cnf_transformation,[],[f3])).
% 23.70/3.50  
% 23.70/3.50  fof(f43,plain,(
% 23.70/3.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 23.70/3.50    inference(definition_unfolding,[],[f33,f31])).
% 23.70/3.50  
% 23.70/3.50  fof(f48,plain,(
% 23.70/3.50    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X2 | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 23.70/3.50    inference(definition_unfolding,[],[f29,f43])).
% 23.70/3.50  
% 23.70/3.50  fof(f28,plain,(
% 23.70/3.50    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 23.70/3.50    inference(cnf_transformation,[],[f17])).
% 23.70/3.50  
% 23.70/3.50  fof(f49,plain,(
% 23.70/3.50    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 23.70/3.50    inference(definition_unfolding,[],[f28,f43])).
% 23.70/3.50  
% 23.70/3.50  fof(f6,axiom,(
% 23.70/3.50    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 23.70/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.70/3.50  
% 23.70/3.50  fof(f18,plain,(
% 23.70/3.50    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 23.70/3.50    inference(nnf_transformation,[],[f6])).
% 23.70/3.50  
% 23.70/3.50  fof(f19,plain,(
% 23.70/3.50    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 23.70/3.50    inference(rectify,[],[f18])).
% 23.70/3.50  
% 23.70/3.50  fof(f20,plain,(
% 23.70/3.50    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1))))),
% 23.70/3.50    introduced(choice_axiom,[])).
% 23.70/3.50  
% 23.70/3.50  fof(f21,plain,(
% 23.70/3.50    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 23.70/3.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f20])).
% 23.70/3.50  
% 23.70/3.50  fof(f34,plain,(
% 23.70/3.50    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 23.70/3.50    inference(cnf_transformation,[],[f21])).
% 23.70/3.50  
% 23.70/3.50  fof(f7,axiom,(
% 23.70/3.50    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 23.70/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.70/3.50  
% 23.70/3.50  fof(f38,plain,(
% 23.70/3.50    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 23.70/3.50    inference(cnf_transformation,[],[f7])).
% 23.70/3.50  
% 23.70/3.50  fof(f8,axiom,(
% 23.70/3.50    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 23.70/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.70/3.50  
% 23.70/3.50  fof(f39,plain,(
% 23.70/3.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 23.70/3.50    inference(cnf_transformation,[],[f8])).
% 23.70/3.50  
% 23.70/3.50  fof(f9,axiom,(
% 23.70/3.50    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 23.70/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.70/3.50  
% 23.70/3.50  fof(f40,plain,(
% 23.70/3.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 23.70/3.50    inference(cnf_transformation,[],[f9])).
% 23.70/3.50  
% 23.70/3.50  fof(f44,plain,(
% 23.70/3.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 23.70/3.50    inference(definition_unfolding,[],[f39,f40])).
% 23.70/3.50  
% 23.70/3.50  fof(f45,plain,(
% 23.70/3.50    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 23.70/3.50    inference(definition_unfolding,[],[f38,f44])).
% 23.70/3.50  
% 23.70/3.50  fof(f57,plain,(
% 23.70/3.50    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 23.70/3.50    inference(definition_unfolding,[],[f34,f45])).
% 23.70/3.50  
% 23.70/3.50  fof(f64,plain,(
% 23.70/3.50    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))) )),
% 23.70/3.50    inference(equality_resolution,[],[f57])).
% 23.70/3.50  
% 23.70/3.50  fof(f1,axiom,(
% 23.70/3.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 23.70/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.70/3.50  
% 23.70/3.50  fof(f24,plain,(
% 23.70/3.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 23.70/3.50    inference(cnf_transformation,[],[f1])).
% 23.70/3.50  
% 23.70/3.50  fof(f46,plain,(
% 23.70/3.50    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 23.70/3.50    inference(definition_unfolding,[],[f24,f43,f43])).
% 23.70/3.50  
% 23.70/3.50  fof(f4,axiom,(
% 23.70/3.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 23.70/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.70/3.50  
% 23.70/3.50  fof(f32,plain,(
% 23.70/3.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 23.70/3.50    inference(cnf_transformation,[],[f4])).
% 23.70/3.50  
% 23.70/3.50  fof(f53,plain,(
% 23.70/3.50    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),X0)))) )),
% 23.70/3.50    inference(definition_unfolding,[],[f32,f43,f43,f31])).
% 23.70/3.50  
% 23.70/3.50  fof(f10,conjecture,(
% 23.70/3.50    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 23.70/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.70/3.50  
% 23.70/3.50  fof(f11,negated_conjecture,(
% 23.70/3.50    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 23.70/3.50    inference(negated_conjecture,[],[f10])).
% 23.70/3.50  
% 23.70/3.50  fof(f12,plain,(
% 23.70/3.50    ? [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & r2_hidden(X0,X1))),
% 23.70/3.50    inference(ennf_transformation,[],[f11])).
% 23.70/3.50  
% 23.70/3.50  fof(f22,plain,(
% 23.70/3.50    ? [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & r2_hidden(X0,X1)) => (k2_xboole_0(k4_xboole_0(sK3,k1_tarski(sK2)),k1_tarski(sK2)) != sK3 & r2_hidden(sK2,sK3))),
% 23.70/3.50    introduced(choice_axiom,[])).
% 23.70/3.50  
% 23.70/3.50  fof(f23,plain,(
% 23.70/3.50    k2_xboole_0(k4_xboole_0(sK3,k1_tarski(sK2)),k1_tarski(sK2)) != sK3 & r2_hidden(sK2,sK3)),
% 23.70/3.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f12,f22])).
% 23.70/3.50  
% 23.70/3.50  fof(f42,plain,(
% 23.70/3.50    k2_xboole_0(k4_xboole_0(sK3,k1_tarski(sK2)),k1_tarski(sK2)) != sK3),
% 23.70/3.50    inference(cnf_transformation,[],[f23])).
% 23.70/3.50  
% 23.70/3.50  fof(f58,plain,(
% 23.70/3.50    k5_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k3_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK2,sK2,sK2,sK2)))))) != sK3),
% 23.70/3.50    inference(definition_unfolding,[],[f42,f43,f31,f45,f45])).
% 23.70/3.50  
% 23.70/3.50  fof(f41,plain,(
% 23.70/3.50    r2_hidden(sK2,sK3)),
% 23.70/3.50    inference(cnf_transformation,[],[f23])).
% 23.70/3.50  
% 23.70/3.50  cnf(c_2,plain,
% 23.70/3.50      ( ~ r2_hidden(sK0(X0,X1,X2),X2)
% 23.70/3.50      | ~ r2_hidden(sK0(X0,X1,X2),X0)
% 23.70/3.50      | k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X2 ),
% 23.70/3.50      inference(cnf_transformation,[],[f48]) ).
% 23.70/3.50  
% 23.70/3.50  cnf(c_529,plain,
% 23.70/3.50      ( ~ r2_hidden(sK0(X0,X1,sK3),X0)
% 23.70/3.50      | ~ r2_hidden(sK0(X0,X1,sK3),sK3)
% 23.70/3.50      | k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = sK3 ),
% 23.70/3.50      inference(instantiation,[status(thm)],[c_2]) ).
% 23.70/3.50  
% 23.70/3.50  cnf(c_994,plain,
% 23.70/3.50      ( ~ r2_hidden(sK0(sK3,X0,sK3),sK3)
% 23.70/3.50      | k5_xboole_0(sK3,k5_xboole_0(X0,k3_xboole_0(X0,sK3))) = sK3 ),
% 23.70/3.50      inference(instantiation,[status(thm)],[c_529]) ).
% 23.70/3.50  
% 23.70/3.50  cnf(c_65082,plain,
% 23.70/3.50      ( ~ r2_hidden(sK0(sK3,k2_enumset1(sK2,sK2,sK2,sK2),sK3),sK3)
% 23.70/3.50      | k5_xboole_0(sK3,k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k3_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK3))) = sK3 ),
% 23.70/3.50      inference(instantiation,[status(thm)],[c_994]) ).
% 23.70/3.50  
% 23.70/3.50  cnf(c_135,plain,
% 23.70/3.50      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 23.70/3.50      theory(equality) ).
% 23.70/3.50  
% 23.70/3.50  cnf(c_443,plain,
% 23.70/3.50      ( r2_hidden(X0,X1) | ~ r2_hidden(sK2,sK3) | X0 != sK2 | X1 != sK3 ),
% 23.70/3.50      inference(instantiation,[status(thm)],[c_135]) ).
% 23.70/3.50  
% 23.70/3.50  cnf(c_563,plain,
% 23.70/3.50      ( r2_hidden(X0,sK3)
% 23.70/3.50      | ~ r2_hidden(sK2,sK3)
% 23.70/3.50      | X0 != sK2
% 23.70/3.50      | sK3 != sK3 ),
% 23.70/3.50      inference(instantiation,[status(thm)],[c_443]) ).
% 23.70/3.50  
% 23.70/3.50  cnf(c_4016,plain,
% 23.70/3.50      ( r2_hidden(sK0(X0,X1,sK3),sK3)
% 23.70/3.50      | ~ r2_hidden(sK2,sK3)
% 23.70/3.50      | sK0(X0,X1,sK3) != sK2
% 23.70/3.50      | sK3 != sK3 ),
% 23.70/3.50      inference(instantiation,[status(thm)],[c_563]) ).
% 23.70/3.50  
% 23.70/3.50  cnf(c_24421,plain,
% 23.70/3.50      ( r2_hidden(sK0(sK3,k2_enumset1(sK2,sK2,sK2,sK2),sK3),sK3)
% 23.70/3.50      | ~ r2_hidden(sK2,sK3)
% 23.70/3.50      | sK0(sK3,k2_enumset1(sK2,sK2,sK2,sK2),sK3) != sK2
% 23.70/3.50      | sK3 != sK3 ),
% 23.70/3.50      inference(instantiation,[status(thm)],[c_4016]) ).
% 23.70/3.50  
% 23.70/3.50  cnf(c_3,plain,
% 23.70/3.50      ( r2_hidden(sK0(X0,X1,X2),X1)
% 23.70/3.50      | r2_hidden(sK0(X0,X1,X2),X2)
% 23.70/3.50      | r2_hidden(sK0(X0,X1,X2),X0)
% 23.70/3.50      | k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X2 ),
% 23.70/3.50      inference(cnf_transformation,[],[f49]) ).
% 23.70/3.50  
% 23.70/3.50  cnf(c_528,plain,
% 23.70/3.50      ( r2_hidden(sK0(X0,X1,sK3),X1)
% 23.70/3.50      | r2_hidden(sK0(X0,X1,sK3),X0)
% 23.70/3.50      | r2_hidden(sK0(X0,X1,sK3),sK3)
% 23.70/3.50      | k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = sK3 ),
% 23.70/3.50      inference(instantiation,[status(thm)],[c_3]) ).
% 23.70/3.50  
% 23.70/3.50  cnf(c_992,plain,
% 23.70/3.50      ( r2_hidden(sK0(sK3,X0,sK3),X0)
% 23.70/3.50      | r2_hidden(sK0(sK3,X0,sK3),sK3)
% 23.70/3.50      | k5_xboole_0(sK3,k5_xboole_0(X0,k3_xboole_0(X0,sK3))) = sK3 ),
% 23.70/3.50      inference(instantiation,[status(thm)],[c_528]) ).
% 23.70/3.50  
% 23.70/3.50  cnf(c_14490,plain,
% 23.70/3.50      ( r2_hidden(sK0(sK3,k2_enumset1(sK2,sK2,sK2,sK2),sK3),k2_enumset1(sK2,sK2,sK2,sK2))
% 23.70/3.50      | r2_hidden(sK0(sK3,k2_enumset1(sK2,sK2,sK2,sK2),sK3),sK3)
% 23.70/3.50      | k5_xboole_0(sK3,k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k3_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK3))) = sK3 ),
% 23.70/3.50      inference(instantiation,[status(thm)],[c_992]) ).
% 23.70/3.50  
% 23.70/3.50  cnf(c_11,plain,
% 23.70/3.50      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) | X0 = X1 ),
% 23.70/3.50      inference(cnf_transformation,[],[f64]) ).
% 23.70/3.50  
% 23.70/3.50  cnf(c_7405,plain,
% 23.70/3.50      ( ~ r2_hidden(sK0(sK3,X0,X1),k2_enumset1(sK2,sK2,sK2,sK2))
% 23.70/3.50      | sK0(sK3,X0,X1) = sK2 ),
% 23.70/3.50      inference(instantiation,[status(thm)],[c_11]) ).
% 23.70/3.50  
% 23.70/3.50  cnf(c_14489,plain,
% 23.70/3.50      ( ~ r2_hidden(sK0(sK3,k2_enumset1(sK2,sK2,sK2,sK2),sK3),k2_enumset1(sK2,sK2,sK2,sK2))
% 23.70/3.50      | sK0(sK3,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = sK2 ),
% 23.70/3.50      inference(instantiation,[status(thm)],[c_7405]) ).
% 23.70/3.50  
% 23.70/3.50  cnf(c_0,plain,
% 23.70/3.50      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
% 23.70/3.50      inference(cnf_transformation,[],[f46]) ).
% 23.70/3.50  
% 23.70/3.50  cnf(c_7,plain,
% 23.70/3.50      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),X0))) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
% 23.70/3.50      inference(cnf_transformation,[],[f53]) ).
% 23.70/3.50  
% 23.70/3.50  cnf(c_12,negated_conjecture,
% 23.70/3.50      ( k5_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k3_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK2,sK2,sK2,sK2)))))) != sK3 ),
% 23.70/3.50      inference(cnf_transformation,[],[f58]) ).
% 23.70/3.50  
% 23.70/3.50  cnf(c_570,plain,
% 23.70/3.50      ( k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k5_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k3_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k2_enumset1(sK2,sK2,sK2,sK2)))) != sK3 ),
% 23.70/3.50      inference(demodulation,[status(thm)],[c_0,c_12]) ).
% 23.70/3.50  
% 23.70/3.50  cnf(c_823,plain,
% 23.70/3.50      ( k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK2,sK2,sK2,sK2)))) != sK3 ),
% 23.70/3.50      inference(demodulation,[status(thm)],[c_7,c_570]) ).
% 23.70/3.50  
% 23.70/3.50  cnf(c_861,plain,
% 23.70/3.50      ( k5_xboole_0(sK3,k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k3_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK3))) != sK3 ),
% 23.70/3.50      inference(superposition,[status(thm)],[c_0,c_823]) ).
% 23.70/3.50  
% 23.70/3.50  cnf(c_131,plain,( X0 = X0 ),theory(equality) ).
% 23.70/3.50  
% 23.70/3.50  cnf(c_564,plain,
% 23.70/3.50      ( sK3 = sK3 ),
% 23.70/3.50      inference(instantiation,[status(thm)],[c_131]) ).
% 23.70/3.50  
% 23.70/3.50  cnf(c_13,negated_conjecture,
% 23.70/3.50      ( r2_hidden(sK2,sK3) ),
% 23.70/3.50      inference(cnf_transformation,[],[f41]) ).
% 23.70/3.50  
% 23.70/3.50  cnf(contradiction,plain,
% 23.70/3.50      ( $false ),
% 23.70/3.50      inference(minisat,
% 23.70/3.50                [status(thm)],
% 23.70/3.50                [c_65082,c_24421,c_14490,c_14489,c_861,c_564,c_13]) ).
% 23.70/3.50  
% 23.70/3.50  
% 23.70/3.50  % SZS output end CNFRefutation for theBenchmark.p
% 23.70/3.50  
% 23.70/3.50  ------                               Statistics
% 23.70/3.50  
% 23.70/3.50  ------ General
% 23.70/3.50  
% 23.70/3.50  abstr_ref_over_cycles:                  0
% 23.70/3.50  abstr_ref_under_cycles:                 0
% 23.70/3.50  gc_basic_clause_elim:                   0
% 23.70/3.50  forced_gc_time:                         0
% 23.70/3.50  parsing_time:                           0.01
% 23.70/3.50  unif_index_cands_time:                  0.
% 23.70/3.50  unif_index_add_time:                    0.
% 23.70/3.50  orderings_time:                         0.
% 23.70/3.50  out_proof_time:                         0.009
% 23.70/3.50  total_time:                             2.987
% 23.70/3.50  num_of_symbols:                         39
% 23.70/3.50  num_of_terms:                           55417
% 23.70/3.50  
% 23.70/3.50  ------ Preprocessing
% 23.70/3.50  
% 23.70/3.50  num_of_splits:                          0
% 23.70/3.50  num_of_split_atoms:                     0
% 23.70/3.50  num_of_reused_defs:                     0
% 23.70/3.50  num_eq_ax_congr_red:                    10
% 23.70/3.50  num_of_sem_filtered_clauses:            1
% 23.70/3.50  num_of_subtypes:                        0
% 23.70/3.50  monotx_restored_types:                  0
% 23.70/3.50  sat_num_of_epr_types:                   0
% 23.70/3.50  sat_num_of_non_cyclic_types:            0
% 23.70/3.50  sat_guarded_non_collapsed_types:        0
% 23.70/3.50  num_pure_diseq_elim:                    0
% 23.70/3.50  simp_replaced_by:                       0
% 23.70/3.50  res_preprocessed:                       55
% 23.70/3.50  prep_upred:                             0
% 23.70/3.50  prep_unflattend:                        0
% 23.70/3.50  smt_new_axioms:                         0
% 23.70/3.50  pred_elim_cands:                        1
% 23.70/3.50  pred_elim:                              0
% 23.70/3.50  pred_elim_cl:                           0
% 23.70/3.50  pred_elim_cycles:                       1
% 23.70/3.50  merged_defs:                            0
% 23.70/3.50  merged_defs_ncl:                        0
% 23.70/3.50  bin_hyper_res:                          0
% 23.70/3.50  prep_cycles:                            3
% 23.70/3.50  pred_elim_time:                         0.
% 23.70/3.50  splitting_time:                         0.
% 23.70/3.50  sem_filter_time:                        0.
% 23.70/3.50  monotx_time:                            0.
% 23.70/3.50  subtype_inf_time:                       0.
% 23.70/3.50  
% 23.70/3.50  ------ Problem properties
% 23.70/3.50  
% 23.70/3.50  clauses:                                14
% 23.70/3.50  conjectures:                            2
% 23.70/3.50  epr:                                    1
% 23.70/3.50  horn:                                   11
% 23.70/3.50  ground:                                 2
% 23.70/3.50  unary:                                  5
% 23.70/3.50  binary:                                 3
% 23.70/3.50  lits:                                   30
% 23.70/3.50  lits_eq:                                11
% 23.70/3.50  fd_pure:                                0
% 23.70/3.50  fd_pseudo:                              0
% 23.70/3.50  fd_cond:                                0
% 23.70/3.50  fd_pseudo_cond:                         5
% 23.70/3.50  ac_symbols:                             0
% 23.70/3.50  
% 23.70/3.50  ------ Propositional Solver
% 23.70/3.50  
% 23.70/3.50  prop_solver_calls:                      27
% 23.70/3.50  prop_fast_solver_calls:                 2619
% 23.70/3.50  smt_solver_calls:                       0
% 23.70/3.50  smt_fast_solver_calls:                  0
% 23.70/3.50  prop_num_of_clauses:                    18308
% 23.70/3.50  prop_preprocess_simplified:             30960
% 23.70/3.50  prop_fo_subsumed:                       2
% 23.70/3.50  prop_solver_time:                       0.
% 23.70/3.50  smt_solver_time:                        0.
% 23.70/3.50  smt_fast_solver_time:                   0.
% 23.70/3.50  prop_fast_solver_time:                  0.
% 23.70/3.50  prop_unsat_core_time:                   0.001
% 23.70/3.50  
% 23.70/3.50  ------ QBF
% 23.70/3.50  
% 23.70/3.50  qbf_q_res:                              0
% 23.70/3.50  qbf_num_tautologies:                    0
% 23.70/3.50  qbf_prep_cycles:                        0
% 23.70/3.50  
% 23.70/3.50  ------ BMC1
% 23.70/3.50  
% 23.70/3.50  bmc1_current_bound:                     -1
% 23.70/3.50  bmc1_last_solved_bound:                 -1
% 23.70/3.50  bmc1_unsat_core_size:                   -1
% 23.70/3.50  bmc1_unsat_core_parents_size:           -1
% 23.70/3.50  bmc1_merge_next_fun:                    0
% 23.70/3.50  bmc1_unsat_core_clauses_time:           0.
% 23.70/3.50  
% 23.70/3.50  ------ Instantiation
% 23.70/3.50  
% 23.70/3.50  inst_num_of_clauses:                    4592
% 23.70/3.50  inst_num_in_passive:                    1831
% 23.70/3.50  inst_num_in_active:                     1270
% 23.70/3.50  inst_num_in_unprocessed:                1491
% 23.70/3.50  inst_num_of_loops:                      1641
% 23.70/3.50  inst_num_of_learning_restarts:          0
% 23.70/3.50  inst_num_moves_active_passive:          369
% 23.70/3.50  inst_lit_activity:                      0
% 23.70/3.50  inst_lit_activity_moves:                1
% 23.70/3.50  inst_num_tautologies:                   0
% 23.70/3.50  inst_num_prop_implied:                  0
% 23.70/3.50  inst_num_existing_simplified:           0
% 23.70/3.50  inst_num_eq_res_simplified:             0
% 23.70/3.50  inst_num_child_elim:                    0
% 23.70/3.50  inst_num_of_dismatching_blockings:      6824
% 23.70/3.50  inst_num_of_non_proper_insts:           5176
% 23.70/3.50  inst_num_of_duplicates:                 0
% 23.70/3.50  inst_inst_num_from_inst_to_res:         0
% 23.70/3.50  inst_dismatching_checking_time:         0.
% 23.70/3.50  
% 23.70/3.50  ------ Resolution
% 23.70/3.50  
% 23.70/3.50  res_num_of_clauses:                     0
% 23.70/3.50  res_num_in_passive:                     0
% 23.70/3.50  res_num_in_active:                      0
% 23.70/3.50  res_num_of_loops:                       58
% 23.70/3.50  res_forward_subset_subsumed:            480
% 23.70/3.50  res_backward_subset_subsumed:           26
% 23.70/3.50  res_forward_subsumed:                   0
% 23.70/3.50  res_backward_subsumed:                  0
% 23.70/3.50  res_forward_subsumption_resolution:     0
% 23.70/3.50  res_backward_subsumption_resolution:    0
% 23.70/3.50  res_clause_to_clause_subsumption:       81059
% 23.70/3.50  res_orphan_elimination:                 0
% 23.70/3.50  res_tautology_del:                      165
% 23.70/3.50  res_num_eq_res_simplified:              0
% 23.70/3.50  res_num_sel_changes:                    0
% 23.70/3.50  res_moves_from_active_to_pass:          0
% 23.70/3.50  
% 23.70/3.50  ------ Superposition
% 23.70/3.50  
% 23.70/3.50  sup_time_total:                         0.
% 23.70/3.50  sup_time_generating:                    0.
% 23.70/3.50  sup_time_sim_full:                      0.
% 23.70/3.50  sup_time_sim_immed:                     0.
% 23.70/3.50  
% 23.70/3.50  sup_num_of_clauses:                     1491
% 23.70/3.50  sup_num_in_active:                      326
% 23.70/3.50  sup_num_in_passive:                     1165
% 23.70/3.50  sup_num_of_loops:                       328
% 23.70/3.50  sup_fw_superposition:                   1919
% 23.70/3.50  sup_bw_superposition:                   1053
% 23.70/3.50  sup_immediate_simplified:               548
% 23.70/3.50  sup_given_eliminated:                   0
% 23.70/3.50  comparisons_done:                       0
% 23.70/3.50  comparisons_avoided:                    46
% 23.70/3.50  
% 23.70/3.50  ------ Simplifications
% 23.70/3.50  
% 23.70/3.50  
% 23.70/3.50  sim_fw_subset_subsumed:                 57
% 23.70/3.50  sim_bw_subset_subsumed:                 10
% 23.70/3.50  sim_fw_subsumed:                        307
% 23.70/3.50  sim_bw_subsumed:                        23
% 23.70/3.50  sim_fw_subsumption_res:                 49
% 23.70/3.50  sim_bw_subsumption_res:                 0
% 23.70/3.50  sim_tautology_del:                      104
% 23.70/3.50  sim_eq_tautology_del:                   1
% 23.70/3.50  sim_eq_res_simp:                        35
% 23.70/3.50  sim_fw_demodulated:                     113
% 23.70/3.50  sim_bw_demodulated:                     2
% 23.70/3.50  sim_light_normalised:                   50
% 23.70/3.50  sim_joinable_taut:                      0
% 23.70/3.50  sim_joinable_simp:                      0
% 23.70/3.50  sim_ac_normalised:                      0
% 23.70/3.50  sim_smt_subsumption:                    0
% 23.70/3.50  
%------------------------------------------------------------------------------
