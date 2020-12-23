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
% DateTime   : Thu Dec  3 11:35:08 EST 2020

% Result     : Theorem 0.52s
% Output     : CNFRefutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 112 expanded)
%              Number of clauses        :   19 (  20 expanded)
%              Number of leaves         :   11 (  30 expanded)
%              Depth                    :   10
%              Number of atoms          :  192 ( 390 expanded)
%              Number of equality atoms :   35 (  91 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f26,plain,(
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
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).

fof(f36,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f68,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f36])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f57,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f52,f53])).

fof(f58,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f51,f57])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f54,f58])).

fof(f5,axiom,(
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

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f30])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
      | r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k3_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
        | r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f23,plain,(
    ? [X0,X1] :
      ( k3_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0)
      & ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f32,plain,
    ( ? [X0,X1] :
        ( k3_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0)
        & ~ r1_xboole_0(k1_tarski(X0),X1) )
   => ( k3_xboole_0(k1_tarski(sK2),sK3) != k1_tarski(sK2)
      & ~ r1_xboole_0(k1_tarski(sK2),sK3) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( k3_xboole_0(k1_tarski(sK2),sK3) != k1_tarski(sK2)
    & ~ r1_xboole_0(k1_tarski(sK2),sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f23,f32])).

fof(f56,plain,(
    k3_xboole_0(k1_tarski(sK2),sK3) != k1_tarski(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f65,plain,(
    k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != k2_enumset1(sK2,sK2,sK2,sK2) ),
    inference(definition_unfolding,[],[f56,f50,f58,f58])).

fof(f55,plain,(
    ~ r1_xboole_0(k1_tarski(sK2),sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f66,plain,(
    ~ r1_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK3) ),
    inference(definition_unfolding,[],[f55,f58])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_6984,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK3))
    | ~ r2_hidden(X0,sK3) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_6986,plain,
    ( ~ r2_hidden(sK2,k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK3))
    | ~ r2_hidden(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_6984])).

cnf(c_16,plain,
    ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
    | r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1753,plain,
    ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),k4_xboole_0(X1,X2))
    | r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_4399,plain,
    ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK3))
    | r2_hidden(X0,k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK3)) ),
    inference(instantiation,[status(thm)],[c_1753])).

cnf(c_4401,plain,
    ( r1_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK3))
    | r2_hidden(sK2,k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK3)) ),
    inference(instantiation,[status(thm)],[c_4399])).

cnf(c_10,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_878,plain,
    ( ~ r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,k2_enumset1(X0,X0,X0,X0)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1260,plain,
    ( ~ r1_xboole_0(k2_enumset1(X0,X0,X0,X0),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK3))
    | ~ r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK2),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK3),k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(X0,X0,X0,X0))
    | ~ r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK2),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK3),k2_enumset1(sK2,sK2,sK2,sK2)),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK3)) ),
    inference(instantiation,[status(thm)],[c_878])).

cnf(c_1262,plain,
    ( ~ r1_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK3))
    | ~ r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK2),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK3),k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK2,sK2,sK2,sK2))
    | ~ r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK2),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK3),k2_enumset1(sK2,sK2,sK2,sK2)),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK3)) ),
    inference(instantiation,[status(thm)],[c_1260])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X0)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(sK0(X0,X1,X2),X1)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_946,plain,
    ( ~ r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK2),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK3),k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK2,sK2,sK2,sK2))
    | r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK2),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK3),k2_enumset1(sK2,sK2,sK2,sK2)),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK3))
    | k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK3)) = k2_enumset1(sK2,sK2,sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_935,plain,
    ( r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK2),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK3),k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK2,sK2,sK2,sK2))
    | k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK3)) = k2_enumset1(sK2,sK2,sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_893,plain,
    ( r1_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK3)
    | r2_hidden(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_17,negated_conjecture,
    ( k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != k2_enumset1(sK2,sK2,sK2,sK2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_18,negated_conjecture,
    ( ~ r1_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK3) ),
    inference(cnf_transformation,[],[f66])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6986,c_4401,c_1262,c_946,c_935,c_893,c_17,c_18])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:27:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 0.52/1.05  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.52/1.05  
% 0.52/1.05  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.52/1.05  
% 0.52/1.05  ------  iProver source info
% 0.52/1.05  
% 0.52/1.05  git: date: 2020-06-30 10:37:57 +0100
% 0.52/1.05  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.52/1.05  git: non_committed_changes: false
% 0.52/1.05  git: last_make_outside_of_git: false
% 0.52/1.05  
% 0.52/1.05  ------ 
% 0.52/1.05  
% 0.52/1.05  ------ Input Options
% 0.52/1.05  
% 0.52/1.05  --out_options                           all
% 0.52/1.05  --tptp_safe_out                         true
% 0.52/1.05  --problem_path                          ""
% 0.52/1.05  --include_path                          ""
% 0.52/1.05  --clausifier                            res/vclausify_rel
% 0.52/1.05  --clausifier_options                    --mode clausify
% 0.52/1.05  --stdin                                 false
% 0.52/1.05  --stats_out                             all
% 0.52/1.05  
% 0.52/1.05  ------ General Options
% 0.52/1.05  
% 0.52/1.05  --fof                                   false
% 0.52/1.05  --time_out_real                         305.
% 0.52/1.05  --time_out_virtual                      -1.
% 0.52/1.05  --symbol_type_check                     false
% 0.52/1.05  --clausify_out                          false
% 0.52/1.05  --sig_cnt_out                           false
% 0.52/1.05  --trig_cnt_out                          false
% 0.52/1.05  --trig_cnt_out_tolerance                1.
% 0.52/1.05  --trig_cnt_out_sk_spl                   false
% 0.52/1.05  --abstr_cl_out                          false
% 0.52/1.05  
% 0.52/1.05  ------ Global Options
% 0.52/1.05  
% 0.52/1.05  --schedule                              default
% 0.52/1.05  --add_important_lit                     false
% 0.52/1.05  --prop_solver_per_cl                    1000
% 0.52/1.05  --min_unsat_core                        false
% 0.52/1.05  --soft_assumptions                      false
% 0.52/1.05  --soft_lemma_size                       3
% 0.52/1.05  --prop_impl_unit_size                   0
% 0.52/1.05  --prop_impl_unit                        []
% 0.52/1.05  --share_sel_clauses                     true
% 0.52/1.05  --reset_solvers                         false
% 0.52/1.05  --bc_imp_inh                            [conj_cone]
% 0.52/1.05  --conj_cone_tolerance                   3.
% 0.52/1.05  --extra_neg_conj                        none
% 0.52/1.05  --large_theory_mode                     true
% 0.52/1.05  --prolific_symb_bound                   200
% 0.52/1.05  --lt_threshold                          2000
% 0.52/1.05  --clause_weak_htbl                      true
% 0.52/1.05  --gc_record_bc_elim                     false
% 0.52/1.05  
% 0.52/1.05  ------ Preprocessing Options
% 0.52/1.05  
% 0.52/1.05  --preprocessing_flag                    true
% 0.52/1.05  --time_out_prep_mult                    0.1
% 0.52/1.05  --splitting_mode                        input
% 0.52/1.05  --splitting_grd                         true
% 0.52/1.05  --splitting_cvd                         false
% 0.52/1.05  --splitting_cvd_svl                     false
% 0.52/1.05  --splitting_nvd                         32
% 0.52/1.05  --sub_typing                            true
% 0.52/1.05  --prep_gs_sim                           true
% 0.52/1.05  --prep_unflatten                        true
% 0.52/1.05  --prep_res_sim                          true
% 0.52/1.05  --prep_upred                            true
% 0.52/1.05  --prep_sem_filter                       exhaustive
% 0.52/1.05  --prep_sem_filter_out                   false
% 0.52/1.05  --pred_elim                             true
% 0.52/1.05  --res_sim_input                         true
% 0.52/1.05  --eq_ax_congr_red                       true
% 0.52/1.05  --pure_diseq_elim                       true
% 0.52/1.05  --brand_transform                       false
% 0.52/1.05  --non_eq_to_eq                          false
% 0.52/1.05  --prep_def_merge                        true
% 0.52/1.05  --prep_def_merge_prop_impl              false
% 0.52/1.05  --prep_def_merge_mbd                    true
% 0.52/1.05  --prep_def_merge_tr_red                 false
% 0.52/1.05  --prep_def_merge_tr_cl                  false
% 0.52/1.05  --smt_preprocessing                     true
% 0.52/1.05  --smt_ac_axioms                         fast
% 0.52/1.05  --preprocessed_out                      false
% 0.52/1.05  --preprocessed_stats                    false
% 0.52/1.05  
% 0.52/1.05  ------ Abstraction refinement Options
% 0.52/1.05  
% 0.52/1.05  --abstr_ref                             []
% 0.52/1.05  --abstr_ref_prep                        false
% 0.52/1.05  --abstr_ref_until_sat                   false
% 0.52/1.05  --abstr_ref_sig_restrict                funpre
% 0.52/1.05  --abstr_ref_af_restrict_to_split_sk     false
% 0.52/1.05  --abstr_ref_under                       []
% 0.52/1.05  
% 0.52/1.05  ------ SAT Options
% 0.52/1.05  
% 0.52/1.05  --sat_mode                              false
% 0.52/1.05  --sat_fm_restart_options                ""
% 0.52/1.05  --sat_gr_def                            false
% 0.52/1.05  --sat_epr_types                         true
% 0.52/1.05  --sat_non_cyclic_types                  false
% 0.52/1.05  --sat_finite_models                     false
% 0.52/1.05  --sat_fm_lemmas                         false
% 0.52/1.05  --sat_fm_prep                           false
% 0.52/1.05  --sat_fm_uc_incr                        true
% 0.52/1.05  --sat_out_model                         small
% 0.52/1.05  --sat_out_clauses                       false
% 0.52/1.05  
% 0.52/1.05  ------ QBF Options
% 0.52/1.05  
% 0.52/1.05  --qbf_mode                              false
% 0.52/1.05  --qbf_elim_univ                         false
% 0.52/1.05  --qbf_dom_inst                          none
% 0.52/1.05  --qbf_dom_pre_inst                      false
% 0.52/1.05  --qbf_sk_in                             false
% 0.52/1.05  --qbf_pred_elim                         true
% 0.52/1.05  --qbf_split                             512
% 0.52/1.05  
% 0.52/1.05  ------ BMC1 Options
% 0.52/1.05  
% 0.52/1.05  --bmc1_incremental                      false
% 0.52/1.05  --bmc1_axioms                           reachable_all
% 0.52/1.05  --bmc1_min_bound                        0
% 0.52/1.05  --bmc1_max_bound                        -1
% 0.52/1.05  --bmc1_max_bound_default                -1
% 0.52/1.05  --bmc1_symbol_reachability              true
% 0.52/1.05  --bmc1_property_lemmas                  false
% 0.52/1.05  --bmc1_k_induction                      false
% 0.52/1.05  --bmc1_non_equiv_states                 false
% 0.52/1.05  --bmc1_deadlock                         false
% 0.52/1.05  --bmc1_ucm                              false
% 0.52/1.05  --bmc1_add_unsat_core                   none
% 0.52/1.05  --bmc1_unsat_core_children              false
% 0.52/1.05  --bmc1_unsat_core_extrapolate_axioms    false
% 0.52/1.05  --bmc1_out_stat                         full
% 0.52/1.05  --bmc1_ground_init                      false
% 0.52/1.05  --bmc1_pre_inst_next_state              false
% 0.52/1.05  --bmc1_pre_inst_state                   false
% 0.52/1.05  --bmc1_pre_inst_reach_state             false
% 0.52/1.05  --bmc1_out_unsat_core                   false
% 0.52/1.05  --bmc1_aig_witness_out                  false
% 0.52/1.05  --bmc1_verbose                          false
% 0.52/1.05  --bmc1_dump_clauses_tptp                false
% 0.52/1.05  --bmc1_dump_unsat_core_tptp             false
% 0.52/1.05  --bmc1_dump_file                        -
% 0.52/1.05  --bmc1_ucm_expand_uc_limit              128
% 0.52/1.05  --bmc1_ucm_n_expand_iterations          6
% 0.52/1.05  --bmc1_ucm_extend_mode                  1
% 0.52/1.05  --bmc1_ucm_init_mode                    2
% 0.52/1.05  --bmc1_ucm_cone_mode                    none
% 0.52/1.05  --bmc1_ucm_reduced_relation_type        0
% 0.52/1.05  --bmc1_ucm_relax_model                  4
% 0.52/1.05  --bmc1_ucm_full_tr_after_sat            true
% 0.52/1.05  --bmc1_ucm_expand_neg_assumptions       false
% 0.52/1.05  --bmc1_ucm_layered_model                none
% 0.52/1.05  --bmc1_ucm_max_lemma_size               10
% 0.52/1.05  
% 0.52/1.05  ------ AIG Options
% 0.52/1.05  
% 0.52/1.05  --aig_mode                              false
% 0.52/1.05  
% 0.52/1.05  ------ Instantiation Options
% 0.52/1.05  
% 0.52/1.05  --instantiation_flag                    true
% 0.52/1.05  --inst_sos_flag                         false
% 0.52/1.05  --inst_sos_phase                        true
% 0.52/1.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.52/1.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.52/1.05  --inst_lit_sel_side                     num_symb
% 0.52/1.05  --inst_solver_per_active                1400
% 0.52/1.05  --inst_solver_calls_frac                1.
% 0.52/1.05  --inst_passive_queue_type               priority_queues
% 0.52/1.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.52/1.05  --inst_passive_queues_freq              [25;2]
% 0.52/1.05  --inst_dismatching                      true
% 0.52/1.05  --inst_eager_unprocessed_to_passive     true
% 0.52/1.05  --inst_prop_sim_given                   true
% 0.52/1.05  --inst_prop_sim_new                     false
% 0.52/1.05  --inst_subs_new                         false
% 0.52/1.05  --inst_eq_res_simp                      false
% 0.52/1.05  --inst_subs_given                       false
% 0.52/1.05  --inst_orphan_elimination               true
% 0.52/1.05  --inst_learning_loop_flag               true
% 0.52/1.05  --inst_learning_start                   3000
% 0.52/1.05  --inst_learning_factor                  2
% 0.52/1.05  --inst_start_prop_sim_after_learn       3
% 0.52/1.05  --inst_sel_renew                        solver
% 0.52/1.05  --inst_lit_activity_flag                true
% 0.52/1.05  --inst_restr_to_given                   false
% 0.52/1.05  --inst_activity_threshold               500
% 0.52/1.05  --inst_out_proof                        true
% 0.52/1.05  
% 0.52/1.05  ------ Resolution Options
% 0.52/1.05  
% 0.52/1.05  --resolution_flag                       true
% 0.52/1.05  --res_lit_sel                           adaptive
% 0.52/1.05  --res_lit_sel_side                      none
% 0.52/1.05  --res_ordering                          kbo
% 0.52/1.05  --res_to_prop_solver                    active
% 0.52/1.05  --res_prop_simpl_new                    false
% 0.52/1.05  --res_prop_simpl_given                  true
% 0.52/1.05  --res_passive_queue_type                priority_queues
% 0.52/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.52/1.05  --res_passive_queues_freq               [15;5]
% 0.52/1.05  --res_forward_subs                      full
% 0.52/1.05  --res_backward_subs                     full
% 0.52/1.05  --res_forward_subs_resolution           true
% 0.52/1.05  --res_backward_subs_resolution          true
% 0.52/1.05  --res_orphan_elimination                true
% 0.52/1.05  --res_time_limit                        2.
% 0.52/1.05  --res_out_proof                         true
% 0.52/1.05  
% 0.52/1.05  ------ Superposition Options
% 0.52/1.05  
% 0.52/1.05  --superposition_flag                    true
% 0.52/1.05  --sup_passive_queue_type                priority_queues
% 0.52/1.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.52/1.05  --sup_passive_queues_freq               [8;1;4]
% 0.52/1.05  --demod_completeness_check              fast
% 0.52/1.05  --demod_use_ground                      true
% 0.52/1.05  --sup_to_prop_solver                    passive
% 0.52/1.05  --sup_prop_simpl_new                    true
% 0.52/1.05  --sup_prop_simpl_given                  true
% 0.52/1.05  --sup_fun_splitting                     false
% 0.52/1.05  --sup_smt_interval                      50000
% 0.52/1.05  
% 0.52/1.05  ------ Superposition Simplification Setup
% 0.52/1.05  
% 0.52/1.05  --sup_indices_passive                   []
% 0.52/1.05  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.52/1.05  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.52/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.52/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 0.52/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.52/1.05  --sup_full_bw                           [BwDemod]
% 0.52/1.05  --sup_immed_triv                        [TrivRules]
% 0.52/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.52/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.52/1.05  --sup_immed_bw_main                     []
% 0.52/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.52/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 0.52/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.52/1.05  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.52/1.05  
% 0.52/1.05  ------ Combination Options
% 0.52/1.05  
% 0.52/1.05  --comb_res_mult                         3
% 0.52/1.05  --comb_sup_mult                         2
% 0.52/1.05  --comb_inst_mult                        10
% 0.52/1.05  
% 0.52/1.05  ------ Debug Options
% 0.52/1.05  
% 0.52/1.05  --dbg_backtrace                         false
% 0.52/1.05  --dbg_dump_prop_clauses                 false
% 0.52/1.05  --dbg_dump_prop_clauses_file            -
% 0.52/1.05  --dbg_out_stat                          false
% 0.52/1.05  ------ Parsing...
% 0.52/1.05  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.52/1.05  
% 0.52/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 0.52/1.05  
% 0.52/1.05  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.52/1.05  
% 0.52/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.52/1.05  ------ Proving...
% 0.52/1.05  ------ Problem Properties 
% 0.52/1.05  
% 0.52/1.05  
% 0.52/1.05  clauses                                 18
% 0.52/1.05  conjectures                             2
% 0.52/1.05  EPR                                     2
% 0.52/1.05  Horn                                    11
% 0.52/1.05  unary                                   4
% 0.52/1.05  binary                                  9
% 0.52/1.05  lits                                    38
% 0.52/1.05  lits eq                                 10
% 0.52/1.05  fd_pure                                 0
% 0.52/1.05  fd_pseudo                               0
% 0.52/1.05  fd_cond                                 0
% 0.52/1.05  fd_pseudo_cond                          3
% 0.52/1.05  AC symbols                              0
% 0.52/1.05  
% 0.52/1.05  ------ Schedule dynamic 5 is on 
% 0.52/1.05  
% 0.52/1.05  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.52/1.05  
% 0.52/1.05  
% 0.52/1.05  ------ 
% 0.52/1.05  Current options:
% 0.52/1.05  ------ 
% 0.52/1.05  
% 0.52/1.05  ------ Input Options
% 0.52/1.05  
% 0.52/1.05  --out_options                           all
% 0.52/1.05  --tptp_safe_out                         true
% 0.52/1.05  --problem_path                          ""
% 0.52/1.05  --include_path                          ""
% 0.52/1.05  --clausifier                            res/vclausify_rel
% 0.52/1.05  --clausifier_options                    --mode clausify
% 0.52/1.05  --stdin                                 false
% 0.52/1.05  --stats_out                             all
% 0.52/1.05  
% 0.52/1.05  ------ General Options
% 0.52/1.05  
% 0.52/1.05  --fof                                   false
% 0.52/1.05  --time_out_real                         305.
% 0.52/1.05  --time_out_virtual                      -1.
% 0.52/1.05  --symbol_type_check                     false
% 0.52/1.05  --clausify_out                          false
% 0.52/1.05  --sig_cnt_out                           false
% 0.52/1.05  --trig_cnt_out                          false
% 0.52/1.05  --trig_cnt_out_tolerance                1.
% 0.52/1.05  --trig_cnt_out_sk_spl                   false
% 0.52/1.05  --abstr_cl_out                          false
% 0.52/1.05  
% 0.52/1.05  ------ Global Options
% 0.52/1.05  
% 0.52/1.05  --schedule                              default
% 0.52/1.05  --add_important_lit                     false
% 0.52/1.05  --prop_solver_per_cl                    1000
% 0.52/1.05  --min_unsat_core                        false
% 0.52/1.05  --soft_assumptions                      false
% 0.52/1.05  --soft_lemma_size                       3
% 0.52/1.05  --prop_impl_unit_size                   0
% 0.52/1.05  --prop_impl_unit                        []
% 0.52/1.05  --share_sel_clauses                     true
% 0.52/1.05  --reset_solvers                         false
% 0.52/1.05  --bc_imp_inh                            [conj_cone]
% 0.52/1.05  --conj_cone_tolerance                   3.
% 0.52/1.05  --extra_neg_conj                        none
% 0.52/1.05  --large_theory_mode                     true
% 0.52/1.05  --prolific_symb_bound                   200
% 0.52/1.05  --lt_threshold                          2000
% 0.52/1.05  --clause_weak_htbl                      true
% 0.52/1.05  --gc_record_bc_elim                     false
% 0.52/1.05  
% 0.52/1.05  ------ Preprocessing Options
% 0.52/1.05  
% 0.52/1.05  --preprocessing_flag                    true
% 0.52/1.05  --time_out_prep_mult                    0.1
% 0.52/1.05  --splitting_mode                        input
% 0.52/1.05  --splitting_grd                         true
% 0.52/1.05  --splitting_cvd                         false
% 0.52/1.05  --splitting_cvd_svl                     false
% 0.52/1.05  --splitting_nvd                         32
% 0.52/1.05  --sub_typing                            true
% 0.52/1.05  --prep_gs_sim                           true
% 0.52/1.05  --prep_unflatten                        true
% 0.52/1.05  --prep_res_sim                          true
% 0.52/1.05  --prep_upred                            true
% 0.52/1.05  --prep_sem_filter                       exhaustive
% 0.52/1.05  --prep_sem_filter_out                   false
% 0.52/1.05  --pred_elim                             true
% 0.52/1.05  --res_sim_input                         true
% 0.52/1.05  --eq_ax_congr_red                       true
% 0.52/1.05  --pure_diseq_elim                       true
% 0.52/1.05  --brand_transform                       false
% 0.52/1.05  --non_eq_to_eq                          false
% 0.52/1.05  --prep_def_merge                        true
% 0.52/1.05  --prep_def_merge_prop_impl              false
% 0.52/1.05  --prep_def_merge_mbd                    true
% 0.52/1.05  --prep_def_merge_tr_red                 false
% 0.52/1.05  --prep_def_merge_tr_cl                  false
% 0.52/1.05  --smt_preprocessing                     true
% 0.52/1.05  --smt_ac_axioms                         fast
% 0.52/1.05  --preprocessed_out                      false
% 0.52/1.05  --preprocessed_stats                    false
% 0.52/1.05  
% 0.52/1.05  ------ Abstraction refinement Options
% 0.52/1.05  
% 0.52/1.05  --abstr_ref                             []
% 0.52/1.05  --abstr_ref_prep                        false
% 0.52/1.05  --abstr_ref_until_sat                   false
% 0.52/1.05  --abstr_ref_sig_restrict                funpre
% 0.52/1.05  --abstr_ref_af_restrict_to_split_sk     false
% 0.52/1.05  --abstr_ref_under                       []
% 0.52/1.05  
% 0.52/1.05  ------ SAT Options
% 0.52/1.05  
% 0.52/1.05  --sat_mode                              false
% 0.52/1.05  --sat_fm_restart_options                ""
% 0.52/1.06  --sat_gr_def                            false
% 0.52/1.06  --sat_epr_types                         true
% 0.52/1.06  --sat_non_cyclic_types                  false
% 0.52/1.06  --sat_finite_models                     false
% 0.52/1.06  --sat_fm_lemmas                         false
% 0.52/1.06  --sat_fm_prep                           false
% 0.52/1.06  --sat_fm_uc_incr                        true
% 0.52/1.06  --sat_out_model                         small
% 0.52/1.06  --sat_out_clauses                       false
% 0.52/1.06  
% 0.52/1.06  ------ QBF Options
% 0.52/1.06  
% 0.52/1.06  --qbf_mode                              false
% 0.52/1.06  --qbf_elim_univ                         false
% 0.52/1.06  --qbf_dom_inst                          none
% 0.52/1.06  --qbf_dom_pre_inst                      false
% 0.52/1.06  --qbf_sk_in                             false
% 0.52/1.06  --qbf_pred_elim                         true
% 0.52/1.06  --qbf_split                             512
% 0.52/1.06  
% 0.52/1.06  ------ BMC1 Options
% 0.52/1.06  
% 0.52/1.06  --bmc1_incremental                      false
% 0.52/1.06  --bmc1_axioms                           reachable_all
% 0.52/1.06  --bmc1_min_bound                        0
% 0.52/1.06  --bmc1_max_bound                        -1
% 0.52/1.06  --bmc1_max_bound_default                -1
% 0.52/1.06  --bmc1_symbol_reachability              true
% 0.52/1.06  --bmc1_property_lemmas                  false
% 0.52/1.06  --bmc1_k_induction                      false
% 0.52/1.06  --bmc1_non_equiv_states                 false
% 0.52/1.06  --bmc1_deadlock                         false
% 0.52/1.06  --bmc1_ucm                              false
% 0.52/1.06  --bmc1_add_unsat_core                   none
% 0.52/1.06  --bmc1_unsat_core_children              false
% 0.52/1.06  --bmc1_unsat_core_extrapolate_axioms    false
% 0.52/1.06  --bmc1_out_stat                         full
% 0.52/1.06  --bmc1_ground_init                      false
% 0.52/1.06  --bmc1_pre_inst_next_state              false
% 0.52/1.06  --bmc1_pre_inst_state                   false
% 0.52/1.06  --bmc1_pre_inst_reach_state             false
% 0.52/1.06  --bmc1_out_unsat_core                   false
% 0.52/1.06  --bmc1_aig_witness_out                  false
% 0.52/1.06  --bmc1_verbose                          false
% 0.52/1.06  --bmc1_dump_clauses_tptp                false
% 0.52/1.06  --bmc1_dump_unsat_core_tptp             false
% 0.52/1.06  --bmc1_dump_file                        -
% 0.52/1.06  --bmc1_ucm_expand_uc_limit              128
% 0.52/1.06  --bmc1_ucm_n_expand_iterations          6
% 0.52/1.06  --bmc1_ucm_extend_mode                  1
% 0.52/1.06  --bmc1_ucm_init_mode                    2
% 0.52/1.06  --bmc1_ucm_cone_mode                    none
% 0.52/1.06  --bmc1_ucm_reduced_relation_type        0
% 0.52/1.06  --bmc1_ucm_relax_model                  4
% 0.52/1.06  --bmc1_ucm_full_tr_after_sat            true
% 0.52/1.06  --bmc1_ucm_expand_neg_assumptions       false
% 0.52/1.06  --bmc1_ucm_layered_model                none
% 0.52/1.06  --bmc1_ucm_max_lemma_size               10
% 0.52/1.06  
% 0.52/1.06  ------ AIG Options
% 0.52/1.06  
% 0.52/1.06  --aig_mode                              false
% 0.52/1.06  
% 0.52/1.06  ------ Instantiation Options
% 0.52/1.06  
% 0.52/1.06  --instantiation_flag                    true
% 0.52/1.06  --inst_sos_flag                         false
% 0.52/1.06  --inst_sos_phase                        true
% 0.52/1.06  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.52/1.06  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.52/1.06  --inst_lit_sel_side                     none
% 0.52/1.06  --inst_solver_per_active                1400
% 0.52/1.06  --inst_solver_calls_frac                1.
% 0.52/1.06  --inst_passive_queue_type               priority_queues
% 0.52/1.06  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.52/1.06  --inst_passive_queues_freq              [25;2]
% 0.52/1.06  --inst_dismatching                      true
% 0.52/1.06  --inst_eager_unprocessed_to_passive     true
% 0.52/1.06  --inst_prop_sim_given                   true
% 0.52/1.06  --inst_prop_sim_new                     false
% 0.52/1.06  --inst_subs_new                         false
% 0.52/1.06  --inst_eq_res_simp                      false
% 0.52/1.06  --inst_subs_given                       false
% 0.52/1.06  --inst_orphan_elimination               true
% 0.52/1.06  --inst_learning_loop_flag               true
% 0.52/1.06  --inst_learning_start                   3000
% 0.52/1.06  --inst_learning_factor                  2
% 0.52/1.06  --inst_start_prop_sim_after_learn       3
% 0.52/1.06  --inst_sel_renew                        solver
% 0.52/1.06  --inst_lit_activity_flag                true
% 0.52/1.06  --inst_restr_to_given                   false
% 0.52/1.06  --inst_activity_threshold               500
% 0.52/1.06  --inst_out_proof                        true
% 0.52/1.06  
% 0.52/1.06  ------ Resolution Options
% 0.52/1.06  
% 0.52/1.06  --resolution_flag                       false
% 0.52/1.06  --res_lit_sel                           adaptive
% 0.52/1.06  --res_lit_sel_side                      none
% 0.52/1.06  --res_ordering                          kbo
% 0.52/1.06  --res_to_prop_solver                    active
% 0.52/1.06  --res_prop_simpl_new                    false
% 0.52/1.06  --res_prop_simpl_given                  true
% 0.52/1.06  --res_passive_queue_type                priority_queues
% 0.52/1.06  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.52/1.06  --res_passive_queues_freq               [15;5]
% 0.52/1.06  --res_forward_subs                      full
% 0.52/1.06  --res_backward_subs                     full
% 0.52/1.06  --res_forward_subs_resolution           true
% 0.52/1.06  --res_backward_subs_resolution          true
% 0.52/1.06  --res_orphan_elimination                true
% 0.52/1.06  --res_time_limit                        2.
% 0.52/1.06  --res_out_proof                         true
% 0.52/1.06  
% 0.52/1.06  ------ Superposition Options
% 0.52/1.06  
% 0.52/1.06  --superposition_flag                    true
% 0.52/1.06  --sup_passive_queue_type                priority_queues
% 0.52/1.06  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.52/1.06  --sup_passive_queues_freq               [8;1;4]
% 0.52/1.06  --demod_completeness_check              fast
% 0.52/1.06  --demod_use_ground                      true
% 0.52/1.06  --sup_to_prop_solver                    passive
% 0.52/1.06  --sup_prop_simpl_new                    true
% 0.52/1.06  --sup_prop_simpl_given                  true
% 0.52/1.06  --sup_fun_splitting                     false
% 0.52/1.06  --sup_smt_interval                      50000
% 0.52/1.06  
% 0.52/1.06  ------ Superposition Simplification Setup
% 0.52/1.06  
% 0.52/1.06  --sup_indices_passive                   []
% 0.52/1.06  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.52/1.06  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.52/1.06  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.52/1.06  --sup_full_triv                         [TrivRules;PropSubs]
% 0.52/1.06  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.52/1.06  --sup_full_bw                           [BwDemod]
% 0.52/1.06  --sup_immed_triv                        [TrivRules]
% 0.52/1.06  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.52/1.06  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.52/1.06  --sup_immed_bw_main                     []
% 0.52/1.06  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.52/1.06  --sup_input_triv                        [Unflattening;TrivRules]
% 0.52/1.06  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.52/1.06  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.52/1.06  
% 0.52/1.06  ------ Combination Options
% 0.52/1.06  
% 0.52/1.06  --comb_res_mult                         3
% 0.52/1.06  --comb_sup_mult                         2
% 0.52/1.06  --comb_inst_mult                        10
% 0.52/1.06  
% 0.52/1.06  ------ Debug Options
% 0.52/1.06  
% 0.52/1.06  --dbg_backtrace                         false
% 0.52/1.06  --dbg_dump_prop_clauses                 false
% 0.52/1.06  --dbg_dump_prop_clauses_file            -
% 0.52/1.06  --dbg_out_stat                          false
% 0.52/1.06  
% 0.52/1.06  
% 0.52/1.06  
% 0.52/1.06  
% 0.52/1.06  ------ Proving...
% 0.52/1.06  
% 0.52/1.06  
% 0.52/1.06  % SZS status Theorem for theBenchmark.p
% 0.52/1.06  
% 0.52/1.06  % SZS output start CNFRefutation for theBenchmark.p
% 0.52/1.06  
% 0.52/1.06  fof(f2,axiom,(
% 0.52/1.06    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.52/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.52/1.06  
% 0.52/1.06  fof(f24,plain,(
% 0.52/1.06    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.52/1.06    inference(nnf_transformation,[],[f2])).
% 0.52/1.06  
% 0.52/1.06  fof(f25,plain,(
% 0.52/1.06    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.52/1.06    inference(flattening,[],[f24])).
% 0.52/1.06  
% 0.52/1.06  fof(f26,plain,(
% 0.52/1.06    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.52/1.06    inference(rectify,[],[f25])).
% 0.52/1.06  
% 0.52/1.06  fof(f27,plain,(
% 0.52/1.06    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 0.52/1.06    introduced(choice_axiom,[])).
% 0.52/1.06  
% 0.52/1.06  fof(f28,plain,(
% 0.52/1.06    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.52/1.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).
% 0.52/1.06  
% 0.52/1.06  fof(f36,plain,(
% 0.52/1.06    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.52/1.06    inference(cnf_transformation,[],[f28])).
% 0.52/1.06  
% 0.52/1.06  fof(f68,plain,(
% 0.52/1.06    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 0.52/1.06    inference(equality_resolution,[],[f36])).
% 0.52/1.06  
% 0.52/1.06  fof(f13,axiom,(
% 0.52/1.06    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 0.52/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.52/1.06  
% 0.52/1.06  fof(f22,plain,(
% 0.52/1.06    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.52/1.06    inference(ennf_transformation,[],[f13])).
% 0.52/1.06  
% 0.52/1.06  fof(f54,plain,(
% 0.52/1.06    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.52/1.06    inference(cnf_transformation,[],[f22])).
% 0.52/1.06  
% 0.52/1.06  fof(f10,axiom,(
% 0.52/1.06    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.52/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.52/1.06  
% 0.52/1.06  fof(f51,plain,(
% 0.52/1.06    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.52/1.06    inference(cnf_transformation,[],[f10])).
% 0.52/1.06  
% 0.52/1.06  fof(f11,axiom,(
% 0.52/1.06    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.52/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.52/1.06  
% 0.52/1.06  fof(f52,plain,(
% 0.52/1.06    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.52/1.06    inference(cnf_transformation,[],[f11])).
% 0.52/1.06  
% 0.52/1.06  fof(f12,axiom,(
% 0.52/1.06    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.52/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.52/1.06  
% 0.52/1.06  fof(f53,plain,(
% 0.52/1.06    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.52/1.06    inference(cnf_transformation,[],[f12])).
% 0.52/1.06  
% 0.52/1.06  fof(f57,plain,(
% 0.52/1.06    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.52/1.06    inference(definition_unfolding,[],[f52,f53])).
% 0.52/1.06  
% 0.52/1.06  fof(f58,plain,(
% 0.52/1.06    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.52/1.06    inference(definition_unfolding,[],[f51,f57])).
% 0.52/1.06  
% 0.52/1.06  fof(f64,plain,(
% 0.52/1.06    ( ! [X0,X1] : (r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 0.52/1.06    inference(definition_unfolding,[],[f54,f58])).
% 0.52/1.06  
% 0.52/1.06  fof(f5,axiom,(
% 0.52/1.06    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.52/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.52/1.06  
% 0.52/1.06  fof(f16,plain,(
% 0.52/1.06    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.52/1.06    inference(rectify,[],[f5])).
% 0.52/1.06  
% 0.52/1.06  fof(f19,plain,(
% 0.52/1.06    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.52/1.06    inference(ennf_transformation,[],[f16])).
% 0.52/1.06  
% 0.52/1.06  fof(f30,plain,(
% 0.52/1.06    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 0.52/1.06    introduced(choice_axiom,[])).
% 0.52/1.06  
% 0.52/1.06  fof(f31,plain,(
% 0.52/1.06    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.52/1.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f30])).
% 0.52/1.06  
% 0.52/1.06  fof(f46,plain,(
% 0.52/1.06    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.52/1.06    inference(cnf_transformation,[],[f31])).
% 0.52/1.06  
% 0.52/1.06  fof(f40,plain,(
% 0.52/1.06    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 0.52/1.06    inference(cnf_transformation,[],[f28])).
% 0.52/1.06  
% 0.52/1.06  fof(f38,plain,(
% 0.52/1.06    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 0.52/1.06    inference(cnf_transformation,[],[f28])).
% 0.52/1.06  
% 0.52/1.06  fof(f14,conjecture,(
% 0.52/1.06    ! [X0,X1] : (k3_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) | r1_xboole_0(k1_tarski(X0),X1))),
% 0.52/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.52/1.06  
% 0.52/1.06  fof(f15,negated_conjecture,(
% 0.52/1.06    ~! [X0,X1] : (k3_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) | r1_xboole_0(k1_tarski(X0),X1))),
% 0.52/1.06    inference(negated_conjecture,[],[f14])).
% 0.52/1.06  
% 0.52/1.06  fof(f23,plain,(
% 0.52/1.06    ? [X0,X1] : (k3_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0) & ~r1_xboole_0(k1_tarski(X0),X1))),
% 0.52/1.06    inference(ennf_transformation,[],[f15])).
% 0.52/1.06  
% 0.52/1.06  fof(f32,plain,(
% 0.52/1.06    ? [X0,X1] : (k3_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0) & ~r1_xboole_0(k1_tarski(X0),X1)) => (k3_xboole_0(k1_tarski(sK2),sK3) != k1_tarski(sK2) & ~r1_xboole_0(k1_tarski(sK2),sK3))),
% 0.52/1.06    introduced(choice_axiom,[])).
% 0.52/1.06  
% 0.52/1.06  fof(f33,plain,(
% 0.52/1.06    k3_xboole_0(k1_tarski(sK2),sK3) != k1_tarski(sK2) & ~r1_xboole_0(k1_tarski(sK2),sK3)),
% 0.52/1.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f23,f32])).
% 0.52/1.06  
% 0.52/1.06  fof(f56,plain,(
% 0.52/1.06    k3_xboole_0(k1_tarski(sK2),sK3) != k1_tarski(sK2)),
% 0.52/1.06    inference(cnf_transformation,[],[f33])).
% 0.52/1.06  
% 0.52/1.06  fof(f9,axiom,(
% 0.52/1.06    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.52/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.52/1.06  
% 0.52/1.06  fof(f50,plain,(
% 0.52/1.06    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.52/1.06    inference(cnf_transformation,[],[f9])).
% 0.52/1.06  
% 0.52/1.06  fof(f65,plain,(
% 0.52/1.06    k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != k2_enumset1(sK2,sK2,sK2,sK2)),
% 0.52/1.06    inference(definition_unfolding,[],[f56,f50,f58,f58])).
% 0.52/1.06  
% 0.52/1.06  fof(f55,plain,(
% 0.52/1.06    ~r1_xboole_0(k1_tarski(sK2),sK3)),
% 0.52/1.06    inference(cnf_transformation,[],[f33])).
% 0.52/1.06  
% 0.52/1.06  fof(f66,plain,(
% 0.52/1.06    ~r1_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK3)),
% 0.52/1.06    inference(definition_unfolding,[],[f55,f58])).
% 0.52/1.06  
% 0.52/1.06  cnf(c_5,plain,
% 0.52/1.06      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 0.52/1.06      inference(cnf_transformation,[],[f68]) ).
% 0.52/1.06  
% 0.52/1.06  cnf(c_6984,plain,
% 0.52/1.06      ( ~ r2_hidden(X0,k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK3))
% 0.52/1.06      | ~ r2_hidden(X0,sK3) ),
% 0.52/1.06      inference(instantiation,[status(thm)],[c_5]) ).
% 0.52/1.06  
% 0.52/1.06  cnf(c_6986,plain,
% 0.52/1.06      ( ~ r2_hidden(sK2,k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK3))
% 0.52/1.06      | ~ r2_hidden(sK2,sK3) ),
% 0.52/1.06      inference(instantiation,[status(thm)],[c_6984]) ).
% 0.52/1.06  
% 0.52/1.06  cnf(c_16,plain,
% 0.52/1.06      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1) ),
% 0.52/1.06      inference(cnf_transformation,[],[f64]) ).
% 0.52/1.06  
% 0.52/1.06  cnf(c_1753,plain,
% 0.52/1.06      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),k4_xboole_0(X1,X2))
% 0.52/1.06      | r2_hidden(X0,k4_xboole_0(X1,X2)) ),
% 0.52/1.06      inference(instantiation,[status(thm)],[c_16]) ).
% 0.52/1.06  
% 0.52/1.06  cnf(c_4399,plain,
% 0.52/1.06      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK3))
% 0.52/1.06      | r2_hidden(X0,k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK3)) ),
% 0.52/1.06      inference(instantiation,[status(thm)],[c_1753]) ).
% 0.52/1.06  
% 0.52/1.06  cnf(c_4401,plain,
% 0.52/1.06      ( r1_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK3))
% 0.52/1.06      | r2_hidden(sK2,k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK3)) ),
% 0.52/1.06      inference(instantiation,[status(thm)],[c_4399]) ).
% 0.52/1.06  
% 0.52/1.06  cnf(c_10,plain,
% 0.52/1.06      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,X1) | ~ r2_hidden(X2,X0) ),
% 0.52/1.06      inference(cnf_transformation,[],[f46]) ).
% 0.52/1.06  
% 0.52/1.06  cnf(c_878,plain,
% 0.52/1.06      ( ~ r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
% 0.52/1.06      | ~ r2_hidden(X2,X1)
% 0.52/1.06      | ~ r2_hidden(X2,k2_enumset1(X0,X0,X0,X0)) ),
% 0.52/1.06      inference(instantiation,[status(thm)],[c_10]) ).
% 0.52/1.06  
% 0.52/1.06  cnf(c_1260,plain,
% 0.52/1.06      ( ~ r1_xboole_0(k2_enumset1(X0,X0,X0,X0),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK3))
% 0.52/1.06      | ~ r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK2),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK3),k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(X0,X0,X0,X0))
% 0.52/1.06      | ~ r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK2),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK3),k2_enumset1(sK2,sK2,sK2,sK2)),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK3)) ),
% 0.52/1.06      inference(instantiation,[status(thm)],[c_878]) ).
% 0.52/1.06  
% 0.52/1.06  cnf(c_1262,plain,
% 0.52/1.06      ( ~ r1_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK3))
% 0.52/1.06      | ~ r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK2),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK3),k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK2,sK2,sK2,sK2))
% 0.52/1.06      | ~ r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK2),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK3),k2_enumset1(sK2,sK2,sK2,sK2)),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK3)) ),
% 0.52/1.06      inference(instantiation,[status(thm)],[c_1260]) ).
% 0.52/1.06  
% 0.52/1.06  cnf(c_1,plain,
% 0.52/1.06      ( ~ r2_hidden(sK0(X0,X1,X2),X0)
% 0.52/1.06      | ~ r2_hidden(sK0(X0,X1,X2),X2)
% 0.52/1.06      | r2_hidden(sK0(X0,X1,X2),X1)
% 0.52/1.06      | k4_xboole_0(X0,X1) = X2 ),
% 0.52/1.06      inference(cnf_transformation,[],[f40]) ).
% 0.52/1.06  
% 0.52/1.06  cnf(c_946,plain,
% 0.52/1.06      ( ~ r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK2),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK3),k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK2,sK2,sK2,sK2))
% 0.52/1.06      | r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK2),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK3),k2_enumset1(sK2,sK2,sK2,sK2)),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK3))
% 0.52/1.06      | k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK3)) = k2_enumset1(sK2,sK2,sK2,sK2) ),
% 0.52/1.06      inference(instantiation,[status(thm)],[c_1]) ).
% 0.52/1.06  
% 0.52/1.06  cnf(c_3,plain,
% 0.52/1.06      ( r2_hidden(sK0(X0,X1,X2),X0)
% 0.52/1.06      | r2_hidden(sK0(X0,X1,X2),X2)
% 0.52/1.06      | k4_xboole_0(X0,X1) = X2 ),
% 0.52/1.06      inference(cnf_transformation,[],[f38]) ).
% 0.52/1.06  
% 0.52/1.06  cnf(c_935,plain,
% 0.52/1.06      ( r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK2),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK3),k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK2,sK2,sK2,sK2))
% 0.52/1.06      | k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK3)) = k2_enumset1(sK2,sK2,sK2,sK2) ),
% 0.52/1.06      inference(instantiation,[status(thm)],[c_3]) ).
% 0.52/1.06  
% 0.52/1.06  cnf(c_893,plain,
% 0.52/1.06      ( r1_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK3)
% 0.52/1.06      | r2_hidden(sK2,sK3) ),
% 0.52/1.06      inference(instantiation,[status(thm)],[c_16]) ).
% 0.52/1.06  
% 0.52/1.06  cnf(c_17,negated_conjecture,
% 0.52/1.06      ( k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != k2_enumset1(sK2,sK2,sK2,sK2) ),
% 0.52/1.06      inference(cnf_transformation,[],[f65]) ).
% 0.52/1.06  
% 0.52/1.06  cnf(c_18,negated_conjecture,
% 0.52/1.06      ( ~ r1_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK3) ),
% 0.52/1.06      inference(cnf_transformation,[],[f66]) ).
% 0.52/1.06  
% 0.52/1.06  cnf(contradiction,plain,
% 0.52/1.06      ( $false ),
% 0.52/1.06      inference(minisat,
% 0.52/1.06                [status(thm)],
% 0.52/1.06                [c_6986,c_4401,c_1262,c_946,c_935,c_893,c_17,c_18]) ).
% 0.52/1.06  
% 0.52/1.06  
% 0.52/1.06  % SZS output end CNFRefutation for theBenchmark.p
% 0.52/1.06  
% 0.52/1.06  ------                               Statistics
% 0.52/1.06  
% 0.52/1.06  ------ General
% 0.52/1.06  
% 0.52/1.06  abstr_ref_over_cycles:                  0
% 0.52/1.06  abstr_ref_under_cycles:                 0
% 0.52/1.06  gc_basic_clause_elim:                   0
% 0.52/1.06  forced_gc_time:                         0
% 0.52/1.06  parsing_time:                           0.01
% 0.52/1.06  unif_index_cands_time:                  0.
% 0.52/1.06  unif_index_add_time:                    0.
% 0.52/1.06  orderings_time:                         0.
% 0.52/1.06  out_proof_time:                         0.008
% 0.52/1.06  total_time:                             0.178
% 0.52/1.06  num_of_symbols:                         41
% 0.52/1.06  num_of_terms:                           7372
% 0.52/1.06  
% 0.52/1.06  ------ Preprocessing
% 0.52/1.06  
% 0.52/1.06  num_of_splits:                          0
% 0.52/1.06  num_of_split_atoms:                     0
% 0.52/1.06  num_of_reused_defs:                     0
% 0.52/1.06  num_eq_ax_congr_red:                    17
% 0.52/1.06  num_of_sem_filtered_clauses:            1
% 0.52/1.06  num_of_subtypes:                        0
% 0.52/1.06  monotx_restored_types:                  0
% 0.52/1.06  sat_num_of_epr_types:                   0
% 0.52/1.06  sat_num_of_non_cyclic_types:            0
% 0.52/1.06  sat_guarded_non_collapsed_types:        0
% 0.52/1.06  num_pure_diseq_elim:                    0
% 0.52/1.06  simp_replaced_by:                       0
% 0.52/1.06  res_preprocessed:                       86
% 0.52/1.06  prep_upred:                             0
% 0.52/1.06  prep_unflattend:                        0
% 0.52/1.06  smt_new_axioms:                         0
% 0.52/1.06  pred_elim_cands:                        2
% 0.52/1.06  pred_elim:                              1
% 0.52/1.06  pred_elim_cl:                           1
% 0.52/1.06  pred_elim_cycles:                       3
% 0.52/1.06  merged_defs:                            8
% 0.52/1.06  merged_defs_ncl:                        0
% 0.52/1.06  bin_hyper_res:                          8
% 0.52/1.06  prep_cycles:                            4
% 0.52/1.06  pred_elim_time:                         0.
% 0.52/1.06  splitting_time:                         0.
% 0.52/1.06  sem_filter_time:                        0.
% 0.52/1.06  monotx_time:                            0.001
% 0.52/1.06  subtype_inf_time:                       0.
% 0.52/1.06  
% 0.52/1.06  ------ Problem properties
% 0.52/1.06  
% 0.52/1.06  clauses:                                18
% 0.52/1.06  conjectures:                            2
% 0.52/1.06  epr:                                    2
% 0.52/1.06  horn:                                   11
% 0.52/1.06  ground:                                 2
% 0.52/1.06  unary:                                  4
% 0.52/1.06  binary:                                 9
% 0.52/1.06  lits:                                   38
% 0.52/1.06  lits_eq:                                10
% 0.52/1.06  fd_pure:                                0
% 0.52/1.06  fd_pseudo:                              0
% 0.52/1.06  fd_cond:                                0
% 0.52/1.06  fd_pseudo_cond:                         3
% 0.52/1.06  ac_symbols:                             0
% 0.52/1.06  
% 0.52/1.06  ------ Propositional Solver
% 0.52/1.06  
% 0.52/1.06  prop_solver_calls:                      27
% 0.52/1.06  prop_fast_solver_calls:                 519
% 0.52/1.06  smt_solver_calls:                       0
% 0.52/1.06  smt_fast_solver_calls:                  0
% 0.52/1.06  prop_num_of_clauses:                    2205
% 0.52/1.06  prop_preprocess_simplified:             6261
% 0.52/1.06  prop_fo_subsumed:                       1
% 0.52/1.06  prop_solver_time:                       0.
% 0.52/1.06  smt_solver_time:                        0.
% 0.52/1.06  smt_fast_solver_time:                   0.
% 0.52/1.06  prop_fast_solver_time:                  0.
% 0.52/1.06  prop_unsat_core_time:                   0.
% 0.52/1.06  
% 0.52/1.06  ------ QBF
% 0.52/1.06  
% 0.52/1.06  qbf_q_res:                              0
% 0.52/1.06  qbf_num_tautologies:                    0
% 0.52/1.06  qbf_prep_cycles:                        0
% 0.52/1.06  
% 0.52/1.06  ------ BMC1
% 0.52/1.06  
% 0.52/1.06  bmc1_current_bound:                     -1
% 0.52/1.06  bmc1_last_solved_bound:                 -1
% 0.52/1.06  bmc1_unsat_core_size:                   -1
% 0.52/1.06  bmc1_unsat_core_parents_size:           -1
% 0.52/1.06  bmc1_merge_next_fun:                    0
% 0.52/1.06  bmc1_unsat_core_clauses_time:           0.
% 0.52/1.06  
% 0.52/1.06  ------ Instantiation
% 0.52/1.06  
% 0.52/1.06  inst_num_of_clauses:                    595
% 0.52/1.06  inst_num_in_passive:                    226
% 0.52/1.06  inst_num_in_active:                     212
% 0.52/1.06  inst_num_in_unprocessed:                156
% 0.52/1.06  inst_num_of_loops:                      279
% 0.52/1.06  inst_num_of_learning_restarts:          0
% 0.52/1.06  inst_num_moves_active_passive:          64
% 0.52/1.06  inst_lit_activity:                      0
% 0.52/1.06  inst_lit_activity_moves:                0
% 0.52/1.06  inst_num_tautologies:                   0
% 0.52/1.06  inst_num_prop_implied:                  0
% 0.52/1.06  inst_num_existing_simplified:           0
% 0.52/1.06  inst_num_eq_res_simplified:             0
% 0.52/1.06  inst_num_child_elim:                    0
% 0.52/1.06  inst_num_of_dismatching_blockings:      446
% 0.52/1.06  inst_num_of_non_proper_insts:           564
% 0.52/1.06  inst_num_of_duplicates:                 0
% 0.52/1.06  inst_inst_num_from_inst_to_res:         0
% 0.52/1.06  inst_dismatching_checking_time:         0.
% 0.52/1.06  
% 0.52/1.06  ------ Resolution
% 0.52/1.06  
% 0.52/1.06  res_num_of_clauses:                     0
% 0.52/1.06  res_num_in_passive:                     0
% 0.52/1.06  res_num_in_active:                      0
% 0.52/1.06  res_num_of_loops:                       90
% 0.52/1.06  res_forward_subset_subsumed:            25
% 0.52/1.06  res_backward_subset_subsumed:           2
% 0.52/1.06  res_forward_subsumed:                   0
% 0.52/1.06  res_backward_subsumed:                  0
% 0.52/1.06  res_forward_subsumption_resolution:     0
% 0.52/1.06  res_backward_subsumption_resolution:    0
% 0.52/1.06  res_clause_to_clause_subsumption:       1423
% 0.52/1.06  res_orphan_elimination:                 0
% 0.52/1.06  res_tautology_del:                      53
% 0.52/1.06  res_num_eq_res_simplified:              0
% 0.52/1.06  res_num_sel_changes:                    0
% 0.52/1.06  res_moves_from_active_to_pass:          0
% 0.52/1.06  
% 0.52/1.06  ------ Superposition
% 0.52/1.06  
% 0.52/1.06  sup_time_total:                         0.
% 0.52/1.06  sup_time_generating:                    0.
% 0.52/1.06  sup_time_sim_full:                      0.
% 0.52/1.06  sup_time_sim_immed:                     0.
% 0.52/1.06  
% 0.52/1.06  sup_num_of_clauses:                     155
% 0.52/1.06  sup_num_in_active:                      43
% 0.52/1.06  sup_num_in_passive:                     112
% 0.52/1.06  sup_num_of_loops:                       54
% 0.52/1.06  sup_fw_superposition:                   388
% 0.52/1.06  sup_bw_superposition:                   381
% 0.52/1.06  sup_immediate_simplified:               497
% 0.52/1.06  sup_given_eliminated:                   2
% 0.52/1.06  comparisons_done:                       0
% 0.52/1.06  comparisons_avoided:                    0
% 0.52/1.06  
% 0.52/1.06  ------ Simplifications
% 0.52/1.06  
% 0.52/1.06  
% 0.52/1.06  sim_fw_subset_subsumed:                 30
% 0.52/1.06  sim_bw_subset_subsumed:                 0
% 0.52/1.06  sim_fw_subsumed:                        89
% 0.52/1.06  sim_bw_subsumed:                        19
% 0.52/1.06  sim_fw_subsumption_res:                 3
% 0.52/1.06  sim_bw_subsumption_res:                 0
% 0.52/1.06  sim_tautology_del:                      28
% 0.52/1.06  sim_eq_tautology_del:                   85
% 0.52/1.06  sim_eq_res_simp:                        8
% 0.52/1.06  sim_fw_demodulated:                     201
% 0.52/1.06  sim_bw_demodulated:                     33
% 0.52/1.06  sim_light_normalised:                   235
% 0.52/1.06  sim_joinable_taut:                      0
% 0.52/1.06  sim_joinable_simp:                      0
% 0.52/1.06  sim_ac_normalised:                      0
% 0.52/1.06  sim_smt_subsumption:                    0
% 0.52/1.06  
%------------------------------------------------------------------------------
