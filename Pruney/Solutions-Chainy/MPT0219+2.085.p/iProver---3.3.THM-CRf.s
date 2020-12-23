%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:29:22 EST 2020

% Result     : Theorem 7.87s
% Output     : CNFRefutation 7.87s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 188 expanded)
%              Number of clauses        :   32 (  36 expanded)
%              Number of leaves         :   17 (  53 expanded)
%              Depth                    :   15
%              Number of atoms          :  231 ( 630 expanded)
%              Number of equality atoms :  179 ( 508 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f57,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1)),k3_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1))) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f43,f33,f45,f45])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f17])).

fof(f21,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f27,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) )
   => ( sK1 != sK2
      & k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( sK1 != sK2
    & k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f21,f27])).

fof(f52,plain,(
    k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f70,plain,(
    k5_xboole_0(k5_xboole_0(k2_tarski(sK1,sK1),k2_tarski(sK2,sK2)),k3_xboole_0(k2_tarski(sK1,sK1),k2_tarski(sK2,sK2))) = k2_tarski(sK1,sK1) ),
    inference(definition_unfolding,[],[f52,f33,f45,f45,f45])).

fof(f11,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f15])).

fof(f54,plain,(
    ! [X4,X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f49,f50])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f48,f54])).

fof(f56,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f47,f55])).

fof(f69,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f46,f56])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f22])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f23])).

fof(f25,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK0(X0,X1,X2,X3) != X2
            & sK0(X0,X1,X2,X3) != X1
            & sK0(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) )
        & ( sK0(X0,X1,X2,X3) = X2
          | sK0(X0,X1,X2,X3) = X1
          | sK0(X0,X1,X2,X3) = X0
          | r2_hidden(sK0(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK0(X0,X1,X2,X3) != X2
              & sK0(X0,X1,X2,X3) != X1
              & sK0(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) )
          & ( sK0(X0,X1,X2,X3) = X2
            | sK0(X0,X1,X2,X3) = X1
            | sK0(X0,X1,X2,X3) = X0
            | r2_hidden(sK0(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).

fof(f38,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f65,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f38,f56])).

fof(f71,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k5_enumset1(X0,X0,X0,X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f65])).

fof(f72,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k5_enumset1(X0,X0,X0,X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f71])).

fof(f35,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f68,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f35,f56])).

fof(f77,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f68])).

fof(f36,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f67,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f36,f56])).

fof(f75,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k5_enumset1(X5,X5,X5,X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f67])).

fof(f76,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k5_enumset1(X5,X5,X5,X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f75])).

fof(f53,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_332,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2417,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK2,k5_enumset1(X2,X2,X2,X2,X2,X3,X4))
    | k5_enumset1(X2,X2,X2,X2,X2,X3,X4) != X1
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_332])).

cnf(c_5102,plain,
    ( ~ r2_hidden(sK2,X0)
    | r2_hidden(sK2,k5_enumset1(X1,X1,X1,X1,X1,X2,X3))
    | k5_enumset1(X1,X1,X1,X1,X1,X2,X3) != X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_2417])).

cnf(c_19207,plain,
    ( r2_hidden(sK2,k5_enumset1(X0,X0,X0,X0,X0,X0,X1))
    | ~ r2_hidden(sK2,k2_tarski(X0,X1))
    | k5_enumset1(X0,X0,X0,X0,X0,X0,X1) != k2_tarski(X0,X1)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_5102])).

cnf(c_19209,plain,
    ( r2_hidden(sK2,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | ~ r2_hidden(sK2,k2_tarski(sK1,sK1))
    | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1) != k2_tarski(sK1,sK1)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_19207])).

cnf(c_0,plain,
    ( k5_xboole_0(k5_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1)),k3_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1))) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_4,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_2,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_325,plain,
    ( k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X1),k3_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1)))) = k2_tarski(X0,X1) ),
    inference(theory_normalisation,[status(thm)],[c_0,c_4,c_2])).

cnf(c_17,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k2_tarski(sK1,sK1),k2_tarski(sK2,sK2)),k3_xboole_0(k2_tarski(sK1,sK1),k2_tarski(sK2,sK2))) = k2_tarski(sK1,sK1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_321,negated_conjecture,
    ( k5_xboole_0(k2_tarski(sK1,sK1),k5_xboole_0(k2_tarski(sK2,sK2),k3_xboole_0(k2_tarski(sK1,sK1),k2_tarski(sK2,sK2)))) = k2_tarski(sK1,sK1) ),
    inference(theory_normalisation,[status(thm)],[c_17,c_4,c_2])).

cnf(c_4504,plain,
    ( k2_tarski(sK1,sK2) = k2_tarski(sK1,sK1) ),
    inference(superposition,[status(thm)],[c_325,c_321])).

cnf(c_14,plain,
    ( k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_10,plain,
    ( r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X2,X0)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_479,plain,
    ( r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4545,plain,
    ( r2_hidden(X0,k2_tarski(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_14,c_479])).

cnf(c_5267,plain,
    ( r2_hidden(sK2,k2_tarski(sK1,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4504,c_4545])).

cnf(c_5271,plain,
    ( r2_hidden(sK2,k2_tarski(sK1,sK1)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5267])).

cnf(c_327,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_775,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_327])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X2,X3))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_619,plain,
    ( ~ r2_hidden(sK2,k5_enumset1(X0,X0,X0,X0,X0,X1,X2))
    | sK2 = X0
    | sK2 = X1
    | sK2 = X2 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_621,plain,
    ( ~ r2_hidden(sK2,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | sK2 = sK1 ),
    inference(instantiation,[status(thm)],[c_619])).

cnf(c_328,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_573,plain,
    ( sK2 != X0
    | sK1 != X0
    | sK1 = sK2 ),
    inference(instantiation,[status(thm)],[c_328])).

cnf(c_574,plain,
    ( sK2 != sK1
    | sK1 = sK2
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_573])).

cnf(c_12,plain,
    ( r2_hidden(X0,k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_24,plain,
    ( r2_hidden(sK1,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_21,plain,
    ( ~ r2_hidden(sK1,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_19,plain,
    ( k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k2_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_16,negated_conjecture,
    ( sK1 != sK2 ),
    inference(cnf_transformation,[],[f53])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_19209,c_5271,c_775,c_621,c_574,c_24,c_21,c_19,c_16])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:38:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.87/1.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.87/1.48  
% 7.87/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.87/1.48  
% 7.87/1.48  ------  iProver source info
% 7.87/1.48  
% 7.87/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.87/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.87/1.48  git: non_committed_changes: false
% 7.87/1.48  git: last_make_outside_of_git: false
% 7.87/1.48  
% 7.87/1.48  ------ 
% 7.87/1.48  ------ Parsing...
% 7.87/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.87/1.48  
% 7.87/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.87/1.48  
% 7.87/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.87/1.48  
% 7.87/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.87/1.48  ------ Proving...
% 7.87/1.48  ------ Problem Properties 
% 7.87/1.48  
% 7.87/1.48  
% 7.87/1.48  clauses                                 18
% 7.87/1.48  conjectures                             2
% 7.87/1.48  EPR                                     1
% 7.87/1.48  Horn                                    16
% 7.87/1.48  unary                                   13
% 7.87/1.48  binary                                  0
% 7.87/1.48  lits                                    31
% 7.87/1.48  lits eq                                 23
% 7.87/1.48  fd_pure                                 0
% 7.87/1.48  fd_pseudo                               0
% 7.87/1.48  fd_cond                                 0
% 7.87/1.48  fd_pseudo_cond                          4
% 7.87/1.48  AC symbols                              1
% 7.87/1.48  
% 7.87/1.48  ------ Input Options Time Limit: Unbounded
% 7.87/1.48  
% 7.87/1.48  
% 7.87/1.48  ------ 
% 7.87/1.48  Current options:
% 7.87/1.48  ------ 
% 7.87/1.48  
% 7.87/1.48  
% 7.87/1.48  
% 7.87/1.48  
% 7.87/1.48  ------ Proving...
% 7.87/1.48  
% 7.87/1.48  
% 7.87/1.48  % SZS status Theorem for theBenchmark.p
% 7.87/1.48  
% 7.87/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.87/1.48  
% 7.87/1.48  fof(f8,axiom,(
% 7.87/1.48    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)),
% 7.87/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.87/1.48  
% 7.87/1.48  fof(f43,plain,(
% 7.87/1.48    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)) )),
% 7.87/1.48    inference(cnf_transformation,[],[f8])).
% 7.87/1.48  
% 7.87/1.48  fof(f5,axiom,(
% 7.87/1.48    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)),
% 7.87/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.87/1.48  
% 7.87/1.48  fof(f33,plain,(
% 7.87/1.48    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 7.87/1.48    inference(cnf_transformation,[],[f5])).
% 7.87/1.48  
% 7.87/1.48  fof(f10,axiom,(
% 7.87/1.48    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 7.87/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.87/1.48  
% 7.87/1.48  fof(f45,plain,(
% 7.87/1.48    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 7.87/1.48    inference(cnf_transformation,[],[f10])).
% 7.87/1.48  
% 7.87/1.48  fof(f57,plain,(
% 7.87/1.48    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1)),k3_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1))) = k2_tarski(X0,X1)) )),
% 7.87/1.48    inference(definition_unfolding,[],[f43,f33,f45,f45])).
% 7.87/1.48  
% 7.87/1.48  fof(f4,axiom,(
% 7.87/1.48    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 7.87/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.87/1.48  
% 7.87/1.48  fof(f32,plain,(
% 7.87/1.48    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 7.87/1.48    inference(cnf_transformation,[],[f4])).
% 7.87/1.48  
% 7.87/1.48  fof(f1,axiom,(
% 7.87/1.48    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 7.87/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.87/1.48  
% 7.87/1.48  fof(f29,plain,(
% 7.87/1.48    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 7.87/1.48    inference(cnf_transformation,[],[f1])).
% 7.87/1.48  
% 7.87/1.48  fof(f17,conjecture,(
% 7.87/1.48    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) => X0 = X1)),
% 7.87/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.87/1.48  
% 7.87/1.48  fof(f18,negated_conjecture,(
% 7.87/1.48    ~! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) => X0 = X1)),
% 7.87/1.48    inference(negated_conjecture,[],[f17])).
% 7.87/1.48  
% 7.87/1.48  fof(f21,plain,(
% 7.87/1.48    ? [X0,X1] : (X0 != X1 & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0))),
% 7.87/1.48    inference(ennf_transformation,[],[f18])).
% 7.87/1.48  
% 7.87/1.48  fof(f27,plain,(
% 7.87/1.48    ? [X0,X1] : (X0 != X1 & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)) => (sK1 != sK2 & k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1))),
% 7.87/1.48    introduced(choice_axiom,[])).
% 7.87/1.48  
% 7.87/1.48  fof(f28,plain,(
% 7.87/1.48    sK1 != sK2 & k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1)),
% 7.87/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f21,f27])).
% 7.87/1.48  
% 7.87/1.48  fof(f52,plain,(
% 7.87/1.48    k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1)),
% 7.87/1.48    inference(cnf_transformation,[],[f28])).
% 7.87/1.48  
% 7.87/1.48  fof(f70,plain,(
% 7.87/1.48    k5_xboole_0(k5_xboole_0(k2_tarski(sK1,sK1),k2_tarski(sK2,sK2)),k3_xboole_0(k2_tarski(sK1,sK1),k2_tarski(sK2,sK2))) = k2_tarski(sK1,sK1)),
% 7.87/1.48    inference(definition_unfolding,[],[f52,f33,f45,f45,f45])).
% 7.87/1.48  
% 7.87/1.48  fof(f11,axiom,(
% 7.87/1.48    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 7.87/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.87/1.48  
% 7.87/1.48  fof(f46,plain,(
% 7.87/1.48    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 7.87/1.48    inference(cnf_transformation,[],[f11])).
% 7.87/1.48  
% 7.87/1.48  fof(f12,axiom,(
% 7.87/1.48    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.87/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.87/1.48  
% 7.87/1.48  fof(f47,plain,(
% 7.87/1.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.87/1.48    inference(cnf_transformation,[],[f12])).
% 7.87/1.48  
% 7.87/1.48  fof(f13,axiom,(
% 7.87/1.48    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 7.87/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.87/1.48  
% 7.87/1.48  fof(f48,plain,(
% 7.87/1.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 7.87/1.48    inference(cnf_transformation,[],[f13])).
% 7.87/1.48  
% 7.87/1.48  fof(f14,axiom,(
% 7.87/1.48    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 7.87/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.87/1.48  
% 7.87/1.48  fof(f49,plain,(
% 7.87/1.48    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 7.87/1.48    inference(cnf_transformation,[],[f14])).
% 7.87/1.48  
% 7.87/1.48  fof(f15,axiom,(
% 7.87/1.48    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 7.87/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.87/1.48  
% 7.87/1.48  fof(f50,plain,(
% 7.87/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 7.87/1.48    inference(cnf_transformation,[],[f15])).
% 7.87/1.48  
% 7.87/1.48  fof(f54,plain,(
% 7.87/1.48    ( ! [X4,X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 7.87/1.48    inference(definition_unfolding,[],[f49,f50])).
% 7.87/1.48  
% 7.87/1.48  fof(f55,plain,(
% 7.87/1.48    ( ! [X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 7.87/1.48    inference(definition_unfolding,[],[f48,f54])).
% 7.87/1.48  
% 7.87/1.48  fof(f56,plain,(
% 7.87/1.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 7.87/1.48    inference(definition_unfolding,[],[f47,f55])).
% 7.87/1.48  
% 7.87/1.48  fof(f69,plain,(
% 7.87/1.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 7.87/1.48    inference(definition_unfolding,[],[f46,f56])).
% 7.87/1.48  
% 7.87/1.48  fof(f7,axiom,(
% 7.87/1.48    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 7.87/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.87/1.48  
% 7.87/1.48  fof(f20,plain,(
% 7.87/1.48    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 7.87/1.48    inference(ennf_transformation,[],[f7])).
% 7.87/1.48  
% 7.87/1.48  fof(f22,plain,(
% 7.87/1.48    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.87/1.48    inference(nnf_transformation,[],[f20])).
% 7.87/1.48  
% 7.87/1.48  fof(f23,plain,(
% 7.87/1.48    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.87/1.48    inference(flattening,[],[f22])).
% 7.87/1.48  
% 7.87/1.48  fof(f24,plain,(
% 7.87/1.48    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.87/1.48    inference(rectify,[],[f23])).
% 7.87/1.48  
% 7.87/1.48  fof(f25,plain,(
% 7.87/1.48    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3))))),
% 7.87/1.48    introduced(choice_axiom,[])).
% 7.87/1.48  
% 7.87/1.48  fof(f26,plain,(
% 7.87/1.48    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.87/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).
% 7.87/1.48  
% 7.87/1.48  fof(f38,plain,(
% 7.87/1.48    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 7.87/1.48    inference(cnf_transformation,[],[f26])).
% 7.87/1.48  
% 7.87/1.48  fof(f65,plain,(
% 7.87/1.48    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 7.87/1.48    inference(definition_unfolding,[],[f38,f56])).
% 7.87/1.48  
% 7.87/1.48  fof(f71,plain,(
% 7.87/1.48    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k5_enumset1(X0,X0,X0,X0,X0,X1,X5) != X3) )),
% 7.87/1.48    inference(equality_resolution,[],[f65])).
% 7.87/1.48  
% 7.87/1.48  fof(f72,plain,(
% 7.87/1.48    ( ! [X0,X5,X1] : (r2_hidden(X5,k5_enumset1(X0,X0,X0,X0,X0,X1,X5))) )),
% 7.87/1.48    inference(equality_resolution,[],[f71])).
% 7.87/1.48  
% 7.87/1.48  fof(f35,plain,(
% 7.87/1.48    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 7.87/1.48    inference(cnf_transformation,[],[f26])).
% 7.87/1.48  
% 7.87/1.48  fof(f68,plain,(
% 7.87/1.48    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 7.87/1.48    inference(definition_unfolding,[],[f35,f56])).
% 7.87/1.48  
% 7.87/1.48  fof(f77,plain,(
% 7.87/1.48    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k5_enumset1(X0,X0,X0,X0,X0,X1,X2))) )),
% 7.87/1.48    inference(equality_resolution,[],[f68])).
% 7.87/1.48  
% 7.87/1.48  fof(f36,plain,(
% 7.87/1.48    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 7.87/1.48    inference(cnf_transformation,[],[f26])).
% 7.87/1.48  
% 7.87/1.48  fof(f67,plain,(
% 7.87/1.48    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 7.87/1.48    inference(definition_unfolding,[],[f36,f56])).
% 7.87/1.48  
% 7.87/1.48  fof(f75,plain,(
% 7.87/1.48    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k5_enumset1(X5,X5,X5,X5,X5,X1,X2) != X3) )),
% 7.87/1.48    inference(equality_resolution,[],[f67])).
% 7.87/1.48  
% 7.87/1.48  fof(f76,plain,(
% 7.87/1.48    ( ! [X2,X5,X1] : (r2_hidden(X5,k5_enumset1(X5,X5,X5,X5,X5,X1,X2))) )),
% 7.87/1.48    inference(equality_resolution,[],[f75])).
% 7.87/1.48  
% 7.87/1.48  fof(f53,plain,(
% 7.87/1.48    sK1 != sK2),
% 7.87/1.48    inference(cnf_transformation,[],[f28])).
% 7.87/1.48  
% 7.87/1.48  cnf(c_332,plain,
% 7.87/1.48      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.87/1.48      theory(equality) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_2417,plain,
% 7.87/1.48      ( ~ r2_hidden(X0,X1)
% 7.87/1.48      | r2_hidden(sK2,k5_enumset1(X2,X2,X2,X2,X2,X3,X4))
% 7.87/1.48      | k5_enumset1(X2,X2,X2,X2,X2,X3,X4) != X1
% 7.87/1.48      | sK2 != X0 ),
% 7.87/1.48      inference(instantiation,[status(thm)],[c_332]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_5102,plain,
% 7.87/1.48      ( ~ r2_hidden(sK2,X0)
% 7.87/1.48      | r2_hidden(sK2,k5_enumset1(X1,X1,X1,X1,X1,X2,X3))
% 7.87/1.48      | k5_enumset1(X1,X1,X1,X1,X1,X2,X3) != X0
% 7.87/1.48      | sK2 != sK2 ),
% 7.87/1.48      inference(instantiation,[status(thm)],[c_2417]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_19207,plain,
% 7.87/1.48      ( r2_hidden(sK2,k5_enumset1(X0,X0,X0,X0,X0,X0,X1))
% 7.87/1.48      | ~ r2_hidden(sK2,k2_tarski(X0,X1))
% 7.87/1.48      | k5_enumset1(X0,X0,X0,X0,X0,X0,X1) != k2_tarski(X0,X1)
% 7.87/1.48      | sK2 != sK2 ),
% 7.87/1.48      inference(instantiation,[status(thm)],[c_5102]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_19209,plain,
% 7.87/1.48      ( r2_hidden(sK2,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))
% 7.87/1.48      | ~ r2_hidden(sK2,k2_tarski(sK1,sK1))
% 7.87/1.48      | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1) != k2_tarski(sK1,sK1)
% 7.87/1.48      | sK2 != sK2 ),
% 7.87/1.48      inference(instantiation,[status(thm)],[c_19207]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_0,plain,
% 7.87/1.48      ( k5_xboole_0(k5_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1)),k3_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1))) = k2_tarski(X0,X1) ),
% 7.87/1.48      inference(cnf_transformation,[],[f57]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_4,plain,
% 7.87/1.48      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 7.87/1.48      inference(cnf_transformation,[],[f32]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_2,plain,
% 7.87/1.48      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 7.87/1.48      inference(cnf_transformation,[],[f29]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_325,plain,
% 7.87/1.48      ( k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X1),k3_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1)))) = k2_tarski(X0,X1) ),
% 7.87/1.48      inference(theory_normalisation,[status(thm)],[c_0,c_4,c_2]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_17,negated_conjecture,
% 7.87/1.48      ( k5_xboole_0(k5_xboole_0(k2_tarski(sK1,sK1),k2_tarski(sK2,sK2)),k3_xboole_0(k2_tarski(sK1,sK1),k2_tarski(sK2,sK2))) = k2_tarski(sK1,sK1) ),
% 7.87/1.48      inference(cnf_transformation,[],[f70]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_321,negated_conjecture,
% 7.87/1.48      ( k5_xboole_0(k2_tarski(sK1,sK1),k5_xboole_0(k2_tarski(sK2,sK2),k3_xboole_0(k2_tarski(sK1,sK1),k2_tarski(sK2,sK2)))) = k2_tarski(sK1,sK1) ),
% 7.87/1.48      inference(theory_normalisation,[status(thm)],[c_17,c_4,c_2]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_4504,plain,
% 7.87/1.48      ( k2_tarski(sK1,sK2) = k2_tarski(sK1,sK1) ),
% 7.87/1.48      inference(superposition,[status(thm)],[c_325,c_321]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_14,plain,
% 7.87/1.48      ( k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
% 7.87/1.48      inference(cnf_transformation,[],[f69]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_10,plain,
% 7.87/1.48      ( r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X2,X0)) ),
% 7.87/1.48      inference(cnf_transformation,[],[f72]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_479,plain,
% 7.87/1.48      ( r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X2,X0)) = iProver_top ),
% 7.87/1.48      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_4545,plain,
% 7.87/1.48      ( r2_hidden(X0,k2_tarski(X1,X0)) = iProver_top ),
% 7.87/1.48      inference(superposition,[status(thm)],[c_14,c_479]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_5267,plain,
% 7.87/1.48      ( r2_hidden(sK2,k2_tarski(sK1,sK1)) = iProver_top ),
% 7.87/1.48      inference(superposition,[status(thm)],[c_4504,c_4545]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_5271,plain,
% 7.87/1.48      ( r2_hidden(sK2,k2_tarski(sK1,sK1)) ),
% 7.87/1.48      inference(predicate_to_equality_rev,[status(thm)],[c_5267]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_327,plain,( X0 = X0 ),theory(equality) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_775,plain,
% 7.87/1.48      ( sK2 = sK2 ),
% 7.87/1.48      inference(instantiation,[status(thm)],[c_327]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_13,plain,
% 7.87/1.48      ( ~ r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X2,X3))
% 7.87/1.48      | X0 = X1
% 7.87/1.48      | X0 = X2
% 7.87/1.48      | X0 = X3 ),
% 7.87/1.48      inference(cnf_transformation,[],[f77]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_619,plain,
% 7.87/1.48      ( ~ r2_hidden(sK2,k5_enumset1(X0,X0,X0,X0,X0,X1,X2))
% 7.87/1.48      | sK2 = X0
% 7.87/1.48      | sK2 = X1
% 7.87/1.48      | sK2 = X2 ),
% 7.87/1.48      inference(instantiation,[status(thm)],[c_13]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_621,plain,
% 7.87/1.48      ( ~ r2_hidden(sK2,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))
% 7.87/1.48      | sK2 = sK1 ),
% 7.87/1.48      inference(instantiation,[status(thm)],[c_619]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_328,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_573,plain,
% 7.87/1.48      ( sK2 != X0 | sK1 != X0 | sK1 = sK2 ),
% 7.87/1.48      inference(instantiation,[status(thm)],[c_328]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_574,plain,
% 7.87/1.48      ( sK2 != sK1 | sK1 = sK2 | sK1 != sK1 ),
% 7.87/1.48      inference(instantiation,[status(thm)],[c_573]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_12,plain,
% 7.87/1.48      ( r2_hidden(X0,k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) ),
% 7.87/1.48      inference(cnf_transformation,[],[f76]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_24,plain,
% 7.87/1.48      ( r2_hidden(sK1,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
% 7.87/1.48      inference(instantiation,[status(thm)],[c_12]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_21,plain,
% 7.87/1.48      ( ~ r2_hidden(sK1,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))
% 7.87/1.48      | sK1 = sK1 ),
% 7.87/1.48      inference(instantiation,[status(thm)],[c_13]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_19,plain,
% 7.87/1.48      ( k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k2_tarski(sK1,sK1) ),
% 7.87/1.48      inference(instantiation,[status(thm)],[c_14]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_16,negated_conjecture,
% 7.87/1.48      ( sK1 != sK2 ),
% 7.87/1.48      inference(cnf_transformation,[],[f53]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(contradiction,plain,
% 7.87/1.48      ( $false ),
% 7.87/1.48      inference(minisat,
% 7.87/1.48                [status(thm)],
% 7.87/1.48                [c_19209,c_5271,c_775,c_621,c_574,c_24,c_21,c_19,c_16]) ).
% 7.87/1.48  
% 7.87/1.48  
% 7.87/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 7.87/1.48  
% 7.87/1.48  ------                               Statistics
% 7.87/1.48  
% 7.87/1.48  ------ Selected
% 7.87/1.48  
% 7.87/1.48  total_time:                             0.867
% 7.87/1.48  
%------------------------------------------------------------------------------
