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
% DateTime   : Thu Dec  3 11:38:17 EST 2020

% Result     : Theorem 2.92s
% Output     : CNFRefutation 2.92s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 282 expanded)
%              Number of clauses        :   27 (  62 expanded)
%              Number of leaves         :   12 (  82 expanded)
%              Depth                    :   19
%              Number of atoms          :  288 (1378 expanded)
%              Number of equality atoms :  144 ( 483 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

fof(f12,plain,(
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
    inference(rectify,[],[f11])).

fof(f13,plain,(
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

fof(f14,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f13])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f27,f28])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f25,f28])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
          & ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
      & ~ r2_hidden(X1,X2)
      & ~ r2_hidden(X0,X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f20,plain,
    ( ? [X0,X1,X2] :
        ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) )
   => ( k4_xboole_0(sK4,k2_tarski(sK2,sK3)) != sK4
      & ~ r2_hidden(sK3,sK4)
      & ~ r2_hidden(sK2,sK4) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( k4_xboole_0(sK4,k2_tarski(sK2,sK3)) != sK4
    & ~ r2_hidden(sK3,sK4)
    & ~ r2_hidden(sK2,sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f9,f20])).

fof(f41,plain,(
    k4_xboole_0(sK4,k2_tarski(sK2,sK3)) != sK4 ),
    inference(cnf_transformation,[],[f21])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f42,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f37,f38])).

fof(f57,plain,(
    k5_xboole_0(sK4,k3_xboole_0(sK4,k2_enumset1(sK2,sK2,sK2,sK3))) != sK4 ),
    inference(definition_unfolding,[],[f41,f28,f42])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f15,plain,(
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
    inference(nnf_transformation,[],[f8])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f17,plain,(
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
    inference(rectify,[],[f16])).

fof(f18,plain,(
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
     => ( ( ( sK1(X0,X1,X2,X3) != X2
            & sK1(X0,X1,X2,X3) != X1
            & sK1(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK1(X0,X1,X2,X3),X3) )
        & ( sK1(X0,X1,X2,X3) = X2
          | sK1(X0,X1,X2,X3) = X1
          | sK1(X0,X1,X2,X3) = X0
          | r2_hidden(sK1(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK1(X0,X1,X2,X3) != X2
              & sK1(X0,X1,X2,X3) != X1
              & sK1(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK1(X0,X1,X2,X3),X3) )
          & ( sK1(X0,X1,X2,X3) = X2
            | sK1(X0,X1,X2,X3) = X1
            | sK1(X0,X1,X2,X3) = X0
            | r2_hidden(sK1(X0,X1,X2,X3),X3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f17,f18])).

fof(f29,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f56,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f29,f38])).

fof(f67,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k2_enumset1(X0,X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f56])).

fof(f40,plain,(
    ~ r2_hidden(sK3,sK4) ),
    inference(cnf_transformation,[],[f21])).

fof(f39,plain,(
    ~ r2_hidden(sK2,sK4) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X0)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(sK0(X0,X1,X2),X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_14,negated_conjecture,
    ( k5_xboole_0(sK4,k3_xboole_0(sK4,k2_enumset1(sK2,sK2,sK2,sK3))) != sK4 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1287,plain,
    ( r2_hidden(sK0(sK4,k2_enumset1(sK2,sK2,sK2,sK3),sK4),sK4) ),
    inference(resolution,[status(thm)],[c_2,c_14])).

cnf(c_2816,plain,
    ( r2_hidden(sK0(sK4,k2_enumset1(sK2,sK2,sK2,sK3),sK4),k2_enumset1(sK2,sK2,sK2,sK3))
    | ~ r2_hidden(sK0(sK4,k2_enumset1(sK2,sK2,sK2,sK3),sK4),sK4)
    | k5_xboole_0(sK4,k3_xboole_0(sK4,k2_enumset1(sK2,sK2,sK2,sK3))) = sK4 ),
    inference(resolution,[status(thm)],[c_0,c_1287])).

cnf(c_622,plain,
    ( r2_hidden(sK0(sK4,k2_enumset1(sK2,sK2,sK2,sK3),sK4),sK4)
    | k5_xboole_0(sK4,k3_xboole_0(sK4,k2_enumset1(sK2,sK2,sK2,sK3))) = sK4 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_643,plain,
    ( r2_hidden(sK0(sK4,k2_enumset1(sK2,sK2,sK2,sK3),sK4),k2_enumset1(sK2,sK2,sK2,sK3))
    | ~ r2_hidden(sK0(sK4,k2_enumset1(sK2,sK2,sK2,sK3),sK4),sK4)
    | k5_xboole_0(sK4,k3_xboole_0(sK4,k2_enumset1(sK2,sK2,sK2,sK3))) = sK4 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_3067,plain,
    ( r2_hidden(sK0(sK4,k2_enumset1(sK2,sK2,sK2,sK3),sK4),k2_enumset1(sK2,sK2,sK2,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2816,c_14,c_622,c_643])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X3))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_3080,plain,
    ( sK0(sK4,k2_enumset1(sK2,sK2,sK2,sK3),sK4) = sK3
    | sK0(sK4,k2_enumset1(sK2,sK2,sK2,sK3),sK4) = sK2 ),
    inference(resolution,[status(thm)],[c_3067,c_13])).

cnf(c_173,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_169,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1062,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_173,c_169])).

cnf(c_3314,plain,
    ( r2_hidden(sK0(sK4,k2_enumset1(sK2,sK2,sK2,sK3),sK4),X0)
    | ~ r2_hidden(sK3,X0)
    | sK0(sK4,k2_enumset1(sK2,sK2,sK2,sK3),sK4) = sK2 ),
    inference(resolution,[status(thm)],[c_3080,c_1062])).

cnf(c_170,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_906,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_170,c_169])).

cnf(c_3341,plain,
    ( r2_hidden(sK0(sK4,k2_enumset1(sK2,sK2,sK2,sK3),sK4),X0)
    | ~ r2_hidden(sK3,X0)
    | sK2 = sK0(sK4,k2_enumset1(sK2,sK2,sK2,sK3),sK4) ),
    inference(resolution,[status(thm)],[c_3314,c_906])).

cnf(c_15,negated_conjecture,
    ( ~ r2_hidden(sK3,sK4) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_3311,plain,
    ( sK0(sK4,k2_enumset1(sK2,sK2,sK2,sK3),sK4) = sK2
    | sK3 = sK0(sK4,k2_enumset1(sK2,sK2,sK2,sK3),sK4) ),
    inference(resolution,[status(thm)],[c_3080,c_906])).

cnf(c_3324,plain,
    ( sK3 = sK0(sK4,k2_enumset1(sK2,sK2,sK2,sK3),sK4)
    | sK2 = sK0(sK4,k2_enumset1(sK2,sK2,sK2,sK3),sK4) ),
    inference(resolution,[status(thm)],[c_3311,c_906])).

cnf(c_3960,plain,
    ( ~ r2_hidden(sK0(sK4,k2_enumset1(sK2,sK2,sK2,sK3),sK4),X0)
    | r2_hidden(sK3,X0)
    | sK2 = sK0(sK4,k2_enumset1(sK2,sK2,sK2,sK3),sK4) ),
    inference(resolution,[status(thm)],[c_3324,c_1062])).

cnf(c_3962,plain,
    ( ~ r2_hidden(sK0(sK4,k2_enumset1(sK2,sK2,sK2,sK3),sK4),sK4)
    | r2_hidden(sK3,sK4)
    | sK2 = sK0(sK4,k2_enumset1(sK2,sK2,sK2,sK3),sK4) ),
    inference(instantiation,[status(thm)],[c_3960])).

cnf(c_4372,plain,
    ( sK2 = sK0(sK4,k2_enumset1(sK2,sK2,sK2,sK3),sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3341,c_15,c_14,c_622,c_3962])).

cnf(c_4383,plain,
    ( ~ r2_hidden(sK0(sK4,k2_enumset1(sK2,sK2,sK2,sK3),sK4),X0)
    | r2_hidden(sK2,X0) ),
    inference(resolution,[status(thm)],[c_4372,c_1062])).

cnf(c_4385,plain,
    ( ~ r2_hidden(sK0(sK4,k2_enumset1(sK2,sK2,sK2,sK3),sK4),sK4)
    | r2_hidden(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_4383])).

cnf(c_16,negated_conjecture,
    ( ~ r2_hidden(sK2,sK4) ),
    inference(cnf_transformation,[],[f39])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4385,c_622,c_14,c_16])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.12  % Command    : iproveropt_run.sh %d %s
% 0.11/0.33  % Computer   : n004.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 14:36:53 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.19/0.34  % Running in FOF mode
% 2.92/0.94  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.92/0.94  
% 2.92/0.94  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.92/0.94  
% 2.92/0.94  ------  iProver source info
% 2.92/0.94  
% 2.92/0.94  git: date: 2020-06-30 10:37:57 +0100
% 2.92/0.94  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.92/0.94  git: non_committed_changes: false
% 2.92/0.94  git: last_make_outside_of_git: false
% 2.92/0.94  
% 2.92/0.94  ------ 
% 2.92/0.94  ------ Parsing...
% 2.92/0.94  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.92/0.94  
% 2.92/0.94  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.92/0.94  
% 2.92/0.94  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.92/0.94  
% 2.92/0.94  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.92/0.94  ------ Proving...
% 2.92/0.94  ------ Problem Properties 
% 2.92/0.94  
% 2.92/0.94  
% 2.92/0.94  clauses                                 17
% 2.92/0.94  conjectures                             3
% 2.92/0.94  EPR                                     2
% 2.92/0.94  Horn                                    11
% 2.92/0.94  unary                                   6
% 2.92/0.94  binary                                  2
% 2.92/0.94  lits                                    41
% 2.92/0.94  lits eq                                 17
% 2.92/0.94  fd_pure                                 0
% 2.92/0.94  fd_pseudo                               0
% 2.92/0.94  fd_cond                                 0
% 2.92/0.94  fd_pseudo_cond                          7
% 2.92/0.94  AC symbols                              0
% 2.92/0.94  
% 2.92/0.94  ------ Input Options Time Limit: Unbounded
% 2.92/0.94  
% 2.92/0.94  
% 2.92/0.94  ------ 
% 2.92/0.94  Current options:
% 2.92/0.94  ------ 
% 2.92/0.94  
% 2.92/0.94  
% 2.92/0.94  
% 2.92/0.94  
% 2.92/0.94  ------ Proving...
% 2.92/0.94  
% 2.92/0.94  
% 2.92/0.94  % SZS status Theorem for theBenchmark.p
% 2.92/0.94  
% 2.92/0.94  % SZS output start CNFRefutation for theBenchmark.p
% 2.92/0.94  
% 2.92/0.94  fof(f1,axiom,(
% 2.92/0.94    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.92/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.92/0.94  
% 2.92/0.94  fof(f10,plain,(
% 2.92/0.94    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.92/0.94    inference(nnf_transformation,[],[f1])).
% 2.92/0.94  
% 2.92/0.94  fof(f11,plain,(
% 2.92/0.94    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.92/0.94    inference(flattening,[],[f10])).
% 2.92/0.94  
% 2.92/0.94  fof(f12,plain,(
% 2.92/0.94    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.92/0.94    inference(rectify,[],[f11])).
% 2.92/0.94  
% 2.92/0.94  fof(f13,plain,(
% 2.92/0.94    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 2.92/0.94    introduced(choice_axiom,[])).
% 2.92/0.94  
% 2.92/0.94  fof(f14,plain,(
% 2.92/0.94    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.92/0.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f13])).
% 2.92/0.94  
% 2.92/0.94  fof(f27,plain,(
% 2.92/0.94    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 2.92/0.94    inference(cnf_transformation,[],[f14])).
% 2.92/0.94  
% 2.92/0.94  fof(f2,axiom,(
% 2.92/0.94    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.92/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.92/0.94  
% 2.92/0.94  fof(f28,plain,(
% 2.92/0.94    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.92/0.94    inference(cnf_transformation,[],[f2])).
% 2.92/0.94  
% 2.92/0.94  fof(f43,plain,(
% 2.92/0.94    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 2.92/0.94    inference(definition_unfolding,[],[f27,f28])).
% 2.92/0.94  
% 2.92/0.94  fof(f25,plain,(
% 2.92/0.94    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 2.92/0.94    inference(cnf_transformation,[],[f14])).
% 2.92/0.94  
% 2.92/0.94  fof(f45,plain,(
% 2.92/0.94    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 2.92/0.94    inference(definition_unfolding,[],[f25,f28])).
% 2.92/0.94  
% 2.92/0.94  fof(f6,conjecture,(
% 2.92/0.94    ! [X0,X1,X2] : ~(k4_xboole_0(X2,k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 2.92/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.92/0.94  
% 2.92/0.94  fof(f7,negated_conjecture,(
% 2.92/0.94    ~! [X0,X1,X2] : ~(k4_xboole_0(X2,k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 2.92/0.94    inference(negated_conjecture,[],[f6])).
% 2.92/0.94  
% 2.92/0.94  fof(f9,plain,(
% 2.92/0.94    ? [X0,X1,X2] : (k4_xboole_0(X2,k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 2.92/0.94    inference(ennf_transformation,[],[f7])).
% 2.92/0.94  
% 2.92/0.94  fof(f20,plain,(
% 2.92/0.94    ? [X0,X1,X2] : (k4_xboole_0(X2,k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) => (k4_xboole_0(sK4,k2_tarski(sK2,sK3)) != sK4 & ~r2_hidden(sK3,sK4) & ~r2_hidden(sK2,sK4))),
% 2.92/0.94    introduced(choice_axiom,[])).
% 2.92/0.94  
% 2.92/0.94  fof(f21,plain,(
% 2.92/0.94    k4_xboole_0(sK4,k2_tarski(sK2,sK3)) != sK4 & ~r2_hidden(sK3,sK4) & ~r2_hidden(sK2,sK4)),
% 2.92/0.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f9,f20])).
% 2.92/0.94  
% 2.92/0.94  fof(f41,plain,(
% 2.92/0.94    k4_xboole_0(sK4,k2_tarski(sK2,sK3)) != sK4),
% 2.92/0.94    inference(cnf_transformation,[],[f21])).
% 2.92/0.94  
% 2.92/0.94  fof(f4,axiom,(
% 2.92/0.94    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.92/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.92/0.94  
% 2.92/0.94  fof(f37,plain,(
% 2.92/0.94    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.92/0.94    inference(cnf_transformation,[],[f4])).
% 2.92/0.94  
% 2.92/0.94  fof(f5,axiom,(
% 2.92/0.94    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.92/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.92/0.94  
% 2.92/0.94  fof(f38,plain,(
% 2.92/0.94    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.92/0.94    inference(cnf_transformation,[],[f5])).
% 2.92/0.94  
% 2.92/0.94  fof(f42,plain,(
% 2.92/0.94    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 2.92/0.94    inference(definition_unfolding,[],[f37,f38])).
% 2.92/0.94  
% 2.92/0.94  fof(f57,plain,(
% 2.92/0.94    k5_xboole_0(sK4,k3_xboole_0(sK4,k2_enumset1(sK2,sK2,sK2,sK3))) != sK4),
% 2.92/0.94    inference(definition_unfolding,[],[f41,f28,f42])).
% 2.92/0.94  
% 2.92/0.94  fof(f3,axiom,(
% 2.92/0.94    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 2.92/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.92/0.94  
% 2.92/0.94  fof(f8,plain,(
% 2.92/0.94    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 2.92/0.94    inference(ennf_transformation,[],[f3])).
% 2.92/0.94  
% 2.92/0.94  fof(f15,plain,(
% 2.92/0.94    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.92/0.94    inference(nnf_transformation,[],[f8])).
% 2.92/0.94  
% 2.92/0.94  fof(f16,plain,(
% 2.92/0.94    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.92/0.94    inference(flattening,[],[f15])).
% 2.92/0.94  
% 2.92/0.94  fof(f17,plain,(
% 2.92/0.94    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.92/0.94    inference(rectify,[],[f16])).
% 2.92/0.94  
% 2.92/0.94  fof(f18,plain,(
% 2.92/0.94    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3))))),
% 2.92/0.94    introduced(choice_axiom,[])).
% 2.92/0.94  
% 2.92/0.94  fof(f19,plain,(
% 2.92/0.94    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.92/0.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f17,f18])).
% 2.92/0.94  
% 2.92/0.94  fof(f29,plain,(
% 2.92/0.94    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 2.92/0.94    inference(cnf_transformation,[],[f19])).
% 2.92/0.94  
% 2.92/0.94  fof(f56,plain,(
% 2.92/0.94    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 2.92/0.94    inference(definition_unfolding,[],[f29,f38])).
% 2.92/0.94  
% 2.92/0.94  fof(f67,plain,(
% 2.92/0.94    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k2_enumset1(X0,X0,X1,X2))) )),
% 2.92/0.94    inference(equality_resolution,[],[f56])).
% 2.92/0.94  
% 2.92/0.94  fof(f40,plain,(
% 2.92/0.94    ~r2_hidden(sK3,sK4)),
% 2.92/0.94    inference(cnf_transformation,[],[f21])).
% 2.92/0.94  
% 2.92/0.94  fof(f39,plain,(
% 2.92/0.94    ~r2_hidden(sK2,sK4)),
% 2.92/0.94    inference(cnf_transformation,[],[f21])).
% 2.92/0.94  
% 2.92/0.94  cnf(c_0,plain,
% 2.92/0.94      ( ~ r2_hidden(sK0(X0,X1,X2),X0)
% 2.92/0.94      | ~ r2_hidden(sK0(X0,X1,X2),X2)
% 2.92/0.94      | r2_hidden(sK0(X0,X1,X2),X1)
% 2.92/0.94      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
% 2.92/0.94      inference(cnf_transformation,[],[f43]) ).
% 2.92/0.94  
% 2.92/0.94  cnf(c_2,plain,
% 2.92/0.94      ( r2_hidden(sK0(X0,X1,X2),X0)
% 2.92/0.94      | r2_hidden(sK0(X0,X1,X2),X2)
% 2.92/0.94      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
% 2.92/0.94      inference(cnf_transformation,[],[f45]) ).
% 2.92/0.94  
% 2.92/0.94  cnf(c_14,negated_conjecture,
% 2.92/0.94      ( k5_xboole_0(sK4,k3_xboole_0(sK4,k2_enumset1(sK2,sK2,sK2,sK3))) != sK4 ),
% 2.92/0.94      inference(cnf_transformation,[],[f57]) ).
% 2.92/0.94  
% 2.92/0.94  cnf(c_1287,plain,
% 2.92/0.94      ( r2_hidden(sK0(sK4,k2_enumset1(sK2,sK2,sK2,sK3),sK4),sK4) ),
% 2.92/0.94      inference(resolution,[status(thm)],[c_2,c_14]) ).
% 2.92/0.94  
% 2.92/0.94  cnf(c_2816,plain,
% 2.92/0.94      ( r2_hidden(sK0(sK4,k2_enumset1(sK2,sK2,sK2,sK3),sK4),k2_enumset1(sK2,sK2,sK2,sK3))
% 2.92/0.94      | ~ r2_hidden(sK0(sK4,k2_enumset1(sK2,sK2,sK2,sK3),sK4),sK4)
% 2.92/0.94      | k5_xboole_0(sK4,k3_xboole_0(sK4,k2_enumset1(sK2,sK2,sK2,sK3))) = sK4 ),
% 2.92/0.94      inference(resolution,[status(thm)],[c_0,c_1287]) ).
% 2.92/0.94  
% 2.92/0.94  cnf(c_622,plain,
% 2.92/0.94      ( r2_hidden(sK0(sK4,k2_enumset1(sK2,sK2,sK2,sK3),sK4),sK4)
% 2.92/0.94      | k5_xboole_0(sK4,k3_xboole_0(sK4,k2_enumset1(sK2,sK2,sK2,sK3))) = sK4 ),
% 2.92/0.94      inference(instantiation,[status(thm)],[c_2]) ).
% 2.92/0.94  
% 2.92/0.94  cnf(c_643,plain,
% 2.92/0.94      ( r2_hidden(sK0(sK4,k2_enumset1(sK2,sK2,sK2,sK3),sK4),k2_enumset1(sK2,sK2,sK2,sK3))
% 2.92/0.94      | ~ r2_hidden(sK0(sK4,k2_enumset1(sK2,sK2,sK2,sK3),sK4),sK4)
% 2.92/0.94      | k5_xboole_0(sK4,k3_xboole_0(sK4,k2_enumset1(sK2,sK2,sK2,sK3))) = sK4 ),
% 2.92/0.94      inference(instantiation,[status(thm)],[c_0]) ).
% 2.92/0.94  
% 2.92/0.94  cnf(c_3067,plain,
% 2.92/0.94      ( r2_hidden(sK0(sK4,k2_enumset1(sK2,sK2,sK2,sK3),sK4),k2_enumset1(sK2,sK2,sK2,sK3)) ),
% 2.92/0.94      inference(global_propositional_subsumption,
% 2.92/0.94                [status(thm)],
% 2.92/0.94                [c_2816,c_14,c_622,c_643]) ).
% 2.92/0.94  
% 2.92/0.94  cnf(c_13,plain,
% 2.92/0.94      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X3))
% 2.92/0.94      | X0 = X1
% 2.92/0.94      | X0 = X2
% 2.92/0.94      | X0 = X3 ),
% 2.92/0.94      inference(cnf_transformation,[],[f67]) ).
% 2.92/0.94  
% 2.92/0.94  cnf(c_3080,plain,
% 2.92/0.94      ( sK0(sK4,k2_enumset1(sK2,sK2,sK2,sK3),sK4) = sK3
% 2.92/0.94      | sK0(sK4,k2_enumset1(sK2,sK2,sK2,sK3),sK4) = sK2 ),
% 2.92/0.94      inference(resolution,[status(thm)],[c_3067,c_13]) ).
% 2.92/0.94  
% 2.92/0.94  cnf(c_173,plain,
% 2.92/0.94      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.92/0.94      theory(equality) ).
% 2.92/0.94  
% 2.92/0.94  cnf(c_169,plain,( X0 = X0 ),theory(equality) ).
% 2.92/0.94  
% 2.92/0.94  cnf(c_1062,plain,
% 2.92/0.94      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X1) | X2 != X0 ),
% 2.92/0.94      inference(resolution,[status(thm)],[c_173,c_169]) ).
% 2.92/0.94  
% 2.92/0.94  cnf(c_3314,plain,
% 2.92/0.94      ( r2_hidden(sK0(sK4,k2_enumset1(sK2,sK2,sK2,sK3),sK4),X0)
% 2.92/0.94      | ~ r2_hidden(sK3,X0)
% 2.92/0.94      | sK0(sK4,k2_enumset1(sK2,sK2,sK2,sK3),sK4) = sK2 ),
% 2.92/0.94      inference(resolution,[status(thm)],[c_3080,c_1062]) ).
% 2.92/0.94  
% 2.92/0.94  cnf(c_170,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.92/0.94  
% 2.92/0.94  cnf(c_906,plain,
% 2.92/0.94      ( X0 != X1 | X1 = X0 ),
% 2.92/0.94      inference(resolution,[status(thm)],[c_170,c_169]) ).
% 2.92/0.94  
% 2.92/0.94  cnf(c_3341,plain,
% 2.92/0.94      ( r2_hidden(sK0(sK4,k2_enumset1(sK2,sK2,sK2,sK3),sK4),X0)
% 2.92/0.94      | ~ r2_hidden(sK3,X0)
% 2.92/0.94      | sK2 = sK0(sK4,k2_enumset1(sK2,sK2,sK2,sK3),sK4) ),
% 2.92/0.94      inference(resolution,[status(thm)],[c_3314,c_906]) ).
% 2.92/0.94  
% 2.92/0.94  cnf(c_15,negated_conjecture,
% 2.92/0.94      ( ~ r2_hidden(sK3,sK4) ),
% 2.92/0.94      inference(cnf_transformation,[],[f40]) ).
% 2.92/0.94  
% 2.92/0.94  cnf(c_3311,plain,
% 2.92/0.94      ( sK0(sK4,k2_enumset1(sK2,sK2,sK2,sK3),sK4) = sK2
% 2.92/0.94      | sK3 = sK0(sK4,k2_enumset1(sK2,sK2,sK2,sK3),sK4) ),
% 2.92/0.94      inference(resolution,[status(thm)],[c_3080,c_906]) ).
% 2.92/0.94  
% 2.92/0.94  cnf(c_3324,plain,
% 2.92/0.94      ( sK3 = sK0(sK4,k2_enumset1(sK2,sK2,sK2,sK3),sK4)
% 2.92/0.94      | sK2 = sK0(sK4,k2_enumset1(sK2,sK2,sK2,sK3),sK4) ),
% 2.92/0.94      inference(resolution,[status(thm)],[c_3311,c_906]) ).
% 2.92/0.94  
% 2.92/0.94  cnf(c_3960,plain,
% 2.92/0.94      ( ~ r2_hidden(sK0(sK4,k2_enumset1(sK2,sK2,sK2,sK3),sK4),X0)
% 2.92/0.94      | r2_hidden(sK3,X0)
% 2.92/0.94      | sK2 = sK0(sK4,k2_enumset1(sK2,sK2,sK2,sK3),sK4) ),
% 2.92/0.94      inference(resolution,[status(thm)],[c_3324,c_1062]) ).
% 2.92/0.94  
% 2.92/0.94  cnf(c_3962,plain,
% 2.92/0.94      ( ~ r2_hidden(sK0(sK4,k2_enumset1(sK2,sK2,sK2,sK3),sK4),sK4)
% 2.92/0.94      | r2_hidden(sK3,sK4)
% 2.92/0.94      | sK2 = sK0(sK4,k2_enumset1(sK2,sK2,sK2,sK3),sK4) ),
% 2.92/0.94      inference(instantiation,[status(thm)],[c_3960]) ).
% 2.92/0.94  
% 2.92/0.94  cnf(c_4372,plain,
% 2.92/0.94      ( sK2 = sK0(sK4,k2_enumset1(sK2,sK2,sK2,sK3),sK4) ),
% 2.92/0.94      inference(global_propositional_subsumption,
% 2.92/0.94                [status(thm)],
% 2.92/0.94                [c_3341,c_15,c_14,c_622,c_3962]) ).
% 2.92/0.94  
% 2.92/0.94  cnf(c_4383,plain,
% 2.92/0.94      ( ~ r2_hidden(sK0(sK4,k2_enumset1(sK2,sK2,sK2,sK3),sK4),X0)
% 2.92/0.94      | r2_hidden(sK2,X0) ),
% 2.92/0.94      inference(resolution,[status(thm)],[c_4372,c_1062]) ).
% 2.92/0.94  
% 2.92/0.94  cnf(c_4385,plain,
% 2.92/0.94      ( ~ r2_hidden(sK0(sK4,k2_enumset1(sK2,sK2,sK2,sK3),sK4),sK4)
% 2.92/0.94      | r2_hidden(sK2,sK4) ),
% 2.92/0.94      inference(instantiation,[status(thm)],[c_4383]) ).
% 2.92/0.94  
% 2.92/0.94  cnf(c_16,negated_conjecture,
% 2.92/0.94      ( ~ r2_hidden(sK2,sK4) ),
% 2.92/0.94      inference(cnf_transformation,[],[f39]) ).
% 2.92/0.94  
% 2.92/0.94  cnf(contradiction,plain,
% 2.92/0.94      ( $false ),
% 2.92/0.94      inference(minisat,[status(thm)],[c_4385,c_622,c_14,c_16]) ).
% 2.92/0.94  
% 2.92/0.94  
% 2.92/0.94  % SZS output end CNFRefutation for theBenchmark.p
% 2.92/0.94  
% 2.92/0.94  ------                               Statistics
% 2.92/0.94  
% 2.92/0.94  ------ Selected
% 2.92/0.94  
% 2.92/0.94  total_time:                             0.126
% 2.92/0.94  
%------------------------------------------------------------------------------
