%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:36:23 EST 2020

% Result     : Theorem 3.78s
% Output     : CNFRefutation 3.78s
% Verified   : 
% Statistics : Number of formulae       :   96 (1052 expanded)
%              Number of clauses        :   45 ( 170 expanded)
%              Number of leaves         :   12 ( 282 expanded)
%              Depth                    :   21
%              Number of atoms          :  263 (2688 expanded)
%              Number of equality atoms :  132 (1257 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f24,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f103,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f26,conjecture,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
      <=> ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f26])).

fof(f37,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
    <~> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f58,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,X2)
        | r2_hidden(X0,X2)
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f59,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,X2)
        | r2_hidden(X0,X2)
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) ) ) ),
    inference(flattening,[],[f58])).

fof(f60,plain,
    ( ? [X0,X1,X2] :
        ( ( r2_hidden(X1,X2)
          | r2_hidden(X0,X2)
          | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1) )
        & ( ( ~ r2_hidden(X1,X2)
            & ~ r2_hidden(X0,X2) )
          | k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) ) )
   => ( ( r2_hidden(sK4,sK5)
        | r2_hidden(sK3,sK5)
        | k4_xboole_0(k2_tarski(sK3,sK4),sK5) != k2_tarski(sK3,sK4) )
      & ( ( ~ r2_hidden(sK4,sK5)
          & ~ r2_hidden(sK3,sK5) )
        | k4_xboole_0(k2_tarski(sK3,sK4),sK5) = k2_tarski(sK3,sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,
    ( ( r2_hidden(sK4,sK5)
      | r2_hidden(sK3,sK5)
      | k4_xboole_0(k2_tarski(sK3,sK4),sK5) != k2_tarski(sK3,sK4) )
    & ( ( ~ r2_hidden(sK4,sK5)
        & ~ r2_hidden(sK3,sK5) )
      | k4_xboole_0(k2_tarski(sK3,sK4),sK5) = k2_tarski(sK3,sK4) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f59,f60])).

fof(f108,plain,
    ( ~ r2_hidden(sK3,sK5)
    | k4_xboole_0(k2_tarski(sK3,sK4),sK5) = k2_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f61])).

fof(f18,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f93,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f18])).

fof(f16,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f88,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f111,plain,(
    ! [X0,X1] : k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f93,f88])).

fof(f136,plain,
    ( ~ r2_hidden(sK3,sK5)
    | k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),sK5) = k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))) ),
    inference(definition_unfolding,[],[f108,f111,f111])).

fof(f109,plain,
    ( ~ r2_hidden(sK4,sK5)
    | k4_xboole_0(k2_tarski(sK3,sK4),sK5) = k2_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f61])).

fof(f135,plain,
    ( ~ r2_hidden(sK4,sK5)
    | k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),sK5) = k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))) ),
    inference(definition_unfolding,[],[f109,f111,f111])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_xboole_0(k2_tarski(X0,X2),X1)
        & ~ r2_hidden(X2,X1)
        & ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X2),k1_tarski(X0))),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f96,f111])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)
    <=> ( ( X0 = X1
          | r2_hidden(X1,X2) )
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)
        | ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)
        | ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0) ) ) ),
    inference(flattening,[],[f56])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f133,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | k4_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))),X2) != k1_tarski(X0) ) ),
    inference(definition_unfolding,[],[f104,f111])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ~ ( r2_hidden(X0,X2)
        & r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))),X2) ) ),
    inference(definition_unfolding,[],[f95,f111])).

fof(f110,plain,
    ( r2_hidden(sK4,sK5)
    | r2_hidden(sK3,sK5)
    | k4_xboole_0(k2_tarski(sK3,sK4),sK5) != k2_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f61])).

fof(f134,plain,
    ( r2_hidden(sK4,sK5)
    | r2_hidden(sK3,sK5)
    | k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),sK5) != k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))) ),
    inference(definition_unfolding,[],[f110,f111,f111])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f50,plain,(
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
    inference(rectify,[],[f49])).

fof(f51,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK2(X0,X1) != X0
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( sK2(X0,X1) = X0
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK2(X0,X1) != X0
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( sK2(X0,X1) = X0
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f50,f51])).

fof(f89,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f144,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f89])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)
      | ~ r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f131,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))),X2) = k1_tarski(X0)
      | ~ r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f106,f111])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f80,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f121,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) ),
    inference(definition_unfolding,[],[f80,f88])).

cnf(c_37,plain,
    ( r2_hidden(X0,X1)
    | k4_xboole_0(X1,k1_tarski(X0)) = X1 ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1472,plain,
    ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    | r2_hidden(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_45,negated_conjecture,
    ( ~ r2_hidden(sK3,sK5)
    | k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),sK5) = k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))) ),
    inference(cnf_transformation,[],[f136])).

cnf(c_1464,plain,
    ( k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),sK5) = k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))
    | r2_hidden(sK3,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_4729,plain,
    ( k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),sK5) = k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))
    | k4_xboole_0(sK5,k1_tarski(sK3)) = sK5 ),
    inference(superposition,[status(thm)],[c_1472,c_1464])).

cnf(c_44,negated_conjecture,
    ( ~ r2_hidden(sK4,sK5)
    | k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),sK5) = k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))) ),
    inference(cnf_transformation,[],[f135])).

cnf(c_23,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1818,plain,
    ( ~ r1_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),sK5)
    | k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),sK5) = k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_31,plain,
    ( r1_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))),X2)
    | r2_hidden(X0,X2)
    | r2_hidden(X1,X2) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_2031,plain,
    ( r1_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),sK5)
    | r2_hidden(sK3,sK5)
    | r2_hidden(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_2403,negated_conjecture,
    ( k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),sK5) = k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_45,c_44,c_1818,c_2031])).

cnf(c_4753,plain,
    ( k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),sK5) = k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4729,c_45,c_44,c_1818,c_2031])).

cnf(c_42,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X2),k1_tarski(X0))),X1) != k1_tarski(X0) ),
    inference(cnf_transformation,[],[f133])).

cnf(c_1467,plain,
    ( k4_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))),X2) != k1_tarski(X0)
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_4769,plain,
    ( k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))) != k1_tarski(sK3)
    | r2_hidden(sK3,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4753,c_1467])).

cnf(c_22,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) != X0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_2022,plain,
    ( r1_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),sK5)
    | k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),sK5) != k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_2029,plain,
    ( k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),sK5) != k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))
    | r1_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2022])).

cnf(c_30,plain,
    ( ~ r1_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))),X2)
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f126])).

cnf(c_4832,plain,
    ( ~ r1_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),sK5)
    | ~ r2_hidden(sK3,sK5) ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_4833,plain,
    ( r1_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),sK5) != iProver_top
    | r2_hidden(sK3,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4832])).

cnf(c_5824,plain,
    ( r2_hidden(sK3,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4769,c_45,c_44,c_1818,c_2029,c_2031,c_4833])).

cnf(c_5829,plain,
    ( k4_xboole_0(sK5,k1_tarski(sK3)) = sK5 ),
    inference(superposition,[status(thm)],[c_1472,c_5824])).

cnf(c_43,negated_conjecture,
    ( r2_hidden(sK3,sK5)
    | r2_hidden(sK4,sK5)
    | k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),sK5) != k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))) ),
    inference(cnf_transformation,[],[f134])).

cnf(c_1466,plain,
    ( k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),sK5) != k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))
    | r2_hidden(sK3,sK5) = iProver_top
    | r2_hidden(sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_4756,plain,
    ( k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))) != k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))
    | r2_hidden(sK3,sK5) = iProver_top
    | r2_hidden(sK4,sK5) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4753,c_1466])).

cnf(c_5024,plain,
    ( r2_hidden(sK3,sK5) = iProver_top
    | r2_hidden(sK4,sK5) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4756])).

cnf(c_28,plain,
    ( ~ r2_hidden(X0,k1_tarski(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f144])).

cnf(c_1902,plain,
    ( ~ r2_hidden(k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),sK5),k1_tarski(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))))
    | r2_hidden(sK3,sK5)
    | r2_hidden(sK4,sK5) ),
    inference(resolution,[status(thm)],[c_28,c_43])).

cnf(c_2187,plain,
    ( r2_hidden(sK3,sK5)
    | r2_hidden(sK4,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1902,c_45,c_44,c_43,c_1818,c_2031])).

cnf(c_38,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_xboole_0(X1,k1_tarski(X0)) != X1 ),
    inference(cnf_transformation,[],[f102])).

cnf(c_2306,plain,
    ( ~ r2_hidden(sK4,sK5)
    | k4_xboole_0(sK5,k1_tarski(sK4)) != sK5 ),
    inference(instantiation,[status(thm)],[c_38])).

cnf(c_4260,plain,
    ( r2_hidden(sK4,sK5)
    | k4_xboole_0(sK5,k1_tarski(sK4)) = sK5 ),
    inference(instantiation,[status(thm)],[c_37])).

cnf(c_4261,plain,
    ( k4_xboole_0(sK5,k1_tarski(sK4)) = sK5
    | r2_hidden(sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4260])).

cnf(c_5026,plain,
    ( r2_hidden(sK4,sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5024,c_45,c_44,c_43,c_1818,c_2022,c_2031,c_2306,c_4261,c_4832])).

cnf(c_40,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X0),k1_tarski(X2))),X1) = k1_tarski(X2) ),
    inference(cnf_transformation,[],[f131])).

cnf(c_1469,plain,
    ( k4_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))),X2) = k1_tarski(X0)
    | r2_hidden(X1,X2) != iProver_top
    | r2_hidden(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_5031,plain,
    ( k4_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(sK4),k1_tarski(X0))),sK5) = k1_tarski(X0)
    | r2_hidden(X0,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_5026,c_1469])).

cnf(c_8701,plain,
    ( k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),sK5) = k1_tarski(sK3) ),
    inference(superposition,[status(thm)],[c_5031,c_5824])).

cnf(c_9646,plain,
    ( k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))) = k1_tarski(sK3) ),
    inference(demodulation,[status(thm)],[c_8701,c_4753])).

cnf(c_18,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_9975,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k1_tarski(sK3)),k1_tarski(sK4)) = k4_xboole_0(X0,k1_tarski(sK3)) ),
    inference(superposition,[status(thm)],[c_9646,c_18])).

cnf(c_10742,plain,
    ( k4_xboole_0(sK5,k1_tarski(sK3)) = k4_xboole_0(sK5,k1_tarski(sK4)) ),
    inference(superposition,[status(thm)],[c_5829,c_9975])).

cnf(c_10807,plain,
    ( k4_xboole_0(sK5,k1_tarski(sK4)) = sK5 ),
    inference(light_normalisation,[status(thm)],[c_10742,c_5829])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10807,c_4832,c_2403,c_2306,c_2022,c_43])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.11  % Command    : iproveropt_run.sh %d %s
% 0.10/0.32  % Computer   : n009.cluster.edu
% 0.10/0.32  % Model      : x86_64 x86_64
% 0.10/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.32  % Memory     : 8042.1875MB
% 0.10/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.32  % CPULimit   : 60
% 0.10/0.32  % WCLimit    : 600
% 0.10/0.32  % DateTime   : Tue Dec  1 18:03:11 EST 2020
% 0.10/0.32  % CPUTime    : 
% 0.10/0.32  % Running in FOF mode
% 3.78/0.96  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.78/0.96  
% 3.78/0.96  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.78/0.96  
% 3.78/0.96  ------  iProver source info
% 3.78/0.96  
% 3.78/0.96  git: date: 2020-06-30 10:37:57 +0100
% 3.78/0.96  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.78/0.96  git: non_committed_changes: false
% 3.78/0.96  git: last_make_outside_of_git: false
% 3.78/0.96  
% 3.78/0.96  ------ 
% 3.78/0.96  ------ Parsing...
% 3.78/0.96  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.78/0.96  
% 3.78/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 3.78/0.96  
% 3.78/0.96  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.78/0.96  
% 3.78/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.78/0.96  ------ Proving...
% 3.78/0.96  ------ Problem Properties 
% 3.78/0.96  
% 3.78/0.96  
% 3.78/0.96  clauses                                 45
% 3.78/0.96  conjectures                             3
% 3.78/0.96  EPR                                     3
% 3.78/0.96  Horn                                    32
% 3.78/0.96  unary                                   12
% 3.78/0.96  binary                                  18
% 3.78/0.96  lits                                    94
% 3.78/0.96  lits eq                                 35
% 3.78/0.96  fd_pure                                 0
% 3.78/0.96  fd_pseudo                               0
% 3.78/0.96  fd_cond                                 0
% 3.78/0.96  fd_pseudo_cond                          8
% 3.78/0.96  AC symbols                              0
% 3.78/0.96  
% 3.78/0.96  ------ Input Options Time Limit: Unbounded
% 3.78/0.96  
% 3.78/0.96  
% 3.78/0.96  ------ 
% 3.78/0.96  Current options:
% 3.78/0.96  ------ 
% 3.78/0.96  
% 3.78/0.96  
% 3.78/0.96  
% 3.78/0.96  
% 3.78/0.96  ------ Proving...
% 3.78/0.96  
% 3.78/0.96  
% 3.78/0.96  % SZS status Theorem for theBenchmark.p
% 3.78/0.96  
% 3.78/0.96  % SZS output start CNFRefutation for theBenchmark.p
% 3.78/0.96  
% 3.78/0.96  fof(f24,axiom,(
% 3.78/0.96    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 3.78/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.78/0.96  
% 3.78/0.96  fof(f55,plain,(
% 3.78/0.96    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 3.78/0.96    inference(nnf_transformation,[],[f24])).
% 3.78/0.96  
% 3.78/0.96  fof(f103,plain,(
% 3.78/0.96    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 3.78/0.96    inference(cnf_transformation,[],[f55])).
% 3.78/0.96  
% 3.78/0.96  fof(f26,conjecture,(
% 3.78/0.96    ! [X0,X1,X2] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 3.78/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.78/0.96  
% 3.78/0.96  fof(f27,negated_conjecture,(
% 3.78/0.96    ~! [X0,X1,X2] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 3.78/0.96    inference(negated_conjecture,[],[f26])).
% 3.78/0.96  
% 3.78/0.96  fof(f37,plain,(
% 3.78/0.96    ? [X0,X1,X2] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) <~> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 3.78/0.96    inference(ennf_transformation,[],[f27])).
% 3.78/0.96  
% 3.78/0.96  fof(f58,plain,(
% 3.78/0.96    ? [X0,X1,X2] : (((r2_hidden(X1,X2) | r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)))),
% 3.78/0.96    inference(nnf_transformation,[],[f37])).
% 3.78/0.96  
% 3.78/0.96  fof(f59,plain,(
% 3.78/0.96    ? [X0,X1,X2] : ((r2_hidden(X1,X2) | r2_hidden(X0,X2) | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)))),
% 3.78/0.96    inference(flattening,[],[f58])).
% 3.78/0.96  
% 3.78/0.96  fof(f60,plain,(
% 3.78/0.96    ? [X0,X1,X2] : ((r2_hidden(X1,X2) | r2_hidden(X0,X2) | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1))) => ((r2_hidden(sK4,sK5) | r2_hidden(sK3,sK5) | k4_xboole_0(k2_tarski(sK3,sK4),sK5) != k2_tarski(sK3,sK4)) & ((~r2_hidden(sK4,sK5) & ~r2_hidden(sK3,sK5)) | k4_xboole_0(k2_tarski(sK3,sK4),sK5) = k2_tarski(sK3,sK4)))),
% 3.78/0.96    introduced(choice_axiom,[])).
% 3.78/0.96  
% 3.78/0.96  fof(f61,plain,(
% 3.78/0.96    (r2_hidden(sK4,sK5) | r2_hidden(sK3,sK5) | k4_xboole_0(k2_tarski(sK3,sK4),sK5) != k2_tarski(sK3,sK4)) & ((~r2_hidden(sK4,sK5) & ~r2_hidden(sK3,sK5)) | k4_xboole_0(k2_tarski(sK3,sK4),sK5) = k2_tarski(sK3,sK4))),
% 3.78/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f59,f60])).
% 3.78/0.96  
% 3.78/0.96  fof(f108,plain,(
% 3.78/0.96    ~r2_hidden(sK3,sK5) | k4_xboole_0(k2_tarski(sK3,sK4),sK5) = k2_tarski(sK3,sK4)),
% 3.78/0.96    inference(cnf_transformation,[],[f61])).
% 3.78/0.96  
% 3.78/0.96  fof(f18,axiom,(
% 3.78/0.96    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)),
% 3.78/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.78/0.96  
% 3.78/0.96  fof(f93,plain,(
% 3.78/0.96    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)) )),
% 3.78/0.96    inference(cnf_transformation,[],[f18])).
% 3.78/0.96  
% 3.78/0.96  fof(f16,axiom,(
% 3.78/0.96    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.78/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.78/0.96  
% 3.78/0.96  fof(f88,plain,(
% 3.78/0.96    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.78/0.96    inference(cnf_transformation,[],[f16])).
% 3.78/0.96  
% 3.78/0.96  fof(f111,plain,(
% 3.78/0.96    ( ! [X0,X1] : (k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))) = k2_tarski(X0,X1)) )),
% 3.78/0.96    inference(definition_unfolding,[],[f93,f88])).
% 3.78/0.96  
% 3.78/0.96  fof(f136,plain,(
% 3.78/0.96    ~r2_hidden(sK3,sK5) | k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),sK5) = k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),
% 3.78/0.96    inference(definition_unfolding,[],[f108,f111,f111])).
% 3.78/0.96  
% 3.78/0.96  fof(f109,plain,(
% 3.78/0.96    ~r2_hidden(sK4,sK5) | k4_xboole_0(k2_tarski(sK3,sK4),sK5) = k2_tarski(sK3,sK4)),
% 3.78/0.96    inference(cnf_transformation,[],[f61])).
% 3.78/0.96  
% 3.78/0.96  fof(f135,plain,(
% 3.78/0.96    ~r2_hidden(sK4,sK5) | k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),sK5) = k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),
% 3.78/0.96    inference(definition_unfolding,[],[f109,f111,f111])).
% 3.78/0.96  
% 3.78/0.96  fof(f14,axiom,(
% 3.78/0.96    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 3.78/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.78/0.96  
% 3.78/0.96  fof(f48,plain,(
% 3.78/0.96    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 3.78/0.96    inference(nnf_transformation,[],[f14])).
% 3.78/0.96  
% 3.78/0.96  fof(f85,plain,(
% 3.78/0.96    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 3.78/0.96    inference(cnf_transformation,[],[f48])).
% 3.78/0.96  
% 3.78/0.96  fof(f21,axiom,(
% 3.78/0.96    ! [X0,X1,X2] : ~(~r1_xboole_0(k2_tarski(X0,X2),X1) & ~r2_hidden(X2,X1) & ~r2_hidden(X0,X1))),
% 3.78/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.78/0.96  
% 3.78/0.96  fof(f34,plain,(
% 3.78/0.96    ! [X0,X1,X2] : (r1_xboole_0(k2_tarski(X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1))),
% 3.78/0.96    inference(ennf_transformation,[],[f21])).
% 3.78/0.96  
% 3.78/0.96  fof(f96,plain,(
% 3.78/0.96    ( ! [X2,X0,X1] : (r1_xboole_0(k2_tarski(X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1)) )),
% 3.78/0.96    inference(cnf_transformation,[],[f34])).
% 3.78/0.96  
% 3.78/0.96  fof(f127,plain,(
% 3.78/0.96    ( ! [X2,X0,X1] : (r1_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X2),k1_tarski(X0))),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1)) )),
% 3.78/0.96    inference(definition_unfolding,[],[f96,f111])).
% 3.78/0.96  
% 3.78/0.96  fof(f25,axiom,(
% 3.78/0.96    ! [X0,X1,X2] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0) <=> ((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)))),
% 3.78/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.78/0.96  
% 3.78/0.96  fof(f56,plain,(
% 3.78/0.96    ! [X0,X1,X2] : ((k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0) | ((X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2))) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0)))),
% 3.78/0.96    inference(nnf_transformation,[],[f25])).
% 3.78/0.96  
% 3.78/0.96  fof(f57,plain,(
% 3.78/0.96    ! [X0,X1,X2] : ((k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0) | (X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2)) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0)))),
% 3.78/0.96    inference(flattening,[],[f56])).
% 3.78/0.96  
% 3.78/0.96  fof(f104,plain,(
% 3.78/0.96    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0)) )),
% 3.78/0.96    inference(cnf_transformation,[],[f57])).
% 3.78/0.96  
% 3.78/0.96  fof(f133,plain,(
% 3.78/0.96    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | k4_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))),X2) != k1_tarski(X0)) )),
% 3.78/0.96    inference(definition_unfolding,[],[f104,f111])).
% 3.78/0.96  
% 3.78/0.96  fof(f86,plain,(
% 3.78/0.96    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 3.78/0.96    inference(cnf_transformation,[],[f48])).
% 3.78/0.96  
% 3.78/0.96  fof(f20,axiom,(
% 3.78/0.96    ! [X0,X1,X2] : ~(r2_hidden(X0,X2) & r1_xboole_0(k2_tarski(X0,X1),X2))),
% 3.78/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.78/0.96  
% 3.78/0.96  fof(f33,plain,(
% 3.78/0.96    ! [X0,X1,X2] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2))),
% 3.78/0.96    inference(ennf_transformation,[],[f20])).
% 3.78/0.96  
% 3.78/0.96  fof(f95,plain,(
% 3.78/0.96    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2)) )),
% 3.78/0.96    inference(cnf_transformation,[],[f33])).
% 3.78/0.96  
% 3.78/0.96  fof(f126,plain,(
% 3.78/0.96    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))),X2)) )),
% 3.78/0.96    inference(definition_unfolding,[],[f95,f111])).
% 3.78/0.96  
% 3.78/0.96  fof(f110,plain,(
% 3.78/0.96    r2_hidden(sK4,sK5) | r2_hidden(sK3,sK5) | k4_xboole_0(k2_tarski(sK3,sK4),sK5) != k2_tarski(sK3,sK4)),
% 3.78/0.96    inference(cnf_transformation,[],[f61])).
% 3.78/0.96  
% 3.78/0.96  fof(f134,plain,(
% 3.78/0.96    r2_hidden(sK4,sK5) | r2_hidden(sK3,sK5) | k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),sK5) != k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))),
% 3.78/0.96    inference(definition_unfolding,[],[f110,f111,f111])).
% 3.78/0.96  
% 3.78/0.96  fof(f17,axiom,(
% 3.78/0.96    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 3.78/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.78/0.96  
% 3.78/0.96  fof(f49,plain,(
% 3.78/0.96    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 3.78/0.96    inference(nnf_transformation,[],[f17])).
% 3.78/0.96  
% 3.78/0.96  fof(f50,plain,(
% 3.78/0.96    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.78/0.96    inference(rectify,[],[f49])).
% 3.78/0.96  
% 3.78/0.96  fof(f51,plain,(
% 3.78/0.96    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 3.78/0.96    introduced(choice_axiom,[])).
% 3.78/0.96  
% 3.78/0.96  fof(f52,plain,(
% 3.78/0.96    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.78/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f50,f51])).
% 3.78/0.96  
% 3.78/0.96  fof(f89,plain,(
% 3.78/0.96    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 3.78/0.96    inference(cnf_transformation,[],[f52])).
% 3.78/0.96  
% 3.78/0.96  fof(f144,plain,(
% 3.78/0.96    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k1_tarski(X0))) )),
% 3.78/0.96    inference(equality_resolution,[],[f89])).
% 3.78/0.96  
% 3.78/0.96  fof(f102,plain,(
% 3.78/0.96    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) )),
% 3.78/0.96    inference(cnf_transformation,[],[f55])).
% 3.78/0.96  
% 3.78/0.96  fof(f106,plain,(
% 3.78/0.96    ( ! [X2,X0,X1] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0) | ~r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 3.78/0.96    inference(cnf_transformation,[],[f57])).
% 3.78/0.96  
% 3.78/0.96  fof(f131,plain,(
% 3.78/0.96    ( ! [X2,X0,X1] : (k4_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))),X2) = k1_tarski(X0) | ~r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 3.78/0.96    inference(definition_unfolding,[],[f106,f111])).
% 3.78/0.96  
% 3.78/0.96  fof(f9,axiom,(
% 3.78/0.96    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 3.78/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.78/0.96  
% 3.78/0.96  fof(f80,plain,(
% 3.78/0.96    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 3.78/0.96    inference(cnf_transformation,[],[f9])).
% 3.78/0.96  
% 3.78/0.96  fof(f121,plain,(
% 3.78/0.96    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1)))) )),
% 3.78/0.96    inference(definition_unfolding,[],[f80,f88])).
% 3.78/0.96  
% 3.78/0.96  cnf(c_37,plain,
% 3.78/0.96      ( r2_hidden(X0,X1) | k4_xboole_0(X1,k1_tarski(X0)) = X1 ),
% 3.78/0.96      inference(cnf_transformation,[],[f103]) ).
% 3.78/0.96  
% 3.78/0.96  cnf(c_1472,plain,
% 3.78/0.96      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
% 3.78/0.96      | r2_hidden(X1,X0) = iProver_top ),
% 3.78/0.96      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.78/0.96  
% 3.78/0.96  cnf(c_45,negated_conjecture,
% 3.78/0.96      ( ~ r2_hidden(sK3,sK5)
% 3.78/0.96      | k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),sK5) = k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))) ),
% 3.78/0.96      inference(cnf_transformation,[],[f136]) ).
% 3.78/0.96  
% 3.78/0.96  cnf(c_1464,plain,
% 3.78/0.96      ( k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),sK5) = k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))
% 3.78/0.96      | r2_hidden(sK3,sK5) != iProver_top ),
% 3.78/0.96      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 3.78/0.96  
% 3.78/0.96  cnf(c_4729,plain,
% 3.78/0.96      ( k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),sK5) = k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))
% 3.78/0.96      | k4_xboole_0(sK5,k1_tarski(sK3)) = sK5 ),
% 3.78/0.96      inference(superposition,[status(thm)],[c_1472,c_1464]) ).
% 3.78/0.96  
% 3.78/0.96  cnf(c_44,negated_conjecture,
% 3.78/0.96      ( ~ r2_hidden(sK4,sK5)
% 3.78/0.96      | k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),sK5) = k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))) ),
% 3.78/0.96      inference(cnf_transformation,[],[f135]) ).
% 3.78/0.96  
% 3.78/0.96  cnf(c_23,plain,
% 3.78/0.96      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 3.78/0.96      inference(cnf_transformation,[],[f85]) ).
% 3.78/0.96  
% 3.78/0.96  cnf(c_1818,plain,
% 3.78/0.96      ( ~ r1_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),sK5)
% 3.78/0.96      | k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),sK5) = k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))) ),
% 3.78/0.96      inference(instantiation,[status(thm)],[c_23]) ).
% 3.78/0.96  
% 3.78/0.96  cnf(c_31,plain,
% 3.78/0.96      ( r1_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))),X2)
% 3.78/0.96      | r2_hidden(X0,X2)
% 3.78/0.96      | r2_hidden(X1,X2) ),
% 3.78/0.96      inference(cnf_transformation,[],[f127]) ).
% 3.78/0.96  
% 3.78/0.96  cnf(c_2031,plain,
% 3.78/0.96      ( r1_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),sK5)
% 3.78/0.96      | r2_hidden(sK3,sK5)
% 3.78/0.96      | r2_hidden(sK4,sK5) ),
% 3.78/0.96      inference(instantiation,[status(thm)],[c_31]) ).
% 3.78/0.96  
% 3.78/0.96  cnf(c_2403,negated_conjecture,
% 3.78/0.96      ( k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),sK5) = k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))) ),
% 3.78/0.96      inference(global_propositional_subsumption,
% 3.78/0.96                [status(thm)],
% 3.78/0.96                [c_45,c_44,c_1818,c_2031]) ).
% 3.78/0.96  
% 3.78/0.96  cnf(c_4753,plain,
% 3.78/0.96      ( k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),sK5) = k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))) ),
% 3.78/0.96      inference(global_propositional_subsumption,
% 3.78/0.96                [status(thm)],
% 3.78/0.96                [c_4729,c_45,c_44,c_1818,c_2031]) ).
% 3.78/0.96  
% 3.78/0.96  cnf(c_42,plain,
% 3.78/0.96      ( ~ r2_hidden(X0,X1)
% 3.78/0.96      | k4_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X2),k1_tarski(X0))),X1) != k1_tarski(X0) ),
% 3.78/0.96      inference(cnf_transformation,[],[f133]) ).
% 3.78/0.96  
% 3.78/0.96  cnf(c_1467,plain,
% 3.78/0.96      ( k4_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))),X2) != k1_tarski(X0)
% 3.78/0.96      | r2_hidden(X0,X2) != iProver_top ),
% 3.78/0.96      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 3.78/0.96  
% 3.78/0.96  cnf(c_4769,plain,
% 3.78/0.96      ( k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))) != k1_tarski(sK3)
% 3.78/0.96      | r2_hidden(sK3,sK5) != iProver_top ),
% 3.78/0.96      inference(superposition,[status(thm)],[c_4753,c_1467]) ).
% 3.78/0.96  
% 3.78/0.96  cnf(c_22,plain,
% 3.78/0.96      ( r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0 ),
% 3.78/0.96      inference(cnf_transformation,[],[f86]) ).
% 3.78/0.96  
% 3.78/0.96  cnf(c_2022,plain,
% 3.78/0.96      ( r1_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),sK5)
% 3.78/0.96      | k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),sK5) != k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))) ),
% 3.78/0.96      inference(instantiation,[status(thm)],[c_22]) ).
% 3.78/0.96  
% 3.78/0.96  cnf(c_2029,plain,
% 3.78/0.96      ( k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),sK5) != k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))
% 3.78/0.96      | r1_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),sK5) = iProver_top ),
% 3.78/0.96      inference(predicate_to_equality,[status(thm)],[c_2022]) ).
% 3.78/0.96  
% 3.78/0.96  cnf(c_30,plain,
% 3.78/0.96      ( ~ r1_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))),X2)
% 3.78/0.96      | ~ r2_hidden(X0,X2) ),
% 3.78/0.96      inference(cnf_transformation,[],[f126]) ).
% 3.78/0.96  
% 3.78/0.96  cnf(c_4832,plain,
% 3.78/0.96      ( ~ r1_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),sK5)
% 3.78/0.96      | ~ r2_hidden(sK3,sK5) ),
% 3.78/0.96      inference(instantiation,[status(thm)],[c_30]) ).
% 3.78/0.96  
% 3.78/0.96  cnf(c_4833,plain,
% 3.78/0.96      ( r1_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),sK5) != iProver_top
% 3.78/0.96      | r2_hidden(sK3,sK5) != iProver_top ),
% 3.78/0.96      inference(predicate_to_equality,[status(thm)],[c_4832]) ).
% 3.78/0.96  
% 3.78/0.96  cnf(c_5824,plain,
% 3.78/0.96      ( r2_hidden(sK3,sK5) != iProver_top ),
% 3.78/0.96      inference(global_propositional_subsumption,
% 3.78/0.96                [status(thm)],
% 3.78/0.96                [c_4769,c_45,c_44,c_1818,c_2029,c_2031,c_4833]) ).
% 3.78/0.96  
% 3.78/0.96  cnf(c_5829,plain,
% 3.78/0.96      ( k4_xboole_0(sK5,k1_tarski(sK3)) = sK5 ),
% 3.78/0.96      inference(superposition,[status(thm)],[c_1472,c_5824]) ).
% 3.78/0.96  
% 3.78/0.96  cnf(c_43,negated_conjecture,
% 3.78/0.96      ( r2_hidden(sK3,sK5)
% 3.78/0.96      | r2_hidden(sK4,sK5)
% 3.78/0.96      | k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),sK5) != k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))) ),
% 3.78/0.96      inference(cnf_transformation,[],[f134]) ).
% 3.78/0.96  
% 3.78/0.96  cnf(c_1466,plain,
% 3.78/0.96      ( k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),sK5) != k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))
% 3.78/0.96      | r2_hidden(sK3,sK5) = iProver_top
% 3.78/0.96      | r2_hidden(sK4,sK5) = iProver_top ),
% 3.78/0.96      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 3.78/0.96  
% 3.78/0.96  cnf(c_4756,plain,
% 3.78/0.96      ( k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))) != k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))
% 3.78/0.96      | r2_hidden(sK3,sK5) = iProver_top
% 3.78/0.96      | r2_hidden(sK4,sK5) = iProver_top ),
% 3.78/0.96      inference(demodulation,[status(thm)],[c_4753,c_1466]) ).
% 3.78/0.96  
% 3.78/0.96  cnf(c_5024,plain,
% 3.78/0.96      ( r2_hidden(sK3,sK5) = iProver_top
% 3.78/0.96      | r2_hidden(sK4,sK5) = iProver_top ),
% 3.78/0.96      inference(equality_resolution_simp,[status(thm)],[c_4756]) ).
% 3.78/0.96  
% 3.78/0.96  cnf(c_28,plain,
% 3.78/0.96      ( ~ r2_hidden(X0,k1_tarski(X1)) | X0 = X1 ),
% 3.78/0.96      inference(cnf_transformation,[],[f144]) ).
% 3.78/0.96  
% 3.78/0.96  cnf(c_1902,plain,
% 3.78/0.96      ( ~ r2_hidden(k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),sK5),k1_tarski(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))))
% 3.78/0.96      | r2_hidden(sK3,sK5)
% 3.78/0.96      | r2_hidden(sK4,sK5) ),
% 3.78/0.96      inference(resolution,[status(thm)],[c_28,c_43]) ).
% 3.78/0.96  
% 3.78/0.96  cnf(c_2187,plain,
% 3.78/0.96      ( r2_hidden(sK3,sK5) | r2_hidden(sK4,sK5) ),
% 3.78/0.96      inference(global_propositional_subsumption,
% 3.78/0.96                [status(thm)],
% 3.78/0.96                [c_1902,c_45,c_44,c_43,c_1818,c_2031]) ).
% 3.78/0.96  
% 3.78/0.96  cnf(c_38,plain,
% 3.78/0.96      ( ~ r2_hidden(X0,X1) | k4_xboole_0(X1,k1_tarski(X0)) != X1 ),
% 3.78/0.96      inference(cnf_transformation,[],[f102]) ).
% 3.78/0.96  
% 3.78/0.96  cnf(c_2306,plain,
% 3.78/0.96      ( ~ r2_hidden(sK4,sK5) | k4_xboole_0(sK5,k1_tarski(sK4)) != sK5 ),
% 3.78/0.96      inference(instantiation,[status(thm)],[c_38]) ).
% 3.78/0.96  
% 3.78/0.96  cnf(c_4260,plain,
% 3.78/0.96      ( r2_hidden(sK4,sK5) | k4_xboole_0(sK5,k1_tarski(sK4)) = sK5 ),
% 3.78/0.96      inference(instantiation,[status(thm)],[c_37]) ).
% 3.78/0.96  
% 3.78/0.96  cnf(c_4261,plain,
% 3.78/0.96      ( k4_xboole_0(sK5,k1_tarski(sK4)) = sK5
% 3.78/0.96      | r2_hidden(sK4,sK5) = iProver_top ),
% 3.78/0.96      inference(predicate_to_equality,[status(thm)],[c_4260]) ).
% 3.78/0.96  
% 3.78/0.96  cnf(c_5026,plain,
% 3.78/0.96      ( r2_hidden(sK4,sK5) = iProver_top ),
% 3.78/0.96      inference(global_propositional_subsumption,
% 3.78/0.96                [status(thm)],
% 3.78/0.96                [c_5024,c_45,c_44,c_43,c_1818,c_2022,c_2031,c_2306,
% 3.78/0.96                 c_4261,c_4832]) ).
% 3.78/0.96  
% 3.78/0.96  cnf(c_40,plain,
% 3.78/0.96      ( ~ r2_hidden(X0,X1)
% 3.78/0.96      | r2_hidden(X2,X1)
% 3.78/0.96      | k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X0),k1_tarski(X2))),X1) = k1_tarski(X2) ),
% 3.78/0.96      inference(cnf_transformation,[],[f131]) ).
% 3.78/0.96  
% 3.78/0.96  cnf(c_1469,plain,
% 3.78/0.96      ( k4_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))),X2) = k1_tarski(X0)
% 3.78/0.96      | r2_hidden(X1,X2) != iProver_top
% 3.78/0.96      | r2_hidden(X0,X2) = iProver_top ),
% 3.78/0.96      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 3.78/0.96  
% 3.78/0.96  cnf(c_5031,plain,
% 3.78/0.96      ( k4_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(sK4),k1_tarski(X0))),sK5) = k1_tarski(X0)
% 3.78/0.96      | r2_hidden(X0,sK5) = iProver_top ),
% 3.78/0.96      inference(superposition,[status(thm)],[c_5026,c_1469]) ).
% 3.78/0.96  
% 3.78/0.96  cnf(c_8701,plain,
% 3.78/0.96      ( k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),sK5) = k1_tarski(sK3) ),
% 3.78/0.96      inference(superposition,[status(thm)],[c_5031,c_5824]) ).
% 3.78/0.96  
% 3.78/0.96  cnf(c_9646,plain,
% 3.78/0.96      ( k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))) = k1_tarski(sK3) ),
% 3.78/0.96      inference(demodulation,[status(thm)],[c_8701,c_4753]) ).
% 3.78/0.96  
% 3.78/0.96  cnf(c_18,plain,
% 3.78/0.96      ( k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 3.78/0.96      inference(cnf_transformation,[],[f121]) ).
% 3.78/0.96  
% 3.78/0.96  cnf(c_9975,plain,
% 3.78/0.96      ( k4_xboole_0(k4_xboole_0(X0,k1_tarski(sK3)),k1_tarski(sK4)) = k4_xboole_0(X0,k1_tarski(sK3)) ),
% 3.78/0.96      inference(superposition,[status(thm)],[c_9646,c_18]) ).
% 3.78/0.96  
% 3.78/0.96  cnf(c_10742,plain,
% 3.78/0.96      ( k4_xboole_0(sK5,k1_tarski(sK3)) = k4_xboole_0(sK5,k1_tarski(sK4)) ),
% 3.78/0.96      inference(superposition,[status(thm)],[c_5829,c_9975]) ).
% 3.78/0.96  
% 3.78/0.96  cnf(c_10807,plain,
% 3.78/0.96      ( k4_xboole_0(sK5,k1_tarski(sK4)) = sK5 ),
% 3.78/0.96      inference(light_normalisation,[status(thm)],[c_10742,c_5829]) ).
% 3.78/0.96  
% 3.78/0.96  cnf(contradiction,plain,
% 3.78/0.96      ( $false ),
% 3.78/0.96      inference(minisat,
% 3.78/0.96                [status(thm)],
% 3.78/0.96                [c_10807,c_4832,c_2403,c_2306,c_2022,c_43]) ).
% 3.78/0.96  
% 3.78/0.96  
% 3.78/0.96  % SZS output end CNFRefutation for theBenchmark.p
% 3.78/0.96  
% 3.78/0.96  ------                               Statistics
% 3.78/0.96  
% 3.78/0.96  ------ Selected
% 3.78/0.96  
% 3.78/0.96  total_time:                             0.301
% 3.78/0.96  
%------------------------------------------------------------------------------
