%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0093+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:28 EST 2020

% Result     : Theorem 3.78s
% Output     : CNFRefutation 3.78s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 156 expanded)
%              Number of clauses        :   41 (  49 expanded)
%              Number of leaves         :   12 (  34 expanded)
%              Depth                    :   11
%              Number of atoms          :  324 ( 657 expanded)
%              Number of equality atoms :   44 (  56 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f13])).

fof(f15,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f15])).

fof(f29,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f4])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,X1) )
       => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f27,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
        & r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(sK3,k4_xboole_0(sK4,sK5))
      & r1_xboole_0(sK3,sK5)
      & r1_tarski(sK3,sK4) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ~ r1_tarski(sK3,k4_xboole_0(sK4,sK5))
    & r1_xboole_0(sK3,sK5)
    & r1_tarski(sK3,sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f12,f27])).

fof(f47,plain,(
    r1_xboole_0(sK3,sK5) ),
    inference(cnf_transformation,[],[f28])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
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

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f19,plain,(
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
    inference(rectify,[],[f18])).

fof(f20,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X0)
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(sK1(X0,X1,X2),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            | ~ r2_hidden(sK1(X0,X1,X2),X0)
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK1(X0,X1,X2),X1)
              & r2_hidden(sK1(X0,X1,X2),X0) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f20])).

fof(f34,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f49,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f34])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
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

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f23])).

fof(f25,plain,(
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

fof(f26,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f25])).

fof(f40,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f52,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f40])).

fof(f39,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f53,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f39])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f48,plain,(
    ~ r1_tarski(sK3,k4_xboole_0(sK4,sK5)) ),
    inference(cnf_transformation,[],[f28])).

fof(f46,plain,(
    r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_1313,plain,
    ( ~ r2_hidden(sK0(sK3,k4_xboole_0(sK4,sK5)),X0)
    | r2_hidden(sK0(sK3,k4_xboole_0(sK4,sK5)),X1)
    | ~ r1_tarski(X0,X1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_16548,plain,
    ( ~ r2_hidden(sK0(sK3,k4_xboole_0(sK4,sK5)),X0)
    | r2_hidden(sK0(sK3,k4_xboole_0(sK4,sK5)),k4_xboole_0(X1,X2))
    | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_1313])).

cnf(c_16550,plain,
    ( r2_hidden(sK0(sK3,k4_xboole_0(sK4,sK5)),k4_xboole_0(k1_xboole_0,k1_xboole_0))
    | ~ r2_hidden(sK0(sK3,k4_xboole_0(sK4,sK5)),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_16548])).

cnf(c_469,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_467,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2777,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_469,c_467])).

cnf(c_15,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_18,negated_conjecture,
    ( r1_xboole_0(sK3,sK5) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_205,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | sK5 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_18])).

cnf(c_206,plain,
    ( k3_xboole_0(sK3,sK5) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_205])).

cnf(c_11175,plain,
    ( r1_tarski(k3_xboole_0(sK3,sK5),X0)
    | ~ r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[status(thm)],[c_2777,c_206])).

cnf(c_11177,plain,
    ( r1_tarski(k3_xboole_0(sK3,sK5),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_11175])).

cnf(c_6582,plain,
    ( r2_hidden(sK0(sK3,k4_xboole_0(sK4,sK5)),X0)
    | ~ r2_hidden(sK0(sK3,k4_xboole_0(sK4,sK5)),k3_xboole_0(sK3,sK5))
    | ~ r1_tarski(k3_xboole_0(sK3,sK5),X0) ),
    inference(instantiation,[status(thm)],[c_1313])).

cnf(c_6603,plain,
    ( ~ r2_hidden(sK0(sK3,k4_xboole_0(sK4,sK5)),k3_xboole_0(sK3,sK5))
    | r2_hidden(sK0(sK3,k4_xboole_0(sK4,sK5)),k1_xboole_0)
    | ~ r1_tarski(k3_xboole_0(sK3,sK5),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_6582])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_996,plain,
    ( ~ r2_hidden(sK0(sK3,k4_xboole_0(sK4,sK5)),X0)
    | r2_hidden(sK0(sK3,k4_xboole_0(sK4,sK5)),k3_xboole_0(sK3,X0))
    | ~ r2_hidden(sK0(sK3,k4_xboole_0(sK4,sK5)),sK3) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_3718,plain,
    ( r2_hidden(sK0(sK3,k4_xboole_0(sK4,sK5)),k3_xboole_0(sK3,sK5))
    | ~ r2_hidden(sK0(sK3,k4_xboole_0(sK4,sK5)),sK5)
    | ~ r2_hidden(sK0(sK3,k4_xboole_0(sK4,sK5)),sK3) ),
    inference(instantiation,[status(thm)],[c_996])).

cnf(c_16,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_2773,plain,
    ( r1_tarski(X0,k4_xboole_0(k1_xboole_0,X1))
    | ~ r1_tarski(X2,k1_xboole_0)
    | X0 != X2 ),
    inference(resolution,[status(thm)],[c_469,c_16])).

cnf(c_2775,plain,
    ( r1_tarski(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0))
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2773])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1157,plain,
    ( r2_hidden(sK0(sK3,k4_xboole_0(sK4,sK5)),X0)
    | r2_hidden(sK0(sK3,k4_xboole_0(sK4,sK5)),k4_xboole_0(sK4,X0))
    | ~ r2_hidden(sK0(sK3,k4_xboole_0(sK4,sK5)),sK4) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1777,plain,
    ( r2_hidden(sK0(sK3,k4_xboole_0(sK4,sK5)),k4_xboole_0(sK4,sK5))
    | r2_hidden(sK0(sK3,k4_xboole_0(sK4,sK5)),sK5)
    | ~ r2_hidden(sK0(sK3,k4_xboole_0(sK4,sK5)),sK4) ),
    inference(instantiation,[status(thm)],[c_1157])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1314,plain,
    ( ~ r2_hidden(sK0(sK3,k4_xboole_0(sK4,sK5)),X0)
    | ~ r2_hidden(sK0(sK3,k4_xboole_0(sK4,sK5)),k4_xboole_0(X1,X0)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1316,plain,
    ( ~ r2_hidden(sK0(sK3,k4_xboole_0(sK4,sK5)),k4_xboole_0(k1_xboole_0,k1_xboole_0))
    | ~ r2_hidden(sK0(sK3,k4_xboole_0(sK4,sK5)),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1314])).

cnf(c_978,plain,
    ( r2_hidden(sK0(sK3,k4_xboole_0(sK4,sK5)),X0)
    | ~ r2_hidden(sK0(sK3,k4_xboole_0(sK4,sK5)),sK3)
    | ~ r1_tarski(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1086,plain,
    ( r2_hidden(sK0(sK3,k4_xboole_0(sK4,sK5)),sK4)
    | ~ r2_hidden(sK0(sK3,k4_xboole_0(sK4,sK5)),sK3)
    | ~ r1_tarski(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_978])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_947,plain,
    ( r1_tarski(X0,X0) ),
    inference(resolution,[status(thm)],[c_0,c_1])).

cnf(c_949,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_947])).

cnf(c_478,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_467])).

cnf(c_17,negated_conjecture,
    ( ~ r1_tarski(sK3,k4_xboole_0(sK4,sK5)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_244,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | k4_xboole_0(sK4,sK5) != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_17])).

cnf(c_245,plain,
    ( ~ r2_hidden(sK0(sK3,k4_xboole_0(sK4,sK5)),k4_xboole_0(sK4,sK5)) ),
    inference(unflattening,[status(thm)],[c_244])).

cnf(c_237,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | k4_xboole_0(sK4,sK5) != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_17])).

cnf(c_238,plain,
    ( r2_hidden(sK0(sK3,k4_xboole_0(sK4,sK5)),sK3) ),
    inference(unflattening,[status(thm)],[c_237])).

cnf(c_19,negated_conjecture,
    ( r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f46])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_16550,c_11177,c_6603,c_3718,c_2775,c_1777,c_1316,c_1086,c_949,c_478,c_245,c_238,c_19])).


%------------------------------------------------------------------------------
