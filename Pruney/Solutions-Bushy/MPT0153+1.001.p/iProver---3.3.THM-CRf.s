%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0153+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:36 EST 2020

% Result     : Theorem 0.99s
% Output     : CNFRefutation 0.99s
% Verified   : 
% Statistics : Number of formulae       :   48 (  74 expanded)
%              Number of clauses        :   21 (  22 expanded)
%              Number of leaves         :    8 (  16 expanded)
%              Depth                    :   12
%              Number of atoms          :  195 ( 462 expanded)
%              Number of equality atoms :  139 ( 323 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f7,plain,(
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
    inference(rectify,[],[f6])).

fof(f8,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK0(X0,X1) != X0
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( sK0(X0,X1) = X0
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK0(X0,X1) != X0
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( sK0(X0,X1) = X0
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f8])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK0(X0,X1) = X0
      | r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

fof(f12,plain,(
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
    inference(rectify,[],[f11])).

fof(f13,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK1(X0,X1,X2) != X1
            & sK1(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( sK1(X0,X1,X2) = X1
          | sK1(X0,X1,X2) = X0
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK1(X0,X1,X2) != X1
              & sK1(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( sK1(X0,X1,X2) = X1
            | sK1(X0,X1,X2) = X0
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f12,f13])).

fof(f21,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f35,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k2_tarski(X0,X1)) ) ),
    inference(equality_resolution,[],[f21])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK0(X0,X1) != X0
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f23,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f31,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f23])).

fof(f32,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_tarski(X0,X4)) ),
    inference(equality_resolution,[],[f31])).

fof(f22,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f33,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f22])).

fof(f34,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_tarski(X4,X1)) ),
    inference(equality_resolution,[],[f33])).

fof(f3,conjecture,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(negated_conjecture,[],[f3])).

fof(f5,plain,(
    ? [X0] : k1_tarski(X0) != k2_tarski(X0,X0) ),
    inference(ennf_transformation,[],[f4])).

fof(f15,plain,
    ( ? [X0] : k1_tarski(X0) != k2_tarski(X0,X0)
   => k1_tarski(sK2) != k2_tarski(sK2,sK2) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    k1_tarski(sK2) != k2_tarski(sK2,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f5,f15])).

fof(f27,plain,(
    k1_tarski(sK2) != k2_tarski(sK2,sK2) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | sK0(X0,X1) = X0
    | k1_tarski(X0) = X1 ),
    inference(cnf_transformation,[],[f19])).

cnf(c_645,plain,
    ( sK0(X0,X1) = X0
    | k1_tarski(X0) = X1
    | r2_hidden(sK0(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k2_tarski(X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_637,plain,
    ( X0 = X1
    | X0 = X2
    | r2_hidden(X0,k2_tarski(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1219,plain,
    ( k2_tarski(X0,X1) = k1_tarski(X2)
    | sK0(X2,k2_tarski(X0,X1)) = X2
    | sK0(X2,k2_tarski(X0,X1)) = X1
    | sK0(X2,k2_tarski(X0,X1)) = X0 ),
    inference(superposition,[status(thm)],[c_645,c_637])).

cnf(c_1234,plain,
    ( k2_tarski(sK2,sK2) = k1_tarski(sK2)
    | sK0(sK2,k2_tarski(sK2,sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_1219])).

cnf(c_473,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_721,plain,
    ( k2_tarski(sK2,sK2) != X0
    | k1_tarski(sK2) != X0
    | k1_tarski(sK2) = k2_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_473])).

cnf(c_755,plain,
    ( k2_tarski(sK2,sK2) != k1_tarski(sK2)
    | k1_tarski(sK2) = k2_tarski(sK2,sK2)
    | k1_tarski(sK2) != k1_tarski(sK2) ),
    inference(instantiation,[status(thm)],[c_721])).

cnf(c_474,plain,
    ( X0 != X1
    | k1_tarski(X0) = k1_tarski(X1) ),
    theory(equality)).

cnf(c_477,plain,
    ( k1_tarski(sK2) = k1_tarski(sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_474])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | sK0(X0,X1) != X0
    | k1_tarski(X0) = X1 ),
    inference(cnf_transformation,[],[f20])).

cnf(c_7,plain,
    ( r2_hidden(X0,k2_tarski(X1,X0)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_197,plain,
    ( k2_tarski(X0,X1) != X2
    | sK0(X3,X2) != X3
    | sK0(X3,X2) != X1
    | k1_tarski(X3) = X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_7])).

cnf(c_198,plain,
    ( sK0(X0,k2_tarski(X1,X2)) != X0
    | sK0(X0,k2_tarski(X1,X2)) != X2
    | k1_tarski(X0) = k2_tarski(X1,X2) ),
    inference(unflattening,[status(thm)],[c_197])).

cnf(c_199,plain,
    ( sK0(sK2,k2_tarski(sK2,sK2)) != sK2
    | k1_tarski(sK2) = k2_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_198])).

cnf(c_8,plain,
    ( r2_hidden(X0,k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_15,plain,
    ( r2_hidden(sK2,k2_tarski(sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_12,plain,
    ( ~ r2_hidden(sK2,k2_tarski(sK2,sK2))
    | sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_10,negated_conjecture,
    ( k1_tarski(sK2) != k2_tarski(sK2,sK2) ),
    inference(cnf_transformation,[],[f27])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1234,c_755,c_477,c_199,c_15,c_12,c_10])).


%------------------------------------------------------------------------------
