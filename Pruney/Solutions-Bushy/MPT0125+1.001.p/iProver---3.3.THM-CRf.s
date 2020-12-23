%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0125+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:32 EST 2020

% Result     : Theorem 3.71s
% Output     : CNFRefutation 3.71s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 135 expanded)
%              Number of clauses        :   41 (  47 expanded)
%              Number of leaves         :   10 (  28 expanded)
%              Depth                    :   11
%              Number of atoms          :  335 ( 849 expanded)
%              Number of equality atoms :  171 ( 433 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f18,plain,(
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
    inference(rectify,[],[f17])).

fof(f19,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            & ~ r2_hidden(sK2(X0,X1,X2),X0) )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( r2_hidden(sK2(X0,X1,X2),X1)
          | r2_hidden(sK2(X0,X1,X2),X0)
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
              & ~ r2_hidden(sK2(X0,X1,X2),X0) )
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( r2_hidden(sK2(X0,X1,X2),X1)
            | r2_hidden(sK2(X0,X1,X2),X0)
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f19])).

fof(f33,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f50,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f33])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
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

fof(f8,plain,(
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
    inference(rectify,[],[f7])).

fof(f9,plain,(
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

fof(f10,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f9])).

fof(f24,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f40,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f24])).

fof(f41,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f40])).

fof(f34,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f49,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f34])).

fof(f35,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f48,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f35])).

fof(f23,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f42,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f23])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(nnf_transformation,[],[f2])).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f11])).

fof(f13,plain,(
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
    inference(rectify,[],[f12])).

fof(f14,plain,(
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

fof(f15,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f14])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) = X2
      | sK1(X0,X1,X2) = X1
      | sK1(X0,X1,X2) = X0
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) = X2
      | sK1(X0,X1,X2) != X1
      | ~ r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) = X2
      | sK1(X0,X1,X2) != X0
      | ~ r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f4,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(negated_conjecture,[],[f4])).

fof(f6,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(ennf_transformation,[],[f5])).

fof(f21,plain,
    ( ? [X0,X1] : k2_tarski(X0,X1) != k2_xboole_0(k1_tarski(X0),k1_tarski(X1))
   => k2_tarski(sK3,sK4) != k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    k2_tarski(sK3,sK4) != k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f6,f21])).

fof(f39,plain,(
    k2_tarski(sK3,sK4) != k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_15,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_546,plain,
    ( r2_hidden(sK1(sK3,sK4,k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),X0)
    | ~ r2_hidden(sK1(sK3,sK4,k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),k2_xboole_0(X0,k1_tarski(sK4)))
    | r2_hidden(sK1(sK3,sK4,k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),k1_tarski(sK4)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_4984,plain,
    ( ~ r2_hidden(sK1(sK3,sK4,k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)))
    | r2_hidden(sK1(sK3,sK4,k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),k1_tarski(sK4))
    | r2_hidden(sK1(sK3,sK4,k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),k1_tarski(sK3)) ),
    inference(instantiation,[status(thm)],[c_546])).

cnf(c_183,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_551,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK1(sK3,sK4,k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),k1_tarski(sK4))
    | sK1(sK3,sK4,k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))) != X0
    | k1_tarski(sK4) != X1 ),
    inference(instantiation,[status(thm)],[c_183])).

cnf(c_1224,plain,
    ( ~ r2_hidden(X0,k1_tarski(sK4))
    | r2_hidden(sK1(sK3,sK4,k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),k1_tarski(sK4))
    | sK1(sK3,sK4,k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))) != X0
    | k1_tarski(sK4) != k1_tarski(sK4) ),
    inference(instantiation,[status(thm)],[c_551])).

cnf(c_3429,plain,
    ( r2_hidden(sK1(sK3,sK4,k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),k1_tarski(sK4))
    | ~ r2_hidden(sK4,k1_tarski(sK4))
    | sK1(sK3,sK4,k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))) != sK4
    | k1_tarski(sK4) != k1_tarski(sK4) ),
    inference(instantiation,[status(thm)],[c_1224])).

cnf(c_3430,plain,
    ( sK1(sK3,sK4,k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))) != sK4
    | k1_tarski(sK4) != k1_tarski(sK4)
    | r2_hidden(sK1(sK3,sK4,k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),k1_tarski(sK4)) = iProver_top
    | r2_hidden(sK4,k1_tarski(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3429])).

cnf(c_180,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2111,plain,
    ( k1_tarski(sK4) = k1_tarski(sK4) ),
    inference(instantiation,[status(thm)],[c_180])).

cnf(c_2,plain,
    ( r2_hidden(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1838,plain,
    ( r2_hidden(sK4,k1_tarski(sK4)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1839,plain,
    ( r2_hidden(sK4,k1_tarski(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1838])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1412,plain,
    ( r2_hidden(X0,k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)))
    | ~ r2_hidden(X0,k1_tarski(sK3)) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1413,plain,
    ( r2_hidden(X0,k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))) = iProver_top
    | r2_hidden(X0,k1_tarski(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1412])).

cnf(c_1415,plain,
    ( r2_hidden(sK3,k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))) = iProver_top
    | r2_hidden(sK3,k1_tarski(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1413])).

cnf(c_1140,plain,
    ( k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)) = k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)) ),
    inference(instantiation,[status(thm)],[c_180])).

cnf(c_567,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK1(sK3,sK4,k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)))
    | sK1(sK3,sK4,k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))) != X0
    | k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)) != X1 ),
    inference(instantiation,[status(thm)],[c_183])).

cnf(c_803,plain,
    ( ~ r2_hidden(X0,k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)))
    | r2_hidden(sK1(sK3,sK4,k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)))
    | sK1(sK3,sK4,k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))) != X0
    | k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)) != k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)) ),
    inference(instantiation,[status(thm)],[c_567])).

cnf(c_804,plain,
    ( sK1(sK3,sK4,k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))) != X0
    | k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)) != k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))
    | r2_hidden(X0,k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))) != iProver_top
    | r2_hidden(sK1(sK3,sK4,k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_803])).

cnf(c_806,plain,
    ( sK1(sK3,sK4,k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))) != sK3
    | k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)) != k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))
    | r2_hidden(sK1(sK3,sK4,k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))) = iProver_top
    | r2_hidden(sK3,k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_804])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_561,plain,
    ( r2_hidden(sK1(sK3,sK4,k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)))
    | ~ r2_hidden(sK1(sK3,sK4,k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),k1_tarski(sK4)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_562,plain,
    ( r2_hidden(sK1(sK3,sK4,k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))) = iProver_top
    | r2_hidden(sK1(sK3,sK4,k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),k1_tarski(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_561])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k1_tarski(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_495,plain,
    ( ~ r2_hidden(sK1(sK3,sK4,k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),k1_tarski(sK3))
    | sK1(sK3,sK4,k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))) = sK3 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_6,plain,
    ( r2_hidden(sK1(X0,X1,X2),X2)
    | sK1(X0,X1,X2) = X1
    | sK1(X0,X1,X2) = X0
    | k2_tarski(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_490,plain,
    ( r2_hidden(sK1(sK3,sK4,k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)))
    | sK1(sK3,sK4,k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))) = sK4
    | sK1(sK3,sK4,k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))) = sK3
    | k2_tarski(sK3,sK4) = k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_491,plain,
    ( sK1(sK3,sK4,k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))) = sK4
    | sK1(sK3,sK4,k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))) = sK3
    | k2_tarski(sK3,sK4) = k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))
    | r2_hidden(sK1(sK3,sK4,k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_490])).

cnf(c_483,plain,
    ( ~ r2_hidden(sK1(sK3,sK4,k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),k1_tarski(sK4))
    | sK1(sK3,sK4,k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))) = sK4 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_4,plain,
    ( ~ r2_hidden(sK1(X0,X1,X2),X2)
    | sK1(X0,X1,X2) != X1
    | k2_tarski(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_460,plain,
    ( ~ r2_hidden(sK1(sK3,sK4,k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)))
    | sK1(sK3,sK4,k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))) != sK4
    | k2_tarski(sK3,sK4) = k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_464,plain,
    ( sK1(sK3,sK4,k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))) != sK4
    | k2_tarski(sK3,sK4) = k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))
    | r2_hidden(sK1(sK3,sK4,k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_460])).

cnf(c_5,plain,
    ( ~ r2_hidden(sK1(X0,X1,X2),X2)
    | sK1(X0,X1,X2) != X0
    | k2_tarski(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_461,plain,
    ( ~ r2_hidden(sK1(sK3,sK4,k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)))
    | sK1(sK3,sK4,k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))) != sK3
    | k2_tarski(sK3,sK4) = k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_462,plain,
    ( sK1(sK3,sK4,k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))) != sK3
    | k2_tarski(sK3,sK4) = k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))
    | r2_hidden(sK1(sK3,sK4,k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_461])).

cnf(c_48,plain,
    ( r2_hidden(X0,k1_tarski(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_50,plain,
    ( r2_hidden(sK3,k1_tarski(sK3)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_48])).

cnf(c_16,negated_conjecture,
    ( k2_tarski(sK3,sK4) != k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)) ),
    inference(cnf_transformation,[],[f39])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4984,c_3430,c_2111,c_1839,c_1415,c_1140,c_806,c_562,c_495,c_491,c_490,c_483,c_464,c_462,c_50,c_16])).


%------------------------------------------------------------------------------
