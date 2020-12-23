%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0046+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:20 EST 2020

% Result     : Theorem 1.48s
% Output     : CNFRefutation 1.48s
% Verified   : 
% Statistics : Number of formulae       :   62 (  98 expanded)
%              Number of clauses        :   31 (  31 expanded)
%              Number of leaves         :    6 (  18 expanded)
%              Depth                    :   12
%              Number of atoms          :  269 ( 701 expanded)
%              Number of equality atoms :   67 ( 121 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f7,plain,(
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
    inference(flattening,[],[f6])).

fof(f8,plain,(
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
    inference(rectify,[],[f7])).

fof(f9,plain,(
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

fof(f10,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f9])).

fof(f19,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f32,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f19])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(nnf_transformation,[],[f2])).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f11])).

fof(f13,plain,(
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
    inference(rectify,[],[f12])).

fof(f14,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK1(X0,X1,X2),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X0)
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(sK1(X0,X1,X2),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK1(X0,X1,X2),X1)
            | ~ r2_hidden(sK1(X0,X1,X2),X0)
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
              & r2_hidden(sK1(X0,X1,X2),X0) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f14])).

fof(f24,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f36,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f24])).

fof(f20,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f31,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f20])).

fof(f26,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f34,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f26])).

fof(f18,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f33,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f18])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f3,conjecture,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(negated_conjecture,[],[f3])).

fof(f5,plain,(
    ? [X0,X1] : k2_xboole_0(X0,X1) != k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,
    ( ? [X0,X1] : k2_xboole_0(X0,X1) != k2_xboole_0(X0,k4_xboole_0(X1,X0))
   => k2_xboole_0(sK2,sK3) != k2_xboole_0(sK2,k4_xboole_0(sK3,sK2)) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    k2_xboole_0(sK2,sK3) != k2_xboole_0(sK2,k4_xboole_0(sK3,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f5,f16])).

fof(f30,plain,(
    k2_xboole_0(sK2,sK3) != k2_xboole_0(sK2,k4_xboole_0(sK3,sK2)) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_677,plain,
    ( r2_hidden(sK0(sK2,sK3,k2_xboole_0(sK2,k4_xboole_0(sK3,sK2))),k2_xboole_0(sK2,X0))
    | ~ r2_hidden(sK0(sK2,sK3,k2_xboole_0(sK2,k4_xboole_0(sK3,sK2))),sK2) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2074,plain,
    ( r2_hidden(sK0(sK2,sK3,k2_xboole_0(sK2,k4_xboole_0(sK3,sK2))),k2_xboole_0(sK2,k4_xboole_0(sK3,sK2)))
    | ~ r2_hidden(sK0(sK2,sK3,k2_xboole_0(sK2,k4_xboole_0(sK3,sK2))),sK2) ),
    inference(instantiation,[status(thm)],[c_677])).

cnf(c_2075,plain,
    ( r2_hidden(sK0(sK2,sK3,k2_xboole_0(sK2,k4_xboole_0(sK3,sK2))),k2_xboole_0(sK2,k4_xboole_0(sK3,sK2))) = iProver_top
    | r2_hidden(sK0(sK2,sK3,k2_xboole_0(sK2,k4_xboole_0(sK3,sK2))),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2074])).

cnf(c_11,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_721,plain,
    ( r2_hidden(sK0(sK2,sK3,k2_xboole_0(sK2,k4_xboole_0(sK3,sK2))),X0)
    | ~ r2_hidden(sK0(sK2,sK3,k2_xboole_0(sK2,k4_xboole_0(sK3,sK2))),k4_xboole_0(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1611,plain,
    ( ~ r2_hidden(sK0(sK2,sK3,k2_xboole_0(sK2,k4_xboole_0(sK3,sK2))),k4_xboole_0(sK3,sK2))
    | r2_hidden(sK0(sK2,sK3,k2_xboole_0(sK2,k4_xboole_0(sK3,sK2))),sK3) ),
    inference(instantiation,[status(thm)],[c_721])).

cnf(c_1612,plain,
    ( r2_hidden(sK0(sK2,sK3,k2_xboole_0(sK2,k4_xboole_0(sK3,sK2))),k4_xboole_0(sK3,sK2)) != iProver_top
    | r2_hidden(sK0(sK2,sK3,k2_xboole_0(sK2,k4_xboole_0(sK3,sK2))),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1611])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_699,plain,
    ( ~ r2_hidden(sK0(sK2,sK3,k2_xboole_0(sK2,k4_xboole_0(sK3,sK2))),X0)
    | r2_hidden(sK0(sK2,sK3,k2_xboole_0(sK2,k4_xboole_0(sK3,sK2))),k2_xboole_0(X1,X0)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1598,plain,
    ( ~ r2_hidden(sK0(sK2,sK3,k2_xboole_0(sK2,k4_xboole_0(sK3,sK2))),k4_xboole_0(sK3,sK2))
    | r2_hidden(sK0(sK2,sK3,k2_xboole_0(sK2,k4_xboole_0(sK3,sK2))),k2_xboole_0(X0,k4_xboole_0(sK3,sK2))) ),
    inference(instantiation,[status(thm)],[c_699])).

cnf(c_1599,plain,
    ( r2_hidden(sK0(sK2,sK3,k2_xboole_0(sK2,k4_xboole_0(sK3,sK2))),k4_xboole_0(sK3,sK2)) != iProver_top
    | r2_hidden(sK0(sK2,sK3,k2_xboole_0(sK2,k4_xboole_0(sK3,sK2))),k2_xboole_0(X0,k4_xboole_0(sK3,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1598])).

cnf(c_1601,plain,
    ( r2_hidden(sK0(sK2,sK3,k2_xboole_0(sK2,k4_xboole_0(sK3,sK2))),k4_xboole_0(sK3,sK2)) != iProver_top
    | r2_hidden(sK0(sK2,sK3,k2_xboole_0(sK2,k4_xboole_0(sK3,sK2))),k2_xboole_0(sK2,k4_xboole_0(sK3,sK2))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1599])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_524,plain,
    ( r2_hidden(sK0(sK2,sK3,k2_xboole_0(sK2,k4_xboole_0(sK3,sK2))),X0)
    | r2_hidden(sK0(sK2,sK3,k2_xboole_0(sK2,k4_xboole_0(sK3,sK2))),k4_xboole_0(sK3,X0))
    | ~ r2_hidden(sK0(sK2,sK3,k2_xboole_0(sK2,k4_xboole_0(sK3,sK2))),sK3) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_540,plain,
    ( r2_hidden(sK0(sK2,sK3,k2_xboole_0(sK2,k4_xboole_0(sK3,sK2))),X0) = iProver_top
    | r2_hidden(sK0(sK2,sK3,k2_xboole_0(sK2,k4_xboole_0(sK3,sK2))),k4_xboole_0(sK3,X0)) = iProver_top
    | r2_hidden(sK0(sK2,sK3,k2_xboole_0(sK2,k4_xboole_0(sK3,sK2))),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_524])).

cnf(c_542,plain,
    ( r2_hidden(sK0(sK2,sK3,k2_xboole_0(sK2,k4_xboole_0(sK3,sK2))),k4_xboole_0(sK3,sK2)) = iProver_top
    | r2_hidden(sK0(sK2,sK3,k2_xboole_0(sK2,k4_xboole_0(sK3,sK2))),sK3) != iProver_top
    | r2_hidden(sK0(sK2,sK3,k2_xboole_0(sK2,k4_xboole_0(sK3,sK2))),sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_540])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_489,plain,
    ( r2_hidden(sK0(sK2,sK3,k2_xboole_0(sK2,k4_xboole_0(sK3,sK2))),k4_xboole_0(sK3,sK2))
    | ~ r2_hidden(sK0(sK2,sK3,k2_xboole_0(sK2,k4_xboole_0(sK3,sK2))),k2_xboole_0(sK2,k4_xboole_0(sK3,sK2)))
    | r2_hidden(sK0(sK2,sK3,k2_xboole_0(sK2,k4_xboole_0(sK3,sK2))),sK2) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_490,plain,
    ( r2_hidden(sK0(sK2,sK3,k2_xboole_0(sK2,k4_xboole_0(sK3,sK2))),k4_xboole_0(sK3,sK2)) = iProver_top
    | r2_hidden(sK0(sK2,sK3,k2_xboole_0(sK2,k4_xboole_0(sK3,sK2))),k2_xboole_0(sK2,k4_xboole_0(sK3,sK2))) != iProver_top
    | r2_hidden(sK0(sK2,sK3,k2_xboole_0(sK2,k4_xboole_0(sK3,sK2))),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_489])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(sK0(X0,X1,X2),X0)
    | k2_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f21])).

cnf(c_453,plain,
    ( r2_hidden(sK0(sK2,sK3,k2_xboole_0(sK2,k4_xboole_0(sK3,sK2))),k2_xboole_0(sK2,k4_xboole_0(sK3,sK2)))
    | r2_hidden(sK0(sK2,sK3,k2_xboole_0(sK2,k4_xboole_0(sK3,sK2))),sK3)
    | r2_hidden(sK0(sK2,sK3,k2_xboole_0(sK2,k4_xboole_0(sK3,sK2))),sK2)
    | k2_xboole_0(sK2,sK3) = k2_xboole_0(sK2,k4_xboole_0(sK3,sK2)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_454,plain,
    ( k2_xboole_0(sK2,sK3) = k2_xboole_0(sK2,k4_xboole_0(sK3,sK2))
    | r2_hidden(sK0(sK2,sK3,k2_xboole_0(sK2,k4_xboole_0(sK3,sK2))),k2_xboole_0(sK2,k4_xboole_0(sK3,sK2))) = iProver_top
    | r2_hidden(sK0(sK2,sK3,k2_xboole_0(sK2,k4_xboole_0(sK3,sK2))),sK3) = iProver_top
    | r2_hidden(sK0(sK2,sK3,k2_xboole_0(sK2,k4_xboole_0(sK3,sK2))),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_453])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X2)
    | ~ r2_hidden(sK0(X0,X1,X2),X0)
    | k2_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f22])).

cnf(c_450,plain,
    ( ~ r2_hidden(sK0(sK2,sK3,k2_xboole_0(sK2,k4_xboole_0(sK3,sK2))),k2_xboole_0(sK2,k4_xboole_0(sK3,sK2)))
    | ~ r2_hidden(sK0(sK2,sK3,k2_xboole_0(sK2,k4_xboole_0(sK3,sK2))),sK2)
    | k2_xboole_0(sK2,sK3) = k2_xboole_0(sK2,k4_xboole_0(sK3,sK2)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_451,plain,
    ( k2_xboole_0(sK2,sK3) = k2_xboole_0(sK2,k4_xboole_0(sK3,sK2))
    | r2_hidden(sK0(sK2,sK3,k2_xboole_0(sK2,k4_xboole_0(sK3,sK2))),k2_xboole_0(sK2,k4_xboole_0(sK3,sK2))) != iProver_top
    | r2_hidden(sK0(sK2,sK3,k2_xboole_0(sK2,k4_xboole_0(sK3,sK2))),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_450])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | k2_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_447,plain,
    ( ~ r2_hidden(sK0(sK2,sK3,k2_xboole_0(sK2,k4_xboole_0(sK3,sK2))),k2_xboole_0(sK2,k4_xboole_0(sK3,sK2)))
    | ~ r2_hidden(sK0(sK2,sK3,k2_xboole_0(sK2,k4_xboole_0(sK3,sK2))),sK3)
    | k2_xboole_0(sK2,sK3) = k2_xboole_0(sK2,k4_xboole_0(sK3,sK2)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_448,plain,
    ( k2_xboole_0(sK2,sK3) = k2_xboole_0(sK2,k4_xboole_0(sK3,sK2))
    | r2_hidden(sK0(sK2,sK3,k2_xboole_0(sK2,k4_xboole_0(sK3,sK2))),k2_xboole_0(sK2,k4_xboole_0(sK3,sK2))) != iProver_top
    | r2_hidden(sK0(sK2,sK3,k2_xboole_0(sK2,k4_xboole_0(sK3,sK2))),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_447])).

cnf(c_12,negated_conjecture,
    ( k2_xboole_0(sK2,sK3) != k2_xboole_0(sK2,k4_xboole_0(sK3,sK2)) ),
    inference(cnf_transformation,[],[f30])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2075,c_1612,c_1601,c_542,c_490,c_454,c_451,c_448,c_12])).


%------------------------------------------------------------------------------
