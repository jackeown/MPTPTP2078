%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0030+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:17 EST 2020

% Result     : Theorem 1.80s
% Output     : CNFRefutation 1.80s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 175 expanded)
%              Number of clauses        :   46 (  52 expanded)
%              Number of leaves         :    6 (  32 expanded)
%              Depth                    :   11
%              Number of atoms          :  310 (1294 expanded)
%              Number of equality atoms :   88 ( 211 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
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
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
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
    inference(flattening,[],[f11])).

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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f12])).

fof(f14,plain,(
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

fof(f15,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f14])).

fof(f26,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f34,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f26])).

fof(f24,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f36,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f24])).

fof(f25,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f35,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f25])).

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
    ! [X0,X1,X2] : k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] : k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(negated_conjecture,[],[f3])).

fof(f5,plain,(
    ? [X0,X1,X2] : k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) != k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,
    ( ? [X0,X1,X2] : k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) != k3_xboole_0(X0,k2_xboole_0(X1,X2))
   => k2_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4)) != k3_xboole_0(sK2,k2_xboole_0(sK3,sK4)) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    k2_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4)) != k3_xboole_0(sK2,k2_xboole_0(sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f5,f16])).

fof(f30,plain,(
    k2_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4)) != k3_xboole_0(sK2,k2_xboole_0(sK3,sK4)) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_2791,plain,
    ( ~ r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),X0)
    | r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k2_xboole_0(X1,X0)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_9970,plain,
    ( r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k2_xboole_0(sK3,sK4))
    | ~ r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),sK4) ),
    inference(instantiation,[status(thm)],[c_2791])).

cnf(c_9971,plain,
    ( r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k2_xboole_0(sK3,sK4)) = iProver_top
    | r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9970])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_2353,plain,
    ( r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k2_xboole_0(sK3,X0))
    | ~ r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),sK3) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_4392,plain,
    ( r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k2_xboole_0(sK3,sK4))
    | ~ r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),sK3) ),
    inference(instantiation,[status(thm)],[c_2353])).

cnf(c_4393,plain,
    ( r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k2_xboole_0(sK3,sK4)) = iProver_top
    | r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4392])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_2352,plain,
    ( ~ r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),X0)
    | r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k3_xboole_0(X0,sK3))
    | ~ r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),sK3) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2363,plain,
    ( r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),X0) != iProver_top
    | r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k3_xboole_0(X0,sK3)) = iProver_top
    | r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2352])).

cnf(c_2365,plain,
    ( r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k3_xboole_0(sK2,sK3)) = iProver_top
    | r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),sK3) != iProver_top
    | r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2363])).

cnf(c_1537,plain,
    ( ~ r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),X0)
    | r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k3_xboole_0(X0,sK4))
    | ~ r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),sK4) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1548,plain,
    ( r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),X0) != iProver_top
    | r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k3_xboole_0(X0,sK4)) = iProver_top
    | r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1537])).

cnf(c_1550,plain,
    ( r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k3_xboole_0(sK2,sK4)) = iProver_top
    | r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),sK4) != iProver_top
    | r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1548])).

cnf(c_11,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_732,plain,
    ( ~ r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k3_xboole_0(sK2,sK3))
    | r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),sK2) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_733,plain,
    ( r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k3_xboole_0(sK2,sK3)) != iProver_top
    | r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_732])).

cnf(c_10,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_729,plain,
    ( ~ r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k3_xboole_0(sK2,sK3))
    | r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),sK3) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_730,plain,
    ( r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k3_xboole_0(sK2,sK3)) != iProver_top
    | r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_729])).

cnf(c_561,plain,
    ( ~ r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k3_xboole_0(sK2,sK4))
    | r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),sK2) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_562,plain,
    ( r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k3_xboole_0(sK2,sK4)) != iProver_top
    | r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_561])).

cnf(c_558,plain,
    ( ~ r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k3_xboole_0(sK2,sK4))
    | r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),sK4) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_559,plain,
    ( r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k3_xboole_0(sK2,sK4)) != iProver_top
    | r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_558])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_530,plain,
    ( ~ r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k2_xboole_0(sK3,sK4))
    | r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),sK4)
    | r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),sK3) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_531,plain,
    ( r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k2_xboole_0(sK3,sK4)) != iProver_top
    | r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),sK4) = iProver_top
    | r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_530])).

cnf(c_511,plain,
    ( ~ r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),X0)
    | r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k3_xboole_0(X0,k2_xboole_0(sK3,sK4)))
    | ~ r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k2_xboole_0(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_522,plain,
    ( r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),X0) != iProver_top
    | r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k3_xboole_0(X0,k2_xboole_0(sK3,sK4))) = iProver_top
    | r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k2_xboole_0(sK3,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_511])).

cnf(c_524,plain,
    ( r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))) = iProver_top
    | r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k2_xboole_0(sK3,sK4)) != iProver_top
    | r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_522])).

cnf(c_486,plain,
    ( ~ r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4)))
    | r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),sK2) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_487,plain,
    ( r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))) != iProver_top
    | r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_486])).

cnf(c_483,plain,
    ( ~ r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4)))
    | r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k2_xboole_0(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_484,plain,
    ( r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))) != iProver_top
    | r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k2_xboole_0(sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_483])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(sK0(X0,X1,X2),X0)
    | k2_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f21])).

cnf(c_454,plain,
    ( r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4)))
    | r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k3_xboole_0(sK2,sK4))
    | r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k3_xboole_0(sK2,sK3))
    | k2_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4)) = k3_xboole_0(sK2,k2_xboole_0(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_455,plain,
    ( k2_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4)) = k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))
    | r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))) = iProver_top
    | r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k3_xboole_0(sK2,sK4)) = iProver_top
    | r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k3_xboole_0(sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_454])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X2)
    | ~ r2_hidden(sK0(X0,X1,X2),X0)
    | k2_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f22])).

cnf(c_451,plain,
    ( ~ r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k3_xboole_0(sK2,sK3))
    | k2_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4)) = k3_xboole_0(sK2,k2_xboole_0(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_452,plain,
    ( k2_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4)) = k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))
    | r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))) != iProver_top
    | r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k3_xboole_0(sK2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_451])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | k2_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_448,plain,
    ( ~ r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k3_xboole_0(sK2,sK4))
    | k2_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4)) = k3_xboole_0(sK2,k2_xboole_0(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_449,plain,
    ( k2_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4)) = k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))
    | r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))) != iProver_top
    | r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k3_xboole_0(sK2,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_448])).

cnf(c_12,negated_conjecture,
    ( k2_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4)) != k3_xboole_0(sK2,k2_xboole_0(sK3,sK4)) ),
    inference(cnf_transformation,[],[f30])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9971,c_4393,c_2365,c_1550,c_733,c_730,c_562,c_559,c_531,c_524,c_487,c_484,c_455,c_452,c_449,c_12])).


%------------------------------------------------------------------------------
