%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:22:24 EST 2020

% Result     : Theorem 3.16s
% Output     : CNFRefutation 3.16s
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
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n016.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:24:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.16/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/0.99  
% 3.16/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.16/0.99  
% 3.16/0.99  ------  iProver source info
% 3.16/0.99  
% 3.16/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.16/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.16/0.99  git: non_committed_changes: false
% 3.16/0.99  git: last_make_outside_of_git: false
% 3.16/0.99  
% 3.16/0.99  ------ 
% 3.16/0.99  
% 3.16/0.99  ------ Input Options
% 3.16/0.99  
% 3.16/0.99  --out_options                           all
% 3.16/0.99  --tptp_safe_out                         true
% 3.16/0.99  --problem_path                          ""
% 3.16/0.99  --include_path                          ""
% 3.16/0.99  --clausifier                            res/vclausify_rel
% 3.16/0.99  --clausifier_options                    --mode clausify
% 3.16/0.99  --stdin                                 false
% 3.16/0.99  --stats_out                             all
% 3.16/0.99  
% 3.16/0.99  ------ General Options
% 3.16/0.99  
% 3.16/0.99  --fof                                   false
% 3.16/0.99  --time_out_real                         305.
% 3.16/0.99  --time_out_virtual                      -1.
% 3.16/0.99  --symbol_type_check                     false
% 3.16/0.99  --clausify_out                          false
% 3.16/0.99  --sig_cnt_out                           false
% 3.16/0.99  --trig_cnt_out                          false
% 3.16/0.99  --trig_cnt_out_tolerance                1.
% 3.16/0.99  --trig_cnt_out_sk_spl                   false
% 3.16/0.99  --abstr_cl_out                          false
% 3.16/0.99  
% 3.16/0.99  ------ Global Options
% 3.16/0.99  
% 3.16/0.99  --schedule                              default
% 3.16/0.99  --add_important_lit                     false
% 3.16/0.99  --prop_solver_per_cl                    1000
% 3.16/0.99  --min_unsat_core                        false
% 3.16/0.99  --soft_assumptions                      false
% 3.16/0.99  --soft_lemma_size                       3
% 3.16/0.99  --prop_impl_unit_size                   0
% 3.16/0.99  --prop_impl_unit                        []
% 3.16/0.99  --share_sel_clauses                     true
% 3.16/0.99  --reset_solvers                         false
% 3.16/0.99  --bc_imp_inh                            [conj_cone]
% 3.16/0.99  --conj_cone_tolerance                   3.
% 3.16/0.99  --extra_neg_conj                        none
% 3.16/0.99  --large_theory_mode                     true
% 3.16/0.99  --prolific_symb_bound                   200
% 3.16/0.99  --lt_threshold                          2000
% 3.16/0.99  --clause_weak_htbl                      true
% 3.16/0.99  --gc_record_bc_elim                     false
% 3.16/0.99  
% 3.16/0.99  ------ Preprocessing Options
% 3.16/0.99  
% 3.16/0.99  --preprocessing_flag                    true
% 3.16/0.99  --time_out_prep_mult                    0.1
% 3.16/0.99  --splitting_mode                        input
% 3.16/0.99  --splitting_grd                         true
% 3.16/0.99  --splitting_cvd                         false
% 3.16/0.99  --splitting_cvd_svl                     false
% 3.16/0.99  --splitting_nvd                         32
% 3.16/0.99  --sub_typing                            true
% 3.16/0.99  --prep_gs_sim                           true
% 3.16/0.99  --prep_unflatten                        true
% 3.16/0.99  --prep_res_sim                          true
% 3.16/0.99  --prep_upred                            true
% 3.16/0.99  --prep_sem_filter                       exhaustive
% 3.16/0.99  --prep_sem_filter_out                   false
% 3.16/0.99  --pred_elim                             true
% 3.16/0.99  --res_sim_input                         true
% 3.16/0.99  --eq_ax_congr_red                       true
% 3.16/0.99  --pure_diseq_elim                       true
% 3.16/0.99  --brand_transform                       false
% 3.16/0.99  --non_eq_to_eq                          false
% 3.16/0.99  --prep_def_merge                        true
% 3.16/0.99  --prep_def_merge_prop_impl              false
% 3.16/0.99  --prep_def_merge_mbd                    true
% 3.16/0.99  --prep_def_merge_tr_red                 false
% 3.16/0.99  --prep_def_merge_tr_cl                  false
% 3.16/0.99  --smt_preprocessing                     true
% 3.16/0.99  --smt_ac_axioms                         fast
% 3.16/0.99  --preprocessed_out                      false
% 3.16/0.99  --preprocessed_stats                    false
% 3.16/0.99  
% 3.16/0.99  ------ Abstraction refinement Options
% 3.16/0.99  
% 3.16/0.99  --abstr_ref                             []
% 3.16/0.99  --abstr_ref_prep                        false
% 3.16/0.99  --abstr_ref_until_sat                   false
% 3.16/0.99  --abstr_ref_sig_restrict                funpre
% 3.16/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.16/0.99  --abstr_ref_under                       []
% 3.16/0.99  
% 3.16/0.99  ------ SAT Options
% 3.16/0.99  
% 3.16/0.99  --sat_mode                              false
% 3.16/0.99  --sat_fm_restart_options                ""
% 3.16/0.99  --sat_gr_def                            false
% 3.16/0.99  --sat_epr_types                         true
% 3.16/0.99  --sat_non_cyclic_types                  false
% 3.16/0.99  --sat_finite_models                     false
% 3.16/0.99  --sat_fm_lemmas                         false
% 3.16/0.99  --sat_fm_prep                           false
% 3.16/0.99  --sat_fm_uc_incr                        true
% 3.16/0.99  --sat_out_model                         small
% 3.16/0.99  --sat_out_clauses                       false
% 3.16/0.99  
% 3.16/0.99  ------ QBF Options
% 3.16/0.99  
% 3.16/0.99  --qbf_mode                              false
% 3.16/0.99  --qbf_elim_univ                         false
% 3.16/0.99  --qbf_dom_inst                          none
% 3.16/0.99  --qbf_dom_pre_inst                      false
% 3.16/0.99  --qbf_sk_in                             false
% 3.16/0.99  --qbf_pred_elim                         true
% 3.16/0.99  --qbf_split                             512
% 3.16/0.99  
% 3.16/0.99  ------ BMC1 Options
% 3.16/0.99  
% 3.16/0.99  --bmc1_incremental                      false
% 3.16/0.99  --bmc1_axioms                           reachable_all
% 3.16/0.99  --bmc1_min_bound                        0
% 3.16/0.99  --bmc1_max_bound                        -1
% 3.16/0.99  --bmc1_max_bound_default                -1
% 3.16/0.99  --bmc1_symbol_reachability              true
% 3.16/0.99  --bmc1_property_lemmas                  false
% 3.16/0.99  --bmc1_k_induction                      false
% 3.16/0.99  --bmc1_non_equiv_states                 false
% 3.16/0.99  --bmc1_deadlock                         false
% 3.16/0.99  --bmc1_ucm                              false
% 3.16/0.99  --bmc1_add_unsat_core                   none
% 3.16/0.99  --bmc1_unsat_core_children              false
% 3.16/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.16/0.99  --bmc1_out_stat                         full
% 3.16/0.99  --bmc1_ground_init                      false
% 3.16/0.99  --bmc1_pre_inst_next_state              false
% 3.16/0.99  --bmc1_pre_inst_state                   false
% 3.16/0.99  --bmc1_pre_inst_reach_state             false
% 3.16/0.99  --bmc1_out_unsat_core                   false
% 3.16/0.99  --bmc1_aig_witness_out                  false
% 3.16/0.99  --bmc1_verbose                          false
% 3.16/0.99  --bmc1_dump_clauses_tptp                false
% 3.16/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.16/0.99  --bmc1_dump_file                        -
% 3.16/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.16/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.16/0.99  --bmc1_ucm_extend_mode                  1
% 3.16/0.99  --bmc1_ucm_init_mode                    2
% 3.16/0.99  --bmc1_ucm_cone_mode                    none
% 3.16/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.16/0.99  --bmc1_ucm_relax_model                  4
% 3.16/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.16/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.16/0.99  --bmc1_ucm_layered_model                none
% 3.16/0.99  --bmc1_ucm_max_lemma_size               10
% 3.16/0.99  
% 3.16/0.99  ------ AIG Options
% 3.16/0.99  
% 3.16/0.99  --aig_mode                              false
% 3.16/0.99  
% 3.16/0.99  ------ Instantiation Options
% 3.16/0.99  
% 3.16/0.99  --instantiation_flag                    true
% 3.16/0.99  --inst_sos_flag                         false
% 3.16/0.99  --inst_sos_phase                        true
% 3.16/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.16/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.16/0.99  --inst_lit_sel_side                     num_symb
% 3.16/0.99  --inst_solver_per_active                1400
% 3.16/0.99  --inst_solver_calls_frac                1.
% 3.16/0.99  --inst_passive_queue_type               priority_queues
% 3.16/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.16/0.99  --inst_passive_queues_freq              [25;2]
% 3.16/0.99  --inst_dismatching                      true
% 3.16/0.99  --inst_eager_unprocessed_to_passive     true
% 3.16/0.99  --inst_prop_sim_given                   true
% 3.16/0.99  --inst_prop_sim_new                     false
% 3.16/0.99  --inst_subs_new                         false
% 3.16/0.99  --inst_eq_res_simp                      false
% 3.16/0.99  --inst_subs_given                       false
% 3.16/0.99  --inst_orphan_elimination               true
% 3.16/0.99  --inst_learning_loop_flag               true
% 3.16/0.99  --inst_learning_start                   3000
% 3.16/0.99  --inst_learning_factor                  2
% 3.16/0.99  --inst_start_prop_sim_after_learn       3
% 3.16/0.99  --inst_sel_renew                        solver
% 3.16/0.99  --inst_lit_activity_flag                true
% 3.16/0.99  --inst_restr_to_given                   false
% 3.16/0.99  --inst_activity_threshold               500
% 3.16/0.99  --inst_out_proof                        true
% 3.16/0.99  
% 3.16/0.99  ------ Resolution Options
% 3.16/0.99  
% 3.16/0.99  --resolution_flag                       true
% 3.16/0.99  --res_lit_sel                           adaptive
% 3.16/0.99  --res_lit_sel_side                      none
% 3.16/0.99  --res_ordering                          kbo
% 3.16/0.99  --res_to_prop_solver                    active
% 3.16/0.99  --res_prop_simpl_new                    false
% 3.16/0.99  --res_prop_simpl_given                  true
% 3.16/0.99  --res_passive_queue_type                priority_queues
% 3.16/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.16/0.99  --res_passive_queues_freq               [15;5]
% 3.16/0.99  --res_forward_subs                      full
% 3.16/0.99  --res_backward_subs                     full
% 3.16/0.99  --res_forward_subs_resolution           true
% 3.16/0.99  --res_backward_subs_resolution          true
% 3.16/0.99  --res_orphan_elimination                true
% 3.16/0.99  --res_time_limit                        2.
% 3.16/0.99  --res_out_proof                         true
% 3.16/0.99  
% 3.16/0.99  ------ Superposition Options
% 3.16/0.99  
% 3.16/0.99  --superposition_flag                    true
% 3.16/0.99  --sup_passive_queue_type                priority_queues
% 3.16/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.16/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.16/0.99  --demod_completeness_check              fast
% 3.16/0.99  --demod_use_ground                      true
% 3.16/0.99  --sup_to_prop_solver                    passive
% 3.16/0.99  --sup_prop_simpl_new                    true
% 3.16/0.99  --sup_prop_simpl_given                  true
% 3.16/0.99  --sup_fun_splitting                     false
% 3.16/0.99  --sup_smt_interval                      50000
% 3.16/0.99  
% 3.16/0.99  ------ Superposition Simplification Setup
% 3.16/0.99  
% 3.16/0.99  --sup_indices_passive                   []
% 3.16/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.16/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/0.99  --sup_full_bw                           [BwDemod]
% 3.16/0.99  --sup_immed_triv                        [TrivRules]
% 3.16/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.16/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/0.99  --sup_immed_bw_main                     []
% 3.16/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.16/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.16/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.16/0.99  
% 3.16/0.99  ------ Combination Options
% 3.16/0.99  
% 3.16/0.99  --comb_res_mult                         3
% 3.16/0.99  --comb_sup_mult                         2
% 3.16/0.99  --comb_inst_mult                        10
% 3.16/0.99  
% 3.16/0.99  ------ Debug Options
% 3.16/0.99  
% 3.16/0.99  --dbg_backtrace                         false
% 3.16/0.99  --dbg_dump_prop_clauses                 false
% 3.16/0.99  --dbg_dump_prop_clauses_file            -
% 3.16/0.99  --dbg_out_stat                          false
% 3.16/0.99  ------ Parsing...
% 3.16/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.16/0.99  
% 3.16/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.16/0.99  
% 3.16/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.16/0.99  
% 3.16/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.16/0.99  ------ Proving...
% 3.16/0.99  ------ Problem Properties 
% 3.16/0.99  
% 3.16/0.99  
% 3.16/0.99  clauses                                 13
% 3.16/0.99  conjectures                             1
% 3.16/0.99  EPR                                     0
% 3.16/0.99  Horn                                    9
% 3.16/0.99  unary                                   1
% 3.16/0.99  binary                                  4
% 3.16/0.99  lits                                    35
% 3.16/0.99  lits eq                                 7
% 3.16/0.99  fd_pure                                 0
% 3.16/0.99  fd_pseudo                               0
% 3.16/0.99  fd_cond                                 0
% 3.16/0.99  fd_pseudo_cond                          6
% 3.16/0.99  AC symbols                              0
% 3.16/0.99  
% 3.16/0.99  ------ Schedule dynamic 5 is on 
% 3.16/0.99  
% 3.16/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.16/0.99  
% 3.16/0.99  
% 3.16/0.99  ------ 
% 3.16/0.99  Current options:
% 3.16/0.99  ------ 
% 3.16/0.99  
% 3.16/0.99  ------ Input Options
% 3.16/0.99  
% 3.16/0.99  --out_options                           all
% 3.16/0.99  --tptp_safe_out                         true
% 3.16/0.99  --problem_path                          ""
% 3.16/0.99  --include_path                          ""
% 3.16/0.99  --clausifier                            res/vclausify_rel
% 3.16/0.99  --clausifier_options                    --mode clausify
% 3.16/0.99  --stdin                                 false
% 3.16/0.99  --stats_out                             all
% 3.16/0.99  
% 3.16/0.99  ------ General Options
% 3.16/0.99  
% 3.16/0.99  --fof                                   false
% 3.16/0.99  --time_out_real                         305.
% 3.16/0.99  --time_out_virtual                      -1.
% 3.16/0.99  --symbol_type_check                     false
% 3.16/0.99  --clausify_out                          false
% 3.16/0.99  --sig_cnt_out                           false
% 3.16/0.99  --trig_cnt_out                          false
% 3.16/0.99  --trig_cnt_out_tolerance                1.
% 3.16/0.99  --trig_cnt_out_sk_spl                   false
% 3.16/0.99  --abstr_cl_out                          false
% 3.16/0.99  
% 3.16/0.99  ------ Global Options
% 3.16/0.99  
% 3.16/0.99  --schedule                              default
% 3.16/0.99  --add_important_lit                     false
% 3.16/0.99  --prop_solver_per_cl                    1000
% 3.16/0.99  --min_unsat_core                        false
% 3.16/0.99  --soft_assumptions                      false
% 3.16/0.99  --soft_lemma_size                       3
% 3.16/0.99  --prop_impl_unit_size                   0
% 3.16/0.99  --prop_impl_unit                        []
% 3.16/0.99  --share_sel_clauses                     true
% 3.16/0.99  --reset_solvers                         false
% 3.16/0.99  --bc_imp_inh                            [conj_cone]
% 3.16/0.99  --conj_cone_tolerance                   3.
% 3.16/0.99  --extra_neg_conj                        none
% 3.16/0.99  --large_theory_mode                     true
% 3.16/0.99  --prolific_symb_bound                   200
% 3.16/0.99  --lt_threshold                          2000
% 3.16/0.99  --clause_weak_htbl                      true
% 3.16/0.99  --gc_record_bc_elim                     false
% 3.16/0.99  
% 3.16/0.99  ------ Preprocessing Options
% 3.16/0.99  
% 3.16/0.99  --preprocessing_flag                    true
% 3.16/0.99  --time_out_prep_mult                    0.1
% 3.16/0.99  --splitting_mode                        input
% 3.16/0.99  --splitting_grd                         true
% 3.16/0.99  --splitting_cvd                         false
% 3.16/0.99  --splitting_cvd_svl                     false
% 3.16/0.99  --splitting_nvd                         32
% 3.16/0.99  --sub_typing                            true
% 3.16/0.99  --prep_gs_sim                           true
% 3.16/0.99  --prep_unflatten                        true
% 3.16/0.99  --prep_res_sim                          true
% 3.16/0.99  --prep_upred                            true
% 3.16/0.99  --prep_sem_filter                       exhaustive
% 3.16/0.99  --prep_sem_filter_out                   false
% 3.16/0.99  --pred_elim                             true
% 3.16/0.99  --res_sim_input                         true
% 3.16/0.99  --eq_ax_congr_red                       true
% 3.16/0.99  --pure_diseq_elim                       true
% 3.16/0.99  --brand_transform                       false
% 3.16/0.99  --non_eq_to_eq                          false
% 3.16/0.99  --prep_def_merge                        true
% 3.16/0.99  --prep_def_merge_prop_impl              false
% 3.16/0.99  --prep_def_merge_mbd                    true
% 3.16/0.99  --prep_def_merge_tr_red                 false
% 3.16/0.99  --prep_def_merge_tr_cl                  false
% 3.16/0.99  --smt_preprocessing                     true
% 3.16/0.99  --smt_ac_axioms                         fast
% 3.16/0.99  --preprocessed_out                      false
% 3.16/0.99  --preprocessed_stats                    false
% 3.16/0.99  
% 3.16/0.99  ------ Abstraction refinement Options
% 3.16/0.99  
% 3.16/0.99  --abstr_ref                             []
% 3.16/0.99  --abstr_ref_prep                        false
% 3.16/0.99  --abstr_ref_until_sat                   false
% 3.16/0.99  --abstr_ref_sig_restrict                funpre
% 3.16/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.16/0.99  --abstr_ref_under                       []
% 3.16/0.99  
% 3.16/0.99  ------ SAT Options
% 3.16/0.99  
% 3.16/0.99  --sat_mode                              false
% 3.16/0.99  --sat_fm_restart_options                ""
% 3.16/0.99  --sat_gr_def                            false
% 3.16/0.99  --sat_epr_types                         true
% 3.16/0.99  --sat_non_cyclic_types                  false
% 3.16/0.99  --sat_finite_models                     false
% 3.16/0.99  --sat_fm_lemmas                         false
% 3.16/0.99  --sat_fm_prep                           false
% 3.16/0.99  --sat_fm_uc_incr                        true
% 3.16/0.99  --sat_out_model                         small
% 3.16/0.99  --sat_out_clauses                       false
% 3.16/0.99  
% 3.16/0.99  ------ QBF Options
% 3.16/0.99  
% 3.16/0.99  --qbf_mode                              false
% 3.16/0.99  --qbf_elim_univ                         false
% 3.16/0.99  --qbf_dom_inst                          none
% 3.16/0.99  --qbf_dom_pre_inst                      false
% 3.16/0.99  --qbf_sk_in                             false
% 3.16/0.99  --qbf_pred_elim                         true
% 3.16/0.99  --qbf_split                             512
% 3.16/0.99  
% 3.16/0.99  ------ BMC1 Options
% 3.16/0.99  
% 3.16/0.99  --bmc1_incremental                      false
% 3.16/0.99  --bmc1_axioms                           reachable_all
% 3.16/0.99  --bmc1_min_bound                        0
% 3.16/0.99  --bmc1_max_bound                        -1
% 3.16/0.99  --bmc1_max_bound_default                -1
% 3.16/0.99  --bmc1_symbol_reachability              true
% 3.16/0.99  --bmc1_property_lemmas                  false
% 3.16/0.99  --bmc1_k_induction                      false
% 3.16/0.99  --bmc1_non_equiv_states                 false
% 3.16/0.99  --bmc1_deadlock                         false
% 3.16/0.99  --bmc1_ucm                              false
% 3.16/0.99  --bmc1_add_unsat_core                   none
% 3.16/0.99  --bmc1_unsat_core_children              false
% 3.16/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.16/0.99  --bmc1_out_stat                         full
% 3.16/0.99  --bmc1_ground_init                      false
% 3.16/0.99  --bmc1_pre_inst_next_state              false
% 3.16/0.99  --bmc1_pre_inst_state                   false
% 3.16/0.99  --bmc1_pre_inst_reach_state             false
% 3.16/0.99  --bmc1_out_unsat_core                   false
% 3.16/0.99  --bmc1_aig_witness_out                  false
% 3.16/0.99  --bmc1_verbose                          false
% 3.16/0.99  --bmc1_dump_clauses_tptp                false
% 3.16/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.16/0.99  --bmc1_dump_file                        -
% 3.16/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.16/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.16/0.99  --bmc1_ucm_extend_mode                  1
% 3.16/0.99  --bmc1_ucm_init_mode                    2
% 3.16/0.99  --bmc1_ucm_cone_mode                    none
% 3.16/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.16/0.99  --bmc1_ucm_relax_model                  4
% 3.16/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.16/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.16/0.99  --bmc1_ucm_layered_model                none
% 3.16/0.99  --bmc1_ucm_max_lemma_size               10
% 3.16/0.99  
% 3.16/0.99  ------ AIG Options
% 3.16/0.99  
% 3.16/0.99  --aig_mode                              false
% 3.16/0.99  
% 3.16/0.99  ------ Instantiation Options
% 3.16/0.99  
% 3.16/0.99  --instantiation_flag                    true
% 3.16/0.99  --inst_sos_flag                         false
% 3.16/0.99  --inst_sos_phase                        true
% 3.16/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.16/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.16/0.99  --inst_lit_sel_side                     none
% 3.16/0.99  --inst_solver_per_active                1400
% 3.16/0.99  --inst_solver_calls_frac                1.
% 3.16/0.99  --inst_passive_queue_type               priority_queues
% 3.16/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.16/0.99  --inst_passive_queues_freq              [25;2]
% 3.16/0.99  --inst_dismatching                      true
% 3.16/0.99  --inst_eager_unprocessed_to_passive     true
% 3.16/0.99  --inst_prop_sim_given                   true
% 3.16/0.99  --inst_prop_sim_new                     false
% 3.16/0.99  --inst_subs_new                         false
% 3.16/0.99  --inst_eq_res_simp                      false
% 3.16/0.99  --inst_subs_given                       false
% 3.16/0.99  --inst_orphan_elimination               true
% 3.16/0.99  --inst_learning_loop_flag               true
% 3.16/0.99  --inst_learning_start                   3000
% 3.16/0.99  --inst_learning_factor                  2
% 3.16/0.99  --inst_start_prop_sim_after_learn       3
% 3.16/0.99  --inst_sel_renew                        solver
% 3.16/0.99  --inst_lit_activity_flag                true
% 3.16/0.99  --inst_restr_to_given                   false
% 3.16/0.99  --inst_activity_threshold               500
% 3.16/0.99  --inst_out_proof                        true
% 3.16/0.99  
% 3.16/0.99  ------ Resolution Options
% 3.16/0.99  
% 3.16/0.99  --resolution_flag                       false
% 3.16/0.99  --res_lit_sel                           adaptive
% 3.16/0.99  --res_lit_sel_side                      none
% 3.16/0.99  --res_ordering                          kbo
% 3.16/0.99  --res_to_prop_solver                    active
% 3.16/0.99  --res_prop_simpl_new                    false
% 3.16/0.99  --res_prop_simpl_given                  true
% 3.16/0.99  --res_passive_queue_type                priority_queues
% 3.16/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.16/0.99  --res_passive_queues_freq               [15;5]
% 3.16/0.99  --res_forward_subs                      full
% 3.16/0.99  --res_backward_subs                     full
% 3.16/0.99  --res_forward_subs_resolution           true
% 3.16/0.99  --res_backward_subs_resolution          true
% 3.16/0.99  --res_orphan_elimination                true
% 3.16/0.99  --res_time_limit                        2.
% 3.16/0.99  --res_out_proof                         true
% 3.16/0.99  
% 3.16/0.99  ------ Superposition Options
% 3.16/0.99  
% 3.16/0.99  --superposition_flag                    true
% 3.16/0.99  --sup_passive_queue_type                priority_queues
% 3.16/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.16/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.16/0.99  --demod_completeness_check              fast
% 3.16/0.99  --demod_use_ground                      true
% 3.16/0.99  --sup_to_prop_solver                    passive
% 3.16/0.99  --sup_prop_simpl_new                    true
% 3.16/0.99  --sup_prop_simpl_given                  true
% 3.16/0.99  --sup_fun_splitting                     false
% 3.16/0.99  --sup_smt_interval                      50000
% 3.16/0.99  
% 3.16/0.99  ------ Superposition Simplification Setup
% 3.16/0.99  
% 3.16/0.99  --sup_indices_passive                   []
% 3.16/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.16/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/0.99  --sup_full_bw                           [BwDemod]
% 3.16/0.99  --sup_immed_triv                        [TrivRules]
% 3.16/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.16/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/0.99  --sup_immed_bw_main                     []
% 3.16/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.16/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.16/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.16/0.99  
% 3.16/0.99  ------ Combination Options
% 3.16/0.99  
% 3.16/0.99  --comb_res_mult                         3
% 3.16/0.99  --comb_sup_mult                         2
% 3.16/0.99  --comb_inst_mult                        10
% 3.16/0.99  
% 3.16/0.99  ------ Debug Options
% 3.16/0.99  
% 3.16/0.99  --dbg_backtrace                         false
% 3.16/0.99  --dbg_dump_prop_clauses                 false
% 3.16/0.99  --dbg_dump_prop_clauses_file            -
% 3.16/0.99  --dbg_out_stat                          false
% 3.16/0.99  
% 3.16/0.99  
% 3.16/0.99  
% 3.16/0.99  
% 3.16/0.99  ------ Proving...
% 3.16/0.99  
% 3.16/0.99  
% 3.16/0.99  % SZS status Theorem for theBenchmark.p
% 3.16/0.99  
% 3.16/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.16/0.99  
% 3.16/0.99  fof(f1,axiom,(
% 3.16/0.99    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 3.16/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/0.99  
% 3.16/0.99  fof(f6,plain,(
% 3.16/0.99    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.16/0.99    inference(nnf_transformation,[],[f1])).
% 3.16/0.99  
% 3.16/0.99  fof(f7,plain,(
% 3.16/0.99    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.16/0.99    inference(flattening,[],[f6])).
% 3.16/0.99  
% 3.16/0.99  fof(f8,plain,(
% 3.16/0.99    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.16/0.99    inference(rectify,[],[f7])).
% 3.16/0.99  
% 3.16/0.99  fof(f9,plain,(
% 3.16/0.99    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.16/0.99    introduced(choice_axiom,[])).
% 3.16/0.99  
% 3.16/0.99  fof(f10,plain,(
% 3.16/0.99    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.16/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f9])).
% 3.16/0.99  
% 3.16/0.99  fof(f20,plain,(
% 3.16/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 3.16/0.99    inference(cnf_transformation,[],[f10])).
% 3.16/0.99  
% 3.16/0.99  fof(f31,plain,(
% 3.16/0.99    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 3.16/0.99    inference(equality_resolution,[],[f20])).
% 3.16/0.99  
% 3.16/0.99  fof(f19,plain,(
% 3.16/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 3.16/0.99    inference(cnf_transformation,[],[f10])).
% 3.16/0.99  
% 3.16/0.99  fof(f32,plain,(
% 3.16/0.99    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X0)) )),
% 3.16/0.99    inference(equality_resolution,[],[f19])).
% 3.16/0.99  
% 3.16/0.99  fof(f2,axiom,(
% 3.16/0.99    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.16/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/0.99  
% 3.16/0.99  fof(f11,plain,(
% 3.16/0.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.16/0.99    inference(nnf_transformation,[],[f2])).
% 3.16/0.99  
% 3.16/0.99  fof(f12,plain,(
% 3.16/0.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.16/0.99    inference(flattening,[],[f11])).
% 3.16/0.99  
% 3.16/0.99  fof(f13,plain,(
% 3.16/0.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.16/0.99    inference(rectify,[],[f12])).
% 3.16/0.99  
% 3.16/0.99  fof(f14,plain,(
% 3.16/0.99    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 3.16/0.99    introduced(choice_axiom,[])).
% 3.16/0.99  
% 3.16/0.99  fof(f15,plain,(
% 3.16/0.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.16/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f14])).
% 3.16/0.99  
% 3.16/0.99  fof(f26,plain,(
% 3.16/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 3.16/0.99    inference(cnf_transformation,[],[f15])).
% 3.16/0.99  
% 3.16/0.99  fof(f34,plain,(
% 3.16/0.99    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_xboole_0(X0,X1)) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 3.16/0.99    inference(equality_resolution,[],[f26])).
% 3.16/0.99  
% 3.16/0.99  fof(f24,plain,(
% 3.16/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 3.16/0.99    inference(cnf_transformation,[],[f15])).
% 3.16/0.99  
% 3.16/0.99  fof(f36,plain,(
% 3.16/0.99    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 3.16/0.99    inference(equality_resolution,[],[f24])).
% 3.16/0.99  
% 3.16/0.99  fof(f25,plain,(
% 3.16/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 3.16/0.99    inference(cnf_transformation,[],[f15])).
% 3.16/0.99  
% 3.16/0.99  fof(f35,plain,(
% 3.16/0.99    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 3.16/0.99    inference(equality_resolution,[],[f25])).
% 3.16/0.99  
% 3.16/0.99  fof(f18,plain,(
% 3.16/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 3.16/0.99    inference(cnf_transformation,[],[f10])).
% 3.16/0.99  
% 3.16/0.99  fof(f33,plain,(
% 3.16/0.99    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,k2_xboole_0(X0,X1))) )),
% 3.16/0.99    inference(equality_resolution,[],[f18])).
% 3.16/0.99  
% 3.16/0.99  fof(f21,plain,(
% 3.16/0.99    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.16/0.99    inference(cnf_transformation,[],[f10])).
% 3.16/0.99  
% 3.16/0.99  fof(f22,plain,(
% 3.16/0.99    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.16/0.99    inference(cnf_transformation,[],[f10])).
% 3.16/0.99  
% 3.16/0.99  fof(f23,plain,(
% 3.16/0.99    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.16/0.99    inference(cnf_transformation,[],[f10])).
% 3.16/0.99  
% 3.16/0.99  fof(f3,conjecture,(
% 3.16/0.99    ! [X0,X1,X2] : k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2))),
% 3.16/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/0.99  
% 3.16/0.99  fof(f4,negated_conjecture,(
% 3.16/0.99    ~! [X0,X1,X2] : k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2))),
% 3.16/0.99    inference(negated_conjecture,[],[f3])).
% 3.16/0.99  
% 3.16/0.99  fof(f5,plain,(
% 3.16/0.99    ? [X0,X1,X2] : k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) != k3_xboole_0(X0,k2_xboole_0(X1,X2))),
% 3.16/0.99    inference(ennf_transformation,[],[f4])).
% 3.16/0.99  
% 3.16/0.99  fof(f16,plain,(
% 3.16/0.99    ? [X0,X1,X2] : k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) != k3_xboole_0(X0,k2_xboole_0(X1,X2)) => k2_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4)) != k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),
% 3.16/0.99    introduced(choice_axiom,[])).
% 3.16/0.99  
% 3.16/0.99  fof(f17,plain,(
% 3.16/0.99    k2_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4)) != k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),
% 3.16/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f5,f16])).
% 3.16/0.99  
% 3.16/0.99  fof(f30,plain,(
% 3.16/0.99    k2_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4)) != k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),
% 3.16/0.99    inference(cnf_transformation,[],[f17])).
% 3.16/0.99  
% 3.16/0.99  cnf(c_3,plain,
% 3.16/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,k2_xboole_0(X2,X1)) ),
% 3.16/0.99      inference(cnf_transformation,[],[f31]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_2791,plain,
% 3.16/0.99      ( ~ r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),X0)
% 3.16/0.99      | r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k2_xboole_0(X1,X0)) ),
% 3.16/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_9970,plain,
% 3.16/0.99      ( r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k2_xboole_0(sK3,sK4))
% 3.16/0.99      | ~ r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),sK4) ),
% 3.16/0.99      inference(instantiation,[status(thm)],[c_2791]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_9971,plain,
% 3.16/0.99      ( r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k2_xboole_0(sK3,sK4)) = iProver_top
% 3.16/0.99      | r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),sK4) != iProver_top ),
% 3.16/0.99      inference(predicate_to_equality,[status(thm)],[c_9970]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_4,plain,
% 3.16/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,k2_xboole_0(X1,X2)) ),
% 3.16/0.99      inference(cnf_transformation,[],[f32]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_2353,plain,
% 3.16/0.99      ( r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k2_xboole_0(sK3,X0))
% 3.16/0.99      | ~ r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),sK3) ),
% 3.16/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_4392,plain,
% 3.16/0.99      ( r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k2_xboole_0(sK3,sK4))
% 3.16/0.99      | ~ r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),sK3) ),
% 3.16/0.99      inference(instantiation,[status(thm)],[c_2353]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_4393,plain,
% 3.16/0.99      ( r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k2_xboole_0(sK3,sK4)) = iProver_top
% 3.16/0.99      | r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),sK3) != iProver_top ),
% 3.16/0.99      inference(predicate_to_equality,[status(thm)],[c_4392]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_9,plain,
% 3.16/0.99      ( ~ r2_hidden(X0,X1)
% 3.16/0.99      | ~ r2_hidden(X0,X2)
% 3.16/0.99      | r2_hidden(X0,k3_xboole_0(X2,X1)) ),
% 3.16/0.99      inference(cnf_transformation,[],[f34]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_2352,plain,
% 3.16/0.99      ( ~ r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),X0)
% 3.16/0.99      | r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k3_xboole_0(X0,sK3))
% 3.16/0.99      | ~ r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),sK3) ),
% 3.16/0.99      inference(instantiation,[status(thm)],[c_9]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_2363,plain,
% 3.16/0.99      ( r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),X0) != iProver_top
% 3.16/0.99      | r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k3_xboole_0(X0,sK3)) = iProver_top
% 3.16/0.99      | r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),sK3) != iProver_top ),
% 3.16/0.99      inference(predicate_to_equality,[status(thm)],[c_2352]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_2365,plain,
% 3.16/0.99      ( r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k3_xboole_0(sK2,sK3)) = iProver_top
% 3.16/0.99      | r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),sK3) != iProver_top
% 3.16/0.99      | r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),sK2) != iProver_top ),
% 3.16/0.99      inference(instantiation,[status(thm)],[c_2363]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_1537,plain,
% 3.16/0.99      ( ~ r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),X0)
% 3.16/0.99      | r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k3_xboole_0(X0,sK4))
% 3.16/0.99      | ~ r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),sK4) ),
% 3.16/0.99      inference(instantiation,[status(thm)],[c_9]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_1548,plain,
% 3.16/0.99      ( r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),X0) != iProver_top
% 3.16/0.99      | r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k3_xboole_0(X0,sK4)) = iProver_top
% 3.16/0.99      | r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),sK4) != iProver_top ),
% 3.16/0.99      inference(predicate_to_equality,[status(thm)],[c_1537]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_1550,plain,
% 3.16/0.99      ( r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k3_xboole_0(sK2,sK4)) = iProver_top
% 3.16/0.99      | r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),sK4) != iProver_top
% 3.16/0.99      | r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),sK2) != iProver_top ),
% 3.16/0.99      inference(instantiation,[status(thm)],[c_1548]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_11,plain,
% 3.16/0.99      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k3_xboole_0(X1,X2)) ),
% 3.16/0.99      inference(cnf_transformation,[],[f36]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_732,plain,
% 3.16/0.99      ( ~ r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k3_xboole_0(sK2,sK3))
% 3.16/0.99      | r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),sK2) ),
% 3.16/0.99      inference(instantiation,[status(thm)],[c_11]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_733,plain,
% 3.16/0.99      ( r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k3_xboole_0(sK2,sK3)) != iProver_top
% 3.16/0.99      | r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),sK2) = iProver_top ),
% 3.16/0.99      inference(predicate_to_equality,[status(thm)],[c_732]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_10,plain,
% 3.16/0.99      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
% 3.16/0.99      inference(cnf_transformation,[],[f35]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_729,plain,
% 3.16/0.99      ( ~ r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k3_xboole_0(sK2,sK3))
% 3.16/0.99      | r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),sK3) ),
% 3.16/0.99      inference(instantiation,[status(thm)],[c_10]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_730,plain,
% 3.16/0.99      ( r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k3_xboole_0(sK2,sK3)) != iProver_top
% 3.16/0.99      | r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),sK3) = iProver_top ),
% 3.16/0.99      inference(predicate_to_equality,[status(thm)],[c_729]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_561,plain,
% 3.16/0.99      ( ~ r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k3_xboole_0(sK2,sK4))
% 3.16/0.99      | r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),sK2) ),
% 3.16/0.99      inference(instantiation,[status(thm)],[c_11]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_562,plain,
% 3.16/0.99      ( r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k3_xboole_0(sK2,sK4)) != iProver_top
% 3.16/0.99      | r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),sK2) = iProver_top ),
% 3.16/0.99      inference(predicate_to_equality,[status(thm)],[c_561]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_558,plain,
% 3.16/0.99      ( ~ r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k3_xboole_0(sK2,sK4))
% 3.16/0.99      | r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),sK4) ),
% 3.16/0.99      inference(instantiation,[status(thm)],[c_10]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_559,plain,
% 3.16/0.99      ( r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k3_xboole_0(sK2,sK4)) != iProver_top
% 3.16/0.99      | r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),sK4) = iProver_top ),
% 3.16/0.99      inference(predicate_to_equality,[status(thm)],[c_558]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_5,plain,
% 3.16/0.99      ( r2_hidden(X0,X1)
% 3.16/0.99      | r2_hidden(X0,X2)
% 3.16/0.99      | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ),
% 3.16/0.99      inference(cnf_transformation,[],[f33]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_530,plain,
% 3.16/0.99      ( ~ r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k2_xboole_0(sK3,sK4))
% 3.16/0.99      | r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),sK4)
% 3.16/0.99      | r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),sK3) ),
% 3.16/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_531,plain,
% 3.16/0.99      ( r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k2_xboole_0(sK3,sK4)) != iProver_top
% 3.16/0.99      | r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),sK4) = iProver_top
% 3.16/0.99      | r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),sK3) = iProver_top ),
% 3.16/0.99      inference(predicate_to_equality,[status(thm)],[c_530]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_511,plain,
% 3.16/0.99      ( ~ r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),X0)
% 3.16/0.99      | r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k3_xboole_0(X0,k2_xboole_0(sK3,sK4)))
% 3.16/0.99      | ~ r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k2_xboole_0(sK3,sK4)) ),
% 3.16/0.99      inference(instantiation,[status(thm)],[c_9]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_522,plain,
% 3.16/0.99      ( r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),X0) != iProver_top
% 3.16/0.99      | r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k3_xboole_0(X0,k2_xboole_0(sK3,sK4))) = iProver_top
% 3.16/0.99      | r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k2_xboole_0(sK3,sK4)) != iProver_top ),
% 3.16/0.99      inference(predicate_to_equality,[status(thm)],[c_511]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_524,plain,
% 3.16/0.99      ( r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))) = iProver_top
% 3.16/0.99      | r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k2_xboole_0(sK3,sK4)) != iProver_top
% 3.16/0.99      | r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),sK2) != iProver_top ),
% 3.16/0.99      inference(instantiation,[status(thm)],[c_522]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_486,plain,
% 3.16/0.99      ( ~ r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4)))
% 3.16/0.99      | r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),sK2) ),
% 3.16/0.99      inference(instantiation,[status(thm)],[c_11]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_487,plain,
% 3.16/0.99      ( r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))) != iProver_top
% 3.16/0.99      | r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),sK2) = iProver_top ),
% 3.16/0.99      inference(predicate_to_equality,[status(thm)],[c_486]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_483,plain,
% 3.16/0.99      ( ~ r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4)))
% 3.16/0.99      | r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k2_xboole_0(sK3,sK4)) ),
% 3.16/0.99      inference(instantiation,[status(thm)],[c_10]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_484,plain,
% 3.16/0.99      ( r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))) != iProver_top
% 3.16/0.99      | r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k2_xboole_0(sK3,sK4)) = iProver_top ),
% 3.16/0.99      inference(predicate_to_equality,[status(thm)],[c_483]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_2,plain,
% 3.16/0.99      ( r2_hidden(sK0(X0,X1,X2),X1)
% 3.16/0.99      | r2_hidden(sK0(X0,X1,X2),X2)
% 3.16/0.99      | r2_hidden(sK0(X0,X1,X2),X0)
% 3.16/0.99      | k2_xboole_0(X0,X1) = X2 ),
% 3.16/0.99      inference(cnf_transformation,[],[f21]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_454,plain,
% 3.16/0.99      ( r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4)))
% 3.16/0.99      | r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k3_xboole_0(sK2,sK4))
% 3.16/0.99      | r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k3_xboole_0(sK2,sK3))
% 3.16/0.99      | k2_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4)) = k3_xboole_0(sK2,k2_xboole_0(sK3,sK4)) ),
% 3.16/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_455,plain,
% 3.16/0.99      ( k2_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4)) = k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))
% 3.16/0.99      | r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))) = iProver_top
% 3.16/0.99      | r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k3_xboole_0(sK2,sK4)) = iProver_top
% 3.16/0.99      | r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k3_xboole_0(sK2,sK3)) = iProver_top ),
% 3.16/0.99      inference(predicate_to_equality,[status(thm)],[c_454]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_1,plain,
% 3.16/0.99      ( ~ r2_hidden(sK0(X0,X1,X2),X2)
% 3.16/0.99      | ~ r2_hidden(sK0(X0,X1,X2),X0)
% 3.16/0.99      | k2_xboole_0(X0,X1) = X2 ),
% 3.16/0.99      inference(cnf_transformation,[],[f22]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_451,plain,
% 3.16/0.99      ( ~ r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4)))
% 3.16/0.99      | ~ r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k3_xboole_0(sK2,sK3))
% 3.16/0.99      | k2_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4)) = k3_xboole_0(sK2,k2_xboole_0(sK3,sK4)) ),
% 3.16/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_452,plain,
% 3.16/0.99      ( k2_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4)) = k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))
% 3.16/0.99      | r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))) != iProver_top
% 3.16/0.99      | r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k3_xboole_0(sK2,sK3)) != iProver_top ),
% 3.16/0.99      inference(predicate_to_equality,[status(thm)],[c_451]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_0,plain,
% 3.16/0.99      ( ~ r2_hidden(sK0(X0,X1,X2),X1)
% 3.16/0.99      | ~ r2_hidden(sK0(X0,X1,X2),X2)
% 3.16/0.99      | k2_xboole_0(X0,X1) = X2 ),
% 3.16/0.99      inference(cnf_transformation,[],[f23]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_448,plain,
% 3.16/0.99      ( ~ r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4)))
% 3.16/0.99      | ~ r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k3_xboole_0(sK2,sK4))
% 3.16/0.99      | k2_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4)) = k3_xboole_0(sK2,k2_xboole_0(sK3,sK4)) ),
% 3.16/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_449,plain,
% 3.16/0.99      ( k2_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4)) = k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))
% 3.16/0.99      | r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))) != iProver_top
% 3.16/0.99      | r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4),k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k3_xboole_0(sK2,sK4)) != iProver_top ),
% 3.16/0.99      inference(predicate_to_equality,[status(thm)],[c_448]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(c_12,negated_conjecture,
% 3.16/0.99      ( k2_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK4)) != k3_xboole_0(sK2,k2_xboole_0(sK3,sK4)) ),
% 3.16/0.99      inference(cnf_transformation,[],[f30]) ).
% 3.16/0.99  
% 3.16/0.99  cnf(contradiction,plain,
% 3.16/0.99      ( $false ),
% 3.16/0.99      inference(minisat,
% 3.16/0.99                [status(thm)],
% 3.16/0.99                [c_9971,c_4393,c_2365,c_1550,c_733,c_730,c_562,c_559,
% 3.16/0.99                 c_531,c_524,c_487,c_484,c_455,c_452,c_449,c_12]) ).
% 3.16/0.99  
% 3.16/0.99  
% 3.16/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.16/0.99  
% 3.16/0.99  ------                               Statistics
% 3.16/0.99  
% 3.16/0.99  ------ General
% 3.16/0.99  
% 3.16/0.99  abstr_ref_over_cycles:                  0
% 3.16/0.99  abstr_ref_under_cycles:                 0
% 3.16/0.99  gc_basic_clause_elim:                   0
% 3.16/0.99  forced_gc_time:                         0
% 3.16/0.99  parsing_time:                           0.009
% 3.16/0.99  unif_index_cands_time:                  0.
% 3.16/0.99  unif_index_add_time:                    0.
% 3.16/0.99  orderings_time:                         0.
% 3.16/0.99  out_proof_time:                         0.008
% 3.16/0.99  total_time:                             0.298
% 3.16/0.99  num_of_symbols:                         39
% 3.16/0.99  num_of_terms:                           13817
% 3.16/0.99  
% 3.16/0.99  ------ Preprocessing
% 3.16/0.99  
% 3.16/0.99  num_of_splits:                          0
% 3.16/0.99  num_of_split_atoms:                     0
% 3.16/0.99  num_of_reused_defs:                     0
% 3.16/0.99  num_eq_ax_congr_red:                    12
% 3.16/0.99  num_of_sem_filtered_clauses:            1
% 3.16/0.99  num_of_subtypes:                        0
% 3.16/0.99  monotx_restored_types:                  0
% 3.16/0.99  sat_num_of_epr_types:                   0
% 3.16/0.99  sat_num_of_non_cyclic_types:            0
% 3.16/0.99  sat_guarded_non_collapsed_types:        0
% 3.16/0.99  num_pure_diseq_elim:                    0
% 3.16/0.99  simp_replaced_by:                       0
% 3.16/0.99  res_preprocessed:                       50
% 3.16/0.99  prep_upred:                             0
% 3.16/0.99  prep_unflattend:                        0
% 3.16/0.99  smt_new_axioms:                         0
% 3.16/0.99  pred_elim_cands:                        1
% 3.16/0.99  pred_elim:                              0
% 3.16/0.99  pred_elim_cl:                           0
% 3.16/0.99  pred_elim_cycles:                       1
% 3.16/0.99  merged_defs:                            0
% 3.16/0.99  merged_defs_ncl:                        0
% 3.16/0.99  bin_hyper_res:                          0
% 3.16/0.99  prep_cycles:                            3
% 3.16/0.99  pred_elim_time:                         0.
% 3.16/0.99  splitting_time:                         0.
% 3.16/0.99  sem_filter_time:                        0.
% 3.16/0.99  monotx_time:                            0.
% 3.16/0.99  subtype_inf_time:                       0.
% 3.16/0.99  
% 3.16/0.99  ------ Problem properties
% 3.16/0.99  
% 3.16/0.99  clauses:                                13
% 3.16/0.99  conjectures:                            1
% 3.16/0.99  epr:                                    0
% 3.16/0.99  horn:                                   9
% 3.16/0.99  ground:                                 1
% 3.16/0.99  unary:                                  1
% 3.16/0.99  binary:                                 4
% 3.16/0.99  lits:                                   35
% 3.16/0.99  lits_eq:                                7
% 3.16/0.99  fd_pure:                                0
% 3.16/0.99  fd_pseudo:                              0
% 3.16/0.99  fd_cond:                                0
% 3.16/0.99  fd_pseudo_cond:                         6
% 3.16/0.99  ac_symbols:                             0
% 3.16/0.99  
% 3.16/0.99  ------ Propositional Solver
% 3.16/0.99  
% 3.16/0.99  prop_solver_calls:                      25
% 3.16/0.99  prop_fast_solver_calls:                 431
% 3.16/0.99  smt_solver_calls:                       0
% 3.16/0.99  smt_fast_solver_calls:                  0
% 3.16/0.99  prop_num_of_clauses:                    3228
% 3.16/0.99  prop_preprocess_simplified:             6730
% 3.16/0.99  prop_fo_subsumed:                       0
% 3.16/0.99  prop_solver_time:                       0.
% 3.16/0.99  smt_solver_time:                        0.
% 3.16/0.99  smt_fast_solver_time:                   0.
% 3.16/0.99  prop_fast_solver_time:                  0.
% 3.16/0.99  prop_unsat_core_time:                   0.
% 3.16/0.99  
% 3.16/0.99  ------ QBF
% 3.16/0.99  
% 3.16/0.99  qbf_q_res:                              0
% 3.16/0.99  qbf_num_tautologies:                    0
% 3.16/0.99  qbf_prep_cycles:                        0
% 3.16/0.99  
% 3.16/0.99  ------ BMC1
% 3.16/0.99  
% 3.16/0.99  bmc1_current_bound:                     -1
% 3.16/0.99  bmc1_last_solved_bound:                 -1
% 3.16/0.99  bmc1_unsat_core_size:                   -1
% 3.16/0.99  bmc1_unsat_core_parents_size:           -1
% 3.16/0.99  bmc1_merge_next_fun:                    0
% 3.16/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.16/0.99  
% 3.16/0.99  ------ Instantiation
% 3.16/0.99  
% 3.16/0.99  inst_num_of_clauses:                    683
% 3.16/0.99  inst_num_in_passive:                    78
% 3.16/0.99  inst_num_in_active:                     261
% 3.16/0.99  inst_num_in_unprocessed:                344
% 3.16/0.99  inst_num_of_loops:                      369
% 3.16/0.99  inst_num_of_learning_restarts:          0
% 3.16/0.99  inst_num_moves_active_passive:          104
% 3.16/0.99  inst_lit_activity:                      0
% 3.16/0.99  inst_lit_activity_moves:                0
% 3.16/0.99  inst_num_tautologies:                   0
% 3.16/0.99  inst_num_prop_implied:                  0
% 3.16/0.99  inst_num_existing_simplified:           0
% 3.16/0.99  inst_num_eq_res_simplified:             0
% 3.16/0.99  inst_num_child_elim:                    0
% 3.16/0.99  inst_num_of_dismatching_blockings:      513
% 3.16/0.99  inst_num_of_non_proper_insts:           502
% 3.16/0.99  inst_num_of_duplicates:                 0
% 3.16/0.99  inst_inst_num_from_inst_to_res:         0
% 3.16/0.99  inst_dismatching_checking_time:         0.
% 3.16/0.99  
% 3.16/0.99  ------ Resolution
% 3.16/0.99  
% 3.16/0.99  res_num_of_clauses:                     0
% 3.16/0.99  res_num_in_passive:                     0
% 3.16/0.99  res_num_in_active:                      0
% 3.16/0.99  res_num_of_loops:                       53
% 3.16/0.99  res_forward_subset_subsumed:            49
% 3.16/0.99  res_backward_subset_subsumed:           0
% 3.16/0.99  res_forward_subsumed:                   0
% 3.16/0.99  res_backward_subsumed:                  0
% 3.16/0.99  res_forward_subsumption_resolution:     0
% 3.16/0.99  res_backward_subsumption_resolution:    0
% 3.16/0.99  res_clause_to_clause_subsumption:       7227
% 3.16/0.99  res_orphan_elimination:                 0
% 3.16/0.99  res_tautology_del:                      7
% 3.16/0.99  res_num_eq_res_simplified:              0
% 3.16/0.99  res_num_sel_changes:                    0
% 3.16/0.99  res_moves_from_active_to_pass:          0
% 3.16/0.99  
% 3.16/0.99  ------ Superposition
% 3.16/0.99  
% 3.16/0.99  sup_time_total:                         0.
% 3.16/0.99  sup_time_generating:                    0.
% 3.16/0.99  sup_time_sim_full:                      0.
% 3.16/0.99  sup_time_sim_immed:                     0.
% 3.16/0.99  
% 3.16/0.99  sup_num_of_clauses:                     489
% 3.16/0.99  sup_num_in_active:                      72
% 3.16/0.99  sup_num_in_passive:                     417
% 3.16/0.99  sup_num_of_loops:                       72
% 3.16/0.99  sup_fw_superposition:                   347
% 3.16/0.99  sup_bw_superposition:                   761
% 3.16/0.99  sup_immediate_simplified:               678
% 3.16/0.99  sup_given_eliminated:                   0
% 3.16/0.99  comparisons_done:                       0
% 3.16/0.99  comparisons_avoided:                    0
% 3.16/0.99  
% 3.16/0.99  ------ Simplifications
% 3.16/0.99  
% 3.16/0.99  
% 3.16/0.99  sim_fw_subset_subsumed:                 25
% 3.16/0.99  sim_bw_subset_subsumed:                 0
% 3.16/0.99  sim_fw_subsumed:                        226
% 3.16/0.99  sim_bw_subsumed:                        0
% 3.16/0.99  sim_fw_subsumption_res:                 17
% 3.16/0.99  sim_bw_subsumption_res:                 0
% 3.16/0.99  sim_tautology_del:                      75
% 3.16/0.99  sim_eq_tautology_del:                   14
% 3.16/0.99  sim_eq_res_simp:                        26
% 3.16/0.99  sim_fw_demodulated:                     241
% 3.16/0.99  sim_bw_demodulated:                     1
% 3.16/0.99  sim_light_normalised:                   299
% 3.16/0.99  sim_joinable_taut:                      0
% 3.16/0.99  sim_joinable_simp:                      0
% 3.16/0.99  sim_ac_normalised:                      0
% 3.16/0.99  sim_smt_subsumption:                    0
% 3.16/0.99  
%------------------------------------------------------------------------------
