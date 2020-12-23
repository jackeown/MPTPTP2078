%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0002+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:13 EST 2020

% Result     : Theorem 1.87s
% Output     : CNFRefutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 152 expanded)
%              Number of clauses        :   42 (  45 expanded)
%              Number of leaves         :    7 (  29 expanded)
%              Depth                    :   11
%              Number of atoms          :  356 (1108 expanded)
%              Number of equality atoms :   83 ( 177 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   22 (   3 average)
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
    inference(nnf_transformation,[],[f2])).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f12])).

fof(f14,plain,(
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
    inference(rectify,[],[f13])).

fof(f15,plain,(
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

fof(f16,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f14,f15])).

fof(f27,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f43,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f27])).

fof(f28,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f42,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f28])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ~ r2_hidden(X3,X0)
        <=> ( r2_hidden(X3,X1)
          <=> r2_hidden(X3,X2) ) )
     => k5_xboole_0(X1,X2) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ! [X3] :
            ( ~ r2_hidden(X3,X0)
          <=> ( r2_hidden(X3,X1)
            <=> r2_hidden(X3,X2) ) )
       => k5_xboole_0(X1,X2) = X0 ) ),
    inference(negated_conjecture,[],[f4])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( k5_xboole_0(X1,X2) != X0
      & ! [X3] :
          ( ~ r2_hidden(X3,X0)
        <=> ( r2_hidden(X3,X1)
          <=> r2_hidden(X3,X2) ) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( k5_xboole_0(X1,X2) != X0
      & ! [X3] :
          ( ( ~ r2_hidden(X3,X0)
            | ( ( ~ r2_hidden(X3,X2)
                | ~ r2_hidden(X3,X1) )
              & ( r2_hidden(X3,X2)
                | r2_hidden(X3,X1) ) ) )
          & ( ( ( r2_hidden(X3,X1)
                | ~ r2_hidden(X3,X2) )
              & ( r2_hidden(X3,X2)
                | ~ r2_hidden(X3,X1) ) )
            | r2_hidden(X3,X0) ) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f18,plain,
    ( ? [X0,X1,X2] :
        ( k5_xboole_0(X1,X2) != X0
        & ! [X3] :
            ( ( ~ r2_hidden(X3,X0)
              | ( ( ~ r2_hidden(X3,X2)
                  | ~ r2_hidden(X3,X1) )
                & ( r2_hidden(X3,X2)
                  | r2_hidden(X3,X1) ) ) )
            & ( ( ( r2_hidden(X3,X1)
                  | ~ r2_hidden(X3,X2) )
                & ( r2_hidden(X3,X2)
                  | ~ r2_hidden(X3,X1) ) )
              | r2_hidden(X3,X0) ) ) )
   => ( k5_xboole_0(sK3,sK4) != sK2
      & ! [X3] :
          ( ( ~ r2_hidden(X3,sK2)
            | ( ( ~ r2_hidden(X3,sK4)
                | ~ r2_hidden(X3,sK3) )
              & ( r2_hidden(X3,sK4)
                | r2_hidden(X3,sK3) ) ) )
          & ( ( ( r2_hidden(X3,sK3)
                | ~ r2_hidden(X3,sK4) )
              & ( r2_hidden(X3,sK4)
                | ~ r2_hidden(X3,sK3) ) )
            | r2_hidden(X3,sK2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( k5_xboole_0(sK3,sK4) != sK2
    & ! [X3] :
        ( ( ~ r2_hidden(X3,sK2)
          | ( ( ~ r2_hidden(X3,sK4)
              | ~ r2_hidden(X3,sK3) )
            & ( r2_hidden(X3,sK4)
              | r2_hidden(X3,sK3) ) ) )
        & ( ( ( r2_hidden(X3,sK3)
              | ~ r2_hidden(X3,sK4) )
            & ( r2_hidden(X3,sK4)
              | ~ r2_hidden(X3,sK3) ) )
          | r2_hidden(X3,sK2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f17,f18])).

fof(f33,plain,(
    ! [X3] :
      ( r2_hidden(X3,sK4)
      | ~ r2_hidden(X3,sK3)
      | r2_hidden(X3,sK2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f26,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f44,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f26])).

fof(f35,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK2)
      | r2_hidden(X3,sK4)
      | r2_hidden(X3,sK3) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f36,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK2)
      | ~ r2_hidden(X3,sK4)
      | ~ r2_hidden(X3,sK3) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f34,plain,(
    ! [X3] :
      ( r2_hidden(X3,sK3)
      | ~ r2_hidden(X3,sK4)
      | r2_hidden(X3,sK2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(nnf_transformation,[],[f1])).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f7])).

fof(f9,plain,(
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
    inference(rectify,[],[f8])).

fof(f10,plain,(
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

fof(f11,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f10])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f37,plain,(
    k5_xboole_0(sK3,sK4) != sK2 ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f38,plain,(
    k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3)) != sK2 ),
    inference(definition_unfolding,[],[f37,f32])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_794,plain,
    ( ~ r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),sK2),k4_xboole_0(X0,sK3))
    | ~ r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),sK2),sK3) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2569,plain,
    ( ~ r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),sK2),k4_xboole_0(sK4,sK3))
    | ~ r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),sK2),sK3) ),
    inference(instantiation,[status(thm)],[c_794])).

cnf(c_2570,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),sK2),k4_xboole_0(sK4,sK3)) != iProver_top
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),sK2),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2569])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_793,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),sK2),X0)
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),sK2),k4_xboole_0(sK3,X0))
    | ~ r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),sK2),sK3) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1682,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),sK2),k4_xboole_0(sK3,sK4))
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),sK2),sK4)
    | ~ r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),sK2),sK3) ),
    inference(instantiation,[status(thm)],[c_793])).

cnf(c_1683,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),sK2),k4_xboole_0(sK3,sK4)) = iProver_top
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),sK2),sK4) = iProver_top
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),sK2),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1682])).

cnf(c_16,negated_conjecture,
    ( r2_hidden(X0,sK2)
    | r2_hidden(X0,sK4)
    | ~ r2_hidden(X0,sK3) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_813,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),sK2),sK2)
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),sK2),sK4)
    | ~ r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),sK2),sK3) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_814,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),sK2),sK2) = iProver_top
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),sK2),sK4) = iProver_top
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),sK2),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_813])).

cnf(c_11,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_738,plain,
    ( ~ r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),sK2),k4_xboole_0(sK3,sK4))
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),sK2),sK3) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_739,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),sK2),k4_xboole_0(sK3,sK4)) != iProver_top
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),sK2),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_738])).

cnf(c_14,negated_conjecture,
    ( ~ r2_hidden(X0,sK2)
    | r2_hidden(X0,sK4)
    | r2_hidden(X0,sK3) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_694,plain,
    ( ~ r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),sK2),sK2)
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),sK2),sK4)
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),sK2),sK3) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_698,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),sK2),sK2) != iProver_top
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),sK2),sK4) = iProver_top
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),sK2),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_694])).

cnf(c_13,negated_conjecture,
    ( ~ r2_hidden(X0,sK2)
    | ~ r2_hidden(X0,sK4)
    | ~ r2_hidden(X0,sK3) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_695,plain,
    ( ~ r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),sK2),sK2)
    | ~ r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),sK2),sK4)
    | ~ r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),sK2),sK3) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_696,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),sK2),sK2) != iProver_top
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),sK2),sK4) != iProver_top
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),sK2),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_695])).

cnf(c_15,negated_conjecture,
    ( r2_hidden(X0,sK2)
    | ~ r2_hidden(X0,sK4)
    | r2_hidden(X0,sK3) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_659,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),sK2),sK2)
    | ~ r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),sK2),sK4)
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),sK2),sK3) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_660,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),sK2),sK2) = iProver_top
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),sK2),sK4) != iProver_top
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),sK2),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_659])).

cnf(c_635,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),sK2),X0)
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),sK2),k4_xboole_0(sK4,X0))
    | ~ r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),sK2),sK4) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_651,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),sK2),X0) = iProver_top
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),sK2),k4_xboole_0(sK4,X0)) = iProver_top
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),sK2),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_635])).

cnf(c_653,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),sK2),k4_xboole_0(sK4,sK3)) = iProver_top
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),sK2),sK4) != iProver_top
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),sK2),sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_651])).

cnf(c_636,plain,
    ( ~ r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),sK2),k4_xboole_0(X0,sK4))
    | ~ r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),sK2),sK4) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_647,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),sK2),k4_xboole_0(X0,sK4)) != iProver_top
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),sK2),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_636])).

cnf(c_649,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),sK2),k4_xboole_0(sK3,sK4)) != iProver_top
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),sK2),sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_647])).

cnf(c_625,plain,
    ( ~ r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),sK2),k4_xboole_0(sK4,sK3))
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),sK2),sK4) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_626,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),sK2),k4_xboole_0(sK4,sK3)) != iProver_top
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),sK2),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_625])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(sK0(X0,X1,X2),X0)
    | k2_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_597,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),sK2),k4_xboole_0(sK4,sK3))
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),sK2),k4_xboole_0(sK3,sK4))
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),sK2),sK2)
    | k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3)) = sK2 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_598,plain,
    ( k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3)) = sK2
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),sK2),k4_xboole_0(sK4,sK3)) = iProver_top
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),sK2),k4_xboole_0(sK3,sK4)) = iProver_top
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),sK2),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_597])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X2)
    | ~ r2_hidden(sK0(X0,X1,X2),X0)
    | k2_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_586,plain,
    ( ~ r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),sK2),k4_xboole_0(sK3,sK4))
    | ~ r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),sK2),sK2)
    | k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3)) = sK2 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_587,plain,
    ( k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3)) = sK2
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),sK2),k4_xboole_0(sK3,sK4)) != iProver_top
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),sK2),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_586])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | k2_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_583,plain,
    ( ~ r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),sK2),k4_xboole_0(sK4,sK3))
    | ~ r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),sK2),sK2)
    | k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3)) = sK2 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_584,plain,
    ( k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3)) = sK2
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),sK2),k4_xboole_0(sK4,sK3)) != iProver_top
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),sK2),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_583])).

cnf(c_12,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3)) != sK2 ),
    inference(cnf_transformation,[],[f38])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2570,c_1683,c_814,c_739,c_698,c_696,c_660,c_653,c_649,c_626,c_598,c_587,c_584,c_12])).


%------------------------------------------------------------------------------
