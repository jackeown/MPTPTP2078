%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0327+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:01 EST 2020

% Result     : Theorem 2.52s
% Output     : CNFRefutation 2.52s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 106 expanded)
%              Number of clauses        :   34 (  35 expanded)
%              Number of leaves         :    9 (  21 expanded)
%              Depth                    :   11
%              Number of atoms          :  320 ( 637 expanded)
%              Number of equality atoms :  105 ( 190 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f23,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f43,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f23])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
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

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f18,plain,(
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
    inference(rectify,[],[f17])).

fof(f19,plain,(
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

fof(f20,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f19])).

fof(f35,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f47,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f35])).

fof(f24,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f41,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f24])).

fof(f42,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f41])).

fof(f33,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f49,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f33])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f13,plain,(
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
    inference(rectify,[],[f12])).

fof(f14,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            & ~ r2_hidden(sK1(X0,X1,X2),X0) )
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( r2_hidden(sK1(X0,X1,X2),X1)
          | r2_hidden(sK1(X0,X1,X2),X0)
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
              & ~ r2_hidden(sK1(X0,X1,X2),X0) )
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( r2_hidden(sK1(X0,X1,X2),X1)
            | r2_hidden(sK1(X0,X1,X2),X0)
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f14])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X1)
      | r2_hidden(sK1(X0,X1,X2),X0)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK1(X0,X1,X2),X1)
      | ~ r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK1(X0,X1,X2),X0)
      | ~ r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    inference(negated_conjecture,[],[f4])).

fof(f6,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f21,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
        & r2_hidden(X0,X1) )
   => ( k2_xboole_0(k4_xboole_0(sK4,k1_tarski(sK3)),k1_tarski(sK3)) != sK4
      & r2_hidden(sK3,sK4) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( k2_xboole_0(k4_xboole_0(sK4,k1_tarski(sK3)),k1_tarski(sK3)) != sK4
    & r2_hidden(sK3,sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f6,f21])).

fof(f40,plain,(
    k2_xboole_0(k4_xboole_0(sK4,k1_tarski(sK3)),k1_tarski(sK3)) != sK4 ),
    inference(cnf_transformation,[],[f22])).

fof(f39,plain,(
    r2_hidden(sK3,sK4) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k1_tarski(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1466,plain,
    ( ~ r2_hidden(sK1(k4_xboole_0(sK4,k1_tarski(sK3)),k1_tarski(sK3),sK4),k1_tarski(X0))
    | sK1(k4_xboole_0(sK4,k1_tarski(sK3)),k1_tarski(sK3),sK4) = X0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1467,plain,
    ( sK1(k4_xboole_0(sK4,k1_tarski(sK3)),k1_tarski(sK3),sK4) = X0
    | r2_hidden(sK1(k4_xboole_0(sK4,k1_tarski(sK3)),k1_tarski(sK3),sK4),k1_tarski(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1466])).

cnf(c_1469,plain,
    ( sK1(k4_xboole_0(sK4,k1_tarski(sK3)),k1_tarski(sK3),sK4) = sK3
    | r2_hidden(sK1(k4_xboole_0(sK4,k1_tarski(sK3)),k1_tarski(sK3),sK4),k1_tarski(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1467])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_603,plain,
    ( ~ r2_hidden(sK1(k4_xboole_0(sK4,k1_tarski(sK3)),k1_tarski(sK3),sK4),X0)
    | r2_hidden(sK1(k4_xboole_0(sK4,k1_tarski(sK3)),k1_tarski(sK3),sK4),k4_xboole_0(X0,k1_tarski(sK3)))
    | r2_hidden(sK1(k4_xboole_0(sK4,k1_tarski(sK3)),k1_tarski(sK3),sK4),k1_tarski(sK3)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1093,plain,
    ( r2_hidden(sK1(k4_xboole_0(sK4,k1_tarski(sK3)),k1_tarski(sK3),sK4),k4_xboole_0(sK4,k1_tarski(sK3)))
    | r2_hidden(sK1(k4_xboole_0(sK4,k1_tarski(sK3)),k1_tarski(sK3),sK4),k1_tarski(sK3))
    | ~ r2_hidden(sK1(k4_xboole_0(sK4,k1_tarski(sK3)),k1_tarski(sK3),sK4),sK4) ),
    inference(instantiation,[status(thm)],[c_603])).

cnf(c_1094,plain,
    ( r2_hidden(sK1(k4_xboole_0(sK4,k1_tarski(sK3)),k1_tarski(sK3),sK4),k4_xboole_0(sK4,k1_tarski(sK3))) = iProver_top
    | r2_hidden(sK1(k4_xboole_0(sK4,k1_tarski(sK3)),k1_tarski(sK3),sK4),k1_tarski(sK3)) = iProver_top
    | r2_hidden(sK1(k4_xboole_0(sK4,k1_tarski(sK3)),k1_tarski(sK3),sK4),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1093])).

cnf(c_2,plain,
    ( r2_hidden(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_979,plain,
    ( r2_hidden(sK4,k1_tarski(sK4)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_192,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_546,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK1(k4_xboole_0(sK4,k1_tarski(sK3)),k1_tarski(sK3),sK4),sK4)
    | sK1(k4_xboole_0(sK4,k1_tarski(sK3)),k1_tarski(sK3),sK4) != X0
    | sK4 != X1 ),
    inference(instantiation,[status(thm)],[c_192])).

cnf(c_894,plain,
    ( ~ r2_hidden(X0,sK4)
    | r2_hidden(sK1(k4_xboole_0(sK4,k1_tarski(sK3)),k1_tarski(sK3),sK4),sK4)
    | sK1(k4_xboole_0(sK4,k1_tarski(sK3)),k1_tarski(sK3),sK4) != X0
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_546])).

cnf(c_895,plain,
    ( sK1(k4_xboole_0(sK4,k1_tarski(sK3)),k1_tarski(sK3),sK4) != X0
    | sK4 != sK4
    | r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(sK1(k4_xboole_0(sK4,k1_tarski(sK3)),k1_tarski(sK3),sK4),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_894])).

cnf(c_897,plain,
    ( sK1(k4_xboole_0(sK4,k1_tarski(sK3)),k1_tarski(sK3),sK4) != sK3
    | sK4 != sK4
    | r2_hidden(sK1(k4_xboole_0(sK4,k1_tarski(sK3)),k1_tarski(sK3),sK4),sK4) = iProver_top
    | r2_hidden(sK3,sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_895])).

cnf(c_587,plain,
    ( ~ r2_hidden(sK4,k1_tarski(X0))
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_825,plain,
    ( ~ r2_hidden(sK4,k1_tarski(sK4))
    | sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_587])).

cnf(c_15,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_532,plain,
    ( ~ r2_hidden(sK1(k4_xboole_0(sK4,k1_tarski(sK3)),k1_tarski(sK3),sK4),k4_xboole_0(sK4,X0))
    | r2_hidden(sK1(k4_xboole_0(sK4,k1_tarski(sK3)),k1_tarski(sK3),sK4),sK4) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_654,plain,
    ( ~ r2_hidden(sK1(k4_xboole_0(sK4,k1_tarski(sK3)),k1_tarski(sK3),sK4),k4_xboole_0(sK4,k1_tarski(sK3)))
    | r2_hidden(sK1(k4_xboole_0(sK4,k1_tarski(sK3)),k1_tarski(sK3),sK4),sK4) ),
    inference(instantiation,[status(thm)],[c_532])).

cnf(c_655,plain,
    ( r2_hidden(sK1(k4_xboole_0(sK4,k1_tarski(sK3)),k1_tarski(sK3),sK4),k4_xboole_0(sK4,k1_tarski(sK3))) != iProver_top
    | r2_hidden(sK1(k4_xboole_0(sK4,k1_tarski(sK3)),k1_tarski(sK3),sK4),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_654])).

cnf(c_6,plain,
    ( r2_hidden(sK1(X0,X1,X2),X1)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | r2_hidden(sK1(X0,X1,X2),X0)
    | k2_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_485,plain,
    ( r2_hidden(sK1(k4_xboole_0(sK4,k1_tarski(sK3)),k1_tarski(sK3),sK4),k4_xboole_0(sK4,k1_tarski(sK3)))
    | r2_hidden(sK1(k4_xboole_0(sK4,k1_tarski(sK3)),k1_tarski(sK3),sK4),k1_tarski(sK3))
    | r2_hidden(sK1(k4_xboole_0(sK4,k1_tarski(sK3)),k1_tarski(sK3),sK4),sK4)
    | k2_xboole_0(k4_xboole_0(sK4,k1_tarski(sK3)),k1_tarski(sK3)) = sK4 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_492,plain,
    ( k2_xboole_0(k4_xboole_0(sK4,k1_tarski(sK3)),k1_tarski(sK3)) = sK4
    | r2_hidden(sK1(k4_xboole_0(sK4,k1_tarski(sK3)),k1_tarski(sK3),sK4),k4_xboole_0(sK4,k1_tarski(sK3))) = iProver_top
    | r2_hidden(sK1(k4_xboole_0(sK4,k1_tarski(sK3)),k1_tarski(sK3),sK4),k1_tarski(sK3)) = iProver_top
    | r2_hidden(sK1(k4_xboole_0(sK4,k1_tarski(sK3)),k1_tarski(sK3),sK4),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_485])).

cnf(c_4,plain,
    ( ~ r2_hidden(sK1(X0,X1,X2),X1)
    | ~ r2_hidden(sK1(X0,X1,X2),X2)
    | k2_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_486,plain,
    ( ~ r2_hidden(sK1(k4_xboole_0(sK4,k1_tarski(sK3)),k1_tarski(sK3),sK4),k1_tarski(sK3))
    | ~ r2_hidden(sK1(k4_xboole_0(sK4,k1_tarski(sK3)),k1_tarski(sK3),sK4),sK4)
    | k2_xboole_0(k4_xboole_0(sK4,k1_tarski(sK3)),k1_tarski(sK3)) = sK4 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_490,plain,
    ( k2_xboole_0(k4_xboole_0(sK4,k1_tarski(sK3)),k1_tarski(sK3)) = sK4
    | r2_hidden(sK1(k4_xboole_0(sK4,k1_tarski(sK3)),k1_tarski(sK3),sK4),k1_tarski(sK3)) != iProver_top
    | r2_hidden(sK1(k4_xboole_0(sK4,k1_tarski(sK3)),k1_tarski(sK3),sK4),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_486])).

cnf(c_5,plain,
    ( ~ r2_hidden(sK1(X0,X1,X2),X2)
    | ~ r2_hidden(sK1(X0,X1,X2),X0)
    | k2_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_487,plain,
    ( ~ r2_hidden(sK1(k4_xboole_0(sK4,k1_tarski(sK3)),k1_tarski(sK3),sK4),k4_xboole_0(sK4,k1_tarski(sK3)))
    | ~ r2_hidden(sK1(k4_xboole_0(sK4,k1_tarski(sK3)),k1_tarski(sK3),sK4),sK4)
    | k2_xboole_0(k4_xboole_0(sK4,k1_tarski(sK3)),k1_tarski(sK3)) = sK4 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_488,plain,
    ( k2_xboole_0(k4_xboole_0(sK4,k1_tarski(sK3)),k1_tarski(sK3)) = sK4
    | r2_hidden(sK1(k4_xboole_0(sK4,k1_tarski(sK3)),k1_tarski(sK3),sK4),k4_xboole_0(sK4,k1_tarski(sK3))) != iProver_top
    | r2_hidden(sK1(k4_xboole_0(sK4,k1_tarski(sK3)),k1_tarski(sK3),sK4),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_487])).

cnf(c_16,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(sK4,k1_tarski(sK3)),k1_tarski(sK3)) != sK4 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_17,negated_conjecture,
    ( r2_hidden(sK3,sK4) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_18,plain,
    ( r2_hidden(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1469,c_1094,c_979,c_897,c_825,c_655,c_492,c_490,c_488,c_16,c_18])).


%------------------------------------------------------------------------------
