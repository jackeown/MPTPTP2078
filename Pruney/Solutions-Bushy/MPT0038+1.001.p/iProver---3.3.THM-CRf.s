%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0038+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:18 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 107 expanded)
%              Number of clauses        :   24 (  31 expanded)
%              Number of leaves         :    8 (  22 expanded)
%              Depth                    :   10
%              Number of atoms          :  238 ( 518 expanded)
%              Number of equality atoms :   41 (  72 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f27,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f38,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f27])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f7,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f9,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f9])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f4,conjecture,(
    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    inference(negated_conjecture,[],[f4])).

fof(f8,plain,(
    ? [X0,X1,X2] : ~ r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    inference(ennf_transformation,[],[f5])).

fof(f21,plain,
    ( ? [X0,X1,X2] : ~ r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))
   => ~ r1_tarski(k2_xboole_0(k3_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5)),k2_xboole_0(sK4,sK5)) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ~ r1_tarski(k2_xboole_0(k3_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5)),k2_xboole_0(sK4,sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f8,f21])).

fof(f37,plain,(
    ~ r1_tarski(k2_xboole_0(k3_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5)),k2_xboole_0(sK4,sK5)) ),
    inference(cnf_transformation,[],[f22])).

fof(f26,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f39,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f26])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
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
    inference(nnf_transformation,[],[f3])).

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
    inference(flattening,[],[f16])).

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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f17])).

fof(f19,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X0)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(sK2(X0,X1,X2),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            | ~ r2_hidden(sK2(X0,X1,X2),X0)
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK2(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f19])).

fof(f32,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f42,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f32])).

fof(f25,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f40,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f25])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f10])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_521,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k2_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_14,negated_conjecture,
    ( ~ r1_tarski(k2_xboole_0(k3_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5)),k2_xboole_0(sK4,sK5)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_175,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | k2_xboole_0(k3_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5)) != X0
    | k2_xboole_0(sK4,sK5) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_14])).

cnf(c_176,plain,
    ( ~ r2_hidden(sK0(k2_xboole_0(k3_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5)),k2_xboole_0(sK4,sK5)),k2_xboole_0(sK4,sK5)) ),
    inference(unflattening,[status(thm)],[c_175])).

cnf(c_511,plain,
    ( r2_hidden(sK0(k2_xboole_0(k3_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5)),k2_xboole_0(sK4,sK5)),k2_xboole_0(sK4,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_176])).

cnf(c_984,plain,
    ( r2_hidden(sK0(k2_xboole_0(k3_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5)),k2_xboole_0(sK4,sK5)),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_521,c_511])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_520,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k2_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_841,plain,
    ( r2_hidden(sK0(k2_xboole_0(k3_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5)),k2_xboole_0(sK4,sK5)),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_520,c_511])).

cnf(c_12,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_832,plain,
    ( ~ r2_hidden(sK0(k2_xboole_0(k3_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5)),k2_xboole_0(sK4,sK5)),k3_xboole_0(sK3,sK4))
    | r2_hidden(sK0(k2_xboole_0(k3_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5)),k2_xboole_0(sK4,sK5)),sK4) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_833,plain,
    ( r2_hidden(sK0(k2_xboole_0(k3_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5)),k2_xboole_0(sK4,sK5)),k3_xboole_0(sK3,sK4)) != iProver_top
    | r2_hidden(sK0(k2_xboole_0(k3_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5)),k2_xboole_0(sK4,sK5)),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_832])).

cnf(c_679,plain,
    ( ~ r2_hidden(sK0(k2_xboole_0(k3_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5)),k2_xboole_0(sK4,sK5)),k3_xboole_0(sK3,sK5))
    | r2_hidden(sK0(k2_xboole_0(k3_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5)),k2_xboole_0(sK4,sK5)),sK5) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_680,plain,
    ( r2_hidden(sK0(k2_xboole_0(k3_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5)),k2_xboole_0(sK4,sK5)),k3_xboole_0(sK3,sK5)) != iProver_top
    | r2_hidden(sK0(k2_xboole_0(k3_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5)),k2_xboole_0(sK4,sK5)),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_679])).

cnf(c_7,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_636,plain,
    ( r2_hidden(sK0(k2_xboole_0(k3_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5)),k2_xboole_0(sK4,sK5)),k3_xboole_0(sK3,sK5))
    | r2_hidden(sK0(k2_xboole_0(k3_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5)),k2_xboole_0(sK4,sK5)),k3_xboole_0(sK3,sK4))
    | ~ r2_hidden(sK0(k2_xboole_0(k3_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5)),k2_xboole_0(sK4,sK5)),k2_xboole_0(k3_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5))) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_637,plain,
    ( r2_hidden(sK0(k2_xboole_0(k3_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5)),k2_xboole_0(sK4,sK5)),k3_xboole_0(sK3,sK5)) = iProver_top
    | r2_hidden(sK0(k2_xboole_0(k3_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5)),k2_xboole_0(sK4,sK5)),k3_xboole_0(sK3,sK4)) = iProver_top
    | r2_hidden(sK0(k2_xboole_0(k3_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5)),k2_xboole_0(sK4,sK5)),k2_xboole_0(k3_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_636])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_168,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | k2_xboole_0(k3_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5)) != X0
    | k2_xboole_0(sK4,sK5) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_14])).

cnf(c_169,plain,
    ( r2_hidden(sK0(k2_xboole_0(k3_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5)),k2_xboole_0(sK4,sK5)),k2_xboole_0(k3_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5))) ),
    inference(unflattening,[status(thm)],[c_168])).

cnf(c_170,plain,
    ( r2_hidden(sK0(k2_xboole_0(k3_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5)),k2_xboole_0(sK4,sK5)),k2_xboole_0(k3_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_169])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_984,c_841,c_833,c_680,c_637,c_170])).


%------------------------------------------------------------------------------
