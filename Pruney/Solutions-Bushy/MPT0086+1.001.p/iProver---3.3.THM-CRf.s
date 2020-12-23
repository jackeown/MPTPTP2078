%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0086+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:26 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :   56 (  71 expanded)
%              Number of clauses        :   28 (  29 expanded)
%              Number of leaves         :   10 (  14 expanded)
%              Depth                    :   11
%              Number of atoms          :  240 ( 391 expanded)
%              Number of equality atoms :   68 (  87 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
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
    inference(nnf_transformation,[],[f2])).

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
     => ( ( r2_hidden(sK1(X0,X1,X2),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X0)
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(sK1(X0,X1,X2),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f18,f19])).

fof(f30,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f43,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f30])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(nnf_transformation,[],[f1])).

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
     => ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f14])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
     => r1_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f6,conjecture,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(negated_conjecture,[],[f6])).

fof(f10,plain,(
    ? [X0,X1] : ~ r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(ennf_transformation,[],[f7])).

fof(f21,plain,
    ( ? [X0,X1] : ~ r1_xboole_0(k4_xboole_0(X0,X1),X1)
   => ~ r1_xboole_0(k4_xboole_0(sK2,sK3),sK3) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ~ r1_xboole_0(k4_xboole_0(sK2,sK3),sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f10,f21])).

fof(f38,plain,(
    ~ r1_xboole_0(k4_xboole_0(sK2,sK3),sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

cnf(c_244,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_589,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK0(k4_xboole_0(sK2,sK3),sK3,k1_xboole_0),k1_xboole_0)
    | X0 != sK0(k4_xboole_0(sK2,sK3),sK3,k1_xboole_0)
    | X1 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_244])).

cnf(c_821,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK2,sK3),sK3,k1_xboole_0),X0)
    | ~ r2_hidden(sK0(k4_xboole_0(sK2,sK3),sK3,k1_xboole_0),k1_xboole_0)
    | X0 != k1_xboole_0
    | sK0(k4_xboole_0(sK2,sK3),sK3,k1_xboole_0) != sK0(k4_xboole_0(sK2,sK3),sK3,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_589])).

cnf(c_2992,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK2,sK3),sK3,k1_xboole_0),k4_xboole_0(X0,k1_xboole_0))
    | ~ r2_hidden(sK0(k4_xboole_0(sK2,sK3),sK3,k1_xboole_0),k1_xboole_0)
    | sK0(k4_xboole_0(sK2,sK3),sK3,k1_xboole_0) != sK0(k4_xboole_0(sK2,sK3),sK3,k1_xboole_0)
    | k4_xboole_0(X0,k1_xboole_0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_821])).

cnf(c_2993,plain,
    ( sK0(k4_xboole_0(sK2,sK3),sK3,k1_xboole_0) != sK0(k4_xboole_0(sK2,sK3),sK3,k1_xboole_0)
    | k4_xboole_0(X0,k1_xboole_0) != k1_xboole_0
    | r2_hidden(sK0(k4_xboole_0(sK2,sK3),sK3,k1_xboole_0),k4_xboole_0(X0,k1_xboole_0)) = iProver_top
    | r2_hidden(sK0(k4_xboole_0(sK2,sK3),sK3,k1_xboole_0),k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2992])).

cnf(c_2995,plain,
    ( sK0(k4_xboole_0(sK2,sK3),sK3,k1_xboole_0) != sK0(k4_xboole_0(sK2,sK3),sK3,k1_xboole_0)
    | k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | r2_hidden(sK0(k4_xboole_0(sK2,sK3),sK3,k1_xboole_0),k4_xboole_0(k1_xboole_0,k1_xboole_0)) = iProver_top
    | r2_hidden(sK0(k4_xboole_0(sK2,sK3),sK3,k1_xboole_0),k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2993])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_572,plain,
    ( ~ r2_hidden(sK0(k4_xboole_0(sK2,sK3),sK3,k1_xboole_0),k4_xboole_0(X0,sK3))
    | ~ r2_hidden(sK0(k4_xboole_0(sK2,sK3),sK3,k1_xboole_0),sK3) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1070,plain,
    ( ~ r2_hidden(sK0(k4_xboole_0(sK2,sK3),sK3,k1_xboole_0),k4_xboole_0(sK2,sK3))
    | ~ r2_hidden(sK0(k4_xboole_0(sK2,sK3),sK3,k1_xboole_0),sK3) ),
    inference(instantiation,[status(thm)],[c_572])).

cnf(c_1071,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK2,sK3),sK3,k1_xboole_0),k4_xboole_0(sK2,sK3)) != iProver_top
    | r2_hidden(sK0(k4_xboole_0(sK2,sK3),sK3,k1_xboole_0),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1070])).

cnf(c_241,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_822,plain,
    ( sK0(k4_xboole_0(sK2,sK3),sK3,k1_xboole_0) = sK0(k4_xboole_0(sK2,sK3),sK3,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_241])).

cnf(c_592,plain,
    ( ~ r2_hidden(sK0(k4_xboole_0(sK2,sK3),sK3,k1_xboole_0),k4_xboole_0(X0,k1_xboole_0))
    | ~ r2_hidden(sK0(k4_xboole_0(sK2,sK3),sK3,k1_xboole_0),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_593,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK2,sK3),sK3,k1_xboole_0),k4_xboole_0(X0,k1_xboole_0)) != iProver_top
    | r2_hidden(sK0(k4_xboole_0(sK2,sK3),sK3,k1_xboole_0),k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_592])).

cnf(c_595,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK2,sK3),sK3,k1_xboole_0),k4_xboole_0(k1_xboole_0,k1_xboole_0)) != iProver_top
    | r2_hidden(sK0(k4_xboole_0(sK2,sK3),sK3,k1_xboole_0),k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_593])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_557,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK2,sK3),sK3,k1_xboole_0),k4_xboole_0(sK2,sK3))
    | r2_hidden(sK0(k4_xboole_0(sK2,sK3),sK3,k1_xboole_0),k1_xboole_0)
    | k3_xboole_0(k4_xboole_0(sK2,sK3),sK3) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_558,plain,
    ( k3_xboole_0(k4_xboole_0(sK2,sK3),sK3) = k1_xboole_0
    | r2_hidden(sK0(k4_xboole_0(sK2,sK3),sK3,k1_xboole_0),k4_xboole_0(sK2,sK3)) = iProver_top
    | r2_hidden(sK0(k4_xboole_0(sK2,sK3),sK3,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_557])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_554,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK2,sK3),sK3,k1_xboole_0),sK3)
    | r2_hidden(sK0(k4_xboole_0(sK2,sK3),sK3,k1_xboole_0),k1_xboole_0)
    | k3_xboole_0(k4_xboole_0(sK2,sK3),sK3) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_555,plain,
    ( k3_xboole_0(k4_xboole_0(sK2,sK3),sK3) = k1_xboole_0
    | r2_hidden(sK0(k4_xboole_0(sK2,sK3),sK3,k1_xboole_0),sK3) = iProver_top
    | r2_hidden(sK0(k4_xboole_0(sK2,sK3),sK3,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_554])).

cnf(c_12,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_15,negated_conjecture,
    ( ~ r1_xboole_0(k4_xboole_0(sK2,sK3),sK3) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_152,plain,
    ( k4_xboole_0(sK2,sK3) != X0
    | k3_xboole_0(X0,X1) != k1_xboole_0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_15])).

cnf(c_153,plain,
    ( k3_xboole_0(k4_xboole_0(sK2,sK3),sK3) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_152])).

cnf(c_14,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_17,plain,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2995,c_1071,c_822,c_595,c_558,c_555,c_153,c_17])).


%------------------------------------------------------------------------------
