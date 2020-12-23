%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0236+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:47 EST 2020

% Result     : Theorem 1.11s
% Output     : CNFRefutation 1.11s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 101 expanded)
%              Number of clauses        :   29 (  33 expanded)
%              Number of leaves         :   11 (  29 expanded)
%              Depth                    :   10
%              Number of atoms          :  210 ( 557 expanded)
%              Number of equality atoms :   95 ( 198 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) ) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] :
                  ( r2_hidden(X4,X0)
                  & r2_hidden(X2,X4) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ? [X7] :
                  ( r2_hidden(X7,X0)
                  & r2_hidden(X5,X7) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f10])).

fof(f14,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK3(X0,X5),X0)
        & r2_hidden(X5,sK3(X0,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(X2,X4) )
     => ( r2_hidden(sK2(X0,X1),X0)
        & r2_hidden(X2,sK2(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X3) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( r2_hidden(X4,X0)
                & r2_hidden(X2,X4) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( ~ r2_hidden(X3,X0)
              | ~ r2_hidden(sK1(X0,X1),X3) )
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ? [X4] :
              ( r2_hidden(X4,X0)
              & r2_hidden(sK1(X0,X1),X4) )
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(sK1(X0,X1),X3) )
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( ( r2_hidden(sK2(X0,X1),X0)
              & r2_hidden(sK1(X0,X1),sK2(X0,X1)) )
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ( r2_hidden(sK3(X0,X5),X0)
                & r2_hidden(X5,sK3(X0,X5)) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f11,f14,f13,f12])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
      | r2_hidden(sK2(X0,X1),X0)
      | r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f18,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f31,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f18])).

fof(f27,plain,(
    ! [X0,X3,X1] :
      ( k3_tarski(X0) = X1
      | ~ r2_hidden(X3,X0)
      | ~ r2_hidden(sK1(X0,X1),X3)
      | ~ r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
      | r2_hidden(sK1(X0,X1),sK2(X0,X1))
      | r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f19,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f29,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f19])).

fof(f30,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f29])).

fof(f3,conjecture,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    inference(negated_conjecture,[],[f3])).

fof(f5,plain,(
    ? [X0] : k3_tarski(k1_tarski(X0)) != X0 ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,
    ( ? [X0] : k3_tarski(k1_tarski(X0)) != X0
   => k3_tarski(k1_tarski(sK4)) != sK4 ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    k3_tarski(k1_tarski(sK4)) != sK4 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f5,f16])).

fof(f28,plain,(
    k3_tarski(k1_tarski(sK4)) != sK4 ),
    inference(cnf_transformation,[],[f17])).

cnf(c_124,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_677,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK1(k1_tarski(sK4),X2),sK2(k1_tarski(sK4),X2))
    | X1 != sK2(k1_tarski(sK4),X2)
    | X0 != sK1(k1_tarski(sK4),X2) ),
    inference(instantiation,[status(thm)],[c_124])).

cnf(c_1975,plain,
    ( r2_hidden(sK1(k1_tarski(sK4),X0),X1)
    | ~ r2_hidden(sK1(k1_tarski(sK4),X0),sK2(k1_tarski(sK4),X0))
    | X1 != sK2(k1_tarski(sK4),X0)
    | sK1(k1_tarski(sK4),X0) != sK1(k1_tarski(sK4),X0) ),
    inference(instantiation,[status(thm)],[c_677])).

cnf(c_1978,plain,
    ( ~ r2_hidden(sK1(k1_tarski(sK4),sK4),sK2(k1_tarski(sK4),sK4))
    | r2_hidden(sK1(k1_tarski(sK4),sK4),sK4)
    | sK1(k1_tarski(sK4),sK4) != sK1(k1_tarski(sK4),sK4)
    | sK4 != sK2(k1_tarski(sK4),sK4) ),
    inference(instantiation,[status(thm)],[c_1975])).

cnf(c_121,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1080,plain,
    ( sK1(k1_tarski(sK4),sK4) = sK1(k1_tarski(sK4),sK4) ),
    inference(instantiation,[status(thm)],[c_121])).

cnf(c_5,plain,
    ( r2_hidden(sK2(X0,X1),X0)
    | r2_hidden(sK1(X0,X1),X1)
    | k3_tarski(X0) = X1 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_294,plain,
    ( k3_tarski(X0) = X1
    | r2_hidden(sK2(X0,X1),X0) = iProver_top
    | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k1_tarski(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_296,plain,
    ( X0 = X1
    | r2_hidden(X0,k1_tarski(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_818,plain,
    ( sK2(k1_tarski(X0),X1) = X0
    | k3_tarski(k1_tarski(X0)) = X1
    | r2_hidden(sK1(k1_tarski(X0),X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_294,c_296])).

cnf(c_871,plain,
    ( sK2(k1_tarski(sK4),sK4) = sK4
    | k3_tarski(k1_tarski(sK4)) = sK4
    | r2_hidden(sK1(k1_tarski(sK4),sK4),sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_818])).

cnf(c_122,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_581,plain,
    ( X0 != X1
    | X0 = sK2(k1_tarski(sK4),sK4)
    | sK2(k1_tarski(sK4),sK4) != X1 ),
    inference(instantiation,[status(thm)],[c_122])).

cnf(c_582,plain,
    ( sK2(k1_tarski(sK4),sK4) != sK4
    | sK4 = sK2(k1_tarski(sK4),sK4)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_581])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(sK1(X1,X2),X0)
    | ~ r2_hidden(sK1(X1,X2),X2)
    | k3_tarski(X1) = X2 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_398,plain,
    ( ~ r2_hidden(X0,k1_tarski(sK4))
    | ~ r2_hidden(sK1(k1_tarski(sK4),sK4),X0)
    | ~ r2_hidden(sK1(k1_tarski(sK4),sK4),sK4)
    | k3_tarski(k1_tarski(sK4)) = sK4 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_399,plain,
    ( k3_tarski(k1_tarski(sK4)) = sK4
    | r2_hidden(X0,k1_tarski(sK4)) != iProver_top
    | r2_hidden(sK1(k1_tarski(sK4),sK4),X0) != iProver_top
    | r2_hidden(sK1(k1_tarski(sK4),sK4),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_398])).

cnf(c_401,plain,
    ( k3_tarski(k1_tarski(sK4)) = sK4
    | r2_hidden(sK1(k1_tarski(sK4),sK4),sK4) != iProver_top
    | r2_hidden(sK4,k1_tarski(sK4)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_399])).

cnf(c_400,plain,
    ( ~ r2_hidden(sK1(k1_tarski(sK4),sK4),sK4)
    | ~ r2_hidden(sK4,k1_tarski(sK4))
    | k3_tarski(k1_tarski(sK4)) = sK4 ),
    inference(instantiation,[status(thm)],[c_398])).

cnf(c_6,plain,
    ( r2_hidden(sK1(X0,X1),X1)
    | r2_hidden(sK1(X0,X1),sK2(X0,X1))
    | k3_tarski(X0) = X1 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_395,plain,
    ( r2_hidden(sK1(k1_tarski(sK4),sK4),sK2(k1_tarski(sK4),sK4))
    | r2_hidden(sK1(k1_tarski(sK4),sK4),sK4)
    | k3_tarski(k1_tarski(sK4)) = sK4 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2,plain,
    ( r2_hidden(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_32,plain,
    ( r2_hidden(X0,k1_tarski(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_34,plain,
    ( r2_hidden(sK4,k1_tarski(sK4)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_33,plain,
    ( r2_hidden(sK4,k1_tarski(sK4)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_30,plain,
    ( ~ r2_hidden(sK4,k1_tarski(sK4))
    | sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_10,negated_conjecture,
    ( k3_tarski(k1_tarski(sK4)) != sK4 ),
    inference(cnf_transformation,[],[f28])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1978,c_1080,c_871,c_582,c_401,c_400,c_395,c_34,c_33,c_30,c_10])).


%------------------------------------------------------------------------------
