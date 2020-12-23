%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:43:50 EST 2020

% Result     : Theorem 2.27s
% Output     : CNFRefutation 2.27s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 132 expanded)
%              Number of clauses        :   45 (  58 expanded)
%              Number of leaves         :   15 (  35 expanded)
%              Depth                    :   13
%              Number of atoms          :  301 ( 659 expanded)
%              Number of equality atoms :  119 ( 184 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   3 average)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
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

fof(f10,plain,(
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
    inference(flattening,[],[f9])).

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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f10])).

fof(f12,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f12])).

fof(f27,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f43,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f27])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f14])).

fof(f18,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK2(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK1(X0,X1),X3),X0)
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK1(X0,X1),X4),X0)
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK1(X0,X1),X3),X0)
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f15,f18,f17,f16])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
      | r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f20])).

fof(f24,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK6(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK5(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0)
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK4(X0,X1)),X0)
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0)
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0)
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK6(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f21,f24,f23,f22])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0)
      | r2_hidden(sK4(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f6,conjecture,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
      & k1_xboole_0 = k1_relat_1(k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f8,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(ennf_transformation,[],[f7])).

fof(f41,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

cnf(c_167,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1573,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK1(X2,X3),X3)
    | X1 != X3
    | X0 != sK1(X2,X3) ),
    inference(instantiation,[status(thm)],[c_167])).

cnf(c_3051,plain,
    ( ~ r2_hidden(sK1(X0,X1),X1)
    | r2_hidden(sK1(X0,X1),X2)
    | X2 != X1
    | sK1(X0,X1) != sK1(X0,X1) ),
    inference(instantiation,[status(thm)],[c_1573])).

cnf(c_10118,plain,
    ( ~ r2_hidden(sK1(X0,X1),X1)
    | r2_hidden(sK1(X0,X1),k4_xboole_0(X2,X1))
    | sK1(X0,X1) != sK1(X0,X1)
    | k4_xboole_0(X2,X1) != X1 ),
    inference(instantiation,[status(thm)],[c_3051])).

cnf(c_10120,plain,
    ( r2_hidden(sK1(k1_xboole_0,k1_xboole_0),k4_xboole_0(k1_xboole_0,k1_xboole_0))
    | ~ r2_hidden(sK1(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | sK1(k1_xboole_0,k1_xboole_0) != sK1(k1_xboole_0,k1_xboole_0)
    | k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_10118])).

cnf(c_164,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3052,plain,
    ( sK1(X0,X1) = sK1(X0,X1) ),
    inference(instantiation,[status(thm)],[c_164])).

cnf(c_3055,plain,
    ( sK1(k1_xboole_0,k1_xboole_0) = sK1(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3052])).

cnf(c_541,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK4(X2,X3),X3)
    | X1 != X3
    | X0 != sK4(X2,X3) ),
    inference(instantiation,[status(thm)],[c_167])).

cnf(c_637,plain,
    ( ~ r2_hidden(sK4(X0,X1),X1)
    | r2_hidden(sK4(X0,X1),X2)
    | X2 != X1
    | sK4(X0,X1) != sK4(X0,X1) ),
    inference(instantiation,[status(thm)],[c_541])).

cnf(c_2086,plain,
    ( ~ r2_hidden(sK4(X0,X1),X1)
    | r2_hidden(sK4(X0,X1),k4_xboole_0(X2,X1))
    | sK4(X0,X1) != sK4(X0,X1)
    | k4_xboole_0(X2,X1) != X1 ),
    inference(instantiation,[status(thm)],[c_637])).

cnf(c_2087,plain,
    ( sK4(X0,X1) != sK4(X0,X1)
    | k4_xboole_0(X2,X1) != X1
    | r2_hidden(sK4(X0,X1),X1) != iProver_top
    | r2_hidden(sK4(X0,X1),k4_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2086])).

cnf(c_2089,plain,
    ( sK4(k1_xboole_0,k1_xboole_0) != sK4(k1_xboole_0,k1_xboole_0)
    | k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | r2_hidden(sK4(k1_xboole_0,k1_xboole_0),k4_xboole_0(k1_xboole_0,k1_xboole_0)) = iProver_top
    | r2_hidden(sK4(k1_xboole_0,k1_xboole_0),k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2087])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1572,plain,
    ( ~ r2_hidden(sK1(X0,X1),X1)
    | ~ r2_hidden(sK1(X0,X1),k4_xboole_0(X2,X1)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1579,plain,
    ( ~ r2_hidden(sK1(k1_xboole_0,k1_xboole_0),k4_xboole_0(k1_xboole_0,k1_xboole_0))
    | ~ r2_hidden(sK1(k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1572])).

cnf(c_8,plain,
    ( r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
    | r2_hidden(sK1(X0,X1),X1)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_405,plain,
    ( k1_relat_1(X0) = X1
    | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) = iProver_top
    | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_6,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_408,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_589,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_408])).

cnf(c_1497,plain,
    ( k1_relat_1(X0) = X1
    | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),k1_xboole_0) != iProver_top
    | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_405,c_589])).

cnf(c_1547,plain,
    ( ~ r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),k1_xboole_0)
    | r2_hidden(sK1(X0,X1),X1)
    | k1_relat_1(X0) = X1 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1497])).

cnf(c_1549,plain,
    ( ~ r2_hidden(k4_tarski(sK1(k1_xboole_0,k1_xboole_0),sK2(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | r2_hidden(sK1(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1547])).

cnf(c_12,plain,
    ( r2_hidden(sK4(X0,X1),X1)
    | r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_401,plain,
    ( k2_relat_1(X0) = X1
    | r2_hidden(sK4(X0,X1),X1) = iProver_top
    | r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_852,plain,
    ( k2_relat_1(X0) = X1
    | r2_hidden(sK4(X0,X1),X1) = iProver_top
    | r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_401,c_589])).

cnf(c_888,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0
    | r2_hidden(sK4(k1_xboole_0,k1_xboole_0),k1_xboole_0) = iProver_top
    | r2_hidden(k4_tarski(sK5(k1_xboole_0,k1_xboole_0),sK4(k1_xboole_0,k1_xboole_0)),k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_852])).

cnf(c_165,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_652,plain,
    ( k1_relat_1(k1_xboole_0) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_165])).

cnf(c_653,plain,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_652])).

cnf(c_638,plain,
    ( sK4(X0,X1) = sK4(X0,X1) ),
    inference(instantiation,[status(thm)],[c_164])).

cnf(c_641,plain,
    ( sK4(k1_xboole_0,k1_xboole_0) = sK4(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_638])).

cnf(c_540,plain,
    ( ~ r2_hidden(sK4(X0,X1),X1)
    | ~ r2_hidden(sK4(X0,X1),k4_xboole_0(X2,X1)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_546,plain,
    ( r2_hidden(sK4(X0,X1),X1) != iProver_top
    | r2_hidden(sK4(X0,X1),k4_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_540])).

cnf(c_548,plain,
    ( r2_hidden(sK4(k1_xboole_0,k1_xboole_0),k4_xboole_0(k1_xboole_0,k1_xboole_0)) != iProver_top
    | r2_hidden(sK4(k1_xboole_0,k1_xboole_0),k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_546])).

cnf(c_522,plain,
    ( k2_relat_1(k1_xboole_0) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_165])).

cnf(c_523,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_522])).

cnf(c_177,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_164])).

cnf(c_40,plain,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_35,plain,
    ( r2_hidden(k4_tarski(sK1(k1_xboole_0,k1_xboole_0),sK2(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | r2_hidden(sK1(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_22,plain,
    ( k2_relat_1(X0) = X1
    | r2_hidden(sK4(X0,X1),X1) = iProver_top
    | r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_24,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0
    | r2_hidden(sK4(k1_xboole_0,k1_xboole_0),k1_xboole_0) = iProver_top
    | r2_hidden(k4_tarski(sK5(k1_xboole_0,k1_xboole_0),sK4(k1_xboole_0,k1_xboole_0)),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_15,negated_conjecture,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f41])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10120,c_3055,c_2089,c_1579,c_1549,c_888,c_653,c_641,c_548,c_523,c_177,c_40,c_35,c_24,c_15])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:36:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 2.27/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.27/0.99  
% 2.27/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.27/0.99  
% 2.27/0.99  ------  iProver source info
% 2.27/0.99  
% 2.27/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.27/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.27/0.99  git: non_committed_changes: false
% 2.27/0.99  git: last_make_outside_of_git: false
% 2.27/0.99  
% 2.27/0.99  ------ 
% 2.27/0.99  
% 2.27/0.99  ------ Input Options
% 2.27/0.99  
% 2.27/0.99  --out_options                           all
% 2.27/0.99  --tptp_safe_out                         true
% 2.27/0.99  --problem_path                          ""
% 2.27/0.99  --include_path                          ""
% 2.27/0.99  --clausifier                            res/vclausify_rel
% 2.27/0.99  --clausifier_options                    --mode clausify
% 2.27/0.99  --stdin                                 false
% 2.27/0.99  --stats_out                             all
% 2.27/0.99  
% 2.27/0.99  ------ General Options
% 2.27/0.99  
% 2.27/0.99  --fof                                   false
% 2.27/0.99  --time_out_real                         305.
% 2.27/0.99  --time_out_virtual                      -1.
% 2.27/0.99  --symbol_type_check                     false
% 2.27/0.99  --clausify_out                          false
% 2.27/0.99  --sig_cnt_out                           false
% 2.27/0.99  --trig_cnt_out                          false
% 2.27/0.99  --trig_cnt_out_tolerance                1.
% 2.27/0.99  --trig_cnt_out_sk_spl                   false
% 2.27/0.99  --abstr_cl_out                          false
% 2.27/0.99  
% 2.27/0.99  ------ Global Options
% 2.27/0.99  
% 2.27/0.99  --schedule                              default
% 2.27/0.99  --add_important_lit                     false
% 2.27/0.99  --prop_solver_per_cl                    1000
% 2.27/0.99  --min_unsat_core                        false
% 2.27/0.99  --soft_assumptions                      false
% 2.27/0.99  --soft_lemma_size                       3
% 2.27/0.99  --prop_impl_unit_size                   0
% 2.27/0.99  --prop_impl_unit                        []
% 2.27/0.99  --share_sel_clauses                     true
% 2.27/0.99  --reset_solvers                         false
% 2.27/0.99  --bc_imp_inh                            [conj_cone]
% 2.27/0.99  --conj_cone_tolerance                   3.
% 2.27/0.99  --extra_neg_conj                        none
% 2.27/0.99  --large_theory_mode                     true
% 2.27/0.99  --prolific_symb_bound                   200
% 2.27/0.99  --lt_threshold                          2000
% 2.27/0.99  --clause_weak_htbl                      true
% 2.27/0.99  --gc_record_bc_elim                     false
% 2.27/0.99  
% 2.27/0.99  ------ Preprocessing Options
% 2.27/0.99  
% 2.27/0.99  --preprocessing_flag                    true
% 2.27/0.99  --time_out_prep_mult                    0.1
% 2.27/0.99  --splitting_mode                        input
% 2.27/0.99  --splitting_grd                         true
% 2.27/0.99  --splitting_cvd                         false
% 2.27/0.99  --splitting_cvd_svl                     false
% 2.27/0.99  --splitting_nvd                         32
% 2.27/0.99  --sub_typing                            true
% 2.27/0.99  --prep_gs_sim                           true
% 2.27/0.99  --prep_unflatten                        true
% 2.27/0.99  --prep_res_sim                          true
% 2.27/0.99  --prep_upred                            true
% 2.27/0.99  --prep_sem_filter                       exhaustive
% 2.27/0.99  --prep_sem_filter_out                   false
% 2.27/0.99  --pred_elim                             true
% 2.27/0.99  --res_sim_input                         true
% 2.27/0.99  --eq_ax_congr_red                       true
% 2.27/0.99  --pure_diseq_elim                       true
% 2.27/0.99  --brand_transform                       false
% 2.27/0.99  --non_eq_to_eq                          false
% 2.27/0.99  --prep_def_merge                        true
% 2.27/0.99  --prep_def_merge_prop_impl              false
% 2.27/0.99  --prep_def_merge_mbd                    true
% 2.27/0.99  --prep_def_merge_tr_red                 false
% 2.27/0.99  --prep_def_merge_tr_cl                  false
% 2.27/0.99  --smt_preprocessing                     true
% 2.27/0.99  --smt_ac_axioms                         fast
% 2.27/0.99  --preprocessed_out                      false
% 2.27/0.99  --preprocessed_stats                    false
% 2.27/0.99  
% 2.27/0.99  ------ Abstraction refinement Options
% 2.27/0.99  
% 2.27/0.99  --abstr_ref                             []
% 2.27/0.99  --abstr_ref_prep                        false
% 2.27/0.99  --abstr_ref_until_sat                   false
% 2.27/0.99  --abstr_ref_sig_restrict                funpre
% 2.27/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.27/0.99  --abstr_ref_under                       []
% 2.27/0.99  
% 2.27/0.99  ------ SAT Options
% 2.27/0.99  
% 2.27/0.99  --sat_mode                              false
% 2.27/0.99  --sat_fm_restart_options                ""
% 2.27/0.99  --sat_gr_def                            false
% 2.27/0.99  --sat_epr_types                         true
% 2.27/0.99  --sat_non_cyclic_types                  false
% 2.27/0.99  --sat_finite_models                     false
% 2.27/0.99  --sat_fm_lemmas                         false
% 2.27/0.99  --sat_fm_prep                           false
% 2.27/0.99  --sat_fm_uc_incr                        true
% 2.27/0.99  --sat_out_model                         small
% 2.27/0.99  --sat_out_clauses                       false
% 2.27/0.99  
% 2.27/0.99  ------ QBF Options
% 2.27/0.99  
% 2.27/0.99  --qbf_mode                              false
% 2.27/0.99  --qbf_elim_univ                         false
% 2.27/0.99  --qbf_dom_inst                          none
% 2.27/0.99  --qbf_dom_pre_inst                      false
% 2.27/0.99  --qbf_sk_in                             false
% 2.27/0.99  --qbf_pred_elim                         true
% 2.27/0.99  --qbf_split                             512
% 2.27/0.99  
% 2.27/0.99  ------ BMC1 Options
% 2.27/0.99  
% 2.27/0.99  --bmc1_incremental                      false
% 2.27/0.99  --bmc1_axioms                           reachable_all
% 2.27/0.99  --bmc1_min_bound                        0
% 2.27/0.99  --bmc1_max_bound                        -1
% 2.27/0.99  --bmc1_max_bound_default                -1
% 2.27/0.99  --bmc1_symbol_reachability              true
% 2.27/0.99  --bmc1_property_lemmas                  false
% 2.27/0.99  --bmc1_k_induction                      false
% 2.27/0.99  --bmc1_non_equiv_states                 false
% 2.27/0.99  --bmc1_deadlock                         false
% 2.27/0.99  --bmc1_ucm                              false
% 2.27/0.99  --bmc1_add_unsat_core                   none
% 2.27/0.99  --bmc1_unsat_core_children              false
% 2.27/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.27/0.99  --bmc1_out_stat                         full
% 2.27/0.99  --bmc1_ground_init                      false
% 2.27/0.99  --bmc1_pre_inst_next_state              false
% 2.27/0.99  --bmc1_pre_inst_state                   false
% 2.27/0.99  --bmc1_pre_inst_reach_state             false
% 2.27/0.99  --bmc1_out_unsat_core                   false
% 2.27/0.99  --bmc1_aig_witness_out                  false
% 2.27/0.99  --bmc1_verbose                          false
% 2.27/0.99  --bmc1_dump_clauses_tptp                false
% 2.27/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.27/0.99  --bmc1_dump_file                        -
% 2.27/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.27/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.27/0.99  --bmc1_ucm_extend_mode                  1
% 2.27/0.99  --bmc1_ucm_init_mode                    2
% 2.27/0.99  --bmc1_ucm_cone_mode                    none
% 2.27/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.27/0.99  --bmc1_ucm_relax_model                  4
% 2.27/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.27/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.27/0.99  --bmc1_ucm_layered_model                none
% 2.27/0.99  --bmc1_ucm_max_lemma_size               10
% 2.27/0.99  
% 2.27/0.99  ------ AIG Options
% 2.27/0.99  
% 2.27/0.99  --aig_mode                              false
% 2.27/0.99  
% 2.27/0.99  ------ Instantiation Options
% 2.27/0.99  
% 2.27/0.99  --instantiation_flag                    true
% 2.27/0.99  --inst_sos_flag                         false
% 2.27/0.99  --inst_sos_phase                        true
% 2.27/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.27/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.27/0.99  --inst_lit_sel_side                     num_symb
% 2.27/0.99  --inst_solver_per_active                1400
% 2.27/0.99  --inst_solver_calls_frac                1.
% 2.27/0.99  --inst_passive_queue_type               priority_queues
% 2.27/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.27/0.99  --inst_passive_queues_freq              [25;2]
% 2.27/0.99  --inst_dismatching                      true
% 2.27/0.99  --inst_eager_unprocessed_to_passive     true
% 2.27/0.99  --inst_prop_sim_given                   true
% 2.27/0.99  --inst_prop_sim_new                     false
% 2.27/0.99  --inst_subs_new                         false
% 2.27/0.99  --inst_eq_res_simp                      false
% 2.27/0.99  --inst_subs_given                       false
% 2.27/0.99  --inst_orphan_elimination               true
% 2.27/0.99  --inst_learning_loop_flag               true
% 2.27/0.99  --inst_learning_start                   3000
% 2.27/0.99  --inst_learning_factor                  2
% 2.27/0.99  --inst_start_prop_sim_after_learn       3
% 2.27/0.99  --inst_sel_renew                        solver
% 2.27/0.99  --inst_lit_activity_flag                true
% 2.27/0.99  --inst_restr_to_given                   false
% 2.27/0.99  --inst_activity_threshold               500
% 2.27/0.99  --inst_out_proof                        true
% 2.27/0.99  
% 2.27/0.99  ------ Resolution Options
% 2.27/0.99  
% 2.27/0.99  --resolution_flag                       true
% 2.27/0.99  --res_lit_sel                           adaptive
% 2.27/0.99  --res_lit_sel_side                      none
% 2.27/0.99  --res_ordering                          kbo
% 2.27/0.99  --res_to_prop_solver                    active
% 2.27/0.99  --res_prop_simpl_new                    false
% 2.27/0.99  --res_prop_simpl_given                  true
% 2.27/0.99  --res_passive_queue_type                priority_queues
% 2.27/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.27/0.99  --res_passive_queues_freq               [15;5]
% 2.27/0.99  --res_forward_subs                      full
% 2.27/0.99  --res_backward_subs                     full
% 2.27/0.99  --res_forward_subs_resolution           true
% 2.27/0.99  --res_backward_subs_resolution          true
% 2.27/0.99  --res_orphan_elimination                true
% 2.27/0.99  --res_time_limit                        2.
% 2.27/0.99  --res_out_proof                         true
% 2.27/0.99  
% 2.27/0.99  ------ Superposition Options
% 2.27/0.99  
% 2.27/0.99  --superposition_flag                    true
% 2.27/0.99  --sup_passive_queue_type                priority_queues
% 2.27/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.27/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.27/0.99  --demod_completeness_check              fast
% 2.27/0.99  --demod_use_ground                      true
% 2.27/0.99  --sup_to_prop_solver                    passive
% 2.27/0.99  --sup_prop_simpl_new                    true
% 2.27/0.99  --sup_prop_simpl_given                  true
% 2.27/0.99  --sup_fun_splitting                     false
% 2.27/0.99  --sup_smt_interval                      50000
% 2.27/0.99  
% 2.27/0.99  ------ Superposition Simplification Setup
% 2.27/0.99  
% 2.27/0.99  --sup_indices_passive                   []
% 2.27/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.27/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.27/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.27/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.27/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.27/0.99  --sup_full_bw                           [BwDemod]
% 2.27/0.99  --sup_immed_triv                        [TrivRules]
% 2.27/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.27/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.27/0.99  --sup_immed_bw_main                     []
% 2.27/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.27/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.27/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.27/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.27/0.99  
% 2.27/0.99  ------ Combination Options
% 2.27/0.99  
% 2.27/0.99  --comb_res_mult                         3
% 2.27/0.99  --comb_sup_mult                         2
% 2.27/0.99  --comb_inst_mult                        10
% 2.27/0.99  
% 2.27/0.99  ------ Debug Options
% 2.27/0.99  
% 2.27/0.99  --dbg_backtrace                         false
% 2.27/0.99  --dbg_dump_prop_clauses                 false
% 2.27/0.99  --dbg_dump_prop_clauses_file            -
% 2.27/0.99  --dbg_out_stat                          false
% 2.27/0.99  ------ Parsing...
% 2.27/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.27/0.99  
% 2.27/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.27/0.99  
% 2.27/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.27/0.99  
% 2.27/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.27/0.99  ------ Proving...
% 2.27/0.99  ------ Problem Properties 
% 2.27/0.99  
% 2.27/0.99  
% 2.27/0.99  clauses                                 16
% 2.27/0.99  conjectures                             1
% 2.27/0.99  EPR                                     0
% 2.27/0.99  Horn                                    10
% 2.27/0.99  unary                                   1
% 2.27/0.99  binary                                  7
% 2.27/0.99  lits                                    40
% 2.27/0.99  lits eq                                 10
% 2.27/0.99  fd_pure                                 0
% 2.27/0.99  fd_pseudo                               0
% 2.27/0.99  fd_cond                                 0
% 2.27/0.99  fd_pseudo_cond                          7
% 2.27/0.99  AC symbols                              0
% 2.27/0.99  
% 2.27/0.99  ------ Schedule dynamic 5 is on 
% 2.27/0.99  
% 2.27/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.27/0.99  
% 2.27/0.99  
% 2.27/0.99  ------ 
% 2.27/0.99  Current options:
% 2.27/0.99  ------ 
% 2.27/0.99  
% 2.27/0.99  ------ Input Options
% 2.27/0.99  
% 2.27/0.99  --out_options                           all
% 2.27/0.99  --tptp_safe_out                         true
% 2.27/0.99  --problem_path                          ""
% 2.27/0.99  --include_path                          ""
% 2.27/0.99  --clausifier                            res/vclausify_rel
% 2.27/0.99  --clausifier_options                    --mode clausify
% 2.27/0.99  --stdin                                 false
% 2.27/0.99  --stats_out                             all
% 2.27/0.99  
% 2.27/0.99  ------ General Options
% 2.27/0.99  
% 2.27/0.99  --fof                                   false
% 2.27/0.99  --time_out_real                         305.
% 2.27/0.99  --time_out_virtual                      -1.
% 2.27/0.99  --symbol_type_check                     false
% 2.27/0.99  --clausify_out                          false
% 2.27/0.99  --sig_cnt_out                           false
% 2.27/0.99  --trig_cnt_out                          false
% 2.27/0.99  --trig_cnt_out_tolerance                1.
% 2.27/0.99  --trig_cnt_out_sk_spl                   false
% 2.27/0.99  --abstr_cl_out                          false
% 2.27/0.99  
% 2.27/0.99  ------ Global Options
% 2.27/0.99  
% 2.27/0.99  --schedule                              default
% 2.27/0.99  --add_important_lit                     false
% 2.27/0.99  --prop_solver_per_cl                    1000
% 2.27/0.99  --min_unsat_core                        false
% 2.27/0.99  --soft_assumptions                      false
% 2.27/0.99  --soft_lemma_size                       3
% 2.27/0.99  --prop_impl_unit_size                   0
% 2.27/0.99  --prop_impl_unit                        []
% 2.27/0.99  --share_sel_clauses                     true
% 2.27/0.99  --reset_solvers                         false
% 2.27/0.99  --bc_imp_inh                            [conj_cone]
% 2.27/0.99  --conj_cone_tolerance                   3.
% 2.27/0.99  --extra_neg_conj                        none
% 2.27/0.99  --large_theory_mode                     true
% 2.27/0.99  --prolific_symb_bound                   200
% 2.27/0.99  --lt_threshold                          2000
% 2.27/0.99  --clause_weak_htbl                      true
% 2.27/0.99  --gc_record_bc_elim                     false
% 2.27/0.99  
% 2.27/0.99  ------ Preprocessing Options
% 2.27/0.99  
% 2.27/0.99  --preprocessing_flag                    true
% 2.27/0.99  --time_out_prep_mult                    0.1
% 2.27/0.99  --splitting_mode                        input
% 2.27/0.99  --splitting_grd                         true
% 2.27/0.99  --splitting_cvd                         false
% 2.27/0.99  --splitting_cvd_svl                     false
% 2.27/0.99  --splitting_nvd                         32
% 2.27/0.99  --sub_typing                            true
% 2.27/0.99  --prep_gs_sim                           true
% 2.27/0.99  --prep_unflatten                        true
% 2.27/0.99  --prep_res_sim                          true
% 2.27/0.99  --prep_upred                            true
% 2.27/0.99  --prep_sem_filter                       exhaustive
% 2.27/0.99  --prep_sem_filter_out                   false
% 2.27/0.99  --pred_elim                             true
% 2.27/0.99  --res_sim_input                         true
% 2.27/0.99  --eq_ax_congr_red                       true
% 2.27/0.99  --pure_diseq_elim                       true
% 2.27/0.99  --brand_transform                       false
% 2.27/0.99  --non_eq_to_eq                          false
% 2.27/0.99  --prep_def_merge                        true
% 2.27/0.99  --prep_def_merge_prop_impl              false
% 2.27/0.99  --prep_def_merge_mbd                    true
% 2.27/0.99  --prep_def_merge_tr_red                 false
% 2.27/0.99  --prep_def_merge_tr_cl                  false
% 2.27/0.99  --smt_preprocessing                     true
% 2.27/0.99  --smt_ac_axioms                         fast
% 2.27/0.99  --preprocessed_out                      false
% 2.27/0.99  --preprocessed_stats                    false
% 2.27/0.99  
% 2.27/0.99  ------ Abstraction refinement Options
% 2.27/0.99  
% 2.27/0.99  --abstr_ref                             []
% 2.27/0.99  --abstr_ref_prep                        false
% 2.27/0.99  --abstr_ref_until_sat                   false
% 2.27/0.99  --abstr_ref_sig_restrict                funpre
% 2.27/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.27/0.99  --abstr_ref_under                       []
% 2.27/0.99  
% 2.27/0.99  ------ SAT Options
% 2.27/0.99  
% 2.27/0.99  --sat_mode                              false
% 2.27/0.99  --sat_fm_restart_options                ""
% 2.27/0.99  --sat_gr_def                            false
% 2.27/0.99  --sat_epr_types                         true
% 2.27/0.99  --sat_non_cyclic_types                  false
% 2.27/0.99  --sat_finite_models                     false
% 2.27/0.99  --sat_fm_lemmas                         false
% 2.27/0.99  --sat_fm_prep                           false
% 2.27/0.99  --sat_fm_uc_incr                        true
% 2.27/0.99  --sat_out_model                         small
% 2.27/0.99  --sat_out_clauses                       false
% 2.27/0.99  
% 2.27/0.99  ------ QBF Options
% 2.27/0.99  
% 2.27/0.99  --qbf_mode                              false
% 2.27/0.99  --qbf_elim_univ                         false
% 2.27/0.99  --qbf_dom_inst                          none
% 2.27/0.99  --qbf_dom_pre_inst                      false
% 2.27/0.99  --qbf_sk_in                             false
% 2.27/0.99  --qbf_pred_elim                         true
% 2.27/0.99  --qbf_split                             512
% 2.27/0.99  
% 2.27/0.99  ------ BMC1 Options
% 2.27/0.99  
% 2.27/0.99  --bmc1_incremental                      false
% 2.27/0.99  --bmc1_axioms                           reachable_all
% 2.27/0.99  --bmc1_min_bound                        0
% 2.27/0.99  --bmc1_max_bound                        -1
% 2.27/0.99  --bmc1_max_bound_default                -1
% 2.27/0.99  --bmc1_symbol_reachability              true
% 2.27/0.99  --bmc1_property_lemmas                  false
% 2.27/0.99  --bmc1_k_induction                      false
% 2.27/0.99  --bmc1_non_equiv_states                 false
% 2.27/0.99  --bmc1_deadlock                         false
% 2.27/0.99  --bmc1_ucm                              false
% 2.27/0.99  --bmc1_add_unsat_core                   none
% 2.27/0.99  --bmc1_unsat_core_children              false
% 2.27/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.27/0.99  --bmc1_out_stat                         full
% 2.27/0.99  --bmc1_ground_init                      false
% 2.27/0.99  --bmc1_pre_inst_next_state              false
% 2.27/0.99  --bmc1_pre_inst_state                   false
% 2.27/0.99  --bmc1_pre_inst_reach_state             false
% 2.27/0.99  --bmc1_out_unsat_core                   false
% 2.27/0.99  --bmc1_aig_witness_out                  false
% 2.27/0.99  --bmc1_verbose                          false
% 2.27/0.99  --bmc1_dump_clauses_tptp                false
% 2.27/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.27/0.99  --bmc1_dump_file                        -
% 2.27/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.27/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.27/0.99  --bmc1_ucm_extend_mode                  1
% 2.27/0.99  --bmc1_ucm_init_mode                    2
% 2.27/0.99  --bmc1_ucm_cone_mode                    none
% 2.27/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.27/0.99  --bmc1_ucm_relax_model                  4
% 2.27/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.27/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.27/0.99  --bmc1_ucm_layered_model                none
% 2.27/0.99  --bmc1_ucm_max_lemma_size               10
% 2.27/0.99  
% 2.27/0.99  ------ AIG Options
% 2.27/0.99  
% 2.27/0.99  --aig_mode                              false
% 2.27/0.99  
% 2.27/0.99  ------ Instantiation Options
% 2.27/0.99  
% 2.27/0.99  --instantiation_flag                    true
% 2.27/0.99  --inst_sos_flag                         false
% 2.27/0.99  --inst_sos_phase                        true
% 2.27/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.27/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.27/0.99  --inst_lit_sel_side                     none
% 2.27/0.99  --inst_solver_per_active                1400
% 2.27/0.99  --inst_solver_calls_frac                1.
% 2.27/0.99  --inst_passive_queue_type               priority_queues
% 2.27/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.27/0.99  --inst_passive_queues_freq              [25;2]
% 2.27/0.99  --inst_dismatching                      true
% 2.27/0.99  --inst_eager_unprocessed_to_passive     true
% 2.27/0.99  --inst_prop_sim_given                   true
% 2.27/0.99  --inst_prop_sim_new                     false
% 2.27/0.99  --inst_subs_new                         false
% 2.27/0.99  --inst_eq_res_simp                      false
% 2.27/0.99  --inst_subs_given                       false
% 2.27/0.99  --inst_orphan_elimination               true
% 2.27/0.99  --inst_learning_loop_flag               true
% 2.27/0.99  --inst_learning_start                   3000
% 2.27/0.99  --inst_learning_factor                  2
% 2.27/0.99  --inst_start_prop_sim_after_learn       3
% 2.27/0.99  --inst_sel_renew                        solver
% 2.27/0.99  --inst_lit_activity_flag                true
% 2.27/0.99  --inst_restr_to_given                   false
% 2.27/0.99  --inst_activity_threshold               500
% 2.27/0.99  --inst_out_proof                        true
% 2.27/0.99  
% 2.27/0.99  ------ Resolution Options
% 2.27/0.99  
% 2.27/0.99  --resolution_flag                       false
% 2.27/0.99  --res_lit_sel                           adaptive
% 2.27/0.99  --res_lit_sel_side                      none
% 2.27/0.99  --res_ordering                          kbo
% 2.27/0.99  --res_to_prop_solver                    active
% 2.27/0.99  --res_prop_simpl_new                    false
% 2.27/0.99  --res_prop_simpl_given                  true
% 2.27/0.99  --res_passive_queue_type                priority_queues
% 2.27/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.27/0.99  --res_passive_queues_freq               [15;5]
% 2.27/0.99  --res_forward_subs                      full
% 2.27/0.99  --res_backward_subs                     full
% 2.27/0.99  --res_forward_subs_resolution           true
% 2.27/0.99  --res_backward_subs_resolution          true
% 2.27/0.99  --res_orphan_elimination                true
% 2.27/0.99  --res_time_limit                        2.
% 2.27/0.99  --res_out_proof                         true
% 2.27/0.99  
% 2.27/0.99  ------ Superposition Options
% 2.27/0.99  
% 2.27/0.99  --superposition_flag                    true
% 2.27/0.99  --sup_passive_queue_type                priority_queues
% 2.27/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.27/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.27/0.99  --demod_completeness_check              fast
% 2.27/0.99  --demod_use_ground                      true
% 2.27/0.99  --sup_to_prop_solver                    passive
% 2.27/0.99  --sup_prop_simpl_new                    true
% 2.27/0.99  --sup_prop_simpl_given                  true
% 2.27/0.99  --sup_fun_splitting                     false
% 2.27/0.99  --sup_smt_interval                      50000
% 2.27/0.99  
% 2.27/0.99  ------ Superposition Simplification Setup
% 2.27/0.99  
% 2.27/0.99  --sup_indices_passive                   []
% 2.27/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.27/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.27/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.27/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.27/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.27/0.99  --sup_full_bw                           [BwDemod]
% 2.27/0.99  --sup_immed_triv                        [TrivRules]
% 2.27/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.27/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.27/0.99  --sup_immed_bw_main                     []
% 2.27/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.27/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.27/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.27/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.27/0.99  
% 2.27/0.99  ------ Combination Options
% 2.27/0.99  
% 2.27/0.99  --comb_res_mult                         3
% 2.27/0.99  --comb_sup_mult                         2
% 2.27/0.99  --comb_inst_mult                        10
% 2.27/0.99  
% 2.27/0.99  ------ Debug Options
% 2.27/0.99  
% 2.27/0.99  --dbg_backtrace                         false
% 2.27/0.99  --dbg_dump_prop_clauses                 false
% 2.27/0.99  --dbg_dump_prop_clauses_file            -
% 2.27/0.99  --dbg_out_stat                          false
% 2.27/0.99  
% 2.27/0.99  
% 2.27/0.99  
% 2.27/0.99  
% 2.27/0.99  ------ Proving...
% 2.27/0.99  
% 2.27/0.99  
% 2.27/0.99  % SZS status Theorem for theBenchmark.p
% 2.27/0.99  
% 2.27/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.27/0.99  
% 2.27/0.99  fof(f2,axiom,(
% 2.27/0.99    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.27/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/0.99  
% 2.27/0.99  fof(f9,plain,(
% 2.27/0.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.27/0.99    inference(nnf_transformation,[],[f2])).
% 2.27/0.99  
% 2.27/0.99  fof(f10,plain,(
% 2.27/0.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.27/0.99    inference(flattening,[],[f9])).
% 2.27/0.99  
% 2.27/0.99  fof(f11,plain,(
% 2.27/0.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.27/0.99    inference(rectify,[],[f10])).
% 2.27/0.99  
% 2.27/0.99  fof(f12,plain,(
% 2.27/0.99    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 2.27/0.99    introduced(choice_axiom,[])).
% 2.27/0.99  
% 2.27/0.99  fof(f13,plain,(
% 2.27/0.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.27/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f12])).
% 2.27/0.99  
% 2.27/0.99  fof(f27,plain,(
% 2.27/0.99    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.27/0.99    inference(cnf_transformation,[],[f13])).
% 2.27/0.99  
% 2.27/0.99  fof(f43,plain,(
% 2.27/0.99    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 2.27/0.99    inference(equality_resolution,[],[f27])).
% 2.27/0.99  
% 2.27/0.99  fof(f4,axiom,(
% 2.27/0.99    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 2.27/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/0.99  
% 2.27/0.99  fof(f14,plain,(
% 2.27/0.99    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 2.27/0.99    inference(nnf_transformation,[],[f4])).
% 2.27/0.99  
% 2.27/0.99  fof(f15,plain,(
% 2.27/0.99    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 2.27/0.99    inference(rectify,[],[f14])).
% 2.27/0.99  
% 2.27/0.99  fof(f18,plain,(
% 2.27/0.99    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0))),
% 2.27/0.99    introduced(choice_axiom,[])).
% 2.27/0.99  
% 2.27/0.99  fof(f17,plain,(
% 2.27/0.99    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) => r2_hidden(k4_tarski(X2,sK2(X0,X1)),X0))) )),
% 2.27/0.99    introduced(choice_axiom,[])).
% 2.27/0.99  
% 2.27/0.99  fof(f16,plain,(
% 2.27/0.99    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK1(X0,X1),X3),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK1(X0,X1),X4),X0) | r2_hidden(sK1(X0,X1),X1))))),
% 2.27/0.99    introduced(choice_axiom,[])).
% 2.27/0.99  
% 2.27/0.99  fof(f19,plain,(
% 2.27/0.99    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK1(X0,X1),X3),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 2.27/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f15,f18,f17,f16])).
% 2.27/0.99  
% 2.27/0.99  fof(f35,plain,(
% 2.27/0.99    ( ! [X0,X1] : (k1_relat_1(X0) = X1 | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) | r2_hidden(sK1(X0,X1),X1)) )),
% 2.27/0.99    inference(cnf_transformation,[],[f19])).
% 2.27/0.99  
% 2.27/0.99  fof(f3,axiom,(
% 2.27/0.99    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.27/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/0.99  
% 2.27/0.99  fof(f32,plain,(
% 2.27/0.99    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.27/0.99    inference(cnf_transformation,[],[f3])).
% 2.27/0.99  
% 2.27/0.99  fof(f5,axiom,(
% 2.27/0.99    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 2.27/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/0.99  
% 2.27/0.99  fof(f20,plain,(
% 2.27/0.99    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 2.27/0.99    inference(nnf_transformation,[],[f5])).
% 2.27/0.99  
% 2.27/0.99  fof(f21,plain,(
% 2.27/0.99    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 2.27/0.99    inference(rectify,[],[f20])).
% 2.27/0.99  
% 2.27/0.99  fof(f24,plain,(
% 2.27/0.99    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK6(X0,X5),X5),X0))),
% 2.27/0.99    introduced(choice_axiom,[])).
% 2.27/0.99  
% 2.27/0.99  fof(f23,plain,(
% 2.27/0.99    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) => r2_hidden(k4_tarski(sK5(X0,X1),X2),X0))) )),
% 2.27/0.99    introduced(choice_axiom,[])).
% 2.27/0.99  
% 2.27/0.99  fof(f22,plain,(
% 2.27/0.99    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK4(X0,X1)),X0) | r2_hidden(sK4(X0,X1),X1))))),
% 2.27/0.99    introduced(choice_axiom,[])).
% 2.27/0.99  
% 2.27/0.99  fof(f25,plain,(
% 2.27/0.99    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0) | r2_hidden(sK4(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK6(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 2.27/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f21,f24,f23,f22])).
% 2.27/0.99  
% 2.27/0.99  fof(f39,plain,(
% 2.27/0.99    ( ! [X0,X1] : (k2_relat_1(X0) = X1 | r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0) | r2_hidden(sK4(X0,X1),X1)) )),
% 2.27/0.99    inference(cnf_transformation,[],[f25])).
% 2.27/0.99  
% 2.27/0.99  fof(f6,conjecture,(
% 2.27/0.99    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.27/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/0.99  
% 2.27/0.99  fof(f7,negated_conjecture,(
% 2.27/0.99    ~(k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0))),
% 2.27/0.99    inference(negated_conjecture,[],[f6])).
% 2.27/0.99  
% 2.27/0.99  fof(f8,plain,(
% 2.27/0.99    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 2.27/0.99    inference(ennf_transformation,[],[f7])).
% 2.27/0.99  
% 2.27/0.99  fof(f41,plain,(
% 2.27/0.99    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 2.27/0.99    inference(cnf_transformation,[],[f8])).
% 2.27/0.99  
% 2.27/0.99  cnf(c_167,plain,
% 2.27/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.27/0.99      theory(equality) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_1573,plain,
% 2.27/0.99      ( r2_hidden(X0,X1)
% 2.27/0.99      | ~ r2_hidden(sK1(X2,X3),X3)
% 2.27/0.99      | X1 != X3
% 2.27/0.99      | X0 != sK1(X2,X3) ),
% 2.27/0.99      inference(instantiation,[status(thm)],[c_167]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_3051,plain,
% 2.27/0.99      ( ~ r2_hidden(sK1(X0,X1),X1)
% 2.27/0.99      | r2_hidden(sK1(X0,X1),X2)
% 2.27/0.99      | X2 != X1
% 2.27/0.99      | sK1(X0,X1) != sK1(X0,X1) ),
% 2.27/0.99      inference(instantiation,[status(thm)],[c_1573]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_10118,plain,
% 2.27/0.99      ( ~ r2_hidden(sK1(X0,X1),X1)
% 2.27/0.99      | r2_hidden(sK1(X0,X1),k4_xboole_0(X2,X1))
% 2.27/0.99      | sK1(X0,X1) != sK1(X0,X1)
% 2.27/0.99      | k4_xboole_0(X2,X1) != X1 ),
% 2.27/0.99      inference(instantiation,[status(thm)],[c_3051]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_10120,plain,
% 2.27/0.99      ( r2_hidden(sK1(k1_xboole_0,k1_xboole_0),k4_xboole_0(k1_xboole_0,k1_xboole_0))
% 2.27/0.99      | ~ r2_hidden(sK1(k1_xboole_0,k1_xboole_0),k1_xboole_0)
% 2.27/0.99      | sK1(k1_xboole_0,k1_xboole_0) != sK1(k1_xboole_0,k1_xboole_0)
% 2.27/0.99      | k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
% 2.27/0.99      inference(instantiation,[status(thm)],[c_10118]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_164,plain,( X0 = X0 ),theory(equality) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_3052,plain,
% 2.27/0.99      ( sK1(X0,X1) = sK1(X0,X1) ),
% 2.27/0.99      inference(instantiation,[status(thm)],[c_164]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_3055,plain,
% 2.27/0.99      ( sK1(k1_xboole_0,k1_xboole_0) = sK1(k1_xboole_0,k1_xboole_0) ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_3052]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_541,plain,
% 2.27/1.00      ( r2_hidden(X0,X1)
% 2.27/1.00      | ~ r2_hidden(sK4(X2,X3),X3)
% 2.27/1.00      | X1 != X3
% 2.27/1.00      | X0 != sK4(X2,X3) ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_167]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_637,plain,
% 2.27/1.00      ( ~ r2_hidden(sK4(X0,X1),X1)
% 2.27/1.00      | r2_hidden(sK4(X0,X1),X2)
% 2.27/1.00      | X2 != X1
% 2.27/1.00      | sK4(X0,X1) != sK4(X0,X1) ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_541]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_2086,plain,
% 2.27/1.00      ( ~ r2_hidden(sK4(X0,X1),X1)
% 2.27/1.00      | r2_hidden(sK4(X0,X1),k4_xboole_0(X2,X1))
% 2.27/1.00      | sK4(X0,X1) != sK4(X0,X1)
% 2.27/1.00      | k4_xboole_0(X2,X1) != X1 ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_637]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_2087,plain,
% 2.27/1.00      ( sK4(X0,X1) != sK4(X0,X1)
% 2.27/1.00      | k4_xboole_0(X2,X1) != X1
% 2.27/1.00      | r2_hidden(sK4(X0,X1),X1) != iProver_top
% 2.27/1.00      | r2_hidden(sK4(X0,X1),k4_xboole_0(X2,X1)) = iProver_top ),
% 2.27/1.00      inference(predicate_to_equality,[status(thm)],[c_2086]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_2089,plain,
% 2.27/1.00      ( sK4(k1_xboole_0,k1_xboole_0) != sK4(k1_xboole_0,k1_xboole_0)
% 2.27/1.00      | k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 2.27/1.00      | r2_hidden(sK4(k1_xboole_0,k1_xboole_0),k4_xboole_0(k1_xboole_0,k1_xboole_0)) = iProver_top
% 2.27/1.00      | r2_hidden(sK4(k1_xboole_0,k1_xboole_0),k1_xboole_0) != iProver_top ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_2087]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_4,plain,
% 2.27/1.00      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 2.27/1.00      inference(cnf_transformation,[],[f43]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1572,plain,
% 2.27/1.00      ( ~ r2_hidden(sK1(X0,X1),X1)
% 2.27/1.00      | ~ r2_hidden(sK1(X0,X1),k4_xboole_0(X2,X1)) ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1579,plain,
% 2.27/1.00      ( ~ r2_hidden(sK1(k1_xboole_0,k1_xboole_0),k4_xboole_0(k1_xboole_0,k1_xboole_0))
% 2.27/1.00      | ~ r2_hidden(sK1(k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_1572]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_8,plain,
% 2.27/1.00      ( r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
% 2.27/1.00      | r2_hidden(sK1(X0,X1),X1)
% 2.27/1.00      | k1_relat_1(X0) = X1 ),
% 2.27/1.00      inference(cnf_transformation,[],[f35]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_405,plain,
% 2.27/1.00      ( k1_relat_1(X0) = X1
% 2.27/1.00      | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) = iProver_top
% 2.27/1.00      | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
% 2.27/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_6,plain,
% 2.27/1.00      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 2.27/1.00      inference(cnf_transformation,[],[f32]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_408,plain,
% 2.27/1.00      ( r2_hidden(X0,X1) != iProver_top
% 2.27/1.00      | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
% 2.27/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_589,plain,
% 2.27/1.00      ( r2_hidden(X0,X1) != iProver_top
% 2.27/1.00      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.27/1.00      inference(superposition,[status(thm)],[c_6,c_408]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1497,plain,
% 2.27/1.00      ( k1_relat_1(X0) = X1
% 2.27/1.00      | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),k1_xboole_0) != iProver_top
% 2.27/1.00      | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
% 2.27/1.00      inference(superposition,[status(thm)],[c_405,c_589]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1547,plain,
% 2.27/1.00      ( ~ r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),k1_xboole_0)
% 2.27/1.00      | r2_hidden(sK1(X0,X1),X1)
% 2.27/1.00      | k1_relat_1(X0) = X1 ),
% 2.27/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_1497]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1549,plain,
% 2.27/1.00      ( ~ r2_hidden(k4_tarski(sK1(k1_xboole_0,k1_xboole_0),sK2(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
% 2.27/1.00      | r2_hidden(sK1(k1_xboole_0,k1_xboole_0),k1_xboole_0)
% 2.27/1.00      | k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_1547]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_12,plain,
% 2.27/1.00      ( r2_hidden(sK4(X0,X1),X1)
% 2.27/1.00      | r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0)
% 2.27/1.00      | k2_relat_1(X0) = X1 ),
% 2.27/1.00      inference(cnf_transformation,[],[f39]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_401,plain,
% 2.27/1.00      ( k2_relat_1(X0) = X1
% 2.27/1.00      | r2_hidden(sK4(X0,X1),X1) = iProver_top
% 2.27/1.00      | r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0) = iProver_top ),
% 2.27/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_852,plain,
% 2.27/1.00      ( k2_relat_1(X0) = X1
% 2.27/1.00      | r2_hidden(sK4(X0,X1),X1) = iProver_top
% 2.27/1.00      | r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),k1_xboole_0) != iProver_top ),
% 2.27/1.00      inference(superposition,[status(thm)],[c_401,c_589]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_888,plain,
% 2.27/1.00      ( k2_relat_1(k1_xboole_0) = k1_xboole_0
% 2.27/1.00      | r2_hidden(sK4(k1_xboole_0,k1_xboole_0),k1_xboole_0) = iProver_top
% 2.27/1.00      | r2_hidden(k4_tarski(sK5(k1_xboole_0,k1_xboole_0),sK4(k1_xboole_0,k1_xboole_0)),k1_xboole_0) != iProver_top ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_852]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_165,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_652,plain,
% 2.27/1.00      ( k1_relat_1(k1_xboole_0) != X0
% 2.27/1.00      | k1_xboole_0 != X0
% 2.27/1.00      | k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_165]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_653,plain,
% 2.27/1.00      ( k1_relat_1(k1_xboole_0) != k1_xboole_0
% 2.27/1.00      | k1_xboole_0 = k1_relat_1(k1_xboole_0)
% 2.27/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_652]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_638,plain,
% 2.27/1.00      ( sK4(X0,X1) = sK4(X0,X1) ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_164]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_641,plain,
% 2.27/1.00      ( sK4(k1_xboole_0,k1_xboole_0) = sK4(k1_xboole_0,k1_xboole_0) ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_638]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_540,plain,
% 2.27/1.00      ( ~ r2_hidden(sK4(X0,X1),X1)
% 2.27/1.00      | ~ r2_hidden(sK4(X0,X1),k4_xboole_0(X2,X1)) ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_546,plain,
% 2.27/1.00      ( r2_hidden(sK4(X0,X1),X1) != iProver_top
% 2.27/1.00      | r2_hidden(sK4(X0,X1),k4_xboole_0(X2,X1)) != iProver_top ),
% 2.27/1.00      inference(predicate_to_equality,[status(thm)],[c_540]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_548,plain,
% 2.27/1.00      ( r2_hidden(sK4(k1_xboole_0,k1_xboole_0),k4_xboole_0(k1_xboole_0,k1_xboole_0)) != iProver_top
% 2.27/1.00      | r2_hidden(sK4(k1_xboole_0,k1_xboole_0),k1_xboole_0) != iProver_top ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_546]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_522,plain,
% 2.27/1.00      ( k2_relat_1(k1_xboole_0) != X0
% 2.27/1.00      | k1_xboole_0 != X0
% 2.27/1.00      | k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_165]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_523,plain,
% 2.27/1.00      ( k2_relat_1(k1_xboole_0) != k1_xboole_0
% 2.27/1.00      | k1_xboole_0 = k2_relat_1(k1_xboole_0)
% 2.27/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_522]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_177,plain,
% 2.27/1.00      ( k1_xboole_0 = k1_xboole_0 ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_164]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_40,plain,
% 2.27/1.00      ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_35,plain,
% 2.27/1.00      ( r2_hidden(k4_tarski(sK1(k1_xboole_0,k1_xboole_0),sK2(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
% 2.27/1.00      | r2_hidden(sK1(k1_xboole_0,k1_xboole_0),k1_xboole_0)
% 2.27/1.00      | k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_22,plain,
% 2.27/1.00      ( k2_relat_1(X0) = X1
% 2.27/1.00      | r2_hidden(sK4(X0,X1),X1) = iProver_top
% 2.27/1.00      | r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0) = iProver_top ),
% 2.27/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_24,plain,
% 2.27/1.00      ( k2_relat_1(k1_xboole_0) = k1_xboole_0
% 2.27/1.00      | r2_hidden(sK4(k1_xboole_0,k1_xboole_0),k1_xboole_0) = iProver_top
% 2.27/1.00      | r2_hidden(k4_tarski(sK5(k1_xboole_0,k1_xboole_0),sK4(k1_xboole_0,k1_xboole_0)),k1_xboole_0) = iProver_top ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_22]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_15,negated_conjecture,
% 2.27/1.00      ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
% 2.27/1.00      | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
% 2.27/1.00      inference(cnf_transformation,[],[f41]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(contradiction,plain,
% 2.27/1.00      ( $false ),
% 2.27/1.00      inference(minisat,
% 2.27/1.00                [status(thm)],
% 2.27/1.00                [c_10120,c_3055,c_2089,c_1579,c_1549,c_888,c_653,c_641,
% 2.27/1.00                 c_548,c_523,c_177,c_40,c_35,c_24,c_15]) ).
% 2.27/1.00  
% 2.27/1.00  
% 2.27/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.27/1.00  
% 2.27/1.00  ------                               Statistics
% 2.27/1.00  
% 2.27/1.00  ------ General
% 2.27/1.00  
% 2.27/1.00  abstr_ref_over_cycles:                  0
% 2.27/1.00  abstr_ref_under_cycles:                 0
% 2.27/1.00  gc_basic_clause_elim:                   0
% 2.27/1.00  forced_gc_time:                         0
% 2.27/1.00  parsing_time:                           0.008
% 2.27/1.00  unif_index_cands_time:                  0.
% 2.27/1.00  unif_index_add_time:                    0.
% 2.27/1.00  orderings_time:                         0.
% 2.27/1.00  out_proof_time:                         0.01
% 2.27/1.00  total_time:                             0.301
% 2.27/1.00  num_of_symbols:                         44
% 2.27/1.00  num_of_terms:                           15428
% 2.27/1.00  
% 2.27/1.00  ------ Preprocessing
% 2.27/1.00  
% 2.27/1.00  num_of_splits:                          0
% 2.27/1.00  num_of_split_atoms:                     0
% 2.27/1.00  num_of_reused_defs:                     0
% 2.27/1.00  num_eq_ax_congr_red:                    32
% 2.27/1.00  num_of_sem_filtered_clauses:            1
% 2.27/1.00  num_of_subtypes:                        0
% 2.27/1.00  monotx_restored_types:                  0
% 2.27/1.00  sat_num_of_epr_types:                   0
% 2.27/1.00  sat_num_of_non_cyclic_types:            0
% 2.27/1.00  sat_guarded_non_collapsed_types:        0
% 2.27/1.00  num_pure_diseq_elim:                    0
% 2.27/1.00  simp_replaced_by:                       0
% 2.27/1.00  res_preprocessed:                       63
% 2.27/1.00  prep_upred:                             0
% 2.27/1.00  prep_unflattend:                        0
% 2.27/1.00  smt_new_axioms:                         0
% 2.27/1.00  pred_elim_cands:                        1
% 2.27/1.00  pred_elim:                              0
% 2.27/1.00  pred_elim_cl:                           0
% 2.27/1.00  pred_elim_cycles:                       1
% 2.27/1.00  merged_defs:                            0
% 2.27/1.00  merged_defs_ncl:                        0
% 2.27/1.00  bin_hyper_res:                          0
% 2.27/1.00  prep_cycles:                            3
% 2.27/1.00  pred_elim_time:                         0.
% 2.27/1.00  splitting_time:                         0.
% 2.27/1.00  sem_filter_time:                        0.
% 2.27/1.00  monotx_time:                            0.
% 2.27/1.00  subtype_inf_time:                       0.
% 2.27/1.00  
% 2.27/1.00  ------ Problem properties
% 2.27/1.00  
% 2.27/1.00  clauses:                                16
% 2.27/1.00  conjectures:                            1
% 2.27/1.00  epr:                                    0
% 2.27/1.00  horn:                                   10
% 2.27/1.00  ground:                                 1
% 2.27/1.00  unary:                                  1
% 2.27/1.00  binary:                                 7
% 2.27/1.00  lits:                                   40
% 2.27/1.00  lits_eq:                                10
% 2.27/1.00  fd_pure:                                0
% 2.27/1.00  fd_pseudo:                              0
% 2.27/1.00  fd_cond:                                0
% 2.27/1.00  fd_pseudo_cond:                         7
% 2.27/1.00  ac_symbols:                             0
% 2.27/1.00  
% 2.27/1.00  ------ Propositional Solver
% 2.27/1.00  
% 2.27/1.00  prop_solver_calls:                      26
% 2.27/1.00  prop_fast_solver_calls:                 447
% 2.27/1.00  smt_solver_calls:                       0
% 2.27/1.00  smt_fast_solver_calls:                  0
% 2.27/1.00  prop_num_of_clauses:                    4638
% 2.27/1.00  prop_preprocess_simplified:             6313
% 2.27/1.00  prop_fo_subsumed:                       0
% 2.27/1.00  prop_solver_time:                       0.
% 2.27/1.00  smt_solver_time:                        0.
% 2.27/1.00  smt_fast_solver_time:                   0.
% 2.27/1.00  prop_fast_solver_time:                  0.
% 2.27/1.00  prop_unsat_core_time:                   0.001
% 2.27/1.00  
% 2.27/1.00  ------ QBF
% 2.27/1.00  
% 2.27/1.00  qbf_q_res:                              0
% 2.27/1.00  qbf_num_tautologies:                    0
% 2.27/1.00  qbf_prep_cycles:                        0
% 2.27/1.00  
% 2.27/1.00  ------ BMC1
% 2.27/1.00  
% 2.27/1.00  bmc1_current_bound:                     -1
% 2.27/1.00  bmc1_last_solved_bound:                 -1
% 2.27/1.00  bmc1_unsat_core_size:                   -1
% 2.27/1.00  bmc1_unsat_core_parents_size:           -1
% 2.27/1.00  bmc1_merge_next_fun:                    0
% 2.27/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.27/1.00  
% 2.27/1.00  ------ Instantiation
% 2.27/1.00  
% 2.27/1.00  inst_num_of_clauses:                    864
% 2.27/1.00  inst_num_in_passive:                    55
% 2.27/1.00  inst_num_in_active:                     396
% 2.27/1.00  inst_num_in_unprocessed:                412
% 2.27/1.00  inst_num_of_loops:                      509
% 2.27/1.00  inst_num_of_learning_restarts:          0
% 2.27/1.00  inst_num_moves_active_passive:          107
% 2.27/1.00  inst_lit_activity:                      0
% 2.27/1.00  inst_lit_activity_moves:                0
% 2.27/1.00  inst_num_tautologies:                   0
% 2.27/1.00  inst_num_prop_implied:                  0
% 2.27/1.00  inst_num_existing_simplified:           0
% 2.27/1.00  inst_num_eq_res_simplified:             0
% 2.27/1.00  inst_num_child_elim:                    0
% 2.27/1.00  inst_num_of_dismatching_blockings:      602
% 2.27/1.00  inst_num_of_non_proper_insts:           707
% 2.27/1.00  inst_num_of_duplicates:                 0
% 2.27/1.00  inst_inst_num_from_inst_to_res:         0
% 2.27/1.00  inst_dismatching_checking_time:         0.
% 2.27/1.00  
% 2.27/1.00  ------ Resolution
% 2.27/1.00  
% 2.27/1.00  res_num_of_clauses:                     0
% 2.27/1.00  res_num_in_passive:                     0
% 2.27/1.00  res_num_in_active:                      0
% 2.27/1.00  res_num_of_loops:                       66
% 2.27/1.00  res_forward_subset_subsumed:            55
% 2.27/1.00  res_backward_subset_subsumed:           0
% 2.27/1.00  res_forward_subsumed:                   0
% 2.27/1.00  res_backward_subsumed:                  0
% 2.27/1.00  res_forward_subsumption_resolution:     0
% 2.27/1.00  res_backward_subsumption_resolution:    0
% 2.27/1.00  res_clause_to_clause_subsumption:       1030
% 2.27/1.00  res_orphan_elimination:                 0
% 2.27/1.00  res_tautology_del:                      146
% 2.27/1.00  res_num_eq_res_simplified:              0
% 2.27/1.00  res_num_sel_changes:                    0
% 2.27/1.00  res_moves_from_active_to_pass:          0
% 2.27/1.00  
% 2.27/1.00  ------ Superposition
% 2.27/1.00  
% 2.27/1.00  sup_time_total:                         0.
% 2.27/1.00  sup_time_generating:                    0.
% 2.27/1.00  sup_time_sim_full:                      0.
% 2.27/1.00  sup_time_sim_immed:                     0.
% 2.27/1.00  
% 2.27/1.00  sup_num_of_clauses:                     655
% 2.27/1.00  sup_num_in_active:                      100
% 2.27/1.00  sup_num_in_passive:                     555
% 2.27/1.00  sup_num_of_loops:                       100
% 2.27/1.00  sup_fw_superposition:                   639
% 2.27/1.00  sup_bw_superposition:                   108
% 2.27/1.00  sup_immediate_simplified:               8
% 2.27/1.00  sup_given_eliminated:                   0
% 2.27/1.00  comparisons_done:                       0
% 2.27/1.00  comparisons_avoided:                    0
% 2.27/1.00  
% 2.27/1.00  ------ Simplifications
% 2.27/1.00  
% 2.27/1.00  
% 2.27/1.00  sim_fw_subset_subsumed:                 0
% 2.27/1.00  sim_bw_subset_subsumed:                 0
% 2.27/1.00  sim_fw_subsumed:                        4
% 2.27/1.00  sim_bw_subsumed:                        0
% 2.27/1.00  sim_fw_subsumption_res:                 0
% 2.27/1.00  sim_bw_subsumption_res:                 0
% 2.27/1.00  sim_tautology_del:                      10
% 2.27/1.00  sim_eq_tautology_del:                   0
% 2.27/1.00  sim_eq_res_simp:                        1
% 2.27/1.00  sim_fw_demodulated:                     4
% 2.27/1.00  sim_bw_demodulated:                     0
% 2.27/1.00  sim_light_normalised:                   0
% 2.27/1.00  sim_joinable_taut:                      0
% 2.27/1.00  sim_joinable_simp:                      0
% 2.27/1.00  sim_ac_normalised:                      0
% 2.27/1.00  sim_smt_subsumption:                    0
% 2.27/1.00  
%------------------------------------------------------------------------------
