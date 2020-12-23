%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:36:23 EST 2020

% Result     : Theorem 3.92s
% Output     : CNFRefutation 3.92s
% Verified   : 
% Statistics : Number of formulae       :   94 (2516 expanded)
%              Number of clauses        :   58 ( 722 expanded)
%              Number of leaves         :    9 ( 524 expanded)
%              Depth                    :   24
%              Number of atoms          :  378 (16603 expanded)
%              Number of equality atoms :  137 (6620 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f7,plain,(
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
    inference(flattening,[],[f6])).

fof(f8,plain,(
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
    inference(rectify,[],[f7])).

fof(f9,plain,(
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

fof(f10,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f9])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
      <=> ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f5,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
    <~> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,X2)
        | r2_hidden(X0,X2)
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,X2)
        | r2_hidden(X0,X2)
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) ) ) ),
    inference(flattening,[],[f16])).

fof(f18,plain,
    ( ? [X0,X1,X2] :
        ( ( r2_hidden(X1,X2)
          | r2_hidden(X0,X2)
          | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1) )
        & ( ( ~ r2_hidden(X1,X2)
            & ~ r2_hidden(X0,X2) )
          | k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) ) )
   => ( ( r2_hidden(sK3,sK4)
        | r2_hidden(sK2,sK4)
        | k4_xboole_0(k2_tarski(sK2,sK3),sK4) != k2_tarski(sK2,sK3) )
      & ( ( ~ r2_hidden(sK3,sK4)
          & ~ r2_hidden(sK2,sK4) )
        | k4_xboole_0(k2_tarski(sK2,sK3),sK4) = k2_tarski(sK2,sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ( r2_hidden(sK3,sK4)
      | r2_hidden(sK2,sK4)
      | k4_xboole_0(k2_tarski(sK2,sK3),sK4) != k2_tarski(sK2,sK3) )
    & ( ( ~ r2_hidden(sK3,sK4)
        & ~ r2_hidden(sK2,sK4) )
      | k4_xboole_0(k2_tarski(sK2,sK3),sK4) = k2_tarski(sK2,sK3) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f17,f18])).

fof(f34,plain,
    ( r2_hidden(sK3,sK4)
    | r2_hidden(sK2,sK4)
    | k4_xboole_0(k2_tarski(sK2,sK3),sK4) != k2_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f26,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f42,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k2_tarski(X0,X1)) ) ),
    inference(equality_resolution,[],[f26])).

fof(f32,plain,
    ( ~ r2_hidden(sK2,sK4)
    | k4_xboole_0(k2_tarski(sK2,sK3),sK4) = k2_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f33,plain,
    ( ~ r2_hidden(sK3,sK4)
    | k4_xboole_0(k2_tarski(sK2,sK3),sK4) = k2_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f27,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f40,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f27])).

fof(f41,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_tarski(X4,X1)) ),
    inference(equality_resolution,[],[f40])).

fof(f28,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f38,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f28])).

fof(f39,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_tarski(X0,X4)) ),
    inference(equality_resolution,[],[f38])).

fof(f21,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f36,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f21])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f22,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f35,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f22])).

cnf(c_163,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_160,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1015,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_163,c_160])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_12,negated_conjecture,
    ( r2_hidden(sK2,sK4)
    | r2_hidden(sK3,sK4)
    | k4_xboole_0(k2_tarski(sK2,sK3),sK4) != k2_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1025,plain,
    ( r2_hidden(sK0(k2_tarski(sK2,sK3),sK4,k2_tarski(sK2,sK3)),k2_tarski(sK2,sK3))
    | r2_hidden(sK2,sK4)
    | r2_hidden(sK3,sK4) ),
    inference(resolution,[status(thm)],[c_2,c_12])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k2_tarski(X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1143,plain,
    ( r2_hidden(sK2,sK4)
    | r2_hidden(sK3,sK4)
    | sK0(k2_tarski(sK2,sK3),sK4,k2_tarski(sK2,sK3)) = sK2
    | sK0(k2_tarski(sK2,sK3),sK4,k2_tarski(sK2,sK3)) = sK3 ),
    inference(resolution,[status(thm)],[c_1025,c_11])).

cnf(c_2881,plain,
    ( r2_hidden(sK0(k2_tarski(sK2,sK3),sK4,k2_tarski(sK2,sK3)),X0)
    | ~ r2_hidden(sK2,X0)
    | r2_hidden(sK2,sK4)
    | r2_hidden(sK3,sK4)
    | sK0(k2_tarski(sK2,sK3),sK4,k2_tarski(sK2,sK3)) = sK3 ),
    inference(resolution,[status(thm)],[c_1015,c_1143])).

cnf(c_14,negated_conjecture,
    ( ~ r2_hidden(sK2,sK4)
    | k4_xboole_0(k2_tarski(sK2,sK3),sK4) = k2_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_13,negated_conjecture,
    ( ~ r2_hidden(sK3,sK4)
    | k4_xboole_0(k2_tarski(sK2,sK3),sK4) = k2_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_19,plain,
    ( ~ r2_hidden(sK2,k2_tarski(sK2,sK2))
    | sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_10,plain,
    ( r2_hidden(X0,k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_22,plain,
    ( r2_hidden(sK2,k2_tarski(sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_9,plain,
    ( r2_hidden(X0,k2_tarski(X1,X0)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_689,plain,
    ( r2_hidden(sK3,k2_tarski(X0,sK3)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_691,plain,
    ( r2_hidden(sK3,k2_tarski(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_689])).

cnf(c_703,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_160])).

cnf(c_583,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k4_xboole_0(X3,X4))
    | X2 != X0
    | k4_xboole_0(X3,X4) != X1 ),
    inference(instantiation,[status(thm)],[c_163])).

cnf(c_846,plain,
    ( ~ r2_hidden(X0,k2_tarski(sK2,sK3))
    | r2_hidden(X1,k4_xboole_0(k2_tarski(sK2,sK3),sK4))
    | X1 != X0
    | k4_xboole_0(k2_tarski(sK2,sK3),sK4) != k2_tarski(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_583])).

cnf(c_848,plain,
    ( ~ r2_hidden(sK2,k2_tarski(sK2,sK3))
    | r2_hidden(sK2,k4_xboole_0(k2_tarski(sK2,sK3),sK4))
    | k4_xboole_0(k2_tarski(sK2,sK3),sK4) != k2_tarski(sK2,sK3)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_846])).

cnf(c_994,plain,
    ( r2_hidden(sK2,k2_tarski(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_2039,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(k2_tarski(sK2,sK3),sK4))
    | ~ r2_hidden(X0,sK4) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2041,plain,
    ( ~ r2_hidden(sK2,k4_xboole_0(k2_tarski(sK2,sK3),sK4))
    | ~ r2_hidden(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_2039])).

cnf(c_1091,plain,
    ( r2_hidden(X0,k4_xboole_0(k2_tarski(sK2,sK3),sK4))
    | ~ r2_hidden(sK3,k2_tarski(sK2,sK3))
    | X0 != sK3
    | k4_xboole_0(k2_tarski(sK2,sK3),sK4) != k2_tarski(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_846])).

cnf(c_2129,plain,
    ( ~ r2_hidden(sK3,k2_tarski(sK2,sK3))
    | r2_hidden(sK3,k4_xboole_0(k2_tarski(sK2,sK3),sK4))
    | k4_xboole_0(k2_tarski(sK2,sK3),sK4) != k2_tarski(sK2,sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1091])).

cnf(c_1146,plain,
    ( ~ r2_hidden(sK3,X0)
    | ~ r2_hidden(sK3,k4_xboole_0(X1,X0)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2639,plain,
    ( ~ r2_hidden(sK3,k4_xboole_0(k2_tarski(sK2,sK3),sK4))
    | ~ r2_hidden(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1146])).

cnf(c_3211,plain,
    ( ~ r2_hidden(sK2,X0)
    | r2_hidden(sK0(k2_tarski(sK2,sK3),sK4,k2_tarski(sK2,sK3)),X0)
    | r2_hidden(sK3,sK4)
    | sK0(k2_tarski(sK2,sK3),sK4,k2_tarski(sK2,sK3)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2881,c_14,c_13,c_19,c_22,c_691,c_703,c_848,c_994,c_2041,c_2129,c_2639])).

cnf(c_3212,plain,
    ( r2_hidden(sK0(k2_tarski(sK2,sK3),sK4,k2_tarski(sK2,sK3)),X0)
    | ~ r2_hidden(sK2,X0)
    | r2_hidden(sK3,sK4)
    | sK0(k2_tarski(sK2,sK3),sK4,k2_tarski(sK2,sK3)) = sK3 ),
    inference(renaming,[status(thm)],[c_3211])).

cnf(c_3217,plain,
    ( ~ r2_hidden(sK2,X0)
    | r2_hidden(sK0(k2_tarski(sK2,sK3),sK4,k2_tarski(sK2,sK3)),X0)
    | sK0(k2_tarski(sK2,sK3),sK4,k2_tarski(sK2,sK3)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3212,c_14,c_13,c_19,c_22,c_691,c_703,c_848,c_994,c_2041,c_2129,c_2639,c_2881])).

cnf(c_3218,plain,
    ( r2_hidden(sK0(k2_tarski(sK2,sK3),sK4,k2_tarski(sK2,sK3)),X0)
    | ~ r2_hidden(sK2,X0)
    | sK0(k2_tarski(sK2,sK3),sK4,k2_tarski(sK2,sK3)) = sK3 ),
    inference(renaming,[status(thm)],[c_3217])).

cnf(c_161,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_835,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_161,c_160])).

cnf(c_3372,plain,
    ( r2_hidden(sK0(k2_tarski(sK2,sK3),sK4,k2_tarski(sK2,sK3)),X0)
    | ~ r2_hidden(sK2,X0)
    | sK3 = sK0(k2_tarski(sK2,sK3),sK4,k2_tarski(sK2,sK3)) ),
    inference(resolution,[status(thm)],[c_3218,c_835])).

cnf(c_3431,plain,
    ( ~ r2_hidden(sK0(k2_tarski(sK2,sK3),sK4,k2_tarski(sK2,sK3)),X0)
    | r2_hidden(sK0(k2_tarski(sK2,sK3),sK4,k2_tarski(sK2,sK3)),X1)
    | ~ r2_hidden(sK2,X1)
    | r2_hidden(sK3,X0) ),
    inference(resolution,[status(thm)],[c_3372,c_1015])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X0)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(sK0(X0,X1,X2),X1)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_2588,plain,
    ( ~ r2_hidden(sK0(k2_tarski(sK2,sK3),sK4,k2_tarski(sK2,sK3)),k2_tarski(sK2,sK3))
    | r2_hidden(sK0(k2_tarski(sK2,sK3),sK4,k2_tarski(sK2,sK3)),sK4)
    | r2_hidden(sK2,sK4)
    | r2_hidden(sK3,sK4)
    | k4_xboole_0(k2_tarski(sK2,sK3),sK4) = k2_tarski(sK2,sK3) ),
    inference(resolution,[status(thm)],[c_0,c_1025])).

cnf(c_542,plain,
    ( ~ r2_hidden(sK0(k2_tarski(sK2,sK3),sK4,k2_tarski(sK2,sK3)),k2_tarski(sK2,sK3))
    | r2_hidden(sK0(k2_tarski(sK2,sK3),sK4,k2_tarski(sK2,sK3)),sK4)
    | k4_xboole_0(k2_tarski(sK2,sK3),sK4) = k2_tarski(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2902,plain,
    ( r2_hidden(sK0(k2_tarski(sK2,sK3),sK4,k2_tarski(sK2,sK3)),sK4)
    | k4_xboole_0(k2_tarski(sK2,sK3),sK4) = k2_tarski(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2588,c_14,c_13,c_12,c_19,c_22,c_542,c_691,c_703,c_848,c_994,c_1025,c_2041,c_2129,c_2639])).

cnf(c_2906,plain,
    ( r2_hidden(sK0(k2_tarski(sK2,sK3),sK4,k2_tarski(sK2,sK3)),sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2902,c_14,c_13,c_12,c_19,c_22,c_542,c_691,c_703,c_848,c_994,c_1025,c_2041,c_2129,c_2639])).

cnf(c_10203,plain,
    ( r2_hidden(sK0(k2_tarski(sK2,sK3),sK4,k2_tarski(sK2,sK3)),X0)
    | ~ r2_hidden(sK2,X0)
    | r2_hidden(sK3,sK4) ),
    inference(resolution,[status(thm)],[c_3431,c_2906])).

cnf(c_10219,plain,
    ( ~ r2_hidden(sK2,X0)
    | r2_hidden(sK0(k2_tarski(sK2,sK3),sK4,k2_tarski(sK2,sK3)),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10203,c_13,c_691,c_703,c_2129,c_2639])).

cnf(c_10220,plain,
    ( r2_hidden(sK0(k2_tarski(sK2,sK3),sK4,k2_tarski(sK2,sK3)),X0)
    | ~ r2_hidden(sK2,X0) ),
    inference(renaming,[status(thm)],[c_10219])).

cnf(c_10441,plain,
    ( ~ r2_hidden(sK0(k2_tarski(sK2,sK3),sK4,k2_tarski(sK2,sK3)),X0)
    | ~ r2_hidden(sK2,k4_xboole_0(X1,X0)) ),
    inference(resolution,[status(thm)],[c_10220,c_4])).

cnf(c_10486,plain,
    ( ~ r2_hidden(sK2,k4_xboole_0(X0,sK4)) ),
    inference(resolution,[status(thm)],[c_10441,c_2906])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_10696,plain,
    ( ~ r2_hidden(sK2,X0)
    | r2_hidden(sK2,sK4) ),
    inference(resolution,[status(thm)],[c_10486,c_3])).

cnf(c_4328,plain,
    ( ~ r2_hidden(sK2,X0)
    | r2_hidden(sK2,k4_xboole_0(X0,sK4))
    | r2_hidden(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2242,plain,
    ( ~ r2_hidden(sK0(k2_tarski(sK2,sK3),sK4,k2_tarski(sK2,sK3)),X0)
    | ~ r2_hidden(sK0(k2_tarski(sK2,sK3),sK4,k2_tarski(sK2,sK3)),k4_xboole_0(X1,X0)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_5906,plain,
    ( ~ r2_hidden(sK0(k2_tarski(sK2,sK3),sK4,k2_tarski(sK2,sK3)),k4_xboole_0(k2_tarski(sK2,sK3),sK4))
    | ~ r2_hidden(sK0(k2_tarski(sK2,sK3),sK4,k2_tarski(sK2,sK3)),sK4) ),
    inference(instantiation,[status(thm)],[c_2242])).

cnf(c_5908,plain,
    ( ~ r2_hidden(X0,k2_tarski(sK2,sK3))
    | r2_hidden(sK0(k2_tarski(sK2,sK3),sK4,k2_tarski(sK2,sK3)),k4_xboole_0(k2_tarski(sK2,sK3),sK4))
    | sK0(k2_tarski(sK2,sK3),sK4,k2_tarski(sK2,sK3)) != X0
    | k4_xboole_0(k2_tarski(sK2,sK3),sK4) != k2_tarski(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_846])).

cnf(c_5912,plain,
    ( r2_hidden(sK0(k2_tarski(sK2,sK3),sK4,k2_tarski(sK2,sK3)),k4_xboole_0(k2_tarski(sK2,sK3),sK4))
    | ~ r2_hidden(sK2,k2_tarski(sK2,sK3))
    | sK0(k2_tarski(sK2,sK3),sK4,k2_tarski(sK2,sK3)) != sK2
    | k4_xboole_0(k2_tarski(sK2,sK3),sK4) != k2_tarski(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_5908])).

cnf(c_10451,plain,
    ( ~ r2_hidden(sK2,k2_tarski(X0,X1))
    | sK0(k2_tarski(sK2,sK3),sK4,k2_tarski(sK2,sK3)) = X0
    | sK0(k2_tarski(sK2,sK3),sK4,k2_tarski(sK2,sK3)) = X1 ),
    inference(resolution,[status(thm)],[c_10220,c_11])).

cnf(c_10455,plain,
    ( ~ r2_hidden(sK2,k2_tarski(sK2,sK2))
    | sK0(k2_tarski(sK2,sK3),sK4,k2_tarski(sK2,sK3)) = sK2 ),
    inference(instantiation,[status(thm)],[c_10451])).

cnf(c_10701,plain,
    ( ~ r2_hidden(sK2,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10696,c_14,c_19,c_22,c_848,c_994,c_2041,c_4328,c_10486])).

cnf(c_10784,plain,
    ( $false ),
    inference(resolution,[status(thm)],[c_10701,c_9])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:23:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.92/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.92/0.97  
% 3.92/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.92/0.97  
% 3.92/0.97  ------  iProver source info
% 3.92/0.97  
% 3.92/0.97  git: date: 2020-06-30 10:37:57 +0100
% 3.92/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.92/0.97  git: non_committed_changes: false
% 3.92/0.97  git: last_make_outside_of_git: false
% 3.92/0.97  
% 3.92/0.97  ------ 
% 3.92/0.97  ------ Parsing...
% 3.92/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.92/0.97  
% 3.92/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.92/0.97  
% 3.92/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.92/0.97  
% 3.92/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.92/0.97  ------ Proving...
% 3.92/0.97  ------ Problem Properties 
% 3.92/0.97  
% 3.92/0.97  
% 3.92/0.97  clauses                                 15
% 3.92/0.97  conjectures                             3
% 3.92/0.97  EPR                                     0
% 3.92/0.97  Horn                                    8
% 3.92/0.97  unary                                   2
% 3.92/0.97  binary                                  4
% 3.92/0.97  lits                                    39
% 3.92/0.97  lits eq                                 15
% 3.92/0.97  fd_pure                                 0
% 3.92/0.97  fd_pseudo                               0
% 3.92/0.97  fd_cond                                 0
% 3.92/0.97  fd_pseudo_cond                          6
% 3.92/0.97  AC symbols                              0
% 3.92/0.97  
% 3.92/0.97  ------ Input Options Time Limit: Unbounded
% 3.92/0.97  
% 3.92/0.97  
% 3.92/0.97  ------ 
% 3.92/0.97  Current options:
% 3.92/0.97  ------ 
% 3.92/0.97  
% 3.92/0.97  
% 3.92/0.97  
% 3.92/0.97  
% 3.92/0.97  ------ Proving...
% 3.92/0.97  
% 3.92/0.97  
% 3.92/0.97  % SZS status Theorem for theBenchmark.p
% 3.92/0.97  
% 3.92/0.97   Resolution empty clause
% 3.92/0.97  
% 3.92/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 3.92/0.97  
% 3.92/0.97  fof(f1,axiom,(
% 3.92/0.97    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.92/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.92/0.97  
% 3.92/0.97  fof(f6,plain,(
% 3.92/0.97    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.92/0.97    inference(nnf_transformation,[],[f1])).
% 3.92/0.97  
% 3.92/0.97  fof(f7,plain,(
% 3.92/0.97    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.92/0.97    inference(flattening,[],[f6])).
% 3.92/0.97  
% 3.92/0.97  fof(f8,plain,(
% 3.92/0.97    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.92/0.97    inference(rectify,[],[f7])).
% 3.92/0.97  
% 3.92/0.97  fof(f9,plain,(
% 3.92/0.97    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.92/0.97    introduced(choice_axiom,[])).
% 3.92/0.97  
% 3.92/0.97  fof(f10,plain,(
% 3.92/0.97    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.92/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f9])).
% 3.92/0.97  
% 3.92/0.97  fof(f23,plain,(
% 3.92/0.97    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.92/0.97    inference(cnf_transformation,[],[f10])).
% 3.92/0.97  
% 3.92/0.97  fof(f3,conjecture,(
% 3.92/0.97    ! [X0,X1,X2] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 3.92/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.92/0.97  
% 3.92/0.97  fof(f4,negated_conjecture,(
% 3.92/0.97    ~! [X0,X1,X2] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 3.92/0.97    inference(negated_conjecture,[],[f3])).
% 3.92/0.97  
% 3.92/0.97  fof(f5,plain,(
% 3.92/0.97    ? [X0,X1,X2] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) <~> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 3.92/0.97    inference(ennf_transformation,[],[f4])).
% 3.92/0.97  
% 3.92/0.97  fof(f16,plain,(
% 3.92/0.97    ? [X0,X1,X2] : (((r2_hidden(X1,X2) | r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)))),
% 3.92/0.97    inference(nnf_transformation,[],[f5])).
% 3.92/0.97  
% 3.92/0.97  fof(f17,plain,(
% 3.92/0.97    ? [X0,X1,X2] : ((r2_hidden(X1,X2) | r2_hidden(X0,X2) | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)))),
% 3.92/0.97    inference(flattening,[],[f16])).
% 3.92/0.97  
% 3.92/0.97  fof(f18,plain,(
% 3.92/0.97    ? [X0,X1,X2] : ((r2_hidden(X1,X2) | r2_hidden(X0,X2) | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1))) => ((r2_hidden(sK3,sK4) | r2_hidden(sK2,sK4) | k4_xboole_0(k2_tarski(sK2,sK3),sK4) != k2_tarski(sK2,sK3)) & ((~r2_hidden(sK3,sK4) & ~r2_hidden(sK2,sK4)) | k4_xboole_0(k2_tarski(sK2,sK3),sK4) = k2_tarski(sK2,sK3)))),
% 3.92/0.97    introduced(choice_axiom,[])).
% 3.92/0.97  
% 3.92/0.97  fof(f19,plain,(
% 3.92/0.97    (r2_hidden(sK3,sK4) | r2_hidden(sK2,sK4) | k4_xboole_0(k2_tarski(sK2,sK3),sK4) != k2_tarski(sK2,sK3)) & ((~r2_hidden(sK3,sK4) & ~r2_hidden(sK2,sK4)) | k4_xboole_0(k2_tarski(sK2,sK3),sK4) = k2_tarski(sK2,sK3))),
% 3.92/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f17,f18])).
% 3.92/0.97  
% 3.92/0.97  fof(f34,plain,(
% 3.92/0.97    r2_hidden(sK3,sK4) | r2_hidden(sK2,sK4) | k4_xboole_0(k2_tarski(sK2,sK3),sK4) != k2_tarski(sK2,sK3)),
% 3.92/0.97    inference(cnf_transformation,[],[f19])).
% 3.92/0.97  
% 3.92/0.97  fof(f2,axiom,(
% 3.92/0.97    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 3.92/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.92/0.97  
% 3.92/0.97  fof(f11,plain,(
% 3.92/0.97    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 3.92/0.97    inference(nnf_transformation,[],[f2])).
% 3.92/0.97  
% 3.92/0.97  fof(f12,plain,(
% 3.92/0.97    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 3.92/0.97    inference(flattening,[],[f11])).
% 3.92/0.97  
% 3.92/0.97  fof(f13,plain,(
% 3.92/0.97    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 3.92/0.97    inference(rectify,[],[f12])).
% 3.92/0.97  
% 3.92/0.97  fof(f14,plain,(
% 3.92/0.97    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK1(X0,X1,X2) != X1 & sK1(X0,X1,X2) != X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | r2_hidden(sK1(X0,X1,X2),X2))))),
% 3.92/0.97    introduced(choice_axiom,[])).
% 3.92/0.97  
% 3.92/0.97  fof(f15,plain,(
% 3.92/0.97    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK1(X0,X1,X2) != X1 & sK1(X0,X1,X2) != X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 3.92/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f14])).
% 3.92/0.97  
% 3.92/0.97  fof(f26,plain,(
% 3.92/0.97    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 3.92/0.97    inference(cnf_transformation,[],[f15])).
% 3.92/0.97  
% 3.92/0.97  fof(f42,plain,(
% 3.92/0.97    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k2_tarski(X0,X1))) )),
% 3.92/0.97    inference(equality_resolution,[],[f26])).
% 3.92/0.97  
% 3.92/0.97  fof(f32,plain,(
% 3.92/0.97    ~r2_hidden(sK2,sK4) | k4_xboole_0(k2_tarski(sK2,sK3),sK4) = k2_tarski(sK2,sK3)),
% 3.92/0.97    inference(cnf_transformation,[],[f19])).
% 3.92/0.97  
% 3.92/0.97  fof(f33,plain,(
% 3.92/0.97    ~r2_hidden(sK3,sK4) | k4_xboole_0(k2_tarski(sK2,sK3),sK4) = k2_tarski(sK2,sK3)),
% 3.92/0.97    inference(cnf_transformation,[],[f19])).
% 3.92/0.97  
% 3.92/0.97  fof(f27,plain,(
% 3.92/0.97    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 3.92/0.97    inference(cnf_transformation,[],[f15])).
% 3.92/0.97  
% 3.92/0.97  fof(f40,plain,(
% 3.92/0.97    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_tarski(X4,X1) != X2) )),
% 3.92/0.97    inference(equality_resolution,[],[f27])).
% 3.92/0.97  
% 3.92/0.97  fof(f41,plain,(
% 3.92/0.97    ( ! [X4,X1] : (r2_hidden(X4,k2_tarski(X4,X1))) )),
% 3.92/0.97    inference(equality_resolution,[],[f40])).
% 3.92/0.97  
% 3.92/0.97  fof(f28,plain,(
% 3.92/0.97    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 3.92/0.97    inference(cnf_transformation,[],[f15])).
% 3.92/0.97  
% 3.92/0.97  fof(f38,plain,(
% 3.92/0.97    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_tarski(X0,X4) != X2) )),
% 3.92/0.97    inference(equality_resolution,[],[f28])).
% 3.92/0.97  
% 3.92/0.97  fof(f39,plain,(
% 3.92/0.97    ( ! [X4,X0] : (r2_hidden(X4,k2_tarski(X0,X4))) )),
% 3.92/0.97    inference(equality_resolution,[],[f38])).
% 3.92/0.97  
% 3.92/0.97  fof(f21,plain,(
% 3.92/0.97    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.92/0.97    inference(cnf_transformation,[],[f10])).
% 3.92/0.97  
% 3.92/0.97  fof(f36,plain,(
% 3.92/0.97    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 3.92/0.97    inference(equality_resolution,[],[f21])).
% 3.92/0.97  
% 3.92/0.97  fof(f25,plain,(
% 3.92/0.97    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.92/0.97    inference(cnf_transformation,[],[f10])).
% 3.92/0.97  
% 3.92/0.97  fof(f22,plain,(
% 3.92/0.97    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 3.92/0.97    inference(cnf_transformation,[],[f10])).
% 3.92/0.97  
% 3.92/0.97  fof(f35,plain,(
% 3.92/0.97    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 3.92/0.97    inference(equality_resolution,[],[f22])).
% 3.92/0.97  
% 3.92/0.97  cnf(c_163,plain,
% 3.92/0.97      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.92/0.97      theory(equality) ).
% 3.92/0.97  
% 3.92/0.97  cnf(c_160,plain,( X0 = X0 ),theory(equality) ).
% 3.92/0.97  
% 3.92/0.97  cnf(c_1015,plain,
% 3.92/0.97      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X1) | X2 != X0 ),
% 3.92/0.97      inference(resolution,[status(thm)],[c_163,c_160]) ).
% 3.92/0.97  
% 3.92/0.97  cnf(c_2,plain,
% 3.92/0.97      ( r2_hidden(sK0(X0,X1,X2),X0)
% 3.92/0.97      | r2_hidden(sK0(X0,X1,X2),X2)
% 3.92/0.97      | k4_xboole_0(X0,X1) = X2 ),
% 3.92/0.97      inference(cnf_transformation,[],[f23]) ).
% 3.92/0.97  
% 3.92/0.97  cnf(c_12,negated_conjecture,
% 3.92/0.97      ( r2_hidden(sK2,sK4)
% 3.92/0.97      | r2_hidden(sK3,sK4)
% 3.92/0.97      | k4_xboole_0(k2_tarski(sK2,sK3),sK4) != k2_tarski(sK2,sK3) ),
% 3.92/0.97      inference(cnf_transformation,[],[f34]) ).
% 3.92/0.97  
% 3.92/0.97  cnf(c_1025,plain,
% 3.92/0.97      ( r2_hidden(sK0(k2_tarski(sK2,sK3),sK4,k2_tarski(sK2,sK3)),k2_tarski(sK2,sK3))
% 3.92/0.97      | r2_hidden(sK2,sK4)
% 3.92/0.97      | r2_hidden(sK3,sK4) ),
% 3.92/0.97      inference(resolution,[status(thm)],[c_2,c_12]) ).
% 3.92/0.97  
% 3.92/0.97  cnf(c_11,plain,
% 3.92/0.97      ( ~ r2_hidden(X0,k2_tarski(X1,X2)) | X0 = X1 | X0 = X2 ),
% 3.92/0.97      inference(cnf_transformation,[],[f42]) ).
% 3.92/0.97  
% 3.92/0.97  cnf(c_1143,plain,
% 3.92/0.97      ( r2_hidden(sK2,sK4)
% 3.92/0.97      | r2_hidden(sK3,sK4)
% 3.92/0.97      | sK0(k2_tarski(sK2,sK3),sK4,k2_tarski(sK2,sK3)) = sK2
% 3.92/0.97      | sK0(k2_tarski(sK2,sK3),sK4,k2_tarski(sK2,sK3)) = sK3 ),
% 3.92/0.97      inference(resolution,[status(thm)],[c_1025,c_11]) ).
% 3.92/0.97  
% 3.92/0.97  cnf(c_2881,plain,
% 3.92/0.97      ( r2_hidden(sK0(k2_tarski(sK2,sK3),sK4,k2_tarski(sK2,sK3)),X0)
% 3.92/0.97      | ~ r2_hidden(sK2,X0)
% 3.92/0.97      | r2_hidden(sK2,sK4)
% 3.92/0.97      | r2_hidden(sK3,sK4)
% 3.92/0.97      | sK0(k2_tarski(sK2,sK3),sK4,k2_tarski(sK2,sK3)) = sK3 ),
% 3.92/0.97      inference(resolution,[status(thm)],[c_1015,c_1143]) ).
% 3.92/0.97  
% 3.92/0.97  cnf(c_14,negated_conjecture,
% 3.92/0.97      ( ~ r2_hidden(sK2,sK4)
% 3.92/0.97      | k4_xboole_0(k2_tarski(sK2,sK3),sK4) = k2_tarski(sK2,sK3) ),
% 3.92/0.97      inference(cnf_transformation,[],[f32]) ).
% 3.92/0.97  
% 3.92/0.97  cnf(c_13,negated_conjecture,
% 3.92/0.97      ( ~ r2_hidden(sK3,sK4)
% 3.92/0.97      | k4_xboole_0(k2_tarski(sK2,sK3),sK4) = k2_tarski(sK2,sK3) ),
% 3.92/0.97      inference(cnf_transformation,[],[f33]) ).
% 3.92/0.97  
% 3.92/0.97  cnf(c_19,plain,
% 3.92/0.97      ( ~ r2_hidden(sK2,k2_tarski(sK2,sK2)) | sK2 = sK2 ),
% 3.92/0.97      inference(instantiation,[status(thm)],[c_11]) ).
% 3.92/0.97  
% 3.92/0.97  cnf(c_10,plain,
% 3.92/0.97      ( r2_hidden(X0,k2_tarski(X0,X1)) ),
% 3.92/0.97      inference(cnf_transformation,[],[f41]) ).
% 3.92/0.97  
% 3.92/0.97  cnf(c_22,plain,
% 3.92/0.97      ( r2_hidden(sK2,k2_tarski(sK2,sK2)) ),
% 3.92/0.97      inference(instantiation,[status(thm)],[c_10]) ).
% 3.92/0.97  
% 3.92/0.97  cnf(c_9,plain,
% 3.92/0.97      ( r2_hidden(X0,k2_tarski(X1,X0)) ),
% 3.92/0.97      inference(cnf_transformation,[],[f39]) ).
% 3.92/0.97  
% 3.92/0.97  cnf(c_689,plain,
% 3.92/0.97      ( r2_hidden(sK3,k2_tarski(X0,sK3)) ),
% 3.92/0.97      inference(instantiation,[status(thm)],[c_9]) ).
% 3.92/0.97  
% 3.92/0.97  cnf(c_691,plain,
% 3.92/0.97      ( r2_hidden(sK3,k2_tarski(sK2,sK3)) ),
% 3.92/0.97      inference(instantiation,[status(thm)],[c_689]) ).
% 3.92/0.97  
% 3.92/0.97  cnf(c_703,plain,
% 3.92/0.97      ( sK3 = sK3 ),
% 3.92/0.97      inference(instantiation,[status(thm)],[c_160]) ).
% 3.92/0.97  
% 3.92/0.97  cnf(c_583,plain,
% 3.92/0.97      ( ~ r2_hidden(X0,X1)
% 3.92/0.97      | r2_hidden(X2,k4_xboole_0(X3,X4))
% 3.92/0.97      | X2 != X0
% 3.92/0.97      | k4_xboole_0(X3,X4) != X1 ),
% 3.92/0.97      inference(instantiation,[status(thm)],[c_163]) ).
% 3.92/0.97  
% 3.92/0.97  cnf(c_846,plain,
% 3.92/0.97      ( ~ r2_hidden(X0,k2_tarski(sK2,sK3))
% 3.92/0.97      | r2_hidden(X1,k4_xboole_0(k2_tarski(sK2,sK3),sK4))
% 3.92/0.97      | X1 != X0
% 3.92/0.97      | k4_xboole_0(k2_tarski(sK2,sK3),sK4) != k2_tarski(sK2,sK3) ),
% 3.92/0.97      inference(instantiation,[status(thm)],[c_583]) ).
% 3.92/0.97  
% 3.92/0.97  cnf(c_848,plain,
% 3.92/0.97      ( ~ r2_hidden(sK2,k2_tarski(sK2,sK3))
% 3.92/0.97      | r2_hidden(sK2,k4_xboole_0(k2_tarski(sK2,sK3),sK4))
% 3.92/0.97      | k4_xboole_0(k2_tarski(sK2,sK3),sK4) != k2_tarski(sK2,sK3)
% 3.92/0.97      | sK2 != sK2 ),
% 3.92/0.97      inference(instantiation,[status(thm)],[c_846]) ).
% 3.92/0.97  
% 3.92/0.97  cnf(c_994,plain,
% 3.92/0.97      ( r2_hidden(sK2,k2_tarski(sK2,sK3)) ),
% 3.92/0.97      inference(instantiation,[status(thm)],[c_10]) ).
% 3.92/0.97  
% 3.92/0.97  cnf(c_4,plain,
% 3.92/0.97      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 3.92/0.97      inference(cnf_transformation,[],[f36]) ).
% 3.92/0.97  
% 3.92/0.97  cnf(c_2039,plain,
% 3.92/0.97      ( ~ r2_hidden(X0,k4_xboole_0(k2_tarski(sK2,sK3),sK4))
% 3.92/0.97      | ~ r2_hidden(X0,sK4) ),
% 3.92/0.97      inference(instantiation,[status(thm)],[c_4]) ).
% 3.92/0.97  
% 3.92/0.97  cnf(c_2041,plain,
% 3.92/0.97      ( ~ r2_hidden(sK2,k4_xboole_0(k2_tarski(sK2,sK3),sK4))
% 3.92/0.97      | ~ r2_hidden(sK2,sK4) ),
% 3.92/0.97      inference(instantiation,[status(thm)],[c_2039]) ).
% 3.92/0.97  
% 3.92/0.97  cnf(c_1091,plain,
% 3.92/0.97      ( r2_hidden(X0,k4_xboole_0(k2_tarski(sK2,sK3),sK4))
% 3.92/0.97      | ~ r2_hidden(sK3,k2_tarski(sK2,sK3))
% 3.92/0.97      | X0 != sK3
% 3.92/0.97      | k4_xboole_0(k2_tarski(sK2,sK3),sK4) != k2_tarski(sK2,sK3) ),
% 3.92/0.97      inference(instantiation,[status(thm)],[c_846]) ).
% 3.92/0.97  
% 3.92/0.97  cnf(c_2129,plain,
% 3.92/0.97      ( ~ r2_hidden(sK3,k2_tarski(sK2,sK3))
% 3.92/0.97      | r2_hidden(sK3,k4_xboole_0(k2_tarski(sK2,sK3),sK4))
% 3.92/0.97      | k4_xboole_0(k2_tarski(sK2,sK3),sK4) != k2_tarski(sK2,sK3)
% 3.92/0.97      | sK3 != sK3 ),
% 3.92/0.97      inference(instantiation,[status(thm)],[c_1091]) ).
% 3.92/0.97  
% 3.92/0.97  cnf(c_1146,plain,
% 3.92/0.97      ( ~ r2_hidden(sK3,X0) | ~ r2_hidden(sK3,k4_xboole_0(X1,X0)) ),
% 3.92/0.97      inference(instantiation,[status(thm)],[c_4]) ).
% 3.92/0.97  
% 3.92/0.97  cnf(c_2639,plain,
% 3.92/0.97      ( ~ r2_hidden(sK3,k4_xboole_0(k2_tarski(sK2,sK3),sK4))
% 3.92/0.97      | ~ r2_hidden(sK3,sK4) ),
% 3.92/0.97      inference(instantiation,[status(thm)],[c_1146]) ).
% 3.92/0.97  
% 3.92/0.97  cnf(c_3211,plain,
% 3.92/0.97      ( ~ r2_hidden(sK2,X0)
% 3.92/0.97      | r2_hidden(sK0(k2_tarski(sK2,sK3),sK4,k2_tarski(sK2,sK3)),X0)
% 3.92/0.97      | r2_hidden(sK3,sK4)
% 3.92/0.97      | sK0(k2_tarski(sK2,sK3),sK4,k2_tarski(sK2,sK3)) = sK3 ),
% 3.92/0.97      inference(global_propositional_subsumption,
% 3.92/0.97                [status(thm)],
% 3.92/0.97                [c_2881,c_14,c_13,c_19,c_22,c_691,c_703,c_848,c_994,c_2041,
% 3.92/0.97                 c_2129,c_2639]) ).
% 3.92/0.97  
% 3.92/0.97  cnf(c_3212,plain,
% 3.92/0.97      ( r2_hidden(sK0(k2_tarski(sK2,sK3),sK4,k2_tarski(sK2,sK3)),X0)
% 3.92/0.97      | ~ r2_hidden(sK2,X0)
% 3.92/0.97      | r2_hidden(sK3,sK4)
% 3.92/0.97      | sK0(k2_tarski(sK2,sK3),sK4,k2_tarski(sK2,sK3)) = sK3 ),
% 3.92/0.97      inference(renaming,[status(thm)],[c_3211]) ).
% 3.92/0.97  
% 3.92/0.97  cnf(c_3217,plain,
% 3.92/0.97      ( ~ r2_hidden(sK2,X0)
% 3.92/0.97      | r2_hidden(sK0(k2_tarski(sK2,sK3),sK4,k2_tarski(sK2,sK3)),X0)
% 3.92/0.97      | sK0(k2_tarski(sK2,sK3),sK4,k2_tarski(sK2,sK3)) = sK3 ),
% 3.92/0.97      inference(global_propositional_subsumption,
% 3.92/0.97                [status(thm)],
% 3.92/0.97                [c_3212,c_14,c_13,c_19,c_22,c_691,c_703,c_848,c_994,c_2041,
% 3.92/0.97                 c_2129,c_2639,c_2881]) ).
% 3.92/0.97  
% 3.92/0.97  cnf(c_3218,plain,
% 3.92/0.97      ( r2_hidden(sK0(k2_tarski(sK2,sK3),sK4,k2_tarski(sK2,sK3)),X0)
% 3.92/0.97      | ~ r2_hidden(sK2,X0)
% 3.92/0.97      | sK0(k2_tarski(sK2,sK3),sK4,k2_tarski(sK2,sK3)) = sK3 ),
% 3.92/0.97      inference(renaming,[status(thm)],[c_3217]) ).
% 3.92/0.97  
% 3.92/0.97  cnf(c_161,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.92/0.97  
% 3.92/0.97  cnf(c_835,plain,
% 3.92/0.97      ( X0 != X1 | X1 = X0 ),
% 3.92/0.97      inference(resolution,[status(thm)],[c_161,c_160]) ).
% 3.92/0.97  
% 3.92/0.97  cnf(c_3372,plain,
% 3.92/0.97      ( r2_hidden(sK0(k2_tarski(sK2,sK3),sK4,k2_tarski(sK2,sK3)),X0)
% 3.92/0.97      | ~ r2_hidden(sK2,X0)
% 3.92/0.97      | sK3 = sK0(k2_tarski(sK2,sK3),sK4,k2_tarski(sK2,sK3)) ),
% 3.92/0.97      inference(resolution,[status(thm)],[c_3218,c_835]) ).
% 3.92/0.97  
% 3.92/0.97  cnf(c_3431,plain,
% 3.92/0.97      ( ~ r2_hidden(sK0(k2_tarski(sK2,sK3),sK4,k2_tarski(sK2,sK3)),X0)
% 3.92/0.97      | r2_hidden(sK0(k2_tarski(sK2,sK3),sK4,k2_tarski(sK2,sK3)),X1)
% 3.92/0.97      | ~ r2_hidden(sK2,X1)
% 3.92/0.97      | r2_hidden(sK3,X0) ),
% 3.92/0.97      inference(resolution,[status(thm)],[c_3372,c_1015]) ).
% 3.92/0.97  
% 3.92/0.97  cnf(c_0,plain,
% 3.92/0.97      ( ~ r2_hidden(sK0(X0,X1,X2),X0)
% 3.92/0.97      | ~ r2_hidden(sK0(X0,X1,X2),X2)
% 3.92/0.97      | r2_hidden(sK0(X0,X1,X2),X1)
% 3.92/0.97      | k4_xboole_0(X0,X1) = X2 ),
% 3.92/0.97      inference(cnf_transformation,[],[f25]) ).
% 3.92/0.97  
% 3.92/0.97  cnf(c_2588,plain,
% 3.92/0.97      ( ~ r2_hidden(sK0(k2_tarski(sK2,sK3),sK4,k2_tarski(sK2,sK3)),k2_tarski(sK2,sK3))
% 3.92/0.97      | r2_hidden(sK0(k2_tarski(sK2,sK3),sK4,k2_tarski(sK2,sK3)),sK4)
% 3.92/0.97      | r2_hidden(sK2,sK4)
% 3.92/0.97      | r2_hidden(sK3,sK4)
% 3.92/0.97      | k4_xboole_0(k2_tarski(sK2,sK3),sK4) = k2_tarski(sK2,sK3) ),
% 3.92/0.97      inference(resolution,[status(thm)],[c_0,c_1025]) ).
% 3.92/0.97  
% 3.92/0.97  cnf(c_542,plain,
% 3.92/0.97      ( ~ r2_hidden(sK0(k2_tarski(sK2,sK3),sK4,k2_tarski(sK2,sK3)),k2_tarski(sK2,sK3))
% 3.92/0.97      | r2_hidden(sK0(k2_tarski(sK2,sK3),sK4,k2_tarski(sK2,sK3)),sK4)
% 3.92/0.97      | k4_xboole_0(k2_tarski(sK2,sK3),sK4) = k2_tarski(sK2,sK3) ),
% 3.92/0.97      inference(instantiation,[status(thm)],[c_0]) ).
% 3.92/0.97  
% 3.92/0.97  cnf(c_2902,plain,
% 3.92/0.97      ( r2_hidden(sK0(k2_tarski(sK2,sK3),sK4,k2_tarski(sK2,sK3)),sK4)
% 3.92/0.97      | k4_xboole_0(k2_tarski(sK2,sK3),sK4) = k2_tarski(sK2,sK3) ),
% 3.92/0.97      inference(global_propositional_subsumption,
% 3.92/0.97                [status(thm)],
% 3.92/0.97                [c_2588,c_14,c_13,c_12,c_19,c_22,c_542,c_691,c_703,c_848,
% 3.92/0.97                 c_994,c_1025,c_2041,c_2129,c_2639]) ).
% 3.92/0.97  
% 3.92/0.97  cnf(c_2906,plain,
% 3.92/0.97      ( r2_hidden(sK0(k2_tarski(sK2,sK3),sK4,k2_tarski(sK2,sK3)),sK4) ),
% 3.92/0.97      inference(global_propositional_subsumption,
% 3.92/0.97                [status(thm)],
% 3.92/0.97                [c_2902,c_14,c_13,c_12,c_19,c_22,c_542,c_691,c_703,c_848,
% 3.92/0.97                 c_994,c_1025,c_2041,c_2129,c_2639]) ).
% 3.92/0.97  
% 3.92/0.97  cnf(c_10203,plain,
% 3.92/0.97      ( r2_hidden(sK0(k2_tarski(sK2,sK3),sK4,k2_tarski(sK2,sK3)),X0)
% 3.92/0.97      | ~ r2_hidden(sK2,X0)
% 3.92/0.97      | r2_hidden(sK3,sK4) ),
% 3.92/0.97      inference(resolution,[status(thm)],[c_3431,c_2906]) ).
% 3.92/0.97  
% 3.92/0.97  cnf(c_10219,plain,
% 3.92/0.97      ( ~ r2_hidden(sK2,X0)
% 3.92/0.97      | r2_hidden(sK0(k2_tarski(sK2,sK3),sK4,k2_tarski(sK2,sK3)),X0) ),
% 3.92/0.97      inference(global_propositional_subsumption,
% 3.92/0.97                [status(thm)],
% 3.92/0.97                [c_10203,c_13,c_691,c_703,c_2129,c_2639]) ).
% 3.92/0.97  
% 3.92/0.97  cnf(c_10220,plain,
% 3.92/0.97      ( r2_hidden(sK0(k2_tarski(sK2,sK3),sK4,k2_tarski(sK2,sK3)),X0)
% 3.92/0.97      | ~ r2_hidden(sK2,X0) ),
% 3.92/0.97      inference(renaming,[status(thm)],[c_10219]) ).
% 3.92/0.97  
% 3.92/0.97  cnf(c_10441,plain,
% 3.92/0.97      ( ~ r2_hidden(sK0(k2_tarski(sK2,sK3),sK4,k2_tarski(sK2,sK3)),X0)
% 3.92/0.97      | ~ r2_hidden(sK2,k4_xboole_0(X1,X0)) ),
% 3.92/0.97      inference(resolution,[status(thm)],[c_10220,c_4]) ).
% 3.92/0.97  
% 3.92/0.97  cnf(c_10486,plain,
% 3.92/0.97      ( ~ r2_hidden(sK2,k4_xboole_0(X0,sK4)) ),
% 3.92/0.97      inference(resolution,[status(thm)],[c_10441,c_2906]) ).
% 3.92/0.97  
% 3.92/0.97  cnf(c_3,plain,
% 3.92/0.97      ( ~ r2_hidden(X0,X1)
% 3.92/0.97      | r2_hidden(X0,X2)
% 3.92/0.97      | r2_hidden(X0,k4_xboole_0(X1,X2)) ),
% 3.92/0.97      inference(cnf_transformation,[],[f35]) ).
% 3.92/0.97  
% 3.92/0.97  cnf(c_10696,plain,
% 3.92/0.97      ( ~ r2_hidden(sK2,X0) | r2_hidden(sK2,sK4) ),
% 3.92/0.97      inference(resolution,[status(thm)],[c_10486,c_3]) ).
% 3.92/0.97  
% 3.92/0.97  cnf(c_4328,plain,
% 3.92/0.97      ( ~ r2_hidden(sK2,X0)
% 3.92/0.97      | r2_hidden(sK2,k4_xboole_0(X0,sK4))
% 3.92/0.97      | r2_hidden(sK2,sK4) ),
% 3.92/0.97      inference(instantiation,[status(thm)],[c_3]) ).
% 3.92/0.97  
% 3.92/0.97  cnf(c_2242,plain,
% 3.92/0.97      ( ~ r2_hidden(sK0(k2_tarski(sK2,sK3),sK4,k2_tarski(sK2,sK3)),X0)
% 3.92/0.97      | ~ r2_hidden(sK0(k2_tarski(sK2,sK3),sK4,k2_tarski(sK2,sK3)),k4_xboole_0(X1,X0)) ),
% 3.92/0.97      inference(instantiation,[status(thm)],[c_4]) ).
% 3.92/0.97  
% 3.92/0.97  cnf(c_5906,plain,
% 3.92/0.97      ( ~ r2_hidden(sK0(k2_tarski(sK2,sK3),sK4,k2_tarski(sK2,sK3)),k4_xboole_0(k2_tarski(sK2,sK3),sK4))
% 3.92/0.97      | ~ r2_hidden(sK0(k2_tarski(sK2,sK3),sK4,k2_tarski(sK2,sK3)),sK4) ),
% 3.92/0.97      inference(instantiation,[status(thm)],[c_2242]) ).
% 3.92/0.97  
% 3.92/0.97  cnf(c_5908,plain,
% 3.92/0.97      ( ~ r2_hidden(X0,k2_tarski(sK2,sK3))
% 3.92/0.97      | r2_hidden(sK0(k2_tarski(sK2,sK3),sK4,k2_tarski(sK2,sK3)),k4_xboole_0(k2_tarski(sK2,sK3),sK4))
% 3.92/0.97      | sK0(k2_tarski(sK2,sK3),sK4,k2_tarski(sK2,sK3)) != X0
% 3.92/0.97      | k4_xboole_0(k2_tarski(sK2,sK3),sK4) != k2_tarski(sK2,sK3) ),
% 3.92/0.97      inference(instantiation,[status(thm)],[c_846]) ).
% 3.92/0.97  
% 3.92/0.97  cnf(c_5912,plain,
% 3.92/0.97      ( r2_hidden(sK0(k2_tarski(sK2,sK3),sK4,k2_tarski(sK2,sK3)),k4_xboole_0(k2_tarski(sK2,sK3),sK4))
% 3.92/0.97      | ~ r2_hidden(sK2,k2_tarski(sK2,sK3))
% 3.92/0.97      | sK0(k2_tarski(sK2,sK3),sK4,k2_tarski(sK2,sK3)) != sK2
% 3.92/0.97      | k4_xboole_0(k2_tarski(sK2,sK3),sK4) != k2_tarski(sK2,sK3) ),
% 3.92/0.97      inference(instantiation,[status(thm)],[c_5908]) ).
% 3.92/0.97  
% 3.92/0.97  cnf(c_10451,plain,
% 3.92/0.97      ( ~ r2_hidden(sK2,k2_tarski(X0,X1))
% 3.92/0.97      | sK0(k2_tarski(sK2,sK3),sK4,k2_tarski(sK2,sK3)) = X0
% 3.92/0.97      | sK0(k2_tarski(sK2,sK3),sK4,k2_tarski(sK2,sK3)) = X1 ),
% 3.92/0.97      inference(resolution,[status(thm)],[c_10220,c_11]) ).
% 3.92/0.97  
% 3.92/0.97  cnf(c_10455,plain,
% 3.92/0.97      ( ~ r2_hidden(sK2,k2_tarski(sK2,sK2))
% 3.92/0.97      | sK0(k2_tarski(sK2,sK3),sK4,k2_tarski(sK2,sK3)) = sK2 ),
% 3.92/0.97      inference(instantiation,[status(thm)],[c_10451]) ).
% 3.92/0.97  
% 3.92/0.97  cnf(c_10701,plain,
% 3.92/0.97      ( ~ r2_hidden(sK2,X0) ),
% 3.92/0.97      inference(global_propositional_subsumption,
% 3.92/0.97                [status(thm)],
% 3.92/0.97                [c_10696,c_14,c_19,c_22,c_848,c_994,c_2041,c_4328,c_10486]) ).
% 3.92/0.97  
% 3.92/0.97  cnf(c_10784,plain,
% 3.92/0.97      ( $false ),
% 3.92/0.97      inference(resolution,[status(thm)],[c_10701,c_9]) ).
% 3.92/0.97  
% 3.92/0.97  
% 3.92/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 3.92/0.97  
% 3.92/0.97  ------                               Statistics
% 3.92/0.97  
% 3.92/0.97  ------ Selected
% 3.92/0.97  
% 3.92/0.97  total_time:                             0.36
% 3.92/0.97  
%------------------------------------------------------------------------------
