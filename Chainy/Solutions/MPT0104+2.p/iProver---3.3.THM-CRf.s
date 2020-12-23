%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0104+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:21 EST 2020

% Result     : Theorem 31.88s
% Output     : CNFRefutation 31.88s
% Verified   : 
% Statistics : Number of formulae       :   54 (  99 expanded)
%              Number of clauses        :   23 (  26 expanded)
%              Number of leaves         :    7 (  20 expanded)
%              Depth                    :   11
%              Number of atoms          :  217 ( 450 expanded)
%              Number of equality atoms :   10 (  20 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f269,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f270,plain,(
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
    inference(flattening,[],[f269])).

fof(f271,plain,(
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
    inference(rectify,[],[f270])).

fof(f272,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f273,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f271,f272])).

fof(f332,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f273])).

fof(f625,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f332])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f161,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f281,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f161])).

fof(f351,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f281])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f158,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f255,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f158])).

fof(f256,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f255])).

fof(f257,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f258,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f256,f257])).

fof(f315,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f258])).

fof(f352,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f281])).

fof(f317,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f258])).

fof(f316,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f258])).

fof(f148,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k4_xboole_0(X1,X0),X2)
        & r1_tarski(k4_xboole_0(X0,X1),X2) )
     => r1_tarski(k5_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f149,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_tarski(k4_xboole_0(X1,X0),X2)
          & r1_tarski(k4_xboole_0(X0,X1),X2) )
       => r1_tarski(k5_xboole_0(X0,X1),X2) ) ),
    inference(negated_conjecture,[],[f148])).

fof(f248,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k5_xboole_0(X0,X1),X2)
      & r1_tarski(k4_xboole_0(X1,X0),X2)
      & r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f149])).

fof(f249,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k5_xboole_0(X0,X1),X2)
      & r1_tarski(k4_xboole_0(X1,X0),X2)
      & r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(flattening,[],[f248])).

fof(f305,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k5_xboole_0(X0,X1),X2)
        & r1_tarski(k4_xboole_0(X1,X0),X2)
        & r1_tarski(k4_xboole_0(X0,X1),X2) )
   => ( ~ r1_tarski(k5_xboole_0(sK15,sK16),sK17)
      & r1_tarski(k4_xboole_0(sK16,sK15),sK17)
      & r1_tarski(k4_xboole_0(sK15,sK16),sK17) ) ),
    introduced(choice_axiom,[])).

fof(f306,plain,
    ( ~ r1_tarski(k5_xboole_0(sK15,sK16),sK17)
    & r1_tarski(k4_xboole_0(sK16,sK15),sK17)
    & r1_tarski(k4_xboole_0(sK15,sK16),sK17) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15,sK16,sK17])],[f249,f305])).

fof(f498,plain,(
    ~ r1_tarski(k5_xboole_0(sK15,sK16),sK17) ),
    inference(cnf_transformation,[],[f306])).

fof(f497,plain,(
    r1_tarski(k4_xboole_0(sK16,sK15),sK17) ),
    inference(cnf_transformation,[],[f306])).

fof(f496,plain,(
    r1_tarski(k4_xboole_0(sK15,sK16),sK17) ),
    inference(cnf_transformation,[],[f306])).

cnf(c_26,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f625])).

cnf(c_8033,plain,
    ( ~ r2_hidden(sK1(k5_xboole_0(sK15,sK16),sK17),X0)
    | r2_hidden(sK1(k5_xboole_0(sK15,sK16),sK17),X1)
    | r2_hidden(sK1(k5_xboole_0(sK15,sK16),sK17),k4_xboole_0(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_61242,plain,
    ( r2_hidden(sK1(k5_xboole_0(sK15,sK16),sK17),X0)
    | r2_hidden(sK1(k5_xboole_0(sK15,sK16),sK17),k4_xboole_0(sK16,X0))
    | ~ r2_hidden(sK1(k5_xboole_0(sK15,sK16),sK17),sK16) ),
    inference(instantiation,[status(thm)],[c_8033])).

cnf(c_143346,plain,
    ( r2_hidden(sK1(k5_xboole_0(sK15,sK16),sK17),k4_xboole_0(sK16,sK15))
    | ~ r2_hidden(sK1(k5_xboole_0(sK15,sK16),sK17),sK16)
    | r2_hidden(sK1(k5_xboole_0(sK15,sK16),sK17),sK15) ),
    inference(instantiation,[status(thm)],[c_61242])).

cnf(c_7179,plain,
    ( ~ r2_hidden(sK1(k5_xboole_0(sK15,sK16),sK17),X0)
    | r2_hidden(sK1(k5_xboole_0(sK15,sK16),sK17),k4_xboole_0(X0,sK16))
    | r2_hidden(sK1(k5_xboole_0(sK15,sK16),sK17),sK16) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_78421,plain,
    ( r2_hidden(sK1(k5_xboole_0(sK15,sK16),sK17),k4_xboole_0(sK15,sK16))
    | r2_hidden(sK1(k5_xboole_0(sK15,sK16),sK17),sK16)
    | ~ r2_hidden(sK1(k5_xboole_0(sK15,sK16),sK17),sK15) ),
    inference(instantiation,[status(thm)],[c_7179])).

cnf(c_46,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f351])).

cnf(c_8005,plain,
    ( r2_hidden(sK1(k5_xboole_0(sK15,sK16),sK17),X0)
    | r2_hidden(sK1(k5_xboole_0(sK15,sK16),sK17),X1)
    | ~ r2_hidden(sK1(k5_xboole_0(sK15,sK16),sK17),k5_xboole_0(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_46])).

cnf(c_60560,plain,
    ( ~ r2_hidden(sK1(k5_xboole_0(sK15,sK16),sK17),k5_xboole_0(sK15,sK16))
    | r2_hidden(sK1(k5_xboole_0(sK15,sK16),sK17),sK16)
    | r2_hidden(sK1(k5_xboole_0(sK15,sK16),sK17),sK15) ),
    inference(instantiation,[status(thm)],[c_8005])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f315])).

cnf(c_5989,plain,
    ( ~ r1_tarski(X0,sK17)
    | ~ r2_hidden(sK1(k5_xboole_0(sK15,sK16),sK17),X0)
    | r2_hidden(sK1(k5_xboole_0(sK15,sK16),sK17),sK17) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_7952,plain,
    ( ~ r1_tarski(k4_xboole_0(sK15,sK16),sK17)
    | ~ r2_hidden(sK1(k5_xboole_0(sK15,sK16),sK17),k4_xboole_0(sK15,sK16))
    | r2_hidden(sK1(k5_xboole_0(sK15,sK16),sK17),sK17) ),
    inference(instantiation,[status(thm)],[c_5989])).

cnf(c_7949,plain,
    ( ~ r1_tarski(k4_xboole_0(sK16,sK15),sK17)
    | ~ r2_hidden(sK1(k5_xboole_0(sK15,sK16),sK17),k4_xboole_0(sK16,sK15))
    | r2_hidden(sK1(k5_xboole_0(sK15,sK16),sK17),sK17) ),
    inference(instantiation,[status(thm)],[c_5989])).

cnf(c_45,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f352])).

cnf(c_6034,plain,
    ( ~ r2_hidden(sK1(k5_xboole_0(sK15,sK16),sK17),k5_xboole_0(sK15,sK16))
    | ~ r2_hidden(sK1(k5_xboole_0(sK15,sK16),sK17),sK16)
    | ~ r2_hidden(sK1(k5_xboole_0(sK15,sK16),sK17),sK15) ),
    inference(instantiation,[status(thm)],[c_45])).

cnf(c_8,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f317])).

cnf(c_5861,plain,
    ( r1_tarski(k5_xboole_0(sK15,sK16),sK17)
    | ~ r2_hidden(sK1(k5_xboole_0(sK15,sK16),sK17),sK17) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_9,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f316])).

cnf(c_5862,plain,
    ( r1_tarski(k5_xboole_0(sK15,sK16),sK17)
    | r2_hidden(sK1(k5_xboole_0(sK15,sK16),sK17),k5_xboole_0(sK15,sK16)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_186,negated_conjecture,
    ( ~ r1_tarski(k5_xboole_0(sK15,sK16),sK17) ),
    inference(cnf_transformation,[],[f498])).

cnf(c_187,negated_conjecture,
    ( r1_tarski(k4_xboole_0(sK16,sK15),sK17) ),
    inference(cnf_transformation,[],[f497])).

cnf(c_188,negated_conjecture,
    ( r1_tarski(k4_xboole_0(sK15,sK16),sK17) ),
    inference(cnf_transformation,[],[f496])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_143346,c_78421,c_60560,c_7952,c_7949,c_6034,c_5861,c_5862,c_186,c_187,c_188])).

%------------------------------------------------------------------------------
