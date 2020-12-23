%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:26:15 EST 2020

% Result     : Theorem 6.80s
% Output     : CNFRefutation 6.80s
% Verified   : 
% Statistics : Number of formulae       :  103 (1191 expanded)
%              Number of clauses        :   64 ( 395 expanded)
%              Number of leaves         :   13 ( 291 expanded)
%              Depth                    :   25
%              Number of atoms          :  400 (6637 expanded)
%              Number of equality atoms :  191 (3315 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(nnf_transformation,[],[f2])).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f8])).

fof(f10,plain,(
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
    inference(rectify,[],[f9])).

fof(f11,plain,(
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

fof(f12,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f11])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f5,conjecture,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    inference(negated_conjecture,[],[f5])).

fof(f7,plain,(
    ? [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k2_tarski(X0,X1) ),
    inference(ennf_transformation,[],[f6])).

fof(f22,plain,
    ( ? [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k2_tarski(X0,X1)
   => k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)) != k2_tarski(sK3,sK4) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)) != k2_tarski(sK3,sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f7,f22])).

fof(f40,plain,(
    k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)) != k2_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f19,plain,(
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
    inference(rectify,[],[f18])).

fof(f20,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK2(X0,X1,X2) != X1
            & sK2(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( sK2(X0,X1,X2) = X1
          | sK2(X0,X1,X2) = X0
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK2(X0,X1,X2) != X1
              & sK2(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( sK2(X0,X1,X2) = X1
            | sK2(X0,X1,X2) = X0
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f19,f20])).

fof(f34,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f51,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k2_tarski(X0,X1)) ) ),
    inference(equality_resolution,[],[f34])).

fof(f35,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f49,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f35])).

fof(f50,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_tarski(X4,X1)) ),
    inference(equality_resolution,[],[f49])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f14,plain,(
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
    inference(rectify,[],[f13])).

fof(f15,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK1(X0,X1) != X0
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( sK1(X0,X1) = X0
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK1(X0,X1) != X0
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( sK1(X0,X1) = X0
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f14,f15])).

fof(f31,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f44,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f31])).

fof(f45,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f44])).

fof(f30,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f46,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f30])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f36,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f47,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f36])).

fof(f48,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_tarski(X0,X4)) ),
    inference(equality_resolution,[],[f47])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f12])).

cnf(c_185,plain,
    ( X0 != X1
    | X2 != X3
    | k2_tarski(X0,X2) = k2_tarski(X1,X3) ),
    theory(equality)).

cnf(c_183,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1289,plain,
    ( ~ r2_hidden(X0,k2_tarski(X1,X2))
    | r2_hidden(X3,k2_tarski(X4,X5))
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    inference(resolution,[status(thm)],[c_185,c_183])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(sK0(X0,X1,X2),X0)
    | k2_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_16,negated_conjecture,
    ( k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)) != k2_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_3571,plain,
    ( r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),k2_tarski(sK3,sK4))
    | r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),k1_tarski(sK4))
    | r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),k1_tarski(sK3)) ),
    inference(resolution,[status(thm)],[c_2,c_16])).

cnf(c_19086,plain,
    ( r2_hidden(X0,k2_tarski(X1,X2))
    | r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),k1_tarski(sK4))
    | r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),k1_tarski(sK3))
    | X0 != sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4))
    | X2 != sK4
    | X1 != sK3 ),
    inference(resolution,[status(thm)],[c_1289,c_3571])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k2_tarski(X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_18,plain,
    ( ~ r2_hidden(sK3,k2_tarski(sK3,sK3))
    | sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_14,plain,
    ( r2_hidden(X0,k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_21,plain,
    ( r2_hidden(sK3,k2_tarski(sK3,sK3)) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_8,plain,
    ( r2_hidden(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_35,plain,
    ( r2_hidden(sK3,k1_tarski(sK3)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_184,plain,
    ( X0 != X1
    | k1_tarski(X0) = k1_tarski(X1) ),
    theory(equality)).

cnf(c_188,plain,
    ( k1_tarski(sK3) = k1_tarski(sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_184])).

cnf(c_642,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k1_tarski(X2))
    | X0 != X2
    | X1 != k1_tarski(X2) ),
    inference(instantiation,[status(thm)],[c_183])).

cnf(c_1163,plain,
    ( ~ r2_hidden(X0,k1_tarski(X0))
    | r2_hidden(X1,k1_tarski(X0))
    | X1 != X0
    | k1_tarski(X0) != k1_tarski(X0) ),
    inference(instantiation,[status(thm)],[c_642])).

cnf(c_4957,plain,
    ( r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),k1_tarski(sK3))
    | ~ r2_hidden(sK3,k1_tarski(sK3))
    | sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) != sK3
    | k1_tarski(sK3) != k1_tarski(sK3) ),
    inference(instantiation,[status(thm)],[c_1163])).

cnf(c_3680,plain,
    ( r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),k1_tarski(sK4))
    | r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),k1_tarski(sK3))
    | sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) = sK4
    | sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) = sK3 ),
    inference(resolution,[status(thm)],[c_3571,c_15])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k1_tarski(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_3200,plain,
    ( ~ r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),k1_tarski(X0))
    | sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) = X0 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_3202,plain,
    ( ~ r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),k1_tarski(sK3))
    | sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) = sK3 ),
    inference(instantiation,[status(thm)],[c_3200])).

cnf(c_3683,plain,
    ( r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),k1_tarski(sK4))
    | sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) = sK4
    | sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3680,c_3202])).

cnf(c_3690,plain,
    ( sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) = sK4
    | sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) = sK3 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3683,c_9])).

cnf(c_180,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1100,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_183,c_180])).

cnf(c_4152,plain,
    ( r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),X0)
    | ~ r2_hidden(sK4,X0)
    | sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) = sK3 ),
    inference(resolution,[status(thm)],[c_3690,c_1100])).

cnf(c_181,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_869,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_181,c_180])).

cnf(c_876,plain,
    ( ~ r2_hidden(X0,k1_tarski(X1))
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_869,c_9])).

cnf(c_1422,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | ~ r2_hidden(X0,k1_tarski(X2)) ),
    inference(resolution,[status(thm)],[c_1100,c_876])).

cnf(c_4246,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),X1)
    | ~ r2_hidden(sK4,k1_tarski(X0))
    | sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) = sK3 ),
    inference(resolution,[status(thm)],[c_4152,c_1422])).

cnf(c_16145,plain,
    ( r2_hidden(X0,k2_tarski(sK3,sK4))
    | r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),k1_tarski(sK4))
    | r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),k1_tarski(sK3))
    | ~ r2_hidden(sK4,k1_tarski(X0))
    | sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) = sK3 ),
    inference(resolution,[status(thm)],[c_4246,c_3571])).

cnf(c_885,plain,
    ( ~ r2_hidden(sK4,k1_tarski(X0))
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1170,plain,
    ( ~ r2_hidden(X0,k1_tarski(X0))
    | r2_hidden(X1,k1_tarski(X2))
    | X1 != X0
    | k1_tarski(X2) != k1_tarski(X0) ),
    inference(instantiation,[status(thm)],[c_642])).

cnf(c_1788,plain,
    ( ~ r2_hidden(X0,k1_tarski(X0))
    | r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),k1_tarski(sK4))
    | sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) != X0
    | k1_tarski(sK4) != k1_tarski(X0) ),
    inference(instantiation,[status(thm)],[c_1170])).

cnf(c_1304,plain,
    ( ~ r2_hidden(X0,k1_tarski(X1))
    | X2 != X0
    | X1 = X2 ),
    inference(resolution,[status(thm)],[c_876,c_181])).

cnf(c_4153,plain,
    ( ~ r2_hidden(sK4,k1_tarski(X0))
    | X0 = sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4))
    | sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) = sK3 ),
    inference(resolution,[status(thm)],[c_3690,c_1304])).

cnf(c_5084,plain,
    ( ~ r2_hidden(sK4,k1_tarski(X0))
    | sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) = X0
    | sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) = sK3 ),
    inference(resolution,[status(thm)],[c_4153,c_869])).

cnf(c_7210,plain,
    ( k1_tarski(sK4) = k1_tarski(X0)
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_184])).

cnf(c_16655,plain,
    ( r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),k1_tarski(sK4))
    | ~ r2_hidden(sK4,k1_tarski(X0))
    | sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_16145,c_8,c_885,c_1788,c_5084,c_7210])).

cnf(c_16678,plain,
    ( r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),k1_tarski(sK4))
    | sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) = sK3 ),
    inference(resolution,[status(thm)],[c_16655,c_8])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | k2_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_4226,plain,
    ( ~ r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),k1_tarski(sK4))
    | ~ r2_hidden(sK4,k2_tarski(sK3,sK4))
    | sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) = sK3
    | k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)) = k2_tarski(sK3,sK4) ),
    inference(resolution,[status(thm)],[c_4152,c_0])).

cnf(c_16691,plain,
    ( ~ r2_hidden(sK4,k2_tarski(sK3,sK4))
    | sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) = sK3
    | k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)) = k2_tarski(sK3,sK4) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_16678,c_4226])).

cnf(c_18331,plain,
    ( sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) = sK3
    | ~ r2_hidden(sK4,k2_tarski(sK3,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_16691,c_16])).

cnf(c_18332,plain,
    ( ~ r2_hidden(sK4,k2_tarski(sK3,sK4))
    | sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) = sK3 ),
    inference(renaming,[status(thm)],[c_18331])).

cnf(c_13,plain,
    ( r2_hidden(X0,k2_tarski(X1,X0)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_18337,plain,
    ( sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) = sK3 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_18332,c_13])).

cnf(c_19299,plain,
    ( r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),k1_tarski(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_19086,c_18,c_21,c_35,c_188,c_4957,c_18337])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X2)
    | ~ r2_hidden(sK0(X0,X1,X2),X0)
    | k2_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_19311,plain,
    ( ~ r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),k2_tarski(sK3,sK4))
    | k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)) = k2_tarski(sK3,sK4) ),
    inference(resolution,[status(thm)],[c_19299,c_1])).

cnf(c_658,plain,
    ( ~ r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),k2_tarski(sK3,sK4))
    | ~ r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),k1_tarski(sK3))
    | k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)) = k2_tarski(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_20045,plain,
    ( ~ r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),k2_tarski(sK3,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_19311,c_16,c_18,c_21,c_35,c_188,c_658,c_4957,c_18337])).

cnf(c_16729,plain,
    ( r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),X0)
    | r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),k1_tarski(sK4))
    | ~ r2_hidden(sK3,X0) ),
    inference(resolution,[status(thm)],[c_16678,c_1100])).

cnf(c_20067,plain,
    ( r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),k1_tarski(sK4))
    | ~ r2_hidden(sK3,k2_tarski(sK3,sK4)) ),
    inference(resolution,[status(thm)],[c_20045,c_16729])).

cnf(c_760,plain,
    ( ~ r2_hidden(k2_tarski(sK3,sK4),k1_tarski(X0))
    | k2_tarski(sK3,sK4) = X0 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_808,plain,
    ( ~ r2_hidden(k2_tarski(sK3,sK4),k1_tarski(k2_tarski(sK3,sK4)))
    | k2_tarski(sK3,sK4) = k2_tarski(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_760])).

cnf(c_809,plain,
    ( r2_hidden(k2_tarski(sK3,sK4),k1_tarski(k2_tarski(sK3,sK4))) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1661,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),k2_tarski(sK3,sK4))
    | sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) != X0
    | k2_tarski(sK3,sK4) != X1 ),
    inference(instantiation,[status(thm)],[c_183])).

cnf(c_9934,plain,
    ( ~ r2_hidden(X0,k2_tarski(sK3,sK4))
    | r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),k2_tarski(sK3,sK4))
    | sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) != X0
    | k2_tarski(sK3,sK4) != k2_tarski(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1661])).

cnf(c_9936,plain,
    ( r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),k2_tarski(sK3,sK4))
    | ~ r2_hidden(sK3,k2_tarski(sK3,sK4))
    | sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) != sK3
    | k2_tarski(sK3,sK4) != k2_tarski(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_9934])).

cnf(c_21649,plain,
    ( ~ r2_hidden(sK3,k2_tarski(sK3,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_20067,c_16,c_18,c_21,c_35,c_188,c_658,c_808,c_809,c_4957,c_9936,c_18337])).

cnf(c_21654,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_21649,c_14])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:28:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 6.80/1.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.80/1.50  
% 6.80/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 6.80/1.50  
% 6.80/1.50  ------  iProver source info
% 6.80/1.50  
% 6.80/1.50  git: date: 2020-06-30 10:37:57 +0100
% 6.80/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 6.80/1.50  git: non_committed_changes: false
% 6.80/1.50  git: last_make_outside_of_git: false
% 6.80/1.50  
% 6.80/1.50  ------ 
% 6.80/1.50  ------ Parsing...
% 6.80/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 6.80/1.50  
% 6.80/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 6.80/1.50  
% 6.80/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 6.80/1.50  
% 6.80/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 6.80/1.50  ------ Proving...
% 6.80/1.50  ------ Problem Properties 
% 6.80/1.50  
% 6.80/1.50  
% 6.80/1.50  clauses                                 17
% 6.80/1.50  conjectures                             1
% 6.80/1.50  EPR                                     0
% 6.80/1.50  Horn                                    12
% 6.80/1.50  unary                                   4
% 6.80/1.50  binary                                  3
% 6.80/1.50  lits                                    42
% 6.80/1.50  lits eq                                 18
% 6.80/1.50  fd_pure                                 0
% 6.80/1.50  fd_pseudo                               0
% 6.80/1.50  fd_cond                                 0
% 6.80/1.50  fd_pseudo_cond                          8
% 6.80/1.50  AC symbols                              0
% 6.80/1.50  
% 6.80/1.50  ------ Input Options Time Limit: Unbounded
% 6.80/1.50  
% 6.80/1.50  
% 6.80/1.50  ------ 
% 6.80/1.50  Current options:
% 6.80/1.50  ------ 
% 6.80/1.50  
% 6.80/1.50  
% 6.80/1.50  
% 6.80/1.50  
% 6.80/1.50  ------ Proving...
% 6.80/1.50  
% 6.80/1.50  
% 6.80/1.50  % SZS status Theorem for theBenchmark.p
% 6.80/1.50  
% 6.80/1.50   Resolution empty clause
% 6.80/1.50  
% 6.80/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 6.80/1.50  
% 6.80/1.50  fof(f2,axiom,(
% 6.80/1.50    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 6.80/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.80/1.50  
% 6.80/1.50  fof(f8,plain,(
% 6.80/1.50    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 6.80/1.50    inference(nnf_transformation,[],[f2])).
% 6.80/1.50  
% 6.80/1.50  fof(f9,plain,(
% 6.80/1.50    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 6.80/1.50    inference(flattening,[],[f8])).
% 6.80/1.50  
% 6.80/1.50  fof(f10,plain,(
% 6.80/1.50    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 6.80/1.50    inference(rectify,[],[f9])).
% 6.80/1.50  
% 6.80/1.50  fof(f11,plain,(
% 6.80/1.50    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 6.80/1.50    introduced(choice_axiom,[])).
% 6.80/1.50  
% 6.80/1.50  fof(f12,plain,(
% 6.80/1.50    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 6.80/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f11])).
% 6.80/1.50  
% 6.80/1.50  fof(f27,plain,(
% 6.80/1.50    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 6.80/1.50    inference(cnf_transformation,[],[f12])).
% 6.80/1.50  
% 6.80/1.50  fof(f5,conjecture,(
% 6.80/1.50    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)),
% 6.80/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.80/1.50  
% 6.80/1.50  fof(f6,negated_conjecture,(
% 6.80/1.50    ~! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)),
% 6.80/1.50    inference(negated_conjecture,[],[f5])).
% 6.80/1.50  
% 6.80/1.50  fof(f7,plain,(
% 6.80/1.50    ? [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k2_tarski(X0,X1)),
% 6.80/1.50    inference(ennf_transformation,[],[f6])).
% 6.80/1.50  
% 6.80/1.50  fof(f22,plain,(
% 6.80/1.50    ? [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k2_tarski(X0,X1) => k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)) != k2_tarski(sK3,sK4)),
% 6.80/1.50    introduced(choice_axiom,[])).
% 6.80/1.50  
% 6.80/1.50  fof(f23,plain,(
% 6.80/1.50    k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)) != k2_tarski(sK3,sK4)),
% 6.80/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f7,f22])).
% 6.80/1.50  
% 6.80/1.50  fof(f40,plain,(
% 6.80/1.50    k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)) != k2_tarski(sK3,sK4)),
% 6.80/1.50    inference(cnf_transformation,[],[f23])).
% 6.80/1.50  
% 6.80/1.50  fof(f4,axiom,(
% 6.80/1.50    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 6.80/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.80/1.50  
% 6.80/1.50  fof(f17,plain,(
% 6.80/1.50    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 6.80/1.50    inference(nnf_transformation,[],[f4])).
% 6.80/1.50  
% 6.80/1.50  fof(f18,plain,(
% 6.80/1.50    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 6.80/1.50    inference(flattening,[],[f17])).
% 6.80/1.50  
% 6.80/1.50  fof(f19,plain,(
% 6.80/1.50    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 6.80/1.50    inference(rectify,[],[f18])).
% 6.80/1.50  
% 6.80/1.50  fof(f20,plain,(
% 6.80/1.50    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK2(X0,X1,X2) != X1 & sK2(X0,X1,X2) != X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (sK2(X0,X1,X2) = X1 | sK2(X0,X1,X2) = X0 | r2_hidden(sK2(X0,X1,X2),X2))))),
% 6.80/1.50    introduced(choice_axiom,[])).
% 6.80/1.50  
% 6.80/1.50  fof(f21,plain,(
% 6.80/1.50    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK2(X0,X1,X2) != X1 & sK2(X0,X1,X2) != X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (sK2(X0,X1,X2) = X1 | sK2(X0,X1,X2) = X0 | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 6.80/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f19,f20])).
% 6.80/1.50  
% 6.80/1.50  fof(f34,plain,(
% 6.80/1.50    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 6.80/1.50    inference(cnf_transformation,[],[f21])).
% 6.80/1.50  
% 6.80/1.50  fof(f51,plain,(
% 6.80/1.50    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k2_tarski(X0,X1))) )),
% 6.80/1.50    inference(equality_resolution,[],[f34])).
% 6.80/1.50  
% 6.80/1.50  fof(f35,plain,(
% 6.80/1.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 6.80/1.50    inference(cnf_transformation,[],[f21])).
% 6.80/1.50  
% 6.80/1.50  fof(f49,plain,(
% 6.80/1.50    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_tarski(X4,X1) != X2) )),
% 6.80/1.50    inference(equality_resolution,[],[f35])).
% 6.80/1.50  
% 6.80/1.50  fof(f50,plain,(
% 6.80/1.50    ( ! [X4,X1] : (r2_hidden(X4,k2_tarski(X4,X1))) )),
% 6.80/1.50    inference(equality_resolution,[],[f49])).
% 6.80/1.50  
% 6.80/1.50  fof(f3,axiom,(
% 6.80/1.50    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 6.80/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.80/1.50  
% 6.80/1.50  fof(f13,plain,(
% 6.80/1.50    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 6.80/1.50    inference(nnf_transformation,[],[f3])).
% 6.80/1.50  
% 6.80/1.50  fof(f14,plain,(
% 6.80/1.50    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 6.80/1.50    inference(rectify,[],[f13])).
% 6.80/1.50  
% 6.80/1.50  fof(f15,plain,(
% 6.80/1.50    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1))))),
% 6.80/1.50    introduced(choice_axiom,[])).
% 6.80/1.50  
% 6.80/1.50  fof(f16,plain,(
% 6.80/1.50    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 6.80/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f14,f15])).
% 6.80/1.50  
% 6.80/1.50  fof(f31,plain,(
% 6.80/1.50    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 6.80/1.50    inference(cnf_transformation,[],[f16])).
% 6.80/1.50  
% 6.80/1.50  fof(f44,plain,(
% 6.80/1.50    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 6.80/1.50    inference(equality_resolution,[],[f31])).
% 6.80/1.50  
% 6.80/1.50  fof(f45,plain,(
% 6.80/1.50    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 6.80/1.50    inference(equality_resolution,[],[f44])).
% 6.80/1.50  
% 6.80/1.50  fof(f30,plain,(
% 6.80/1.50    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 6.80/1.50    inference(cnf_transformation,[],[f16])).
% 6.80/1.50  
% 6.80/1.50  fof(f46,plain,(
% 6.80/1.50    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k1_tarski(X0))) )),
% 6.80/1.50    inference(equality_resolution,[],[f30])).
% 6.80/1.50  
% 6.80/1.50  fof(f29,plain,(
% 6.80/1.50    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 6.80/1.50    inference(cnf_transformation,[],[f12])).
% 6.80/1.50  
% 6.80/1.50  fof(f36,plain,(
% 6.80/1.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 6.80/1.50    inference(cnf_transformation,[],[f21])).
% 6.80/1.50  
% 6.80/1.50  fof(f47,plain,(
% 6.80/1.50    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_tarski(X0,X4) != X2) )),
% 6.80/1.50    inference(equality_resolution,[],[f36])).
% 6.80/1.50  
% 6.80/1.50  fof(f48,plain,(
% 6.80/1.50    ( ! [X4,X0] : (r2_hidden(X4,k2_tarski(X0,X4))) )),
% 6.80/1.50    inference(equality_resolution,[],[f47])).
% 6.80/1.50  
% 6.80/1.50  fof(f28,plain,(
% 6.80/1.50    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 6.80/1.50    inference(cnf_transformation,[],[f12])).
% 6.80/1.50  
% 6.80/1.50  cnf(c_185,plain,
% 6.80/1.50      ( X0 != X1 | X2 != X3 | k2_tarski(X0,X2) = k2_tarski(X1,X3) ),
% 6.80/1.50      theory(equality) ).
% 6.80/1.50  
% 6.80/1.50  cnf(c_183,plain,
% 6.80/1.50      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 6.80/1.50      theory(equality) ).
% 6.80/1.50  
% 6.80/1.50  cnf(c_1289,plain,
% 6.80/1.50      ( ~ r2_hidden(X0,k2_tarski(X1,X2))
% 6.80/1.50      | r2_hidden(X3,k2_tarski(X4,X5))
% 6.80/1.50      | X3 != X0
% 6.80/1.50      | X4 != X1
% 6.80/1.50      | X5 != X2 ),
% 6.80/1.50      inference(resolution,[status(thm)],[c_185,c_183]) ).
% 6.80/1.50  
% 6.80/1.50  cnf(c_2,plain,
% 6.80/1.50      ( r2_hidden(sK0(X0,X1,X2),X1)
% 6.80/1.50      | r2_hidden(sK0(X0,X1,X2),X2)
% 6.80/1.50      | r2_hidden(sK0(X0,X1,X2),X0)
% 6.80/1.50      | k2_xboole_0(X0,X1) = X2 ),
% 6.80/1.50      inference(cnf_transformation,[],[f27]) ).
% 6.80/1.50  
% 6.80/1.50  cnf(c_16,negated_conjecture,
% 6.80/1.50      ( k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)) != k2_tarski(sK3,sK4) ),
% 6.80/1.50      inference(cnf_transformation,[],[f40]) ).
% 6.80/1.50  
% 6.80/1.50  cnf(c_3571,plain,
% 6.80/1.50      ( r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),k2_tarski(sK3,sK4))
% 6.80/1.50      | r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),k1_tarski(sK4))
% 6.80/1.50      | r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),k1_tarski(sK3)) ),
% 6.80/1.50      inference(resolution,[status(thm)],[c_2,c_16]) ).
% 6.80/1.50  
% 6.80/1.50  cnf(c_19086,plain,
% 6.80/1.50      ( r2_hidden(X0,k2_tarski(X1,X2))
% 6.80/1.50      | r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),k1_tarski(sK4))
% 6.80/1.50      | r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),k1_tarski(sK3))
% 6.80/1.50      | X0 != sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4))
% 6.80/1.50      | X2 != sK4
% 6.80/1.50      | X1 != sK3 ),
% 6.80/1.50      inference(resolution,[status(thm)],[c_1289,c_3571]) ).
% 6.80/1.50  
% 6.80/1.50  cnf(c_15,plain,
% 6.80/1.50      ( ~ r2_hidden(X0,k2_tarski(X1,X2)) | X0 = X1 | X0 = X2 ),
% 6.80/1.50      inference(cnf_transformation,[],[f51]) ).
% 6.80/1.50  
% 6.80/1.50  cnf(c_18,plain,
% 6.80/1.50      ( ~ r2_hidden(sK3,k2_tarski(sK3,sK3)) | sK3 = sK3 ),
% 6.80/1.50      inference(instantiation,[status(thm)],[c_15]) ).
% 6.80/1.50  
% 6.80/1.50  cnf(c_14,plain,
% 6.80/1.50      ( r2_hidden(X0,k2_tarski(X0,X1)) ),
% 6.80/1.50      inference(cnf_transformation,[],[f50]) ).
% 6.80/1.50  
% 6.80/1.50  cnf(c_21,plain,
% 6.80/1.50      ( r2_hidden(sK3,k2_tarski(sK3,sK3)) ),
% 6.80/1.50      inference(instantiation,[status(thm)],[c_14]) ).
% 6.80/1.50  
% 6.80/1.50  cnf(c_8,plain,
% 6.80/1.50      ( r2_hidden(X0,k1_tarski(X0)) ),
% 6.80/1.50      inference(cnf_transformation,[],[f45]) ).
% 6.80/1.50  
% 6.80/1.50  cnf(c_35,plain,
% 6.80/1.50      ( r2_hidden(sK3,k1_tarski(sK3)) ),
% 6.80/1.50      inference(instantiation,[status(thm)],[c_8]) ).
% 6.80/1.50  
% 6.80/1.50  cnf(c_184,plain,
% 6.80/1.50      ( X0 != X1 | k1_tarski(X0) = k1_tarski(X1) ),
% 6.80/1.51      theory(equality) ).
% 6.80/1.51  
% 6.80/1.51  cnf(c_188,plain,
% 6.80/1.51      ( k1_tarski(sK3) = k1_tarski(sK3) | sK3 != sK3 ),
% 6.80/1.51      inference(instantiation,[status(thm)],[c_184]) ).
% 6.80/1.51  
% 6.80/1.51  cnf(c_642,plain,
% 6.80/1.51      ( r2_hidden(X0,X1)
% 6.80/1.51      | ~ r2_hidden(X2,k1_tarski(X2))
% 6.80/1.51      | X0 != X2
% 6.80/1.51      | X1 != k1_tarski(X2) ),
% 6.80/1.51      inference(instantiation,[status(thm)],[c_183]) ).
% 6.80/1.51  
% 6.80/1.51  cnf(c_1163,plain,
% 6.80/1.51      ( ~ r2_hidden(X0,k1_tarski(X0))
% 6.80/1.51      | r2_hidden(X1,k1_tarski(X0))
% 6.80/1.51      | X1 != X0
% 6.80/1.51      | k1_tarski(X0) != k1_tarski(X0) ),
% 6.80/1.51      inference(instantiation,[status(thm)],[c_642]) ).
% 6.80/1.51  
% 6.80/1.51  cnf(c_4957,plain,
% 6.80/1.51      ( r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),k1_tarski(sK3))
% 6.80/1.51      | ~ r2_hidden(sK3,k1_tarski(sK3))
% 6.80/1.51      | sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) != sK3
% 6.80/1.51      | k1_tarski(sK3) != k1_tarski(sK3) ),
% 6.80/1.51      inference(instantiation,[status(thm)],[c_1163]) ).
% 6.80/1.51  
% 6.80/1.51  cnf(c_3680,plain,
% 6.80/1.51      ( r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),k1_tarski(sK4))
% 6.80/1.51      | r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),k1_tarski(sK3))
% 6.80/1.51      | sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) = sK4
% 6.80/1.51      | sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) = sK3 ),
% 6.80/1.51      inference(resolution,[status(thm)],[c_3571,c_15]) ).
% 6.80/1.51  
% 6.80/1.51  cnf(c_9,plain,
% 6.80/1.51      ( ~ r2_hidden(X0,k1_tarski(X1)) | X0 = X1 ),
% 6.80/1.51      inference(cnf_transformation,[],[f46]) ).
% 6.80/1.51  
% 6.80/1.51  cnf(c_3200,plain,
% 6.80/1.51      ( ~ r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),k1_tarski(X0))
% 6.80/1.51      | sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) = X0 ),
% 6.80/1.51      inference(instantiation,[status(thm)],[c_9]) ).
% 6.80/1.51  
% 6.80/1.51  cnf(c_3202,plain,
% 6.80/1.51      ( ~ r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),k1_tarski(sK3))
% 6.80/1.51      | sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) = sK3 ),
% 6.80/1.51      inference(instantiation,[status(thm)],[c_3200]) ).
% 6.80/1.51  
% 6.80/1.51  cnf(c_3683,plain,
% 6.80/1.51      ( r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),k1_tarski(sK4))
% 6.80/1.51      | sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) = sK4
% 6.80/1.51      | sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) = sK3 ),
% 6.80/1.51      inference(global_propositional_subsumption,[status(thm)],[c_3680,c_3202]) ).
% 6.80/1.51  
% 6.80/1.51  cnf(c_3690,plain,
% 6.80/1.51      ( sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) = sK4
% 6.80/1.51      | sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) = sK3 ),
% 6.80/1.51      inference(forward_subsumption_resolution,[status(thm)],[c_3683,c_9]) ).
% 6.80/1.51  
% 6.80/1.51  cnf(c_180,plain,( X0 = X0 ),theory(equality) ).
% 6.80/1.51  
% 6.80/1.51  cnf(c_1100,plain,
% 6.80/1.51      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X1) | X2 != X0 ),
% 6.80/1.51      inference(resolution,[status(thm)],[c_183,c_180]) ).
% 6.80/1.51  
% 6.80/1.51  cnf(c_4152,plain,
% 6.80/1.51      ( r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),X0)
% 6.80/1.51      | ~ r2_hidden(sK4,X0)
% 6.80/1.51      | sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) = sK3 ),
% 6.80/1.51      inference(resolution,[status(thm)],[c_3690,c_1100]) ).
% 6.80/1.51  
% 6.80/1.51  cnf(c_181,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 6.80/1.51  
% 6.80/1.51  cnf(c_869,plain,
% 6.80/1.51      ( X0 != X1 | X1 = X0 ),
% 6.80/1.51      inference(resolution,[status(thm)],[c_181,c_180]) ).
% 6.80/1.51  
% 6.80/1.51  cnf(c_876,plain,
% 6.80/1.51      ( ~ r2_hidden(X0,k1_tarski(X1)) | X1 = X0 ),
% 6.80/1.51      inference(resolution,[status(thm)],[c_869,c_9]) ).
% 6.80/1.51  
% 6.80/1.51  cnf(c_1422,plain,
% 6.80/1.51      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X1) | ~ r2_hidden(X0,k1_tarski(X2)) ),
% 6.80/1.51      inference(resolution,[status(thm)],[c_1100,c_876]) ).
% 6.80/1.51  
% 6.80/1.51  cnf(c_4246,plain,
% 6.80/1.51      ( r2_hidden(X0,X1)
% 6.80/1.51      | ~ r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),X1)
% 6.80/1.51      | ~ r2_hidden(sK4,k1_tarski(X0))
% 6.80/1.51      | sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) = sK3 ),
% 6.80/1.51      inference(resolution,[status(thm)],[c_4152,c_1422]) ).
% 6.80/1.51  
% 6.80/1.51  cnf(c_16145,plain,
% 6.80/1.51      ( r2_hidden(X0,k2_tarski(sK3,sK4))
% 6.80/1.51      | r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),k1_tarski(sK4))
% 6.80/1.51      | r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),k1_tarski(sK3))
% 6.80/1.51      | ~ r2_hidden(sK4,k1_tarski(X0))
% 6.80/1.51      | sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) = sK3 ),
% 6.80/1.51      inference(resolution,[status(thm)],[c_4246,c_3571]) ).
% 6.80/1.51  
% 6.80/1.51  cnf(c_885,plain,
% 6.80/1.51      ( ~ r2_hidden(sK4,k1_tarski(X0)) | sK4 = X0 ),
% 6.80/1.51      inference(instantiation,[status(thm)],[c_9]) ).
% 6.80/1.51  
% 6.80/1.51  cnf(c_1170,plain,
% 6.80/1.51      ( ~ r2_hidden(X0,k1_tarski(X0))
% 6.80/1.51      | r2_hidden(X1,k1_tarski(X2))
% 6.80/1.51      | X1 != X0
% 6.80/1.51      | k1_tarski(X2) != k1_tarski(X0) ),
% 6.80/1.51      inference(instantiation,[status(thm)],[c_642]) ).
% 6.80/1.51  
% 6.80/1.51  cnf(c_1788,plain,
% 6.80/1.51      ( ~ r2_hidden(X0,k1_tarski(X0))
% 6.80/1.51      | r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),k1_tarski(sK4))
% 6.80/1.51      | sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) != X0
% 6.80/1.51      | k1_tarski(sK4) != k1_tarski(X0) ),
% 6.80/1.51      inference(instantiation,[status(thm)],[c_1170]) ).
% 6.80/1.51  
% 6.80/1.51  cnf(c_1304,plain,
% 6.80/1.51      ( ~ r2_hidden(X0,k1_tarski(X1)) | X2 != X0 | X1 = X2 ),
% 6.80/1.51      inference(resolution,[status(thm)],[c_876,c_181]) ).
% 6.80/1.51  
% 6.80/1.51  cnf(c_4153,plain,
% 6.80/1.51      ( ~ r2_hidden(sK4,k1_tarski(X0))
% 6.80/1.51      | X0 = sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4))
% 6.80/1.51      | sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) = sK3 ),
% 6.80/1.51      inference(resolution,[status(thm)],[c_3690,c_1304]) ).
% 6.80/1.51  
% 6.80/1.51  cnf(c_5084,plain,
% 6.80/1.51      ( ~ r2_hidden(sK4,k1_tarski(X0))
% 6.80/1.51      | sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) = X0
% 6.80/1.51      | sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) = sK3 ),
% 6.80/1.51      inference(resolution,[status(thm)],[c_4153,c_869]) ).
% 6.80/1.51  
% 6.80/1.51  cnf(c_7210,plain,
% 6.80/1.51      ( k1_tarski(sK4) = k1_tarski(X0) | sK4 != X0 ),
% 6.80/1.51      inference(instantiation,[status(thm)],[c_184]) ).
% 6.80/1.51  
% 6.80/1.51  cnf(c_16655,plain,
% 6.80/1.51      ( r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),k1_tarski(sK4))
% 6.80/1.51      | ~ r2_hidden(sK4,k1_tarski(X0))
% 6.80/1.51      | sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) = sK3 ),
% 6.80/1.51      inference(global_propositional_subsumption,
% 6.80/1.51                [status(thm)],
% 6.80/1.51                [c_16145,c_8,c_885,c_1788,c_5084,c_7210]) ).
% 6.80/1.51  
% 6.80/1.51  cnf(c_16678,plain,
% 6.80/1.51      ( r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),k1_tarski(sK4))
% 6.80/1.51      | sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) = sK3 ),
% 6.80/1.51      inference(resolution,[status(thm)],[c_16655,c_8]) ).
% 6.80/1.51  
% 6.80/1.51  cnf(c_0,plain,
% 6.80/1.51      ( ~ r2_hidden(sK0(X0,X1,X2),X1)
% 6.80/1.51      | ~ r2_hidden(sK0(X0,X1,X2),X2)
% 6.80/1.51      | k2_xboole_0(X0,X1) = X2 ),
% 6.80/1.51      inference(cnf_transformation,[],[f29]) ).
% 6.80/1.51  
% 6.80/1.51  cnf(c_4226,plain,
% 6.80/1.51      ( ~ r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),k1_tarski(sK4))
% 6.80/1.51      | ~ r2_hidden(sK4,k2_tarski(sK3,sK4))
% 6.80/1.51      | sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) = sK3
% 6.80/1.51      | k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)) = k2_tarski(sK3,sK4) ),
% 6.80/1.51      inference(resolution,[status(thm)],[c_4152,c_0]) ).
% 6.80/1.51  
% 6.80/1.51  cnf(c_16691,plain,
% 6.80/1.51      ( ~ r2_hidden(sK4,k2_tarski(sK3,sK4))
% 6.80/1.51      | sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) = sK3
% 6.80/1.51      | k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)) = k2_tarski(sK3,sK4) ),
% 6.80/1.51      inference(backward_subsumption_resolution,[status(thm)],[c_16678,c_4226]) ).
% 6.80/1.51  
% 6.80/1.51  cnf(c_18331,plain,
% 6.80/1.51      ( sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) = sK3
% 6.80/1.51      | ~ r2_hidden(sK4,k2_tarski(sK3,sK4)) ),
% 6.80/1.51      inference(global_propositional_subsumption,[status(thm)],[c_16691,c_16]) ).
% 6.80/1.51  
% 6.80/1.51  cnf(c_18332,plain,
% 6.80/1.51      ( ~ r2_hidden(sK4,k2_tarski(sK3,sK4))
% 6.80/1.51      | sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) = sK3 ),
% 6.80/1.51      inference(renaming,[status(thm)],[c_18331]) ).
% 6.80/1.51  
% 6.80/1.51  cnf(c_13,plain,
% 6.80/1.51      ( r2_hidden(X0,k2_tarski(X1,X0)) ),
% 6.80/1.51      inference(cnf_transformation,[],[f48]) ).
% 6.80/1.51  
% 6.80/1.51  cnf(c_18337,plain,
% 6.80/1.51      ( sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) = sK3 ),
% 6.80/1.51      inference(forward_subsumption_resolution,[status(thm)],[c_18332,c_13]) ).
% 6.80/1.51  
% 6.80/1.51  cnf(c_19299,plain,
% 6.80/1.51      ( r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),k1_tarski(sK3)) ),
% 6.80/1.51      inference(global_propositional_subsumption,
% 6.80/1.51                [status(thm)],
% 6.80/1.51                [c_19086,c_18,c_21,c_35,c_188,c_4957,c_18337]) ).
% 6.80/1.51  
% 6.80/1.51  cnf(c_1,plain,
% 6.80/1.51      ( ~ r2_hidden(sK0(X0,X1,X2),X2)
% 6.80/1.51      | ~ r2_hidden(sK0(X0,X1,X2),X0)
% 6.80/1.51      | k2_xboole_0(X0,X1) = X2 ),
% 6.80/1.51      inference(cnf_transformation,[],[f28]) ).
% 6.80/1.51  
% 6.80/1.51  cnf(c_19311,plain,
% 6.80/1.51      ( ~ r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),k2_tarski(sK3,sK4))
% 6.80/1.51      | k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)) = k2_tarski(sK3,sK4) ),
% 6.80/1.51      inference(resolution,[status(thm)],[c_19299,c_1]) ).
% 6.80/1.51  
% 6.80/1.51  cnf(c_658,plain,
% 6.80/1.51      ( ~ r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),k2_tarski(sK3,sK4))
% 6.80/1.51      | ~ r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),k1_tarski(sK3))
% 6.80/1.51      | k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)) = k2_tarski(sK3,sK4) ),
% 6.80/1.51      inference(instantiation,[status(thm)],[c_1]) ).
% 6.80/1.51  
% 6.80/1.51  cnf(c_20045,plain,
% 6.80/1.51      ( ~ r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),k2_tarski(sK3,sK4)) ),
% 6.80/1.51      inference(global_propositional_subsumption,
% 6.80/1.51                [status(thm)],
% 6.80/1.51                [c_19311,c_16,c_18,c_21,c_35,c_188,c_658,c_4957,c_18337]) ).
% 6.80/1.51  
% 6.80/1.51  cnf(c_16729,plain,
% 6.80/1.51      ( r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),X0)
% 6.80/1.51      | r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),k1_tarski(sK4))
% 6.80/1.51      | ~ r2_hidden(sK3,X0) ),
% 6.80/1.51      inference(resolution,[status(thm)],[c_16678,c_1100]) ).
% 6.80/1.51  
% 6.80/1.51  cnf(c_20067,plain,
% 6.80/1.51      ( r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),k1_tarski(sK4))
% 6.80/1.51      | ~ r2_hidden(sK3,k2_tarski(sK3,sK4)) ),
% 6.80/1.51      inference(resolution,[status(thm)],[c_20045,c_16729]) ).
% 6.80/1.51  
% 6.80/1.51  cnf(c_760,plain,
% 6.80/1.51      ( ~ r2_hidden(k2_tarski(sK3,sK4),k1_tarski(X0))
% 6.80/1.51      | k2_tarski(sK3,sK4) = X0 ),
% 6.80/1.51      inference(instantiation,[status(thm)],[c_9]) ).
% 6.80/1.51  
% 6.80/1.51  cnf(c_808,plain,
% 6.80/1.51      ( ~ r2_hidden(k2_tarski(sK3,sK4),k1_tarski(k2_tarski(sK3,sK4)))
% 6.80/1.51      | k2_tarski(sK3,sK4) = k2_tarski(sK3,sK4) ),
% 6.80/1.51      inference(instantiation,[status(thm)],[c_760]) ).
% 6.80/1.51  
% 6.80/1.51  cnf(c_809,plain,
% 6.80/1.51      ( r2_hidden(k2_tarski(sK3,sK4),k1_tarski(k2_tarski(sK3,sK4))) ),
% 6.80/1.51      inference(instantiation,[status(thm)],[c_8]) ).
% 6.80/1.51  
% 6.80/1.51  cnf(c_1661,plain,
% 6.80/1.51      ( ~ r2_hidden(X0,X1)
% 6.80/1.51      | r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),k2_tarski(sK3,sK4))
% 6.80/1.51      | sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) != X0
% 6.80/1.51      | k2_tarski(sK3,sK4) != X1 ),
% 6.80/1.51      inference(instantiation,[status(thm)],[c_183]) ).
% 6.80/1.51  
% 6.80/1.51  cnf(c_9934,plain,
% 6.80/1.51      ( ~ r2_hidden(X0,k2_tarski(sK3,sK4))
% 6.80/1.51      | r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),k2_tarski(sK3,sK4))
% 6.80/1.51      | sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) != X0
% 6.80/1.51      | k2_tarski(sK3,sK4) != k2_tarski(sK3,sK4) ),
% 6.80/1.51      inference(instantiation,[status(thm)],[c_1661]) ).
% 6.80/1.51  
% 6.80/1.51  cnf(c_9936,plain,
% 6.80/1.51      ( r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),k2_tarski(sK3,sK4))
% 6.80/1.51      | ~ r2_hidden(sK3,k2_tarski(sK3,sK4))
% 6.80/1.51      | sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) != sK3
% 6.80/1.51      | k2_tarski(sK3,sK4) != k2_tarski(sK3,sK4) ),
% 6.80/1.51      inference(instantiation,[status(thm)],[c_9934]) ).
% 6.80/1.51  
% 6.80/1.51  cnf(c_21649,plain,
% 6.80/1.51      ( ~ r2_hidden(sK3,k2_tarski(sK3,sK4)) ),
% 6.80/1.51      inference(global_propositional_subsumption,
% 6.80/1.51                [status(thm)],
% 6.80/1.51                [c_20067,c_16,c_18,c_21,c_35,c_188,c_658,c_808,c_809,c_4957,
% 6.80/1.51                 c_9936,c_18337]) ).
% 6.80/1.51  
% 6.80/1.51  cnf(c_21654,plain,
% 6.80/1.51      ( $false ),
% 6.80/1.51      inference(forward_subsumption_resolution,[status(thm)],[c_21649,c_14]) ).
% 6.80/1.51  
% 6.80/1.51  
% 6.80/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 6.80/1.51  
% 6.80/1.51  ------                               Statistics
% 6.80/1.51  
% 6.80/1.51  ------ Selected
% 6.80/1.51  
% 6.80/1.51  total_time:                             0.671
% 6.80/1.51  
%------------------------------------------------------------------------------
