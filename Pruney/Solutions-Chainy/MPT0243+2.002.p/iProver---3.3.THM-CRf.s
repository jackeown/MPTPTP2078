%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:31:54 EST 2020

% Result     : Theorem 3.97s
% Output     : CNFRefutation 3.97s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 249 expanded)
%              Number of clauses        :   58 (  85 expanded)
%              Number of leaves         :   14 (  50 expanded)
%              Depth                    :   17
%              Number of atoms          :  330 ( 874 expanded)
%              Number of equality atoms :   65 ( 111 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

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

fof(f17,plain,(
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

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f19,plain,(
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
    inference(rectify,[],[f18])).

fof(f20,plain,(
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

fof(f21,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f20])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f22])).

fof(f38,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f56,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f36])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_tarski(X0,X1),X2)
      <=> ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <~> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2)
        | ~ r1_tarski(k2_tarski(X0,X1),X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2)
        | ~ r1_tarski(k2_tarski(X0,X1),X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f25])).

fof(f27,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_hidden(X1,X2)
          | ~ r2_hidden(X0,X2)
          | ~ r1_tarski(k2_tarski(X0,X1),X2) )
        & ( ( r2_hidden(X1,X2)
            & r2_hidden(X0,X2) )
          | r1_tarski(k2_tarski(X0,X1),X2) ) )
   => ( ( ~ r2_hidden(sK2,sK3)
        | ~ r2_hidden(sK1,sK3)
        | ~ r1_tarski(k2_tarski(sK1,sK2),sK3) )
      & ( ( r2_hidden(sK2,sK3)
          & r2_hidden(sK1,sK3) )
        | r1_tarski(k2_tarski(sK1,sK2),sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ( ~ r2_hidden(sK2,sK3)
      | ~ r2_hidden(sK1,sK3)
      | ~ r1_tarski(k2_tarski(sK1,sK2),sK3) )
    & ( ( r2_hidden(sK2,sK3)
        & r2_hidden(sK1,sK3) )
      | r1_tarski(k2_tarski(sK1,sK2),sK3) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f26,f27])).

fof(f47,plain,
    ( r2_hidden(sK2,sK3)
    | r1_tarski(k2_tarski(sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f50,plain,
    ( r2_hidden(sK2,sK3)
    | r1_tarski(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),sK3) ),
    inference(definition_unfolding,[],[f47,f43])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f48,plain,
    ( ~ r2_hidden(sK2,sK3)
    | ~ r2_hidden(sK1,sK3)
    | ~ r1_tarski(k2_tarski(sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f49,plain,
    ( ~ r2_hidden(sK2,sK3)
    | ~ r2_hidden(sK1,sK3)
    | ~ r1_tarski(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),sK3) ),
    inference(definition_unfolding,[],[f48,f43])).

fof(f46,plain,
    ( r2_hidden(sK1,sK3)
    | r1_tarski(k2_tarski(sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f51,plain,
    ( r2_hidden(sK1,sK3)
    | r1_tarski(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),sK3) ),
    inference(definition_unfolding,[],[f46,f43])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

cnf(c_2,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X2)
    | ~ r2_hidden(sK0(X0,X1,X2),X0)
    | k2_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_16206,plain,
    ( ~ r2_hidden(sK0(X0,k1_tarski(sK2),X1),X1)
    | ~ r2_hidden(sK0(X0,k1_tarski(sK2),X1),X0)
    | k2_xboole_0(X0,k1_tarski(sK2)) = X1 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_16213,plain,
    ( ~ r2_hidden(sK0(sK3,k1_tarski(sK2),sK3),sK3)
    | k2_xboole_0(sK3,k1_tarski(sK2)) = sK3 ),
    inference(instantiation,[status(thm)],[c_16206])).

cnf(c_319,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_7469,plain,
    ( k2_xboole_0(X0,k1_tarski(sK2)) != X1
    | sK3 != X1
    | sK3 = k2_xboole_0(X0,k1_tarski(sK2)) ),
    inference(instantiation,[status(thm)],[c_319])).

cnf(c_7470,plain,
    ( k2_xboole_0(sK3,k1_tarski(sK2)) != sK3
    | sK3 = k2_xboole_0(sK3,k1_tarski(sK2))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_7469])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1444,plain,
    ( ~ r1_tarski(X0,k2_xboole_0(k1_tarski(X1),X2))
    | ~ r1_tarski(k2_xboole_0(k1_tarski(X1),X2),X0)
    | X0 = k2_xboole_0(k1_tarski(X1),X2) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_3613,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tarski(X0),X1),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))
    | ~ r1_tarski(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k2_xboole_0(k1_tarski(X0),X1))
    | k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k2_xboole_0(k1_tarski(X0),X1) ),
    inference(instantiation,[status(thm)],[c_1444])).

cnf(c_7412,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))
    | k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) ),
    inference(instantiation,[status(thm)],[c_3613])).

cnf(c_14,plain,
    ( r1_tarski(k1_tarski(X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_6593,plain,
    ( r1_tarski(k1_tarski(sK1),sK3)
    | ~ r2_hidden(sK1,sK3) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_9,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1665,plain,
    ( r1_tarski(k2_xboole_0(k1_tarski(X0),X1),k2_xboole_0(k1_tarski(X0),X1)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_5292,plain,
    ( r1_tarski(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) ),
    inference(instantiation,[status(thm)],[c_1665])).

cnf(c_6512,plain,
    ( r1_tarski(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))) ),
    inference(instantiation,[status(thm)],[c_5292])).

cnf(c_13,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1688,plain,
    ( r1_tarski(k2_xboole_0(k1_tarski(X0),X1),k2_xboole_0(X2,X1))
    | ~ r1_tarski(k1_tarski(X0),X2) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_6096,plain,
    ( r1_tarski(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k2_xboole_0(X0,k1_tarski(sK2)))
    | ~ r1_tarski(k1_tarski(sK1),X0) ),
    inference(instantiation,[status(thm)],[c_1688])).

cnf(c_6102,plain,
    ( r1_tarski(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k2_xboole_0(sK3,k1_tarski(sK2)))
    | ~ r1_tarski(k1_tarski(sK1),sK3) ),
    inference(instantiation,[status(thm)],[c_6096])).

cnf(c_322,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1368,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_xboole_0(k1_tarski(X2),X3),X4)
    | X4 != X1
    | k2_xboole_0(k1_tarski(X2),X3) != X0 ),
    inference(instantiation,[status(thm)],[c_322])).

cnf(c_2092,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X2)
    | r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X3)
    | X3 != X2
    | k2_xboole_0(k1_tarski(X0),X1) != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(instantiation,[status(thm)],[c_1368])).

cnf(c_5253,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),X0)
    | r1_tarski(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),sK3)
    | k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) != k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_2092])).

cnf(c_6095,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k2_xboole_0(X0,k1_tarski(sK2)))
    | r1_tarski(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),sK3)
    | k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) != k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))
    | sK3 != k2_xboole_0(X0,k1_tarski(sK2)) ),
    inference(instantiation,[status(thm)],[c_5253])).

cnf(c_6098,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k2_xboole_0(sK3,k1_tarski(sK2)))
    | r1_tarski(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),sK3)
    | k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) != k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))
    | sK3 != k2_xboole_0(sK3,k1_tarski(sK2)) ),
    inference(instantiation,[status(thm)],[c_6095])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(sK0(X0,X1,X2),X0)
    | k2_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_17,negated_conjecture,
    ( r1_tarski(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),sK3)
    | r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1337,plain,
    ( ~ r1_tarski(X0,k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))
    | r1_tarski(X0,sK3)
    | r2_hidden(sK2,sK3) ),
    inference(resolution,[status(thm)],[c_11,c_17])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1571,plain,
    ( ~ r1_tarski(X0,k1_tarski(sK2))
    | r1_tarski(X0,sK3)
    | r2_hidden(sK2,sK3) ),
    inference(resolution,[status(thm)],[c_1337,c_10])).

cnf(c_1335,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k1_tarski(X2))
    | ~ r2_hidden(X2,X1) ),
    inference(resolution,[status(thm)],[c_11,c_14])).

cnf(c_1779,plain,
    ( ~ r1_tarski(X0,k1_tarski(sK2))
    | r1_tarski(X0,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1571,c_1335])).

cnf(c_2048,plain,
    ( r1_tarski(k1_tarski(X0),sK3)
    | ~ r2_hidden(X0,k1_tarski(sK2)) ),
    inference(resolution,[status(thm)],[c_1779,c_14])).

cnf(c_15,plain,
    ( ~ r1_tarski(k1_tarski(X0),X1)
    | r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_2551,plain,
    ( ~ r2_hidden(X0,k1_tarski(sK2))
    | r2_hidden(X0,sK3) ),
    inference(resolution,[status(thm)],[c_2048,c_15])).

cnf(c_3088,plain,
    ( r2_hidden(sK0(X0,k1_tarski(sK2),X1),X1)
    | r2_hidden(sK0(X0,k1_tarski(sK2),X1),X0)
    | r2_hidden(sK0(X0,k1_tarski(sK2),X1),sK3)
    | k2_xboole_0(X0,k1_tarski(sK2)) = X1 ),
    inference(resolution,[status(thm)],[c_3,c_2551])).

cnf(c_318,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2283,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_319,c_318])).

cnf(c_4031,plain,
    ( r2_hidden(sK0(X0,k1_tarski(sK2),X1),X1)
    | r2_hidden(sK0(X0,k1_tarski(sK2),X1),X0)
    | r2_hidden(sK0(X0,k1_tarski(sK2),X1),sK3)
    | X1 = k2_xboole_0(X0,k1_tarski(sK2)) ),
    inference(resolution,[status(thm)],[c_3088,c_2283])).

cnf(c_4033,plain,
    ( r2_hidden(sK0(sK3,k1_tarski(sK2),sK3),sK3)
    | sK3 = k2_xboole_0(sK3,k1_tarski(sK2)) ),
    inference(instantiation,[status(thm)],[c_4031])).

cnf(c_2046,plain,
    ( r1_tarski(k1_tarski(sK2),sK3) ),
    inference(resolution,[status(thm)],[c_1779,c_9])).

cnf(c_16,negated_conjecture,
    ( ~ r1_tarski(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),sK3)
    | ~ r2_hidden(sK1,sK3)
    | ~ r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_689,plain,
    ( r1_tarski(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),sK3) != iProver_top
    | r2_hidden(sK1,sK3) != iProver_top
    | r2_hidden(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_21,plain,
    ( r1_tarski(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),sK3) != iProver_top
    | r2_hidden(sK1,sK3) != iProver_top
    | r2_hidden(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_18,negated_conjecture,
    ( r1_tarski(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),sK3)
    | r2_hidden(sK1,sK3) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1338,plain,
    ( ~ r1_tarski(X0,k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))
    | r1_tarski(X0,sK3)
    | r2_hidden(sK1,sK3) ),
    inference(resolution,[status(thm)],[c_11,c_18])).

cnf(c_12,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1637,plain,
    ( r1_tarski(k1_tarski(sK1),sK3)
    | r2_hidden(sK1,sK3) ),
    inference(resolution,[status(thm)],[c_1338,c_12])).

cnf(c_1660,plain,
    ( r2_hidden(sK1,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1637,c_15])).

cnf(c_1661,plain,
    ( r2_hidden(sK1,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1660])).

cnf(c_1755,plain,
    ( r1_tarski(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),sK3) != iProver_top
    | r2_hidden(sK2,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_689,c_21,c_1661])).

cnf(c_1757,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),sK3)
    | ~ r2_hidden(sK2,sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1755])).

cnf(c_1526,plain,
    ( ~ r1_tarski(k1_tarski(sK2),sK3)
    | r2_hidden(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_41,plain,
    ( ~ r1_tarski(sK3,sK3)
    | sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_37,plain,
    ( r1_tarski(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_16213,c_7470,c_7412,c_6593,c_6512,c_6102,c_6098,c_4033,c_2046,c_1757,c_1660,c_1526,c_41,c_37])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:55:06 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.97/0.96  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.97/0.96  
% 3.97/0.96  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.97/0.96  
% 3.97/0.96  ------  iProver source info
% 3.97/0.96  
% 3.97/0.96  git: date: 2020-06-30 10:37:57 +0100
% 3.97/0.96  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.97/0.96  git: non_committed_changes: false
% 3.97/0.96  git: last_make_outside_of_git: false
% 3.97/0.96  
% 3.97/0.96  ------ 
% 3.97/0.96  
% 3.97/0.96  ------ Input Options
% 3.97/0.96  
% 3.97/0.96  --out_options                           all
% 3.97/0.96  --tptp_safe_out                         true
% 3.97/0.96  --problem_path                          ""
% 3.97/0.96  --include_path                          ""
% 3.97/0.96  --clausifier                            res/vclausify_rel
% 3.97/0.96  --clausifier_options                    --mode clausify
% 3.97/0.96  --stdin                                 false
% 3.97/0.96  --stats_out                             sel
% 3.97/0.96  
% 3.97/0.96  ------ General Options
% 3.97/0.96  
% 3.97/0.96  --fof                                   false
% 3.97/0.96  --time_out_real                         604.99
% 3.97/0.96  --time_out_virtual                      -1.
% 3.97/0.96  --symbol_type_check                     false
% 3.97/0.96  --clausify_out                          false
% 3.97/0.96  --sig_cnt_out                           false
% 3.97/0.96  --trig_cnt_out                          false
% 3.97/0.96  --trig_cnt_out_tolerance                1.
% 3.97/0.96  --trig_cnt_out_sk_spl                   false
% 3.97/0.96  --abstr_cl_out                          false
% 3.97/0.96  
% 3.97/0.96  ------ Global Options
% 3.97/0.96  
% 3.97/0.96  --schedule                              none
% 3.97/0.96  --add_important_lit                     false
% 3.97/0.96  --prop_solver_per_cl                    1000
% 3.97/0.96  --min_unsat_core                        false
% 3.97/0.96  --soft_assumptions                      false
% 3.97/0.96  --soft_lemma_size                       3
% 3.97/0.96  --prop_impl_unit_size                   0
% 3.97/0.96  --prop_impl_unit                        []
% 3.97/0.96  --share_sel_clauses                     true
% 3.97/0.96  --reset_solvers                         false
% 3.97/0.96  --bc_imp_inh                            [conj_cone]
% 3.97/0.96  --conj_cone_tolerance                   3.
% 3.97/0.96  --extra_neg_conj                        none
% 3.97/0.96  --large_theory_mode                     true
% 3.97/0.96  --prolific_symb_bound                   200
% 3.97/0.96  --lt_threshold                          2000
% 3.97/0.96  --clause_weak_htbl                      true
% 3.97/0.96  --gc_record_bc_elim                     false
% 3.97/0.96  
% 3.97/0.96  ------ Preprocessing Options
% 3.97/0.96  
% 3.97/0.96  --preprocessing_flag                    true
% 3.97/0.96  --time_out_prep_mult                    0.1
% 3.97/0.96  --splitting_mode                        input
% 3.97/0.96  --splitting_grd                         true
% 3.97/0.96  --splitting_cvd                         false
% 3.97/0.96  --splitting_cvd_svl                     false
% 3.97/0.96  --splitting_nvd                         32
% 3.97/0.96  --sub_typing                            true
% 3.97/0.96  --prep_gs_sim                           false
% 3.97/0.96  --prep_unflatten                        true
% 3.97/0.96  --prep_res_sim                          true
% 3.97/0.96  --prep_upred                            true
% 3.97/0.96  --prep_sem_filter                       exhaustive
% 3.97/0.96  --prep_sem_filter_out                   false
% 3.97/0.96  --pred_elim                             false
% 3.97/0.96  --res_sim_input                         true
% 3.97/0.96  --eq_ax_congr_red                       true
% 3.97/0.96  --pure_diseq_elim                       true
% 3.97/0.96  --brand_transform                       false
% 3.97/0.96  --non_eq_to_eq                          false
% 3.97/0.96  --prep_def_merge                        true
% 3.97/0.96  --prep_def_merge_prop_impl              false
% 3.97/0.96  --prep_def_merge_mbd                    true
% 3.97/0.96  --prep_def_merge_tr_red                 false
% 3.97/0.96  --prep_def_merge_tr_cl                  false
% 3.97/0.96  --smt_preprocessing                     true
% 3.97/0.96  --smt_ac_axioms                         fast
% 3.97/0.96  --preprocessed_out                      false
% 3.97/0.96  --preprocessed_stats                    false
% 3.97/0.96  
% 3.97/0.96  ------ Abstraction refinement Options
% 3.97/0.96  
% 3.97/0.96  --abstr_ref                             []
% 3.97/0.96  --abstr_ref_prep                        false
% 3.97/0.96  --abstr_ref_until_sat                   false
% 3.97/0.96  --abstr_ref_sig_restrict                funpre
% 3.97/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 3.97/0.96  --abstr_ref_under                       []
% 3.97/0.96  
% 3.97/0.96  ------ SAT Options
% 3.97/0.96  
% 3.97/0.96  --sat_mode                              false
% 3.97/0.96  --sat_fm_restart_options                ""
% 3.97/0.96  --sat_gr_def                            false
% 3.97/0.96  --sat_epr_types                         true
% 3.97/0.96  --sat_non_cyclic_types                  false
% 3.97/0.96  --sat_finite_models                     false
% 3.97/0.96  --sat_fm_lemmas                         false
% 3.97/0.96  --sat_fm_prep                           false
% 3.97/0.96  --sat_fm_uc_incr                        true
% 3.97/0.96  --sat_out_model                         small
% 3.97/0.96  --sat_out_clauses                       false
% 3.97/0.96  
% 3.97/0.96  ------ QBF Options
% 3.97/0.96  
% 3.97/0.96  --qbf_mode                              false
% 3.97/0.96  --qbf_elim_univ                         false
% 3.97/0.96  --qbf_dom_inst                          none
% 3.97/0.96  --qbf_dom_pre_inst                      false
% 3.97/0.96  --qbf_sk_in                             false
% 3.97/0.96  --qbf_pred_elim                         true
% 3.97/0.96  --qbf_split                             512
% 3.97/0.96  
% 3.97/0.96  ------ BMC1 Options
% 3.97/0.96  
% 3.97/0.96  --bmc1_incremental                      false
% 3.97/0.96  --bmc1_axioms                           reachable_all
% 3.97/0.96  --bmc1_min_bound                        0
% 3.97/0.96  --bmc1_max_bound                        -1
% 3.97/0.96  --bmc1_max_bound_default                -1
% 3.97/0.96  --bmc1_symbol_reachability              true
% 3.97/0.96  --bmc1_property_lemmas                  false
% 3.97/0.96  --bmc1_k_induction                      false
% 3.97/0.96  --bmc1_non_equiv_states                 false
% 3.97/0.96  --bmc1_deadlock                         false
% 3.97/0.96  --bmc1_ucm                              false
% 3.97/0.96  --bmc1_add_unsat_core                   none
% 3.97/0.96  --bmc1_unsat_core_children              false
% 3.97/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 3.97/0.96  --bmc1_out_stat                         full
% 3.97/0.96  --bmc1_ground_init                      false
% 3.97/0.96  --bmc1_pre_inst_next_state              false
% 3.97/0.96  --bmc1_pre_inst_state                   false
% 3.97/0.96  --bmc1_pre_inst_reach_state             false
% 3.97/0.96  --bmc1_out_unsat_core                   false
% 3.97/0.96  --bmc1_aig_witness_out                  false
% 3.97/0.96  --bmc1_verbose                          false
% 3.97/0.96  --bmc1_dump_clauses_tptp                false
% 3.97/0.96  --bmc1_dump_unsat_core_tptp             false
% 3.97/0.96  --bmc1_dump_file                        -
% 3.97/0.96  --bmc1_ucm_expand_uc_limit              128
% 3.97/0.96  --bmc1_ucm_n_expand_iterations          6
% 3.97/0.96  --bmc1_ucm_extend_mode                  1
% 3.97/0.96  --bmc1_ucm_init_mode                    2
% 3.97/0.96  --bmc1_ucm_cone_mode                    none
% 3.97/0.96  --bmc1_ucm_reduced_relation_type        0
% 3.97/0.96  --bmc1_ucm_relax_model                  4
% 3.97/0.96  --bmc1_ucm_full_tr_after_sat            true
% 3.97/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 3.97/0.96  --bmc1_ucm_layered_model                none
% 3.97/0.96  --bmc1_ucm_max_lemma_size               10
% 3.97/0.96  
% 3.97/0.96  ------ AIG Options
% 3.97/0.96  
% 3.97/0.96  --aig_mode                              false
% 3.97/0.96  
% 3.97/0.96  ------ Instantiation Options
% 3.97/0.96  
% 3.97/0.96  --instantiation_flag                    true
% 3.97/0.96  --inst_sos_flag                         false
% 3.97/0.96  --inst_sos_phase                        true
% 3.97/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.97/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.97/0.96  --inst_lit_sel_side                     num_symb
% 3.97/0.96  --inst_solver_per_active                1400
% 3.97/0.96  --inst_solver_calls_frac                1.
% 3.97/0.96  --inst_passive_queue_type               priority_queues
% 3.97/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.97/0.96  --inst_passive_queues_freq              [25;2]
% 3.97/0.96  --inst_dismatching                      true
% 3.97/0.96  --inst_eager_unprocessed_to_passive     true
% 3.97/0.96  --inst_prop_sim_given                   true
% 3.97/0.96  --inst_prop_sim_new                     false
% 3.97/0.96  --inst_subs_new                         false
% 3.97/0.96  --inst_eq_res_simp                      false
% 3.97/0.96  --inst_subs_given                       false
% 3.97/0.96  --inst_orphan_elimination               true
% 3.97/0.96  --inst_learning_loop_flag               true
% 3.97/0.96  --inst_learning_start                   3000
% 3.97/0.96  --inst_learning_factor                  2
% 3.97/0.96  --inst_start_prop_sim_after_learn       3
% 3.97/0.96  --inst_sel_renew                        solver
% 3.97/0.96  --inst_lit_activity_flag                true
% 3.97/0.96  --inst_restr_to_given                   false
% 3.97/0.96  --inst_activity_threshold               500
% 3.97/0.96  --inst_out_proof                        true
% 3.97/0.96  
% 3.97/0.96  ------ Resolution Options
% 3.97/0.96  
% 3.97/0.96  --resolution_flag                       true
% 3.97/0.96  --res_lit_sel                           adaptive
% 3.97/0.96  --res_lit_sel_side                      none
% 3.97/0.96  --res_ordering                          kbo
% 3.97/0.96  --res_to_prop_solver                    active
% 3.97/0.96  --res_prop_simpl_new                    false
% 3.97/0.96  --res_prop_simpl_given                  true
% 3.97/0.96  --res_passive_queue_type                priority_queues
% 3.97/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.97/0.96  --res_passive_queues_freq               [15;5]
% 3.97/0.96  --res_forward_subs                      full
% 3.97/0.96  --res_backward_subs                     full
% 3.97/0.96  --res_forward_subs_resolution           true
% 3.97/0.96  --res_backward_subs_resolution          true
% 3.97/0.96  --res_orphan_elimination                true
% 3.97/0.96  --res_time_limit                        2.
% 3.97/0.96  --res_out_proof                         true
% 3.97/0.96  
% 3.97/0.96  ------ Superposition Options
% 3.97/0.96  
% 3.97/0.96  --superposition_flag                    true
% 3.97/0.96  --sup_passive_queue_type                priority_queues
% 3.97/0.96  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.97/0.96  --sup_passive_queues_freq               [1;4]
% 3.97/0.96  --demod_completeness_check              fast
% 3.97/0.96  --demod_use_ground                      true
% 3.97/0.96  --sup_to_prop_solver                    passive
% 3.97/0.96  --sup_prop_simpl_new                    true
% 3.97/0.96  --sup_prop_simpl_given                  true
% 3.97/0.96  --sup_fun_splitting                     false
% 3.97/0.96  --sup_smt_interval                      50000
% 3.97/0.96  
% 3.97/0.96  ------ Superposition Simplification Setup
% 3.97/0.96  
% 3.97/0.96  --sup_indices_passive                   []
% 3.97/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.97/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.97/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.97/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 3.97/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.97/0.96  --sup_full_bw                           [BwDemod]
% 3.97/0.96  --sup_immed_triv                        [TrivRules]
% 3.97/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.97/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.97/0.96  --sup_immed_bw_main                     []
% 3.97/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.97/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 3.97/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.97/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.97/0.96  
% 3.97/0.96  ------ Combination Options
% 3.97/0.96  
% 3.97/0.96  --comb_res_mult                         3
% 3.97/0.96  --comb_sup_mult                         2
% 3.97/0.96  --comb_inst_mult                        10
% 3.97/0.96  
% 3.97/0.96  ------ Debug Options
% 3.97/0.96  
% 3.97/0.96  --dbg_backtrace                         false
% 3.97/0.96  --dbg_dump_prop_clauses                 false
% 3.97/0.96  --dbg_dump_prop_clauses_file            -
% 3.97/0.96  --dbg_out_stat                          false
% 3.97/0.96  ------ Parsing...
% 3.97/0.96  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.97/0.96  
% 3.97/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 3.97/0.96  
% 3.97/0.96  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.97/0.96  
% 3.97/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.97/0.96  ------ Proving...
% 3.97/0.96  ------ Problem Properties 
% 3.97/0.96  
% 3.97/0.96  
% 3.97/0.96  clauses                                 18
% 3.97/0.96  conjectures                             3
% 3.97/0.96  EPR                                     3
% 3.97/0.96  Horn                                    14
% 3.97/0.96  unary                                   3
% 3.97/0.96  binary                                  8
% 3.97/0.96  lits                                    41
% 3.97/0.96  lits eq                                 5
% 3.97/0.96  fd_pure                                 0
% 3.97/0.96  fd_pseudo                               0
% 3.97/0.96  fd_cond                                 0
% 3.97/0.96  fd_pseudo_cond                          4
% 3.97/0.96  AC symbols                              0
% 3.97/0.96  
% 3.97/0.96  ------ Input Options Time Limit: Unbounded
% 3.97/0.96  
% 3.97/0.96  
% 3.97/0.96  ------ 
% 3.97/0.96  Current options:
% 3.97/0.96  ------ 
% 3.97/0.96  
% 3.97/0.96  ------ Input Options
% 3.97/0.96  
% 3.97/0.96  --out_options                           all
% 3.97/0.96  --tptp_safe_out                         true
% 3.97/0.96  --problem_path                          ""
% 3.97/0.96  --include_path                          ""
% 3.97/0.96  --clausifier                            res/vclausify_rel
% 3.97/0.96  --clausifier_options                    --mode clausify
% 3.97/0.96  --stdin                                 false
% 3.97/0.96  --stats_out                             sel
% 3.97/0.96  
% 3.97/0.96  ------ General Options
% 3.97/0.96  
% 3.97/0.96  --fof                                   false
% 3.97/0.96  --time_out_real                         604.99
% 3.97/0.96  --time_out_virtual                      -1.
% 3.97/0.96  --symbol_type_check                     false
% 3.97/0.96  --clausify_out                          false
% 3.97/0.96  --sig_cnt_out                           false
% 3.97/0.96  --trig_cnt_out                          false
% 3.97/0.96  --trig_cnt_out_tolerance                1.
% 3.97/0.96  --trig_cnt_out_sk_spl                   false
% 3.97/0.96  --abstr_cl_out                          false
% 3.97/0.96  
% 3.97/0.96  ------ Global Options
% 3.97/0.96  
% 3.97/0.96  --schedule                              none
% 3.97/0.96  --add_important_lit                     false
% 3.97/0.96  --prop_solver_per_cl                    1000
% 3.97/0.96  --min_unsat_core                        false
% 3.97/0.96  --soft_assumptions                      false
% 3.97/0.96  --soft_lemma_size                       3
% 3.97/0.96  --prop_impl_unit_size                   0
% 3.97/0.96  --prop_impl_unit                        []
% 3.97/0.96  --share_sel_clauses                     true
% 3.97/0.96  --reset_solvers                         false
% 3.97/0.96  --bc_imp_inh                            [conj_cone]
% 3.97/0.96  --conj_cone_tolerance                   3.
% 3.97/0.96  --extra_neg_conj                        none
% 3.97/0.96  --large_theory_mode                     true
% 3.97/0.96  --prolific_symb_bound                   200
% 3.97/0.96  --lt_threshold                          2000
% 3.97/0.96  --clause_weak_htbl                      true
% 3.97/0.96  --gc_record_bc_elim                     false
% 3.97/0.96  
% 3.97/0.96  ------ Preprocessing Options
% 3.97/0.96  
% 3.97/0.96  --preprocessing_flag                    true
% 3.97/0.96  --time_out_prep_mult                    0.1
% 3.97/0.96  --splitting_mode                        input
% 3.97/0.96  --splitting_grd                         true
% 3.97/0.96  --splitting_cvd                         false
% 3.97/0.96  --splitting_cvd_svl                     false
% 3.97/0.96  --splitting_nvd                         32
% 3.97/0.96  --sub_typing                            true
% 3.97/0.96  --prep_gs_sim                           false
% 3.97/0.96  --prep_unflatten                        true
% 3.97/0.96  --prep_res_sim                          true
% 3.97/0.96  --prep_upred                            true
% 3.97/0.96  --prep_sem_filter                       exhaustive
% 3.97/0.96  --prep_sem_filter_out                   false
% 3.97/0.96  --pred_elim                             false
% 3.97/0.96  --res_sim_input                         true
% 3.97/0.96  --eq_ax_congr_red                       true
% 3.97/0.96  --pure_diseq_elim                       true
% 3.97/0.96  --brand_transform                       false
% 3.97/0.96  --non_eq_to_eq                          false
% 3.97/0.96  --prep_def_merge                        true
% 3.97/0.96  --prep_def_merge_prop_impl              false
% 3.97/0.96  --prep_def_merge_mbd                    true
% 3.97/0.96  --prep_def_merge_tr_red                 false
% 3.97/0.96  --prep_def_merge_tr_cl                  false
% 3.97/0.96  --smt_preprocessing                     true
% 3.97/0.96  --smt_ac_axioms                         fast
% 3.97/0.96  --preprocessed_out                      false
% 3.97/0.96  --preprocessed_stats                    false
% 3.97/0.96  
% 3.97/0.96  ------ Abstraction refinement Options
% 3.97/0.96  
% 3.97/0.96  --abstr_ref                             []
% 3.97/0.96  --abstr_ref_prep                        false
% 3.97/0.96  --abstr_ref_until_sat                   false
% 3.97/0.96  --abstr_ref_sig_restrict                funpre
% 3.97/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 3.97/0.96  --abstr_ref_under                       []
% 3.97/0.96  
% 3.97/0.96  ------ SAT Options
% 3.97/0.96  
% 3.97/0.96  --sat_mode                              false
% 3.97/0.96  --sat_fm_restart_options                ""
% 3.97/0.96  --sat_gr_def                            false
% 3.97/0.96  --sat_epr_types                         true
% 3.97/0.96  --sat_non_cyclic_types                  false
% 3.97/0.96  --sat_finite_models                     false
% 3.97/0.96  --sat_fm_lemmas                         false
% 3.97/0.96  --sat_fm_prep                           false
% 3.97/0.96  --sat_fm_uc_incr                        true
% 3.97/0.96  --sat_out_model                         small
% 3.97/0.96  --sat_out_clauses                       false
% 3.97/0.96  
% 3.97/0.96  ------ QBF Options
% 3.97/0.96  
% 3.97/0.96  --qbf_mode                              false
% 3.97/0.96  --qbf_elim_univ                         false
% 3.97/0.96  --qbf_dom_inst                          none
% 3.97/0.96  --qbf_dom_pre_inst                      false
% 3.97/0.96  --qbf_sk_in                             false
% 3.97/0.96  --qbf_pred_elim                         true
% 3.97/0.96  --qbf_split                             512
% 3.97/0.96  
% 3.97/0.96  ------ BMC1 Options
% 3.97/0.96  
% 3.97/0.96  --bmc1_incremental                      false
% 3.97/0.96  --bmc1_axioms                           reachable_all
% 3.97/0.96  --bmc1_min_bound                        0
% 3.97/0.96  --bmc1_max_bound                        -1
% 3.97/0.96  --bmc1_max_bound_default                -1
% 3.97/0.96  --bmc1_symbol_reachability              true
% 3.97/0.96  --bmc1_property_lemmas                  false
% 3.97/0.96  --bmc1_k_induction                      false
% 3.97/0.96  --bmc1_non_equiv_states                 false
% 3.97/0.96  --bmc1_deadlock                         false
% 3.97/0.96  --bmc1_ucm                              false
% 3.97/0.96  --bmc1_add_unsat_core                   none
% 3.97/0.96  --bmc1_unsat_core_children              false
% 3.97/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 3.97/0.96  --bmc1_out_stat                         full
% 3.97/0.96  --bmc1_ground_init                      false
% 3.97/0.96  --bmc1_pre_inst_next_state              false
% 3.97/0.96  --bmc1_pre_inst_state                   false
% 3.97/0.96  --bmc1_pre_inst_reach_state             false
% 3.97/0.96  --bmc1_out_unsat_core                   false
% 3.97/0.96  --bmc1_aig_witness_out                  false
% 3.97/0.96  --bmc1_verbose                          false
% 3.97/0.96  --bmc1_dump_clauses_tptp                false
% 3.97/0.96  --bmc1_dump_unsat_core_tptp             false
% 3.97/0.96  --bmc1_dump_file                        -
% 3.97/0.96  --bmc1_ucm_expand_uc_limit              128
% 3.97/0.96  --bmc1_ucm_n_expand_iterations          6
% 3.97/0.96  --bmc1_ucm_extend_mode                  1
% 3.97/0.96  --bmc1_ucm_init_mode                    2
% 3.97/0.96  --bmc1_ucm_cone_mode                    none
% 3.97/0.96  --bmc1_ucm_reduced_relation_type        0
% 3.97/0.96  --bmc1_ucm_relax_model                  4
% 3.97/0.96  --bmc1_ucm_full_tr_after_sat            true
% 3.97/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 3.97/0.96  --bmc1_ucm_layered_model                none
% 3.97/0.96  --bmc1_ucm_max_lemma_size               10
% 3.97/0.96  
% 3.97/0.96  ------ AIG Options
% 3.97/0.96  
% 3.97/0.96  --aig_mode                              false
% 3.97/0.96  
% 3.97/0.96  ------ Instantiation Options
% 3.97/0.96  
% 3.97/0.96  --instantiation_flag                    true
% 3.97/0.96  --inst_sos_flag                         false
% 3.97/0.96  --inst_sos_phase                        true
% 3.97/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.97/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.97/0.96  --inst_lit_sel_side                     num_symb
% 3.97/0.96  --inst_solver_per_active                1400
% 3.97/0.96  --inst_solver_calls_frac                1.
% 3.97/0.96  --inst_passive_queue_type               priority_queues
% 3.97/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.97/0.96  --inst_passive_queues_freq              [25;2]
% 3.97/0.96  --inst_dismatching                      true
% 3.97/0.96  --inst_eager_unprocessed_to_passive     true
% 3.97/0.96  --inst_prop_sim_given                   true
% 3.97/0.96  --inst_prop_sim_new                     false
% 3.97/0.96  --inst_subs_new                         false
% 3.97/0.96  --inst_eq_res_simp                      false
% 3.97/0.96  --inst_subs_given                       false
% 3.97/0.96  --inst_orphan_elimination               true
% 3.97/0.96  --inst_learning_loop_flag               true
% 3.97/0.96  --inst_learning_start                   3000
% 3.97/0.96  --inst_learning_factor                  2
% 3.97/0.96  --inst_start_prop_sim_after_learn       3
% 3.97/0.96  --inst_sel_renew                        solver
% 3.97/0.96  --inst_lit_activity_flag                true
% 3.97/0.96  --inst_restr_to_given                   false
% 3.97/0.96  --inst_activity_threshold               500
% 3.97/0.96  --inst_out_proof                        true
% 3.97/0.96  
% 3.97/0.96  ------ Resolution Options
% 3.97/0.96  
% 3.97/0.96  --resolution_flag                       true
% 3.97/0.96  --res_lit_sel                           adaptive
% 3.97/0.96  --res_lit_sel_side                      none
% 3.97/0.96  --res_ordering                          kbo
% 3.97/0.96  --res_to_prop_solver                    active
% 3.97/0.96  --res_prop_simpl_new                    false
% 3.97/0.96  --res_prop_simpl_given                  true
% 3.97/0.96  --res_passive_queue_type                priority_queues
% 3.97/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.97/0.96  --res_passive_queues_freq               [15;5]
% 3.97/0.96  --res_forward_subs                      full
% 3.97/0.96  --res_backward_subs                     full
% 3.97/0.96  --res_forward_subs_resolution           true
% 3.97/0.96  --res_backward_subs_resolution          true
% 3.97/0.96  --res_orphan_elimination                true
% 3.97/0.96  --res_time_limit                        2.
% 3.97/0.96  --res_out_proof                         true
% 3.97/0.96  
% 3.97/0.96  ------ Superposition Options
% 3.97/0.96  
% 3.97/0.96  --superposition_flag                    true
% 3.97/0.96  --sup_passive_queue_type                priority_queues
% 3.97/0.96  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.97/0.96  --sup_passive_queues_freq               [1;4]
% 3.97/0.96  --demod_completeness_check              fast
% 3.97/0.96  --demod_use_ground                      true
% 3.97/0.96  --sup_to_prop_solver                    passive
% 3.97/0.96  --sup_prop_simpl_new                    true
% 3.97/0.96  --sup_prop_simpl_given                  true
% 3.97/0.96  --sup_fun_splitting                     false
% 3.97/0.96  --sup_smt_interval                      50000
% 3.97/0.96  
% 3.97/0.96  ------ Superposition Simplification Setup
% 3.97/0.96  
% 3.97/0.96  --sup_indices_passive                   []
% 3.97/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.97/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.97/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.97/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 3.97/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.97/0.96  --sup_full_bw                           [BwDemod]
% 3.97/0.96  --sup_immed_triv                        [TrivRules]
% 3.97/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.97/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.97/0.96  --sup_immed_bw_main                     []
% 3.97/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.97/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 3.97/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.97/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.97/0.96  
% 3.97/0.96  ------ Combination Options
% 3.97/0.96  
% 3.97/0.96  --comb_res_mult                         3
% 3.97/0.96  --comb_sup_mult                         2
% 3.97/0.96  --comb_inst_mult                        10
% 3.97/0.96  
% 3.97/0.96  ------ Debug Options
% 3.97/0.96  
% 3.97/0.96  --dbg_backtrace                         false
% 3.97/0.96  --dbg_dump_prop_clauses                 false
% 3.97/0.96  --dbg_dump_prop_clauses_file            -
% 3.97/0.96  --dbg_out_stat                          false
% 3.97/0.96  
% 3.97/0.96  
% 3.97/0.96  
% 3.97/0.96  
% 3.97/0.96  ------ Proving...
% 3.97/0.96  
% 3.97/0.96  
% 3.97/0.96  % SZS status Theorem for theBenchmark.p
% 3.97/0.96  
% 3.97/0.96  % SZS output start CNFRefutation for theBenchmark.p
% 3.97/0.96  
% 3.97/0.96  fof(f2,axiom,(
% 3.97/0.96    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 3.97/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.97/0.96  
% 3.97/0.96  fof(f17,plain,(
% 3.97/0.96    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.97/0.96    inference(nnf_transformation,[],[f2])).
% 3.97/0.96  
% 3.97/0.96  fof(f18,plain,(
% 3.97/0.96    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.97/0.96    inference(flattening,[],[f17])).
% 3.97/0.96  
% 3.97/0.96  fof(f19,plain,(
% 3.97/0.96    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.97/0.96    inference(rectify,[],[f18])).
% 3.97/0.96  
% 3.97/0.96  fof(f20,plain,(
% 3.97/0.96    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.97/0.96    introduced(choice_axiom,[])).
% 3.97/0.96  
% 3.97/0.96  fof(f21,plain,(
% 3.97/0.96    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.97/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f20])).
% 3.97/0.96  
% 3.97/0.96  fof(f34,plain,(
% 3.97/0.96    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.97/0.96    inference(cnf_transformation,[],[f21])).
% 3.97/0.96  
% 3.97/0.96  fof(f3,axiom,(
% 3.97/0.96    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.97/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.97/0.96  
% 3.97/0.96  fof(f22,plain,(
% 3.97/0.96    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.97/0.96    inference(nnf_transformation,[],[f3])).
% 3.97/0.96  
% 3.97/0.96  fof(f23,plain,(
% 3.97/0.96    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.97/0.96    inference(flattening,[],[f22])).
% 3.97/0.96  
% 3.97/0.96  fof(f38,plain,(
% 3.97/0.96    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.97/0.96    inference(cnf_transformation,[],[f23])).
% 3.97/0.96  
% 3.97/0.96  fof(f9,axiom,(
% 3.97/0.96    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 3.97/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.97/0.96  
% 3.97/0.96  fof(f24,plain,(
% 3.97/0.96    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 3.97/0.96    inference(nnf_transformation,[],[f9])).
% 3.97/0.96  
% 3.97/0.96  fof(f45,plain,(
% 3.97/0.96    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 3.97/0.96    inference(cnf_transformation,[],[f24])).
% 3.97/0.96  
% 3.97/0.96  fof(f36,plain,(
% 3.97/0.96    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.97/0.96    inference(cnf_transformation,[],[f23])).
% 3.97/0.96  
% 3.97/0.96  fof(f56,plain,(
% 3.97/0.96    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.97/0.96    inference(equality_resolution,[],[f36])).
% 3.97/0.96  
% 3.97/0.96  fof(f7,axiom,(
% 3.97/0.96    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)))),
% 3.97/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.97/0.96  
% 3.97/0.96  fof(f15,plain,(
% 3.97/0.96    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) | ~r1_tarski(X0,X1))),
% 3.97/0.96    inference(ennf_transformation,[],[f7])).
% 3.97/0.96  
% 3.97/0.96  fof(f42,plain,(
% 3.97/0.96    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 3.97/0.96    inference(cnf_transformation,[],[f15])).
% 3.97/0.96  
% 3.97/0.96  fof(f33,plain,(
% 3.97/0.96    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.97/0.96    inference(cnf_transformation,[],[f21])).
% 3.97/0.96  
% 3.97/0.96  fof(f5,axiom,(
% 3.97/0.96    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 3.97/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.97/0.96  
% 3.97/0.96  fof(f13,plain,(
% 3.97/0.96    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.97/0.96    inference(ennf_transformation,[],[f5])).
% 3.97/0.96  
% 3.97/0.96  fof(f14,plain,(
% 3.97/0.96    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 3.97/0.96    inference(flattening,[],[f13])).
% 3.97/0.96  
% 3.97/0.96  fof(f40,plain,(
% 3.97/0.96    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 3.97/0.96    inference(cnf_transformation,[],[f14])).
% 3.97/0.96  
% 3.97/0.96  fof(f10,conjecture,(
% 3.97/0.96    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 3.97/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.97/0.96  
% 3.97/0.96  fof(f11,negated_conjecture,(
% 3.97/0.96    ~! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 3.97/0.96    inference(negated_conjecture,[],[f10])).
% 3.97/0.96  
% 3.97/0.96  fof(f16,plain,(
% 3.97/0.96    ? [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <~> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 3.97/0.96    inference(ennf_transformation,[],[f11])).
% 3.97/0.96  
% 3.97/0.96  fof(f25,plain,(
% 3.97/0.96    ? [X0,X1,X2] : (((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | r1_tarski(k2_tarski(X0,X1),X2)))),
% 3.97/0.96    inference(nnf_transformation,[],[f16])).
% 3.97/0.96  
% 3.97/0.96  fof(f26,plain,(
% 3.97/0.96    ? [X0,X1,X2] : ((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | r1_tarski(k2_tarski(X0,X1),X2)))),
% 3.97/0.96    inference(flattening,[],[f25])).
% 3.97/0.96  
% 3.97/0.96  fof(f27,plain,(
% 3.97/0.96    ? [X0,X1,X2] : ((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | r1_tarski(k2_tarski(X0,X1),X2))) => ((~r2_hidden(sK2,sK3) | ~r2_hidden(sK1,sK3) | ~r1_tarski(k2_tarski(sK1,sK2),sK3)) & ((r2_hidden(sK2,sK3) & r2_hidden(sK1,sK3)) | r1_tarski(k2_tarski(sK1,sK2),sK3)))),
% 3.97/0.96    introduced(choice_axiom,[])).
% 3.97/0.96  
% 3.97/0.96  fof(f28,plain,(
% 3.97/0.96    (~r2_hidden(sK2,sK3) | ~r2_hidden(sK1,sK3) | ~r1_tarski(k2_tarski(sK1,sK2),sK3)) & ((r2_hidden(sK2,sK3) & r2_hidden(sK1,sK3)) | r1_tarski(k2_tarski(sK1,sK2),sK3))),
% 3.97/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f26,f27])).
% 3.97/0.96  
% 3.97/0.96  fof(f47,plain,(
% 3.97/0.96    r2_hidden(sK2,sK3) | r1_tarski(k2_tarski(sK1,sK2),sK3)),
% 3.97/0.96    inference(cnf_transformation,[],[f28])).
% 3.97/0.96  
% 3.97/0.96  fof(f8,axiom,(
% 3.97/0.96    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)),
% 3.97/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.97/0.96  
% 3.97/0.96  fof(f43,plain,(
% 3.97/0.96    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)) )),
% 3.97/0.96    inference(cnf_transformation,[],[f8])).
% 3.97/0.96  
% 3.97/0.96  fof(f50,plain,(
% 3.97/0.96    r2_hidden(sK2,sK3) | r1_tarski(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),sK3)),
% 3.97/0.96    inference(definition_unfolding,[],[f47,f43])).
% 3.97/0.96  
% 3.97/0.96  fof(f4,axiom,(
% 3.97/0.96    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 3.97/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.97/0.96  
% 3.97/0.96  fof(f12,plain,(
% 3.97/0.96    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 3.97/0.96    inference(ennf_transformation,[],[f4])).
% 3.97/0.96  
% 3.97/0.96  fof(f39,plain,(
% 3.97/0.96    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 3.97/0.96    inference(cnf_transformation,[],[f12])).
% 3.97/0.96  
% 3.97/0.96  fof(f44,plain,(
% 3.97/0.96    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)) )),
% 3.97/0.96    inference(cnf_transformation,[],[f24])).
% 3.97/0.96  
% 3.97/0.96  fof(f48,plain,(
% 3.97/0.96    ~r2_hidden(sK2,sK3) | ~r2_hidden(sK1,sK3) | ~r1_tarski(k2_tarski(sK1,sK2),sK3)),
% 3.97/0.96    inference(cnf_transformation,[],[f28])).
% 3.97/0.96  
% 3.97/0.96  fof(f49,plain,(
% 3.97/0.96    ~r2_hidden(sK2,sK3) | ~r2_hidden(sK1,sK3) | ~r1_tarski(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),sK3)),
% 3.97/0.96    inference(definition_unfolding,[],[f48,f43])).
% 3.97/0.96  
% 3.97/0.96  fof(f46,plain,(
% 3.97/0.96    r2_hidden(sK1,sK3) | r1_tarski(k2_tarski(sK1,sK2),sK3)),
% 3.97/0.96    inference(cnf_transformation,[],[f28])).
% 3.97/0.96  
% 3.97/0.96  fof(f51,plain,(
% 3.97/0.96    r2_hidden(sK1,sK3) | r1_tarski(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),sK3)),
% 3.97/0.96    inference(definition_unfolding,[],[f46,f43])).
% 3.97/0.96  
% 3.97/0.96  fof(f6,axiom,(
% 3.97/0.96    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 3.97/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.97/0.96  
% 3.97/0.96  fof(f41,plain,(
% 3.97/0.96    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.97/0.96    inference(cnf_transformation,[],[f6])).
% 3.97/0.96  
% 3.97/0.96  cnf(c_2,plain,
% 3.97/0.96      ( ~ r2_hidden(sK0(X0,X1,X2),X2)
% 3.97/0.96      | ~ r2_hidden(sK0(X0,X1,X2),X0)
% 3.97/0.96      | k2_xboole_0(X0,X1) = X2 ),
% 3.97/0.96      inference(cnf_transformation,[],[f34]) ).
% 3.97/0.96  
% 3.97/0.96  cnf(c_16206,plain,
% 3.97/0.96      ( ~ r2_hidden(sK0(X0,k1_tarski(sK2),X1),X1)
% 3.97/0.96      | ~ r2_hidden(sK0(X0,k1_tarski(sK2),X1),X0)
% 3.97/0.96      | k2_xboole_0(X0,k1_tarski(sK2)) = X1 ),
% 3.97/0.96      inference(instantiation,[status(thm)],[c_2]) ).
% 3.97/0.96  
% 3.97/0.96  cnf(c_16213,plain,
% 3.97/0.96      ( ~ r2_hidden(sK0(sK3,k1_tarski(sK2),sK3),sK3)
% 3.97/0.96      | k2_xboole_0(sK3,k1_tarski(sK2)) = sK3 ),
% 3.97/0.96      inference(instantiation,[status(thm)],[c_16206]) ).
% 3.97/0.96  
% 3.97/0.96  cnf(c_319,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.97/0.96  
% 3.97/0.96  cnf(c_7469,plain,
% 3.97/0.96      ( k2_xboole_0(X0,k1_tarski(sK2)) != X1
% 3.97/0.96      | sK3 != X1
% 3.97/0.96      | sK3 = k2_xboole_0(X0,k1_tarski(sK2)) ),
% 3.97/0.96      inference(instantiation,[status(thm)],[c_319]) ).
% 3.97/0.96  
% 3.97/0.96  cnf(c_7470,plain,
% 3.97/0.96      ( k2_xboole_0(sK3,k1_tarski(sK2)) != sK3
% 3.97/0.96      | sK3 = k2_xboole_0(sK3,k1_tarski(sK2))
% 3.97/0.96      | sK3 != sK3 ),
% 3.97/0.96      inference(instantiation,[status(thm)],[c_7469]) ).
% 3.97/0.96  
% 3.97/0.96  cnf(c_7,plain,
% 3.97/0.96      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.97/0.96      inference(cnf_transformation,[],[f38]) ).
% 3.97/0.96  
% 3.97/0.96  cnf(c_1444,plain,
% 3.97/0.96      ( ~ r1_tarski(X0,k2_xboole_0(k1_tarski(X1),X2))
% 3.97/0.96      | ~ r1_tarski(k2_xboole_0(k1_tarski(X1),X2),X0)
% 3.97/0.96      | X0 = k2_xboole_0(k1_tarski(X1),X2) ),
% 3.97/0.96      inference(instantiation,[status(thm)],[c_7]) ).
% 3.97/0.96  
% 3.97/0.96  cnf(c_3613,plain,
% 3.97/0.96      ( ~ r1_tarski(k2_xboole_0(k1_tarski(X0),X1),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))
% 3.97/0.96      | ~ r1_tarski(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k2_xboole_0(k1_tarski(X0),X1))
% 3.97/0.96      | k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k2_xboole_0(k1_tarski(X0),X1) ),
% 3.97/0.96      inference(instantiation,[status(thm)],[c_1444]) ).
% 3.97/0.96  
% 3.97/0.96  cnf(c_7412,plain,
% 3.97/0.96      ( ~ r1_tarski(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))
% 3.97/0.96      | k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) ),
% 3.97/0.96      inference(instantiation,[status(thm)],[c_3613]) ).
% 3.97/0.96  
% 3.97/0.96  cnf(c_14,plain,
% 3.97/0.96      ( r1_tarski(k1_tarski(X0),X1) | ~ r2_hidden(X0,X1) ),
% 3.97/0.96      inference(cnf_transformation,[],[f45]) ).
% 3.97/0.96  
% 3.97/0.96  cnf(c_6593,plain,
% 3.97/0.96      ( r1_tarski(k1_tarski(sK1),sK3) | ~ r2_hidden(sK1,sK3) ),
% 3.97/0.96      inference(instantiation,[status(thm)],[c_14]) ).
% 3.97/0.96  
% 3.97/0.96  cnf(c_9,plain,
% 3.97/0.96      ( r1_tarski(X0,X0) ),
% 3.97/0.96      inference(cnf_transformation,[],[f56]) ).
% 3.97/0.96  
% 3.97/0.96  cnf(c_1665,plain,
% 3.97/0.96      ( r1_tarski(k2_xboole_0(k1_tarski(X0),X1),k2_xboole_0(k1_tarski(X0),X1)) ),
% 3.97/0.96      inference(instantiation,[status(thm)],[c_9]) ).
% 3.97/0.96  
% 3.97/0.96  cnf(c_5292,plain,
% 3.97/0.96      ( r1_tarski(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) ),
% 3.97/0.96      inference(instantiation,[status(thm)],[c_1665]) ).
% 3.97/0.96  
% 3.97/0.96  cnf(c_6512,plain,
% 3.97/0.96      ( r1_tarski(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))) ),
% 3.97/0.96      inference(instantiation,[status(thm)],[c_5292]) ).
% 3.97/0.96  
% 3.97/0.96  cnf(c_13,plain,
% 3.97/0.96      ( ~ r1_tarski(X0,X1)
% 3.97/0.96      | r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ),
% 3.97/0.96      inference(cnf_transformation,[],[f42]) ).
% 3.97/0.96  
% 3.97/0.96  cnf(c_1688,plain,
% 3.97/0.96      ( r1_tarski(k2_xboole_0(k1_tarski(X0),X1),k2_xboole_0(X2,X1))
% 3.97/0.96      | ~ r1_tarski(k1_tarski(X0),X2) ),
% 3.97/0.96      inference(instantiation,[status(thm)],[c_13]) ).
% 3.97/0.96  
% 3.97/0.96  cnf(c_6096,plain,
% 3.97/0.96      ( r1_tarski(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k2_xboole_0(X0,k1_tarski(sK2)))
% 3.97/0.96      | ~ r1_tarski(k1_tarski(sK1),X0) ),
% 3.97/0.96      inference(instantiation,[status(thm)],[c_1688]) ).
% 3.97/0.96  
% 3.97/0.96  cnf(c_6102,plain,
% 3.97/0.96      ( r1_tarski(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k2_xboole_0(sK3,k1_tarski(sK2)))
% 3.97/0.96      | ~ r1_tarski(k1_tarski(sK1),sK3) ),
% 3.97/0.96      inference(instantiation,[status(thm)],[c_6096]) ).
% 3.97/0.96  
% 3.97/0.96  cnf(c_322,plain,
% 3.97/0.96      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.97/0.96      theory(equality) ).
% 3.97/0.96  
% 3.97/0.96  cnf(c_1368,plain,
% 3.97/0.96      ( ~ r1_tarski(X0,X1)
% 3.97/0.96      | r1_tarski(k2_xboole_0(k1_tarski(X2),X3),X4)
% 3.97/0.96      | X4 != X1
% 3.97/0.96      | k2_xboole_0(k1_tarski(X2),X3) != X0 ),
% 3.97/0.96      inference(instantiation,[status(thm)],[c_322]) ).
% 3.97/0.96  
% 3.97/0.96  cnf(c_2092,plain,
% 3.97/0.96      ( ~ r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X2)
% 3.97/0.96      | r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X3)
% 3.97/0.96      | X3 != X2
% 3.97/0.96      | k2_xboole_0(k1_tarski(X0),X1) != k2_xboole_0(k1_tarski(X0),X1) ),
% 3.97/0.96      inference(instantiation,[status(thm)],[c_1368]) ).
% 3.97/0.96  
% 3.97/0.96  cnf(c_5253,plain,
% 3.97/0.96      ( ~ r1_tarski(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),X0)
% 3.97/0.96      | r1_tarski(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),sK3)
% 3.97/0.96      | k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) != k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))
% 3.97/0.96      | sK3 != X0 ),
% 3.97/0.96      inference(instantiation,[status(thm)],[c_2092]) ).
% 3.97/0.96  
% 3.97/0.96  cnf(c_6095,plain,
% 3.97/0.96      ( ~ r1_tarski(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k2_xboole_0(X0,k1_tarski(sK2)))
% 3.97/0.96      | r1_tarski(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),sK3)
% 3.97/0.96      | k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) != k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))
% 3.97/0.96      | sK3 != k2_xboole_0(X0,k1_tarski(sK2)) ),
% 3.97/0.96      inference(instantiation,[status(thm)],[c_5253]) ).
% 3.97/0.96  
% 3.97/0.96  cnf(c_6098,plain,
% 3.97/0.96      ( ~ r1_tarski(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k2_xboole_0(sK3,k1_tarski(sK2)))
% 3.97/0.96      | r1_tarski(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),sK3)
% 3.97/0.96      | k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) != k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))
% 3.97/0.96      | sK3 != k2_xboole_0(sK3,k1_tarski(sK2)) ),
% 3.97/0.96      inference(instantiation,[status(thm)],[c_6095]) ).
% 3.97/0.96  
% 3.97/0.96  cnf(c_3,plain,
% 3.97/0.96      ( r2_hidden(sK0(X0,X1,X2),X1)
% 3.97/0.96      | r2_hidden(sK0(X0,X1,X2),X2)
% 3.97/0.96      | r2_hidden(sK0(X0,X1,X2),X0)
% 3.97/0.96      | k2_xboole_0(X0,X1) = X2 ),
% 3.97/0.96      inference(cnf_transformation,[],[f33]) ).
% 3.97/0.96  
% 3.97/0.96  cnf(c_11,plain,
% 3.97/0.96      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 3.97/0.96      inference(cnf_transformation,[],[f40]) ).
% 3.97/0.96  
% 3.97/0.96  cnf(c_17,negated_conjecture,
% 3.97/0.96      ( r1_tarski(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),sK3)
% 3.97/0.96      | r2_hidden(sK2,sK3) ),
% 3.97/0.96      inference(cnf_transformation,[],[f50]) ).
% 3.97/0.96  
% 3.97/0.96  cnf(c_1337,plain,
% 3.97/0.96      ( ~ r1_tarski(X0,k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))
% 3.97/0.96      | r1_tarski(X0,sK3)
% 3.97/0.96      | r2_hidden(sK2,sK3) ),
% 3.97/0.96      inference(resolution,[status(thm)],[c_11,c_17]) ).
% 3.97/0.96  
% 3.97/0.96  cnf(c_10,plain,
% 3.97/0.96      ( ~ r1_tarski(X0,X1) | r1_tarski(X0,k2_xboole_0(X2,X1)) ),
% 3.97/0.96      inference(cnf_transformation,[],[f39]) ).
% 3.97/0.96  
% 3.97/0.96  cnf(c_1571,plain,
% 3.97/0.96      ( ~ r1_tarski(X0,k1_tarski(sK2))
% 3.97/0.96      | r1_tarski(X0,sK3)
% 3.97/0.96      | r2_hidden(sK2,sK3) ),
% 3.97/0.96      inference(resolution,[status(thm)],[c_1337,c_10]) ).
% 3.97/0.96  
% 3.97/0.96  cnf(c_1335,plain,
% 3.97/0.96      ( r1_tarski(X0,X1)
% 3.97/0.96      | ~ r1_tarski(X0,k1_tarski(X2))
% 3.97/0.96      | ~ r2_hidden(X2,X1) ),
% 3.97/0.96      inference(resolution,[status(thm)],[c_11,c_14]) ).
% 3.97/0.96  
% 3.97/0.96  cnf(c_1779,plain,
% 3.97/0.96      ( ~ r1_tarski(X0,k1_tarski(sK2)) | r1_tarski(X0,sK3) ),
% 3.97/0.96      inference(forward_subsumption_resolution,
% 3.97/0.96                [status(thm)],
% 3.97/0.96                [c_1571,c_1335]) ).
% 3.97/0.96  
% 3.97/0.96  cnf(c_2048,plain,
% 3.97/0.96      ( r1_tarski(k1_tarski(X0),sK3) | ~ r2_hidden(X0,k1_tarski(sK2)) ),
% 3.97/0.96      inference(resolution,[status(thm)],[c_1779,c_14]) ).
% 3.97/0.96  
% 3.97/0.96  cnf(c_15,plain,
% 3.97/0.96      ( ~ r1_tarski(k1_tarski(X0),X1) | r2_hidden(X0,X1) ),
% 3.97/0.96      inference(cnf_transformation,[],[f44]) ).
% 3.97/0.96  
% 3.97/0.96  cnf(c_2551,plain,
% 3.97/0.96      ( ~ r2_hidden(X0,k1_tarski(sK2)) | r2_hidden(X0,sK3) ),
% 3.97/0.96      inference(resolution,[status(thm)],[c_2048,c_15]) ).
% 3.97/0.96  
% 3.97/0.96  cnf(c_3088,plain,
% 3.97/0.96      ( r2_hidden(sK0(X0,k1_tarski(sK2),X1),X1)
% 3.97/0.96      | r2_hidden(sK0(X0,k1_tarski(sK2),X1),X0)
% 3.97/0.96      | r2_hidden(sK0(X0,k1_tarski(sK2),X1),sK3)
% 3.97/0.96      | k2_xboole_0(X0,k1_tarski(sK2)) = X1 ),
% 3.97/0.96      inference(resolution,[status(thm)],[c_3,c_2551]) ).
% 3.97/0.96  
% 3.97/0.96  cnf(c_318,plain,( X0 = X0 ),theory(equality) ).
% 3.97/0.96  
% 3.97/0.96  cnf(c_2283,plain,
% 3.97/0.96      ( X0 != X1 | X1 = X0 ),
% 3.97/0.96      inference(resolution,[status(thm)],[c_319,c_318]) ).
% 3.97/0.96  
% 3.97/0.96  cnf(c_4031,plain,
% 3.97/0.96      ( r2_hidden(sK0(X0,k1_tarski(sK2),X1),X1)
% 3.97/0.96      | r2_hidden(sK0(X0,k1_tarski(sK2),X1),X0)
% 3.97/0.96      | r2_hidden(sK0(X0,k1_tarski(sK2),X1),sK3)
% 3.97/0.96      | X1 = k2_xboole_0(X0,k1_tarski(sK2)) ),
% 3.97/0.96      inference(resolution,[status(thm)],[c_3088,c_2283]) ).
% 3.97/0.96  
% 3.97/0.96  cnf(c_4033,plain,
% 3.97/0.96      ( r2_hidden(sK0(sK3,k1_tarski(sK2),sK3),sK3)
% 3.97/0.96      | sK3 = k2_xboole_0(sK3,k1_tarski(sK2)) ),
% 3.97/0.96      inference(instantiation,[status(thm)],[c_4031]) ).
% 3.97/0.96  
% 3.97/0.96  cnf(c_2046,plain,
% 3.97/0.96      ( r1_tarski(k1_tarski(sK2),sK3) ),
% 3.97/0.96      inference(resolution,[status(thm)],[c_1779,c_9]) ).
% 3.97/0.96  
% 3.97/0.96  cnf(c_16,negated_conjecture,
% 3.97/0.96      ( ~ r1_tarski(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),sK3)
% 3.97/0.96      | ~ r2_hidden(sK1,sK3)
% 3.97/0.96      | ~ r2_hidden(sK2,sK3) ),
% 3.97/0.96      inference(cnf_transformation,[],[f49]) ).
% 3.97/0.96  
% 3.97/0.96  cnf(c_689,plain,
% 3.97/0.96      ( r1_tarski(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),sK3) != iProver_top
% 3.97/0.96      | r2_hidden(sK1,sK3) != iProver_top
% 3.97/0.96      | r2_hidden(sK2,sK3) != iProver_top ),
% 3.97/0.96      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.97/0.96  
% 3.97/0.96  cnf(c_21,plain,
% 3.97/0.96      ( r1_tarski(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),sK3) != iProver_top
% 3.97/0.96      | r2_hidden(sK1,sK3) != iProver_top
% 3.97/0.96      | r2_hidden(sK2,sK3) != iProver_top ),
% 3.97/0.96      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.97/0.96  
% 3.97/0.96  cnf(c_18,negated_conjecture,
% 3.97/0.96      ( r1_tarski(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),sK3)
% 3.97/0.96      | r2_hidden(sK1,sK3) ),
% 3.97/0.96      inference(cnf_transformation,[],[f51]) ).
% 3.97/0.96  
% 3.97/0.96  cnf(c_1338,plain,
% 3.97/0.96      ( ~ r1_tarski(X0,k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))
% 3.97/0.96      | r1_tarski(X0,sK3)
% 3.97/0.96      | r2_hidden(sK1,sK3) ),
% 3.97/0.96      inference(resolution,[status(thm)],[c_11,c_18]) ).
% 3.97/0.96  
% 3.97/0.96  cnf(c_12,plain,
% 3.97/0.96      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 3.97/0.96      inference(cnf_transformation,[],[f41]) ).
% 3.97/0.96  
% 3.97/0.96  cnf(c_1637,plain,
% 3.97/0.96      ( r1_tarski(k1_tarski(sK1),sK3) | r2_hidden(sK1,sK3) ),
% 3.97/0.96      inference(resolution,[status(thm)],[c_1338,c_12]) ).
% 3.97/0.96  
% 3.97/0.96  cnf(c_1660,plain,
% 3.97/0.96      ( r2_hidden(sK1,sK3) ),
% 3.97/0.96      inference(forward_subsumption_resolution,
% 3.97/0.96                [status(thm)],
% 3.97/0.96                [c_1637,c_15]) ).
% 3.97/0.96  
% 3.97/0.96  cnf(c_1661,plain,
% 3.97/0.96      ( r2_hidden(sK1,sK3) = iProver_top ),
% 3.97/0.96      inference(predicate_to_equality,[status(thm)],[c_1660]) ).
% 3.97/0.96  
% 3.97/0.96  cnf(c_1755,plain,
% 3.97/0.96      ( r1_tarski(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),sK3) != iProver_top
% 3.97/0.96      | r2_hidden(sK2,sK3) != iProver_top ),
% 3.97/0.96      inference(global_propositional_subsumption,
% 3.97/0.96                [status(thm)],
% 3.97/0.96                [c_689,c_21,c_1661]) ).
% 3.97/0.96  
% 3.97/0.96  cnf(c_1757,plain,
% 3.97/0.96      ( ~ r1_tarski(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),sK3)
% 3.97/0.96      | ~ r2_hidden(sK2,sK3) ),
% 3.97/0.96      inference(predicate_to_equality_rev,[status(thm)],[c_1755]) ).
% 3.97/0.96  
% 3.97/0.96  cnf(c_1526,plain,
% 3.97/0.96      ( ~ r1_tarski(k1_tarski(sK2),sK3) | r2_hidden(sK2,sK3) ),
% 3.97/0.96      inference(instantiation,[status(thm)],[c_15]) ).
% 3.97/0.96  
% 3.97/0.96  cnf(c_41,plain,
% 3.97/0.96      ( ~ r1_tarski(sK3,sK3) | sK3 = sK3 ),
% 3.97/0.96      inference(instantiation,[status(thm)],[c_7]) ).
% 3.97/0.96  
% 3.97/0.96  cnf(c_37,plain,
% 3.97/0.96      ( r1_tarski(sK3,sK3) ),
% 3.97/0.96      inference(instantiation,[status(thm)],[c_9]) ).
% 3.97/0.96  
% 3.97/0.96  cnf(contradiction,plain,
% 3.97/0.96      ( $false ),
% 3.97/0.96      inference(minisat,
% 3.97/0.96                [status(thm)],
% 3.97/0.96                [c_16213,c_7470,c_7412,c_6593,c_6512,c_6102,c_6098,
% 3.97/0.96                 c_4033,c_2046,c_1757,c_1660,c_1526,c_41,c_37]) ).
% 3.97/0.96  
% 3.97/0.96  
% 3.97/0.96  % SZS output end CNFRefutation for theBenchmark.p
% 3.97/0.96  
% 3.97/0.96  ------                               Statistics
% 3.97/0.96  
% 3.97/0.96  ------ Selected
% 3.97/0.96  
% 3.97/0.96  total_time:                             0.446
% 3.97/0.96  
%------------------------------------------------------------------------------
