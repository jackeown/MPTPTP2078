%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0060+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:22 EST 2020

% Result     : Theorem 3.46s
% Output     : CNFRefutation 3.46s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 164 expanded)
%              Number of clauses        :   42 (  49 expanded)
%              Number of leaves         :    8 (  30 expanded)
%              Depth                    :   11
%              Number of atoms          :  373 (1211 expanded)
%              Number of equality atoms :   86 ( 190 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(nnf_transformation,[],[f3])).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f17])).

fof(f19,plain,(
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
    inference(rectify,[],[f18])).

fof(f20,plain,(
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

fof(f21,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f19,f20])).

fof(f38,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f49,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f38])).

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

fof(f24,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f45,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f24])).

fof(f37,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f50,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f37])).

fof(f36,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f51,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f36])).

fof(f25,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f44,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f25])).

fof(f26,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f43,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f26])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(nnf_transformation,[],[f2])).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f12])).

fof(f14,plain,(
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
    inference(rectify,[],[f13])).

fof(f15,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X0)
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(sK1(X0,X1,X2),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            | ~ r2_hidden(sK1(X0,X1,X2),X0)
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK1(X0,X1,X2),X1)
              & r2_hidden(sK1(X0,X1,X2),X0) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f14,f15])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK1(X0,X1,X2),X1)
      | ~ r2_hidden(sK1(X0,X1,X2),X0)
      | ~ r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X1)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X0)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f4,conjecture,(
    ! [X0,X1,X2] : k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] : k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(negated_conjecture,[],[f4])).

fof(f6,plain,(
    ? [X0,X1,X2] : k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) != k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(ennf_transformation,[],[f5])).

fof(f22,plain,
    ( ? [X0,X1,X2] : k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) != k4_xboole_0(X0,k2_xboole_0(X1,X2))
   => k3_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK3,sK5)) != k4_xboole_0(sK3,k2_xboole_0(sK4,sK5)) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    k3_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK3,sK5)) != k4_xboole_0(sK3,k2_xboole_0(sK4,sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f6,f22])).

fof(f42,plain,(
    k3_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK3,sK5)) != k4_xboole_0(sK3,k2_xboole_0(sK4,sK5)) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1033,plain,
    ( r2_hidden(sK1(k4_xboole_0(sK3,sK4),k4_xboole_0(sK3,sK5),k4_xboole_0(sK3,k2_xboole_0(sK4,sK5))),X0)
    | r2_hidden(sK1(k4_xboole_0(sK3,sK4),k4_xboole_0(sK3,sK5),k4_xboole_0(sK3,k2_xboole_0(sK4,sK5))),k4_xboole_0(sK3,X0))
    | ~ r2_hidden(sK1(k4_xboole_0(sK3,sK4),k4_xboole_0(sK3,sK5),k4_xboole_0(sK3,k2_xboole_0(sK4,sK5))),sK3) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_7859,plain,
    ( r2_hidden(sK1(k4_xboole_0(sK3,sK4),k4_xboole_0(sK3,sK5),k4_xboole_0(sK3,k2_xboole_0(sK4,sK5))),k4_xboole_0(sK3,sK4))
    | r2_hidden(sK1(k4_xboole_0(sK3,sK4),k4_xboole_0(sK3,sK5),k4_xboole_0(sK3,k2_xboole_0(sK4,sK5))),sK4)
    | ~ r2_hidden(sK1(k4_xboole_0(sK3,sK4),k4_xboole_0(sK3,sK5),k4_xboole_0(sK3,k2_xboole_0(sK4,sK5))),sK3) ),
    inference(instantiation,[status(thm)],[c_1033])).

cnf(c_7860,plain,
    ( r2_hidden(sK1(k4_xboole_0(sK3,sK4),k4_xboole_0(sK3,sK5),k4_xboole_0(sK3,k2_xboole_0(sK4,sK5))),k4_xboole_0(sK3,sK4)) = iProver_top
    | r2_hidden(sK1(k4_xboole_0(sK3,sK4),k4_xboole_0(sK3,sK5),k4_xboole_0(sK3,k2_xboole_0(sK4,sK5))),sK4) = iProver_top
    | r2_hidden(sK1(k4_xboole_0(sK3,sK4),k4_xboole_0(sK3,sK5),k4_xboole_0(sK3,k2_xboole_0(sK4,sK5))),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7859])).

cnf(c_7836,plain,
    ( r2_hidden(sK1(k4_xboole_0(sK3,sK4),k4_xboole_0(sK3,sK5),k4_xboole_0(sK3,k2_xboole_0(sK4,sK5))),k4_xboole_0(sK3,k2_xboole_0(sK4,sK5)))
    | r2_hidden(sK1(k4_xboole_0(sK3,sK4),k4_xboole_0(sK3,sK5),k4_xboole_0(sK3,k2_xboole_0(sK4,sK5))),k2_xboole_0(sK4,sK5))
    | ~ r2_hidden(sK1(k4_xboole_0(sK3,sK4),k4_xboole_0(sK3,sK5),k4_xboole_0(sK3,k2_xboole_0(sK4,sK5))),sK3) ),
    inference(instantiation,[status(thm)],[c_1033])).

cnf(c_7837,plain,
    ( r2_hidden(sK1(k4_xboole_0(sK3,sK4),k4_xboole_0(sK3,sK5),k4_xboole_0(sK3,k2_xboole_0(sK4,sK5))),k4_xboole_0(sK3,k2_xboole_0(sK4,sK5))) = iProver_top
    | r2_hidden(sK1(k4_xboole_0(sK3,sK4),k4_xboole_0(sK3,sK5),k4_xboole_0(sK3,k2_xboole_0(sK4,sK5))),k2_xboole_0(sK4,sK5)) = iProver_top
    | r2_hidden(sK1(k4_xboole_0(sK3,sK4),k4_xboole_0(sK3,sK5),k4_xboole_0(sK3,k2_xboole_0(sK4,sK5))),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7836])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_912,plain,
    ( r2_hidden(sK1(k4_xboole_0(sK3,sK4),k4_xboole_0(sK3,sK5),k4_xboole_0(sK3,k2_xboole_0(sK4,sK5))),X0)
    | ~ r2_hidden(sK1(k4_xboole_0(sK3,sK4),k4_xboole_0(sK3,sK5),k4_xboole_0(sK3,k2_xboole_0(sK4,sK5))),k2_xboole_0(X0,sK5))
    | r2_hidden(sK1(k4_xboole_0(sK3,sK4),k4_xboole_0(sK3,sK5),k4_xboole_0(sK3,k2_xboole_0(sK4,sK5))),sK5) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_7175,plain,
    ( ~ r2_hidden(sK1(k4_xboole_0(sK3,sK4),k4_xboole_0(sK3,sK5),k4_xboole_0(sK3,k2_xboole_0(sK4,sK5))),k2_xboole_0(sK4,sK5))
    | r2_hidden(sK1(k4_xboole_0(sK3,sK4),k4_xboole_0(sK3,sK5),k4_xboole_0(sK3,k2_xboole_0(sK4,sK5))),sK5)
    | r2_hidden(sK1(k4_xboole_0(sK3,sK4),k4_xboole_0(sK3,sK5),k4_xboole_0(sK3,k2_xboole_0(sK4,sK5))),sK4) ),
    inference(instantiation,[status(thm)],[c_912])).

cnf(c_7176,plain,
    ( r2_hidden(sK1(k4_xboole_0(sK3,sK4),k4_xboole_0(sK3,sK5),k4_xboole_0(sK3,k2_xboole_0(sK4,sK5))),k2_xboole_0(sK4,sK5)) != iProver_top
    | r2_hidden(sK1(k4_xboole_0(sK3,sK4),k4_xboole_0(sK3,sK5),k4_xboole_0(sK3,k2_xboole_0(sK4,sK5))),sK5) = iProver_top
    | r2_hidden(sK1(k4_xboole_0(sK3,sK4),k4_xboole_0(sK3,sK5),k4_xboole_0(sK3,k2_xboole_0(sK4,sK5))),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7175])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1322,plain,
    ( ~ r2_hidden(sK1(k4_xboole_0(sK3,sK4),k4_xboole_0(sK3,sK5),k4_xboole_0(sK3,k2_xboole_0(sK4,sK5))),k4_xboole_0(sK3,sK4))
    | ~ r2_hidden(sK1(k4_xboole_0(sK3,sK4),k4_xboole_0(sK3,sK5),k4_xboole_0(sK3,k2_xboole_0(sK4,sK5))),sK4) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1323,plain,
    ( r2_hidden(sK1(k4_xboole_0(sK3,sK4),k4_xboole_0(sK3,sK5),k4_xboole_0(sK3,k2_xboole_0(sK4,sK5))),k4_xboole_0(sK3,sK4)) != iProver_top
    | r2_hidden(sK1(k4_xboole_0(sK3,sK4),k4_xboole_0(sK3,sK5),k4_xboole_0(sK3,k2_xboole_0(sK4,sK5))),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1322])).

cnf(c_17,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_585,plain,
    ( ~ r2_hidden(sK1(k4_xboole_0(sK3,sK4),k4_xboole_0(sK3,sK5),k4_xboole_0(sK3,k2_xboole_0(sK4,sK5))),k4_xboole_0(sK3,X0))
    | r2_hidden(sK1(k4_xboole_0(sK3,sK4),k4_xboole_0(sK3,sK5),k4_xboole_0(sK3,k2_xboole_0(sK4,sK5))),sK3) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1314,plain,
    ( ~ r2_hidden(sK1(k4_xboole_0(sK3,sK4),k4_xboole_0(sK3,sK5),k4_xboole_0(sK3,k2_xboole_0(sK4,sK5))),k4_xboole_0(sK3,sK4))
    | r2_hidden(sK1(k4_xboole_0(sK3,sK4),k4_xboole_0(sK3,sK5),k4_xboole_0(sK3,k2_xboole_0(sK4,sK5))),sK3) ),
    inference(instantiation,[status(thm)],[c_585])).

cnf(c_1315,plain,
    ( r2_hidden(sK1(k4_xboole_0(sK3,sK4),k4_xboole_0(sK3,sK5),k4_xboole_0(sK3,k2_xboole_0(sK4,sK5))),k4_xboole_0(sK3,sK4)) != iProver_top
    | r2_hidden(sK1(k4_xboole_0(sK3,sK4),k4_xboole_0(sK3,sK5),k4_xboole_0(sK3,k2_xboole_0(sK4,sK5))),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1314])).

cnf(c_1305,plain,
    ( ~ r2_hidden(sK1(k4_xboole_0(sK3,sK4),k4_xboole_0(sK3,sK5),k4_xboole_0(sK3,k2_xboole_0(sK4,sK5))),k4_xboole_0(sK3,sK5))
    | ~ r2_hidden(sK1(k4_xboole_0(sK3,sK4),k4_xboole_0(sK3,sK5),k4_xboole_0(sK3,k2_xboole_0(sK4,sK5))),sK5) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1306,plain,
    ( r2_hidden(sK1(k4_xboole_0(sK3,sK4),k4_xboole_0(sK3,sK5),k4_xboole_0(sK3,k2_xboole_0(sK4,sK5))),k4_xboole_0(sK3,sK5)) != iProver_top
    | r2_hidden(sK1(k4_xboole_0(sK3,sK4),k4_xboole_0(sK3,sK5),k4_xboole_0(sK3,k2_xboole_0(sK4,sK5))),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1305])).

cnf(c_1010,plain,
    ( ~ r2_hidden(sK1(k4_xboole_0(sK3,sK4),k4_xboole_0(sK3,sK5),k4_xboole_0(sK3,k2_xboole_0(sK4,sK5))),k4_xboole_0(sK3,k2_xboole_0(sK4,sK5)))
    | r2_hidden(sK1(k4_xboole_0(sK3,sK4),k4_xboole_0(sK3,sK5),k4_xboole_0(sK3,k2_xboole_0(sK4,sK5))),sK3) ),
    inference(instantiation,[status(thm)],[c_585])).

cnf(c_1011,plain,
    ( r2_hidden(sK1(k4_xboole_0(sK3,sK4),k4_xboole_0(sK3,sK5),k4_xboole_0(sK3,k2_xboole_0(sK4,sK5))),k4_xboole_0(sK3,k2_xboole_0(sK4,sK5))) != iProver_top
    | r2_hidden(sK1(k4_xboole_0(sK3,sK4),k4_xboole_0(sK3,sK5),k4_xboole_0(sK3,k2_xboole_0(sK4,sK5))),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1010])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_628,plain,
    ( r2_hidden(sK1(k4_xboole_0(sK3,sK4),k4_xboole_0(sK3,sK5),k4_xboole_0(sK3,k2_xboole_0(sK4,sK5))),k2_xboole_0(sK4,sK5))
    | ~ r2_hidden(sK1(k4_xboole_0(sK3,sK4),k4_xboole_0(sK3,sK5),k4_xboole_0(sK3,k2_xboole_0(sK4,sK5))),sK4) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_629,plain,
    ( r2_hidden(sK1(k4_xboole_0(sK3,sK4),k4_xboole_0(sK3,sK5),k4_xboole_0(sK3,k2_xboole_0(sK4,sK5))),k2_xboole_0(sK4,sK5)) = iProver_top
    | r2_hidden(sK1(k4_xboole_0(sK3,sK4),k4_xboole_0(sK3,sK5),k4_xboole_0(sK3,k2_xboole_0(sK4,sK5))),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_628])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_625,plain,
    ( r2_hidden(sK1(k4_xboole_0(sK3,sK4),k4_xboole_0(sK3,sK5),k4_xboole_0(sK3,k2_xboole_0(sK4,sK5))),k2_xboole_0(sK4,sK5))
    | ~ r2_hidden(sK1(k4_xboole_0(sK3,sK4),k4_xboole_0(sK3,sK5),k4_xboole_0(sK3,k2_xboole_0(sK4,sK5))),sK5) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_626,plain,
    ( r2_hidden(sK1(k4_xboole_0(sK3,sK4),k4_xboole_0(sK3,sK5),k4_xboole_0(sK3,k2_xboole_0(sK4,sK5))),k2_xboole_0(sK4,sK5)) = iProver_top
    | r2_hidden(sK1(k4_xboole_0(sK3,sK4),k4_xboole_0(sK3,sK5),k4_xboole_0(sK3,k2_xboole_0(sK4,sK5))),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_625])).

cnf(c_552,plain,
    ( ~ r2_hidden(sK1(k4_xboole_0(sK3,sK4),k4_xboole_0(sK3,sK5),k4_xboole_0(sK3,k2_xboole_0(sK4,sK5))),k4_xboole_0(sK3,k2_xboole_0(sK4,sK5)))
    | ~ r2_hidden(sK1(k4_xboole_0(sK3,sK4),k4_xboole_0(sK3,sK5),k4_xboole_0(sK3,k2_xboole_0(sK4,sK5))),k2_xboole_0(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_553,plain,
    ( r2_hidden(sK1(k4_xboole_0(sK3,sK4),k4_xboole_0(sK3,sK5),k4_xboole_0(sK3,k2_xboole_0(sK4,sK5))),k4_xboole_0(sK3,k2_xboole_0(sK4,sK5))) != iProver_top
    | r2_hidden(sK1(k4_xboole_0(sK3,sK4),k4_xboole_0(sK3,sK5),k4_xboole_0(sK3,k2_xboole_0(sK4,sK5))),k2_xboole_0(sK4,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_552])).

cnf(c_539,plain,
    ( r2_hidden(sK1(k4_xboole_0(sK3,sK4),k4_xboole_0(sK3,sK5),k4_xboole_0(sK3,k2_xboole_0(sK4,sK5))),k4_xboole_0(sK3,sK5))
    | r2_hidden(sK1(k4_xboole_0(sK3,sK4),k4_xboole_0(sK3,sK5),k4_xboole_0(sK3,k2_xboole_0(sK4,sK5))),sK5)
    | ~ r2_hidden(sK1(k4_xboole_0(sK3,sK4),k4_xboole_0(sK3,sK5),k4_xboole_0(sK3,k2_xboole_0(sK4,sK5))),sK3) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_540,plain,
    ( r2_hidden(sK1(k4_xboole_0(sK3,sK4),k4_xboole_0(sK3,sK5),k4_xboole_0(sK3,k2_xboole_0(sK4,sK5))),k4_xboole_0(sK3,sK5)) = iProver_top
    | r2_hidden(sK1(k4_xboole_0(sK3,sK4),k4_xboole_0(sK3,sK5),k4_xboole_0(sK3,k2_xboole_0(sK4,sK5))),sK5) = iProver_top
    | r2_hidden(sK1(k4_xboole_0(sK3,sK4),k4_xboole_0(sK3,sK5),k4_xboole_0(sK3,k2_xboole_0(sK4,sK5))),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_539])).

cnf(c_6,plain,
    ( ~ r2_hidden(sK1(X0,X1,X2),X1)
    | ~ r2_hidden(sK1(X0,X1,X2),X0)
    | ~ r2_hidden(sK1(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_505,plain,
    ( ~ r2_hidden(sK1(k4_xboole_0(sK3,sK4),k4_xboole_0(sK3,sK5),k4_xboole_0(sK3,k2_xboole_0(sK4,sK5))),k4_xboole_0(sK3,k2_xboole_0(sK4,sK5)))
    | ~ r2_hidden(sK1(k4_xboole_0(sK3,sK4),k4_xboole_0(sK3,sK5),k4_xboole_0(sK3,k2_xboole_0(sK4,sK5))),k4_xboole_0(sK3,sK5))
    | ~ r2_hidden(sK1(k4_xboole_0(sK3,sK4),k4_xboole_0(sK3,sK5),k4_xboole_0(sK3,k2_xboole_0(sK4,sK5))),k4_xboole_0(sK3,sK4))
    | k3_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK3,sK5)) = k4_xboole_0(sK3,k2_xboole_0(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_512,plain,
    ( k3_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK3,sK5)) = k4_xboole_0(sK3,k2_xboole_0(sK4,sK5))
    | r2_hidden(sK1(k4_xboole_0(sK3,sK4),k4_xboole_0(sK3,sK5),k4_xboole_0(sK3,k2_xboole_0(sK4,sK5))),k4_xboole_0(sK3,k2_xboole_0(sK4,sK5))) != iProver_top
    | r2_hidden(sK1(k4_xboole_0(sK3,sK4),k4_xboole_0(sK3,sK5),k4_xboole_0(sK3,k2_xboole_0(sK4,sK5))),k4_xboole_0(sK3,sK5)) != iProver_top
    | r2_hidden(sK1(k4_xboole_0(sK3,sK4),k4_xboole_0(sK3,sK5),k4_xboole_0(sK3,k2_xboole_0(sK4,sK5))),k4_xboole_0(sK3,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_505])).

cnf(c_7,plain,
    ( r2_hidden(sK1(X0,X1,X2),X1)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_506,plain,
    ( r2_hidden(sK1(k4_xboole_0(sK3,sK4),k4_xboole_0(sK3,sK5),k4_xboole_0(sK3,k2_xboole_0(sK4,sK5))),k4_xboole_0(sK3,k2_xboole_0(sK4,sK5)))
    | r2_hidden(sK1(k4_xboole_0(sK3,sK4),k4_xboole_0(sK3,sK5),k4_xboole_0(sK3,k2_xboole_0(sK4,sK5))),k4_xboole_0(sK3,sK5))
    | k3_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK3,sK5)) = k4_xboole_0(sK3,k2_xboole_0(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_510,plain,
    ( k3_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK3,sK5)) = k4_xboole_0(sK3,k2_xboole_0(sK4,sK5))
    | r2_hidden(sK1(k4_xboole_0(sK3,sK4),k4_xboole_0(sK3,sK5),k4_xboole_0(sK3,k2_xboole_0(sK4,sK5))),k4_xboole_0(sK3,k2_xboole_0(sK4,sK5))) = iProver_top
    | r2_hidden(sK1(k4_xboole_0(sK3,sK4),k4_xboole_0(sK3,sK5),k4_xboole_0(sK3,k2_xboole_0(sK4,sK5))),k4_xboole_0(sK3,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_506])).

cnf(c_8,plain,
    ( r2_hidden(sK1(X0,X1,X2),X0)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_507,plain,
    ( r2_hidden(sK1(k4_xboole_0(sK3,sK4),k4_xboole_0(sK3,sK5),k4_xboole_0(sK3,k2_xboole_0(sK4,sK5))),k4_xboole_0(sK3,k2_xboole_0(sK4,sK5)))
    | r2_hidden(sK1(k4_xboole_0(sK3,sK4),k4_xboole_0(sK3,sK5),k4_xboole_0(sK3,k2_xboole_0(sK4,sK5))),k4_xboole_0(sK3,sK4))
    | k3_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK3,sK5)) = k4_xboole_0(sK3,k2_xboole_0(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_508,plain,
    ( k3_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK3,sK5)) = k4_xboole_0(sK3,k2_xboole_0(sK4,sK5))
    | r2_hidden(sK1(k4_xboole_0(sK3,sK4),k4_xboole_0(sK3,sK5),k4_xboole_0(sK3,k2_xboole_0(sK4,sK5))),k4_xboole_0(sK3,k2_xboole_0(sK4,sK5))) = iProver_top
    | r2_hidden(sK1(k4_xboole_0(sK3,sK4),k4_xboole_0(sK3,sK5),k4_xboole_0(sK3,k2_xboole_0(sK4,sK5))),k4_xboole_0(sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_507])).

cnf(c_18,negated_conjecture,
    ( k3_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK3,sK5)) != k4_xboole_0(sK3,k2_xboole_0(sK4,sK5)) ),
    inference(cnf_transformation,[],[f42])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7860,c_7837,c_7176,c_1323,c_1315,c_1306,c_1011,c_629,c_626,c_553,c_540,c_512,c_510,c_508,c_18])).


%------------------------------------------------------------------------------
