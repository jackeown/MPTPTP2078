%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0059+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:22 EST 2020

% Result     : Theorem 3.02s
% Output     : CNFRefutation 3.02s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 692 expanded)
%              Number of clauses        :   41 ( 163 expanded)
%              Number of leaves         :   10 ( 150 expanded)
%              Depth                    :   18
%              Number of atoms          :  369 (4967 expanded)
%              Number of equality atoms :   56 ( 730 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f4,conjecture,(
    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(negated_conjecture,[],[f4])).

fof(f6,plain,(
    ? [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) != k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(ennf_transformation,[],[f5])).

fof(f22,plain,
    ( ? [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) != k4_xboole_0(X0,k4_xboole_0(X1,X2))
   => k2_xboole_0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5)) != k4_xboole_0(sK3,k4_xboole_0(sK4,sK5)) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    k2_xboole_0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5)) != k4_xboole_0(sK3,k4_xboole_0(sK4,sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f6,f22])).

fof(f42,plain,(
    k2_xboole_0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5)) != k4_xboole_0(sK3,k4_xboole_0(sK4,sK5)) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X1)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f32,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f46,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f32])).

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

fof(f30,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f48,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f30])).

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

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f31,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f47,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f31])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(sK0(X0,X1,X2),X0)
    | k2_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_18,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5)) != k4_xboole_0(sK3,k4_xboole_0(sK4,sK5)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_5599,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5),k4_xboole_0(sK3,k4_xboole_0(sK4,sK5))),k4_xboole_0(sK3,k4_xboole_0(sK4,sK5)))
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5),k4_xboole_0(sK3,k4_xboole_0(sK4,sK5))),k4_xboole_0(sK3,sK4))
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5),k4_xboole_0(sK3,k4_xboole_0(sK4,sK5))),k3_xboole_0(sK3,sK5)) ),
    inference(resolution,[status(thm)],[c_2,c_18])).

cnf(c_202,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_199,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1997,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_202,c_199])).

cnf(c_7,plain,
    ( r2_hidden(sK1(X0,X1,X2),X1)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_984,plain,
    ( r2_hidden(sK1(X0,X1,X1),X1)
    | k3_xboole_0(X0,X1) = X1 ),
    inference(factoring,[status(thm)],[c_7])).

cnf(c_2016,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK1(X2,X0,X0),X0)
    | r2_hidden(k3_xboole_0(X2,X0),X1) ),
    inference(resolution,[status(thm)],[c_1997,c_984])).

cnf(c_17,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2044,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(X1,X2))
    | r2_hidden(sK1(X3,X0,X0),X0)
    | r2_hidden(k3_xboole_0(X3,X0),X1) ),
    inference(resolution,[status(thm)],[c_2016,c_17])).

cnf(c_6086,plain,
    ( r2_hidden(sK1(X0,sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5),k4_xboole_0(sK3,k4_xboole_0(sK4,sK5))),sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5),k4_xboole_0(sK3,k4_xboole_0(sK4,sK5)))),sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5),k4_xboole_0(sK3,k4_xboole_0(sK4,sK5))))
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5),k4_xboole_0(sK3,k4_xboole_0(sK4,sK5))),k4_xboole_0(sK3,sK4))
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5),k4_xboole_0(sK3,k4_xboole_0(sK4,sK5))),k3_xboole_0(sK3,sK5))
    | r2_hidden(k3_xboole_0(X0,sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5),k4_xboole_0(sK3,k4_xboole_0(sK4,sK5)))),sK3) ),
    inference(resolution,[status(thm)],[c_5599,c_2044])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_821,plain,
    ( ~ r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5),k4_xboole_0(sK3,k4_xboole_0(sK4,sK5))),X0)
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5),k4_xboole_0(sK3,k4_xboole_0(sK4,sK5))),k3_xboole_0(sK3,X0))
    | ~ r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5),k4_xboole_0(sK3,k4_xboole_0(sK4,sK5))),sK3) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2666,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5),k4_xboole_0(sK3,k4_xboole_0(sK4,sK5))),k3_xboole_0(sK3,sK5))
    | ~ r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5),k4_xboole_0(sK3,k4_xboole_0(sK4,sK5))),sK5)
    | ~ r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5),k4_xboole_0(sK3,k4_xboole_0(sK4,sK5))),sK3) ),
    inference(instantiation,[status(thm)],[c_821])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_801,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5),k4_xboole_0(sK3,k4_xboole_0(sK4,sK5))),X0)
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5),k4_xboole_0(sK3,k4_xboole_0(sK4,sK5))),k4_xboole_0(sK3,X0))
    | ~ r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5),k4_xboole_0(sK3,k4_xboole_0(sK4,sK5))),sK3) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_3960,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5),k4_xboole_0(sK3,k4_xboole_0(sK4,sK5))),k4_xboole_0(sK3,sK4))
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5),k4_xboole_0(sK3,k4_xboole_0(sK4,sK5))),sK4)
    | ~ r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5),k4_xboole_0(sK3,k4_xboole_0(sK4,sK5))),sK3) ),
    inference(instantiation,[status(thm)],[c_801])).

cnf(c_6085,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5),k4_xboole_0(sK3,k4_xboole_0(sK4,sK5))),k4_xboole_0(sK3,sK4))
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5),k4_xboole_0(sK3,k4_xboole_0(sK4,sK5))),k3_xboole_0(sK3,sK5))
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5),k4_xboole_0(sK3,k4_xboole_0(sK4,sK5))),sK3) ),
    inference(resolution,[status(thm)],[c_5599,c_17])).

cnf(c_859,plain,
    ( ~ r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5),k4_xboole_0(sK3,k4_xboole_0(sK4,sK5))),k4_xboole_0(sK3,sK4))
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5),k4_xboole_0(sK3,k4_xboole_0(sK4,sK5))),sK3) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_11,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_909,plain,
    ( ~ r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5),k4_xboole_0(sK3,k4_xboole_0(sK4,sK5))),k3_xboole_0(sK3,sK5))
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5),k4_xboole_0(sK3,k4_xboole_0(sK4,sK5))),sK3) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_6092,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5),k4_xboole_0(sK3,k4_xboole_0(sK4,sK5))),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6085,c_859,c_909])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_6083,plain,
    ( ~ r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5),k4_xboole_0(sK3,k4_xboole_0(sK4,sK5))),k4_xboole_0(sK4,sK5))
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5),k4_xboole_0(sK3,k4_xboole_0(sK4,sK5))),k4_xboole_0(sK3,sK4))
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5),k4_xboole_0(sK3,k4_xboole_0(sK4,sK5))),k3_xboole_0(sK3,sK5)) ),
    inference(resolution,[status(thm)],[c_5599,c_16])).

cnf(c_6543,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5),k4_xboole_0(sK3,k4_xboole_0(sK4,sK5))),k4_xboole_0(sK3,sK4))
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5),k4_xboole_0(sK3,k4_xboole_0(sK4,sK5))),k3_xboole_0(sK3,sK5))
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5),k4_xboole_0(sK3,k4_xboole_0(sK4,sK5))),sK5)
    | ~ r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5),k4_xboole_0(sK3,k4_xboole_0(sK4,sK5))),sK4) ),
    inference(resolution,[status(thm)],[c_6083,c_15])).

cnf(c_6546,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5),k4_xboole_0(sK3,k4_xboole_0(sK4,sK5))),k3_xboole_0(sK3,sK5))
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5),k4_xboole_0(sK3,k4_xboole_0(sK4,sK5))),k4_xboole_0(sK3,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6086,c_859,c_909,c_2666,c_3960,c_6085,c_6543])).

cnf(c_6547,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5),k4_xboole_0(sK3,k4_xboole_0(sK4,sK5))),k4_xboole_0(sK3,sK4))
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5),k4_xboole_0(sK3,k4_xboole_0(sK4,sK5))),k3_xboole_0(sK3,sK5)) ),
    inference(renaming,[status(thm)],[c_6546])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X2)
    | ~ r2_hidden(sK0(X0,X1,X2),X0)
    | k2_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_6562,plain,
    ( ~ r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5),k4_xboole_0(sK3,k4_xboole_0(sK4,sK5))),k4_xboole_0(sK3,k4_xboole_0(sK4,sK5)))
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5),k4_xboole_0(sK3,k4_xboole_0(sK4,sK5))),k3_xboole_0(sK3,sK5))
    | k2_xboole_0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5)) = k4_xboole_0(sK3,k4_xboole_0(sK4,sK5)) ),
    inference(resolution,[status(thm)],[c_6547,c_1])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | k2_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_734,plain,
    ( ~ r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5),k4_xboole_0(sK3,k4_xboole_0(sK4,sK5))),k4_xboole_0(sK3,k4_xboole_0(sK4,sK5)))
    | ~ r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5),k4_xboole_0(sK3,k4_xboole_0(sK4,sK5))),k3_xboole_0(sK3,sK5))
    | k2_xboole_0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5)) = k4_xboole_0(sK3,k4_xboole_0(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_6921,plain,
    ( ~ r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5),k4_xboole_0(sK3,k4_xboole_0(sK4,sK5))),k4_xboole_0(sK3,k4_xboole_0(sK4,sK5))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6562,c_18,c_734])).

cnf(c_6934,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5),k4_xboole_0(sK3,k4_xboole_0(sK4,sK5))),k4_xboole_0(sK4,sK5))
    | ~ r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5),k4_xboole_0(sK3,k4_xboole_0(sK4,sK5))),sK3) ),
    inference(resolution,[status(thm)],[c_6921,c_15])).

cnf(c_7274,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5),k4_xboole_0(sK3,k4_xboole_0(sK4,sK5))),k4_xboole_0(sK4,sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6934,c_859,c_909,c_6085])).

cnf(c_7777,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5),k4_xboole_0(sK3,k4_xboole_0(sK4,sK5))),sK4) ),
    inference(resolution,[status(thm)],[c_7274,c_17])).

cnf(c_7775,plain,
    ( ~ r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5),k4_xboole_0(sK3,k4_xboole_0(sK4,sK5))),sK5) ),
    inference(resolution,[status(thm)],[c_7274,c_16])).

cnf(c_6564,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5),k4_xboole_0(sK3,k4_xboole_0(sK4,sK5))),k3_xboole_0(sK3,sK5))
    | ~ r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5),k4_xboole_0(sK3,k4_xboole_0(sK4,sK5))),sK4) ),
    inference(resolution,[status(thm)],[c_6547,c_16])).

cnf(c_10,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_6909,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5),k4_xboole_0(sK3,k4_xboole_0(sK4,sK5))),sK5)
    | ~ r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK5),k4_xboole_0(sK3,k4_xboole_0(sK4,sK5))),sK4) ),
    inference(resolution,[status(thm)],[c_6564,c_10])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7777,c_7775,c_6909])).


%------------------------------------------------------------------------------
