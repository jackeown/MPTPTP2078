%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0124+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:32 EST 2020

% Result     : Theorem 3.32s
% Output     : CNFRefutation 3.32s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 602 expanded)
%              Number of clauses        :   38 ( 155 expanded)
%              Number of leaves         :    9 ( 120 expanded)
%              Depth                    :   15
%              Number of atoms          :  378 (4221 expanded)
%              Number of equality atoms :   52 ( 578 expanded)
%              Maximal formula depth    :   11 (   6 average)
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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

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
    inference(flattening,[],[f10])).

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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f11])).

fof(f13,plain,(
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

fof(f14,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f13])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X2,X1)
     => k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X2,X1)
       => k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) != k4_xboole_0(X0,X2)
      & r1_tarski(X2,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,
    ( ? [X0,X1,X2] :
        ( k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) != k4_xboole_0(X0,X2)
        & r1_tarski(X2,X1) )
   => ( k2_xboole_0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,k4_xboole_0(sK4,sK5))) != k4_xboole_0(sK3,sK5)
      & r1_tarski(sK5,sK4) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( k2_xboole_0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,k4_xboole_0(sK4,sK5))) != k4_xboole_0(sK3,sK5)
    & r1_tarski(sK5,sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f9,f25])).

fof(f47,plain,(
    k2_xboole_0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,k4_xboole_0(sK4,sK5))) != k4_xboole_0(sK3,sK5) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f23,plain,(
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

fof(f24,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f22,f23])).

fof(f40,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f56,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f40])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f46,plain,(
    r1_tarski(sK5,sK4) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
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
    inference(flattening,[],[f15])).

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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f16])).

fof(f18,plain,(
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

fof(f19,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f17,f18])).

fof(f36,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f51,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f36])).

fof(f42,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f54,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f41,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f55,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f41])).

fof(f35,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f52,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f35])).

fof(f34,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f53,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f34])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(sK0(X0,X1,X2),X0)
    | k2_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_19,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,k4_xboole_0(sK4,sK5))) != k4_xboole_0(sK3,sK5) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_11914,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,k4_xboole_0(sK4,sK5)),k4_xboole_0(sK3,sK5)),k4_xboole_0(sK3,sK5))
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,k4_xboole_0(sK4,sK5)),k4_xboole_0(sK3,sK5)),k4_xboole_0(sK3,sK4))
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,k4_xboole_0(sK4,sK5)),k4_xboole_0(sK3,sK5)),k3_xboole_0(sK3,k4_xboole_0(sK4,sK5))) ),
    inference(resolution,[status(thm)],[c_3,c_19])).

cnf(c_906,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,k4_xboole_0(sK4,sK5)),k4_xboole_0(sK3,sK5)),k4_xboole_0(sK3,sK5))
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,k4_xboole_0(sK4,sK5)),k4_xboole_0(sK3,sK5)),k4_xboole_0(sK3,sK4))
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,k4_xboole_0(sK4,sK5)),k4_xboole_0(sK3,sK5)),k3_xboole_0(sK3,k4_xboole_0(sK4,sK5)))
    | k2_xboole_0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,k4_xboole_0(sK4,sK5))) = k4_xboole_0(sK3,sK5) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_18,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_953,plain,
    ( ~ r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,k4_xboole_0(sK4,sK5)),k4_xboole_0(sK3,sK5)),k4_xboole_0(sK3,sK5))
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,k4_xboole_0(sK4,sK5)),k4_xboole_0(sK3,sK5)),sK3) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_2,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X2)
    | ~ r2_hidden(sK0(X0,X1,X2),X0)
    | k2_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_1015,plain,
    ( ~ r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,k4_xboole_0(sK4,sK5)),k4_xboole_0(sK3,sK5)),k4_xboole_0(sK3,sK5))
    | ~ r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,k4_xboole_0(sK4,sK5)),k4_xboole_0(sK3,sK5)),k4_xboole_0(sK3,sK4))
    | k2_xboole_0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,k4_xboole_0(sK4,sK5))) = k4_xboole_0(sK3,sK5) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1043,plain,
    ( ~ r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,k4_xboole_0(sK4,sK5)),k4_xboole_0(sK3,sK5)),k4_xboole_0(sK3,sK4))
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,k4_xboole_0(sK4,sK5)),k4_xboole_0(sK3,sK5)),sK3) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_20,negated_conjecture,
    ( r1_tarski(sK5,sK4) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_217,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | sK5 != X1
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_20])).

cnf(c_218,plain,
    ( ~ r2_hidden(X0,sK5)
    | r2_hidden(X0,sK4) ),
    inference(unflattening,[status(thm)],[c_217])).

cnf(c_1818,plain,
    ( ~ r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,k4_xboole_0(sK4,sK5)),k4_xboole_0(sK3,sK5)),sK5)
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,k4_xboole_0(sK4,sK5)),k4_xboole_0(sK3,sK5)),sK4) ),
    inference(instantiation,[status(thm)],[c_218])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_984,plain,
    ( ~ r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,k4_xboole_0(sK4,sK5)),k4_xboole_0(sK3,sK5)),X0)
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,k4_xboole_0(sK4,sK5)),k4_xboole_0(sK3,sK5)),k3_xboole_0(sK3,X0))
    | ~ r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,k4_xboole_0(sK4,sK5)),k4_xboole_0(sK3,sK5)),sK3) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2792,plain,
    ( ~ r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,k4_xboole_0(sK4,sK5)),k4_xboole_0(sK3,sK5)),k4_xboole_0(sK4,sK5))
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,k4_xboole_0(sK4,sK5)),k4_xboole_0(sK3,sK5)),k3_xboole_0(sK3,k4_xboole_0(sK4,sK5)))
    | ~ r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,k4_xboole_0(sK4,sK5)),k4_xboole_0(sK3,sK5)),sK3) ),
    inference(instantiation,[status(thm)],[c_984])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_990,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,k4_xboole_0(sK4,sK5)),k4_xboole_0(sK3,sK5)),X0)
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,k4_xboole_0(sK4,sK5)),k4_xboole_0(sK3,sK5)),k4_xboole_0(sK3,X0))
    | ~ r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,k4_xboole_0(sK4,sK5)),k4_xboole_0(sK3,sK5)),sK3) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_2844,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,k4_xboole_0(sK4,sK5)),k4_xboole_0(sK3,sK5)),k4_xboole_0(sK3,sK5))
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,k4_xboole_0(sK4,sK5)),k4_xboole_0(sK3,sK5)),sK5)
    | ~ r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,k4_xboole_0(sK4,sK5)),k4_xboole_0(sK3,sK5)),sK3) ),
    inference(instantiation,[status(thm)],[c_990])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1773,plain,
    ( ~ r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,k4_xboole_0(sK4,sK5)),k4_xboole_0(sK3,sK5)),X0)
    | ~ r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,k4_xboole_0(sK4,sK5)),k4_xboole_0(sK3,sK5)),k4_xboole_0(X1,X0)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_3586,plain,
    ( ~ r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,k4_xboole_0(sK4,sK5)),k4_xboole_0(sK3,sK5)),k4_xboole_0(sK3,sK4))
    | ~ r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,k4_xboole_0(sK4,sK5)),k4_xboole_0(sK3,sK5)),sK4) ),
    inference(instantiation,[status(thm)],[c_1773])).

cnf(c_4493,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,k4_xboole_0(sK4,sK5)),k4_xboole_0(sK3,sK5)),k4_xboole_0(sK3,sK4))
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,k4_xboole_0(sK4,sK5)),k4_xboole_0(sK3,sK5)),sK4)
    | ~ r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,k4_xboole_0(sK4,sK5)),k4_xboole_0(sK3,sK5)),sK3) ),
    inference(instantiation,[status(thm)],[c_990])).

cnf(c_4797,plain,
    ( ~ r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,k4_xboole_0(sK4,sK5)),k4_xboole_0(sK3,sK5)),k4_xboole_0(sK3,sK5))
    | ~ r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,k4_xboole_0(sK4,sK5)),k4_xboole_0(sK3,sK5)),sK5) ),
    inference(instantiation,[status(thm)],[c_1773])).

cnf(c_1772,plain,
    ( ~ r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,k4_xboole_0(sK4,sK5)),k4_xboole_0(sK3,sK5)),X0)
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,k4_xboole_0(sK4,sK5)),k4_xboole_0(sK3,sK5)),X1)
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,k4_xboole_0(sK4,sK5)),k4_xboole_0(sK3,sK5)),k4_xboole_0(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_4004,plain,
    ( ~ r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,k4_xboole_0(sK4,sK5)),k4_xboole_0(sK3,sK5)),X0)
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,k4_xboole_0(sK4,sK5)),k4_xboole_0(sK3,sK5)),k4_xboole_0(X0,sK5))
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,k4_xboole_0(sK4,sK5)),k4_xboole_0(sK3,sK5)),sK5) ),
    inference(instantiation,[status(thm)],[c_1772])).

cnf(c_11106,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,k4_xboole_0(sK4,sK5)),k4_xboole_0(sK3,sK5)),k4_xboole_0(sK4,sK5))
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,k4_xboole_0(sK4,sK5)),k4_xboole_0(sK3,sK5)),sK5)
    | ~ r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,k4_xboole_0(sK4,sK5)),k4_xboole_0(sK3,sK5)),sK4) ),
    inference(instantiation,[status(thm)],[c_4004])).

cnf(c_12769,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,k4_xboole_0(sK4,sK5)),k4_xboole_0(sK3,sK5)),k4_xboole_0(sK3,sK4))
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,k4_xboole_0(sK4,sK5)),k4_xboole_0(sK3,sK5)),k3_xboole_0(sK3,k4_xboole_0(sK4,sK5))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11914,c_19,c_906,c_953,c_1015,c_1043,c_1818,c_2792,c_2844,c_3586,c_4493,c_4797,c_11106])).

cnf(c_12773,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,k4_xboole_0(sK4,sK5)),k4_xboole_0(sK3,sK5)),k3_xboole_0(sK3,k4_xboole_0(sK4,sK5))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12769,c_19,c_906,c_953,c_1015,c_1043,c_1818,c_2792,c_2844,c_3586,c_4493,c_4797,c_11106])).

cnf(c_11,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_12785,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,k4_xboole_0(sK4,sK5)),k4_xboole_0(sK3,sK5)),k4_xboole_0(sK4,sK5)) ),
    inference(resolution,[status(thm)],[c_12773,c_11])).

cnf(c_13043,plain,
    ( ~ r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,k4_xboole_0(sK4,sK5)),k4_xboole_0(sK3,sK5)),sK5) ),
    inference(resolution,[status(thm)],[c_12785,c_17])).

cnf(c_12,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1093,plain,
    ( ~ r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,k4_xboole_0(sK4,sK5)),k4_xboole_0(sK3,sK5)),k3_xboole_0(sK3,k4_xboole_0(sK4,sK5)))
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,k4_xboole_0(sK4,sK5)),k4_xboole_0(sK3,sK5)),sK3) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | k2_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_925,plain,
    ( ~ r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,k4_xboole_0(sK4,sK5)),k4_xboole_0(sK3,sK5)),k4_xboole_0(sK3,sK5))
    | ~ r2_hidden(sK0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,k4_xboole_0(sK4,sK5)),k4_xboole_0(sK3,sK5)),k3_xboole_0(sK3,k4_xboole_0(sK4,sK5)))
    | k2_xboole_0(k4_xboole_0(sK3,sK4),k3_xboole_0(sK3,k4_xboole_0(sK4,sK5))) = k4_xboole_0(sK3,sK5) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13043,c_12773,c_2844,c_1093,c_925,c_19])).


%------------------------------------------------------------------------------
