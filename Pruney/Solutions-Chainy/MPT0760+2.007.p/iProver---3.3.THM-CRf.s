%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:54:15 EST 2020

% Result     : Theorem 3.58s
% Output     : CNFRefutation 3.58s
% Verified   : 
% Statistics : Number of formulae       :   74 (  94 expanded)
%              Number of clauses        :   32 (  33 expanded)
%              Number of leaves         :   15 (  21 expanded)
%              Depth                    :   15
%              Number of atoms          :  314 ( 379 expanded)
%              Number of equality atoms :  105 ( 126 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   15 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3 )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | ~ r2_hidden(X3,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3 )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | ~ r2_hidden(X3,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f39])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k4_tarski(X4,X1),X0)
                  | X1 = X4 )
                & ( ( r2_hidden(k4_tarski(X4,X1),X0)
                    & X1 != X4 )
                  | ~ r2_hidden(X4,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f40])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
            | X1 = X3
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(k4_tarski(X3,X1),X0)
              & X1 != X3 )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK5(X0,X1,X2),X1),X0)
          | sK5(X0,X1,X2) = X1
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ( r2_hidden(k4_tarski(sK5(X0,X1,X2),X1),X0)
            & sK5(X0,X1,X2) != X1 )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ( ( ~ r2_hidden(k4_tarski(sK5(X0,X1,X2),X1),X0)
                | sK5(X0,X1,X2) = X1
                | ~ r2_hidden(sK5(X0,X1,X2),X2) )
              & ( ( r2_hidden(k4_tarski(sK5(X0,X1,X2),X1),X0)
                  & sK5(X0,X1,X2) != X1 )
                | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k4_tarski(X4,X1),X0)
                  | X1 = X4 )
                & ( ( r2_hidden(k4_tarski(X4,X1),X0)
                    & X1 != X4 )
                  | ~ r2_hidden(X4,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f41,f42])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k1_wellord1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK5(X0,X1,X2),X1),X0)
      | r2_hidden(sK5(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k1_wellord1(X1,X0)
        | r2_hidden(X0,k3_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k1_wellord1(X1,X0)
          | r2_hidden(X0,k3_relat_1(X1)) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f21,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 != k1_wellord1(X1,X0)
      & ~ r2_hidden(X0,k3_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f22,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 != k1_wellord1(X1,X0)
      & ~ r2_hidden(X0,k3_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f44,plain,
    ( ? [X0,X1] :
        ( k1_xboole_0 != k1_wellord1(X1,X0)
        & ~ r2_hidden(X0,k3_relat_1(X1))
        & v1_relat_1(X1) )
   => ( k1_xboole_0 != k1_wellord1(sK7,sK6)
      & ~ r2_hidden(sK6,k3_relat_1(sK7))
      & v1_relat_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( k1_xboole_0 != k1_wellord1(sK7,sK6)
    & ~ r2_hidden(sK6,k3_relat_1(sK7))
    & v1_relat_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f22,f44])).

fof(f79,plain,(
    v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f45])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f14,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f37,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK4(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK3(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK2(X0,X1)),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK2(X0,X1)),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK2(X0,X1)),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK4(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f34,f37,f36,f35])).

fof(f68,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f101,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X6,X5),X0) ) ),
    inference(equality_resolution,[],[f68])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f71,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
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

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f25,plain,(
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
    inference(rectify,[],[f24])).

fof(f26,plain,(
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

fof(f27,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).

fof(f48,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f95,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f48])).

fof(f80,plain,(
    ~ r2_hidden(sK6,k3_relat_1(sK7)) ),
    inference(cnf_transformation,[],[f45])).

fof(f81,plain,(
    k1_xboole_0 != k1_wellord1(sK7,sK6) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_21,plain,
    ( r2_hidden(sK5(X0,X1,X2),X2)
    | r2_hidden(k4_tarski(sK5(X0,X1,X2),X1),X0)
    | ~ v1_relat_1(X0)
    | k1_wellord1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_28,negated_conjecture,
    ( v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_329,plain,
    ( r2_hidden(sK5(X0,X1,X2),X2)
    | r2_hidden(k4_tarski(sK5(X0,X1,X2),X1),X0)
    | k1_wellord1(X0,X1) = X2
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_28])).

cnf(c_330,plain,
    ( r2_hidden(sK5(sK7,X0,X1),X1)
    | r2_hidden(k4_tarski(sK5(sK7,X0,X1),X0),sK7)
    | k1_wellord1(sK7,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_329])).

cnf(c_9664,plain,
    ( k1_wellord1(sK7,X0) = X1
    | r2_hidden(sK5(sK7,X0,X1),X1) = iProver_top
    | r2_hidden(k4_tarski(sK5(sK7,X0,X1),X0),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_330])).

cnf(c_13,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_19,negated_conjecture,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_303,plain,
    ( ~ r2_hidden(X0,X1)
    | X0 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_19])).

cnf(c_304,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_303])).

cnf(c_9666,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_304])).

cnf(c_10049,plain,
    ( k1_wellord1(sK7,X0) = k1_xboole_0
    | r2_hidden(k4_tarski(sK5(sK7,X0,k1_xboole_0),X0),sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_9664,c_9666])).

cnf(c_16,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_9669,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_10628,plain,
    ( k1_wellord1(sK7,X0) = k1_xboole_0
    | r2_hidden(X0,k2_relat_1(sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_10049,c_9669])).

cnf(c_18,plain,
    ( ~ v1_relat_1(X0)
    | k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_362,plain,
    ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_28])).

cnf(c_363,plain,
    ( k2_xboole_0(k1_relat_1(sK7),k2_relat_1(sK7)) = k3_relat_1(sK7) ),
    inference(unflattening,[status(thm)],[c_362])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_9672,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k2_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_9886,plain,
    ( r2_hidden(X0,k3_relat_1(sK7)) = iProver_top
    | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_363,c_9672])).

cnf(c_11237,plain,
    ( k1_wellord1(sK7,X0) = k1_xboole_0
    | r2_hidden(X0,k3_relat_1(sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_10628,c_9886])).

cnf(c_27,negated_conjecture,
    ( ~ r2_hidden(sK6,k3_relat_1(sK7)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_9668,plain,
    ( r2_hidden(sK6,k3_relat_1(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_11587,plain,
    ( k1_wellord1(sK7,sK6) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_11237,c_9668])).

cnf(c_590,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_5574,plain,
    ( X0 != X1
    | X0 = k1_wellord1(sK7,X2)
    | k1_wellord1(sK7,X2) != X1 ),
    inference(instantiation,[status(thm)],[c_590])).

cnf(c_6228,plain,
    ( k1_wellord1(sK7,sK6) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k1_wellord1(sK7,sK6) ),
    inference(instantiation,[status(thm)],[c_5574])).

cnf(c_6229,plain,
    ( k1_wellord1(sK7,sK6) != k1_xboole_0
    | k1_xboole_0 = k1_wellord1(sK7,sK6)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6228])).

cnf(c_589,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_612,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_589])).

cnf(c_26,negated_conjecture,
    ( k1_xboole_0 != k1_wellord1(sK7,sK6) ),
    inference(cnf_transformation,[],[f81])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11587,c_6229,c_612,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:04:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.58/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.58/0.99  
% 3.58/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.58/0.99  
% 3.58/0.99  ------  iProver source info
% 3.58/0.99  
% 3.58/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.58/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.58/0.99  git: non_committed_changes: false
% 3.58/0.99  git: last_make_outside_of_git: false
% 3.58/0.99  
% 3.58/0.99  ------ 
% 3.58/0.99  ------ Parsing...
% 3.58/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.58/0.99  
% 3.58/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.58/0.99  
% 3.58/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.58/0.99  
% 3.58/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.58/0.99  ------ Proving...
% 3.58/0.99  ------ Problem Properties 
% 3.58/0.99  
% 3.58/0.99  
% 3.58/0.99  clauses                                 27
% 3.58/0.99  conjectures                             2
% 3.58/0.99  EPR                                     1
% 3.58/0.99  Horn                                    18
% 3.58/0.99  unary                                   6
% 3.58/0.99  binary                                  7
% 3.58/0.99  lits                                    65
% 3.58/0.99  lits eq                                 17
% 3.58/0.99  fd_pure                                 0
% 3.58/0.99  fd_pseudo                               0
% 3.58/0.99  fd_cond                                 0
% 3.58/0.99  fd_pseudo_cond                          11
% 3.58/0.99  AC symbols                              0
% 3.58/0.99  
% 3.58/0.99  ------ Input Options Time Limit: Unbounded
% 3.58/0.99  
% 3.58/0.99  
% 3.58/0.99  
% 3.58/0.99  
% 3.58/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 3.58/0.99  Current options:
% 3.58/0.99  ------ 
% 3.58/0.99  
% 3.58/0.99  
% 3.58/0.99  
% 3.58/0.99  
% 3.58/0.99  ------ Proving...
% 3.58/0.99  
% 3.58/0.99  
% 3.58/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.58/0.99  
% 3.58/0.99  ------ Proving...
% 3.58/0.99  
% 3.58/0.99  
% 3.58/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.58/0.99  
% 3.58/0.99  ------ Proving...
% 3.58/0.99  
% 3.58/0.99  
% 3.58/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.58/0.99  
% 3.58/0.99  ------ Proving...
% 3.58/0.99  
% 3.58/0.99  
% 3.58/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.58/0.99  
% 3.58/0.99  ------ Proving...
% 3.58/0.99  
% 3.58/0.99  
% 3.58/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.58/0.99  
% 3.58/0.99  ------ Proving...
% 3.58/0.99  
% 3.58/0.99  
% 3.58/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.58/0.99  
% 3.58/0.99  ------ Proving...
% 3.58/0.99  
% 3.58/0.99  
% 3.58/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.58/0.99  
% 3.58/0.99  ------ Proving...
% 3.58/0.99  
% 3.58/0.99  
% 3.58/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.58/0.99  
% 3.58/0.99  ------ Proving...
% 3.58/0.99  
% 3.58/0.99  
% 3.58/0.99  ------ Preprocessing... sf_s  rm: 8 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.58/0.99  
% 3.58/0.99  ------ Proving...
% 3.58/0.99  
% 3.58/0.99  
% 3.58/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.58/0.99  
% 3.58/0.99  ------ Proving...
% 3.58/0.99  
% 3.58/0.99  
% 3.58/0.99  ------ Preprocessing... sf_s  rm: 7 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.58/0.99  
% 3.58/0.99  ------ Proving...
% 3.58/0.99  
% 3.58/0.99  
% 3.58/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.58/0.99  
% 3.58/0.99  ------ Proving...
% 3.58/0.99  
% 3.58/0.99  
% 3.58/0.99  % SZS status Theorem for theBenchmark.p
% 3.58/0.99  
% 3.58/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.58/0.99  
% 3.58/0.99  fof(f15,axiom,(
% 3.58/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))))),
% 3.58/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.58/0.99  
% 3.58/0.99  fof(f20,plain,(
% 3.58/0.99    ! [X0] : (! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))) | ~v1_relat_1(X0))),
% 3.58/0.99    inference(ennf_transformation,[],[f15])).
% 3.58/0.99  
% 3.58/0.99  fof(f39,plain,(
% 3.58/0.99    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : (((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3) | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | ~r2_hidden(X3,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 3.58/0.99    inference(nnf_transformation,[],[f20])).
% 3.58/0.99  
% 3.58/0.99  fof(f40,plain,(
% 3.58/0.99    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | ~r2_hidden(X3,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 3.58/0.99    inference(flattening,[],[f39])).
% 3.58/0.99  
% 3.58/0.99  fof(f41,plain,(
% 3.58/0.99    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4) & ((r2_hidden(k4_tarski(X4,X1),X0) & X1 != X4) | ~r2_hidden(X4,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 3.58/0.99    inference(rectify,[],[f40])).
% 3.58/0.99  
% 3.58/0.99  fof(f42,plain,(
% 3.58/0.99    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2))) => ((~r2_hidden(k4_tarski(sK5(X0,X1,X2),X1),X0) | sK5(X0,X1,X2) = X1 | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((r2_hidden(k4_tarski(sK5(X0,X1,X2),X1),X0) & sK5(X0,X1,X2) != X1) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 3.58/0.99    introduced(choice_axiom,[])).
% 3.58/0.99  
% 3.58/0.99  fof(f43,plain,(
% 3.58/0.99    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ((~r2_hidden(k4_tarski(sK5(X0,X1,X2),X1),X0) | sK5(X0,X1,X2) = X1 | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((r2_hidden(k4_tarski(sK5(X0,X1,X2),X1),X0) & sK5(X0,X1,X2) != X1) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4) & ((r2_hidden(k4_tarski(X4,X1),X0) & X1 != X4) | ~r2_hidden(X4,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 3.58/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f41,f42])).
% 3.58/0.99  
% 3.58/0.99  fof(f77,plain,(
% 3.58/0.99    ( ! [X2,X0,X1] : (k1_wellord1(X0,X1) = X2 | r2_hidden(k4_tarski(sK5(X0,X1,X2),X1),X0) | r2_hidden(sK5(X0,X1,X2),X2) | ~v1_relat_1(X0)) )),
% 3.58/0.99    inference(cnf_transformation,[],[f43])).
% 3.58/0.99  
% 3.58/0.99  fof(f16,conjecture,(
% 3.58/0.99    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k1_wellord1(X1,X0) | r2_hidden(X0,k3_relat_1(X1))))),
% 3.58/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.58/0.99  
% 3.58/0.99  fof(f17,negated_conjecture,(
% 3.58/0.99    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k1_wellord1(X1,X0) | r2_hidden(X0,k3_relat_1(X1))))),
% 3.58/0.99    inference(negated_conjecture,[],[f16])).
% 3.58/0.99  
% 3.58/0.99  fof(f21,plain,(
% 3.58/0.99    ? [X0,X1] : ((k1_xboole_0 != k1_wellord1(X1,X0) & ~r2_hidden(X0,k3_relat_1(X1))) & v1_relat_1(X1))),
% 3.58/0.99    inference(ennf_transformation,[],[f17])).
% 3.58/0.99  
% 3.58/0.99  fof(f22,plain,(
% 3.58/0.99    ? [X0,X1] : (k1_xboole_0 != k1_wellord1(X1,X0) & ~r2_hidden(X0,k3_relat_1(X1)) & v1_relat_1(X1))),
% 3.58/0.99    inference(flattening,[],[f21])).
% 3.58/0.99  
% 3.58/0.99  fof(f44,plain,(
% 3.58/0.99    ? [X0,X1] : (k1_xboole_0 != k1_wellord1(X1,X0) & ~r2_hidden(X0,k3_relat_1(X1)) & v1_relat_1(X1)) => (k1_xboole_0 != k1_wellord1(sK7,sK6) & ~r2_hidden(sK6,k3_relat_1(sK7)) & v1_relat_1(sK7))),
% 3.58/0.99    introduced(choice_axiom,[])).
% 3.58/0.99  
% 3.58/0.99  fof(f45,plain,(
% 3.58/0.99    k1_xboole_0 != k1_wellord1(sK7,sK6) & ~r2_hidden(sK6,k3_relat_1(sK7)) & v1_relat_1(sK7)),
% 3.58/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f22,f44])).
% 3.58/0.99  
% 3.58/0.99  fof(f79,plain,(
% 3.58/0.99    v1_relat_1(sK7)),
% 3.58/0.99    inference(cnf_transformation,[],[f45])).
% 3.58/0.99  
% 3.58/0.99  fof(f4,axiom,(
% 3.58/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.58/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.58/0.99  
% 3.58/0.99  fof(f59,plain,(
% 3.58/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.58/0.99    inference(cnf_transformation,[],[f4])).
% 3.58/0.99  
% 3.58/0.99  fof(f14,axiom,(
% 3.58/0.99    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.58/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.58/0.99  
% 3.58/0.99  fof(f19,plain,(
% 3.58/0.99    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.58/0.99    inference(ennf_transformation,[],[f14])).
% 3.58/0.99  
% 3.58/0.99  fof(f72,plain,(
% 3.58/0.99    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.58/0.99    inference(cnf_transformation,[],[f19])).
% 3.58/0.99  
% 3.58/0.99  fof(f12,axiom,(
% 3.58/0.99    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 3.58/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.58/0.99  
% 3.58/0.99  fof(f33,plain,(
% 3.58/0.99    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 3.58/0.99    inference(nnf_transformation,[],[f12])).
% 3.58/0.99  
% 3.58/0.99  fof(f34,plain,(
% 3.58/0.99    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 3.58/0.99    inference(rectify,[],[f33])).
% 3.58/0.99  
% 3.58/0.99  fof(f37,plain,(
% 3.58/0.99    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK4(X0,X5),X5),X0))),
% 3.58/0.99    introduced(choice_axiom,[])).
% 3.58/0.99  
% 3.58/0.99  fof(f36,plain,(
% 3.58/0.99    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) => r2_hidden(k4_tarski(sK3(X0,X1),X2),X0))) )),
% 3.58/0.99    introduced(choice_axiom,[])).
% 3.58/0.99  
% 3.58/0.99  fof(f35,plain,(
% 3.58/0.99    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK2(X0,X1)),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK2(X0,X1)),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 3.58/0.99    introduced(choice_axiom,[])).
% 3.58/0.99  
% 3.58/0.99  fof(f38,plain,(
% 3.58/0.99    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK2(X0,X1)),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK4(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 3.58/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f34,f37,f36,f35])).
% 3.58/0.99  
% 3.58/0.99  fof(f68,plain,(
% 3.58/0.99    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X6,X5),X0) | k2_relat_1(X0) != X1) )),
% 3.58/0.99    inference(cnf_transformation,[],[f38])).
% 3.58/0.99  
% 3.58/0.99  fof(f101,plain,(
% 3.58/0.99    ( ! [X6,X0,X5] : (r2_hidden(X5,k2_relat_1(X0)) | ~r2_hidden(k4_tarski(X6,X5),X0)) )),
% 3.58/0.99    inference(equality_resolution,[],[f68])).
% 3.58/0.99  
% 3.58/0.99  fof(f13,axiom,(
% 3.58/0.99    ! [X0] : (v1_relat_1(X0) => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0))),
% 3.58/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.58/0.99  
% 3.58/0.99  fof(f18,plain,(
% 3.58/0.99    ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0))),
% 3.58/0.99    inference(ennf_transformation,[],[f13])).
% 3.58/0.99  
% 3.58/0.99  fof(f71,plain,(
% 3.58/0.99    ( ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.58/0.99    inference(cnf_transformation,[],[f18])).
% 3.58/0.99  
% 3.58/0.99  fof(f1,axiom,(
% 3.58/0.99    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 3.58/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.58/0.99  
% 3.58/0.99  fof(f23,plain,(
% 3.58/0.99    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.58/0.99    inference(nnf_transformation,[],[f1])).
% 3.58/0.99  
% 3.58/0.99  fof(f24,plain,(
% 3.58/0.99    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.58/0.99    inference(flattening,[],[f23])).
% 3.58/0.99  
% 3.58/0.99  fof(f25,plain,(
% 3.58/0.99    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.58/0.99    inference(rectify,[],[f24])).
% 3.58/0.99  
% 3.58/0.99  fof(f26,plain,(
% 3.58/0.99    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.58/0.99    introduced(choice_axiom,[])).
% 3.58/0.99  
% 3.58/0.99  fof(f27,plain,(
% 3.58/0.99    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.58/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).
% 3.58/0.99  
% 3.58/0.99  fof(f48,plain,(
% 3.58/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 3.58/0.99    inference(cnf_transformation,[],[f27])).
% 3.58/0.99  
% 3.58/0.99  fof(f95,plain,(
% 3.58/0.99    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 3.58/0.99    inference(equality_resolution,[],[f48])).
% 3.58/0.99  
% 3.58/0.99  fof(f80,plain,(
% 3.58/0.99    ~r2_hidden(sK6,k3_relat_1(sK7))),
% 3.58/0.99    inference(cnf_transformation,[],[f45])).
% 3.58/0.99  
% 3.58/0.99  fof(f81,plain,(
% 3.58/0.99    k1_xboole_0 != k1_wellord1(sK7,sK6)),
% 3.58/0.99    inference(cnf_transformation,[],[f45])).
% 3.58/0.99  
% 3.58/0.99  cnf(c_21,plain,
% 3.58/0.99      ( r2_hidden(sK5(X0,X1,X2),X2)
% 3.58/0.99      | r2_hidden(k4_tarski(sK5(X0,X1,X2),X1),X0)
% 3.58/0.99      | ~ v1_relat_1(X0)
% 3.58/0.99      | k1_wellord1(X0,X1) = X2 ),
% 3.58/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_28,negated_conjecture,
% 3.58/0.99      ( v1_relat_1(sK7) ),
% 3.58/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_329,plain,
% 3.58/0.99      ( r2_hidden(sK5(X0,X1,X2),X2)
% 3.58/0.99      | r2_hidden(k4_tarski(sK5(X0,X1,X2),X1),X0)
% 3.58/0.99      | k1_wellord1(X0,X1) = X2
% 3.58/0.99      | sK7 != X0 ),
% 3.58/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_28]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_330,plain,
% 3.58/0.99      ( r2_hidden(sK5(sK7,X0,X1),X1)
% 3.58/0.99      | r2_hidden(k4_tarski(sK5(sK7,X0,X1),X0),sK7)
% 3.58/0.99      | k1_wellord1(sK7,X0) = X1 ),
% 3.58/0.99      inference(unflattening,[status(thm)],[c_329]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_9664,plain,
% 3.58/0.99      ( k1_wellord1(sK7,X0) = X1
% 3.58/0.99      | r2_hidden(sK5(sK7,X0,X1),X1) = iProver_top
% 3.58/0.99      | r2_hidden(k4_tarski(sK5(sK7,X0,X1),X0),sK7) = iProver_top ),
% 3.58/0.99      inference(predicate_to_equality,[status(thm)],[c_330]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_13,plain,
% 3.58/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 3.58/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_19,negated_conjecture,
% 3.58/0.99      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 3.58/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_303,plain,
% 3.58/0.99      ( ~ r2_hidden(X0,X1) | X0 != X2 | k1_xboole_0 != X1 ),
% 3.58/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_19]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_304,plain,
% 3.58/0.99      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 3.58/0.99      inference(unflattening,[status(thm)],[c_303]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_9666,plain,
% 3.58/0.99      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.58/0.99      inference(predicate_to_equality,[status(thm)],[c_304]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_10049,plain,
% 3.58/0.99      ( k1_wellord1(sK7,X0) = k1_xboole_0
% 3.58/0.99      | r2_hidden(k4_tarski(sK5(sK7,X0,k1_xboole_0),X0),sK7) = iProver_top ),
% 3.58/0.99      inference(superposition,[status(thm)],[c_9664,c_9666]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_16,plain,
% 3.58/0.99      ( r2_hidden(X0,k2_relat_1(X1)) | ~ r2_hidden(k4_tarski(X2,X0),X1) ),
% 3.58/0.99      inference(cnf_transformation,[],[f101]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_9669,plain,
% 3.58/0.99      ( r2_hidden(X0,k2_relat_1(X1)) = iProver_top
% 3.58/0.99      | r2_hidden(k4_tarski(X2,X0),X1) != iProver_top ),
% 3.58/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_10628,plain,
% 3.58/0.99      ( k1_wellord1(sK7,X0) = k1_xboole_0
% 3.58/0.99      | r2_hidden(X0,k2_relat_1(sK7)) = iProver_top ),
% 3.58/0.99      inference(superposition,[status(thm)],[c_10049,c_9669]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_18,plain,
% 3.58/0.99      ( ~ v1_relat_1(X0)
% 3.58/0.99      | k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ),
% 3.58/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_362,plain,
% 3.58/0.99      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
% 3.58/0.99      | sK7 != X0 ),
% 3.58/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_28]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_363,plain,
% 3.58/0.99      ( k2_xboole_0(k1_relat_1(sK7),k2_relat_1(sK7)) = k3_relat_1(sK7) ),
% 3.58/0.99      inference(unflattening,[status(thm)],[c_362]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_3,plain,
% 3.58/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,k2_xboole_0(X2,X1)) ),
% 3.58/0.99      inference(cnf_transformation,[],[f95]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_9672,plain,
% 3.58/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.58/0.99      | r2_hidden(X0,k2_xboole_0(X2,X1)) = iProver_top ),
% 3.58/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_9886,plain,
% 3.58/0.99      ( r2_hidden(X0,k3_relat_1(sK7)) = iProver_top
% 3.58/0.99      | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
% 3.58/0.99      inference(superposition,[status(thm)],[c_363,c_9672]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_11237,plain,
% 3.58/0.99      ( k1_wellord1(sK7,X0) = k1_xboole_0
% 3.58/0.99      | r2_hidden(X0,k3_relat_1(sK7)) = iProver_top ),
% 3.58/0.99      inference(superposition,[status(thm)],[c_10628,c_9886]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_27,negated_conjecture,
% 3.58/0.99      ( ~ r2_hidden(sK6,k3_relat_1(sK7)) ),
% 3.58/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_9668,plain,
% 3.58/0.99      ( r2_hidden(sK6,k3_relat_1(sK7)) != iProver_top ),
% 3.58/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_11587,plain,
% 3.58/0.99      ( k1_wellord1(sK7,sK6) = k1_xboole_0 ),
% 3.58/0.99      inference(superposition,[status(thm)],[c_11237,c_9668]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_590,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_5574,plain,
% 3.58/0.99      ( X0 != X1 | X0 = k1_wellord1(sK7,X2) | k1_wellord1(sK7,X2) != X1 ),
% 3.58/0.99      inference(instantiation,[status(thm)],[c_590]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_6228,plain,
% 3.58/0.99      ( k1_wellord1(sK7,sK6) != X0
% 3.58/0.99      | k1_xboole_0 != X0
% 3.58/0.99      | k1_xboole_0 = k1_wellord1(sK7,sK6) ),
% 3.58/0.99      inference(instantiation,[status(thm)],[c_5574]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_6229,plain,
% 3.58/0.99      ( k1_wellord1(sK7,sK6) != k1_xboole_0
% 3.58/0.99      | k1_xboole_0 = k1_wellord1(sK7,sK6)
% 3.58/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.58/0.99      inference(instantiation,[status(thm)],[c_6228]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_589,plain,( X0 = X0 ),theory(equality) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_612,plain,
% 3.58/0.99      ( k1_xboole_0 = k1_xboole_0 ),
% 3.58/0.99      inference(instantiation,[status(thm)],[c_589]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_26,negated_conjecture,
% 3.58/0.99      ( k1_xboole_0 != k1_wellord1(sK7,sK6) ),
% 3.58/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(contradiction,plain,
% 3.58/0.99      ( $false ),
% 3.58/0.99      inference(minisat,[status(thm)],[c_11587,c_6229,c_612,c_26]) ).
% 3.58/0.99  
% 3.58/0.99  
% 3.58/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.58/0.99  
% 3.58/0.99  ------                               Statistics
% 3.58/0.99  
% 3.58/0.99  ------ Selected
% 3.58/0.99  
% 3.58/0.99  total_time:                             0.24
% 3.58/0.99  
%------------------------------------------------------------------------------
