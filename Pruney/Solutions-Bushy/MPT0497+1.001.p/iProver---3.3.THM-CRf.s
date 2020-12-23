%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0497+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:26 EST 2020

% Result     : Theorem 3.77s
% Output     : CNFRefutation 3.77s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 213 expanded)
%              Number of clauses        :   50 (  61 expanded)
%              Number of leaves         :   19 (  50 expanded)
%              Depth                    :   12
%              Number of atoms          :  448 (1077 expanded)
%              Number of equality atoms :   88 ( 221 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k7_relat_1(X1,X0) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k7_relat_1(X1,X0) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ( k7_relat_1(X1,X0) = k1_xboole_0
      <~> r1_xboole_0(k1_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f38,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k7_relat_1(X1,X0) != k1_xboole_0 )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k7_relat_1(X1,X0) = k1_xboole_0 )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f39,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k7_relat_1(X1,X0) != k1_xboole_0 )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k7_relat_1(X1,X0) = k1_xboole_0 )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f38])).

fof(f40,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
          | k7_relat_1(X1,X0) != k1_xboole_0 )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k7_relat_1(X1,X0) = k1_xboole_0 )
        & v1_relat_1(X1) )
   => ( ( ~ r1_xboole_0(k1_relat_1(sK7),sK6)
        | k7_relat_1(sK7,sK6) != k1_xboole_0 )
      & ( r1_xboole_0(k1_relat_1(sK7),sK6)
        | k7_relat_1(sK7,sK6) = k1_xboole_0 )
      & v1_relat_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ( ~ r1_xboole_0(k1_relat_1(sK7),sK6)
      | k7_relat_1(sK7,sK6) != k1_xboole_0 )
    & ( r1_xboole_0(k1_relat_1(sK7),sK6)
      | k7_relat_1(sK7,sK6) = k1_xboole_0 )
    & v1_relat_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f39,f40])).

fof(f68,plain,
    ( r1_xboole_0(k1_relat_1(sK7),sK6)
    | k7_relat_1(sK7,sK6) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f41])).

fof(f67,plain,(
    v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f41])).

fof(f8,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f42,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
          | ~ r2_hidden(sK5(X0,X1,X2),X0)
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK5(X0,X1,X2),X1)
            & r2_hidden(sK5(X0,X1,X2),X0) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
            | ~ r2_hidden(sK5(X0,X1,X2),X0)
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK5(X0,X1,X2),X1)
              & r2_hidden(sK5(X0,X1,X2),X0) )
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f34,f35])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK5(X0,X1,X2),X1)
      | r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK5(X0,X1,X2),X0)
      | r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
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

fof(f27,plain,(
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
    inference(rectify,[],[f26])).

fof(f30,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK3(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK2(X0,X1),X3),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK2(X0,X1),X4),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK2(X0,X1),X3),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f27,f30,f29,f28])).

fof(f50,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f74,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f50])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( v1_relat_1(X2)
         => ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X0)
                    | ~ r2_hidden(X5,X1) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X0)
                      & r2_hidden(X5,X1) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f22])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ( r2_hidden(k4_tarski(X3,X4),X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2) )
        & ( ( r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X0)
            & r2_hidden(sK0(X0,X1,X2),X1) )
          | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X0)
                  | ~ r2_hidden(sK0(X0,X1,X2),X1)
                  | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2) )
                & ( ( r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X0)
                    & r2_hidden(sK0(X0,X1,X2),X1) )
                  | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X0)
                    | ~ r2_hidden(X5,X1) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X0)
                      & r2_hidden(X5,X1) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f24])).

fof(f46,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X2)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(X5,X1)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f70,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(X5,X1)
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f56,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f75,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f56])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f51,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f73,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f51])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X0)
      | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f69,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK7),sK6)
    | k7_relat_1(sK7,sK6) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_312,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_13883,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k3_xboole_0(sK6,k1_relat_1(sK7)))
    | k3_xboole_0(sK6,k1_relat_1(sK7)) != X0 ),
    inference(instantiation,[status(thm)],[c_312])).

cnf(c_13885,plain,
    ( v1_xboole_0(k3_xboole_0(sK6,k1_relat_1(sK7)))
    | ~ v1_xboole_0(k1_xboole_0)
    | k3_xboole_0(sK6,k1_relat_1(sK7)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_13883])).

cnf(c_24,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_10742,plain,
    ( ~ r2_hidden(sK0(sK7,sK6,k1_xboole_0),k3_xboole_0(sK6,k1_relat_1(sK7)))
    | ~ v1_xboole_0(k3_xboole_0(sK6,k1_relat_1(sK7))) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_310,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_309,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2262,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_310,c_309])).

cnf(c_26,negated_conjecture,
    ( r1_xboole_0(k1_relat_1(sK7),sK6)
    | k7_relat_1(sK7,sK6) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_9028,plain,
    ( r1_xboole_0(k1_relat_1(sK7),sK6)
    | k1_xboole_0 = k7_relat_1(sK7,sK6) ),
    inference(resolution,[status(thm)],[c_2262,c_26])).

cnf(c_27,negated_conjecture,
    ( v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_21,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_0,plain,
    ( ~ v1_xboole_0(X0)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_86,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_18,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1160,plain,
    ( r1_xboole_0(k1_relat_1(sK7),sK6)
    | k3_xboole_0(k1_relat_1(sK7),sK6) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_13,plain,
    ( r2_hidden(sK5(X0,X1,X2),X1)
    | r2_hidden(sK5(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1231,plain,
    ( r2_hidden(sK5(k1_relat_1(sK7),sK6,k1_xboole_0),sK6)
    | r2_hidden(sK5(k1_relat_1(sK7),sK6,k1_xboole_0),k1_xboole_0)
    | k3_xboole_0(k1_relat_1(sK7),sK6) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_14,plain,
    ( r2_hidden(sK5(X0,X1,X2),X0)
    | r2_hidden(sK5(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1230,plain,
    ( r2_hidden(sK5(k1_relat_1(sK7),sK6,k1_xboole_0),k1_relat_1(sK7))
    | r2_hidden(sK5(k1_relat_1(sK7),sK6,k1_xboole_0),k1_xboole_0)
    | k3_xboole_0(k1_relat_1(sK7),sK6) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_311,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1393,plain,
    ( r1_xboole_0(k1_relat_1(sK7),sK6)
    | v1_relat_1(k7_relat_1(sK7,sK6))
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_311,c_26])).

cnf(c_1699,plain,
    ( r1_xboole_0(k1_relat_1(sK7),sK6)
    | v1_xboole_0(k7_relat_1(sK7,sK6))
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_312,c_26])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,sK4(X1,X0)),X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2174,plain,
    ( ~ r2_hidden(sK5(k1_relat_1(sK7),sK6,k1_xboole_0),k1_relat_1(sK7))
    | r2_hidden(k4_tarski(sK5(k1_relat_1(sK7),sK6,k1_xboole_0),sK4(sK7,sK5(k1_relat_1(sK7),sK6,k1_xboole_0))),sK7) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_4167,plain,
    ( ~ r2_hidden(sK5(k1_relat_1(sK7),sK6,k1_xboole_0),k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),X3)
    | r2_hidden(k4_tarski(X0,X2),k7_relat_1(X3,X1))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(k7_relat_1(X3,X1)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_3879,plain,
    ( ~ r2_hidden(sK5(k1_relat_1(sK7),sK6,k1_xboole_0),X0)
    | r2_hidden(k4_tarski(sK5(k1_relat_1(sK7),sK6,k1_xboole_0),sK4(sK7,sK5(k1_relat_1(sK7),sK6,k1_xboole_0))),k7_relat_1(sK7,X0))
    | ~ r2_hidden(k4_tarski(sK5(k1_relat_1(sK7),sK6,k1_xboole_0),sK4(sK7,sK5(k1_relat_1(sK7),sK6,k1_xboole_0))),sK7)
    | ~ v1_relat_1(k7_relat_1(sK7,X0))
    | ~ v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_7107,plain,
    ( ~ r2_hidden(sK5(k1_relat_1(sK7),sK6,k1_xboole_0),sK6)
    | r2_hidden(k4_tarski(sK5(k1_relat_1(sK7),sK6,k1_xboole_0),sK4(sK7,sK5(k1_relat_1(sK7),sK6,k1_xboole_0))),k7_relat_1(sK7,sK6))
    | ~ r2_hidden(k4_tarski(sK5(k1_relat_1(sK7),sK6,k1_xboole_0),sK4(sK7,sK5(k1_relat_1(sK7),sK6,k1_xboole_0))),sK7)
    | ~ v1_relat_1(k7_relat_1(sK7,sK6))
    | ~ v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_3879])).

cnf(c_9131,plain,
    ( ~ r2_hidden(k4_tarski(sK5(k1_relat_1(sK7),sK6,k1_xboole_0),sK4(sK7,sK5(k1_relat_1(sK7),sK6,k1_xboole_0))),k7_relat_1(sK7,sK6))
    | ~ v1_xboole_0(k7_relat_1(sK7,sK6)) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_9269,plain,
    ( r1_xboole_0(k1_relat_1(sK7),sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9028,c_27,c_21,c_86,c_1160,c_1231,c_1230,c_1393,c_1699,c_2174,c_4167,c_7107,c_9131])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1356,plain,
    ( ~ r2_hidden(sK0(sK7,sK6,k1_xboole_0),X0)
    | r2_hidden(sK0(sK7,sK6,k1_xboole_0),k3_xboole_0(sK6,X0))
    | ~ r2_hidden(sK0(sK7,sK6,k1_xboole_0),sK6) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1789,plain,
    ( r2_hidden(sK0(sK7,sK6,k1_xboole_0),k3_xboole_0(sK6,k1_relat_1(sK7)))
    | ~ r2_hidden(sK0(sK7,sK6,k1_xboole_0),k1_relat_1(sK7))
    | ~ r2_hidden(sK0(sK7,sK6,k1_xboole_0),sK6) ),
    inference(instantiation,[status(thm)],[c_1356])).

cnf(c_905,plain,
    ( k7_relat_1(sK7,sK6) = k1_xboole_0
    | r1_xboole_0(k1_relat_1(sK7),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_23,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_908,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1295,plain,
    ( k7_relat_1(sK7,sK6) = k1_xboole_0
    | r1_xboole_0(sK6,k1_relat_1(sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_905,c_908])).

cnf(c_19,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_911,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1524,plain,
    ( k7_relat_1(sK7,sK6) = k1_xboole_0
    | k3_xboole_0(sK6,k1_relat_1(sK7)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1295,c_911])).

cnf(c_10,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1489,plain,
    ( r2_hidden(sK0(sK7,sK6,k1_xboole_0),k1_relat_1(sK7))
    | ~ r2_hidden(k4_tarski(sK0(sK7,sK6,k1_xboole_0),sK1(sK7,sK6,k1_xboole_0)),sK7) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1327,plain,
    ( ~ r2_hidden(k4_tarski(sK0(sK7,sK6,k1_xboole_0),sK1(sK7,sK6,k1_xboole_0)),k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_3,plain,
    ( r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X0)
    | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1285,plain,
    ( r2_hidden(k4_tarski(sK0(sK7,sK6,k1_xboole_0),sK1(sK7,sK6,k1_xboole_0)),sK7)
    | r2_hidden(k4_tarski(sK0(sK7,sK6,k1_xboole_0),sK1(sK7,sK6,k1_xboole_0)),k1_xboole_0)
    | ~ v1_relat_1(sK7)
    | ~ v1_relat_1(k1_xboole_0)
    | k7_relat_1(sK7,sK6) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_4,plain,
    ( r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1286,plain,
    ( r2_hidden(sK0(sK7,sK6,k1_xboole_0),sK6)
    | r2_hidden(k4_tarski(sK0(sK7,sK6,k1_xboole_0),sK1(sK7,sK6,k1_xboole_0)),k1_xboole_0)
    | ~ v1_relat_1(sK7)
    | ~ v1_relat_1(k1_xboole_0)
    | k7_relat_1(sK7,sK6) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_25,negated_conjecture,
    ( ~ r1_xboole_0(k1_relat_1(sK7),sK6)
    | k7_relat_1(sK7,sK6) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f69])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13885,c_10742,c_9269,c_1789,c_1524,c_1489,c_1327,c_1285,c_1286,c_86,c_21,c_25,c_27])).


%------------------------------------------------------------------------------
