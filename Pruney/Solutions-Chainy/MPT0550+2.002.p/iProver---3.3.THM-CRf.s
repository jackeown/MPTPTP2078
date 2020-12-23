%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:46:28 EST 2020

% Result     : Theorem 2.38s
% Output     : CNFRefutation 2.38s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 268 expanded)
%              Number of clauses        :   49 (  82 expanded)
%              Number of leaves         :   21 (  64 expanded)
%              Depth                    :   18
%              Number of atoms          :  377 (1132 expanded)
%              Number of equality atoms :   99 ( 306 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   15 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f7])).

fof(f42,plain,(
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
    inference(rectify,[],[f41])).

fof(f45,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK7(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK6(X0,X1),X3),X0)
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0)
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK6(X0,X1),X3),X0)
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0)
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f42,f45,f44,f43])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0)
      | r2_hidden(sK6(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( k1_xboole_0 = k9_relat_1(X1,X0)
          & r1_tarski(X0,k1_relat_1(X1))
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ~ ( k1_xboole_0 = k9_relat_1(X1,X0)
            & r1_tarski(X0,k1_relat_1(X1))
            & k1_xboole_0 != X0 ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f23,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k9_relat_1(X1,X0)
      & r1_tarski(X0,k1_relat_1(X1))
      & k1_xboole_0 != X0
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f24,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k9_relat_1(X1,X0)
      & r1_tarski(X0,k1_relat_1(X1))
      & k1_xboole_0 != X0
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f51,plain,
    ( ? [X0,X1] :
        ( k1_xboole_0 = k9_relat_1(X1,X0)
        & r1_tarski(X0,k1_relat_1(X1))
        & k1_xboole_0 != X0
        & v1_relat_1(X1) )
   => ( k1_xboole_0 = k9_relat_1(sK11,sK10)
      & r1_tarski(sK10,k1_relat_1(sK11))
      & k1_xboole_0 != sK10
      & v1_relat_1(sK11) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( k1_xboole_0 = k9_relat_1(sK11,sK10)
    & r1_tarski(sK10,k1_relat_1(sK11))
    & k1_xboole_0 != sK10
    & v1_relat_1(sK11) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11])],[f24,f51])).

fof(f83,plain,(
    k1_xboole_0 = k9_relat_1(sK11,sK10) ),
    inference(cnf_transformation,[],[f52])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X3,X0),X2)
              & r2_hidden(X3,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X4,X0),X2)
              & r2_hidden(X4,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f47])).

fof(f49,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK9(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK9(X0,X1,X2),X0),X2)
        & r2_hidden(sK9(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK9(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK9(X0,X1,X2),X0),X2)
            & r2_hidden(sK9(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f48,f49])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK9(X0,X1,X2),k1_relat_1(X2))
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f80,plain,(
    v1_relat_1(sK11) ),
    inference(cnf_transformation,[],[f52])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK9(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X4,X3),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X4,X3),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X4,X3),X0) ) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X4,X3),X0) )
                  | ~ r2_hidden(X3,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X4,X3),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( r2_hidden(X5,X1)
                      & r2_hidden(k4_tarski(X5,X3),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X7,X6),X0) ) )
                & ( ? [X8] :
                      ( r2_hidden(X8,X1)
                      & r2_hidden(k4_tarski(X8,X6),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f35])).

fof(f39,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X8,X6),X0) )
     => ( r2_hidden(sK5(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(sK5(X0,X1,X6),X6),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(X5,X3),X0) )
     => ( r2_hidden(sK4(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK4(X0,X1,X2),X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(X4,X1)
                | ~ r2_hidden(k4_tarski(X4,X3),X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X5,X3),X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( ~ r2_hidden(X4,X1)
              | ~ r2_hidden(k4_tarski(X4,sK3(X0,X1,X2)),X0) )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X1)
              & r2_hidden(k4_tarski(X5,sK3(X0,X1,X2)),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(k4_tarski(X4,sK3(X0,X1,X2)),X0) )
                | ~ r2_hidden(sK3(X0,X1,X2),X2) )
              & ( ( r2_hidden(sK4(X0,X1,X2),X1)
                  & r2_hidden(k4_tarski(sK4(X0,X1,X2),sK3(X0,X1,X2)),X0) )
                | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X7,X6),X0) ) )
                & ( ( r2_hidden(sK5(X0,X1,X6),X1)
                    & r2_hidden(k4_tarski(sK5(X0,X1,X6),X6),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f36,f39,f38,f37])).

fof(f63,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X7,X6),X0)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f84,plain,(
    ! [X6,X0,X7,X1] :
      ( r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X7,X6),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f63])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).

fof(f53,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f11,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f10,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f67,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f88,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f67])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f31])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f82,plain,(
    r1_tarski(sK10,k1_relat_1(sK11)) ),
    inference(cnf_transformation,[],[f52])).

fof(f81,plain,(
    k1_xboole_0 != sK10 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_15,plain,
    ( r2_hidden(sK6(X0,X1),X1)
    | r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1482,plain,
    ( k1_relat_1(X0) = X1
    | r2_hidden(sK6(X0,X1),X1) = iProver_top
    | r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_27,negated_conjecture,
    ( k1_xboole_0 = k9_relat_1(sK11,sK10) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_21,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK9(X0,X2,X1),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_30,negated_conjecture,
    ( v1_relat_1(sK11) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_631,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK9(X0,X2,X1),k1_relat_1(X1))
    | sK11 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_30])).

cnf(c_632,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK11,X1))
    | r2_hidden(sK9(X0,X1,sK11),k1_relat_1(sK11)) ),
    inference(unflattening,[status(thm)],[c_631])).

cnf(c_1469,plain,
    ( r2_hidden(X0,k9_relat_1(sK11,X1)) != iProver_top
    | r2_hidden(sK9(X0,X1,sK11),k1_relat_1(sK11)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_632])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK9(X0,X2,X1),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_643,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK9(X0,X2,X1),X0),X1)
    | sK11 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_30])).

cnf(c_644,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK11,X1))
    | r2_hidden(k4_tarski(sK9(X0,X1,sK11),X0),sK11) ),
    inference(unflattening,[status(thm)],[c_643])).

cnf(c_1468,plain,
    ( r2_hidden(X0,k9_relat_1(sK11,X1)) != iProver_top
    | r2_hidden(k4_tarski(sK9(X0,X1,sK11),X0),sK11) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_644])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k9_relat_1(X3,X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X3)
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_618,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k9_relat_1(X3,X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X3)
    | sK11 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_30])).

cnf(c_619,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k9_relat_1(sK11,X1))
    | ~ r2_hidden(k4_tarski(X0,X2),sK11) ),
    inference(unflattening,[status(thm)],[c_618])).

cnf(c_1470,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,k9_relat_1(sK11,X1)) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),sK11) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_619])).

cnf(c_2189,plain,
    ( r2_hidden(X0,k9_relat_1(sK11,X1)) != iProver_top
    | r2_hidden(X0,k9_relat_1(sK11,X2)) = iProver_top
    | r2_hidden(sK9(X0,X1,sK11),X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1468,c_1470])).

cnf(c_2473,plain,
    ( r2_hidden(X0,k9_relat_1(sK11,X1)) != iProver_top
    | r2_hidden(X0,k9_relat_1(sK11,k1_relat_1(sK11))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1469,c_2189])).

cnf(c_2489,plain,
    ( r2_hidden(X0,k9_relat_1(sK11,k1_relat_1(sK11))) = iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_27,c_2473])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_5,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_334,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_5])).

cnf(c_335,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_334])).

cnf(c_336,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_335])).

cnf(c_2623,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2489,c_336])).

cnf(c_5267,plain,
    ( k1_relat_1(k1_xboole_0) = X0
    | r2_hidden(sK6(k1_xboole_0,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1482,c_2623])).

cnf(c_25,plain,
    ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_24,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1846,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_25,c_24])).

cnf(c_5307,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK6(k1_xboole_0,X0),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5267,c_1846])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,sK8(X1,X0)),X1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1480,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK8(X1,X0)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_5019,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK11)) != iProver_top
    | r2_hidden(sK8(sK11,X0),k9_relat_1(sK11,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1480,c_1470])).

cnf(c_8895,plain,
    ( r2_hidden(X0,k1_relat_1(sK11)) != iProver_top
    | r2_hidden(X0,sK10) != iProver_top
    | r2_hidden(sK8(sK11,X0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_27,c_5019])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_28,negated_conjecture,
    ( r1_tarski(sK10,k1_relat_1(sK11)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_403,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | k1_relat_1(sK11) != X2
    | sK10 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_28])).

cnf(c_404,plain,
    ( r2_hidden(X0,k1_relat_1(sK11))
    | ~ r2_hidden(X0,sK10) ),
    inference(unflattening,[status(thm)],[c_403])).

cnf(c_405,plain,
    ( r2_hidden(X0,k1_relat_1(sK11)) = iProver_top
    | r2_hidden(X0,sK10) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_404])).

cnf(c_9057,plain,
    ( r2_hidden(X0,sK10) != iProver_top
    | r2_hidden(sK8(sK11,X0),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8895,c_405])).

cnf(c_9065,plain,
    ( r2_hidden(X0,sK10) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_9057,c_2623])).

cnf(c_9080,plain,
    ( sK10 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5307,c_9065])).

cnf(c_1003,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1692,plain,
    ( sK10 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK10 ),
    inference(instantiation,[status(thm)],[c_1003])).

cnf(c_1693,plain,
    ( sK10 != k1_xboole_0
    | k1_xboole_0 = sK10
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1692])).

cnf(c_1002,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1031,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1002])).

cnf(c_29,negated_conjecture,
    ( k1_xboole_0 != sK10 ),
    inference(cnf_transformation,[],[f81])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9080,c_1693,c_1031,c_29])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:22:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 2.38/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.38/1.01  
% 2.38/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.38/1.01  
% 2.38/1.01  ------  iProver source info
% 2.38/1.01  
% 2.38/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.38/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.38/1.01  git: non_committed_changes: false
% 2.38/1.01  git: last_make_outside_of_git: false
% 2.38/1.01  
% 2.38/1.01  ------ 
% 2.38/1.01  
% 2.38/1.01  ------ Input Options
% 2.38/1.01  
% 2.38/1.01  --out_options                           all
% 2.38/1.01  --tptp_safe_out                         true
% 2.38/1.01  --problem_path                          ""
% 2.38/1.01  --include_path                          ""
% 2.38/1.01  --clausifier                            res/vclausify_rel
% 2.38/1.01  --clausifier_options                    --mode clausify
% 2.38/1.01  --stdin                                 false
% 2.38/1.01  --stats_out                             all
% 2.38/1.01  
% 2.38/1.01  ------ General Options
% 2.38/1.01  
% 2.38/1.01  --fof                                   false
% 2.38/1.01  --time_out_real                         305.
% 2.38/1.01  --time_out_virtual                      -1.
% 2.38/1.01  --symbol_type_check                     false
% 2.38/1.01  --clausify_out                          false
% 2.38/1.01  --sig_cnt_out                           false
% 2.38/1.01  --trig_cnt_out                          false
% 2.38/1.01  --trig_cnt_out_tolerance                1.
% 2.38/1.01  --trig_cnt_out_sk_spl                   false
% 2.38/1.01  --abstr_cl_out                          false
% 2.38/1.01  
% 2.38/1.01  ------ Global Options
% 2.38/1.01  
% 2.38/1.01  --schedule                              default
% 2.38/1.01  --add_important_lit                     false
% 2.38/1.01  --prop_solver_per_cl                    1000
% 2.38/1.01  --min_unsat_core                        false
% 2.38/1.01  --soft_assumptions                      false
% 2.38/1.01  --soft_lemma_size                       3
% 2.38/1.01  --prop_impl_unit_size                   0
% 2.38/1.01  --prop_impl_unit                        []
% 2.38/1.01  --share_sel_clauses                     true
% 2.38/1.01  --reset_solvers                         false
% 2.38/1.01  --bc_imp_inh                            [conj_cone]
% 2.38/1.01  --conj_cone_tolerance                   3.
% 2.38/1.01  --extra_neg_conj                        none
% 2.38/1.01  --large_theory_mode                     true
% 2.38/1.01  --prolific_symb_bound                   200
% 2.38/1.01  --lt_threshold                          2000
% 2.38/1.01  --clause_weak_htbl                      true
% 2.38/1.01  --gc_record_bc_elim                     false
% 2.38/1.01  
% 2.38/1.01  ------ Preprocessing Options
% 2.38/1.01  
% 2.38/1.01  --preprocessing_flag                    true
% 2.38/1.01  --time_out_prep_mult                    0.1
% 2.38/1.01  --splitting_mode                        input
% 2.38/1.01  --splitting_grd                         true
% 2.38/1.01  --splitting_cvd                         false
% 2.38/1.01  --splitting_cvd_svl                     false
% 2.38/1.01  --splitting_nvd                         32
% 2.38/1.01  --sub_typing                            true
% 2.38/1.01  --prep_gs_sim                           true
% 2.38/1.01  --prep_unflatten                        true
% 2.38/1.01  --prep_res_sim                          true
% 2.38/1.01  --prep_upred                            true
% 2.38/1.01  --prep_sem_filter                       exhaustive
% 2.38/1.01  --prep_sem_filter_out                   false
% 2.38/1.01  --pred_elim                             true
% 2.38/1.01  --res_sim_input                         true
% 2.38/1.01  --eq_ax_congr_red                       true
% 2.38/1.01  --pure_diseq_elim                       true
% 2.38/1.01  --brand_transform                       false
% 2.38/1.01  --non_eq_to_eq                          false
% 2.38/1.01  --prep_def_merge                        true
% 2.38/1.01  --prep_def_merge_prop_impl              false
% 2.38/1.01  --prep_def_merge_mbd                    true
% 2.38/1.01  --prep_def_merge_tr_red                 false
% 2.38/1.01  --prep_def_merge_tr_cl                  false
% 2.38/1.01  --smt_preprocessing                     true
% 2.38/1.01  --smt_ac_axioms                         fast
% 2.38/1.01  --preprocessed_out                      false
% 2.38/1.01  --preprocessed_stats                    false
% 2.38/1.01  
% 2.38/1.01  ------ Abstraction refinement Options
% 2.38/1.01  
% 2.38/1.01  --abstr_ref                             []
% 2.38/1.01  --abstr_ref_prep                        false
% 2.38/1.01  --abstr_ref_until_sat                   false
% 2.38/1.01  --abstr_ref_sig_restrict                funpre
% 2.38/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.38/1.01  --abstr_ref_under                       []
% 2.38/1.01  
% 2.38/1.01  ------ SAT Options
% 2.38/1.01  
% 2.38/1.01  --sat_mode                              false
% 2.38/1.01  --sat_fm_restart_options                ""
% 2.38/1.01  --sat_gr_def                            false
% 2.38/1.01  --sat_epr_types                         true
% 2.38/1.01  --sat_non_cyclic_types                  false
% 2.38/1.01  --sat_finite_models                     false
% 2.38/1.01  --sat_fm_lemmas                         false
% 2.38/1.01  --sat_fm_prep                           false
% 2.38/1.01  --sat_fm_uc_incr                        true
% 2.38/1.01  --sat_out_model                         small
% 2.38/1.01  --sat_out_clauses                       false
% 2.38/1.01  
% 2.38/1.01  ------ QBF Options
% 2.38/1.01  
% 2.38/1.01  --qbf_mode                              false
% 2.38/1.01  --qbf_elim_univ                         false
% 2.38/1.01  --qbf_dom_inst                          none
% 2.38/1.01  --qbf_dom_pre_inst                      false
% 2.38/1.01  --qbf_sk_in                             false
% 2.38/1.01  --qbf_pred_elim                         true
% 2.38/1.01  --qbf_split                             512
% 2.38/1.01  
% 2.38/1.01  ------ BMC1 Options
% 2.38/1.01  
% 2.38/1.01  --bmc1_incremental                      false
% 2.38/1.01  --bmc1_axioms                           reachable_all
% 2.38/1.01  --bmc1_min_bound                        0
% 2.38/1.01  --bmc1_max_bound                        -1
% 2.38/1.01  --bmc1_max_bound_default                -1
% 2.38/1.01  --bmc1_symbol_reachability              true
% 2.38/1.01  --bmc1_property_lemmas                  false
% 2.38/1.01  --bmc1_k_induction                      false
% 2.38/1.01  --bmc1_non_equiv_states                 false
% 2.38/1.01  --bmc1_deadlock                         false
% 2.38/1.01  --bmc1_ucm                              false
% 2.38/1.01  --bmc1_add_unsat_core                   none
% 2.38/1.01  --bmc1_unsat_core_children              false
% 2.38/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.38/1.01  --bmc1_out_stat                         full
% 2.38/1.01  --bmc1_ground_init                      false
% 2.38/1.01  --bmc1_pre_inst_next_state              false
% 2.38/1.01  --bmc1_pre_inst_state                   false
% 2.38/1.01  --bmc1_pre_inst_reach_state             false
% 2.38/1.01  --bmc1_out_unsat_core                   false
% 2.38/1.01  --bmc1_aig_witness_out                  false
% 2.38/1.01  --bmc1_verbose                          false
% 2.38/1.01  --bmc1_dump_clauses_tptp                false
% 2.38/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.38/1.01  --bmc1_dump_file                        -
% 2.38/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.38/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.38/1.01  --bmc1_ucm_extend_mode                  1
% 2.38/1.01  --bmc1_ucm_init_mode                    2
% 2.38/1.01  --bmc1_ucm_cone_mode                    none
% 2.38/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.38/1.01  --bmc1_ucm_relax_model                  4
% 2.38/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.38/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.38/1.01  --bmc1_ucm_layered_model                none
% 2.38/1.01  --bmc1_ucm_max_lemma_size               10
% 2.38/1.01  
% 2.38/1.01  ------ AIG Options
% 2.38/1.01  
% 2.38/1.01  --aig_mode                              false
% 2.38/1.01  
% 2.38/1.01  ------ Instantiation Options
% 2.38/1.01  
% 2.38/1.01  --instantiation_flag                    true
% 2.38/1.01  --inst_sos_flag                         false
% 2.38/1.01  --inst_sos_phase                        true
% 2.38/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.38/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.38/1.01  --inst_lit_sel_side                     num_symb
% 2.38/1.01  --inst_solver_per_active                1400
% 2.38/1.01  --inst_solver_calls_frac                1.
% 2.38/1.01  --inst_passive_queue_type               priority_queues
% 2.38/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.38/1.01  --inst_passive_queues_freq              [25;2]
% 2.38/1.01  --inst_dismatching                      true
% 2.38/1.01  --inst_eager_unprocessed_to_passive     true
% 2.38/1.01  --inst_prop_sim_given                   true
% 2.38/1.01  --inst_prop_sim_new                     false
% 2.38/1.01  --inst_subs_new                         false
% 2.38/1.01  --inst_eq_res_simp                      false
% 2.38/1.01  --inst_subs_given                       false
% 2.38/1.01  --inst_orphan_elimination               true
% 2.38/1.01  --inst_learning_loop_flag               true
% 2.38/1.01  --inst_learning_start                   3000
% 2.38/1.01  --inst_learning_factor                  2
% 2.38/1.01  --inst_start_prop_sim_after_learn       3
% 2.38/1.01  --inst_sel_renew                        solver
% 2.38/1.01  --inst_lit_activity_flag                true
% 2.38/1.01  --inst_restr_to_given                   false
% 2.38/1.01  --inst_activity_threshold               500
% 2.38/1.01  --inst_out_proof                        true
% 2.38/1.01  
% 2.38/1.01  ------ Resolution Options
% 2.38/1.01  
% 2.38/1.01  --resolution_flag                       true
% 2.38/1.01  --res_lit_sel                           adaptive
% 2.38/1.01  --res_lit_sel_side                      none
% 2.38/1.01  --res_ordering                          kbo
% 2.38/1.01  --res_to_prop_solver                    active
% 2.38/1.01  --res_prop_simpl_new                    false
% 2.38/1.01  --res_prop_simpl_given                  true
% 2.38/1.01  --res_passive_queue_type                priority_queues
% 2.38/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.38/1.01  --res_passive_queues_freq               [15;5]
% 2.38/1.01  --res_forward_subs                      full
% 2.38/1.01  --res_backward_subs                     full
% 2.38/1.01  --res_forward_subs_resolution           true
% 2.38/1.01  --res_backward_subs_resolution          true
% 2.38/1.01  --res_orphan_elimination                true
% 2.38/1.01  --res_time_limit                        2.
% 2.38/1.01  --res_out_proof                         true
% 2.38/1.01  
% 2.38/1.01  ------ Superposition Options
% 2.38/1.01  
% 2.38/1.01  --superposition_flag                    true
% 2.38/1.01  --sup_passive_queue_type                priority_queues
% 2.38/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.38/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.38/1.01  --demod_completeness_check              fast
% 2.38/1.01  --demod_use_ground                      true
% 2.38/1.01  --sup_to_prop_solver                    passive
% 2.38/1.01  --sup_prop_simpl_new                    true
% 2.38/1.01  --sup_prop_simpl_given                  true
% 2.38/1.01  --sup_fun_splitting                     false
% 2.38/1.01  --sup_smt_interval                      50000
% 2.38/1.01  
% 2.38/1.01  ------ Superposition Simplification Setup
% 2.38/1.01  
% 2.38/1.01  --sup_indices_passive                   []
% 2.38/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.38/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.38/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.38/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.38/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.38/1.01  --sup_full_bw                           [BwDemod]
% 2.38/1.01  --sup_immed_triv                        [TrivRules]
% 2.38/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.38/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.38/1.01  --sup_immed_bw_main                     []
% 2.38/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.38/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.38/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.38/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.38/1.01  
% 2.38/1.01  ------ Combination Options
% 2.38/1.01  
% 2.38/1.01  --comb_res_mult                         3
% 2.38/1.01  --comb_sup_mult                         2
% 2.38/1.01  --comb_inst_mult                        10
% 2.38/1.01  
% 2.38/1.01  ------ Debug Options
% 2.38/1.01  
% 2.38/1.01  --dbg_backtrace                         false
% 2.38/1.01  --dbg_dump_prop_clauses                 false
% 2.38/1.01  --dbg_dump_prop_clauses_file            -
% 2.38/1.01  --dbg_out_stat                          false
% 2.38/1.01  ------ Parsing...
% 2.38/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.38/1.01  
% 2.38/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e 
% 2.38/1.01  
% 2.38/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.38/1.01  
% 2.38/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.38/1.01  ------ Proving...
% 2.38/1.01  ------ Problem Properties 
% 2.38/1.01  
% 2.38/1.01  
% 2.38/1.01  clauses                                 32
% 2.38/1.01  conjectures                             3
% 2.38/1.01  EPR                                     4
% 2.38/1.01  Horn                                    25
% 2.38/1.01  unary                                   8
% 2.38/1.01  binary                                  15
% 2.38/1.01  lits                                    66
% 2.38/1.01  lits eq                                 16
% 2.38/1.01  fd_pure                                 0
% 2.38/1.01  fd_pseudo                               0
% 2.38/1.01  fd_cond                                 1
% 2.38/1.01  fd_pseudo_cond                          6
% 2.38/1.01  AC symbols                              0
% 2.38/1.01  
% 2.38/1.01  ------ Schedule dynamic 5 is on 
% 2.38/1.01  
% 2.38/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.38/1.01  
% 2.38/1.01  
% 2.38/1.01  ------ 
% 2.38/1.01  Current options:
% 2.38/1.01  ------ 
% 2.38/1.01  
% 2.38/1.01  ------ Input Options
% 2.38/1.01  
% 2.38/1.01  --out_options                           all
% 2.38/1.01  --tptp_safe_out                         true
% 2.38/1.01  --problem_path                          ""
% 2.38/1.01  --include_path                          ""
% 2.38/1.01  --clausifier                            res/vclausify_rel
% 2.38/1.01  --clausifier_options                    --mode clausify
% 2.38/1.01  --stdin                                 false
% 2.38/1.01  --stats_out                             all
% 2.38/1.01  
% 2.38/1.01  ------ General Options
% 2.38/1.01  
% 2.38/1.01  --fof                                   false
% 2.38/1.01  --time_out_real                         305.
% 2.38/1.01  --time_out_virtual                      -1.
% 2.38/1.01  --symbol_type_check                     false
% 2.38/1.01  --clausify_out                          false
% 2.38/1.01  --sig_cnt_out                           false
% 2.38/1.01  --trig_cnt_out                          false
% 2.38/1.01  --trig_cnt_out_tolerance                1.
% 2.38/1.01  --trig_cnt_out_sk_spl                   false
% 2.38/1.01  --abstr_cl_out                          false
% 2.38/1.01  
% 2.38/1.01  ------ Global Options
% 2.38/1.01  
% 2.38/1.01  --schedule                              default
% 2.38/1.01  --add_important_lit                     false
% 2.38/1.01  --prop_solver_per_cl                    1000
% 2.38/1.01  --min_unsat_core                        false
% 2.38/1.01  --soft_assumptions                      false
% 2.38/1.01  --soft_lemma_size                       3
% 2.38/1.01  --prop_impl_unit_size                   0
% 2.38/1.01  --prop_impl_unit                        []
% 2.38/1.01  --share_sel_clauses                     true
% 2.38/1.01  --reset_solvers                         false
% 2.38/1.01  --bc_imp_inh                            [conj_cone]
% 2.38/1.01  --conj_cone_tolerance                   3.
% 2.38/1.01  --extra_neg_conj                        none
% 2.38/1.01  --large_theory_mode                     true
% 2.38/1.01  --prolific_symb_bound                   200
% 2.38/1.01  --lt_threshold                          2000
% 2.38/1.01  --clause_weak_htbl                      true
% 2.38/1.01  --gc_record_bc_elim                     false
% 2.38/1.01  
% 2.38/1.01  ------ Preprocessing Options
% 2.38/1.01  
% 2.38/1.01  --preprocessing_flag                    true
% 2.38/1.01  --time_out_prep_mult                    0.1
% 2.38/1.01  --splitting_mode                        input
% 2.38/1.01  --splitting_grd                         true
% 2.38/1.01  --splitting_cvd                         false
% 2.38/1.01  --splitting_cvd_svl                     false
% 2.38/1.01  --splitting_nvd                         32
% 2.38/1.01  --sub_typing                            true
% 2.38/1.01  --prep_gs_sim                           true
% 2.38/1.01  --prep_unflatten                        true
% 2.38/1.01  --prep_res_sim                          true
% 2.38/1.01  --prep_upred                            true
% 2.38/1.01  --prep_sem_filter                       exhaustive
% 2.38/1.01  --prep_sem_filter_out                   false
% 2.38/1.01  --pred_elim                             true
% 2.38/1.01  --res_sim_input                         true
% 2.38/1.01  --eq_ax_congr_red                       true
% 2.38/1.01  --pure_diseq_elim                       true
% 2.38/1.01  --brand_transform                       false
% 2.38/1.01  --non_eq_to_eq                          false
% 2.38/1.01  --prep_def_merge                        true
% 2.38/1.01  --prep_def_merge_prop_impl              false
% 2.38/1.01  --prep_def_merge_mbd                    true
% 2.38/1.01  --prep_def_merge_tr_red                 false
% 2.38/1.01  --prep_def_merge_tr_cl                  false
% 2.38/1.01  --smt_preprocessing                     true
% 2.38/1.01  --smt_ac_axioms                         fast
% 2.38/1.01  --preprocessed_out                      false
% 2.38/1.01  --preprocessed_stats                    false
% 2.38/1.01  
% 2.38/1.01  ------ Abstraction refinement Options
% 2.38/1.01  
% 2.38/1.01  --abstr_ref                             []
% 2.38/1.01  --abstr_ref_prep                        false
% 2.38/1.01  --abstr_ref_until_sat                   false
% 2.38/1.01  --abstr_ref_sig_restrict                funpre
% 2.38/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.38/1.01  --abstr_ref_under                       []
% 2.38/1.01  
% 2.38/1.01  ------ SAT Options
% 2.38/1.01  
% 2.38/1.01  --sat_mode                              false
% 2.38/1.01  --sat_fm_restart_options                ""
% 2.38/1.01  --sat_gr_def                            false
% 2.38/1.01  --sat_epr_types                         true
% 2.38/1.01  --sat_non_cyclic_types                  false
% 2.38/1.01  --sat_finite_models                     false
% 2.38/1.01  --sat_fm_lemmas                         false
% 2.38/1.01  --sat_fm_prep                           false
% 2.38/1.01  --sat_fm_uc_incr                        true
% 2.38/1.01  --sat_out_model                         small
% 2.38/1.01  --sat_out_clauses                       false
% 2.38/1.01  
% 2.38/1.01  ------ QBF Options
% 2.38/1.01  
% 2.38/1.01  --qbf_mode                              false
% 2.38/1.01  --qbf_elim_univ                         false
% 2.38/1.01  --qbf_dom_inst                          none
% 2.38/1.01  --qbf_dom_pre_inst                      false
% 2.38/1.01  --qbf_sk_in                             false
% 2.38/1.01  --qbf_pred_elim                         true
% 2.38/1.01  --qbf_split                             512
% 2.38/1.01  
% 2.38/1.01  ------ BMC1 Options
% 2.38/1.01  
% 2.38/1.01  --bmc1_incremental                      false
% 2.38/1.01  --bmc1_axioms                           reachable_all
% 2.38/1.01  --bmc1_min_bound                        0
% 2.38/1.01  --bmc1_max_bound                        -1
% 2.38/1.01  --bmc1_max_bound_default                -1
% 2.38/1.01  --bmc1_symbol_reachability              true
% 2.38/1.01  --bmc1_property_lemmas                  false
% 2.38/1.01  --bmc1_k_induction                      false
% 2.38/1.01  --bmc1_non_equiv_states                 false
% 2.38/1.01  --bmc1_deadlock                         false
% 2.38/1.01  --bmc1_ucm                              false
% 2.38/1.01  --bmc1_add_unsat_core                   none
% 2.38/1.01  --bmc1_unsat_core_children              false
% 2.38/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.38/1.01  --bmc1_out_stat                         full
% 2.38/1.01  --bmc1_ground_init                      false
% 2.38/1.01  --bmc1_pre_inst_next_state              false
% 2.38/1.01  --bmc1_pre_inst_state                   false
% 2.38/1.01  --bmc1_pre_inst_reach_state             false
% 2.38/1.01  --bmc1_out_unsat_core                   false
% 2.38/1.01  --bmc1_aig_witness_out                  false
% 2.38/1.01  --bmc1_verbose                          false
% 2.38/1.01  --bmc1_dump_clauses_tptp                false
% 2.38/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.38/1.01  --bmc1_dump_file                        -
% 2.38/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.38/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.38/1.01  --bmc1_ucm_extend_mode                  1
% 2.38/1.01  --bmc1_ucm_init_mode                    2
% 2.38/1.01  --bmc1_ucm_cone_mode                    none
% 2.38/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.38/1.01  --bmc1_ucm_relax_model                  4
% 2.38/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.38/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.38/1.01  --bmc1_ucm_layered_model                none
% 2.38/1.01  --bmc1_ucm_max_lemma_size               10
% 2.38/1.01  
% 2.38/1.01  ------ AIG Options
% 2.38/1.01  
% 2.38/1.01  --aig_mode                              false
% 2.38/1.01  
% 2.38/1.01  ------ Instantiation Options
% 2.38/1.01  
% 2.38/1.01  --instantiation_flag                    true
% 2.38/1.01  --inst_sos_flag                         false
% 2.38/1.01  --inst_sos_phase                        true
% 2.38/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.38/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.38/1.01  --inst_lit_sel_side                     none
% 2.38/1.01  --inst_solver_per_active                1400
% 2.38/1.01  --inst_solver_calls_frac                1.
% 2.38/1.01  --inst_passive_queue_type               priority_queues
% 2.38/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.38/1.01  --inst_passive_queues_freq              [25;2]
% 2.38/1.01  --inst_dismatching                      true
% 2.38/1.01  --inst_eager_unprocessed_to_passive     true
% 2.38/1.01  --inst_prop_sim_given                   true
% 2.38/1.01  --inst_prop_sim_new                     false
% 2.38/1.01  --inst_subs_new                         false
% 2.38/1.01  --inst_eq_res_simp                      false
% 2.38/1.01  --inst_subs_given                       false
% 2.38/1.01  --inst_orphan_elimination               true
% 2.38/1.01  --inst_learning_loop_flag               true
% 2.38/1.01  --inst_learning_start                   3000
% 2.38/1.01  --inst_learning_factor                  2
% 2.38/1.01  --inst_start_prop_sim_after_learn       3
% 2.38/1.01  --inst_sel_renew                        solver
% 2.38/1.01  --inst_lit_activity_flag                true
% 2.38/1.01  --inst_restr_to_given                   false
% 2.38/1.01  --inst_activity_threshold               500
% 2.38/1.01  --inst_out_proof                        true
% 2.38/1.01  
% 2.38/1.01  ------ Resolution Options
% 2.38/1.01  
% 2.38/1.01  --resolution_flag                       false
% 2.38/1.01  --res_lit_sel                           adaptive
% 2.38/1.01  --res_lit_sel_side                      none
% 2.38/1.01  --res_ordering                          kbo
% 2.38/1.01  --res_to_prop_solver                    active
% 2.38/1.01  --res_prop_simpl_new                    false
% 2.38/1.01  --res_prop_simpl_given                  true
% 2.38/1.01  --res_passive_queue_type                priority_queues
% 2.38/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.38/1.01  --res_passive_queues_freq               [15;5]
% 2.38/1.01  --res_forward_subs                      full
% 2.38/1.01  --res_backward_subs                     full
% 2.38/1.01  --res_forward_subs_resolution           true
% 2.38/1.01  --res_backward_subs_resolution          true
% 2.38/1.01  --res_orphan_elimination                true
% 2.38/1.01  --res_time_limit                        2.
% 2.38/1.01  --res_out_proof                         true
% 2.38/1.01  
% 2.38/1.01  ------ Superposition Options
% 2.38/1.01  
% 2.38/1.01  --superposition_flag                    true
% 2.38/1.01  --sup_passive_queue_type                priority_queues
% 2.38/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.38/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.38/1.01  --demod_completeness_check              fast
% 2.38/1.01  --demod_use_ground                      true
% 2.38/1.01  --sup_to_prop_solver                    passive
% 2.38/1.01  --sup_prop_simpl_new                    true
% 2.38/1.01  --sup_prop_simpl_given                  true
% 2.38/1.01  --sup_fun_splitting                     false
% 2.38/1.01  --sup_smt_interval                      50000
% 2.38/1.01  
% 2.38/1.01  ------ Superposition Simplification Setup
% 2.38/1.01  
% 2.38/1.01  --sup_indices_passive                   []
% 2.38/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.38/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.38/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.38/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.38/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.38/1.01  --sup_full_bw                           [BwDemod]
% 2.38/1.01  --sup_immed_triv                        [TrivRules]
% 2.38/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.38/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.38/1.01  --sup_immed_bw_main                     []
% 2.38/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.38/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.38/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.38/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.38/1.01  
% 2.38/1.01  ------ Combination Options
% 2.38/1.01  
% 2.38/1.01  --comb_res_mult                         3
% 2.38/1.01  --comb_sup_mult                         2
% 2.38/1.01  --comb_inst_mult                        10
% 2.38/1.01  
% 2.38/1.01  ------ Debug Options
% 2.38/1.01  
% 2.38/1.01  --dbg_backtrace                         false
% 2.38/1.01  --dbg_dump_prop_clauses                 false
% 2.38/1.01  --dbg_dump_prop_clauses_file            -
% 2.38/1.01  --dbg_out_stat                          false
% 2.38/1.01  
% 2.38/1.01  
% 2.38/1.01  
% 2.38/1.01  
% 2.38/1.01  ------ Proving...
% 2.38/1.01  
% 2.38/1.01  
% 2.38/1.01  % SZS status Theorem for theBenchmark.p
% 2.38/1.01  
% 2.38/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.38/1.01  
% 2.38/1.01  fof(f7,axiom,(
% 2.38/1.01    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 2.38/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.38/1.01  
% 2.38/1.01  fof(f41,plain,(
% 2.38/1.01    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 2.38/1.01    inference(nnf_transformation,[],[f7])).
% 2.38/1.01  
% 2.38/1.01  fof(f42,plain,(
% 2.38/1.01    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 2.38/1.01    inference(rectify,[],[f41])).
% 2.38/1.01  
% 2.38/1.01  fof(f45,plain,(
% 2.38/1.01    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0))),
% 2.38/1.01    introduced(choice_axiom,[])).
% 2.38/1.01  
% 2.38/1.01  fof(f44,plain,(
% 2.38/1.01    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) => r2_hidden(k4_tarski(X2,sK7(X0,X1)),X0))) )),
% 2.38/1.01    introduced(choice_axiom,[])).
% 2.38/1.01  
% 2.38/1.01  fof(f43,plain,(
% 2.38/1.01    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK6(X0,X1),X3),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0) | r2_hidden(sK6(X0,X1),X1))))),
% 2.38/1.01    introduced(choice_axiom,[])).
% 2.38/1.01  
% 2.38/1.01  fof(f46,plain,(
% 2.38/1.01    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK6(X0,X1),X3),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0) | r2_hidden(sK6(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 2.38/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f42,f45,f44,f43])).
% 2.38/1.01  
% 2.38/1.01  fof(f69,plain,(
% 2.38/1.01    ( ! [X0,X1] : (k1_relat_1(X0) = X1 | r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0) | r2_hidden(sK6(X0,X1),X1)) )),
% 2.38/1.01    inference(cnf_transformation,[],[f46])).
% 2.38/1.01  
% 2.38/1.01  fof(f13,conjecture,(
% 2.38/1.01    ! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k9_relat_1(X1,X0) & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0))),
% 2.38/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.38/1.01  
% 2.38/1.01  fof(f14,negated_conjecture,(
% 2.38/1.01    ~! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k9_relat_1(X1,X0) & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0))),
% 2.38/1.01    inference(negated_conjecture,[],[f13])).
% 2.38/1.01  
% 2.38/1.01  fof(f23,plain,(
% 2.38/1.01    ? [X0,X1] : ((k1_xboole_0 = k9_relat_1(X1,X0) & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0) & v1_relat_1(X1))),
% 2.38/1.01    inference(ennf_transformation,[],[f14])).
% 2.38/1.01  
% 2.38/1.01  fof(f24,plain,(
% 2.38/1.01    ? [X0,X1] : (k1_xboole_0 = k9_relat_1(X1,X0) & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0 & v1_relat_1(X1))),
% 2.38/1.01    inference(flattening,[],[f23])).
% 2.38/1.01  
% 2.38/1.01  fof(f51,plain,(
% 2.38/1.01    ? [X0,X1] : (k1_xboole_0 = k9_relat_1(X1,X0) & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0 & v1_relat_1(X1)) => (k1_xboole_0 = k9_relat_1(sK11,sK10) & r1_tarski(sK10,k1_relat_1(sK11)) & k1_xboole_0 != sK10 & v1_relat_1(sK11))),
% 2.38/1.01    introduced(choice_axiom,[])).
% 2.38/1.01  
% 2.38/1.01  fof(f52,plain,(
% 2.38/1.01    k1_xboole_0 = k9_relat_1(sK11,sK10) & r1_tarski(sK10,k1_relat_1(sK11)) & k1_xboole_0 != sK10 & v1_relat_1(sK11)),
% 2.38/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11])],[f24,f51])).
% 2.38/1.01  
% 2.38/1.01  fof(f83,plain,(
% 2.38/1.01    k1_xboole_0 = k9_relat_1(sK11,sK10)),
% 2.38/1.01    inference(cnf_transformation,[],[f52])).
% 2.38/1.01  
% 2.38/1.01  fof(f8,axiom,(
% 2.38/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 2.38/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.38/1.01  
% 2.38/1.01  fof(f19,plain,(
% 2.38/1.01    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 2.38/1.01    inference(ennf_transformation,[],[f8])).
% 2.38/1.01  
% 2.38/1.01  fof(f47,plain,(
% 2.38/1.01    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 2.38/1.01    inference(nnf_transformation,[],[f19])).
% 2.38/1.01  
% 2.38/1.01  fof(f48,plain,(
% 2.38/1.01    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 2.38/1.01    inference(rectify,[],[f47])).
% 2.38/1.01  
% 2.38/1.01  fof(f49,plain,(
% 2.38/1.01    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK9(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK9(X0,X1,X2),X0),X2) & r2_hidden(sK9(X0,X1,X2),k1_relat_1(X2))))),
% 2.38/1.01    introduced(choice_axiom,[])).
% 2.38/1.01  
% 2.38/1.01  fof(f50,plain,(
% 2.38/1.01    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK9(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK9(X0,X1,X2),X0),X2) & r2_hidden(sK9(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 2.38/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f48,f49])).
% 2.38/1.01  
% 2.38/1.01  fof(f71,plain,(
% 2.38/1.01    ( ! [X2,X0,X1] : (r2_hidden(sK9(X0,X1,X2),k1_relat_1(X2)) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 2.38/1.01    inference(cnf_transformation,[],[f50])).
% 2.38/1.01  
% 2.38/1.01  fof(f80,plain,(
% 2.38/1.01    v1_relat_1(sK11)),
% 2.38/1.01    inference(cnf_transformation,[],[f52])).
% 2.38/1.01  
% 2.38/1.01  fof(f72,plain,(
% 2.38/1.01    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK9(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 2.38/1.01    inference(cnf_transformation,[],[f50])).
% 2.38/1.01  
% 2.38/1.01  fof(f6,axiom,(
% 2.38/1.01    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)))))),
% 2.38/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.38/1.01  
% 2.38/1.01  fof(f18,plain,(
% 2.38/1.01    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)))) | ~v1_relat_1(X0))),
% 2.38/1.01    inference(ennf_transformation,[],[f6])).
% 2.38/1.01  
% 2.38/1.01  fof(f35,plain,(
% 2.38/1.01    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,X3),X0)) | ~r2_hidden(X3,X2)) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,X3),X0))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)) | ~r2_hidden(X3,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 2.38/1.01    inference(nnf_transformation,[],[f18])).
% 2.38/1.01  
% 2.38/1.01  fof(f36,plain,(
% 2.38/1.01    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,X3),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X3),X0)) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X7,X6),X0))) & (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X8,X6),X0)) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 2.38/1.01    inference(rectify,[],[f35])).
% 2.38/1.01  
% 2.38/1.01  fof(f39,plain,(
% 2.38/1.01    ! [X6,X1,X0] : (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X8,X6),X0)) => (r2_hidden(sK5(X0,X1,X6),X1) & r2_hidden(k4_tarski(sK5(X0,X1,X6),X6),X0)))),
% 2.38/1.01    introduced(choice_axiom,[])).
% 2.38/1.01  
% 2.38/1.01  fof(f38,plain,(
% 2.38/1.01    ( ! [X3] : (! [X2,X1,X0] : (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X3),X0)) => (r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK4(X0,X1,X2),X3),X0)))) )),
% 2.38/1.01    introduced(choice_axiom,[])).
% 2.38/1.01  
% 2.38/1.01  fof(f37,plain,(
% 2.38/1.01    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,X3),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X3),X0)) | r2_hidden(X3,X2))) => ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,sK3(X0,X1,X2)),X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,sK3(X0,X1,X2)),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 2.38/1.01    introduced(choice_axiom,[])).
% 2.38/1.01  
% 2.38/1.01  fof(f40,plain,(
% 2.38/1.01    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,sK3(X0,X1,X2)),X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK4(X0,X1,X2),sK3(X0,X1,X2)),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X7,X6),X0))) & ((r2_hidden(sK5(X0,X1,X6),X1) & r2_hidden(k4_tarski(sK5(X0,X1,X6),X6),X0)) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 2.38/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f36,f39,f38,f37])).
% 2.38/1.01  
% 2.38/1.01  fof(f63,plain,(
% 2.38/1.01    ( ! [X6,X2,X0,X7,X1] : (r2_hidden(X6,X2) | ~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X7,X6),X0) | k9_relat_1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 2.38/1.01    inference(cnf_transformation,[],[f40])).
% 2.38/1.01  
% 2.38/1.01  fof(f84,plain,(
% 2.38/1.01    ( ! [X6,X0,X7,X1] : (r2_hidden(X6,k9_relat_1(X0,X1)) | ~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X7,X6),X0) | ~v1_relat_1(X0)) )),
% 2.38/1.01    inference(equality_resolution,[],[f63])).
% 2.38/1.01  
% 2.38/1.01  fof(f1,axiom,(
% 2.38/1.01    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.38/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.38/1.01  
% 2.38/1.01  fof(f25,plain,(
% 2.38/1.01    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.38/1.01    inference(nnf_transformation,[],[f1])).
% 2.38/1.01  
% 2.38/1.01  fof(f26,plain,(
% 2.38/1.01    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.38/1.01    inference(rectify,[],[f25])).
% 2.38/1.01  
% 2.38/1.01  fof(f27,plain,(
% 2.38/1.01    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.38/1.01    introduced(choice_axiom,[])).
% 2.38/1.01  
% 2.38/1.01  fof(f28,plain,(
% 2.38/1.01    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.38/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).
% 2.38/1.01  
% 2.38/1.01  fof(f53,plain,(
% 2.38/1.01    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 2.38/1.01    inference(cnf_transformation,[],[f28])).
% 2.38/1.01  
% 2.38/1.01  fof(f3,axiom,(
% 2.38/1.01    v1_xboole_0(k1_xboole_0)),
% 2.38/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.38/1.01  
% 2.38/1.01  fof(f58,plain,(
% 2.38/1.01    v1_xboole_0(k1_xboole_0)),
% 2.38/1.01    inference(cnf_transformation,[],[f3])).
% 2.38/1.01  
% 2.38/1.01  fof(f11,axiom,(
% 2.38/1.01    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 2.38/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.38/1.01  
% 2.38/1.01  fof(f78,plain,(
% 2.38/1.01    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 2.38/1.01    inference(cnf_transformation,[],[f11])).
% 2.38/1.01  
% 2.38/1.01  fof(f10,axiom,(
% 2.38/1.01    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.38/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.38/1.01  
% 2.38/1.01  fof(f76,plain,(
% 2.38/1.01    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 2.38/1.01    inference(cnf_transformation,[],[f10])).
% 2.38/1.01  
% 2.38/1.01  fof(f67,plain,(
% 2.38/1.01    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 2.38/1.01    inference(cnf_transformation,[],[f46])).
% 2.38/1.01  
% 2.38/1.01  fof(f88,plain,(
% 2.38/1.01    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 2.38/1.01    inference(equality_resolution,[],[f67])).
% 2.38/1.01  
% 2.38/1.01  fof(f2,axiom,(
% 2.38/1.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.38/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.38/1.01  
% 2.38/1.01  fof(f15,plain,(
% 2.38/1.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.38/1.01    inference(ennf_transformation,[],[f2])).
% 2.38/1.01  
% 2.38/1.01  fof(f29,plain,(
% 2.38/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.38/1.01    inference(nnf_transformation,[],[f15])).
% 2.38/1.01  
% 2.38/1.01  fof(f30,plain,(
% 2.38/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.38/1.01    inference(rectify,[],[f29])).
% 2.38/1.01  
% 2.38/1.01  fof(f31,plain,(
% 2.38/1.01    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 2.38/1.01    introduced(choice_axiom,[])).
% 2.38/1.01  
% 2.38/1.01  fof(f32,plain,(
% 2.38/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.38/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f31])).
% 2.38/1.01  
% 2.38/1.01  fof(f55,plain,(
% 2.38/1.01    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 2.38/1.01    inference(cnf_transformation,[],[f32])).
% 2.38/1.01  
% 2.38/1.01  fof(f82,plain,(
% 2.38/1.01    r1_tarski(sK10,k1_relat_1(sK11))),
% 2.38/1.01    inference(cnf_transformation,[],[f52])).
% 2.38/1.01  
% 2.38/1.01  fof(f81,plain,(
% 2.38/1.01    k1_xboole_0 != sK10),
% 2.38/1.01    inference(cnf_transformation,[],[f52])).
% 2.38/1.01  
% 2.38/1.01  cnf(c_15,plain,
% 2.38/1.01      ( r2_hidden(sK6(X0,X1),X1)
% 2.38/1.01      | r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0)
% 2.38/1.01      | k1_relat_1(X0) = X1 ),
% 2.38/1.01      inference(cnf_transformation,[],[f69]) ).
% 2.38/1.01  
% 2.38/1.01  cnf(c_1482,plain,
% 2.38/1.01      ( k1_relat_1(X0) = X1
% 2.38/1.01      | r2_hidden(sK6(X0,X1),X1) = iProver_top
% 2.38/1.01      | r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0) = iProver_top ),
% 2.38/1.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.38/1.01  
% 2.38/1.01  cnf(c_27,negated_conjecture,
% 2.38/1.01      ( k1_xboole_0 = k9_relat_1(sK11,sK10) ),
% 2.38/1.01      inference(cnf_transformation,[],[f83]) ).
% 2.38/1.01  
% 2.38/1.01  cnf(c_21,plain,
% 2.38/1.01      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 2.38/1.01      | r2_hidden(sK9(X0,X2,X1),k1_relat_1(X1))
% 2.38/1.01      | ~ v1_relat_1(X1) ),
% 2.38/1.01      inference(cnf_transformation,[],[f71]) ).
% 2.38/1.01  
% 2.38/1.01  cnf(c_30,negated_conjecture,
% 2.38/1.01      ( v1_relat_1(sK11) ),
% 2.38/1.01      inference(cnf_transformation,[],[f80]) ).
% 2.38/1.01  
% 2.38/1.01  cnf(c_631,plain,
% 2.38/1.01      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 2.38/1.01      | r2_hidden(sK9(X0,X2,X1),k1_relat_1(X1))
% 2.38/1.01      | sK11 != X1 ),
% 2.38/1.01      inference(resolution_lifted,[status(thm)],[c_21,c_30]) ).
% 2.38/1.01  
% 2.38/1.01  cnf(c_632,plain,
% 2.38/1.01      ( ~ r2_hidden(X0,k9_relat_1(sK11,X1))
% 2.38/1.01      | r2_hidden(sK9(X0,X1,sK11),k1_relat_1(sK11)) ),
% 2.38/1.01      inference(unflattening,[status(thm)],[c_631]) ).
% 2.38/1.01  
% 2.38/1.01  cnf(c_1469,plain,
% 2.38/1.01      ( r2_hidden(X0,k9_relat_1(sK11,X1)) != iProver_top
% 2.38/1.01      | r2_hidden(sK9(X0,X1,sK11),k1_relat_1(sK11)) = iProver_top ),
% 2.38/1.01      inference(predicate_to_equality,[status(thm)],[c_632]) ).
% 2.38/1.01  
% 2.38/1.01  cnf(c_20,plain,
% 2.38/1.01      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 2.38/1.01      | r2_hidden(k4_tarski(sK9(X0,X2,X1),X0),X1)
% 2.38/1.01      | ~ v1_relat_1(X1) ),
% 2.38/1.01      inference(cnf_transformation,[],[f72]) ).
% 2.38/1.01  
% 2.38/1.01  cnf(c_643,plain,
% 2.38/1.01      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 2.38/1.01      | r2_hidden(k4_tarski(sK9(X0,X2,X1),X0),X1)
% 2.38/1.01      | sK11 != X1 ),
% 2.38/1.01      inference(resolution_lifted,[status(thm)],[c_20,c_30]) ).
% 2.38/1.01  
% 2.38/1.01  cnf(c_644,plain,
% 2.38/1.01      ( ~ r2_hidden(X0,k9_relat_1(sK11,X1))
% 2.38/1.01      | r2_hidden(k4_tarski(sK9(X0,X1,sK11),X0),sK11) ),
% 2.38/1.01      inference(unflattening,[status(thm)],[c_643]) ).
% 2.38/1.01  
% 2.38/1.01  cnf(c_1468,plain,
% 2.38/1.01      ( r2_hidden(X0,k9_relat_1(sK11,X1)) != iProver_top
% 2.38/1.01      | r2_hidden(k4_tarski(sK9(X0,X1,sK11),X0),sK11) = iProver_top ),
% 2.38/1.01      inference(predicate_to_equality,[status(thm)],[c_644]) ).
% 2.38/1.01  
% 2.38/1.01  cnf(c_11,plain,
% 2.38/1.01      ( ~ r2_hidden(X0,X1)
% 2.38/1.01      | r2_hidden(X2,k9_relat_1(X3,X1))
% 2.38/1.01      | ~ r2_hidden(k4_tarski(X0,X2),X3)
% 2.38/1.01      | ~ v1_relat_1(X3) ),
% 2.38/1.01      inference(cnf_transformation,[],[f84]) ).
% 2.38/1.01  
% 2.38/1.01  cnf(c_618,plain,
% 2.38/1.01      ( ~ r2_hidden(X0,X1)
% 2.38/1.01      | r2_hidden(X2,k9_relat_1(X3,X1))
% 2.38/1.01      | ~ r2_hidden(k4_tarski(X0,X2),X3)
% 2.38/1.01      | sK11 != X3 ),
% 2.38/1.01      inference(resolution_lifted,[status(thm)],[c_11,c_30]) ).
% 2.38/1.01  
% 2.38/1.01  cnf(c_619,plain,
% 2.38/1.01      ( ~ r2_hidden(X0,X1)
% 2.38/1.01      | r2_hidden(X2,k9_relat_1(sK11,X1))
% 2.38/1.01      | ~ r2_hidden(k4_tarski(X0,X2),sK11) ),
% 2.38/1.01      inference(unflattening,[status(thm)],[c_618]) ).
% 2.38/1.01  
% 2.38/1.01  cnf(c_1470,plain,
% 2.38/1.01      ( r2_hidden(X0,X1) != iProver_top
% 2.38/1.01      | r2_hidden(X2,k9_relat_1(sK11,X1)) = iProver_top
% 2.38/1.01      | r2_hidden(k4_tarski(X0,X2),sK11) != iProver_top ),
% 2.38/1.01      inference(predicate_to_equality,[status(thm)],[c_619]) ).
% 2.38/1.01  
% 2.38/1.01  cnf(c_2189,plain,
% 2.38/1.01      ( r2_hidden(X0,k9_relat_1(sK11,X1)) != iProver_top
% 2.38/1.01      | r2_hidden(X0,k9_relat_1(sK11,X2)) = iProver_top
% 2.38/1.01      | r2_hidden(sK9(X0,X1,sK11),X2) != iProver_top ),
% 2.38/1.01      inference(superposition,[status(thm)],[c_1468,c_1470]) ).
% 2.38/1.01  
% 2.38/1.01  cnf(c_2473,plain,
% 2.38/1.01      ( r2_hidden(X0,k9_relat_1(sK11,X1)) != iProver_top
% 2.38/1.01      | r2_hidden(X0,k9_relat_1(sK11,k1_relat_1(sK11))) = iProver_top ),
% 2.38/1.01      inference(superposition,[status(thm)],[c_1469,c_2189]) ).
% 2.38/1.01  
% 2.38/1.01  cnf(c_2489,plain,
% 2.38/1.01      ( r2_hidden(X0,k9_relat_1(sK11,k1_relat_1(sK11))) = iProver_top
% 2.38/1.01      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.38/1.01      inference(superposition,[status(thm)],[c_27,c_2473]) ).
% 2.38/1.01  
% 2.38/1.01  cnf(c_1,plain,
% 2.38/1.01      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 2.38/1.01      inference(cnf_transformation,[],[f53]) ).
% 2.38/1.01  
% 2.38/1.01  cnf(c_5,plain,
% 2.38/1.01      ( v1_xboole_0(k1_xboole_0) ),
% 2.38/1.01      inference(cnf_transformation,[],[f58]) ).
% 2.38/1.01  
% 2.38/1.01  cnf(c_334,plain,
% 2.38/1.01      ( ~ r2_hidden(X0,X1) | k1_xboole_0 != X1 ),
% 2.38/1.01      inference(resolution_lifted,[status(thm)],[c_1,c_5]) ).
% 2.38/1.01  
% 2.38/1.01  cnf(c_335,plain,
% 2.38/1.01      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 2.38/1.01      inference(unflattening,[status(thm)],[c_334]) ).
% 2.38/1.01  
% 2.38/1.01  cnf(c_336,plain,
% 2.38/1.01      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.38/1.01      inference(predicate_to_equality,[status(thm)],[c_335]) ).
% 2.38/1.01  
% 2.38/1.01  cnf(c_2623,plain,
% 2.38/1.01      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.38/1.01      inference(global_propositional_subsumption,
% 2.38/1.01                [status(thm)],
% 2.38/1.01                [c_2489,c_336]) ).
% 2.38/1.01  
% 2.38/1.01  cnf(c_5267,plain,
% 2.38/1.01      ( k1_relat_1(k1_xboole_0) = X0
% 2.38/1.01      | r2_hidden(sK6(k1_xboole_0,X0),X0) = iProver_top ),
% 2.38/1.01      inference(superposition,[status(thm)],[c_1482,c_2623]) ).
% 2.38/1.01  
% 2.38/1.01  cnf(c_25,plain,
% 2.38/1.01      ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.38/1.01      inference(cnf_transformation,[],[f78]) ).
% 2.38/1.01  
% 2.38/1.01  cnf(c_24,plain,
% 2.38/1.01      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 2.38/1.01      inference(cnf_transformation,[],[f76]) ).
% 2.38/1.01  
% 2.38/1.01  cnf(c_1846,plain,
% 2.38/1.01      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.38/1.01      inference(superposition,[status(thm)],[c_25,c_24]) ).
% 2.38/1.01  
% 2.38/1.01  cnf(c_5307,plain,
% 2.38/1.01      ( k1_xboole_0 = X0
% 2.38/1.01      | r2_hidden(sK6(k1_xboole_0,X0),X0) = iProver_top ),
% 2.38/1.01      inference(demodulation,[status(thm)],[c_5267,c_1846]) ).
% 2.38/1.01  
% 2.38/1.01  cnf(c_17,plain,
% 2.38/1.01      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.38/1.01      | r2_hidden(k4_tarski(X0,sK8(X1,X0)),X1) ),
% 2.38/1.01      inference(cnf_transformation,[],[f88]) ).
% 2.38/1.01  
% 2.38/1.01  cnf(c_1480,plain,
% 2.38/1.01      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 2.38/1.01      | r2_hidden(k4_tarski(X0,sK8(X1,X0)),X1) = iProver_top ),
% 2.38/1.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.38/1.01  
% 2.38/1.01  cnf(c_5019,plain,
% 2.38/1.01      ( r2_hidden(X0,X1) != iProver_top
% 2.38/1.01      | r2_hidden(X0,k1_relat_1(sK11)) != iProver_top
% 2.38/1.01      | r2_hidden(sK8(sK11,X0),k9_relat_1(sK11,X1)) = iProver_top ),
% 2.38/1.01      inference(superposition,[status(thm)],[c_1480,c_1470]) ).
% 2.38/1.01  
% 2.38/1.01  cnf(c_8895,plain,
% 2.38/1.01      ( r2_hidden(X0,k1_relat_1(sK11)) != iProver_top
% 2.38/1.01      | r2_hidden(X0,sK10) != iProver_top
% 2.38/1.01      | r2_hidden(sK8(sK11,X0),k1_xboole_0) = iProver_top ),
% 2.38/1.01      inference(superposition,[status(thm)],[c_27,c_5019]) ).
% 2.38/1.01  
% 2.38/1.01  cnf(c_4,plain,
% 2.38/1.01      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 2.38/1.01      inference(cnf_transformation,[],[f55]) ).
% 2.38/1.01  
% 2.38/1.01  cnf(c_28,negated_conjecture,
% 2.38/1.01      ( r1_tarski(sK10,k1_relat_1(sK11)) ),
% 2.38/1.01      inference(cnf_transformation,[],[f82]) ).
% 2.38/1.01  
% 2.38/1.01  cnf(c_403,plain,
% 2.38/1.01      ( ~ r2_hidden(X0,X1)
% 2.38/1.01      | r2_hidden(X0,X2)
% 2.38/1.01      | k1_relat_1(sK11) != X2
% 2.38/1.01      | sK10 != X1 ),
% 2.38/1.01      inference(resolution_lifted,[status(thm)],[c_4,c_28]) ).
% 2.38/1.01  
% 2.38/1.01  cnf(c_404,plain,
% 2.38/1.01      ( r2_hidden(X0,k1_relat_1(sK11)) | ~ r2_hidden(X0,sK10) ),
% 2.38/1.01      inference(unflattening,[status(thm)],[c_403]) ).
% 2.38/1.01  
% 2.38/1.01  cnf(c_405,plain,
% 2.38/1.01      ( r2_hidden(X0,k1_relat_1(sK11)) = iProver_top
% 2.38/1.01      | r2_hidden(X0,sK10) != iProver_top ),
% 2.38/1.01      inference(predicate_to_equality,[status(thm)],[c_404]) ).
% 2.38/1.01  
% 2.38/1.01  cnf(c_9057,plain,
% 2.38/1.01      ( r2_hidden(X0,sK10) != iProver_top
% 2.38/1.01      | r2_hidden(sK8(sK11,X0),k1_xboole_0) = iProver_top ),
% 2.38/1.01      inference(global_propositional_subsumption,
% 2.38/1.01                [status(thm)],
% 2.38/1.01                [c_8895,c_405]) ).
% 2.38/1.01  
% 2.38/1.01  cnf(c_9065,plain,
% 2.38/1.01      ( r2_hidden(X0,sK10) != iProver_top ),
% 2.38/1.01      inference(forward_subsumption_resolution,
% 2.38/1.01                [status(thm)],
% 2.38/1.01                [c_9057,c_2623]) ).
% 2.38/1.01  
% 2.38/1.01  cnf(c_9080,plain,
% 2.38/1.01      ( sK10 = k1_xboole_0 ),
% 2.38/1.01      inference(superposition,[status(thm)],[c_5307,c_9065]) ).
% 2.38/1.01  
% 2.38/1.01  cnf(c_1003,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.38/1.01  
% 2.38/1.01  cnf(c_1692,plain,
% 2.38/1.01      ( sK10 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK10 ),
% 2.38/1.01      inference(instantiation,[status(thm)],[c_1003]) ).
% 2.38/1.01  
% 2.38/1.01  cnf(c_1693,plain,
% 2.38/1.01      ( sK10 != k1_xboole_0
% 2.38/1.01      | k1_xboole_0 = sK10
% 2.38/1.01      | k1_xboole_0 != k1_xboole_0 ),
% 2.38/1.01      inference(instantiation,[status(thm)],[c_1692]) ).
% 2.38/1.01  
% 2.38/1.01  cnf(c_1002,plain,( X0 = X0 ),theory(equality) ).
% 2.38/1.01  
% 2.38/1.01  cnf(c_1031,plain,
% 2.38/1.01      ( k1_xboole_0 = k1_xboole_0 ),
% 2.38/1.01      inference(instantiation,[status(thm)],[c_1002]) ).
% 2.38/1.01  
% 2.38/1.01  cnf(c_29,negated_conjecture,
% 2.38/1.01      ( k1_xboole_0 != sK10 ),
% 2.38/1.01      inference(cnf_transformation,[],[f81]) ).
% 2.38/1.01  
% 2.38/1.01  cnf(contradiction,plain,
% 2.38/1.01      ( $false ),
% 2.38/1.01      inference(minisat,[status(thm)],[c_9080,c_1693,c_1031,c_29]) ).
% 2.38/1.01  
% 2.38/1.01  
% 2.38/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.38/1.01  
% 2.38/1.01  ------                               Statistics
% 2.38/1.01  
% 2.38/1.01  ------ General
% 2.38/1.01  
% 2.38/1.01  abstr_ref_over_cycles:                  0
% 2.38/1.01  abstr_ref_under_cycles:                 0
% 2.38/1.01  gc_basic_clause_elim:                   0
% 2.38/1.01  forced_gc_time:                         0
% 2.38/1.01  parsing_time:                           0.03
% 2.38/1.01  unif_index_cands_time:                  0.
% 2.38/1.01  unif_index_add_time:                    0.
% 2.38/1.01  orderings_time:                         0.
% 2.38/1.01  out_proof_time:                         0.008
% 2.38/1.01  total_time:                             0.312
% 2.38/1.01  num_of_symbols:                         54
% 2.38/1.01  num_of_terms:                           8614
% 2.38/1.01  
% 2.38/1.01  ------ Preprocessing
% 2.38/1.01  
% 2.38/1.01  num_of_splits:                          0
% 2.38/1.01  num_of_split_atoms:                     0
% 2.38/1.01  num_of_reused_defs:                     0
% 2.38/1.01  num_eq_ax_congr_red:                    43
% 2.38/1.01  num_of_sem_filtered_clauses:            1
% 2.38/1.01  num_of_subtypes:                        0
% 2.38/1.01  monotx_restored_types:                  0
% 2.38/1.01  sat_num_of_epr_types:                   0
% 2.38/1.01  sat_num_of_non_cyclic_types:            0
% 2.38/1.01  sat_guarded_non_collapsed_types:        0
% 2.38/1.01  num_pure_diseq_elim:                    0
% 2.38/1.01  simp_replaced_by:                       0
% 2.38/1.01  res_preprocessed:                       125
% 2.38/1.01  prep_upred:                             0
% 2.38/1.01  prep_unflattend:                        47
% 2.38/1.01  smt_new_axioms:                         0
% 2.38/1.01  pred_elim_cands:                        4
% 2.38/1.01  pred_elim:                              1
% 2.38/1.01  pred_elim_cl:                           -2
% 2.38/1.01  pred_elim_cycles:                       5
% 2.38/1.01  merged_defs:                            0
% 2.38/1.01  merged_defs_ncl:                        0
% 2.38/1.01  bin_hyper_res:                          0
% 2.38/1.01  prep_cycles:                            3
% 2.38/1.01  pred_elim_time:                         0.023
% 2.38/1.01  splitting_time:                         0.
% 2.38/1.01  sem_filter_time:                        0.
% 2.38/1.01  monotx_time:                            0.
% 2.38/1.01  subtype_inf_time:                       0.
% 2.38/1.01  
% 2.38/1.01  ------ Problem properties
% 2.38/1.01  
% 2.38/1.01  clauses:                                32
% 2.38/1.01  conjectures:                            3
% 2.38/1.01  epr:                                    4
% 2.38/1.01  horn:                                   25
% 2.38/1.01  ground:                                 5
% 2.38/1.01  unary:                                  8
% 2.38/1.01  binary:                                 15
% 2.38/1.01  lits:                                   66
% 2.38/1.01  lits_eq:                                16
% 2.38/1.01  fd_pure:                                0
% 2.38/1.01  fd_pseudo:                              0
% 2.38/1.01  fd_cond:                                1
% 2.38/1.01  fd_pseudo_cond:                         6
% 2.38/1.01  ac_symbols:                             0
% 2.38/1.01  
% 2.38/1.01  ------ Propositional Solver
% 2.38/1.01  
% 2.38/1.01  prop_solver_calls:                      24
% 2.38/1.01  prop_fast_solver_calls:                 885
% 2.38/1.01  smt_solver_calls:                       0
% 2.38/1.01  smt_fast_solver_calls:                  0
% 2.38/1.01  prop_num_of_clauses:                    3635
% 2.38/1.01  prop_preprocess_simplified:             8879
% 2.38/1.01  prop_fo_subsumed:                       10
% 2.38/1.01  prop_solver_time:                       0.
% 2.38/1.01  smt_solver_time:                        0.
% 2.38/1.01  smt_fast_solver_time:                   0.
% 2.38/1.01  prop_fast_solver_time:                  0.
% 2.38/1.01  prop_unsat_core_time:                   0.
% 2.38/1.01  
% 2.38/1.01  ------ QBF
% 2.38/1.01  
% 2.38/1.01  qbf_q_res:                              0
% 2.38/1.01  qbf_num_tautologies:                    0
% 2.38/1.01  qbf_prep_cycles:                        0
% 2.38/1.01  
% 2.38/1.01  ------ BMC1
% 2.38/1.01  
% 2.38/1.01  bmc1_current_bound:                     -1
% 2.38/1.01  bmc1_last_solved_bound:                 -1
% 2.38/1.01  bmc1_unsat_core_size:                   -1
% 2.38/1.01  bmc1_unsat_core_parents_size:           -1
% 2.38/1.01  bmc1_merge_next_fun:                    0
% 2.38/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.38/1.01  
% 2.38/1.01  ------ Instantiation
% 2.38/1.01  
% 2.38/1.01  inst_num_of_clauses:                    1011
% 2.38/1.01  inst_num_in_passive:                    431
% 2.38/1.01  inst_num_in_active:                     374
% 2.38/1.01  inst_num_in_unprocessed:                206
% 2.38/1.01  inst_num_of_loops:                      440
% 2.38/1.01  inst_num_of_learning_restarts:          0
% 2.38/1.01  inst_num_moves_active_passive:          62
% 2.38/1.01  inst_lit_activity:                      0
% 2.38/1.01  inst_lit_activity_moves:                0
% 2.38/1.01  inst_num_tautologies:                   0
% 2.38/1.01  inst_num_prop_implied:                  0
% 2.38/1.01  inst_num_existing_simplified:           0
% 2.38/1.01  inst_num_eq_res_simplified:             0
% 2.38/1.01  inst_num_child_elim:                    0
% 2.38/1.01  inst_num_of_dismatching_blockings:      196
% 2.38/1.01  inst_num_of_non_proper_insts:           704
% 2.38/1.01  inst_num_of_duplicates:                 0
% 2.38/1.01  inst_inst_num_from_inst_to_res:         0
% 2.38/1.01  inst_dismatching_checking_time:         0.
% 2.38/1.01  
% 2.38/1.01  ------ Resolution
% 2.38/1.01  
% 2.38/1.01  res_num_of_clauses:                     0
% 2.38/1.01  res_num_in_passive:                     0
% 2.38/1.01  res_num_in_active:                      0
% 2.38/1.01  res_num_of_loops:                       128
% 2.38/1.01  res_forward_subset_subsumed:            27
% 2.38/1.01  res_backward_subset_subsumed:           0
% 2.38/1.01  res_forward_subsumed:                   5
% 2.38/1.01  res_backward_subsumed:                  1
% 2.38/1.01  res_forward_subsumption_resolution:     2
% 2.38/1.01  res_backward_subsumption_resolution:    0
% 2.38/1.01  res_clause_to_clause_subsumption:       711
% 2.38/1.01  res_orphan_elimination:                 0
% 2.38/1.01  res_tautology_del:                      26
% 2.38/1.01  res_num_eq_res_simplified:              0
% 2.38/1.01  res_num_sel_changes:                    0
% 2.38/1.01  res_moves_from_active_to_pass:          0
% 2.38/1.01  
% 2.38/1.01  ------ Superposition
% 2.38/1.01  
% 2.38/1.01  sup_time_total:                         0.
% 2.38/1.01  sup_time_generating:                    0.
% 2.38/1.01  sup_time_sim_full:                      0.
% 2.38/1.01  sup_time_sim_immed:                     0.
% 2.38/1.01  
% 2.38/1.01  sup_num_of_clauses:                     213
% 2.38/1.01  sup_num_in_active:                      83
% 2.38/1.01  sup_num_in_passive:                     130
% 2.38/1.01  sup_num_of_loops:                       86
% 2.38/1.01  sup_fw_superposition:                   230
% 2.38/1.01  sup_bw_superposition:                   104
% 2.38/1.01  sup_immediate_simplified:               66
% 2.38/1.01  sup_given_eliminated:                   2
% 2.38/1.01  comparisons_done:                       0
% 2.38/1.01  comparisons_avoided:                    0
% 2.38/1.01  
% 2.38/1.01  ------ Simplifications
% 2.38/1.01  
% 2.38/1.01  
% 2.38/1.01  sim_fw_subset_subsumed:                 26
% 2.38/1.01  sim_bw_subset_subsumed:                 1
% 2.38/1.01  sim_fw_subsumed:                        20
% 2.38/1.01  sim_bw_subsumed:                        1
% 2.38/1.01  sim_fw_subsumption_res:                 1
% 2.38/1.01  sim_bw_subsumption_res:                 0
% 2.38/1.01  sim_tautology_del:                      8
% 2.38/1.01  sim_eq_tautology_del:                   11
% 2.38/1.01  sim_eq_res_simp:                        0
% 2.38/1.01  sim_fw_demodulated:                     3
% 2.38/1.01  sim_bw_demodulated:                     8
% 2.38/1.01  sim_light_normalised:                   30
% 2.38/1.01  sim_joinable_taut:                      0
% 2.38/1.01  sim_joinable_simp:                      0
% 2.38/1.01  sim_ac_normalised:                      0
% 2.38/1.01  sim_smt_subsumption:                    0
% 2.38/1.01  
%------------------------------------------------------------------------------
