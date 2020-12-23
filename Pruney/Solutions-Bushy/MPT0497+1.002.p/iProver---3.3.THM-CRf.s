%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0497+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:26 EST 2020

% Result     : Theorem 7.71s
% Output     : CNFRefutation 7.71s
% Verified   : 
% Statistics : Number of formulae       :  145 (1233 expanded)
%              Number of clauses        :   82 ( 430 expanded)
%              Number of leaves         :   18 ( 257 expanded)
%              Depth                    :   28
%              Number of atoms          :  526 (6000 expanded)
%              Number of equality atoms :  186 (1456 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
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

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f38,plain,(
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

fof(f39,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f37,f38])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK5(X0,X1,X2),X1)
      | r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f10,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f10])).

fof(f59,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f84,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f59])).

fof(f8,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f13,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK5(X0,X1,X2),X0)
      | r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
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

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f33,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK3(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
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

fof(f34,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f30,f33,f32,f31])).

fof(f55,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f81,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f55])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k7_relat_1(X1,X0) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k7_relat_1(X1,X0) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ( k7_relat_1(X1,X0) = k1_xboole_0
      <~> r1_xboole_0(k1_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f43,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k7_relat_1(X1,X0) != k1_xboole_0 )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k7_relat_1(X1,X0) = k1_xboole_0 )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f44,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k7_relat_1(X1,X0) != k1_xboole_0 )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k7_relat_1(X1,X0) = k1_xboole_0 )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f43])).

fof(f45,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
          | k7_relat_1(X1,X0) != k1_xboole_0 )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k7_relat_1(X1,X0) = k1_xboole_0 )
        & v1_relat_1(X1) )
   => ( ( ~ r1_xboole_0(k1_relat_1(sK8),sK7)
        | k7_relat_1(sK8,sK7) != k1_xboole_0 )
      & ( r1_xboole_0(k1_relat_1(sK8),sK7)
        | k7_relat_1(sK8,sK7) = k1_xboole_0 )
      & v1_relat_1(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ( ~ r1_xboole_0(k1_relat_1(sK8),sK7)
      | k7_relat_1(sK8,sK7) != k1_xboole_0 )
    & ( r1_xboole_0(k1_relat_1(sK8),sK7)
      | k7_relat_1(sK8,sK7) = k1_xboole_0 )
    & v1_relat_1(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f44,f45])).

fof(f75,plain,
    ( r1_xboole_0(k1_relat_1(sK8),sK7)
    | k7_relat_1(sK8,sK7) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f46])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f61,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f82,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f61])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f74,plain,(
    v1_relat_1(sK8) ),
    inference(cnf_transformation,[],[f46])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f47,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

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

fof(f17,plain,(
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

fof(f24,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f26,plain,(
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
    inference(rectify,[],[f25])).

fof(f27,plain,(
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

fof(f28,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f27])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X0)
      | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f56,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f80,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f56])).

fof(f51,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X2)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(X5,X1)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f77,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(X5,X1)
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f51])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f76,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK8),sK7)
    | k7_relat_1(sK8,sK7) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_13,plain,
    ( r2_hidden(sK5(X0,X1,X2),X1)
    | r2_hidden(sK5(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1431,plain,
    ( k3_xboole_0(X0,X1) = X2
    | r2_hidden(sK5(X0,X1,X2),X2) = iProver_top
    | r2_hidden(sK5(X0,X1,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_23,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_17,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1427,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2243,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_23,c_1427])).

cnf(c_21,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_26,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_443,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_26])).

cnf(c_444,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_443])).

cnf(c_445,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_444])).

cnf(c_2296,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2243,c_445])).

cnf(c_2899,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r2_hidden(sK5(X0,X1,k1_xboole_0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1431,c_2296])).

cnf(c_14,plain,
    ( r2_hidden(sK5(X0,X1,X2),X0)
    | r2_hidden(sK5(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1430,plain,
    ( k3_xboole_0(X0,X1) = X2
    | r2_hidden(sK5(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK5(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2653,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r2_hidden(sK5(X0,X1,k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1430,c_2296])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,sK4(X1,X0)),X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1433,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK4(X1,X0)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_28,negated_conjecture,
    ( r1_xboole_0(k1_relat_1(sK8),sK7)
    | k7_relat_1(sK8,sK7) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1419,plain,
    ( k7_relat_1(sK8,sK7) = k1_xboole_0
    | r1_xboole_0(k1_relat_1(sK8),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_19,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1425,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1842,plain,
    ( k7_relat_1(sK8,sK7) = k1_xboole_0
    | k3_xboole_0(k1_relat_1(sK8),sK7) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1419,c_1425])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1429,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X0,k3_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2612,plain,
    ( k7_relat_1(sK8,sK7) = k1_xboole_0
    | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
    | r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1842,c_1429])).

cnf(c_3115,plain,
    ( r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
    | k7_relat_1(sK8,sK7) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2612,c_445])).

cnf(c_3116,plain,
    ( k7_relat_1(sK8,sK7) = k1_xboole_0
    | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
    | r2_hidden(X0,sK7) != iProver_top ),
    inference(renaming,[status(thm)],[c_3115])).

cnf(c_3126,plain,
    ( k7_relat_1(sK8,sK7) = k1_xboole_0
    | k3_xboole_0(X0,k1_relat_1(sK8)) = X1
    | r2_hidden(sK5(X0,k1_relat_1(sK8),X1),X1) = iProver_top
    | r2_hidden(sK5(X0,k1_relat_1(sK8),X1),sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1431,c_3116])).

cnf(c_3283,plain,
    ( k7_relat_1(sK8,sK7) = k1_xboole_0
    | k3_xboole_0(sK7,k1_relat_1(sK8)) = X0
    | r2_hidden(sK5(sK7,k1_relat_1(sK8),X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1430,c_3126])).

cnf(c_2301,plain,
    ( r2_hidden(X0,k1_relat_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1433,c_2296])).

cnf(c_3859,plain,
    ( k7_relat_1(sK8,sK7) = k1_xboole_0
    | k3_xboole_0(sK7,k1_relat_1(sK8)) = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3283,c_2301])).

cnf(c_22,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1423,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1758,plain,
    ( k7_relat_1(sK8,sK7) = k1_xboole_0
    | r1_xboole_0(sK7,k1_relat_1(sK8)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1419,c_1423])).

cnf(c_1888,plain,
    ( k7_relat_1(sK8,sK7) = k1_xboole_0
    | k3_xboole_0(sK7,k1_relat_1(sK8)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1758,c_1425])).

cnf(c_2240,plain,
    ( r2_hidden(X0,k1_relat_1(k3_xboole_0(X1,X2))) != iProver_top
    | r2_hidden(k4_tarski(X0,sK4(k3_xboole_0(X1,X2),X0)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1433,c_1427])).

cnf(c_6141,plain,
    ( k7_relat_1(sK8,sK7) = k1_xboole_0
    | r2_hidden(X0,k1_relat_1(k3_xboole_0(sK7,k1_relat_1(sK8)))) != iProver_top
    | r2_hidden(k4_tarski(X0,sK4(k1_xboole_0,X0)),sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_1888,c_2240])).

cnf(c_1,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_6138,plain,
    ( k7_relat_1(sK8,sK7) = k1_xboole_0
    | r2_hidden(X0,k1_relat_1(k3_xboole_0(k1_relat_1(sK8),sK7))) != iProver_top
    | r2_hidden(k4_tarski(X0,sK4(k1_xboole_0,X0)),k1_relat_1(sK8)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1842,c_2240])).

cnf(c_6520,plain,
    ( k7_relat_1(sK8,sK7) = k1_xboole_0
    | r2_hidden(X0,k1_relat_1(k3_xboole_0(k1_relat_1(sK8),sK7))) != iProver_top
    | r2_hidden(k4_tarski(X0,sK4(k1_xboole_0,X0)),sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_6138,c_3116])).

cnf(c_6640,plain,
    ( k7_relat_1(sK8,sK7) = k1_xboole_0
    | r2_hidden(X0,k1_relat_1(k3_xboole_0(sK7,k1_relat_1(sK8)))) != iProver_top
    | r2_hidden(k4_tarski(X0,sK4(k1_xboole_0,X0)),sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_6520])).

cnf(c_7212,plain,
    ( r2_hidden(X0,k1_relat_1(k3_xboole_0(sK7,k1_relat_1(sK8)))) != iProver_top
    | k7_relat_1(sK8,sK7) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6141,c_6640])).

cnf(c_7213,plain,
    ( k7_relat_1(sK8,sK7) = k1_xboole_0
    | r2_hidden(X0,k1_relat_1(k3_xboole_0(sK7,k1_relat_1(sK8)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_7212])).

cnf(c_9721,plain,
    ( k7_relat_1(sK8,sK7) = k1_xboole_0
    | k3_xboole_0(k1_relat_1(k3_xboole_0(sK7,k1_relat_1(sK8))),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2653,c_7213])).

cnf(c_10278,plain,
    ( k7_relat_1(sK8,sK7) = k1_xboole_0
    | k3_xboole_0(X0,k1_relat_1(k3_xboole_0(sK7,k1_relat_1(sK8)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_9721,c_1])).

cnf(c_11731,plain,
    ( k7_relat_1(sK8,sK7) = k1_xboole_0
    | k3_xboole_0(X0,k1_relat_1(k1_relat_1(k1_xboole_0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3859,c_10278])).

cnf(c_29,negated_conjecture,
    ( v1_relat_1(sK8) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_0,plain,
    ( ~ v1_xboole_0(X0)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_94,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_4,plain,
    ( r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1846,plain,
    ( r2_hidden(sK0(sK8,sK7,k1_xboole_0),sK7)
    | r2_hidden(k4_tarski(sK0(sK8,sK7,k1_xboole_0),sK1(sK8,sK7,k1_xboole_0)),k1_xboole_0)
    | ~ v1_relat_1(sK8)
    | ~ v1_relat_1(k1_xboole_0)
    | k7_relat_1(sK8,sK7) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_3,plain,
    ( r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X0)
    | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1845,plain,
    ( r2_hidden(k4_tarski(sK0(sK8,sK7,k1_xboole_0),sK1(sK8,sK7,k1_xboole_0)),sK8)
    | r2_hidden(k4_tarski(sK0(sK8,sK7,k1_xboole_0),sK1(sK8,sK7,k1_xboole_0)),k1_xboole_0)
    | ~ v1_relat_1(sK8)
    | ~ v1_relat_1(k1_xboole_0)
    | k7_relat_1(sK8,sK7) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2206,plain,
    ( ~ r2_hidden(k4_tarski(sK0(sK8,sK7,k1_xboole_0),sK1(sK8,sK7,k1_xboole_0)),k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_10,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2355,plain,
    ( r2_hidden(sK0(sK8,sK7,k1_xboole_0),k1_relat_1(sK8))
    | ~ r2_hidden(k4_tarski(sK0(sK8,sK7,k1_xboole_0),sK1(sK8,sK7,k1_xboole_0)),sK8) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2358,plain,
    ( ~ r2_hidden(sK0(sK8,sK7,k1_xboole_0),X0)
    | r2_hidden(sK0(sK8,sK7,k1_xboole_0),k3_xboole_0(X0,sK7))
    | ~ r2_hidden(sK0(sK8,sK7,k1_xboole_0),sK7) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_4622,plain,
    ( r2_hidden(sK0(sK8,sK7,k1_xboole_0),k3_xboole_0(k1_relat_1(sK8),sK7))
    | ~ r2_hidden(sK0(sK8,sK7,k1_xboole_0),k1_relat_1(sK8))
    | ~ r2_hidden(sK0(sK8,sK7,k1_xboole_0),sK7) ),
    inference(instantiation,[status(thm)],[c_2358])).

cnf(c_9673,plain,
    ( ~ r2_hidden(sK0(sK8,sK7,k1_xboole_0),k3_xboole_0(k1_relat_1(sK8),sK7))
    | ~ v1_xboole_0(k3_xboole_0(k1_relat_1(sK8),sK7)) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_772,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2874,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k3_xboole_0(k1_relat_1(sK8),X1))
    | k3_xboole_0(k1_relat_1(sK8),X1) != X0 ),
    inference(instantiation,[status(thm)],[c_772])).

cnf(c_13262,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k3_xboole_0(k1_relat_1(sK8),sK7))
    | k3_xboole_0(k1_relat_1(sK8),sK7) != X0 ),
    inference(instantiation,[status(thm)],[c_2874])).

cnf(c_13264,plain,
    ( v1_xboole_0(k3_xboole_0(k1_relat_1(sK8),sK7))
    | ~ v1_xboole_0(k1_xboole_0)
    | k3_xboole_0(k1_relat_1(sK8),sK7) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_13262])).

cnf(c_13425,plain,
    ( k7_relat_1(sK8,sK7) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11731,c_29,c_21,c_94,c_1842,c_1846,c_1845,c_2206,c_2355,c_4622,c_9673,c_13264])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),X3)
    | r2_hidden(k4_tarski(X0,X2),k7_relat_1(X3,X1))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(k7_relat_1(X3,X1)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1439,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(k4_tarski(X0,X2),X3) != iProver_top
    | r2_hidden(k4_tarski(X0,X2),k7_relat_1(X3,X1)) = iProver_top
    | v1_relat_1(X3) != iProver_top
    | v1_relat_1(k7_relat_1(X3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_13448,plain,
    ( r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK8) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),k1_xboole_0) = iProver_top
    | v1_relat_1(k7_relat_1(sK8,sK7)) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_13425,c_1439])).

cnf(c_13466,plain,
    ( r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK8) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),k1_xboole_0) = iProver_top
    | v1_relat_1(sK8) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13448,c_13425])).

cnf(c_30,plain,
    ( v1_relat_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_44,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_93,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_95,plain,
    ( v1_xboole_0(k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_93])).

cnf(c_32755,plain,
    ( r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK8) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13466,c_30,c_44,c_95])).

cnf(c_32764,plain,
    ( r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK8) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_32755,c_2296])).

cnf(c_32772,plain,
    ( r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
    | r2_hidden(X0,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1433,c_32764])).

cnf(c_33105,plain,
    ( k3_xboole_0(k1_relat_1(sK8),X0) = k1_xboole_0
    | r2_hidden(sK5(k1_relat_1(sK8),X0,k1_xboole_0),sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2653,c_32772])).

cnf(c_38244,plain,
    ( k3_xboole_0(k1_relat_1(sK8),sK7) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2899,c_33105])).

cnf(c_18,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1658,plain,
    ( r1_xboole_0(k1_relat_1(sK8),sK7)
    | k3_xboole_0(k1_relat_1(sK8),sK7) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_27,negated_conjecture,
    ( ~ r1_xboole_0(k1_relat_1(sK8),sK7)
    | k7_relat_1(sK8,sK7) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f76])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_38244,c_13425,c_1658,c_27])).


%------------------------------------------------------------------------------
