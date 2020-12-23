%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:48:21 EST 2020

% Result     : Theorem 7.88s
% Output     : CNFRefutation 7.88s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 209 expanded)
%              Number of clauses        :   67 (  77 expanded)
%              Number of leaves         :   22 (  45 expanded)
%              Depth                    :   21
%              Number of atoms          :  432 ( 754 expanded)
%              Number of equality atoms :  160 ( 263 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f7,axiom,(
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
    inference(nnf_transformation,[],[f7])).

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
     => r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK2(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK1(X0,X1),X3),X0)
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK1(X0,X1),X4),X0)
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK1(X0,X1),X3),X0)
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f30,f33,f32,f31])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
      | r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f12,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( ! [X2] : ~ r2_hidden(X2,k1_relat_1(X1))
          & r2_hidden(X0,k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f39,plain,(
    ! [X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
     => r2_hidden(sK5(X1),k1_relat_1(X1)) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X1),k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f20,f39])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X1),k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f70,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r2_hidden(X0,k1_relat_1(X1))
        <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <~> k1_xboole_0 != k11_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f42,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k11_relat_1(X1,X0)
        | ~ r2_hidden(X0,k1_relat_1(X1)) )
      & ( k1_xboole_0 != k11_relat_1(X1,X0)
        | r2_hidden(X0,k1_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f43,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k11_relat_1(X1,X0)
        | ~ r2_hidden(X0,k1_relat_1(X1)) )
      & ( k1_xboole_0 != k11_relat_1(X1,X0)
        | r2_hidden(X0,k1_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f42])).

fof(f44,plain,
    ( ? [X0,X1] :
        ( ( k1_xboole_0 = k11_relat_1(X1,X0)
          | ~ r2_hidden(X0,k1_relat_1(X1)) )
        & ( k1_xboole_0 != k11_relat_1(X1,X0)
          | r2_hidden(X0,k1_relat_1(X1)) )
        & v1_relat_1(X1) )
   => ( ( k1_xboole_0 = k11_relat_1(sK7,sK6)
        | ~ r2_hidden(sK6,k1_relat_1(sK7)) )
      & ( k1_xboole_0 != k11_relat_1(sK7,sK6)
        | r2_hidden(sK6,k1_relat_1(sK7)) )
      & v1_relat_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ( k1_xboole_0 = k11_relat_1(sK7,sK6)
      | ~ r2_hidden(sK6,k1_relat_1(sK7)) )
    & ( k1_xboole_0 != k11_relat_1(sK7,sK6)
      | r2_hidden(sK6,k1_relat_1(sK7)) )
    & v1_relat_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f43,f44])).

fof(f72,plain,(
    v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f45])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f36,plain,(
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
    inference(rectify,[],[f35])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK4(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2)
        & r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2)
            & r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f36,f37])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2))
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
        | r2_hidden(X0,X1) )
      & ( ~ r2_hidden(X0,X1)
        | k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f74,plain,
    ( k1_xboole_0 = k11_relat_1(sK7,sK6)
    | ~ r2_hidden(sK6,k1_relat_1(sK7)) ),
    inference(cnf_transformation,[],[f45])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f25,plain,(
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
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).

fof(f47,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f76,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f47])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | ~ r2_hidden(X1,k11_relat_1(X2,X0)) )
        & ( r2_hidden(X1,k11_relat_1(X2,X0))
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k11_relat_1(X2,X0))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f58,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f79,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f58])).

fof(f73,plain,
    ( k1_xboole_0 != k11_relat_1(sK7,sK6)
    | r2_hidden(sK6,k1_relat_1(sK7)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_10,plain,
    ( k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_24647,plain,
    ( k2_xboole_0(k1_tarski(sK3(sK7,sK6)),k11_relat_1(sK7,sK6)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_355,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1362,plain,
    ( X0 != X1
    | k2_xboole_0(k1_tarski(X2),X3) != X1
    | k2_xboole_0(k1_tarski(X2),X3) = X0 ),
    inference(instantiation,[status(thm)],[c_355])).

cnf(c_9260,plain,
    ( X0 != k11_relat_1(sK7,sK6)
    | k2_xboole_0(k1_tarski(sK3(sK7,sK6)),k11_relat_1(sK7,sK6)) = X0
    | k2_xboole_0(k1_tarski(sK3(sK7,sK6)),k11_relat_1(sK7,sK6)) != k11_relat_1(sK7,sK6) ),
    inference(instantiation,[status(thm)],[c_1362])).

cnf(c_9261,plain,
    ( k2_xboole_0(k1_tarski(sK3(sK7,sK6)),k11_relat_1(sK7,sK6)) != k11_relat_1(sK7,sK6)
    | k2_xboole_0(k1_tarski(sK3(sK7,sK6)),k11_relat_1(sK7,sK6)) = k1_xboole_0
    | k1_xboole_0 != k11_relat_1(sK7,sK6) ),
    inference(instantiation,[status(thm)],[c_9260])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | k2_xboole_0(k1_tarski(X0),X1) = X1 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_7423,plain,
    ( ~ r2_hidden(sK3(sK7,sK6),k11_relat_1(sK7,sK6))
    | k2_xboole_0(k1_tarski(sK3(sK7,sK6)),k11_relat_1(sK7,sK6)) = k11_relat_1(sK7,sK6) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_13,plain,
    ( r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
    | r2_hidden(sK1(X0,X1),X1)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_954,plain,
    ( k1_relat_1(X0) = X1
    | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) = iProver_top
    | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_24,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_21,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK5(X1),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_946,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
    | r2_hidden(sK5(X1),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1911,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | r2_hidden(sK5(k1_xboole_0),k1_relat_1(k1_xboole_0)) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_24,c_946])).

cnf(c_25,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1915,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | r2_hidden(sK5(k1_xboole_0),k1_xboole_0) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1911,c_25])).

cnf(c_28,negated_conjecture,
    ( v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_941,plain,
    ( v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_6,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_16,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_951,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k3_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1226,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_951])).

cnf(c_1352,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_941,c_1226])).

cnf(c_2565,plain,
    ( r2_hidden(sK5(k1_xboole_0),k1_xboole_0) = iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1915,c_1352])).

cnf(c_2566,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | r2_hidden(sK5(k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(renaming,[status(thm)],[c_2565])).

cnf(c_4283,plain,
    ( k1_relat_1(k1_xboole_0) = X0
    | r2_hidden(sK1(k1_xboole_0,X0),X0) = iProver_top
    | r2_hidden(sK5(k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_954,c_2566])).

cnf(c_4339,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(k1_xboole_0,X0),X0) = iProver_top
    | r2_hidden(sK5(k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4283,c_25])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK4(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_949,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK4(X0,X2,X1),X2) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK4(X0,X2,X1),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_947,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK4(X0,X2,X1),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_7,plain,
    ( r2_hidden(X0,X1)
    | k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_959,plain,
    ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
    | r2_hidden(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_26,negated_conjecture,
    ( ~ r2_hidden(sK6,k1_relat_1(sK7))
    | k1_xboole_0 = k11_relat_1(sK7,sK6) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_943,plain,
    ( k1_xboole_0 = k11_relat_1(sK7,sK6)
    | r2_hidden(sK6,k1_relat_1(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_1398,plain,
    ( k11_relat_1(sK7,sK6) = k1_xboole_0
    | k4_xboole_0(k1_tarski(sK6),k1_relat_1(sK7)) = k1_tarski(sK6) ),
    inference(superposition,[status(thm)],[c_959,c_943])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_961,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1683,plain,
    ( k11_relat_1(sK7,sK6) = k1_xboole_0
    | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
    | r2_hidden(X0,k1_tarski(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1398,c_961])).

cnf(c_2501,plain,
    ( k11_relat_1(sK7,sK6) = k1_xboole_0
    | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(sK4(X0,X1,sK7),k1_tarski(sK6)) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_947,c_1683])).

cnf(c_29,plain,
    ( v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_3134,plain,
    ( r2_hidden(sK4(X0,X1,sK7),k1_tarski(sK6)) != iProver_top
    | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | k11_relat_1(sK7,sK6) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2501,c_29])).

cnf(c_3135,plain,
    ( k11_relat_1(sK7,sK6) = k1_xboole_0
    | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(sK4(X0,X1,sK7),k1_tarski(sK6)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3134])).

cnf(c_3144,plain,
    ( k11_relat_1(sK7,sK6) = k1_xboole_0
    | r2_hidden(X0,k9_relat_1(sK7,k1_tarski(sK6))) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_949,c_3135])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_tarski(X1)) = k11_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_956,plain,
    ( k9_relat_1(X0,k1_tarski(X1)) = k11_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1435,plain,
    ( k9_relat_1(sK7,k1_tarski(X0)) = k11_relat_1(sK7,X0) ),
    inference(superposition,[status(thm)],[c_941,c_956])).

cnf(c_3148,plain,
    ( k11_relat_1(sK7,sK6) = k1_xboole_0
    | r2_hidden(X0,k11_relat_1(sK7,sK6)) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3144,c_1435])).

cnf(c_3189,plain,
    ( r2_hidden(X0,k11_relat_1(sK7,sK6)) != iProver_top
    | k11_relat_1(sK7,sK6) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3148,c_29])).

cnf(c_3190,plain,
    ( k11_relat_1(sK7,sK6) = k1_xboole_0
    | r2_hidden(X0,k11_relat_1(sK7,sK6)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3189])).

cnf(c_4474,plain,
    ( k11_relat_1(sK7,sK6) = k1_xboole_0
    | r2_hidden(sK5(k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4339,c_3190])).

cnf(c_957,plain,
    ( k2_xboole_0(k1_tarski(X0),X1) = X1
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4897,plain,
    ( k11_relat_1(sK7,sK6) = k1_xboole_0
    | k2_xboole_0(k1_tarski(sK5(k1_xboole_0)),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4474,c_957])).

cnf(c_5672,plain,
    ( k11_relat_1(sK7,sK6) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4897,c_10])).

cnf(c_23,plain,
    ( r2_hidden(X0,k11_relat_1(X1,X2))
    | ~ r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1195,plain,
    ( r2_hidden(X0,k11_relat_1(sK7,X1))
    | ~ r2_hidden(k4_tarski(X1,X0),sK7)
    | ~ v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_2045,plain,
    ( r2_hidden(sK3(sK7,X0),k11_relat_1(sK7,X0))
    | ~ r2_hidden(k4_tarski(X0,sK3(sK7,X0)),sK7)
    | ~ v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_1195])).

cnf(c_3990,plain,
    ( r2_hidden(sK3(sK7,sK6),k11_relat_1(sK7,sK6))
    | ~ r2_hidden(k4_tarski(sK6,sK3(sK7,sK6)),sK7)
    | ~ v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_2045])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,sK3(X1,X0)),X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2044,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK7))
    | r2_hidden(k4_tarski(X0,sK3(sK7,X0)),sK7) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_3432,plain,
    ( r2_hidden(k4_tarski(sK6,sK3(sK7,sK6)),sK7)
    | ~ r2_hidden(sK6,k1_relat_1(sK7)) ),
    inference(instantiation,[status(thm)],[c_2044])).

cnf(c_1188,plain,
    ( k11_relat_1(sK7,sK6) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k11_relat_1(sK7,sK6) ),
    inference(instantiation,[status(thm)],[c_355])).

cnf(c_1189,plain,
    ( k11_relat_1(sK7,sK6) != k1_xboole_0
    | k1_xboole_0 = k11_relat_1(sK7,sK6)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1188])).

cnf(c_354,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_377,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_354])).

cnf(c_27,negated_conjecture,
    ( r2_hidden(sK6,k1_relat_1(sK7))
    | k1_xboole_0 != k11_relat_1(sK7,sK6) ),
    inference(cnf_transformation,[],[f73])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_24647,c_9261,c_7423,c_5672,c_3990,c_3432,c_1189,c_377,c_27,c_28])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:50:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.88/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.88/1.49  
% 7.88/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.88/1.49  
% 7.88/1.49  ------  iProver source info
% 7.88/1.49  
% 7.88/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.88/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.88/1.49  git: non_committed_changes: false
% 7.88/1.49  git: last_make_outside_of_git: false
% 7.88/1.49  
% 7.88/1.49  ------ 
% 7.88/1.49  
% 7.88/1.49  ------ Input Options
% 7.88/1.49  
% 7.88/1.49  --out_options                           all
% 7.88/1.49  --tptp_safe_out                         true
% 7.88/1.49  --problem_path                          ""
% 7.88/1.49  --include_path                          ""
% 7.88/1.49  --clausifier                            res/vclausify_rel
% 7.88/1.49  --clausifier_options                    --mode clausify
% 7.88/1.49  --stdin                                 false
% 7.88/1.49  --stats_out                             all
% 7.88/1.49  
% 7.88/1.49  ------ General Options
% 7.88/1.49  
% 7.88/1.49  --fof                                   false
% 7.88/1.49  --time_out_real                         305.
% 7.88/1.49  --time_out_virtual                      -1.
% 7.88/1.49  --symbol_type_check                     false
% 7.88/1.49  --clausify_out                          false
% 7.88/1.49  --sig_cnt_out                           false
% 7.88/1.49  --trig_cnt_out                          false
% 7.88/1.49  --trig_cnt_out_tolerance                1.
% 7.88/1.49  --trig_cnt_out_sk_spl                   false
% 7.88/1.49  --abstr_cl_out                          false
% 7.88/1.49  
% 7.88/1.49  ------ Global Options
% 7.88/1.49  
% 7.88/1.49  --schedule                              default
% 7.88/1.49  --add_important_lit                     false
% 7.88/1.49  --prop_solver_per_cl                    1000
% 7.88/1.49  --min_unsat_core                        false
% 7.88/1.49  --soft_assumptions                      false
% 7.88/1.49  --soft_lemma_size                       3
% 7.88/1.49  --prop_impl_unit_size                   0
% 7.88/1.49  --prop_impl_unit                        []
% 7.88/1.49  --share_sel_clauses                     true
% 7.88/1.49  --reset_solvers                         false
% 7.88/1.49  --bc_imp_inh                            [conj_cone]
% 7.88/1.49  --conj_cone_tolerance                   3.
% 7.88/1.49  --extra_neg_conj                        none
% 7.88/1.49  --large_theory_mode                     true
% 7.88/1.49  --prolific_symb_bound                   200
% 7.88/1.49  --lt_threshold                          2000
% 7.88/1.49  --clause_weak_htbl                      true
% 7.88/1.49  --gc_record_bc_elim                     false
% 7.88/1.49  
% 7.88/1.49  ------ Preprocessing Options
% 7.88/1.49  
% 7.88/1.49  --preprocessing_flag                    true
% 7.88/1.49  --time_out_prep_mult                    0.1
% 7.88/1.49  --splitting_mode                        input
% 7.88/1.49  --splitting_grd                         true
% 7.88/1.49  --splitting_cvd                         false
% 7.88/1.49  --splitting_cvd_svl                     false
% 7.88/1.49  --splitting_nvd                         32
% 7.88/1.49  --sub_typing                            true
% 7.88/1.49  --prep_gs_sim                           true
% 7.88/1.49  --prep_unflatten                        true
% 7.88/1.49  --prep_res_sim                          true
% 7.88/1.49  --prep_upred                            true
% 7.88/1.49  --prep_sem_filter                       exhaustive
% 7.88/1.49  --prep_sem_filter_out                   false
% 7.88/1.49  --pred_elim                             true
% 7.88/1.49  --res_sim_input                         true
% 7.88/1.49  --eq_ax_congr_red                       true
% 7.88/1.49  --pure_diseq_elim                       true
% 7.88/1.49  --brand_transform                       false
% 7.88/1.49  --non_eq_to_eq                          false
% 7.88/1.49  --prep_def_merge                        true
% 7.88/1.49  --prep_def_merge_prop_impl              false
% 7.88/1.49  --prep_def_merge_mbd                    true
% 7.88/1.49  --prep_def_merge_tr_red                 false
% 7.88/1.49  --prep_def_merge_tr_cl                  false
% 7.88/1.49  --smt_preprocessing                     true
% 7.88/1.49  --smt_ac_axioms                         fast
% 7.88/1.49  --preprocessed_out                      false
% 7.88/1.49  --preprocessed_stats                    false
% 7.88/1.49  
% 7.88/1.49  ------ Abstraction refinement Options
% 7.88/1.49  
% 7.88/1.49  --abstr_ref                             []
% 7.88/1.49  --abstr_ref_prep                        false
% 7.88/1.49  --abstr_ref_until_sat                   false
% 7.88/1.49  --abstr_ref_sig_restrict                funpre
% 7.88/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.88/1.49  --abstr_ref_under                       []
% 7.88/1.49  
% 7.88/1.49  ------ SAT Options
% 7.88/1.49  
% 7.88/1.49  --sat_mode                              false
% 7.88/1.49  --sat_fm_restart_options                ""
% 7.88/1.49  --sat_gr_def                            false
% 7.88/1.49  --sat_epr_types                         true
% 7.88/1.49  --sat_non_cyclic_types                  false
% 7.88/1.49  --sat_finite_models                     false
% 7.88/1.49  --sat_fm_lemmas                         false
% 7.88/1.49  --sat_fm_prep                           false
% 7.88/1.49  --sat_fm_uc_incr                        true
% 7.88/1.49  --sat_out_model                         small
% 7.88/1.49  --sat_out_clauses                       false
% 7.88/1.49  
% 7.88/1.49  ------ QBF Options
% 7.88/1.49  
% 7.88/1.49  --qbf_mode                              false
% 7.88/1.49  --qbf_elim_univ                         false
% 7.88/1.49  --qbf_dom_inst                          none
% 7.88/1.49  --qbf_dom_pre_inst                      false
% 7.88/1.49  --qbf_sk_in                             false
% 7.88/1.49  --qbf_pred_elim                         true
% 7.88/1.49  --qbf_split                             512
% 7.88/1.49  
% 7.88/1.49  ------ BMC1 Options
% 7.88/1.49  
% 7.88/1.49  --bmc1_incremental                      false
% 7.88/1.49  --bmc1_axioms                           reachable_all
% 7.88/1.49  --bmc1_min_bound                        0
% 7.88/1.49  --bmc1_max_bound                        -1
% 7.88/1.49  --bmc1_max_bound_default                -1
% 7.88/1.49  --bmc1_symbol_reachability              true
% 7.88/1.49  --bmc1_property_lemmas                  false
% 7.88/1.49  --bmc1_k_induction                      false
% 7.88/1.49  --bmc1_non_equiv_states                 false
% 7.88/1.49  --bmc1_deadlock                         false
% 7.88/1.49  --bmc1_ucm                              false
% 7.88/1.49  --bmc1_add_unsat_core                   none
% 7.88/1.49  --bmc1_unsat_core_children              false
% 7.88/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.88/1.49  --bmc1_out_stat                         full
% 7.88/1.49  --bmc1_ground_init                      false
% 7.88/1.49  --bmc1_pre_inst_next_state              false
% 7.88/1.49  --bmc1_pre_inst_state                   false
% 7.88/1.49  --bmc1_pre_inst_reach_state             false
% 7.88/1.49  --bmc1_out_unsat_core                   false
% 7.88/1.49  --bmc1_aig_witness_out                  false
% 7.88/1.49  --bmc1_verbose                          false
% 7.88/1.49  --bmc1_dump_clauses_tptp                false
% 7.88/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.88/1.49  --bmc1_dump_file                        -
% 7.88/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.88/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.88/1.49  --bmc1_ucm_extend_mode                  1
% 7.88/1.49  --bmc1_ucm_init_mode                    2
% 7.88/1.49  --bmc1_ucm_cone_mode                    none
% 7.88/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.88/1.49  --bmc1_ucm_relax_model                  4
% 7.88/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.88/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.88/1.49  --bmc1_ucm_layered_model                none
% 7.88/1.49  --bmc1_ucm_max_lemma_size               10
% 7.88/1.49  
% 7.88/1.49  ------ AIG Options
% 7.88/1.49  
% 7.88/1.49  --aig_mode                              false
% 7.88/1.49  
% 7.88/1.49  ------ Instantiation Options
% 7.88/1.49  
% 7.88/1.49  --instantiation_flag                    true
% 7.88/1.49  --inst_sos_flag                         false
% 7.88/1.49  --inst_sos_phase                        true
% 7.88/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.88/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.88/1.49  --inst_lit_sel_side                     num_symb
% 7.88/1.49  --inst_solver_per_active                1400
% 7.88/1.49  --inst_solver_calls_frac                1.
% 7.88/1.49  --inst_passive_queue_type               priority_queues
% 7.88/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.88/1.49  --inst_passive_queues_freq              [25;2]
% 7.88/1.49  --inst_dismatching                      true
% 7.88/1.49  --inst_eager_unprocessed_to_passive     true
% 7.88/1.49  --inst_prop_sim_given                   true
% 7.88/1.49  --inst_prop_sim_new                     false
% 7.88/1.49  --inst_subs_new                         false
% 7.88/1.49  --inst_eq_res_simp                      false
% 7.88/1.49  --inst_subs_given                       false
% 7.88/1.49  --inst_orphan_elimination               true
% 7.88/1.49  --inst_learning_loop_flag               true
% 7.88/1.49  --inst_learning_start                   3000
% 7.88/1.49  --inst_learning_factor                  2
% 7.88/1.49  --inst_start_prop_sim_after_learn       3
% 7.88/1.49  --inst_sel_renew                        solver
% 7.88/1.49  --inst_lit_activity_flag                true
% 7.88/1.49  --inst_restr_to_given                   false
% 7.88/1.49  --inst_activity_threshold               500
% 7.88/1.49  --inst_out_proof                        true
% 7.88/1.49  
% 7.88/1.49  ------ Resolution Options
% 7.88/1.49  
% 7.88/1.49  --resolution_flag                       true
% 7.88/1.49  --res_lit_sel                           adaptive
% 7.88/1.49  --res_lit_sel_side                      none
% 7.88/1.49  --res_ordering                          kbo
% 7.88/1.49  --res_to_prop_solver                    active
% 7.88/1.49  --res_prop_simpl_new                    false
% 7.88/1.49  --res_prop_simpl_given                  true
% 7.88/1.49  --res_passive_queue_type                priority_queues
% 7.88/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.88/1.49  --res_passive_queues_freq               [15;5]
% 7.88/1.49  --res_forward_subs                      full
% 7.88/1.49  --res_backward_subs                     full
% 7.88/1.49  --res_forward_subs_resolution           true
% 7.88/1.49  --res_backward_subs_resolution          true
% 7.88/1.49  --res_orphan_elimination                true
% 7.88/1.49  --res_time_limit                        2.
% 7.88/1.49  --res_out_proof                         true
% 7.88/1.49  
% 7.88/1.49  ------ Superposition Options
% 7.88/1.49  
% 7.88/1.49  --superposition_flag                    true
% 7.88/1.49  --sup_passive_queue_type                priority_queues
% 7.88/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.88/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.88/1.49  --demod_completeness_check              fast
% 7.88/1.49  --demod_use_ground                      true
% 7.88/1.49  --sup_to_prop_solver                    passive
% 7.88/1.49  --sup_prop_simpl_new                    true
% 7.88/1.49  --sup_prop_simpl_given                  true
% 7.88/1.49  --sup_fun_splitting                     false
% 7.88/1.49  --sup_smt_interval                      50000
% 7.88/1.49  
% 7.88/1.49  ------ Superposition Simplification Setup
% 7.88/1.49  
% 7.88/1.49  --sup_indices_passive                   []
% 7.88/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.88/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.88/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.88/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.88/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.88/1.49  --sup_full_bw                           [BwDemod]
% 7.88/1.49  --sup_immed_triv                        [TrivRules]
% 7.88/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.88/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.88/1.49  --sup_immed_bw_main                     []
% 7.88/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.88/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.88/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.88/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.88/1.49  
% 7.88/1.49  ------ Combination Options
% 7.88/1.49  
% 7.88/1.49  --comb_res_mult                         3
% 7.88/1.49  --comb_sup_mult                         2
% 7.88/1.49  --comb_inst_mult                        10
% 7.88/1.49  
% 7.88/1.49  ------ Debug Options
% 7.88/1.49  
% 7.88/1.49  --dbg_backtrace                         false
% 7.88/1.49  --dbg_dump_prop_clauses                 false
% 7.88/1.49  --dbg_dump_prop_clauses_file            -
% 7.88/1.49  --dbg_out_stat                          false
% 7.88/1.49  ------ Parsing...
% 7.88/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.88/1.49  
% 7.88/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.88/1.49  
% 7.88/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.88/1.49  
% 7.88/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.88/1.49  ------ Proving...
% 7.88/1.49  ------ Problem Properties 
% 7.88/1.49  
% 7.88/1.49  
% 7.88/1.49  clauses                                 29
% 7.88/1.49  conjectures                             3
% 7.88/1.49  EPR                                     1
% 7.88/1.49  Horn                                    23
% 7.88/1.49  unary                                   5
% 7.88/1.49  binary                                  11
% 7.88/1.49  lits                                    69
% 7.88/1.49  lits eq                                 15
% 7.88/1.49  fd_pure                                 0
% 7.88/1.49  fd_pseudo                               0
% 7.88/1.49  fd_cond                                 0
% 7.88/1.49  fd_pseudo_cond                          5
% 7.88/1.49  AC symbols                              0
% 7.88/1.49  
% 7.88/1.49  ------ Schedule dynamic 5 is on 
% 7.88/1.49  
% 7.88/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.88/1.49  
% 7.88/1.49  
% 7.88/1.49  ------ 
% 7.88/1.49  Current options:
% 7.88/1.49  ------ 
% 7.88/1.49  
% 7.88/1.49  ------ Input Options
% 7.88/1.49  
% 7.88/1.49  --out_options                           all
% 7.88/1.49  --tptp_safe_out                         true
% 7.88/1.49  --problem_path                          ""
% 7.88/1.49  --include_path                          ""
% 7.88/1.49  --clausifier                            res/vclausify_rel
% 7.88/1.49  --clausifier_options                    --mode clausify
% 7.88/1.49  --stdin                                 false
% 7.88/1.49  --stats_out                             all
% 7.88/1.49  
% 7.88/1.49  ------ General Options
% 7.88/1.49  
% 7.88/1.49  --fof                                   false
% 7.88/1.49  --time_out_real                         305.
% 7.88/1.49  --time_out_virtual                      -1.
% 7.88/1.49  --symbol_type_check                     false
% 7.88/1.49  --clausify_out                          false
% 7.88/1.49  --sig_cnt_out                           false
% 7.88/1.49  --trig_cnt_out                          false
% 7.88/1.49  --trig_cnt_out_tolerance                1.
% 7.88/1.49  --trig_cnt_out_sk_spl                   false
% 7.88/1.49  --abstr_cl_out                          false
% 7.88/1.49  
% 7.88/1.49  ------ Global Options
% 7.88/1.49  
% 7.88/1.49  --schedule                              default
% 7.88/1.49  --add_important_lit                     false
% 7.88/1.49  --prop_solver_per_cl                    1000
% 7.88/1.49  --min_unsat_core                        false
% 7.88/1.49  --soft_assumptions                      false
% 7.88/1.49  --soft_lemma_size                       3
% 7.88/1.49  --prop_impl_unit_size                   0
% 7.88/1.49  --prop_impl_unit                        []
% 7.88/1.49  --share_sel_clauses                     true
% 7.88/1.49  --reset_solvers                         false
% 7.88/1.49  --bc_imp_inh                            [conj_cone]
% 7.88/1.49  --conj_cone_tolerance                   3.
% 7.88/1.49  --extra_neg_conj                        none
% 7.88/1.49  --large_theory_mode                     true
% 7.88/1.49  --prolific_symb_bound                   200
% 7.88/1.49  --lt_threshold                          2000
% 7.88/1.49  --clause_weak_htbl                      true
% 7.88/1.49  --gc_record_bc_elim                     false
% 7.88/1.49  
% 7.88/1.49  ------ Preprocessing Options
% 7.88/1.49  
% 7.88/1.49  --preprocessing_flag                    true
% 7.88/1.49  --time_out_prep_mult                    0.1
% 7.88/1.49  --splitting_mode                        input
% 7.88/1.49  --splitting_grd                         true
% 7.88/1.49  --splitting_cvd                         false
% 7.88/1.49  --splitting_cvd_svl                     false
% 7.88/1.49  --splitting_nvd                         32
% 7.88/1.49  --sub_typing                            true
% 7.88/1.49  --prep_gs_sim                           true
% 7.88/1.49  --prep_unflatten                        true
% 7.88/1.49  --prep_res_sim                          true
% 7.88/1.49  --prep_upred                            true
% 7.88/1.49  --prep_sem_filter                       exhaustive
% 7.88/1.49  --prep_sem_filter_out                   false
% 7.88/1.49  --pred_elim                             true
% 7.88/1.49  --res_sim_input                         true
% 7.88/1.49  --eq_ax_congr_red                       true
% 7.88/1.49  --pure_diseq_elim                       true
% 7.88/1.49  --brand_transform                       false
% 7.88/1.49  --non_eq_to_eq                          false
% 7.88/1.49  --prep_def_merge                        true
% 7.88/1.49  --prep_def_merge_prop_impl              false
% 7.88/1.49  --prep_def_merge_mbd                    true
% 7.88/1.49  --prep_def_merge_tr_red                 false
% 7.88/1.49  --prep_def_merge_tr_cl                  false
% 7.88/1.49  --smt_preprocessing                     true
% 7.88/1.49  --smt_ac_axioms                         fast
% 7.88/1.49  --preprocessed_out                      false
% 7.88/1.49  --preprocessed_stats                    false
% 7.88/1.49  
% 7.88/1.49  ------ Abstraction refinement Options
% 7.88/1.49  
% 7.88/1.49  --abstr_ref                             []
% 7.88/1.49  --abstr_ref_prep                        false
% 7.88/1.49  --abstr_ref_until_sat                   false
% 7.88/1.49  --abstr_ref_sig_restrict                funpre
% 7.88/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.88/1.49  --abstr_ref_under                       []
% 7.88/1.49  
% 7.88/1.49  ------ SAT Options
% 7.88/1.49  
% 7.88/1.49  --sat_mode                              false
% 7.88/1.49  --sat_fm_restart_options                ""
% 7.88/1.49  --sat_gr_def                            false
% 7.88/1.49  --sat_epr_types                         true
% 7.88/1.49  --sat_non_cyclic_types                  false
% 7.88/1.49  --sat_finite_models                     false
% 7.88/1.49  --sat_fm_lemmas                         false
% 7.88/1.49  --sat_fm_prep                           false
% 7.88/1.49  --sat_fm_uc_incr                        true
% 7.88/1.49  --sat_out_model                         small
% 7.88/1.49  --sat_out_clauses                       false
% 7.88/1.49  
% 7.88/1.49  ------ QBF Options
% 7.88/1.49  
% 7.88/1.49  --qbf_mode                              false
% 7.88/1.49  --qbf_elim_univ                         false
% 7.88/1.49  --qbf_dom_inst                          none
% 7.88/1.49  --qbf_dom_pre_inst                      false
% 7.88/1.49  --qbf_sk_in                             false
% 7.88/1.49  --qbf_pred_elim                         true
% 7.88/1.49  --qbf_split                             512
% 7.88/1.49  
% 7.88/1.49  ------ BMC1 Options
% 7.88/1.49  
% 7.88/1.49  --bmc1_incremental                      false
% 7.88/1.49  --bmc1_axioms                           reachable_all
% 7.88/1.49  --bmc1_min_bound                        0
% 7.88/1.49  --bmc1_max_bound                        -1
% 7.88/1.49  --bmc1_max_bound_default                -1
% 7.88/1.49  --bmc1_symbol_reachability              true
% 7.88/1.49  --bmc1_property_lemmas                  false
% 7.88/1.49  --bmc1_k_induction                      false
% 7.88/1.49  --bmc1_non_equiv_states                 false
% 7.88/1.49  --bmc1_deadlock                         false
% 7.88/1.49  --bmc1_ucm                              false
% 7.88/1.49  --bmc1_add_unsat_core                   none
% 7.88/1.49  --bmc1_unsat_core_children              false
% 7.88/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.88/1.49  --bmc1_out_stat                         full
% 7.88/1.49  --bmc1_ground_init                      false
% 7.88/1.49  --bmc1_pre_inst_next_state              false
% 7.88/1.49  --bmc1_pre_inst_state                   false
% 7.88/1.49  --bmc1_pre_inst_reach_state             false
% 7.88/1.49  --bmc1_out_unsat_core                   false
% 7.88/1.49  --bmc1_aig_witness_out                  false
% 7.88/1.49  --bmc1_verbose                          false
% 7.88/1.49  --bmc1_dump_clauses_tptp                false
% 7.88/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.88/1.49  --bmc1_dump_file                        -
% 7.88/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.88/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.88/1.49  --bmc1_ucm_extend_mode                  1
% 7.88/1.49  --bmc1_ucm_init_mode                    2
% 7.88/1.49  --bmc1_ucm_cone_mode                    none
% 7.88/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.88/1.49  --bmc1_ucm_relax_model                  4
% 7.88/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.88/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.88/1.49  --bmc1_ucm_layered_model                none
% 7.88/1.49  --bmc1_ucm_max_lemma_size               10
% 7.88/1.49  
% 7.88/1.49  ------ AIG Options
% 7.88/1.49  
% 7.88/1.49  --aig_mode                              false
% 7.88/1.49  
% 7.88/1.49  ------ Instantiation Options
% 7.88/1.49  
% 7.88/1.49  --instantiation_flag                    true
% 7.88/1.49  --inst_sos_flag                         false
% 7.88/1.49  --inst_sos_phase                        true
% 7.88/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.88/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.88/1.49  --inst_lit_sel_side                     none
% 7.88/1.49  --inst_solver_per_active                1400
% 7.88/1.49  --inst_solver_calls_frac                1.
% 7.88/1.49  --inst_passive_queue_type               priority_queues
% 7.88/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.88/1.49  --inst_passive_queues_freq              [25;2]
% 7.88/1.49  --inst_dismatching                      true
% 7.88/1.49  --inst_eager_unprocessed_to_passive     true
% 7.88/1.49  --inst_prop_sim_given                   true
% 7.88/1.49  --inst_prop_sim_new                     false
% 7.88/1.49  --inst_subs_new                         false
% 7.88/1.49  --inst_eq_res_simp                      false
% 7.88/1.49  --inst_subs_given                       false
% 7.88/1.49  --inst_orphan_elimination               true
% 7.88/1.49  --inst_learning_loop_flag               true
% 7.88/1.49  --inst_learning_start                   3000
% 7.88/1.49  --inst_learning_factor                  2
% 7.88/1.49  --inst_start_prop_sim_after_learn       3
% 7.88/1.49  --inst_sel_renew                        solver
% 7.88/1.49  --inst_lit_activity_flag                true
% 7.88/1.49  --inst_restr_to_given                   false
% 7.88/1.49  --inst_activity_threshold               500
% 7.88/1.49  --inst_out_proof                        true
% 7.88/1.49  
% 7.88/1.49  ------ Resolution Options
% 7.88/1.49  
% 7.88/1.49  --resolution_flag                       false
% 7.88/1.49  --res_lit_sel                           adaptive
% 7.88/1.49  --res_lit_sel_side                      none
% 7.88/1.49  --res_ordering                          kbo
% 7.88/1.49  --res_to_prop_solver                    active
% 7.88/1.49  --res_prop_simpl_new                    false
% 7.88/1.49  --res_prop_simpl_given                  true
% 7.88/1.49  --res_passive_queue_type                priority_queues
% 7.88/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.88/1.49  --res_passive_queues_freq               [15;5]
% 7.88/1.49  --res_forward_subs                      full
% 7.88/1.49  --res_backward_subs                     full
% 7.88/1.49  --res_forward_subs_resolution           true
% 7.88/1.49  --res_backward_subs_resolution          true
% 7.88/1.49  --res_orphan_elimination                true
% 7.88/1.49  --res_time_limit                        2.
% 7.88/1.49  --res_out_proof                         true
% 7.88/1.49  
% 7.88/1.49  ------ Superposition Options
% 7.88/1.49  
% 7.88/1.49  --superposition_flag                    true
% 7.88/1.49  --sup_passive_queue_type                priority_queues
% 7.88/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.88/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.88/1.49  --demod_completeness_check              fast
% 7.88/1.49  --demod_use_ground                      true
% 7.88/1.49  --sup_to_prop_solver                    passive
% 7.88/1.49  --sup_prop_simpl_new                    true
% 7.88/1.49  --sup_prop_simpl_given                  true
% 7.88/1.49  --sup_fun_splitting                     false
% 7.88/1.49  --sup_smt_interval                      50000
% 7.88/1.49  
% 7.88/1.49  ------ Superposition Simplification Setup
% 7.88/1.49  
% 7.88/1.49  --sup_indices_passive                   []
% 7.88/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.88/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.88/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.88/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.88/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.88/1.49  --sup_full_bw                           [BwDemod]
% 7.88/1.49  --sup_immed_triv                        [TrivRules]
% 7.88/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.88/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.88/1.49  --sup_immed_bw_main                     []
% 7.88/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.88/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.88/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.88/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.88/1.49  
% 7.88/1.49  ------ Combination Options
% 7.88/1.49  
% 7.88/1.49  --comb_res_mult                         3
% 7.88/1.49  --comb_sup_mult                         2
% 7.88/1.49  --comb_inst_mult                        10
% 7.88/1.49  
% 7.88/1.49  ------ Debug Options
% 7.88/1.49  
% 7.88/1.49  --dbg_backtrace                         false
% 7.88/1.49  --dbg_dump_prop_clauses                 false
% 7.88/1.49  --dbg_dump_prop_clauses_file            -
% 7.88/1.49  --dbg_out_stat                          false
% 7.88/1.49  
% 7.88/1.49  
% 7.88/1.49  
% 7.88/1.49  
% 7.88/1.49  ------ Proving...
% 7.88/1.49  
% 7.88/1.49  
% 7.88/1.49  % SZS status Theorem for theBenchmark.p
% 7.88/1.49  
% 7.88/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.88/1.49  
% 7.88/1.49  fof(f5,axiom,(
% 7.88/1.49    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 7.88/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.88/1.49  
% 7.88/1.49  fof(f56,plain,(
% 7.88/1.49    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 7.88/1.49    inference(cnf_transformation,[],[f5])).
% 7.88/1.49  
% 7.88/1.49  fof(f4,axiom,(
% 7.88/1.49    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 7.88/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.88/1.49  
% 7.88/1.49  fof(f15,plain,(
% 7.88/1.49    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1))),
% 7.88/1.49    inference(ennf_transformation,[],[f4])).
% 7.88/1.49  
% 7.88/1.49  fof(f55,plain,(
% 7.88/1.49    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1)) )),
% 7.88/1.49    inference(cnf_transformation,[],[f15])).
% 7.88/1.49  
% 7.88/1.49  fof(f7,axiom,(
% 7.88/1.49    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 7.88/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.88/1.49  
% 7.88/1.49  fof(f29,plain,(
% 7.88/1.49    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 7.88/1.49    inference(nnf_transformation,[],[f7])).
% 7.88/1.49  
% 7.88/1.49  fof(f30,plain,(
% 7.88/1.49    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 7.88/1.49    inference(rectify,[],[f29])).
% 7.88/1.49  
% 7.88/1.49  fof(f33,plain,(
% 7.88/1.49    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0))),
% 7.88/1.49    introduced(choice_axiom,[])).
% 7.88/1.49  
% 7.88/1.49  fof(f32,plain,(
% 7.88/1.49    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) => r2_hidden(k4_tarski(X2,sK2(X0,X1)),X0))) )),
% 7.88/1.49    introduced(choice_axiom,[])).
% 7.88/1.49  
% 7.88/1.49  fof(f31,plain,(
% 7.88/1.49    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK1(X0,X1),X3),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK1(X0,X1),X4),X0) | r2_hidden(sK1(X0,X1),X1))))),
% 7.88/1.49    introduced(choice_axiom,[])).
% 7.88/1.49  
% 7.88/1.49  fof(f34,plain,(
% 7.88/1.49    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK1(X0,X1),X3),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 7.88/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f30,f33,f32,f31])).
% 7.88/1.49  
% 7.88/1.49  fof(f60,plain,(
% 7.88/1.49    ( ! [X0,X1] : (k1_relat_1(X0) = X1 | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) | r2_hidden(sK1(X0,X1),X1)) )),
% 7.88/1.49    inference(cnf_transformation,[],[f34])).
% 7.88/1.49  
% 7.88/1.49  fof(f12,axiom,(
% 7.88/1.49    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 7.88/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.88/1.49  
% 7.88/1.49  fof(f71,plain,(
% 7.88/1.49    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 7.88/1.49    inference(cnf_transformation,[],[f12])).
% 7.88/1.49  
% 7.88/1.49  fof(f10,axiom,(
% 7.88/1.49    ! [X0,X1] : (v1_relat_1(X1) => ~(! [X2] : ~r2_hidden(X2,k1_relat_1(X1)) & r2_hidden(X0,k2_relat_1(X1))))),
% 7.88/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.88/1.49  
% 7.88/1.49  fof(f19,plain,(
% 7.88/1.49    ! [X0,X1] : ((? [X2] : r2_hidden(X2,k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1))) | ~v1_relat_1(X1))),
% 7.88/1.49    inference(ennf_transformation,[],[f10])).
% 7.88/1.49  
% 7.88/1.49  fof(f20,plain,(
% 7.88/1.49    ! [X0,X1] : (? [X2] : r2_hidden(X2,k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 7.88/1.49    inference(flattening,[],[f19])).
% 7.88/1.49  
% 7.88/1.49  fof(f39,plain,(
% 7.88/1.49    ! [X1] : (? [X2] : r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(sK5(X1),k1_relat_1(X1)))),
% 7.88/1.49    introduced(choice_axiom,[])).
% 7.88/1.49  
% 7.88/1.49  fof(f40,plain,(
% 7.88/1.49    ! [X0,X1] : (r2_hidden(sK5(X1),k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 7.88/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f20,f39])).
% 7.88/1.49  
% 7.88/1.49  fof(f67,plain,(
% 7.88/1.49    ( ! [X0,X1] : (r2_hidden(sK5(X1),k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 7.88/1.49    inference(cnf_transformation,[],[f40])).
% 7.88/1.49  
% 7.88/1.49  fof(f70,plain,(
% 7.88/1.49    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 7.88/1.49    inference(cnf_transformation,[],[f12])).
% 7.88/1.49  
% 7.88/1.49  fof(f13,conjecture,(
% 7.88/1.49    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 7.88/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.88/1.49  
% 7.88/1.49  fof(f14,negated_conjecture,(
% 7.88/1.49    ~! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 7.88/1.49    inference(negated_conjecture,[],[f13])).
% 7.88/1.49  
% 7.88/1.49  fof(f22,plain,(
% 7.88/1.49    ? [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <~> k1_xboole_0 != k11_relat_1(X1,X0)) & v1_relat_1(X1))),
% 7.88/1.49    inference(ennf_transformation,[],[f14])).
% 7.88/1.49  
% 7.88/1.49  fof(f42,plain,(
% 7.88/1.49    ? [X0,X1] : (((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1)))) & v1_relat_1(X1))),
% 7.88/1.49    inference(nnf_transformation,[],[f22])).
% 7.88/1.49  
% 7.88/1.49  fof(f43,plain,(
% 7.88/1.49    ? [X0,X1] : ((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 7.88/1.49    inference(flattening,[],[f42])).
% 7.88/1.49  
% 7.88/1.49  fof(f44,plain,(
% 7.88/1.49    ? [X0,X1] : ((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1))) & v1_relat_1(X1)) => ((k1_xboole_0 = k11_relat_1(sK7,sK6) | ~r2_hidden(sK6,k1_relat_1(sK7))) & (k1_xboole_0 != k11_relat_1(sK7,sK6) | r2_hidden(sK6,k1_relat_1(sK7))) & v1_relat_1(sK7))),
% 7.88/1.49    introduced(choice_axiom,[])).
% 7.88/1.49  
% 7.88/1.49  fof(f45,plain,(
% 7.88/1.49    (k1_xboole_0 = k11_relat_1(sK7,sK6) | ~r2_hidden(sK6,k1_relat_1(sK7))) & (k1_xboole_0 != k11_relat_1(sK7,sK6) | r2_hidden(sK6,k1_relat_1(sK7))) & v1_relat_1(sK7)),
% 7.88/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f43,f44])).
% 7.88/1.49  
% 7.88/1.49  fof(f72,plain,(
% 7.88/1.49    v1_relat_1(sK7)),
% 7.88/1.49    inference(cnf_transformation,[],[f45])).
% 7.88/1.49  
% 7.88/1.49  fof(f2,axiom,(
% 7.88/1.49    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 7.88/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.88/1.49  
% 7.88/1.49  fof(f52,plain,(
% 7.88/1.49    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 7.88/1.49    inference(cnf_transformation,[],[f2])).
% 7.88/1.49  
% 7.88/1.49  fof(f8,axiom,(
% 7.88/1.49    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k3_xboole_0(X0,X1)))),
% 7.88/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.88/1.49  
% 7.88/1.49  fof(f17,plain,(
% 7.88/1.49    ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 7.88/1.49    inference(ennf_transformation,[],[f8])).
% 7.88/1.49  
% 7.88/1.49  fof(f62,plain,(
% 7.88/1.49    ( ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 7.88/1.49    inference(cnf_transformation,[],[f17])).
% 7.88/1.49  
% 7.88/1.49  fof(f9,axiom,(
% 7.88/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 7.88/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.88/1.49  
% 7.88/1.49  fof(f18,plain,(
% 7.88/1.49    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 7.88/1.49    inference(ennf_transformation,[],[f9])).
% 7.88/1.49  
% 7.88/1.49  fof(f35,plain,(
% 7.88/1.49    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 7.88/1.49    inference(nnf_transformation,[],[f18])).
% 7.88/1.49  
% 7.88/1.49  fof(f36,plain,(
% 7.88/1.49    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 7.88/1.49    inference(rectify,[],[f35])).
% 7.88/1.49  
% 7.88/1.49  fof(f37,plain,(
% 7.88/1.49    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2) & r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2))))),
% 7.88/1.49    introduced(choice_axiom,[])).
% 7.88/1.49  
% 7.88/1.49  fof(f38,plain,(
% 7.88/1.49    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2) & r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 7.88/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f36,f37])).
% 7.88/1.49  
% 7.88/1.49  fof(f65,plain,(
% 7.88/1.49    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 7.88/1.49    inference(cnf_transformation,[],[f38])).
% 7.88/1.49  
% 7.88/1.49  fof(f63,plain,(
% 7.88/1.49    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2)) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 7.88/1.49    inference(cnf_transformation,[],[f38])).
% 7.88/1.49  
% 7.88/1.49  fof(f3,axiom,(
% 7.88/1.49    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) <=> ~r2_hidden(X0,X1))),
% 7.88/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.88/1.49  
% 7.88/1.49  fof(f28,plain,(
% 7.88/1.49    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) | r2_hidden(X0,X1)) & (~r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0)))),
% 7.88/1.49    inference(nnf_transformation,[],[f3])).
% 7.88/1.49  
% 7.88/1.49  fof(f54,plain,(
% 7.88/1.49    ( ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) | r2_hidden(X0,X1)) )),
% 7.88/1.49    inference(cnf_transformation,[],[f28])).
% 7.88/1.49  
% 7.88/1.49  fof(f74,plain,(
% 7.88/1.49    k1_xboole_0 = k11_relat_1(sK7,sK6) | ~r2_hidden(sK6,k1_relat_1(sK7))),
% 7.88/1.49    inference(cnf_transformation,[],[f45])).
% 7.88/1.49  
% 7.88/1.49  fof(f1,axiom,(
% 7.88/1.49    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 7.88/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.88/1.49  
% 7.88/1.49  fof(f23,plain,(
% 7.88/1.49    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.88/1.49    inference(nnf_transformation,[],[f1])).
% 7.88/1.49  
% 7.88/1.49  fof(f24,plain,(
% 7.88/1.49    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.88/1.49    inference(flattening,[],[f23])).
% 7.88/1.49  
% 7.88/1.49  fof(f25,plain,(
% 7.88/1.49    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.88/1.49    inference(rectify,[],[f24])).
% 7.88/1.49  
% 7.88/1.49  fof(f26,plain,(
% 7.88/1.49    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 7.88/1.49    introduced(choice_axiom,[])).
% 7.88/1.49  
% 7.88/1.49  fof(f27,plain,(
% 7.88/1.49    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.88/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).
% 7.88/1.49  
% 7.88/1.49  fof(f47,plain,(
% 7.88/1.49    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 7.88/1.49    inference(cnf_transformation,[],[f27])).
% 7.88/1.49  
% 7.88/1.49  fof(f76,plain,(
% 7.88/1.49    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 7.88/1.49    inference(equality_resolution,[],[f47])).
% 7.88/1.49  
% 7.88/1.49  fof(f6,axiom,(
% 7.88/1.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 7.88/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.88/1.49  
% 7.88/1.49  fof(f16,plain,(
% 7.88/1.49    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 7.88/1.49    inference(ennf_transformation,[],[f6])).
% 7.88/1.49  
% 7.88/1.49  fof(f57,plain,(
% 7.88/1.49    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 7.88/1.49    inference(cnf_transformation,[],[f16])).
% 7.88/1.49  
% 7.88/1.49  fof(f11,axiom,(
% 7.88/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))))),
% 7.88/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.88/1.49  
% 7.88/1.49  fof(f21,plain,(
% 7.88/1.49    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))) | ~v1_relat_1(X2))),
% 7.88/1.49    inference(ennf_transformation,[],[f11])).
% 7.88/1.49  
% 7.88/1.49  fof(f41,plain,(
% 7.88/1.49    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(X1,k11_relat_1(X2,X0))) & (r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_relat_1(X2))),
% 7.88/1.49    inference(nnf_transformation,[],[f21])).
% 7.88/1.49  
% 7.88/1.49  fof(f68,plain,(
% 7.88/1.49    ( ! [X2,X0,X1] : (r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 7.88/1.49    inference(cnf_transformation,[],[f41])).
% 7.88/1.49  
% 7.88/1.49  fof(f58,plain,(
% 7.88/1.49    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 7.88/1.49    inference(cnf_transformation,[],[f34])).
% 7.88/1.49  
% 7.88/1.49  fof(f79,plain,(
% 7.88/1.49    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 7.88/1.49    inference(equality_resolution,[],[f58])).
% 7.88/1.49  
% 7.88/1.49  fof(f73,plain,(
% 7.88/1.49    k1_xboole_0 != k11_relat_1(sK7,sK6) | r2_hidden(sK6,k1_relat_1(sK7))),
% 7.88/1.49    inference(cnf_transformation,[],[f45])).
% 7.88/1.49  
% 7.88/1.49  cnf(c_10,plain,
% 7.88/1.49      ( k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
% 7.88/1.49      inference(cnf_transformation,[],[f56]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_24647,plain,
% 7.88/1.49      ( k2_xboole_0(k1_tarski(sK3(sK7,sK6)),k11_relat_1(sK7,sK6)) != k1_xboole_0 ),
% 7.88/1.49      inference(instantiation,[status(thm)],[c_10]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_355,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_1362,plain,
% 7.88/1.49      ( X0 != X1
% 7.88/1.49      | k2_xboole_0(k1_tarski(X2),X3) != X1
% 7.88/1.49      | k2_xboole_0(k1_tarski(X2),X3) = X0 ),
% 7.88/1.49      inference(instantiation,[status(thm)],[c_355]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_9260,plain,
% 7.88/1.49      ( X0 != k11_relat_1(sK7,sK6)
% 7.88/1.49      | k2_xboole_0(k1_tarski(sK3(sK7,sK6)),k11_relat_1(sK7,sK6)) = X0
% 7.88/1.49      | k2_xboole_0(k1_tarski(sK3(sK7,sK6)),k11_relat_1(sK7,sK6)) != k11_relat_1(sK7,sK6) ),
% 7.88/1.49      inference(instantiation,[status(thm)],[c_1362]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_9261,plain,
% 7.88/1.49      ( k2_xboole_0(k1_tarski(sK3(sK7,sK6)),k11_relat_1(sK7,sK6)) != k11_relat_1(sK7,sK6)
% 7.88/1.49      | k2_xboole_0(k1_tarski(sK3(sK7,sK6)),k11_relat_1(sK7,sK6)) = k1_xboole_0
% 7.88/1.49      | k1_xboole_0 != k11_relat_1(sK7,sK6) ),
% 7.88/1.49      inference(instantiation,[status(thm)],[c_9260]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_9,plain,
% 7.88/1.49      ( ~ r2_hidden(X0,X1) | k2_xboole_0(k1_tarski(X0),X1) = X1 ),
% 7.88/1.49      inference(cnf_transformation,[],[f55]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_7423,plain,
% 7.88/1.49      ( ~ r2_hidden(sK3(sK7,sK6),k11_relat_1(sK7,sK6))
% 7.88/1.49      | k2_xboole_0(k1_tarski(sK3(sK7,sK6)),k11_relat_1(sK7,sK6)) = k11_relat_1(sK7,sK6) ),
% 7.88/1.49      inference(instantiation,[status(thm)],[c_9]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_13,plain,
% 7.88/1.49      ( r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
% 7.88/1.49      | r2_hidden(sK1(X0,X1),X1)
% 7.88/1.49      | k1_relat_1(X0) = X1 ),
% 7.88/1.49      inference(cnf_transformation,[],[f60]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_954,plain,
% 7.88/1.49      ( k1_relat_1(X0) = X1
% 7.88/1.49      | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) = iProver_top
% 7.88/1.49      | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
% 7.88/1.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_24,plain,
% 7.88/1.49      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 7.88/1.49      inference(cnf_transformation,[],[f71]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_21,plain,
% 7.88/1.49      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 7.88/1.49      | r2_hidden(sK5(X1),k1_relat_1(X1))
% 7.88/1.49      | ~ v1_relat_1(X1) ),
% 7.88/1.49      inference(cnf_transformation,[],[f67]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_946,plain,
% 7.88/1.49      ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
% 7.88/1.49      | r2_hidden(sK5(X1),k1_relat_1(X1)) = iProver_top
% 7.88/1.49      | v1_relat_1(X1) != iProver_top ),
% 7.88/1.49      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_1911,plain,
% 7.88/1.49      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 7.88/1.49      | r2_hidden(sK5(k1_xboole_0),k1_relat_1(k1_xboole_0)) = iProver_top
% 7.88/1.49      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 7.88/1.49      inference(superposition,[status(thm)],[c_24,c_946]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_25,plain,
% 7.88/1.49      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 7.88/1.49      inference(cnf_transformation,[],[f70]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_1915,plain,
% 7.88/1.49      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 7.88/1.49      | r2_hidden(sK5(k1_xboole_0),k1_xboole_0) = iProver_top
% 7.88/1.49      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 7.88/1.49      inference(light_normalisation,[status(thm)],[c_1911,c_25]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_28,negated_conjecture,
% 7.88/1.49      ( v1_relat_1(sK7) ),
% 7.88/1.49      inference(cnf_transformation,[],[f72]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_941,plain,
% 7.88/1.49      ( v1_relat_1(sK7) = iProver_top ),
% 7.88/1.49      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_6,plain,
% 7.88/1.49      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 7.88/1.49      inference(cnf_transformation,[],[f52]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_16,plain,
% 7.88/1.49      ( ~ v1_relat_1(X0) | v1_relat_1(k3_xboole_0(X0,X1)) ),
% 7.88/1.49      inference(cnf_transformation,[],[f62]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_951,plain,
% 7.88/1.49      ( v1_relat_1(X0) != iProver_top
% 7.88/1.49      | v1_relat_1(k3_xboole_0(X0,X1)) = iProver_top ),
% 7.88/1.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_1226,plain,
% 7.88/1.49      ( v1_relat_1(X0) != iProver_top
% 7.88/1.49      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 7.88/1.49      inference(superposition,[status(thm)],[c_6,c_951]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_1352,plain,
% 7.88/1.49      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 7.88/1.49      inference(superposition,[status(thm)],[c_941,c_1226]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_2565,plain,
% 7.88/1.49      ( r2_hidden(sK5(k1_xboole_0),k1_xboole_0) = iProver_top
% 7.88/1.49      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.88/1.49      inference(global_propositional_subsumption,
% 7.88/1.49                [status(thm)],
% 7.88/1.49                [c_1915,c_1352]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_2566,plain,
% 7.88/1.49      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 7.88/1.49      | r2_hidden(sK5(k1_xboole_0),k1_xboole_0) = iProver_top ),
% 7.88/1.49      inference(renaming,[status(thm)],[c_2565]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_4283,plain,
% 7.88/1.49      ( k1_relat_1(k1_xboole_0) = X0
% 7.88/1.49      | r2_hidden(sK1(k1_xboole_0,X0),X0) = iProver_top
% 7.88/1.49      | r2_hidden(sK5(k1_xboole_0),k1_xboole_0) = iProver_top ),
% 7.88/1.49      inference(superposition,[status(thm)],[c_954,c_2566]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_4339,plain,
% 7.88/1.49      ( k1_xboole_0 = X0
% 7.88/1.49      | r2_hidden(sK1(k1_xboole_0,X0),X0) = iProver_top
% 7.88/1.49      | r2_hidden(sK5(k1_xboole_0),k1_xboole_0) = iProver_top ),
% 7.88/1.49      inference(demodulation,[status(thm)],[c_4283,c_25]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_18,plain,
% 7.88/1.49      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 7.88/1.49      | r2_hidden(sK4(X0,X2,X1),X2)
% 7.88/1.49      | ~ v1_relat_1(X1) ),
% 7.88/1.49      inference(cnf_transformation,[],[f65]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_949,plain,
% 7.88/1.49      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 7.88/1.49      | r2_hidden(sK4(X0,X2,X1),X2) = iProver_top
% 7.88/1.49      | v1_relat_1(X1) != iProver_top ),
% 7.88/1.49      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_20,plain,
% 7.88/1.49      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 7.88/1.49      | r2_hidden(sK4(X0,X2,X1),k1_relat_1(X1))
% 7.88/1.49      | ~ v1_relat_1(X1) ),
% 7.88/1.49      inference(cnf_transformation,[],[f63]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_947,plain,
% 7.88/1.49      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 7.88/1.49      | r2_hidden(sK4(X0,X2,X1),k1_relat_1(X1)) = iProver_top
% 7.88/1.49      | v1_relat_1(X1) != iProver_top ),
% 7.88/1.49      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_7,plain,
% 7.88/1.49      ( r2_hidden(X0,X1)
% 7.88/1.49      | k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) ),
% 7.88/1.49      inference(cnf_transformation,[],[f54]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_959,plain,
% 7.88/1.49      ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
% 7.88/1.49      | r2_hidden(X0,X1) = iProver_top ),
% 7.88/1.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_26,negated_conjecture,
% 7.88/1.49      ( ~ r2_hidden(sK6,k1_relat_1(sK7))
% 7.88/1.49      | k1_xboole_0 = k11_relat_1(sK7,sK6) ),
% 7.88/1.49      inference(cnf_transformation,[],[f74]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_943,plain,
% 7.88/1.49      ( k1_xboole_0 = k11_relat_1(sK7,sK6)
% 7.88/1.49      | r2_hidden(sK6,k1_relat_1(sK7)) != iProver_top ),
% 7.88/1.49      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_1398,plain,
% 7.88/1.49      ( k11_relat_1(sK7,sK6) = k1_xboole_0
% 7.88/1.49      | k4_xboole_0(k1_tarski(sK6),k1_relat_1(sK7)) = k1_tarski(sK6) ),
% 7.88/1.49      inference(superposition,[status(thm)],[c_959,c_943]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_4,plain,
% 7.88/1.49      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 7.88/1.49      inference(cnf_transformation,[],[f76]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_961,plain,
% 7.88/1.49      ( r2_hidden(X0,X1) != iProver_top
% 7.88/1.49      | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
% 7.88/1.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_1683,plain,
% 7.88/1.49      ( k11_relat_1(sK7,sK6) = k1_xboole_0
% 7.88/1.49      | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
% 7.88/1.49      | r2_hidden(X0,k1_tarski(sK6)) != iProver_top ),
% 7.88/1.49      inference(superposition,[status(thm)],[c_1398,c_961]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_2501,plain,
% 7.88/1.49      ( k11_relat_1(sK7,sK6) = k1_xboole_0
% 7.88/1.49      | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 7.88/1.49      | r2_hidden(sK4(X0,X1,sK7),k1_tarski(sK6)) != iProver_top
% 7.88/1.49      | v1_relat_1(sK7) != iProver_top ),
% 7.88/1.49      inference(superposition,[status(thm)],[c_947,c_1683]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_29,plain,
% 7.88/1.49      ( v1_relat_1(sK7) = iProver_top ),
% 7.88/1.49      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_3134,plain,
% 7.88/1.49      ( r2_hidden(sK4(X0,X1,sK7),k1_tarski(sK6)) != iProver_top
% 7.88/1.49      | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 7.88/1.49      | k11_relat_1(sK7,sK6) = k1_xboole_0 ),
% 7.88/1.49      inference(global_propositional_subsumption,
% 7.88/1.49                [status(thm)],
% 7.88/1.49                [c_2501,c_29]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_3135,plain,
% 7.88/1.49      ( k11_relat_1(sK7,sK6) = k1_xboole_0
% 7.88/1.49      | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 7.88/1.49      | r2_hidden(sK4(X0,X1,sK7),k1_tarski(sK6)) != iProver_top ),
% 7.88/1.49      inference(renaming,[status(thm)],[c_3134]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_3144,plain,
% 7.88/1.49      ( k11_relat_1(sK7,sK6) = k1_xboole_0
% 7.88/1.49      | r2_hidden(X0,k9_relat_1(sK7,k1_tarski(sK6))) != iProver_top
% 7.88/1.49      | v1_relat_1(sK7) != iProver_top ),
% 7.88/1.49      inference(superposition,[status(thm)],[c_949,c_3135]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_11,plain,
% 7.88/1.49      ( ~ v1_relat_1(X0)
% 7.88/1.49      | k9_relat_1(X0,k1_tarski(X1)) = k11_relat_1(X0,X1) ),
% 7.88/1.49      inference(cnf_transformation,[],[f57]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_956,plain,
% 7.88/1.49      ( k9_relat_1(X0,k1_tarski(X1)) = k11_relat_1(X0,X1)
% 7.88/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.88/1.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_1435,plain,
% 7.88/1.49      ( k9_relat_1(sK7,k1_tarski(X0)) = k11_relat_1(sK7,X0) ),
% 7.88/1.49      inference(superposition,[status(thm)],[c_941,c_956]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_3148,plain,
% 7.88/1.49      ( k11_relat_1(sK7,sK6) = k1_xboole_0
% 7.88/1.49      | r2_hidden(X0,k11_relat_1(sK7,sK6)) != iProver_top
% 7.88/1.49      | v1_relat_1(sK7) != iProver_top ),
% 7.88/1.49      inference(demodulation,[status(thm)],[c_3144,c_1435]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_3189,plain,
% 7.88/1.49      ( r2_hidden(X0,k11_relat_1(sK7,sK6)) != iProver_top
% 7.88/1.49      | k11_relat_1(sK7,sK6) = k1_xboole_0 ),
% 7.88/1.49      inference(global_propositional_subsumption,
% 7.88/1.49                [status(thm)],
% 7.88/1.49                [c_3148,c_29]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_3190,plain,
% 7.88/1.49      ( k11_relat_1(sK7,sK6) = k1_xboole_0
% 7.88/1.49      | r2_hidden(X0,k11_relat_1(sK7,sK6)) != iProver_top ),
% 7.88/1.49      inference(renaming,[status(thm)],[c_3189]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_4474,plain,
% 7.88/1.49      ( k11_relat_1(sK7,sK6) = k1_xboole_0
% 7.88/1.49      | r2_hidden(sK5(k1_xboole_0),k1_xboole_0) = iProver_top ),
% 7.88/1.49      inference(superposition,[status(thm)],[c_4339,c_3190]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_957,plain,
% 7.88/1.49      ( k2_xboole_0(k1_tarski(X0),X1) = X1
% 7.88/1.49      | r2_hidden(X0,X1) != iProver_top ),
% 7.88/1.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_4897,plain,
% 7.88/1.49      ( k11_relat_1(sK7,sK6) = k1_xboole_0
% 7.88/1.49      | k2_xboole_0(k1_tarski(sK5(k1_xboole_0)),k1_xboole_0) = k1_xboole_0 ),
% 7.88/1.49      inference(superposition,[status(thm)],[c_4474,c_957]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_5672,plain,
% 7.88/1.49      ( k11_relat_1(sK7,sK6) = k1_xboole_0 ),
% 7.88/1.50      inference(forward_subsumption_resolution,
% 7.88/1.50                [status(thm)],
% 7.88/1.50                [c_4897,c_10]) ).
% 7.88/1.50  
% 7.88/1.50  cnf(c_23,plain,
% 7.88/1.50      ( r2_hidden(X0,k11_relat_1(X1,X2))
% 7.88/1.50      | ~ r2_hidden(k4_tarski(X2,X0),X1)
% 7.88/1.50      | ~ v1_relat_1(X1) ),
% 7.88/1.50      inference(cnf_transformation,[],[f68]) ).
% 7.88/1.50  
% 7.88/1.50  cnf(c_1195,plain,
% 7.88/1.50      ( r2_hidden(X0,k11_relat_1(sK7,X1))
% 7.88/1.50      | ~ r2_hidden(k4_tarski(X1,X0),sK7)
% 7.88/1.50      | ~ v1_relat_1(sK7) ),
% 7.88/1.50      inference(instantiation,[status(thm)],[c_23]) ).
% 7.88/1.50  
% 7.88/1.50  cnf(c_2045,plain,
% 7.88/1.50      ( r2_hidden(sK3(sK7,X0),k11_relat_1(sK7,X0))
% 7.88/1.50      | ~ r2_hidden(k4_tarski(X0,sK3(sK7,X0)),sK7)
% 7.88/1.50      | ~ v1_relat_1(sK7) ),
% 7.88/1.50      inference(instantiation,[status(thm)],[c_1195]) ).
% 7.88/1.50  
% 7.88/1.50  cnf(c_3990,plain,
% 7.88/1.50      ( r2_hidden(sK3(sK7,sK6),k11_relat_1(sK7,sK6))
% 7.88/1.50      | ~ r2_hidden(k4_tarski(sK6,sK3(sK7,sK6)),sK7)
% 7.88/1.50      | ~ v1_relat_1(sK7) ),
% 7.88/1.50      inference(instantiation,[status(thm)],[c_2045]) ).
% 7.88/1.50  
% 7.88/1.50  cnf(c_15,plain,
% 7.88/1.50      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 7.88/1.50      | r2_hidden(k4_tarski(X0,sK3(X1,X0)),X1) ),
% 7.88/1.50      inference(cnf_transformation,[],[f79]) ).
% 7.88/1.50  
% 7.88/1.50  cnf(c_2044,plain,
% 7.88/1.50      ( ~ r2_hidden(X0,k1_relat_1(sK7))
% 7.88/1.50      | r2_hidden(k4_tarski(X0,sK3(sK7,X0)),sK7) ),
% 7.88/1.50      inference(instantiation,[status(thm)],[c_15]) ).
% 7.88/1.50  
% 7.88/1.50  cnf(c_3432,plain,
% 7.88/1.50      ( r2_hidden(k4_tarski(sK6,sK3(sK7,sK6)),sK7)
% 7.88/1.50      | ~ r2_hidden(sK6,k1_relat_1(sK7)) ),
% 7.88/1.50      inference(instantiation,[status(thm)],[c_2044]) ).
% 7.88/1.50  
% 7.88/1.50  cnf(c_1188,plain,
% 7.88/1.50      ( k11_relat_1(sK7,sK6) != X0
% 7.88/1.50      | k1_xboole_0 != X0
% 7.88/1.50      | k1_xboole_0 = k11_relat_1(sK7,sK6) ),
% 7.88/1.50      inference(instantiation,[status(thm)],[c_355]) ).
% 7.88/1.50  
% 7.88/1.50  cnf(c_1189,plain,
% 7.88/1.50      ( k11_relat_1(sK7,sK6) != k1_xboole_0
% 7.88/1.50      | k1_xboole_0 = k11_relat_1(sK7,sK6)
% 7.88/1.50      | k1_xboole_0 != k1_xboole_0 ),
% 7.88/1.50      inference(instantiation,[status(thm)],[c_1188]) ).
% 7.88/1.50  
% 7.88/1.50  cnf(c_354,plain,( X0 = X0 ),theory(equality) ).
% 7.88/1.50  
% 7.88/1.50  cnf(c_377,plain,
% 7.88/1.50      ( k1_xboole_0 = k1_xboole_0 ),
% 7.88/1.50      inference(instantiation,[status(thm)],[c_354]) ).
% 7.88/1.50  
% 7.88/1.50  cnf(c_27,negated_conjecture,
% 7.88/1.50      ( r2_hidden(sK6,k1_relat_1(sK7))
% 7.88/1.50      | k1_xboole_0 != k11_relat_1(sK7,sK6) ),
% 7.88/1.50      inference(cnf_transformation,[],[f73]) ).
% 7.88/1.50  
% 7.88/1.50  cnf(contradiction,plain,
% 7.88/1.50      ( $false ),
% 7.88/1.50      inference(minisat,
% 7.88/1.50                [status(thm)],
% 7.88/1.50                [c_24647,c_9261,c_7423,c_5672,c_3990,c_3432,c_1189,c_377,
% 7.88/1.50                 c_27,c_28]) ).
% 7.88/1.50  
% 7.88/1.50  
% 7.88/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.88/1.50  
% 7.88/1.50  ------                               Statistics
% 7.88/1.50  
% 7.88/1.50  ------ General
% 7.88/1.50  
% 7.88/1.50  abstr_ref_over_cycles:                  0
% 7.88/1.50  abstr_ref_under_cycles:                 0
% 7.88/1.50  gc_basic_clause_elim:                   0
% 7.88/1.50  forced_gc_time:                         0
% 7.88/1.50  parsing_time:                           0.013
% 7.88/1.50  unif_index_cands_time:                  0.
% 7.88/1.50  unif_index_add_time:                    0.
% 7.88/1.50  orderings_time:                         0.
% 7.88/1.50  out_proof_time:                         0.01
% 7.88/1.50  total_time:                             0.967
% 7.88/1.50  num_of_symbols:                         51
% 7.88/1.50  num_of_terms:                           33182
% 7.88/1.50  
% 7.88/1.50  ------ Preprocessing
% 7.88/1.50  
% 7.88/1.50  num_of_splits:                          0
% 7.88/1.50  num_of_split_atoms:                     0
% 7.88/1.50  num_of_reused_defs:                     0
% 7.88/1.50  num_eq_ax_congr_red:                    36
% 7.88/1.50  num_of_sem_filtered_clauses:            1
% 7.88/1.50  num_of_subtypes:                        0
% 7.88/1.50  monotx_restored_types:                  0
% 7.88/1.50  sat_num_of_epr_types:                   0
% 7.88/1.50  sat_num_of_non_cyclic_types:            0
% 7.88/1.50  sat_guarded_non_collapsed_types:        0
% 7.88/1.50  num_pure_diseq_elim:                    0
% 7.88/1.50  simp_replaced_by:                       0
% 7.88/1.50  res_preprocessed:                       112
% 7.88/1.50  prep_upred:                             0
% 7.88/1.50  prep_unflattend:                        0
% 7.88/1.50  smt_new_axioms:                         0
% 7.88/1.50  pred_elim_cands:                        2
% 7.88/1.50  pred_elim:                              0
% 7.88/1.50  pred_elim_cl:                           0
% 7.88/1.50  pred_elim_cycles:                       1
% 7.88/1.50  merged_defs:                            12
% 7.88/1.50  merged_defs_ncl:                        0
% 7.88/1.50  bin_hyper_res:                          12
% 7.88/1.50  prep_cycles:                            3
% 7.88/1.50  pred_elim_time:                         0.
% 7.88/1.50  splitting_time:                         0.
% 7.88/1.50  sem_filter_time:                        0.
% 7.88/1.50  monotx_time:                            0.001
% 7.88/1.50  subtype_inf_time:                       0.
% 7.88/1.50  
% 7.88/1.50  ------ Problem properties
% 7.88/1.50  
% 7.88/1.50  clauses:                                29
% 7.88/1.50  conjectures:                            3
% 7.88/1.50  epr:                                    1
% 7.88/1.50  horn:                                   23
% 7.88/1.50  ground:                                 5
% 7.88/1.50  unary:                                  5
% 7.88/1.50  binary:                                 11
% 7.88/1.50  lits:                                   69
% 7.88/1.50  lits_eq:                                15
% 7.88/1.50  fd_pure:                                0
% 7.88/1.50  fd_pseudo:                              0
% 7.88/1.50  fd_cond:                                0
% 7.88/1.50  fd_pseudo_cond:                         5
% 7.88/1.50  ac_symbols:                             0
% 7.88/1.50  
% 7.88/1.50  ------ Propositional Solver
% 7.88/1.50  
% 7.88/1.50  prop_solver_calls:                      27
% 7.88/1.50  prop_fast_solver_calls:                 960
% 7.88/1.50  smt_solver_calls:                       0
% 7.88/1.50  smt_fast_solver_calls:                  0
% 7.88/1.50  prop_num_of_clauses:                    9989
% 7.88/1.50  prop_preprocess_simplified:             14432
% 7.88/1.50  prop_fo_subsumed:                       11
% 7.88/1.50  prop_solver_time:                       0.
% 7.88/1.50  smt_solver_time:                        0.
% 7.88/1.50  smt_fast_solver_time:                   0.
% 7.88/1.50  prop_fast_solver_time:                  0.
% 7.88/1.50  prop_unsat_core_time:                   0.001
% 7.88/1.50  
% 7.88/1.50  ------ QBF
% 7.88/1.50  
% 7.88/1.50  qbf_q_res:                              0
% 7.88/1.50  qbf_num_tautologies:                    0
% 7.88/1.50  qbf_prep_cycles:                        0
% 7.88/1.50  
% 7.88/1.50  ------ BMC1
% 7.88/1.50  
% 7.88/1.50  bmc1_current_bound:                     -1
% 7.88/1.50  bmc1_last_solved_bound:                 -1
% 7.88/1.50  bmc1_unsat_core_size:                   -1
% 7.88/1.50  bmc1_unsat_core_parents_size:           -1
% 7.88/1.50  bmc1_merge_next_fun:                    0
% 7.88/1.50  bmc1_unsat_core_clauses_time:           0.
% 7.88/1.50  
% 7.88/1.50  ------ Instantiation
% 7.88/1.50  
% 7.88/1.50  inst_num_of_clauses:                    2217
% 7.88/1.50  inst_num_in_passive:                    682
% 7.88/1.50  inst_num_in_active:                     743
% 7.88/1.50  inst_num_in_unprocessed:                791
% 7.88/1.50  inst_num_of_loops:                      956
% 7.88/1.50  inst_num_of_learning_restarts:          0
% 7.88/1.50  inst_num_moves_active_passive:          207
% 7.88/1.50  inst_lit_activity:                      0
% 7.88/1.50  inst_lit_activity_moves:                0
% 7.88/1.50  inst_num_tautologies:                   0
% 7.88/1.50  inst_num_prop_implied:                  0
% 7.88/1.50  inst_num_existing_simplified:           0
% 7.88/1.50  inst_num_eq_res_simplified:             0
% 7.88/1.50  inst_num_child_elim:                    0
% 7.88/1.50  inst_num_of_dismatching_blockings:      2123
% 7.88/1.50  inst_num_of_non_proper_insts:           1738
% 7.88/1.50  inst_num_of_duplicates:                 0
% 7.88/1.50  inst_inst_num_from_inst_to_res:         0
% 7.88/1.50  inst_dismatching_checking_time:         0.
% 7.88/1.50  
% 7.88/1.50  ------ Resolution
% 7.88/1.50  
% 7.88/1.50  res_num_of_clauses:                     0
% 7.88/1.50  res_num_in_passive:                     0
% 7.88/1.50  res_num_in_active:                      0
% 7.88/1.50  res_num_of_loops:                       115
% 7.88/1.50  res_forward_subset_subsumed:            81
% 7.88/1.50  res_backward_subset_subsumed:           0
% 7.88/1.50  res_forward_subsumed:                   0
% 7.88/1.50  res_backward_subsumed:                  0
% 7.88/1.50  res_forward_subsumption_resolution:     0
% 7.88/1.50  res_backward_subsumption_resolution:    0
% 7.88/1.50  res_clause_to_clause_subsumption:       3293
% 7.88/1.50  res_orphan_elimination:                 0
% 7.88/1.50  res_tautology_del:                      175
% 7.88/1.50  res_num_eq_res_simplified:              0
% 7.88/1.50  res_num_sel_changes:                    0
% 7.88/1.50  res_moves_from_active_to_pass:          0
% 7.88/1.50  
% 7.88/1.50  ------ Superposition
% 7.88/1.50  
% 7.88/1.50  sup_time_total:                         0.
% 7.88/1.50  sup_time_generating:                    0.
% 7.88/1.50  sup_time_sim_full:                      0.
% 7.88/1.50  sup_time_sim_immed:                     0.
% 7.88/1.50  
% 7.88/1.50  sup_num_of_clauses:                     868
% 7.88/1.50  sup_num_in_active:                      155
% 7.88/1.50  sup_num_in_passive:                     713
% 7.88/1.50  sup_num_of_loops:                       190
% 7.88/1.50  sup_fw_superposition:                   625
% 7.88/1.50  sup_bw_superposition:                   647
% 7.88/1.50  sup_immediate_simplified:               183
% 7.88/1.50  sup_given_eliminated:                   4
% 7.88/1.50  comparisons_done:                       0
% 7.88/1.50  comparisons_avoided:                    74
% 7.88/1.50  
% 7.88/1.50  ------ Simplifications
% 7.88/1.50  
% 7.88/1.50  
% 7.88/1.50  sim_fw_subset_subsumed:                 55
% 7.88/1.50  sim_bw_subset_subsumed:                 127
% 7.88/1.50  sim_fw_subsumed:                        62
% 7.88/1.50  sim_bw_subsumed:                        6
% 7.88/1.50  sim_fw_subsumption_res:                 5
% 7.88/1.50  sim_bw_subsumption_res:                 0
% 7.88/1.50  sim_tautology_del:                      48
% 7.88/1.50  sim_eq_tautology_del:                   41
% 7.88/1.50  sim_eq_res_simp:                        2
% 7.88/1.50  sim_fw_demodulated:                     32
% 7.88/1.50  sim_bw_demodulated:                     4
% 7.88/1.50  sim_light_normalised:                   45
% 7.88/1.50  sim_joinable_taut:                      0
% 7.88/1.50  sim_joinable_simp:                      0
% 7.88/1.50  sim_ac_normalised:                      0
% 7.88/1.50  sim_smt_subsumption:                    0
% 7.88/1.50  
%------------------------------------------------------------------------------
