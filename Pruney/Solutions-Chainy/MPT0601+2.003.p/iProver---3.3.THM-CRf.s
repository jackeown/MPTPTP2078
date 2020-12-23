%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:48:19 EST 2020

% Result     : Theorem 7.72s
% Output     : CNFRefutation 7.72s
% Verified   : 
% Statistics : Number of formulae       :  151 (28364 expanded)
%              Number of clauses        :   91 (10446 expanded)
%              Number of leaves         :   17 (6445 expanded)
%              Depth                    :   40
%              Number of atoms          :  424 (91231 expanded)
%              Number of equality atoms :  200 (33006 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :   12 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f9,axiom,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( k1_xboole_0 = k9_relat_1(X1,X0)
          & r1_tarski(X0,k1_relat_1(X1))
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k9_relat_1(X1,X0)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k9_relat_1(X1,X0)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k9_relat_1(X1,X0)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r2_hidden(X0,k1_relat_1(X1))
        <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <~> k1_xboole_0 != k11_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f35,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k11_relat_1(X1,X0)
        | ~ r2_hidden(X0,k1_relat_1(X1)) )
      & ( k1_xboole_0 != k11_relat_1(X1,X0)
        | r2_hidden(X0,k1_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f36,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k11_relat_1(X1,X0)
        | ~ r2_hidden(X0,k1_relat_1(X1)) )
      & ( k1_xboole_0 != k11_relat_1(X1,X0)
        | r2_hidden(X0,k1_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f37,plain,
    ( ? [X0,X1] :
        ( ( k1_xboole_0 = k11_relat_1(X1,X0)
          | ~ r2_hidden(X0,k1_relat_1(X1)) )
        & ( k1_xboole_0 != k11_relat_1(X1,X0)
          | r2_hidden(X0,k1_relat_1(X1)) )
        & v1_relat_1(X1) )
   => ( ( k1_xboole_0 = k11_relat_1(sK5,sK4)
        | ~ r2_hidden(sK4,k1_relat_1(sK5)) )
      & ( k1_xboole_0 != k11_relat_1(sK5,sK4)
        | r2_hidden(sK4,k1_relat_1(sK5)) )
      & v1_relat_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ( k1_xboole_0 = k11_relat_1(sK5,sK4)
      | ~ r2_hidden(sK4,k1_relat_1(sK5)) )
    & ( k1_xboole_0 != k11_relat_1(sK5,sK4)
      | r2_hidden(sK4,k1_relat_1(sK5)) )
    & v1_relat_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f36,f37])).

fof(f62,plain,(
    v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f38])).

fof(f4,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f25])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f68,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f47])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f45,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | ~ r2_hidden(X1,k11_relat_1(X2,X0)) )
        & ( r2_hidden(X1,k11_relat_1(X2,X0))
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,k11_relat_1(X2,X0))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
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

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f32,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK2(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
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

fof(f33,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f29,f32,f31,f30])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
      | r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f53,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f71,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f53])).

fof(f54,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f70,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f64,plain,
    ( k1_xboole_0 = k11_relat_1(sK5,sK4)
    | ~ r2_hidden(sK4,k1_relat_1(sK5)) ),
    inference(cnf_transformation,[],[f38])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k11_relat_1(X2,X0))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f63,plain,
    ( k1_xboole_0 != k11_relat_1(sK5,sK4)
    | r2_hidden(sK4,k1_relat_1(sK5)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1041,plain,
    ( k3_xboole_0(X0,X1) = X2
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_11,plain,
    ( r1_tarski(k1_tarski(X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1034,plain,
    ( r1_tarski(k1_tarski(X0),X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_19,plain,
    ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_20,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k9_relat_1(X1,X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1027,plain,
    ( k9_relat_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3224,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_relat_1(k1_xboole_0)) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_19,c_1027])).

cnf(c_25,negated_conjecture,
    ( v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1022,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_10,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_18,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1028,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k3_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2041,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_10,c_1028])).

cnf(c_2045,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1022,c_2041])).

cnf(c_3275,plain,
    ( r1_tarski(X0,k1_relat_1(k1_xboole_0)) != iProver_top
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3224,c_2045])).

cnf(c_3276,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_relat_1(k1_xboole_0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3275])).

cnf(c_3280,plain,
    ( k1_tarski(X0) = k1_xboole_0
    | r2_hidden(X0,k1_relat_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1034,c_3276])).

cnf(c_8,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1035,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3279,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1035,c_3276])).

cnf(c_3301,plain,
    ( k1_tarski(X0) = k1_xboole_0
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3280,c_3279])).

cnf(c_6,plain,
    ( k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_13,plain,
    ( k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1717,plain,
    ( k1_tarski(X0) != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6,c_13])).

cnf(c_3548,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3301,c_1717])).

cnf(c_3556,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r2_hidden(sK0(X0,X1,k1_xboole_0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1041,c_3548])).

cnf(c_21,plain,
    ( ~ r2_hidden(X0,k11_relat_1(X1,X2))
    | r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1026,plain,
    ( r2_hidden(X0,k11_relat_1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3881,plain,
    ( k3_xboole_0(X0,k11_relat_1(X1,X2)) = k1_xboole_0
    | r2_hidden(k4_tarski(X2,sK0(X0,k11_relat_1(X1,X2),k1_xboole_0)),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3556,c_1026])).

cnf(c_15,plain,
    ( r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
    | r2_hidden(sK1(X0,X1),X1)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1031,plain,
    ( k1_relat_1(X0) = X1
    | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) = iProver_top
    | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,sK3(X1,X0)),X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1029,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK3(X1,X0)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2527,plain,
    ( r2_hidden(X0,k1_relat_1(k11_relat_1(X1,X2))) != iProver_top
    | r2_hidden(k4_tarski(X2,k4_tarski(X0,sK3(k11_relat_1(X1,X2),X0))),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1029,c_1026])).

cnf(c_4288,plain,
    ( r2_hidden(X0,k1_relat_1(k11_relat_1(k1_xboole_0,X1))) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2527,c_3548])).

cnf(c_4904,plain,
    ( r2_hidden(X0,k1_relat_1(k11_relat_1(k1_xboole_0,X1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4288,c_2045])).

cnf(c_4914,plain,
    ( k1_relat_1(k1_relat_1(k11_relat_1(k1_xboole_0,X0))) = X1
    | r2_hidden(sK1(k1_relat_1(k11_relat_1(k1_xboole_0,X0)),X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1031,c_4904])).

cnf(c_6993,plain,
    ( k1_relat_1(k1_relat_1(k11_relat_1(k1_xboole_0,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4914,c_3548])).

cnf(c_4915,plain,
    ( r2_hidden(X0,k1_relat_1(k1_relat_1(k11_relat_1(k1_xboole_0,X1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1029,c_4904])).

cnf(c_5070,plain,
    ( r2_hidden(X0,k1_relat_1(k1_relat_1(k1_relat_1(k11_relat_1(k1_xboole_0,X1))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1029,c_4915])).

cnf(c_5395,plain,
    ( r2_hidden(X0,k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k11_relat_1(k1_xboole_0,X1)))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1029,c_5070])).

cnf(c_5636,plain,
    ( r2_hidden(X0,k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k11_relat_1(k1_xboole_0,X1))))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1029,c_5395])).

cnf(c_5959,plain,
    ( r2_hidden(X0,k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k11_relat_1(k1_xboole_0,X1)))))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1029,c_5636])).

cnf(c_6001,plain,
    ( r2_hidden(X0,k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k11_relat_1(k1_xboole_0,X1))))))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1029,c_5959])).

cnf(c_7004,plain,
    ( k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k11_relat_1(k1_xboole_0,X0)))))))) = k1_relat_1(k1_relat_1(k11_relat_1(k1_xboole_0,X1))) ),
    inference(superposition,[status(thm)],[c_4914,c_6001])).

cnf(c_6062,plain,
    ( r2_hidden(X0,k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k11_relat_1(k1_xboole_0,X1)))))))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1029,c_6001])).

cnf(c_6787,plain,
    ( r2_hidden(X0,k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k11_relat_1(k1_xboole_0,X1))))))))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1029,c_6062])).

cnf(c_7006,plain,
    ( k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k11_relat_1(k1_xboole_0,X0)))))))))) = k1_relat_1(k1_relat_1(k11_relat_1(k1_xboole_0,X1))) ),
    inference(superposition,[status(thm)],[c_4914,c_6787])).

cnf(c_7007,plain,
    ( k1_relat_1(k1_relat_1(k11_relat_1(k1_xboole_0,X0))) = sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_7006])).

cnf(c_7189,plain,
    ( k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(sP0_iProver_split))))) = k1_relat_1(k1_relat_1(k11_relat_1(k1_xboole_0,X0))) ),
    inference(light_normalisation,[status(thm)],[c_7004,c_7007])).

cnf(c_7190,plain,
    ( k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(sP0_iProver_split))))) = sP0_iProver_split ),
    inference(demodulation,[status(thm)],[c_7189,c_7007])).

cnf(c_7005,plain,
    ( k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k11_relat_1(k1_xboole_0,X0))))))))) = k1_relat_1(k1_relat_1(k11_relat_1(k1_xboole_0,X1))) ),
    inference(superposition,[status(thm)],[c_4914,c_6062])).

cnf(c_7186,plain,
    ( k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(sP0_iProver_split)))))) = k1_relat_1(k1_relat_1(k11_relat_1(k1_xboole_0,X0))) ),
    inference(light_normalisation,[status(thm)],[c_7005,c_7007])).

cnf(c_7187,plain,
    ( k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(sP0_iProver_split)))))) = sP0_iProver_split ),
    inference(demodulation,[status(thm)],[c_7186,c_7007])).

cnf(c_7191,plain,
    ( k1_relat_1(sP0_iProver_split) = sP0_iProver_split ),
    inference(demodulation,[status(thm)],[c_7190,c_7187])).

cnf(c_6998,plain,
    ( k1_relat_1(k1_relat_1(k11_relat_1(k1_xboole_0,X0))) = k1_relat_1(k11_relat_1(k1_xboole_0,X1)) ),
    inference(superposition,[status(thm)],[c_4914,c_4904])).

cnf(c_7239,plain,
    ( k1_relat_1(k11_relat_1(k1_xboole_0,X0)) = sP0_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_6998,c_7007])).

cnf(c_7243,plain,
    ( sP0_iProver_split = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6993,c_7191,c_7239])).

cnf(c_19252,plain,
    ( k3_xboole_0(X0,k11_relat_1(X1,X2)) = sP0_iProver_split
    | r2_hidden(k4_tarski(X2,sK0(X0,k11_relat_1(X1,X2),sP0_iProver_split)),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3881,c_7243])).

cnf(c_16,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1030,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_19259,plain,
    ( k3_xboole_0(X0,k11_relat_1(X1,X2)) = sP0_iProver_split
    | r2_hidden(X2,k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_19252,c_1030])).

cnf(c_23,negated_conjecture,
    ( ~ r2_hidden(sK4,k1_relat_1(sK5))
    | k1_xboole_0 = k11_relat_1(sK5,sK4) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1024,plain,
    ( k1_xboole_0 = k11_relat_1(sK5,sK4)
    | r2_hidden(sK4,k1_relat_1(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_7305,plain,
    ( k11_relat_1(sK5,sK4) = sP0_iProver_split
    | r2_hidden(sK4,k1_relat_1(sK5)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7243,c_1024])).

cnf(c_19479,plain,
    ( k11_relat_1(sK5,sK4) = sP0_iProver_split
    | k3_xboole_0(X0,k11_relat_1(sK5,sK4)) = sP0_iProver_split
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_19259,c_7305])).

cnf(c_19531,plain,
    ( ~ v1_relat_1(sK5)
    | k11_relat_1(sK5,sK4) = sP0_iProver_split
    | k3_xboole_0(X0,k11_relat_1(sK5,sK4)) = sP0_iProver_split ),
    inference(predicate_to_equality_rev,[status(thm)],[c_19479])).

cnf(c_19591,plain,
    ( k3_xboole_0(X0,k11_relat_1(sK5,sK4)) = sP0_iProver_split
    | k11_relat_1(sK5,sK4) = sP0_iProver_split ),
    inference(global_propositional_subsumption,[status(thm)],[c_19479,c_25,c_19531])).

cnf(c_19592,plain,
    ( k11_relat_1(sK5,sK4) = sP0_iProver_split
    | k3_xboole_0(X0,k11_relat_1(sK5,sK4)) = sP0_iProver_split ),
    inference(renaming,[status(thm)],[c_19591])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1040,plain,
    ( k3_xboole_0(X0,X1) = X2
    | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2782,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r2_hidden(sK0(X0,X1,X0),X0) = iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_1040])).

cnf(c_2784,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r2_hidden(sK0(X0,X1,X0),X0) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2782])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | ~ r2_hidden(sK0(X0,X1,X2),X0)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1042,plain,
    ( k3_xboole_0(X0,X1) = X2
    | r2_hidden(sK0(X0,X1,X2),X0) != iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) != iProver_top
    | r2_hidden(sK0(X0,X1,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_16847,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r2_hidden(sK0(X0,X1,X0),X0) != iProver_top
    | r2_hidden(sK0(X0,X1,X0),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2784,c_1042])).

cnf(c_17629,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r2_hidden(sK0(X0,X1,X0),X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16847,c_2784])).

cnf(c_17649,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_2784,c_17629])).

cnf(c_19653,plain,
    ( k11_relat_1(sK5,sK4) = sP0_iProver_split ),
    inference(superposition,[status(thm)],[c_19592,c_17649])).

cnf(c_22,plain,
    ( r2_hidden(X0,k11_relat_1(X1,X2))
    | ~ r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1025,plain,
    ( r2_hidden(X0,k11_relat_1(X1,X2)) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2528,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(sK3(X1,X0),k11_relat_1(X1,X0)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1029,c_1025])).

cnf(c_19960,plain,
    ( r2_hidden(sK3(sK5,sK4),sP0_iProver_split) = iProver_top
    | r2_hidden(sK4,k1_relat_1(sK5)) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_19653,c_2528])).

cnf(c_26,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_24,negated_conjecture,
    ( r2_hidden(sK4,k1_relat_1(sK5))
    | k1_xboole_0 != k11_relat_1(sK5,sK4) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1023,plain,
    ( k1_xboole_0 != k11_relat_1(sK5,sK4)
    | r2_hidden(sK4,k1_relat_1(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_7306,plain,
    ( k11_relat_1(sK5,sK4) != sP0_iProver_split
    | r2_hidden(sK4,k1_relat_1(sK5)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7243,c_1023])).

cnf(c_20044,plain,
    ( r2_hidden(sK3(sK5,sK4),sP0_iProver_split) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_19960,c_26,c_7306,c_19653])).

cnf(c_7168,plain,
    ( r2_hidden(X0,sP0_iProver_split) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7007,c_4915])).

cnf(c_20048,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_20044,c_7168])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:36:46 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.72/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.72/1.49  
% 7.72/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.72/1.49  
% 7.72/1.49  ------  iProver source info
% 7.72/1.49  
% 7.72/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.72/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.72/1.49  git: non_committed_changes: false
% 7.72/1.49  git: last_make_outside_of_git: false
% 7.72/1.49  
% 7.72/1.49  ------ 
% 7.72/1.49  
% 7.72/1.49  ------ Input Options
% 7.72/1.49  
% 7.72/1.49  --out_options                           all
% 7.72/1.49  --tptp_safe_out                         true
% 7.72/1.49  --problem_path                          ""
% 7.72/1.49  --include_path                          ""
% 7.72/1.49  --clausifier                            res/vclausify_rel
% 7.72/1.49  --clausifier_options                    ""
% 7.72/1.49  --stdin                                 false
% 7.72/1.49  --stats_out                             all
% 7.72/1.49  
% 7.72/1.49  ------ General Options
% 7.72/1.49  
% 7.72/1.49  --fof                                   false
% 7.72/1.49  --time_out_real                         305.
% 7.72/1.49  --time_out_virtual                      -1.
% 7.72/1.49  --symbol_type_check                     false
% 7.72/1.49  --clausify_out                          false
% 7.72/1.49  --sig_cnt_out                           false
% 7.72/1.49  --trig_cnt_out                          false
% 7.72/1.49  --trig_cnt_out_tolerance                1.
% 7.72/1.49  --trig_cnt_out_sk_spl                   false
% 7.72/1.49  --abstr_cl_out                          false
% 7.72/1.49  
% 7.72/1.49  ------ Global Options
% 7.72/1.49  
% 7.72/1.49  --schedule                              default
% 7.72/1.49  --add_important_lit                     false
% 7.72/1.49  --prop_solver_per_cl                    1000
% 7.72/1.49  --min_unsat_core                        false
% 7.72/1.49  --soft_assumptions                      false
% 7.72/1.49  --soft_lemma_size                       3
% 7.72/1.49  --prop_impl_unit_size                   0
% 7.72/1.49  --prop_impl_unit                        []
% 7.72/1.49  --share_sel_clauses                     true
% 7.72/1.49  --reset_solvers                         false
% 7.72/1.49  --bc_imp_inh                            [conj_cone]
% 7.72/1.49  --conj_cone_tolerance                   3.
% 7.72/1.49  --extra_neg_conj                        none
% 7.72/1.49  --large_theory_mode                     true
% 7.72/1.49  --prolific_symb_bound                   200
% 7.72/1.49  --lt_threshold                          2000
% 7.72/1.49  --clause_weak_htbl                      true
% 7.72/1.49  --gc_record_bc_elim                     false
% 7.72/1.49  
% 7.72/1.49  ------ Preprocessing Options
% 7.72/1.49  
% 7.72/1.49  --preprocessing_flag                    true
% 7.72/1.49  --time_out_prep_mult                    0.1
% 7.72/1.49  --splitting_mode                        input
% 7.72/1.49  --splitting_grd                         true
% 7.72/1.49  --splitting_cvd                         false
% 7.72/1.49  --splitting_cvd_svl                     false
% 7.72/1.49  --splitting_nvd                         32
% 7.72/1.49  --sub_typing                            true
% 7.72/1.49  --prep_gs_sim                           true
% 7.72/1.49  --prep_unflatten                        true
% 7.72/1.49  --prep_res_sim                          true
% 7.72/1.49  --prep_upred                            true
% 7.72/1.49  --prep_sem_filter                       exhaustive
% 7.72/1.49  --prep_sem_filter_out                   false
% 7.72/1.49  --pred_elim                             true
% 7.72/1.49  --res_sim_input                         true
% 7.72/1.49  --eq_ax_congr_red                       true
% 7.72/1.49  --pure_diseq_elim                       true
% 7.72/1.49  --brand_transform                       false
% 7.72/1.49  --non_eq_to_eq                          false
% 7.72/1.49  --prep_def_merge                        true
% 7.72/1.49  --prep_def_merge_prop_impl              false
% 7.72/1.49  --prep_def_merge_mbd                    true
% 7.72/1.49  --prep_def_merge_tr_red                 false
% 7.72/1.49  --prep_def_merge_tr_cl                  false
% 7.72/1.49  --smt_preprocessing                     true
% 7.72/1.49  --smt_ac_axioms                         fast
% 7.72/1.49  --preprocessed_out                      false
% 7.72/1.49  --preprocessed_stats                    false
% 7.72/1.49  
% 7.72/1.49  ------ Abstraction refinement Options
% 7.72/1.49  
% 7.72/1.49  --abstr_ref                             []
% 7.72/1.49  --abstr_ref_prep                        false
% 7.72/1.49  --abstr_ref_until_sat                   false
% 7.72/1.49  --abstr_ref_sig_restrict                funpre
% 7.72/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.72/1.49  --abstr_ref_under                       []
% 7.72/1.49  
% 7.72/1.49  ------ SAT Options
% 7.72/1.49  
% 7.72/1.49  --sat_mode                              false
% 7.72/1.49  --sat_fm_restart_options                ""
% 7.72/1.49  --sat_gr_def                            false
% 7.72/1.49  --sat_epr_types                         true
% 7.72/1.49  --sat_non_cyclic_types                  false
% 7.72/1.49  --sat_finite_models                     false
% 7.72/1.49  --sat_fm_lemmas                         false
% 7.72/1.49  --sat_fm_prep                           false
% 7.72/1.49  --sat_fm_uc_incr                        true
% 7.72/1.49  --sat_out_model                         small
% 7.72/1.49  --sat_out_clauses                       false
% 7.72/1.49  
% 7.72/1.49  ------ QBF Options
% 7.72/1.49  
% 7.72/1.49  --qbf_mode                              false
% 7.72/1.49  --qbf_elim_univ                         false
% 7.72/1.49  --qbf_dom_inst                          none
% 7.72/1.49  --qbf_dom_pre_inst                      false
% 7.72/1.49  --qbf_sk_in                             false
% 7.72/1.49  --qbf_pred_elim                         true
% 7.72/1.49  --qbf_split                             512
% 7.72/1.49  
% 7.72/1.49  ------ BMC1 Options
% 7.72/1.49  
% 7.72/1.49  --bmc1_incremental                      false
% 7.72/1.49  --bmc1_axioms                           reachable_all
% 7.72/1.49  --bmc1_min_bound                        0
% 7.72/1.49  --bmc1_max_bound                        -1
% 7.72/1.49  --bmc1_max_bound_default                -1
% 7.72/1.49  --bmc1_symbol_reachability              true
% 7.72/1.49  --bmc1_property_lemmas                  false
% 7.72/1.49  --bmc1_k_induction                      false
% 7.72/1.49  --bmc1_non_equiv_states                 false
% 7.72/1.49  --bmc1_deadlock                         false
% 7.72/1.49  --bmc1_ucm                              false
% 7.72/1.49  --bmc1_add_unsat_core                   none
% 7.72/1.49  --bmc1_unsat_core_children              false
% 7.72/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.72/1.49  --bmc1_out_stat                         full
% 7.72/1.49  --bmc1_ground_init                      false
% 7.72/1.49  --bmc1_pre_inst_next_state              false
% 7.72/1.49  --bmc1_pre_inst_state                   false
% 7.72/1.49  --bmc1_pre_inst_reach_state             false
% 7.72/1.49  --bmc1_out_unsat_core                   false
% 7.72/1.49  --bmc1_aig_witness_out                  false
% 7.72/1.49  --bmc1_verbose                          false
% 7.72/1.49  --bmc1_dump_clauses_tptp                false
% 7.72/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.72/1.49  --bmc1_dump_file                        -
% 7.72/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.72/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.72/1.49  --bmc1_ucm_extend_mode                  1
% 7.72/1.49  --bmc1_ucm_init_mode                    2
% 7.72/1.49  --bmc1_ucm_cone_mode                    none
% 7.72/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.72/1.49  --bmc1_ucm_relax_model                  4
% 7.72/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.72/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.72/1.49  --bmc1_ucm_layered_model                none
% 7.72/1.49  --bmc1_ucm_max_lemma_size               10
% 7.72/1.49  
% 7.72/1.49  ------ AIG Options
% 7.72/1.49  
% 7.72/1.49  --aig_mode                              false
% 7.72/1.49  
% 7.72/1.49  ------ Instantiation Options
% 7.72/1.49  
% 7.72/1.49  --instantiation_flag                    true
% 7.72/1.49  --inst_sos_flag                         true
% 7.72/1.49  --inst_sos_phase                        true
% 7.72/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.72/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.72/1.49  --inst_lit_sel_side                     num_symb
% 7.72/1.49  --inst_solver_per_active                1400
% 7.72/1.49  --inst_solver_calls_frac                1.
% 7.72/1.49  --inst_passive_queue_type               priority_queues
% 7.72/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.72/1.49  --inst_passive_queues_freq              [25;2]
% 7.72/1.49  --inst_dismatching                      true
% 7.72/1.49  --inst_eager_unprocessed_to_passive     true
% 7.72/1.49  --inst_prop_sim_given                   true
% 7.72/1.49  --inst_prop_sim_new                     false
% 7.72/1.49  --inst_subs_new                         false
% 7.72/1.49  --inst_eq_res_simp                      false
% 7.72/1.49  --inst_subs_given                       false
% 7.72/1.49  --inst_orphan_elimination               true
% 7.72/1.49  --inst_learning_loop_flag               true
% 7.72/1.49  --inst_learning_start                   3000
% 7.72/1.49  --inst_learning_factor                  2
% 7.72/1.49  --inst_start_prop_sim_after_learn       3
% 7.72/1.49  --inst_sel_renew                        solver
% 7.72/1.49  --inst_lit_activity_flag                true
% 7.72/1.49  --inst_restr_to_given                   false
% 7.72/1.49  --inst_activity_threshold               500
% 7.72/1.49  --inst_out_proof                        true
% 7.72/1.49  
% 7.72/1.49  ------ Resolution Options
% 7.72/1.49  
% 7.72/1.49  --resolution_flag                       true
% 7.72/1.49  --res_lit_sel                           adaptive
% 7.72/1.49  --res_lit_sel_side                      none
% 7.72/1.49  --res_ordering                          kbo
% 7.72/1.49  --res_to_prop_solver                    active
% 7.72/1.49  --res_prop_simpl_new                    false
% 7.72/1.49  --res_prop_simpl_given                  true
% 7.72/1.49  --res_passive_queue_type                priority_queues
% 7.72/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.72/1.49  --res_passive_queues_freq               [15;5]
% 7.72/1.49  --res_forward_subs                      full
% 7.72/1.49  --res_backward_subs                     full
% 7.72/1.49  --res_forward_subs_resolution           true
% 7.72/1.49  --res_backward_subs_resolution          true
% 7.72/1.49  --res_orphan_elimination                true
% 7.72/1.49  --res_time_limit                        2.
% 7.72/1.49  --res_out_proof                         true
% 7.72/1.49  
% 7.72/1.49  ------ Superposition Options
% 7.72/1.49  
% 7.72/1.49  --superposition_flag                    true
% 7.72/1.49  --sup_passive_queue_type                priority_queues
% 7.72/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.72/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.72/1.49  --demod_completeness_check              fast
% 7.72/1.49  --demod_use_ground                      true
% 7.72/1.49  --sup_to_prop_solver                    passive
% 7.72/1.49  --sup_prop_simpl_new                    true
% 7.72/1.49  --sup_prop_simpl_given                  true
% 7.72/1.49  --sup_fun_splitting                     true
% 7.72/1.49  --sup_smt_interval                      50000
% 7.72/1.49  
% 7.72/1.49  ------ Superposition Simplification Setup
% 7.72/1.49  
% 7.72/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.72/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.72/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.72/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.72/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.72/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.72/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.72/1.49  --sup_immed_triv                        [TrivRules]
% 7.72/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.72/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.72/1.49  --sup_immed_bw_main                     []
% 7.72/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.72/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.72/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.72/1.49  --sup_input_bw                          []
% 7.72/1.49  
% 7.72/1.49  ------ Combination Options
% 7.72/1.49  
% 7.72/1.49  --comb_res_mult                         3
% 7.72/1.49  --comb_sup_mult                         2
% 7.72/1.49  --comb_inst_mult                        10
% 7.72/1.49  
% 7.72/1.49  ------ Debug Options
% 7.72/1.49  
% 7.72/1.49  --dbg_backtrace                         false
% 7.72/1.49  --dbg_dump_prop_clauses                 false
% 7.72/1.49  --dbg_dump_prop_clauses_file            -
% 7.72/1.49  --dbg_out_stat                          false
% 7.72/1.49  ------ Parsing...
% 7.72/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.72/1.49  
% 7.72/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.72/1.49  
% 7.72/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.72/1.49  
% 7.72/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.72/1.49  ------ Proving...
% 7.72/1.49  ------ Problem Properties 
% 7.72/1.49  
% 7.72/1.49  
% 7.72/1.49  clauses                                 25
% 7.72/1.49  conjectures                             3
% 7.72/1.49  EPR                                     3
% 7.72/1.49  Horn                                    22
% 7.72/1.49  unary                                   6
% 7.72/1.49  binary                                  9
% 7.72/1.49  lits                                    56
% 7.72/1.49  lits eq                                 14
% 7.72/1.49  fd_pure                                 0
% 7.72/1.49  fd_pseudo                               0
% 7.72/1.49  fd_cond                                 1
% 7.72/1.49  fd_pseudo_cond                          6
% 7.72/1.49  AC symbols                              0
% 7.72/1.49  
% 7.72/1.49  ------ Schedule dynamic 5 is on 
% 7.72/1.49  
% 7.72/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.72/1.49  
% 7.72/1.49  
% 7.72/1.49  ------ 
% 7.72/1.49  Current options:
% 7.72/1.49  ------ 
% 7.72/1.49  
% 7.72/1.49  ------ Input Options
% 7.72/1.49  
% 7.72/1.49  --out_options                           all
% 7.72/1.49  --tptp_safe_out                         true
% 7.72/1.49  --problem_path                          ""
% 7.72/1.49  --include_path                          ""
% 7.72/1.49  --clausifier                            res/vclausify_rel
% 7.72/1.49  --clausifier_options                    ""
% 7.72/1.49  --stdin                                 false
% 7.72/1.49  --stats_out                             all
% 7.72/1.49  
% 7.72/1.49  ------ General Options
% 7.72/1.49  
% 7.72/1.49  --fof                                   false
% 7.72/1.49  --time_out_real                         305.
% 7.72/1.49  --time_out_virtual                      -1.
% 7.72/1.49  --symbol_type_check                     false
% 7.72/1.49  --clausify_out                          false
% 7.72/1.49  --sig_cnt_out                           false
% 7.72/1.49  --trig_cnt_out                          false
% 7.72/1.49  --trig_cnt_out_tolerance                1.
% 7.72/1.49  --trig_cnt_out_sk_spl                   false
% 7.72/1.49  --abstr_cl_out                          false
% 7.72/1.49  
% 7.72/1.49  ------ Global Options
% 7.72/1.49  
% 7.72/1.49  --schedule                              default
% 7.72/1.49  --add_important_lit                     false
% 7.72/1.49  --prop_solver_per_cl                    1000
% 7.72/1.49  --min_unsat_core                        false
% 7.72/1.49  --soft_assumptions                      false
% 7.72/1.49  --soft_lemma_size                       3
% 7.72/1.49  --prop_impl_unit_size                   0
% 7.72/1.49  --prop_impl_unit                        []
% 7.72/1.49  --share_sel_clauses                     true
% 7.72/1.49  --reset_solvers                         false
% 7.72/1.49  --bc_imp_inh                            [conj_cone]
% 7.72/1.49  --conj_cone_tolerance                   3.
% 7.72/1.49  --extra_neg_conj                        none
% 7.72/1.49  --large_theory_mode                     true
% 7.72/1.49  --prolific_symb_bound                   200
% 7.72/1.49  --lt_threshold                          2000
% 7.72/1.49  --clause_weak_htbl                      true
% 7.72/1.49  --gc_record_bc_elim                     false
% 7.72/1.49  
% 7.72/1.49  ------ Preprocessing Options
% 7.72/1.49  
% 7.72/1.49  --preprocessing_flag                    true
% 7.72/1.49  --time_out_prep_mult                    0.1
% 7.72/1.49  --splitting_mode                        input
% 7.72/1.49  --splitting_grd                         true
% 7.72/1.49  --splitting_cvd                         false
% 7.72/1.49  --splitting_cvd_svl                     false
% 7.72/1.49  --splitting_nvd                         32
% 7.72/1.49  --sub_typing                            true
% 7.72/1.49  --prep_gs_sim                           true
% 7.72/1.49  --prep_unflatten                        true
% 7.72/1.49  --prep_res_sim                          true
% 7.72/1.49  --prep_upred                            true
% 7.72/1.49  --prep_sem_filter                       exhaustive
% 7.72/1.49  --prep_sem_filter_out                   false
% 7.72/1.49  --pred_elim                             true
% 7.72/1.49  --res_sim_input                         true
% 7.72/1.49  --eq_ax_congr_red                       true
% 7.72/1.49  --pure_diseq_elim                       true
% 7.72/1.49  --brand_transform                       false
% 7.72/1.49  --non_eq_to_eq                          false
% 7.72/1.49  --prep_def_merge                        true
% 7.72/1.49  --prep_def_merge_prop_impl              false
% 7.72/1.49  --prep_def_merge_mbd                    true
% 7.72/1.49  --prep_def_merge_tr_red                 false
% 7.72/1.49  --prep_def_merge_tr_cl                  false
% 7.72/1.49  --smt_preprocessing                     true
% 7.72/1.49  --smt_ac_axioms                         fast
% 7.72/1.49  --preprocessed_out                      false
% 7.72/1.49  --preprocessed_stats                    false
% 7.72/1.49  
% 7.72/1.49  ------ Abstraction refinement Options
% 7.72/1.49  
% 7.72/1.49  --abstr_ref                             []
% 7.72/1.49  --abstr_ref_prep                        false
% 7.72/1.49  --abstr_ref_until_sat                   false
% 7.72/1.49  --abstr_ref_sig_restrict                funpre
% 7.72/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.72/1.49  --abstr_ref_under                       []
% 7.72/1.49  
% 7.72/1.49  ------ SAT Options
% 7.72/1.49  
% 7.72/1.49  --sat_mode                              false
% 7.72/1.49  --sat_fm_restart_options                ""
% 7.72/1.49  --sat_gr_def                            false
% 7.72/1.49  --sat_epr_types                         true
% 7.72/1.49  --sat_non_cyclic_types                  false
% 7.72/1.49  --sat_finite_models                     false
% 7.72/1.49  --sat_fm_lemmas                         false
% 7.72/1.49  --sat_fm_prep                           false
% 7.72/1.49  --sat_fm_uc_incr                        true
% 7.72/1.49  --sat_out_model                         small
% 7.72/1.49  --sat_out_clauses                       false
% 7.72/1.49  
% 7.72/1.49  ------ QBF Options
% 7.72/1.49  
% 7.72/1.49  --qbf_mode                              false
% 7.72/1.49  --qbf_elim_univ                         false
% 7.72/1.49  --qbf_dom_inst                          none
% 7.72/1.49  --qbf_dom_pre_inst                      false
% 7.72/1.49  --qbf_sk_in                             false
% 7.72/1.49  --qbf_pred_elim                         true
% 7.72/1.49  --qbf_split                             512
% 7.72/1.49  
% 7.72/1.49  ------ BMC1 Options
% 7.72/1.49  
% 7.72/1.49  --bmc1_incremental                      false
% 7.72/1.49  --bmc1_axioms                           reachable_all
% 7.72/1.49  --bmc1_min_bound                        0
% 7.72/1.49  --bmc1_max_bound                        -1
% 7.72/1.49  --bmc1_max_bound_default                -1
% 7.72/1.49  --bmc1_symbol_reachability              true
% 7.72/1.49  --bmc1_property_lemmas                  false
% 7.72/1.49  --bmc1_k_induction                      false
% 7.72/1.49  --bmc1_non_equiv_states                 false
% 7.72/1.49  --bmc1_deadlock                         false
% 7.72/1.49  --bmc1_ucm                              false
% 7.72/1.49  --bmc1_add_unsat_core                   none
% 7.72/1.49  --bmc1_unsat_core_children              false
% 7.72/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.72/1.49  --bmc1_out_stat                         full
% 7.72/1.49  --bmc1_ground_init                      false
% 7.72/1.49  --bmc1_pre_inst_next_state              false
% 7.72/1.49  --bmc1_pre_inst_state                   false
% 7.72/1.49  --bmc1_pre_inst_reach_state             false
% 7.72/1.49  --bmc1_out_unsat_core                   false
% 7.72/1.49  --bmc1_aig_witness_out                  false
% 7.72/1.49  --bmc1_verbose                          false
% 7.72/1.49  --bmc1_dump_clauses_tptp                false
% 7.72/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.72/1.49  --bmc1_dump_file                        -
% 7.72/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.72/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.72/1.49  --bmc1_ucm_extend_mode                  1
% 7.72/1.49  --bmc1_ucm_init_mode                    2
% 7.72/1.49  --bmc1_ucm_cone_mode                    none
% 7.72/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.72/1.49  --bmc1_ucm_relax_model                  4
% 7.72/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.72/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.72/1.49  --bmc1_ucm_layered_model                none
% 7.72/1.49  --bmc1_ucm_max_lemma_size               10
% 7.72/1.49  
% 7.72/1.49  ------ AIG Options
% 7.72/1.49  
% 7.72/1.49  --aig_mode                              false
% 7.72/1.49  
% 7.72/1.49  ------ Instantiation Options
% 7.72/1.49  
% 7.72/1.49  --instantiation_flag                    true
% 7.72/1.49  --inst_sos_flag                         true
% 7.72/1.49  --inst_sos_phase                        true
% 7.72/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.72/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.72/1.49  --inst_lit_sel_side                     none
% 7.72/1.49  --inst_solver_per_active                1400
% 7.72/1.49  --inst_solver_calls_frac                1.
% 7.72/1.49  --inst_passive_queue_type               priority_queues
% 7.72/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.72/1.49  --inst_passive_queues_freq              [25;2]
% 7.72/1.49  --inst_dismatching                      true
% 7.72/1.49  --inst_eager_unprocessed_to_passive     true
% 7.72/1.49  --inst_prop_sim_given                   true
% 7.72/1.49  --inst_prop_sim_new                     false
% 7.72/1.49  --inst_subs_new                         false
% 7.72/1.49  --inst_eq_res_simp                      false
% 7.72/1.49  --inst_subs_given                       false
% 7.72/1.49  --inst_orphan_elimination               true
% 7.72/1.49  --inst_learning_loop_flag               true
% 7.72/1.49  --inst_learning_start                   3000
% 7.72/1.49  --inst_learning_factor                  2
% 7.72/1.49  --inst_start_prop_sim_after_learn       3
% 7.72/1.49  --inst_sel_renew                        solver
% 7.72/1.49  --inst_lit_activity_flag                true
% 7.72/1.49  --inst_restr_to_given                   false
% 7.72/1.49  --inst_activity_threshold               500
% 7.72/1.49  --inst_out_proof                        true
% 7.72/1.49  
% 7.72/1.49  ------ Resolution Options
% 7.72/1.49  
% 7.72/1.49  --resolution_flag                       false
% 7.72/1.49  --res_lit_sel                           adaptive
% 7.72/1.49  --res_lit_sel_side                      none
% 7.72/1.49  --res_ordering                          kbo
% 7.72/1.49  --res_to_prop_solver                    active
% 7.72/1.49  --res_prop_simpl_new                    false
% 7.72/1.49  --res_prop_simpl_given                  true
% 7.72/1.49  --res_passive_queue_type                priority_queues
% 7.72/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.72/1.49  --res_passive_queues_freq               [15;5]
% 7.72/1.49  --res_forward_subs                      full
% 7.72/1.49  --res_backward_subs                     full
% 7.72/1.49  --res_forward_subs_resolution           true
% 7.72/1.49  --res_backward_subs_resolution          true
% 7.72/1.49  --res_orphan_elimination                true
% 7.72/1.49  --res_time_limit                        2.
% 7.72/1.49  --res_out_proof                         true
% 7.72/1.49  
% 7.72/1.49  ------ Superposition Options
% 7.72/1.49  
% 7.72/1.49  --superposition_flag                    true
% 7.72/1.49  --sup_passive_queue_type                priority_queues
% 7.72/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.72/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.72/1.49  --demod_completeness_check              fast
% 7.72/1.49  --demod_use_ground                      true
% 7.72/1.49  --sup_to_prop_solver                    passive
% 7.72/1.49  --sup_prop_simpl_new                    true
% 7.72/1.49  --sup_prop_simpl_given                  true
% 7.72/1.49  --sup_fun_splitting                     true
% 7.72/1.49  --sup_smt_interval                      50000
% 7.72/1.49  
% 7.72/1.49  ------ Superposition Simplification Setup
% 7.72/1.49  
% 7.72/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.72/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.72/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.72/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.72/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.72/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.72/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.72/1.49  --sup_immed_triv                        [TrivRules]
% 7.72/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.72/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.72/1.49  --sup_immed_bw_main                     []
% 7.72/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.72/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.72/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.72/1.49  --sup_input_bw                          []
% 7.72/1.49  
% 7.72/1.49  ------ Combination Options
% 7.72/1.49  
% 7.72/1.49  --comb_res_mult                         3
% 7.72/1.49  --comb_sup_mult                         2
% 7.72/1.49  --comb_inst_mult                        10
% 7.72/1.49  
% 7.72/1.49  ------ Debug Options
% 7.72/1.49  
% 7.72/1.49  --dbg_backtrace                         false
% 7.72/1.49  --dbg_dump_prop_clauses                 false
% 7.72/1.49  --dbg_dump_prop_clauses_file            -
% 7.72/1.49  --dbg_out_stat                          false
% 7.72/1.49  
% 7.72/1.49  
% 7.72/1.49  
% 7.72/1.49  
% 7.72/1.49  ------ Proving...
% 7.72/1.49  
% 7.72/1.49  
% 7.72/1.49  % SZS status Theorem for theBenchmark.p
% 7.72/1.49  
% 7.72/1.49   Resolution empty clause
% 7.72/1.49  
% 7.72/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.72/1.49  
% 7.72/1.49  fof(f1,axiom,(
% 7.72/1.49    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 7.72/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.72/1.49  
% 7.72/1.49  fof(f20,plain,(
% 7.72/1.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 7.72/1.49    inference(nnf_transformation,[],[f1])).
% 7.72/1.49  
% 7.72/1.49  fof(f21,plain,(
% 7.72/1.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 7.72/1.49    inference(flattening,[],[f20])).
% 7.72/1.49  
% 7.72/1.49  fof(f22,plain,(
% 7.72/1.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 7.72/1.49    inference(rectify,[],[f21])).
% 7.72/1.49  
% 7.72/1.49  fof(f23,plain,(
% 7.72/1.49    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 7.72/1.49    introduced(choice_axiom,[])).
% 7.72/1.49  
% 7.72/1.49  fof(f24,plain,(
% 7.72/1.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 7.72/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).
% 7.72/1.49  
% 7.72/1.49  fof(f43,plain,(
% 7.72/1.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 7.72/1.49    inference(cnf_transformation,[],[f24])).
% 7.72/1.49  
% 7.72/1.49  fof(f5,axiom,(
% 7.72/1.49    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 7.72/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.72/1.49  
% 7.72/1.49  fof(f27,plain,(
% 7.72/1.49    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 7.72/1.49    inference(nnf_transformation,[],[f5])).
% 7.72/1.49  
% 7.72/1.49  fof(f51,plain,(
% 7.72/1.49    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 7.72/1.49    inference(cnf_transformation,[],[f27])).
% 7.72/1.49  
% 7.72/1.49  fof(f9,axiom,(
% 7.72/1.49    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 7.72/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.72/1.49  
% 7.72/1.49  fof(f58,plain,(
% 7.72/1.49    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) )),
% 7.72/1.49    inference(cnf_transformation,[],[f9])).
% 7.72/1.49  
% 7.72/1.49  fof(f10,axiom,(
% 7.72/1.49    ! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k9_relat_1(X1,X0) & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0))),
% 7.72/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.72/1.49  
% 7.72/1.49  fof(f16,plain,(
% 7.72/1.49    ! [X0,X1] : ((k1_xboole_0 != k9_relat_1(X1,X0) | ~r1_tarski(X0,k1_relat_1(X1)) | k1_xboole_0 = X0) | ~v1_relat_1(X1))),
% 7.72/1.49    inference(ennf_transformation,[],[f10])).
% 7.72/1.49  
% 7.72/1.49  fof(f17,plain,(
% 7.72/1.49    ! [X0,X1] : (k1_xboole_0 != k9_relat_1(X1,X0) | ~r1_tarski(X0,k1_relat_1(X1)) | k1_xboole_0 = X0 | ~v1_relat_1(X1))),
% 7.72/1.49    inference(flattening,[],[f16])).
% 7.72/1.49  
% 7.72/1.49  fof(f59,plain,(
% 7.72/1.49    ( ! [X0,X1] : (k1_xboole_0 != k9_relat_1(X1,X0) | ~r1_tarski(X0,k1_relat_1(X1)) | k1_xboole_0 = X0 | ~v1_relat_1(X1)) )),
% 7.72/1.49    inference(cnf_transformation,[],[f17])).
% 7.72/1.49  
% 7.72/1.49  fof(f12,conjecture,(
% 7.72/1.49    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 7.72/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.72/1.49  
% 7.72/1.49  fof(f13,negated_conjecture,(
% 7.72/1.49    ~! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 7.72/1.49    inference(negated_conjecture,[],[f12])).
% 7.72/1.49  
% 7.72/1.49  fof(f19,plain,(
% 7.72/1.49    ? [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <~> k1_xboole_0 != k11_relat_1(X1,X0)) & v1_relat_1(X1))),
% 7.72/1.49    inference(ennf_transformation,[],[f13])).
% 7.72/1.49  
% 7.72/1.49  fof(f35,plain,(
% 7.72/1.49    ? [X0,X1] : (((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1)))) & v1_relat_1(X1))),
% 7.72/1.49    inference(nnf_transformation,[],[f19])).
% 7.72/1.49  
% 7.72/1.49  fof(f36,plain,(
% 7.72/1.49    ? [X0,X1] : ((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 7.72/1.49    inference(flattening,[],[f35])).
% 7.72/1.49  
% 7.72/1.49  fof(f37,plain,(
% 7.72/1.49    ? [X0,X1] : ((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1))) & v1_relat_1(X1)) => ((k1_xboole_0 = k11_relat_1(sK5,sK4) | ~r2_hidden(sK4,k1_relat_1(sK5))) & (k1_xboole_0 != k11_relat_1(sK5,sK4) | r2_hidden(sK4,k1_relat_1(sK5))) & v1_relat_1(sK5))),
% 7.72/1.49    introduced(choice_axiom,[])).
% 7.72/1.49  
% 7.72/1.49  fof(f38,plain,(
% 7.72/1.49    (k1_xboole_0 = k11_relat_1(sK5,sK4) | ~r2_hidden(sK4,k1_relat_1(sK5))) & (k1_xboole_0 != k11_relat_1(sK5,sK4) | r2_hidden(sK4,k1_relat_1(sK5))) & v1_relat_1(sK5)),
% 7.72/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f36,f37])).
% 7.72/1.49  
% 7.72/1.49  fof(f62,plain,(
% 7.72/1.49    v1_relat_1(sK5)),
% 7.72/1.49    inference(cnf_transformation,[],[f38])).
% 7.72/1.49  
% 7.72/1.49  fof(f4,axiom,(
% 7.72/1.49    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 7.72/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.72/1.49  
% 7.72/1.49  fof(f49,plain,(
% 7.72/1.49    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 7.72/1.49    inference(cnf_transformation,[],[f4])).
% 7.72/1.49  
% 7.72/1.49  fof(f8,axiom,(
% 7.72/1.49    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k3_xboole_0(X0,X1)))),
% 7.72/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.72/1.49  
% 7.72/1.49  fof(f15,plain,(
% 7.72/1.49    ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 7.72/1.49    inference(ennf_transformation,[],[f8])).
% 7.72/1.49  
% 7.72/1.49  fof(f57,plain,(
% 7.72/1.49    ( ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 7.72/1.49    inference(cnf_transformation,[],[f15])).
% 7.72/1.49  
% 7.72/1.49  fof(f3,axiom,(
% 7.72/1.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.72/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.72/1.49  
% 7.72/1.49  fof(f25,plain,(
% 7.72/1.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.72/1.49    inference(nnf_transformation,[],[f3])).
% 7.72/1.49  
% 7.72/1.49  fof(f26,plain,(
% 7.72/1.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.72/1.49    inference(flattening,[],[f25])).
% 7.72/1.49  
% 7.72/1.49  fof(f47,plain,(
% 7.72/1.49    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 7.72/1.49    inference(cnf_transformation,[],[f26])).
% 7.72/1.49  
% 7.72/1.49  fof(f68,plain,(
% 7.72/1.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.72/1.49    inference(equality_resolution,[],[f47])).
% 7.72/1.49  
% 7.72/1.49  fof(f2,axiom,(
% 7.72/1.49    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 7.72/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.72/1.49  
% 7.72/1.49  fof(f14,plain,(
% 7.72/1.49    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 7.72/1.49    inference(rectify,[],[f2])).
% 7.72/1.49  
% 7.72/1.49  fof(f45,plain,(
% 7.72/1.49    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 7.72/1.49    inference(cnf_transformation,[],[f14])).
% 7.72/1.49  
% 7.72/1.49  fof(f6,axiom,(
% 7.72/1.49    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0),
% 7.72/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.72/1.49  
% 7.72/1.49  fof(f52,plain,(
% 7.72/1.49    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0) )),
% 7.72/1.49    inference(cnf_transformation,[],[f6])).
% 7.72/1.49  
% 7.72/1.49  fof(f11,axiom,(
% 7.72/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))))),
% 7.72/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.72/1.49  
% 7.72/1.49  fof(f18,plain,(
% 7.72/1.49    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))) | ~v1_relat_1(X2))),
% 7.72/1.49    inference(ennf_transformation,[],[f11])).
% 7.72/1.49  
% 7.72/1.49  fof(f34,plain,(
% 7.72/1.49    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(X1,k11_relat_1(X2,X0))) & (r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_relat_1(X2))),
% 7.72/1.49    inference(nnf_transformation,[],[f18])).
% 7.72/1.49  
% 7.72/1.49  fof(f61,plain,(
% 7.72/1.49    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(X1,k11_relat_1(X2,X0)) | ~v1_relat_1(X2)) )),
% 7.72/1.49    inference(cnf_transformation,[],[f34])).
% 7.72/1.49  
% 7.72/1.49  fof(f7,axiom,(
% 7.72/1.49    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 7.72/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.72/1.49  
% 7.72/1.49  fof(f28,plain,(
% 7.72/1.49    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 7.72/1.49    inference(nnf_transformation,[],[f7])).
% 7.72/1.49  
% 7.72/1.49  fof(f29,plain,(
% 7.72/1.49    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 7.72/1.49    inference(rectify,[],[f28])).
% 7.72/1.49  
% 7.72/1.49  fof(f32,plain,(
% 7.72/1.49    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0))),
% 7.72/1.49    introduced(choice_axiom,[])).
% 7.72/1.49  
% 7.72/1.49  fof(f31,plain,(
% 7.72/1.49    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) => r2_hidden(k4_tarski(X2,sK2(X0,X1)),X0))) )),
% 7.72/1.49    introduced(choice_axiom,[])).
% 7.72/1.49  
% 7.72/1.49  fof(f30,plain,(
% 7.72/1.49    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK1(X0,X1),X3),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK1(X0,X1),X4),X0) | r2_hidden(sK1(X0,X1),X1))))),
% 7.72/1.49    introduced(choice_axiom,[])).
% 7.72/1.49  
% 7.72/1.49  fof(f33,plain,(
% 7.72/1.49    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK1(X0,X1),X3),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 7.72/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f29,f32,f31,f30])).
% 7.72/1.49  
% 7.72/1.49  fof(f55,plain,(
% 7.72/1.49    ( ! [X0,X1] : (k1_relat_1(X0) = X1 | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) | r2_hidden(sK1(X0,X1),X1)) )),
% 7.72/1.49    inference(cnf_transformation,[],[f33])).
% 7.72/1.49  
% 7.72/1.49  fof(f53,plain,(
% 7.72/1.49    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 7.72/1.49    inference(cnf_transformation,[],[f33])).
% 7.72/1.49  
% 7.72/1.49  fof(f71,plain,(
% 7.72/1.49    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 7.72/1.49    inference(equality_resolution,[],[f53])).
% 7.72/1.49  
% 7.72/1.49  fof(f54,plain,(
% 7.72/1.49    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 7.72/1.49    inference(cnf_transformation,[],[f33])).
% 7.72/1.49  
% 7.72/1.49  fof(f70,plain,(
% 7.72/1.49    ( ! [X6,X0,X5] : (r2_hidden(X5,k1_relat_1(X0)) | ~r2_hidden(k4_tarski(X5,X6),X0)) )),
% 7.72/1.49    inference(equality_resolution,[],[f54])).
% 7.72/1.49  
% 7.72/1.49  fof(f64,plain,(
% 7.72/1.49    k1_xboole_0 = k11_relat_1(sK5,sK4) | ~r2_hidden(sK4,k1_relat_1(sK5))),
% 7.72/1.49    inference(cnf_transformation,[],[f38])).
% 7.72/1.49  
% 7.72/1.49  fof(f42,plain,(
% 7.72/1.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 7.72/1.49    inference(cnf_transformation,[],[f24])).
% 7.72/1.49  
% 7.72/1.49  fof(f44,plain,(
% 7.72/1.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 7.72/1.49    inference(cnf_transformation,[],[f24])).
% 7.72/1.49  
% 7.72/1.49  fof(f60,plain,(
% 7.72/1.49    ( ! [X2,X0,X1] : (r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 7.72/1.49    inference(cnf_transformation,[],[f34])).
% 7.72/1.49  
% 7.72/1.49  fof(f63,plain,(
% 7.72/1.49    k1_xboole_0 != k11_relat_1(sK5,sK4) | r2_hidden(sK4,k1_relat_1(sK5))),
% 7.72/1.49    inference(cnf_transformation,[],[f38])).
% 7.72/1.49  
% 7.72/1.49  cnf(c_1,plain,
% 7.72/1.49      ( r2_hidden(sK0(X0,X1,X2),X1)
% 7.72/1.49      | r2_hidden(sK0(X0,X1,X2),X2)
% 7.72/1.49      | k3_xboole_0(X0,X1) = X2 ),
% 7.72/1.49      inference(cnf_transformation,[],[f43]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_1041,plain,
% 7.72/1.49      ( k3_xboole_0(X0,X1) = X2
% 7.72/1.49      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
% 7.72/1.49      | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top ),
% 7.72/1.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_11,plain,
% 7.72/1.49      ( r1_tarski(k1_tarski(X0),X1) | ~ r2_hidden(X0,X1) ),
% 7.72/1.49      inference(cnf_transformation,[],[f51]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_1034,plain,
% 7.72/1.49      ( r1_tarski(k1_tarski(X0),X1) = iProver_top
% 7.72/1.49      | r2_hidden(X0,X1) != iProver_top ),
% 7.72/1.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_19,plain,
% 7.72/1.49      ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.72/1.49      inference(cnf_transformation,[],[f58]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_20,plain,
% 7.72/1.49      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 7.72/1.49      | ~ v1_relat_1(X1)
% 7.72/1.49      | k9_relat_1(X1,X0) != k1_xboole_0
% 7.72/1.49      | k1_xboole_0 = X0 ),
% 7.72/1.49      inference(cnf_transformation,[],[f59]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_1027,plain,
% 7.72/1.49      ( k9_relat_1(X0,X1) != k1_xboole_0
% 7.72/1.49      | k1_xboole_0 = X1
% 7.72/1.49      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 7.72/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.72/1.49      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_3224,plain,
% 7.72/1.49      ( k1_xboole_0 = X0
% 7.72/1.49      | r1_tarski(X0,k1_relat_1(k1_xboole_0)) != iProver_top
% 7.72/1.49      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 7.72/1.49      inference(superposition,[status(thm)],[c_19,c_1027]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_25,negated_conjecture,
% 7.72/1.49      ( v1_relat_1(sK5) ),
% 7.72/1.49      inference(cnf_transformation,[],[f62]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_1022,plain,
% 7.72/1.49      ( v1_relat_1(sK5) = iProver_top ),
% 7.72/1.49      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_10,plain,
% 7.72/1.49      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 7.72/1.49      inference(cnf_transformation,[],[f49]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_18,plain,
% 7.72/1.49      ( ~ v1_relat_1(X0) | v1_relat_1(k3_xboole_0(X0,X1)) ),
% 7.72/1.49      inference(cnf_transformation,[],[f57]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_1028,plain,
% 7.72/1.49      ( v1_relat_1(X0) != iProver_top
% 7.72/1.49      | v1_relat_1(k3_xboole_0(X0,X1)) = iProver_top ),
% 7.72/1.49      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_2041,plain,
% 7.72/1.49      ( v1_relat_1(X0) != iProver_top | v1_relat_1(k1_xboole_0) = iProver_top ),
% 7.72/1.49      inference(superposition,[status(thm)],[c_10,c_1028]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_2045,plain,
% 7.72/1.49      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 7.72/1.49      inference(superposition,[status(thm)],[c_1022,c_2041]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_3275,plain,
% 7.72/1.49      ( r1_tarski(X0,k1_relat_1(k1_xboole_0)) != iProver_top
% 7.72/1.49      | k1_xboole_0 = X0 ),
% 7.72/1.49      inference(global_propositional_subsumption,[status(thm)],[c_3224,c_2045]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_3276,plain,
% 7.72/1.49      ( k1_xboole_0 = X0
% 7.72/1.49      | r1_tarski(X0,k1_relat_1(k1_xboole_0)) != iProver_top ),
% 7.72/1.49      inference(renaming,[status(thm)],[c_3275]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_3280,plain,
% 7.72/1.49      ( k1_tarski(X0) = k1_xboole_0
% 7.72/1.49      | r2_hidden(X0,k1_relat_1(k1_xboole_0)) != iProver_top ),
% 7.72/1.49      inference(superposition,[status(thm)],[c_1034,c_3276]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_8,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f68]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_1035,plain,
% 7.72/1.49      ( r1_tarski(X0,X0) = iProver_top ),
% 7.72/1.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_3279,plain,
% 7.72/1.49      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 7.72/1.49      inference(superposition,[status(thm)],[c_1035,c_3276]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_3301,plain,
% 7.72/1.49      ( k1_tarski(X0) = k1_xboole_0
% 7.72/1.49      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.72/1.49      inference(light_normalisation,[status(thm)],[c_3280,c_3279]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_6,plain,
% 7.72/1.49      ( k2_xboole_0(X0,X0) = X0 ),
% 7.72/1.49      inference(cnf_transformation,[],[f45]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_13,plain,
% 7.72/1.49      ( k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
% 7.72/1.49      inference(cnf_transformation,[],[f52]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_1717,plain,
% 7.72/1.49      ( k1_tarski(X0) != k1_xboole_0 ),
% 7.72/1.49      inference(superposition,[status(thm)],[c_6,c_13]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_3548,plain,
% 7.72/1.49      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.72/1.49      inference(global_propositional_subsumption,[status(thm)],[c_3301,c_1717]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_3556,plain,
% 7.72/1.49      ( k3_xboole_0(X0,X1) = k1_xboole_0
% 7.72/1.49      | r2_hidden(sK0(X0,X1,k1_xboole_0),X1) = iProver_top ),
% 7.72/1.49      inference(superposition,[status(thm)],[c_1041,c_3548]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_21,plain,
% 7.72/1.49      ( ~ r2_hidden(X0,k11_relat_1(X1,X2))
% 7.72/1.49      | r2_hidden(k4_tarski(X2,X0),X1)
% 7.72/1.49      | ~ v1_relat_1(X1) ),
% 7.72/1.49      inference(cnf_transformation,[],[f61]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_1026,plain,
% 7.72/1.49      ( r2_hidden(X0,k11_relat_1(X1,X2)) != iProver_top
% 7.72/1.49      | r2_hidden(k4_tarski(X2,X0),X1) = iProver_top
% 7.72/1.49      | v1_relat_1(X1) != iProver_top ),
% 7.72/1.49      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_3881,plain,
% 7.72/1.49      ( k3_xboole_0(X0,k11_relat_1(X1,X2)) = k1_xboole_0
% 7.72/1.49      | r2_hidden(k4_tarski(X2,sK0(X0,k11_relat_1(X1,X2),k1_xboole_0)),X1) = iProver_top
% 7.72/1.49      | v1_relat_1(X1) != iProver_top ),
% 7.72/1.49      inference(superposition,[status(thm)],[c_3556,c_1026]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_15,plain,
% 7.72/1.49      ( r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
% 7.72/1.49      | r2_hidden(sK1(X0,X1),X1)
% 7.72/1.49      | k1_relat_1(X0) = X1 ),
% 7.72/1.49      inference(cnf_transformation,[],[f55]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_1031,plain,
% 7.72/1.49      ( k1_relat_1(X0) = X1
% 7.72/1.49      | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) = iProver_top
% 7.72/1.49      | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
% 7.72/1.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_17,plain,
% 7.72/1.49      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 7.72/1.49      | r2_hidden(k4_tarski(X0,sK3(X1,X0)),X1) ),
% 7.72/1.49      inference(cnf_transformation,[],[f71]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_1029,plain,
% 7.72/1.49      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 7.72/1.49      | r2_hidden(k4_tarski(X0,sK3(X1,X0)),X1) = iProver_top ),
% 7.72/1.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_2527,plain,
% 7.72/1.49      ( r2_hidden(X0,k1_relat_1(k11_relat_1(X1,X2))) != iProver_top
% 7.72/1.49      | r2_hidden(k4_tarski(X2,k4_tarski(X0,sK3(k11_relat_1(X1,X2),X0))),X1) = iProver_top
% 7.72/1.49      | v1_relat_1(X1) != iProver_top ),
% 7.72/1.49      inference(superposition,[status(thm)],[c_1029,c_1026]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_4288,plain,
% 7.72/1.49      ( r2_hidden(X0,k1_relat_1(k11_relat_1(k1_xboole_0,X1))) != iProver_top
% 7.72/1.49      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 7.72/1.49      inference(superposition,[status(thm)],[c_2527,c_3548]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_4904,plain,
% 7.72/1.49      ( r2_hidden(X0,k1_relat_1(k11_relat_1(k1_xboole_0,X1))) != iProver_top ),
% 7.72/1.49      inference(global_propositional_subsumption,[status(thm)],[c_4288,c_2045]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_4914,plain,
% 7.72/1.49      ( k1_relat_1(k1_relat_1(k11_relat_1(k1_xboole_0,X0))) = X1
% 7.72/1.49      | r2_hidden(sK1(k1_relat_1(k11_relat_1(k1_xboole_0,X0)),X1),X1) = iProver_top ),
% 7.72/1.49      inference(superposition,[status(thm)],[c_1031,c_4904]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_6993,plain,
% 7.72/1.49      ( k1_relat_1(k1_relat_1(k11_relat_1(k1_xboole_0,X0))) = k1_xboole_0 ),
% 7.72/1.49      inference(superposition,[status(thm)],[c_4914,c_3548]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_4915,plain,
% 7.72/1.49      ( r2_hidden(X0,k1_relat_1(k1_relat_1(k11_relat_1(k1_xboole_0,X1)))) != iProver_top ),
% 7.72/1.49      inference(superposition,[status(thm)],[c_1029,c_4904]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_5070,plain,
% 7.72/1.49      ( r2_hidden(X0,k1_relat_1(k1_relat_1(k1_relat_1(k11_relat_1(k1_xboole_0,X1))))) != iProver_top ),
% 7.72/1.49      inference(superposition,[status(thm)],[c_1029,c_4915]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_5395,plain,
% 7.72/1.49      ( r2_hidden(X0,k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k11_relat_1(k1_xboole_0,X1)))))) != iProver_top ),
% 7.72/1.49      inference(superposition,[status(thm)],[c_1029,c_5070]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_5636,plain,
% 7.72/1.49      ( r2_hidden(X0,k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k11_relat_1(k1_xboole_0,X1))))))) != iProver_top ),
% 7.72/1.49      inference(superposition,[status(thm)],[c_1029,c_5395]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_5959,plain,
% 7.72/1.49      ( r2_hidden(X0,k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k11_relat_1(k1_xboole_0,X1)))))))) != iProver_top ),
% 7.72/1.49      inference(superposition,[status(thm)],[c_1029,c_5636]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_6001,plain,
% 7.72/1.49      ( r2_hidden(X0,k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k11_relat_1(k1_xboole_0,X1))))))))) != iProver_top ),
% 7.72/1.49      inference(superposition,[status(thm)],[c_1029,c_5959]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_7004,plain,
% 7.72/1.49      ( k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k11_relat_1(k1_xboole_0,X0)))))))) = k1_relat_1(k1_relat_1(k11_relat_1(k1_xboole_0,X1))) ),
% 7.72/1.49      inference(superposition,[status(thm)],[c_4914,c_6001]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_6062,plain,
% 7.72/1.49      ( r2_hidden(X0,k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k11_relat_1(k1_xboole_0,X1)))))))))) != iProver_top ),
% 7.72/1.49      inference(superposition,[status(thm)],[c_1029,c_6001]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_6787,plain,
% 7.72/1.49      ( r2_hidden(X0,k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k11_relat_1(k1_xboole_0,X1))))))))))) != iProver_top ),
% 7.72/1.49      inference(superposition,[status(thm)],[c_1029,c_6062]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_7006,plain,
% 7.72/1.49      ( k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k11_relat_1(k1_xboole_0,X0)))))))))) = k1_relat_1(k1_relat_1(k11_relat_1(k1_xboole_0,X1))) ),
% 7.72/1.49      inference(superposition,[status(thm)],[c_4914,c_6787]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_7007,plain,
% 7.72/1.49      ( k1_relat_1(k1_relat_1(k11_relat_1(k1_xboole_0,X0))) = sP0_iProver_split ),
% 7.72/1.49      inference(splitting,
% 7.72/1.49                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 7.72/1.49                [c_7006]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_7189,plain,
% 7.72/1.49      ( k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(sP0_iProver_split))))) = k1_relat_1(k1_relat_1(k11_relat_1(k1_xboole_0,X0))) ),
% 7.72/1.49      inference(light_normalisation,[status(thm)],[c_7004,c_7007]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_7190,plain,
% 7.72/1.49      ( k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(sP0_iProver_split))))) = sP0_iProver_split ),
% 7.72/1.49      inference(demodulation,[status(thm)],[c_7189,c_7007]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_7005,plain,
% 7.72/1.49      ( k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k11_relat_1(k1_xboole_0,X0))))))))) = k1_relat_1(k1_relat_1(k11_relat_1(k1_xboole_0,X1))) ),
% 7.72/1.49      inference(superposition,[status(thm)],[c_4914,c_6062]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_7186,plain,
% 7.72/1.49      ( k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(sP0_iProver_split)))))) = k1_relat_1(k1_relat_1(k11_relat_1(k1_xboole_0,X0))) ),
% 7.72/1.49      inference(light_normalisation,[status(thm)],[c_7005,c_7007]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_7187,plain,
% 7.72/1.49      ( k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(sP0_iProver_split)))))) = sP0_iProver_split ),
% 7.72/1.49      inference(demodulation,[status(thm)],[c_7186,c_7007]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_7191,plain,
% 7.72/1.49      ( k1_relat_1(sP0_iProver_split) = sP0_iProver_split ),
% 7.72/1.49      inference(demodulation,[status(thm)],[c_7190,c_7187]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_6998,plain,
% 7.72/1.49      ( k1_relat_1(k1_relat_1(k11_relat_1(k1_xboole_0,X0))) = k1_relat_1(k11_relat_1(k1_xboole_0,X1)) ),
% 7.72/1.49      inference(superposition,[status(thm)],[c_4914,c_4904]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_7239,plain,
% 7.72/1.49      ( k1_relat_1(k11_relat_1(k1_xboole_0,X0)) = sP0_iProver_split ),
% 7.72/1.49      inference(light_normalisation,[status(thm)],[c_6998,c_7007]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_7243,plain,
% 7.72/1.49      ( sP0_iProver_split = k1_xboole_0 ),
% 7.72/1.49      inference(demodulation,[status(thm)],[c_6993,c_7191,c_7239]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_19252,plain,
% 7.72/1.49      ( k3_xboole_0(X0,k11_relat_1(X1,X2)) = sP0_iProver_split
% 7.72/1.49      | r2_hidden(k4_tarski(X2,sK0(X0,k11_relat_1(X1,X2),sP0_iProver_split)),X1) = iProver_top
% 7.72/1.49      | v1_relat_1(X1) != iProver_top ),
% 7.72/1.49      inference(light_normalisation,[status(thm)],[c_3881,c_7243]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_16,plain,
% 7.72/1.49      ( r2_hidden(X0,k1_relat_1(X1)) | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
% 7.72/1.49      inference(cnf_transformation,[],[f70]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_1030,plain,
% 7.72/1.49      ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
% 7.72/1.49      | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top ),
% 7.72/1.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_19259,plain,
% 7.72/1.49      ( k3_xboole_0(X0,k11_relat_1(X1,X2)) = sP0_iProver_split
% 7.72/1.49      | r2_hidden(X2,k1_relat_1(X1)) = iProver_top
% 7.72/1.49      | v1_relat_1(X1) != iProver_top ),
% 7.72/1.49      inference(superposition,[status(thm)],[c_19252,c_1030]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_23,negated_conjecture,
% 7.72/1.49      ( ~ r2_hidden(sK4,k1_relat_1(sK5)) | k1_xboole_0 = k11_relat_1(sK5,sK4) ),
% 7.72/1.49      inference(cnf_transformation,[],[f64]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_1024,plain,
% 7.72/1.49      ( k1_xboole_0 = k11_relat_1(sK5,sK4)
% 7.72/1.49      | r2_hidden(sK4,k1_relat_1(sK5)) != iProver_top ),
% 7.72/1.49      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_7305,plain,
% 7.72/1.49      ( k11_relat_1(sK5,sK4) = sP0_iProver_split
% 7.72/1.49      | r2_hidden(sK4,k1_relat_1(sK5)) != iProver_top ),
% 7.72/1.49      inference(demodulation,[status(thm)],[c_7243,c_1024]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_19479,plain,
% 7.72/1.49      ( k11_relat_1(sK5,sK4) = sP0_iProver_split
% 7.72/1.49      | k3_xboole_0(X0,k11_relat_1(sK5,sK4)) = sP0_iProver_split
% 7.72/1.49      | v1_relat_1(sK5) != iProver_top ),
% 7.72/1.49      inference(superposition,[status(thm)],[c_19259,c_7305]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_19531,plain,
% 7.72/1.49      ( ~ v1_relat_1(sK5)
% 7.72/1.49      | k11_relat_1(sK5,sK4) = sP0_iProver_split
% 7.72/1.49      | k3_xboole_0(X0,k11_relat_1(sK5,sK4)) = sP0_iProver_split ),
% 7.72/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_19479]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_19591,plain,
% 7.72/1.49      ( k3_xboole_0(X0,k11_relat_1(sK5,sK4)) = sP0_iProver_split
% 7.72/1.49      | k11_relat_1(sK5,sK4) = sP0_iProver_split ),
% 7.72/1.49      inference(global_propositional_subsumption,
% 7.72/1.49                [status(thm)],
% 7.72/1.49                [c_19479,c_25,c_19531]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_19592,plain,
% 7.72/1.49      ( k11_relat_1(sK5,sK4) = sP0_iProver_split
% 7.72/1.49      | k3_xboole_0(X0,k11_relat_1(sK5,sK4)) = sP0_iProver_split ),
% 7.72/1.49      inference(renaming,[status(thm)],[c_19591]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_2,plain,
% 7.72/1.49      ( r2_hidden(sK0(X0,X1,X2),X0)
% 7.72/1.49      | r2_hidden(sK0(X0,X1,X2),X2)
% 7.72/1.49      | k3_xboole_0(X0,X1) = X2 ),
% 7.72/1.49      inference(cnf_transformation,[],[f42]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_1040,plain,
% 7.72/1.49      ( k3_xboole_0(X0,X1) = X2
% 7.72/1.49      | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
% 7.72/1.49      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
% 7.72/1.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_2782,plain,
% 7.72/1.49      ( k3_xboole_0(X0,X1) = X0
% 7.72/1.49      | r2_hidden(sK0(X0,X1,X0),X0) = iProver_top
% 7.72/1.49      | iProver_top != iProver_top ),
% 7.72/1.49      inference(equality_factoring,[status(thm)],[c_1040]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_2784,plain,
% 7.72/1.49      ( k3_xboole_0(X0,X1) = X0 | r2_hidden(sK0(X0,X1,X0),X0) = iProver_top ),
% 7.72/1.49      inference(equality_resolution_simp,[status(thm)],[c_2782]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_0,plain,
% 7.72/1.49      ( ~ r2_hidden(sK0(X0,X1,X2),X1)
% 7.72/1.49      | ~ r2_hidden(sK0(X0,X1,X2),X0)
% 7.72/1.49      | ~ r2_hidden(sK0(X0,X1,X2),X2)
% 7.72/1.49      | k3_xboole_0(X0,X1) = X2 ),
% 7.72/1.49      inference(cnf_transformation,[],[f44]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_1042,plain,
% 7.72/1.49      ( k3_xboole_0(X0,X1) = X2
% 7.72/1.49      | r2_hidden(sK0(X0,X1,X2),X0) != iProver_top
% 7.72/1.49      | r2_hidden(sK0(X0,X1,X2),X2) != iProver_top
% 7.72/1.49      | r2_hidden(sK0(X0,X1,X2),X1) != iProver_top ),
% 7.72/1.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_16847,plain,
% 7.72/1.49      ( k3_xboole_0(X0,X1) = X0
% 7.72/1.49      | r2_hidden(sK0(X0,X1,X0),X0) != iProver_top
% 7.72/1.49      | r2_hidden(sK0(X0,X1,X0),X1) != iProver_top ),
% 7.72/1.49      inference(superposition,[status(thm)],[c_2784,c_1042]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_17629,plain,
% 7.72/1.49      ( k3_xboole_0(X0,X1) = X0 | r2_hidden(sK0(X0,X1,X0),X1) != iProver_top ),
% 7.72/1.49      inference(global_propositional_subsumption,
% 7.72/1.49                [status(thm)],
% 7.72/1.49                [c_16847,c_2784]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_17649,plain,
% 7.72/1.49      ( k3_xboole_0(X0,X0) = X0 ),
% 7.72/1.49      inference(superposition,[status(thm)],[c_2784,c_17629]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_19653,plain,
% 7.72/1.49      ( k11_relat_1(sK5,sK4) = sP0_iProver_split ),
% 7.72/1.49      inference(superposition,[status(thm)],[c_19592,c_17649]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_22,plain,
% 7.72/1.49      ( r2_hidden(X0,k11_relat_1(X1,X2))
% 7.72/1.49      | ~ r2_hidden(k4_tarski(X2,X0),X1)
% 7.72/1.49      | ~ v1_relat_1(X1) ),
% 7.72/1.49      inference(cnf_transformation,[],[f60]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_1025,plain,
% 7.72/1.49      ( r2_hidden(X0,k11_relat_1(X1,X2)) = iProver_top
% 7.72/1.49      | r2_hidden(k4_tarski(X2,X0),X1) != iProver_top
% 7.72/1.49      | v1_relat_1(X1) != iProver_top ),
% 7.72/1.49      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_2528,plain,
% 7.72/1.49      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 7.72/1.49      | r2_hidden(sK3(X1,X0),k11_relat_1(X1,X0)) = iProver_top
% 7.72/1.49      | v1_relat_1(X1) != iProver_top ),
% 7.72/1.49      inference(superposition,[status(thm)],[c_1029,c_1025]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_19960,plain,
% 7.72/1.49      ( r2_hidden(sK3(sK5,sK4),sP0_iProver_split) = iProver_top
% 7.72/1.49      | r2_hidden(sK4,k1_relat_1(sK5)) != iProver_top
% 7.72/1.49      | v1_relat_1(sK5) != iProver_top ),
% 7.72/1.49      inference(superposition,[status(thm)],[c_19653,c_2528]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_26,plain,
% 7.72/1.49      ( v1_relat_1(sK5) = iProver_top ),
% 7.72/1.49      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_24,negated_conjecture,
% 7.72/1.49      ( r2_hidden(sK4,k1_relat_1(sK5)) | k1_xboole_0 != k11_relat_1(sK5,sK4) ),
% 7.72/1.49      inference(cnf_transformation,[],[f63]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_1023,plain,
% 7.72/1.49      ( k1_xboole_0 != k11_relat_1(sK5,sK4)
% 7.72/1.49      | r2_hidden(sK4,k1_relat_1(sK5)) = iProver_top ),
% 7.72/1.49      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_7306,plain,
% 7.72/1.49      ( k11_relat_1(sK5,sK4) != sP0_iProver_split
% 7.72/1.49      | r2_hidden(sK4,k1_relat_1(sK5)) = iProver_top ),
% 7.72/1.49      inference(demodulation,[status(thm)],[c_7243,c_1023]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_20044,plain,
% 7.72/1.49      ( r2_hidden(sK3(sK5,sK4),sP0_iProver_split) = iProver_top ),
% 7.72/1.49      inference(global_propositional_subsumption,
% 7.72/1.49                [status(thm)],
% 7.72/1.49                [c_19960,c_26,c_7306,c_19653]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_7168,plain,
% 7.72/1.49      ( r2_hidden(X0,sP0_iProver_split) != iProver_top ),
% 7.72/1.49      inference(demodulation,[status(thm)],[c_7007,c_4915]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_20048,plain,
% 7.72/1.49      ( $false ),
% 7.72/1.49      inference(superposition,[status(thm)],[c_20044,c_7168]) ).
% 7.72/1.49  
% 7.72/1.49  
% 7.72/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.72/1.49  
% 7.72/1.49  ------                               Statistics
% 7.72/1.49  
% 7.72/1.49  ------ General
% 7.72/1.49  
% 7.72/1.49  abstr_ref_over_cycles:                  0
% 7.72/1.49  abstr_ref_under_cycles:                 0
% 7.72/1.49  gc_basic_clause_elim:                   0
% 7.72/1.49  forced_gc_time:                         0
% 7.72/1.49  parsing_time:                           0.008
% 7.72/1.49  unif_index_cands_time:                  0.
% 7.72/1.49  unif_index_add_time:                    0.
% 7.72/1.49  orderings_time:                         0.
% 7.72/1.49  out_proof_time:                         0.011
% 7.72/1.49  total_time:                             0.683
% 7.72/1.49  num_of_symbols:                         49
% 7.72/1.49  num_of_terms:                           45088
% 7.72/1.49  
% 7.72/1.49  ------ Preprocessing
% 7.72/1.49  
% 7.72/1.49  num_of_splits:                          0
% 7.72/1.49  num_of_split_atoms:                     1
% 7.72/1.49  num_of_reused_defs:                     0
% 7.72/1.49  num_eq_ax_congr_red:                    39
% 7.72/1.49  num_of_sem_filtered_clauses:            1
% 7.72/1.49  num_of_subtypes:                        0
% 7.72/1.49  monotx_restored_types:                  0
% 7.72/1.49  sat_num_of_epr_types:                   0
% 7.72/1.49  sat_num_of_non_cyclic_types:            0
% 7.72/1.49  sat_guarded_non_collapsed_types:        0
% 7.72/1.49  num_pure_diseq_elim:                    0
% 7.72/1.49  simp_replaced_by:                       0
% 7.72/1.49  res_preprocessed:                       123
% 7.72/1.49  prep_upred:                             0
% 7.72/1.49  prep_unflattend:                        0
% 7.72/1.49  smt_new_axioms:                         0
% 7.72/1.49  pred_elim_cands:                        3
% 7.72/1.49  pred_elim:                              0
% 7.72/1.49  pred_elim_cl:                           0
% 7.72/1.49  pred_elim_cycles:                       2
% 7.72/1.49  merged_defs:                            16
% 7.72/1.49  merged_defs_ncl:                        0
% 7.72/1.49  bin_hyper_res:                          16
% 7.72/1.49  prep_cycles:                            4
% 7.72/1.49  pred_elim_time:                         0.
% 7.72/1.49  splitting_time:                         0.
% 7.72/1.49  sem_filter_time:                        0.
% 7.72/1.49  monotx_time:                            0.
% 7.72/1.49  subtype_inf_time:                       0.
% 7.72/1.49  
% 7.72/1.49  ------ Problem properties
% 7.72/1.49  
% 7.72/1.49  clauses:                                25
% 7.72/1.49  conjectures:                            3
% 7.72/1.49  epr:                                    3
% 7.72/1.49  horn:                                   22
% 7.72/1.49  ground:                                 3
% 7.72/1.49  unary:                                  6
% 7.72/1.49  binary:                                 9
% 7.72/1.49  lits:                                   56
% 7.72/1.49  lits_eq:                                14
% 7.72/1.49  fd_pure:                                0
% 7.72/1.49  fd_pseudo:                              0
% 7.72/1.49  fd_cond:                                1
% 7.72/1.49  fd_pseudo_cond:                         6
% 7.72/1.49  ac_symbols:                             0
% 7.72/1.49  
% 7.72/1.49  ------ Propositional Solver
% 7.72/1.49  
% 7.72/1.49  prop_solver_calls:                      31
% 7.72/1.49  prop_fast_solver_calls:                 1001
% 7.72/1.49  smt_solver_calls:                       0
% 7.72/1.49  smt_fast_solver_calls:                  0
% 7.72/1.49  prop_num_of_clauses:                    11542
% 7.72/1.49  prop_preprocess_simplified:             14469
% 7.72/1.49  prop_fo_subsumed:                       9
% 7.72/1.49  prop_solver_time:                       0.
% 7.72/1.49  smt_solver_time:                        0.
% 7.72/1.49  smt_fast_solver_time:                   0.
% 7.72/1.49  prop_fast_solver_time:                  0.
% 7.72/1.49  prop_unsat_core_time:                   0.
% 7.72/1.49  
% 7.72/1.49  ------ QBF
% 7.72/1.49  
% 7.72/1.49  qbf_q_res:                              0
% 7.72/1.49  qbf_num_tautologies:                    0
% 7.72/1.49  qbf_prep_cycles:                        0
% 7.72/1.49  
% 7.72/1.49  ------ BMC1
% 7.72/1.49  
% 7.72/1.49  bmc1_current_bound:                     -1
% 7.72/1.49  bmc1_last_solved_bound:                 -1
% 7.72/1.49  bmc1_unsat_core_size:                   -1
% 7.72/1.49  bmc1_unsat_core_parents_size:           -1
% 7.72/1.49  bmc1_merge_next_fun:                    0
% 7.72/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.72/1.49  
% 7.72/1.49  ------ Instantiation
% 7.72/1.49  
% 7.72/1.49  inst_num_of_clauses:                    1691
% 7.72/1.49  inst_num_in_passive:                    582
% 7.72/1.49  inst_num_in_active:                     768
% 7.72/1.49  inst_num_in_unprocessed:                341
% 7.72/1.49  inst_num_of_loops:                      910
% 7.72/1.49  inst_num_of_learning_restarts:          0
% 7.72/1.49  inst_num_moves_active_passive:          140
% 7.72/1.49  inst_lit_activity:                      0
% 7.72/1.49  inst_lit_activity_moves:                0
% 7.72/1.49  inst_num_tautologies:                   0
% 7.72/1.49  inst_num_prop_implied:                  0
% 7.72/1.49  inst_num_existing_simplified:           0
% 7.72/1.49  inst_num_eq_res_simplified:             0
% 7.72/1.49  inst_num_child_elim:                    0
% 7.72/1.49  inst_num_of_dismatching_blockings:      939
% 7.72/1.49  inst_num_of_non_proper_insts:           1405
% 7.72/1.49  inst_num_of_duplicates:                 0
% 7.72/1.49  inst_inst_num_from_inst_to_res:         0
% 7.72/1.49  inst_dismatching_checking_time:         0.
% 7.72/1.49  
% 7.72/1.49  ------ Resolution
% 7.72/1.49  
% 7.72/1.49  res_num_of_clauses:                     0
% 7.72/1.49  res_num_in_passive:                     0
% 7.72/1.49  res_num_in_active:                      0
% 7.72/1.49  res_num_of_loops:                       127
% 7.72/1.49  res_forward_subset_subsumed:            134
% 7.72/1.49  res_backward_subset_subsumed:           4
% 7.72/1.49  res_forward_subsumed:                   0
% 7.72/1.49  res_backward_subsumed:                  0
% 7.72/1.49  res_forward_subsumption_resolution:     0
% 7.72/1.49  res_backward_subsumption_resolution:    0
% 7.72/1.49  res_clause_to_clause_subsumption:       14260
% 7.72/1.49  res_orphan_elimination:                 0
% 7.72/1.49  res_tautology_del:                      103
% 7.72/1.49  res_num_eq_res_simplified:              0
% 7.72/1.49  res_num_sel_changes:                    0
% 7.72/1.49  res_moves_from_active_to_pass:          0
% 7.72/1.49  
% 7.72/1.49  ------ Superposition
% 7.72/1.49  
% 7.72/1.49  sup_time_total:                         0.
% 7.72/1.49  sup_time_generating:                    0.
% 7.72/1.49  sup_time_sim_full:                      0.
% 7.72/1.49  sup_time_sim_immed:                     0.
% 7.72/1.49  
% 7.72/1.49  sup_num_of_clauses:                     1726
% 7.72/1.49  sup_num_in_active:                      128
% 7.72/1.49  sup_num_in_passive:                     1598
% 7.72/1.49  sup_num_of_loops:                       180
% 7.72/1.49  sup_fw_superposition:                   1530
% 7.72/1.49  sup_bw_superposition:                   1416
% 7.72/1.49  sup_immediate_simplified:               784
% 7.72/1.49  sup_given_eliminated:                   5
% 7.72/1.49  comparisons_done:                       0
% 7.72/1.49  comparisons_avoided:                    0
% 7.72/1.49  
% 7.72/1.49  ------ Simplifications
% 7.72/1.49  
% 7.72/1.49  
% 7.72/1.49  sim_fw_subset_subsumed:                 99
% 7.72/1.49  sim_bw_subset_subsumed:                 9
% 7.72/1.49  sim_fw_subsumed:                        219
% 7.72/1.49  sim_bw_subsumed:                        5
% 7.72/1.49  sim_fw_subsumption_res:                 0
% 7.72/1.49  sim_bw_subsumption_res:                 0
% 7.72/1.49  sim_tautology_del:                      54
% 7.72/1.49  sim_eq_tautology_del:                   119
% 7.72/1.49  sim_eq_res_simp:                        8
% 7.72/1.49  sim_fw_demodulated:                     430
% 7.72/1.49  sim_bw_demodulated:                     134
% 7.72/1.49  sim_light_normalised:                   198
% 7.72/1.49  sim_joinable_taut:                      0
% 7.72/1.49  sim_joinable_simp:                      0
% 7.72/1.49  sim_ac_normalised:                      0
% 7.72/1.49  sim_smt_subsumption:                    0
% 7.72/1.49  
%------------------------------------------------------------------------------
