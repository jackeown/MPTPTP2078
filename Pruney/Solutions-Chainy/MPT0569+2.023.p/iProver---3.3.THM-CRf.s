%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:47:30 EST 2020

% Result     : Theorem 3.32s
% Output     : CNFRefutation 3.32s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 221 expanded)
%              Number of clauses        :   69 (  78 expanded)
%              Number of leaves         :   21 (  50 expanded)
%              Depth                    :   13
%              Number of atoms          :  424 ( 868 expanded)
%              Number of equality atoms :   97 ( 177 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   10 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f44])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f40])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f41,f42])).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f22,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k10_relat_1(X1,X0)
        <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f39,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <~> r1_xboole_0(k2_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f59,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 != k10_relat_1(X1,X0) )
      & ( r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f60,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 != k10_relat_1(X1,X0) )
      & ( r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f59])).

fof(f61,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 != k10_relat_1(X1,X0) )
        & ( r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 = k10_relat_1(X1,X0) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_xboole_0(k2_relat_1(sK8),sK7)
        | k1_xboole_0 != k10_relat_1(sK8,sK7) )
      & ( r1_xboole_0(k2_relat_1(sK8),sK7)
        | k1_xboole_0 = k10_relat_1(sK8,sK7) )
      & v1_relat_1(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,
    ( ( ~ r1_xboole_0(k2_relat_1(sK8),sK7)
      | k1_xboole_0 != k10_relat_1(sK8,sK7) )
    & ( r1_xboole_0(k2_relat_1(sK8),sK7)
      | k1_xboole_0 = k10_relat_1(sK8,sK7) )
    & v1_relat_1(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f60,f61])).

fof(f97,plain,
    ( r1_xboole_0(k2_relat_1(sK8),sK7)
    | k1_xboole_0 = k10_relat_1(sK8,sK7) ),
    inference(cnf_transformation,[],[f62])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f9,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( X1 = X2
      | ~ r1_xboole_0(X3,X1)
      | ~ r1_xboole_0(X2,X0)
      | k2_xboole_0(X0,X1) != k2_xboole_0(X2,X3) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( X1 = X2
      | ~ r1_xboole_0(X3,X1)
      | ~ r1_xboole_0(X2,X0)
      | k2_xboole_0(X0,X1) != k2_xboole_0(X2,X3) ) ),
    inference(flattening,[],[f31])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X2
      | ~ r1_xboole_0(X3,X1)
      | ~ r1_xboole_0(X2,X0)
      | k2_xboole_0(X0,X1) != k2_xboole_0(X2,X3) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X0,X3),X2)
              & r2_hidden(X3,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X0,X4),X2)
              & r2_hidden(X4,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f55])).

fof(f57,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X0,X4),X2)
          & r2_hidden(X4,k2_relat_1(X2)) )
     => ( r2_hidden(sK6(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X0,sK6(X0,X1,X2)),X2)
        & r2_hidden(sK6(X0,X1,X2),k2_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ( r2_hidden(sK6(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(X0,sK6(X0,X1,X2)),X2)
            & r2_hidden(sK6(X0,X1,X2),k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f56,f57])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X2),k2_relat_1(X2))
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f96,plain,(
    v1_relat_1(sK8) ),
    inference(cnf_transformation,[],[f62])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f92,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X0,X3),X2)
      | ~ r2_hidden(X3,k2_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f50,plain,(
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
    inference(rectify,[],[f49])).

fof(f53,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK5(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK4(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK5(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f50,f53,f52,f51])).

fof(f86,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f104,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X6,X5),X0) ) ),
    inference(equality_resolution,[],[f86])).

fof(f85,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f105,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK5(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f85])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f98,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK8),sK7)
    | k1_xboole_0 != k10_relat_1(sK8,sK7) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_4,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1918,plain,
    ( ~ r1_xboole_0(X0,k10_relat_1(sK8,sK7))
    | ~ r2_hidden(X1,X0)
    | ~ r2_hidden(X1,k10_relat_1(sK8,sK7)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_8083,plain,
    ( ~ r1_xboole_0(X0,k10_relat_1(sK8,sK7))
    | ~ r2_hidden(sK5(sK8,sK1(k2_relat_1(sK8),sK7)),X0)
    | ~ r2_hidden(sK5(sK8,sK1(k2_relat_1(sK8),sK7)),k10_relat_1(sK8,sK7)) ),
    inference(instantiation,[status(thm)],[c_1918])).

cnf(c_8085,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k10_relat_1(sK8,sK7))
    | ~ r2_hidden(sK5(sK8,sK1(k2_relat_1(sK8),sK7)),k10_relat_1(sK8,sK7))
    | ~ r2_hidden(sK5(sK8,sK1(k2_relat_1(sK8),sK7)),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_8083])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_8049,plain,
    ( r2_hidden(sK5(sK8,sK1(k2_relat_1(sK8),sK7)),X0)
    | ~ r2_hidden(sK5(sK8,sK1(k2_relat_1(sK8),sK7)),k10_relat_1(sK8,sK7))
    | ~ r1_tarski(k10_relat_1(sK8,sK7),X0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_8066,plain,
    ( ~ r2_hidden(sK5(sK8,sK1(k2_relat_1(sK8),sK7)),k10_relat_1(sK8,sK7))
    | r2_hidden(sK5(sK8,sK1(k2_relat_1(sK8),sK7)),k1_xboole_0)
    | ~ r1_tarski(k10_relat_1(sK8,sK7),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_8049])).

cnf(c_32,negated_conjecture,
    ( r1_xboole_0(k2_relat_1(sK8),sK7)
    | k1_xboole_0 = k10_relat_1(sK8,sK7) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1648,plain,
    ( k1_xboole_0 = k10_relat_1(sK8,sK7)
    | r1_xboole_0(k2_relat_1(sK8),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_17,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1656,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4152,plain,
    ( k10_relat_1(sK8,sK7) = k1_xboole_0
    | k4_xboole_0(k2_xboole_0(k2_relat_1(sK8),sK7),sK7) = k2_relat_1(sK8) ),
    inference(superposition,[status(thm)],[c_1648,c_1656])).

cnf(c_13,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_89,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_14,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(X2,X3)
    | X2 = X1
    | k2_xboole_0(X2,X0) != k2_xboole_0(X3,X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1840,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(k10_relat_1(sK8,sK7),X2)
    | k10_relat_1(sK8,sK7) = X1
    | k2_xboole_0(k10_relat_1(sK8,sK7),X0) != k2_xboole_0(X2,X1) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_2006,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(k10_relat_1(sK8,sK7),k10_relat_1(sK8,sK7))
    | k10_relat_1(sK8,sK7) = X1
    | k2_xboole_0(k10_relat_1(sK8,sK7),X0) != k2_xboole_0(k10_relat_1(sK8,sK7),X1) ),
    inference(instantiation,[status(thm)],[c_1840])).

cnf(c_2012,plain,
    ( ~ r1_xboole_0(k10_relat_1(sK8,sK7),k10_relat_1(sK8,sK7))
    | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | k10_relat_1(sK8,sK7) = k1_xboole_0
    | k2_xboole_0(k10_relat_1(sK8,sK7),k1_xboole_0) != k2_xboole_0(k10_relat_1(sK8,sK7),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2006])).

cnf(c_5,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1851,plain,
    ( r1_xboole_0(X0,k10_relat_1(sK8,sK7))
    | r2_hidden(sK1(X0,k10_relat_1(sK8,sK7)),k10_relat_1(sK8,sK7)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2010,plain,
    ( r1_xboole_0(k10_relat_1(sK8,sK7),k10_relat_1(sK8,sK7))
    | r2_hidden(sK1(k10_relat_1(sK8,sK7),k10_relat_1(sK8,sK7)),k10_relat_1(sK8,sK7)) ),
    inference(instantiation,[status(thm)],[c_1851])).

cnf(c_1009,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2378,plain,
    ( k2_xboole_0(k10_relat_1(sK8,sK7),X0) = k2_xboole_0(k10_relat_1(sK8,sK7),X0) ),
    inference(instantiation,[status(thm)],[c_1009])).

cnf(c_2379,plain,
    ( k2_xboole_0(k10_relat_1(sK8,sK7),k1_xboole_0) = k2_xboole_0(k10_relat_1(sK8,sK7),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2378])).

cnf(c_16,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1657,plain,
    ( k4_xboole_0(X0,X1) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2631,plain,
    ( k10_relat_1(sK8,sK7) = k1_xboole_0
    | k4_xboole_0(k2_relat_1(sK8),sK7) = k2_relat_1(sK8) ),
    inference(superposition,[status(thm)],[c_1648,c_1657])).

cnf(c_15,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) != X0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1658,plain,
    ( k4_xboole_0(X0,X1) != X0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2753,plain,
    ( k10_relat_1(sK8,sK7) = k1_xboole_0
    | r1_xboole_0(k2_relat_1(sK8),sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_2631,c_1658])).

cnf(c_2755,plain,
    ( r1_xboole_0(k2_relat_1(sK8),sK7)
    | k10_relat_1(sK8,sK7) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2753])).

cnf(c_27,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK6(X0,X2,X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_33,negated_conjecture,
    ( v1_relat_1(sK8) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_446,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK6(X0,X2,X1),k2_relat_1(X1))
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_33])).

cnf(c_447,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK8,X1))
    | r2_hidden(sK6(X0,X1,sK8),k2_relat_1(sK8)) ),
    inference(unflattening,[status(thm)],[c_446])).

cnf(c_3029,plain,
    ( r2_hidden(sK6(sK1(k10_relat_1(sK8,sK7),k10_relat_1(sK8,sK7)),sK7,sK8),k2_relat_1(sK8))
    | ~ r2_hidden(sK1(k10_relat_1(sK8,sK7),k10_relat_1(sK8,sK7)),k10_relat_1(sK8,sK7)) ),
    inference(instantiation,[status(thm)],[c_447])).

cnf(c_25,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK6(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_470,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK6(X0,X2,X1),X2)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_33])).

cnf(c_471,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK8,X1))
    | r2_hidden(sK6(X0,X1,sK8),X1) ),
    inference(unflattening,[status(thm)],[c_470])).

cnf(c_3027,plain,
    ( r2_hidden(sK6(sK1(k10_relat_1(sK8,sK7),k10_relat_1(sK8,sK7)),sK7,sK8),sK7)
    | ~ r2_hidden(sK1(k10_relat_1(sK8,sK7),k10_relat_1(sK8,sK7)),k10_relat_1(sK8,sK7)) ),
    inference(instantiation,[status(thm)],[c_471])).

cnf(c_1768,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK8),sK7)
    | ~ r2_hidden(X0,k2_relat_1(sK8))
    | ~ r2_hidden(X0,sK7) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_3822,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK8),sK7)
    | ~ r2_hidden(sK6(sK1(k10_relat_1(sK8,sK7),k10_relat_1(sK8,sK7)),sK7,sK8),k2_relat_1(sK8))
    | ~ r2_hidden(sK6(sK1(k10_relat_1(sK8,sK7),k10_relat_1(sK8,sK7)),sK7,sK8),sK7) ),
    inference(instantiation,[status(thm)],[c_1768])).

cnf(c_4664,plain,
    ( k10_relat_1(sK8,sK7) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4152,c_89,c_2012,c_2010,c_2379,c_2755,c_3029,c_3027,c_3822])).

cnf(c_24,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(X3,X1))
    | ~ r2_hidden(X0,k2_relat_1(X3))
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_426,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(X3,X1))
    | ~ r2_hidden(X0,k2_relat_1(X3))
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | sK8 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_33])).

cnf(c_427,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(sK8,X1))
    | ~ r2_hidden(X0,k2_relat_1(sK8))
    | ~ r2_hidden(k4_tarski(X2,X0),sK8) ),
    inference(unflattening,[status(thm)],[c_426])).

cnf(c_22,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_439,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(sK8,X1))
    | ~ r2_hidden(k4_tarski(X2,X0),sK8) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_427,c_22])).

cnf(c_2168,plain,
    ( r2_hidden(X0,k10_relat_1(sK8,sK7))
    | ~ r2_hidden(k4_tarski(X0,sK1(k2_relat_1(sK8),sK7)),sK8)
    | ~ r2_hidden(sK1(k2_relat_1(sK8),sK7),sK7) ),
    inference(instantiation,[status(thm)],[c_439])).

cnf(c_4086,plain,
    ( r2_hidden(sK5(sK8,sK1(k2_relat_1(sK8),sK7)),k10_relat_1(sK8,sK7))
    | ~ r2_hidden(k4_tarski(sK5(sK8,sK1(k2_relat_1(sK8),sK7)),sK1(k2_relat_1(sK8),sK7)),sK8)
    | ~ r2_hidden(sK1(k2_relat_1(sK8),sK7),sK7) ),
    inference(instantiation,[status(thm)],[c_2168])).

cnf(c_1012,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3135,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k10_relat_1(sK8,sK7),X2)
    | X2 != X1
    | k10_relat_1(sK8,sK7) != X0 ),
    inference(instantiation,[status(thm)],[c_1012])).

cnf(c_3137,plain,
    ( r1_tarski(k10_relat_1(sK8,sK7),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k10_relat_1(sK8,sK7) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3135])).

cnf(c_23,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(k4_tarski(sK5(X1,X0),X0),X1) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_2207,plain,
    ( r2_hidden(k4_tarski(sK5(sK8,sK1(k2_relat_1(sK8),sK7)),sK1(k2_relat_1(sK8),sK7)),sK8)
    | ~ r2_hidden(sK1(k2_relat_1(sK8),sK7),k2_relat_1(sK8)) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_1014,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1872,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,k10_relat_1(sK8,sK7))
    | X2 != X0
    | k10_relat_1(sK8,sK7) != X1 ),
    inference(instantiation,[status(thm)],[c_1014])).

cnf(c_1874,plain,
    ( r1_xboole_0(k1_xboole_0,k10_relat_1(sK8,sK7))
    | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | k10_relat_1(sK8,sK7) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1872])).

cnf(c_1010,plain,
    ( X0 != X1
    | X2 != X1
    | X0 = X2 ),
    theory(equality)).

cnf(c_1783,plain,
    ( k10_relat_1(sK8,sK7) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k10_relat_1(sK8,sK7) ),
    inference(instantiation,[status(thm)],[c_1010])).

cnf(c_1784,plain,
    ( k10_relat_1(sK8,sK7) != k1_xboole_0
    | k1_xboole_0 = k10_relat_1(sK8,sK7)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1783])).

cnf(c_1708,plain,
    ( r1_xboole_0(k2_relat_1(sK8),sK7)
    | r2_hidden(sK1(k2_relat_1(sK8),sK7),sK7) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_6,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1709,plain,
    ( r1_xboole_0(k2_relat_1(sK8),sK7)
    | r2_hidden(sK1(k2_relat_1(sK8),sK7),k2_relat_1(sK8)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1034,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1009])).

cnf(c_10,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_94,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_31,negated_conjecture,
    ( ~ r1_xboole_0(k2_relat_1(sK8),sK7)
    | k1_xboole_0 != k10_relat_1(sK8,sK7) ),
    inference(cnf_transformation,[],[f98])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8085,c_8066,c_4664,c_4086,c_3137,c_2207,c_1874,c_1784,c_1708,c_1709,c_1034,c_94,c_89,c_31])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:02:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.32/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.32/0.97  
% 3.32/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.32/0.97  
% 3.32/0.97  ------  iProver source info
% 3.32/0.97  
% 3.32/0.97  git: date: 2020-06-30 10:37:57 +0100
% 3.32/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.32/0.97  git: non_committed_changes: false
% 3.32/0.97  git: last_make_outside_of_git: false
% 3.32/0.97  
% 3.32/0.97  ------ 
% 3.32/0.97  
% 3.32/0.97  ------ Input Options
% 3.32/0.97  
% 3.32/0.97  --out_options                           all
% 3.32/0.97  --tptp_safe_out                         true
% 3.32/0.97  --problem_path                          ""
% 3.32/0.97  --include_path                          ""
% 3.32/0.97  --clausifier                            res/vclausify_rel
% 3.32/0.97  --clausifier_options                    ""
% 3.32/0.97  --stdin                                 false
% 3.32/0.97  --stats_out                             all
% 3.32/0.97  
% 3.32/0.97  ------ General Options
% 3.32/0.97  
% 3.32/0.97  --fof                                   false
% 3.32/0.97  --time_out_real                         305.
% 3.32/0.97  --time_out_virtual                      -1.
% 3.32/0.97  --symbol_type_check                     false
% 3.32/0.97  --clausify_out                          false
% 3.32/0.97  --sig_cnt_out                           false
% 3.32/0.97  --trig_cnt_out                          false
% 3.32/0.97  --trig_cnt_out_tolerance                1.
% 3.32/0.97  --trig_cnt_out_sk_spl                   false
% 3.32/0.97  --abstr_cl_out                          false
% 3.32/0.97  
% 3.32/0.97  ------ Global Options
% 3.32/0.97  
% 3.32/0.97  --schedule                              default
% 3.32/0.97  --add_important_lit                     false
% 3.32/0.97  --prop_solver_per_cl                    1000
% 3.32/0.97  --min_unsat_core                        false
% 3.32/0.97  --soft_assumptions                      false
% 3.32/0.97  --soft_lemma_size                       3
% 3.32/0.97  --prop_impl_unit_size                   0
% 3.32/0.97  --prop_impl_unit                        []
% 3.32/0.97  --share_sel_clauses                     true
% 3.32/0.97  --reset_solvers                         false
% 3.32/0.97  --bc_imp_inh                            [conj_cone]
% 3.32/0.97  --conj_cone_tolerance                   3.
% 3.32/0.97  --extra_neg_conj                        none
% 3.32/0.97  --large_theory_mode                     true
% 3.32/0.97  --prolific_symb_bound                   200
% 3.32/0.97  --lt_threshold                          2000
% 3.32/0.97  --clause_weak_htbl                      true
% 3.32/0.97  --gc_record_bc_elim                     false
% 3.32/0.97  
% 3.32/0.97  ------ Preprocessing Options
% 3.32/0.97  
% 3.32/0.97  --preprocessing_flag                    true
% 3.32/0.97  --time_out_prep_mult                    0.1
% 3.32/0.97  --splitting_mode                        input
% 3.32/0.97  --splitting_grd                         true
% 3.32/0.97  --splitting_cvd                         false
% 3.32/0.97  --splitting_cvd_svl                     false
% 3.32/0.97  --splitting_nvd                         32
% 3.32/0.97  --sub_typing                            true
% 3.32/0.97  --prep_gs_sim                           true
% 3.32/0.97  --prep_unflatten                        true
% 3.32/0.97  --prep_res_sim                          true
% 3.32/0.97  --prep_upred                            true
% 3.32/0.97  --prep_sem_filter                       exhaustive
% 3.32/0.97  --prep_sem_filter_out                   false
% 3.32/0.97  --pred_elim                             true
% 3.32/0.97  --res_sim_input                         true
% 3.32/0.97  --eq_ax_congr_red                       true
% 3.32/0.97  --pure_diseq_elim                       true
% 3.32/0.97  --brand_transform                       false
% 3.32/0.97  --non_eq_to_eq                          false
% 3.32/0.97  --prep_def_merge                        true
% 3.32/0.97  --prep_def_merge_prop_impl              false
% 3.32/0.97  --prep_def_merge_mbd                    true
% 3.32/0.97  --prep_def_merge_tr_red                 false
% 3.32/0.97  --prep_def_merge_tr_cl                  false
% 3.32/0.97  --smt_preprocessing                     true
% 3.32/0.97  --smt_ac_axioms                         fast
% 3.32/0.97  --preprocessed_out                      false
% 3.32/0.97  --preprocessed_stats                    false
% 3.32/0.97  
% 3.32/0.97  ------ Abstraction refinement Options
% 3.32/0.97  
% 3.32/0.97  --abstr_ref                             []
% 3.32/0.97  --abstr_ref_prep                        false
% 3.32/0.97  --abstr_ref_until_sat                   false
% 3.32/0.97  --abstr_ref_sig_restrict                funpre
% 3.32/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 3.32/0.97  --abstr_ref_under                       []
% 3.32/0.97  
% 3.32/0.97  ------ SAT Options
% 3.32/0.97  
% 3.32/0.97  --sat_mode                              false
% 3.32/0.97  --sat_fm_restart_options                ""
% 3.32/0.97  --sat_gr_def                            false
% 3.32/0.97  --sat_epr_types                         true
% 3.32/0.97  --sat_non_cyclic_types                  false
% 3.32/0.97  --sat_finite_models                     false
% 3.32/0.97  --sat_fm_lemmas                         false
% 3.32/0.97  --sat_fm_prep                           false
% 3.32/0.97  --sat_fm_uc_incr                        true
% 3.32/0.97  --sat_out_model                         small
% 3.32/0.97  --sat_out_clauses                       false
% 3.32/0.97  
% 3.32/0.97  ------ QBF Options
% 3.32/0.97  
% 3.32/0.97  --qbf_mode                              false
% 3.32/0.97  --qbf_elim_univ                         false
% 3.32/0.97  --qbf_dom_inst                          none
% 3.32/0.97  --qbf_dom_pre_inst                      false
% 3.32/0.97  --qbf_sk_in                             false
% 3.32/0.97  --qbf_pred_elim                         true
% 3.32/0.97  --qbf_split                             512
% 3.32/0.97  
% 3.32/0.97  ------ BMC1 Options
% 3.32/0.97  
% 3.32/0.97  --bmc1_incremental                      false
% 3.32/0.97  --bmc1_axioms                           reachable_all
% 3.32/0.97  --bmc1_min_bound                        0
% 3.32/0.97  --bmc1_max_bound                        -1
% 3.32/0.97  --bmc1_max_bound_default                -1
% 3.32/0.97  --bmc1_symbol_reachability              true
% 3.32/0.97  --bmc1_property_lemmas                  false
% 3.32/0.97  --bmc1_k_induction                      false
% 3.32/0.97  --bmc1_non_equiv_states                 false
% 3.32/0.97  --bmc1_deadlock                         false
% 3.32/0.97  --bmc1_ucm                              false
% 3.32/0.97  --bmc1_add_unsat_core                   none
% 3.32/0.97  --bmc1_unsat_core_children              false
% 3.32/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 3.32/0.97  --bmc1_out_stat                         full
% 3.32/0.97  --bmc1_ground_init                      false
% 3.32/0.97  --bmc1_pre_inst_next_state              false
% 3.32/0.97  --bmc1_pre_inst_state                   false
% 3.32/0.97  --bmc1_pre_inst_reach_state             false
% 3.32/0.97  --bmc1_out_unsat_core                   false
% 3.32/0.97  --bmc1_aig_witness_out                  false
% 3.32/0.97  --bmc1_verbose                          false
% 3.32/0.97  --bmc1_dump_clauses_tptp                false
% 3.32/0.97  --bmc1_dump_unsat_core_tptp             false
% 3.32/0.97  --bmc1_dump_file                        -
% 3.32/0.97  --bmc1_ucm_expand_uc_limit              128
% 3.32/0.97  --bmc1_ucm_n_expand_iterations          6
% 3.32/0.97  --bmc1_ucm_extend_mode                  1
% 3.32/0.97  --bmc1_ucm_init_mode                    2
% 3.32/0.97  --bmc1_ucm_cone_mode                    none
% 3.32/0.97  --bmc1_ucm_reduced_relation_type        0
% 3.32/0.97  --bmc1_ucm_relax_model                  4
% 3.32/0.97  --bmc1_ucm_full_tr_after_sat            true
% 3.32/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 3.32/0.97  --bmc1_ucm_layered_model                none
% 3.32/0.97  --bmc1_ucm_max_lemma_size               10
% 3.32/0.97  
% 3.32/0.97  ------ AIG Options
% 3.32/0.97  
% 3.32/0.97  --aig_mode                              false
% 3.32/0.97  
% 3.32/0.97  ------ Instantiation Options
% 3.32/0.97  
% 3.32/0.97  --instantiation_flag                    true
% 3.32/0.97  --inst_sos_flag                         true
% 3.32/0.97  --inst_sos_phase                        true
% 3.32/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.32/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.32/0.97  --inst_lit_sel_side                     num_symb
% 3.32/0.97  --inst_solver_per_active                1400
% 3.32/0.97  --inst_solver_calls_frac                1.
% 3.32/0.97  --inst_passive_queue_type               priority_queues
% 3.32/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.32/0.97  --inst_passive_queues_freq              [25;2]
% 3.32/0.97  --inst_dismatching                      true
% 3.32/0.97  --inst_eager_unprocessed_to_passive     true
% 3.32/0.97  --inst_prop_sim_given                   true
% 3.32/0.97  --inst_prop_sim_new                     false
% 3.32/0.97  --inst_subs_new                         false
% 3.32/0.97  --inst_eq_res_simp                      false
% 3.32/0.97  --inst_subs_given                       false
% 3.32/0.97  --inst_orphan_elimination               true
% 3.32/0.97  --inst_learning_loop_flag               true
% 3.32/0.97  --inst_learning_start                   3000
% 3.32/0.97  --inst_learning_factor                  2
% 3.32/0.97  --inst_start_prop_sim_after_learn       3
% 3.32/0.97  --inst_sel_renew                        solver
% 3.32/0.97  --inst_lit_activity_flag                true
% 3.32/0.97  --inst_restr_to_given                   false
% 3.32/0.97  --inst_activity_threshold               500
% 3.32/0.97  --inst_out_proof                        true
% 3.32/0.97  
% 3.32/0.97  ------ Resolution Options
% 3.32/0.97  
% 3.32/0.97  --resolution_flag                       true
% 3.32/0.97  --res_lit_sel                           adaptive
% 3.32/0.97  --res_lit_sel_side                      none
% 3.32/0.97  --res_ordering                          kbo
% 3.32/0.97  --res_to_prop_solver                    active
% 3.32/0.97  --res_prop_simpl_new                    false
% 3.32/0.97  --res_prop_simpl_given                  true
% 3.32/0.97  --res_passive_queue_type                priority_queues
% 3.32/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.32/0.97  --res_passive_queues_freq               [15;5]
% 3.32/0.97  --res_forward_subs                      full
% 3.32/0.97  --res_backward_subs                     full
% 3.32/0.97  --res_forward_subs_resolution           true
% 3.32/0.97  --res_backward_subs_resolution          true
% 3.32/0.97  --res_orphan_elimination                true
% 3.32/0.97  --res_time_limit                        2.
% 3.32/0.97  --res_out_proof                         true
% 3.32/0.97  
% 3.32/0.97  ------ Superposition Options
% 3.32/0.97  
% 3.32/0.97  --superposition_flag                    true
% 3.32/0.97  --sup_passive_queue_type                priority_queues
% 3.32/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.32/0.97  --sup_passive_queues_freq               [8;1;4]
% 3.32/0.97  --demod_completeness_check              fast
% 3.32/0.97  --demod_use_ground                      true
% 3.32/0.97  --sup_to_prop_solver                    passive
% 3.32/0.97  --sup_prop_simpl_new                    true
% 3.32/0.97  --sup_prop_simpl_given                  true
% 3.32/0.97  --sup_fun_splitting                     true
% 3.32/0.97  --sup_smt_interval                      50000
% 3.32/0.97  
% 3.32/0.97  ------ Superposition Simplification Setup
% 3.32/0.97  
% 3.32/0.97  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.32/0.97  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.32/0.97  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.32/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.32/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 3.32/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.32/0.97  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.32/0.97  --sup_immed_triv                        [TrivRules]
% 3.32/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.32/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.32/0.97  --sup_immed_bw_main                     []
% 3.32/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.32/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 3.32/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.32/0.97  --sup_input_bw                          []
% 3.32/0.97  
% 3.32/0.97  ------ Combination Options
% 3.32/0.97  
% 3.32/0.97  --comb_res_mult                         3
% 3.32/0.97  --comb_sup_mult                         2
% 3.32/0.97  --comb_inst_mult                        10
% 3.32/0.97  
% 3.32/0.97  ------ Debug Options
% 3.32/0.97  
% 3.32/0.97  --dbg_backtrace                         false
% 3.32/0.97  --dbg_dump_prop_clauses                 false
% 3.32/0.97  --dbg_dump_prop_clauses_file            -
% 3.32/0.97  --dbg_out_stat                          false
% 3.32/0.97  ------ Parsing...
% 3.32/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.32/0.97  
% 3.32/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.32/0.97  
% 3.32/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.32/0.97  
% 3.32/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.32/0.97  ------ Proving...
% 3.32/0.97  ------ Problem Properties 
% 3.32/0.97  
% 3.32/0.97  
% 3.32/0.97  clauses                                 33
% 3.32/0.97  conjectures                             2
% 3.32/0.97  EPR                                     5
% 3.32/0.97  Horn                                    26
% 3.32/0.97  unary                                   9
% 3.32/0.97  binary                                  16
% 3.32/0.97  lits                                    66
% 3.32/0.97  lits eq                                 14
% 3.32/0.97  fd_pure                                 0
% 3.32/0.97  fd_pseudo                               0
% 3.32/0.97  fd_cond                                 0
% 3.32/0.97  fd_pseudo_cond                          3
% 3.32/0.97  AC symbols                              0
% 3.32/0.97  
% 3.32/0.97  ------ Schedule dynamic 5 is on 
% 3.32/0.97  
% 3.32/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.32/0.97  
% 3.32/0.97  
% 3.32/0.97  ------ 
% 3.32/0.97  Current options:
% 3.32/0.97  ------ 
% 3.32/0.97  
% 3.32/0.97  ------ Input Options
% 3.32/0.97  
% 3.32/0.97  --out_options                           all
% 3.32/0.97  --tptp_safe_out                         true
% 3.32/0.97  --problem_path                          ""
% 3.32/0.97  --include_path                          ""
% 3.32/0.97  --clausifier                            res/vclausify_rel
% 3.32/0.97  --clausifier_options                    ""
% 3.32/0.97  --stdin                                 false
% 3.32/0.97  --stats_out                             all
% 3.32/0.97  
% 3.32/0.97  ------ General Options
% 3.32/0.97  
% 3.32/0.97  --fof                                   false
% 3.32/0.97  --time_out_real                         305.
% 3.32/0.97  --time_out_virtual                      -1.
% 3.32/0.97  --symbol_type_check                     false
% 3.32/0.97  --clausify_out                          false
% 3.32/0.97  --sig_cnt_out                           false
% 3.32/0.97  --trig_cnt_out                          false
% 3.32/0.97  --trig_cnt_out_tolerance                1.
% 3.32/0.97  --trig_cnt_out_sk_spl                   false
% 3.32/0.97  --abstr_cl_out                          false
% 3.32/0.97  
% 3.32/0.97  ------ Global Options
% 3.32/0.97  
% 3.32/0.97  --schedule                              default
% 3.32/0.97  --add_important_lit                     false
% 3.32/0.97  --prop_solver_per_cl                    1000
% 3.32/0.97  --min_unsat_core                        false
% 3.32/0.97  --soft_assumptions                      false
% 3.32/0.97  --soft_lemma_size                       3
% 3.32/0.97  --prop_impl_unit_size                   0
% 3.32/0.97  --prop_impl_unit                        []
% 3.32/0.97  --share_sel_clauses                     true
% 3.32/0.97  --reset_solvers                         false
% 3.32/0.97  --bc_imp_inh                            [conj_cone]
% 3.32/0.97  --conj_cone_tolerance                   3.
% 3.32/0.97  --extra_neg_conj                        none
% 3.32/0.97  --large_theory_mode                     true
% 3.32/0.97  --prolific_symb_bound                   200
% 3.32/0.97  --lt_threshold                          2000
% 3.32/0.97  --clause_weak_htbl                      true
% 3.32/0.97  --gc_record_bc_elim                     false
% 3.32/0.97  
% 3.32/0.97  ------ Preprocessing Options
% 3.32/0.97  
% 3.32/0.97  --preprocessing_flag                    true
% 3.32/0.97  --time_out_prep_mult                    0.1
% 3.32/0.97  --splitting_mode                        input
% 3.32/0.97  --splitting_grd                         true
% 3.32/0.97  --splitting_cvd                         false
% 3.32/0.97  --splitting_cvd_svl                     false
% 3.32/0.97  --splitting_nvd                         32
% 3.32/0.97  --sub_typing                            true
% 3.32/0.97  --prep_gs_sim                           true
% 3.32/0.97  --prep_unflatten                        true
% 3.32/0.97  --prep_res_sim                          true
% 3.32/0.97  --prep_upred                            true
% 3.32/0.97  --prep_sem_filter                       exhaustive
% 3.32/0.97  --prep_sem_filter_out                   false
% 3.32/0.97  --pred_elim                             true
% 3.32/0.97  --res_sim_input                         true
% 3.32/0.97  --eq_ax_congr_red                       true
% 3.32/0.97  --pure_diseq_elim                       true
% 3.32/0.97  --brand_transform                       false
% 3.32/0.97  --non_eq_to_eq                          false
% 3.32/0.97  --prep_def_merge                        true
% 3.32/0.97  --prep_def_merge_prop_impl              false
% 3.32/0.97  --prep_def_merge_mbd                    true
% 3.32/0.97  --prep_def_merge_tr_red                 false
% 3.32/0.97  --prep_def_merge_tr_cl                  false
% 3.32/0.97  --smt_preprocessing                     true
% 3.32/0.97  --smt_ac_axioms                         fast
% 3.32/0.97  --preprocessed_out                      false
% 3.32/0.97  --preprocessed_stats                    false
% 3.32/0.97  
% 3.32/0.97  ------ Abstraction refinement Options
% 3.32/0.97  
% 3.32/0.97  --abstr_ref                             []
% 3.32/0.97  --abstr_ref_prep                        false
% 3.32/0.97  --abstr_ref_until_sat                   false
% 3.32/0.97  --abstr_ref_sig_restrict                funpre
% 3.32/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 3.32/0.97  --abstr_ref_under                       []
% 3.32/0.97  
% 3.32/0.97  ------ SAT Options
% 3.32/0.97  
% 3.32/0.97  --sat_mode                              false
% 3.32/0.97  --sat_fm_restart_options                ""
% 3.32/0.97  --sat_gr_def                            false
% 3.32/0.97  --sat_epr_types                         true
% 3.32/0.97  --sat_non_cyclic_types                  false
% 3.32/0.97  --sat_finite_models                     false
% 3.32/0.97  --sat_fm_lemmas                         false
% 3.32/0.97  --sat_fm_prep                           false
% 3.32/0.97  --sat_fm_uc_incr                        true
% 3.32/0.97  --sat_out_model                         small
% 3.32/0.97  --sat_out_clauses                       false
% 3.32/0.97  
% 3.32/0.97  ------ QBF Options
% 3.32/0.97  
% 3.32/0.97  --qbf_mode                              false
% 3.32/0.97  --qbf_elim_univ                         false
% 3.32/0.97  --qbf_dom_inst                          none
% 3.32/0.97  --qbf_dom_pre_inst                      false
% 3.32/0.97  --qbf_sk_in                             false
% 3.32/0.97  --qbf_pred_elim                         true
% 3.32/0.97  --qbf_split                             512
% 3.32/0.97  
% 3.32/0.97  ------ BMC1 Options
% 3.32/0.97  
% 3.32/0.97  --bmc1_incremental                      false
% 3.32/0.97  --bmc1_axioms                           reachable_all
% 3.32/0.97  --bmc1_min_bound                        0
% 3.32/0.97  --bmc1_max_bound                        -1
% 3.32/0.97  --bmc1_max_bound_default                -1
% 3.32/0.97  --bmc1_symbol_reachability              true
% 3.32/0.97  --bmc1_property_lemmas                  false
% 3.32/0.97  --bmc1_k_induction                      false
% 3.32/0.97  --bmc1_non_equiv_states                 false
% 3.32/0.97  --bmc1_deadlock                         false
% 3.32/0.97  --bmc1_ucm                              false
% 3.32/0.97  --bmc1_add_unsat_core                   none
% 3.32/0.97  --bmc1_unsat_core_children              false
% 3.32/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 3.32/0.97  --bmc1_out_stat                         full
% 3.32/0.97  --bmc1_ground_init                      false
% 3.32/0.97  --bmc1_pre_inst_next_state              false
% 3.32/0.97  --bmc1_pre_inst_state                   false
% 3.32/0.97  --bmc1_pre_inst_reach_state             false
% 3.32/0.97  --bmc1_out_unsat_core                   false
% 3.32/0.97  --bmc1_aig_witness_out                  false
% 3.32/0.97  --bmc1_verbose                          false
% 3.32/0.97  --bmc1_dump_clauses_tptp                false
% 3.32/0.97  --bmc1_dump_unsat_core_tptp             false
% 3.32/0.97  --bmc1_dump_file                        -
% 3.32/0.97  --bmc1_ucm_expand_uc_limit              128
% 3.32/0.97  --bmc1_ucm_n_expand_iterations          6
% 3.32/0.97  --bmc1_ucm_extend_mode                  1
% 3.32/0.97  --bmc1_ucm_init_mode                    2
% 3.32/0.97  --bmc1_ucm_cone_mode                    none
% 3.32/0.97  --bmc1_ucm_reduced_relation_type        0
% 3.32/0.97  --bmc1_ucm_relax_model                  4
% 3.32/0.97  --bmc1_ucm_full_tr_after_sat            true
% 3.32/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 3.32/0.97  --bmc1_ucm_layered_model                none
% 3.32/0.97  --bmc1_ucm_max_lemma_size               10
% 3.32/0.97  
% 3.32/0.97  ------ AIG Options
% 3.32/0.97  
% 3.32/0.97  --aig_mode                              false
% 3.32/0.97  
% 3.32/0.97  ------ Instantiation Options
% 3.32/0.97  
% 3.32/0.97  --instantiation_flag                    true
% 3.32/0.97  --inst_sos_flag                         true
% 3.32/0.97  --inst_sos_phase                        true
% 3.32/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.32/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.32/0.97  --inst_lit_sel_side                     none
% 3.32/0.97  --inst_solver_per_active                1400
% 3.32/0.97  --inst_solver_calls_frac                1.
% 3.32/0.97  --inst_passive_queue_type               priority_queues
% 3.32/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.32/0.97  --inst_passive_queues_freq              [25;2]
% 3.32/0.97  --inst_dismatching                      true
% 3.32/0.97  --inst_eager_unprocessed_to_passive     true
% 3.32/0.97  --inst_prop_sim_given                   true
% 3.32/0.97  --inst_prop_sim_new                     false
% 3.32/0.97  --inst_subs_new                         false
% 3.32/0.97  --inst_eq_res_simp                      false
% 3.32/0.97  --inst_subs_given                       false
% 3.32/0.97  --inst_orphan_elimination               true
% 3.32/0.97  --inst_learning_loop_flag               true
% 3.32/0.97  --inst_learning_start                   3000
% 3.32/0.97  --inst_learning_factor                  2
% 3.32/0.97  --inst_start_prop_sim_after_learn       3
% 3.32/0.97  --inst_sel_renew                        solver
% 3.32/0.97  --inst_lit_activity_flag                true
% 3.32/0.97  --inst_restr_to_given                   false
% 3.32/0.97  --inst_activity_threshold               500
% 3.32/0.97  --inst_out_proof                        true
% 3.32/0.97  
% 3.32/0.97  ------ Resolution Options
% 3.32/0.97  
% 3.32/0.97  --resolution_flag                       false
% 3.32/0.97  --res_lit_sel                           adaptive
% 3.32/0.97  --res_lit_sel_side                      none
% 3.32/0.97  --res_ordering                          kbo
% 3.32/0.97  --res_to_prop_solver                    active
% 3.32/0.97  --res_prop_simpl_new                    false
% 3.32/0.97  --res_prop_simpl_given                  true
% 3.32/0.97  --res_passive_queue_type                priority_queues
% 3.32/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.32/0.97  --res_passive_queues_freq               [15;5]
% 3.32/0.97  --res_forward_subs                      full
% 3.32/0.97  --res_backward_subs                     full
% 3.32/0.97  --res_forward_subs_resolution           true
% 3.32/0.97  --res_backward_subs_resolution          true
% 3.32/0.97  --res_orphan_elimination                true
% 3.32/0.97  --res_time_limit                        2.
% 3.32/0.97  --res_out_proof                         true
% 3.32/0.97  
% 3.32/0.97  ------ Superposition Options
% 3.32/0.97  
% 3.32/0.97  --superposition_flag                    true
% 3.32/0.97  --sup_passive_queue_type                priority_queues
% 3.32/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.32/0.97  --sup_passive_queues_freq               [8;1;4]
% 3.32/0.97  --demod_completeness_check              fast
% 3.32/0.97  --demod_use_ground                      true
% 3.32/0.97  --sup_to_prop_solver                    passive
% 3.32/0.97  --sup_prop_simpl_new                    true
% 3.32/0.97  --sup_prop_simpl_given                  true
% 3.32/0.97  --sup_fun_splitting                     true
% 3.32/0.97  --sup_smt_interval                      50000
% 3.32/0.97  
% 3.32/0.97  ------ Superposition Simplification Setup
% 3.32/0.97  
% 3.32/0.97  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.32/0.97  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.32/0.97  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.32/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.32/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 3.32/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.32/0.97  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.32/0.97  --sup_immed_triv                        [TrivRules]
% 3.32/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.32/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.32/0.97  --sup_immed_bw_main                     []
% 3.32/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.32/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 3.32/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.32/0.97  --sup_input_bw                          []
% 3.32/0.97  
% 3.32/0.97  ------ Combination Options
% 3.32/0.97  
% 3.32/0.97  --comb_res_mult                         3
% 3.32/0.97  --comb_sup_mult                         2
% 3.32/0.97  --comb_inst_mult                        10
% 3.32/0.97  
% 3.32/0.97  ------ Debug Options
% 3.32/0.97  
% 3.32/0.97  --dbg_backtrace                         false
% 3.32/0.97  --dbg_dump_prop_clauses                 false
% 3.32/0.97  --dbg_dump_prop_clauses_file            -
% 3.32/0.97  --dbg_out_stat                          false
% 3.32/0.97  
% 3.32/0.97  
% 3.32/0.97  
% 3.32/0.97  
% 3.32/0.97  ------ Proving...
% 3.32/0.97  
% 3.32/0.97  
% 3.32/0.97  % SZS status Theorem for theBenchmark.p
% 3.32/0.97  
% 3.32/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 3.32/0.97  
% 3.32/0.97  fof(f2,axiom,(
% 3.32/0.97    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.32/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.32/0.97  
% 3.32/0.97  fof(f24,plain,(
% 3.32/0.97    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.32/0.97    inference(rectify,[],[f2])).
% 3.32/0.97  
% 3.32/0.97  fof(f27,plain,(
% 3.32/0.97    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 3.32/0.97    inference(ennf_transformation,[],[f24])).
% 3.32/0.97  
% 3.32/0.97  fof(f44,plain,(
% 3.32/0.97    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 3.32/0.97    introduced(choice_axiom,[])).
% 3.32/0.97  
% 3.32/0.97  fof(f45,plain,(
% 3.32/0.97    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 3.32/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f44])).
% 3.32/0.97  
% 3.32/0.97  fof(f68,plain,(
% 3.32/0.97    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 3.32/0.97    inference(cnf_transformation,[],[f45])).
% 3.32/0.97  
% 3.32/0.97  fof(f1,axiom,(
% 3.32/0.97    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.32/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.32/0.97  
% 3.32/0.97  fof(f26,plain,(
% 3.32/0.97    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.32/0.97    inference(ennf_transformation,[],[f1])).
% 3.32/0.97  
% 3.32/0.97  fof(f40,plain,(
% 3.32/0.97    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.32/0.97    inference(nnf_transformation,[],[f26])).
% 3.32/0.97  
% 3.32/0.97  fof(f41,plain,(
% 3.32/0.97    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.32/0.97    inference(rectify,[],[f40])).
% 3.32/0.97  
% 3.32/0.97  fof(f42,plain,(
% 3.32/0.97    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.32/0.97    introduced(choice_axiom,[])).
% 3.32/0.97  
% 3.32/0.97  fof(f43,plain,(
% 3.32/0.97    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.32/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f41,f42])).
% 3.32/0.97  
% 3.32/0.97  fof(f63,plain,(
% 3.32/0.97    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.32/0.97    inference(cnf_transformation,[],[f43])).
% 3.32/0.97  
% 3.32/0.97  fof(f22,conjecture,(
% 3.32/0.97    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 3.32/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.32/0.97  
% 3.32/0.97  fof(f23,negated_conjecture,(
% 3.32/0.97    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 3.32/0.97    inference(negated_conjecture,[],[f22])).
% 3.32/0.97  
% 3.32/0.97  fof(f39,plain,(
% 3.32/0.97    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <~> r1_xboole_0(k2_relat_1(X1),X0)) & v1_relat_1(X1))),
% 3.32/0.97    inference(ennf_transformation,[],[f23])).
% 3.32/0.97  
% 3.32/0.97  fof(f59,plain,(
% 3.32/0.97    ? [X0,X1] : (((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0))) & v1_relat_1(X1))),
% 3.32/0.97    inference(nnf_transformation,[],[f39])).
% 3.32/0.97  
% 3.32/0.97  fof(f60,plain,(
% 3.32/0.97    ? [X0,X1] : ((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) & v1_relat_1(X1))),
% 3.32/0.97    inference(flattening,[],[f59])).
% 3.32/0.97  
% 3.32/0.97  fof(f61,plain,(
% 3.32/0.97    ? [X0,X1] : ((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) & v1_relat_1(X1)) => ((~r1_xboole_0(k2_relat_1(sK8),sK7) | k1_xboole_0 != k10_relat_1(sK8,sK7)) & (r1_xboole_0(k2_relat_1(sK8),sK7) | k1_xboole_0 = k10_relat_1(sK8,sK7)) & v1_relat_1(sK8))),
% 3.32/0.97    introduced(choice_axiom,[])).
% 3.32/0.97  
% 3.32/0.97  fof(f62,plain,(
% 3.32/0.97    (~r1_xboole_0(k2_relat_1(sK8),sK7) | k1_xboole_0 != k10_relat_1(sK8,sK7)) & (r1_xboole_0(k2_relat_1(sK8),sK7) | k1_xboole_0 = k10_relat_1(sK8,sK7)) & v1_relat_1(sK8)),
% 3.32/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f60,f61])).
% 3.32/0.97  
% 3.32/0.97  fof(f97,plain,(
% 3.32/0.97    r1_xboole_0(k2_relat_1(sK8),sK7) | k1_xboole_0 = k10_relat_1(sK8,sK7)),
% 3.32/0.97    inference(cnf_transformation,[],[f62])).
% 3.32/0.97  
% 3.32/0.97  fof(f12,axiom,(
% 3.32/0.97    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0)),
% 3.32/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.32/0.97  
% 3.32/0.97  fof(f33,plain,(
% 3.32/0.97    ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 | ~r1_xboole_0(X0,X1))),
% 3.32/0.97    inference(ennf_transformation,[],[f12])).
% 3.32/0.97  
% 3.32/0.97  fof(f80,plain,(
% 3.32/0.97    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 3.32/0.97    inference(cnf_transformation,[],[f33])).
% 3.32/0.97  
% 3.32/0.97  fof(f9,axiom,(
% 3.32/0.97    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 3.32/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.32/0.97  
% 3.32/0.97  fof(f76,plain,(
% 3.32/0.97    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 3.32/0.97    inference(cnf_transformation,[],[f9])).
% 3.32/0.97  
% 3.32/0.97  fof(f10,axiom,(
% 3.32/0.97    ! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 3.32/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.32/0.97  
% 3.32/0.97  fof(f31,plain,(
% 3.32/0.97    ! [X0,X1,X2,X3] : (X1 = X2 | (~r1_xboole_0(X3,X1) | ~r1_xboole_0(X2,X0) | k2_xboole_0(X0,X1) != k2_xboole_0(X2,X3)))),
% 3.32/0.97    inference(ennf_transformation,[],[f10])).
% 3.32/0.97  
% 3.32/0.97  fof(f32,plain,(
% 3.32/0.97    ! [X0,X1,X2,X3] : (X1 = X2 | ~r1_xboole_0(X3,X1) | ~r1_xboole_0(X2,X0) | k2_xboole_0(X0,X1) != k2_xboole_0(X2,X3))),
% 3.32/0.97    inference(flattening,[],[f31])).
% 3.32/0.97  
% 3.32/0.97  fof(f77,plain,(
% 3.32/0.97    ( ! [X2,X0,X3,X1] : (X1 = X2 | ~r1_xboole_0(X3,X1) | ~r1_xboole_0(X2,X0) | k2_xboole_0(X0,X1) != k2_xboole_0(X2,X3)) )),
% 3.32/0.97    inference(cnf_transformation,[],[f32])).
% 3.32/0.97  
% 3.32/0.97  fof(f67,plain,(
% 3.32/0.97    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 3.32/0.97    inference(cnf_transformation,[],[f45])).
% 3.32/0.97  
% 3.32/0.97  fof(f11,axiom,(
% 3.32/0.97    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 3.32/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.32/0.97  
% 3.32/0.97  fof(f48,plain,(
% 3.32/0.97    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 3.32/0.97    inference(nnf_transformation,[],[f11])).
% 3.32/0.97  
% 3.32/0.97  fof(f78,plain,(
% 3.32/0.97    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 3.32/0.97    inference(cnf_transformation,[],[f48])).
% 3.32/0.97  
% 3.32/0.97  fof(f79,plain,(
% 3.32/0.97    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 3.32/0.97    inference(cnf_transformation,[],[f48])).
% 3.32/0.97  
% 3.32/0.97  fof(f18,axiom,(
% 3.32/0.97    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 3.32/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.32/0.97  
% 3.32/0.97  fof(f35,plain,(
% 3.32/0.97    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 3.32/0.97    inference(ennf_transformation,[],[f18])).
% 3.32/0.97  
% 3.32/0.97  fof(f55,plain,(
% 3.32/0.97    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.32/0.97    inference(nnf_transformation,[],[f35])).
% 3.32/0.97  
% 3.32/0.97  fof(f56,plain,(
% 3.32/0.97    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.32/0.97    inference(rectify,[],[f55])).
% 3.32/0.97  
% 3.32/0.97  fof(f57,plain,(
% 3.32/0.97    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) => (r2_hidden(sK6(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK6(X0,X1,X2)),X2) & r2_hidden(sK6(X0,X1,X2),k2_relat_1(X2))))),
% 3.32/0.97    introduced(choice_axiom,[])).
% 3.32/0.97  
% 3.32/0.97  fof(f58,plain,(
% 3.32/0.97    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & ((r2_hidden(sK6(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK6(X0,X1,X2)),X2) & r2_hidden(sK6(X0,X1,X2),k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.32/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f56,f57])).
% 3.32/0.97  
% 3.32/0.97  fof(f89,plain,(
% 3.32/0.97    ( ! [X2,X0,X1] : (r2_hidden(sK6(X0,X1,X2),k2_relat_1(X2)) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.32/0.97    inference(cnf_transformation,[],[f58])).
% 3.32/0.97  
% 3.32/0.97  fof(f96,plain,(
% 3.32/0.97    v1_relat_1(sK8)),
% 3.32/0.97    inference(cnf_transformation,[],[f62])).
% 3.32/0.97  
% 3.32/0.97  fof(f91,plain,(
% 3.32/0.97    ( ! [X2,X0,X1] : (r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.32/0.97    inference(cnf_transformation,[],[f58])).
% 3.32/0.97  
% 3.32/0.97  fof(f92,plain,(
% 3.32/0.97    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,k10_relat_1(X2,X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 3.32/0.97    inference(cnf_transformation,[],[f58])).
% 3.32/0.97  
% 3.32/0.97  fof(f17,axiom,(
% 3.32/0.97    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 3.32/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.32/0.97  
% 3.32/0.97  fof(f49,plain,(
% 3.32/0.97    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 3.32/0.97    inference(nnf_transformation,[],[f17])).
% 3.32/0.97  
% 3.32/0.97  fof(f50,plain,(
% 3.32/0.97    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 3.32/0.97    inference(rectify,[],[f49])).
% 3.32/0.97  
% 3.32/0.97  fof(f53,plain,(
% 3.32/0.97    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK5(X0,X5),X5),X0))),
% 3.32/0.97    introduced(choice_axiom,[])).
% 3.32/0.97  
% 3.32/0.97  fof(f52,plain,(
% 3.32/0.97    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) => r2_hidden(k4_tarski(sK4(X0,X1),X2),X0))) )),
% 3.32/0.97    introduced(choice_axiom,[])).
% 3.32/0.97  
% 3.32/0.97  fof(f51,plain,(
% 3.32/0.97    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 3.32/0.98    introduced(choice_axiom,[])).
% 3.32/0.98  
% 3.32/0.98  fof(f54,plain,(
% 3.32/0.98    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK5(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 3.32/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f50,f53,f52,f51])).
% 3.32/0.98  
% 3.32/0.98  fof(f86,plain,(
% 3.32/0.98    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X6,X5),X0) | k2_relat_1(X0) != X1) )),
% 3.32/0.98    inference(cnf_transformation,[],[f54])).
% 3.32/0.98  
% 3.32/0.98  fof(f104,plain,(
% 3.32/0.98    ( ! [X6,X0,X5] : (r2_hidden(X5,k2_relat_1(X0)) | ~r2_hidden(k4_tarski(X6,X5),X0)) )),
% 3.32/0.98    inference(equality_resolution,[],[f86])).
% 3.32/0.98  
% 3.32/0.98  fof(f85,plain,(
% 3.32/0.98    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK5(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 3.32/0.98    inference(cnf_transformation,[],[f54])).
% 3.32/0.98  
% 3.32/0.98  fof(f105,plain,(
% 3.32/0.98    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK5(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 3.32/0.98    inference(equality_resolution,[],[f85])).
% 3.32/0.98  
% 3.32/0.98  fof(f66,plain,(
% 3.32/0.98    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 3.32/0.98    inference(cnf_transformation,[],[f45])).
% 3.32/0.98  
% 3.32/0.98  fof(f5,axiom,(
% 3.32/0.98    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.32/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.32/0.98  
% 3.32/0.98  fof(f72,plain,(
% 3.32/0.98    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.32/0.98    inference(cnf_transformation,[],[f5])).
% 3.32/0.98  
% 3.32/0.98  fof(f98,plain,(
% 3.32/0.98    ~r1_xboole_0(k2_relat_1(sK8),sK7) | k1_xboole_0 != k10_relat_1(sK8,sK7)),
% 3.32/0.98    inference(cnf_transformation,[],[f62])).
% 3.32/0.98  
% 3.32/0.98  cnf(c_4,plain,
% 3.32/0.98      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,X1) | ~ r2_hidden(X2,X0) ),
% 3.32/0.98      inference(cnf_transformation,[],[f68]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_1918,plain,
% 3.32/0.98      ( ~ r1_xboole_0(X0,k10_relat_1(sK8,sK7))
% 3.32/0.98      | ~ r2_hidden(X1,X0)
% 3.32/0.98      | ~ r2_hidden(X1,k10_relat_1(sK8,sK7)) ),
% 3.32/0.98      inference(instantiation,[status(thm)],[c_4]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_8083,plain,
% 3.32/0.98      ( ~ r1_xboole_0(X0,k10_relat_1(sK8,sK7))
% 3.32/0.98      | ~ r2_hidden(sK5(sK8,sK1(k2_relat_1(sK8),sK7)),X0)
% 3.32/0.98      | ~ r2_hidden(sK5(sK8,sK1(k2_relat_1(sK8),sK7)),k10_relat_1(sK8,sK7)) ),
% 3.32/0.98      inference(instantiation,[status(thm)],[c_1918]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_8085,plain,
% 3.32/0.98      ( ~ r1_xboole_0(k1_xboole_0,k10_relat_1(sK8,sK7))
% 3.32/0.98      | ~ r2_hidden(sK5(sK8,sK1(k2_relat_1(sK8),sK7)),k10_relat_1(sK8,sK7))
% 3.32/0.98      | ~ r2_hidden(sK5(sK8,sK1(k2_relat_1(sK8),sK7)),k1_xboole_0) ),
% 3.32/0.98      inference(instantiation,[status(thm)],[c_8083]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_3,plain,
% 3.32/0.98      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 3.32/0.98      inference(cnf_transformation,[],[f63]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_8049,plain,
% 3.32/0.98      ( r2_hidden(sK5(sK8,sK1(k2_relat_1(sK8),sK7)),X0)
% 3.32/0.98      | ~ r2_hidden(sK5(sK8,sK1(k2_relat_1(sK8),sK7)),k10_relat_1(sK8,sK7))
% 3.32/0.98      | ~ r1_tarski(k10_relat_1(sK8,sK7),X0) ),
% 3.32/0.98      inference(instantiation,[status(thm)],[c_3]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_8066,plain,
% 3.32/0.98      ( ~ r2_hidden(sK5(sK8,sK1(k2_relat_1(sK8),sK7)),k10_relat_1(sK8,sK7))
% 3.32/0.98      | r2_hidden(sK5(sK8,sK1(k2_relat_1(sK8),sK7)),k1_xboole_0)
% 3.32/0.98      | ~ r1_tarski(k10_relat_1(sK8,sK7),k1_xboole_0) ),
% 3.32/0.98      inference(instantiation,[status(thm)],[c_8049]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_32,negated_conjecture,
% 3.32/0.98      ( r1_xboole_0(k2_relat_1(sK8),sK7)
% 3.32/0.98      | k1_xboole_0 = k10_relat_1(sK8,sK7) ),
% 3.32/0.98      inference(cnf_transformation,[],[f97]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_1648,plain,
% 3.32/0.98      ( k1_xboole_0 = k10_relat_1(sK8,sK7)
% 3.32/0.98      | r1_xboole_0(k2_relat_1(sK8),sK7) = iProver_top ),
% 3.32/0.98      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_17,plain,
% 3.32/0.98      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 ),
% 3.32/0.98      inference(cnf_transformation,[],[f80]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_1656,plain,
% 3.32/0.98      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0
% 3.32/0.98      | r1_xboole_0(X0,X1) != iProver_top ),
% 3.32/0.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_4152,plain,
% 3.32/0.98      ( k10_relat_1(sK8,sK7) = k1_xboole_0
% 3.32/0.98      | k4_xboole_0(k2_xboole_0(k2_relat_1(sK8),sK7),sK7) = k2_relat_1(sK8) ),
% 3.32/0.98      inference(superposition,[status(thm)],[c_1648,c_1656]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_13,plain,
% 3.32/0.98      ( r1_xboole_0(X0,k1_xboole_0) ),
% 3.32/0.98      inference(cnf_transformation,[],[f76]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_89,plain,
% 3.32/0.98      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 3.32/0.98      inference(instantiation,[status(thm)],[c_13]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_14,plain,
% 3.32/0.98      ( ~ r1_xboole_0(X0,X1)
% 3.32/0.98      | ~ r1_xboole_0(X2,X3)
% 3.32/0.98      | X2 = X1
% 3.32/0.98      | k2_xboole_0(X2,X0) != k2_xboole_0(X3,X1) ),
% 3.32/0.98      inference(cnf_transformation,[],[f77]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_1840,plain,
% 3.32/0.98      ( ~ r1_xboole_0(X0,X1)
% 3.32/0.98      | ~ r1_xboole_0(k10_relat_1(sK8,sK7),X2)
% 3.32/0.98      | k10_relat_1(sK8,sK7) = X1
% 3.32/0.98      | k2_xboole_0(k10_relat_1(sK8,sK7),X0) != k2_xboole_0(X2,X1) ),
% 3.32/0.98      inference(instantiation,[status(thm)],[c_14]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_2006,plain,
% 3.32/0.98      ( ~ r1_xboole_0(X0,X1)
% 3.32/0.98      | ~ r1_xboole_0(k10_relat_1(sK8,sK7),k10_relat_1(sK8,sK7))
% 3.32/0.98      | k10_relat_1(sK8,sK7) = X1
% 3.32/0.98      | k2_xboole_0(k10_relat_1(sK8,sK7),X0) != k2_xboole_0(k10_relat_1(sK8,sK7),X1) ),
% 3.32/0.98      inference(instantiation,[status(thm)],[c_1840]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_2012,plain,
% 3.32/0.98      ( ~ r1_xboole_0(k10_relat_1(sK8,sK7),k10_relat_1(sK8,sK7))
% 3.32/0.98      | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
% 3.32/0.98      | k10_relat_1(sK8,sK7) = k1_xboole_0
% 3.32/0.98      | k2_xboole_0(k10_relat_1(sK8,sK7),k1_xboole_0) != k2_xboole_0(k10_relat_1(sK8,sK7),k1_xboole_0) ),
% 3.32/0.98      inference(instantiation,[status(thm)],[c_2006]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_5,plain,
% 3.32/0.98      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X1) ),
% 3.32/0.98      inference(cnf_transformation,[],[f67]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_1851,plain,
% 3.32/0.98      ( r1_xboole_0(X0,k10_relat_1(sK8,sK7))
% 3.32/0.98      | r2_hidden(sK1(X0,k10_relat_1(sK8,sK7)),k10_relat_1(sK8,sK7)) ),
% 3.32/0.98      inference(instantiation,[status(thm)],[c_5]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_2010,plain,
% 3.32/0.98      ( r1_xboole_0(k10_relat_1(sK8,sK7),k10_relat_1(sK8,sK7))
% 3.32/0.98      | r2_hidden(sK1(k10_relat_1(sK8,sK7),k10_relat_1(sK8,sK7)),k10_relat_1(sK8,sK7)) ),
% 3.32/0.98      inference(instantiation,[status(thm)],[c_1851]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_1009,plain,( X0 = X0 ),theory(equality) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_2378,plain,
% 3.32/0.98      ( k2_xboole_0(k10_relat_1(sK8,sK7),X0) = k2_xboole_0(k10_relat_1(sK8,sK7),X0) ),
% 3.32/0.98      inference(instantiation,[status(thm)],[c_1009]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_2379,plain,
% 3.32/0.98      ( k2_xboole_0(k10_relat_1(sK8,sK7),k1_xboole_0) = k2_xboole_0(k10_relat_1(sK8,sK7),k1_xboole_0) ),
% 3.32/0.98      inference(instantiation,[status(thm)],[c_2378]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_16,plain,
% 3.32/0.98      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 3.32/0.98      inference(cnf_transformation,[],[f78]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_1657,plain,
% 3.32/0.98      ( k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1) != iProver_top ),
% 3.32/0.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_2631,plain,
% 3.32/0.98      ( k10_relat_1(sK8,sK7) = k1_xboole_0
% 3.32/0.98      | k4_xboole_0(k2_relat_1(sK8),sK7) = k2_relat_1(sK8) ),
% 3.32/0.98      inference(superposition,[status(thm)],[c_1648,c_1657]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_15,plain,
% 3.32/0.98      ( r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0 ),
% 3.32/0.98      inference(cnf_transformation,[],[f79]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_1658,plain,
% 3.32/0.98      ( k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1) = iProver_top ),
% 3.32/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_2753,plain,
% 3.32/0.98      ( k10_relat_1(sK8,sK7) = k1_xboole_0
% 3.32/0.98      | r1_xboole_0(k2_relat_1(sK8),sK7) = iProver_top ),
% 3.32/0.98      inference(superposition,[status(thm)],[c_2631,c_1658]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_2755,plain,
% 3.32/0.98      ( r1_xboole_0(k2_relat_1(sK8),sK7)
% 3.32/0.98      | k10_relat_1(sK8,sK7) = k1_xboole_0 ),
% 3.32/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_2753]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_27,plain,
% 3.32/0.98      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 3.32/0.98      | r2_hidden(sK6(X0,X2,X1),k2_relat_1(X1))
% 3.32/0.98      | ~ v1_relat_1(X1) ),
% 3.32/0.98      inference(cnf_transformation,[],[f89]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_33,negated_conjecture,
% 3.32/0.98      ( v1_relat_1(sK8) ),
% 3.32/0.98      inference(cnf_transformation,[],[f96]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_446,plain,
% 3.32/0.98      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 3.32/0.98      | r2_hidden(sK6(X0,X2,X1),k2_relat_1(X1))
% 3.32/0.98      | sK8 != X1 ),
% 3.32/0.98      inference(resolution_lifted,[status(thm)],[c_27,c_33]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_447,plain,
% 3.32/0.98      ( ~ r2_hidden(X0,k10_relat_1(sK8,X1))
% 3.32/0.98      | r2_hidden(sK6(X0,X1,sK8),k2_relat_1(sK8)) ),
% 3.32/0.98      inference(unflattening,[status(thm)],[c_446]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_3029,plain,
% 3.32/0.98      ( r2_hidden(sK6(sK1(k10_relat_1(sK8,sK7),k10_relat_1(sK8,sK7)),sK7,sK8),k2_relat_1(sK8))
% 3.32/0.98      | ~ r2_hidden(sK1(k10_relat_1(sK8,sK7),k10_relat_1(sK8,sK7)),k10_relat_1(sK8,sK7)) ),
% 3.32/0.98      inference(instantiation,[status(thm)],[c_447]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_25,plain,
% 3.32/0.98      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 3.32/0.98      | r2_hidden(sK6(X0,X2,X1),X2)
% 3.32/0.98      | ~ v1_relat_1(X1) ),
% 3.32/0.98      inference(cnf_transformation,[],[f91]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_470,plain,
% 3.32/0.98      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 3.32/0.98      | r2_hidden(sK6(X0,X2,X1),X2)
% 3.32/0.98      | sK8 != X1 ),
% 3.32/0.98      inference(resolution_lifted,[status(thm)],[c_25,c_33]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_471,plain,
% 3.32/0.98      ( ~ r2_hidden(X0,k10_relat_1(sK8,X1))
% 3.32/0.98      | r2_hidden(sK6(X0,X1,sK8),X1) ),
% 3.32/0.98      inference(unflattening,[status(thm)],[c_470]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_3027,plain,
% 3.32/0.98      ( r2_hidden(sK6(sK1(k10_relat_1(sK8,sK7),k10_relat_1(sK8,sK7)),sK7,sK8),sK7)
% 3.32/0.98      | ~ r2_hidden(sK1(k10_relat_1(sK8,sK7),k10_relat_1(sK8,sK7)),k10_relat_1(sK8,sK7)) ),
% 3.32/0.98      inference(instantiation,[status(thm)],[c_471]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_1768,plain,
% 3.32/0.98      ( ~ r1_xboole_0(k2_relat_1(sK8),sK7)
% 3.32/0.98      | ~ r2_hidden(X0,k2_relat_1(sK8))
% 3.32/0.98      | ~ r2_hidden(X0,sK7) ),
% 3.32/0.98      inference(instantiation,[status(thm)],[c_4]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_3822,plain,
% 3.32/0.98      ( ~ r1_xboole_0(k2_relat_1(sK8),sK7)
% 3.32/0.98      | ~ r2_hidden(sK6(sK1(k10_relat_1(sK8,sK7),k10_relat_1(sK8,sK7)),sK7,sK8),k2_relat_1(sK8))
% 3.32/0.98      | ~ r2_hidden(sK6(sK1(k10_relat_1(sK8,sK7),k10_relat_1(sK8,sK7)),sK7,sK8),sK7) ),
% 3.32/0.98      inference(instantiation,[status(thm)],[c_1768]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_4664,plain,
% 3.32/0.98      ( k10_relat_1(sK8,sK7) = k1_xboole_0 ),
% 3.32/0.98      inference(global_propositional_subsumption,
% 3.32/0.98                [status(thm)],
% 3.32/0.98                [c_4152,c_89,c_2012,c_2010,c_2379,c_2755,c_3029,c_3027,
% 3.32/0.98                 c_3822]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_24,plain,
% 3.32/0.98      ( ~ r2_hidden(X0,X1)
% 3.32/0.98      | r2_hidden(X2,k10_relat_1(X3,X1))
% 3.32/0.98      | ~ r2_hidden(X0,k2_relat_1(X3))
% 3.32/0.98      | ~ r2_hidden(k4_tarski(X2,X0),X3)
% 3.32/0.98      | ~ v1_relat_1(X3) ),
% 3.32/0.98      inference(cnf_transformation,[],[f92]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_426,plain,
% 3.32/0.98      ( ~ r2_hidden(X0,X1)
% 3.32/0.98      | r2_hidden(X2,k10_relat_1(X3,X1))
% 3.32/0.98      | ~ r2_hidden(X0,k2_relat_1(X3))
% 3.32/0.98      | ~ r2_hidden(k4_tarski(X2,X0),X3)
% 3.32/0.98      | sK8 != X3 ),
% 3.32/0.98      inference(resolution_lifted,[status(thm)],[c_24,c_33]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_427,plain,
% 3.32/0.98      ( ~ r2_hidden(X0,X1)
% 3.32/0.98      | r2_hidden(X2,k10_relat_1(sK8,X1))
% 3.32/0.98      | ~ r2_hidden(X0,k2_relat_1(sK8))
% 3.32/0.98      | ~ r2_hidden(k4_tarski(X2,X0),sK8) ),
% 3.32/0.98      inference(unflattening,[status(thm)],[c_426]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_22,plain,
% 3.32/0.98      ( r2_hidden(X0,k2_relat_1(X1)) | ~ r2_hidden(k4_tarski(X2,X0),X1) ),
% 3.32/0.98      inference(cnf_transformation,[],[f104]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_439,plain,
% 3.32/0.98      ( ~ r2_hidden(X0,X1)
% 3.32/0.98      | r2_hidden(X2,k10_relat_1(sK8,X1))
% 3.32/0.98      | ~ r2_hidden(k4_tarski(X2,X0),sK8) ),
% 3.32/0.98      inference(forward_subsumption_resolution,
% 3.32/0.98                [status(thm)],
% 3.32/0.98                [c_427,c_22]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_2168,plain,
% 3.32/0.98      ( r2_hidden(X0,k10_relat_1(sK8,sK7))
% 3.32/0.98      | ~ r2_hidden(k4_tarski(X0,sK1(k2_relat_1(sK8),sK7)),sK8)
% 3.32/0.98      | ~ r2_hidden(sK1(k2_relat_1(sK8),sK7),sK7) ),
% 3.32/0.98      inference(instantiation,[status(thm)],[c_439]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_4086,plain,
% 3.32/0.98      ( r2_hidden(sK5(sK8,sK1(k2_relat_1(sK8),sK7)),k10_relat_1(sK8,sK7))
% 3.32/0.98      | ~ r2_hidden(k4_tarski(sK5(sK8,sK1(k2_relat_1(sK8),sK7)),sK1(k2_relat_1(sK8),sK7)),sK8)
% 3.32/0.98      | ~ r2_hidden(sK1(k2_relat_1(sK8),sK7),sK7) ),
% 3.32/0.98      inference(instantiation,[status(thm)],[c_2168]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_1012,plain,
% 3.32/0.98      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.32/0.98      theory(equality) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_3135,plain,
% 3.32/0.98      ( ~ r1_tarski(X0,X1)
% 3.32/0.98      | r1_tarski(k10_relat_1(sK8,sK7),X2)
% 3.32/0.98      | X2 != X1
% 3.32/0.98      | k10_relat_1(sK8,sK7) != X0 ),
% 3.32/0.98      inference(instantiation,[status(thm)],[c_1012]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_3137,plain,
% 3.32/0.98      ( r1_tarski(k10_relat_1(sK8,sK7),k1_xboole_0)
% 3.32/0.98      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 3.32/0.98      | k10_relat_1(sK8,sK7) != k1_xboole_0
% 3.32/0.98      | k1_xboole_0 != k1_xboole_0 ),
% 3.32/0.98      inference(instantiation,[status(thm)],[c_3135]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_23,plain,
% 3.32/0.98      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 3.32/0.98      | r2_hidden(k4_tarski(sK5(X1,X0),X0),X1) ),
% 3.32/0.98      inference(cnf_transformation,[],[f105]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_2207,plain,
% 3.32/0.98      ( r2_hidden(k4_tarski(sK5(sK8,sK1(k2_relat_1(sK8),sK7)),sK1(k2_relat_1(sK8),sK7)),sK8)
% 3.32/0.98      | ~ r2_hidden(sK1(k2_relat_1(sK8),sK7),k2_relat_1(sK8)) ),
% 3.32/0.98      inference(instantiation,[status(thm)],[c_23]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_1014,plain,
% 3.32/0.98      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.32/0.98      theory(equality) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_1872,plain,
% 3.32/0.98      ( ~ r1_xboole_0(X0,X1)
% 3.32/0.98      | r1_xboole_0(X2,k10_relat_1(sK8,sK7))
% 3.32/0.98      | X2 != X0
% 3.32/0.98      | k10_relat_1(sK8,sK7) != X1 ),
% 3.32/0.98      inference(instantiation,[status(thm)],[c_1014]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_1874,plain,
% 3.32/0.98      ( r1_xboole_0(k1_xboole_0,k10_relat_1(sK8,sK7))
% 3.32/0.98      | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
% 3.32/0.98      | k10_relat_1(sK8,sK7) != k1_xboole_0
% 3.32/0.98      | k1_xboole_0 != k1_xboole_0 ),
% 3.32/0.98      inference(instantiation,[status(thm)],[c_1872]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_1010,plain,( X0 != X1 | X2 != X1 | X0 = X2 ),theory(equality) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_1783,plain,
% 3.32/0.98      ( k10_relat_1(sK8,sK7) != X0
% 3.32/0.98      | k1_xboole_0 != X0
% 3.32/0.98      | k1_xboole_0 = k10_relat_1(sK8,sK7) ),
% 3.32/0.98      inference(instantiation,[status(thm)],[c_1010]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_1784,plain,
% 3.32/0.98      ( k10_relat_1(sK8,sK7) != k1_xboole_0
% 3.32/0.98      | k1_xboole_0 = k10_relat_1(sK8,sK7)
% 3.32/0.98      | k1_xboole_0 != k1_xboole_0 ),
% 3.32/0.98      inference(instantiation,[status(thm)],[c_1783]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_1708,plain,
% 3.32/0.98      ( r1_xboole_0(k2_relat_1(sK8),sK7)
% 3.32/0.98      | r2_hidden(sK1(k2_relat_1(sK8),sK7),sK7) ),
% 3.32/0.98      inference(instantiation,[status(thm)],[c_5]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_6,plain,
% 3.32/0.98      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 3.32/0.98      inference(cnf_transformation,[],[f66]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_1709,plain,
% 3.32/0.98      ( r1_xboole_0(k2_relat_1(sK8),sK7)
% 3.32/0.98      | r2_hidden(sK1(k2_relat_1(sK8),sK7),k2_relat_1(sK8)) ),
% 3.32/0.98      inference(instantiation,[status(thm)],[c_6]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_1034,plain,
% 3.32/0.98      ( k1_xboole_0 = k1_xboole_0 ),
% 3.32/0.98      inference(instantiation,[status(thm)],[c_1009]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_10,plain,
% 3.32/0.98      ( r1_tarski(k1_xboole_0,X0) ),
% 3.32/0.98      inference(cnf_transformation,[],[f72]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_94,plain,
% 3.32/0.98      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 3.32/0.98      inference(instantiation,[status(thm)],[c_10]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_31,negated_conjecture,
% 3.32/0.98      ( ~ r1_xboole_0(k2_relat_1(sK8),sK7)
% 3.32/0.98      | k1_xboole_0 != k10_relat_1(sK8,sK7) ),
% 3.32/0.98      inference(cnf_transformation,[],[f98]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(contradiction,plain,
% 3.32/0.98      ( $false ),
% 3.32/0.98      inference(minisat,
% 3.32/0.98                [status(thm)],
% 3.32/0.98                [c_8085,c_8066,c_4664,c_4086,c_3137,c_2207,c_1874,c_1784,
% 3.32/0.98                 c_1708,c_1709,c_1034,c_94,c_89,c_31]) ).
% 3.32/0.98  
% 3.32/0.98  
% 3.32/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.32/0.98  
% 3.32/0.98  ------                               Statistics
% 3.32/0.98  
% 3.32/0.98  ------ General
% 3.32/0.98  
% 3.32/0.98  abstr_ref_over_cycles:                  0
% 3.32/0.98  abstr_ref_under_cycles:                 0
% 3.32/0.98  gc_basic_clause_elim:                   0
% 3.32/0.98  forced_gc_time:                         0
% 3.32/0.98  parsing_time:                           0.01
% 3.32/0.98  unif_index_cands_time:                  0.
% 3.32/0.98  unif_index_add_time:                    0.
% 3.32/0.98  orderings_time:                         0.
% 3.32/0.98  out_proof_time:                         0.01
% 3.32/0.98  total_time:                             0.27
% 3.32/0.98  num_of_symbols:                         53
% 3.32/0.98  num_of_terms:                           9921
% 3.32/0.98  
% 3.32/0.98  ------ Preprocessing
% 3.32/0.98  
% 3.32/0.98  num_of_splits:                          0
% 3.32/0.98  num_of_split_atoms:                     0
% 3.32/0.98  num_of_reused_defs:                     0
% 3.32/0.98  num_eq_ax_congr_red:                    47
% 3.32/0.98  num_of_sem_filtered_clauses:            1
% 3.32/0.98  num_of_subtypes:                        0
% 3.32/0.98  monotx_restored_types:                  0
% 3.32/0.98  sat_num_of_epr_types:                   0
% 3.32/0.98  sat_num_of_non_cyclic_types:            0
% 3.32/0.98  sat_guarded_non_collapsed_types:        0
% 3.32/0.98  num_pure_diseq_elim:                    0
% 3.32/0.98  simp_replaced_by:                       0
% 3.32/0.98  res_preprocessed:                       160
% 3.32/0.98  prep_upred:                             0
% 3.32/0.98  prep_unflattend:                        39
% 3.32/0.98  smt_new_axioms:                         0
% 3.32/0.98  pred_elim_cands:                        3
% 3.32/0.98  pred_elim:                              1
% 3.32/0.98  pred_elim_cl:                           1
% 3.32/0.98  pred_elim_cycles:                       3
% 3.32/0.98  merged_defs:                            16
% 3.32/0.98  merged_defs_ncl:                        0
% 3.32/0.98  bin_hyper_res:                          16
% 3.32/0.98  prep_cycles:                            4
% 3.32/0.98  pred_elim_time:                         0.006
% 3.32/0.98  splitting_time:                         0.
% 3.32/0.98  sem_filter_time:                        0.
% 3.32/0.98  monotx_time:                            0.
% 3.32/0.98  subtype_inf_time:                       0.
% 3.32/0.98  
% 3.32/0.98  ------ Problem properties
% 3.32/0.98  
% 3.32/0.98  clauses:                                33
% 3.32/0.98  conjectures:                            2
% 3.32/0.98  epr:                                    5
% 3.32/0.98  horn:                                   26
% 3.32/0.98  ground:                                 4
% 3.32/0.98  unary:                                  9
% 3.32/0.98  binary:                                 16
% 3.32/0.98  lits:                                   66
% 3.32/0.98  lits_eq:                                14
% 3.32/0.98  fd_pure:                                0
% 3.32/0.98  fd_pseudo:                              0
% 3.32/0.98  fd_cond:                                0
% 3.32/0.98  fd_pseudo_cond:                         3
% 3.32/0.98  ac_symbols:                             0
% 3.32/0.98  
% 3.32/0.98  ------ Propositional Solver
% 3.32/0.98  
% 3.32/0.98  prop_solver_calls:                      31
% 3.32/0.98  prop_fast_solver_calls:                 982
% 3.32/0.98  smt_solver_calls:                       0
% 3.32/0.98  smt_fast_solver_calls:                  0
% 3.32/0.98  prop_num_of_clauses:                    3711
% 3.32/0.98  prop_preprocess_simplified:             8972
% 3.32/0.98  prop_fo_subsumed:                       7
% 3.32/0.98  prop_solver_time:                       0.
% 3.32/0.98  smt_solver_time:                        0.
% 3.32/0.98  smt_fast_solver_time:                   0.
% 3.32/0.98  prop_fast_solver_time:                  0.
% 3.32/0.98  prop_unsat_core_time:                   0.
% 3.32/0.98  
% 3.32/0.98  ------ QBF
% 3.32/0.98  
% 3.32/0.98  qbf_q_res:                              0
% 3.32/0.98  qbf_num_tautologies:                    0
% 3.32/0.98  qbf_prep_cycles:                        0
% 3.32/0.98  
% 3.32/0.98  ------ BMC1
% 3.32/0.98  
% 3.32/0.98  bmc1_current_bound:                     -1
% 3.32/0.98  bmc1_last_solved_bound:                 -1
% 3.32/0.98  bmc1_unsat_core_size:                   -1
% 3.32/0.98  bmc1_unsat_core_parents_size:           -1
% 3.32/0.98  bmc1_merge_next_fun:                    0
% 3.32/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.32/0.98  
% 3.32/0.98  ------ Instantiation
% 3.32/0.98  
% 3.32/0.98  inst_num_of_clauses:                    884
% 3.32/0.98  inst_num_in_passive:                    381
% 3.32/0.98  inst_num_in_active:                     355
% 3.32/0.98  inst_num_in_unprocessed:                147
% 3.32/0.98  inst_num_of_loops:                      500
% 3.32/0.98  inst_num_of_learning_restarts:          0
% 3.32/0.98  inst_num_moves_active_passive:          140
% 3.32/0.98  inst_lit_activity:                      0
% 3.32/0.98  inst_lit_activity_moves:                0
% 3.32/0.98  inst_num_tautologies:                   0
% 3.32/0.98  inst_num_prop_implied:                  0
% 3.32/0.98  inst_num_existing_simplified:           0
% 3.32/0.98  inst_num_eq_res_simplified:             0
% 3.32/0.98  inst_num_child_elim:                    0
% 3.32/0.98  inst_num_of_dismatching_blockings:      355
% 3.32/0.98  inst_num_of_non_proper_insts:           914
% 3.32/0.98  inst_num_of_duplicates:                 0
% 3.32/0.98  inst_inst_num_from_inst_to_res:         0
% 3.32/0.98  inst_dismatching_checking_time:         0.
% 3.32/0.98  
% 3.32/0.98  ------ Resolution
% 3.32/0.98  
% 3.32/0.98  res_num_of_clauses:                     0
% 3.32/0.98  res_num_in_passive:                     0
% 3.32/0.98  res_num_in_active:                      0
% 3.32/0.98  res_num_of_loops:                       164
% 3.32/0.98  res_forward_subset_subsumed:            38
% 3.32/0.98  res_backward_subset_subsumed:           0
% 3.32/0.98  res_forward_subsumed:                   0
% 3.32/0.98  res_backward_subsumed:                  0
% 3.32/0.98  res_forward_subsumption_resolution:     1
% 3.32/0.98  res_backward_subsumption_resolution:    0
% 3.32/0.98  res_clause_to_clause_subsumption:       720
% 3.32/0.98  res_orphan_elimination:                 0
% 3.32/0.98  res_tautology_del:                      65
% 3.32/0.98  res_num_eq_res_simplified:              0
% 3.32/0.98  res_num_sel_changes:                    0
% 3.32/0.98  res_moves_from_active_to_pass:          0
% 3.32/0.98  
% 3.32/0.98  ------ Superposition
% 3.32/0.98  
% 3.32/0.98  sup_time_total:                         0.
% 3.32/0.98  sup_time_generating:                    0.
% 3.32/0.98  sup_time_sim_full:                      0.
% 3.32/0.98  sup_time_sim_immed:                     0.
% 3.32/0.98  
% 3.32/0.98  sup_num_of_clauses:                     206
% 3.32/0.98  sup_num_in_active:                      73
% 3.32/0.98  sup_num_in_passive:                     133
% 3.32/0.98  sup_num_of_loops:                       98
% 3.32/0.98  sup_fw_superposition:                   200
% 3.32/0.98  sup_bw_superposition:                   89
% 3.32/0.98  sup_immediate_simplified:               59
% 3.32/0.98  sup_given_eliminated:                   0
% 3.32/0.98  comparisons_done:                       0
% 3.32/0.98  comparisons_avoided:                    3
% 3.32/0.98  
% 3.32/0.98  ------ Simplifications
% 3.32/0.98  
% 3.32/0.98  
% 3.32/0.98  sim_fw_subset_subsumed:                 28
% 3.32/0.98  sim_bw_subset_subsumed:                 11
% 3.32/0.98  sim_fw_subsumed:                        11
% 3.32/0.98  sim_bw_subsumed:                        20
% 3.32/0.98  sim_fw_subsumption_res:                 0
% 3.32/0.98  sim_bw_subsumption_res:                 0
% 3.32/0.98  sim_tautology_del:                      8
% 3.32/0.98  sim_eq_tautology_del:                   3
% 3.32/0.98  sim_eq_res_simp:                        1
% 3.32/0.98  sim_fw_demodulated:                     3
% 3.32/0.98  sim_bw_demodulated:                     3
% 3.32/0.98  sim_light_normalised:                   23
% 3.32/0.98  sim_joinable_taut:                      0
% 3.32/0.98  sim_joinable_simp:                      0
% 3.32/0.98  sim_ac_normalised:                      0
% 3.32/0.98  sim_smt_subsumption:                    0
% 3.32/0.98  
%------------------------------------------------------------------------------
