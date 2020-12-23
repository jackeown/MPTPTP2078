%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:47:27 EST 2020

% Result     : Timeout 59.77s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :  162 ( 304 expanded)
%              Number of clauses        :   79 ( 103 expanded)
%              Number of leaves         :   28 (  75 expanded)
%              Depth                    :   21
%              Number of atoms          :  560 (1169 expanded)
%              Number of equality atoms :  179 ( 346 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   15 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f41,plain,(
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
    inference(rectify,[],[f40])).

fof(f44,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK8(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK7(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK6(X0,X1)),X0)
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK6(X0,X1)),X0)
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK6(X0,X1)),X0)
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0)
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK8(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f41,f44,f43,f42])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0)
      | r2_hidden(sK6(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f8,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f32])).

fof(f65,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f76,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK8(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f102,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK8(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f76])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f47,plain,(
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
    inference(rectify,[],[f46])).

fof(f48,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X0,X4),X2)
          & r2_hidden(X4,k2_relat_1(X2)) )
     => ( r2_hidden(sK9(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X0,sK9(X0,X1,X2)),X2)
        & r2_hidden(sK9(X0,X1,X2),k2_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ( r2_hidden(sK9(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(X0,sK9(X0,X1,X2)),X2)
            & r2_hidden(sK9(X0,X1,X2),k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f47,f48])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK9(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK9(X0,X1,X2),k2_relat_1(X2))
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k10_relat_1(X1,X0)
        <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <~> r1_xboole_0(k2_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f50,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 != k10_relat_1(X1,X0) )
      & ( r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f51,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 != k10_relat_1(X1,X0) )
      & ( r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f50])).

fof(f52,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 != k10_relat_1(X1,X0) )
        & ( r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 = k10_relat_1(X1,X0) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_xboole_0(k2_relat_1(sK11),sK10)
        | k1_xboole_0 != k10_relat_1(sK11,sK10) )
      & ( r1_xboole_0(k2_relat_1(sK11),sK10)
        | k1_xboole_0 = k10_relat_1(sK11,sK10) )
      & v1_relat_1(sK11) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( ( ~ r1_xboole_0(k2_relat_1(sK11),sK10)
      | k1_xboole_0 != k10_relat_1(sK11,sK10) )
    & ( r1_xboole_0(k2_relat_1(sK11),sK10)
      | k1_xboole_0 = k10_relat_1(sK11,sK10) )
    & v1_relat_1(sK11) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11])],[f51,f52])).

fof(f86,plain,
    ( r1_xboole_0(k2_relat_1(sK11),sK10)
    | k1_xboole_0 = k10_relat_1(sK11,sK10) ),
    inference(cnf_transformation,[],[f53])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f90,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f61,f66])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f88,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f54,f66,f66])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f93,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f69,f66])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(nnf_transformation,[],[f2])).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f24])).

fof(f26,plain,(
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
    inference(rectify,[],[f25])).

fof(f27,plain,(
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

fof(f28,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).

fof(f57,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f95,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f57])).

fof(f56,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f96,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f56])).

fof(f85,plain,(
    v1_relat_1(sK11) ),
    inference(cnf_transformation,[],[f53])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X3,X4),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) ) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( r2_hidden(X5,X1)
                      & r2_hidden(k4_tarski(X3,X5),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X6,X7),X0) ) )
                & ( ? [X8] :
                      ( r2_hidden(X8,X1)
                      & r2_hidden(k4_tarski(X6,X8),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f34])).

fof(f38,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X6,X8),X0) )
     => ( r2_hidden(sK5(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(X6,sK5(X0,X1,X6)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(X3,X5),X0) )
     => ( r2_hidden(sK4(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X3,sK4(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(X4,X1)
                | ~ r2_hidden(k4_tarski(X3,X4),X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X3,X5),X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( ~ r2_hidden(X4,X1)
              | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),X4),X0) )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X1)
              & r2_hidden(k4_tarski(sK3(X0,X1,X2),X5),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),X4),X0) )
                | ~ r2_hidden(sK3(X0,X1,X2),X2) )
              & ( ( r2_hidden(sK4(X0,X1,X2),X1)
                  & r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0) )
                | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X6,X7),X0) ) )
                & ( ( r2_hidden(sK5(X0,X1,X6),X1)
                    & r2_hidden(k4_tarski(X6,sK5(X0,X1,X6)),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f35,f38,f37,f36])).

fof(f72,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f98,plain,(
    ! [X6,X0,X7,X1] :
      ( r2_hidden(X6,k10_relat_1(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f72])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f94,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k4_xboole_0(k2_relat_1(X1),k4_xboole_0(k2_relat_1(X1),X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f84,f66])).

fof(f55,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f97,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f55])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f17,f30])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f92,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f63,f66])).

fof(f87,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK11),sK10)
    | k1_xboole_0 != k10_relat_1(sK11,sK10) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_12,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_96256,plain,
    ( r1_xboole_0(k1_tarski(sK8(sK11,sK1(k2_relat_1(sK11),sK10))),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_22,plain,
    ( r2_hidden(sK6(X0,X1),X1)
    | r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1238,plain,
    ( k2_relat_1(X0) = X1
    | r2_hidden(sK6(X0,X1),X1) = iProver_top
    | r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1247,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_13,plain,
    ( ~ r1_xboole_0(k1_tarski(X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1246,plain,
    ( r1_xboole_0(k1_tarski(X0),X1) != iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2646,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1247,c_1246])).

cnf(c_13304,plain,
    ( k2_relat_1(k1_xboole_0) = X0
    | r2_hidden(sK6(k1_xboole_0,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1238,c_2646])).

cnf(c_11,plain,
    ( r2_hidden(sK2(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1248,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK2(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_24,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(k4_tarski(sK8(X1,X0),X0),X1) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1236,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(sK8(X1,X0),X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_13305,plain,
    ( r2_hidden(X0,k2_relat_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1236,c_2646])).

cnf(c_13514,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1248,c_13305])).

cnf(c_14237,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK6(k1_xboole_0,X0),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_13304,c_13514])).

cnf(c_26,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK9(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1235,plain,
    ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK9(X0,X2,X1),X2) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_28,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK9(X0,X2,X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1233,plain,
    ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK9(X0,X2,X1),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_31,negated_conjecture,
    ( r1_xboole_0(k2_relat_1(sK11),sK10)
    | k1_xboole_0 = k10_relat_1(sK11,sK10) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1230,plain,
    ( k1_xboole_0 = k10_relat_1(sK11,sK10)
    | r1_xboole_0(k2_relat_1(sK11),sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_8,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1251,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_14,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1269,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_0,c_14])).

cnf(c_1284,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0
    | r1_xboole_0(X1,X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1251,c_1269])).

cnf(c_1627,plain,
    ( k10_relat_1(sK11,sK10) = k1_xboole_0
    | k1_setfam_1(k2_tarski(sK10,k2_relat_1(sK11))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1230,c_1284])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1255,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_6815,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k4_xboole_0(X1,X2)) = iProver_top
    | r2_hidden(X0,k1_setfam_1(k2_tarski(X1,X2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_14,c_1255])).

cnf(c_8595,plain,
    ( k10_relat_1(sK11,sK10) = k1_xboole_0
    | r2_hidden(X0,k4_xboole_0(sK10,k2_relat_1(sK11))) = iProver_top
    | r2_hidden(X0,sK10) != iProver_top
    | r2_hidden(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1627,c_6815])).

cnf(c_1556,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_13,c_12])).

cnf(c_1557,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1556])).

cnf(c_9213,plain,
    ( r2_hidden(X0,sK10) != iProver_top
    | r2_hidden(X0,k4_xboole_0(sK10,k2_relat_1(sK11))) = iProver_top
    | k10_relat_1(sK11,sK10) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8595,c_1557])).

cnf(c_9214,plain,
    ( k10_relat_1(sK11,sK10) = k1_xboole_0
    | r2_hidden(X0,k4_xboole_0(sK10,k2_relat_1(sK11))) = iProver_top
    | r2_hidden(X0,sK10) != iProver_top ),
    inference(renaming,[status(thm)],[c_9213])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1254,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_9224,plain,
    ( k10_relat_1(sK11,sK10) = k1_xboole_0
    | r2_hidden(X0,k2_relat_1(sK11)) != iProver_top
    | r2_hidden(X0,sK10) != iProver_top ),
    inference(superposition,[status(thm)],[c_9214,c_1254])).

cnf(c_9562,plain,
    ( k10_relat_1(sK11,sK10) = k1_xboole_0
    | r2_hidden(X0,k10_relat_1(sK11,X1)) != iProver_top
    | r2_hidden(sK9(X0,X1,sK11),sK10) != iProver_top
    | v1_relat_1(sK11) != iProver_top ),
    inference(superposition,[status(thm)],[c_1233,c_9224])).

cnf(c_32,negated_conjecture,
    ( v1_relat_1(sK11) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_33,plain,
    ( v1_relat_1(sK11) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_10512,plain,
    ( r2_hidden(sK9(X0,X1,sK11),sK10) != iProver_top
    | r2_hidden(X0,k10_relat_1(sK11,X1)) != iProver_top
    | k10_relat_1(sK11,sK10) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9562,c_33])).

cnf(c_10513,plain,
    ( k10_relat_1(sK11,sK10) = k1_xboole_0
    | r2_hidden(X0,k10_relat_1(sK11,X1)) != iProver_top
    | r2_hidden(sK9(X0,X1,sK11),sK10) != iProver_top ),
    inference(renaming,[status(thm)],[c_10512])).

cnf(c_10521,plain,
    ( k10_relat_1(sK11,sK10) = k1_xboole_0
    | r2_hidden(X0,k10_relat_1(sK11,sK10)) != iProver_top
    | v1_relat_1(sK11) != iProver_top ),
    inference(superposition,[status(thm)],[c_1235,c_10513])).

cnf(c_95478,plain,
    ( r2_hidden(X0,k10_relat_1(sK11,sK10)) != iProver_top
    | k10_relat_1(sK11,sK10) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10521,c_33])).

cnf(c_95479,plain,
    ( k10_relat_1(sK11,sK10) = k1_xboole_0
    | r2_hidden(X0,k10_relat_1(sK11,sK10)) != iProver_top ),
    inference(renaming,[status(thm)],[c_95478])).

cnf(c_95502,plain,
    ( k10_relat_1(sK11,sK10) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_14237,c_95479])).

cnf(c_582,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_23931,plain,
    ( sK8(sK11,sK1(k2_relat_1(sK11),sK10)) = sK8(sK11,sK1(k2_relat_1(sK11),sK10)) ),
    inference(instantiation,[status(thm)],[c_582])).

cnf(c_585,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_10271,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),k10_relat_1(sK11,k4_xboole_0(k2_relat_1(sK11),k4_xboole_0(k2_relat_1(sK11),sK10))))
    | X0 != sK8(sK11,sK1(k2_relat_1(sK11),sK10))
    | X1 != k10_relat_1(sK11,k4_xboole_0(k2_relat_1(sK11),k4_xboole_0(k2_relat_1(sK11),sK10))) ),
    inference(instantiation,[status(thm)],[c_585])).

cnf(c_23930,plain,
    ( r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),X0)
    | ~ r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),k10_relat_1(sK11,k4_xboole_0(k2_relat_1(sK11),k4_xboole_0(k2_relat_1(sK11),sK10))))
    | X0 != k10_relat_1(sK11,k4_xboole_0(k2_relat_1(sK11),k4_xboole_0(k2_relat_1(sK11),sK10)))
    | sK8(sK11,sK1(k2_relat_1(sK11),sK10)) != sK8(sK11,sK1(k2_relat_1(sK11),sK10)) ),
    inference(instantiation,[status(thm)],[c_10271])).

cnf(c_23933,plain,
    ( ~ r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),k10_relat_1(sK11,k4_xboole_0(k2_relat_1(sK11),k4_xboole_0(k2_relat_1(sK11),sK10))))
    | r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),k1_xboole_0)
    | sK8(sK11,sK1(k2_relat_1(sK11),sK10)) != sK8(sK11,sK1(k2_relat_1(sK11),sK10))
    | k1_xboole_0 != k10_relat_1(sK11,k4_xboole_0(k2_relat_1(sK11),k4_xboole_0(k2_relat_1(sK11),sK10))) ),
    inference(instantiation,[status(thm)],[c_23930])).

cnf(c_22914,plain,
    ( ~ r1_xboole_0(k1_tarski(sK8(sK11,sK1(k2_relat_1(sK11),sK10))),X0)
    | ~ r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),X0) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_22916,plain,
    ( ~ r1_xboole_0(k1_tarski(sK8(sK11,sK1(k2_relat_1(sK11),sK10))),k1_xboole_0)
    | ~ r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_22914])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(X3,X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_2752,plain,
    ( r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),k10_relat_1(sK11,X0))
    | ~ r2_hidden(k4_tarski(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),sK1(k2_relat_1(sK11),sK10)),sK11)
    | ~ r2_hidden(sK1(k2_relat_1(sK11),sK10),X0)
    | ~ v1_relat_1(sK11) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_9097,plain,
    ( r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),k10_relat_1(sK11,k4_xboole_0(k2_relat_1(sK11),k4_xboole_0(k2_relat_1(sK11),sK10))))
    | ~ r2_hidden(k4_tarski(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),sK1(k2_relat_1(sK11),sK10)),sK11)
    | ~ r2_hidden(sK1(k2_relat_1(sK11),sK10),k4_xboole_0(k2_relat_1(sK11),k4_xboole_0(k2_relat_1(sK11),sK10)))
    | ~ v1_relat_1(sK11) ),
    inference(instantiation,[status(thm)],[c_2752])).

cnf(c_583,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2687,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_583,c_582])).

cnf(c_4193,plain,
    ( r1_xboole_0(k2_relat_1(sK11),sK10)
    | k10_relat_1(sK11,sK10) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2687,c_31])).

cnf(c_4497,plain,
    ( r1_xboole_0(k2_relat_1(sK11),sK10)
    | X0 != k1_xboole_0
    | k10_relat_1(sK11,sK10) = X0 ),
    inference(resolution,[status(thm)],[c_4193,c_583])).

cnf(c_2685,plain,
    ( r1_xboole_0(k2_relat_1(sK11),sK10)
    | X0 != k10_relat_1(sK11,sK10)
    | k1_xboole_0 = X0 ),
    inference(resolution,[status(thm)],[c_583,c_31])).

cnf(c_5399,plain,
    ( r1_xboole_0(k2_relat_1(sK11),sK10)
    | k10_relat_1(sK11,sK10) != k1_xboole_0
    | k1_xboole_0 = k10_relat_1(sK11,sK10) ),
    inference(resolution,[status(thm)],[c_4497,c_2685])).

cnf(c_601,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_582])).

cnf(c_1846,plain,
    ( k10_relat_1(sK11,sK10) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k10_relat_1(sK11,sK10) ),
    inference(instantiation,[status(thm)],[c_583])).

cnf(c_1847,plain,
    ( k10_relat_1(sK11,sK10) != k1_xboole_0
    | k1_xboole_0 = k10_relat_1(sK11,sK10)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1846])).

cnf(c_5445,plain,
    ( k10_relat_1(sK11,sK10) != k1_xboole_0
    | k1_xboole_0 = k10_relat_1(sK11,sK10) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5399,c_601,c_1847])).

cnf(c_29,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k4_xboole_0(k2_relat_1(X0),k4_xboole_0(k2_relat_1(X0),X1))) = k10_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_4540,plain,
    ( r1_xboole_0(k2_relat_1(sK11),sK10)
    | ~ v1_relat_1(sK11)
    | k1_xboole_0 = k10_relat_1(sK11,k4_xboole_0(k2_relat_1(sK11),k4_xboole_0(k2_relat_1(sK11),sK10))) ),
    inference(resolution,[status(thm)],[c_29,c_2685])).

cnf(c_1937,plain,
    ( r2_hidden(k4_tarski(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),sK1(k2_relat_1(sK11),sK10)),sK11)
    | ~ r2_hidden(sK1(k2_relat_1(sK11),sK10),k2_relat_1(sK11)) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_6,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1690,plain,
    ( ~ r2_hidden(sK1(k2_relat_1(sK11),sK10),k4_xboole_0(k2_relat_1(sK11),k4_xboole_0(k2_relat_1(sK11),sK10)))
    | r2_hidden(sK1(k2_relat_1(sK11),sK10),k2_relat_1(sK11)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_10,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1537,plain,
    ( r1_xboole_0(k2_relat_1(sK11),sK10)
    | r2_hidden(sK1(k2_relat_1(sK11),sK10),k4_xboole_0(k2_relat_1(sK11),k4_xboole_0(k2_relat_1(sK11),sK10))) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_30,negated_conjecture,
    ( ~ r1_xboole_0(k2_relat_1(sK11),sK10)
    | k1_xboole_0 != k10_relat_1(sK11,sK10) ),
    inference(cnf_transformation,[],[f87])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_96256,c_95502,c_23931,c_23933,c_22916,c_9097,c_5445,c_4540,c_1937,c_1690,c_1537,c_30,c_32])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:39:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 59.77/8.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 59.77/8.02  
% 59.77/8.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 59.77/8.02  
% 59.77/8.02  ------  iProver source info
% 59.77/8.02  
% 59.77/8.02  git: date: 2020-06-30 10:37:57 +0100
% 59.77/8.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 59.77/8.02  git: non_committed_changes: false
% 59.77/8.02  git: last_make_outside_of_git: false
% 59.77/8.02  
% 59.77/8.02  ------ 
% 59.77/8.02  ------ Parsing...
% 59.77/8.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 59.77/8.02  
% 59.77/8.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 59.77/8.02  
% 59.77/8.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 59.77/8.02  
% 59.77/8.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 59.77/8.02  ------ Proving...
% 59.77/8.02  ------ Problem Properties 
% 59.77/8.02  
% 59.77/8.02  
% 59.77/8.02  clauses                                 32
% 59.77/8.02  conjectures                             3
% 59.77/8.02  EPR                                     2
% 59.77/8.02  Horn                                    22
% 59.77/8.02  unary                                   4
% 59.77/8.02  binary                                  13
% 59.77/8.02  lits                                    81
% 59.77/8.02  lits eq                                 16
% 59.77/8.02  fd_pure                                 0
% 59.77/8.02  fd_pseudo                               0
% 59.77/8.02  fd_cond                                 1
% 59.77/8.02  fd_pseudo_cond                          8
% 59.77/8.02  AC symbols                              0
% 59.77/8.02  
% 59.77/8.02  ------ Input Options Time Limit: Unbounded
% 59.77/8.02  
% 59.77/8.02  
% 59.77/8.02  ------ 
% 59.77/8.02  Current options:
% 59.77/8.02  ------ 
% 59.77/8.02  
% 59.77/8.02  
% 59.77/8.02  
% 59.77/8.02  
% 59.77/8.02  ------ Proving...
% 59.77/8.02  
% 59.77/8.02  
% 59.77/8.02  % SZS status Theorem for theBenchmark.p
% 59.77/8.02  
% 59.77/8.02  % SZS output start CNFRefutation for theBenchmark.p
% 59.77/8.02  
% 59.77/8.02  fof(f7,axiom,(
% 59.77/8.02    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 59.77/8.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.77/8.02  
% 59.77/8.02  fof(f67,plain,(
% 59.77/8.02    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 59.77/8.02    inference(cnf_transformation,[],[f7])).
% 59.77/8.02  
% 59.77/8.02  fof(f11,axiom,(
% 59.77/8.02    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 59.77/8.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.77/8.02  
% 59.77/8.02  fof(f40,plain,(
% 59.77/8.02    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 59.77/8.02    inference(nnf_transformation,[],[f11])).
% 59.77/8.02  
% 59.77/8.02  fof(f41,plain,(
% 59.77/8.02    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 59.77/8.02    inference(rectify,[],[f40])).
% 59.77/8.02  
% 59.77/8.02  fof(f44,plain,(
% 59.77/8.02    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK8(X0,X5),X5),X0))),
% 59.77/8.02    introduced(choice_axiom,[])).
% 59.77/8.02  
% 59.77/8.02  fof(f43,plain,(
% 59.77/8.02    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) => r2_hidden(k4_tarski(sK7(X0,X1),X2),X0))) )),
% 59.77/8.02    introduced(choice_axiom,[])).
% 59.77/8.02  
% 59.77/8.02  fof(f42,plain,(
% 59.77/8.02    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK6(X0,X1)),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK6(X0,X1)),X0) | r2_hidden(sK6(X0,X1),X1))))),
% 59.77/8.02    introduced(choice_axiom,[])).
% 59.77/8.02  
% 59.77/8.02  fof(f45,plain,(
% 59.77/8.02    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK6(X0,X1)),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0) | r2_hidden(sK6(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK8(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 59.77/8.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f41,f44,f43,f42])).
% 59.77/8.02  
% 59.77/8.02  fof(f78,plain,(
% 59.77/8.02    ( ! [X0,X1] : (k2_relat_1(X0) = X1 | r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0) | r2_hidden(sK6(X0,X1),X1)) )),
% 59.77/8.02    inference(cnf_transformation,[],[f45])).
% 59.77/8.02  
% 59.77/8.02  fof(f8,axiom,(
% 59.77/8.02    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 59.77/8.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.77/8.02  
% 59.77/8.02  fof(f19,plain,(
% 59.77/8.02    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 59.77/8.02    inference(ennf_transformation,[],[f8])).
% 59.77/8.02  
% 59.77/8.02  fof(f68,plain,(
% 59.77/8.02    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1)) )),
% 59.77/8.02    inference(cnf_transformation,[],[f19])).
% 59.77/8.02  
% 59.77/8.02  fof(f5,axiom,(
% 59.77/8.02    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 59.77/8.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.77/8.02  
% 59.77/8.02  fof(f18,plain,(
% 59.77/8.02    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 59.77/8.02    inference(ennf_transformation,[],[f5])).
% 59.77/8.02  
% 59.77/8.02  fof(f32,plain,(
% 59.77/8.02    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 59.77/8.02    introduced(choice_axiom,[])).
% 59.77/8.02  
% 59.77/8.02  fof(f33,plain,(
% 59.77/8.02    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 59.77/8.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f32])).
% 59.77/8.02  
% 59.77/8.02  fof(f65,plain,(
% 59.77/8.02    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 59.77/8.02    inference(cnf_transformation,[],[f33])).
% 59.77/8.02  
% 59.77/8.02  fof(f76,plain,(
% 59.77/8.02    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK8(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 59.77/8.02    inference(cnf_transformation,[],[f45])).
% 59.77/8.02  
% 59.77/8.02  fof(f102,plain,(
% 59.77/8.02    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK8(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 59.77/8.02    inference(equality_resolution,[],[f76])).
% 59.77/8.02  
% 59.77/8.02  fof(f12,axiom,(
% 59.77/8.02    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 59.77/8.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.77/8.02  
% 59.77/8.02  fof(f21,plain,(
% 59.77/8.02    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 59.77/8.02    inference(ennf_transformation,[],[f12])).
% 59.77/8.02  
% 59.77/8.02  fof(f46,plain,(
% 59.77/8.02    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 59.77/8.02    inference(nnf_transformation,[],[f21])).
% 59.77/8.02  
% 59.77/8.02  fof(f47,plain,(
% 59.77/8.02    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 59.77/8.02    inference(rectify,[],[f46])).
% 59.77/8.02  
% 59.77/8.02  fof(f48,plain,(
% 59.77/8.02    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) => (r2_hidden(sK9(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK9(X0,X1,X2)),X2) & r2_hidden(sK9(X0,X1,X2),k2_relat_1(X2))))),
% 59.77/8.02    introduced(choice_axiom,[])).
% 59.77/8.02  
% 59.77/8.02  fof(f49,plain,(
% 59.77/8.02    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & ((r2_hidden(sK9(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK9(X0,X1,X2)),X2) & r2_hidden(sK9(X0,X1,X2),k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 59.77/8.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f47,f48])).
% 59.77/8.02  
% 59.77/8.02  fof(f82,plain,(
% 59.77/8.02    ( ! [X2,X0,X1] : (r2_hidden(sK9(X0,X1,X2),X1) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 59.77/8.02    inference(cnf_transformation,[],[f49])).
% 59.77/8.02  
% 59.77/8.02  fof(f80,plain,(
% 59.77/8.02    ( ! [X2,X0,X1] : (r2_hidden(sK9(X0,X1,X2),k2_relat_1(X2)) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 59.77/8.02    inference(cnf_transformation,[],[f49])).
% 59.77/8.02  
% 59.77/8.02  fof(f14,conjecture,(
% 59.77/8.02    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 59.77/8.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.77/8.02  
% 59.77/8.02  fof(f15,negated_conjecture,(
% 59.77/8.02    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 59.77/8.02    inference(negated_conjecture,[],[f14])).
% 59.77/8.02  
% 59.77/8.02  fof(f23,plain,(
% 59.77/8.02    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <~> r1_xboole_0(k2_relat_1(X1),X0)) & v1_relat_1(X1))),
% 59.77/8.02    inference(ennf_transformation,[],[f15])).
% 59.77/8.02  
% 59.77/8.02  fof(f50,plain,(
% 59.77/8.02    ? [X0,X1] : (((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0))) & v1_relat_1(X1))),
% 59.77/8.02    inference(nnf_transformation,[],[f23])).
% 59.77/8.02  
% 59.77/8.02  fof(f51,plain,(
% 59.77/8.02    ? [X0,X1] : ((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) & v1_relat_1(X1))),
% 59.77/8.02    inference(flattening,[],[f50])).
% 59.77/8.02  
% 59.77/8.02  fof(f52,plain,(
% 59.77/8.02    ? [X0,X1] : ((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) & v1_relat_1(X1)) => ((~r1_xboole_0(k2_relat_1(sK11),sK10) | k1_xboole_0 != k10_relat_1(sK11,sK10)) & (r1_xboole_0(k2_relat_1(sK11),sK10) | k1_xboole_0 = k10_relat_1(sK11,sK10)) & v1_relat_1(sK11))),
% 59.77/8.02    introduced(choice_axiom,[])).
% 59.77/8.02  
% 59.77/8.02  fof(f53,plain,(
% 59.77/8.02    (~r1_xboole_0(k2_relat_1(sK11),sK10) | k1_xboole_0 != k10_relat_1(sK11,sK10)) & (r1_xboole_0(k2_relat_1(sK11),sK10) | k1_xboole_0 = k10_relat_1(sK11,sK10)) & v1_relat_1(sK11)),
% 59.77/8.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11])],[f51,f52])).
% 59.77/8.02  
% 59.77/8.02  fof(f86,plain,(
% 59.77/8.02    r1_xboole_0(k2_relat_1(sK11),sK10) | k1_xboole_0 = k10_relat_1(sK11,sK10)),
% 59.77/8.02    inference(cnf_transformation,[],[f53])).
% 59.77/8.02  
% 59.77/8.02  fof(f3,axiom,(
% 59.77/8.02    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 59.77/8.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.77/8.02  
% 59.77/8.02  fof(f29,plain,(
% 59.77/8.02    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 59.77/8.02    inference(nnf_transformation,[],[f3])).
% 59.77/8.02  
% 59.77/8.02  fof(f61,plain,(
% 59.77/8.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 59.77/8.02    inference(cnf_transformation,[],[f29])).
% 59.77/8.02  
% 59.77/8.02  fof(f6,axiom,(
% 59.77/8.02    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 59.77/8.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.77/8.02  
% 59.77/8.02  fof(f66,plain,(
% 59.77/8.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 59.77/8.02    inference(cnf_transformation,[],[f6])).
% 59.77/8.02  
% 59.77/8.02  fof(f90,plain,(
% 59.77/8.02    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 59.77/8.02    inference(definition_unfolding,[],[f61,f66])).
% 59.77/8.02  
% 59.77/8.02  fof(f1,axiom,(
% 59.77/8.02    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 59.77/8.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.77/8.02  
% 59.77/8.02  fof(f54,plain,(
% 59.77/8.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 59.77/8.02    inference(cnf_transformation,[],[f1])).
% 59.77/8.02  
% 59.77/8.02  fof(f88,plain,(
% 59.77/8.02    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 59.77/8.02    inference(definition_unfolding,[],[f54,f66,f66])).
% 59.77/8.02  
% 59.77/8.02  fof(f9,axiom,(
% 59.77/8.02    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 59.77/8.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.77/8.02  
% 59.77/8.02  fof(f69,plain,(
% 59.77/8.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 59.77/8.02    inference(cnf_transformation,[],[f9])).
% 59.77/8.02  
% 59.77/8.02  fof(f93,plain,(
% 59.77/8.02    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 59.77/8.02    inference(definition_unfolding,[],[f69,f66])).
% 59.77/8.02  
% 59.77/8.02  fof(f2,axiom,(
% 59.77/8.02    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 59.77/8.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.77/8.02  
% 59.77/8.02  fof(f24,plain,(
% 59.77/8.02    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 59.77/8.02    inference(nnf_transformation,[],[f2])).
% 59.77/8.02  
% 59.77/8.02  fof(f25,plain,(
% 59.77/8.02    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 59.77/8.02    inference(flattening,[],[f24])).
% 59.77/8.02  
% 59.77/8.02  fof(f26,plain,(
% 59.77/8.02    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 59.77/8.02    inference(rectify,[],[f25])).
% 59.77/8.02  
% 59.77/8.02  fof(f27,plain,(
% 59.77/8.02    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 59.77/8.02    introduced(choice_axiom,[])).
% 59.77/8.02  
% 59.77/8.02  fof(f28,plain,(
% 59.77/8.02    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 59.77/8.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).
% 59.77/8.02  
% 59.77/8.02  fof(f57,plain,(
% 59.77/8.02    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 59.77/8.02    inference(cnf_transformation,[],[f28])).
% 59.77/8.02  
% 59.77/8.02  fof(f95,plain,(
% 59.77/8.02    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 59.77/8.02    inference(equality_resolution,[],[f57])).
% 59.77/8.02  
% 59.77/8.02  fof(f56,plain,(
% 59.77/8.02    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 59.77/8.02    inference(cnf_transformation,[],[f28])).
% 59.77/8.02  
% 59.77/8.02  fof(f96,plain,(
% 59.77/8.02    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 59.77/8.02    inference(equality_resolution,[],[f56])).
% 59.77/8.02  
% 59.77/8.02  fof(f85,plain,(
% 59.77/8.02    v1_relat_1(sK11)),
% 59.77/8.02    inference(cnf_transformation,[],[f53])).
% 59.77/8.02  
% 59.77/8.02  fof(f10,axiom,(
% 59.77/8.02    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))))),
% 59.77/8.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.77/8.02  
% 59.77/8.02  fof(f20,plain,(
% 59.77/8.02    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))) | ~v1_relat_1(X0))),
% 59.77/8.02    inference(ennf_transformation,[],[f10])).
% 59.77/8.02  
% 59.77/8.02  fof(f34,plain,(
% 59.77/8.02    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 59.77/8.02    inference(nnf_transformation,[],[f20])).
% 59.77/8.02  
% 59.77/8.02  fof(f35,plain,(
% 59.77/8.02    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0))) & (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X6,X8),X0)) | ~r2_hidden(X6,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 59.77/8.02    inference(rectify,[],[f34])).
% 59.77/8.02  
% 59.77/8.02  fof(f38,plain,(
% 59.77/8.02    ! [X6,X1,X0] : (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X6,X8),X0)) => (r2_hidden(sK5(X0,X1,X6),X1) & r2_hidden(k4_tarski(X6,sK5(X0,X1,X6)),X0)))),
% 59.77/8.02    introduced(choice_axiom,[])).
% 59.77/8.02  
% 59.77/8.02  fof(f37,plain,(
% 59.77/8.02    ( ! [X3] : (! [X2,X1,X0] : (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X3,X5),X0)) => (r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(k4_tarski(X3,sK4(X0,X1,X2)),X0)))) )),
% 59.77/8.02    introduced(choice_axiom,[])).
% 59.77/8.02  
% 59.77/8.02  fof(f36,plain,(
% 59.77/8.02    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(X3,X2))) => ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),X4),X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(sK3(X0,X1,X2),X5),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 59.77/8.02    introduced(choice_axiom,[])).
% 59.77/8.02  
% 59.77/8.02  fof(f39,plain,(
% 59.77/8.02    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),X4),X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0))) & ((r2_hidden(sK5(X0,X1,X6),X1) & r2_hidden(k4_tarski(X6,sK5(X0,X1,X6)),X0)) | ~r2_hidden(X6,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 59.77/8.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f35,f38,f37,f36])).
% 59.77/8.02  
% 59.77/8.02  fof(f72,plain,(
% 59.77/8.02    ( ! [X6,X2,X0,X7,X1] : (r2_hidden(X6,X2) | ~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0) | k10_relat_1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 59.77/8.02    inference(cnf_transformation,[],[f39])).
% 59.77/8.02  
% 59.77/8.02  fof(f98,plain,(
% 59.77/8.02    ( ! [X6,X0,X7,X1] : (r2_hidden(X6,k10_relat_1(X0,X1)) | ~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0) | ~v1_relat_1(X0)) )),
% 59.77/8.02    inference(equality_resolution,[],[f72])).
% 59.77/8.02  
% 59.77/8.02  fof(f13,axiom,(
% 59.77/8.02    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 59.77/8.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.77/8.02  
% 59.77/8.02  fof(f22,plain,(
% 59.77/8.02    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 59.77/8.02    inference(ennf_transformation,[],[f13])).
% 59.77/8.02  
% 59.77/8.02  fof(f84,plain,(
% 59.77/8.02    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 59.77/8.02    inference(cnf_transformation,[],[f22])).
% 59.77/8.02  
% 59.77/8.02  fof(f94,plain,(
% 59.77/8.02    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k4_xboole_0(k2_relat_1(X1),k4_xboole_0(k2_relat_1(X1),X0))) | ~v1_relat_1(X1)) )),
% 59.77/8.02    inference(definition_unfolding,[],[f84,f66])).
% 59.77/8.02  
% 59.77/8.02  fof(f55,plain,(
% 59.77/8.02    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 59.77/8.02    inference(cnf_transformation,[],[f28])).
% 59.77/8.02  
% 59.77/8.02  fof(f97,plain,(
% 59.77/8.02    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 59.77/8.02    inference(equality_resolution,[],[f55])).
% 59.77/8.02  
% 59.77/8.02  fof(f4,axiom,(
% 59.77/8.02    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 59.77/8.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.77/8.02  
% 59.77/8.02  fof(f16,plain,(
% 59.77/8.02    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 59.77/8.02    inference(rectify,[],[f4])).
% 59.77/8.02  
% 59.77/8.02  fof(f17,plain,(
% 59.77/8.02    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 59.77/8.02    inference(ennf_transformation,[],[f16])).
% 59.77/8.02  
% 59.77/8.02  fof(f30,plain,(
% 59.77/8.02    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)))),
% 59.77/8.02    introduced(choice_axiom,[])).
% 59.77/8.02  
% 59.77/8.02  fof(f31,plain,(
% 59.77/8.02    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 59.77/8.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f17,f30])).
% 59.77/8.02  
% 59.77/8.02  fof(f63,plain,(
% 59.77/8.02    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 59.77/8.02    inference(cnf_transformation,[],[f31])).
% 59.77/8.02  
% 59.77/8.02  fof(f92,plain,(
% 59.77/8.02    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) | r1_xboole_0(X0,X1)) )),
% 59.77/8.02    inference(definition_unfolding,[],[f63,f66])).
% 59.77/8.02  
% 59.77/8.02  fof(f87,plain,(
% 59.77/8.02    ~r1_xboole_0(k2_relat_1(sK11),sK10) | k1_xboole_0 != k10_relat_1(sK11,sK10)),
% 59.77/8.02    inference(cnf_transformation,[],[f53])).
% 59.77/8.02  
% 59.77/8.02  cnf(c_12,plain,
% 59.77/8.02      ( r1_xboole_0(X0,k1_xboole_0) ),
% 59.77/8.02      inference(cnf_transformation,[],[f67]) ).
% 59.77/8.02  
% 59.77/8.02  cnf(c_96256,plain,
% 59.77/8.02      ( r1_xboole_0(k1_tarski(sK8(sK11,sK1(k2_relat_1(sK11),sK10))),k1_xboole_0) ),
% 59.77/8.02      inference(instantiation,[status(thm)],[c_12]) ).
% 59.77/8.02  
% 59.77/8.02  cnf(c_22,plain,
% 59.77/8.02      ( r2_hidden(sK6(X0,X1),X1)
% 59.77/8.02      | r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0)
% 59.77/8.02      | k2_relat_1(X0) = X1 ),
% 59.77/8.02      inference(cnf_transformation,[],[f78]) ).
% 59.77/8.02  
% 59.77/8.02  cnf(c_1238,plain,
% 59.77/8.02      ( k2_relat_1(X0) = X1
% 59.77/8.02      | r2_hidden(sK6(X0,X1),X1) = iProver_top
% 59.77/8.02      | r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0) = iProver_top ),
% 59.77/8.02      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 59.77/8.02  
% 59.77/8.02  cnf(c_1247,plain,
% 59.77/8.02      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 59.77/8.02      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 59.77/8.02  
% 59.77/8.02  cnf(c_13,plain,
% 59.77/8.02      ( ~ r1_xboole_0(k1_tarski(X0),X1) | ~ r2_hidden(X0,X1) ),
% 59.77/8.02      inference(cnf_transformation,[],[f68]) ).
% 59.77/8.02  
% 59.77/8.02  cnf(c_1246,plain,
% 59.77/8.02      ( r1_xboole_0(k1_tarski(X0),X1) != iProver_top
% 59.77/8.02      | r2_hidden(X0,X1) != iProver_top ),
% 59.77/8.02      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 59.77/8.02  
% 59.77/8.02  cnf(c_2646,plain,
% 59.77/8.02      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 59.77/8.02      inference(superposition,[status(thm)],[c_1247,c_1246]) ).
% 59.77/8.02  
% 59.77/8.02  cnf(c_13304,plain,
% 59.77/8.02      ( k2_relat_1(k1_xboole_0) = X0
% 59.77/8.02      | r2_hidden(sK6(k1_xboole_0,X0),X0) = iProver_top ),
% 59.77/8.02      inference(superposition,[status(thm)],[c_1238,c_2646]) ).
% 59.77/8.02  
% 59.77/8.02  cnf(c_11,plain,
% 59.77/8.02      ( r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0 ),
% 59.77/8.02      inference(cnf_transformation,[],[f65]) ).
% 59.77/8.02  
% 59.77/8.02  cnf(c_1248,plain,
% 59.77/8.02      ( k1_xboole_0 = X0 | r2_hidden(sK2(X0),X0) = iProver_top ),
% 59.77/8.02      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 59.77/8.02  
% 59.77/8.02  cnf(c_24,plain,
% 59.77/8.02      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 59.77/8.02      | r2_hidden(k4_tarski(sK8(X1,X0),X0),X1) ),
% 59.77/8.02      inference(cnf_transformation,[],[f102]) ).
% 59.77/8.02  
% 59.77/8.02  cnf(c_1236,plain,
% 59.77/8.02      ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
% 59.77/8.02      | r2_hidden(k4_tarski(sK8(X1,X0),X0),X1) = iProver_top ),
% 59.77/8.02      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 59.77/8.02  
% 59.77/8.02  cnf(c_13305,plain,
% 59.77/8.02      ( r2_hidden(X0,k2_relat_1(k1_xboole_0)) != iProver_top ),
% 59.77/8.02      inference(superposition,[status(thm)],[c_1236,c_2646]) ).
% 59.77/8.02  
% 59.77/8.02  cnf(c_13514,plain,
% 59.77/8.02      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 59.77/8.02      inference(superposition,[status(thm)],[c_1248,c_13305]) ).
% 59.77/8.02  
% 59.77/8.02  cnf(c_14237,plain,
% 59.77/8.02      ( k1_xboole_0 = X0
% 59.77/8.02      | r2_hidden(sK6(k1_xboole_0,X0),X0) = iProver_top ),
% 59.77/8.02      inference(demodulation,[status(thm)],[c_13304,c_13514]) ).
% 59.77/8.02  
% 59.77/8.02  cnf(c_26,plain,
% 59.77/8.02      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 59.77/8.02      | r2_hidden(sK9(X0,X2,X1),X2)
% 59.77/8.02      | ~ v1_relat_1(X1) ),
% 59.77/8.02      inference(cnf_transformation,[],[f82]) ).
% 59.77/8.02  
% 59.77/8.02  cnf(c_1235,plain,
% 59.77/8.02      ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
% 59.77/8.02      | r2_hidden(sK9(X0,X2,X1),X2) = iProver_top
% 59.77/8.02      | v1_relat_1(X1) != iProver_top ),
% 59.77/8.02      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 59.77/8.02  
% 59.77/8.02  cnf(c_28,plain,
% 59.77/8.02      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 59.77/8.02      | r2_hidden(sK9(X0,X2,X1),k2_relat_1(X1))
% 59.77/8.02      | ~ v1_relat_1(X1) ),
% 59.77/8.02      inference(cnf_transformation,[],[f80]) ).
% 59.77/8.02  
% 59.77/8.02  cnf(c_1233,plain,
% 59.77/8.02      ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
% 59.77/8.02      | r2_hidden(sK9(X0,X2,X1),k2_relat_1(X1)) = iProver_top
% 59.77/8.02      | v1_relat_1(X1) != iProver_top ),
% 59.77/8.02      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 59.77/8.02  
% 59.77/8.02  cnf(c_31,negated_conjecture,
% 59.77/8.02      ( r1_xboole_0(k2_relat_1(sK11),sK10)
% 59.77/8.02      | k1_xboole_0 = k10_relat_1(sK11,sK10) ),
% 59.77/8.02      inference(cnf_transformation,[],[f86]) ).
% 59.77/8.02  
% 59.77/8.02  cnf(c_1230,plain,
% 59.77/8.02      ( k1_xboole_0 = k10_relat_1(sK11,sK10)
% 59.77/8.02      | r1_xboole_0(k2_relat_1(sK11),sK10) = iProver_top ),
% 59.77/8.02      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 59.77/8.02  
% 59.77/8.02  cnf(c_8,plain,
% 59.77/8.02      ( ~ r1_xboole_0(X0,X1)
% 59.77/8.02      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 59.77/8.02      inference(cnf_transformation,[],[f90]) ).
% 59.77/8.02  
% 59.77/8.02  cnf(c_1251,plain,
% 59.77/8.02      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 59.77/8.02      | r1_xboole_0(X0,X1) != iProver_top ),
% 59.77/8.02      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 59.77/8.02  
% 59.77/8.02  cnf(c_0,plain,
% 59.77/8.02      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 59.77/8.02      inference(cnf_transformation,[],[f88]) ).
% 59.77/8.02  
% 59.77/8.02  cnf(c_14,plain,
% 59.77/8.02      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
% 59.77/8.02      inference(cnf_transformation,[],[f93]) ).
% 59.77/8.02  
% 59.77/8.02  cnf(c_1269,plain,
% 59.77/8.02      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0)) ),
% 59.77/8.02      inference(light_normalisation,[status(thm)],[c_0,c_14]) ).
% 59.77/8.02  
% 59.77/8.02  cnf(c_1284,plain,
% 59.77/8.02      ( k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0
% 59.77/8.02      | r1_xboole_0(X1,X0) != iProver_top ),
% 59.77/8.02      inference(demodulation,[status(thm)],[c_1251,c_1269]) ).
% 59.77/8.02  
% 59.77/8.02  cnf(c_1627,plain,
% 59.77/8.02      ( k10_relat_1(sK11,sK10) = k1_xboole_0
% 59.77/8.02      | k1_setfam_1(k2_tarski(sK10,k2_relat_1(sK11))) = k1_xboole_0 ),
% 59.77/8.02      inference(superposition,[status(thm)],[c_1230,c_1284]) ).
% 59.77/8.02  
% 59.77/8.02  cnf(c_4,plain,
% 59.77/8.02      ( ~ r2_hidden(X0,X1)
% 59.77/8.02      | r2_hidden(X0,X2)
% 59.77/8.02      | r2_hidden(X0,k4_xboole_0(X1,X2)) ),
% 59.77/8.02      inference(cnf_transformation,[],[f95]) ).
% 59.77/8.02  
% 59.77/8.02  cnf(c_1255,plain,
% 59.77/8.02      ( r2_hidden(X0,X1) != iProver_top
% 59.77/8.02      | r2_hidden(X0,X2) = iProver_top
% 59.77/8.02      | r2_hidden(X0,k4_xboole_0(X1,X2)) = iProver_top ),
% 59.77/8.02      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 59.77/8.02  
% 59.77/8.02  cnf(c_6815,plain,
% 59.77/8.02      ( r2_hidden(X0,X1) != iProver_top
% 59.77/8.02      | r2_hidden(X0,k4_xboole_0(X1,X2)) = iProver_top
% 59.77/8.02      | r2_hidden(X0,k1_setfam_1(k2_tarski(X1,X2))) = iProver_top ),
% 59.77/8.02      inference(superposition,[status(thm)],[c_14,c_1255]) ).
% 59.77/8.02  
% 59.77/8.02  cnf(c_8595,plain,
% 59.77/8.02      ( k10_relat_1(sK11,sK10) = k1_xboole_0
% 59.77/8.02      | r2_hidden(X0,k4_xboole_0(sK10,k2_relat_1(sK11))) = iProver_top
% 59.77/8.02      | r2_hidden(X0,sK10) != iProver_top
% 59.77/8.02      | r2_hidden(X0,k1_xboole_0) = iProver_top ),
% 59.77/8.02      inference(superposition,[status(thm)],[c_1627,c_6815]) ).
% 59.77/8.02  
% 59.77/8.02  cnf(c_1556,plain,
% 59.77/8.02      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 59.77/8.02      inference(resolution,[status(thm)],[c_13,c_12]) ).
% 59.77/8.02  
% 59.77/8.02  cnf(c_1557,plain,
% 59.77/8.02      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 59.77/8.02      inference(predicate_to_equality,[status(thm)],[c_1556]) ).
% 59.77/8.02  
% 59.77/8.02  cnf(c_9213,plain,
% 59.77/8.02      ( r2_hidden(X0,sK10) != iProver_top
% 59.77/8.02      | r2_hidden(X0,k4_xboole_0(sK10,k2_relat_1(sK11))) = iProver_top
% 59.77/8.02      | k10_relat_1(sK11,sK10) = k1_xboole_0 ),
% 59.77/8.02      inference(global_propositional_subsumption,
% 59.77/8.02                [status(thm)],
% 59.77/8.02                [c_8595,c_1557]) ).
% 59.77/8.02  
% 59.77/8.02  cnf(c_9214,plain,
% 59.77/8.02      ( k10_relat_1(sK11,sK10) = k1_xboole_0
% 59.77/8.02      | r2_hidden(X0,k4_xboole_0(sK10,k2_relat_1(sK11))) = iProver_top
% 59.77/8.02      | r2_hidden(X0,sK10) != iProver_top ),
% 59.77/8.02      inference(renaming,[status(thm)],[c_9213]) ).
% 59.77/8.02  
% 59.77/8.02  cnf(c_5,plain,
% 59.77/8.02      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 59.77/8.02      inference(cnf_transformation,[],[f96]) ).
% 59.77/8.02  
% 59.77/8.02  cnf(c_1254,plain,
% 59.77/8.02      ( r2_hidden(X0,X1) != iProver_top
% 59.77/8.02      | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
% 59.77/8.02      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 59.77/8.02  
% 59.77/8.02  cnf(c_9224,plain,
% 59.77/8.02      ( k10_relat_1(sK11,sK10) = k1_xboole_0
% 59.77/8.02      | r2_hidden(X0,k2_relat_1(sK11)) != iProver_top
% 59.77/8.02      | r2_hidden(X0,sK10) != iProver_top ),
% 59.77/8.02      inference(superposition,[status(thm)],[c_9214,c_1254]) ).
% 59.77/8.02  
% 59.77/8.02  cnf(c_9562,plain,
% 59.77/8.02      ( k10_relat_1(sK11,sK10) = k1_xboole_0
% 59.77/8.02      | r2_hidden(X0,k10_relat_1(sK11,X1)) != iProver_top
% 59.77/8.02      | r2_hidden(sK9(X0,X1,sK11),sK10) != iProver_top
% 59.77/8.02      | v1_relat_1(sK11) != iProver_top ),
% 59.77/8.02      inference(superposition,[status(thm)],[c_1233,c_9224]) ).
% 59.77/8.02  
% 59.77/8.02  cnf(c_32,negated_conjecture,
% 59.77/8.02      ( v1_relat_1(sK11) ),
% 59.77/8.02      inference(cnf_transformation,[],[f85]) ).
% 59.77/8.02  
% 59.77/8.02  cnf(c_33,plain,
% 59.77/8.02      ( v1_relat_1(sK11) = iProver_top ),
% 59.77/8.02      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 59.77/8.02  
% 59.77/8.02  cnf(c_10512,plain,
% 59.77/8.02      ( r2_hidden(sK9(X0,X1,sK11),sK10) != iProver_top
% 59.77/8.02      | r2_hidden(X0,k10_relat_1(sK11,X1)) != iProver_top
% 59.77/8.02      | k10_relat_1(sK11,sK10) = k1_xboole_0 ),
% 59.77/8.02      inference(global_propositional_subsumption,
% 59.77/8.02                [status(thm)],
% 59.77/8.02                [c_9562,c_33]) ).
% 59.77/8.02  
% 59.77/8.02  cnf(c_10513,plain,
% 59.77/8.02      ( k10_relat_1(sK11,sK10) = k1_xboole_0
% 59.77/8.02      | r2_hidden(X0,k10_relat_1(sK11,X1)) != iProver_top
% 59.77/8.02      | r2_hidden(sK9(X0,X1,sK11),sK10) != iProver_top ),
% 59.77/8.02      inference(renaming,[status(thm)],[c_10512]) ).
% 59.77/8.02  
% 59.77/8.02  cnf(c_10521,plain,
% 59.77/8.02      ( k10_relat_1(sK11,sK10) = k1_xboole_0
% 59.77/8.02      | r2_hidden(X0,k10_relat_1(sK11,sK10)) != iProver_top
% 59.77/8.02      | v1_relat_1(sK11) != iProver_top ),
% 59.77/8.02      inference(superposition,[status(thm)],[c_1235,c_10513]) ).
% 59.77/8.02  
% 59.77/8.02  cnf(c_95478,plain,
% 59.77/8.02      ( r2_hidden(X0,k10_relat_1(sK11,sK10)) != iProver_top
% 59.77/8.02      | k10_relat_1(sK11,sK10) = k1_xboole_0 ),
% 59.77/8.02      inference(global_propositional_subsumption,
% 59.77/8.02                [status(thm)],
% 59.77/8.02                [c_10521,c_33]) ).
% 59.77/8.02  
% 59.77/8.02  cnf(c_95479,plain,
% 59.77/8.02      ( k10_relat_1(sK11,sK10) = k1_xboole_0
% 59.77/8.02      | r2_hidden(X0,k10_relat_1(sK11,sK10)) != iProver_top ),
% 59.77/8.02      inference(renaming,[status(thm)],[c_95478]) ).
% 59.77/8.02  
% 59.77/8.02  cnf(c_95502,plain,
% 59.77/8.02      ( k10_relat_1(sK11,sK10) = k1_xboole_0 ),
% 59.77/8.02      inference(superposition,[status(thm)],[c_14237,c_95479]) ).
% 59.77/8.02  
% 59.77/8.02  cnf(c_582,plain,( X0 = X0 ),theory(equality) ).
% 59.77/8.02  
% 59.77/8.02  cnf(c_23931,plain,
% 59.77/8.02      ( sK8(sK11,sK1(k2_relat_1(sK11),sK10)) = sK8(sK11,sK1(k2_relat_1(sK11),sK10)) ),
% 59.77/8.02      inference(instantiation,[status(thm)],[c_582]) ).
% 59.77/8.02  
% 59.77/8.02  cnf(c_585,plain,
% 59.77/8.02      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 59.77/8.02      theory(equality) ).
% 59.77/8.02  
% 59.77/8.02  cnf(c_10271,plain,
% 59.77/8.02      ( r2_hidden(X0,X1)
% 59.77/8.02      | ~ r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),k10_relat_1(sK11,k4_xboole_0(k2_relat_1(sK11),k4_xboole_0(k2_relat_1(sK11),sK10))))
% 59.77/8.02      | X0 != sK8(sK11,sK1(k2_relat_1(sK11),sK10))
% 59.77/8.02      | X1 != k10_relat_1(sK11,k4_xboole_0(k2_relat_1(sK11),k4_xboole_0(k2_relat_1(sK11),sK10))) ),
% 59.77/8.02      inference(instantiation,[status(thm)],[c_585]) ).
% 59.77/8.02  
% 59.77/8.02  cnf(c_23930,plain,
% 59.77/8.02      ( r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),X0)
% 59.77/8.02      | ~ r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),k10_relat_1(sK11,k4_xboole_0(k2_relat_1(sK11),k4_xboole_0(k2_relat_1(sK11),sK10))))
% 59.77/8.02      | X0 != k10_relat_1(sK11,k4_xboole_0(k2_relat_1(sK11),k4_xboole_0(k2_relat_1(sK11),sK10)))
% 59.77/8.02      | sK8(sK11,sK1(k2_relat_1(sK11),sK10)) != sK8(sK11,sK1(k2_relat_1(sK11),sK10)) ),
% 59.77/8.02      inference(instantiation,[status(thm)],[c_10271]) ).
% 59.77/8.02  
% 59.77/8.02  cnf(c_23933,plain,
% 59.77/8.02      ( ~ r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),k10_relat_1(sK11,k4_xboole_0(k2_relat_1(sK11),k4_xboole_0(k2_relat_1(sK11),sK10))))
% 59.77/8.02      | r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),k1_xboole_0)
% 59.77/8.02      | sK8(sK11,sK1(k2_relat_1(sK11),sK10)) != sK8(sK11,sK1(k2_relat_1(sK11),sK10))
% 59.77/8.02      | k1_xboole_0 != k10_relat_1(sK11,k4_xboole_0(k2_relat_1(sK11),k4_xboole_0(k2_relat_1(sK11),sK10))) ),
% 59.77/8.02      inference(instantiation,[status(thm)],[c_23930]) ).
% 59.77/8.02  
% 59.77/8.02  cnf(c_22914,plain,
% 59.77/8.02      ( ~ r1_xboole_0(k1_tarski(sK8(sK11,sK1(k2_relat_1(sK11),sK10))),X0)
% 59.77/8.02      | ~ r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),X0) ),
% 59.77/8.02      inference(instantiation,[status(thm)],[c_13]) ).
% 59.77/8.02  
% 59.77/8.02  cnf(c_22916,plain,
% 59.77/8.02      ( ~ r1_xboole_0(k1_tarski(sK8(sK11,sK1(k2_relat_1(sK11),sK10))),k1_xboole_0)
% 59.77/8.02      | ~ r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),k1_xboole_0) ),
% 59.77/8.02      inference(instantiation,[status(thm)],[c_22914]) ).
% 59.77/8.02  
% 59.77/8.02  cnf(c_18,plain,
% 59.77/8.02      ( ~ r2_hidden(X0,X1)
% 59.77/8.02      | r2_hidden(X2,k10_relat_1(X3,X1))
% 59.77/8.02      | ~ r2_hidden(k4_tarski(X2,X0),X3)
% 59.77/8.02      | ~ v1_relat_1(X3) ),
% 59.77/8.02      inference(cnf_transformation,[],[f98]) ).
% 59.77/8.02  
% 59.77/8.02  cnf(c_2752,plain,
% 59.77/8.02      ( r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),k10_relat_1(sK11,X0))
% 59.77/8.02      | ~ r2_hidden(k4_tarski(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),sK1(k2_relat_1(sK11),sK10)),sK11)
% 59.77/8.02      | ~ r2_hidden(sK1(k2_relat_1(sK11),sK10),X0)
% 59.77/8.02      | ~ v1_relat_1(sK11) ),
% 59.77/8.02      inference(instantiation,[status(thm)],[c_18]) ).
% 59.77/8.02  
% 59.77/8.02  cnf(c_9097,plain,
% 59.77/8.02      ( r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),k10_relat_1(sK11,k4_xboole_0(k2_relat_1(sK11),k4_xboole_0(k2_relat_1(sK11),sK10))))
% 59.77/8.02      | ~ r2_hidden(k4_tarski(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),sK1(k2_relat_1(sK11),sK10)),sK11)
% 59.77/8.02      | ~ r2_hidden(sK1(k2_relat_1(sK11),sK10),k4_xboole_0(k2_relat_1(sK11),k4_xboole_0(k2_relat_1(sK11),sK10)))
% 59.77/8.02      | ~ v1_relat_1(sK11) ),
% 59.77/8.02      inference(instantiation,[status(thm)],[c_2752]) ).
% 59.77/8.02  
% 59.77/8.02  cnf(c_583,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 59.77/8.02  
% 59.77/8.02  cnf(c_2687,plain,
% 59.77/8.02      ( X0 != X1 | X1 = X0 ),
% 59.77/8.02      inference(resolution,[status(thm)],[c_583,c_582]) ).
% 59.77/8.02  
% 59.77/8.02  cnf(c_4193,plain,
% 59.77/8.02      ( r1_xboole_0(k2_relat_1(sK11),sK10)
% 59.77/8.02      | k10_relat_1(sK11,sK10) = k1_xboole_0 ),
% 59.77/8.02      inference(resolution,[status(thm)],[c_2687,c_31]) ).
% 59.77/8.02  
% 59.77/8.02  cnf(c_4497,plain,
% 59.77/8.02      ( r1_xboole_0(k2_relat_1(sK11),sK10)
% 59.77/8.02      | X0 != k1_xboole_0
% 59.77/8.02      | k10_relat_1(sK11,sK10) = X0 ),
% 59.77/8.02      inference(resolution,[status(thm)],[c_4193,c_583]) ).
% 59.77/8.02  
% 59.77/8.02  cnf(c_2685,plain,
% 59.77/8.02      ( r1_xboole_0(k2_relat_1(sK11),sK10)
% 59.77/8.02      | X0 != k10_relat_1(sK11,sK10)
% 59.77/8.02      | k1_xboole_0 = X0 ),
% 59.77/8.02      inference(resolution,[status(thm)],[c_583,c_31]) ).
% 59.77/8.02  
% 59.77/8.02  cnf(c_5399,plain,
% 59.77/8.02      ( r1_xboole_0(k2_relat_1(sK11),sK10)
% 59.77/8.02      | k10_relat_1(sK11,sK10) != k1_xboole_0
% 59.77/8.02      | k1_xboole_0 = k10_relat_1(sK11,sK10) ),
% 59.77/8.02      inference(resolution,[status(thm)],[c_4497,c_2685]) ).
% 59.77/8.02  
% 59.77/8.02  cnf(c_601,plain,
% 59.77/8.02      ( k1_xboole_0 = k1_xboole_0 ),
% 59.77/8.02      inference(instantiation,[status(thm)],[c_582]) ).
% 59.77/8.02  
% 59.77/8.02  cnf(c_1846,plain,
% 59.77/8.02      ( k10_relat_1(sK11,sK10) != X0
% 59.77/8.02      | k1_xboole_0 != X0
% 59.77/8.02      | k1_xboole_0 = k10_relat_1(sK11,sK10) ),
% 59.77/8.02      inference(instantiation,[status(thm)],[c_583]) ).
% 59.77/8.02  
% 59.77/8.02  cnf(c_1847,plain,
% 59.77/8.02      ( k10_relat_1(sK11,sK10) != k1_xboole_0
% 59.77/8.02      | k1_xboole_0 = k10_relat_1(sK11,sK10)
% 59.77/8.02      | k1_xboole_0 != k1_xboole_0 ),
% 59.77/8.02      inference(instantiation,[status(thm)],[c_1846]) ).
% 59.77/8.02  
% 59.77/8.02  cnf(c_5445,plain,
% 59.77/8.02      ( k10_relat_1(sK11,sK10) != k1_xboole_0
% 59.77/8.02      | k1_xboole_0 = k10_relat_1(sK11,sK10) ),
% 59.77/8.02      inference(global_propositional_subsumption,
% 59.77/8.02                [status(thm)],
% 59.77/8.02                [c_5399,c_601,c_1847]) ).
% 59.77/8.02  
% 59.77/8.02  cnf(c_29,plain,
% 59.77/8.02      ( ~ v1_relat_1(X0)
% 59.77/8.02      | k10_relat_1(X0,k4_xboole_0(k2_relat_1(X0),k4_xboole_0(k2_relat_1(X0),X1))) = k10_relat_1(X0,X1) ),
% 59.77/8.02      inference(cnf_transformation,[],[f94]) ).
% 59.77/8.02  
% 59.77/8.02  cnf(c_4540,plain,
% 59.77/8.02      ( r1_xboole_0(k2_relat_1(sK11),sK10)
% 59.77/8.02      | ~ v1_relat_1(sK11)
% 59.77/8.02      | k1_xboole_0 = k10_relat_1(sK11,k4_xboole_0(k2_relat_1(sK11),k4_xboole_0(k2_relat_1(sK11),sK10))) ),
% 59.77/8.02      inference(resolution,[status(thm)],[c_29,c_2685]) ).
% 59.77/8.02  
% 59.77/8.02  cnf(c_1937,plain,
% 59.77/8.02      ( r2_hidden(k4_tarski(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),sK1(k2_relat_1(sK11),sK10)),sK11)
% 59.77/8.02      | ~ r2_hidden(sK1(k2_relat_1(sK11),sK10),k2_relat_1(sK11)) ),
% 59.77/8.02      inference(instantiation,[status(thm)],[c_24]) ).
% 59.77/8.02  
% 59.77/8.02  cnf(c_6,plain,
% 59.77/8.02      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
% 59.77/8.02      inference(cnf_transformation,[],[f97]) ).
% 59.77/8.02  
% 59.77/8.02  cnf(c_1690,plain,
% 59.77/8.02      ( ~ r2_hidden(sK1(k2_relat_1(sK11),sK10),k4_xboole_0(k2_relat_1(sK11),k4_xboole_0(k2_relat_1(sK11),sK10)))
% 59.77/8.02      | r2_hidden(sK1(k2_relat_1(sK11),sK10),k2_relat_1(sK11)) ),
% 59.77/8.02      inference(instantiation,[status(thm)],[c_6]) ).
% 59.77/8.02  
% 59.77/8.02  cnf(c_10,plain,
% 59.77/8.02      ( r1_xboole_0(X0,X1)
% 59.77/8.02      | r2_hidden(sK1(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 59.77/8.02      inference(cnf_transformation,[],[f92]) ).
% 59.77/8.02  
% 59.77/8.02  cnf(c_1537,plain,
% 59.77/8.02      ( r1_xboole_0(k2_relat_1(sK11),sK10)
% 59.77/8.02      | r2_hidden(sK1(k2_relat_1(sK11),sK10),k4_xboole_0(k2_relat_1(sK11),k4_xboole_0(k2_relat_1(sK11),sK10))) ),
% 59.77/8.02      inference(instantiation,[status(thm)],[c_10]) ).
% 59.77/8.02  
% 59.77/8.02  cnf(c_30,negated_conjecture,
% 59.77/8.02      ( ~ r1_xboole_0(k2_relat_1(sK11),sK10)
% 59.77/8.02      | k1_xboole_0 != k10_relat_1(sK11,sK10) ),
% 59.77/8.02      inference(cnf_transformation,[],[f87]) ).
% 59.77/8.02  
% 59.77/8.02  cnf(contradiction,plain,
% 59.77/8.02      ( $false ),
% 59.77/8.02      inference(minisat,
% 59.77/8.02                [status(thm)],
% 59.77/8.02                [c_96256,c_95502,c_23931,c_23933,c_22916,c_9097,c_5445,
% 59.77/8.02                 c_4540,c_1937,c_1690,c_1537,c_30,c_32]) ).
% 59.77/8.02  
% 59.77/8.02  
% 59.77/8.02  % SZS output end CNFRefutation for theBenchmark.p
% 59.77/8.02  
% 59.77/8.02  ------                               Statistics
% 59.77/8.02  
% 59.77/8.02  ------ Selected
% 59.77/8.02  
% 59.77/8.02  total_time:                             7.427
% 59.77/8.02  
%------------------------------------------------------------------------------
