%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:46:23 EST 2020

% Result     : Theorem 3.83s
% Output     : CNFRefutation 3.83s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 201 expanded)
%              Number of clauses        :   57 (  70 expanded)
%              Number of leaves         :   24 (  47 expanded)
%              Depth                    :   15
%              Number of atoms          :  387 ( 727 expanded)
%              Number of equality atoms :  109 ( 214 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   15 (   2 average)
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

fof(f15,plain,(
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

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f23])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k9_relat_1(X1,X0)
        <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k9_relat_1(X1,X0)
      <~> r1_xboole_0(k1_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f40,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k9_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k9_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f41,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k9_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k9_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f40])).

fof(f42,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k9_relat_1(X1,X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 = k9_relat_1(X1,X0) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_xboole_0(k1_relat_1(sK9),sK8)
        | k1_xboole_0 != k9_relat_1(sK9,sK8) )
      & ( r1_xboole_0(k1_relat_1(sK9),sK8)
        | k1_xboole_0 = k9_relat_1(sK9,sK8) )
      & v1_relat_1(sK9) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ( ~ r1_xboole_0(k1_relat_1(sK9),sK8)
      | k1_xboole_0 != k9_relat_1(sK9,sK8) )
    & ( r1_xboole_0(k1_relat_1(sK9),sK8)
      | k1_xboole_0 = k9_relat_1(sK9,sK8) )
    & v1_relat_1(sK9) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f41,f42])).

fof(f70,plain,
    ( r1_xboole_0(k1_relat_1(sK9),sK8)
    | k1_xboole_0 = k9_relat_1(sK9,sK8) ),
    inference(cnf_transformation,[],[f43])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k7_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k7_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X1,X0)
      | ~ r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f69,plain,(
    v1_relat_1(sK9) ),
    inference(cnf_transformation,[],[f43])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f11,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f5,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f3,axiom,(
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
    inference(rectify,[],[f3])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f18,f25])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f7,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f72,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(definition_unfolding,[],[f53,f50])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f31,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X8,X6),X0) )
     => ( r2_hidden(sK4(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(sK4(X0,X1,X6),X6),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(X5,X3),X0) )
     => ( r2_hidden(sK3(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK3(X0,X1,X2),X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
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
              | ~ r2_hidden(k4_tarski(X4,sK2(X0,X1,X2)),X0) )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X1)
              & r2_hidden(k4_tarski(X5,sK2(X0,X1,X2)),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(k4_tarski(X4,sK2(X0,X1,X2)),X0) )
                | ~ r2_hidden(sK2(X0,X1,X2),X2) )
              & ( ( r2_hidden(sK3(X0,X1,X2),X1)
                  & r2_hidden(k4_tarski(sK3(X0,X1,X2),sK2(X0,X1,X2)),X0) )
                | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X7,X6),X0) ) )
                & ( ( r2_hidden(sK4(X0,X1,X6),X1)
                    & r2_hidden(k4_tarski(sK4(X0,X1,X6),X6),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f28,f31,f30,f29])).

fof(f56,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X7,X6),X0)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f73,plain,(
    ! [X6,X0,X7,X1] :
      ( r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X7,X6),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f56])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f37,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK6(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK5(X0,X1),X3),X0)
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK5(X0,X1),X4),X0)
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK5(X0,X1),X3),X0)
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0)
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f34,f37,f36,f35])).

fof(f60,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f77,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f60])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f71,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK9),sK8)
    | k1_xboole_0 != k9_relat_1(sK9,sK8) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_272,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_15260,plain,
    ( sK7(sK9,sK0(k1_relat_1(sK9),sK8)) = sK7(sK9,sK0(k1_relat_1(sK9),sK8)) ),
    inference(instantiation,[status(thm)],[c_272])).

cnf(c_276,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_5280,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK7(sK9,sK0(k1_relat_1(sK9),sK8)),k9_relat_1(sK9,sK8))
    | X0 != sK7(sK9,sK0(k1_relat_1(sK9),sK8))
    | X1 != k9_relat_1(sK9,sK8) ),
    inference(instantiation,[status(thm)],[c_276])).

cnf(c_15259,plain,
    ( r2_hidden(sK7(sK9,sK0(k1_relat_1(sK9),sK8)),X0)
    | ~ r2_hidden(sK7(sK9,sK0(k1_relat_1(sK9),sK8)),k9_relat_1(sK9,sK8))
    | X0 != k9_relat_1(sK9,sK8)
    | sK7(sK9,sK0(k1_relat_1(sK9),sK8)) != sK7(sK9,sK0(k1_relat_1(sK9),sK8)) ),
    inference(instantiation,[status(thm)],[c_5280])).

cnf(c_15262,plain,
    ( ~ r2_hidden(sK7(sK9,sK0(k1_relat_1(sK9),sK8)),k9_relat_1(sK9,sK8))
    | r2_hidden(sK7(sK9,sK0(k1_relat_1(sK9),sK8)),k1_xboole_0)
    | sK7(sK9,sK0(k1_relat_1(sK9),sK8)) != sK7(sK9,sK0(k1_relat_1(sK9),sK8))
    | k1_xboole_0 != k9_relat_1(sK9,sK8) ),
    inference(instantiation,[status(thm)],[c_15259])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_5293,plain,
    ( ~ r2_hidden(sK7(sK9,sK0(k1_relat_1(sK9),sK8)),X0)
    | ~ r2_hidden(sK7(sK9,sK0(k1_relat_1(sK9),sK8)),k9_relat_1(sK9,sK8))
    | ~ r1_xboole_0(k9_relat_1(sK9,sK8),X0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_5295,plain,
    ( ~ r2_hidden(sK7(sK9,sK0(k1_relat_1(sK9),sK8)),k9_relat_1(sK9,sK8))
    | ~ r2_hidden(sK7(sK9,sK0(k1_relat_1(sK9),sK8)),k1_xboole_0)
    | ~ r1_xboole_0(k9_relat_1(sK9,sK8),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_5293])).

cnf(c_25,negated_conjecture,
    ( r1_xboole_0(k1_relat_1(sK9),sK8)
    | k1_xboole_0 = k9_relat_1(sK9,sK8) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_783,plain,
    ( k1_xboole_0 = k9_relat_1(sK9,sK8)
    | r1_xboole_0(k1_relat_1(sK9),sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_22,plain,
    ( ~ r1_xboole_0(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_786,plain,
    ( k7_relat_1(X0,X1) = k1_xboole_0
    | r1_xboole_0(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1866,plain,
    ( k7_relat_1(sK9,sK8) = k1_xboole_0
    | k9_relat_1(sK9,sK8) = k1_xboole_0
    | v1_relat_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_783,c_786])).

cnf(c_26,negated_conjecture,
    ( v1_relat_1(sK9) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1885,plain,
    ( ~ v1_relat_1(sK9)
    | k7_relat_1(sK9,sK8) = k1_xboole_0
    | k9_relat_1(sK9,sK8) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1866])).

cnf(c_4896,plain,
    ( k9_relat_1(sK9,sK8) = k1_xboole_0
    | k7_relat_1(sK9,sK8) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1866,c_26,c_1885])).

cnf(c_4897,plain,
    ( k7_relat_1(sK9,sK8) = k1_xboole_0
    | k9_relat_1(sK9,sK8) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_4896])).

cnf(c_782,plain,
    ( v1_relat_1(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_19,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_787,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1643,plain,
    ( k2_relat_1(k7_relat_1(sK9,X0)) = k9_relat_1(sK9,X0) ),
    inference(superposition,[status(thm)],[c_782,c_787])).

cnf(c_4901,plain,
    ( k9_relat_1(sK9,sK8) = k2_relat_1(k1_xboole_0)
    | k9_relat_1(sK9,sK8) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4897,c_1643])).

cnf(c_20,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_4904,plain,
    ( k9_relat_1(sK9,sK8) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4901,c_20])).

cnf(c_3381,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK9,sK8))
    | r2_hidden(X1,k1_xboole_0)
    | r1_xboole_0(k1_relat_1(sK9),sK8)
    | X1 != X0 ),
    inference(resolution,[status(thm)],[c_276,c_25])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_3516,plain,
    ( r2_hidden(X0,k1_xboole_0)
    | r1_xboole_0(k9_relat_1(sK9,sK8),X1)
    | r1_xboole_0(k1_relat_1(sK9),sK8)
    | X0 != sK0(k9_relat_1(sK9,sK8),X1) ),
    inference(resolution,[status(thm)],[c_3381,c_3])).

cnf(c_6,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_800,plain,
    ( r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top
    | r1_xboole_0(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1749,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | r1_xboole_0(X1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_800])).

cnf(c_8,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_798,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1275,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_798])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1281,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1275,c_7])).

cnf(c_1893,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1749,c_1281])).

cnf(c_1894,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1893])).

cnf(c_3817,plain,
    ( r1_xboole_0(k9_relat_1(sK9,sK8),X1)
    | r1_xboole_0(k1_relat_1(sK9),sK8)
    | X0 != sK0(k9_relat_1(sK9,sK8),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3516,c_1894])).

cnf(c_3818,plain,
    ( r1_xboole_0(k9_relat_1(sK9,sK8),X0)
    | r1_xboole_0(k1_relat_1(sK9),sK8)
    | X1 != sK0(k9_relat_1(sK9,sK8),X0) ),
    inference(renaming,[status(thm)],[c_3817])).

cnf(c_3839,plain,
    ( r1_xboole_0(k9_relat_1(sK9,sK8),X0)
    | r1_xboole_0(k1_relat_1(sK9),sK8) ),
    inference(resolution,[status(thm)],[c_3818,c_7])).

cnf(c_3841,plain,
    ( r1_xboole_0(k9_relat_1(sK9,sK8),k1_xboole_0)
    | r1_xboole_0(k1_relat_1(sK9),sK8) ),
    inference(instantiation,[status(thm)],[c_3839])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k9_relat_1(X3,X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X3)
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1217,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2))
    | ~ r2_hidden(k4_tarski(sK0(X3,X2),X0),X1)
    | ~ r2_hidden(sK0(X3,X2),X2)
    | ~ v1_relat_1(X1) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1850,plain,
    ( r2_hidden(sK7(sK9,sK0(k1_relat_1(sK9),sK8)),k9_relat_1(sK9,sK8))
    | ~ r2_hidden(k4_tarski(sK0(k1_relat_1(sK9),sK8),sK7(sK9,sK0(k1_relat_1(sK9),sK8))),sK9)
    | ~ r2_hidden(sK0(k1_relat_1(sK9),sK8),sK8)
    | ~ v1_relat_1(sK9) ),
    inference(instantiation,[status(thm)],[c_1217])).

cnf(c_273,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1365,plain,
    ( k9_relat_1(sK9,sK8) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k9_relat_1(sK9,sK8) ),
    inference(instantiation,[status(thm)],[c_273])).

cnf(c_1366,plain,
    ( k9_relat_1(sK9,sK8) != k1_xboole_0
    | k1_xboole_0 = k9_relat_1(sK9,sK8)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1365])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,sK7(X1,X0)),X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1150,plain,
    ( r2_hidden(k4_tarski(sK0(k1_relat_1(sK9),sK8),sK7(sK9,sK0(k1_relat_1(sK9),sK8))),sK9)
    | ~ r2_hidden(sK0(k1_relat_1(sK9),sK8),k1_relat_1(sK9)) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1010,plain,
    ( r2_hidden(sK0(k1_relat_1(sK9),sK8),k1_relat_1(sK9))
    | r1_xboole_0(k1_relat_1(sK9),sK8) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1007,plain,
    ( r2_hidden(sK0(k1_relat_1(sK9),sK8),sK8)
    | r1_xboole_0(k1_relat_1(sK9),sK8) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_292,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_272])).

cnf(c_24,negated_conjecture,
    ( ~ r1_xboole_0(k1_relat_1(sK9),sK8)
    | k1_xboole_0 != k9_relat_1(sK9,sK8) ),
    inference(cnf_transformation,[],[f71])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_15260,c_15262,c_5295,c_4904,c_3841,c_1850,c_1366,c_1150,c_1010,c_1007,c_292,c_24,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 09:57:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.83/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.83/0.99  
% 3.83/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.83/0.99  
% 3.83/0.99  ------  iProver source info
% 3.83/0.99  
% 3.83/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.83/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.83/0.99  git: non_committed_changes: false
% 3.83/0.99  git: last_make_outside_of_git: false
% 3.83/0.99  
% 3.83/0.99  ------ 
% 3.83/0.99  
% 3.83/0.99  ------ Input Options
% 3.83/0.99  
% 3.83/0.99  --out_options                           all
% 3.83/0.99  --tptp_safe_out                         true
% 3.83/0.99  --problem_path                          ""
% 3.83/0.99  --include_path                          ""
% 3.83/0.99  --clausifier                            res/vclausify_rel
% 3.83/0.99  --clausifier_options                    --mode clausify
% 3.83/0.99  --stdin                                 false
% 3.83/0.99  --stats_out                             sel
% 3.83/0.99  
% 3.83/0.99  ------ General Options
% 3.83/0.99  
% 3.83/0.99  --fof                                   false
% 3.83/0.99  --time_out_real                         604.99
% 3.83/0.99  --time_out_virtual                      -1.
% 3.83/0.99  --symbol_type_check                     false
% 3.83/0.99  --clausify_out                          false
% 3.83/0.99  --sig_cnt_out                           false
% 3.83/0.99  --trig_cnt_out                          false
% 3.83/0.99  --trig_cnt_out_tolerance                1.
% 3.83/0.99  --trig_cnt_out_sk_spl                   false
% 3.83/0.99  --abstr_cl_out                          false
% 3.83/0.99  
% 3.83/0.99  ------ Global Options
% 3.83/0.99  
% 3.83/0.99  --schedule                              none
% 3.83/0.99  --add_important_lit                     false
% 3.83/0.99  --prop_solver_per_cl                    1000
% 3.83/0.99  --min_unsat_core                        false
% 3.83/0.99  --soft_assumptions                      false
% 3.83/0.99  --soft_lemma_size                       3
% 3.83/0.99  --prop_impl_unit_size                   0
% 3.83/0.99  --prop_impl_unit                        []
% 3.83/0.99  --share_sel_clauses                     true
% 3.83/0.99  --reset_solvers                         false
% 3.83/0.99  --bc_imp_inh                            [conj_cone]
% 3.83/0.99  --conj_cone_tolerance                   3.
% 3.83/0.99  --extra_neg_conj                        none
% 3.83/0.99  --large_theory_mode                     true
% 3.83/0.99  --prolific_symb_bound                   200
% 3.83/0.99  --lt_threshold                          2000
% 3.83/0.99  --clause_weak_htbl                      true
% 3.83/0.99  --gc_record_bc_elim                     false
% 3.83/0.99  
% 3.83/0.99  ------ Preprocessing Options
% 3.83/0.99  
% 3.83/0.99  --preprocessing_flag                    true
% 3.83/0.99  --time_out_prep_mult                    0.1
% 3.83/0.99  --splitting_mode                        input
% 3.83/0.99  --splitting_grd                         true
% 3.83/0.99  --splitting_cvd                         false
% 3.83/0.99  --splitting_cvd_svl                     false
% 3.83/0.99  --splitting_nvd                         32
% 3.83/0.99  --sub_typing                            true
% 3.83/0.99  --prep_gs_sim                           false
% 3.83/0.99  --prep_unflatten                        true
% 3.83/0.99  --prep_res_sim                          true
% 3.83/0.99  --prep_upred                            true
% 3.83/0.99  --prep_sem_filter                       exhaustive
% 3.83/0.99  --prep_sem_filter_out                   false
% 3.83/0.99  --pred_elim                             false
% 3.83/0.99  --res_sim_input                         true
% 3.83/0.99  --eq_ax_congr_red                       true
% 3.83/0.99  --pure_diseq_elim                       true
% 3.83/0.99  --brand_transform                       false
% 3.83/0.99  --non_eq_to_eq                          false
% 3.83/0.99  --prep_def_merge                        true
% 3.83/0.99  --prep_def_merge_prop_impl              false
% 3.83/0.99  --prep_def_merge_mbd                    true
% 3.83/0.99  --prep_def_merge_tr_red                 false
% 3.83/0.99  --prep_def_merge_tr_cl                  false
% 3.83/0.99  --smt_preprocessing                     true
% 3.83/0.99  --smt_ac_axioms                         fast
% 3.83/0.99  --preprocessed_out                      false
% 3.83/0.99  --preprocessed_stats                    false
% 3.83/0.99  
% 3.83/0.99  ------ Abstraction refinement Options
% 3.83/0.99  
% 3.83/0.99  --abstr_ref                             []
% 3.83/0.99  --abstr_ref_prep                        false
% 3.83/0.99  --abstr_ref_until_sat                   false
% 3.83/0.99  --abstr_ref_sig_restrict                funpre
% 3.83/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.83/0.99  --abstr_ref_under                       []
% 3.83/0.99  
% 3.83/0.99  ------ SAT Options
% 3.83/0.99  
% 3.83/0.99  --sat_mode                              false
% 3.83/0.99  --sat_fm_restart_options                ""
% 3.83/0.99  --sat_gr_def                            false
% 3.83/0.99  --sat_epr_types                         true
% 3.83/0.99  --sat_non_cyclic_types                  false
% 3.83/0.99  --sat_finite_models                     false
% 3.83/0.99  --sat_fm_lemmas                         false
% 3.83/0.99  --sat_fm_prep                           false
% 3.83/0.99  --sat_fm_uc_incr                        true
% 3.83/0.99  --sat_out_model                         small
% 3.83/0.99  --sat_out_clauses                       false
% 3.83/0.99  
% 3.83/0.99  ------ QBF Options
% 3.83/0.99  
% 3.83/0.99  --qbf_mode                              false
% 3.83/0.99  --qbf_elim_univ                         false
% 3.83/0.99  --qbf_dom_inst                          none
% 3.83/0.99  --qbf_dom_pre_inst                      false
% 3.83/0.99  --qbf_sk_in                             false
% 3.83/0.99  --qbf_pred_elim                         true
% 3.83/0.99  --qbf_split                             512
% 3.83/0.99  
% 3.83/0.99  ------ BMC1 Options
% 3.83/0.99  
% 3.83/0.99  --bmc1_incremental                      false
% 3.83/0.99  --bmc1_axioms                           reachable_all
% 3.83/0.99  --bmc1_min_bound                        0
% 3.83/0.99  --bmc1_max_bound                        -1
% 3.83/0.99  --bmc1_max_bound_default                -1
% 3.83/0.99  --bmc1_symbol_reachability              true
% 3.83/0.99  --bmc1_property_lemmas                  false
% 3.83/0.99  --bmc1_k_induction                      false
% 3.83/0.99  --bmc1_non_equiv_states                 false
% 3.83/0.99  --bmc1_deadlock                         false
% 3.83/0.99  --bmc1_ucm                              false
% 3.83/0.99  --bmc1_add_unsat_core                   none
% 3.83/0.99  --bmc1_unsat_core_children              false
% 3.83/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.83/0.99  --bmc1_out_stat                         full
% 3.83/0.99  --bmc1_ground_init                      false
% 3.83/0.99  --bmc1_pre_inst_next_state              false
% 3.83/0.99  --bmc1_pre_inst_state                   false
% 3.83/0.99  --bmc1_pre_inst_reach_state             false
% 3.83/0.99  --bmc1_out_unsat_core                   false
% 3.83/0.99  --bmc1_aig_witness_out                  false
% 3.83/0.99  --bmc1_verbose                          false
% 3.83/0.99  --bmc1_dump_clauses_tptp                false
% 3.83/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.83/0.99  --bmc1_dump_file                        -
% 3.83/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.83/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.83/0.99  --bmc1_ucm_extend_mode                  1
% 3.83/0.99  --bmc1_ucm_init_mode                    2
% 3.83/0.99  --bmc1_ucm_cone_mode                    none
% 3.83/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.83/0.99  --bmc1_ucm_relax_model                  4
% 3.83/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.83/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.83/0.99  --bmc1_ucm_layered_model                none
% 3.83/0.99  --bmc1_ucm_max_lemma_size               10
% 3.83/0.99  
% 3.83/0.99  ------ AIG Options
% 3.83/0.99  
% 3.83/0.99  --aig_mode                              false
% 3.83/0.99  
% 3.83/0.99  ------ Instantiation Options
% 3.83/0.99  
% 3.83/0.99  --instantiation_flag                    true
% 3.83/0.99  --inst_sos_flag                         false
% 3.83/0.99  --inst_sos_phase                        true
% 3.83/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.83/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.83/0.99  --inst_lit_sel_side                     num_symb
% 3.83/0.99  --inst_solver_per_active                1400
% 3.83/0.99  --inst_solver_calls_frac                1.
% 3.83/0.99  --inst_passive_queue_type               priority_queues
% 3.83/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.83/0.99  --inst_passive_queues_freq              [25;2]
% 3.83/0.99  --inst_dismatching                      true
% 3.83/0.99  --inst_eager_unprocessed_to_passive     true
% 3.83/0.99  --inst_prop_sim_given                   true
% 3.83/0.99  --inst_prop_sim_new                     false
% 3.83/0.99  --inst_subs_new                         false
% 3.83/0.99  --inst_eq_res_simp                      false
% 3.83/0.99  --inst_subs_given                       false
% 3.83/0.99  --inst_orphan_elimination               true
% 3.83/0.99  --inst_learning_loop_flag               true
% 3.83/0.99  --inst_learning_start                   3000
% 3.83/0.99  --inst_learning_factor                  2
% 3.83/0.99  --inst_start_prop_sim_after_learn       3
% 3.83/0.99  --inst_sel_renew                        solver
% 3.83/0.99  --inst_lit_activity_flag                true
% 3.83/0.99  --inst_restr_to_given                   false
% 3.83/0.99  --inst_activity_threshold               500
% 3.83/0.99  --inst_out_proof                        true
% 3.83/0.99  
% 3.83/0.99  ------ Resolution Options
% 3.83/0.99  
% 3.83/0.99  --resolution_flag                       true
% 3.83/0.99  --res_lit_sel                           adaptive
% 3.83/0.99  --res_lit_sel_side                      none
% 3.83/0.99  --res_ordering                          kbo
% 3.83/0.99  --res_to_prop_solver                    active
% 3.83/0.99  --res_prop_simpl_new                    false
% 3.83/0.99  --res_prop_simpl_given                  true
% 3.83/0.99  --res_passive_queue_type                priority_queues
% 3.83/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.83/0.99  --res_passive_queues_freq               [15;5]
% 3.83/0.99  --res_forward_subs                      full
% 3.83/0.99  --res_backward_subs                     full
% 3.83/0.99  --res_forward_subs_resolution           true
% 3.83/0.99  --res_backward_subs_resolution          true
% 3.83/0.99  --res_orphan_elimination                true
% 3.83/0.99  --res_time_limit                        2.
% 3.83/0.99  --res_out_proof                         true
% 3.83/0.99  
% 3.83/0.99  ------ Superposition Options
% 3.83/0.99  
% 3.83/0.99  --superposition_flag                    true
% 3.83/0.99  --sup_passive_queue_type                priority_queues
% 3.83/0.99  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.83/0.99  --sup_passive_queues_freq               [1;4]
% 3.83/0.99  --demod_completeness_check              fast
% 3.83/0.99  --demod_use_ground                      true
% 3.83/0.99  --sup_to_prop_solver                    passive
% 3.83/0.99  --sup_prop_simpl_new                    true
% 3.83/0.99  --sup_prop_simpl_given                  true
% 3.83/0.99  --sup_fun_splitting                     false
% 3.83/0.99  --sup_smt_interval                      50000
% 3.83/0.99  
% 3.83/0.99  ------ Superposition Simplification Setup
% 3.83/0.99  
% 3.83/0.99  --sup_indices_passive                   []
% 3.83/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.83/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.83/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.83/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.83/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.83/0.99  --sup_full_bw                           [BwDemod]
% 3.83/0.99  --sup_immed_triv                        [TrivRules]
% 3.83/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.83/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.83/0.99  --sup_immed_bw_main                     []
% 3.83/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.83/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.83/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.83/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.83/0.99  
% 3.83/0.99  ------ Combination Options
% 3.83/0.99  
% 3.83/0.99  --comb_res_mult                         3
% 3.83/0.99  --comb_sup_mult                         2
% 3.83/0.99  --comb_inst_mult                        10
% 3.83/0.99  
% 3.83/0.99  ------ Debug Options
% 3.83/0.99  
% 3.83/0.99  --dbg_backtrace                         false
% 3.83/0.99  --dbg_dump_prop_clauses                 false
% 3.83/0.99  --dbg_dump_prop_clauses_file            -
% 3.83/0.99  --dbg_out_stat                          false
% 3.83/0.99  ------ Parsing...
% 3.83/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.83/0.99  
% 3.83/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.83/0.99  
% 3.83/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.83/0.99  
% 3.83/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.83/0.99  ------ Proving...
% 3.83/0.99  ------ Problem Properties 
% 3.83/0.99  
% 3.83/0.99  
% 3.83/0.99  clauses                                 27
% 3.83/0.99  conjectures                             3
% 3.83/0.99  EPR                                     2
% 3.83/0.99  Horn                                    20
% 3.83/0.99  unary                                   7
% 3.83/0.99  binary                                  9
% 3.83/0.99  lits                                    63
% 3.83/0.99  lits eq                                 15
% 3.83/0.99  fd_pure                                 0
% 3.83/0.99  fd_pseudo                               0
% 3.83/0.99  fd_cond                                 0
% 3.83/0.99  fd_pseudo_cond                          5
% 3.83/0.99  AC symbols                              0
% 3.83/0.99  
% 3.83/0.99  ------ Input Options Time Limit: Unbounded
% 3.83/0.99  
% 3.83/0.99  
% 3.83/0.99  ------ 
% 3.83/0.99  Current options:
% 3.83/0.99  ------ 
% 3.83/0.99  
% 3.83/0.99  ------ Input Options
% 3.83/0.99  
% 3.83/0.99  --out_options                           all
% 3.83/0.99  --tptp_safe_out                         true
% 3.83/0.99  --problem_path                          ""
% 3.83/0.99  --include_path                          ""
% 3.83/0.99  --clausifier                            res/vclausify_rel
% 3.83/0.99  --clausifier_options                    --mode clausify
% 3.83/0.99  --stdin                                 false
% 3.83/0.99  --stats_out                             sel
% 3.83/0.99  
% 3.83/0.99  ------ General Options
% 3.83/0.99  
% 3.83/0.99  --fof                                   false
% 3.83/0.99  --time_out_real                         604.99
% 3.83/0.99  --time_out_virtual                      -1.
% 3.83/0.99  --symbol_type_check                     false
% 3.83/0.99  --clausify_out                          false
% 3.83/0.99  --sig_cnt_out                           false
% 3.83/0.99  --trig_cnt_out                          false
% 3.83/0.99  --trig_cnt_out_tolerance                1.
% 3.83/0.99  --trig_cnt_out_sk_spl                   false
% 3.83/0.99  --abstr_cl_out                          false
% 3.83/0.99  
% 3.83/0.99  ------ Global Options
% 3.83/0.99  
% 3.83/0.99  --schedule                              none
% 3.83/0.99  --add_important_lit                     false
% 3.83/0.99  --prop_solver_per_cl                    1000
% 3.83/0.99  --min_unsat_core                        false
% 3.83/0.99  --soft_assumptions                      false
% 3.83/0.99  --soft_lemma_size                       3
% 3.83/0.99  --prop_impl_unit_size                   0
% 3.83/0.99  --prop_impl_unit                        []
% 3.83/0.99  --share_sel_clauses                     true
% 3.83/0.99  --reset_solvers                         false
% 3.83/0.99  --bc_imp_inh                            [conj_cone]
% 3.83/0.99  --conj_cone_tolerance                   3.
% 3.83/0.99  --extra_neg_conj                        none
% 3.83/0.99  --large_theory_mode                     true
% 3.83/0.99  --prolific_symb_bound                   200
% 3.83/0.99  --lt_threshold                          2000
% 3.83/0.99  --clause_weak_htbl                      true
% 3.83/0.99  --gc_record_bc_elim                     false
% 3.83/0.99  
% 3.83/0.99  ------ Preprocessing Options
% 3.83/0.99  
% 3.83/0.99  --preprocessing_flag                    true
% 3.83/0.99  --time_out_prep_mult                    0.1
% 3.83/0.99  --splitting_mode                        input
% 3.83/0.99  --splitting_grd                         true
% 3.83/0.99  --splitting_cvd                         false
% 3.83/0.99  --splitting_cvd_svl                     false
% 3.83/0.99  --splitting_nvd                         32
% 3.83/0.99  --sub_typing                            true
% 3.83/0.99  --prep_gs_sim                           false
% 3.83/0.99  --prep_unflatten                        true
% 3.83/0.99  --prep_res_sim                          true
% 3.83/0.99  --prep_upred                            true
% 3.83/0.99  --prep_sem_filter                       exhaustive
% 3.83/0.99  --prep_sem_filter_out                   false
% 3.83/0.99  --pred_elim                             false
% 3.83/0.99  --res_sim_input                         true
% 3.83/0.99  --eq_ax_congr_red                       true
% 3.83/0.99  --pure_diseq_elim                       true
% 3.83/0.99  --brand_transform                       false
% 3.83/0.99  --non_eq_to_eq                          false
% 3.83/0.99  --prep_def_merge                        true
% 3.83/0.99  --prep_def_merge_prop_impl              false
% 3.83/0.99  --prep_def_merge_mbd                    true
% 3.83/0.99  --prep_def_merge_tr_red                 false
% 3.83/0.99  --prep_def_merge_tr_cl                  false
% 3.83/0.99  --smt_preprocessing                     true
% 3.83/0.99  --smt_ac_axioms                         fast
% 3.83/0.99  --preprocessed_out                      false
% 3.83/0.99  --preprocessed_stats                    false
% 3.83/0.99  
% 3.83/0.99  ------ Abstraction refinement Options
% 3.83/0.99  
% 3.83/0.99  --abstr_ref                             []
% 3.83/0.99  --abstr_ref_prep                        false
% 3.83/0.99  --abstr_ref_until_sat                   false
% 3.83/0.99  --abstr_ref_sig_restrict                funpre
% 3.83/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.83/0.99  --abstr_ref_under                       []
% 3.83/0.99  
% 3.83/0.99  ------ SAT Options
% 3.83/0.99  
% 3.83/0.99  --sat_mode                              false
% 3.83/0.99  --sat_fm_restart_options                ""
% 3.83/0.99  --sat_gr_def                            false
% 3.83/0.99  --sat_epr_types                         true
% 3.83/0.99  --sat_non_cyclic_types                  false
% 3.83/0.99  --sat_finite_models                     false
% 3.83/0.99  --sat_fm_lemmas                         false
% 3.83/0.99  --sat_fm_prep                           false
% 3.83/0.99  --sat_fm_uc_incr                        true
% 3.83/0.99  --sat_out_model                         small
% 3.83/0.99  --sat_out_clauses                       false
% 3.83/0.99  
% 3.83/0.99  ------ QBF Options
% 3.83/0.99  
% 3.83/0.99  --qbf_mode                              false
% 3.83/0.99  --qbf_elim_univ                         false
% 3.83/0.99  --qbf_dom_inst                          none
% 3.83/0.99  --qbf_dom_pre_inst                      false
% 3.83/0.99  --qbf_sk_in                             false
% 3.83/0.99  --qbf_pred_elim                         true
% 3.83/0.99  --qbf_split                             512
% 3.83/0.99  
% 3.83/0.99  ------ BMC1 Options
% 3.83/0.99  
% 3.83/0.99  --bmc1_incremental                      false
% 3.83/0.99  --bmc1_axioms                           reachable_all
% 3.83/0.99  --bmc1_min_bound                        0
% 3.83/0.99  --bmc1_max_bound                        -1
% 3.83/0.99  --bmc1_max_bound_default                -1
% 3.83/0.99  --bmc1_symbol_reachability              true
% 3.83/0.99  --bmc1_property_lemmas                  false
% 3.83/0.99  --bmc1_k_induction                      false
% 3.83/0.99  --bmc1_non_equiv_states                 false
% 3.83/0.99  --bmc1_deadlock                         false
% 3.83/0.99  --bmc1_ucm                              false
% 3.83/0.99  --bmc1_add_unsat_core                   none
% 3.83/0.99  --bmc1_unsat_core_children              false
% 3.83/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.83/0.99  --bmc1_out_stat                         full
% 3.83/0.99  --bmc1_ground_init                      false
% 3.83/0.99  --bmc1_pre_inst_next_state              false
% 3.83/0.99  --bmc1_pre_inst_state                   false
% 3.83/0.99  --bmc1_pre_inst_reach_state             false
% 3.83/0.99  --bmc1_out_unsat_core                   false
% 3.83/0.99  --bmc1_aig_witness_out                  false
% 3.83/0.99  --bmc1_verbose                          false
% 3.83/0.99  --bmc1_dump_clauses_tptp                false
% 3.83/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.83/0.99  --bmc1_dump_file                        -
% 3.83/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.83/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.83/0.99  --bmc1_ucm_extend_mode                  1
% 3.83/0.99  --bmc1_ucm_init_mode                    2
% 3.83/0.99  --bmc1_ucm_cone_mode                    none
% 3.83/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.83/0.99  --bmc1_ucm_relax_model                  4
% 3.83/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.83/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.83/0.99  --bmc1_ucm_layered_model                none
% 3.83/0.99  --bmc1_ucm_max_lemma_size               10
% 3.83/0.99  
% 3.83/0.99  ------ AIG Options
% 3.83/0.99  
% 3.83/0.99  --aig_mode                              false
% 3.83/0.99  
% 3.83/0.99  ------ Instantiation Options
% 3.83/0.99  
% 3.83/0.99  --instantiation_flag                    true
% 3.83/0.99  --inst_sos_flag                         false
% 3.83/0.99  --inst_sos_phase                        true
% 3.83/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.83/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.83/0.99  --inst_lit_sel_side                     num_symb
% 3.83/0.99  --inst_solver_per_active                1400
% 3.83/0.99  --inst_solver_calls_frac                1.
% 3.83/0.99  --inst_passive_queue_type               priority_queues
% 3.83/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.83/0.99  --inst_passive_queues_freq              [25;2]
% 3.83/0.99  --inst_dismatching                      true
% 3.83/0.99  --inst_eager_unprocessed_to_passive     true
% 3.83/0.99  --inst_prop_sim_given                   true
% 3.83/0.99  --inst_prop_sim_new                     false
% 3.83/0.99  --inst_subs_new                         false
% 3.83/0.99  --inst_eq_res_simp                      false
% 3.83/0.99  --inst_subs_given                       false
% 3.83/0.99  --inst_orphan_elimination               true
% 3.83/0.99  --inst_learning_loop_flag               true
% 3.83/0.99  --inst_learning_start                   3000
% 3.83/0.99  --inst_learning_factor                  2
% 3.83/0.99  --inst_start_prop_sim_after_learn       3
% 3.83/0.99  --inst_sel_renew                        solver
% 3.83/0.99  --inst_lit_activity_flag                true
% 3.83/0.99  --inst_restr_to_given                   false
% 3.83/0.99  --inst_activity_threshold               500
% 3.83/0.99  --inst_out_proof                        true
% 3.83/0.99  
% 3.83/0.99  ------ Resolution Options
% 3.83/0.99  
% 3.83/0.99  --resolution_flag                       true
% 3.83/0.99  --res_lit_sel                           adaptive
% 3.83/0.99  --res_lit_sel_side                      none
% 3.83/0.99  --res_ordering                          kbo
% 3.83/0.99  --res_to_prop_solver                    active
% 3.83/0.99  --res_prop_simpl_new                    false
% 3.83/0.99  --res_prop_simpl_given                  true
% 3.83/0.99  --res_passive_queue_type                priority_queues
% 3.83/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.83/0.99  --res_passive_queues_freq               [15;5]
% 3.83/0.99  --res_forward_subs                      full
% 3.83/0.99  --res_backward_subs                     full
% 3.83/0.99  --res_forward_subs_resolution           true
% 3.83/0.99  --res_backward_subs_resolution          true
% 3.83/0.99  --res_orphan_elimination                true
% 3.83/0.99  --res_time_limit                        2.
% 3.83/0.99  --res_out_proof                         true
% 3.83/0.99  
% 3.83/0.99  ------ Superposition Options
% 3.83/0.99  
% 3.83/0.99  --superposition_flag                    true
% 3.83/0.99  --sup_passive_queue_type                priority_queues
% 3.83/0.99  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.83/0.99  --sup_passive_queues_freq               [1;4]
% 3.83/0.99  --demod_completeness_check              fast
% 3.83/0.99  --demod_use_ground                      true
% 3.83/0.99  --sup_to_prop_solver                    passive
% 3.83/0.99  --sup_prop_simpl_new                    true
% 3.83/0.99  --sup_prop_simpl_given                  true
% 3.83/0.99  --sup_fun_splitting                     false
% 3.83/0.99  --sup_smt_interval                      50000
% 3.83/0.99  
% 3.83/0.99  ------ Superposition Simplification Setup
% 3.83/0.99  
% 3.83/0.99  --sup_indices_passive                   []
% 3.83/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.83/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.83/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.83/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.83/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.83/0.99  --sup_full_bw                           [BwDemod]
% 3.83/0.99  --sup_immed_triv                        [TrivRules]
% 3.83/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.83/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.83/0.99  --sup_immed_bw_main                     []
% 3.83/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.83/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.83/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.83/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.83/0.99  
% 3.83/0.99  ------ Combination Options
% 3.83/0.99  
% 3.83/0.99  --comb_res_mult                         3
% 3.83/0.99  --comb_sup_mult                         2
% 3.83/0.99  --comb_inst_mult                        10
% 3.83/0.99  
% 3.83/0.99  ------ Debug Options
% 3.83/0.99  
% 3.83/0.99  --dbg_backtrace                         false
% 3.83/0.99  --dbg_dump_prop_clauses                 false
% 3.83/0.99  --dbg_dump_prop_clauses_file            -
% 3.83/0.99  --dbg_out_stat                          false
% 3.83/0.99  
% 3.83/0.99  
% 3.83/0.99  
% 3.83/0.99  
% 3.83/0.99  ------ Proving...
% 3.83/0.99  
% 3.83/0.99  
% 3.83/0.99  % SZS status Theorem for theBenchmark.p
% 3.83/0.99  
% 3.83/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.83/0.99  
% 3.83/0.99  fof(f2,axiom,(
% 3.83/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.83/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/0.99  
% 3.83/0.99  fof(f15,plain,(
% 3.83/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.83/0.99    inference(rectify,[],[f2])).
% 3.83/0.99  
% 3.83/0.99  fof(f17,plain,(
% 3.83/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 3.83/0.99    inference(ennf_transformation,[],[f15])).
% 3.83/0.99  
% 3.83/0.99  fof(f23,plain,(
% 3.83/0.99    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.83/0.99    introduced(choice_axiom,[])).
% 3.83/0.99  
% 3.83/0.99  fof(f24,plain,(
% 3.83/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 3.83/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f23])).
% 3.83/0.99  
% 3.83/0.99  fof(f47,plain,(
% 3.83/0.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 3.83/0.99    inference(cnf_transformation,[],[f24])).
% 3.83/0.99  
% 3.83/0.99  fof(f13,conjecture,(
% 3.83/0.99    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 3.83/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/0.99  
% 3.83/0.99  fof(f14,negated_conjecture,(
% 3.83/0.99    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 3.83/0.99    inference(negated_conjecture,[],[f13])).
% 3.83/0.99  
% 3.83/0.99  fof(f22,plain,(
% 3.83/0.99    ? [X0,X1] : ((k1_xboole_0 = k9_relat_1(X1,X0) <~> r1_xboole_0(k1_relat_1(X1),X0)) & v1_relat_1(X1))),
% 3.83/0.99    inference(ennf_transformation,[],[f14])).
% 3.83/0.99  
% 3.83/0.99  fof(f40,plain,(
% 3.83/0.99    ? [X0,X1] : (((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k9_relat_1(X1,X0))) & v1_relat_1(X1))),
% 3.83/0.99    inference(nnf_transformation,[],[f22])).
% 3.83/0.99  
% 3.83/0.99  fof(f41,plain,(
% 3.83/0.99    ? [X0,X1] : ((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k9_relat_1(X1,X0)) & v1_relat_1(X1))),
% 3.83/0.99    inference(flattening,[],[f40])).
% 3.83/0.99  
% 3.83/0.99  fof(f42,plain,(
% 3.83/0.99    ? [X0,X1] : ((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k9_relat_1(X1,X0)) & v1_relat_1(X1)) => ((~r1_xboole_0(k1_relat_1(sK9),sK8) | k1_xboole_0 != k9_relat_1(sK9,sK8)) & (r1_xboole_0(k1_relat_1(sK9),sK8) | k1_xboole_0 = k9_relat_1(sK9,sK8)) & v1_relat_1(sK9))),
% 3.83/0.99    introduced(choice_axiom,[])).
% 3.83/0.99  
% 3.83/0.99  fof(f43,plain,(
% 3.83/0.99    (~r1_xboole_0(k1_relat_1(sK9),sK8) | k1_xboole_0 != k9_relat_1(sK9,sK8)) & (r1_xboole_0(k1_relat_1(sK9),sK8) | k1_xboole_0 = k9_relat_1(sK9,sK8)) & v1_relat_1(sK9)),
% 3.83/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f41,f42])).
% 3.83/0.99  
% 3.83/0.99  fof(f70,plain,(
% 3.83/0.99    r1_xboole_0(k1_relat_1(sK9),sK8) | k1_xboole_0 = k9_relat_1(sK9,sK8)),
% 3.83/0.99    inference(cnf_transformation,[],[f43])).
% 3.83/0.99  
% 3.83/0.99  fof(f12,axiom,(
% 3.83/0.99    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 3.83/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/0.99  
% 3.83/0.99  fof(f21,plain,(
% 3.83/0.99    ! [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.83/0.99    inference(ennf_transformation,[],[f12])).
% 3.83/0.99  
% 3.83/0.99  fof(f39,plain,(
% 3.83/0.99    ! [X0,X1] : (((k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.83/0.99    inference(nnf_transformation,[],[f21])).
% 3.83/0.99  
% 3.83/0.99  fof(f68,plain,(
% 3.83/0.99    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.83/0.99    inference(cnf_transformation,[],[f39])).
% 3.83/0.99  
% 3.83/0.99  fof(f69,plain,(
% 3.83/0.99    v1_relat_1(sK9)),
% 3.83/0.99    inference(cnf_transformation,[],[f43])).
% 3.83/0.99  
% 3.83/0.99  fof(f10,axiom,(
% 3.83/0.99    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)))),
% 3.83/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/0.99  
% 3.83/0.99  fof(f20,plain,(
% 3.83/0.99    ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 3.83/0.99    inference(ennf_transformation,[],[f10])).
% 3.83/0.99  
% 3.83/0.99  fof(f64,plain,(
% 3.83/0.99    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 3.83/0.99    inference(cnf_transformation,[],[f20])).
% 3.83/0.99  
% 3.83/0.99  fof(f11,axiom,(
% 3.83/0.99    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.83/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/0.99  
% 3.83/0.99  fof(f66,plain,(
% 3.83/0.99    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 3.83/0.99    inference(cnf_transformation,[],[f11])).
% 3.83/0.99  
% 3.83/0.99  fof(f45,plain,(
% 3.83/0.99    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 3.83/0.99    inference(cnf_transformation,[],[f24])).
% 3.83/0.99  
% 3.83/0.99  fof(f5,axiom,(
% 3.83/0.99    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 3.83/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/0.99  
% 3.83/0.99  fof(f51,plain,(
% 3.83/0.99    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 3.83/0.99    inference(cnf_transformation,[],[f5])).
% 3.83/0.99  
% 3.83/0.99  fof(f3,axiom,(
% 3.83/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.83/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/0.99  
% 3.83/0.99  fof(f16,plain,(
% 3.83/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.83/0.99    inference(rectify,[],[f3])).
% 3.83/0.99  
% 3.83/0.99  fof(f18,plain,(
% 3.83/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.83/0.99    inference(ennf_transformation,[],[f16])).
% 3.83/0.99  
% 3.83/0.99  fof(f25,plain,(
% 3.83/0.99    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)))),
% 3.83/0.99    introduced(choice_axiom,[])).
% 3.83/0.99  
% 3.83/0.99  fof(f26,plain,(
% 3.83/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.83/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f18,f25])).
% 3.83/0.99  
% 3.83/0.99  fof(f49,plain,(
% 3.83/0.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 3.83/0.99    inference(cnf_transformation,[],[f26])).
% 3.83/0.99  
% 3.83/0.99  fof(f7,axiom,(
% 3.83/0.99    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 3.83/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/0.99  
% 3.83/0.99  fof(f53,plain,(
% 3.83/0.99    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 3.83/0.99    inference(cnf_transformation,[],[f7])).
% 3.83/0.99  
% 3.83/0.99  fof(f4,axiom,(
% 3.83/0.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.83/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/0.99  
% 3.83/0.99  fof(f50,plain,(
% 3.83/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.83/0.99    inference(cnf_transformation,[],[f4])).
% 3.83/0.99  
% 3.83/0.99  fof(f72,plain,(
% 3.83/0.99    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 3.83/0.99    inference(definition_unfolding,[],[f53,f50])).
% 3.83/0.99  
% 3.83/0.99  fof(f6,axiom,(
% 3.83/0.99    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 3.83/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/0.99  
% 3.83/0.99  fof(f52,plain,(
% 3.83/0.99    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.83/0.99    inference(cnf_transformation,[],[f6])).
% 3.83/0.99  
% 3.83/0.99  fof(f8,axiom,(
% 3.83/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)))))),
% 3.83/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/0.99  
% 3.83/0.99  fof(f19,plain,(
% 3.83/0.99    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)))) | ~v1_relat_1(X0))),
% 3.83/0.99    inference(ennf_transformation,[],[f8])).
% 3.83/0.99  
% 3.83/0.99  fof(f27,plain,(
% 3.83/0.99    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,X3),X0)) | ~r2_hidden(X3,X2)) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,X3),X0))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)) | ~r2_hidden(X3,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 3.83/0.99    inference(nnf_transformation,[],[f19])).
% 3.83/0.99  
% 3.83/0.99  fof(f28,plain,(
% 3.83/0.99    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,X3),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X3),X0)) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X7,X6),X0))) & (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X8,X6),X0)) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 3.83/0.99    inference(rectify,[],[f27])).
% 3.83/0.99  
% 3.83/0.99  fof(f31,plain,(
% 3.83/0.99    ! [X6,X1,X0] : (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X8,X6),X0)) => (r2_hidden(sK4(X0,X1,X6),X1) & r2_hidden(k4_tarski(sK4(X0,X1,X6),X6),X0)))),
% 3.83/0.99    introduced(choice_axiom,[])).
% 3.83/0.99  
% 3.83/0.99  fof(f30,plain,(
% 3.83/0.99    ( ! [X3] : (! [X2,X1,X0] : (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X3),X0)) => (r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK3(X0,X1,X2),X3),X0)))) )),
% 3.83/0.99    introduced(choice_axiom,[])).
% 3.83/0.99  
% 3.83/0.99  fof(f29,plain,(
% 3.83/0.99    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,X3),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X3),X0)) | r2_hidden(X3,X2))) => ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,sK2(X0,X1,X2)),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,sK2(X0,X1,X2)),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 3.83/0.99    introduced(choice_axiom,[])).
% 3.83/0.99  
% 3.83/0.99  fof(f32,plain,(
% 3.83/0.99    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,sK2(X0,X1,X2)),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK3(X0,X1,X2),sK2(X0,X1,X2)),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X7,X6),X0))) & ((r2_hidden(sK4(X0,X1,X6),X1) & r2_hidden(k4_tarski(sK4(X0,X1,X6),X6),X0)) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 3.83/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f28,f31,f30,f29])).
% 3.83/0.99  
% 3.83/0.99  fof(f56,plain,(
% 3.83/0.99    ( ! [X6,X2,X0,X7,X1] : (r2_hidden(X6,X2) | ~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X7,X6),X0) | k9_relat_1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 3.83/0.99    inference(cnf_transformation,[],[f32])).
% 3.83/0.99  
% 3.83/0.99  fof(f73,plain,(
% 3.83/0.99    ( ! [X6,X0,X7,X1] : (r2_hidden(X6,k9_relat_1(X0,X1)) | ~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X7,X6),X0) | ~v1_relat_1(X0)) )),
% 3.83/0.99    inference(equality_resolution,[],[f56])).
% 3.83/0.99  
% 3.83/0.99  fof(f9,axiom,(
% 3.83/0.99    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 3.83/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/0.99  
% 3.83/0.99  fof(f33,plain,(
% 3.83/0.99    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 3.83/0.99    inference(nnf_transformation,[],[f9])).
% 3.83/0.99  
% 3.83/0.99  fof(f34,plain,(
% 3.83/0.99    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 3.83/0.99    inference(rectify,[],[f33])).
% 3.83/0.99  
% 3.83/0.99  fof(f37,plain,(
% 3.83/0.99    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0))),
% 3.83/0.99    introduced(choice_axiom,[])).
% 3.83/0.99  
% 3.83/0.99  fof(f36,plain,(
% 3.83/0.99    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) => r2_hidden(k4_tarski(X2,sK6(X0,X1)),X0))) )),
% 3.83/0.99    introduced(choice_axiom,[])).
% 3.83/0.99  
% 3.83/0.99  fof(f35,plain,(
% 3.83/0.99    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK5(X0,X1),X3),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK5(X0,X1),X4),X0) | r2_hidden(sK5(X0,X1),X1))))),
% 3.83/0.99    introduced(choice_axiom,[])).
% 3.83/0.99  
% 3.83/0.99  fof(f38,plain,(
% 3.83/0.99    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK5(X0,X1),X3),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0) | r2_hidden(sK5(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 3.83/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f34,f37,f36,f35])).
% 3.83/0.99  
% 3.83/0.99  fof(f60,plain,(
% 3.83/0.99    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 3.83/0.99    inference(cnf_transformation,[],[f38])).
% 3.83/0.99  
% 3.83/0.99  fof(f77,plain,(
% 3.83/0.99    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 3.83/0.99    inference(equality_resolution,[],[f60])).
% 3.83/0.99  
% 3.83/0.99  fof(f46,plain,(
% 3.83/0.99    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 3.83/0.99    inference(cnf_transformation,[],[f24])).
% 3.83/0.99  
% 3.83/0.99  fof(f71,plain,(
% 3.83/0.99    ~r1_xboole_0(k1_relat_1(sK9),sK8) | k1_xboole_0 != k9_relat_1(sK9,sK8)),
% 3.83/0.99    inference(cnf_transformation,[],[f43])).
% 3.83/0.99  
% 3.83/0.99  cnf(c_272,plain,( X0 = X0 ),theory(equality) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_15260,plain,
% 3.83/0.99      ( sK7(sK9,sK0(k1_relat_1(sK9),sK8)) = sK7(sK9,sK0(k1_relat_1(sK9),sK8)) ),
% 3.83/0.99      inference(instantiation,[status(thm)],[c_272]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_276,plain,
% 3.83/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.83/0.99      theory(equality) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_5280,plain,
% 3.83/0.99      ( r2_hidden(X0,X1)
% 3.83/0.99      | ~ r2_hidden(sK7(sK9,sK0(k1_relat_1(sK9),sK8)),k9_relat_1(sK9,sK8))
% 3.83/0.99      | X0 != sK7(sK9,sK0(k1_relat_1(sK9),sK8))
% 3.83/0.99      | X1 != k9_relat_1(sK9,sK8) ),
% 3.83/0.99      inference(instantiation,[status(thm)],[c_276]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_15259,plain,
% 3.83/0.99      ( r2_hidden(sK7(sK9,sK0(k1_relat_1(sK9),sK8)),X0)
% 3.83/0.99      | ~ r2_hidden(sK7(sK9,sK0(k1_relat_1(sK9),sK8)),k9_relat_1(sK9,sK8))
% 3.83/0.99      | X0 != k9_relat_1(sK9,sK8)
% 3.83/0.99      | sK7(sK9,sK0(k1_relat_1(sK9),sK8)) != sK7(sK9,sK0(k1_relat_1(sK9),sK8)) ),
% 3.83/0.99      inference(instantiation,[status(thm)],[c_5280]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_15262,plain,
% 3.83/0.99      ( ~ r2_hidden(sK7(sK9,sK0(k1_relat_1(sK9),sK8)),k9_relat_1(sK9,sK8))
% 3.83/0.99      | r2_hidden(sK7(sK9,sK0(k1_relat_1(sK9),sK8)),k1_xboole_0)
% 3.83/0.99      | sK7(sK9,sK0(k1_relat_1(sK9),sK8)) != sK7(sK9,sK0(k1_relat_1(sK9),sK8))
% 3.83/0.99      | k1_xboole_0 != k9_relat_1(sK9,sK8) ),
% 3.83/0.99      inference(instantiation,[status(thm)],[c_15259]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_1,plain,
% 3.83/0.99      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 3.83/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_5293,plain,
% 3.83/0.99      ( ~ r2_hidden(sK7(sK9,sK0(k1_relat_1(sK9),sK8)),X0)
% 3.83/0.99      | ~ r2_hidden(sK7(sK9,sK0(k1_relat_1(sK9),sK8)),k9_relat_1(sK9,sK8))
% 3.83/0.99      | ~ r1_xboole_0(k9_relat_1(sK9,sK8),X0) ),
% 3.83/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_5295,plain,
% 3.83/0.99      ( ~ r2_hidden(sK7(sK9,sK0(k1_relat_1(sK9),sK8)),k9_relat_1(sK9,sK8))
% 3.83/0.99      | ~ r2_hidden(sK7(sK9,sK0(k1_relat_1(sK9),sK8)),k1_xboole_0)
% 3.83/0.99      | ~ r1_xboole_0(k9_relat_1(sK9,sK8),k1_xboole_0) ),
% 3.83/0.99      inference(instantiation,[status(thm)],[c_5293]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_25,negated_conjecture,
% 3.83/0.99      ( r1_xboole_0(k1_relat_1(sK9),sK8)
% 3.83/0.99      | k1_xboole_0 = k9_relat_1(sK9,sK8) ),
% 3.83/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_783,plain,
% 3.83/0.99      ( k1_xboole_0 = k9_relat_1(sK9,sK8)
% 3.83/0.99      | r1_xboole_0(k1_relat_1(sK9),sK8) = iProver_top ),
% 3.83/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_22,plain,
% 3.83/0.99      ( ~ r1_xboole_0(k1_relat_1(X0),X1)
% 3.83/0.99      | ~ v1_relat_1(X0)
% 3.83/0.99      | k7_relat_1(X0,X1) = k1_xboole_0 ),
% 3.83/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_786,plain,
% 3.83/0.99      ( k7_relat_1(X0,X1) = k1_xboole_0
% 3.83/0.99      | r1_xboole_0(k1_relat_1(X0),X1) != iProver_top
% 3.83/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.83/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_1866,plain,
% 3.83/0.99      ( k7_relat_1(sK9,sK8) = k1_xboole_0
% 3.83/0.99      | k9_relat_1(sK9,sK8) = k1_xboole_0
% 3.83/0.99      | v1_relat_1(sK9) != iProver_top ),
% 3.83/0.99      inference(superposition,[status(thm)],[c_783,c_786]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_26,negated_conjecture,
% 3.83/0.99      ( v1_relat_1(sK9) ),
% 3.83/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_1885,plain,
% 3.83/0.99      ( ~ v1_relat_1(sK9)
% 3.83/0.99      | k7_relat_1(sK9,sK8) = k1_xboole_0
% 3.83/0.99      | k9_relat_1(sK9,sK8) = k1_xboole_0 ),
% 3.83/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_1866]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_4896,plain,
% 3.83/0.99      ( k9_relat_1(sK9,sK8) = k1_xboole_0
% 3.83/0.99      | k7_relat_1(sK9,sK8) = k1_xboole_0 ),
% 3.83/0.99      inference(global_propositional_subsumption,
% 3.83/0.99                [status(thm)],
% 3.83/0.99                [c_1866,c_26,c_1885]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_4897,plain,
% 3.83/0.99      ( k7_relat_1(sK9,sK8) = k1_xboole_0
% 3.83/0.99      | k9_relat_1(sK9,sK8) = k1_xboole_0 ),
% 3.83/0.99      inference(renaming,[status(thm)],[c_4896]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_782,plain,
% 3.83/0.99      ( v1_relat_1(sK9) = iProver_top ),
% 3.83/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_19,plain,
% 3.83/0.99      ( ~ v1_relat_1(X0)
% 3.83/0.99      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 3.83/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_787,plain,
% 3.83/0.99      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 3.83/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.83/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_1643,plain,
% 3.83/0.99      ( k2_relat_1(k7_relat_1(sK9,X0)) = k9_relat_1(sK9,X0) ),
% 3.83/0.99      inference(superposition,[status(thm)],[c_782,c_787]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_4901,plain,
% 3.83/0.99      ( k9_relat_1(sK9,sK8) = k2_relat_1(k1_xboole_0)
% 3.83/0.99      | k9_relat_1(sK9,sK8) = k1_xboole_0 ),
% 3.83/0.99      inference(superposition,[status(thm)],[c_4897,c_1643]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_20,plain,
% 3.83/0.99      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.83/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_4904,plain,
% 3.83/0.99      ( k9_relat_1(sK9,sK8) = k1_xboole_0 ),
% 3.83/0.99      inference(light_normalisation,[status(thm)],[c_4901,c_20]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_3381,plain,
% 3.83/0.99      ( ~ r2_hidden(X0,k9_relat_1(sK9,sK8))
% 3.83/0.99      | r2_hidden(X1,k1_xboole_0)
% 3.83/0.99      | r1_xboole_0(k1_relat_1(sK9),sK8)
% 3.83/0.99      | X1 != X0 ),
% 3.83/0.99      inference(resolution,[status(thm)],[c_276,c_25]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_3,plain,
% 3.83/0.99      ( r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1) ),
% 3.83/0.99      inference(cnf_transformation,[],[f45]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_3516,plain,
% 3.83/0.99      ( r2_hidden(X0,k1_xboole_0)
% 3.83/0.99      | r1_xboole_0(k9_relat_1(sK9,sK8),X1)
% 3.83/0.99      | r1_xboole_0(k1_relat_1(sK9),sK8)
% 3.83/0.99      | X0 != sK0(k9_relat_1(sK9,sK8),X1) ),
% 3.83/0.99      inference(resolution,[status(thm)],[c_3381,c_3]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_6,plain,
% 3.83/0.99      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.83/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_4,plain,
% 3.83/0.99      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2)) | ~ r1_xboole_0(X1,X2) ),
% 3.83/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_800,plain,
% 3.83/0.99      ( r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top
% 3.83/0.99      | r1_xboole_0(X1,X2) != iProver_top ),
% 3.83/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_1749,plain,
% 3.83/0.99      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 3.83/0.99      | r1_xboole_0(X1,k1_xboole_0) != iProver_top ),
% 3.83/0.99      inference(superposition,[status(thm)],[c_6,c_800]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_8,plain,
% 3.83/0.99      ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
% 3.83/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_798,plain,
% 3.83/0.99      ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) = iProver_top ),
% 3.83/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_1275,plain,
% 3.83/0.99      ( r1_xboole_0(k5_xboole_0(X0,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 3.83/0.99      inference(superposition,[status(thm)],[c_6,c_798]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_7,plain,
% 3.83/0.99      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.83/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_1281,plain,
% 3.83/0.99      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 3.83/0.99      inference(light_normalisation,[status(thm)],[c_1275,c_7]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_1893,plain,
% 3.83/0.99      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.83/0.99      inference(forward_subsumption_resolution,
% 3.83/0.99                [status(thm)],
% 3.83/0.99                [c_1749,c_1281]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_1894,plain,
% 3.83/0.99      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 3.83/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_1893]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_3817,plain,
% 3.83/0.99      ( r1_xboole_0(k9_relat_1(sK9,sK8),X1)
% 3.83/0.99      | r1_xboole_0(k1_relat_1(sK9),sK8)
% 3.83/0.99      | X0 != sK0(k9_relat_1(sK9,sK8),X1) ),
% 3.83/0.99      inference(global_propositional_subsumption,
% 3.83/0.99                [status(thm)],
% 3.83/0.99                [c_3516,c_1894]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_3818,plain,
% 3.83/0.99      ( r1_xboole_0(k9_relat_1(sK9,sK8),X0)
% 3.83/0.99      | r1_xboole_0(k1_relat_1(sK9),sK8)
% 3.83/0.99      | X1 != sK0(k9_relat_1(sK9,sK8),X0) ),
% 3.83/0.99      inference(renaming,[status(thm)],[c_3817]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_3839,plain,
% 3.83/0.99      ( r1_xboole_0(k9_relat_1(sK9,sK8),X0)
% 3.83/0.99      | r1_xboole_0(k1_relat_1(sK9),sK8) ),
% 3.83/0.99      inference(resolution,[status(thm)],[c_3818,c_7]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_3841,plain,
% 3.83/0.99      ( r1_xboole_0(k9_relat_1(sK9,sK8),k1_xboole_0)
% 3.83/0.99      | r1_xboole_0(k1_relat_1(sK9),sK8) ),
% 3.83/0.99      inference(instantiation,[status(thm)],[c_3839]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_12,plain,
% 3.83/0.99      ( ~ r2_hidden(X0,X1)
% 3.83/0.99      | r2_hidden(X2,k9_relat_1(X3,X1))
% 3.83/0.99      | ~ r2_hidden(k4_tarski(X0,X2),X3)
% 3.83/0.99      | ~ v1_relat_1(X3) ),
% 3.83/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_1217,plain,
% 3.83/0.99      ( r2_hidden(X0,k9_relat_1(X1,X2))
% 3.83/0.99      | ~ r2_hidden(k4_tarski(sK0(X3,X2),X0),X1)
% 3.83/0.99      | ~ r2_hidden(sK0(X3,X2),X2)
% 3.83/0.99      | ~ v1_relat_1(X1) ),
% 3.83/0.99      inference(instantiation,[status(thm)],[c_12]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_1850,plain,
% 3.83/0.99      ( r2_hidden(sK7(sK9,sK0(k1_relat_1(sK9),sK8)),k9_relat_1(sK9,sK8))
% 3.83/0.99      | ~ r2_hidden(k4_tarski(sK0(k1_relat_1(sK9),sK8),sK7(sK9,sK0(k1_relat_1(sK9),sK8))),sK9)
% 3.83/0.99      | ~ r2_hidden(sK0(k1_relat_1(sK9),sK8),sK8)
% 3.83/0.99      | ~ v1_relat_1(sK9) ),
% 3.83/0.99      inference(instantiation,[status(thm)],[c_1217]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_273,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_1365,plain,
% 3.83/0.99      ( k9_relat_1(sK9,sK8) != X0
% 3.83/0.99      | k1_xboole_0 != X0
% 3.83/0.99      | k1_xboole_0 = k9_relat_1(sK9,sK8) ),
% 3.83/0.99      inference(instantiation,[status(thm)],[c_273]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_1366,plain,
% 3.83/0.99      ( k9_relat_1(sK9,sK8) != k1_xboole_0
% 3.83/0.99      | k1_xboole_0 = k9_relat_1(sK9,sK8)
% 3.83/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.83/0.99      inference(instantiation,[status(thm)],[c_1365]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_18,plain,
% 3.83/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.83/0.99      | r2_hidden(k4_tarski(X0,sK7(X1,X0)),X1) ),
% 3.83/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_1150,plain,
% 3.83/0.99      ( r2_hidden(k4_tarski(sK0(k1_relat_1(sK9),sK8),sK7(sK9,sK0(k1_relat_1(sK9),sK8))),sK9)
% 3.83/0.99      | ~ r2_hidden(sK0(k1_relat_1(sK9),sK8),k1_relat_1(sK9)) ),
% 3.83/0.99      inference(instantiation,[status(thm)],[c_18]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_1010,plain,
% 3.83/0.99      ( r2_hidden(sK0(k1_relat_1(sK9),sK8),k1_relat_1(sK9))
% 3.83/0.99      | r1_xboole_0(k1_relat_1(sK9),sK8) ),
% 3.83/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_2,plain,
% 3.83/0.99      ( r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1) ),
% 3.83/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_1007,plain,
% 3.83/0.99      ( r2_hidden(sK0(k1_relat_1(sK9),sK8),sK8)
% 3.83/0.99      | r1_xboole_0(k1_relat_1(sK9),sK8) ),
% 3.83/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_292,plain,
% 3.83/0.99      ( k1_xboole_0 = k1_xboole_0 ),
% 3.83/0.99      inference(instantiation,[status(thm)],[c_272]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_24,negated_conjecture,
% 3.83/0.99      ( ~ r1_xboole_0(k1_relat_1(sK9),sK8)
% 3.83/0.99      | k1_xboole_0 != k9_relat_1(sK9,sK8) ),
% 3.83/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(contradiction,plain,
% 3.83/0.99      ( $false ),
% 3.83/0.99      inference(minisat,
% 3.83/0.99                [status(thm)],
% 3.83/0.99                [c_15260,c_15262,c_5295,c_4904,c_3841,c_1850,c_1366,
% 3.83/0.99                 c_1150,c_1010,c_1007,c_292,c_24,c_26]) ).
% 3.83/0.99  
% 3.83/0.99  
% 3.83/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.83/0.99  
% 3.83/0.99  ------                               Statistics
% 3.83/0.99  
% 3.83/0.99  ------ Selected
% 3.83/0.99  
% 3.83/0.99  total_time:                             0.402
% 3.83/0.99  
%------------------------------------------------------------------------------
