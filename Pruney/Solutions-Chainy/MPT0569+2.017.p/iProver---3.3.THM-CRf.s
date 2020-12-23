%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:47:29 EST 2020

% Result     : Theorem 3.53s
% Output     : CNFRefutation 3.53s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 272 expanded)
%              Number of clauses        :   59 (  95 expanded)
%              Number of leaves         :   19 (  62 expanded)
%              Depth                    :   14
%              Number of atoms          :  376 (1063 expanded)
%              Number of equality atoms :  110 ( 335 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
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

fof(f11,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f16])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k10_relat_1(X1,X0)
        <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <~> r1_xboole_0(k2_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f30,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 != k10_relat_1(X1,X0) )
      & ( r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f31,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 != k10_relat_1(X1,X0) )
      & ( r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f32,plain,
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

fof(f33,plain,
    ( ( ~ r1_xboole_0(k2_relat_1(sK8),sK7)
      | k1_xboole_0 != k10_relat_1(sK8,sK7) )
    & ( r1_xboole_0(k2_relat_1(sK8),sK7)
      | k1_xboole_0 = k10_relat_1(sK8,sK7) )
    & v1_relat_1(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f31,f32])).

fof(f54,plain,
    ( r1_xboole_0(k2_relat_1(sK8),sK7)
    | k1_xboole_0 = k10_relat_1(sK8,sK7) ),
    inference(cnf_transformation,[],[f33])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f53,plain,(
    v1_relat_1(sK8) ),
    inference(cnf_transformation,[],[f33])).

fof(f55,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK8),sK7)
    | k1_xboole_0 != k10_relat_1(sK8,sK7) ),
    inference(cnf_transformation,[],[f33])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f18,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f19,plain,(
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
    inference(rectify,[],[f18])).

fof(f22,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X6,X8),X0) )
     => ( r2_hidden(sK3(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(X6,sK3(X0,X1,X6)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(X3,X5),X0) )
     => ( r2_hidden(sK2(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X3,sK2(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
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
              | ~ r2_hidden(k4_tarski(sK1(X0,X1,X2),X4),X0) )
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X1)
              & r2_hidden(k4_tarski(sK1(X0,X1,X2),X5),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(k4_tarski(sK1(X0,X1,X2),X4),X0) )
                | ~ r2_hidden(sK1(X0,X1,X2),X2) )
              & ( ( r2_hidden(sK2(X0,X1,X2),X1)
                  & r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X0) )
                | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X6,X7),X0) ) )
                & ( ( r2_hidden(sK3(X0,X1,X6),X1)
                    & r2_hidden(k4_tarski(X6,sK3(X0,X1,X6)),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f19,f22,f21,f20])).

fof(f42,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f56,plain,(
    ! [X6,X0,X7,X1] :
      ( r2_hidden(X6,k10_relat_1(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f25,plain,(
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
    inference(rectify,[],[f24])).

fof(f28,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK6(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK5(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0)
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK4(X0,X1)),X0)
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0)
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0)
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK6(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f25,f28,f27,f26])).

fof(f46,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK6(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f60,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK6(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f46])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK1(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f3])).

cnf(c_837,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_12590,plain,
    ( sK6(sK8,sK0(k2_relat_1(sK8),sK7)) = sK6(sK8,sK0(k2_relat_1(sK8),sK7)) ),
    inference(instantiation,[status(thm)],[c_837])).

cnf(c_841,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3781,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK6(sK8,sK0(k2_relat_1(sK8),sK7)),k10_relat_1(sK8,sK7))
    | X0 != sK6(sK8,sK0(k2_relat_1(sK8),sK7))
    | X1 != k10_relat_1(sK8,sK7) ),
    inference(instantiation,[status(thm)],[c_841])).

cnf(c_12589,plain,
    ( r2_hidden(sK6(sK8,sK0(k2_relat_1(sK8),sK7)),X0)
    | ~ r2_hidden(sK6(sK8,sK0(k2_relat_1(sK8),sK7)),k10_relat_1(sK8,sK7))
    | X0 != k10_relat_1(sK8,sK7)
    | sK6(sK8,sK0(k2_relat_1(sK8),sK7)) != sK6(sK8,sK0(k2_relat_1(sK8),sK7)) ),
    inference(instantiation,[status(thm)],[c_3781])).

cnf(c_12592,plain,
    ( ~ r2_hidden(sK6(sK8,sK0(k2_relat_1(sK8),sK7)),k10_relat_1(sK8,sK7))
    | r2_hidden(sK6(sK8,sK0(k2_relat_1(sK8),sK7)),k1_xboole_0)
    | sK6(sK8,sK0(k2_relat_1(sK8),sK7)) != sK6(sK8,sK0(k2_relat_1(sK8),sK7))
    | k1_xboole_0 != k10_relat_1(sK8,sK7) ),
    inference(instantiation,[status(thm)],[c_12589])).

cnf(c_839,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_11663,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,k10_relat_1(sK8,sK7))
    | X2 != X0
    | k10_relat_1(sK8,sK7) != X1 ),
    inference(instantiation,[status(thm)],[c_839])).

cnf(c_11665,plain,
    ( r1_xboole_0(k1_xboole_0,k10_relat_1(sK8,sK7))
    | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | k10_relat_1(sK8,sK7) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_11663])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_3782,plain,
    ( ~ r2_hidden(sK6(sK8,sK0(k2_relat_1(sK8),sK7)),X0)
    | ~ r2_hidden(sK6(sK8,sK0(k2_relat_1(sK8),sK7)),k10_relat_1(sK8,sK7))
    | ~ r1_xboole_0(X0,k10_relat_1(sK8,sK7)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_3789,plain,
    ( ~ r2_hidden(sK6(sK8,sK0(k2_relat_1(sK8),sK7)),k10_relat_1(sK8,sK7))
    | ~ r2_hidden(sK6(sK8,sK0(k2_relat_1(sK8),sK7)),k1_xboole_0)
    | ~ r1_xboole_0(k1_xboole_0,k10_relat_1(sK8,sK7)) ),
    inference(instantiation,[status(thm)],[c_3782])).

cnf(c_2268,plain,
    ( ~ r2_hidden(sK2(sK8,X0,X1),X0)
    | ~ r2_hidden(sK2(sK8,X0,X1),X2)
    | ~ r1_xboole_0(X2,X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2275,plain,
    ( ~ r2_hidden(sK2(sK8,k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2268])).

cnf(c_20,negated_conjecture,
    ( r1_xboole_0(k2_relat_1(sK8),sK7)
    | k1_xboole_0 = k10_relat_1(sK8,sK7) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1286,plain,
    ( k1_xboole_0 = k10_relat_1(sK8,sK7)
    | r1_xboole_0(k2_relat_1(sK8),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1295,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1726,plain,
    ( k10_relat_1(sK8,sK7) = k1_xboole_0
    | k3_xboole_0(k2_relat_1(sK8),sK7) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1286,c_1295])).

cnf(c_0,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1296,plain,
    ( k3_xboole_0(X0,X1) != k1_xboole_0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2054,plain,
    ( k10_relat_1(sK8,sK7) = k1_xboole_0
    | r1_xboole_0(k2_relat_1(sK8),sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_1726,c_1296])).

cnf(c_1982,plain,
    ( ~ r2_hidden(sK1(sK8,X0,X1),X1)
    | ~ r2_hidden(sK1(sK8,X0,X1),X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1989,plain,
    ( ~ r2_hidden(sK1(sK8,k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1982])).

cnf(c_16,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k3_xboole_0(k2_relat_1(X0),X1)) = k10_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_21,negated_conjecture,
    ( v1_relat_1(sK8) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_274,plain,
    ( k10_relat_1(X0,k3_xboole_0(k2_relat_1(X0),X1)) = k10_relat_1(X0,X1)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_21])).

cnf(c_275,plain,
    ( k10_relat_1(sK8,k3_xboole_0(k2_relat_1(sK8),X0)) = k10_relat_1(sK8,X0) ),
    inference(unflattening,[status(thm)],[c_274])).

cnf(c_1729,plain,
    ( k10_relat_1(sK8,sK7) = k1_xboole_0
    | k10_relat_1(sK8,k1_xboole_0) = k10_relat_1(sK8,sK7) ),
    inference(superposition,[status(thm)],[c_1726,c_275])).

cnf(c_19,negated_conjecture,
    ( ~ r1_xboole_0(k2_relat_1(sK8),sK7)
    | k1_xboole_0 != k10_relat_1(sK8,sK7) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1287,plain,
    ( k1_xboole_0 != k10_relat_1(sK8,sK7)
    | r1_xboole_0(k2_relat_1(sK8),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1783,plain,
    ( k10_relat_1(sK8,sK7) = k1_xboole_0
    | k10_relat_1(sK8,k1_xboole_0) != k1_xboole_0
    | r1_xboole_0(k2_relat_1(sK8),sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1729,c_1287])).

cnf(c_24,plain,
    ( k1_xboole_0 != k10_relat_1(sK8,sK7)
    | r1_xboole_0(k2_relat_1(sK8),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_860,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_837])).

cnf(c_838,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1495,plain,
    ( k10_relat_1(sK8,sK7) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k10_relat_1(sK8,sK7) ),
    inference(instantiation,[status(thm)],[c_838])).

cnf(c_1496,plain,
    ( k10_relat_1(sK8,sK7) != k1_xboole_0
    | k1_xboole_0 = k10_relat_1(sK8,sK7)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1495])).

cnf(c_1786,plain,
    ( k10_relat_1(sK8,k1_xboole_0) != k1_xboole_0
    | r1_xboole_0(k2_relat_1(sK8),sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1783,c_24,c_860,c_1496])).

cnf(c_1788,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK8),sK7)
    | k10_relat_1(sK8,k1_xboole_0) != k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1786])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(X3,X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_328,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(X3,X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | sK8 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_21])).

cnf(c_329,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(sK8,X1))
    | ~ r2_hidden(k4_tarski(X2,X0),sK8) ),
    inference(unflattening,[status(thm)],[c_328])).

cnf(c_1464,plain,
    ( r2_hidden(X0,k10_relat_1(sK8,sK7))
    | ~ r2_hidden(k4_tarski(X0,sK0(k2_relat_1(sK8),sK7)),sK8)
    | ~ r2_hidden(sK0(k2_relat_1(sK8),sK7),sK7) ),
    inference(instantiation,[status(thm)],[c_329])).

cnf(c_1659,plain,
    ( r2_hidden(sK6(sK8,sK0(k2_relat_1(sK8),sK7)),k10_relat_1(sK8,sK7))
    | ~ r2_hidden(k4_tarski(sK6(sK8,sK0(k2_relat_1(sK8),sK7)),sK0(k2_relat_1(sK8),sK7)),sK8)
    | ~ r2_hidden(sK0(k2_relat_1(sK8),sK7),sK7) ),
    inference(instantiation,[status(thm)],[c_1464])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(k4_tarski(sK6(X1,X0),X0),X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1492,plain,
    ( r2_hidden(k4_tarski(sK6(sK8,sK0(k2_relat_1(sK8),sK7)),sK0(k2_relat_1(sK8),sK7)),sK8)
    | ~ r2_hidden(sK0(k2_relat_1(sK8),sK7),k2_relat_1(sK8)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_4,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1435,plain,
    ( r2_hidden(sK0(k2_relat_1(sK8),sK7),k2_relat_1(sK8))
    | r1_xboole_0(k2_relat_1(sK8),sK7) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1432,plain,
    ( r2_hidden(sK0(k2_relat_1(sK8),sK7),sK7)
    | r1_xboole_0(k2_relat_1(sK8),sK7) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_7,plain,
    ( r2_hidden(sK2(X0,X1,X2),X1)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | ~ v1_relat_1(X0)
    | k10_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_295,plain,
    ( r2_hidden(sK2(X0,X1,X2),X1)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k10_relat_1(X0,X1) = X2
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_21])).

cnf(c_296,plain,
    ( r2_hidden(sK2(sK8,X0,X1),X0)
    | r2_hidden(sK1(sK8,X0,X1),X1)
    | k10_relat_1(sK8,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_295])).

cnf(c_298,plain,
    ( r2_hidden(sK2(sK8,k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | r2_hidden(sK1(sK8,k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | k10_relat_1(sK8,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_296])).

cnf(c_64,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | k3_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_5,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_54,plain,
    ( k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_23,plain,
    ( k1_xboole_0 = k10_relat_1(sK8,sK7)
    | r1_xboole_0(k2_relat_1(sK8),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12590,c_12592,c_11665,c_3789,c_2275,c_2054,c_1989,c_1788,c_1786,c_1659,c_1492,c_1435,c_1432,c_860,c_298,c_64,c_54,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:37:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.53/1.02  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.53/1.02  
% 3.53/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.53/1.02  
% 3.53/1.02  ------  iProver source info
% 3.53/1.02  
% 3.53/1.02  git: date: 2020-06-30 10:37:57 +0100
% 3.53/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.53/1.02  git: non_committed_changes: false
% 3.53/1.02  git: last_make_outside_of_git: false
% 3.53/1.02  
% 3.53/1.02  ------ 
% 3.53/1.02  
% 3.53/1.02  ------ Input Options
% 3.53/1.02  
% 3.53/1.02  --out_options                           all
% 3.53/1.02  --tptp_safe_out                         true
% 3.53/1.02  --problem_path                          ""
% 3.53/1.02  --include_path                          ""
% 3.53/1.02  --clausifier                            res/vclausify_rel
% 3.53/1.02  --clausifier_options                    --mode clausify
% 3.53/1.02  --stdin                                 false
% 3.53/1.02  --stats_out                             all
% 3.53/1.02  
% 3.53/1.02  ------ General Options
% 3.53/1.02  
% 3.53/1.02  --fof                                   false
% 3.53/1.02  --time_out_real                         305.
% 3.53/1.02  --time_out_virtual                      -1.
% 3.53/1.02  --symbol_type_check                     false
% 3.53/1.02  --clausify_out                          false
% 3.53/1.02  --sig_cnt_out                           false
% 3.53/1.02  --trig_cnt_out                          false
% 3.53/1.02  --trig_cnt_out_tolerance                1.
% 3.53/1.02  --trig_cnt_out_sk_spl                   false
% 3.53/1.02  --abstr_cl_out                          false
% 3.53/1.02  
% 3.53/1.02  ------ Global Options
% 3.53/1.02  
% 3.53/1.02  --schedule                              default
% 3.53/1.02  --add_important_lit                     false
% 3.53/1.02  --prop_solver_per_cl                    1000
% 3.53/1.02  --min_unsat_core                        false
% 3.53/1.02  --soft_assumptions                      false
% 3.53/1.02  --soft_lemma_size                       3
% 3.53/1.02  --prop_impl_unit_size                   0
% 3.53/1.02  --prop_impl_unit                        []
% 3.53/1.02  --share_sel_clauses                     true
% 3.53/1.02  --reset_solvers                         false
% 3.53/1.02  --bc_imp_inh                            [conj_cone]
% 3.53/1.02  --conj_cone_tolerance                   3.
% 3.53/1.02  --extra_neg_conj                        none
% 3.53/1.02  --large_theory_mode                     true
% 3.53/1.02  --prolific_symb_bound                   200
% 3.53/1.02  --lt_threshold                          2000
% 3.53/1.02  --clause_weak_htbl                      true
% 3.53/1.02  --gc_record_bc_elim                     false
% 3.53/1.02  
% 3.53/1.02  ------ Preprocessing Options
% 3.53/1.02  
% 3.53/1.02  --preprocessing_flag                    true
% 3.53/1.02  --time_out_prep_mult                    0.1
% 3.53/1.02  --splitting_mode                        input
% 3.53/1.02  --splitting_grd                         true
% 3.53/1.02  --splitting_cvd                         false
% 3.53/1.02  --splitting_cvd_svl                     false
% 3.53/1.02  --splitting_nvd                         32
% 3.53/1.02  --sub_typing                            true
% 3.53/1.02  --prep_gs_sim                           true
% 3.53/1.02  --prep_unflatten                        true
% 3.53/1.02  --prep_res_sim                          true
% 3.53/1.02  --prep_upred                            true
% 3.53/1.02  --prep_sem_filter                       exhaustive
% 3.53/1.02  --prep_sem_filter_out                   false
% 3.53/1.02  --pred_elim                             true
% 3.53/1.02  --res_sim_input                         true
% 3.53/1.02  --eq_ax_congr_red                       true
% 3.53/1.02  --pure_diseq_elim                       true
% 3.53/1.02  --brand_transform                       false
% 3.53/1.02  --non_eq_to_eq                          false
% 3.53/1.02  --prep_def_merge                        true
% 3.53/1.02  --prep_def_merge_prop_impl              false
% 3.53/1.02  --prep_def_merge_mbd                    true
% 3.53/1.02  --prep_def_merge_tr_red                 false
% 3.53/1.02  --prep_def_merge_tr_cl                  false
% 3.53/1.02  --smt_preprocessing                     true
% 3.53/1.02  --smt_ac_axioms                         fast
% 3.53/1.02  --preprocessed_out                      false
% 3.53/1.02  --preprocessed_stats                    false
% 3.53/1.02  
% 3.53/1.02  ------ Abstraction refinement Options
% 3.53/1.02  
% 3.53/1.02  --abstr_ref                             []
% 3.53/1.02  --abstr_ref_prep                        false
% 3.53/1.02  --abstr_ref_until_sat                   false
% 3.53/1.02  --abstr_ref_sig_restrict                funpre
% 3.53/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.53/1.02  --abstr_ref_under                       []
% 3.53/1.02  
% 3.53/1.02  ------ SAT Options
% 3.53/1.02  
% 3.53/1.02  --sat_mode                              false
% 3.53/1.02  --sat_fm_restart_options                ""
% 3.53/1.02  --sat_gr_def                            false
% 3.53/1.02  --sat_epr_types                         true
% 3.53/1.02  --sat_non_cyclic_types                  false
% 3.53/1.02  --sat_finite_models                     false
% 3.53/1.02  --sat_fm_lemmas                         false
% 3.53/1.02  --sat_fm_prep                           false
% 3.53/1.02  --sat_fm_uc_incr                        true
% 3.53/1.02  --sat_out_model                         small
% 3.53/1.02  --sat_out_clauses                       false
% 3.53/1.02  
% 3.53/1.02  ------ QBF Options
% 3.53/1.02  
% 3.53/1.02  --qbf_mode                              false
% 3.53/1.02  --qbf_elim_univ                         false
% 3.53/1.02  --qbf_dom_inst                          none
% 3.53/1.02  --qbf_dom_pre_inst                      false
% 3.53/1.02  --qbf_sk_in                             false
% 3.53/1.02  --qbf_pred_elim                         true
% 3.53/1.02  --qbf_split                             512
% 3.53/1.02  
% 3.53/1.02  ------ BMC1 Options
% 3.53/1.02  
% 3.53/1.02  --bmc1_incremental                      false
% 3.53/1.02  --bmc1_axioms                           reachable_all
% 3.53/1.02  --bmc1_min_bound                        0
% 3.53/1.02  --bmc1_max_bound                        -1
% 3.53/1.02  --bmc1_max_bound_default                -1
% 3.53/1.02  --bmc1_symbol_reachability              true
% 3.53/1.02  --bmc1_property_lemmas                  false
% 3.53/1.02  --bmc1_k_induction                      false
% 3.53/1.02  --bmc1_non_equiv_states                 false
% 3.53/1.02  --bmc1_deadlock                         false
% 3.53/1.02  --bmc1_ucm                              false
% 3.53/1.02  --bmc1_add_unsat_core                   none
% 3.53/1.02  --bmc1_unsat_core_children              false
% 3.53/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.53/1.02  --bmc1_out_stat                         full
% 3.53/1.02  --bmc1_ground_init                      false
% 3.53/1.02  --bmc1_pre_inst_next_state              false
% 3.53/1.02  --bmc1_pre_inst_state                   false
% 3.53/1.02  --bmc1_pre_inst_reach_state             false
% 3.53/1.02  --bmc1_out_unsat_core                   false
% 3.53/1.02  --bmc1_aig_witness_out                  false
% 3.53/1.02  --bmc1_verbose                          false
% 3.53/1.02  --bmc1_dump_clauses_tptp                false
% 3.53/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.53/1.02  --bmc1_dump_file                        -
% 3.53/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.53/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.53/1.02  --bmc1_ucm_extend_mode                  1
% 3.53/1.02  --bmc1_ucm_init_mode                    2
% 3.53/1.02  --bmc1_ucm_cone_mode                    none
% 3.53/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.53/1.02  --bmc1_ucm_relax_model                  4
% 3.53/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.53/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.53/1.02  --bmc1_ucm_layered_model                none
% 3.53/1.02  --bmc1_ucm_max_lemma_size               10
% 3.53/1.02  
% 3.53/1.02  ------ AIG Options
% 3.53/1.02  
% 3.53/1.02  --aig_mode                              false
% 3.53/1.02  
% 3.53/1.02  ------ Instantiation Options
% 3.53/1.02  
% 3.53/1.02  --instantiation_flag                    true
% 3.53/1.02  --inst_sos_flag                         false
% 3.53/1.02  --inst_sos_phase                        true
% 3.53/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.53/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.53/1.02  --inst_lit_sel_side                     num_symb
% 3.53/1.02  --inst_solver_per_active                1400
% 3.53/1.02  --inst_solver_calls_frac                1.
% 3.53/1.02  --inst_passive_queue_type               priority_queues
% 3.53/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.53/1.02  --inst_passive_queues_freq              [25;2]
% 3.53/1.02  --inst_dismatching                      true
% 3.53/1.02  --inst_eager_unprocessed_to_passive     true
% 3.53/1.02  --inst_prop_sim_given                   true
% 3.53/1.02  --inst_prop_sim_new                     false
% 3.53/1.02  --inst_subs_new                         false
% 3.53/1.02  --inst_eq_res_simp                      false
% 3.53/1.02  --inst_subs_given                       false
% 3.53/1.02  --inst_orphan_elimination               true
% 3.53/1.02  --inst_learning_loop_flag               true
% 3.53/1.02  --inst_learning_start                   3000
% 3.53/1.02  --inst_learning_factor                  2
% 3.53/1.02  --inst_start_prop_sim_after_learn       3
% 3.53/1.02  --inst_sel_renew                        solver
% 3.53/1.02  --inst_lit_activity_flag                true
% 3.53/1.02  --inst_restr_to_given                   false
% 3.53/1.02  --inst_activity_threshold               500
% 3.53/1.02  --inst_out_proof                        true
% 3.53/1.02  
% 3.53/1.02  ------ Resolution Options
% 3.53/1.02  
% 3.53/1.02  --resolution_flag                       true
% 3.53/1.02  --res_lit_sel                           adaptive
% 3.53/1.02  --res_lit_sel_side                      none
% 3.53/1.02  --res_ordering                          kbo
% 3.53/1.02  --res_to_prop_solver                    active
% 3.53/1.02  --res_prop_simpl_new                    false
% 3.53/1.02  --res_prop_simpl_given                  true
% 3.53/1.02  --res_passive_queue_type                priority_queues
% 3.53/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.53/1.02  --res_passive_queues_freq               [15;5]
% 3.53/1.02  --res_forward_subs                      full
% 3.53/1.02  --res_backward_subs                     full
% 3.53/1.02  --res_forward_subs_resolution           true
% 3.53/1.02  --res_backward_subs_resolution          true
% 3.53/1.02  --res_orphan_elimination                true
% 3.53/1.02  --res_time_limit                        2.
% 3.53/1.02  --res_out_proof                         true
% 3.53/1.02  
% 3.53/1.02  ------ Superposition Options
% 3.53/1.02  
% 3.53/1.02  --superposition_flag                    true
% 3.53/1.02  --sup_passive_queue_type                priority_queues
% 3.53/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.53/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.53/1.02  --demod_completeness_check              fast
% 3.53/1.02  --demod_use_ground                      true
% 3.53/1.02  --sup_to_prop_solver                    passive
% 3.53/1.02  --sup_prop_simpl_new                    true
% 3.53/1.02  --sup_prop_simpl_given                  true
% 3.53/1.02  --sup_fun_splitting                     false
% 3.53/1.02  --sup_smt_interval                      50000
% 3.53/1.02  
% 3.53/1.02  ------ Superposition Simplification Setup
% 3.53/1.02  
% 3.53/1.02  --sup_indices_passive                   []
% 3.53/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.53/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.53/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.53/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.53/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.53/1.02  --sup_full_bw                           [BwDemod]
% 3.53/1.02  --sup_immed_triv                        [TrivRules]
% 3.53/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.53/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.53/1.02  --sup_immed_bw_main                     []
% 3.53/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.53/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.53/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.53/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.53/1.02  
% 3.53/1.02  ------ Combination Options
% 3.53/1.02  
% 3.53/1.02  --comb_res_mult                         3
% 3.53/1.02  --comb_sup_mult                         2
% 3.53/1.02  --comb_inst_mult                        10
% 3.53/1.02  
% 3.53/1.02  ------ Debug Options
% 3.53/1.02  
% 3.53/1.02  --dbg_backtrace                         false
% 3.53/1.02  --dbg_dump_prop_clauses                 false
% 3.53/1.02  --dbg_dump_prop_clauses_file            -
% 3.53/1.02  --dbg_out_stat                          false
% 3.53/1.02  ------ Parsing...
% 3.53/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.53/1.02  
% 3.53/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.53/1.02  
% 3.53/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.53/1.02  
% 3.53/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.53/1.02  ------ Proving...
% 3.53/1.02  ------ Problem Properties 
% 3.53/1.02  
% 3.53/1.02  
% 3.53/1.02  clauses                                 21
% 3.53/1.02  conjectures                             2
% 3.53/1.02  EPR                                     1
% 3.53/1.02  Horn                                    15
% 3.53/1.02  unary                                   4
% 3.53/1.02  binary                                  10
% 3.53/1.02  lits                                    46
% 3.53/1.02  lits eq                                 13
% 3.53/1.02  fd_pure                                 0
% 3.53/1.02  fd_pseudo                               0
% 3.53/1.02  fd_cond                                 0
% 3.53/1.02  fd_pseudo_cond                          5
% 3.53/1.02  AC symbols                              0
% 3.53/1.02  
% 3.53/1.02  ------ Schedule dynamic 5 is on 
% 3.53/1.02  
% 3.53/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.53/1.02  
% 3.53/1.02  
% 3.53/1.02  ------ 
% 3.53/1.02  Current options:
% 3.53/1.02  ------ 
% 3.53/1.02  
% 3.53/1.02  ------ Input Options
% 3.53/1.02  
% 3.53/1.02  --out_options                           all
% 3.53/1.02  --tptp_safe_out                         true
% 3.53/1.02  --problem_path                          ""
% 3.53/1.02  --include_path                          ""
% 3.53/1.02  --clausifier                            res/vclausify_rel
% 3.53/1.02  --clausifier_options                    --mode clausify
% 3.53/1.02  --stdin                                 false
% 3.53/1.02  --stats_out                             all
% 3.53/1.02  
% 3.53/1.02  ------ General Options
% 3.53/1.02  
% 3.53/1.02  --fof                                   false
% 3.53/1.02  --time_out_real                         305.
% 3.53/1.02  --time_out_virtual                      -1.
% 3.53/1.02  --symbol_type_check                     false
% 3.53/1.02  --clausify_out                          false
% 3.53/1.02  --sig_cnt_out                           false
% 3.53/1.02  --trig_cnt_out                          false
% 3.53/1.02  --trig_cnt_out_tolerance                1.
% 3.53/1.02  --trig_cnt_out_sk_spl                   false
% 3.53/1.02  --abstr_cl_out                          false
% 3.53/1.02  
% 3.53/1.02  ------ Global Options
% 3.53/1.02  
% 3.53/1.02  --schedule                              default
% 3.53/1.02  --add_important_lit                     false
% 3.53/1.02  --prop_solver_per_cl                    1000
% 3.53/1.02  --min_unsat_core                        false
% 3.53/1.02  --soft_assumptions                      false
% 3.53/1.02  --soft_lemma_size                       3
% 3.53/1.02  --prop_impl_unit_size                   0
% 3.53/1.02  --prop_impl_unit                        []
% 3.53/1.02  --share_sel_clauses                     true
% 3.53/1.02  --reset_solvers                         false
% 3.53/1.02  --bc_imp_inh                            [conj_cone]
% 3.53/1.02  --conj_cone_tolerance                   3.
% 3.53/1.02  --extra_neg_conj                        none
% 3.53/1.02  --large_theory_mode                     true
% 3.53/1.02  --prolific_symb_bound                   200
% 3.53/1.02  --lt_threshold                          2000
% 3.53/1.02  --clause_weak_htbl                      true
% 3.53/1.02  --gc_record_bc_elim                     false
% 3.53/1.02  
% 3.53/1.02  ------ Preprocessing Options
% 3.53/1.02  
% 3.53/1.02  --preprocessing_flag                    true
% 3.53/1.02  --time_out_prep_mult                    0.1
% 3.53/1.02  --splitting_mode                        input
% 3.53/1.02  --splitting_grd                         true
% 3.53/1.02  --splitting_cvd                         false
% 3.53/1.02  --splitting_cvd_svl                     false
% 3.53/1.02  --splitting_nvd                         32
% 3.53/1.02  --sub_typing                            true
% 3.53/1.02  --prep_gs_sim                           true
% 3.53/1.02  --prep_unflatten                        true
% 3.53/1.02  --prep_res_sim                          true
% 3.53/1.02  --prep_upred                            true
% 3.53/1.02  --prep_sem_filter                       exhaustive
% 3.53/1.02  --prep_sem_filter_out                   false
% 3.53/1.02  --pred_elim                             true
% 3.53/1.02  --res_sim_input                         true
% 3.53/1.02  --eq_ax_congr_red                       true
% 3.53/1.02  --pure_diseq_elim                       true
% 3.53/1.02  --brand_transform                       false
% 3.53/1.02  --non_eq_to_eq                          false
% 3.53/1.02  --prep_def_merge                        true
% 3.53/1.02  --prep_def_merge_prop_impl              false
% 3.53/1.02  --prep_def_merge_mbd                    true
% 3.53/1.02  --prep_def_merge_tr_red                 false
% 3.53/1.02  --prep_def_merge_tr_cl                  false
% 3.53/1.02  --smt_preprocessing                     true
% 3.53/1.02  --smt_ac_axioms                         fast
% 3.53/1.02  --preprocessed_out                      false
% 3.53/1.02  --preprocessed_stats                    false
% 3.53/1.02  
% 3.53/1.02  ------ Abstraction refinement Options
% 3.53/1.02  
% 3.53/1.02  --abstr_ref                             []
% 3.53/1.02  --abstr_ref_prep                        false
% 3.53/1.02  --abstr_ref_until_sat                   false
% 3.53/1.02  --abstr_ref_sig_restrict                funpre
% 3.53/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.53/1.02  --abstr_ref_under                       []
% 3.53/1.02  
% 3.53/1.02  ------ SAT Options
% 3.53/1.02  
% 3.53/1.02  --sat_mode                              false
% 3.53/1.02  --sat_fm_restart_options                ""
% 3.53/1.02  --sat_gr_def                            false
% 3.53/1.02  --sat_epr_types                         true
% 3.53/1.02  --sat_non_cyclic_types                  false
% 3.53/1.02  --sat_finite_models                     false
% 3.53/1.02  --sat_fm_lemmas                         false
% 3.53/1.02  --sat_fm_prep                           false
% 3.53/1.02  --sat_fm_uc_incr                        true
% 3.53/1.02  --sat_out_model                         small
% 3.53/1.02  --sat_out_clauses                       false
% 3.53/1.02  
% 3.53/1.02  ------ QBF Options
% 3.53/1.02  
% 3.53/1.02  --qbf_mode                              false
% 3.53/1.02  --qbf_elim_univ                         false
% 3.53/1.02  --qbf_dom_inst                          none
% 3.53/1.02  --qbf_dom_pre_inst                      false
% 3.53/1.02  --qbf_sk_in                             false
% 3.53/1.02  --qbf_pred_elim                         true
% 3.53/1.02  --qbf_split                             512
% 3.53/1.02  
% 3.53/1.02  ------ BMC1 Options
% 3.53/1.02  
% 3.53/1.02  --bmc1_incremental                      false
% 3.53/1.02  --bmc1_axioms                           reachable_all
% 3.53/1.02  --bmc1_min_bound                        0
% 3.53/1.02  --bmc1_max_bound                        -1
% 3.53/1.02  --bmc1_max_bound_default                -1
% 3.53/1.02  --bmc1_symbol_reachability              true
% 3.53/1.02  --bmc1_property_lemmas                  false
% 3.53/1.02  --bmc1_k_induction                      false
% 3.53/1.02  --bmc1_non_equiv_states                 false
% 3.53/1.02  --bmc1_deadlock                         false
% 3.53/1.02  --bmc1_ucm                              false
% 3.53/1.02  --bmc1_add_unsat_core                   none
% 3.53/1.02  --bmc1_unsat_core_children              false
% 3.53/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.53/1.02  --bmc1_out_stat                         full
% 3.53/1.02  --bmc1_ground_init                      false
% 3.53/1.02  --bmc1_pre_inst_next_state              false
% 3.53/1.02  --bmc1_pre_inst_state                   false
% 3.53/1.02  --bmc1_pre_inst_reach_state             false
% 3.53/1.02  --bmc1_out_unsat_core                   false
% 3.53/1.02  --bmc1_aig_witness_out                  false
% 3.53/1.02  --bmc1_verbose                          false
% 3.53/1.02  --bmc1_dump_clauses_tptp                false
% 3.53/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.53/1.02  --bmc1_dump_file                        -
% 3.53/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.53/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.53/1.02  --bmc1_ucm_extend_mode                  1
% 3.53/1.02  --bmc1_ucm_init_mode                    2
% 3.53/1.02  --bmc1_ucm_cone_mode                    none
% 3.53/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.53/1.02  --bmc1_ucm_relax_model                  4
% 3.53/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.53/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.53/1.02  --bmc1_ucm_layered_model                none
% 3.53/1.02  --bmc1_ucm_max_lemma_size               10
% 3.53/1.02  
% 3.53/1.02  ------ AIG Options
% 3.53/1.02  
% 3.53/1.02  --aig_mode                              false
% 3.53/1.02  
% 3.53/1.02  ------ Instantiation Options
% 3.53/1.02  
% 3.53/1.02  --instantiation_flag                    true
% 3.53/1.02  --inst_sos_flag                         false
% 3.53/1.02  --inst_sos_phase                        true
% 3.53/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.53/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.53/1.02  --inst_lit_sel_side                     none
% 3.53/1.02  --inst_solver_per_active                1400
% 3.53/1.02  --inst_solver_calls_frac                1.
% 3.53/1.02  --inst_passive_queue_type               priority_queues
% 3.53/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.53/1.02  --inst_passive_queues_freq              [25;2]
% 3.53/1.02  --inst_dismatching                      true
% 3.53/1.02  --inst_eager_unprocessed_to_passive     true
% 3.53/1.02  --inst_prop_sim_given                   true
% 3.53/1.02  --inst_prop_sim_new                     false
% 3.53/1.02  --inst_subs_new                         false
% 3.53/1.02  --inst_eq_res_simp                      false
% 3.53/1.02  --inst_subs_given                       false
% 3.53/1.02  --inst_orphan_elimination               true
% 3.53/1.02  --inst_learning_loop_flag               true
% 3.53/1.02  --inst_learning_start                   3000
% 3.53/1.02  --inst_learning_factor                  2
% 3.53/1.02  --inst_start_prop_sim_after_learn       3
% 3.53/1.02  --inst_sel_renew                        solver
% 3.53/1.02  --inst_lit_activity_flag                true
% 3.53/1.02  --inst_restr_to_given                   false
% 3.53/1.02  --inst_activity_threshold               500
% 3.53/1.02  --inst_out_proof                        true
% 3.53/1.02  
% 3.53/1.02  ------ Resolution Options
% 3.53/1.02  
% 3.53/1.02  --resolution_flag                       false
% 3.53/1.02  --res_lit_sel                           adaptive
% 3.53/1.02  --res_lit_sel_side                      none
% 3.53/1.02  --res_ordering                          kbo
% 3.53/1.02  --res_to_prop_solver                    active
% 3.53/1.02  --res_prop_simpl_new                    false
% 3.53/1.02  --res_prop_simpl_given                  true
% 3.53/1.02  --res_passive_queue_type                priority_queues
% 3.53/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.53/1.02  --res_passive_queues_freq               [15;5]
% 3.53/1.02  --res_forward_subs                      full
% 3.53/1.02  --res_backward_subs                     full
% 3.53/1.02  --res_forward_subs_resolution           true
% 3.53/1.02  --res_backward_subs_resolution          true
% 3.53/1.02  --res_orphan_elimination                true
% 3.53/1.02  --res_time_limit                        2.
% 3.53/1.02  --res_out_proof                         true
% 3.53/1.02  
% 3.53/1.02  ------ Superposition Options
% 3.53/1.02  
% 3.53/1.02  --superposition_flag                    true
% 3.53/1.02  --sup_passive_queue_type                priority_queues
% 3.53/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.53/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.53/1.02  --demod_completeness_check              fast
% 3.53/1.02  --demod_use_ground                      true
% 3.53/1.02  --sup_to_prop_solver                    passive
% 3.53/1.02  --sup_prop_simpl_new                    true
% 3.53/1.02  --sup_prop_simpl_given                  true
% 3.53/1.02  --sup_fun_splitting                     false
% 3.53/1.02  --sup_smt_interval                      50000
% 3.53/1.02  
% 3.53/1.02  ------ Superposition Simplification Setup
% 3.53/1.02  
% 3.53/1.02  --sup_indices_passive                   []
% 3.53/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.53/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.53/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.53/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.53/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.53/1.02  --sup_full_bw                           [BwDemod]
% 3.53/1.02  --sup_immed_triv                        [TrivRules]
% 3.53/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.53/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.53/1.02  --sup_immed_bw_main                     []
% 3.53/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.53/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.53/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.53/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.53/1.02  
% 3.53/1.02  ------ Combination Options
% 3.53/1.02  
% 3.53/1.02  --comb_res_mult                         3
% 3.53/1.02  --comb_sup_mult                         2
% 3.53/1.02  --comb_inst_mult                        10
% 3.53/1.02  
% 3.53/1.02  ------ Debug Options
% 3.53/1.02  
% 3.53/1.02  --dbg_backtrace                         false
% 3.53/1.02  --dbg_dump_prop_clauses                 false
% 3.53/1.02  --dbg_dump_prop_clauses_file            -
% 3.53/1.02  --dbg_out_stat                          false
% 3.53/1.02  
% 3.53/1.02  
% 3.53/1.02  
% 3.53/1.02  
% 3.53/1.02  ------ Proving...
% 3.53/1.02  
% 3.53/1.02  
% 3.53/1.02  % SZS status Theorem for theBenchmark.p
% 3.53/1.02  
% 3.53/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 3.53/1.02  
% 3.53/1.02  fof(f2,axiom,(
% 3.53/1.02    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.53/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/1.02  
% 3.53/1.02  fof(f10,plain,(
% 3.53/1.02    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.53/1.02    inference(rectify,[],[f2])).
% 3.53/1.02  
% 3.53/1.02  fof(f11,plain,(
% 3.53/1.02    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 3.53/1.02    inference(ennf_transformation,[],[f10])).
% 3.53/1.02  
% 3.53/1.02  fof(f16,plain,(
% 3.53/1.02    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.53/1.02    introduced(choice_axiom,[])).
% 3.53/1.02  
% 3.53/1.02  fof(f17,plain,(
% 3.53/1.02    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 3.53/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f16])).
% 3.53/1.02  
% 3.53/1.02  fof(f38,plain,(
% 3.53/1.02    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 3.53/1.02    inference(cnf_transformation,[],[f17])).
% 3.53/1.02  
% 3.53/1.02  fof(f8,conjecture,(
% 3.53/1.02    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 3.53/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/1.02  
% 3.53/1.02  fof(f9,negated_conjecture,(
% 3.53/1.02    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 3.53/1.02    inference(negated_conjecture,[],[f8])).
% 3.53/1.02  
% 3.53/1.02  fof(f14,plain,(
% 3.53/1.02    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <~> r1_xboole_0(k2_relat_1(X1),X0)) & v1_relat_1(X1))),
% 3.53/1.02    inference(ennf_transformation,[],[f9])).
% 3.53/1.02  
% 3.53/1.02  fof(f30,plain,(
% 3.53/1.02    ? [X0,X1] : (((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0))) & v1_relat_1(X1))),
% 3.53/1.02    inference(nnf_transformation,[],[f14])).
% 3.53/1.02  
% 3.53/1.02  fof(f31,plain,(
% 3.53/1.02    ? [X0,X1] : ((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) & v1_relat_1(X1))),
% 3.53/1.02    inference(flattening,[],[f30])).
% 3.53/1.02  
% 3.53/1.02  fof(f32,plain,(
% 3.53/1.02    ? [X0,X1] : ((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) & v1_relat_1(X1)) => ((~r1_xboole_0(k2_relat_1(sK8),sK7) | k1_xboole_0 != k10_relat_1(sK8,sK7)) & (r1_xboole_0(k2_relat_1(sK8),sK7) | k1_xboole_0 = k10_relat_1(sK8,sK7)) & v1_relat_1(sK8))),
% 3.53/1.02    introduced(choice_axiom,[])).
% 3.53/1.02  
% 3.53/1.02  fof(f33,plain,(
% 3.53/1.02    (~r1_xboole_0(k2_relat_1(sK8),sK7) | k1_xboole_0 != k10_relat_1(sK8,sK7)) & (r1_xboole_0(k2_relat_1(sK8),sK7) | k1_xboole_0 = k10_relat_1(sK8,sK7)) & v1_relat_1(sK8)),
% 3.53/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f31,f32])).
% 3.53/1.02  
% 3.53/1.02  fof(f54,plain,(
% 3.53/1.02    r1_xboole_0(k2_relat_1(sK8),sK7) | k1_xboole_0 = k10_relat_1(sK8,sK7)),
% 3.53/1.02    inference(cnf_transformation,[],[f33])).
% 3.53/1.02  
% 3.53/1.02  fof(f1,axiom,(
% 3.53/1.02    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 3.53/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/1.02  
% 3.53/1.02  fof(f15,plain,(
% 3.53/1.02    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 3.53/1.02    inference(nnf_transformation,[],[f1])).
% 3.53/1.02  
% 3.53/1.02  fof(f34,plain,(
% 3.53/1.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 3.53/1.02    inference(cnf_transformation,[],[f15])).
% 3.53/1.02  
% 3.53/1.02  fof(f35,plain,(
% 3.53/1.02    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 3.53/1.02    inference(cnf_transformation,[],[f15])).
% 3.53/1.02  
% 3.53/1.02  fof(f6,axiom,(
% 3.53/1.02    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 3.53/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/1.02  
% 3.53/1.02  fof(f13,plain,(
% 3.53/1.02    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.53/1.02    inference(ennf_transformation,[],[f6])).
% 3.53/1.02  
% 3.53/1.02  fof(f50,plain,(
% 3.53/1.02    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 3.53/1.02    inference(cnf_transformation,[],[f13])).
% 3.53/1.02  
% 3.53/1.02  fof(f53,plain,(
% 3.53/1.02    v1_relat_1(sK8)),
% 3.53/1.02    inference(cnf_transformation,[],[f33])).
% 3.53/1.02  
% 3.53/1.02  fof(f55,plain,(
% 3.53/1.02    ~r1_xboole_0(k2_relat_1(sK8),sK7) | k1_xboole_0 != k10_relat_1(sK8,sK7)),
% 3.53/1.02    inference(cnf_transformation,[],[f33])).
% 3.53/1.02  
% 3.53/1.02  fof(f4,axiom,(
% 3.53/1.02    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))))),
% 3.53/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/1.02  
% 3.53/1.02  fof(f12,plain,(
% 3.53/1.02    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))) | ~v1_relat_1(X0))),
% 3.53/1.02    inference(ennf_transformation,[],[f4])).
% 3.53/1.02  
% 3.53/1.02  fof(f18,plain,(
% 3.53/1.02    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 3.53/1.02    inference(nnf_transformation,[],[f12])).
% 3.53/1.02  
% 3.53/1.02  fof(f19,plain,(
% 3.53/1.02    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0))) & (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X6,X8),X0)) | ~r2_hidden(X6,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 3.53/1.02    inference(rectify,[],[f18])).
% 3.53/1.02  
% 3.53/1.02  fof(f22,plain,(
% 3.53/1.02    ! [X6,X1,X0] : (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X6,X8),X0)) => (r2_hidden(sK3(X0,X1,X6),X1) & r2_hidden(k4_tarski(X6,sK3(X0,X1,X6)),X0)))),
% 3.53/1.02    introduced(choice_axiom,[])).
% 3.53/1.02  
% 3.53/1.02  fof(f21,plain,(
% 3.53/1.02    ( ! [X3] : (! [X2,X1,X0] : (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X3,X5),X0)) => (r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(k4_tarski(X3,sK2(X0,X1,X2)),X0)))) )),
% 3.53/1.02    introduced(choice_axiom,[])).
% 3.53/1.02  
% 3.53/1.02  fof(f20,plain,(
% 3.53/1.02    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(X3,X2))) => ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(sK1(X0,X1,X2),X4),X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X5),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 3.53/1.02    introduced(choice_axiom,[])).
% 3.53/1.02  
% 3.53/1.02  fof(f23,plain,(
% 3.53/1.02    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(sK1(X0,X1,X2),X4),X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0))) & ((r2_hidden(sK3(X0,X1,X6),X1) & r2_hidden(k4_tarski(X6,sK3(X0,X1,X6)),X0)) | ~r2_hidden(X6,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 3.53/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f19,f22,f21,f20])).
% 3.53/1.02  
% 3.53/1.02  fof(f42,plain,(
% 3.53/1.02    ( ! [X6,X2,X0,X7,X1] : (r2_hidden(X6,X2) | ~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0) | k10_relat_1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 3.53/1.02    inference(cnf_transformation,[],[f23])).
% 3.53/1.02  
% 3.53/1.02  fof(f56,plain,(
% 3.53/1.02    ( ! [X6,X0,X7,X1] : (r2_hidden(X6,k10_relat_1(X0,X1)) | ~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0) | ~v1_relat_1(X0)) )),
% 3.53/1.02    inference(equality_resolution,[],[f42])).
% 3.53/1.02  
% 3.53/1.02  fof(f5,axiom,(
% 3.53/1.02    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 3.53/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/1.02  
% 3.53/1.02  fof(f24,plain,(
% 3.53/1.02    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 3.53/1.02    inference(nnf_transformation,[],[f5])).
% 3.53/1.02  
% 3.53/1.02  fof(f25,plain,(
% 3.53/1.02    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 3.53/1.02    inference(rectify,[],[f24])).
% 3.53/1.02  
% 3.53/1.02  fof(f28,plain,(
% 3.53/1.02    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK6(X0,X5),X5),X0))),
% 3.53/1.02    introduced(choice_axiom,[])).
% 3.53/1.02  
% 3.53/1.02  fof(f27,plain,(
% 3.53/1.02    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) => r2_hidden(k4_tarski(sK5(X0,X1),X2),X0))) )),
% 3.53/1.02    introduced(choice_axiom,[])).
% 3.53/1.02  
% 3.53/1.02  fof(f26,plain,(
% 3.53/1.02    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK4(X0,X1)),X0) | r2_hidden(sK4(X0,X1),X1))))),
% 3.53/1.02    introduced(choice_axiom,[])).
% 3.53/1.02  
% 3.53/1.02  fof(f29,plain,(
% 3.53/1.02    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0) | r2_hidden(sK4(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK6(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 3.53/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f25,f28,f27,f26])).
% 3.53/1.02  
% 3.53/1.02  fof(f46,plain,(
% 3.53/1.02    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK6(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 3.53/1.02    inference(cnf_transformation,[],[f29])).
% 3.53/1.02  
% 3.53/1.02  fof(f60,plain,(
% 3.53/1.02    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK6(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 3.53/1.02    inference(equality_resolution,[],[f46])).
% 3.53/1.02  
% 3.53/1.02  fof(f36,plain,(
% 3.53/1.02    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 3.53/1.02    inference(cnf_transformation,[],[f17])).
% 3.53/1.02  
% 3.53/1.02  fof(f37,plain,(
% 3.53/1.02    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 3.53/1.02    inference(cnf_transformation,[],[f17])).
% 3.53/1.02  
% 3.53/1.02  fof(f44,plain,(
% 3.53/1.02    ( ! [X2,X0,X1] : (k10_relat_1(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X2) | ~v1_relat_1(X0)) )),
% 3.53/1.02    inference(cnf_transformation,[],[f23])).
% 3.53/1.02  
% 3.53/1.02  fof(f3,axiom,(
% 3.53/1.02    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 3.53/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/1.02  
% 3.53/1.02  fof(f39,plain,(
% 3.53/1.02    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 3.53/1.02    inference(cnf_transformation,[],[f3])).
% 3.53/1.02  
% 3.53/1.02  cnf(c_837,plain,( X0 = X0 ),theory(equality) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_12590,plain,
% 3.53/1.02      ( sK6(sK8,sK0(k2_relat_1(sK8),sK7)) = sK6(sK8,sK0(k2_relat_1(sK8),sK7)) ),
% 3.53/1.02      inference(instantiation,[status(thm)],[c_837]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_841,plain,
% 3.53/1.02      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.53/1.02      theory(equality) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_3781,plain,
% 3.53/1.02      ( r2_hidden(X0,X1)
% 3.53/1.02      | ~ r2_hidden(sK6(sK8,sK0(k2_relat_1(sK8),sK7)),k10_relat_1(sK8,sK7))
% 3.53/1.02      | X0 != sK6(sK8,sK0(k2_relat_1(sK8),sK7))
% 3.53/1.02      | X1 != k10_relat_1(sK8,sK7) ),
% 3.53/1.02      inference(instantiation,[status(thm)],[c_841]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_12589,plain,
% 3.53/1.02      ( r2_hidden(sK6(sK8,sK0(k2_relat_1(sK8),sK7)),X0)
% 3.53/1.02      | ~ r2_hidden(sK6(sK8,sK0(k2_relat_1(sK8),sK7)),k10_relat_1(sK8,sK7))
% 3.53/1.02      | X0 != k10_relat_1(sK8,sK7)
% 3.53/1.02      | sK6(sK8,sK0(k2_relat_1(sK8),sK7)) != sK6(sK8,sK0(k2_relat_1(sK8),sK7)) ),
% 3.53/1.02      inference(instantiation,[status(thm)],[c_3781]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_12592,plain,
% 3.53/1.02      ( ~ r2_hidden(sK6(sK8,sK0(k2_relat_1(sK8),sK7)),k10_relat_1(sK8,sK7))
% 3.53/1.02      | r2_hidden(sK6(sK8,sK0(k2_relat_1(sK8),sK7)),k1_xboole_0)
% 3.53/1.02      | sK6(sK8,sK0(k2_relat_1(sK8),sK7)) != sK6(sK8,sK0(k2_relat_1(sK8),sK7))
% 3.53/1.02      | k1_xboole_0 != k10_relat_1(sK8,sK7) ),
% 3.53/1.02      inference(instantiation,[status(thm)],[c_12589]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_839,plain,
% 3.53/1.02      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.53/1.02      theory(equality) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_11663,plain,
% 3.53/1.02      ( ~ r1_xboole_0(X0,X1)
% 3.53/1.02      | r1_xboole_0(X2,k10_relat_1(sK8,sK7))
% 3.53/1.02      | X2 != X0
% 3.53/1.02      | k10_relat_1(sK8,sK7) != X1 ),
% 3.53/1.02      inference(instantiation,[status(thm)],[c_839]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_11665,plain,
% 3.53/1.02      ( r1_xboole_0(k1_xboole_0,k10_relat_1(sK8,sK7))
% 3.53/1.02      | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
% 3.53/1.02      | k10_relat_1(sK8,sK7) != k1_xboole_0
% 3.53/1.02      | k1_xboole_0 != k1_xboole_0 ),
% 3.53/1.02      inference(instantiation,[status(thm)],[c_11663]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_2,plain,
% 3.53/1.02      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 3.53/1.02      inference(cnf_transformation,[],[f38]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_3782,plain,
% 3.53/1.02      ( ~ r2_hidden(sK6(sK8,sK0(k2_relat_1(sK8),sK7)),X0)
% 3.53/1.02      | ~ r2_hidden(sK6(sK8,sK0(k2_relat_1(sK8),sK7)),k10_relat_1(sK8,sK7))
% 3.53/1.02      | ~ r1_xboole_0(X0,k10_relat_1(sK8,sK7)) ),
% 3.53/1.02      inference(instantiation,[status(thm)],[c_2]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_3789,plain,
% 3.53/1.02      ( ~ r2_hidden(sK6(sK8,sK0(k2_relat_1(sK8),sK7)),k10_relat_1(sK8,sK7))
% 3.53/1.02      | ~ r2_hidden(sK6(sK8,sK0(k2_relat_1(sK8),sK7)),k1_xboole_0)
% 3.53/1.02      | ~ r1_xboole_0(k1_xboole_0,k10_relat_1(sK8,sK7)) ),
% 3.53/1.02      inference(instantiation,[status(thm)],[c_3782]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_2268,plain,
% 3.53/1.02      ( ~ r2_hidden(sK2(sK8,X0,X1),X0)
% 3.53/1.02      | ~ r2_hidden(sK2(sK8,X0,X1),X2)
% 3.53/1.02      | ~ r1_xboole_0(X2,X0) ),
% 3.53/1.02      inference(instantiation,[status(thm)],[c_2]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_2275,plain,
% 3.53/1.02      ( ~ r2_hidden(sK2(sK8,k1_xboole_0,k1_xboole_0),k1_xboole_0)
% 3.53/1.02      | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 3.53/1.02      inference(instantiation,[status(thm)],[c_2268]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_20,negated_conjecture,
% 3.53/1.02      ( r1_xboole_0(k2_relat_1(sK8),sK7)
% 3.53/1.02      | k1_xboole_0 = k10_relat_1(sK8,sK7) ),
% 3.53/1.02      inference(cnf_transformation,[],[f54]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_1286,plain,
% 3.53/1.02      ( k1_xboole_0 = k10_relat_1(sK8,sK7)
% 3.53/1.02      | r1_xboole_0(k2_relat_1(sK8),sK7) = iProver_top ),
% 3.53/1.02      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_1,plain,
% 3.53/1.02      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 3.53/1.02      inference(cnf_transformation,[],[f34]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_1295,plain,
% 3.53/1.02      ( k3_xboole_0(X0,X1) = k1_xboole_0
% 3.53/1.02      | r1_xboole_0(X0,X1) != iProver_top ),
% 3.53/1.02      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_1726,plain,
% 3.53/1.02      ( k10_relat_1(sK8,sK7) = k1_xboole_0
% 3.53/1.02      | k3_xboole_0(k2_relat_1(sK8),sK7) = k1_xboole_0 ),
% 3.53/1.02      inference(superposition,[status(thm)],[c_1286,c_1295]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_0,plain,
% 3.53/1.02      ( r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0 ),
% 3.53/1.02      inference(cnf_transformation,[],[f35]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_1296,plain,
% 3.53/1.02      ( k3_xboole_0(X0,X1) != k1_xboole_0
% 3.53/1.02      | r1_xboole_0(X0,X1) = iProver_top ),
% 3.53/1.02      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_2054,plain,
% 3.53/1.02      ( k10_relat_1(sK8,sK7) = k1_xboole_0
% 3.53/1.02      | r1_xboole_0(k2_relat_1(sK8),sK7) = iProver_top ),
% 3.53/1.02      inference(superposition,[status(thm)],[c_1726,c_1296]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_1982,plain,
% 3.53/1.02      ( ~ r2_hidden(sK1(sK8,X0,X1),X1)
% 3.53/1.02      | ~ r2_hidden(sK1(sK8,X0,X1),X2)
% 3.53/1.02      | ~ r1_xboole_0(X2,X1) ),
% 3.53/1.02      inference(instantiation,[status(thm)],[c_2]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_1989,plain,
% 3.53/1.02      ( ~ r2_hidden(sK1(sK8,k1_xboole_0,k1_xboole_0),k1_xboole_0)
% 3.53/1.02      | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 3.53/1.02      inference(instantiation,[status(thm)],[c_1982]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_16,plain,
% 3.53/1.02      ( ~ v1_relat_1(X0)
% 3.53/1.02      | k10_relat_1(X0,k3_xboole_0(k2_relat_1(X0),X1)) = k10_relat_1(X0,X1) ),
% 3.53/1.02      inference(cnf_transformation,[],[f50]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_21,negated_conjecture,
% 3.53/1.02      ( v1_relat_1(sK8) ),
% 3.53/1.02      inference(cnf_transformation,[],[f53]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_274,plain,
% 3.53/1.02      ( k10_relat_1(X0,k3_xboole_0(k2_relat_1(X0),X1)) = k10_relat_1(X0,X1)
% 3.53/1.02      | sK8 != X0 ),
% 3.53/1.02      inference(resolution_lifted,[status(thm)],[c_16,c_21]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_275,plain,
% 3.53/1.02      ( k10_relat_1(sK8,k3_xboole_0(k2_relat_1(sK8),X0)) = k10_relat_1(sK8,X0) ),
% 3.53/1.02      inference(unflattening,[status(thm)],[c_274]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_1729,plain,
% 3.53/1.02      ( k10_relat_1(sK8,sK7) = k1_xboole_0
% 3.53/1.02      | k10_relat_1(sK8,k1_xboole_0) = k10_relat_1(sK8,sK7) ),
% 3.53/1.02      inference(superposition,[status(thm)],[c_1726,c_275]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_19,negated_conjecture,
% 3.53/1.02      ( ~ r1_xboole_0(k2_relat_1(sK8),sK7)
% 3.53/1.02      | k1_xboole_0 != k10_relat_1(sK8,sK7) ),
% 3.53/1.02      inference(cnf_transformation,[],[f55]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_1287,plain,
% 3.53/1.02      ( k1_xboole_0 != k10_relat_1(sK8,sK7)
% 3.53/1.02      | r1_xboole_0(k2_relat_1(sK8),sK7) != iProver_top ),
% 3.53/1.02      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_1783,plain,
% 3.53/1.02      ( k10_relat_1(sK8,sK7) = k1_xboole_0
% 3.53/1.02      | k10_relat_1(sK8,k1_xboole_0) != k1_xboole_0
% 3.53/1.02      | r1_xboole_0(k2_relat_1(sK8),sK7) != iProver_top ),
% 3.53/1.02      inference(superposition,[status(thm)],[c_1729,c_1287]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_24,plain,
% 3.53/1.02      ( k1_xboole_0 != k10_relat_1(sK8,sK7)
% 3.53/1.02      | r1_xboole_0(k2_relat_1(sK8),sK7) != iProver_top ),
% 3.53/1.02      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_860,plain,
% 3.53/1.02      ( k1_xboole_0 = k1_xboole_0 ),
% 3.53/1.02      inference(instantiation,[status(thm)],[c_837]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_838,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_1495,plain,
% 3.53/1.02      ( k10_relat_1(sK8,sK7) != X0
% 3.53/1.02      | k1_xboole_0 != X0
% 3.53/1.02      | k1_xboole_0 = k10_relat_1(sK8,sK7) ),
% 3.53/1.02      inference(instantiation,[status(thm)],[c_838]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_1496,plain,
% 3.53/1.02      ( k10_relat_1(sK8,sK7) != k1_xboole_0
% 3.53/1.02      | k1_xboole_0 = k10_relat_1(sK8,sK7)
% 3.53/1.02      | k1_xboole_0 != k1_xboole_0 ),
% 3.53/1.02      inference(instantiation,[status(thm)],[c_1495]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_1786,plain,
% 3.53/1.02      ( k10_relat_1(sK8,k1_xboole_0) != k1_xboole_0
% 3.53/1.02      | r1_xboole_0(k2_relat_1(sK8),sK7) != iProver_top ),
% 3.53/1.02      inference(global_propositional_subsumption,
% 3.53/1.02                [status(thm)],
% 3.53/1.02                [c_1783,c_24,c_860,c_1496]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_1788,plain,
% 3.53/1.02      ( ~ r1_xboole_0(k2_relat_1(sK8),sK7)
% 3.53/1.02      | k10_relat_1(sK8,k1_xboole_0) != k1_xboole_0 ),
% 3.53/1.02      inference(predicate_to_equality_rev,[status(thm)],[c_1786]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_9,plain,
% 3.53/1.02      ( ~ r2_hidden(X0,X1)
% 3.53/1.02      | r2_hidden(X2,k10_relat_1(X3,X1))
% 3.53/1.02      | ~ r2_hidden(k4_tarski(X2,X0),X3)
% 3.53/1.02      | ~ v1_relat_1(X3) ),
% 3.53/1.02      inference(cnf_transformation,[],[f56]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_328,plain,
% 3.53/1.02      ( ~ r2_hidden(X0,X1)
% 3.53/1.02      | r2_hidden(X2,k10_relat_1(X3,X1))
% 3.53/1.02      | ~ r2_hidden(k4_tarski(X2,X0),X3)
% 3.53/1.02      | sK8 != X3 ),
% 3.53/1.02      inference(resolution_lifted,[status(thm)],[c_9,c_21]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_329,plain,
% 3.53/1.02      ( ~ r2_hidden(X0,X1)
% 3.53/1.02      | r2_hidden(X2,k10_relat_1(sK8,X1))
% 3.53/1.02      | ~ r2_hidden(k4_tarski(X2,X0),sK8) ),
% 3.53/1.02      inference(unflattening,[status(thm)],[c_328]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_1464,plain,
% 3.53/1.02      ( r2_hidden(X0,k10_relat_1(sK8,sK7))
% 3.53/1.02      | ~ r2_hidden(k4_tarski(X0,sK0(k2_relat_1(sK8),sK7)),sK8)
% 3.53/1.02      | ~ r2_hidden(sK0(k2_relat_1(sK8),sK7),sK7) ),
% 3.53/1.02      inference(instantiation,[status(thm)],[c_329]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_1659,plain,
% 3.53/1.02      ( r2_hidden(sK6(sK8,sK0(k2_relat_1(sK8),sK7)),k10_relat_1(sK8,sK7))
% 3.53/1.02      | ~ r2_hidden(k4_tarski(sK6(sK8,sK0(k2_relat_1(sK8),sK7)),sK0(k2_relat_1(sK8),sK7)),sK8)
% 3.53/1.02      | ~ r2_hidden(sK0(k2_relat_1(sK8),sK7),sK7) ),
% 3.53/1.02      inference(instantiation,[status(thm)],[c_1464]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_15,plain,
% 3.53/1.02      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 3.53/1.02      | r2_hidden(k4_tarski(sK6(X1,X0),X0),X1) ),
% 3.53/1.02      inference(cnf_transformation,[],[f60]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_1492,plain,
% 3.53/1.02      ( r2_hidden(k4_tarski(sK6(sK8,sK0(k2_relat_1(sK8),sK7)),sK0(k2_relat_1(sK8),sK7)),sK8)
% 3.53/1.02      | ~ r2_hidden(sK0(k2_relat_1(sK8),sK7),k2_relat_1(sK8)) ),
% 3.53/1.02      inference(instantiation,[status(thm)],[c_15]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_4,plain,
% 3.53/1.02      ( r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1) ),
% 3.53/1.02      inference(cnf_transformation,[],[f36]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_1435,plain,
% 3.53/1.02      ( r2_hidden(sK0(k2_relat_1(sK8),sK7),k2_relat_1(sK8))
% 3.53/1.02      | r1_xboole_0(k2_relat_1(sK8),sK7) ),
% 3.53/1.02      inference(instantiation,[status(thm)],[c_4]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_3,plain,
% 3.53/1.02      ( r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1) ),
% 3.53/1.02      inference(cnf_transformation,[],[f37]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_1432,plain,
% 3.53/1.02      ( r2_hidden(sK0(k2_relat_1(sK8),sK7),sK7)
% 3.53/1.02      | r1_xboole_0(k2_relat_1(sK8),sK7) ),
% 3.53/1.02      inference(instantiation,[status(thm)],[c_3]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_7,plain,
% 3.53/1.02      ( r2_hidden(sK2(X0,X1,X2),X1)
% 3.53/1.02      | r2_hidden(sK1(X0,X1,X2),X2)
% 3.53/1.02      | ~ v1_relat_1(X0)
% 3.53/1.02      | k10_relat_1(X0,X1) = X2 ),
% 3.53/1.02      inference(cnf_transformation,[],[f44]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_295,plain,
% 3.53/1.02      ( r2_hidden(sK2(X0,X1,X2),X1)
% 3.53/1.02      | r2_hidden(sK1(X0,X1,X2),X2)
% 3.53/1.02      | k10_relat_1(X0,X1) = X2
% 3.53/1.02      | sK8 != X0 ),
% 3.53/1.02      inference(resolution_lifted,[status(thm)],[c_7,c_21]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_296,plain,
% 3.53/1.02      ( r2_hidden(sK2(sK8,X0,X1),X0)
% 3.53/1.02      | r2_hidden(sK1(sK8,X0,X1),X1)
% 3.53/1.02      | k10_relat_1(sK8,X0) = X1 ),
% 3.53/1.02      inference(unflattening,[status(thm)],[c_295]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_298,plain,
% 3.53/1.02      ( r2_hidden(sK2(sK8,k1_xboole_0,k1_xboole_0),k1_xboole_0)
% 3.53/1.02      | r2_hidden(sK1(sK8,k1_xboole_0,k1_xboole_0),k1_xboole_0)
% 3.53/1.02      | k10_relat_1(sK8,k1_xboole_0) = k1_xboole_0 ),
% 3.53/1.02      inference(instantiation,[status(thm)],[c_296]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_64,plain,
% 3.53/1.02      ( r1_xboole_0(k1_xboole_0,k1_xboole_0)
% 3.53/1.02      | k3_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
% 3.53/1.02      inference(instantiation,[status(thm)],[c_0]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_5,plain,
% 3.53/1.02      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.53/1.02      inference(cnf_transformation,[],[f39]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_54,plain,
% 3.53/1.02      ( k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.53/1.02      inference(instantiation,[status(thm)],[c_5]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_23,plain,
% 3.53/1.02      ( k1_xboole_0 = k10_relat_1(sK8,sK7)
% 3.53/1.02      | r1_xboole_0(k2_relat_1(sK8),sK7) = iProver_top ),
% 3.53/1.02      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(contradiction,plain,
% 3.53/1.02      ( $false ),
% 3.53/1.02      inference(minisat,
% 3.53/1.02                [status(thm)],
% 3.53/1.02                [c_12590,c_12592,c_11665,c_3789,c_2275,c_2054,c_1989,
% 3.53/1.02                 c_1788,c_1786,c_1659,c_1492,c_1435,c_1432,c_860,c_298,
% 3.53/1.02                 c_64,c_54,c_23]) ).
% 3.53/1.02  
% 3.53/1.02  
% 3.53/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 3.53/1.02  
% 3.53/1.02  ------                               Statistics
% 3.53/1.02  
% 3.53/1.02  ------ General
% 3.53/1.02  
% 3.53/1.02  abstr_ref_over_cycles:                  0
% 3.53/1.02  abstr_ref_under_cycles:                 0
% 3.53/1.02  gc_basic_clause_elim:                   0
% 3.53/1.02  forced_gc_time:                         0
% 3.53/1.02  parsing_time:                           0.011
% 3.53/1.02  unif_index_cands_time:                  0.
% 3.53/1.02  unif_index_add_time:                    0.
% 3.53/1.02  orderings_time:                         0.
% 3.53/1.02  out_proof_time:                         0.005
% 3.53/1.02  total_time:                             0.5
% 3.53/1.02  num_of_symbols:                         49
% 3.53/1.02  num_of_terms:                           12634
% 3.53/1.02  
% 3.53/1.02  ------ Preprocessing
% 3.53/1.02  
% 3.53/1.02  num_of_splits:                          0
% 3.53/1.02  num_of_split_atoms:                     0
% 3.53/1.02  num_of_reused_defs:                     0
% 3.53/1.02  num_eq_ax_congr_red:                    45
% 3.53/1.02  num_of_sem_filtered_clauses:            1
% 3.53/1.02  num_of_subtypes:                        0
% 3.53/1.02  monotx_restored_types:                  0
% 3.53/1.02  sat_num_of_epr_types:                   0
% 3.53/1.02  sat_num_of_non_cyclic_types:            0
% 3.53/1.02  sat_guarded_non_collapsed_types:        0
% 3.53/1.02  num_pure_diseq_elim:                    0
% 3.53/1.02  simp_replaced_by:                       0
% 3.53/1.02  res_preprocessed:                       110
% 3.53/1.02  prep_upred:                             0
% 3.53/1.02  prep_unflattend:                        39
% 3.53/1.02  smt_new_axioms:                         0
% 3.53/1.02  pred_elim_cands:                        2
% 3.53/1.02  pred_elim:                              1
% 3.53/1.02  pred_elim_cl:                           1
% 3.53/1.02  pred_elim_cycles:                       3
% 3.53/1.02  merged_defs:                            16
% 3.53/1.02  merged_defs_ncl:                        0
% 3.53/1.02  bin_hyper_res:                          16
% 3.53/1.02  prep_cycles:                            4
% 3.53/1.02  pred_elim_time:                         0.009
% 3.53/1.02  splitting_time:                         0.
% 3.53/1.02  sem_filter_time:                        0.
% 3.53/1.02  monotx_time:                            0.001
% 3.53/1.02  subtype_inf_time:                       0.
% 3.53/1.02  
% 3.53/1.02  ------ Problem properties
% 3.53/1.02  
% 3.53/1.02  clauses:                                21
% 3.53/1.02  conjectures:                            2
% 3.53/1.02  epr:                                    1
% 3.53/1.02  horn:                                   15
% 3.53/1.02  ground:                                 4
% 3.53/1.02  unary:                                  4
% 3.53/1.02  binary:                                 10
% 3.53/1.02  lits:                                   46
% 3.53/1.02  lits_eq:                                13
% 3.53/1.02  fd_pure:                                0
% 3.53/1.02  fd_pseudo:                              0
% 3.53/1.02  fd_cond:                                0
% 3.53/1.02  fd_pseudo_cond:                         5
% 3.53/1.02  ac_symbols:                             0
% 3.53/1.02  
% 3.53/1.02  ------ Propositional Solver
% 3.53/1.02  
% 3.53/1.02  prop_solver_calls:                      29
% 3.53/1.02  prop_fast_solver_calls:                 1008
% 3.53/1.02  smt_solver_calls:                       0
% 3.53/1.02  smt_fast_solver_calls:                  0
% 3.53/1.02  prop_num_of_clauses:                    3697
% 3.53/1.02  prop_preprocess_simplified:             7390
% 3.53/1.02  prop_fo_subsumed:                       44
% 3.53/1.02  prop_solver_time:                       0.
% 3.53/1.02  smt_solver_time:                        0.
% 3.53/1.02  smt_fast_solver_time:                   0.
% 3.53/1.02  prop_fast_solver_time:                  0.
% 3.53/1.02  prop_unsat_core_time:                   0.
% 3.53/1.02  
% 3.53/1.02  ------ QBF
% 3.53/1.02  
% 3.53/1.02  qbf_q_res:                              0
% 3.53/1.02  qbf_num_tautologies:                    0
% 3.53/1.02  qbf_prep_cycles:                        0
% 3.53/1.02  
% 3.53/1.02  ------ BMC1
% 3.53/1.02  
% 3.53/1.02  bmc1_current_bound:                     -1
% 3.53/1.02  bmc1_last_solved_bound:                 -1
% 3.53/1.02  bmc1_unsat_core_size:                   -1
% 3.53/1.02  bmc1_unsat_core_parents_size:           -1
% 3.53/1.02  bmc1_merge_next_fun:                    0
% 3.53/1.02  bmc1_unsat_core_clauses_time:           0.
% 3.53/1.02  
% 3.53/1.02  ------ Instantiation
% 3.53/1.02  
% 3.53/1.02  inst_num_of_clauses:                    918
% 3.53/1.02  inst_num_in_passive:                    53
% 3.53/1.02  inst_num_in_active:                     515
% 3.53/1.02  inst_num_in_unprocessed:                349
% 3.53/1.02  inst_num_of_loops:                      669
% 3.53/1.02  inst_num_of_learning_restarts:          0
% 3.53/1.02  inst_num_moves_active_passive:          148
% 3.53/1.02  inst_lit_activity:                      0
% 3.53/1.02  inst_lit_activity_moves:                0
% 3.53/1.02  inst_num_tautologies:                   0
% 3.53/1.02  inst_num_prop_implied:                  0
% 3.53/1.02  inst_num_existing_simplified:           0
% 3.53/1.02  inst_num_eq_res_simplified:             0
% 3.53/1.02  inst_num_child_elim:                    0
% 3.53/1.02  inst_num_of_dismatching_blockings:      728
% 3.53/1.02  inst_num_of_non_proper_insts:           1126
% 3.53/1.02  inst_num_of_duplicates:                 0
% 3.53/1.02  inst_inst_num_from_inst_to_res:         0
% 3.53/1.02  inst_dismatching_checking_time:         0.
% 3.53/1.02  
% 3.53/1.02  ------ Resolution
% 3.53/1.02  
% 3.53/1.02  res_num_of_clauses:                     0
% 3.53/1.02  res_num_in_passive:                     0
% 3.53/1.02  res_num_in_active:                      0
% 3.53/1.02  res_num_of_loops:                       114
% 3.53/1.02  res_forward_subset_subsumed:            75
% 3.53/1.02  res_backward_subset_subsumed:           0
% 3.53/1.02  res_forward_subsumed:                   0
% 3.53/1.02  res_backward_subsumed:                  0
% 3.53/1.02  res_forward_subsumption_resolution:     0
% 3.53/1.02  res_backward_subsumption_resolution:    0
% 3.53/1.02  res_clause_to_clause_subsumption:       4128
% 3.53/1.02  res_orphan_elimination:                 0
% 3.53/1.02  res_tautology_del:                      111
% 3.53/1.02  res_num_eq_res_simplified:              0
% 3.53/1.02  res_num_sel_changes:                    0
% 3.53/1.02  res_moves_from_active_to_pass:          0
% 3.53/1.02  
% 3.53/1.02  ------ Superposition
% 3.53/1.02  
% 3.53/1.02  sup_time_total:                         0.
% 3.53/1.02  sup_time_generating:                    0.
% 3.53/1.02  sup_time_sim_full:                      0.
% 3.53/1.02  sup_time_sim_immed:                     0.
% 3.53/1.02  
% 3.53/1.02  sup_num_of_clauses:                     284
% 3.53/1.02  sup_num_in_active:                      126
% 3.53/1.02  sup_num_in_passive:                     158
% 3.53/1.02  sup_num_of_loops:                       132
% 3.53/1.02  sup_fw_superposition:                   466
% 3.53/1.02  sup_bw_superposition:                   156
% 3.53/1.02  sup_immediate_simplified:               250
% 3.53/1.02  sup_given_eliminated:                   0
% 3.53/1.02  comparisons_done:                       0
% 3.53/1.02  comparisons_avoided:                    0
% 3.53/1.02  
% 3.53/1.02  ------ Simplifications
% 3.53/1.02  
% 3.53/1.02  
% 3.53/1.02  sim_fw_subset_subsumed:                 12
% 3.53/1.02  sim_bw_subset_subsumed:                 21
% 3.53/1.02  sim_fw_subsumed:                        63
% 3.53/1.02  sim_bw_subsumed:                        0
% 3.53/1.02  sim_fw_subsumption_res:                 1
% 3.53/1.02  sim_bw_subsumption_res:                 0
% 3.53/1.02  sim_tautology_del:                      60
% 3.53/1.02  sim_eq_tautology_del:                   158
% 3.53/1.02  sim_eq_res_simp:                        2
% 3.53/1.02  sim_fw_demodulated:                     204
% 3.53/1.02  sim_bw_demodulated:                     2
% 3.53/1.02  sim_light_normalised:                   34
% 3.53/1.02  sim_joinable_taut:                      0
% 3.53/1.02  sim_joinable_simp:                      0
% 3.53/1.02  sim_ac_normalised:                      0
% 3.53/1.02  sim_smt_subsumption:                    0
% 3.53/1.02  
%------------------------------------------------------------------------------
