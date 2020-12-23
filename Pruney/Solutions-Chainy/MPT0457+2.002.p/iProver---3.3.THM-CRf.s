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
% DateTime   : Thu Dec  3 11:43:27 EST 2020

% Result     : Theorem 15.31s
% Output     : CNFRefutation 15.31s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 307 expanded)
%              Number of clauses        :   28 (  91 expanded)
%              Number of leaves         :   18 (  95 expanded)
%              Depth                    :   16
%              Number of atoms          :  339 (1406 expanded)
%              Number of equality atoms :   50 ( 217 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   17 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
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

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f15,plain,(
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
    inference(rectify,[],[f14])).

fof(f16,plain,(
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

fof(f17,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f37,f40])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f7,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          & v1_relat_1(X1) )
     => ( ~ r1_tarski(k2_relat_1(k5_relat_1(X0,sK9)),k2_relat_1(sK9))
        & v1_relat_1(sK9) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k2_relat_1(k5_relat_1(sK8,X1)),k2_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ~ r1_tarski(k2_relat_1(k5_relat_1(sK8,sK9)),k2_relat_1(sK9))
    & v1_relat_1(sK9)
    & v1_relat_1(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f12,f31,f30])).

fof(f54,plain,(
    ~ r1_tarski(k2_relat_1(k5_relat_1(sK8,sK9)),k2_relat_1(sK9)) ),
    inference(cnf_transformation,[],[f32])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f11,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ? [X3,X4] :
                      ( ( ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                      & ( ? [X5] :
                            ( r2_hidden(k4_tarski(X5,X4),X1)
                            & r2_hidden(k4_tarski(X3,X5),X0) )
                        | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
                & ( ! [X3,X4] :
                      ( ( r2_hidden(k4_tarski(X3,X4),X2)
                        | ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) ) )
                      & ( ? [X5] :
                            ( r2_hidden(k4_tarski(X5,X4),X1)
                            & r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ? [X3,X4] :
                      ( ( ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                      & ( ? [X6] :
                            ( r2_hidden(k4_tarski(X6,X4),X1)
                            & r2_hidden(k4_tarski(X3,X6),X0) )
                        | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
                & ( ! [X7,X8] :
                      ( ( r2_hidden(k4_tarski(X7,X8),X2)
                        | ! [X9] :
                            ( ~ r2_hidden(k4_tarski(X9,X8),X1)
                            | ~ r2_hidden(k4_tarski(X7,X9),X0) ) )
                      & ( ? [X10] :
                            ( r2_hidden(k4_tarski(X10,X8),X1)
                            & r2_hidden(k4_tarski(X7,X10),X0) )
                        | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f24])).

fof(f28,plain,(
    ! [X8,X7,X1,X0] :
      ( ? [X10] :
          ( r2_hidden(k4_tarski(X10,X8),X1)
          & r2_hidden(k4_tarski(X7,X10),X0) )
     => ( r2_hidden(k4_tarski(sK7(X0,X1,X7,X8),X8),X1)
        & r2_hidden(k4_tarski(X7,sK7(X0,X1,X7,X8)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k4_tarski(X6,X4),X1)
          & r2_hidden(k4_tarski(X3,X6),X0) )
     => ( r2_hidden(k4_tarski(sK6(X0,X1,X2),X4),X1)
        & r2_hidden(k4_tarski(X3,sK6(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ! [X5] :
                ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                | ~ r2_hidden(k4_tarski(X3,X5),X0) )
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ? [X6] :
                ( r2_hidden(k4_tarski(X6,X4),X1)
                & r2_hidden(k4_tarski(X3,X6),X0) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ! [X5] :
              ( ~ r2_hidden(k4_tarski(X5,sK5(X0,X1,X2)),X1)
              | ~ r2_hidden(k4_tarski(sK4(X0,X1,X2),X5),X0) )
          | ~ r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2) )
        & ( ? [X6] :
              ( r2_hidden(k4_tarski(X6,sK5(X0,X1,X2)),X1)
              & r2_hidden(k4_tarski(sK4(X0,X1,X2),X6),X0) )
          | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ( ( ! [X5] :
                          ( ~ r2_hidden(k4_tarski(X5,sK5(X0,X1,X2)),X1)
                          | ~ r2_hidden(k4_tarski(sK4(X0,X1,X2),X5),X0) )
                      | ~ r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2) )
                    & ( ( r2_hidden(k4_tarski(sK6(X0,X1,X2),sK5(X0,X1,X2)),X1)
                        & r2_hidden(k4_tarski(sK4(X0,X1,X2),sK6(X0,X1,X2)),X0) )
                      | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2) ) ) )
                & ( ! [X7,X8] :
                      ( ( r2_hidden(k4_tarski(X7,X8),X2)
                        | ! [X9] :
                            ( ~ r2_hidden(k4_tarski(X9,X8),X1)
                            | ~ r2_hidden(k4_tarski(X7,X9),X0) ) )
                      & ( ( r2_hidden(k4_tarski(sK7(X0,X1,X7,X8),X8),X1)
                          & r2_hidden(k4_tarski(X7,sK7(X0,X1,X7,X8)),X0) )
                        | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f25,f28,f27,f26])).

fof(f46,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK7(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f67,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK7(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f19,plain,(
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
    inference(rectify,[],[f18])).

fof(f22,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK3(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK2(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK1(X0,X1)),X0)
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK1(X0,X1)),X0)
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK1(X0,X1)),X0)
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0)
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK3(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f19,f22,f21,f20])).

fof(f42,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f64,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X6,X5),X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f41,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f65,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK3(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f41])).

fof(f52,plain,(
    v1_relat_1(sK8) ),
    inference(cnf_transformation,[],[f32])).

fof(f53,plain,(
    v1_relat_1(sK9) ),
    inference(cnf_transformation,[],[f32])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f38,f40])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_3462,plain,
    ( r2_hidden(sK0(X0,X1,X1),X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X1 ),
    inference(factoring,[status(thm)],[c_1])).

cnf(c_371,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_370,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2144,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_371,c_370])).

cnf(c_7457,plain,
    ( r2_hidden(sK0(X0,X1,X1),X1)
    | X1 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(resolution,[status(thm)],[c_3462,c_2144])).

cnf(c_6,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_18,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(k5_relat_1(sK8,sK9)),k2_relat_1(sK9)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_235,plain,
    ( k2_relat_1(k5_relat_1(sK8,sK9)) != k4_xboole_0(X0,X1)
    | k2_relat_1(sK9) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_18])).

cnf(c_236,plain,
    ( k2_relat_1(k5_relat_1(sK8,sK9)) != k4_xboole_0(k2_relat_1(sK9),X0) ),
    inference(unflattening,[status(thm)],[c_235])).

cnf(c_35636,plain,
    ( r2_hidden(sK0(k2_relat_1(sK9),k2_relat_1(k5_relat_1(sK8,sK9)),k2_relat_1(k5_relat_1(sK8,sK9))),k2_relat_1(k5_relat_1(sK8,sK9))) ),
    inference(resolution,[status(thm)],[c_7457,c_236])).

cnf(c_17,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_15,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
    | r2_hidden(k4_tarski(sK7(X2,X3,X0,X1),X1),X3)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(k5_relat_1(X2,X3)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_791,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
    | r2_hidden(k4_tarski(sK7(X2,X3,X0,X1),X1),X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_17,c_15])).

cnf(c_9,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_9672,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),k5_relat_1(X3,X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X3) ),
    inference(resolution,[status(thm)],[c_791,c_9])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(k4_tarski(sK3(X1,X0),X0),X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_10472,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | ~ r2_hidden(X0,k2_relat_1(k5_relat_1(X2,X1)))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(resolution,[status(thm)],[c_9672,c_10])).

cnf(c_35827,plain,
    ( r2_hidden(sK0(k2_relat_1(sK9),k2_relat_1(k5_relat_1(sK8,sK9)),k2_relat_1(k5_relat_1(sK8,sK9))),k2_relat_1(sK9))
    | ~ v1_relat_1(sK9)
    | ~ v1_relat_1(sK8) ),
    inference(resolution,[status(thm)],[c_35636,c_10472])).

cnf(c_20,negated_conjecture,
    ( v1_relat_1(sK8) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_19,negated_conjecture,
    ( v1_relat_1(sK9) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_36069,plain,
    ( r2_hidden(sK0(k2_relat_1(sK9),k2_relat_1(k5_relat_1(sK8,sK9)),k2_relat_1(k5_relat_1(sK8,sK9))),k2_relat_1(sK9)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_35827,c_20,c_19])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | ~ r2_hidden(sK0(X0,X1,X2),X0)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_35825,plain,
    ( ~ r2_hidden(sK0(k2_relat_1(sK9),k2_relat_1(k5_relat_1(sK8,sK9)),k2_relat_1(k5_relat_1(sK8,sK9))),k2_relat_1(k5_relat_1(sK8,sK9)))
    | ~ r2_hidden(sK0(k2_relat_1(sK9),k2_relat_1(k5_relat_1(sK8,sK9)),k2_relat_1(k5_relat_1(sK8,sK9))),k2_relat_1(sK9))
    | k4_xboole_0(k2_relat_1(sK9),k4_xboole_0(k2_relat_1(sK9),k2_relat_1(k5_relat_1(sK8,sK9)))) = k2_relat_1(k5_relat_1(sK8,sK9)) ),
    inference(resolution,[status(thm)],[c_35636,c_0])).

cnf(c_36080,plain,
    ( ~ r2_hidden(sK0(k2_relat_1(sK9),k2_relat_1(k5_relat_1(sK8,sK9)),k2_relat_1(k5_relat_1(sK8,sK9))),k2_relat_1(k5_relat_1(sK8,sK9)))
    | k4_xboole_0(k2_relat_1(sK9),k4_xboole_0(k2_relat_1(sK9),k2_relat_1(k5_relat_1(sK8,sK9)))) = k2_relat_1(k5_relat_1(sK8,sK9)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_36069,c_35825])).

cnf(c_36084,plain,
    ( k4_xboole_0(k2_relat_1(sK9),k4_xboole_0(k2_relat_1(sK9),k2_relat_1(k5_relat_1(sK8,sK9)))) = k2_relat_1(k5_relat_1(sK8,sK9)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_36080,c_20,c_19,c_35636,c_35825,c_35827])).

cnf(c_36453,plain,
    ( k2_relat_1(k5_relat_1(sK8,sK9)) = k4_xboole_0(k2_relat_1(sK9),k4_xboole_0(k2_relat_1(sK9),k2_relat_1(k5_relat_1(sK8,sK9)))) ),
    inference(resolution,[status(thm)],[c_36084,c_2144])).

cnf(c_36563,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_36453,c_236])).

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
% 0.13/0.34  % DateTime   : Tue Dec  1 12:49:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 15.31/2.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.31/2.49  
% 15.31/2.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.31/2.49  
% 15.31/2.49  ------  iProver source info
% 15.31/2.49  
% 15.31/2.49  git: date: 2020-06-30 10:37:57 +0100
% 15.31/2.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.31/2.49  git: non_committed_changes: false
% 15.31/2.49  git: last_make_outside_of_git: false
% 15.31/2.49  
% 15.31/2.49  ------ 
% 15.31/2.49  ------ Parsing...
% 15.31/2.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.31/2.49  
% 15.31/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 15.31/2.49  
% 15.31/2.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.31/2.49  
% 15.31/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.31/2.49  ------ Proving...
% 15.31/2.49  ------ Problem Properties 
% 15.31/2.49  
% 15.31/2.49  
% 15.31/2.49  clauses                                 20
% 15.31/2.49  conjectures                             2
% 15.31/2.49  EPR                                     2
% 15.31/2.49  Horn                                    15
% 15.31/2.49  unary                                   3
% 15.31/2.49  binary                                  4
% 15.31/2.49  lits                                    68
% 15.31/2.49  lits eq                                 9
% 15.31/2.49  fd_pure                                 0
% 15.31/2.49  fd_pseudo                               0
% 15.31/2.49  fd_cond                                 0
% 15.31/2.49  fd_pseudo_cond                          8
% 15.31/2.49  AC symbols                              0
% 15.31/2.49  
% 15.31/2.49  ------ Input Options Time Limit: Unbounded
% 15.31/2.49  
% 15.31/2.49  
% 15.31/2.49  ------ 
% 15.31/2.49  Current options:
% 15.31/2.49  ------ 
% 15.31/2.49  
% 15.31/2.49  
% 15.31/2.49  
% 15.31/2.49  
% 15.31/2.49  ------ Proving...
% 15.31/2.49  
% 15.31/2.49  
% 15.31/2.49  % SZS status Theorem for theBenchmark.p
% 15.31/2.49  
% 15.31/2.49   Resolution empty clause
% 15.31/2.49  
% 15.31/2.49  % SZS output start CNFRefutation for theBenchmark.p
% 15.31/2.49  
% 15.31/2.49  fof(f1,axiom,(
% 15.31/2.49    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 15.31/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.31/2.49  
% 15.31/2.49  fof(f13,plain,(
% 15.31/2.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 15.31/2.49    inference(nnf_transformation,[],[f1])).
% 15.31/2.49  
% 15.31/2.49  fof(f14,plain,(
% 15.31/2.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 15.31/2.49    inference(flattening,[],[f13])).
% 15.31/2.49  
% 15.31/2.49  fof(f15,plain,(
% 15.31/2.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 15.31/2.49    inference(rectify,[],[f14])).
% 15.31/2.49  
% 15.31/2.49  fof(f16,plain,(
% 15.31/2.49    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 15.31/2.49    introduced(choice_axiom,[])).
% 15.31/2.49  
% 15.31/2.49  fof(f17,plain,(
% 15.31/2.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 15.31/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).
% 15.31/2.49  
% 15.31/2.49  fof(f37,plain,(
% 15.31/2.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 15.31/2.49    inference(cnf_transformation,[],[f17])).
% 15.31/2.49  
% 15.31/2.49  fof(f3,axiom,(
% 15.31/2.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 15.31/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.31/2.49  
% 15.31/2.49  fof(f40,plain,(
% 15.31/2.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 15.31/2.49    inference(cnf_transformation,[],[f3])).
% 15.31/2.49  
% 15.31/2.49  fof(f56,plain,(
% 15.31/2.49    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 15.31/2.49    inference(definition_unfolding,[],[f37,f40])).
% 15.31/2.49  
% 15.31/2.49  fof(f2,axiom,(
% 15.31/2.49    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 15.31/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.31/2.49  
% 15.31/2.49  fof(f39,plain,(
% 15.31/2.49    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 15.31/2.49    inference(cnf_transformation,[],[f2])).
% 15.31/2.49  
% 15.31/2.49  fof(f7,conjecture,(
% 15.31/2.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 15.31/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.31/2.49  
% 15.31/2.49  fof(f8,negated_conjecture,(
% 15.31/2.49    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 15.31/2.49    inference(negated_conjecture,[],[f7])).
% 15.31/2.49  
% 15.31/2.49  fof(f12,plain,(
% 15.31/2.49    ? [X0] : (? [X1] : (~r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 15.31/2.49    inference(ennf_transformation,[],[f8])).
% 15.31/2.49  
% 15.31/2.49  fof(f31,plain,(
% 15.31/2.49    ( ! [X0] : (? [X1] : (~r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) & v1_relat_1(X1)) => (~r1_tarski(k2_relat_1(k5_relat_1(X0,sK9)),k2_relat_1(sK9)) & v1_relat_1(sK9))) )),
% 15.31/2.49    introduced(choice_axiom,[])).
% 15.31/2.49  
% 15.31/2.49  fof(f30,plain,(
% 15.31/2.49    ? [X0] : (? [X1] : (~r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k2_relat_1(k5_relat_1(sK8,X1)),k2_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(sK8))),
% 15.31/2.49    introduced(choice_axiom,[])).
% 15.31/2.49  
% 15.31/2.49  fof(f32,plain,(
% 15.31/2.49    (~r1_tarski(k2_relat_1(k5_relat_1(sK8,sK9)),k2_relat_1(sK9)) & v1_relat_1(sK9)) & v1_relat_1(sK8)),
% 15.31/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f12,f31,f30])).
% 15.31/2.49  
% 15.31/2.49  fof(f54,plain,(
% 15.31/2.49    ~r1_tarski(k2_relat_1(k5_relat_1(sK8,sK9)),k2_relat_1(sK9))),
% 15.31/2.49    inference(cnf_transformation,[],[f32])).
% 15.31/2.49  
% 15.31/2.49  fof(f6,axiom,(
% 15.31/2.49    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 15.31/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.31/2.49  
% 15.31/2.49  fof(f10,plain,(
% 15.31/2.49    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 15.31/2.49    inference(ennf_transformation,[],[f6])).
% 15.31/2.49  
% 15.31/2.49  fof(f11,plain,(
% 15.31/2.49    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 15.31/2.49    inference(flattening,[],[f10])).
% 15.31/2.49  
% 15.31/2.49  fof(f51,plain,(
% 15.31/2.49    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 15.31/2.49    inference(cnf_transformation,[],[f11])).
% 15.31/2.49  
% 15.31/2.49  fof(f5,axiom,(
% 15.31/2.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))))))),
% 15.31/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.31/2.49  
% 15.31/2.49  fof(f9,plain,(
% 15.31/2.49    ! [X0] : (! [X1] : (! [X2] : ((k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 15.31/2.49    inference(ennf_transformation,[],[f5])).
% 15.31/2.49  
% 15.31/2.49  fof(f24,plain,(
% 15.31/2.49    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | ! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0))) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 15.31/2.49    inference(nnf_transformation,[],[f9])).
% 15.31/2.49  
% 15.31/2.49  fof(f25,plain,(
% 15.31/2.49    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0))) & (? [X10] : (r2_hidden(k4_tarski(X10,X8),X1) & r2_hidden(k4_tarski(X7,X10),X0)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 15.31/2.49    inference(rectify,[],[f24])).
% 15.31/2.49  
% 15.31/2.49  fof(f28,plain,(
% 15.31/2.49    ! [X8,X7,X1,X0] : (? [X10] : (r2_hidden(k4_tarski(X10,X8),X1) & r2_hidden(k4_tarski(X7,X10),X0)) => (r2_hidden(k4_tarski(sK7(X0,X1,X7,X8),X8),X1) & r2_hidden(k4_tarski(X7,sK7(X0,X1,X7,X8)),X0)))),
% 15.31/2.49    introduced(choice_axiom,[])).
% 15.31/2.49  
% 15.31/2.49  fof(f27,plain,(
% 15.31/2.49    ( ! [X4,X3] : (! [X2,X1,X0] : (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) => (r2_hidden(k4_tarski(sK6(X0,X1,X2),X4),X1) & r2_hidden(k4_tarski(X3,sK6(X0,X1,X2)),X0)))) )),
% 15.31/2.49    introduced(choice_axiom,[])).
% 15.31/2.49  
% 15.31/2.49  fof(f26,plain,(
% 15.31/2.49    ! [X2,X1,X0] : (? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) | r2_hidden(k4_tarski(X3,X4),X2))) => ((! [X5] : (~r2_hidden(k4_tarski(X5,sK5(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK4(X0,X1,X2),X5),X0)) | ~r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,sK5(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK4(X0,X1,X2),X6),X0)) | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2))))),
% 15.31/2.49    introduced(choice_axiom,[])).
% 15.31/2.49  
% 15.31/2.49  fof(f29,plain,(
% 15.31/2.49    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ((! [X5] : (~r2_hidden(k4_tarski(X5,sK5(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK4(X0,X1,X2),X5),X0)) | ~r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK6(X0,X1,X2),sK5(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK4(X0,X1,X2),sK6(X0,X1,X2)),X0)) | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0))) & ((r2_hidden(k4_tarski(sK7(X0,X1,X7,X8),X8),X1) & r2_hidden(k4_tarski(X7,sK7(X0,X1,X7,X8)),X0)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 15.31/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f25,f28,f27,f26])).
% 15.31/2.49  
% 15.31/2.49  fof(f46,plain,(
% 15.31/2.49    ( ! [X2,X0,X8,X7,X1] : (r2_hidden(k4_tarski(sK7(X0,X1,X7,X8),X8),X1) | ~r2_hidden(k4_tarski(X7,X8),X2) | k5_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 15.31/2.49    inference(cnf_transformation,[],[f29])).
% 15.31/2.49  
% 15.31/2.49  fof(f67,plain,(
% 15.31/2.49    ( ! [X0,X8,X7,X1] : (r2_hidden(k4_tarski(sK7(X0,X1,X7,X8),X8),X1) | ~r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 15.31/2.49    inference(equality_resolution,[],[f46])).
% 15.31/2.49  
% 15.31/2.49  fof(f4,axiom,(
% 15.31/2.49    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 15.31/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.31/2.49  
% 15.31/2.49  fof(f18,plain,(
% 15.31/2.49    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 15.31/2.49    inference(nnf_transformation,[],[f4])).
% 15.31/2.49  
% 15.31/2.49  fof(f19,plain,(
% 15.31/2.49    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 15.31/2.49    inference(rectify,[],[f18])).
% 15.31/2.49  
% 15.31/2.49  fof(f22,plain,(
% 15.31/2.49    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK3(X0,X5),X5),X0))),
% 15.31/2.49    introduced(choice_axiom,[])).
% 15.31/2.49  
% 15.31/2.49  fof(f21,plain,(
% 15.31/2.49    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) => r2_hidden(k4_tarski(sK2(X0,X1),X2),X0))) )),
% 15.31/2.49    introduced(choice_axiom,[])).
% 15.31/2.49  
% 15.31/2.49  fof(f20,plain,(
% 15.31/2.49    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK1(X0,X1)),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK1(X0,X1)),X0) | r2_hidden(sK1(X0,X1),X1))))),
% 15.31/2.49    introduced(choice_axiom,[])).
% 15.31/2.49  
% 15.31/2.49  fof(f23,plain,(
% 15.31/2.49    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK1(X0,X1)),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK3(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 15.31/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f19,f22,f21,f20])).
% 15.31/2.49  
% 15.31/2.49  fof(f42,plain,(
% 15.31/2.49    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X6,X5),X0) | k2_relat_1(X0) != X1) )),
% 15.31/2.49    inference(cnf_transformation,[],[f23])).
% 15.31/2.49  
% 15.31/2.49  fof(f64,plain,(
% 15.31/2.49    ( ! [X6,X0,X5] : (r2_hidden(X5,k2_relat_1(X0)) | ~r2_hidden(k4_tarski(X6,X5),X0)) )),
% 15.31/2.49    inference(equality_resolution,[],[f42])).
% 15.31/2.49  
% 15.31/2.49  fof(f41,plain,(
% 15.31/2.49    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK3(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 15.31/2.49    inference(cnf_transformation,[],[f23])).
% 15.31/2.49  
% 15.31/2.49  fof(f65,plain,(
% 15.31/2.49    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK3(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 15.31/2.49    inference(equality_resolution,[],[f41])).
% 15.31/2.49  
% 15.31/2.49  fof(f52,plain,(
% 15.31/2.49    v1_relat_1(sK8)),
% 15.31/2.49    inference(cnf_transformation,[],[f32])).
% 15.31/2.49  
% 15.31/2.49  fof(f53,plain,(
% 15.31/2.49    v1_relat_1(sK9)),
% 15.31/2.49    inference(cnf_transformation,[],[f32])).
% 15.31/2.49  
% 15.31/2.49  fof(f38,plain,(
% 15.31/2.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 15.31/2.49    inference(cnf_transformation,[],[f17])).
% 15.31/2.49  
% 15.31/2.49  fof(f55,plain,(
% 15.31/2.49    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 15.31/2.49    inference(definition_unfolding,[],[f38,f40])).
% 15.31/2.49  
% 15.31/2.49  cnf(c_1,plain,
% 15.31/2.49      ( r2_hidden(sK0(X0,X1,X2),X1)
% 15.31/2.49      | r2_hidden(sK0(X0,X1,X2),X2)
% 15.31/2.49      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
% 15.31/2.49      inference(cnf_transformation,[],[f56]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_3462,plain,
% 15.31/2.49      ( r2_hidden(sK0(X0,X1,X1),X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X1 ),
% 15.31/2.49      inference(factoring,[status(thm)],[c_1]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_371,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_370,plain,( X0 = X0 ),theory(equality) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_2144,plain,
% 15.31/2.49      ( X0 != X1 | X1 = X0 ),
% 15.31/2.49      inference(resolution,[status(thm)],[c_371,c_370]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_7457,plain,
% 15.31/2.49      ( r2_hidden(sK0(X0,X1,X1),X1) | X1 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 15.31/2.49      inference(resolution,[status(thm)],[c_3462,c_2144]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_6,plain,
% 15.31/2.49      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 15.31/2.49      inference(cnf_transformation,[],[f39]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_18,negated_conjecture,
% 15.31/2.49      ( ~ r1_tarski(k2_relat_1(k5_relat_1(sK8,sK9)),k2_relat_1(sK9)) ),
% 15.31/2.49      inference(cnf_transformation,[],[f54]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_235,plain,
% 15.31/2.49      ( k2_relat_1(k5_relat_1(sK8,sK9)) != k4_xboole_0(X0,X1)
% 15.31/2.49      | k2_relat_1(sK9) != X0 ),
% 15.31/2.49      inference(resolution_lifted,[status(thm)],[c_6,c_18]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_236,plain,
% 15.31/2.49      ( k2_relat_1(k5_relat_1(sK8,sK9)) != k4_xboole_0(k2_relat_1(sK9),X0) ),
% 15.31/2.49      inference(unflattening,[status(thm)],[c_235]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_35636,plain,
% 15.31/2.49      ( r2_hidden(sK0(k2_relat_1(sK9),k2_relat_1(k5_relat_1(sK8,sK9)),k2_relat_1(k5_relat_1(sK8,sK9))),k2_relat_1(k5_relat_1(sK8,sK9))) ),
% 15.31/2.49      inference(resolution,[status(thm)],[c_7457,c_236]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_17,plain,
% 15.31/2.49      ( ~ v1_relat_1(X0) | ~ v1_relat_1(X1) | v1_relat_1(k5_relat_1(X1,X0)) ),
% 15.31/2.49      inference(cnf_transformation,[],[f51]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_15,plain,
% 15.31/2.49      ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
% 15.31/2.49      | r2_hidden(k4_tarski(sK7(X2,X3,X0,X1),X1),X3)
% 15.31/2.49      | ~ v1_relat_1(X3)
% 15.31/2.49      | ~ v1_relat_1(X2)
% 15.31/2.49      | ~ v1_relat_1(k5_relat_1(X2,X3)) ),
% 15.31/2.49      inference(cnf_transformation,[],[f67]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_791,plain,
% 15.31/2.49      ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
% 15.31/2.49      | r2_hidden(k4_tarski(sK7(X2,X3,X0,X1),X1),X3)
% 15.31/2.49      | ~ v1_relat_1(X2)
% 15.31/2.49      | ~ v1_relat_1(X3) ),
% 15.31/2.49      inference(backward_subsumption_resolution,[status(thm)],[c_17,c_15]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_9,plain,
% 15.31/2.49      ( r2_hidden(X0,k2_relat_1(X1)) | ~ r2_hidden(k4_tarski(X2,X0),X1) ),
% 15.31/2.49      inference(cnf_transformation,[],[f64]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_9672,plain,
% 15.31/2.49      ( r2_hidden(X0,k2_relat_1(X1))
% 15.31/2.49      | ~ r2_hidden(k4_tarski(X2,X0),k5_relat_1(X3,X1))
% 15.31/2.49      | ~ v1_relat_1(X1)
% 15.31/2.49      | ~ v1_relat_1(X3) ),
% 15.31/2.49      inference(resolution,[status(thm)],[c_791,c_9]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_10,plain,
% 15.31/2.49      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 15.31/2.49      | r2_hidden(k4_tarski(sK3(X1,X0),X0),X1) ),
% 15.31/2.49      inference(cnf_transformation,[],[f65]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_10472,plain,
% 15.31/2.49      ( r2_hidden(X0,k2_relat_1(X1))
% 15.31/2.49      | ~ r2_hidden(X0,k2_relat_1(k5_relat_1(X2,X1)))
% 15.31/2.49      | ~ v1_relat_1(X2)
% 15.31/2.49      | ~ v1_relat_1(X1) ),
% 15.31/2.49      inference(resolution,[status(thm)],[c_9672,c_10]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_35827,plain,
% 15.31/2.49      ( r2_hidden(sK0(k2_relat_1(sK9),k2_relat_1(k5_relat_1(sK8,sK9)),k2_relat_1(k5_relat_1(sK8,sK9))),k2_relat_1(sK9))
% 15.31/2.49      | ~ v1_relat_1(sK9)
% 15.31/2.49      | ~ v1_relat_1(sK8) ),
% 15.31/2.49      inference(resolution,[status(thm)],[c_35636,c_10472]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_20,negated_conjecture,
% 15.31/2.49      ( v1_relat_1(sK8) ),
% 15.31/2.49      inference(cnf_transformation,[],[f52]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_19,negated_conjecture,
% 15.31/2.49      ( v1_relat_1(sK9) ),
% 15.31/2.49      inference(cnf_transformation,[],[f53]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_36069,plain,
% 15.31/2.49      ( r2_hidden(sK0(k2_relat_1(sK9),k2_relat_1(k5_relat_1(sK8,sK9)),k2_relat_1(k5_relat_1(sK8,sK9))),k2_relat_1(sK9)) ),
% 15.31/2.49      inference(global_propositional_subsumption,
% 15.31/2.49                [status(thm)],
% 15.31/2.49                [c_35827,c_20,c_19]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_0,plain,
% 15.31/2.49      ( ~ r2_hidden(sK0(X0,X1,X2),X1)
% 15.31/2.49      | ~ r2_hidden(sK0(X0,X1,X2),X0)
% 15.31/2.49      | ~ r2_hidden(sK0(X0,X1,X2),X2)
% 15.31/2.49      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
% 15.31/2.49      inference(cnf_transformation,[],[f55]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_35825,plain,
% 15.31/2.49      ( ~ r2_hidden(sK0(k2_relat_1(sK9),k2_relat_1(k5_relat_1(sK8,sK9)),k2_relat_1(k5_relat_1(sK8,sK9))),k2_relat_1(k5_relat_1(sK8,sK9)))
% 15.31/2.49      | ~ r2_hidden(sK0(k2_relat_1(sK9),k2_relat_1(k5_relat_1(sK8,sK9)),k2_relat_1(k5_relat_1(sK8,sK9))),k2_relat_1(sK9))
% 15.31/2.49      | k4_xboole_0(k2_relat_1(sK9),k4_xboole_0(k2_relat_1(sK9),k2_relat_1(k5_relat_1(sK8,sK9)))) = k2_relat_1(k5_relat_1(sK8,sK9)) ),
% 15.31/2.49      inference(resolution,[status(thm)],[c_35636,c_0]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_36080,plain,
% 15.31/2.49      ( ~ r2_hidden(sK0(k2_relat_1(sK9),k2_relat_1(k5_relat_1(sK8,sK9)),k2_relat_1(k5_relat_1(sK8,sK9))),k2_relat_1(k5_relat_1(sK8,sK9)))
% 15.31/2.49      | k4_xboole_0(k2_relat_1(sK9),k4_xboole_0(k2_relat_1(sK9),k2_relat_1(k5_relat_1(sK8,sK9)))) = k2_relat_1(k5_relat_1(sK8,sK9)) ),
% 15.31/2.49      inference(backward_subsumption_resolution,
% 15.31/2.49                [status(thm)],
% 15.31/2.49                [c_36069,c_35825]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_36084,plain,
% 15.31/2.49      ( k4_xboole_0(k2_relat_1(sK9),k4_xboole_0(k2_relat_1(sK9),k2_relat_1(k5_relat_1(sK8,sK9)))) = k2_relat_1(k5_relat_1(sK8,sK9)) ),
% 15.31/2.49      inference(global_propositional_subsumption,
% 15.31/2.49                [status(thm)],
% 15.31/2.49                [c_36080,c_20,c_19,c_35636,c_35825,c_35827]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_36453,plain,
% 15.31/2.49      ( k2_relat_1(k5_relat_1(sK8,sK9)) = k4_xboole_0(k2_relat_1(sK9),k4_xboole_0(k2_relat_1(sK9),k2_relat_1(k5_relat_1(sK8,sK9)))) ),
% 15.31/2.49      inference(resolution,[status(thm)],[c_36084,c_2144]) ).
% 15.31/2.49  
% 15.31/2.49  cnf(c_36563,plain,
% 15.31/2.49      ( $false ),
% 15.31/2.49      inference(forward_subsumption_resolution,[status(thm)],[c_36453,c_236]) ).
% 15.31/2.49  
% 15.31/2.49  
% 15.31/2.49  % SZS output end CNFRefutation for theBenchmark.p
% 15.31/2.49  
% 15.31/2.49  ------                               Statistics
% 15.31/2.49  
% 15.31/2.49  ------ Selected
% 15.31/2.49  
% 15.31/2.49  total_time:                             1.566
% 15.31/2.49  
%------------------------------------------------------------------------------
