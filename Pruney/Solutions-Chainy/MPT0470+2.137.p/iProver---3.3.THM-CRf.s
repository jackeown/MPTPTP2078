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
% DateTime   : Thu Dec  3 11:44:19 EST 2020

% Result     : Theorem 3.36s
% Output     : CNFRefutation 3.36s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 413 expanded)
%              Number of clauses        :   77 ( 154 expanded)
%              Number of leaves         :   21 (  99 expanded)
%              Depth                    :   20
%              Number of atoms          :  459 (1594 expanded)
%              Number of equality atoms :  168 ( 470 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   17 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
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

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f23,plain,(
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

fof(f24,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f38,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f61,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f38])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f59,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f43,f45])).

fof(f37,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f62,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f37])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ! [X3] :
                  ~ ( r2_hidden(X3,X2)
                    & r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f25,plain,(
    ! [X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
     => ( ! [X3] :
            ( ~ r2_hidden(X3,sK1(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK1(X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,sK1(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK1(X1),X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f12,f25])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X1),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f10,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f19,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f35,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK8,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK8) )
      & v1_relat_1(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK8,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK8) )
    & v1_relat_1(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f19,f35])).

fof(f57,plain,(
    v1_relat_1(sK8) ),
    inference(cnf_transformation,[],[f36])).

fof(f58,plain,
    ( k1_xboole_0 != k5_relat_1(sK8,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK8) ),
    inference(cnf_transformation,[],[f36])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f15,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k4_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k4_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ! [X1,X2] : ~ r2_hidden(k4_tarski(X1,X2),X0)
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
     => r2_hidden(k4_tarski(sK6(X0),sK7(X0)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(k4_tarski(sK6(X0),sK7(X0)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f18,f33])).

fof(f56,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(k4_tarski(sK6(X0),sK7(X0)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f6,axiom,(
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

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f31,plain,(
    ! [X8,X7,X1,X0] :
      ( ? [X10] :
          ( r2_hidden(k4_tarski(X10,X8),X1)
          & r2_hidden(k4_tarski(X7,X10),X0) )
     => ( r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1)
        & r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k4_tarski(X6,X4),X1)
          & r2_hidden(k4_tarski(X3,X6),X0) )
     => ( r2_hidden(k4_tarski(sK4(X0,X1,X2),X4),X1)
        & r2_hidden(k4_tarski(X3,sK4(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
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
              ( ~ r2_hidden(k4_tarski(X5,sK3(X0,X1,X2)),X1)
              | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),X5),X0) )
          | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) )
        & ( ? [X6] :
              ( r2_hidden(k4_tarski(X6,sK3(X0,X1,X2)),X1)
              & r2_hidden(k4_tarski(sK2(X0,X1,X2),X6),X0) )
          | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ( ( ! [X5] :
                          ( ~ r2_hidden(k4_tarski(X5,sK3(X0,X1,X2)),X1)
                          | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),X5),X0) )
                      | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) )
                    & ( ( r2_hidden(k4_tarski(sK4(X0,X1,X2),sK3(X0,X1,X2)),X1)
                        & r2_hidden(k4_tarski(sK2(X0,X1,X2),sK4(X0,X1,X2)),X0) )
                      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) ) ) )
                & ( ! [X7,X8] :
                      ( ( r2_hidden(k4_tarski(X7,X8),X2)
                        | ! [X9] :
                            ( ~ r2_hidden(k4_tarski(X9,X8),X1)
                            | ~ r2_hidden(k4_tarski(X7,X9),X0) ) )
                      & ( ( r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1)
                          & r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0) )
                        | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f28,f31,f30,f29])).

fof(f49,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f64,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f49])).

fof(f48,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f65,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f48])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_541,plain,
    ( k4_xboole_0(X0,X1) = X2
    | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_7,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_539,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1052,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_539])).

cnf(c_6,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_548,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_6,c_7])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_538,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_983,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_548,c_538])).

cnf(c_1069,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1052,c_983])).

cnf(c_1993,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r2_hidden(sK0(X0,X1,k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_541,c_1069])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK1(X1),X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_536,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(sK1(X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4990,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1993,c_536])).

cnf(c_5204,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k1_xboole_0
    | r2_hidden(sK1(k4_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4990,c_538])).

cnf(c_8684,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k1_xboole_0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5204,c_536])).

cnf(c_20,negated_conjecture,
    ( v1_relat_1(sK8) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_21,plain,
    ( v1_relat_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_19,negated_conjecture,
    ( k1_xboole_0 != k5_relat_1(sK8,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK8) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_206,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_219,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_206])).

cnf(c_16,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_744,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k5_relat_1(sK8,X0))
    | ~ v1_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_745,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k5_relat_1(sK8,X0)) = iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_744])).

cnf(c_747,plain,
    ( v1_relat_1(k5_relat_1(sK8,k1_xboole_0)) = iProver_top
    | v1_relat_1(sK8) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_745])).

cnf(c_207,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_757,plain,
    ( k5_relat_1(k1_xboole_0,sK8) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k5_relat_1(k1_xboole_0,sK8) ),
    inference(instantiation,[status(thm)],[c_207])).

cnf(c_758,plain,
    ( k5_relat_1(k1_xboole_0,sK8) != k1_xboole_0
    | k1_xboole_0 = k5_relat_1(k1_xboole_0,sK8)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_757])).

cnf(c_526,plain,
    ( v1_relat_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_17,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_528,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_822,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_548,c_528])).

cnf(c_832,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_526,c_822])).

cnf(c_18,plain,
    ( r2_hidden(k4_tarski(sK6(X0),sK7(X0)),X0)
    | ~ v1_relat_1(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1043,plain,
    ( r2_hidden(k4_tarski(sK6(k5_relat_1(sK8,k1_xboole_0)),sK7(k5_relat_1(sK8,k1_xboole_0))),k5_relat_1(sK8,k1_xboole_0))
    | ~ v1_relat_1(k5_relat_1(sK8,k1_xboole_0))
    | k1_xboole_0 = k5_relat_1(sK8,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1044,plain,
    ( k1_xboole_0 = k5_relat_1(sK8,k1_xboole_0)
    | r2_hidden(k4_tarski(sK6(k5_relat_1(sK8,k1_xboole_0)),sK7(k5_relat_1(sK8,k1_xboole_0))),k5_relat_1(sK8,k1_xboole_0)) = iProver_top
    | v1_relat_1(k5_relat_1(sK8,k1_xboole_0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1043])).

cnf(c_14,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
    | r2_hidden(k4_tarski(sK5(X2,X3,X0,X1),X1),X3)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(k5_relat_1(X2,X3)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1171,plain,
    ( r2_hidden(k4_tarski(sK5(sK8,k1_xboole_0,sK6(k5_relat_1(sK8,k1_xboole_0)),sK7(k5_relat_1(sK8,k1_xboole_0))),sK7(k5_relat_1(sK8,k1_xboole_0))),k1_xboole_0)
    | ~ r2_hidden(k4_tarski(sK6(k5_relat_1(sK8,k1_xboole_0)),sK7(k5_relat_1(sK8,k1_xboole_0))),k5_relat_1(sK8,k1_xboole_0))
    | ~ v1_relat_1(k5_relat_1(sK8,k1_xboole_0))
    | ~ v1_relat_1(sK8)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1172,plain,
    ( r2_hidden(k4_tarski(sK5(sK8,k1_xboole_0,sK6(k5_relat_1(sK8,k1_xboole_0)),sK7(k5_relat_1(sK8,k1_xboole_0))),sK7(k5_relat_1(sK8,k1_xboole_0))),k1_xboole_0) = iProver_top
    | r2_hidden(k4_tarski(sK6(k5_relat_1(sK8,k1_xboole_0)),sK7(k5_relat_1(sK8,k1_xboole_0))),k5_relat_1(sK8,k1_xboole_0)) != iProver_top
    | v1_relat_1(k5_relat_1(sK8,k1_xboole_0)) != iProver_top
    | v1_relat_1(sK8) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1171])).

cnf(c_529,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k5_relat_1(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_527,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(k4_tarski(sK6(X0),sK7(X0)),X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_15,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
    | r2_hidden(k4_tarski(X0,sK5(X2,X3,X0,X1)),X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(k5_relat_1(X2,X3)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_530,plain,
    ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK5(X2,X3,X0,X1)),X2) = iProver_top
    | v1_relat_1(X3) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(k5_relat_1(X2,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_620,plain,
    ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK5(X2,X3,X0,X1)),X2) = iProver_top
    | v1_relat_1(X3) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_530,c_529])).

cnf(c_1371,plain,
    ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k1_xboole_0,X2)) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_620,c_1069])).

cnf(c_1426,plain,
    ( v1_relat_1(X2) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),k5_relat_1(k1_xboole_0,X2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1371,c_832])).

cnf(c_1427,plain,
    ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k1_xboole_0,X2)) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_1426])).

cnf(c_1433,plain,
    ( k5_relat_1(k1_xboole_0,X0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k5_relat_1(k1_xboole_0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_527,c_1427])).

cnf(c_1574,plain,
    ( k5_relat_1(k1_xboole_0,X0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_529,c_1433])).

cnf(c_2398,plain,
    ( v1_relat_1(X0) != iProver_top
    | k5_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1574,c_832])).

cnf(c_2399,plain,
    ( k5_relat_1(k1_xboole_0,X0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2398])).

cnf(c_2406,plain,
    ( k5_relat_1(k1_xboole_0,sK8) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_526,c_2399])).

cnf(c_2273,plain,
    ( r2_hidden(sK0(X0,X1,X0),X0)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(factoring,[status(thm)],[c_2])).

cnf(c_4312,plain,
    ( r2_hidden(sK1(X0),X0)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_2273,c_9])).

cnf(c_923,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_207,c_206])).

cnf(c_4519,plain,
    ( r2_hidden(sK1(X0),X0)
    | X0 = k4_xboole_0(X0,X1) ),
    inference(resolution,[status(thm)],[c_4312,c_923])).

cnf(c_212,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_4553,plain,
    ( r2_hidden(sK1(X0),X0)
    | v1_relat_1(X0)
    | ~ v1_relat_1(k4_xboole_0(X0,X1)) ),
    inference(resolution,[status(thm)],[c_4519,c_212])).

cnf(c_801,plain,
    ( v1_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)))
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_212,c_6])).

cnf(c_837,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_832])).

cnf(c_840,plain,
    ( v1_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_801,c_837])).

cnf(c_4566,plain,
    ( r2_hidden(sK1(X0),X0)
    | v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_4553,c_840])).

cnf(c_1002,plain,
    ( r2_hidden(sK1(X0),X0)
    | ~ v1_relat_1(X0)
    | k1_xboole_0 = X0 ),
    inference(resolution,[status(thm)],[c_9,c_18])).

cnf(c_1464,plain,
    ( r2_hidden(sK1(X0),X0)
    | ~ v1_relat_1(X0)
    | X0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1002,c_923])).

cnf(c_4763,plain,
    ( r2_hidden(sK1(X0),X0)
    | X0 = k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_4566,c_1464])).

cnf(c_4784,plain,
    ( X0 = k1_xboole_0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4763])).

cnf(c_8018,plain,
    ( ~ r2_hidden(k4_tarski(sK5(sK8,k1_xboole_0,sK6(k5_relat_1(sK8,k1_xboole_0)),sK7(k5_relat_1(sK8,k1_xboole_0))),sK7(k5_relat_1(sK8,k1_xboole_0))),X0)
    | r2_hidden(sK1(X0),X0) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_8022,plain,
    ( r2_hidden(k4_tarski(sK5(sK8,k1_xboole_0,sK6(k5_relat_1(sK8,k1_xboole_0)),sK7(k5_relat_1(sK8,k1_xboole_0))),sK7(k5_relat_1(sK8,k1_xboole_0))),X0) != iProver_top
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8018])).

cnf(c_209,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3617,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(sK5(sK8,k1_xboole_0,sK6(k5_relat_1(sK8,k1_xboole_0)),sK7(k5_relat_1(sK8,k1_xboole_0))),sK7(k5_relat_1(sK8,k1_xboole_0))),k1_xboole_0)
    | X0 != k4_tarski(sK5(sK8,k1_xboole_0,sK6(k5_relat_1(sK8,k1_xboole_0)),sK7(k5_relat_1(sK8,k1_xboole_0))),sK7(k5_relat_1(sK8,k1_xboole_0)))
    | X1 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_209])).

cnf(c_8375,plain,
    ( r2_hidden(k4_tarski(sK5(sK8,k1_xboole_0,sK6(k5_relat_1(sK8,k1_xboole_0)),sK7(k5_relat_1(sK8,k1_xboole_0))),sK7(k5_relat_1(sK8,k1_xboole_0))),X0)
    | ~ r2_hidden(k4_tarski(sK5(sK8,k1_xboole_0,sK6(k5_relat_1(sK8,k1_xboole_0)),sK7(k5_relat_1(sK8,k1_xboole_0))),sK7(k5_relat_1(sK8,k1_xboole_0))),k1_xboole_0)
    | X0 != k1_xboole_0
    | k4_tarski(sK5(sK8,k1_xboole_0,sK6(k5_relat_1(sK8,k1_xboole_0)),sK7(k5_relat_1(sK8,k1_xboole_0))),sK7(k5_relat_1(sK8,k1_xboole_0))) != k4_tarski(sK5(sK8,k1_xboole_0,sK6(k5_relat_1(sK8,k1_xboole_0)),sK7(k5_relat_1(sK8,k1_xboole_0))),sK7(k5_relat_1(sK8,k1_xboole_0))) ),
    inference(instantiation,[status(thm)],[c_3617])).

cnf(c_8377,plain,
    ( X0 != k1_xboole_0
    | k4_tarski(sK5(sK8,k1_xboole_0,sK6(k5_relat_1(sK8,k1_xboole_0)),sK7(k5_relat_1(sK8,k1_xboole_0))),sK7(k5_relat_1(sK8,k1_xboole_0))) != k4_tarski(sK5(sK8,k1_xboole_0,sK6(k5_relat_1(sK8,k1_xboole_0)),sK7(k5_relat_1(sK8,k1_xboole_0))),sK7(k5_relat_1(sK8,k1_xboole_0)))
    | r2_hidden(k4_tarski(sK5(sK8,k1_xboole_0,sK6(k5_relat_1(sK8,k1_xboole_0)),sK7(k5_relat_1(sK8,k1_xboole_0))),sK7(k5_relat_1(sK8,k1_xboole_0))),X0) = iProver_top
    | r2_hidden(k4_tarski(sK5(sK8,k1_xboole_0,sK6(k5_relat_1(sK8,k1_xboole_0)),sK7(k5_relat_1(sK8,k1_xboole_0))),sK7(k5_relat_1(sK8,k1_xboole_0))),k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8375])).

cnf(c_8376,plain,
    ( k4_tarski(sK5(sK8,k1_xboole_0,sK6(k5_relat_1(sK8,k1_xboole_0)),sK7(k5_relat_1(sK8,k1_xboole_0))),sK7(k5_relat_1(sK8,k1_xboole_0))) = k4_tarski(sK5(sK8,k1_xboole_0,sK6(k5_relat_1(sK8,k1_xboole_0)),sK7(k5_relat_1(sK8,k1_xboole_0))),sK7(k5_relat_1(sK8,k1_xboole_0))) ),
    inference(instantiation,[status(thm)],[c_206])).

cnf(c_8718,plain,
    ( r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8684,c_21,c_19,c_219,c_747,c_758,c_832,c_1044,c_1172,c_2406,c_4784,c_8022,c_8377,c_8376])).

cnf(c_8729,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_8718,c_1069])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n002.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:17:06 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.36/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.36/0.99  
% 3.36/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.36/0.99  
% 3.36/0.99  ------  iProver source info
% 3.36/0.99  
% 3.36/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.36/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.36/0.99  git: non_committed_changes: false
% 3.36/0.99  git: last_make_outside_of_git: false
% 3.36/0.99  
% 3.36/0.99  ------ 
% 3.36/0.99  ------ Parsing...
% 3.36/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.36/0.99  
% 3.36/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.36/0.99  
% 3.36/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.36/0.99  
% 3.36/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.36/0.99  ------ Proving...
% 3.36/0.99  ------ Problem Properties 
% 3.36/0.99  
% 3.36/0.99  
% 3.36/0.99  clauses                                 21
% 3.36/0.99  conjectures                             2
% 3.36/0.99  EPR                                     1
% 3.36/0.99  Horn                                    14
% 3.36/0.99  unary                                   3
% 3.36/0.99  binary                                  5
% 3.36/0.99  lits                                    70
% 3.36/0.99  lits eq                                 11
% 3.36/0.99  fd_pure                                 0
% 3.36/0.99  fd_pseudo                               0
% 3.36/0.99  fd_cond                                 1
% 3.36/0.99  fd_pseudo_cond                          6
% 3.36/0.99  AC symbols                              0
% 3.36/0.99  
% 3.36/0.99  ------ Input Options Time Limit: Unbounded
% 3.36/0.99  
% 3.36/0.99  
% 3.36/0.99  ------ 
% 3.36/0.99  Current options:
% 3.36/0.99  ------ 
% 3.36/0.99  
% 3.36/0.99  
% 3.36/0.99  
% 3.36/0.99  
% 3.36/0.99  ------ Proving...
% 3.36/0.99  
% 3.36/0.99  
% 3.36/0.99  % SZS status Theorem for theBenchmark.p
% 3.36/0.99  
% 3.36/0.99   Resolution empty clause
% 3.36/0.99  
% 3.36/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.36/0.99  
% 3.36/0.99  fof(f1,axiom,(
% 3.36/0.99    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.36/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/0.99  
% 3.36/0.99  fof(f20,plain,(
% 3.36/0.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.36/0.99    inference(nnf_transformation,[],[f1])).
% 3.36/0.99  
% 3.36/0.99  fof(f21,plain,(
% 3.36/0.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.36/0.99    inference(flattening,[],[f20])).
% 3.36/0.99  
% 3.36/0.99  fof(f22,plain,(
% 3.36/0.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.36/0.99    inference(rectify,[],[f21])).
% 3.36/0.99  
% 3.36/0.99  fof(f23,plain,(
% 3.36/0.99    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.36/0.99    introduced(choice_axiom,[])).
% 3.36/0.99  
% 3.36/0.99  fof(f24,plain,(
% 3.36/0.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.36/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).
% 3.36/0.99  
% 3.36/0.99  fof(f40,plain,(
% 3.36/0.99    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.36/0.99    inference(cnf_transformation,[],[f24])).
% 3.36/0.99  
% 3.36/0.99  fof(f3,axiom,(
% 3.36/0.99    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.36/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/0.99  
% 3.36/0.99  fof(f44,plain,(
% 3.36/0.99    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.36/0.99    inference(cnf_transformation,[],[f3])).
% 3.36/0.99  
% 3.36/0.99  fof(f38,plain,(
% 3.36/0.99    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.36/0.99    inference(cnf_transformation,[],[f24])).
% 3.36/0.99  
% 3.36/0.99  fof(f61,plain,(
% 3.36/0.99    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 3.36/0.99    inference(equality_resolution,[],[f38])).
% 3.36/0.99  
% 3.36/0.99  fof(f2,axiom,(
% 3.36/0.99    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 3.36/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/0.99  
% 3.36/0.99  fof(f43,plain,(
% 3.36/0.99    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 3.36/0.99    inference(cnf_transformation,[],[f2])).
% 3.36/0.99  
% 3.36/0.99  fof(f4,axiom,(
% 3.36/0.99    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 3.36/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/0.99  
% 3.36/0.99  fof(f45,plain,(
% 3.36/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 3.36/0.99    inference(cnf_transformation,[],[f4])).
% 3.36/0.99  
% 3.36/0.99  fof(f59,plain,(
% 3.36/0.99    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0) )),
% 3.36/0.99    inference(definition_unfolding,[],[f43,f45])).
% 3.36/0.99  
% 3.36/0.99  fof(f37,plain,(
% 3.36/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.36/0.99    inference(cnf_transformation,[],[f24])).
% 3.36/0.99  
% 3.36/0.99  fof(f62,plain,(
% 3.36/0.99    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 3.36/0.99    inference(equality_resolution,[],[f37])).
% 3.36/0.99  
% 3.36/0.99  fof(f5,axiom,(
% 3.36/0.99    ! [X0,X1] : ~(! [X2] : ~(! [X3] : ~(r2_hidden(X3,X2) & r2_hidden(X3,X1)) & r2_hidden(X2,X1)) & r2_hidden(X0,X1))),
% 3.36/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/0.99  
% 3.36/0.99  fof(f12,plain,(
% 3.36/0.99    ! [X0,X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) | ~r2_hidden(X0,X1))),
% 3.36/0.99    inference(ennf_transformation,[],[f5])).
% 3.36/0.99  
% 3.36/0.99  fof(f25,plain,(
% 3.36/0.99    ! [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) => (! [X3] : (~r2_hidden(X3,sK1(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK1(X1),X1)))),
% 3.36/0.99    introduced(choice_axiom,[])).
% 3.36/0.99  
% 3.36/0.99  fof(f26,plain,(
% 3.36/0.99    ! [X0,X1] : ((! [X3] : (~r2_hidden(X3,sK1(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK1(X1),X1)) | ~r2_hidden(X0,X1))),
% 3.36/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f12,f25])).
% 3.36/0.99  
% 3.36/0.99  fof(f46,plain,(
% 3.36/0.99    ( ! [X0,X1] : (r2_hidden(sK1(X1),X1) | ~r2_hidden(X0,X1)) )),
% 3.36/0.99    inference(cnf_transformation,[],[f26])).
% 3.36/0.99  
% 3.36/0.99  fof(f10,conjecture,(
% 3.36/0.99    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 3.36/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/0.99  
% 3.36/0.99  fof(f11,negated_conjecture,(
% 3.36/0.99    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 3.36/0.99    inference(negated_conjecture,[],[f10])).
% 3.36/0.99  
% 3.36/0.99  fof(f19,plain,(
% 3.36/0.99    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 3.36/0.99    inference(ennf_transformation,[],[f11])).
% 3.36/0.99  
% 3.36/0.99  fof(f35,plain,(
% 3.36/0.99    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK8,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK8)) & v1_relat_1(sK8))),
% 3.36/0.99    introduced(choice_axiom,[])).
% 3.36/0.99  
% 3.36/0.99  fof(f36,plain,(
% 3.36/0.99    (k1_xboole_0 != k5_relat_1(sK8,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK8)) & v1_relat_1(sK8)),
% 3.36/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f19,f35])).
% 3.36/0.99  
% 3.36/0.99  fof(f57,plain,(
% 3.36/0.99    v1_relat_1(sK8)),
% 3.36/0.99    inference(cnf_transformation,[],[f36])).
% 3.36/0.99  
% 3.36/0.99  fof(f58,plain,(
% 3.36/0.99    k1_xboole_0 != k5_relat_1(sK8,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK8)),
% 3.36/0.99    inference(cnf_transformation,[],[f36])).
% 3.36/0.99  
% 3.36/0.99  fof(f7,axiom,(
% 3.36/0.99    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 3.36/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/0.99  
% 3.36/0.99  fof(f14,plain,(
% 3.36/0.99    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 3.36/0.99    inference(ennf_transformation,[],[f7])).
% 3.36/0.99  
% 3.36/0.99  fof(f15,plain,(
% 3.36/0.99    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 3.36/0.99    inference(flattening,[],[f14])).
% 3.36/0.99  
% 3.36/0.99  fof(f54,plain,(
% 3.36/0.99    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.36/0.99    inference(cnf_transformation,[],[f15])).
% 3.36/0.99  
% 3.36/0.99  fof(f8,axiom,(
% 3.36/0.99    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k4_xboole_0(X0,X1)))),
% 3.36/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/0.99  
% 3.36/0.99  fof(f16,plain,(
% 3.36/0.99    ! [X0,X1] : (v1_relat_1(k4_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 3.36/0.99    inference(ennf_transformation,[],[f8])).
% 3.36/0.99  
% 3.36/0.99  fof(f55,plain,(
% 3.36/0.99    ( ! [X0,X1] : (v1_relat_1(k4_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 3.36/0.99    inference(cnf_transformation,[],[f16])).
% 3.36/0.99  
% 3.36/0.99  fof(f9,axiom,(
% 3.36/0.99    ! [X0] : (v1_relat_1(X0) => (! [X1,X2] : ~r2_hidden(k4_tarski(X1,X2),X0) => k1_xboole_0 = X0))),
% 3.36/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/0.99  
% 3.36/0.99  fof(f17,plain,(
% 3.36/0.99    ! [X0] : ((k1_xboole_0 = X0 | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)) | ~v1_relat_1(X0))),
% 3.36/0.99    inference(ennf_transformation,[],[f9])).
% 3.36/0.99  
% 3.36/0.99  fof(f18,plain,(
% 3.36/0.99    ! [X0] : (k1_xboole_0 = X0 | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0) | ~v1_relat_1(X0))),
% 3.36/0.99    inference(flattening,[],[f17])).
% 3.36/0.99  
% 3.36/0.99  fof(f33,plain,(
% 3.36/0.99    ! [X0] : (? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0) => r2_hidden(k4_tarski(sK6(X0),sK7(X0)),X0))),
% 3.36/0.99    introduced(choice_axiom,[])).
% 3.36/0.99  
% 3.36/0.99  fof(f34,plain,(
% 3.36/0.99    ! [X0] : (k1_xboole_0 = X0 | r2_hidden(k4_tarski(sK6(X0),sK7(X0)),X0) | ~v1_relat_1(X0))),
% 3.36/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f18,f33])).
% 3.36/0.99  
% 3.36/0.99  fof(f56,plain,(
% 3.36/0.99    ( ! [X0] : (k1_xboole_0 = X0 | r2_hidden(k4_tarski(sK6(X0),sK7(X0)),X0) | ~v1_relat_1(X0)) )),
% 3.36/0.99    inference(cnf_transformation,[],[f34])).
% 3.36/0.99  
% 3.36/0.99  fof(f6,axiom,(
% 3.36/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))))))),
% 3.36/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/0.99  
% 3.36/0.99  fof(f13,plain,(
% 3.36/0.99    ! [X0] : (! [X1] : (! [X2] : ((k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.36/0.99    inference(ennf_transformation,[],[f6])).
% 3.36/0.99  
% 3.36/0.99  fof(f27,plain,(
% 3.36/0.99    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | ! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0))) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.36/0.99    inference(nnf_transformation,[],[f13])).
% 3.36/0.99  
% 3.36/0.99  fof(f28,plain,(
% 3.36/0.99    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0))) & (? [X10] : (r2_hidden(k4_tarski(X10,X8),X1) & r2_hidden(k4_tarski(X7,X10),X0)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.36/0.99    inference(rectify,[],[f27])).
% 3.36/0.99  
% 3.36/0.99  fof(f31,plain,(
% 3.36/0.99    ! [X8,X7,X1,X0] : (? [X10] : (r2_hidden(k4_tarski(X10,X8),X1) & r2_hidden(k4_tarski(X7,X10),X0)) => (r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1) & r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0)))),
% 3.36/0.99    introduced(choice_axiom,[])).
% 3.36/0.99  
% 3.36/0.99  fof(f30,plain,(
% 3.36/0.99    ( ! [X4,X3] : (! [X2,X1,X0] : (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) => (r2_hidden(k4_tarski(sK4(X0,X1,X2),X4),X1) & r2_hidden(k4_tarski(X3,sK4(X0,X1,X2)),X0)))) )),
% 3.36/0.99    introduced(choice_axiom,[])).
% 3.36/0.99  
% 3.36/0.99  fof(f29,plain,(
% 3.36/0.99    ! [X2,X1,X0] : (? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) | r2_hidden(k4_tarski(X3,X4),X2))) => ((! [X5] : (~r2_hidden(k4_tarski(X5,sK3(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),X5),X0)) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,sK3(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),X6),X0)) | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2))))),
% 3.36/0.99    introduced(choice_axiom,[])).
% 3.36/0.99  
% 3.36/0.99  fof(f32,plain,(
% 3.36/0.99    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ((! [X5] : (~r2_hidden(k4_tarski(X5,sK3(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),X5),X0)) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK4(X0,X1,X2),sK3(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),sK4(X0,X1,X2)),X0)) | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0))) & ((r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1) & r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.36/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f28,f31,f30,f29])).
% 3.36/0.99  
% 3.36/0.99  fof(f49,plain,(
% 3.36/0.99    ( ! [X2,X0,X8,X7,X1] : (r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1) | ~r2_hidden(k4_tarski(X7,X8),X2) | k5_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.36/0.99    inference(cnf_transformation,[],[f32])).
% 3.36/0.99  
% 3.36/0.99  fof(f64,plain,(
% 3.36/0.99    ( ! [X0,X8,X7,X1] : (r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1) | ~r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.36/0.99    inference(equality_resolution,[],[f49])).
% 3.36/0.99  
% 3.36/0.99  fof(f48,plain,(
% 3.36/0.99    ( ! [X2,X0,X8,X7,X1] : (r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0) | ~r2_hidden(k4_tarski(X7,X8),X2) | k5_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.36/0.99    inference(cnf_transformation,[],[f32])).
% 3.36/0.99  
% 3.36/0.99  fof(f65,plain,(
% 3.36/0.99    ( ! [X0,X8,X7,X1] : (r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0) | ~r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.36/0.99    inference(equality_resolution,[],[f48])).
% 3.36/0.99  
% 3.36/0.99  cnf(c_2,plain,
% 3.36/0.99      ( r2_hidden(sK0(X0,X1,X2),X0)
% 3.36/0.99      | r2_hidden(sK0(X0,X1,X2),X2)
% 3.36/0.99      | k4_xboole_0(X0,X1) = X2 ),
% 3.36/0.99      inference(cnf_transformation,[],[f40]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_541,plain,
% 3.36/0.99      ( k4_xboole_0(X0,X1) = X2
% 3.36/0.99      | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
% 3.36/0.99      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
% 3.36/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_7,plain,
% 3.36/0.99      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.36/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_4,plain,
% 3.36/0.99      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 3.36/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_539,plain,
% 3.36/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.36/0.99      | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
% 3.36/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_1052,plain,
% 3.36/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.36/0.99      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.36/0.99      inference(superposition,[status(thm)],[c_7,c_539]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_6,plain,
% 3.36/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 3.36/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_548,plain,
% 3.36/0.99      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.36/0.99      inference(light_normalisation,[status(thm)],[c_6,c_7]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_5,plain,
% 3.36/0.99      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
% 3.36/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_538,plain,
% 3.36/0.99      ( r2_hidden(X0,X1) = iProver_top
% 3.36/0.99      | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
% 3.36/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_983,plain,
% 3.36/0.99      ( r2_hidden(X0,X1) = iProver_top
% 3.36/0.99      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.36/0.99      inference(superposition,[status(thm)],[c_548,c_538]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_1069,plain,
% 3.36/0.99      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.36/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1052,c_983]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_1993,plain,
% 3.36/0.99      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 3.36/0.99      | r2_hidden(sK0(X0,X1,k1_xboole_0),X0) = iProver_top ),
% 3.36/0.99      inference(superposition,[status(thm)],[c_541,c_1069]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_9,plain,
% 3.36/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(sK1(X1),X1) ),
% 3.36/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_536,plain,
% 3.36/0.99      ( r2_hidden(X0,X1) != iProver_top | r2_hidden(sK1(X1),X1) = iProver_top ),
% 3.36/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_4990,plain,
% 3.36/0.99      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 3.36/0.99      | r2_hidden(sK1(X0),X0) = iProver_top ),
% 3.36/0.99      inference(superposition,[status(thm)],[c_1993,c_536]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_5204,plain,
% 3.36/0.99      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k1_xboole_0
% 3.36/0.99      | r2_hidden(sK1(k4_xboole_0(X0,X1)),X0) = iProver_top ),
% 3.36/0.99      inference(superposition,[status(thm)],[c_4990,c_538]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_8684,plain,
% 3.36/0.99      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k1_xboole_0
% 3.36/0.99      | r2_hidden(sK1(X0),X0) = iProver_top ),
% 3.36/0.99      inference(superposition,[status(thm)],[c_5204,c_536]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_20,negated_conjecture,
% 3.36/0.99      ( v1_relat_1(sK8) ),
% 3.36/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_21,plain,
% 3.36/0.99      ( v1_relat_1(sK8) = iProver_top ),
% 3.36/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_19,negated_conjecture,
% 3.36/0.99      ( k1_xboole_0 != k5_relat_1(sK8,k1_xboole_0)
% 3.36/0.99      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK8) ),
% 3.36/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_206,plain,( X0 = X0 ),theory(equality) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_219,plain,
% 3.36/0.99      ( k1_xboole_0 = k1_xboole_0 ),
% 3.36/0.99      inference(instantiation,[status(thm)],[c_206]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_16,plain,
% 3.36/0.99      ( ~ v1_relat_1(X0) | ~ v1_relat_1(X1) | v1_relat_1(k5_relat_1(X1,X0)) ),
% 3.36/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_744,plain,
% 3.36/0.99      ( ~ v1_relat_1(X0) | v1_relat_1(k5_relat_1(sK8,X0)) | ~ v1_relat_1(sK8) ),
% 3.36/0.99      inference(instantiation,[status(thm)],[c_16]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_745,plain,
% 3.36/0.99      ( v1_relat_1(X0) != iProver_top
% 3.36/0.99      | v1_relat_1(k5_relat_1(sK8,X0)) = iProver_top
% 3.36/0.99      | v1_relat_1(sK8) != iProver_top ),
% 3.36/0.99      inference(predicate_to_equality,[status(thm)],[c_744]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_747,plain,
% 3.36/0.99      ( v1_relat_1(k5_relat_1(sK8,k1_xboole_0)) = iProver_top
% 3.36/0.99      | v1_relat_1(sK8) != iProver_top
% 3.36/0.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.36/0.99      inference(instantiation,[status(thm)],[c_745]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_207,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_757,plain,
% 3.36/0.99      ( k5_relat_1(k1_xboole_0,sK8) != X0
% 3.36/0.99      | k1_xboole_0 != X0
% 3.36/0.99      | k1_xboole_0 = k5_relat_1(k1_xboole_0,sK8) ),
% 3.36/0.99      inference(instantiation,[status(thm)],[c_207]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_758,plain,
% 3.36/0.99      ( k5_relat_1(k1_xboole_0,sK8) != k1_xboole_0
% 3.36/0.99      | k1_xboole_0 = k5_relat_1(k1_xboole_0,sK8)
% 3.36/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.36/0.99      inference(instantiation,[status(thm)],[c_757]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_526,plain,
% 3.36/0.99      ( v1_relat_1(sK8) = iProver_top ),
% 3.36/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_17,plain,
% 3.36/0.99      ( ~ v1_relat_1(X0) | v1_relat_1(k4_xboole_0(X0,X1)) ),
% 3.36/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_528,plain,
% 3.36/0.99      ( v1_relat_1(X0) != iProver_top
% 3.36/0.99      | v1_relat_1(k4_xboole_0(X0,X1)) = iProver_top ),
% 3.36/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_822,plain,
% 3.36/0.99      ( v1_relat_1(X0) != iProver_top | v1_relat_1(k1_xboole_0) = iProver_top ),
% 3.36/0.99      inference(superposition,[status(thm)],[c_548,c_528]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_832,plain,
% 3.36/0.99      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 3.36/0.99      inference(superposition,[status(thm)],[c_526,c_822]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_18,plain,
% 3.36/0.99      ( r2_hidden(k4_tarski(sK6(X0),sK7(X0)),X0)
% 3.36/0.99      | ~ v1_relat_1(X0)
% 3.36/0.99      | k1_xboole_0 = X0 ),
% 3.36/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_1043,plain,
% 3.36/0.99      ( r2_hidden(k4_tarski(sK6(k5_relat_1(sK8,k1_xboole_0)),sK7(k5_relat_1(sK8,k1_xboole_0))),k5_relat_1(sK8,k1_xboole_0))
% 3.36/0.99      | ~ v1_relat_1(k5_relat_1(sK8,k1_xboole_0))
% 3.36/0.99      | k1_xboole_0 = k5_relat_1(sK8,k1_xboole_0) ),
% 3.36/0.99      inference(instantiation,[status(thm)],[c_18]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_1044,plain,
% 3.36/0.99      ( k1_xboole_0 = k5_relat_1(sK8,k1_xboole_0)
% 3.36/0.99      | r2_hidden(k4_tarski(sK6(k5_relat_1(sK8,k1_xboole_0)),sK7(k5_relat_1(sK8,k1_xboole_0))),k5_relat_1(sK8,k1_xboole_0)) = iProver_top
% 3.36/0.99      | v1_relat_1(k5_relat_1(sK8,k1_xboole_0)) != iProver_top ),
% 3.36/0.99      inference(predicate_to_equality,[status(thm)],[c_1043]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_14,plain,
% 3.36/0.99      ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
% 3.36/0.99      | r2_hidden(k4_tarski(sK5(X2,X3,X0,X1),X1),X3)
% 3.36/0.99      | ~ v1_relat_1(X3)
% 3.36/0.99      | ~ v1_relat_1(X2)
% 3.36/0.99      | ~ v1_relat_1(k5_relat_1(X2,X3)) ),
% 3.36/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_1171,plain,
% 3.36/0.99      ( r2_hidden(k4_tarski(sK5(sK8,k1_xboole_0,sK6(k5_relat_1(sK8,k1_xboole_0)),sK7(k5_relat_1(sK8,k1_xboole_0))),sK7(k5_relat_1(sK8,k1_xboole_0))),k1_xboole_0)
% 3.36/0.99      | ~ r2_hidden(k4_tarski(sK6(k5_relat_1(sK8,k1_xboole_0)),sK7(k5_relat_1(sK8,k1_xboole_0))),k5_relat_1(sK8,k1_xboole_0))
% 3.36/0.99      | ~ v1_relat_1(k5_relat_1(sK8,k1_xboole_0))
% 3.36/0.99      | ~ v1_relat_1(sK8)
% 3.36/0.99      | ~ v1_relat_1(k1_xboole_0) ),
% 3.36/0.99      inference(instantiation,[status(thm)],[c_14]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_1172,plain,
% 3.36/0.99      ( r2_hidden(k4_tarski(sK5(sK8,k1_xboole_0,sK6(k5_relat_1(sK8,k1_xboole_0)),sK7(k5_relat_1(sK8,k1_xboole_0))),sK7(k5_relat_1(sK8,k1_xboole_0))),k1_xboole_0) = iProver_top
% 3.36/0.99      | r2_hidden(k4_tarski(sK6(k5_relat_1(sK8,k1_xboole_0)),sK7(k5_relat_1(sK8,k1_xboole_0))),k5_relat_1(sK8,k1_xboole_0)) != iProver_top
% 3.36/0.99      | v1_relat_1(k5_relat_1(sK8,k1_xboole_0)) != iProver_top
% 3.36/0.99      | v1_relat_1(sK8) != iProver_top
% 3.36/0.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.36/0.99      inference(predicate_to_equality,[status(thm)],[c_1171]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_529,plain,
% 3.36/0.99      ( v1_relat_1(X0) != iProver_top
% 3.36/0.99      | v1_relat_1(X1) != iProver_top
% 3.36/0.99      | v1_relat_1(k5_relat_1(X1,X0)) = iProver_top ),
% 3.36/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_527,plain,
% 3.36/0.99      ( k1_xboole_0 = X0
% 3.36/0.99      | r2_hidden(k4_tarski(sK6(X0),sK7(X0)),X0) = iProver_top
% 3.36/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.36/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_15,plain,
% 3.36/0.99      ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
% 3.36/0.99      | r2_hidden(k4_tarski(X0,sK5(X2,X3,X0,X1)),X2)
% 3.36/0.99      | ~ v1_relat_1(X3)
% 3.36/0.99      | ~ v1_relat_1(X2)
% 3.36/0.99      | ~ v1_relat_1(k5_relat_1(X2,X3)) ),
% 3.36/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_530,plain,
% 3.36/0.99      ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3)) != iProver_top
% 3.36/0.99      | r2_hidden(k4_tarski(X0,sK5(X2,X3,X0,X1)),X2) = iProver_top
% 3.36/0.99      | v1_relat_1(X3) != iProver_top
% 3.36/0.99      | v1_relat_1(X2) != iProver_top
% 3.36/0.99      | v1_relat_1(k5_relat_1(X2,X3)) != iProver_top ),
% 3.36/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_620,plain,
% 3.36/0.99      ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3)) != iProver_top
% 3.36/0.99      | r2_hidden(k4_tarski(X0,sK5(X2,X3,X0,X1)),X2) = iProver_top
% 3.36/0.99      | v1_relat_1(X3) != iProver_top
% 3.36/0.99      | v1_relat_1(X2) != iProver_top ),
% 3.36/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_530,c_529]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_1371,plain,
% 3.36/0.99      ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k1_xboole_0,X2)) != iProver_top
% 3.36/0.99      | v1_relat_1(X2) != iProver_top
% 3.36/0.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.36/0.99      inference(superposition,[status(thm)],[c_620,c_1069]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_1426,plain,
% 3.36/0.99      ( v1_relat_1(X2) != iProver_top
% 3.36/0.99      | r2_hidden(k4_tarski(X0,X1),k5_relat_1(k1_xboole_0,X2)) != iProver_top ),
% 3.36/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1371,c_832]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_1427,plain,
% 3.36/0.99      ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k1_xboole_0,X2)) != iProver_top
% 3.36/0.99      | v1_relat_1(X2) != iProver_top ),
% 3.36/0.99      inference(renaming,[status(thm)],[c_1426]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_1433,plain,
% 3.36/0.99      ( k5_relat_1(k1_xboole_0,X0) = k1_xboole_0
% 3.36/0.99      | v1_relat_1(X0) != iProver_top
% 3.36/0.99      | v1_relat_1(k5_relat_1(k1_xboole_0,X0)) != iProver_top ),
% 3.36/0.99      inference(superposition,[status(thm)],[c_527,c_1427]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_1574,plain,
% 3.36/0.99      ( k5_relat_1(k1_xboole_0,X0) = k1_xboole_0
% 3.36/0.99      | v1_relat_1(X0) != iProver_top
% 3.36/0.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.36/0.99      inference(superposition,[status(thm)],[c_529,c_1433]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_2398,plain,
% 3.36/0.99      ( v1_relat_1(X0) != iProver_top
% 3.36/0.99      | k5_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.36/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1574,c_832]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_2399,plain,
% 3.36/0.99      ( k5_relat_1(k1_xboole_0,X0) = k1_xboole_0
% 3.36/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.36/0.99      inference(renaming,[status(thm)],[c_2398]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_2406,plain,
% 3.36/0.99      ( k5_relat_1(k1_xboole_0,sK8) = k1_xboole_0 ),
% 3.36/0.99      inference(superposition,[status(thm)],[c_526,c_2399]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_2273,plain,
% 3.36/0.99      ( r2_hidden(sK0(X0,X1,X0),X0) | k4_xboole_0(X0,X1) = X0 ),
% 3.36/0.99      inference(factoring,[status(thm)],[c_2]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_4312,plain,
% 3.36/0.99      ( r2_hidden(sK1(X0),X0) | k4_xboole_0(X0,X1) = X0 ),
% 3.36/0.99      inference(resolution,[status(thm)],[c_2273,c_9]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_923,plain,
% 3.36/0.99      ( X0 != X1 | X1 = X0 ),
% 3.36/0.99      inference(resolution,[status(thm)],[c_207,c_206]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_4519,plain,
% 3.36/0.99      ( r2_hidden(sK1(X0),X0) | X0 = k4_xboole_0(X0,X1) ),
% 3.36/0.99      inference(resolution,[status(thm)],[c_4312,c_923]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_212,plain,
% 3.36/0.99      ( ~ v1_relat_1(X0) | v1_relat_1(X1) | X1 != X0 ),
% 3.36/0.99      theory(equality) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_4553,plain,
% 3.36/0.99      ( r2_hidden(sK1(X0),X0)
% 3.36/0.99      | v1_relat_1(X0)
% 3.36/0.99      | ~ v1_relat_1(k4_xboole_0(X0,X1)) ),
% 3.36/0.99      inference(resolution,[status(thm)],[c_4519,c_212]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_801,plain,
% 3.36/0.99      ( v1_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)))
% 3.36/0.99      | ~ v1_relat_1(k1_xboole_0) ),
% 3.36/0.99      inference(resolution,[status(thm)],[c_212,c_6]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_837,plain,
% 3.36/0.99      ( v1_relat_1(k1_xboole_0) ),
% 3.36/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_832]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_840,plain,
% 3.36/0.99      ( v1_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) ),
% 3.36/0.99      inference(global_propositional_subsumption,[status(thm)],[c_801,c_837]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_4566,plain,
% 3.36/0.99      ( r2_hidden(sK1(X0),X0) | v1_relat_1(X0) ),
% 3.36/0.99      inference(resolution,[status(thm)],[c_4553,c_840]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_1002,plain,
% 3.36/0.99      ( r2_hidden(sK1(X0),X0) | ~ v1_relat_1(X0) | k1_xboole_0 = X0 ),
% 3.36/0.99      inference(resolution,[status(thm)],[c_9,c_18]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_1464,plain,
% 3.36/0.99      ( r2_hidden(sK1(X0),X0) | ~ v1_relat_1(X0) | X0 = k1_xboole_0 ),
% 3.36/0.99      inference(resolution,[status(thm)],[c_1002,c_923]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_4763,plain,
% 3.36/0.99      ( r2_hidden(sK1(X0),X0) | X0 = k1_xboole_0 ),
% 3.36/0.99      inference(backward_subsumption_resolution,[status(thm)],[c_4566,c_1464]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_4784,plain,
% 3.36/0.99      ( X0 = k1_xboole_0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 3.36/0.99      inference(predicate_to_equality,[status(thm)],[c_4763]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_8018,plain,
% 3.36/0.99      ( ~ r2_hidden(k4_tarski(sK5(sK8,k1_xboole_0,sK6(k5_relat_1(sK8,k1_xboole_0)),sK7(k5_relat_1(sK8,k1_xboole_0))),sK7(k5_relat_1(sK8,k1_xboole_0))),X0)
% 3.36/0.99      | r2_hidden(sK1(X0),X0) ),
% 3.36/0.99      inference(instantiation,[status(thm)],[c_9]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_8022,plain,
% 3.36/0.99      ( r2_hidden(k4_tarski(sK5(sK8,k1_xboole_0,sK6(k5_relat_1(sK8,k1_xboole_0)),sK7(k5_relat_1(sK8,k1_xboole_0))),sK7(k5_relat_1(sK8,k1_xboole_0))),X0) != iProver_top
% 3.36/0.99      | r2_hidden(sK1(X0),X0) = iProver_top ),
% 3.36/0.99      inference(predicate_to_equality,[status(thm)],[c_8018]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_209,plain,
% 3.36/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.36/0.99      theory(equality) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_3617,plain,
% 3.36/0.99      ( r2_hidden(X0,X1)
% 3.36/0.99      | ~ r2_hidden(k4_tarski(sK5(sK8,k1_xboole_0,sK6(k5_relat_1(sK8,k1_xboole_0)),sK7(k5_relat_1(sK8,k1_xboole_0))),sK7(k5_relat_1(sK8,k1_xboole_0))),k1_xboole_0)
% 3.36/0.99      | X0 != k4_tarski(sK5(sK8,k1_xboole_0,sK6(k5_relat_1(sK8,k1_xboole_0)),sK7(k5_relat_1(sK8,k1_xboole_0))),sK7(k5_relat_1(sK8,k1_xboole_0)))
% 3.36/0.99      | X1 != k1_xboole_0 ),
% 3.36/0.99      inference(instantiation,[status(thm)],[c_209]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_8375,plain,
% 3.36/0.99      ( r2_hidden(k4_tarski(sK5(sK8,k1_xboole_0,sK6(k5_relat_1(sK8,k1_xboole_0)),sK7(k5_relat_1(sK8,k1_xboole_0))),sK7(k5_relat_1(sK8,k1_xboole_0))),X0)
% 3.36/0.99      | ~ r2_hidden(k4_tarski(sK5(sK8,k1_xboole_0,sK6(k5_relat_1(sK8,k1_xboole_0)),sK7(k5_relat_1(sK8,k1_xboole_0))),sK7(k5_relat_1(sK8,k1_xboole_0))),k1_xboole_0)
% 3.36/0.99      | X0 != k1_xboole_0
% 3.36/0.99      | k4_tarski(sK5(sK8,k1_xboole_0,sK6(k5_relat_1(sK8,k1_xboole_0)),sK7(k5_relat_1(sK8,k1_xboole_0))),sK7(k5_relat_1(sK8,k1_xboole_0))) != k4_tarski(sK5(sK8,k1_xboole_0,sK6(k5_relat_1(sK8,k1_xboole_0)),sK7(k5_relat_1(sK8,k1_xboole_0))),sK7(k5_relat_1(sK8,k1_xboole_0))) ),
% 3.36/0.99      inference(instantiation,[status(thm)],[c_3617]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_8377,plain,
% 3.36/0.99      ( X0 != k1_xboole_0
% 3.36/0.99      | k4_tarski(sK5(sK8,k1_xboole_0,sK6(k5_relat_1(sK8,k1_xboole_0)),sK7(k5_relat_1(sK8,k1_xboole_0))),sK7(k5_relat_1(sK8,k1_xboole_0))) != k4_tarski(sK5(sK8,k1_xboole_0,sK6(k5_relat_1(sK8,k1_xboole_0)),sK7(k5_relat_1(sK8,k1_xboole_0))),sK7(k5_relat_1(sK8,k1_xboole_0)))
% 3.36/0.99      | r2_hidden(k4_tarski(sK5(sK8,k1_xboole_0,sK6(k5_relat_1(sK8,k1_xboole_0)),sK7(k5_relat_1(sK8,k1_xboole_0))),sK7(k5_relat_1(sK8,k1_xboole_0))),X0) = iProver_top
% 3.36/0.99      | r2_hidden(k4_tarski(sK5(sK8,k1_xboole_0,sK6(k5_relat_1(sK8,k1_xboole_0)),sK7(k5_relat_1(sK8,k1_xboole_0))),sK7(k5_relat_1(sK8,k1_xboole_0))),k1_xboole_0) != iProver_top ),
% 3.36/0.99      inference(predicate_to_equality,[status(thm)],[c_8375]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_8376,plain,
% 3.36/0.99      ( k4_tarski(sK5(sK8,k1_xboole_0,sK6(k5_relat_1(sK8,k1_xboole_0)),sK7(k5_relat_1(sK8,k1_xboole_0))),sK7(k5_relat_1(sK8,k1_xboole_0))) = k4_tarski(sK5(sK8,k1_xboole_0,sK6(k5_relat_1(sK8,k1_xboole_0)),sK7(k5_relat_1(sK8,k1_xboole_0))),sK7(k5_relat_1(sK8,k1_xboole_0))) ),
% 3.36/0.99      inference(instantiation,[status(thm)],[c_206]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_8718,plain,
% 3.36/0.99      ( r2_hidden(sK1(X0),X0) = iProver_top ),
% 3.36/0.99      inference(global_propositional_subsumption,
% 3.36/0.99                [status(thm)],
% 3.36/0.99                [c_8684,c_21,c_19,c_219,c_747,c_758,c_832,c_1044,c_1172,
% 3.36/0.99                 c_2406,c_4784,c_8022,c_8377,c_8376]) ).
% 3.36/0.99  
% 3.36/0.99  cnf(c_8729,plain,
% 3.36/0.99      ( $false ),
% 3.36/0.99      inference(superposition,[status(thm)],[c_8718,c_1069]) ).
% 3.36/0.99  
% 3.36/0.99  
% 3.36/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.36/0.99  
% 3.36/0.99  ------                               Statistics
% 3.36/0.99  
% 3.36/0.99  ------ Selected
% 3.36/0.99  
% 3.36/0.99  total_time:                             0.325
% 3.36/0.99  
%------------------------------------------------------------------------------
