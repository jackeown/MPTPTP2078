%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:57:16 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 189 expanded)
%              Number of clauses        :   60 (  82 expanded)
%              Number of leaves         :   17 (  48 expanded)
%              Depth                    :   16
%              Number of atoms          :  310 ( 722 expanded)
%              Number of equality atoms :   89 ( 139 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   15 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ! [X3] :
                  ~ ( r2_hidden(X3,X2)
                    & r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f19,plain,(
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

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,sK1(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK1(X1),X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f19])).

fof(f34,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,sK1(X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f1,axiom,(
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

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f17])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f7,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

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

fof(f14,plain,(
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

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f25,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X6,X8),X0) )
     => ( r2_hidden(sK4(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(X6,sK4(X0,X1,X6)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(X3,X5),X0) )
     => ( r2_hidden(sK3(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X3,sK3(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
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
              | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),X4),X0) )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X1)
              & r2_hidden(k4_tarski(sK2(X0,X1,X2),X5),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),X4),X0) )
                | ~ r2_hidden(sK2(X0,X1,X2),X2) )
              & ( ( r2_hidden(sK3(X0,X1,X2),X1)
                  & r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0) )
                | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X6,X7),X0) ) )
                & ( ( r2_hidden(sK4(X0,X1,X6),X1)
                    & r2_hidden(k4_tarski(X6,sK4(X0,X1,X6)),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f22,f25,f24,f23])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f8,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X1),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f9,conjecture,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( r1_xboole_0(X1,X0)
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ~ ( ! [X1] :
              ~ ( r1_xboole_0(X1,X0)
                & r2_hidden(X1,X0) )
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f9])).

fof(f16,plain,(
    ? [X0] :
      ( ! [X1] :
          ( ~ r1_xboole_0(X1,X0)
          | ~ r2_hidden(X1,X0) )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,
    ( ? [X0] :
        ( ! [X1] :
            ( ~ r1_xboole_0(X1,X0)
            | ~ r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 )
   => ( ! [X1] :
          ( ~ r1_xboole_0(X1,sK5)
          | ~ r2_hidden(X1,sK5) )
      & k1_xboole_0 != sK5 ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ! [X1] :
        ( ~ r1_xboole_0(X1,sK5)
        | ~ r2_hidden(X1,sK5) )
    & k1_xboole_0 != sK5 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f16,f27])).

fof(f46,plain,(
    ! [X1] :
      ( ~ r1_xboole_0(X1,sK5)
      | ~ r2_hidden(X1,sK5) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f45,plain,(
    k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,sK1(X1)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1846,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,sK1(X1))
    | ~ r2_hidden(sK2(k6_relat_1(X2),X3,X1),X1) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_5273,plain,
    ( ~ r2_hidden(sK2(k6_relat_1(X0),X1,sK5),sK5)
    | ~ r2_hidden(sK0(sK1(sK5),sK5),sK1(sK5))
    | ~ r2_hidden(sK0(sK1(sK5),sK5),sK5) ),
    inference(instantiation,[status(thm)],[c_1846])).

cnf(c_5305,plain,
    ( ~ r2_hidden(sK2(k6_relat_1(k1_xboole_0),k1_xboole_0,sK5),sK5)
    | ~ r2_hidden(sK0(sK1(sK5),sK5),sK1(sK5))
    | ~ r2_hidden(sK0(sK1(sK5),sK5),sK5) ),
    inference(instantiation,[status(thm)],[c_5273])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_2152,plain,
    ( ~ r2_hidden(sK3(k6_relat_1(X0),X1,X2),X1)
    | ~ r2_hidden(sK3(k6_relat_1(X0),X1,X2),X3)
    | ~ r1_xboole_0(X3,X1) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_5045,plain,
    ( ~ r2_hidden(sK3(k6_relat_1(X0),X1,sK5),X1)
    | ~ r2_hidden(sK3(k6_relat_1(X0),X1,sK5),X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(instantiation,[status(thm)],[c_2152])).

cnf(c_5052,plain,
    ( ~ r2_hidden(sK3(k6_relat_1(k1_xboole_0),k1_xboole_0,sK5),k1_xboole_0)
    | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_5045])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_861,plain,
    ( r2_hidden(sK0(X0,sK5),sK5)
    | r1_xboole_0(X0,sK5) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_4299,plain,
    ( r2_hidden(sK0(sK1(sK5),sK5),sK5)
    | r1_xboole_0(sK1(sK5),sK5) ),
    inference(instantiation,[status(thm)],[c_861])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_4295,plain,
    ( r2_hidden(sK0(sK1(sK5),sK5),sK1(sK5))
    | r1_xboole_0(sK1(sK5),sK5) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_14,plain,
    ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_7,plain,
    ( r2_hidden(sK3(X0,X1,X2),X1)
    | r2_hidden(sK2(X0,X1,X2),X2)
    | ~ v1_relat_1(X0)
    | k10_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_12,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_262,plain,
    ( r2_hidden(sK3(X0,X1,X2),X1)
    | r2_hidden(sK2(X0,X1,X2),X2)
    | k10_relat_1(X0,X1) = X2
    | k6_relat_1(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_12])).

cnf(c_263,plain,
    ( r2_hidden(sK3(k6_relat_1(X0),X1,X2),X1)
    | r2_hidden(sK2(k6_relat_1(X0),X1,X2),X2)
    | k10_relat_1(k6_relat_1(X0),X1) = X2 ),
    inference(unflattening,[status(thm)],[c_262])).

cnf(c_749,plain,
    ( k10_relat_1(k6_relat_1(X0),X1) = X2
    | r2_hidden(sK3(k6_relat_1(X0),X1,X2),X1) = iProver_top
    | r2_hidden(sK2(k6_relat_1(X0),X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_263])).

cnf(c_3379,plain,
    ( k10_relat_1(k6_relat_1(k1_xboole_0),X0) = X1
    | r2_hidden(sK3(k1_xboole_0,X0,X1),X0) = iProver_top
    | r2_hidden(sK2(k6_relat_1(k1_xboole_0),X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_14,c_749])).

cnf(c_13,plain,
    ( k10_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_3561,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK3(k1_xboole_0,X1,X0),X1) = iProver_top
    | r2_hidden(sK2(k1_xboole_0,X1,X0),X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3379,c_13,c_14])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_15,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_176,plain,
    ( ~ r2_hidden(X0,X1)
    | X0 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_15])).

cnf(c_177,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_176])).

cnf(c_751,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_177])).

cnf(c_3780,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK2(k1_xboole_0,k1_xboole_0,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3561,c_751])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK1(X1),X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_753,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(sK1(X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3980,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3780,c_753])).

cnf(c_16,negated_conjecture,
    ( ~ r2_hidden(X0,sK5)
    | ~ r1_xboole_0(X0,sK5) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_752,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r1_xboole_0(X0,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4203,plain,
    ( sK5 = k1_xboole_0
    | r1_xboole_0(sK1(sK5),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3980,c_752])).

cnf(c_4260,plain,
    ( ~ r1_xboole_0(sK1(sK5),sK5)
    | sK5 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4203])).

cnf(c_2159,plain,
    ( ~ r2_hidden(sK3(k6_relat_1(k1_xboole_0),k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2152])).

cnf(c_1847,plain,
    ( ~ r2_hidden(sK2(k6_relat_1(X0),X1,X2),X2)
    | ~ r2_hidden(sK2(k6_relat_1(X0),X1,X2),X3)
    | ~ r1_xboole_0(X3,X2) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1854,plain,
    ( ~ r2_hidden(sK2(k6_relat_1(k1_xboole_0),k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1847])).

cnf(c_506,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_977,plain,
    ( X0 != X1
    | sK5 != X1
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_506])).

cnf(c_1651,plain,
    ( X0 != k10_relat_1(k6_relat_1(X1),X2)
    | sK5 = X0
    | sK5 != k10_relat_1(k6_relat_1(X1),X2) ),
    inference(instantiation,[status(thm)],[c_977])).

cnf(c_1652,plain,
    ( sK5 != k10_relat_1(k6_relat_1(k1_xboole_0),k1_xboole_0)
    | sK5 = k1_xboole_0
    | k1_xboole_0 != k10_relat_1(k6_relat_1(k1_xboole_0),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1651])).

cnf(c_1544,plain,
    ( X0 != X1
    | X0 = k10_relat_1(k6_relat_1(X2),X3)
    | k10_relat_1(k6_relat_1(X2),X3) != X1 ),
    inference(instantiation,[status(thm)],[c_506])).

cnf(c_1545,plain,
    ( k10_relat_1(k6_relat_1(k1_xboole_0),k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k10_relat_1(k6_relat_1(k1_xboole_0),k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1544])).

cnf(c_1495,plain,
    ( r2_hidden(sK3(k6_relat_1(X0),X1,sK5),X1)
    | r2_hidden(sK2(k6_relat_1(X0),X1,sK5),sK5)
    | k10_relat_1(k6_relat_1(X0),X1) = sK5 ),
    inference(instantiation,[status(thm)],[c_263])).

cnf(c_1498,plain,
    ( r2_hidden(sK3(k6_relat_1(k1_xboole_0),k1_xboole_0,sK5),k1_xboole_0)
    | r2_hidden(sK2(k6_relat_1(k1_xboole_0),k1_xboole_0,sK5),sK5)
    | k10_relat_1(k6_relat_1(k1_xboole_0),k1_xboole_0) = sK5 ),
    inference(instantiation,[status(thm)],[c_1495])).

cnf(c_1041,plain,
    ( X0 != sK5
    | sK5 = X0
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_977])).

cnf(c_1493,plain,
    ( k10_relat_1(k6_relat_1(X0),X1) != sK5
    | sK5 = k10_relat_1(k6_relat_1(X0),X1)
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_1041])).

cnf(c_1496,plain,
    ( k10_relat_1(k6_relat_1(k1_xboole_0),k1_xboole_0) != sK5
    | sK5 = k10_relat_1(k6_relat_1(k1_xboole_0),k1_xboole_0)
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_1493])).

cnf(c_505,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1042,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_505])).

cnf(c_914,plain,
    ( sK5 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_506])).

cnf(c_915,plain,
    ( sK5 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_914])).

cnf(c_872,plain,
    ( ~ r2_hidden(sK0(X0,k1_xboole_0),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_177])).

cnf(c_876,plain,
    ( ~ r2_hidden(sK0(k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_872])).

cnf(c_524,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_505])).

cnf(c_265,plain,
    ( r2_hidden(sK3(k6_relat_1(k1_xboole_0),k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | r2_hidden(sK2(k6_relat_1(k1_xboole_0),k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | k10_relat_1(k6_relat_1(k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_263])).

cnf(c_50,plain,
    ( r2_hidden(sK0(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_17,negated_conjecture,
    ( k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f45])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5305,c_5052,c_4299,c_4295,c_4260,c_2159,c_1854,c_1652,c_1545,c_1498,c_1496,c_1042,c_915,c_876,c_524,c_265,c_50,c_17])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:41:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.99/1.08  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.08  
% 1.99/1.08  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.99/1.08  
% 1.99/1.08  ------  iProver source info
% 1.99/1.08  
% 1.99/1.08  git: date: 2020-06-30 10:37:57 +0100
% 1.99/1.08  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.99/1.08  git: non_committed_changes: false
% 1.99/1.08  git: last_make_outside_of_git: false
% 1.99/1.08  
% 1.99/1.08  ------ 
% 1.99/1.08  
% 1.99/1.08  ------ Input Options
% 1.99/1.08  
% 1.99/1.08  --out_options                           all
% 1.99/1.08  --tptp_safe_out                         true
% 1.99/1.08  --problem_path                          ""
% 1.99/1.08  --include_path                          ""
% 1.99/1.08  --clausifier                            res/vclausify_rel
% 1.99/1.08  --clausifier_options                    --mode clausify
% 1.99/1.08  --stdin                                 false
% 1.99/1.08  --stats_out                             all
% 1.99/1.08  
% 1.99/1.08  ------ General Options
% 1.99/1.08  
% 1.99/1.08  --fof                                   false
% 1.99/1.08  --time_out_real                         305.
% 1.99/1.08  --time_out_virtual                      -1.
% 1.99/1.08  --symbol_type_check                     false
% 1.99/1.08  --clausify_out                          false
% 1.99/1.08  --sig_cnt_out                           false
% 1.99/1.08  --trig_cnt_out                          false
% 1.99/1.08  --trig_cnt_out_tolerance                1.
% 1.99/1.08  --trig_cnt_out_sk_spl                   false
% 1.99/1.08  --abstr_cl_out                          false
% 1.99/1.08  
% 1.99/1.08  ------ Global Options
% 1.99/1.08  
% 1.99/1.08  --schedule                              default
% 1.99/1.08  --add_important_lit                     false
% 1.99/1.08  --prop_solver_per_cl                    1000
% 1.99/1.08  --min_unsat_core                        false
% 1.99/1.08  --soft_assumptions                      false
% 1.99/1.08  --soft_lemma_size                       3
% 1.99/1.08  --prop_impl_unit_size                   0
% 1.99/1.08  --prop_impl_unit                        []
% 1.99/1.08  --share_sel_clauses                     true
% 1.99/1.08  --reset_solvers                         false
% 1.99/1.08  --bc_imp_inh                            [conj_cone]
% 1.99/1.08  --conj_cone_tolerance                   3.
% 1.99/1.08  --extra_neg_conj                        none
% 1.99/1.08  --large_theory_mode                     true
% 1.99/1.08  --prolific_symb_bound                   200
% 1.99/1.08  --lt_threshold                          2000
% 1.99/1.08  --clause_weak_htbl                      true
% 1.99/1.08  --gc_record_bc_elim                     false
% 1.99/1.08  
% 1.99/1.08  ------ Preprocessing Options
% 1.99/1.08  
% 1.99/1.08  --preprocessing_flag                    true
% 1.99/1.08  --time_out_prep_mult                    0.1
% 1.99/1.08  --splitting_mode                        input
% 1.99/1.08  --splitting_grd                         true
% 1.99/1.08  --splitting_cvd                         false
% 1.99/1.08  --splitting_cvd_svl                     false
% 1.99/1.08  --splitting_nvd                         32
% 1.99/1.08  --sub_typing                            true
% 1.99/1.08  --prep_gs_sim                           true
% 1.99/1.08  --prep_unflatten                        true
% 1.99/1.08  --prep_res_sim                          true
% 1.99/1.08  --prep_upred                            true
% 1.99/1.08  --prep_sem_filter                       exhaustive
% 1.99/1.08  --prep_sem_filter_out                   false
% 1.99/1.08  --pred_elim                             true
% 1.99/1.08  --res_sim_input                         true
% 1.99/1.08  --eq_ax_congr_red                       true
% 1.99/1.08  --pure_diseq_elim                       true
% 1.99/1.08  --brand_transform                       false
% 1.99/1.08  --non_eq_to_eq                          false
% 1.99/1.08  --prep_def_merge                        true
% 1.99/1.08  --prep_def_merge_prop_impl              false
% 1.99/1.08  --prep_def_merge_mbd                    true
% 1.99/1.08  --prep_def_merge_tr_red                 false
% 1.99/1.08  --prep_def_merge_tr_cl                  false
% 1.99/1.08  --smt_preprocessing                     true
% 1.99/1.08  --smt_ac_axioms                         fast
% 1.99/1.08  --preprocessed_out                      false
% 1.99/1.08  --preprocessed_stats                    false
% 1.99/1.08  
% 1.99/1.08  ------ Abstraction refinement Options
% 1.99/1.08  
% 1.99/1.08  --abstr_ref                             []
% 1.99/1.08  --abstr_ref_prep                        false
% 1.99/1.08  --abstr_ref_until_sat                   false
% 1.99/1.08  --abstr_ref_sig_restrict                funpre
% 1.99/1.08  --abstr_ref_af_restrict_to_split_sk     false
% 1.99/1.08  --abstr_ref_under                       []
% 1.99/1.08  
% 1.99/1.08  ------ SAT Options
% 1.99/1.08  
% 1.99/1.08  --sat_mode                              false
% 1.99/1.08  --sat_fm_restart_options                ""
% 1.99/1.08  --sat_gr_def                            false
% 1.99/1.08  --sat_epr_types                         true
% 1.99/1.08  --sat_non_cyclic_types                  false
% 1.99/1.08  --sat_finite_models                     false
% 1.99/1.08  --sat_fm_lemmas                         false
% 1.99/1.08  --sat_fm_prep                           false
% 1.99/1.08  --sat_fm_uc_incr                        true
% 1.99/1.08  --sat_out_model                         small
% 1.99/1.08  --sat_out_clauses                       false
% 1.99/1.08  
% 1.99/1.08  ------ QBF Options
% 1.99/1.08  
% 1.99/1.08  --qbf_mode                              false
% 1.99/1.08  --qbf_elim_univ                         false
% 1.99/1.08  --qbf_dom_inst                          none
% 1.99/1.08  --qbf_dom_pre_inst                      false
% 1.99/1.08  --qbf_sk_in                             false
% 1.99/1.08  --qbf_pred_elim                         true
% 1.99/1.08  --qbf_split                             512
% 1.99/1.08  
% 1.99/1.08  ------ BMC1 Options
% 1.99/1.08  
% 1.99/1.08  --bmc1_incremental                      false
% 1.99/1.08  --bmc1_axioms                           reachable_all
% 1.99/1.08  --bmc1_min_bound                        0
% 1.99/1.08  --bmc1_max_bound                        -1
% 1.99/1.08  --bmc1_max_bound_default                -1
% 1.99/1.08  --bmc1_symbol_reachability              true
% 1.99/1.08  --bmc1_property_lemmas                  false
% 1.99/1.08  --bmc1_k_induction                      false
% 1.99/1.08  --bmc1_non_equiv_states                 false
% 1.99/1.08  --bmc1_deadlock                         false
% 1.99/1.08  --bmc1_ucm                              false
% 1.99/1.08  --bmc1_add_unsat_core                   none
% 1.99/1.08  --bmc1_unsat_core_children              false
% 1.99/1.08  --bmc1_unsat_core_extrapolate_axioms    false
% 1.99/1.08  --bmc1_out_stat                         full
% 1.99/1.08  --bmc1_ground_init                      false
% 1.99/1.08  --bmc1_pre_inst_next_state              false
% 1.99/1.08  --bmc1_pre_inst_state                   false
% 1.99/1.08  --bmc1_pre_inst_reach_state             false
% 1.99/1.08  --bmc1_out_unsat_core                   false
% 1.99/1.08  --bmc1_aig_witness_out                  false
% 1.99/1.08  --bmc1_verbose                          false
% 1.99/1.08  --bmc1_dump_clauses_tptp                false
% 1.99/1.08  --bmc1_dump_unsat_core_tptp             false
% 1.99/1.08  --bmc1_dump_file                        -
% 1.99/1.08  --bmc1_ucm_expand_uc_limit              128
% 1.99/1.08  --bmc1_ucm_n_expand_iterations          6
% 1.99/1.08  --bmc1_ucm_extend_mode                  1
% 1.99/1.08  --bmc1_ucm_init_mode                    2
% 1.99/1.08  --bmc1_ucm_cone_mode                    none
% 1.99/1.08  --bmc1_ucm_reduced_relation_type        0
% 1.99/1.08  --bmc1_ucm_relax_model                  4
% 1.99/1.08  --bmc1_ucm_full_tr_after_sat            true
% 1.99/1.08  --bmc1_ucm_expand_neg_assumptions       false
% 1.99/1.08  --bmc1_ucm_layered_model                none
% 1.99/1.08  --bmc1_ucm_max_lemma_size               10
% 1.99/1.08  
% 1.99/1.08  ------ AIG Options
% 1.99/1.08  
% 1.99/1.08  --aig_mode                              false
% 1.99/1.08  
% 1.99/1.08  ------ Instantiation Options
% 1.99/1.08  
% 1.99/1.08  --instantiation_flag                    true
% 1.99/1.08  --inst_sos_flag                         false
% 1.99/1.08  --inst_sos_phase                        true
% 1.99/1.08  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.99/1.08  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.99/1.08  --inst_lit_sel_side                     num_symb
% 1.99/1.08  --inst_solver_per_active                1400
% 1.99/1.08  --inst_solver_calls_frac                1.
% 1.99/1.08  --inst_passive_queue_type               priority_queues
% 1.99/1.08  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.99/1.08  --inst_passive_queues_freq              [25;2]
% 1.99/1.08  --inst_dismatching                      true
% 1.99/1.08  --inst_eager_unprocessed_to_passive     true
% 1.99/1.08  --inst_prop_sim_given                   true
% 1.99/1.08  --inst_prop_sim_new                     false
% 1.99/1.08  --inst_subs_new                         false
% 1.99/1.08  --inst_eq_res_simp                      false
% 1.99/1.08  --inst_subs_given                       false
% 1.99/1.08  --inst_orphan_elimination               true
% 1.99/1.08  --inst_learning_loop_flag               true
% 1.99/1.08  --inst_learning_start                   3000
% 1.99/1.08  --inst_learning_factor                  2
% 1.99/1.08  --inst_start_prop_sim_after_learn       3
% 1.99/1.08  --inst_sel_renew                        solver
% 1.99/1.08  --inst_lit_activity_flag                true
% 1.99/1.08  --inst_restr_to_given                   false
% 1.99/1.08  --inst_activity_threshold               500
% 1.99/1.08  --inst_out_proof                        true
% 1.99/1.08  
% 1.99/1.08  ------ Resolution Options
% 1.99/1.08  
% 1.99/1.08  --resolution_flag                       true
% 1.99/1.08  --res_lit_sel                           adaptive
% 1.99/1.08  --res_lit_sel_side                      none
% 1.99/1.08  --res_ordering                          kbo
% 1.99/1.08  --res_to_prop_solver                    active
% 1.99/1.08  --res_prop_simpl_new                    false
% 1.99/1.08  --res_prop_simpl_given                  true
% 1.99/1.08  --res_passive_queue_type                priority_queues
% 1.99/1.08  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.99/1.08  --res_passive_queues_freq               [15;5]
% 1.99/1.08  --res_forward_subs                      full
% 1.99/1.08  --res_backward_subs                     full
% 1.99/1.08  --res_forward_subs_resolution           true
% 1.99/1.08  --res_backward_subs_resolution          true
% 1.99/1.08  --res_orphan_elimination                true
% 1.99/1.08  --res_time_limit                        2.
% 1.99/1.08  --res_out_proof                         true
% 1.99/1.08  
% 1.99/1.08  ------ Superposition Options
% 1.99/1.08  
% 1.99/1.08  --superposition_flag                    true
% 1.99/1.08  --sup_passive_queue_type                priority_queues
% 1.99/1.08  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.99/1.08  --sup_passive_queues_freq               [8;1;4]
% 1.99/1.08  --demod_completeness_check              fast
% 1.99/1.08  --demod_use_ground                      true
% 1.99/1.08  --sup_to_prop_solver                    passive
% 1.99/1.08  --sup_prop_simpl_new                    true
% 1.99/1.08  --sup_prop_simpl_given                  true
% 1.99/1.08  --sup_fun_splitting                     false
% 1.99/1.08  --sup_smt_interval                      50000
% 1.99/1.08  
% 1.99/1.08  ------ Superposition Simplification Setup
% 1.99/1.08  
% 1.99/1.08  --sup_indices_passive                   []
% 1.99/1.08  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.99/1.08  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.99/1.08  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.99/1.08  --sup_full_triv                         [TrivRules;PropSubs]
% 1.99/1.08  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.99/1.08  --sup_full_bw                           [BwDemod]
% 1.99/1.08  --sup_immed_triv                        [TrivRules]
% 1.99/1.08  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.99/1.08  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.99/1.08  --sup_immed_bw_main                     []
% 1.99/1.08  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.99/1.08  --sup_input_triv                        [Unflattening;TrivRules]
% 1.99/1.08  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.99/1.08  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.99/1.08  
% 1.99/1.08  ------ Combination Options
% 1.99/1.08  
% 1.99/1.08  --comb_res_mult                         3
% 1.99/1.08  --comb_sup_mult                         2
% 1.99/1.08  --comb_inst_mult                        10
% 1.99/1.08  
% 1.99/1.08  ------ Debug Options
% 1.99/1.08  
% 1.99/1.08  --dbg_backtrace                         false
% 1.99/1.08  --dbg_dump_prop_clauses                 false
% 1.99/1.08  --dbg_dump_prop_clauses_file            -
% 1.99/1.08  --dbg_out_stat                          false
% 1.99/1.08  ------ Parsing...
% 1.99/1.08  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.99/1.08  
% 1.99/1.08  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 1.99/1.08  
% 1.99/1.08  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.99/1.08  
% 1.99/1.08  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.99/1.08  ------ Proving...
% 1.99/1.08  ------ Problem Properties 
% 1.99/1.08  
% 1.99/1.08  
% 1.99/1.08  clauses                                 16
% 1.99/1.08  conjectures                             2
% 1.99/1.08  EPR                                     4
% 1.99/1.08  Horn                                    12
% 1.99/1.08  unary                                   4
% 1.99/1.08  binary                                  6
% 1.99/1.08  lits                                    35
% 1.99/1.08  lits eq                                 6
% 1.99/1.08  fd_pure                                 0
% 1.99/1.08  fd_pseudo                               0
% 1.99/1.08  fd_cond                                 0
% 1.99/1.08  fd_pseudo_cond                          3
% 1.99/1.08  AC symbols                              0
% 1.99/1.08  
% 1.99/1.08  ------ Schedule dynamic 5 is on 
% 1.99/1.08  
% 1.99/1.08  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.99/1.08  
% 1.99/1.08  
% 1.99/1.08  ------ 
% 1.99/1.08  Current options:
% 1.99/1.08  ------ 
% 1.99/1.08  
% 1.99/1.08  ------ Input Options
% 1.99/1.08  
% 1.99/1.08  --out_options                           all
% 1.99/1.08  --tptp_safe_out                         true
% 1.99/1.08  --problem_path                          ""
% 1.99/1.08  --include_path                          ""
% 1.99/1.08  --clausifier                            res/vclausify_rel
% 1.99/1.08  --clausifier_options                    --mode clausify
% 1.99/1.08  --stdin                                 false
% 1.99/1.08  --stats_out                             all
% 1.99/1.08  
% 1.99/1.08  ------ General Options
% 1.99/1.08  
% 1.99/1.08  --fof                                   false
% 1.99/1.08  --time_out_real                         305.
% 1.99/1.08  --time_out_virtual                      -1.
% 1.99/1.08  --symbol_type_check                     false
% 1.99/1.08  --clausify_out                          false
% 1.99/1.08  --sig_cnt_out                           false
% 1.99/1.08  --trig_cnt_out                          false
% 1.99/1.08  --trig_cnt_out_tolerance                1.
% 1.99/1.08  --trig_cnt_out_sk_spl                   false
% 1.99/1.08  --abstr_cl_out                          false
% 1.99/1.08  
% 1.99/1.08  ------ Global Options
% 1.99/1.08  
% 1.99/1.08  --schedule                              default
% 1.99/1.08  --add_important_lit                     false
% 1.99/1.08  --prop_solver_per_cl                    1000
% 1.99/1.08  --min_unsat_core                        false
% 1.99/1.08  --soft_assumptions                      false
% 1.99/1.08  --soft_lemma_size                       3
% 1.99/1.08  --prop_impl_unit_size                   0
% 1.99/1.08  --prop_impl_unit                        []
% 1.99/1.08  --share_sel_clauses                     true
% 1.99/1.08  --reset_solvers                         false
% 1.99/1.08  --bc_imp_inh                            [conj_cone]
% 1.99/1.08  --conj_cone_tolerance                   3.
% 1.99/1.08  --extra_neg_conj                        none
% 1.99/1.08  --large_theory_mode                     true
% 1.99/1.08  --prolific_symb_bound                   200
% 1.99/1.08  --lt_threshold                          2000
% 1.99/1.08  --clause_weak_htbl                      true
% 1.99/1.08  --gc_record_bc_elim                     false
% 1.99/1.08  
% 1.99/1.08  ------ Preprocessing Options
% 1.99/1.08  
% 1.99/1.08  --preprocessing_flag                    true
% 1.99/1.08  --time_out_prep_mult                    0.1
% 1.99/1.08  --splitting_mode                        input
% 1.99/1.08  --splitting_grd                         true
% 1.99/1.08  --splitting_cvd                         false
% 1.99/1.08  --splitting_cvd_svl                     false
% 1.99/1.08  --splitting_nvd                         32
% 1.99/1.08  --sub_typing                            true
% 1.99/1.08  --prep_gs_sim                           true
% 1.99/1.08  --prep_unflatten                        true
% 1.99/1.08  --prep_res_sim                          true
% 1.99/1.08  --prep_upred                            true
% 1.99/1.08  --prep_sem_filter                       exhaustive
% 1.99/1.08  --prep_sem_filter_out                   false
% 1.99/1.08  --pred_elim                             true
% 1.99/1.08  --res_sim_input                         true
% 1.99/1.08  --eq_ax_congr_red                       true
% 1.99/1.08  --pure_diseq_elim                       true
% 1.99/1.08  --brand_transform                       false
% 1.99/1.08  --non_eq_to_eq                          false
% 1.99/1.08  --prep_def_merge                        true
% 1.99/1.08  --prep_def_merge_prop_impl              false
% 1.99/1.08  --prep_def_merge_mbd                    true
% 1.99/1.08  --prep_def_merge_tr_red                 false
% 1.99/1.08  --prep_def_merge_tr_cl                  false
% 1.99/1.08  --smt_preprocessing                     true
% 1.99/1.08  --smt_ac_axioms                         fast
% 1.99/1.08  --preprocessed_out                      false
% 1.99/1.08  --preprocessed_stats                    false
% 1.99/1.08  
% 1.99/1.08  ------ Abstraction refinement Options
% 1.99/1.08  
% 1.99/1.08  --abstr_ref                             []
% 1.99/1.08  --abstr_ref_prep                        false
% 1.99/1.08  --abstr_ref_until_sat                   false
% 1.99/1.08  --abstr_ref_sig_restrict                funpre
% 1.99/1.08  --abstr_ref_af_restrict_to_split_sk     false
% 1.99/1.08  --abstr_ref_under                       []
% 1.99/1.08  
% 1.99/1.08  ------ SAT Options
% 1.99/1.08  
% 1.99/1.08  --sat_mode                              false
% 1.99/1.08  --sat_fm_restart_options                ""
% 1.99/1.08  --sat_gr_def                            false
% 1.99/1.08  --sat_epr_types                         true
% 1.99/1.08  --sat_non_cyclic_types                  false
% 1.99/1.08  --sat_finite_models                     false
% 1.99/1.08  --sat_fm_lemmas                         false
% 1.99/1.08  --sat_fm_prep                           false
% 1.99/1.08  --sat_fm_uc_incr                        true
% 1.99/1.08  --sat_out_model                         small
% 1.99/1.08  --sat_out_clauses                       false
% 1.99/1.08  
% 1.99/1.08  ------ QBF Options
% 1.99/1.08  
% 1.99/1.08  --qbf_mode                              false
% 1.99/1.08  --qbf_elim_univ                         false
% 1.99/1.08  --qbf_dom_inst                          none
% 1.99/1.08  --qbf_dom_pre_inst                      false
% 1.99/1.08  --qbf_sk_in                             false
% 1.99/1.08  --qbf_pred_elim                         true
% 1.99/1.08  --qbf_split                             512
% 1.99/1.08  
% 1.99/1.08  ------ BMC1 Options
% 1.99/1.08  
% 1.99/1.08  --bmc1_incremental                      false
% 1.99/1.08  --bmc1_axioms                           reachable_all
% 1.99/1.08  --bmc1_min_bound                        0
% 1.99/1.08  --bmc1_max_bound                        -1
% 1.99/1.08  --bmc1_max_bound_default                -1
% 1.99/1.08  --bmc1_symbol_reachability              true
% 1.99/1.08  --bmc1_property_lemmas                  false
% 1.99/1.08  --bmc1_k_induction                      false
% 1.99/1.08  --bmc1_non_equiv_states                 false
% 1.99/1.08  --bmc1_deadlock                         false
% 1.99/1.08  --bmc1_ucm                              false
% 1.99/1.08  --bmc1_add_unsat_core                   none
% 1.99/1.08  --bmc1_unsat_core_children              false
% 1.99/1.08  --bmc1_unsat_core_extrapolate_axioms    false
% 1.99/1.08  --bmc1_out_stat                         full
% 1.99/1.08  --bmc1_ground_init                      false
% 1.99/1.08  --bmc1_pre_inst_next_state              false
% 1.99/1.08  --bmc1_pre_inst_state                   false
% 1.99/1.08  --bmc1_pre_inst_reach_state             false
% 1.99/1.08  --bmc1_out_unsat_core                   false
% 1.99/1.08  --bmc1_aig_witness_out                  false
% 1.99/1.08  --bmc1_verbose                          false
% 1.99/1.08  --bmc1_dump_clauses_tptp                false
% 1.99/1.08  --bmc1_dump_unsat_core_tptp             false
% 1.99/1.08  --bmc1_dump_file                        -
% 1.99/1.08  --bmc1_ucm_expand_uc_limit              128
% 1.99/1.08  --bmc1_ucm_n_expand_iterations          6
% 1.99/1.08  --bmc1_ucm_extend_mode                  1
% 1.99/1.08  --bmc1_ucm_init_mode                    2
% 1.99/1.08  --bmc1_ucm_cone_mode                    none
% 1.99/1.08  --bmc1_ucm_reduced_relation_type        0
% 1.99/1.08  --bmc1_ucm_relax_model                  4
% 1.99/1.08  --bmc1_ucm_full_tr_after_sat            true
% 1.99/1.08  --bmc1_ucm_expand_neg_assumptions       false
% 1.99/1.08  --bmc1_ucm_layered_model                none
% 1.99/1.08  --bmc1_ucm_max_lemma_size               10
% 1.99/1.08  
% 1.99/1.08  ------ AIG Options
% 1.99/1.08  
% 1.99/1.08  --aig_mode                              false
% 1.99/1.08  
% 1.99/1.08  ------ Instantiation Options
% 1.99/1.08  
% 1.99/1.08  --instantiation_flag                    true
% 1.99/1.08  --inst_sos_flag                         false
% 1.99/1.08  --inst_sos_phase                        true
% 1.99/1.08  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.99/1.08  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.99/1.08  --inst_lit_sel_side                     none
% 1.99/1.08  --inst_solver_per_active                1400
% 1.99/1.08  --inst_solver_calls_frac                1.
% 1.99/1.08  --inst_passive_queue_type               priority_queues
% 1.99/1.08  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.99/1.08  --inst_passive_queues_freq              [25;2]
% 1.99/1.08  --inst_dismatching                      true
% 1.99/1.08  --inst_eager_unprocessed_to_passive     true
% 1.99/1.08  --inst_prop_sim_given                   true
% 1.99/1.08  --inst_prop_sim_new                     false
% 1.99/1.08  --inst_subs_new                         false
% 1.99/1.08  --inst_eq_res_simp                      false
% 1.99/1.08  --inst_subs_given                       false
% 1.99/1.08  --inst_orphan_elimination               true
% 1.99/1.08  --inst_learning_loop_flag               true
% 1.99/1.08  --inst_learning_start                   3000
% 1.99/1.08  --inst_learning_factor                  2
% 1.99/1.08  --inst_start_prop_sim_after_learn       3
% 1.99/1.08  --inst_sel_renew                        solver
% 1.99/1.08  --inst_lit_activity_flag                true
% 1.99/1.08  --inst_restr_to_given                   false
% 1.99/1.08  --inst_activity_threshold               500
% 1.99/1.08  --inst_out_proof                        true
% 1.99/1.08  
% 1.99/1.08  ------ Resolution Options
% 1.99/1.08  
% 1.99/1.08  --resolution_flag                       false
% 1.99/1.08  --res_lit_sel                           adaptive
% 1.99/1.08  --res_lit_sel_side                      none
% 1.99/1.08  --res_ordering                          kbo
% 1.99/1.08  --res_to_prop_solver                    active
% 1.99/1.08  --res_prop_simpl_new                    false
% 1.99/1.08  --res_prop_simpl_given                  true
% 1.99/1.08  --res_passive_queue_type                priority_queues
% 1.99/1.08  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.99/1.08  --res_passive_queues_freq               [15;5]
% 1.99/1.08  --res_forward_subs                      full
% 1.99/1.08  --res_backward_subs                     full
% 1.99/1.08  --res_forward_subs_resolution           true
% 1.99/1.08  --res_backward_subs_resolution          true
% 1.99/1.08  --res_orphan_elimination                true
% 1.99/1.08  --res_time_limit                        2.
% 1.99/1.08  --res_out_proof                         true
% 1.99/1.08  
% 1.99/1.08  ------ Superposition Options
% 1.99/1.08  
% 1.99/1.08  --superposition_flag                    true
% 1.99/1.08  --sup_passive_queue_type                priority_queues
% 1.99/1.08  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.99/1.08  --sup_passive_queues_freq               [8;1;4]
% 1.99/1.08  --demod_completeness_check              fast
% 1.99/1.08  --demod_use_ground                      true
% 1.99/1.08  --sup_to_prop_solver                    passive
% 1.99/1.08  --sup_prop_simpl_new                    true
% 1.99/1.08  --sup_prop_simpl_given                  true
% 1.99/1.08  --sup_fun_splitting                     false
% 1.99/1.08  --sup_smt_interval                      50000
% 1.99/1.08  
% 1.99/1.08  ------ Superposition Simplification Setup
% 1.99/1.08  
% 1.99/1.08  --sup_indices_passive                   []
% 1.99/1.08  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.99/1.08  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.99/1.08  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.99/1.08  --sup_full_triv                         [TrivRules;PropSubs]
% 1.99/1.08  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.99/1.08  --sup_full_bw                           [BwDemod]
% 1.99/1.08  --sup_immed_triv                        [TrivRules]
% 1.99/1.08  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.99/1.08  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.99/1.08  --sup_immed_bw_main                     []
% 1.99/1.08  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.99/1.08  --sup_input_triv                        [Unflattening;TrivRules]
% 1.99/1.08  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.99/1.08  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.99/1.08  
% 1.99/1.08  ------ Combination Options
% 1.99/1.08  
% 1.99/1.08  --comb_res_mult                         3
% 1.99/1.08  --comb_sup_mult                         2
% 1.99/1.08  --comb_inst_mult                        10
% 1.99/1.08  
% 1.99/1.08  ------ Debug Options
% 1.99/1.08  
% 1.99/1.08  --dbg_backtrace                         false
% 1.99/1.08  --dbg_dump_prop_clauses                 false
% 1.99/1.08  --dbg_dump_prop_clauses_file            -
% 1.99/1.08  --dbg_out_stat                          false
% 1.99/1.08  
% 1.99/1.08  
% 1.99/1.08  
% 1.99/1.08  
% 1.99/1.08  ------ Proving...
% 1.99/1.08  
% 1.99/1.08  
% 1.99/1.08  % SZS status Theorem for theBenchmark.p
% 1.99/1.08  
% 1.99/1.08  % SZS output start CNFRefutation for theBenchmark.p
% 1.99/1.08  
% 1.99/1.08  fof(f3,axiom,(
% 1.99/1.08    ! [X0,X1] : ~(! [X2] : ~(! [X3] : ~(r2_hidden(X3,X2) & r2_hidden(X3,X1)) & r2_hidden(X2,X1)) & r2_hidden(X0,X1))),
% 1.99/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/1.08  
% 1.99/1.08  fof(f13,plain,(
% 1.99/1.08    ! [X0,X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) | ~r2_hidden(X0,X1))),
% 1.99/1.08    inference(ennf_transformation,[],[f3])).
% 1.99/1.08  
% 1.99/1.08  fof(f19,plain,(
% 1.99/1.08    ! [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) => (! [X3] : (~r2_hidden(X3,sK1(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK1(X1),X1)))),
% 1.99/1.08    introduced(choice_axiom,[])).
% 1.99/1.08  
% 1.99/1.08  fof(f20,plain,(
% 1.99/1.08    ! [X0,X1] : ((! [X3] : (~r2_hidden(X3,sK1(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK1(X1),X1)) | ~r2_hidden(X0,X1))),
% 1.99/1.08    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f19])).
% 1.99/1.08  
% 1.99/1.08  fof(f34,plain,(
% 1.99/1.08    ( ! [X0,X3,X1] : (~r2_hidden(X3,sK1(X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(X0,X1)) )),
% 1.99/1.08    inference(cnf_transformation,[],[f20])).
% 1.99/1.08  
% 1.99/1.08  fof(f1,axiom,(
% 1.99/1.08    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.99/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/1.08  
% 1.99/1.08  fof(f11,plain,(
% 1.99/1.08    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.99/1.08    inference(rectify,[],[f1])).
% 1.99/1.08  
% 1.99/1.08  fof(f12,plain,(
% 1.99/1.08    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.99/1.08    inference(ennf_transformation,[],[f11])).
% 1.99/1.08  
% 1.99/1.08  fof(f17,plain,(
% 1.99/1.08    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 1.99/1.08    introduced(choice_axiom,[])).
% 1.99/1.08  
% 1.99/1.08  fof(f18,plain,(
% 1.99/1.08    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.99/1.08    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f17])).
% 1.99/1.08  
% 1.99/1.08  fof(f31,plain,(
% 1.99/1.08    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.99/1.08    inference(cnf_transformation,[],[f18])).
% 1.99/1.08  
% 1.99/1.08  fof(f30,plain,(
% 1.99/1.08    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 1.99/1.08    inference(cnf_transformation,[],[f18])).
% 1.99/1.08  
% 1.99/1.08  fof(f29,plain,(
% 1.99/1.08    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 1.99/1.08    inference(cnf_transformation,[],[f18])).
% 1.99/1.08  
% 1.99/1.08  fof(f7,axiom,(
% 1.99/1.08    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.99/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/1.08  
% 1.99/1.08  fof(f43,plain,(
% 1.99/1.08    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.99/1.08    inference(cnf_transformation,[],[f7])).
% 1.99/1.08  
% 1.99/1.08  fof(f4,axiom,(
% 1.99/1.08    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))))),
% 1.99/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/1.08  
% 1.99/1.08  fof(f14,plain,(
% 1.99/1.08    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))) | ~v1_relat_1(X0))),
% 1.99/1.08    inference(ennf_transformation,[],[f4])).
% 1.99/1.08  
% 1.99/1.08  fof(f21,plain,(
% 1.99/1.08    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 1.99/1.08    inference(nnf_transformation,[],[f14])).
% 1.99/1.08  
% 1.99/1.08  fof(f22,plain,(
% 1.99/1.08    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0))) & (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X6,X8),X0)) | ~r2_hidden(X6,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 1.99/1.08    inference(rectify,[],[f21])).
% 1.99/1.08  
% 1.99/1.08  fof(f25,plain,(
% 1.99/1.08    ! [X6,X1,X0] : (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X6,X8),X0)) => (r2_hidden(sK4(X0,X1,X6),X1) & r2_hidden(k4_tarski(X6,sK4(X0,X1,X6)),X0)))),
% 1.99/1.08    introduced(choice_axiom,[])).
% 1.99/1.08  
% 1.99/1.08  fof(f24,plain,(
% 1.99/1.08    ( ! [X3] : (! [X2,X1,X0] : (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X3,X5),X0)) => (r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(k4_tarski(X3,sK3(X0,X1,X2)),X0)))) )),
% 1.99/1.08    introduced(choice_axiom,[])).
% 1.99/1.08  
% 1.99/1.08  fof(f23,plain,(
% 1.99/1.08    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(X3,X2))) => ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),X4),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),X5),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 1.99/1.08    introduced(choice_axiom,[])).
% 1.99/1.08  
% 1.99/1.08  fof(f26,plain,(
% 1.99/1.08    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),X4),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0))) & ((r2_hidden(sK4(X0,X1,X6),X1) & r2_hidden(k4_tarski(X6,sK4(X0,X1,X6)),X0)) | ~r2_hidden(X6,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 1.99/1.08    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f22,f25,f24,f23])).
% 1.99/1.08  
% 1.99/1.08  fof(f39,plain,(
% 1.99/1.08    ( ! [X2,X0,X1] : (k10_relat_1(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X2) | ~v1_relat_1(X0)) )),
% 1.99/1.08    inference(cnf_transformation,[],[f26])).
% 1.99/1.08  
% 1.99/1.08  fof(f5,axiom,(
% 1.99/1.08    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 1.99/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/1.08  
% 1.99/1.08  fof(f41,plain,(
% 1.99/1.08    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.99/1.08    inference(cnf_transformation,[],[f5])).
% 1.99/1.08  
% 1.99/1.08  fof(f6,axiom,(
% 1.99/1.08    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 1.99/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/1.08  
% 1.99/1.08  fof(f42,plain,(
% 1.99/1.08    ( ! [X0] : (k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)) )),
% 1.99/1.08    inference(cnf_transformation,[],[f6])).
% 1.99/1.08  
% 1.99/1.08  fof(f2,axiom,(
% 1.99/1.08    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.99/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/1.08  
% 1.99/1.08  fof(f32,plain,(
% 1.99/1.08    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.99/1.08    inference(cnf_transformation,[],[f2])).
% 1.99/1.08  
% 1.99/1.08  fof(f8,axiom,(
% 1.99/1.08    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.99/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/1.08  
% 1.99/1.08  fof(f15,plain,(
% 1.99/1.08    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.99/1.08    inference(ennf_transformation,[],[f8])).
% 1.99/1.08  
% 1.99/1.08  fof(f44,plain,(
% 1.99/1.08    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 1.99/1.08    inference(cnf_transformation,[],[f15])).
% 1.99/1.08  
% 1.99/1.08  fof(f33,plain,(
% 1.99/1.08    ( ! [X0,X1] : (r2_hidden(sK1(X1),X1) | ~r2_hidden(X0,X1)) )),
% 1.99/1.08    inference(cnf_transformation,[],[f20])).
% 1.99/1.08  
% 1.99/1.08  fof(f9,conjecture,(
% 1.99/1.08    ! [X0] : ~(! [X1] : ~(r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 1.99/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/1.08  
% 1.99/1.08  fof(f10,negated_conjecture,(
% 1.99/1.08    ~! [X0] : ~(! [X1] : ~(r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 1.99/1.08    inference(negated_conjecture,[],[f9])).
% 1.99/1.08  
% 1.99/1.08  fof(f16,plain,(
% 1.99/1.08    ? [X0] : (! [X1] : (~r1_xboole_0(X1,X0) | ~r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 1.99/1.08    inference(ennf_transformation,[],[f10])).
% 1.99/1.08  
% 1.99/1.08  fof(f27,plain,(
% 1.99/1.08    ? [X0] : (! [X1] : (~r1_xboole_0(X1,X0) | ~r2_hidden(X1,X0)) & k1_xboole_0 != X0) => (! [X1] : (~r1_xboole_0(X1,sK5) | ~r2_hidden(X1,sK5)) & k1_xboole_0 != sK5)),
% 1.99/1.08    introduced(choice_axiom,[])).
% 1.99/1.08  
% 1.99/1.08  fof(f28,plain,(
% 1.99/1.08    ! [X1] : (~r1_xboole_0(X1,sK5) | ~r2_hidden(X1,sK5)) & k1_xboole_0 != sK5),
% 1.99/1.08    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f16,f27])).
% 1.99/1.08  
% 1.99/1.08  fof(f46,plain,(
% 1.99/1.08    ( ! [X1] : (~r1_xboole_0(X1,sK5) | ~r2_hidden(X1,sK5)) )),
% 1.99/1.08    inference(cnf_transformation,[],[f28])).
% 1.99/1.08  
% 1.99/1.08  fof(f45,plain,(
% 1.99/1.08    k1_xboole_0 != sK5),
% 1.99/1.08    inference(cnf_transformation,[],[f28])).
% 1.99/1.08  
% 1.99/1.08  cnf(c_4,plain,
% 1.99/1.08      ( ~ r2_hidden(X0,X1)
% 1.99/1.08      | ~ r2_hidden(X2,X1)
% 1.99/1.08      | ~ r2_hidden(X2,sK1(X1)) ),
% 1.99/1.08      inference(cnf_transformation,[],[f34]) ).
% 1.99/1.08  
% 1.99/1.08  cnf(c_1846,plain,
% 1.99/1.08      ( ~ r2_hidden(X0,X1)
% 1.99/1.08      | ~ r2_hidden(X0,sK1(X1))
% 1.99/1.08      | ~ r2_hidden(sK2(k6_relat_1(X2),X3,X1),X1) ),
% 1.99/1.08      inference(instantiation,[status(thm)],[c_4]) ).
% 1.99/1.08  
% 1.99/1.08  cnf(c_5273,plain,
% 1.99/1.08      ( ~ r2_hidden(sK2(k6_relat_1(X0),X1,sK5),sK5)
% 1.99/1.08      | ~ r2_hidden(sK0(sK1(sK5),sK5),sK1(sK5))
% 1.99/1.08      | ~ r2_hidden(sK0(sK1(sK5),sK5),sK5) ),
% 1.99/1.08      inference(instantiation,[status(thm)],[c_1846]) ).
% 1.99/1.08  
% 1.99/1.08  cnf(c_5305,plain,
% 1.99/1.08      ( ~ r2_hidden(sK2(k6_relat_1(k1_xboole_0),k1_xboole_0,sK5),sK5)
% 1.99/1.08      | ~ r2_hidden(sK0(sK1(sK5),sK5),sK1(sK5))
% 1.99/1.08      | ~ r2_hidden(sK0(sK1(sK5),sK5),sK5) ),
% 1.99/1.08      inference(instantiation,[status(thm)],[c_5273]) ).
% 1.99/1.08  
% 1.99/1.08  cnf(c_0,plain,
% 1.99/1.08      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 1.99/1.08      inference(cnf_transformation,[],[f31]) ).
% 1.99/1.08  
% 1.99/1.08  cnf(c_2152,plain,
% 1.99/1.08      ( ~ r2_hidden(sK3(k6_relat_1(X0),X1,X2),X1)
% 1.99/1.08      | ~ r2_hidden(sK3(k6_relat_1(X0),X1,X2),X3)
% 1.99/1.08      | ~ r1_xboole_0(X3,X1) ),
% 1.99/1.08      inference(instantiation,[status(thm)],[c_0]) ).
% 1.99/1.08  
% 1.99/1.08  cnf(c_5045,plain,
% 1.99/1.08      ( ~ r2_hidden(sK3(k6_relat_1(X0),X1,sK5),X1)
% 1.99/1.08      | ~ r2_hidden(sK3(k6_relat_1(X0),X1,sK5),X2)
% 1.99/1.08      | ~ r1_xboole_0(X2,X1) ),
% 1.99/1.08      inference(instantiation,[status(thm)],[c_2152]) ).
% 1.99/1.08  
% 1.99/1.08  cnf(c_5052,plain,
% 1.99/1.08      ( ~ r2_hidden(sK3(k6_relat_1(k1_xboole_0),k1_xboole_0,sK5),k1_xboole_0)
% 1.99/1.08      | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 1.99/1.08      inference(instantiation,[status(thm)],[c_5045]) ).
% 1.99/1.08  
% 1.99/1.08  cnf(c_1,plain,
% 1.99/1.08      ( r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1) ),
% 1.99/1.08      inference(cnf_transformation,[],[f30]) ).
% 1.99/1.08  
% 1.99/1.08  cnf(c_861,plain,
% 1.99/1.08      ( r2_hidden(sK0(X0,sK5),sK5) | r1_xboole_0(X0,sK5) ),
% 1.99/1.08      inference(instantiation,[status(thm)],[c_1]) ).
% 1.99/1.08  
% 1.99/1.08  cnf(c_4299,plain,
% 1.99/1.08      ( r2_hidden(sK0(sK1(sK5),sK5),sK5) | r1_xboole_0(sK1(sK5),sK5) ),
% 1.99/1.08      inference(instantiation,[status(thm)],[c_861]) ).
% 1.99/1.08  
% 1.99/1.08  cnf(c_2,plain,
% 1.99/1.08      ( r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1) ),
% 1.99/1.08      inference(cnf_transformation,[],[f29]) ).
% 1.99/1.08  
% 1.99/1.08  cnf(c_4295,plain,
% 1.99/1.08      ( r2_hidden(sK0(sK1(sK5),sK5),sK1(sK5))
% 1.99/1.08      | r1_xboole_0(sK1(sK5),sK5) ),
% 1.99/1.08      inference(instantiation,[status(thm)],[c_2]) ).
% 1.99/1.08  
% 1.99/1.08  cnf(c_14,plain,
% 1.99/1.08      ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 1.99/1.08      inference(cnf_transformation,[],[f43]) ).
% 1.99/1.08  
% 1.99/1.08  cnf(c_7,plain,
% 1.99/1.08      ( r2_hidden(sK3(X0,X1,X2),X1)
% 1.99/1.08      | r2_hidden(sK2(X0,X1,X2),X2)
% 1.99/1.08      | ~ v1_relat_1(X0)
% 1.99/1.08      | k10_relat_1(X0,X1) = X2 ),
% 1.99/1.08      inference(cnf_transformation,[],[f39]) ).
% 1.99/1.08  
% 1.99/1.08  cnf(c_12,plain,
% 1.99/1.08      ( v1_relat_1(k6_relat_1(X0)) ),
% 1.99/1.08      inference(cnf_transformation,[],[f41]) ).
% 1.99/1.08  
% 1.99/1.08  cnf(c_262,plain,
% 1.99/1.08      ( r2_hidden(sK3(X0,X1,X2),X1)
% 1.99/1.08      | r2_hidden(sK2(X0,X1,X2),X2)
% 1.99/1.08      | k10_relat_1(X0,X1) = X2
% 1.99/1.08      | k6_relat_1(X3) != X0 ),
% 1.99/1.08      inference(resolution_lifted,[status(thm)],[c_7,c_12]) ).
% 1.99/1.08  
% 1.99/1.08  cnf(c_263,plain,
% 1.99/1.08      ( r2_hidden(sK3(k6_relat_1(X0),X1,X2),X1)
% 1.99/1.08      | r2_hidden(sK2(k6_relat_1(X0),X1,X2),X2)
% 1.99/1.08      | k10_relat_1(k6_relat_1(X0),X1) = X2 ),
% 1.99/1.08      inference(unflattening,[status(thm)],[c_262]) ).
% 1.99/1.08  
% 1.99/1.08  cnf(c_749,plain,
% 1.99/1.08      ( k10_relat_1(k6_relat_1(X0),X1) = X2
% 1.99/1.08      | r2_hidden(sK3(k6_relat_1(X0),X1,X2),X1) = iProver_top
% 1.99/1.08      | r2_hidden(sK2(k6_relat_1(X0),X1,X2),X2) = iProver_top ),
% 1.99/1.08      inference(predicate_to_equality,[status(thm)],[c_263]) ).
% 1.99/1.08  
% 1.99/1.08  cnf(c_3379,plain,
% 1.99/1.08      ( k10_relat_1(k6_relat_1(k1_xboole_0),X0) = X1
% 1.99/1.08      | r2_hidden(sK3(k1_xboole_0,X0,X1),X0) = iProver_top
% 1.99/1.08      | r2_hidden(sK2(k6_relat_1(k1_xboole_0),X0,X1),X1) = iProver_top ),
% 1.99/1.08      inference(superposition,[status(thm)],[c_14,c_749]) ).
% 1.99/1.08  
% 1.99/1.08  cnf(c_13,plain,
% 1.99/1.08      ( k10_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 1.99/1.08      inference(cnf_transformation,[],[f42]) ).
% 1.99/1.08  
% 1.99/1.08  cnf(c_3561,plain,
% 1.99/1.08      ( k1_xboole_0 = X0
% 1.99/1.08      | r2_hidden(sK3(k1_xboole_0,X1,X0),X1) = iProver_top
% 1.99/1.08      | r2_hidden(sK2(k1_xboole_0,X1,X0),X0) = iProver_top ),
% 1.99/1.08      inference(light_normalisation,[status(thm)],[c_3379,c_13,c_14]) ).
% 1.99/1.08  
% 1.99/1.08  cnf(c_3,plain,
% 1.99/1.08      ( r1_tarski(k1_xboole_0,X0) ),
% 1.99/1.08      inference(cnf_transformation,[],[f32]) ).
% 1.99/1.08  
% 1.99/1.08  cnf(c_15,plain,
% 1.99/1.08      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 1.99/1.08      inference(cnf_transformation,[],[f44]) ).
% 1.99/1.08  
% 1.99/1.08  cnf(c_176,plain,
% 1.99/1.08      ( ~ r2_hidden(X0,X1) | X0 != X2 | k1_xboole_0 != X1 ),
% 1.99/1.08      inference(resolution_lifted,[status(thm)],[c_3,c_15]) ).
% 1.99/1.08  
% 1.99/1.08  cnf(c_177,plain,
% 1.99/1.08      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 1.99/1.08      inference(unflattening,[status(thm)],[c_176]) ).
% 1.99/1.08  
% 1.99/1.08  cnf(c_751,plain,
% 1.99/1.08      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 1.99/1.08      inference(predicate_to_equality,[status(thm)],[c_177]) ).
% 1.99/1.08  
% 1.99/1.08  cnf(c_3780,plain,
% 1.99/1.08      ( k1_xboole_0 = X0
% 1.99/1.08      | r2_hidden(sK2(k1_xboole_0,k1_xboole_0,X0),X0) = iProver_top ),
% 1.99/1.08      inference(superposition,[status(thm)],[c_3561,c_751]) ).
% 1.99/1.08  
% 1.99/1.08  cnf(c_5,plain,
% 1.99/1.08      ( ~ r2_hidden(X0,X1) | r2_hidden(sK1(X1),X1) ),
% 1.99/1.08      inference(cnf_transformation,[],[f33]) ).
% 1.99/1.08  
% 1.99/1.08  cnf(c_753,plain,
% 1.99/1.08      ( r2_hidden(X0,X1) != iProver_top
% 1.99/1.08      | r2_hidden(sK1(X1),X1) = iProver_top ),
% 1.99/1.08      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 1.99/1.08  
% 1.99/1.08  cnf(c_3980,plain,
% 1.99/1.08      ( k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 1.99/1.08      inference(superposition,[status(thm)],[c_3780,c_753]) ).
% 1.99/1.08  
% 1.99/1.08  cnf(c_16,negated_conjecture,
% 1.99/1.08      ( ~ r2_hidden(X0,sK5) | ~ r1_xboole_0(X0,sK5) ),
% 1.99/1.08      inference(cnf_transformation,[],[f46]) ).
% 1.99/1.08  
% 1.99/1.08  cnf(c_752,plain,
% 1.99/1.08      ( r2_hidden(X0,sK5) != iProver_top
% 1.99/1.08      | r1_xboole_0(X0,sK5) != iProver_top ),
% 1.99/1.08      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 1.99/1.08  
% 1.99/1.08  cnf(c_4203,plain,
% 1.99/1.08      ( sK5 = k1_xboole_0 | r1_xboole_0(sK1(sK5),sK5) != iProver_top ),
% 1.99/1.08      inference(superposition,[status(thm)],[c_3980,c_752]) ).
% 1.99/1.08  
% 1.99/1.08  cnf(c_4260,plain,
% 1.99/1.08      ( ~ r1_xboole_0(sK1(sK5),sK5) | sK5 = k1_xboole_0 ),
% 1.99/1.08      inference(predicate_to_equality_rev,[status(thm)],[c_4203]) ).
% 1.99/1.08  
% 1.99/1.08  cnf(c_2159,plain,
% 1.99/1.08      ( ~ r2_hidden(sK3(k6_relat_1(k1_xboole_0),k1_xboole_0,k1_xboole_0),k1_xboole_0)
% 1.99/1.08      | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 1.99/1.08      inference(instantiation,[status(thm)],[c_2152]) ).
% 1.99/1.08  
% 1.99/1.08  cnf(c_1847,plain,
% 1.99/1.08      ( ~ r2_hidden(sK2(k6_relat_1(X0),X1,X2),X2)
% 1.99/1.08      | ~ r2_hidden(sK2(k6_relat_1(X0),X1,X2),X3)
% 1.99/1.08      | ~ r1_xboole_0(X3,X2) ),
% 1.99/1.08      inference(instantiation,[status(thm)],[c_0]) ).
% 1.99/1.08  
% 1.99/1.08  cnf(c_1854,plain,
% 1.99/1.08      ( ~ r2_hidden(sK2(k6_relat_1(k1_xboole_0),k1_xboole_0,k1_xboole_0),k1_xboole_0)
% 1.99/1.08      | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 1.99/1.08      inference(instantiation,[status(thm)],[c_1847]) ).
% 1.99/1.08  
% 1.99/1.08  cnf(c_506,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 1.99/1.08  
% 1.99/1.08  cnf(c_977,plain,
% 1.99/1.08      ( X0 != X1 | sK5 != X1 | sK5 = X0 ),
% 1.99/1.08      inference(instantiation,[status(thm)],[c_506]) ).
% 1.99/1.08  
% 1.99/1.08  cnf(c_1651,plain,
% 1.99/1.08      ( X0 != k10_relat_1(k6_relat_1(X1),X2)
% 1.99/1.08      | sK5 = X0
% 1.99/1.08      | sK5 != k10_relat_1(k6_relat_1(X1),X2) ),
% 1.99/1.08      inference(instantiation,[status(thm)],[c_977]) ).
% 1.99/1.08  
% 1.99/1.08  cnf(c_1652,plain,
% 1.99/1.08      ( sK5 != k10_relat_1(k6_relat_1(k1_xboole_0),k1_xboole_0)
% 1.99/1.08      | sK5 = k1_xboole_0
% 1.99/1.08      | k1_xboole_0 != k10_relat_1(k6_relat_1(k1_xboole_0),k1_xboole_0) ),
% 1.99/1.08      inference(instantiation,[status(thm)],[c_1651]) ).
% 1.99/1.08  
% 1.99/1.08  cnf(c_1544,plain,
% 1.99/1.08      ( X0 != X1
% 1.99/1.08      | X0 = k10_relat_1(k6_relat_1(X2),X3)
% 1.99/1.08      | k10_relat_1(k6_relat_1(X2),X3) != X1 ),
% 1.99/1.08      inference(instantiation,[status(thm)],[c_506]) ).
% 1.99/1.08  
% 1.99/1.08  cnf(c_1545,plain,
% 1.99/1.08      ( k10_relat_1(k6_relat_1(k1_xboole_0),k1_xboole_0) != k1_xboole_0
% 1.99/1.08      | k1_xboole_0 = k10_relat_1(k6_relat_1(k1_xboole_0),k1_xboole_0)
% 1.99/1.08      | k1_xboole_0 != k1_xboole_0 ),
% 1.99/1.08      inference(instantiation,[status(thm)],[c_1544]) ).
% 1.99/1.08  
% 1.99/1.08  cnf(c_1495,plain,
% 1.99/1.08      ( r2_hidden(sK3(k6_relat_1(X0),X1,sK5),X1)
% 1.99/1.08      | r2_hidden(sK2(k6_relat_1(X0),X1,sK5),sK5)
% 1.99/1.08      | k10_relat_1(k6_relat_1(X0),X1) = sK5 ),
% 1.99/1.08      inference(instantiation,[status(thm)],[c_263]) ).
% 1.99/1.08  
% 1.99/1.08  cnf(c_1498,plain,
% 1.99/1.08      ( r2_hidden(sK3(k6_relat_1(k1_xboole_0),k1_xboole_0,sK5),k1_xboole_0)
% 1.99/1.08      | r2_hidden(sK2(k6_relat_1(k1_xboole_0),k1_xboole_0,sK5),sK5)
% 1.99/1.08      | k10_relat_1(k6_relat_1(k1_xboole_0),k1_xboole_0) = sK5 ),
% 1.99/1.08      inference(instantiation,[status(thm)],[c_1495]) ).
% 1.99/1.08  
% 1.99/1.08  cnf(c_1041,plain,
% 1.99/1.08      ( X0 != sK5 | sK5 = X0 | sK5 != sK5 ),
% 1.99/1.08      inference(instantiation,[status(thm)],[c_977]) ).
% 1.99/1.08  
% 1.99/1.08  cnf(c_1493,plain,
% 1.99/1.08      ( k10_relat_1(k6_relat_1(X0),X1) != sK5
% 1.99/1.08      | sK5 = k10_relat_1(k6_relat_1(X0),X1)
% 1.99/1.08      | sK5 != sK5 ),
% 1.99/1.08      inference(instantiation,[status(thm)],[c_1041]) ).
% 1.99/1.08  
% 1.99/1.08  cnf(c_1496,plain,
% 1.99/1.08      ( k10_relat_1(k6_relat_1(k1_xboole_0),k1_xboole_0) != sK5
% 1.99/1.08      | sK5 = k10_relat_1(k6_relat_1(k1_xboole_0),k1_xboole_0)
% 1.99/1.08      | sK5 != sK5 ),
% 1.99/1.08      inference(instantiation,[status(thm)],[c_1493]) ).
% 1.99/1.08  
% 1.99/1.08  cnf(c_505,plain,( X0 = X0 ),theory(equality) ).
% 1.99/1.08  
% 1.99/1.08  cnf(c_1042,plain,
% 1.99/1.08      ( sK5 = sK5 ),
% 1.99/1.08      inference(instantiation,[status(thm)],[c_505]) ).
% 1.99/1.08  
% 1.99/1.08  cnf(c_914,plain,
% 1.99/1.08      ( sK5 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK5 ),
% 1.99/1.08      inference(instantiation,[status(thm)],[c_506]) ).
% 1.99/1.08  
% 1.99/1.08  cnf(c_915,plain,
% 1.99/1.08      ( sK5 != k1_xboole_0
% 1.99/1.08      | k1_xboole_0 = sK5
% 1.99/1.08      | k1_xboole_0 != k1_xboole_0 ),
% 1.99/1.08      inference(instantiation,[status(thm)],[c_914]) ).
% 1.99/1.08  
% 1.99/1.08  cnf(c_872,plain,
% 1.99/1.08      ( ~ r2_hidden(sK0(X0,k1_xboole_0),k1_xboole_0) ),
% 1.99/1.08      inference(instantiation,[status(thm)],[c_177]) ).
% 1.99/1.08  
% 1.99/1.08  cnf(c_876,plain,
% 1.99/1.08      ( ~ r2_hidden(sK0(k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
% 1.99/1.08      inference(instantiation,[status(thm)],[c_872]) ).
% 1.99/1.08  
% 1.99/1.08  cnf(c_524,plain,
% 1.99/1.08      ( k1_xboole_0 = k1_xboole_0 ),
% 1.99/1.08      inference(instantiation,[status(thm)],[c_505]) ).
% 1.99/1.08  
% 1.99/1.08  cnf(c_265,plain,
% 1.99/1.08      ( r2_hidden(sK3(k6_relat_1(k1_xboole_0),k1_xboole_0,k1_xboole_0),k1_xboole_0)
% 1.99/1.08      | r2_hidden(sK2(k6_relat_1(k1_xboole_0),k1_xboole_0,k1_xboole_0),k1_xboole_0)
% 1.99/1.08      | k10_relat_1(k6_relat_1(k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
% 1.99/1.08      inference(instantiation,[status(thm)],[c_263]) ).
% 1.99/1.08  
% 1.99/1.08  cnf(c_50,plain,
% 1.99/1.08      ( r2_hidden(sK0(k1_xboole_0,k1_xboole_0),k1_xboole_0)
% 1.99/1.08      | r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 1.99/1.08      inference(instantiation,[status(thm)],[c_2]) ).
% 1.99/1.08  
% 1.99/1.08  cnf(c_17,negated_conjecture,
% 1.99/1.08      ( k1_xboole_0 != sK5 ),
% 1.99/1.08      inference(cnf_transformation,[],[f45]) ).
% 1.99/1.08  
% 1.99/1.08  cnf(contradiction,plain,
% 1.99/1.08      ( $false ),
% 1.99/1.08      inference(minisat,
% 1.99/1.08                [status(thm)],
% 1.99/1.08                [c_5305,c_5052,c_4299,c_4295,c_4260,c_2159,c_1854,c_1652,
% 1.99/1.08                 c_1545,c_1498,c_1496,c_1042,c_915,c_876,c_524,c_265,
% 1.99/1.08                 c_50,c_17]) ).
% 1.99/1.08  
% 1.99/1.08  
% 1.99/1.08  % SZS output end CNFRefutation for theBenchmark.p
% 1.99/1.08  
% 1.99/1.08  ------                               Statistics
% 1.99/1.08  
% 1.99/1.08  ------ General
% 1.99/1.08  
% 1.99/1.08  abstr_ref_over_cycles:                  0
% 1.99/1.08  abstr_ref_under_cycles:                 0
% 1.99/1.08  gc_basic_clause_elim:                   0
% 1.99/1.08  forced_gc_time:                         0
% 1.99/1.08  parsing_time:                           0.011
% 1.99/1.08  unif_index_cands_time:                  0.
% 1.99/1.08  unif_index_add_time:                    0.
% 1.99/1.08  orderings_time:                         0.
% 1.99/1.08  out_proof_time:                         0.017
% 1.99/1.08  total_time:                             0.234
% 1.99/1.08  num_of_symbols:                         45
% 1.99/1.08  num_of_terms:                           6228
% 1.99/1.08  
% 1.99/1.08  ------ Preprocessing
% 1.99/1.08  
% 1.99/1.08  num_of_splits:                          0
% 1.99/1.08  num_of_split_atoms:                     0
% 1.99/1.08  num_of_reused_defs:                     0
% 1.99/1.08  num_eq_ax_congr_red:                    37
% 1.99/1.08  num_of_sem_filtered_clauses:            1
% 1.99/1.08  num_of_subtypes:                        0
% 1.99/1.08  monotx_restored_types:                  0
% 1.99/1.08  sat_num_of_epr_types:                   0
% 1.99/1.08  sat_num_of_non_cyclic_types:            0
% 1.99/1.08  sat_guarded_non_collapsed_types:        0
% 1.99/1.08  num_pure_diseq_elim:                    0
% 1.99/1.08  simp_replaced_by:                       0
% 1.99/1.08  res_preprocessed:                       87
% 1.99/1.08  prep_upred:                             0
% 1.99/1.08  prep_unflattend:                        24
% 1.99/1.08  smt_new_axioms:                         0
% 1.99/1.08  pred_elim_cands:                        2
% 1.99/1.08  pred_elim:                              2
% 1.99/1.08  pred_elim_cl:                           2
% 1.99/1.08  pred_elim_cycles:                       5
% 1.99/1.08  merged_defs:                            0
% 1.99/1.08  merged_defs_ncl:                        0
% 1.99/1.08  bin_hyper_res:                          0
% 1.99/1.08  prep_cycles:                            4
% 1.99/1.08  pred_elim_time:                         0.006
% 1.99/1.08  splitting_time:                         0.
% 1.99/1.08  sem_filter_time:                        0.
% 1.99/1.08  monotx_time:                            0.001
% 1.99/1.08  subtype_inf_time:                       0.
% 1.99/1.08  
% 1.99/1.08  ------ Problem properties
% 1.99/1.08  
% 1.99/1.08  clauses:                                16
% 1.99/1.08  conjectures:                            2
% 1.99/1.08  epr:                                    4
% 1.99/1.08  horn:                                   12
% 1.99/1.08  ground:                                 2
% 1.99/1.08  unary:                                  4
% 1.99/1.08  binary:                                 6
% 1.99/1.08  lits:                                   35
% 1.99/1.08  lits_eq:                                6
% 1.99/1.08  fd_pure:                                0
% 1.99/1.08  fd_pseudo:                              0
% 1.99/1.08  fd_cond:                                0
% 1.99/1.08  fd_pseudo_cond:                         3
% 1.99/1.08  ac_symbols:                             0
% 1.99/1.08  
% 1.99/1.08  ------ Propositional Solver
% 1.99/1.08  
% 1.99/1.08  prop_solver_calls:                      30
% 1.99/1.08  prop_fast_solver_calls:                 559
% 1.99/1.08  smt_solver_calls:                       0
% 1.99/1.08  smt_fast_solver_calls:                  0
% 1.99/1.08  prop_num_of_clauses:                    2018
% 1.99/1.08  prop_preprocess_simplified:             5226
% 1.99/1.08  prop_fo_subsumed:                       3
% 1.99/1.08  prop_solver_time:                       0.
% 1.99/1.08  smt_solver_time:                        0.
% 1.99/1.08  smt_fast_solver_time:                   0.
% 1.99/1.08  prop_fast_solver_time:                  0.
% 1.99/1.08  prop_unsat_core_time:                   0.
% 1.99/1.08  
% 1.99/1.08  ------ QBF
% 1.99/1.08  
% 1.99/1.08  qbf_q_res:                              0
% 1.99/1.08  qbf_num_tautologies:                    0
% 1.99/1.08  qbf_prep_cycles:                        0
% 1.99/1.08  
% 1.99/1.08  ------ BMC1
% 1.99/1.08  
% 1.99/1.08  bmc1_current_bound:                     -1
% 1.99/1.08  bmc1_last_solved_bound:                 -1
% 1.99/1.08  bmc1_unsat_core_size:                   -1
% 1.99/1.08  bmc1_unsat_core_parents_size:           -1
% 1.99/1.08  bmc1_merge_next_fun:                    0
% 1.99/1.08  bmc1_unsat_core_clauses_time:           0.
% 1.99/1.08  
% 1.99/1.08  ------ Instantiation
% 1.99/1.08  
% 1.99/1.08  inst_num_of_clauses:                    478
% 1.99/1.08  inst_num_in_passive:                    205
% 1.99/1.08  inst_num_in_active:                     249
% 1.99/1.08  inst_num_in_unprocessed:                23
% 1.99/1.08  inst_num_of_loops:                      295
% 1.99/1.08  inst_num_of_learning_restarts:          0
% 1.99/1.08  inst_num_moves_active_passive:          41
% 1.99/1.08  inst_lit_activity:                      0
% 1.99/1.08  inst_lit_activity_moves:                0
% 1.99/1.08  inst_num_tautologies:                   0
% 1.99/1.08  inst_num_prop_implied:                  0
% 1.99/1.08  inst_num_existing_simplified:           0
% 1.99/1.08  inst_num_eq_res_simplified:             0
% 1.99/1.08  inst_num_child_elim:                    0
% 1.99/1.08  inst_num_of_dismatching_blockings:      204
% 1.99/1.08  inst_num_of_non_proper_insts:           291
% 1.99/1.08  inst_num_of_duplicates:                 0
% 1.99/1.08  inst_inst_num_from_inst_to_res:         0
% 1.99/1.08  inst_dismatching_checking_time:         0.
% 1.99/1.08  
% 1.99/1.08  ------ Resolution
% 1.99/1.08  
% 1.99/1.08  res_num_of_clauses:                     0
% 1.99/1.08  res_num_in_passive:                     0
% 1.99/1.08  res_num_in_active:                      0
% 1.99/1.08  res_num_of_loops:                       91
% 1.99/1.08  res_forward_subset_subsumed:            18
% 1.99/1.08  res_backward_subset_subsumed:           0
% 1.99/1.08  res_forward_subsumed:                   0
% 1.99/1.08  res_backward_subsumed:                  0
% 1.99/1.08  res_forward_subsumption_resolution:     0
% 1.99/1.08  res_backward_subsumption_resolution:    0
% 1.99/1.08  res_clause_to_clause_subsumption:       486
% 1.99/1.08  res_orphan_elimination:                 0
% 1.99/1.08  res_tautology_del:                      26
% 1.99/1.08  res_num_eq_res_simplified:              0
% 1.99/1.08  res_num_sel_changes:                    0
% 1.99/1.08  res_moves_from_active_to_pass:          0
% 1.99/1.08  
% 1.99/1.08  ------ Superposition
% 1.99/1.08  
% 1.99/1.08  sup_time_total:                         0.
% 1.99/1.08  sup_time_generating:                    0.
% 1.99/1.08  sup_time_sim_full:                      0.
% 1.99/1.08  sup_time_sim_immed:                     0.
% 1.99/1.08  
% 1.99/1.08  sup_num_of_clauses:                     161
% 1.99/1.08  sup_num_in_active:                      55
% 1.99/1.08  sup_num_in_passive:                     106
% 1.99/1.08  sup_num_of_loops:                       58
% 1.99/1.08  sup_fw_superposition:                   116
% 1.99/1.08  sup_bw_superposition:                   137
% 1.99/1.08  sup_immediate_simplified:               40
% 1.99/1.08  sup_given_eliminated:                   0
% 1.99/1.08  comparisons_done:                       0
% 1.99/1.08  comparisons_avoided:                    0
% 1.99/1.08  
% 1.99/1.08  ------ Simplifications
% 1.99/1.08  
% 1.99/1.08  
% 1.99/1.08  sim_fw_subset_subsumed:                 5
% 1.99/1.08  sim_bw_subset_subsumed:                 12
% 1.99/1.08  sim_fw_subsumed:                        16
% 1.99/1.08  sim_bw_subsumed:                        5
% 1.99/1.08  sim_fw_subsumption_res:                 0
% 1.99/1.08  sim_bw_subsumption_res:                 0
% 1.99/1.08  sim_tautology_del:                      0
% 1.99/1.08  sim_eq_tautology_del:                   3
% 1.99/1.08  sim_eq_res_simp:                        0
% 1.99/1.08  sim_fw_demodulated:                     23
% 1.99/1.08  sim_bw_demodulated:                     1
% 1.99/1.08  sim_light_normalised:                   11
% 1.99/1.08  sim_joinable_taut:                      0
% 1.99/1.08  sim_joinable_simp:                      0
% 1.99/1.08  sim_ac_normalised:                      0
% 1.99/1.08  sim_smt_subsumption:                    0
% 1.99/1.08  
%------------------------------------------------------------------------------
