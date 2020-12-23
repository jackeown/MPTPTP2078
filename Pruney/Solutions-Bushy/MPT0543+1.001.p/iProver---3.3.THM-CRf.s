%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0543+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:32 EST 2020

% Result     : Theorem 7.18s
% Output     : CNFRefutation 7.18s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 231 expanded)
%              Number of clauses        :   49 (  61 expanded)
%              Number of leaves         :   10 (  60 expanded)
%              Depth                    :   13
%              Number of atoms          :  403 (1169 expanded)
%              Number of equality atoms :   55 ( 174 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal clause size      :   15 (   3 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f10,plain,(
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
    inference(nnf_transformation,[],[f7])).

fof(f11,plain,(
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
    inference(rectify,[],[f10])).

fof(f14,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X8,X6),X0) )
     => ( r2_hidden(sK2(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(sK2(X0,X1,X6),X6),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(X5,X3),X0) )
     => ( r2_hidden(sK1(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK1(X0,X1,X2),X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
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
              | ~ r2_hidden(k4_tarski(X4,sK0(X0,X1,X2)),X0) )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X1)
              & r2_hidden(k4_tarski(X5,sK0(X0,X1,X2)),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(k4_tarski(X4,sK0(X0,X1,X2)),X0) )
                | ~ r2_hidden(sK0(X0,X1,X2),X2) )
              & ( ( r2_hidden(sK1(X0,X1,X2),X1)
                  & r2_hidden(k4_tarski(sK1(X0,X1,X2),sK0(X0,X1,X2)),X0) )
                | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X7,X6),X0) ) )
                & ( ( r2_hidden(sK2(X0,X1,X6),X1)
                    & r2_hidden(k4_tarski(sK2(X0,X1,X6),X6),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f14,f13,f12])).

fof(f30,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X7,X6),X0)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f46,plain,(
    ! [X6,X0,X7,X1] :
      ( r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X7,X6),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f30])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f9,plain,(
    ? [X0,X1] :
      ( k9_relat_1(X1,X0) != k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,
    ( ? [X0,X1] :
        ( k9_relat_1(X1,X0) != k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
        & v1_relat_1(X1) )
   => ( k9_relat_1(sK6,sK5) != k9_relat_1(sK6,k3_xboole_0(k1_relat_1(sK6),sK5))
      & v1_relat_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( k9_relat_1(sK6,sK5) != k9_relat_1(sK6,k3_xboole_0(k1_relat_1(sK6),sK5))
    & v1_relat_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f9,f25])).

fof(f44,plain,(
    v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f18,plain,(
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
    inference(rectify,[],[f17])).

fof(f19,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f19])).

fof(f36,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f49,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f36])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f8])).

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK4(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2)
        & r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f23])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2))
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f33,plain,(
    ! [X4,X2,X0,X1] :
      ( k9_relat_1(X0,X1) = X2
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(k4_tarski(X4,sK0(X0,X1,X2)),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f35,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f50,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f35])).

fof(f29,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f47,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X6),X1)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f29])).

fof(f28,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK2(X0,X1,X6),X6),X0)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f48,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k4_tarski(sK2(X0,X1,X6),X6),X0)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f28])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK0(X0,X1,X2)),X0)
      | r2_hidden(sK0(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f45,plain,(
    k9_relat_1(sK6,sK5) != k9_relat_1(sK6,k3_xboole_0(k1_relat_1(sK6),sK5)) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k9_relat_1(X3,X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X3)
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_18,negated_conjecture,
    ( v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_243,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k9_relat_1(X3,X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X3)
    | sK6 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_18])).

cnf(c_244,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k9_relat_1(sK6,X1))
    | ~ r2_hidden(k4_tarski(X0,X2),sK6) ),
    inference(unflattening,[status(thm)],[c_243])).

cnf(c_784,plain,
    ( r2_hidden(X0,k9_relat_1(sK6,k3_xboole_0(X1,X2)))
    | ~ r2_hidden(X3,k3_xboole_0(X1,X2))
    | ~ r2_hidden(k4_tarski(X3,X0),sK6) ),
    inference(instantiation,[status(thm)],[c_244])).

cnf(c_3746,plain,
    ( ~ r2_hidden(sK4(sK0(sK6,sK5,k9_relat_1(sK6,k3_xboole_0(k1_relat_1(sK6),sK5))),sK5,sK6),k3_xboole_0(X0,X1))
    | r2_hidden(sK0(sK6,sK5,k9_relat_1(sK6,k3_xboole_0(k1_relat_1(sK6),sK5))),k9_relat_1(sK6,k3_xboole_0(X0,X1)))
    | ~ r2_hidden(k4_tarski(sK4(sK0(sK6,sK5,k9_relat_1(sK6,k3_xboole_0(k1_relat_1(sK6),sK5))),sK5,sK6),sK0(sK6,sK5,k9_relat_1(sK6,k3_xboole_0(k1_relat_1(sK6),sK5)))),sK6) ),
    inference(instantiation,[status(thm)],[c_784])).

cnf(c_14502,plain,
    ( ~ r2_hidden(sK4(sK0(sK6,sK5,k9_relat_1(sK6,k3_xboole_0(k1_relat_1(sK6),sK5))),sK5,sK6),k3_xboole_0(k1_relat_1(sK6),sK5))
    | r2_hidden(sK0(sK6,sK5,k9_relat_1(sK6,k3_xboole_0(k1_relat_1(sK6),sK5))),k9_relat_1(sK6,k3_xboole_0(k1_relat_1(sK6),sK5)))
    | ~ r2_hidden(k4_tarski(sK4(sK0(sK6,sK5,k9_relat_1(sK6,k3_xboole_0(k1_relat_1(sK6),sK5))),sK5,sK6),sK0(sK6,sK5,k9_relat_1(sK6,k3_xboole_0(k1_relat_1(sK6),sK5)))),sK6) ),
    inference(instantiation,[status(thm)],[c_3746])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_3675,plain,
    ( ~ r2_hidden(sK4(sK0(sK6,sK5,k9_relat_1(sK6,k3_xboole_0(k1_relat_1(sK6),sK5))),sK5,sK6),X0)
    | r2_hidden(sK4(sK0(sK6,sK5,k9_relat_1(sK6,k3_xboole_0(k1_relat_1(sK6),sK5))),sK5,sK6),k3_xboole_0(X0,sK5))
    | ~ r2_hidden(sK4(sK0(sK6,sK5,k9_relat_1(sK6,k3_xboole_0(k1_relat_1(sK6),sK5))),sK5,sK6),sK5) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_12618,plain,
    ( r2_hidden(sK4(sK0(sK6,sK5,k9_relat_1(sK6,k3_xboole_0(k1_relat_1(sK6),sK5))),sK5,sK6),k3_xboole_0(k1_relat_1(sK6),sK5))
    | ~ r2_hidden(sK4(sK0(sK6,sK5,k9_relat_1(sK6,k3_xboole_0(k1_relat_1(sK6),sK5))),sK5,sK6),k1_relat_1(sK6))
    | ~ r2_hidden(sK4(sK0(sK6,sK5,k9_relat_1(sK6,k3_xboole_0(k1_relat_1(sK6),sK5))),sK5,sK6),sK5) ),
    inference(instantiation,[status(thm)],[c_3675])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK4(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_282,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK4(X0,X2,X1),X2)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_18])).

cnf(c_283,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK6,X1))
    | r2_hidden(sK4(X0,X1,sK6),X1) ),
    inference(unflattening,[status(thm)],[c_282])).

cnf(c_2175,plain,
    ( r2_hidden(sK4(sK0(sK6,sK5,k9_relat_1(sK6,k3_xboole_0(k1_relat_1(sK6),sK5))),sK5,sK6),sK5)
    | ~ r2_hidden(sK0(sK6,sK5,k9_relat_1(sK6,k3_xboole_0(k1_relat_1(sK6),sK5))),k9_relat_1(sK6,sK5)) ),
    inference(instantiation,[status(thm)],[c_283])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK4(X0,X2,X1),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_270,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK4(X0,X2,X1),X0),X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_18])).

cnf(c_271,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK6,X1))
    | r2_hidden(k4_tarski(sK4(X0,X1,sK6),X0),sK6) ),
    inference(unflattening,[status(thm)],[c_270])).

cnf(c_2176,plain,
    ( ~ r2_hidden(sK0(sK6,sK5,k9_relat_1(sK6,k3_xboole_0(k1_relat_1(sK6),sK5))),k9_relat_1(sK6,sK5))
    | r2_hidden(k4_tarski(sK4(sK0(sK6,sK5,k9_relat_1(sK6,k3_xboole_0(k1_relat_1(sK6),sK5))),sK5,sK6),sK0(sK6,sK5,k9_relat_1(sK6,k3_xboole_0(k1_relat_1(sK6),sK5)))),sK6) ),
    inference(instantiation,[status(thm)],[c_271])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK4(X0,X2,X1),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_258,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK4(X0,X2,X1),k1_relat_1(X1))
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_18])).

cnf(c_259,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK6,X1))
    | r2_hidden(sK4(X0,X1,sK6),k1_relat_1(sK6)) ),
    inference(unflattening,[status(thm)],[c_258])).

cnf(c_2177,plain,
    ( r2_hidden(sK4(sK0(sK6,sK5,k9_relat_1(sK6,k3_xboole_0(k1_relat_1(sK6),sK5))),sK5,sK6),k1_relat_1(sK6))
    | ~ r2_hidden(sK0(sK6,sK5,k9_relat_1(sK6,k3_xboole_0(k1_relat_1(sK6),sK5))),k9_relat_1(sK6,sK5)) ),
    inference(instantiation,[status(thm)],[c_259])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(sK0(X2,X1,X3),X3)
    | ~ r2_hidden(k4_tarski(X0,sK0(X2,X1,X3)),X2)
    | ~ v1_relat_1(X2)
    | k9_relat_1(X2,X1) = X3 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_225,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(sK0(X2,X1,X3),X3)
    | ~ r2_hidden(k4_tarski(X0,sK0(X2,X1,X3)),X2)
    | k9_relat_1(X2,X1) = X3
    | sK6 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_18])).

cnf(c_226,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(sK0(sK6,X1,X2),X2)
    | ~ r2_hidden(k4_tarski(X0,sK0(sK6,X1,X2)),sK6)
    | k9_relat_1(sK6,X1) = X2 ),
    inference(unflattening,[status(thm)],[c_225])).

cnf(c_797,plain,
    ( ~ r2_hidden(X0,sK5)
    | ~ r2_hidden(sK0(sK6,sK5,k9_relat_1(sK6,k3_xboole_0(k1_relat_1(sK6),sK5))),k9_relat_1(sK6,k3_xboole_0(k1_relat_1(sK6),sK5)))
    | ~ r2_hidden(k4_tarski(X0,sK0(sK6,sK5,k9_relat_1(sK6,k3_xboole_0(k1_relat_1(sK6),sK5)))),sK6)
    | k9_relat_1(sK6,sK5) = k9_relat_1(sK6,k3_xboole_0(k1_relat_1(sK6),sK5)) ),
    inference(instantiation,[status(thm)],[c_226])).

cnf(c_1654,plain,
    ( ~ r2_hidden(sK2(sK6,k3_xboole_0(k1_relat_1(sK6),sK5),sK0(sK6,sK5,k9_relat_1(sK6,k3_xboole_0(k1_relat_1(sK6),sK5)))),sK5)
    | ~ r2_hidden(sK0(sK6,sK5,k9_relat_1(sK6,k3_xboole_0(k1_relat_1(sK6),sK5))),k9_relat_1(sK6,k3_xboole_0(k1_relat_1(sK6),sK5)))
    | ~ r2_hidden(k4_tarski(sK2(sK6,k3_xboole_0(k1_relat_1(sK6),sK5),sK0(sK6,sK5,k9_relat_1(sK6,k3_xboole_0(k1_relat_1(sK6),sK5)))),sK0(sK6,sK5,k9_relat_1(sK6,k3_xboole_0(k1_relat_1(sK6),sK5)))),sK6)
    | k9_relat_1(sK6,sK5) = k9_relat_1(sK6,k3_xboole_0(k1_relat_1(sK6),sK5)) ),
    inference(instantiation,[status(thm)],[c_797])).

cnf(c_932,plain,
    ( r2_hidden(X0,k9_relat_1(sK6,sK5))
    | ~ r2_hidden(sK1(sK6,sK5,k9_relat_1(sK6,k3_xboole_0(k1_relat_1(sK6),sK5))),sK5)
    | ~ r2_hidden(k4_tarski(sK1(sK6,sK5,k9_relat_1(sK6,k3_xboole_0(k1_relat_1(sK6),sK5))),X0),sK6) ),
    inference(instantiation,[status(thm)],[c_244])).

cnf(c_1288,plain,
    ( ~ r2_hidden(sK1(sK6,sK5,k9_relat_1(sK6,k3_xboole_0(k1_relat_1(sK6),sK5))),sK5)
    | r2_hidden(sK0(sK6,sK5,k9_relat_1(sK6,k3_xboole_0(k1_relat_1(sK6),sK5))),k9_relat_1(sK6,sK5))
    | ~ r2_hidden(k4_tarski(sK1(sK6,sK5,k9_relat_1(sK6,k3_xboole_0(k1_relat_1(sK6),sK5))),sK0(sK6,sK5,k9_relat_1(sK6,k3_xboole_0(k1_relat_1(sK6),sK5)))),sK6) ),
    inference(instantiation,[status(thm)],[c_932])).

cnf(c_11,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_896,plain,
    ( ~ r2_hidden(sK2(sK6,k3_xboole_0(k1_relat_1(sK6),sK5),sK0(sK6,sK5,k9_relat_1(sK6,k3_xboole_0(k1_relat_1(sK6),sK5)))),k3_xboole_0(k1_relat_1(sK6),sK5))
    | r2_hidden(sK2(sK6,k3_xboole_0(k1_relat_1(sK6),sK5),sK0(sK6,sK5,k9_relat_1(sK6,k3_xboole_0(k1_relat_1(sK6),sK5)))),sK5) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK2(X1,X2,X0),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_306,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK2(X1,X2,X0),X2)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_18])).

cnf(c_307,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK6,X1))
    | r2_hidden(sK2(sK6,X1,X0),X1) ),
    inference(unflattening,[status(thm)],[c_306])).

cnf(c_820,plain,
    ( r2_hidden(sK2(sK6,k3_xboole_0(k1_relat_1(sK6),sK5),sK0(sK6,sK5,k9_relat_1(sK6,k3_xboole_0(k1_relat_1(sK6),sK5)))),k3_xboole_0(k1_relat_1(sK6),sK5))
    | ~ r2_hidden(sK0(sK6,sK5,k9_relat_1(sK6,k3_xboole_0(k1_relat_1(sK6),sK5))),k9_relat_1(sK6,k3_xboole_0(k1_relat_1(sK6),sK5))) ),
    inference(instantiation,[status(thm)],[c_307])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK2(X1,X2,X0),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_294,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK2(X1,X2,X0),X0),X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_18])).

cnf(c_295,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK6,X1))
    | r2_hidden(k4_tarski(sK2(sK6,X1,X0),X0),sK6) ),
    inference(unflattening,[status(thm)],[c_294])).

cnf(c_821,plain,
    ( ~ r2_hidden(sK0(sK6,sK5,k9_relat_1(sK6,k3_xboole_0(k1_relat_1(sK6),sK5))),k9_relat_1(sK6,k3_xboole_0(k1_relat_1(sK6),sK5)))
    | r2_hidden(k4_tarski(sK2(sK6,k3_xboole_0(k1_relat_1(sK6),sK5),sK0(sK6,sK5,k9_relat_1(sK6,k3_xboole_0(k1_relat_1(sK6),sK5)))),sK0(sK6,sK5,k9_relat_1(sK6,k3_xboole_0(k1_relat_1(sK6),sK5)))),sK6) ),
    inference(instantiation,[status(thm)],[c_295])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK0(X0,X1,X2)),X0)
    | ~ v1_relat_1(X0)
    | k9_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_195,plain,
    ( r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK0(X0,X1,X2)),X0)
    | k9_relat_1(X0,X1) = X2
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_18])).

cnf(c_196,plain,
    ( r2_hidden(sK0(sK6,X0,X1),X1)
    | r2_hidden(k4_tarski(sK1(sK6,X0,X1),sK0(sK6,X0,X1)),sK6)
    | k9_relat_1(sK6,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_195])).

cnf(c_794,plain,
    ( r2_hidden(sK0(sK6,sK5,k9_relat_1(sK6,k3_xboole_0(k1_relat_1(sK6),sK5))),k9_relat_1(sK6,k3_xboole_0(k1_relat_1(sK6),sK5)))
    | r2_hidden(k4_tarski(sK1(sK6,sK5,k9_relat_1(sK6,k3_xboole_0(k1_relat_1(sK6),sK5))),sK0(sK6,sK5,k9_relat_1(sK6,k3_xboole_0(k1_relat_1(sK6),sK5)))),sK6)
    | k9_relat_1(sK6,sK5) = k9_relat_1(sK6,k3_xboole_0(k1_relat_1(sK6),sK5)) ),
    inference(instantiation,[status(thm)],[c_196])).

cnf(c_2,plain,
    ( r2_hidden(sK1(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | ~ v1_relat_1(X0)
    | k9_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_210,plain,
    ( r2_hidden(sK1(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k9_relat_1(X0,X1) = X2
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_18])).

cnf(c_211,plain,
    ( r2_hidden(sK1(sK6,X0,X1),X0)
    | r2_hidden(sK0(sK6,X0,X1),X1)
    | k9_relat_1(sK6,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_210])).

cnf(c_791,plain,
    ( r2_hidden(sK1(sK6,sK5,k9_relat_1(sK6,k3_xboole_0(k1_relat_1(sK6),sK5))),sK5)
    | r2_hidden(sK0(sK6,sK5,k9_relat_1(sK6,k3_xboole_0(k1_relat_1(sK6),sK5))),k9_relat_1(sK6,k3_xboole_0(k1_relat_1(sK6),sK5)))
    | k9_relat_1(sK6,sK5) = k9_relat_1(sK6,k3_xboole_0(k1_relat_1(sK6),sK5)) ),
    inference(instantiation,[status(thm)],[c_211])).

cnf(c_17,negated_conjecture,
    ( k9_relat_1(sK6,sK5) != k9_relat_1(sK6,k3_xboole_0(k1_relat_1(sK6),sK5)) ),
    inference(cnf_transformation,[],[f45])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_14502,c_12618,c_2175,c_2176,c_2177,c_1654,c_1288,c_896,c_820,c_821,c_794,c_791,c_17])).


%------------------------------------------------------------------------------
