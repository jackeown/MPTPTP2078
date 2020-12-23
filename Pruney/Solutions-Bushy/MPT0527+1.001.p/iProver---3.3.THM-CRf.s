%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0527+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:30 EST 2020

% Result     : Theorem 3.71s
% Output     : CNFRefutation 3.71s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 154 expanded)
%              Number of clauses        :   30 (  34 expanded)
%              Number of leaves         :    7 (  30 expanded)
%              Depth                    :   11
%              Number of atoms          :  349 (1259 expanded)
%              Number of equality atoms :   42 ( 149 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal clause size      :   16 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( k8_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X1)
                  & r2_hidden(X4,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k8_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X1)
                  & r2_hidden(X4,X0) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k8_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k8_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X1)
                    | ~ r2_hidden(X6,X0) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X1)
                      & r2_hidden(X6,X0) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k8_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f12])).

fof(f14,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ( r2_hidden(k4_tarski(X3,X4),X1)
              & r2_hidden(X4,X0) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X0)
          | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2) )
        & ( ( r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X1)
            & r2_hidden(sK1(X0,X1,X2),X0) )
          | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X1)
                  | ~ r2_hidden(sK1(X0,X1,X2),X0)
                  | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2) )
                & ( ( r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X1)
                    & r2_hidden(sK1(X0,X1,X2),X0) )
                  | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X1)
                    | ~ r2_hidden(X6,X0) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X1)
                      & r2_hidden(X6,X0) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k8_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f14])).

fof(f29,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X2)
      | ~ r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(X6,X0)
      | k8_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f46,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(X6,X0)
      | ~ v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f29])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(nnf_transformation,[],[f3])).

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
     => ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f23])).

fof(f39,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f51,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f39])).

fof(f27,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(X6,X0)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k8_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f48,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X6,X0)
      | ~ r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1))
      | ~ v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f27])).

fof(f28,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k8_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f47,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1))
      | ~ v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f28])).

fof(f37,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f53,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f37])).

fof(f38,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f52,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f38])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X0,X1) = X2
      | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X1)
      | ~ r2_hidden(sK1(X0,X1,X2),X0)
      | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X1)
      | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X0)
      | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( k8_relat_1(X0,k8_relat_1(X1,X2)) != k8_relat_1(k3_xboole_0(X0,X1),X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,
    ( ? [X0,X1,X2] :
        ( k8_relat_1(X0,k8_relat_1(X1,X2)) != k8_relat_1(k3_xboole_0(X0,X1),X2)
        & v1_relat_1(X2) )
   => ( k8_relat_1(k3_xboole_0(sK5,sK6),sK7) != k8_relat_1(sK5,k8_relat_1(sK6,sK7))
      & v1_relat_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( k8_relat_1(k3_xboole_0(sK5,sK6),sK7) != k8_relat_1(sK5,k8_relat_1(sK6,sK7))
    & v1_relat_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f10,f25])).

fof(f45,plain,(
    k8_relat_1(k3_xboole_0(sK5,sK6),sK7) != k8_relat_1(sK5,k8_relat_1(sK6,sK7)) ),
    inference(cnf_transformation,[],[f26])).

fof(f44,plain,(
    v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | r2_hidden(k4_tarski(X2,X0),k8_relat_1(X1,X3))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(k8_relat_1(X1,X3)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_2754,plain,
    ( ~ r2_hidden(sK1(k3_xboole_0(sK5,sK6),sK7,k8_relat_1(sK5,k8_relat_1(sK6,sK7))),sK5)
    | ~ r2_hidden(k4_tarski(X0,sK1(k3_xboole_0(sK5,sK6),sK7,k8_relat_1(sK5,k8_relat_1(sK6,sK7)))),X1)
    | r2_hidden(k4_tarski(X0,sK1(k3_xboole_0(sK5,sK6),sK7,k8_relat_1(sK5,k8_relat_1(sK6,sK7)))),k8_relat_1(sK5,X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(k8_relat_1(sK5,X1)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_12739,plain,
    ( ~ r2_hidden(sK1(k3_xboole_0(sK5,sK6),sK7,k8_relat_1(sK5,k8_relat_1(sK6,sK7))),sK5)
    | ~ r2_hidden(k4_tarski(sK0(k3_xboole_0(sK5,sK6),sK7,k8_relat_1(sK5,k8_relat_1(sK6,sK7))),sK1(k3_xboole_0(sK5,sK6),sK7,k8_relat_1(sK5,k8_relat_1(sK6,sK7)))),k8_relat_1(sK6,sK7))
    | r2_hidden(k4_tarski(sK0(k3_xboole_0(sK5,sK6),sK7,k8_relat_1(sK5,k8_relat_1(sK6,sK7))),sK1(k3_xboole_0(sK5,sK6),sK7,k8_relat_1(sK5,k8_relat_1(sK6,sK7)))),k8_relat_1(sK5,k8_relat_1(sK6,sK7)))
    | ~ v1_relat_1(k8_relat_1(sK6,sK7))
    | ~ v1_relat_1(k8_relat_1(sK5,k8_relat_1(sK6,sK7))) ),
    inference(instantiation,[status(thm)],[c_2754])).

cnf(c_2739,plain,
    ( ~ r2_hidden(sK1(k3_xboole_0(sK5,sK6),sK7,k8_relat_1(sK5,k8_relat_1(sK6,sK7))),sK6)
    | ~ r2_hidden(k4_tarski(X0,sK1(k3_xboole_0(sK5,sK6),sK7,k8_relat_1(sK5,k8_relat_1(sK6,sK7)))),X1)
    | r2_hidden(k4_tarski(X0,sK1(k3_xboole_0(sK5,sK6),sK7,k8_relat_1(sK5,k8_relat_1(sK6,sK7)))),k8_relat_1(sK6,X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(k8_relat_1(sK6,X1)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_6129,plain,
    ( ~ r2_hidden(sK1(k3_xboole_0(sK5,sK6),sK7,k8_relat_1(sK5,k8_relat_1(sK6,sK7))),sK6)
    | r2_hidden(k4_tarski(sK0(k3_xboole_0(sK5,sK6),sK7,k8_relat_1(sK5,k8_relat_1(sK6,sK7))),sK1(k3_xboole_0(sK5,sK6),sK7,k8_relat_1(sK5,k8_relat_1(sK6,sK7)))),k8_relat_1(sK6,sK7))
    | ~ r2_hidden(k4_tarski(sK0(k3_xboole_0(sK5,sK6),sK7,k8_relat_1(sK5,k8_relat_1(sK6,sK7))),sK1(k3_xboole_0(sK5,sK6),sK7,k8_relat_1(sK5,k8_relat_1(sK6,sK7)))),sK7)
    | ~ v1_relat_1(k8_relat_1(sK6,sK7))
    | ~ v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_2739])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2741,plain,
    ( ~ r2_hidden(sK1(k3_xboole_0(sK5,sK6),sK7,k8_relat_1(sK5,k8_relat_1(sK6,sK7))),X0)
    | r2_hidden(sK1(k3_xboole_0(sK5,sK6),sK7,k8_relat_1(sK5,k8_relat_1(sK6,sK7))),k3_xboole_0(X0,sK6))
    | ~ r2_hidden(sK1(k3_xboole_0(sK5,sK6),sK7,k8_relat_1(sK5,k8_relat_1(sK6,sK7))),sK6) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_5084,plain,
    ( r2_hidden(sK1(k3_xboole_0(sK5,sK6),sK7,k8_relat_1(sK5,k8_relat_1(sK6,sK7))),k3_xboole_0(sK5,sK6))
    | ~ r2_hidden(sK1(k3_xboole_0(sK5,sK6),sK7,k8_relat_1(sK5,k8_relat_1(sK6,sK7))),sK6)
    | ~ r2_hidden(sK1(k3_xboole_0(sK5,sK6),sK7,k8_relat_1(sK5,k8_relat_1(sK6,sK7))),sK5) ),
    inference(instantiation,[status(thm)],[c_2741])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k8_relat_1(X1,X3))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(k8_relat_1(X1,X3)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2995,plain,
    ( r2_hidden(sK1(k3_xboole_0(sK5,sK6),sK7,k8_relat_1(sK5,k8_relat_1(sK6,sK7))),sK6)
    | ~ r2_hidden(k4_tarski(sK0(k3_xboole_0(sK5,sK6),sK7,k8_relat_1(sK5,k8_relat_1(sK6,sK7))),sK1(k3_xboole_0(sK5,sK6),sK7,k8_relat_1(sK5,k8_relat_1(sK6,sK7)))),k8_relat_1(sK6,sK7))
    | ~ v1_relat_1(k8_relat_1(sK6,sK7))
    | ~ v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_4,plain,
    ( r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(X0,X1),k8_relat_1(X3,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(k8_relat_1(X3,X2)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2992,plain,
    ( ~ r2_hidden(k4_tarski(sK0(k3_xboole_0(sK5,sK6),sK7,k8_relat_1(sK5,k8_relat_1(sK6,sK7))),sK1(k3_xboole_0(sK5,sK6),sK7,k8_relat_1(sK5,k8_relat_1(sK6,sK7)))),k8_relat_1(sK6,sK7))
    | r2_hidden(k4_tarski(sK0(k3_xboole_0(sK5,sK6),sK7,k8_relat_1(sK5,k8_relat_1(sK6,sK7))),sK1(k3_xboole_0(sK5,sK6),sK7,k8_relat_1(sK5,k8_relat_1(sK6,sK7)))),sK7)
    | ~ v1_relat_1(k8_relat_1(sK6,sK7))
    | ~ v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_15,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1500,plain,
    ( ~ r2_hidden(sK1(k3_xboole_0(sK5,sK6),sK7,k8_relat_1(sK5,k8_relat_1(sK6,sK7))),k3_xboole_0(sK5,sK6))
    | r2_hidden(sK1(k3_xboole_0(sK5,sK6),sK7,k8_relat_1(sK5,k8_relat_1(sK6,sK7))),sK5) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_14,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1497,plain,
    ( ~ r2_hidden(sK1(k3_xboole_0(sK5,sK6),sK7,k8_relat_1(sK5,k8_relat_1(sK6,sK7))),k3_xboole_0(sK5,sK6))
    | r2_hidden(sK1(k3_xboole_0(sK5,sK6),sK7,k8_relat_1(sK5,k8_relat_1(sK6,sK7))),sK6) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1445,plain,
    ( r2_hidden(sK1(k3_xboole_0(sK5,sK6),sK7,k8_relat_1(sK5,k8_relat_1(sK6,sK7))),sK5)
    | ~ r2_hidden(k4_tarski(sK0(k3_xboole_0(sK5,sK6),sK7,k8_relat_1(sK5,k8_relat_1(sK6,sK7))),sK1(k3_xboole_0(sK5,sK6),sK7,k8_relat_1(sK5,k8_relat_1(sK6,sK7)))),k8_relat_1(sK5,k8_relat_1(sK6,sK7)))
    | ~ v1_relat_1(k8_relat_1(sK6,sK7))
    | ~ v1_relat_1(k8_relat_1(sK5,k8_relat_1(sK6,sK7))) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1442,plain,
    ( r2_hidden(k4_tarski(sK0(k3_xboole_0(sK5,sK6),sK7,k8_relat_1(sK5,k8_relat_1(sK6,sK7))),sK1(k3_xboole_0(sK5,sK6),sK7,k8_relat_1(sK5,k8_relat_1(sK6,sK7)))),k8_relat_1(sK6,sK7))
    | ~ r2_hidden(k4_tarski(sK0(k3_xboole_0(sK5,sK6),sK7,k8_relat_1(sK5,k8_relat_1(sK6,sK7))),sK1(k3_xboole_0(sK5,sK6),sK7,k8_relat_1(sK5,k8_relat_1(sK6,sK7)))),k8_relat_1(sK5,k8_relat_1(sK6,sK7)))
    | ~ v1_relat_1(k8_relat_1(sK6,sK7))
    | ~ v1_relat_1(k8_relat_1(sK5,k8_relat_1(sK6,sK7))) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_16,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k8_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_932,plain,
    ( v1_relat_1(k8_relat_1(sK6,sK7))
    | ~ v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_825,plain,
    ( ~ v1_relat_1(k8_relat_1(sK6,sK7))
    | v1_relat_1(k8_relat_1(sK5,k8_relat_1(sK6,sK7))) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK1(X0,X1,X2),X0)
    | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X1)
    | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | k8_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_768,plain,
    ( ~ r2_hidden(sK1(k3_xboole_0(sK5,sK6),sK7,k8_relat_1(sK5,k8_relat_1(sK6,sK7))),k3_xboole_0(sK5,sK6))
    | ~ r2_hidden(k4_tarski(sK0(k3_xboole_0(sK5,sK6),sK7,k8_relat_1(sK5,k8_relat_1(sK6,sK7))),sK1(k3_xboole_0(sK5,sK6),sK7,k8_relat_1(sK5,k8_relat_1(sK6,sK7)))),k8_relat_1(sK5,k8_relat_1(sK6,sK7)))
    | ~ r2_hidden(k4_tarski(sK0(k3_xboole_0(sK5,sK6),sK7,k8_relat_1(sK5,k8_relat_1(sK6,sK7))),sK1(k3_xboole_0(sK5,sK6),sK7,k8_relat_1(sK5,k8_relat_1(sK6,sK7)))),sK7)
    | ~ v1_relat_1(k8_relat_1(sK5,k8_relat_1(sK6,sK7)))
    | ~ v1_relat_1(sK7)
    | k8_relat_1(k3_xboole_0(sK5,sK6),sK7) = k8_relat_1(sK5,k8_relat_1(sK6,sK7)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1,plain,
    ( r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X1)
    | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | k8_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_765,plain,
    ( r2_hidden(k4_tarski(sK0(k3_xboole_0(sK5,sK6),sK7,k8_relat_1(sK5,k8_relat_1(sK6,sK7))),sK1(k3_xboole_0(sK5,sK6),sK7,k8_relat_1(sK5,k8_relat_1(sK6,sK7)))),k8_relat_1(sK5,k8_relat_1(sK6,sK7)))
    | r2_hidden(k4_tarski(sK0(k3_xboole_0(sK5,sK6),sK7,k8_relat_1(sK5,k8_relat_1(sK6,sK7))),sK1(k3_xboole_0(sK5,sK6),sK7,k8_relat_1(sK5,k8_relat_1(sK6,sK7)))),sK7)
    | ~ v1_relat_1(k8_relat_1(sK5,k8_relat_1(sK6,sK7)))
    | ~ v1_relat_1(sK7)
    | k8_relat_1(k3_xboole_0(sK5,sK6),sK7) = k8_relat_1(sK5,k8_relat_1(sK6,sK7)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2,plain,
    ( r2_hidden(sK1(X0,X1,X2),X0)
    | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | k8_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_762,plain,
    ( r2_hidden(sK1(k3_xboole_0(sK5,sK6),sK7,k8_relat_1(sK5,k8_relat_1(sK6,sK7))),k3_xboole_0(sK5,sK6))
    | r2_hidden(k4_tarski(sK0(k3_xboole_0(sK5,sK6),sK7,k8_relat_1(sK5,k8_relat_1(sK6,sK7))),sK1(k3_xboole_0(sK5,sK6),sK7,k8_relat_1(sK5,k8_relat_1(sK6,sK7)))),k8_relat_1(sK5,k8_relat_1(sK6,sK7)))
    | ~ v1_relat_1(k8_relat_1(sK5,k8_relat_1(sK6,sK7)))
    | ~ v1_relat_1(sK7)
    | k8_relat_1(k3_xboole_0(sK5,sK6),sK7) = k8_relat_1(sK5,k8_relat_1(sK6,sK7)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_17,negated_conjecture,
    ( k8_relat_1(k3_xboole_0(sK5,sK6),sK7) != k8_relat_1(sK5,k8_relat_1(sK6,sK7)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_18,negated_conjecture,
    ( v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f44])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12739,c_6129,c_5084,c_2995,c_2992,c_1500,c_1497,c_1445,c_1442,c_932,c_825,c_768,c_765,c_762,c_17,c_18])).


%------------------------------------------------------------------------------
