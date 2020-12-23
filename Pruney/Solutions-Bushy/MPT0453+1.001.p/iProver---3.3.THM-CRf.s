%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0453+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:20 EST 2020

% Result     : Theorem 7.94s
% Output     : CNFRefutation 7.94s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 211 expanded)
%              Number of clauses        :   55 (  65 expanded)
%              Number of leaves         :   11 (  42 expanded)
%              Depth                    :   11
%              Number of atoms          :  419 (1247 expanded)
%              Number of equality atoms :  111 ( 227 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f24,plain,(
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
    inference(rectify,[],[f23])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X0)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(sK2(X0,X1,X2),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            | ~ r2_hidden(sK2(X0,X1,X2),X0)
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK2(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f25])).

fof(f39,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f60,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f39])).

fof(f40,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f59,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f40])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( k4_relat_1(X0) = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r2_hidden(k4_tarski(X3,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k4_relat_1(X0) = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r2_hidden(k4_tarski(X3,X2),X0) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k4_relat_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) )
                  & ( r2_hidden(k4_tarski(X3,X2),X0)
                    | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
            & ( ! [X2,X3] :
                  ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r2_hidden(k4_tarski(X3,X2),X0) )
                  & ( r2_hidden(k4_tarski(X3,X2),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
              | k4_relat_1(X0) != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k4_relat_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) )
                  & ( r2_hidden(k4_tarski(X3,X2),X0)
                    | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X5,X4),X0) )
                  & ( r2_hidden(k4_tarski(X5,X4),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
              | k4_relat_1(X0) != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f27])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( r2_hidden(k4_tarski(X3,X2),X0)
            | r2_hidden(k4_tarski(X2,X3),X1) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0)
          | ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) )
        & ( r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0)
          | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k4_relat_1(X0) = X1
              | ( ( ~ r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0)
                  | ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) )
                & ( r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0)
                  | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X5,X4),X0) )
                  & ( r2_hidden(k4_tarski(X5,X4),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
              | k4_relat_1(X0) != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f28,f29])).

fof(f46,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r2_hidden(k4_tarski(X5,X4),X0)
      | k4_relat_1(X0) != X1
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f61,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(k4_tarski(X4,X5),k4_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X4),X0)
      | ~ v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f41,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f58,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f45,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X4),X0)
      | ~ r2_hidden(k4_tarski(X4,X5),X1)
      | k4_relat_1(X0) != X1
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f62,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(k4_tarski(X5,X4),X0)
      | ~ r2_hidden(k4_tarski(X4,X5),k4_relat_1(X0))
      | ~ v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f45])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f49,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( X0 = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X0)
              <=> r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( X0 = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X0)
              <=> r2_hidden(k4_tarski(X2,X3),X1) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( X0 = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r2_hidden(k4_tarski(X2,X3),X0) )
                  & ( r2_hidden(k4_tarski(X2,X3),X1)
                    | r2_hidden(k4_tarski(X2,X3),X0) ) ) )
            & ( ! [X2,X3] :
                  ( ( r2_hidden(k4_tarski(X2,X3),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) )
                  & ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
              | X0 != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( X0 = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r2_hidden(k4_tarski(X2,X3),X0) )
                  & ( r2_hidden(k4_tarski(X2,X3),X1)
                    | r2_hidden(k4_tarski(X2,X3),X0) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) )
                  & ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X4,X5),X0) ) )
              | X0 != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f18])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r2_hidden(k4_tarski(X2,X3),X1)
            | ~ r2_hidden(k4_tarski(X2,X3),X0) )
          & ( r2_hidden(k4_tarski(X2,X3),X1)
            | r2_hidden(k4_tarski(X2,X3),X0) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)
          | ~ r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0) )
        & ( r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)
          | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( X0 = X1
              | ( ( ~ r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)
                  | ~ r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0) )
                & ( r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)
                  | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) )
                  & ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X4,X5),X0) ) )
              | X0 != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f20])).

fof(f37,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)
      | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f38,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)
      | ~ r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f9,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k3_xboole_0(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k3_xboole_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => k3_xboole_0(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k3_xboole_0(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k3_xboole_0(k4_relat_1(X0),k4_relat_1(X1)) != k4_relat_1(k3_xboole_0(X0,X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k3_xboole_0(k4_relat_1(X0),k4_relat_1(X1)) != k4_relat_1(k3_xboole_0(X0,X1))
          & v1_relat_1(X1) )
     => ( k3_xboole_0(k4_relat_1(X0),k4_relat_1(sK6)) != k4_relat_1(k3_xboole_0(X0,sK6))
        & v1_relat_1(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k3_xboole_0(k4_relat_1(X0),k4_relat_1(X1)) != k4_relat_1(k3_xboole_0(X0,X1))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k3_xboole_0(k4_relat_1(sK5),k4_relat_1(X1)) != k4_relat_1(k3_xboole_0(sK5,X1))
          & v1_relat_1(X1) )
      & v1_relat_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6)) != k4_relat_1(k3_xboole_0(sK5,sK6))
    & v1_relat_1(sK6)
    & v1_relat_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f17,f32,f31])).

fof(f55,plain,(
    k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6)) != k4_relat_1(k3_xboole_0(sK5,sK6)) ),
    inference(cnf_transformation,[],[f33])).

fof(f54,plain,(
    v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f33])).

fof(f53,plain,(
    v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_10,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_5715,plain,
    ( ~ r2_hidden(k4_tarski(sK1(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6))),sK0(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6)))),k3_xboole_0(sK5,sK6))
    | r2_hidden(k4_tarski(sK1(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6))),sK0(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6)))),sK5) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_5716,plain,
    ( r2_hidden(k4_tarski(sK1(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6))),sK0(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6)))),k3_xboole_0(sK5,sK6)) != iProver_top
    | r2_hidden(k4_tarski(sK1(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6))),sK0(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6)))),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5715])).

cnf(c_9,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_5712,plain,
    ( ~ r2_hidden(k4_tarski(sK1(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6))),sK0(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6)))),k3_xboole_0(sK5,sK6))
    | r2_hidden(k4_tarski(sK1(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6))),sK0(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6)))),sK6) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_5713,plain,
    ( r2_hidden(k4_tarski(sK1(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6))),sK0(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6)))),k3_xboole_0(sK5,sK6)) != iProver_top
    | r2_hidden(k4_tarski(sK1(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6))),sK0(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6)))),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5712])).

cnf(c_13,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | r2_hidden(k4_tarski(X1,X0),k4_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(k4_relat_1(X2)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_5699,plain,
    ( ~ r2_hidden(k4_tarski(sK1(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6))),sK0(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6)))),k3_xboole_0(sK5,sK6))
    | r2_hidden(k4_tarski(sK0(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6))),sK1(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6)))),k4_relat_1(k3_xboole_0(sK5,sK6)))
    | ~ v1_relat_1(k3_xboole_0(sK5,sK6))
    | ~ v1_relat_1(k4_relat_1(k3_xboole_0(sK5,sK6))) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_5700,plain,
    ( r2_hidden(k4_tarski(sK1(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6))),sK0(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6)))),k3_xboole_0(sK5,sK6)) != iProver_top
    | r2_hidden(k4_tarski(sK0(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6))),sK1(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6)))),k4_relat_1(k3_xboole_0(sK5,sK6))) = iProver_top
    | v1_relat_1(k3_xboole_0(sK5,sK6)) != iProver_top
    | v1_relat_1(k4_relat_1(k3_xboole_0(sK5,sK6))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5699])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2183,plain,
    ( ~ r2_hidden(k4_tarski(sK0(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6))),sK1(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6)))),X0)
    | r2_hidden(k4_tarski(sK0(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6))),sK1(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6)))),k3_xboole_0(X0,k4_relat_1(sK6)))
    | ~ r2_hidden(k4_tarski(sK0(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6))),sK1(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6)))),k4_relat_1(sK6)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_3817,plain,
    ( r2_hidden(k4_tarski(sK0(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6))),sK1(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6)))),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6)))
    | ~ r2_hidden(k4_tarski(sK0(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6))),sK1(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6)))),k4_relat_1(sK6))
    | ~ r2_hidden(k4_tarski(sK0(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6))),sK1(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6)))),k4_relat_1(sK5)) ),
    inference(instantiation,[status(thm)],[c_2183])).

cnf(c_3818,plain,
    ( r2_hidden(k4_tarski(sK0(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6))),sK1(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6)))),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6))) = iProver_top
    | r2_hidden(k4_tarski(sK0(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6))),sK1(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6)))),k4_relat_1(sK6)) != iProver_top
    | r2_hidden(k4_tarski(sK0(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6))),sK1(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6)))),k4_relat_1(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3817])).

cnf(c_3223,plain,
    ( ~ r2_hidden(k4_tarski(sK1(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6))),sK0(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6)))),sK5)
    | r2_hidden(k4_tarski(sK0(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6))),sK1(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6)))),k4_relat_1(sK5))
    | ~ v1_relat_1(k4_relat_1(sK5))
    | ~ v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_3224,plain,
    ( r2_hidden(k4_tarski(sK1(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6))),sK0(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6)))),sK5) != iProver_top
    | r2_hidden(k4_tarski(sK0(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6))),sK1(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6)))),k4_relat_1(sK5)) = iProver_top
    | v1_relat_1(k4_relat_1(sK5)) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3223])).

cnf(c_3206,plain,
    ( ~ r2_hidden(k4_tarski(sK1(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6))),sK0(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6)))),X0)
    | r2_hidden(k4_tarski(sK1(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6))),sK0(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6)))),k3_xboole_0(X0,sK6))
    | ~ r2_hidden(k4_tarski(sK1(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6))),sK0(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6)))),sK6) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_3207,plain,
    ( r2_hidden(k4_tarski(sK1(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6))),sK0(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6)))),X0) != iProver_top
    | r2_hidden(k4_tarski(sK1(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6))),sK0(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6)))),k3_xboole_0(X0,sK6)) = iProver_top
    | r2_hidden(k4_tarski(sK1(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6))),sK0(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6)))),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3206])).

cnf(c_3209,plain,
    ( r2_hidden(k4_tarski(sK1(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6))),sK0(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6)))),k3_xboole_0(sK5,sK6)) = iProver_top
    | r2_hidden(k4_tarski(sK1(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6))),sK0(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6)))),sK6) != iProver_top
    | r2_hidden(k4_tarski(sK1(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6))),sK0(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6)))),sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3207])).

cnf(c_3202,plain,
    ( ~ r2_hidden(k4_tarski(sK1(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6))),sK0(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6)))),sK6)
    | r2_hidden(k4_tarski(sK0(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6))),sK1(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6)))),k4_relat_1(sK6))
    | ~ v1_relat_1(k4_relat_1(sK6))
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_3203,plain,
    ( r2_hidden(k4_tarski(sK1(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6))),sK0(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6)))),sK6) != iProver_top
    | r2_hidden(k4_tarski(sK0(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6))),sK1(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6)))),k4_relat_1(sK6)) = iProver_top
    | v1_relat_1(k4_relat_1(sK6)) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3202])).

cnf(c_14,plain,
    ( r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(X1,X0),k4_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(k4_relat_1(X2)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2346,plain,
    ( r2_hidden(k4_tarski(sK1(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6))),sK0(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6)))),k3_xboole_0(sK5,sK6))
    | ~ r2_hidden(k4_tarski(sK0(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6))),sK1(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6)))),k4_relat_1(k3_xboole_0(sK5,sK6)))
    | ~ v1_relat_1(k3_xboole_0(sK5,sK6))
    | ~ v1_relat_1(k4_relat_1(k3_xboole_0(sK5,sK6))) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_2347,plain,
    ( r2_hidden(k4_tarski(sK1(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6))),sK0(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6)))),k3_xboole_0(sK5,sK6)) = iProver_top
    | r2_hidden(k4_tarski(sK0(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6))),sK1(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6)))),k4_relat_1(k3_xboole_0(sK5,sK6))) != iProver_top
    | v1_relat_1(k3_xboole_0(sK5,sK6)) != iProver_top
    | v1_relat_1(k4_relat_1(k3_xboole_0(sK5,sK6))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2346])).

cnf(c_2208,plain,
    ( r2_hidden(k4_tarski(sK1(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6))),sK0(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6)))),sK5)
    | ~ r2_hidden(k4_tarski(sK0(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6))),sK1(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6)))),k4_relat_1(sK5))
    | ~ v1_relat_1(k4_relat_1(sK5))
    | ~ v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_2209,plain,
    ( r2_hidden(k4_tarski(sK1(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6))),sK0(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6)))),sK5) = iProver_top
    | r2_hidden(k4_tarski(sK0(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6))),sK1(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6)))),k4_relat_1(sK5)) != iProver_top
    | v1_relat_1(k4_relat_1(sK5)) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2208])).

cnf(c_2192,plain,
    ( r2_hidden(k4_tarski(sK1(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6))),sK0(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6)))),sK6)
    | ~ r2_hidden(k4_tarski(sK0(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6))),sK1(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6)))),k4_relat_1(sK6))
    | ~ v1_relat_1(k4_relat_1(sK6))
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_2193,plain,
    ( r2_hidden(k4_tarski(sK1(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6))),sK0(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6)))),sK6) = iProver_top
    | r2_hidden(k4_tarski(sK0(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6))),sK1(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6)))),k4_relat_1(sK6)) != iProver_top
    | v1_relat_1(k4_relat_1(sK6)) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2192])).

cnf(c_15,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k4_relat_1(X0)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2027,plain,
    ( v1_relat_1(k4_relat_1(sK6))
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_2028,plain,
    ( v1_relat_1(k4_relat_1(sK6)) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2027])).

cnf(c_1430,plain,
    ( ~ r2_hidden(k4_tarski(sK0(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6))),sK1(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6)))),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6)))
    | r2_hidden(k4_tarski(sK0(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6))),sK1(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6)))),k4_relat_1(sK5)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1431,plain,
    ( r2_hidden(k4_tarski(sK0(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6))),sK1(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6)))),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6))) != iProver_top
    | r2_hidden(k4_tarski(sK0(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6))),sK1(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6)))),k4_relat_1(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1430])).

cnf(c_1427,plain,
    ( ~ r2_hidden(k4_tarski(sK0(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6))),sK1(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6)))),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6)))
    | r2_hidden(k4_tarski(sK0(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6))),sK1(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6)))),k4_relat_1(sK6)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1428,plain,
    ( r2_hidden(k4_tarski(sK0(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6))),sK1(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6)))),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6))) != iProver_top
    | r2_hidden(k4_tarski(sK0(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6))),sK1(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6)))),k4_relat_1(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1427])).

cnf(c_16,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1139,plain,
    ( v1_relat_1(k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6)))
    | ~ v1_relat_1(k4_relat_1(sK5)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1140,plain,
    ( v1_relat_1(k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6))) = iProver_top
    | v1_relat_1(k4_relat_1(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1139])).

cnf(c_877,plain,
    ( v1_relat_1(k3_xboole_0(sK5,sK6))
    | ~ v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_878,plain,
    ( v1_relat_1(k3_xboole_0(sK5,sK6)) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_877])).

cnf(c_831,plain,
    ( ~ v1_relat_1(k3_xboole_0(sK5,sK6))
    | v1_relat_1(k4_relat_1(k3_xboole_0(sK5,sK6))) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_832,plain,
    ( v1_relat_1(k3_xboole_0(sK5,sK6)) != iProver_top
    | v1_relat_1(k4_relat_1(k3_xboole_0(sK5,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_831])).

cnf(c_2,plain,
    ( r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)
    | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_790,plain,
    ( r2_hidden(k4_tarski(sK0(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6))),sK1(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6)))),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6)))
    | r2_hidden(k4_tarski(sK0(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6))),sK1(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6)))),k4_relat_1(k3_xboole_0(sK5,sK6)))
    | ~ v1_relat_1(k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6)))
    | ~ v1_relat_1(k4_relat_1(k3_xboole_0(sK5,sK6)))
    | k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6)) = k4_relat_1(k3_xboole_0(sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_791,plain,
    ( k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6)) = k4_relat_1(k3_xboole_0(sK5,sK6))
    | r2_hidden(k4_tarski(sK0(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6))),sK1(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6)))),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6))) = iProver_top
    | r2_hidden(k4_tarski(sK0(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6))),sK1(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6)))),k4_relat_1(k3_xboole_0(sK5,sK6))) = iProver_top
    | v1_relat_1(k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6))) != iProver_top
    | v1_relat_1(k4_relat_1(k3_xboole_0(sK5,sK6))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_790])).

cnf(c_1,plain,
    ( ~ r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)
    | ~ r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_787,plain,
    ( ~ r2_hidden(k4_tarski(sK0(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6))),sK1(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6)))),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6)))
    | ~ r2_hidden(k4_tarski(sK0(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6))),sK1(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6)))),k4_relat_1(k3_xboole_0(sK5,sK6)))
    | ~ v1_relat_1(k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6)))
    | ~ v1_relat_1(k4_relat_1(k3_xboole_0(sK5,sK6)))
    | k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6)) = k4_relat_1(k3_xboole_0(sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_788,plain,
    ( k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6)) = k4_relat_1(k3_xboole_0(sK5,sK6))
    | r2_hidden(k4_tarski(sK0(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6))),sK1(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6)))),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6))) != iProver_top
    | r2_hidden(k4_tarski(sK0(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6))),sK1(k4_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6)))),k4_relat_1(k3_xboole_0(sK5,sK6))) != iProver_top
    | v1_relat_1(k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6))) != iProver_top
    | v1_relat_1(k4_relat_1(k3_xboole_0(sK5,sK6))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_787])).

cnf(c_31,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_33,plain,
    ( v1_relat_1(k4_relat_1(sK5)) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_19,negated_conjecture,
    ( k3_xboole_0(k4_relat_1(sK5),k4_relat_1(sK6)) != k4_relat_1(k3_xboole_0(sK5,sK6)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_20,negated_conjecture,
    ( v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_23,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_21,negated_conjecture,
    ( v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_22,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5716,c_5713,c_5700,c_3818,c_3224,c_3209,c_3203,c_2347,c_2209,c_2193,c_2028,c_1431,c_1428,c_1140,c_878,c_832,c_791,c_788,c_33,c_19,c_23,c_22])).


%------------------------------------------------------------------------------
