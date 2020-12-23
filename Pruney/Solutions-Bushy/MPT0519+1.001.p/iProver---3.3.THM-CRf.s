%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0519+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:29 EST 2020

% Result     : Theorem 3.21s
% Output     : CNFRefutation 3.21s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 127 expanded)
%              Number of clauses        :   38 (  39 expanded)
%              Number of leaves         :   13 (  29 expanded)
%              Depth                    :   12
%              Number of atoms          :  392 ( 733 expanded)
%              Number of equality atoms :   82 ( 131 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
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

fof(f26,plain,(
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
    inference(rectify,[],[f25])).

fof(f29,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK5(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK4(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
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

fof(f30,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f26,f29,f28,f27])).

fof(f47,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f60,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X6,X5),X0) ) ),
    inference(equality_resolution,[],[f47])).

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

fof(f10,plain,(
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

fof(f15,plain,(
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
    inference(nnf_transformation,[],[f10])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f17,plain,(
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
    inference(rectify,[],[f16])).

fof(f18,plain,(
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

fof(f19,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f18])).

fof(f35,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X2)
      | ~ r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(X6,X0)
      | k8_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f54,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(X6,X0)
      | ~ v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f35])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f33,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(X6,X0)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k8_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f56,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X6,X0)
      | ~ r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1))
      | ~ v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f33])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f46,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f61,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK5(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f46])).

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
     => ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X0)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(sK2(X0,X1,X2),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f22,f23])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X0)
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k2_relat_1(X1),X0) = k2_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k3_xboole_0(k2_relat_1(X1),X0) = k2_relat_1(k8_relat_1(X0,X1)) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f14,plain,(
    ? [X0,X1] :
      ( k3_xboole_0(k2_relat_1(X1),X0) != k2_relat_1(k8_relat_1(X0,X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f31,plain,
    ( ? [X0,X1] :
        ( k3_xboole_0(k2_relat_1(X1),X0) != k2_relat_1(k8_relat_1(X0,X1))
        & v1_relat_1(X1) )
   => ( k3_xboole_0(k2_relat_1(sK7),sK6) != k2_relat_1(k8_relat_1(sK6,sK7))
      & v1_relat_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( k3_xboole_0(k2_relat_1(sK7),sK6) != k2_relat_1(k8_relat_1(sK6,sK7))
    & v1_relat_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f14,f31])).

fof(f53,plain,(
    k3_xboole_0(k2_relat_1(sK7),sK6) != k2_relat_1(k8_relat_1(sK6,sK7)) ),
    inference(cnf_transformation,[],[f32])).

fof(f52,plain,(
    v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_15,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_3032,plain,
    ( r2_hidden(sK2(k2_relat_1(sK7),sK6,k2_relat_1(k8_relat_1(sK6,sK7))),k2_relat_1(k8_relat_1(sK6,sK7)))
    | ~ r2_hidden(k4_tarski(sK5(sK7,sK2(k2_relat_1(sK7),sK6,k2_relat_1(k8_relat_1(sK6,sK7)))),sK2(k2_relat_1(sK7),sK6,k2_relat_1(k8_relat_1(sK6,sK7)))),k8_relat_1(sK6,sK7)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_3033,plain,
    ( r2_hidden(sK2(k2_relat_1(sK7),sK6,k2_relat_1(k8_relat_1(sK6,sK7))),k2_relat_1(k8_relat_1(sK6,sK7))) = iProver_top
    | r2_hidden(k4_tarski(sK5(sK7,sK2(k2_relat_1(sK7),sK6,k2_relat_1(k8_relat_1(sK6,sK7)))),sK2(k2_relat_1(sK7),sK6,k2_relat_1(k8_relat_1(sK6,sK7)))),k8_relat_1(sK6,sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3032])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | r2_hidden(k4_tarski(X2,X0),k8_relat_1(X1,X3))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(k8_relat_1(X1,X3)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_906,plain,
    ( ~ r2_hidden(sK2(k2_relat_1(sK7),sK6,k2_relat_1(k8_relat_1(sK6,sK7))),sK6)
    | ~ r2_hidden(k4_tarski(X0,sK2(k2_relat_1(sK7),sK6,k2_relat_1(k8_relat_1(sK6,sK7)))),X1)
    | r2_hidden(k4_tarski(X0,sK2(k2_relat_1(sK7),sK6,k2_relat_1(k8_relat_1(sK6,sK7)))),k8_relat_1(sK6,X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(k8_relat_1(sK6,X1)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1907,plain,
    ( ~ r2_hidden(sK2(k2_relat_1(sK7),sK6,k2_relat_1(k8_relat_1(sK6,sK7))),sK6)
    | r2_hidden(k4_tarski(sK5(sK7,sK2(k2_relat_1(sK7),sK6,k2_relat_1(k8_relat_1(sK6,sK7)))),sK2(k2_relat_1(sK7),sK6,k2_relat_1(k8_relat_1(sK6,sK7)))),k8_relat_1(sK6,sK7))
    | ~ r2_hidden(k4_tarski(sK5(sK7,sK2(k2_relat_1(sK7),sK6,k2_relat_1(k8_relat_1(sK6,sK7)))),sK2(k2_relat_1(sK7),sK6,k2_relat_1(k8_relat_1(sK6,sK7)))),sK7)
    | ~ v1_relat_1(k8_relat_1(sK6,sK7))
    | ~ v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_906])).

cnf(c_1908,plain,
    ( r2_hidden(sK2(k2_relat_1(sK7),sK6,k2_relat_1(k8_relat_1(sK6,sK7))),sK6) != iProver_top
    | r2_hidden(k4_tarski(sK5(sK7,sK2(k2_relat_1(sK7),sK6,k2_relat_1(k8_relat_1(sK6,sK7)))),sK2(k2_relat_1(sK7),sK6,k2_relat_1(k8_relat_1(sK6,sK7)))),k8_relat_1(sK6,sK7)) = iProver_top
    | r2_hidden(k4_tarski(sK5(sK7,sK2(k2_relat_1(sK7),sK6,k2_relat_1(k8_relat_1(sK6,sK7)))),sK2(k2_relat_1(sK7),sK6,k2_relat_1(k8_relat_1(sK6,sK7)))),sK7) != iProver_top
    | v1_relat_1(k8_relat_1(sK6,sK7)) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1907])).

cnf(c_17,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k8_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1375,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k8_relat_1(sK6,X0)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1376,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k8_relat_1(sK6,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1375])).

cnf(c_1378,plain,
    ( v1_relat_1(k8_relat_1(sK6,sK7)) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1376])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k8_relat_1(X1,X3))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(k8_relat_1(X1,X3)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1011,plain,
    ( r2_hidden(sK2(k2_relat_1(sK7),sK6,k2_relat_1(k8_relat_1(sK6,sK7))),sK6)
    | ~ r2_hidden(k4_tarski(sK5(k8_relat_1(sK6,sK7),sK2(k2_relat_1(sK7),sK6,k2_relat_1(k8_relat_1(sK6,sK7)))),sK2(k2_relat_1(sK7),sK6,k2_relat_1(k8_relat_1(sK6,sK7)))),k8_relat_1(sK6,sK7))
    | ~ v1_relat_1(k8_relat_1(sK6,sK7))
    | ~ v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1012,plain,
    ( r2_hidden(sK2(k2_relat_1(sK7),sK6,k2_relat_1(k8_relat_1(sK6,sK7))),sK6) = iProver_top
    | r2_hidden(k4_tarski(sK5(k8_relat_1(sK6,sK7),sK2(k2_relat_1(sK7),sK6,k2_relat_1(k8_relat_1(sK6,sK7)))),sK2(k2_relat_1(sK7),sK6,k2_relat_1(k8_relat_1(sK6,sK7)))),k8_relat_1(sK6,sK7)) != iProver_top
    | v1_relat_1(k8_relat_1(sK6,sK7)) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1011])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_18,plain,
    ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_229,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ v1_relat_1(X3)
    | k2_relat_1(X3) != X2
    | k2_relat_1(k8_relat_1(X4,X3)) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_18])).

cnf(c_230,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | ~ r2_hidden(X0,k2_relat_1(k8_relat_1(X2,X1)))
    | ~ v1_relat_1(X1) ),
    inference(unflattening,[status(thm)],[c_229])).

cnf(c_963,plain,
    ( ~ r2_hidden(sK2(k2_relat_1(sK7),sK6,k2_relat_1(k8_relat_1(sK6,sK7))),k2_relat_1(k8_relat_1(sK6,sK7)))
    | r2_hidden(sK2(k2_relat_1(sK7),sK6,k2_relat_1(k8_relat_1(sK6,sK7))),k2_relat_1(sK7))
    | ~ v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_230])).

cnf(c_964,plain,
    ( r2_hidden(sK2(k2_relat_1(sK7),sK6,k2_relat_1(k8_relat_1(sK6,sK7))),k2_relat_1(k8_relat_1(sK6,sK7))) != iProver_top
    | r2_hidden(sK2(k2_relat_1(sK7),sK6,k2_relat_1(k8_relat_1(sK6,sK7))),k2_relat_1(sK7)) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_963])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(k4_tarski(sK5(X1,X0),X0),X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_960,plain,
    ( ~ r2_hidden(sK2(k2_relat_1(sK7),sK6,k2_relat_1(k8_relat_1(sK6,sK7))),k2_relat_1(k8_relat_1(sK6,sK7)))
    | r2_hidden(k4_tarski(sK5(k8_relat_1(sK6,sK7),sK2(k2_relat_1(sK7),sK6,k2_relat_1(k8_relat_1(sK6,sK7)))),sK2(k2_relat_1(sK7),sK6,k2_relat_1(k8_relat_1(sK6,sK7)))),k8_relat_1(sK6,sK7)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_961,plain,
    ( r2_hidden(sK2(k2_relat_1(sK7),sK6,k2_relat_1(k8_relat_1(sK6,sK7))),k2_relat_1(k8_relat_1(sK6,sK7))) != iProver_top
    | r2_hidden(k4_tarski(sK5(k8_relat_1(sK6,sK7),sK2(k2_relat_1(sK7),sK6,k2_relat_1(k8_relat_1(sK6,sK7)))),sK2(k2_relat_1(sK7),sK6,k2_relat_1(k8_relat_1(sK6,sK7)))),k8_relat_1(sK6,sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_960])).

cnf(c_942,plain,
    ( ~ r2_hidden(sK2(k2_relat_1(sK7),sK6,k2_relat_1(k8_relat_1(sK6,sK7))),k2_relat_1(sK7))
    | r2_hidden(k4_tarski(sK5(sK7,sK2(k2_relat_1(sK7),sK6,k2_relat_1(k8_relat_1(sK6,sK7)))),sK2(k2_relat_1(sK7),sK6,k2_relat_1(k8_relat_1(sK6,sK7)))),sK7) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_943,plain,
    ( r2_hidden(sK2(k2_relat_1(sK7),sK6,k2_relat_1(k8_relat_1(sK6,sK7))),k2_relat_1(sK7)) != iProver_top
    | r2_hidden(k4_tarski(sK5(sK7,sK2(k2_relat_1(sK7),sK6,k2_relat_1(k8_relat_1(sK6,sK7)))),sK2(k2_relat_1(sK7),sK6,k2_relat_1(k8_relat_1(sK6,sK7)))),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_942])).

cnf(c_7,plain,
    ( ~ r2_hidden(sK2(X0,X1,X2),X1)
    | ~ r2_hidden(sK2(X0,X1,X2),X0)
    | ~ r2_hidden(sK2(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_903,plain,
    ( ~ r2_hidden(sK2(k2_relat_1(sK7),sK6,k2_relat_1(k8_relat_1(sK6,sK7))),k2_relat_1(k8_relat_1(sK6,sK7)))
    | ~ r2_hidden(sK2(k2_relat_1(sK7),sK6,k2_relat_1(k8_relat_1(sK6,sK7))),k2_relat_1(sK7))
    | ~ r2_hidden(sK2(k2_relat_1(sK7),sK6,k2_relat_1(k8_relat_1(sK6,sK7))),sK6)
    | k3_xboole_0(k2_relat_1(sK7),sK6) = k2_relat_1(k8_relat_1(sK6,sK7)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_904,plain,
    ( k3_xboole_0(k2_relat_1(sK7),sK6) = k2_relat_1(k8_relat_1(sK6,sK7))
    | r2_hidden(sK2(k2_relat_1(sK7),sK6,k2_relat_1(k8_relat_1(sK6,sK7))),k2_relat_1(k8_relat_1(sK6,sK7))) != iProver_top
    | r2_hidden(sK2(k2_relat_1(sK7),sK6,k2_relat_1(k8_relat_1(sK6,sK7))),k2_relat_1(sK7)) != iProver_top
    | r2_hidden(sK2(k2_relat_1(sK7),sK6,k2_relat_1(k8_relat_1(sK6,sK7))),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_903])).

cnf(c_9,plain,
    ( r2_hidden(sK2(X0,X1,X2),X0)
    | r2_hidden(sK2(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_900,plain,
    ( r2_hidden(sK2(k2_relat_1(sK7),sK6,k2_relat_1(k8_relat_1(sK6,sK7))),k2_relat_1(k8_relat_1(sK6,sK7)))
    | r2_hidden(sK2(k2_relat_1(sK7),sK6,k2_relat_1(k8_relat_1(sK6,sK7))),k2_relat_1(sK7))
    | k3_xboole_0(k2_relat_1(sK7),sK6) = k2_relat_1(k8_relat_1(sK6,sK7)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_901,plain,
    ( k3_xboole_0(k2_relat_1(sK7),sK6) = k2_relat_1(k8_relat_1(sK6,sK7))
    | r2_hidden(sK2(k2_relat_1(sK7),sK6,k2_relat_1(k8_relat_1(sK6,sK7))),k2_relat_1(k8_relat_1(sK6,sK7))) = iProver_top
    | r2_hidden(sK2(k2_relat_1(sK7),sK6,k2_relat_1(k8_relat_1(sK6,sK7))),k2_relat_1(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_900])).

cnf(c_8,plain,
    ( r2_hidden(sK2(X0,X1,X2),X1)
    | r2_hidden(sK2(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_897,plain,
    ( r2_hidden(sK2(k2_relat_1(sK7),sK6,k2_relat_1(k8_relat_1(sK6,sK7))),k2_relat_1(k8_relat_1(sK6,sK7)))
    | r2_hidden(sK2(k2_relat_1(sK7),sK6,k2_relat_1(k8_relat_1(sK6,sK7))),sK6)
    | k3_xboole_0(k2_relat_1(sK7),sK6) = k2_relat_1(k8_relat_1(sK6,sK7)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_898,plain,
    ( k3_xboole_0(k2_relat_1(sK7),sK6) = k2_relat_1(k8_relat_1(sK6,sK7))
    | r2_hidden(sK2(k2_relat_1(sK7),sK6,k2_relat_1(k8_relat_1(sK6,sK7))),k2_relat_1(k8_relat_1(sK6,sK7))) = iProver_top
    | r2_hidden(sK2(k2_relat_1(sK7),sK6,k2_relat_1(k8_relat_1(sK6,sK7))),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_897])).

cnf(c_19,negated_conjecture,
    ( k3_xboole_0(k2_relat_1(sK7),sK6) != k2_relat_1(k8_relat_1(sK6,sK7)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_20,negated_conjecture,
    ( v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_21,plain,
    ( v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3033,c_1908,c_1378,c_1012,c_964,c_961,c_943,c_904,c_901,c_898,c_19,c_21])).


%------------------------------------------------------------------------------
