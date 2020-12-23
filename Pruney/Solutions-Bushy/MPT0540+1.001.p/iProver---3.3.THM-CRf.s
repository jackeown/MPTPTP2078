%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0540+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:31 EST 2020

% Result     : Theorem 3.68s
% Output     : CNFRefutation 3.68s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 206 expanded)
%              Number of clauses        :   54 (  71 expanded)
%              Number of leaves         :    8 (  34 expanded)
%              Depth                    :   14
%              Number of atoms          :  483 (1481 expanded)
%              Number of equality atoms :   49 ( 158 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal clause size      :   16 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
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

fof(f8,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k8_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X1)
                  & r2_hidden(X4,X0) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

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
    inference(nnf_transformation,[],[f8])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f19,plain,(
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
    inference(rectify,[],[f18])).

fof(f20,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ( r2_hidden(k4_tarski(X3,X4),X1)
              & r2_hidden(X4,X0) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) )
        & ( ( r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X1)
                  | ~ r2_hidden(sK3(X0,X1,X2),X0)
                  | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) )
                & ( ( r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X1)
                    & r2_hidden(sK3(X0,X1,X2),X0) )
                  | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f19,f20])).

fof(f32,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X2)
      | ~ r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(X6,X0)
      | k8_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f43,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(X6,X0)
      | ~ v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f32])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( v1_relat_1(X2)
         => ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X0)
                    | ~ r2_hidden(X5,X1) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X0)
                      & r2_hidden(X5,X1) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f13])).

fof(f15,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ( r2_hidden(k4_tarski(X3,X4),X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2) )
        & ( ( r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X0)
            & r2_hidden(sK0(X0,X1,X2),X1) )
          | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X0)
                  | ~ r2_hidden(sK0(X0,X1,X2),X1)
                  | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2) )
                & ( ( r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X0)
                    & r2_hidden(sK0(X0,X1,X2),X1) )
                  | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X0)
                    | ~ r2_hidden(X5,X1) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X0)
                      & r2_hidden(X5,X1) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f15])).

fof(f26,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X2)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(X5,X1)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f40,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(X5,X1)
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f26])).

fof(f24,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f42,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f24])).

fof(f25,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f41,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f25])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f31,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k8_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f44,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1))
      | ~ v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f31])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f30,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(X6,X0)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k8_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f45,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X6,X0)
      | ~ r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1))
      | ~ v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f30])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X0,X1) = X2
      | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X0)
      | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( k7_relat_1(k8_relat_1(X0,X2),X1) != k8_relat_1(X0,k7_relat_1(X2,X1))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f22,plain,
    ( ? [X0,X1,X2] :
        ( k7_relat_1(k8_relat_1(X0,X2),X1) != k8_relat_1(X0,k7_relat_1(X2,X1))
        & v1_relat_1(X2) )
   => ( k7_relat_1(k8_relat_1(sK4,sK6),sK5) != k8_relat_1(sK4,k7_relat_1(sK6,sK5))
      & v1_relat_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( k7_relat_1(k8_relat_1(sK4,sK6),sK5) != k8_relat_1(sK4,k7_relat_1(sK6,sK5))
    & v1_relat_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f11,f22])).

fof(f39,plain,(
    k7_relat_1(k8_relat_1(sK4,sK6),sK5) != k8_relat_1(sK4,k7_relat_1(sK6,sK5)) ),
    inference(cnf_transformation,[],[f23])).

fof(f38,plain,(
    v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | r2_hidden(k4_tarski(X2,X0),k8_relat_1(X1,X3))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(k8_relat_1(X1,X3)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_180,plain,
    ( ~ r2_hidden(X0_41,X0_40)
    | ~ r2_hidden(k4_tarski(X1_41,X0_41),X1_40)
    | r2_hidden(k4_tarski(X1_41,X0_41),k8_relat_1(X0_40,X1_40))
    | ~ v1_relat_1(X1_40)
    | ~ v1_relat_1(k8_relat_1(X0_40,X1_40)) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_3444,plain,
    ( ~ r2_hidden(sK1(k8_relat_1(sK4,sK6),sK5,k8_relat_1(sK4,k7_relat_1(sK6,sK5))),sK4)
    | ~ r2_hidden(k4_tarski(X0_41,sK1(k8_relat_1(sK4,sK6),sK5,k8_relat_1(sK4,k7_relat_1(sK6,sK5)))),X0_40)
    | r2_hidden(k4_tarski(X0_41,sK1(k8_relat_1(sK4,sK6),sK5,k8_relat_1(sK4,k7_relat_1(sK6,sK5)))),k8_relat_1(sK4,X0_40))
    | ~ v1_relat_1(X0_40)
    | ~ v1_relat_1(k8_relat_1(sK4,X0_40)) ),
    inference(instantiation,[status(thm)],[c_180])).

cnf(c_5423,plain,
    ( ~ r2_hidden(sK1(k8_relat_1(sK4,sK6),sK5,k8_relat_1(sK4,k7_relat_1(sK6,sK5))),sK4)
    | ~ r2_hidden(k4_tarski(sK0(k8_relat_1(sK4,sK6),sK5,k8_relat_1(sK4,k7_relat_1(sK6,sK5))),sK1(k8_relat_1(sK4,sK6),sK5,k8_relat_1(sK4,k7_relat_1(sK6,sK5)))),X0_40)
    | r2_hidden(k4_tarski(sK0(k8_relat_1(sK4,sK6),sK5,k8_relat_1(sK4,k7_relat_1(sK6,sK5))),sK1(k8_relat_1(sK4,sK6),sK5,k8_relat_1(sK4,k7_relat_1(sK6,sK5)))),k8_relat_1(sK4,X0_40))
    | ~ v1_relat_1(X0_40)
    | ~ v1_relat_1(k8_relat_1(sK4,X0_40)) ),
    inference(instantiation,[status(thm)],[c_3444])).

cnf(c_8371,plain,
    ( ~ r2_hidden(sK1(k8_relat_1(sK4,sK6),sK5,k8_relat_1(sK4,k7_relat_1(sK6,sK5))),sK4)
    | r2_hidden(k4_tarski(sK0(k8_relat_1(sK4,sK6),sK5,k8_relat_1(sK4,k7_relat_1(sK6,sK5))),sK1(k8_relat_1(sK4,sK6),sK5,k8_relat_1(sK4,k7_relat_1(sK6,sK5)))),k8_relat_1(sK4,k7_relat_1(sK6,sK5)))
    | ~ r2_hidden(k4_tarski(sK0(k8_relat_1(sK4,sK6),sK5,k8_relat_1(sK4,k7_relat_1(sK6,sK5))),sK1(k8_relat_1(sK4,sK6),sK5,k8_relat_1(sK4,k7_relat_1(sK6,sK5)))),k7_relat_1(sK6,sK5))
    | ~ v1_relat_1(k8_relat_1(sK4,k7_relat_1(sK6,sK5)))
    | ~ v1_relat_1(k7_relat_1(sK6,sK5)) ),
    inference(instantiation,[status(thm)],[c_5423])).

cnf(c_3941,plain,
    ( ~ r2_hidden(sK1(k8_relat_1(sK4,sK6),sK5,k8_relat_1(sK4,k7_relat_1(sK6,sK5))),sK4)
    | r2_hidden(k4_tarski(sK0(k8_relat_1(sK4,sK6),sK5,k8_relat_1(sK4,k7_relat_1(sK6,sK5))),sK1(k8_relat_1(sK4,sK6),sK5,k8_relat_1(sK4,k7_relat_1(sK6,sK5)))),k8_relat_1(sK4,sK6))
    | ~ r2_hidden(k4_tarski(sK0(k8_relat_1(sK4,sK6),sK5,k8_relat_1(sK4,k7_relat_1(sK6,sK5))),sK1(k8_relat_1(sK4,sK6),sK5,k8_relat_1(sK4,k7_relat_1(sK6,sK5)))),sK6)
    | ~ v1_relat_1(k8_relat_1(sK4,sK6))
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_3444])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),X3)
    | r2_hidden(k4_tarski(X0,X2),k7_relat_1(X3,X1))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(k7_relat_1(X3,X1)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_186,plain,
    ( ~ r2_hidden(X0_41,X0_40)
    | ~ r2_hidden(k4_tarski(X0_41,X1_41),X1_40)
    | r2_hidden(k4_tarski(X0_41,X1_41),k7_relat_1(X1_40,X0_40))
    | ~ v1_relat_1(X1_40)
    | ~ v1_relat_1(k7_relat_1(X1_40,X0_40)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_998,plain,
    ( ~ r2_hidden(sK0(k8_relat_1(sK4,sK6),sK5,k8_relat_1(sK4,k7_relat_1(sK6,sK5))),sK5)
    | ~ r2_hidden(k4_tarski(sK0(k8_relat_1(sK4,sK6),sK5,k8_relat_1(sK4,k7_relat_1(sK6,sK5))),X0_41),X0_40)
    | r2_hidden(k4_tarski(sK0(k8_relat_1(sK4,sK6),sK5,k8_relat_1(sK4,k7_relat_1(sK6,sK5))),X0_41),k7_relat_1(X0_40,sK5))
    | ~ v1_relat_1(X0_40)
    | ~ v1_relat_1(k7_relat_1(X0_40,sK5)) ),
    inference(instantiation,[status(thm)],[c_186])).

cnf(c_3683,plain,
    ( ~ r2_hidden(sK0(k8_relat_1(sK4,sK6),sK5,k8_relat_1(sK4,k7_relat_1(sK6,sK5))),sK5)
    | ~ r2_hidden(k4_tarski(sK0(k8_relat_1(sK4,sK6),sK5,k8_relat_1(sK4,k7_relat_1(sK6,sK5))),sK1(k8_relat_1(sK4,sK6),sK5,k8_relat_1(sK4,k7_relat_1(sK6,sK5)))),X0_40)
    | r2_hidden(k4_tarski(sK0(k8_relat_1(sK4,sK6),sK5,k8_relat_1(sK4,k7_relat_1(sK6,sK5))),sK1(k8_relat_1(sK4,sK6),sK5,k8_relat_1(sK4,k7_relat_1(sK6,sK5)))),k7_relat_1(X0_40,sK5))
    | ~ v1_relat_1(X0_40)
    | ~ v1_relat_1(k7_relat_1(X0_40,sK5)) ),
    inference(instantiation,[status(thm)],[c_998])).

cnf(c_3686,plain,
    ( ~ r2_hidden(sK0(k8_relat_1(sK4,sK6),sK5,k8_relat_1(sK4,k7_relat_1(sK6,sK5))),sK5)
    | r2_hidden(k4_tarski(sK0(k8_relat_1(sK4,sK6),sK5,k8_relat_1(sK4,k7_relat_1(sK6,sK5))),sK1(k8_relat_1(sK4,sK6),sK5,k8_relat_1(sK4,k7_relat_1(sK6,sK5)))),k7_relat_1(sK6,sK5))
    | ~ r2_hidden(k4_tarski(sK0(k8_relat_1(sK4,sK6),sK5,k8_relat_1(sK4,k7_relat_1(sK6,sK5))),sK1(k8_relat_1(sK4,sK6),sK5,k8_relat_1(sK4,k7_relat_1(sK6,sK5)))),sK6)
    | ~ v1_relat_1(k7_relat_1(sK6,sK5))
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_3683])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),k7_relat_1(X3,X1))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(k7_relat_1(X3,X1)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_184,plain,
    ( r2_hidden(X0_41,X0_40)
    | ~ r2_hidden(k4_tarski(X0_41,X1_41),k7_relat_1(X1_40,X0_40))
    | ~ v1_relat_1(X1_40)
    | ~ v1_relat_1(k7_relat_1(X1_40,X0_40)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1674,plain,
    ( r2_hidden(sK0(X0_40,X1_40,X2_40),X3_40)
    | ~ r2_hidden(k4_tarski(sK0(X0_40,X1_40,X2_40),sK1(X0_40,X1_40,X2_40)),k7_relat_1(X4_40,X3_40))
    | ~ v1_relat_1(X4_40)
    | ~ v1_relat_1(k7_relat_1(X4_40,X3_40)) ),
    inference(instantiation,[status(thm)],[c_184])).

cnf(c_3440,plain,
    ( r2_hidden(sK0(k8_relat_1(sK4,sK6),sK5,k8_relat_1(sK4,k7_relat_1(sK6,sK5))),sK5)
    | ~ r2_hidden(k4_tarski(sK0(k8_relat_1(sK4,sK6),sK5,k8_relat_1(sK4,k7_relat_1(sK6,sK5))),sK1(k8_relat_1(sK4,sK6),sK5,k8_relat_1(sK4,k7_relat_1(sK6,sK5)))),k7_relat_1(sK6,sK5))
    | ~ v1_relat_1(k7_relat_1(sK6,sK5))
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_1674])).

cnf(c_4,plain,
    ( r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(X0,X1),k7_relat_1(X2,X3))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(k7_relat_1(X2,X3)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_185,plain,
    ( r2_hidden(k4_tarski(X0_41,X1_41),X0_40)
    | ~ r2_hidden(k4_tarski(X0_41,X1_41),k7_relat_1(X0_40,X1_40))
    | ~ v1_relat_1(X0_40)
    | ~ v1_relat_1(k7_relat_1(X0_40,X1_40)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_177,plain,
    ( ~ v1_relat_1(X0_40)
    | v1_relat_1(k7_relat_1(X0_40,X1_40)) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_270,plain,
    ( ~ v1_relat_1(X0_40)
    | ~ r2_hidden(k4_tarski(X0_41,X1_41),k7_relat_1(X0_40,X1_40))
    | r2_hidden(k4_tarski(X0_41,X1_41),X0_40) ),
    inference(global_propositional_subsumption,[status(thm)],[c_185,c_177])).

cnf(c_271,plain,
    ( r2_hidden(k4_tarski(X0_41,X1_41),X0_40)
    | ~ r2_hidden(k4_tarski(X0_41,X1_41),k7_relat_1(X0_40,X1_40))
    | ~ v1_relat_1(X0_40) ),
    inference(renaming,[status(thm)],[c_270])).

cnf(c_3437,plain,
    ( ~ r2_hidden(k4_tarski(sK0(k8_relat_1(sK4,sK6),sK5,k8_relat_1(sK4,k7_relat_1(sK6,sK5))),sK1(k8_relat_1(sK4,sK6),sK5,k8_relat_1(sK4,k7_relat_1(sK6,sK5)))),k7_relat_1(sK6,sK5))
    | r2_hidden(k4_tarski(sK0(k8_relat_1(sK4,sK6),sK5,k8_relat_1(sK4,k7_relat_1(sK6,sK5))),sK1(k8_relat_1(sK4,sK6),sK5,k8_relat_1(sK4,k7_relat_1(sK6,sK5)))),sK6)
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_271])).

cnf(c_10,plain,
    ( r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(X0,X1),k8_relat_1(X3,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(k8_relat_1(X3,X2)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_179,plain,
    ( r2_hidden(k4_tarski(X0_41,X1_41),X0_40)
    | ~ r2_hidden(k4_tarski(X0_41,X1_41),k8_relat_1(X1_40,X0_40))
    | ~ v1_relat_1(X0_40)
    | ~ v1_relat_1(k8_relat_1(X1_40,X0_40)) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k8_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_176,plain,
    ( ~ v1_relat_1(X0_40)
    | v1_relat_1(k8_relat_1(X1_40,X0_40)) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_282,plain,
    ( ~ v1_relat_1(X0_40)
    | ~ r2_hidden(k4_tarski(X0_41,X1_41),k8_relat_1(X1_40,X0_40))
    | r2_hidden(k4_tarski(X0_41,X1_41),X0_40) ),
    inference(global_propositional_subsumption,[status(thm)],[c_179,c_176])).

cnf(c_283,plain,
    ( r2_hidden(k4_tarski(X0_41,X1_41),X0_40)
    | ~ r2_hidden(k4_tarski(X0_41,X1_41),k8_relat_1(X1_40,X0_40))
    | ~ v1_relat_1(X0_40) ),
    inference(renaming,[status(thm)],[c_282])).

cnf(c_781,plain,
    ( r2_hidden(k4_tarski(sK0(X0_40,X1_40,k8_relat_1(X2_40,X3_40)),sK1(X0_40,X1_40,k8_relat_1(X2_40,X3_40))),X3_40)
    | ~ r2_hidden(k4_tarski(sK0(X0_40,X1_40,k8_relat_1(X2_40,X3_40)),sK1(X0_40,X1_40,k8_relat_1(X2_40,X3_40))),k8_relat_1(X2_40,X3_40))
    | ~ v1_relat_1(X3_40) ),
    inference(instantiation,[status(thm)],[c_283])).

cnf(c_2264,plain,
    ( ~ r2_hidden(k4_tarski(sK0(k8_relat_1(sK4,sK6),sK5,k8_relat_1(sK4,k7_relat_1(sK6,sK5))),sK1(k8_relat_1(sK4,sK6),sK5,k8_relat_1(sK4,k7_relat_1(sK6,sK5)))),k8_relat_1(sK4,k7_relat_1(sK6,sK5)))
    | r2_hidden(k4_tarski(sK0(k8_relat_1(sK4,sK6),sK5,k8_relat_1(sK4,k7_relat_1(sK6,sK5))),sK1(k8_relat_1(sK4,sK6),sK5,k8_relat_1(sK4,k7_relat_1(sK6,sK5)))),k7_relat_1(sK6,sK5))
    | ~ v1_relat_1(k7_relat_1(sK6,sK5)) ),
    inference(instantiation,[status(thm)],[c_781])).

cnf(c_11,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k8_relat_1(X1,X3))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(k8_relat_1(X1,X3)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_178,plain,
    ( r2_hidden(X0_41,X0_40)
    | ~ r2_hidden(k4_tarski(X1_41,X0_41),k8_relat_1(X0_40,X1_40))
    | ~ v1_relat_1(X1_40)
    | ~ v1_relat_1(k8_relat_1(X0_40,X1_40)) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_709,plain,
    ( r2_hidden(sK1(X0_40,X1_40,k8_relat_1(X2_40,X3_40)),X2_40)
    | ~ r2_hidden(k4_tarski(sK0(X0_40,X1_40,k8_relat_1(X2_40,X3_40)),sK1(X0_40,X1_40,k8_relat_1(X2_40,X3_40))),k8_relat_1(X2_40,X3_40))
    | ~ v1_relat_1(X3_40)
    | ~ v1_relat_1(k8_relat_1(X2_40,X3_40)) ),
    inference(instantiation,[status(thm)],[c_178])).

cnf(c_2265,plain,
    ( r2_hidden(sK1(k8_relat_1(sK4,sK6),sK5,k8_relat_1(sK4,k7_relat_1(sK6,sK5))),sK4)
    | ~ r2_hidden(k4_tarski(sK0(k8_relat_1(sK4,sK6),sK5,k8_relat_1(sK4,k7_relat_1(sK6,sK5))),sK1(k8_relat_1(sK4,sK6),sK5,k8_relat_1(sK4,k7_relat_1(sK6,sK5)))),k8_relat_1(sK4,k7_relat_1(sK6,sK5)))
    | ~ v1_relat_1(k8_relat_1(sK4,k7_relat_1(sK6,sK5)))
    | ~ v1_relat_1(k7_relat_1(sK6,sK5)) ),
    inference(instantiation,[status(thm)],[c_709])).

cnf(c_2073,plain,
    ( v1_relat_1(k8_relat_1(sK4,k7_relat_1(sK6,sK5)))
    | ~ v1_relat_1(k7_relat_1(sK6,sK5)) ),
    inference(instantiation,[status(thm)],[c_176])).

cnf(c_1564,plain,
    ( v1_relat_1(k8_relat_1(sK4,sK6))
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_176])).

cnf(c_1042,plain,
    ( v1_relat_1(k7_relat_1(sK6,sK5))
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_177])).

cnf(c_1019,plain,
    ( ~ r2_hidden(k4_tarski(sK0(k8_relat_1(sK4,sK6),sK5,k8_relat_1(sK4,k7_relat_1(sK6,sK5))),sK1(k8_relat_1(sK4,sK6),sK5,k8_relat_1(sK4,k7_relat_1(sK6,sK5)))),k8_relat_1(sK4,sK6))
    | r2_hidden(k4_tarski(sK0(k8_relat_1(sK4,sK6),sK5,k8_relat_1(sK4,k7_relat_1(sK6,sK5))),sK1(k8_relat_1(sK4,sK6),sK5,k8_relat_1(sK4,k7_relat_1(sK6,sK5)))),sK6)
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_283])).

cnf(c_1016,plain,
    ( r2_hidden(sK1(k8_relat_1(sK4,sK6),sK5,k8_relat_1(sK4,k7_relat_1(sK6,sK5))),sK4)
    | ~ r2_hidden(k4_tarski(sK0(k8_relat_1(sK4,sK6),sK5,k8_relat_1(sK4,k7_relat_1(sK6,sK5))),sK1(k8_relat_1(sK4,sK6),sK5,k8_relat_1(sK4,k7_relat_1(sK6,sK5)))),k8_relat_1(sK4,sK6))
    | ~ v1_relat_1(k8_relat_1(sK4,sK6))
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_178])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X0)
    | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_189,plain,
    ( ~ r2_hidden(sK0(X0_40,X1_40,X2_40),X1_40)
    | ~ r2_hidden(k4_tarski(sK0(X0_40,X1_40,X2_40),sK1(X0_40,X1_40,X2_40)),X0_40)
    | ~ r2_hidden(k4_tarski(sK0(X0_40,X1_40,X2_40),sK1(X0_40,X1_40,X2_40)),X2_40)
    | ~ v1_relat_1(X0_40)
    | ~ v1_relat_1(X2_40)
    | k7_relat_1(X0_40,X1_40) = X2_40 ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1013,plain,
    ( ~ r2_hidden(sK0(k8_relat_1(sK4,sK6),sK5,k8_relat_1(sK4,k7_relat_1(sK6,sK5))),sK5)
    | ~ r2_hidden(k4_tarski(sK0(k8_relat_1(sK4,sK6),sK5,k8_relat_1(sK4,k7_relat_1(sK6,sK5))),sK1(k8_relat_1(sK4,sK6),sK5,k8_relat_1(sK4,k7_relat_1(sK6,sK5)))),k8_relat_1(sK4,k7_relat_1(sK6,sK5)))
    | ~ r2_hidden(k4_tarski(sK0(k8_relat_1(sK4,sK6),sK5,k8_relat_1(sK4,k7_relat_1(sK6,sK5))),sK1(k8_relat_1(sK4,sK6),sK5,k8_relat_1(sK4,k7_relat_1(sK6,sK5)))),k8_relat_1(sK4,sK6))
    | ~ v1_relat_1(k8_relat_1(sK4,k7_relat_1(sK6,sK5)))
    | ~ v1_relat_1(k8_relat_1(sK4,sK6))
    | k7_relat_1(k8_relat_1(sK4,sK6),sK5) = k8_relat_1(sK4,k7_relat_1(sK6,sK5)) ),
    inference(instantiation,[status(thm)],[c_189])).

cnf(c_1,plain,
    ( r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X0)
    | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_188,plain,
    ( r2_hidden(k4_tarski(sK0(X0_40,X1_40,X2_40),sK1(X0_40,X1_40,X2_40)),X2_40)
    | r2_hidden(k4_tarski(sK0(X0_40,X1_40,X2_40),sK1(X0_40,X1_40,X2_40)),X0_40)
    | ~ v1_relat_1(X0_40)
    | ~ v1_relat_1(X2_40)
    | k7_relat_1(X0_40,X1_40) = X2_40 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_780,plain,
    ( r2_hidden(k4_tarski(sK0(X0_40,X1_40,k8_relat_1(X2_40,X3_40)),sK1(X0_40,X1_40,k8_relat_1(X2_40,X3_40))),X0_40)
    | r2_hidden(k4_tarski(sK0(X0_40,X1_40,k8_relat_1(X2_40,X3_40)),sK1(X0_40,X1_40,k8_relat_1(X2_40,X3_40))),k8_relat_1(X2_40,X3_40))
    | ~ v1_relat_1(X0_40)
    | ~ v1_relat_1(k8_relat_1(X2_40,X3_40))
    | k7_relat_1(X0_40,X1_40) = k8_relat_1(X2_40,X3_40) ),
    inference(instantiation,[status(thm)],[c_188])).

cnf(c_919,plain,
    ( r2_hidden(k4_tarski(sK0(k8_relat_1(sK4,sK6),sK5,k8_relat_1(sK4,k7_relat_1(sK6,sK5))),sK1(k8_relat_1(sK4,sK6),sK5,k8_relat_1(sK4,k7_relat_1(sK6,sK5)))),k8_relat_1(sK4,k7_relat_1(sK6,sK5)))
    | r2_hidden(k4_tarski(sK0(k8_relat_1(sK4,sK6),sK5,k8_relat_1(sK4,k7_relat_1(sK6,sK5))),sK1(k8_relat_1(sK4,sK6),sK5,k8_relat_1(sK4,k7_relat_1(sK6,sK5)))),k8_relat_1(sK4,sK6))
    | ~ v1_relat_1(k8_relat_1(sK4,k7_relat_1(sK6,sK5)))
    | ~ v1_relat_1(k8_relat_1(sK4,sK6))
    | k7_relat_1(k8_relat_1(sK4,sK6),sK5) = k8_relat_1(sK4,k7_relat_1(sK6,sK5)) ),
    inference(instantiation,[status(thm)],[c_780])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_187,plain,
    ( r2_hidden(sK0(X0_40,X1_40,X2_40),X1_40)
    | r2_hidden(k4_tarski(sK0(X0_40,X1_40,X2_40),sK1(X0_40,X1_40,X2_40)),X2_40)
    | ~ v1_relat_1(X0_40)
    | ~ v1_relat_1(X2_40)
    | k7_relat_1(X0_40,X1_40) = X2_40 ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_708,plain,
    ( r2_hidden(sK0(X0_40,X1_40,k8_relat_1(X2_40,X3_40)),X1_40)
    | r2_hidden(k4_tarski(sK0(X0_40,X1_40,k8_relat_1(X2_40,X3_40)),sK1(X0_40,X1_40,k8_relat_1(X2_40,X3_40))),k8_relat_1(X2_40,X3_40))
    | ~ v1_relat_1(X0_40)
    | ~ v1_relat_1(k8_relat_1(X2_40,X3_40))
    | k7_relat_1(X0_40,X1_40) = k8_relat_1(X2_40,X3_40) ),
    inference(instantiation,[status(thm)],[c_187])).

cnf(c_898,plain,
    ( r2_hidden(sK0(k8_relat_1(sK4,sK6),sK5,k8_relat_1(sK4,k7_relat_1(sK6,sK5))),sK5)
    | r2_hidden(k4_tarski(sK0(k8_relat_1(sK4,sK6),sK5,k8_relat_1(sK4,k7_relat_1(sK6,sK5))),sK1(k8_relat_1(sK4,sK6),sK5,k8_relat_1(sK4,k7_relat_1(sK6,sK5)))),k8_relat_1(sK4,k7_relat_1(sK6,sK5)))
    | ~ v1_relat_1(k8_relat_1(sK4,k7_relat_1(sK6,sK5)))
    | ~ v1_relat_1(k8_relat_1(sK4,sK6))
    | k7_relat_1(k8_relat_1(sK4,sK6),sK5) = k8_relat_1(sK4,k7_relat_1(sK6,sK5)) ),
    inference(instantiation,[status(thm)],[c_708])).

cnf(c_14,negated_conjecture,
    ( k7_relat_1(k8_relat_1(sK4,sK6),sK5) != k8_relat_1(sK4,k7_relat_1(sK6,sK5)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_175,negated_conjecture,
    ( k7_relat_1(k8_relat_1(sK4,sK6),sK5) != k8_relat_1(sK4,k7_relat_1(sK6,sK5)) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_15,negated_conjecture,
    ( v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f38])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8371,c_3941,c_3686,c_3440,c_3437,c_2264,c_2265,c_2073,c_1564,c_1042,c_1019,c_1016,c_1013,c_919,c_898,c_175,c_15])).


%------------------------------------------------------------------------------
