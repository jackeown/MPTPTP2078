%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:45:41 EST 2020

% Result     : Theorem 3.54s
% Output     : CNFRefutation 3.54s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 233 expanded)
%              Number of clauses        :   56 (  81 expanded)
%              Number of leaves         :   11 (  50 expanded)
%              Depth                    :   15
%              Number of atoms          :  385 (1158 expanded)
%              Number of equality atoms :   49 (  94 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
             => r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X1)
              | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                & r2_hidden(k4_tarski(X2,X3),X0) ) )
          & ( ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
                | ~ r2_hidden(k4_tarski(X2,X3),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                & r2_hidden(k4_tarski(X2,X3),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f19])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(k4_tarski(X2,X3),X1)
          & r2_hidden(k4_tarski(X2,X3),X0) )
     => ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
        & r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
              & r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f20,f21])).

fof(f32,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r2_hidden(k4_tarski(X4,X5),X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f14,plain,(
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
    inference(flattening,[],[f14])).

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
    inference(rectify,[],[f15])).

fof(f17,plain,(
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

fof(f18,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f17])).

fof(f28,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X2)
      | ~ r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(X6,X0)
      | k8_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f42,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(X6,X0)
      | ~ v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f28])).

fof(f27,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k8_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f43,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1))
      | ~ v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f27])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( ( r1_tarski(X0,X1)
              & r1_tarski(X2,X3) )
           => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ! [X3] :
            ( v1_relat_1(X3)
           => ( ( r1_tarski(X0,X1)
                & r1_tarski(X2,X3) )
             => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
     => ( ~ r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,sK7))
        & r1_tarski(X0,X1)
        & r1_tarski(X2,sK7)
        & v1_relat_1(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3))
            & r1_tarski(X0,X1)
            & r1_tarski(X2,X3)
            & v1_relat_1(X3) )
        & v1_relat_1(X2) )
   => ( ? [X3] :
          ( ~ r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,X3))
          & r1_tarski(sK4,sK5)
          & r1_tarski(sK6,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ~ r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))
    & r1_tarski(sK4,sK5)
    & r1_tarski(sK6,sK7)
    & v1_relat_1(sK7)
    & v1_relat_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f13,f24,f23])).

fof(f38,plain,(
    v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f25])).

fof(f40,plain,(
    r1_tarski(sK4,sK5) ),
    inference(cnf_transformation,[],[f25])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f26,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(X6,X0)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k8_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f44,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X6,X0)
      | ~ r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1))
      | ~ v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f26])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f41,plain,(
    ~ r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)) ),
    inference(cnf_transformation,[],[f25])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f39,plain,(
    r1_tarski(sK6,sK7) ),
    inference(cnf_transformation,[],[f25])).

fof(f37,plain,(
    v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X3),X0)
    | r2_hidden(k4_tarski(X2,X3),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_368,plain,
    ( ~ r1_tarski(X0_41,X1_41)
    | ~ r2_hidden(k4_tarski(X0_43,X0_42),X0_41)
    | r2_hidden(k4_tarski(X0_43,X0_42),X1_41)
    | ~ v1_relat_1(X0_41) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1034,plain,
    ( ~ r1_tarski(sK6,X0_41)
    | r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),X0_41)
    | ~ r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),sK6)
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_368])).

cnf(c_14973,plain,
    ( ~ r1_tarski(sK6,sK7)
    | r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),sK7)
    | ~ r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),sK6)
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_1034])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | r2_hidden(k4_tarski(X2,X0),k8_relat_1(X1,X3))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(k8_relat_1(X1,X3)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_373,plain,
    ( ~ r2_hidden(X0_42,X0_41)
    | ~ r2_hidden(k4_tarski(X0_43,X0_42),X1_41)
    | r2_hidden(k4_tarski(X0_43,X0_42),k8_relat_1(X0_41,X1_41))
    | ~ v1_relat_1(X1_41)
    | ~ v1_relat_1(k8_relat_1(X0_41,X1_41)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1025,plain,
    ( ~ r2_hidden(sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK4)
    | ~ r2_hidden(k4_tarski(X0_43,sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),X0_41)
    | r2_hidden(k4_tarski(X0_43,sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),k8_relat_1(sK4,X0_41))
    | ~ v1_relat_1(X0_41)
    | ~ v1_relat_1(k8_relat_1(sK4,X0_41)) ),
    inference(instantiation,[status(thm)],[c_373])).

cnf(c_1483,plain,
    ( ~ r2_hidden(sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK4)
    | ~ r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),X0_41)
    | r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),k8_relat_1(sK4,X0_41))
    | ~ v1_relat_1(X0_41)
    | ~ v1_relat_1(k8_relat_1(sK4,X0_41)) ),
    inference(instantiation,[status(thm)],[c_1025])).

cnf(c_7099,plain,
    ( ~ r2_hidden(sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK4)
    | r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),k8_relat_1(sK4,sK7))
    | ~ r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),sK7)
    | ~ v1_relat_1(k8_relat_1(sK4,sK7))
    | ~ v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_1483])).

cnf(c_384,plain,
    ( ~ r2_hidden(X0_42,X0_41)
    | r2_hidden(X1_42,X1_41)
    | X1_42 != X0_42
    | X1_41 != X0_41 ),
    theory(equality)).

cnf(c_1077,plain,
    ( r2_hidden(X0_42,X0_41)
    | ~ r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),X1_41)
    | X0_42 != k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)))
    | X0_41 != X1_41 ),
    inference(instantiation,[status(thm)],[c_384])).

cnf(c_1584,plain,
    ( ~ r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),X0_41)
    | r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),X1_41)
    | k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))) != k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)))
    | X1_41 != X0_41 ),
    inference(instantiation,[status(thm)],[c_1077])).

cnf(c_2449,plain,
    ( ~ r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),X0_41)
    | r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),k8_relat_1(X1_41,k8_relat_1(sK5,sK7)))
    | k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))) != k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)))
    | k8_relat_1(X1_41,k8_relat_1(sK5,sK7)) != X0_41 ),
    inference(instantiation,[status(thm)],[c_1584])).

cnf(c_5132,plain,
    ( r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),k8_relat_1(X0_41,k8_relat_1(sK5,sK7)))
    | ~ r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),k8_relat_1(X0_41,sK7))
    | k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))) != k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)))
    | k8_relat_1(X0_41,k8_relat_1(sK5,sK7)) != k8_relat_1(X0_41,sK7) ),
    inference(instantiation,[status(thm)],[c_2449])).

cnf(c_7098,plain,
    ( r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),k8_relat_1(sK4,k8_relat_1(sK5,sK7)))
    | ~ r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),k8_relat_1(sK4,sK7))
    | k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))) != k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)))
    | k8_relat_1(sK4,k8_relat_1(sK5,sK7)) != k8_relat_1(sK4,sK7) ),
    inference(instantiation,[status(thm)],[c_5132])).

cnf(c_4,plain,
    ( r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(X0,X1),k8_relat_1(X3,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(k8_relat_1(X3,X2)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_372,plain,
    ( r2_hidden(k4_tarski(X0_43,X0_42),X0_41)
    | ~ r2_hidden(k4_tarski(X0_43,X0_42),k8_relat_1(X1_41,X0_41))
    | ~ v1_relat_1(X0_41)
    | ~ v1_relat_1(k8_relat_1(X1_41,X0_41)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k8_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_367,plain,
    ( ~ v1_relat_1(X0_41)
    | v1_relat_1(k8_relat_1(X1_41,X0_41)) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_453,plain,
    ( ~ v1_relat_1(X0_41)
    | ~ r2_hidden(k4_tarski(X0_43,X0_42),k8_relat_1(X1_41,X0_41))
    | r2_hidden(k4_tarski(X0_43,X0_42),X0_41) ),
    inference(global_propositional_subsumption,[status(thm)],[c_372,c_367])).

cnf(c_454,plain,
    ( r2_hidden(k4_tarski(X0_43,X0_42),X0_41)
    | ~ r2_hidden(k4_tarski(X0_43,X0_42),k8_relat_1(X1_41,X0_41))
    | ~ v1_relat_1(X0_41) ),
    inference(renaming,[status(thm)],[c_453])).

cnf(c_1246,plain,
    ( r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),X0_41)
    | ~ r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),k8_relat_1(X1_41,X0_41))
    | ~ v1_relat_1(X0_41) ),
    inference(instantiation,[status(thm)],[c_454])).

cnf(c_1623,plain,
    ( ~ r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),k8_relat_1(X0_41,k8_relat_1(sK5,sK7)))
    | r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),k8_relat_1(sK5,sK7))
    | ~ v1_relat_1(k8_relat_1(sK5,sK7)) ),
    inference(instantiation,[status(thm)],[c_1246])).

cnf(c_2470,plain,
    ( r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),k8_relat_1(sK5,sK7))
    | ~ r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),k8_relat_1(sK4,k8_relat_1(sK5,sK7)))
    | ~ v1_relat_1(k8_relat_1(sK5,sK7)) ),
    inference(instantiation,[status(thm)],[c_1623])).

cnf(c_1858,plain,
    ( v1_relat_1(k8_relat_1(sK5,sK7))
    | ~ v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_367])).

cnf(c_379,plain,
    ( X0_42 = X0_42 ),
    theory(equality)).

cnf(c_1332,plain,
    ( k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))) = k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))) ),
    inference(instantiation,[status(thm)],[c_379])).

cnf(c_14,negated_conjecture,
    ( v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_362,negated_conjecture,
    ( v1_relat_1(sK7) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_695,plain,
    ( v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_362])).

cnf(c_12,negated_conjecture,
    ( r1_tarski(sK4,sK5) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_364,negated_conjecture,
    ( r1_tarski(sK4,sK5) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_693,plain,
    ( r1_tarski(sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_364])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X2)
    | k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_366,plain,
    ( ~ r1_tarski(X0_41,X1_41)
    | ~ v1_relat_1(X2_41)
    | k8_relat_1(X0_41,k8_relat_1(X1_41,X2_41)) = k8_relat_1(X0_41,X2_41) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_691,plain,
    ( k8_relat_1(X0_41,k8_relat_1(X1_41,X2_41)) = k8_relat_1(X0_41,X2_41)
    | r1_tarski(X0_41,X1_41) != iProver_top
    | v1_relat_1(X2_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_366])).

cnf(c_986,plain,
    ( k8_relat_1(sK4,k8_relat_1(sK5,X0_41)) = k8_relat_1(sK4,X0_41)
    | v1_relat_1(X0_41) != iProver_top ),
    inference(superposition,[status(thm)],[c_693,c_691])).

cnf(c_1005,plain,
    ( k8_relat_1(sK4,k8_relat_1(sK5,sK7)) = k8_relat_1(sK4,sK7) ),
    inference(superposition,[status(thm)],[c_695,c_986])).

cnf(c_690,plain,
    ( v1_relat_1(X0_41) != iProver_top
    | v1_relat_1(k8_relat_1(X1_41,X0_41)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_367])).

cnf(c_1321,plain,
    ( v1_relat_1(k8_relat_1(sK5,sK7)) != iProver_top
    | v1_relat_1(k8_relat_1(sK4,sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1005,c_690])).

cnf(c_1322,plain,
    ( ~ v1_relat_1(k8_relat_1(sK5,sK7))
    | v1_relat_1(k8_relat_1(sK4,sK7)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1321])).

cnf(c_969,plain,
    ( ~ r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),k8_relat_1(sK4,sK6))
    | r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),sK6)
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_454])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k8_relat_1(X1,X3))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(k8_relat_1(X1,X3)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_371,plain,
    ( r2_hidden(X0_42,X0_41)
    | ~ r2_hidden(k4_tarski(X0_43,X0_42),k8_relat_1(X0_41,X1_41))
    | ~ v1_relat_1(X1_41)
    | ~ v1_relat_1(k8_relat_1(X0_41,X1_41)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_966,plain,
    ( r2_hidden(sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK4)
    | ~ r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),k8_relat_1(sK4,sK6))
    | ~ v1_relat_1(k8_relat_1(sK4,sK6))
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_371])).

cnf(c_925,plain,
    ( v1_relat_1(k8_relat_1(sK4,sK6))
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_367])).

cnf(c_6,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_11,negated_conjecture,
    ( ~ r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_247,plain,
    ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
    | ~ v1_relat_1(X0)
    | k8_relat_1(sK5,sK7) != X1
    | k8_relat_1(sK4,sK6) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_11])).

cnf(c_248,plain,
    ( ~ r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),k8_relat_1(sK5,sK7))
    | ~ v1_relat_1(k8_relat_1(sK4,sK6)) ),
    inference(unflattening,[status(thm)],[c_247])).

cnf(c_7,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_237,plain,
    ( r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
    | ~ v1_relat_1(X0)
    | k8_relat_1(sK5,sK7) != X1
    | k8_relat_1(sK4,sK6) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_11])).

cnf(c_238,plain,
    ( r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),k8_relat_1(sK4,sK6))
    | ~ v1_relat_1(k8_relat_1(sK4,sK6)) ),
    inference(unflattening,[status(thm)],[c_237])).

cnf(c_13,negated_conjecture,
    ( r1_tarski(sK6,sK7) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_15,negated_conjecture,
    ( v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f37])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_14973,c_7099,c_7098,c_2470,c_1858,c_1332,c_1322,c_1005,c_969,c_966,c_925,c_248,c_238,c_13,c_14,c_15])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:40:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.54/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.54/1.01  
% 3.54/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.54/1.01  
% 3.54/1.01  ------  iProver source info
% 3.54/1.01  
% 3.54/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.54/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.54/1.01  git: non_committed_changes: false
% 3.54/1.01  git: last_make_outside_of_git: false
% 3.54/1.01  
% 3.54/1.01  ------ 
% 3.54/1.01  
% 3.54/1.01  ------ Input Options
% 3.54/1.01  
% 3.54/1.01  --out_options                           all
% 3.54/1.01  --tptp_safe_out                         true
% 3.54/1.01  --problem_path                          ""
% 3.54/1.01  --include_path                          ""
% 3.54/1.01  --clausifier                            res/vclausify_rel
% 3.54/1.01  --clausifier_options                    --mode clausify
% 3.54/1.01  --stdin                                 false
% 3.54/1.01  --stats_out                             all
% 3.54/1.01  
% 3.54/1.01  ------ General Options
% 3.54/1.01  
% 3.54/1.01  --fof                                   false
% 3.54/1.01  --time_out_real                         305.
% 3.54/1.01  --time_out_virtual                      -1.
% 3.54/1.01  --symbol_type_check                     false
% 3.54/1.01  --clausify_out                          false
% 3.54/1.01  --sig_cnt_out                           false
% 3.54/1.01  --trig_cnt_out                          false
% 3.54/1.01  --trig_cnt_out_tolerance                1.
% 3.54/1.01  --trig_cnt_out_sk_spl                   false
% 3.54/1.01  --abstr_cl_out                          false
% 3.54/1.01  
% 3.54/1.01  ------ Global Options
% 3.54/1.01  
% 3.54/1.01  --schedule                              default
% 3.54/1.01  --add_important_lit                     false
% 3.54/1.01  --prop_solver_per_cl                    1000
% 3.54/1.01  --min_unsat_core                        false
% 3.54/1.01  --soft_assumptions                      false
% 3.54/1.01  --soft_lemma_size                       3
% 3.54/1.01  --prop_impl_unit_size                   0
% 3.54/1.01  --prop_impl_unit                        []
% 3.54/1.01  --share_sel_clauses                     true
% 3.54/1.01  --reset_solvers                         false
% 3.54/1.01  --bc_imp_inh                            [conj_cone]
% 3.54/1.01  --conj_cone_tolerance                   3.
% 3.54/1.01  --extra_neg_conj                        none
% 3.54/1.01  --large_theory_mode                     true
% 3.54/1.01  --prolific_symb_bound                   200
% 3.54/1.01  --lt_threshold                          2000
% 3.54/1.01  --clause_weak_htbl                      true
% 3.54/1.01  --gc_record_bc_elim                     false
% 3.54/1.01  
% 3.54/1.01  ------ Preprocessing Options
% 3.54/1.01  
% 3.54/1.01  --preprocessing_flag                    true
% 3.54/1.01  --time_out_prep_mult                    0.1
% 3.54/1.01  --splitting_mode                        input
% 3.54/1.01  --splitting_grd                         true
% 3.54/1.01  --splitting_cvd                         false
% 3.54/1.01  --splitting_cvd_svl                     false
% 3.54/1.01  --splitting_nvd                         32
% 3.54/1.01  --sub_typing                            true
% 3.54/1.01  --prep_gs_sim                           true
% 3.54/1.01  --prep_unflatten                        true
% 3.54/1.01  --prep_res_sim                          true
% 3.54/1.01  --prep_upred                            true
% 3.54/1.01  --prep_sem_filter                       exhaustive
% 3.54/1.01  --prep_sem_filter_out                   false
% 3.54/1.01  --pred_elim                             true
% 3.54/1.01  --res_sim_input                         true
% 3.54/1.01  --eq_ax_congr_red                       true
% 3.54/1.01  --pure_diseq_elim                       true
% 3.54/1.01  --brand_transform                       false
% 3.54/1.01  --non_eq_to_eq                          false
% 3.54/1.01  --prep_def_merge                        true
% 3.54/1.01  --prep_def_merge_prop_impl              false
% 3.54/1.01  --prep_def_merge_mbd                    true
% 3.54/1.01  --prep_def_merge_tr_red                 false
% 3.54/1.01  --prep_def_merge_tr_cl                  false
% 3.54/1.01  --smt_preprocessing                     true
% 3.54/1.01  --smt_ac_axioms                         fast
% 3.54/1.01  --preprocessed_out                      false
% 3.54/1.01  --preprocessed_stats                    false
% 3.54/1.01  
% 3.54/1.01  ------ Abstraction refinement Options
% 3.54/1.01  
% 3.54/1.01  --abstr_ref                             []
% 3.54/1.01  --abstr_ref_prep                        false
% 3.54/1.01  --abstr_ref_until_sat                   false
% 3.54/1.01  --abstr_ref_sig_restrict                funpre
% 3.54/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.54/1.01  --abstr_ref_under                       []
% 3.54/1.01  
% 3.54/1.01  ------ SAT Options
% 3.54/1.01  
% 3.54/1.01  --sat_mode                              false
% 3.54/1.01  --sat_fm_restart_options                ""
% 3.54/1.01  --sat_gr_def                            false
% 3.54/1.01  --sat_epr_types                         true
% 3.54/1.01  --sat_non_cyclic_types                  false
% 3.54/1.01  --sat_finite_models                     false
% 3.54/1.01  --sat_fm_lemmas                         false
% 3.54/1.01  --sat_fm_prep                           false
% 3.54/1.01  --sat_fm_uc_incr                        true
% 3.54/1.01  --sat_out_model                         small
% 3.54/1.01  --sat_out_clauses                       false
% 3.54/1.01  
% 3.54/1.01  ------ QBF Options
% 3.54/1.01  
% 3.54/1.01  --qbf_mode                              false
% 3.54/1.01  --qbf_elim_univ                         false
% 3.54/1.01  --qbf_dom_inst                          none
% 3.54/1.01  --qbf_dom_pre_inst                      false
% 3.54/1.01  --qbf_sk_in                             false
% 3.54/1.01  --qbf_pred_elim                         true
% 3.54/1.01  --qbf_split                             512
% 3.54/1.01  
% 3.54/1.01  ------ BMC1 Options
% 3.54/1.01  
% 3.54/1.01  --bmc1_incremental                      false
% 3.54/1.01  --bmc1_axioms                           reachable_all
% 3.54/1.01  --bmc1_min_bound                        0
% 3.54/1.01  --bmc1_max_bound                        -1
% 3.54/1.01  --bmc1_max_bound_default                -1
% 3.54/1.01  --bmc1_symbol_reachability              true
% 3.54/1.01  --bmc1_property_lemmas                  false
% 3.54/1.01  --bmc1_k_induction                      false
% 3.54/1.01  --bmc1_non_equiv_states                 false
% 3.54/1.01  --bmc1_deadlock                         false
% 3.54/1.01  --bmc1_ucm                              false
% 3.54/1.01  --bmc1_add_unsat_core                   none
% 3.54/1.01  --bmc1_unsat_core_children              false
% 3.54/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.54/1.01  --bmc1_out_stat                         full
% 3.54/1.01  --bmc1_ground_init                      false
% 3.54/1.01  --bmc1_pre_inst_next_state              false
% 3.54/1.01  --bmc1_pre_inst_state                   false
% 3.54/1.01  --bmc1_pre_inst_reach_state             false
% 3.54/1.01  --bmc1_out_unsat_core                   false
% 3.54/1.01  --bmc1_aig_witness_out                  false
% 3.54/1.01  --bmc1_verbose                          false
% 3.54/1.01  --bmc1_dump_clauses_tptp                false
% 3.54/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.54/1.01  --bmc1_dump_file                        -
% 3.54/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.54/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.54/1.01  --bmc1_ucm_extend_mode                  1
% 3.54/1.01  --bmc1_ucm_init_mode                    2
% 3.54/1.01  --bmc1_ucm_cone_mode                    none
% 3.54/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.54/1.01  --bmc1_ucm_relax_model                  4
% 3.54/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.54/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.54/1.01  --bmc1_ucm_layered_model                none
% 3.54/1.01  --bmc1_ucm_max_lemma_size               10
% 3.54/1.01  
% 3.54/1.01  ------ AIG Options
% 3.54/1.01  
% 3.54/1.01  --aig_mode                              false
% 3.54/1.01  
% 3.54/1.01  ------ Instantiation Options
% 3.54/1.01  
% 3.54/1.01  --instantiation_flag                    true
% 3.54/1.01  --inst_sos_flag                         false
% 3.54/1.01  --inst_sos_phase                        true
% 3.54/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.54/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.54/1.01  --inst_lit_sel_side                     num_symb
% 3.54/1.01  --inst_solver_per_active                1400
% 3.54/1.01  --inst_solver_calls_frac                1.
% 3.54/1.01  --inst_passive_queue_type               priority_queues
% 3.54/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.54/1.01  --inst_passive_queues_freq              [25;2]
% 3.54/1.01  --inst_dismatching                      true
% 3.54/1.01  --inst_eager_unprocessed_to_passive     true
% 3.54/1.01  --inst_prop_sim_given                   true
% 3.54/1.01  --inst_prop_sim_new                     false
% 3.54/1.01  --inst_subs_new                         false
% 3.54/1.01  --inst_eq_res_simp                      false
% 3.54/1.01  --inst_subs_given                       false
% 3.54/1.01  --inst_orphan_elimination               true
% 3.54/1.01  --inst_learning_loop_flag               true
% 3.54/1.01  --inst_learning_start                   3000
% 3.54/1.01  --inst_learning_factor                  2
% 3.54/1.01  --inst_start_prop_sim_after_learn       3
% 3.54/1.01  --inst_sel_renew                        solver
% 3.54/1.01  --inst_lit_activity_flag                true
% 3.54/1.01  --inst_restr_to_given                   false
% 3.54/1.01  --inst_activity_threshold               500
% 3.54/1.01  --inst_out_proof                        true
% 3.54/1.01  
% 3.54/1.01  ------ Resolution Options
% 3.54/1.01  
% 3.54/1.01  --resolution_flag                       true
% 3.54/1.01  --res_lit_sel                           adaptive
% 3.54/1.01  --res_lit_sel_side                      none
% 3.54/1.01  --res_ordering                          kbo
% 3.54/1.01  --res_to_prop_solver                    active
% 3.54/1.01  --res_prop_simpl_new                    false
% 3.54/1.01  --res_prop_simpl_given                  true
% 3.54/1.01  --res_passive_queue_type                priority_queues
% 3.54/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.54/1.01  --res_passive_queues_freq               [15;5]
% 3.54/1.01  --res_forward_subs                      full
% 3.54/1.01  --res_backward_subs                     full
% 3.54/1.01  --res_forward_subs_resolution           true
% 3.54/1.01  --res_backward_subs_resolution          true
% 3.54/1.01  --res_orphan_elimination                true
% 3.54/1.01  --res_time_limit                        2.
% 3.54/1.01  --res_out_proof                         true
% 3.54/1.01  
% 3.54/1.01  ------ Superposition Options
% 3.54/1.01  
% 3.54/1.01  --superposition_flag                    true
% 3.54/1.01  --sup_passive_queue_type                priority_queues
% 3.54/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.54/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.54/1.01  --demod_completeness_check              fast
% 3.54/1.01  --demod_use_ground                      true
% 3.54/1.01  --sup_to_prop_solver                    passive
% 3.54/1.01  --sup_prop_simpl_new                    true
% 3.54/1.01  --sup_prop_simpl_given                  true
% 3.54/1.01  --sup_fun_splitting                     false
% 3.54/1.01  --sup_smt_interval                      50000
% 3.54/1.01  
% 3.54/1.01  ------ Superposition Simplification Setup
% 3.54/1.01  
% 3.54/1.01  --sup_indices_passive                   []
% 3.54/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.54/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.54/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.54/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.54/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.54/1.01  --sup_full_bw                           [BwDemod]
% 3.54/1.01  --sup_immed_triv                        [TrivRules]
% 3.54/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.54/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.54/1.01  --sup_immed_bw_main                     []
% 3.54/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.54/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.54/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.54/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.54/1.01  
% 3.54/1.01  ------ Combination Options
% 3.54/1.01  
% 3.54/1.01  --comb_res_mult                         3
% 3.54/1.01  --comb_sup_mult                         2
% 3.54/1.01  --comb_inst_mult                        10
% 3.54/1.01  
% 3.54/1.01  ------ Debug Options
% 3.54/1.01  
% 3.54/1.01  --dbg_backtrace                         false
% 3.54/1.01  --dbg_dump_prop_clauses                 false
% 3.54/1.01  --dbg_dump_prop_clauses_file            -
% 3.54/1.01  --dbg_out_stat                          false
% 3.54/1.01  ------ Parsing...
% 3.54/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.54/1.01  
% 3.54/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.54/1.01  
% 3.54/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.54/1.01  
% 3.54/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.54/1.01  ------ Proving...
% 3.54/1.01  ------ Problem Properties 
% 3.54/1.01  
% 3.54/1.01  
% 3.54/1.01  clauses                                 16
% 3.54/1.01  conjectures                             5
% 3.54/1.01  EPR                                     4
% 3.54/1.01  Horn                                    13
% 3.54/1.01  unary                                   5
% 3.54/1.01  binary                                  1
% 3.54/1.01  lits                                    49
% 3.54/1.01  lits eq                                 4
% 3.54/1.01  fd_pure                                 0
% 3.54/1.01  fd_pseudo                               0
% 3.54/1.01  fd_cond                                 0
% 3.54/1.01  fd_pseudo_cond                          3
% 3.54/1.01  AC symbols                              0
% 3.54/1.01  
% 3.54/1.01  ------ Schedule dynamic 5 is on 
% 3.54/1.01  
% 3.54/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.54/1.01  
% 3.54/1.01  
% 3.54/1.01  ------ 
% 3.54/1.01  Current options:
% 3.54/1.01  ------ 
% 3.54/1.01  
% 3.54/1.01  ------ Input Options
% 3.54/1.01  
% 3.54/1.01  --out_options                           all
% 3.54/1.01  --tptp_safe_out                         true
% 3.54/1.01  --problem_path                          ""
% 3.54/1.01  --include_path                          ""
% 3.54/1.01  --clausifier                            res/vclausify_rel
% 3.54/1.01  --clausifier_options                    --mode clausify
% 3.54/1.01  --stdin                                 false
% 3.54/1.01  --stats_out                             all
% 3.54/1.01  
% 3.54/1.01  ------ General Options
% 3.54/1.01  
% 3.54/1.01  --fof                                   false
% 3.54/1.01  --time_out_real                         305.
% 3.54/1.01  --time_out_virtual                      -1.
% 3.54/1.01  --symbol_type_check                     false
% 3.54/1.01  --clausify_out                          false
% 3.54/1.01  --sig_cnt_out                           false
% 3.54/1.01  --trig_cnt_out                          false
% 3.54/1.01  --trig_cnt_out_tolerance                1.
% 3.54/1.01  --trig_cnt_out_sk_spl                   false
% 3.54/1.01  --abstr_cl_out                          false
% 3.54/1.01  
% 3.54/1.01  ------ Global Options
% 3.54/1.01  
% 3.54/1.01  --schedule                              default
% 3.54/1.01  --add_important_lit                     false
% 3.54/1.01  --prop_solver_per_cl                    1000
% 3.54/1.01  --min_unsat_core                        false
% 3.54/1.01  --soft_assumptions                      false
% 3.54/1.01  --soft_lemma_size                       3
% 3.54/1.01  --prop_impl_unit_size                   0
% 3.54/1.01  --prop_impl_unit                        []
% 3.54/1.01  --share_sel_clauses                     true
% 3.54/1.01  --reset_solvers                         false
% 3.54/1.01  --bc_imp_inh                            [conj_cone]
% 3.54/1.01  --conj_cone_tolerance                   3.
% 3.54/1.01  --extra_neg_conj                        none
% 3.54/1.01  --large_theory_mode                     true
% 3.54/1.01  --prolific_symb_bound                   200
% 3.54/1.01  --lt_threshold                          2000
% 3.54/1.01  --clause_weak_htbl                      true
% 3.54/1.01  --gc_record_bc_elim                     false
% 3.54/1.01  
% 3.54/1.01  ------ Preprocessing Options
% 3.54/1.01  
% 3.54/1.01  --preprocessing_flag                    true
% 3.54/1.01  --time_out_prep_mult                    0.1
% 3.54/1.01  --splitting_mode                        input
% 3.54/1.01  --splitting_grd                         true
% 3.54/1.01  --splitting_cvd                         false
% 3.54/1.01  --splitting_cvd_svl                     false
% 3.54/1.01  --splitting_nvd                         32
% 3.54/1.01  --sub_typing                            true
% 3.54/1.01  --prep_gs_sim                           true
% 3.54/1.01  --prep_unflatten                        true
% 3.54/1.01  --prep_res_sim                          true
% 3.54/1.01  --prep_upred                            true
% 3.54/1.01  --prep_sem_filter                       exhaustive
% 3.54/1.01  --prep_sem_filter_out                   false
% 3.54/1.01  --pred_elim                             true
% 3.54/1.01  --res_sim_input                         true
% 3.54/1.01  --eq_ax_congr_red                       true
% 3.54/1.01  --pure_diseq_elim                       true
% 3.54/1.01  --brand_transform                       false
% 3.54/1.01  --non_eq_to_eq                          false
% 3.54/1.01  --prep_def_merge                        true
% 3.54/1.01  --prep_def_merge_prop_impl              false
% 3.54/1.01  --prep_def_merge_mbd                    true
% 3.54/1.01  --prep_def_merge_tr_red                 false
% 3.54/1.01  --prep_def_merge_tr_cl                  false
% 3.54/1.01  --smt_preprocessing                     true
% 3.54/1.01  --smt_ac_axioms                         fast
% 3.54/1.01  --preprocessed_out                      false
% 3.54/1.01  --preprocessed_stats                    false
% 3.54/1.01  
% 3.54/1.01  ------ Abstraction refinement Options
% 3.54/1.01  
% 3.54/1.01  --abstr_ref                             []
% 3.54/1.01  --abstr_ref_prep                        false
% 3.54/1.01  --abstr_ref_until_sat                   false
% 3.54/1.01  --abstr_ref_sig_restrict                funpre
% 3.54/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.54/1.01  --abstr_ref_under                       []
% 3.54/1.01  
% 3.54/1.01  ------ SAT Options
% 3.54/1.01  
% 3.54/1.01  --sat_mode                              false
% 3.54/1.01  --sat_fm_restart_options                ""
% 3.54/1.01  --sat_gr_def                            false
% 3.54/1.01  --sat_epr_types                         true
% 3.54/1.01  --sat_non_cyclic_types                  false
% 3.54/1.01  --sat_finite_models                     false
% 3.54/1.01  --sat_fm_lemmas                         false
% 3.54/1.01  --sat_fm_prep                           false
% 3.54/1.01  --sat_fm_uc_incr                        true
% 3.54/1.01  --sat_out_model                         small
% 3.54/1.01  --sat_out_clauses                       false
% 3.54/1.01  
% 3.54/1.01  ------ QBF Options
% 3.54/1.01  
% 3.54/1.01  --qbf_mode                              false
% 3.54/1.01  --qbf_elim_univ                         false
% 3.54/1.01  --qbf_dom_inst                          none
% 3.54/1.01  --qbf_dom_pre_inst                      false
% 3.54/1.01  --qbf_sk_in                             false
% 3.54/1.01  --qbf_pred_elim                         true
% 3.54/1.01  --qbf_split                             512
% 3.54/1.01  
% 3.54/1.01  ------ BMC1 Options
% 3.54/1.01  
% 3.54/1.01  --bmc1_incremental                      false
% 3.54/1.01  --bmc1_axioms                           reachable_all
% 3.54/1.01  --bmc1_min_bound                        0
% 3.54/1.01  --bmc1_max_bound                        -1
% 3.54/1.01  --bmc1_max_bound_default                -1
% 3.54/1.01  --bmc1_symbol_reachability              true
% 3.54/1.01  --bmc1_property_lemmas                  false
% 3.54/1.01  --bmc1_k_induction                      false
% 3.54/1.01  --bmc1_non_equiv_states                 false
% 3.54/1.01  --bmc1_deadlock                         false
% 3.54/1.01  --bmc1_ucm                              false
% 3.54/1.01  --bmc1_add_unsat_core                   none
% 3.54/1.01  --bmc1_unsat_core_children              false
% 3.54/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.54/1.01  --bmc1_out_stat                         full
% 3.54/1.01  --bmc1_ground_init                      false
% 3.54/1.01  --bmc1_pre_inst_next_state              false
% 3.54/1.01  --bmc1_pre_inst_state                   false
% 3.54/1.01  --bmc1_pre_inst_reach_state             false
% 3.54/1.01  --bmc1_out_unsat_core                   false
% 3.54/1.01  --bmc1_aig_witness_out                  false
% 3.54/1.01  --bmc1_verbose                          false
% 3.54/1.01  --bmc1_dump_clauses_tptp                false
% 3.54/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.54/1.01  --bmc1_dump_file                        -
% 3.54/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.54/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.54/1.01  --bmc1_ucm_extend_mode                  1
% 3.54/1.01  --bmc1_ucm_init_mode                    2
% 3.54/1.01  --bmc1_ucm_cone_mode                    none
% 3.54/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.54/1.01  --bmc1_ucm_relax_model                  4
% 3.54/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.54/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.54/1.01  --bmc1_ucm_layered_model                none
% 3.54/1.01  --bmc1_ucm_max_lemma_size               10
% 3.54/1.01  
% 3.54/1.01  ------ AIG Options
% 3.54/1.01  
% 3.54/1.01  --aig_mode                              false
% 3.54/1.01  
% 3.54/1.01  ------ Instantiation Options
% 3.54/1.01  
% 3.54/1.01  --instantiation_flag                    true
% 3.54/1.01  --inst_sos_flag                         false
% 3.54/1.01  --inst_sos_phase                        true
% 3.54/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.54/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.54/1.01  --inst_lit_sel_side                     none
% 3.54/1.01  --inst_solver_per_active                1400
% 3.54/1.01  --inst_solver_calls_frac                1.
% 3.54/1.01  --inst_passive_queue_type               priority_queues
% 3.54/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.54/1.01  --inst_passive_queues_freq              [25;2]
% 3.54/1.01  --inst_dismatching                      true
% 3.54/1.01  --inst_eager_unprocessed_to_passive     true
% 3.54/1.01  --inst_prop_sim_given                   true
% 3.54/1.01  --inst_prop_sim_new                     false
% 3.54/1.01  --inst_subs_new                         false
% 3.54/1.01  --inst_eq_res_simp                      false
% 3.54/1.01  --inst_subs_given                       false
% 3.54/1.01  --inst_orphan_elimination               true
% 3.54/1.01  --inst_learning_loop_flag               true
% 3.54/1.01  --inst_learning_start                   3000
% 3.54/1.01  --inst_learning_factor                  2
% 3.54/1.01  --inst_start_prop_sim_after_learn       3
% 3.54/1.01  --inst_sel_renew                        solver
% 3.54/1.01  --inst_lit_activity_flag                true
% 3.54/1.01  --inst_restr_to_given                   false
% 3.54/1.01  --inst_activity_threshold               500
% 3.54/1.01  --inst_out_proof                        true
% 3.54/1.01  
% 3.54/1.01  ------ Resolution Options
% 3.54/1.01  
% 3.54/1.01  --resolution_flag                       false
% 3.54/1.01  --res_lit_sel                           adaptive
% 3.54/1.01  --res_lit_sel_side                      none
% 3.54/1.01  --res_ordering                          kbo
% 3.54/1.01  --res_to_prop_solver                    active
% 3.54/1.01  --res_prop_simpl_new                    false
% 3.54/1.01  --res_prop_simpl_given                  true
% 3.54/1.01  --res_passive_queue_type                priority_queues
% 3.54/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.54/1.01  --res_passive_queues_freq               [15;5]
% 3.54/1.01  --res_forward_subs                      full
% 3.54/1.01  --res_backward_subs                     full
% 3.54/1.01  --res_forward_subs_resolution           true
% 3.54/1.01  --res_backward_subs_resolution          true
% 3.54/1.01  --res_orphan_elimination                true
% 3.54/1.01  --res_time_limit                        2.
% 3.54/1.01  --res_out_proof                         true
% 3.54/1.01  
% 3.54/1.01  ------ Superposition Options
% 3.54/1.01  
% 3.54/1.01  --superposition_flag                    true
% 3.54/1.01  --sup_passive_queue_type                priority_queues
% 3.54/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.54/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.54/1.01  --demod_completeness_check              fast
% 3.54/1.01  --demod_use_ground                      true
% 3.54/1.01  --sup_to_prop_solver                    passive
% 3.54/1.01  --sup_prop_simpl_new                    true
% 3.54/1.01  --sup_prop_simpl_given                  true
% 3.54/1.01  --sup_fun_splitting                     false
% 3.54/1.01  --sup_smt_interval                      50000
% 3.54/1.01  
% 3.54/1.01  ------ Superposition Simplification Setup
% 3.54/1.01  
% 3.54/1.01  --sup_indices_passive                   []
% 3.54/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.54/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.54/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.54/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.54/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.54/1.01  --sup_full_bw                           [BwDemod]
% 3.54/1.01  --sup_immed_triv                        [TrivRules]
% 3.54/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.54/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.54/1.01  --sup_immed_bw_main                     []
% 3.54/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.54/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.54/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.54/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.54/1.01  
% 3.54/1.01  ------ Combination Options
% 3.54/1.01  
% 3.54/1.01  --comb_res_mult                         3
% 3.54/1.01  --comb_sup_mult                         2
% 3.54/1.01  --comb_inst_mult                        10
% 3.54/1.01  
% 3.54/1.01  ------ Debug Options
% 3.54/1.01  
% 3.54/1.01  --dbg_backtrace                         false
% 3.54/1.01  --dbg_dump_prop_clauses                 false
% 3.54/1.01  --dbg_dump_prop_clauses_file            -
% 3.54/1.01  --dbg_out_stat                          false
% 3.54/1.01  
% 3.54/1.01  
% 3.54/1.01  
% 3.54/1.01  
% 3.54/1.01  ------ Proving...
% 3.54/1.01  
% 3.54/1.01  
% 3.54/1.01  % SZS status Theorem for theBenchmark.p
% 3.54/1.01  
% 3.54/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.54/1.01  
% 3.54/1.01  fof(f2,axiom,(
% 3.54/1.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X0) => r2_hidden(k4_tarski(X2,X3),X1))))),
% 3.54/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.54/1.01  
% 3.54/1.01  fof(f8,plain,(
% 3.54/1.01    ! [X0] : (! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0))) | ~v1_relat_1(X0))),
% 3.54/1.01    inference(ennf_transformation,[],[f2])).
% 3.54/1.01  
% 3.54/1.01  fof(f19,plain,(
% 3.54/1.01    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | ? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0))) & (! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 3.54/1.01    inference(nnf_transformation,[],[f8])).
% 3.54/1.01  
% 3.54/1.01  fof(f20,plain,(
% 3.54/1.01    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | ? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0))) & (! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 3.54/1.01    inference(rectify,[],[f19])).
% 3.54/1.01  
% 3.54/1.01  fof(f21,plain,(
% 3.54/1.01    ! [X1,X0] : (? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0)) => (~r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) & r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)))),
% 3.54/1.01    introduced(choice_axiom,[])).
% 3.54/1.01  
% 3.54/1.01  fof(f22,plain,(
% 3.54/1.01    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | (~r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) & r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0))) & (! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 3.54/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f20,f21])).
% 3.54/1.01  
% 3.54/1.01  fof(f32,plain,(
% 3.54/1.01    ( ! [X4,X0,X5,X1] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0) | ~r1_tarski(X0,X1) | ~v1_relat_1(X0)) )),
% 3.54/1.01    inference(cnf_transformation,[],[f22])).
% 3.54/1.01  
% 3.54/1.01  fof(f1,axiom,(
% 3.54/1.01    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k8_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0))))))),
% 3.54/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.54/1.01  
% 3.54/1.01  fof(f7,plain,(
% 3.54/1.01    ! [X0,X1] : (! [X2] : ((k8_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 3.54/1.01    inference(ennf_transformation,[],[f1])).
% 3.54/1.01  
% 3.54/1.01  fof(f14,plain,(
% 3.54/1.01    ! [X0,X1] : (! [X2] : (((k8_relat_1(X0,X1) = X2 | ? [X3,X4] : (((~r2_hidden(k4_tarski(X3,X4),X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | (~r2_hidden(k4_tarski(X3,X4),X1) | ~r2_hidden(X4,X0))) & ((r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k8_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 3.54/1.01    inference(nnf_transformation,[],[f7])).
% 3.54/1.01  
% 3.54/1.01  fof(f15,plain,(
% 3.54/1.01    ! [X0,X1] : (! [X2] : (((k8_relat_1(X0,X1) = X2 | ? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X1) | ~r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(k4_tarski(X3,X4),X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k8_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 3.54/1.01    inference(flattening,[],[f14])).
% 3.54/1.01  
% 3.54/1.01  fof(f16,plain,(
% 3.54/1.01    ! [X0,X1] : (! [X2] : (((k8_relat_1(X0,X1) = X2 | ? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X1) | ~r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X5,X6] : ((r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(k4_tarski(X5,X6),X1) | ~r2_hidden(X6,X0)) & ((r2_hidden(k4_tarski(X5,X6),X1) & r2_hidden(X6,X0)) | ~r2_hidden(k4_tarski(X5,X6),X2))) | k8_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 3.54/1.01    inference(rectify,[],[f15])).
% 3.54/1.01  
% 3.54/1.01  fof(f17,plain,(
% 3.54/1.01    ! [X2,X1,X0] : (? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X1) | ~r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0)) | r2_hidden(k4_tarski(X3,X4),X2))) => ((~r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2))))),
% 3.54/1.01    introduced(choice_axiom,[])).
% 3.54/1.01  
% 3.54/1.01  fof(f18,plain,(
% 3.54/1.01    ! [X0,X1] : (! [X2] : (((k8_relat_1(X0,X1) = X2 | ((~r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2)))) & (! [X5,X6] : ((r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(k4_tarski(X5,X6),X1) | ~r2_hidden(X6,X0)) & ((r2_hidden(k4_tarski(X5,X6),X1) & r2_hidden(X6,X0)) | ~r2_hidden(k4_tarski(X5,X6),X2))) | k8_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 3.54/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f17])).
% 3.54/1.01  
% 3.54/1.01  fof(f28,plain,(
% 3.54/1.01    ( ! [X6,X2,X0,X5,X1] : (r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(k4_tarski(X5,X6),X1) | ~r2_hidden(X6,X0) | k8_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 3.54/1.01    inference(cnf_transformation,[],[f18])).
% 3.54/1.01  
% 3.54/1.01  fof(f42,plain,(
% 3.54/1.01    ( ! [X6,X0,X5,X1] : (r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1)) | ~r2_hidden(k4_tarski(X5,X6),X1) | ~r2_hidden(X6,X0) | ~v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 3.54/1.01    inference(equality_resolution,[],[f28])).
% 3.54/1.01  
% 3.54/1.01  fof(f27,plain,(
% 3.54/1.01    ( ! [X6,X2,X0,X5,X1] : (r2_hidden(k4_tarski(X5,X6),X1) | ~r2_hidden(k4_tarski(X5,X6),X2) | k8_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 3.54/1.01    inference(cnf_transformation,[],[f18])).
% 3.54/1.01  
% 3.54/1.01  fof(f43,plain,(
% 3.54/1.01    ( ! [X6,X0,X5,X1] : (r2_hidden(k4_tarski(X5,X6),X1) | ~r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1)) | ~v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 3.54/1.01    inference(equality_resolution,[],[f27])).
% 3.54/1.01  
% 3.54/1.01  fof(f3,axiom,(
% 3.54/1.01    ! [X0,X1] : (v1_relat_1(X1) => v1_relat_1(k8_relat_1(X0,X1)))),
% 3.54/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.54/1.01  
% 3.54/1.01  fof(f9,plain,(
% 3.54/1.01    ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 3.54/1.01    inference(ennf_transformation,[],[f3])).
% 3.54/1.01  
% 3.54/1.01  fof(f35,plain,(
% 3.54/1.01    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 3.54/1.01    inference(cnf_transformation,[],[f9])).
% 3.54/1.01  
% 3.54/1.01  fof(f5,conjecture,(
% 3.54/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)))))),
% 3.54/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.54/1.01  
% 3.54/1.01  fof(f6,negated_conjecture,(
% 3.54/1.01    ~! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)))))),
% 3.54/1.01    inference(negated_conjecture,[],[f5])).
% 3.54/1.01  
% 3.54/1.01  fof(f12,plain,(
% 3.54/1.01    ? [X0,X1,X2] : (? [X3] : ((~r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) & (r1_tarski(X0,X1) & r1_tarski(X2,X3))) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 3.54/1.01    inference(ennf_transformation,[],[f6])).
% 3.54/1.01  
% 3.54/1.01  fof(f13,plain,(
% 3.54/1.01    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) & r1_tarski(X0,X1) & r1_tarski(X2,X3) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 3.54/1.01    inference(flattening,[],[f12])).
% 3.54/1.01  
% 3.54/1.01  fof(f24,plain,(
% 3.54/1.01    ( ! [X2,X0,X1] : (? [X3] : (~r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) & r1_tarski(X0,X1) & r1_tarski(X2,X3) & v1_relat_1(X3)) => (~r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,sK7)) & r1_tarski(X0,X1) & r1_tarski(X2,sK7) & v1_relat_1(sK7))) )),
% 3.54/1.01    introduced(choice_axiom,[])).
% 3.54/1.01  
% 3.54/1.01  fof(f23,plain,(
% 3.54/1.01    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) & r1_tarski(X0,X1) & r1_tarski(X2,X3) & v1_relat_1(X3)) & v1_relat_1(X2)) => (? [X3] : (~r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,X3)) & r1_tarski(sK4,sK5) & r1_tarski(sK6,X3) & v1_relat_1(X3)) & v1_relat_1(sK6))),
% 3.54/1.01    introduced(choice_axiom,[])).
% 3.54/1.01  
% 3.54/1.01  fof(f25,plain,(
% 3.54/1.01    (~r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)) & r1_tarski(sK4,sK5) & r1_tarski(sK6,sK7) & v1_relat_1(sK7)) & v1_relat_1(sK6)),
% 3.54/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f13,f24,f23])).
% 3.54/1.01  
% 3.54/1.01  fof(f38,plain,(
% 3.54/1.01    v1_relat_1(sK7)),
% 3.54/1.01    inference(cnf_transformation,[],[f25])).
% 3.54/1.01  
% 3.54/1.01  fof(f40,plain,(
% 3.54/1.01    r1_tarski(sK4,sK5)),
% 3.54/1.01    inference(cnf_transformation,[],[f25])).
% 3.54/1.01  
% 3.54/1.01  fof(f4,axiom,(
% 3.54/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2))))),
% 3.54/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.54/1.01  
% 3.54/1.01  fof(f10,plain,(
% 3.54/1.01    ! [X0,X1,X2] : ((k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 3.54/1.01    inference(ennf_transformation,[],[f4])).
% 3.54/1.01  
% 3.54/1.01  fof(f11,plain,(
% 3.54/1.01    ! [X0,X1,X2] : (k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 3.54/1.01    inference(flattening,[],[f10])).
% 3.54/1.01  
% 3.54/1.01  fof(f36,plain,(
% 3.54/1.01    ( ! [X2,X0,X1] : (k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 3.54/1.01    inference(cnf_transformation,[],[f11])).
% 3.54/1.01  
% 3.54/1.01  fof(f26,plain,(
% 3.54/1.01    ( ! [X6,X2,X0,X5,X1] : (r2_hidden(X6,X0) | ~r2_hidden(k4_tarski(X5,X6),X2) | k8_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 3.54/1.01    inference(cnf_transformation,[],[f18])).
% 3.54/1.01  
% 3.54/1.01  fof(f44,plain,(
% 3.54/1.01    ( ! [X6,X0,X5,X1] : (r2_hidden(X6,X0) | ~r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1)) | ~v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 3.54/1.01    inference(equality_resolution,[],[f26])).
% 3.54/1.01  
% 3.54/1.01  fof(f34,plain,(
% 3.54/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) | ~v1_relat_1(X0)) )),
% 3.54/1.01    inference(cnf_transformation,[],[f22])).
% 3.54/1.01  
% 3.54/1.01  fof(f41,plain,(
% 3.54/1.01    ~r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),
% 3.54/1.01    inference(cnf_transformation,[],[f25])).
% 3.54/1.01  
% 3.54/1.01  fof(f33,plain,(
% 3.54/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) | ~v1_relat_1(X0)) )),
% 3.54/1.01    inference(cnf_transformation,[],[f22])).
% 3.54/1.01  
% 3.54/1.01  fof(f39,plain,(
% 3.54/1.01    r1_tarski(sK6,sK7)),
% 3.54/1.01    inference(cnf_transformation,[],[f25])).
% 3.54/1.01  
% 3.54/1.01  fof(f37,plain,(
% 3.54/1.01    v1_relat_1(sK6)),
% 3.54/1.01    inference(cnf_transformation,[],[f25])).
% 3.54/1.01  
% 3.54/1.01  cnf(c_8,plain,
% 3.54/1.01      ( ~ r1_tarski(X0,X1)
% 3.54/1.01      | ~ r2_hidden(k4_tarski(X2,X3),X0)
% 3.54/1.01      | r2_hidden(k4_tarski(X2,X3),X1)
% 3.54/1.01      | ~ v1_relat_1(X0) ),
% 3.54/1.01      inference(cnf_transformation,[],[f32]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_368,plain,
% 3.54/1.01      ( ~ r1_tarski(X0_41,X1_41)
% 3.54/1.01      | ~ r2_hidden(k4_tarski(X0_43,X0_42),X0_41)
% 3.54/1.01      | r2_hidden(k4_tarski(X0_43,X0_42),X1_41)
% 3.54/1.01      | ~ v1_relat_1(X0_41) ),
% 3.54/1.01      inference(subtyping,[status(esa)],[c_8]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_1034,plain,
% 3.54/1.01      ( ~ r1_tarski(sK6,X0_41)
% 3.54/1.01      | r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),X0_41)
% 3.54/1.01      | ~ r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),sK6)
% 3.54/1.01      | ~ v1_relat_1(sK6) ),
% 3.54/1.01      inference(instantiation,[status(thm)],[c_368]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_14973,plain,
% 3.54/1.01      ( ~ r1_tarski(sK6,sK7)
% 3.54/1.01      | r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),sK7)
% 3.54/1.01      | ~ r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),sK6)
% 3.54/1.01      | ~ v1_relat_1(sK6) ),
% 3.54/1.01      inference(instantiation,[status(thm)],[c_1034]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_3,plain,
% 3.54/1.01      ( ~ r2_hidden(X0,X1)
% 3.54/1.01      | ~ r2_hidden(k4_tarski(X2,X0),X3)
% 3.54/1.01      | r2_hidden(k4_tarski(X2,X0),k8_relat_1(X1,X3))
% 3.54/1.01      | ~ v1_relat_1(X3)
% 3.54/1.01      | ~ v1_relat_1(k8_relat_1(X1,X3)) ),
% 3.54/1.01      inference(cnf_transformation,[],[f42]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_373,plain,
% 3.54/1.01      ( ~ r2_hidden(X0_42,X0_41)
% 3.54/1.01      | ~ r2_hidden(k4_tarski(X0_43,X0_42),X1_41)
% 3.54/1.01      | r2_hidden(k4_tarski(X0_43,X0_42),k8_relat_1(X0_41,X1_41))
% 3.54/1.01      | ~ v1_relat_1(X1_41)
% 3.54/1.01      | ~ v1_relat_1(k8_relat_1(X0_41,X1_41)) ),
% 3.54/1.01      inference(subtyping,[status(esa)],[c_3]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_1025,plain,
% 3.54/1.01      ( ~ r2_hidden(sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK4)
% 3.54/1.01      | ~ r2_hidden(k4_tarski(X0_43,sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),X0_41)
% 3.54/1.01      | r2_hidden(k4_tarski(X0_43,sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),k8_relat_1(sK4,X0_41))
% 3.54/1.01      | ~ v1_relat_1(X0_41)
% 3.54/1.01      | ~ v1_relat_1(k8_relat_1(sK4,X0_41)) ),
% 3.54/1.01      inference(instantiation,[status(thm)],[c_373]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_1483,plain,
% 3.54/1.01      ( ~ r2_hidden(sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK4)
% 3.54/1.01      | ~ r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),X0_41)
% 3.54/1.01      | r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),k8_relat_1(sK4,X0_41))
% 3.54/1.01      | ~ v1_relat_1(X0_41)
% 3.54/1.01      | ~ v1_relat_1(k8_relat_1(sK4,X0_41)) ),
% 3.54/1.01      inference(instantiation,[status(thm)],[c_1025]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_7099,plain,
% 3.54/1.01      ( ~ r2_hidden(sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK4)
% 3.54/1.01      | r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),k8_relat_1(sK4,sK7))
% 3.54/1.01      | ~ r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),sK7)
% 3.54/1.01      | ~ v1_relat_1(k8_relat_1(sK4,sK7))
% 3.54/1.01      | ~ v1_relat_1(sK7) ),
% 3.54/1.01      inference(instantiation,[status(thm)],[c_1483]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_384,plain,
% 3.54/1.01      ( ~ r2_hidden(X0_42,X0_41)
% 3.54/1.01      | r2_hidden(X1_42,X1_41)
% 3.54/1.01      | X1_42 != X0_42
% 3.54/1.01      | X1_41 != X0_41 ),
% 3.54/1.01      theory(equality) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_1077,plain,
% 3.54/1.01      ( r2_hidden(X0_42,X0_41)
% 3.54/1.01      | ~ r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),X1_41)
% 3.54/1.01      | X0_42 != k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)))
% 3.54/1.01      | X0_41 != X1_41 ),
% 3.54/1.01      inference(instantiation,[status(thm)],[c_384]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_1584,plain,
% 3.54/1.01      ( ~ r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),X0_41)
% 3.54/1.01      | r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),X1_41)
% 3.54/1.01      | k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))) != k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)))
% 3.54/1.01      | X1_41 != X0_41 ),
% 3.54/1.01      inference(instantiation,[status(thm)],[c_1077]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_2449,plain,
% 3.54/1.01      ( ~ r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),X0_41)
% 3.54/1.01      | r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),k8_relat_1(X1_41,k8_relat_1(sK5,sK7)))
% 3.54/1.01      | k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))) != k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)))
% 3.54/1.01      | k8_relat_1(X1_41,k8_relat_1(sK5,sK7)) != X0_41 ),
% 3.54/1.01      inference(instantiation,[status(thm)],[c_1584]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_5132,plain,
% 3.54/1.01      ( r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),k8_relat_1(X0_41,k8_relat_1(sK5,sK7)))
% 3.54/1.01      | ~ r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),k8_relat_1(X0_41,sK7))
% 3.54/1.01      | k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))) != k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)))
% 3.54/1.01      | k8_relat_1(X0_41,k8_relat_1(sK5,sK7)) != k8_relat_1(X0_41,sK7) ),
% 3.54/1.01      inference(instantiation,[status(thm)],[c_2449]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_7098,plain,
% 3.54/1.01      ( r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),k8_relat_1(sK4,k8_relat_1(sK5,sK7)))
% 3.54/1.01      | ~ r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),k8_relat_1(sK4,sK7))
% 3.54/1.01      | k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))) != k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)))
% 3.54/1.01      | k8_relat_1(sK4,k8_relat_1(sK5,sK7)) != k8_relat_1(sK4,sK7) ),
% 3.54/1.01      inference(instantiation,[status(thm)],[c_5132]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_4,plain,
% 3.54/1.01      ( r2_hidden(k4_tarski(X0,X1),X2)
% 3.54/1.01      | ~ r2_hidden(k4_tarski(X0,X1),k8_relat_1(X3,X2))
% 3.54/1.01      | ~ v1_relat_1(X2)
% 3.54/1.01      | ~ v1_relat_1(k8_relat_1(X3,X2)) ),
% 3.54/1.01      inference(cnf_transformation,[],[f43]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_372,plain,
% 3.54/1.01      ( r2_hidden(k4_tarski(X0_43,X0_42),X0_41)
% 3.54/1.01      | ~ r2_hidden(k4_tarski(X0_43,X0_42),k8_relat_1(X1_41,X0_41))
% 3.54/1.01      | ~ v1_relat_1(X0_41)
% 3.54/1.01      | ~ v1_relat_1(k8_relat_1(X1_41,X0_41)) ),
% 3.54/1.01      inference(subtyping,[status(esa)],[c_4]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_9,plain,
% 3.54/1.01      ( ~ v1_relat_1(X0) | v1_relat_1(k8_relat_1(X1,X0)) ),
% 3.54/1.01      inference(cnf_transformation,[],[f35]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_367,plain,
% 3.54/1.01      ( ~ v1_relat_1(X0_41) | v1_relat_1(k8_relat_1(X1_41,X0_41)) ),
% 3.54/1.01      inference(subtyping,[status(esa)],[c_9]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_453,plain,
% 3.54/1.01      ( ~ v1_relat_1(X0_41)
% 3.54/1.01      | ~ r2_hidden(k4_tarski(X0_43,X0_42),k8_relat_1(X1_41,X0_41))
% 3.54/1.01      | r2_hidden(k4_tarski(X0_43,X0_42),X0_41) ),
% 3.54/1.01      inference(global_propositional_subsumption,
% 3.54/1.01                [status(thm)],
% 3.54/1.01                [c_372,c_367]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_454,plain,
% 3.54/1.01      ( r2_hidden(k4_tarski(X0_43,X0_42),X0_41)
% 3.54/1.01      | ~ r2_hidden(k4_tarski(X0_43,X0_42),k8_relat_1(X1_41,X0_41))
% 3.54/1.01      | ~ v1_relat_1(X0_41) ),
% 3.54/1.01      inference(renaming,[status(thm)],[c_453]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_1246,plain,
% 3.54/1.01      ( r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),X0_41)
% 3.54/1.01      | ~ r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),k8_relat_1(X1_41,X0_41))
% 3.54/1.01      | ~ v1_relat_1(X0_41) ),
% 3.54/1.01      inference(instantiation,[status(thm)],[c_454]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_1623,plain,
% 3.54/1.01      ( ~ r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),k8_relat_1(X0_41,k8_relat_1(sK5,sK7)))
% 3.54/1.01      | r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),k8_relat_1(sK5,sK7))
% 3.54/1.01      | ~ v1_relat_1(k8_relat_1(sK5,sK7)) ),
% 3.54/1.01      inference(instantiation,[status(thm)],[c_1246]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_2470,plain,
% 3.54/1.01      ( r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),k8_relat_1(sK5,sK7))
% 3.54/1.01      | ~ r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),k8_relat_1(sK4,k8_relat_1(sK5,sK7)))
% 3.54/1.01      | ~ v1_relat_1(k8_relat_1(sK5,sK7)) ),
% 3.54/1.01      inference(instantiation,[status(thm)],[c_1623]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_1858,plain,
% 3.54/1.01      ( v1_relat_1(k8_relat_1(sK5,sK7)) | ~ v1_relat_1(sK7) ),
% 3.54/1.01      inference(instantiation,[status(thm)],[c_367]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_379,plain,( X0_42 = X0_42 ),theory(equality) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_1332,plain,
% 3.54/1.01      ( k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))) = k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))) ),
% 3.54/1.01      inference(instantiation,[status(thm)],[c_379]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_14,negated_conjecture,
% 3.54/1.01      ( v1_relat_1(sK7) ),
% 3.54/1.01      inference(cnf_transformation,[],[f38]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_362,negated_conjecture,
% 3.54/1.01      ( v1_relat_1(sK7) ),
% 3.54/1.01      inference(subtyping,[status(esa)],[c_14]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_695,plain,
% 3.54/1.01      ( v1_relat_1(sK7) = iProver_top ),
% 3.54/1.01      inference(predicate_to_equality,[status(thm)],[c_362]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_12,negated_conjecture,
% 3.54/1.01      ( r1_tarski(sK4,sK5) ),
% 3.54/1.01      inference(cnf_transformation,[],[f40]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_364,negated_conjecture,
% 3.54/1.01      ( r1_tarski(sK4,sK5) ),
% 3.54/1.01      inference(subtyping,[status(esa)],[c_12]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_693,plain,
% 3.54/1.01      ( r1_tarski(sK4,sK5) = iProver_top ),
% 3.54/1.01      inference(predicate_to_equality,[status(thm)],[c_364]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_10,plain,
% 3.54/1.01      ( ~ r1_tarski(X0,X1)
% 3.54/1.01      | ~ v1_relat_1(X2)
% 3.54/1.01      | k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2) ),
% 3.54/1.01      inference(cnf_transformation,[],[f36]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_366,plain,
% 3.54/1.01      ( ~ r1_tarski(X0_41,X1_41)
% 3.54/1.01      | ~ v1_relat_1(X2_41)
% 3.54/1.01      | k8_relat_1(X0_41,k8_relat_1(X1_41,X2_41)) = k8_relat_1(X0_41,X2_41) ),
% 3.54/1.01      inference(subtyping,[status(esa)],[c_10]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_691,plain,
% 3.54/1.01      ( k8_relat_1(X0_41,k8_relat_1(X1_41,X2_41)) = k8_relat_1(X0_41,X2_41)
% 3.54/1.01      | r1_tarski(X0_41,X1_41) != iProver_top
% 3.54/1.01      | v1_relat_1(X2_41) != iProver_top ),
% 3.54/1.01      inference(predicate_to_equality,[status(thm)],[c_366]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_986,plain,
% 3.54/1.01      ( k8_relat_1(sK4,k8_relat_1(sK5,X0_41)) = k8_relat_1(sK4,X0_41)
% 3.54/1.01      | v1_relat_1(X0_41) != iProver_top ),
% 3.54/1.01      inference(superposition,[status(thm)],[c_693,c_691]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_1005,plain,
% 3.54/1.01      ( k8_relat_1(sK4,k8_relat_1(sK5,sK7)) = k8_relat_1(sK4,sK7) ),
% 3.54/1.01      inference(superposition,[status(thm)],[c_695,c_986]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_690,plain,
% 3.54/1.01      ( v1_relat_1(X0_41) != iProver_top
% 3.54/1.01      | v1_relat_1(k8_relat_1(X1_41,X0_41)) = iProver_top ),
% 3.54/1.01      inference(predicate_to_equality,[status(thm)],[c_367]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_1321,plain,
% 3.54/1.01      ( v1_relat_1(k8_relat_1(sK5,sK7)) != iProver_top
% 3.54/1.01      | v1_relat_1(k8_relat_1(sK4,sK7)) = iProver_top ),
% 3.54/1.01      inference(superposition,[status(thm)],[c_1005,c_690]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_1322,plain,
% 3.54/1.01      ( ~ v1_relat_1(k8_relat_1(sK5,sK7))
% 3.54/1.01      | v1_relat_1(k8_relat_1(sK4,sK7)) ),
% 3.54/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_1321]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_969,plain,
% 3.54/1.01      ( ~ r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),k8_relat_1(sK4,sK6))
% 3.54/1.01      | r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),sK6)
% 3.54/1.01      | ~ v1_relat_1(sK6) ),
% 3.54/1.01      inference(instantiation,[status(thm)],[c_454]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_5,plain,
% 3.54/1.01      ( r2_hidden(X0,X1)
% 3.54/1.01      | ~ r2_hidden(k4_tarski(X2,X0),k8_relat_1(X1,X3))
% 3.54/1.01      | ~ v1_relat_1(X3)
% 3.54/1.01      | ~ v1_relat_1(k8_relat_1(X1,X3)) ),
% 3.54/1.01      inference(cnf_transformation,[],[f44]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_371,plain,
% 3.54/1.01      ( r2_hidden(X0_42,X0_41)
% 3.54/1.01      | ~ r2_hidden(k4_tarski(X0_43,X0_42),k8_relat_1(X0_41,X1_41))
% 3.54/1.01      | ~ v1_relat_1(X1_41)
% 3.54/1.01      | ~ v1_relat_1(k8_relat_1(X0_41,X1_41)) ),
% 3.54/1.01      inference(subtyping,[status(esa)],[c_5]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_966,plain,
% 3.54/1.01      ( r2_hidden(sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK4)
% 3.54/1.01      | ~ r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),k8_relat_1(sK4,sK6))
% 3.54/1.01      | ~ v1_relat_1(k8_relat_1(sK4,sK6))
% 3.54/1.01      | ~ v1_relat_1(sK6) ),
% 3.54/1.01      inference(instantiation,[status(thm)],[c_371]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_925,plain,
% 3.54/1.01      ( v1_relat_1(k8_relat_1(sK4,sK6)) | ~ v1_relat_1(sK6) ),
% 3.54/1.01      inference(instantiation,[status(thm)],[c_367]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_6,plain,
% 3.54/1.01      ( r1_tarski(X0,X1)
% 3.54/1.01      | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
% 3.54/1.01      | ~ v1_relat_1(X0) ),
% 3.54/1.01      inference(cnf_transformation,[],[f34]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_11,negated_conjecture,
% 3.54/1.01      ( ~ r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)) ),
% 3.54/1.01      inference(cnf_transformation,[],[f41]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_247,plain,
% 3.54/1.01      ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
% 3.54/1.01      | ~ v1_relat_1(X0)
% 3.54/1.01      | k8_relat_1(sK5,sK7) != X1
% 3.54/1.01      | k8_relat_1(sK4,sK6) != X0 ),
% 3.54/1.01      inference(resolution_lifted,[status(thm)],[c_6,c_11]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_248,plain,
% 3.54/1.01      ( ~ r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),k8_relat_1(sK5,sK7))
% 3.54/1.01      | ~ v1_relat_1(k8_relat_1(sK4,sK6)) ),
% 3.54/1.01      inference(unflattening,[status(thm)],[c_247]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_7,plain,
% 3.54/1.01      ( r1_tarski(X0,X1)
% 3.54/1.01      | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
% 3.54/1.01      | ~ v1_relat_1(X0) ),
% 3.54/1.01      inference(cnf_transformation,[],[f33]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_237,plain,
% 3.54/1.01      ( r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
% 3.54/1.01      | ~ v1_relat_1(X0)
% 3.54/1.01      | k8_relat_1(sK5,sK7) != X1
% 3.54/1.01      | k8_relat_1(sK4,sK6) != X0 ),
% 3.54/1.01      inference(resolution_lifted,[status(thm)],[c_7,c_11]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_238,plain,
% 3.54/1.01      ( r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),k8_relat_1(sK4,sK6))
% 3.54/1.01      | ~ v1_relat_1(k8_relat_1(sK4,sK6)) ),
% 3.54/1.01      inference(unflattening,[status(thm)],[c_237]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_13,negated_conjecture,
% 3.54/1.01      ( r1_tarski(sK6,sK7) ),
% 3.54/1.01      inference(cnf_transformation,[],[f39]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_15,negated_conjecture,
% 3.54/1.01      ( v1_relat_1(sK6) ),
% 3.54/1.01      inference(cnf_transformation,[],[f37]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(contradiction,plain,
% 3.54/1.01      ( $false ),
% 3.54/1.01      inference(minisat,
% 3.54/1.01                [status(thm)],
% 3.54/1.01                [c_14973,c_7099,c_7098,c_2470,c_1858,c_1332,c_1322,
% 3.54/1.01                 c_1005,c_969,c_966,c_925,c_248,c_238,c_13,c_14,c_15]) ).
% 3.54/1.01  
% 3.54/1.01  
% 3.54/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.54/1.01  
% 3.54/1.01  ------                               Statistics
% 3.54/1.01  
% 3.54/1.01  ------ General
% 3.54/1.01  
% 3.54/1.01  abstr_ref_over_cycles:                  0
% 3.54/1.01  abstr_ref_under_cycles:                 0
% 3.54/1.01  gc_basic_clause_elim:                   0
% 3.54/1.01  forced_gc_time:                         0
% 3.54/1.01  parsing_time:                           0.021
% 3.54/1.01  unif_index_cands_time:                  0.
% 3.54/1.01  unif_index_add_time:                    0.
% 3.54/1.01  orderings_time:                         0.
% 3.54/1.01  out_proof_time:                         0.009
% 3.54/1.01  total_time:                             0.467
% 3.54/1.01  num_of_symbols:                         47
% 3.54/1.01  num_of_terms:                           11984
% 3.54/1.01  
% 3.54/1.01  ------ Preprocessing
% 3.54/1.01  
% 3.54/1.01  num_of_splits:                          0
% 3.54/1.01  num_of_split_atoms:                     0
% 3.54/1.01  num_of_reused_defs:                     0
% 3.54/1.01  num_eq_ax_congr_red:                    20
% 3.54/1.01  num_of_sem_filtered_clauses:            1
% 3.54/1.01  num_of_subtypes:                        3
% 3.54/1.01  monotx_restored_types:                  0
% 3.54/1.01  sat_num_of_epr_types:                   0
% 3.54/1.01  sat_num_of_non_cyclic_types:            0
% 3.54/1.01  sat_guarded_non_collapsed_types:        1
% 3.54/1.01  num_pure_diseq_elim:                    0
% 3.54/1.01  simp_replaced_by:                       0
% 3.54/1.01  res_preprocessed:                       67
% 3.54/1.01  prep_upred:                             0
% 3.54/1.01  prep_unflattend:                        12
% 3.54/1.01  smt_new_axioms:                         0
% 3.54/1.01  pred_elim_cands:                        3
% 3.54/1.01  pred_elim:                              0
% 3.54/1.01  pred_elim_cl:                           0
% 3.54/1.01  pred_elim_cycles:                       1
% 3.54/1.01  merged_defs:                            0
% 3.54/1.01  merged_defs_ncl:                        0
% 3.54/1.01  bin_hyper_res:                          0
% 3.54/1.01  prep_cycles:                            3
% 3.54/1.01  pred_elim_time:                         0.002
% 3.54/1.01  splitting_time:                         0.
% 3.54/1.01  sem_filter_time:                        0.
% 3.54/1.01  monotx_time:                            0.
% 3.54/1.01  subtype_inf_time:                       0.
% 3.54/1.01  
% 3.54/1.01  ------ Problem properties
% 3.54/1.01  
% 3.54/1.01  clauses:                                16
% 3.54/1.01  conjectures:                            5
% 3.54/1.01  epr:                                    4
% 3.54/1.01  horn:                                   13
% 3.54/1.01  ground:                                 5
% 3.54/1.01  unary:                                  5
% 3.54/1.01  binary:                                 1
% 3.54/1.01  lits:                                   49
% 3.54/1.01  lits_eq:                                4
% 3.54/1.01  fd_pure:                                0
% 3.54/1.01  fd_pseudo:                              0
% 3.54/1.01  fd_cond:                                0
% 3.54/1.01  fd_pseudo_cond:                         3
% 3.54/1.01  ac_symbols:                             0
% 3.54/1.01  
% 3.54/1.01  ------ Propositional Solver
% 3.54/1.01  
% 3.54/1.01  prop_solver_calls:                      27
% 3.54/1.01  prop_fast_solver_calls:                 704
% 3.54/1.01  smt_solver_calls:                       0
% 3.54/1.01  smt_fast_solver_calls:                  0
% 3.54/1.01  prop_num_of_clauses:                    4361
% 3.54/1.01  prop_preprocess_simplified:             6113
% 3.54/1.01  prop_fo_subsumed:                       10
% 3.54/1.01  prop_solver_time:                       0.
% 3.54/1.01  smt_solver_time:                        0.
% 3.54/1.01  smt_fast_solver_time:                   0.
% 3.54/1.01  prop_fast_solver_time:                  0.
% 3.54/1.01  prop_unsat_core_time:                   0.
% 3.54/1.01  
% 3.54/1.01  ------ QBF
% 3.54/1.01  
% 3.54/1.01  qbf_q_res:                              0
% 3.54/1.01  qbf_num_tautologies:                    0
% 3.54/1.01  qbf_prep_cycles:                        0
% 3.54/1.01  
% 3.54/1.01  ------ BMC1
% 3.54/1.01  
% 3.54/1.01  bmc1_current_bound:                     -1
% 3.54/1.01  bmc1_last_solved_bound:                 -1
% 3.54/1.01  bmc1_unsat_core_size:                   -1
% 3.54/1.01  bmc1_unsat_core_parents_size:           -1
% 3.54/1.01  bmc1_merge_next_fun:                    0
% 3.54/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.54/1.01  
% 3.54/1.01  ------ Instantiation
% 3.54/1.01  
% 3.54/1.01  inst_num_of_clauses:                    889
% 3.54/1.01  inst_num_in_passive:                    378
% 3.54/1.01  inst_num_in_active:                     483
% 3.54/1.01  inst_num_in_unprocessed:                27
% 3.54/1.01  inst_num_of_loops:                      582
% 3.54/1.01  inst_num_of_learning_restarts:          0
% 3.54/1.01  inst_num_moves_active_passive:          92
% 3.54/1.01  inst_lit_activity:                      0
% 3.54/1.01  inst_lit_activity_moves:                0
% 3.54/1.01  inst_num_tautologies:                   0
% 3.54/1.01  inst_num_prop_implied:                  0
% 3.54/1.01  inst_num_existing_simplified:           0
% 3.54/1.01  inst_num_eq_res_simplified:             0
% 3.54/1.01  inst_num_child_elim:                    0
% 3.54/1.01  inst_num_of_dismatching_blockings:      992
% 3.54/1.01  inst_num_of_non_proper_insts:           1480
% 3.54/1.01  inst_num_of_duplicates:                 0
% 3.54/1.01  inst_inst_num_from_inst_to_res:         0
% 3.54/1.01  inst_dismatching_checking_time:         0.
% 3.54/1.01  
% 3.54/1.01  ------ Resolution
% 3.54/1.01  
% 3.54/1.01  res_num_of_clauses:                     0
% 3.54/1.01  res_num_in_passive:                     0
% 3.54/1.01  res_num_in_active:                      0
% 3.54/1.01  res_num_of_loops:                       70
% 3.54/1.01  res_forward_subset_subsumed:            99
% 3.54/1.01  res_backward_subset_subsumed:           0
% 3.54/1.01  res_forward_subsumed:                   0
% 3.54/1.01  res_backward_subsumed:                  0
% 3.54/1.01  res_forward_subsumption_resolution:     0
% 3.54/1.01  res_backward_subsumption_resolution:    0
% 3.54/1.01  res_clause_to_clause_subsumption:       2391
% 3.54/1.01  res_orphan_elimination:                 0
% 3.54/1.01  res_tautology_del:                      179
% 3.54/1.01  res_num_eq_res_simplified:              0
% 3.54/1.01  res_num_sel_changes:                    0
% 3.54/1.01  res_moves_from_active_to_pass:          0
% 3.54/1.01  
% 3.54/1.01  ------ Superposition
% 3.54/1.01  
% 3.54/1.01  sup_time_total:                         0.
% 3.54/1.01  sup_time_generating:                    0.
% 3.54/1.01  sup_time_sim_full:                      0.
% 3.54/1.01  sup_time_sim_immed:                     0.
% 3.54/1.01  
% 3.54/1.01  sup_num_of_clauses:                     517
% 3.54/1.01  sup_num_in_active:                      113
% 3.54/1.01  sup_num_in_passive:                     404
% 3.54/1.01  sup_num_of_loops:                       116
% 3.54/1.01  sup_fw_superposition:                   478
% 3.54/1.01  sup_bw_superposition:                   269
% 3.54/1.01  sup_immediate_simplified:               159
% 3.54/1.01  sup_given_eliminated:                   0
% 3.54/1.01  comparisons_done:                       0
% 3.54/1.01  comparisons_avoided:                    0
% 3.54/1.01  
% 3.54/1.01  ------ Simplifications
% 3.54/1.01  
% 3.54/1.01  
% 3.54/1.01  sim_fw_subset_subsumed:                 12
% 3.54/1.01  sim_bw_subset_subsumed:                 2
% 3.54/1.01  sim_fw_subsumed:                        59
% 3.54/1.01  sim_bw_subsumed:                        6
% 3.54/1.01  sim_fw_subsumption_res:                 3
% 3.54/1.01  sim_bw_subsumption_res:                 0
% 3.54/1.01  sim_tautology_del:                      83
% 3.54/1.01  sim_eq_tautology_del:                   21
% 3.54/1.01  sim_eq_res_simp:                        3
% 3.54/1.01  sim_fw_demodulated:                     1
% 3.54/1.01  sim_bw_demodulated:                     3
% 3.54/1.01  sim_light_normalised:                   108
% 3.54/1.01  sim_joinable_taut:                      0
% 3.54/1.01  sim_joinable_simp:                      0
% 3.54/1.01  sim_ac_normalised:                      0
% 3.54/1.01  sim_smt_subsumption:                    0
% 3.54/1.01  
%------------------------------------------------------------------------------
