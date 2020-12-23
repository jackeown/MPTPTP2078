%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:47:56 EST 2020

% Result     : Theorem 3.79s
% Output     : CNFRefutation 3.79s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 123 expanded)
%              Number of clauses        :   24 (  26 expanded)
%              Number of leaves         :   14 (  33 expanded)
%              Depth                    :   10
%              Number of atoms          :  332 ( 616 expanded)
%              Number of equality atoms :   23 (  23 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f14])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).

fof(f36,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f27])).

fof(f31,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK6(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK5(X0,X1),X3),X0)
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK5(X0,X1),X4),X0)
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK5(X0,X1),X3),X0)
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0)
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f28,f31,f30,f29])).

fof(f49,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f61,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f49])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( v1_relat_1(X2)
         => ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f18,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f20,plain,(
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
    inference(rectify,[],[f19])).

fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ( r2_hidden(k4_tarski(X3,X4),X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X0)
          | ~ r2_hidden(sK1(X0,X1,X2),X1)
          | ~ r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2) )
        & ( ( r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X0)
            & r2_hidden(sK1(X0,X1,X2),X1) )
          | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X0)
                  | ~ r2_hidden(sK1(X0,X1,X2),X1)
                  | ~ r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2) )
                & ( ( r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X0)
                    & r2_hidden(sK1(X0,X1,X2),X1) )
                  | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f20,f21])).

fof(f41,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X2)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(X5,X1)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f58,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(X5,X1)
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
             => r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X1)
              | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f23,plain,(
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
    inference(nnf_transformation,[],[f10])).

fof(f24,plain,(
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
    inference(rectify,[],[f23])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(k4_tarski(X2,X3),X1)
          & r2_hidden(k4_tarski(X2,X3),X0) )
     => ( ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)
        & r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)
              & r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f24,f25])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( ( r1_tarski(X2,X1)
              & r1_tarski(k1_relat_1(X2),X0) )
           => r1_tarski(X2,k7_relat_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ( ( r1_tarski(X2,X1)
                & r1_tarski(k1_relat_1(X2),X0) )
             => r1_tarski(X2,k7_relat_1(X1,X0)) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,k7_relat_1(X1,X0))
          & r1_tarski(X2,X1)
          & r1_tarski(k1_relat_1(X2),X0)
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,k7_relat_1(X1,X0))
          & r1_tarski(X2,X1)
          & r1_tarski(k1_relat_1(X2),X0)
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,k7_relat_1(X1,X0))
          & r1_tarski(X2,X1)
          & r1_tarski(k1_relat_1(X2),X0)
          & v1_relat_1(X2) )
     => ( ~ r1_tarski(sK10,k7_relat_1(X1,X0))
        & r1_tarski(sK10,X1)
        & r1_tarski(k1_relat_1(sK10),X0)
        & v1_relat_1(sK10) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(X2,k7_relat_1(X1,X0))
            & r1_tarski(X2,X1)
            & r1_tarski(k1_relat_1(X2),X0)
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ~ r1_tarski(X2,k7_relat_1(sK9,sK8))
          & r1_tarski(X2,sK9)
          & r1_tarski(k1_relat_1(X2),sK8)
          & v1_relat_1(X2) )
      & v1_relat_1(sK9) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ~ r1_tarski(sK10,k7_relat_1(sK9,sK8))
    & r1_tarski(sK10,sK9)
    & r1_tarski(k1_relat_1(sK10),sK8)
    & v1_relat_1(sK10)
    & v1_relat_1(sK9) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f13,f34,f33])).

fof(f57,plain,(
    ~ r1_tarski(sK10,k7_relat_1(sK9,sK8)) ),
    inference(cnf_transformation,[],[f35])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f56,plain,(
    r1_tarski(sK10,sK9) ),
    inference(cnf_transformation,[],[f35])).

fof(f55,plain,(
    r1_tarski(k1_relat_1(sK10),sK8) ),
    inference(cnf_transformation,[],[f35])).

fof(f54,plain,(
    v1_relat_1(sK10) ),
    inference(cnf_transformation,[],[f35])).

fof(f53,plain,(
    v1_relat_1(sK9) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1851,plain,
    ( ~ r2_hidden(k4_tarski(sK3(X0,k7_relat_1(sK9,sK8)),sK4(X0,k7_relat_1(sK9,sK8))),X0)
    | r2_hidden(k4_tarski(sK3(X0,k7_relat_1(sK9,sK8)),sK4(X0,k7_relat_1(sK9,sK8))),X1)
    | ~ r1_tarski(X0,X1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_5478,plain,
    ( r2_hidden(k4_tarski(sK3(sK10,k7_relat_1(sK9,sK8)),sK4(sK10,k7_relat_1(sK9,sK8))),sK9)
    | ~ r2_hidden(k4_tarski(sK3(sK10,k7_relat_1(sK9,sK8)),sK4(sK10,k7_relat_1(sK9,sK8))),sK10)
    | ~ r1_tarski(sK10,sK9) ),
    inference(instantiation,[status(thm)],[c_1851])).

cnf(c_14,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1666,plain,
    ( r2_hidden(sK3(sK10,k7_relat_1(sK9,sK8)),k1_relat_1(sK10))
    | ~ r2_hidden(k4_tarski(sK3(sK10,k7_relat_1(sK9,sK8)),X0),sK10) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_2869,plain,
    ( r2_hidden(sK3(sK10,k7_relat_1(sK9,sK8)),k1_relat_1(sK10))
    | ~ r2_hidden(k4_tarski(sK3(sK10,k7_relat_1(sK9,sK8)),sK4(sK10,k7_relat_1(sK9,sK8))),sK10) ),
    inference(instantiation,[status(thm)],[c_1666])).

cnf(c_1068,plain,
    ( ~ r2_hidden(sK3(sK10,k7_relat_1(sK9,sK8)),X0)
    | r2_hidden(sK3(sK10,k7_relat_1(sK9,sK8)),sK8)
    | ~ r1_tarski(X0,sK8) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1264,plain,
    ( ~ r2_hidden(sK3(sK10,k7_relat_1(sK9,sK8)),k1_relat_1(sK10))
    | r2_hidden(sK3(sK10,k7_relat_1(sK9,sK8)),sK8)
    | ~ r1_tarski(k1_relat_1(sK10),sK8) ),
    inference(instantiation,[status(thm)],[c_1068])).

cnf(c_16,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_913,plain,
    ( v1_relat_1(k7_relat_1(sK9,sK8))
    | ~ v1_relat_1(sK9) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),X3)
    | r2_hidden(k4_tarski(X0,X2),k7_relat_1(X3,X1))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(k7_relat_1(X3,X1)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_855,plain,
    ( ~ r2_hidden(sK3(sK10,k7_relat_1(sK9,sK8)),sK8)
    | r2_hidden(k4_tarski(sK3(sK10,k7_relat_1(sK9,sK8)),sK4(sK10,k7_relat_1(sK9,sK8))),k7_relat_1(sK9,sK8))
    | ~ r2_hidden(k4_tarski(sK3(sK10,k7_relat_1(sK9,sK8)),sK4(sK10,k7_relat_1(sK9,sK8))),sK9)
    | ~ v1_relat_1(k7_relat_1(sK9,sK8))
    | ~ v1_relat_1(sK9) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_9,plain,
    ( ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)
    | r1_tarski(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_17,negated_conjecture,
    ( ~ r1_tarski(sK10,k7_relat_1(sK9,sK8)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_323,plain,
    ( ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(sK9,sK8) != X1
    | sK10 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_17])).

cnf(c_324,plain,
    ( ~ r2_hidden(k4_tarski(sK3(sK10,k7_relat_1(sK9,sK8)),sK4(sK10,k7_relat_1(sK9,sK8))),k7_relat_1(sK9,sK8))
    | ~ v1_relat_1(sK10) ),
    inference(unflattening,[status(thm)],[c_323])).

cnf(c_10,plain,
    ( r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0)
    | r1_tarski(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_312,plain,
    ( r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0)
    | ~ v1_relat_1(X0)
    | k7_relat_1(sK9,sK8) != X1
    | sK10 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_17])).

cnf(c_313,plain,
    ( r2_hidden(k4_tarski(sK3(sK10,k7_relat_1(sK9,sK8)),sK4(sK10,k7_relat_1(sK9,sK8))),sK10)
    | ~ v1_relat_1(sK10) ),
    inference(unflattening,[status(thm)],[c_312])).

cnf(c_18,negated_conjecture,
    ( r1_tarski(sK10,sK9) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_19,negated_conjecture,
    ( r1_tarski(k1_relat_1(sK10),sK8) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_20,negated_conjecture,
    ( v1_relat_1(sK10) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_21,negated_conjecture,
    ( v1_relat_1(sK9) ),
    inference(cnf_transformation,[],[f53])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5478,c_2869,c_1264,c_913,c_855,c_324,c_313,c_18,c_19,c_20,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:42:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.79/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.79/0.99  
% 3.79/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.79/0.99  
% 3.79/0.99  ------  iProver source info
% 3.79/0.99  
% 3.79/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.79/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.79/0.99  git: non_committed_changes: false
% 3.79/0.99  git: last_make_outside_of_git: false
% 3.79/0.99  
% 3.79/0.99  ------ 
% 3.79/0.99  
% 3.79/0.99  ------ Input Options
% 3.79/0.99  
% 3.79/0.99  --out_options                           all
% 3.79/0.99  --tptp_safe_out                         true
% 3.79/0.99  --problem_path                          ""
% 3.79/0.99  --include_path                          ""
% 3.79/0.99  --clausifier                            res/vclausify_rel
% 3.79/0.99  --clausifier_options                    ""
% 3.79/0.99  --stdin                                 false
% 3.79/0.99  --stats_out                             all
% 3.79/0.99  
% 3.79/0.99  ------ General Options
% 3.79/0.99  
% 3.79/0.99  --fof                                   false
% 3.79/0.99  --time_out_real                         305.
% 3.79/0.99  --time_out_virtual                      -1.
% 3.79/0.99  --symbol_type_check                     false
% 3.79/0.99  --clausify_out                          false
% 3.79/0.99  --sig_cnt_out                           false
% 3.79/0.99  --trig_cnt_out                          false
% 3.79/0.99  --trig_cnt_out_tolerance                1.
% 3.79/0.99  --trig_cnt_out_sk_spl                   false
% 3.79/0.99  --abstr_cl_out                          false
% 3.79/0.99  
% 3.79/0.99  ------ Global Options
% 3.79/0.99  
% 3.79/0.99  --schedule                              default
% 3.79/0.99  --add_important_lit                     false
% 3.79/0.99  --prop_solver_per_cl                    1000
% 3.79/0.99  --min_unsat_core                        false
% 3.79/0.99  --soft_assumptions                      false
% 3.79/0.99  --soft_lemma_size                       3
% 3.79/0.99  --prop_impl_unit_size                   0
% 3.79/0.99  --prop_impl_unit                        []
% 3.79/0.99  --share_sel_clauses                     true
% 3.79/0.99  --reset_solvers                         false
% 3.79/0.99  --bc_imp_inh                            [conj_cone]
% 3.79/0.99  --conj_cone_tolerance                   3.
% 3.79/0.99  --extra_neg_conj                        none
% 3.79/0.99  --large_theory_mode                     true
% 3.79/0.99  --prolific_symb_bound                   200
% 3.79/0.99  --lt_threshold                          2000
% 3.79/0.99  --clause_weak_htbl                      true
% 3.79/0.99  --gc_record_bc_elim                     false
% 3.79/0.99  
% 3.79/0.99  ------ Preprocessing Options
% 3.79/0.99  
% 3.79/0.99  --preprocessing_flag                    true
% 3.79/0.99  --time_out_prep_mult                    0.1
% 3.79/0.99  --splitting_mode                        input
% 3.79/0.99  --splitting_grd                         true
% 3.79/0.99  --splitting_cvd                         false
% 3.79/0.99  --splitting_cvd_svl                     false
% 3.79/0.99  --splitting_nvd                         32
% 3.79/0.99  --sub_typing                            true
% 3.79/0.99  --prep_gs_sim                           true
% 3.79/0.99  --prep_unflatten                        true
% 3.79/0.99  --prep_res_sim                          true
% 3.79/0.99  --prep_upred                            true
% 3.79/0.99  --prep_sem_filter                       exhaustive
% 3.79/0.99  --prep_sem_filter_out                   false
% 3.79/0.99  --pred_elim                             true
% 3.79/0.99  --res_sim_input                         true
% 3.79/0.99  --eq_ax_congr_red                       true
% 3.79/0.99  --pure_diseq_elim                       true
% 3.79/0.99  --brand_transform                       false
% 3.79/0.99  --non_eq_to_eq                          false
% 3.79/0.99  --prep_def_merge                        true
% 3.79/0.99  --prep_def_merge_prop_impl              false
% 3.79/0.99  --prep_def_merge_mbd                    true
% 3.79/0.99  --prep_def_merge_tr_red                 false
% 3.79/0.99  --prep_def_merge_tr_cl                  false
% 3.79/0.99  --smt_preprocessing                     true
% 3.79/0.99  --smt_ac_axioms                         fast
% 3.79/0.99  --preprocessed_out                      false
% 3.79/0.99  --preprocessed_stats                    false
% 3.79/0.99  
% 3.79/0.99  ------ Abstraction refinement Options
% 3.79/0.99  
% 3.79/0.99  --abstr_ref                             []
% 3.79/0.99  --abstr_ref_prep                        false
% 3.79/0.99  --abstr_ref_until_sat                   false
% 3.79/0.99  --abstr_ref_sig_restrict                funpre
% 3.79/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.79/0.99  --abstr_ref_under                       []
% 3.79/0.99  
% 3.79/0.99  ------ SAT Options
% 3.79/0.99  
% 3.79/0.99  --sat_mode                              false
% 3.79/0.99  --sat_fm_restart_options                ""
% 3.79/0.99  --sat_gr_def                            false
% 3.79/0.99  --sat_epr_types                         true
% 3.79/0.99  --sat_non_cyclic_types                  false
% 3.79/0.99  --sat_finite_models                     false
% 3.79/0.99  --sat_fm_lemmas                         false
% 3.79/0.99  --sat_fm_prep                           false
% 3.79/0.99  --sat_fm_uc_incr                        true
% 3.79/0.99  --sat_out_model                         small
% 3.79/0.99  --sat_out_clauses                       false
% 3.79/0.99  
% 3.79/0.99  ------ QBF Options
% 3.79/0.99  
% 3.79/0.99  --qbf_mode                              false
% 3.79/0.99  --qbf_elim_univ                         false
% 3.79/0.99  --qbf_dom_inst                          none
% 3.79/0.99  --qbf_dom_pre_inst                      false
% 3.79/0.99  --qbf_sk_in                             false
% 3.79/0.99  --qbf_pred_elim                         true
% 3.79/0.99  --qbf_split                             512
% 3.79/0.99  
% 3.79/0.99  ------ BMC1 Options
% 3.79/0.99  
% 3.79/0.99  --bmc1_incremental                      false
% 3.79/0.99  --bmc1_axioms                           reachable_all
% 3.79/0.99  --bmc1_min_bound                        0
% 3.79/0.99  --bmc1_max_bound                        -1
% 3.79/0.99  --bmc1_max_bound_default                -1
% 3.79/0.99  --bmc1_symbol_reachability              true
% 3.79/0.99  --bmc1_property_lemmas                  false
% 3.79/0.99  --bmc1_k_induction                      false
% 3.79/0.99  --bmc1_non_equiv_states                 false
% 3.79/0.99  --bmc1_deadlock                         false
% 3.79/0.99  --bmc1_ucm                              false
% 3.79/0.99  --bmc1_add_unsat_core                   none
% 3.79/0.99  --bmc1_unsat_core_children              false
% 3.79/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.79/0.99  --bmc1_out_stat                         full
% 3.79/0.99  --bmc1_ground_init                      false
% 3.79/0.99  --bmc1_pre_inst_next_state              false
% 3.79/0.99  --bmc1_pre_inst_state                   false
% 3.79/0.99  --bmc1_pre_inst_reach_state             false
% 3.79/0.99  --bmc1_out_unsat_core                   false
% 3.79/0.99  --bmc1_aig_witness_out                  false
% 3.79/0.99  --bmc1_verbose                          false
% 3.79/0.99  --bmc1_dump_clauses_tptp                false
% 3.79/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.79/0.99  --bmc1_dump_file                        -
% 3.79/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.79/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.79/0.99  --bmc1_ucm_extend_mode                  1
% 3.79/0.99  --bmc1_ucm_init_mode                    2
% 3.79/0.99  --bmc1_ucm_cone_mode                    none
% 3.79/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.79/0.99  --bmc1_ucm_relax_model                  4
% 3.79/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.79/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.79/0.99  --bmc1_ucm_layered_model                none
% 3.79/0.99  --bmc1_ucm_max_lemma_size               10
% 3.79/0.99  
% 3.79/0.99  ------ AIG Options
% 3.79/0.99  
% 3.79/0.99  --aig_mode                              false
% 3.79/0.99  
% 3.79/0.99  ------ Instantiation Options
% 3.79/0.99  
% 3.79/0.99  --instantiation_flag                    true
% 3.79/0.99  --inst_sos_flag                         true
% 3.79/0.99  --inst_sos_phase                        true
% 3.79/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.79/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.79/0.99  --inst_lit_sel_side                     num_symb
% 3.79/0.99  --inst_solver_per_active                1400
% 3.79/0.99  --inst_solver_calls_frac                1.
% 3.79/0.99  --inst_passive_queue_type               priority_queues
% 3.79/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.79/0.99  --inst_passive_queues_freq              [25;2]
% 3.79/0.99  --inst_dismatching                      true
% 3.79/0.99  --inst_eager_unprocessed_to_passive     true
% 3.79/0.99  --inst_prop_sim_given                   true
% 3.79/0.99  --inst_prop_sim_new                     false
% 3.79/0.99  --inst_subs_new                         false
% 3.79/0.99  --inst_eq_res_simp                      false
% 3.79/0.99  --inst_subs_given                       false
% 3.79/0.99  --inst_orphan_elimination               true
% 3.79/0.99  --inst_learning_loop_flag               true
% 3.79/0.99  --inst_learning_start                   3000
% 3.79/0.99  --inst_learning_factor                  2
% 3.79/0.99  --inst_start_prop_sim_after_learn       3
% 3.79/0.99  --inst_sel_renew                        solver
% 3.79/0.99  --inst_lit_activity_flag                true
% 3.79/0.99  --inst_restr_to_given                   false
% 3.79/0.99  --inst_activity_threshold               500
% 3.79/0.99  --inst_out_proof                        true
% 3.79/0.99  
% 3.79/0.99  ------ Resolution Options
% 3.79/0.99  
% 3.79/0.99  --resolution_flag                       true
% 3.79/0.99  --res_lit_sel                           adaptive
% 3.79/0.99  --res_lit_sel_side                      none
% 3.79/0.99  --res_ordering                          kbo
% 3.79/0.99  --res_to_prop_solver                    active
% 3.79/0.99  --res_prop_simpl_new                    false
% 3.79/0.99  --res_prop_simpl_given                  true
% 3.79/0.99  --res_passive_queue_type                priority_queues
% 3.79/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.79/0.99  --res_passive_queues_freq               [15;5]
% 3.79/0.99  --res_forward_subs                      full
% 3.79/0.99  --res_backward_subs                     full
% 3.79/0.99  --res_forward_subs_resolution           true
% 3.79/0.99  --res_backward_subs_resolution          true
% 3.79/0.99  --res_orphan_elimination                true
% 3.79/0.99  --res_time_limit                        2.
% 3.79/0.99  --res_out_proof                         true
% 3.79/0.99  
% 3.79/0.99  ------ Superposition Options
% 3.79/0.99  
% 3.79/0.99  --superposition_flag                    true
% 3.79/0.99  --sup_passive_queue_type                priority_queues
% 3.79/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.79/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.79/0.99  --demod_completeness_check              fast
% 3.79/0.99  --demod_use_ground                      true
% 3.79/0.99  --sup_to_prop_solver                    passive
% 3.79/0.99  --sup_prop_simpl_new                    true
% 3.79/0.99  --sup_prop_simpl_given                  true
% 3.79/0.99  --sup_fun_splitting                     true
% 3.79/0.99  --sup_smt_interval                      50000
% 3.79/0.99  
% 3.79/0.99  ------ Superposition Simplification Setup
% 3.79/0.99  
% 3.79/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.79/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.79/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.79/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.79/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.79/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.79/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.79/0.99  --sup_immed_triv                        [TrivRules]
% 3.79/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.79/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.79/0.99  --sup_immed_bw_main                     []
% 3.79/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.79/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.79/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.79/0.99  --sup_input_bw                          []
% 3.79/0.99  
% 3.79/0.99  ------ Combination Options
% 3.79/0.99  
% 3.79/0.99  --comb_res_mult                         3
% 3.79/0.99  --comb_sup_mult                         2
% 3.79/0.99  --comb_inst_mult                        10
% 3.79/0.99  
% 3.79/0.99  ------ Debug Options
% 3.79/0.99  
% 3.79/0.99  --dbg_backtrace                         false
% 3.79/0.99  --dbg_dump_prop_clauses                 false
% 3.79/0.99  --dbg_dump_prop_clauses_file            -
% 3.79/0.99  --dbg_out_stat                          false
% 3.79/0.99  ------ Parsing...
% 3.79/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.79/0.99  
% 3.79/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.79/0.99  
% 3.79/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.79/0.99  
% 3.79/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.79/0.99  ------ Proving...
% 3.79/0.99  ------ Problem Properties 
% 3.79/0.99  
% 3.79/0.99  
% 3.79/0.99  clauses                                 22
% 3.79/0.99  conjectures                             5
% 3.79/0.99  EPR                                     4
% 3.79/0.99  Horn                                    17
% 3.79/0.99  unary                                   5
% 3.79/0.99  binary                                  5
% 3.79/0.99  lits                                    63
% 3.79/0.99  lits eq                                 5
% 3.79/0.99  fd_pure                                 0
% 3.79/0.99  fd_pseudo                               0
% 3.79/0.99  fd_cond                                 0
% 3.79/0.99  fd_pseudo_cond                          5
% 3.79/0.99  AC symbols                              0
% 3.79/0.99  
% 3.79/0.99  ------ Schedule dynamic 5 is on 
% 3.79/0.99  
% 3.79/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.79/0.99  
% 3.79/0.99  
% 3.79/0.99  ------ 
% 3.79/0.99  Current options:
% 3.79/0.99  ------ 
% 3.79/0.99  
% 3.79/0.99  ------ Input Options
% 3.79/0.99  
% 3.79/0.99  --out_options                           all
% 3.79/0.99  --tptp_safe_out                         true
% 3.79/0.99  --problem_path                          ""
% 3.79/0.99  --include_path                          ""
% 3.79/0.99  --clausifier                            res/vclausify_rel
% 3.79/0.99  --clausifier_options                    ""
% 3.79/0.99  --stdin                                 false
% 3.79/0.99  --stats_out                             all
% 3.79/0.99  
% 3.79/0.99  ------ General Options
% 3.79/0.99  
% 3.79/0.99  --fof                                   false
% 3.79/0.99  --time_out_real                         305.
% 3.79/0.99  --time_out_virtual                      -1.
% 3.79/0.99  --symbol_type_check                     false
% 3.79/0.99  --clausify_out                          false
% 3.79/0.99  --sig_cnt_out                           false
% 3.79/0.99  --trig_cnt_out                          false
% 3.79/0.99  --trig_cnt_out_tolerance                1.
% 3.79/0.99  --trig_cnt_out_sk_spl                   false
% 3.79/0.99  --abstr_cl_out                          false
% 3.79/0.99  
% 3.79/0.99  ------ Global Options
% 3.79/0.99  
% 3.79/0.99  --schedule                              default
% 3.79/0.99  --add_important_lit                     false
% 3.79/0.99  --prop_solver_per_cl                    1000
% 3.79/0.99  --min_unsat_core                        false
% 3.79/0.99  --soft_assumptions                      false
% 3.79/0.99  --soft_lemma_size                       3
% 3.79/0.99  --prop_impl_unit_size                   0
% 3.79/0.99  --prop_impl_unit                        []
% 3.79/0.99  --share_sel_clauses                     true
% 3.79/0.99  --reset_solvers                         false
% 3.79/0.99  --bc_imp_inh                            [conj_cone]
% 3.79/0.99  --conj_cone_tolerance                   3.
% 3.79/0.99  --extra_neg_conj                        none
% 3.79/0.99  --large_theory_mode                     true
% 3.79/0.99  --prolific_symb_bound                   200
% 3.79/0.99  --lt_threshold                          2000
% 3.79/0.99  --clause_weak_htbl                      true
% 3.79/0.99  --gc_record_bc_elim                     false
% 3.79/0.99  
% 3.79/0.99  ------ Preprocessing Options
% 3.79/0.99  
% 3.79/0.99  --preprocessing_flag                    true
% 3.79/0.99  --time_out_prep_mult                    0.1
% 3.79/0.99  --splitting_mode                        input
% 3.79/0.99  --splitting_grd                         true
% 3.79/0.99  --splitting_cvd                         false
% 3.79/0.99  --splitting_cvd_svl                     false
% 3.79/0.99  --splitting_nvd                         32
% 3.79/0.99  --sub_typing                            true
% 3.79/0.99  --prep_gs_sim                           true
% 3.79/0.99  --prep_unflatten                        true
% 3.79/0.99  --prep_res_sim                          true
% 3.79/0.99  --prep_upred                            true
% 3.79/0.99  --prep_sem_filter                       exhaustive
% 3.79/0.99  --prep_sem_filter_out                   false
% 3.79/0.99  --pred_elim                             true
% 3.79/0.99  --res_sim_input                         true
% 3.79/0.99  --eq_ax_congr_red                       true
% 3.79/0.99  --pure_diseq_elim                       true
% 3.79/0.99  --brand_transform                       false
% 3.79/0.99  --non_eq_to_eq                          false
% 3.79/0.99  --prep_def_merge                        true
% 3.79/0.99  --prep_def_merge_prop_impl              false
% 3.79/0.99  --prep_def_merge_mbd                    true
% 3.79/0.99  --prep_def_merge_tr_red                 false
% 3.79/0.99  --prep_def_merge_tr_cl                  false
% 3.79/0.99  --smt_preprocessing                     true
% 3.79/0.99  --smt_ac_axioms                         fast
% 3.79/0.99  --preprocessed_out                      false
% 3.79/0.99  --preprocessed_stats                    false
% 3.79/0.99  
% 3.79/0.99  ------ Abstraction refinement Options
% 3.79/0.99  
% 3.79/0.99  --abstr_ref                             []
% 3.79/0.99  --abstr_ref_prep                        false
% 3.79/0.99  --abstr_ref_until_sat                   false
% 3.79/0.99  --abstr_ref_sig_restrict                funpre
% 3.79/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.79/0.99  --abstr_ref_under                       []
% 3.79/0.99  
% 3.79/0.99  ------ SAT Options
% 3.79/0.99  
% 3.79/0.99  --sat_mode                              false
% 3.79/0.99  --sat_fm_restart_options                ""
% 3.79/0.99  --sat_gr_def                            false
% 3.79/0.99  --sat_epr_types                         true
% 3.79/0.99  --sat_non_cyclic_types                  false
% 3.79/0.99  --sat_finite_models                     false
% 3.79/0.99  --sat_fm_lemmas                         false
% 3.79/0.99  --sat_fm_prep                           false
% 3.79/0.99  --sat_fm_uc_incr                        true
% 3.79/0.99  --sat_out_model                         small
% 3.79/0.99  --sat_out_clauses                       false
% 3.79/0.99  
% 3.79/0.99  ------ QBF Options
% 3.79/0.99  
% 3.79/0.99  --qbf_mode                              false
% 3.79/0.99  --qbf_elim_univ                         false
% 3.79/0.99  --qbf_dom_inst                          none
% 3.79/0.99  --qbf_dom_pre_inst                      false
% 3.79/0.99  --qbf_sk_in                             false
% 3.79/0.99  --qbf_pred_elim                         true
% 3.79/0.99  --qbf_split                             512
% 3.79/0.99  
% 3.79/0.99  ------ BMC1 Options
% 3.79/0.99  
% 3.79/0.99  --bmc1_incremental                      false
% 3.79/0.99  --bmc1_axioms                           reachable_all
% 3.79/0.99  --bmc1_min_bound                        0
% 3.79/0.99  --bmc1_max_bound                        -1
% 3.79/0.99  --bmc1_max_bound_default                -1
% 3.79/0.99  --bmc1_symbol_reachability              true
% 3.79/0.99  --bmc1_property_lemmas                  false
% 3.79/0.99  --bmc1_k_induction                      false
% 3.79/0.99  --bmc1_non_equiv_states                 false
% 3.79/0.99  --bmc1_deadlock                         false
% 3.79/0.99  --bmc1_ucm                              false
% 3.79/0.99  --bmc1_add_unsat_core                   none
% 3.79/0.99  --bmc1_unsat_core_children              false
% 3.79/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.79/0.99  --bmc1_out_stat                         full
% 3.79/0.99  --bmc1_ground_init                      false
% 3.79/0.99  --bmc1_pre_inst_next_state              false
% 3.79/0.99  --bmc1_pre_inst_state                   false
% 3.79/0.99  --bmc1_pre_inst_reach_state             false
% 3.79/0.99  --bmc1_out_unsat_core                   false
% 3.79/0.99  --bmc1_aig_witness_out                  false
% 3.79/0.99  --bmc1_verbose                          false
% 3.79/0.99  --bmc1_dump_clauses_tptp                false
% 3.79/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.79/0.99  --bmc1_dump_file                        -
% 3.79/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.79/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.79/0.99  --bmc1_ucm_extend_mode                  1
% 3.79/0.99  --bmc1_ucm_init_mode                    2
% 3.79/0.99  --bmc1_ucm_cone_mode                    none
% 3.79/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.79/0.99  --bmc1_ucm_relax_model                  4
% 3.79/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.79/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.79/0.99  --bmc1_ucm_layered_model                none
% 3.79/0.99  --bmc1_ucm_max_lemma_size               10
% 3.79/0.99  
% 3.79/0.99  ------ AIG Options
% 3.79/0.99  
% 3.79/0.99  --aig_mode                              false
% 3.79/0.99  
% 3.79/0.99  ------ Instantiation Options
% 3.79/0.99  
% 3.79/0.99  --instantiation_flag                    true
% 3.79/0.99  --inst_sos_flag                         true
% 3.79/0.99  --inst_sos_phase                        true
% 3.79/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.79/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.79/0.99  --inst_lit_sel_side                     none
% 3.79/0.99  --inst_solver_per_active                1400
% 3.79/0.99  --inst_solver_calls_frac                1.
% 3.79/0.99  --inst_passive_queue_type               priority_queues
% 3.79/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.79/0.99  --inst_passive_queues_freq              [25;2]
% 3.79/0.99  --inst_dismatching                      true
% 3.79/0.99  --inst_eager_unprocessed_to_passive     true
% 3.79/0.99  --inst_prop_sim_given                   true
% 3.79/0.99  --inst_prop_sim_new                     false
% 3.79/0.99  --inst_subs_new                         false
% 3.79/0.99  --inst_eq_res_simp                      false
% 3.79/0.99  --inst_subs_given                       false
% 3.79/0.99  --inst_orphan_elimination               true
% 3.79/0.99  --inst_learning_loop_flag               true
% 3.79/0.99  --inst_learning_start                   3000
% 3.79/0.99  --inst_learning_factor                  2
% 3.79/0.99  --inst_start_prop_sim_after_learn       3
% 3.79/0.99  --inst_sel_renew                        solver
% 3.79/0.99  --inst_lit_activity_flag                true
% 3.79/0.99  --inst_restr_to_given                   false
% 3.79/0.99  --inst_activity_threshold               500
% 3.79/0.99  --inst_out_proof                        true
% 3.79/0.99  
% 3.79/0.99  ------ Resolution Options
% 3.79/0.99  
% 3.79/0.99  --resolution_flag                       false
% 3.79/0.99  --res_lit_sel                           adaptive
% 3.79/0.99  --res_lit_sel_side                      none
% 3.79/0.99  --res_ordering                          kbo
% 3.79/0.99  --res_to_prop_solver                    active
% 3.79/0.99  --res_prop_simpl_new                    false
% 3.79/0.99  --res_prop_simpl_given                  true
% 3.79/0.99  --res_passive_queue_type                priority_queues
% 3.79/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.79/0.99  --res_passive_queues_freq               [15;5]
% 3.79/0.99  --res_forward_subs                      full
% 3.79/0.99  --res_backward_subs                     full
% 3.79/0.99  --res_forward_subs_resolution           true
% 3.79/0.99  --res_backward_subs_resolution          true
% 3.79/0.99  --res_orphan_elimination                true
% 3.79/0.99  --res_time_limit                        2.
% 3.79/0.99  --res_out_proof                         true
% 3.79/0.99  
% 3.79/0.99  ------ Superposition Options
% 3.79/0.99  
% 3.79/0.99  --superposition_flag                    true
% 3.79/0.99  --sup_passive_queue_type                priority_queues
% 3.79/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.79/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.79/0.99  --demod_completeness_check              fast
% 3.79/0.99  --demod_use_ground                      true
% 3.79/0.99  --sup_to_prop_solver                    passive
% 3.79/0.99  --sup_prop_simpl_new                    true
% 3.79/0.99  --sup_prop_simpl_given                  true
% 3.79/0.99  --sup_fun_splitting                     true
% 3.79/0.99  --sup_smt_interval                      50000
% 3.79/0.99  
% 3.79/0.99  ------ Superposition Simplification Setup
% 3.79/0.99  
% 3.79/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.79/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.79/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.79/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.79/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.79/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.79/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.79/0.99  --sup_immed_triv                        [TrivRules]
% 3.79/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.79/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.79/0.99  --sup_immed_bw_main                     []
% 3.79/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.79/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.79/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.79/0.99  --sup_input_bw                          []
% 3.79/0.99  
% 3.79/0.99  ------ Combination Options
% 3.79/0.99  
% 3.79/0.99  --comb_res_mult                         3
% 3.79/0.99  --comb_sup_mult                         2
% 3.79/0.99  --comb_inst_mult                        10
% 3.79/0.99  
% 3.79/0.99  ------ Debug Options
% 3.79/0.99  
% 3.79/0.99  --dbg_backtrace                         false
% 3.79/0.99  --dbg_dump_prop_clauses                 false
% 3.79/0.99  --dbg_dump_prop_clauses_file            -
% 3.79/0.99  --dbg_out_stat                          false
% 3.79/0.99  
% 3.79/0.99  
% 3.79/0.99  
% 3.79/0.99  
% 3.79/0.99  ------ Proving...
% 3.79/0.99  
% 3.79/0.99  
% 3.79/0.99  % SZS status Theorem for theBenchmark.p
% 3.79/0.99  
% 3.79/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.79/0.99  
% 3.79/0.99  fof(f1,axiom,(
% 3.79/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.79/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.79/0.99  
% 3.79/0.99  fof(f8,plain,(
% 3.79/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.79/0.99    inference(ennf_transformation,[],[f1])).
% 3.79/0.99  
% 3.79/0.99  fof(f14,plain,(
% 3.79/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.79/0.99    inference(nnf_transformation,[],[f8])).
% 3.79/0.99  
% 3.79/0.99  fof(f15,plain,(
% 3.79/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.79/0.99    inference(rectify,[],[f14])).
% 3.79/0.99  
% 3.79/0.99  fof(f16,plain,(
% 3.79/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.79/0.99    introduced(choice_axiom,[])).
% 3.79/0.99  
% 3.79/0.99  fof(f17,plain,(
% 3.79/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.79/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).
% 3.79/0.99  
% 3.79/0.99  fof(f36,plain,(
% 3.79/0.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.79/0.99    inference(cnf_transformation,[],[f17])).
% 3.79/0.99  
% 3.79/0.99  fof(f4,axiom,(
% 3.79/0.99    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 3.79/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.79/0.99  
% 3.79/0.99  fof(f27,plain,(
% 3.79/0.99    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 3.79/0.99    inference(nnf_transformation,[],[f4])).
% 3.79/0.99  
% 3.79/0.99  fof(f28,plain,(
% 3.79/0.99    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 3.79/0.99    inference(rectify,[],[f27])).
% 3.79/0.99  
% 3.79/0.99  fof(f31,plain,(
% 3.79/0.99    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0))),
% 3.79/0.99    introduced(choice_axiom,[])).
% 3.79/0.99  
% 3.79/0.99  fof(f30,plain,(
% 3.79/0.99    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) => r2_hidden(k4_tarski(X2,sK6(X0,X1)),X0))) )),
% 3.79/0.99    introduced(choice_axiom,[])).
% 3.79/0.99  
% 3.79/0.99  fof(f29,plain,(
% 3.79/0.99    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK5(X0,X1),X3),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK5(X0,X1),X4),X0) | r2_hidden(sK5(X0,X1),X1))))),
% 3.79/0.99    introduced(choice_axiom,[])).
% 3.79/0.99  
% 3.79/0.99  fof(f32,plain,(
% 3.79/0.99    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK5(X0,X1),X3),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0) | r2_hidden(sK5(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 3.79/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f28,f31,f30,f29])).
% 3.79/0.99  
% 3.79/0.99  fof(f49,plain,(
% 3.79/0.99    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 3.79/0.99    inference(cnf_transformation,[],[f32])).
% 3.79/0.99  
% 3.79/0.99  fof(f61,plain,(
% 3.79/0.99    ( ! [X6,X0,X5] : (r2_hidden(X5,k1_relat_1(X0)) | ~r2_hidden(k4_tarski(X5,X6),X0)) )),
% 3.79/0.99    inference(equality_resolution,[],[f49])).
% 3.79/0.99  
% 3.79/0.99  fof(f5,axiom,(
% 3.79/0.99    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 3.79/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.79/0.99  
% 3.79/0.99  fof(f11,plain,(
% 3.79/0.99    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 3.79/0.99    inference(ennf_transformation,[],[f5])).
% 3.79/0.99  
% 3.79/0.99  fof(f52,plain,(
% 3.79/0.99    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 3.79/0.99    inference(cnf_transformation,[],[f11])).
% 3.79/0.99  
% 3.79/0.99  fof(f2,axiom,(
% 3.79/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (v1_relat_1(X2) => (k7_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1))))))),
% 3.79/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.79/1.00  
% 3.79/1.00  fof(f9,plain,(
% 3.79/1.00    ! [X0] : (! [X1,X2] : ((k7_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 3.79/1.00    inference(ennf_transformation,[],[f2])).
% 3.79/1.00  
% 3.79/1.00  fof(f18,plain,(
% 3.79/1.00    ! [X0] : (! [X1,X2] : (((k7_relat_1(X0,X1) = X2 | ? [X3,X4] : (((~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | (~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1))) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k7_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 3.79/1.00    inference(nnf_transformation,[],[f9])).
% 3.79/1.00  
% 3.79/1.00  fof(f19,plain,(
% 3.79/1.00    ! [X0] : (! [X1,X2] : (((k7_relat_1(X0,X1) = X2 | ? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k7_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 3.79/1.00    inference(flattening,[],[f18])).
% 3.79/1.00  
% 3.79/1.00  fof(f20,plain,(
% 3.79/1.00    ! [X0] : (! [X1,X2] : (((k7_relat_1(X0,X1) = X2 | ? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X5,X6] : ((r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(X5,X1)) & ((r2_hidden(k4_tarski(X5,X6),X0) & r2_hidden(X5,X1)) | ~r2_hidden(k4_tarski(X5,X6),X2))) | k7_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 3.79/1.00    inference(rectify,[],[f19])).
% 3.79/1.00  
% 3.79/1.00  fof(f21,plain,(
% 3.79/1.00    ! [X2,X1,X0] : (? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | r2_hidden(k4_tarski(X3,X4),X2))) => ((~r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X0) | ~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X0) & r2_hidden(sK1(X0,X1,X2),X1)) | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2))))),
% 3.79/1.00    introduced(choice_axiom,[])).
% 3.79/1.00  
% 3.79/1.00  fof(f22,plain,(
% 3.79/1.00    ! [X0] : (! [X1,X2] : (((k7_relat_1(X0,X1) = X2 | ((~r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X0) | ~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X0) & r2_hidden(sK1(X0,X1,X2),X1)) | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2)))) & (! [X5,X6] : ((r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(X5,X1)) & ((r2_hidden(k4_tarski(X5,X6),X0) & r2_hidden(X5,X1)) | ~r2_hidden(k4_tarski(X5,X6),X2))) | k7_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 3.79/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f20,f21])).
% 3.79/1.00  
% 3.79/1.00  fof(f41,plain,(
% 3.79/1.00    ( ! [X6,X2,X0,X5,X1] : (r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(X5,X1) | k7_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 3.79/1.00    inference(cnf_transformation,[],[f22])).
% 3.79/1.00  
% 3.79/1.00  fof(f58,plain,(
% 3.79/1.00    ( ! [X6,X0,X5,X1] : (r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1)) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(X5,X1) | ~v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 3.79/1.00    inference(equality_resolution,[],[f41])).
% 3.79/1.00  
% 3.79/1.00  fof(f3,axiom,(
% 3.79/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X0) => r2_hidden(k4_tarski(X2,X3),X1))))),
% 3.79/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.79/1.00  
% 3.79/1.00  fof(f10,plain,(
% 3.79/1.00    ! [X0] : (! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0))) | ~v1_relat_1(X0))),
% 3.79/1.00    inference(ennf_transformation,[],[f3])).
% 3.79/1.00  
% 3.79/1.00  fof(f23,plain,(
% 3.79/1.00    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | ? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0))) & (! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 3.79/1.00    inference(nnf_transformation,[],[f10])).
% 3.79/1.00  
% 3.79/1.00  fof(f24,plain,(
% 3.79/1.00    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | ? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0))) & (! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 3.79/1.00    inference(rectify,[],[f23])).
% 3.79/1.00  
% 3.79/1.00  fof(f25,plain,(
% 3.79/1.00    ! [X1,X0] : (? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0)) => (~r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) & r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0)))),
% 3.79/1.00    introduced(choice_axiom,[])).
% 3.79/1.00  
% 3.79/1.00  fof(f26,plain,(
% 3.79/1.00    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | (~r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) & r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0))) & (! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 3.79/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f24,f25])).
% 3.79/1.00  
% 3.79/1.00  fof(f47,plain,(
% 3.79/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) | ~v1_relat_1(X0)) )),
% 3.79/1.00    inference(cnf_transformation,[],[f26])).
% 3.79/1.00  
% 3.79/1.00  fof(f6,conjecture,(
% 3.79/1.00    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => ((r1_tarski(X2,X1) & r1_tarski(k1_relat_1(X2),X0)) => r1_tarski(X2,k7_relat_1(X1,X0)))))),
% 3.79/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.79/1.00  
% 3.79/1.00  fof(f7,negated_conjecture,(
% 3.79/1.00    ~! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => ((r1_tarski(X2,X1) & r1_tarski(k1_relat_1(X2),X0)) => r1_tarski(X2,k7_relat_1(X1,X0)))))),
% 3.79/1.00    inference(negated_conjecture,[],[f6])).
% 3.79/1.00  
% 3.79/1.00  fof(f12,plain,(
% 3.79/1.00    ? [X0,X1] : (? [X2] : ((~r1_tarski(X2,k7_relat_1(X1,X0)) & (r1_tarski(X2,X1) & r1_tarski(k1_relat_1(X2),X0))) & v1_relat_1(X2)) & v1_relat_1(X1))),
% 3.79/1.00    inference(ennf_transformation,[],[f7])).
% 3.79/1.00  
% 3.79/1.00  fof(f13,plain,(
% 3.79/1.00    ? [X0,X1] : (? [X2] : (~r1_tarski(X2,k7_relat_1(X1,X0)) & r1_tarski(X2,X1) & r1_tarski(k1_relat_1(X2),X0) & v1_relat_1(X2)) & v1_relat_1(X1))),
% 3.79/1.00    inference(flattening,[],[f12])).
% 3.79/1.00  
% 3.79/1.00  fof(f34,plain,(
% 3.79/1.00    ( ! [X0,X1] : (? [X2] : (~r1_tarski(X2,k7_relat_1(X1,X0)) & r1_tarski(X2,X1) & r1_tarski(k1_relat_1(X2),X0) & v1_relat_1(X2)) => (~r1_tarski(sK10,k7_relat_1(X1,X0)) & r1_tarski(sK10,X1) & r1_tarski(k1_relat_1(sK10),X0) & v1_relat_1(sK10))) )),
% 3.79/1.00    introduced(choice_axiom,[])).
% 3.79/1.00  
% 3.79/1.00  fof(f33,plain,(
% 3.79/1.00    ? [X0,X1] : (? [X2] : (~r1_tarski(X2,k7_relat_1(X1,X0)) & r1_tarski(X2,X1) & r1_tarski(k1_relat_1(X2),X0) & v1_relat_1(X2)) & v1_relat_1(X1)) => (? [X2] : (~r1_tarski(X2,k7_relat_1(sK9,sK8)) & r1_tarski(X2,sK9) & r1_tarski(k1_relat_1(X2),sK8) & v1_relat_1(X2)) & v1_relat_1(sK9))),
% 3.79/1.00    introduced(choice_axiom,[])).
% 3.79/1.00  
% 3.79/1.00  fof(f35,plain,(
% 3.79/1.00    (~r1_tarski(sK10,k7_relat_1(sK9,sK8)) & r1_tarski(sK10,sK9) & r1_tarski(k1_relat_1(sK10),sK8) & v1_relat_1(sK10)) & v1_relat_1(sK9)),
% 3.79/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f13,f34,f33])).
% 3.79/1.00  
% 3.79/1.00  fof(f57,plain,(
% 3.79/1.00    ~r1_tarski(sK10,k7_relat_1(sK9,sK8))),
% 3.79/1.00    inference(cnf_transformation,[],[f35])).
% 3.79/1.00  
% 3.79/1.00  fof(f46,plain,(
% 3.79/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) | ~v1_relat_1(X0)) )),
% 3.79/1.00    inference(cnf_transformation,[],[f26])).
% 3.79/1.00  
% 3.79/1.00  fof(f56,plain,(
% 3.79/1.00    r1_tarski(sK10,sK9)),
% 3.79/1.00    inference(cnf_transformation,[],[f35])).
% 3.79/1.00  
% 3.79/1.00  fof(f55,plain,(
% 3.79/1.00    r1_tarski(k1_relat_1(sK10),sK8)),
% 3.79/1.00    inference(cnf_transformation,[],[f35])).
% 3.79/1.00  
% 3.79/1.00  fof(f54,plain,(
% 3.79/1.00    v1_relat_1(sK10)),
% 3.79/1.00    inference(cnf_transformation,[],[f35])).
% 3.79/1.00  
% 3.79/1.00  fof(f53,plain,(
% 3.79/1.00    v1_relat_1(sK9)),
% 3.79/1.00    inference(cnf_transformation,[],[f35])).
% 3.79/1.00  
% 3.79/1.00  cnf(c_2,plain,
% 3.79/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 3.79/1.00      inference(cnf_transformation,[],[f36]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_1851,plain,
% 3.79/1.00      ( ~ r2_hidden(k4_tarski(sK3(X0,k7_relat_1(sK9,sK8)),sK4(X0,k7_relat_1(sK9,sK8))),X0)
% 3.79/1.00      | r2_hidden(k4_tarski(sK3(X0,k7_relat_1(sK9,sK8)),sK4(X0,k7_relat_1(sK9,sK8))),X1)
% 3.79/1.00      | ~ r1_tarski(X0,X1) ),
% 3.79/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_5478,plain,
% 3.79/1.00      ( r2_hidden(k4_tarski(sK3(sK10,k7_relat_1(sK9,sK8)),sK4(sK10,k7_relat_1(sK9,sK8))),sK9)
% 3.79/1.00      | ~ r2_hidden(k4_tarski(sK3(sK10,k7_relat_1(sK9,sK8)),sK4(sK10,k7_relat_1(sK9,sK8))),sK10)
% 3.79/1.00      | ~ r1_tarski(sK10,sK9) ),
% 3.79/1.00      inference(instantiation,[status(thm)],[c_1851]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_14,plain,
% 3.79/1.00      ( r2_hidden(X0,k1_relat_1(X1)) | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
% 3.79/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_1666,plain,
% 3.79/1.00      ( r2_hidden(sK3(sK10,k7_relat_1(sK9,sK8)),k1_relat_1(sK10))
% 3.79/1.00      | ~ r2_hidden(k4_tarski(sK3(sK10,k7_relat_1(sK9,sK8)),X0),sK10) ),
% 3.79/1.00      inference(instantiation,[status(thm)],[c_14]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_2869,plain,
% 3.79/1.00      ( r2_hidden(sK3(sK10,k7_relat_1(sK9,sK8)),k1_relat_1(sK10))
% 3.79/1.00      | ~ r2_hidden(k4_tarski(sK3(sK10,k7_relat_1(sK9,sK8)),sK4(sK10,k7_relat_1(sK9,sK8))),sK10) ),
% 3.79/1.00      inference(instantiation,[status(thm)],[c_1666]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_1068,plain,
% 3.79/1.00      ( ~ r2_hidden(sK3(sK10,k7_relat_1(sK9,sK8)),X0)
% 3.79/1.00      | r2_hidden(sK3(sK10,k7_relat_1(sK9,sK8)),sK8)
% 3.79/1.00      | ~ r1_tarski(X0,sK8) ),
% 3.79/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_1264,plain,
% 3.79/1.00      ( ~ r2_hidden(sK3(sK10,k7_relat_1(sK9,sK8)),k1_relat_1(sK10))
% 3.79/1.00      | r2_hidden(sK3(sK10,k7_relat_1(sK9,sK8)),sK8)
% 3.79/1.00      | ~ r1_tarski(k1_relat_1(sK10),sK8) ),
% 3.79/1.00      inference(instantiation,[status(thm)],[c_1068]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_16,plain,
% 3.79/1.00      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 3.79/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_913,plain,
% 3.79/1.00      ( v1_relat_1(k7_relat_1(sK9,sK8)) | ~ v1_relat_1(sK9) ),
% 3.79/1.00      inference(instantiation,[status(thm)],[c_16]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_6,plain,
% 3.79/1.00      ( ~ r2_hidden(X0,X1)
% 3.79/1.00      | ~ r2_hidden(k4_tarski(X0,X2),X3)
% 3.79/1.00      | r2_hidden(k4_tarski(X0,X2),k7_relat_1(X3,X1))
% 3.79/1.00      | ~ v1_relat_1(X3)
% 3.79/1.00      | ~ v1_relat_1(k7_relat_1(X3,X1)) ),
% 3.79/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_855,plain,
% 3.79/1.00      ( ~ r2_hidden(sK3(sK10,k7_relat_1(sK9,sK8)),sK8)
% 3.79/1.00      | r2_hidden(k4_tarski(sK3(sK10,k7_relat_1(sK9,sK8)),sK4(sK10,k7_relat_1(sK9,sK8))),k7_relat_1(sK9,sK8))
% 3.79/1.00      | ~ r2_hidden(k4_tarski(sK3(sK10,k7_relat_1(sK9,sK8)),sK4(sK10,k7_relat_1(sK9,sK8))),sK9)
% 3.79/1.00      | ~ v1_relat_1(k7_relat_1(sK9,sK8))
% 3.79/1.00      | ~ v1_relat_1(sK9) ),
% 3.79/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_9,plain,
% 3.79/1.00      ( ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)
% 3.79/1.00      | r1_tarski(X0,X1)
% 3.79/1.00      | ~ v1_relat_1(X0) ),
% 3.79/1.00      inference(cnf_transformation,[],[f47]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_17,negated_conjecture,
% 3.79/1.00      ( ~ r1_tarski(sK10,k7_relat_1(sK9,sK8)) ),
% 3.79/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_323,plain,
% 3.79/1.00      ( ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)
% 3.79/1.00      | ~ v1_relat_1(X0)
% 3.79/1.00      | k7_relat_1(sK9,sK8) != X1
% 3.79/1.00      | sK10 != X0 ),
% 3.79/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_17]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_324,plain,
% 3.79/1.00      ( ~ r2_hidden(k4_tarski(sK3(sK10,k7_relat_1(sK9,sK8)),sK4(sK10,k7_relat_1(sK9,sK8))),k7_relat_1(sK9,sK8))
% 3.79/1.00      | ~ v1_relat_1(sK10) ),
% 3.79/1.00      inference(unflattening,[status(thm)],[c_323]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_10,plain,
% 3.79/1.00      ( r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0)
% 3.79/1.00      | r1_tarski(X0,X1)
% 3.79/1.00      | ~ v1_relat_1(X0) ),
% 3.79/1.00      inference(cnf_transformation,[],[f46]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_312,plain,
% 3.79/1.00      ( r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0)
% 3.79/1.00      | ~ v1_relat_1(X0)
% 3.79/1.00      | k7_relat_1(sK9,sK8) != X1
% 3.79/1.00      | sK10 != X0 ),
% 3.79/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_17]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_313,plain,
% 3.79/1.00      ( r2_hidden(k4_tarski(sK3(sK10,k7_relat_1(sK9,sK8)),sK4(sK10,k7_relat_1(sK9,sK8))),sK10)
% 3.79/1.00      | ~ v1_relat_1(sK10) ),
% 3.79/1.00      inference(unflattening,[status(thm)],[c_312]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_18,negated_conjecture,
% 3.79/1.00      ( r1_tarski(sK10,sK9) ),
% 3.79/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_19,negated_conjecture,
% 3.79/1.00      ( r1_tarski(k1_relat_1(sK10),sK8) ),
% 3.79/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_20,negated_conjecture,
% 3.79/1.00      ( v1_relat_1(sK10) ),
% 3.79/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_21,negated_conjecture,
% 3.79/1.00      ( v1_relat_1(sK9) ),
% 3.79/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(contradiction,plain,
% 3.79/1.00      ( $false ),
% 3.79/1.00      inference(minisat,
% 3.79/1.00                [status(thm)],
% 3.79/1.00                [c_5478,c_2869,c_1264,c_913,c_855,c_324,c_313,c_18,c_19,
% 3.79/1.00                 c_20,c_21]) ).
% 3.79/1.00  
% 3.79/1.00  
% 3.79/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.79/1.00  
% 3.79/1.00  ------                               Statistics
% 3.79/1.00  
% 3.79/1.00  ------ General
% 3.79/1.00  
% 3.79/1.00  abstr_ref_over_cycles:                  0
% 3.79/1.00  abstr_ref_under_cycles:                 0
% 3.79/1.00  gc_basic_clause_elim:                   0
% 3.79/1.00  forced_gc_time:                         0
% 3.79/1.00  parsing_time:                           0.006
% 3.79/1.00  unif_index_cands_time:                  0.
% 3.79/1.00  unif_index_add_time:                    0.
% 3.79/1.00  orderings_time:                         0.
% 3.79/1.00  out_proof_time:                         0.007
% 3.79/1.00  total_time:                             0.181
% 3.79/1.00  num_of_symbols:                         48
% 3.79/1.00  num_of_terms:                           8298
% 3.79/1.00  
% 3.79/1.00  ------ Preprocessing
% 3.79/1.00  
% 3.79/1.00  num_of_splits:                          0
% 3.79/1.00  num_of_split_atoms:                     0
% 3.79/1.00  num_of_reused_defs:                     0
% 3.79/1.00  num_eq_ax_congr_red:                    36
% 3.79/1.00  num_of_sem_filtered_clauses:            1
% 3.79/1.00  num_of_subtypes:                        0
% 3.79/1.00  monotx_restored_types:                  0
% 3.79/1.00  sat_num_of_epr_types:                   0
% 3.79/1.00  sat_num_of_non_cyclic_types:            0
% 3.79/1.00  sat_guarded_non_collapsed_types:        0
% 3.79/1.00  num_pure_diseq_elim:                    0
% 3.79/1.00  simp_replaced_by:                       0
% 3.79/1.00  res_preprocessed:                       83
% 3.79/1.00  prep_upred:                             0
% 3.79/1.00  prep_unflattend:                        32
% 3.79/1.00  smt_new_axioms:                         0
% 3.79/1.00  pred_elim_cands:                        3
% 3.79/1.00  pred_elim:                              0
% 3.79/1.00  pred_elim_cl:                           0
% 3.79/1.00  pred_elim_cycles:                       1
% 3.79/1.00  merged_defs:                            0
% 3.79/1.00  merged_defs_ncl:                        0
% 3.79/1.00  bin_hyper_res:                          0
% 3.79/1.00  prep_cycles:                            3
% 3.79/1.00  pred_elim_time:                         0.002
% 3.79/1.00  splitting_time:                         0.
% 3.79/1.00  sem_filter_time:                        0.
% 3.79/1.00  monotx_time:                            0.
% 3.79/1.00  subtype_inf_time:                       0.
% 3.79/1.00  
% 3.79/1.00  ------ Problem properties
% 3.79/1.00  
% 3.79/1.00  clauses:                                22
% 3.79/1.00  conjectures:                            5
% 3.79/1.00  epr:                                    4
% 3.79/1.00  horn:                                   17
% 3.79/1.00  ground:                                 5
% 3.79/1.00  unary:                                  5
% 3.79/1.00  binary:                                 5
% 3.79/1.00  lits:                                   63
% 3.79/1.00  lits_eq:                                5
% 3.79/1.00  fd_pure:                                0
% 3.79/1.00  fd_pseudo:                              0
% 3.79/1.00  fd_cond:                                0
% 3.79/1.00  fd_pseudo_cond:                         5
% 3.79/1.00  ac_symbols:                             0
% 3.79/1.00  
% 3.79/1.00  ------ Propositional Solver
% 3.79/1.00  
% 3.79/1.00  prop_solver_calls:                      24
% 3.79/1.00  prop_fast_solver_calls:                 689
% 3.79/1.00  smt_solver_calls:                       0
% 3.79/1.00  smt_fast_solver_calls:                  0
% 3.79/1.00  prop_num_of_clauses:                    2794
% 3.79/1.00  prop_preprocess_simplified:             6850
% 3.79/1.00  prop_fo_subsumed:                       3
% 3.79/1.00  prop_solver_time:                       0.
% 3.79/1.00  smt_solver_time:                        0.
% 3.79/1.00  smt_fast_solver_time:                   0.
% 3.79/1.00  prop_fast_solver_time:                  0.
% 3.79/1.00  prop_unsat_core_time:                   0.
% 3.79/1.00  
% 3.79/1.00  ------ QBF
% 3.79/1.00  
% 3.79/1.00  qbf_q_res:                              0
% 3.79/1.00  qbf_num_tautologies:                    0
% 3.79/1.00  qbf_prep_cycles:                        0
% 3.79/1.00  
% 3.79/1.00  ------ BMC1
% 3.79/1.00  
% 3.79/1.00  bmc1_current_bound:                     -1
% 3.79/1.00  bmc1_last_solved_bound:                 -1
% 3.79/1.00  bmc1_unsat_core_size:                   -1
% 3.79/1.00  bmc1_unsat_core_parents_size:           -1
% 3.79/1.00  bmc1_merge_next_fun:                    0
% 3.79/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.79/1.00  
% 3.79/1.00  ------ Instantiation
% 3.79/1.00  
% 3.79/1.00  inst_num_of_clauses:                    582
% 3.79/1.00  inst_num_in_passive:                    330
% 3.79/1.00  inst_num_in_active:                     242
% 3.79/1.00  inst_num_in_unprocessed:                9
% 3.79/1.00  inst_num_of_loops:                      279
% 3.79/1.00  inst_num_of_learning_restarts:          0
% 3.79/1.00  inst_num_moves_active_passive:          35
% 3.79/1.00  inst_lit_activity:                      0
% 3.79/1.00  inst_lit_activity_moves:                0
% 3.79/1.00  inst_num_tautologies:                   0
% 3.79/1.00  inst_num_prop_implied:                  0
% 3.79/1.00  inst_num_existing_simplified:           0
% 3.79/1.00  inst_num_eq_res_simplified:             0
% 3.79/1.00  inst_num_child_elim:                    0
% 3.79/1.00  inst_num_of_dismatching_blockings:      253
% 3.79/1.00  inst_num_of_non_proper_insts:           473
% 3.79/1.00  inst_num_of_duplicates:                 0
% 3.79/1.00  inst_inst_num_from_inst_to_res:         0
% 3.79/1.00  inst_dismatching_checking_time:         0.
% 3.79/1.00  
% 3.79/1.00  ------ Resolution
% 3.79/1.00  
% 3.79/1.00  res_num_of_clauses:                     0
% 3.79/1.00  res_num_in_passive:                     0
% 3.79/1.00  res_num_in_active:                      0
% 3.79/1.00  res_num_of_loops:                       86
% 3.79/1.00  res_forward_subset_subsumed:            65
% 3.79/1.00  res_backward_subset_subsumed:           0
% 3.79/1.00  res_forward_subsumed:                   6
% 3.79/1.00  res_backward_subsumed:                  0
% 3.79/1.00  res_forward_subsumption_resolution:     0
% 3.79/1.00  res_backward_subsumption_resolution:    0
% 3.79/1.00  res_clause_to_clause_subsumption:       1257
% 3.79/1.00  res_orphan_elimination:                 0
% 3.79/1.00  res_tautology_del:                      24
% 3.79/1.00  res_num_eq_res_simplified:              0
% 3.79/1.00  res_num_sel_changes:                    0
% 3.79/1.00  res_moves_from_active_to_pass:          0
% 3.79/1.00  
% 3.79/1.00  ------ Superposition
% 3.79/1.00  
% 3.79/1.00  sup_time_total:                         0.
% 3.79/1.00  sup_time_generating:                    0.
% 3.79/1.00  sup_time_sim_full:                      0.
% 3.79/1.00  sup_time_sim_immed:                     0.
% 3.79/1.00  
% 3.79/1.00  sup_num_of_clauses:                     240
% 3.79/1.00  sup_num_in_active:                      54
% 3.79/1.00  sup_num_in_passive:                     186
% 3.79/1.00  sup_num_of_loops:                       54
% 3.79/1.00  sup_fw_superposition:                   123
% 3.79/1.00  sup_bw_superposition:                   129
% 3.79/1.00  sup_immediate_simplified:               12
% 3.79/1.00  sup_given_eliminated:                   0
% 3.79/1.00  comparisons_done:                       0
% 3.79/1.00  comparisons_avoided:                    0
% 3.79/1.00  
% 3.79/1.00  ------ Simplifications
% 3.79/1.00  
% 3.79/1.00  
% 3.79/1.00  sim_fw_subset_subsumed:                 4
% 3.79/1.00  sim_bw_subset_subsumed:                 0
% 3.79/1.00  sim_fw_subsumed:                        6
% 3.79/1.00  sim_bw_subsumed:                        3
% 3.79/1.00  sim_fw_subsumption_res:                 0
% 3.79/1.00  sim_bw_subsumption_res:                 0
% 3.79/1.00  sim_tautology_del:                      14
% 3.79/1.00  sim_eq_tautology_del:                   1
% 3.79/1.00  sim_eq_res_simp:                        1
% 3.79/1.00  sim_fw_demodulated:                     0
% 3.79/1.00  sim_bw_demodulated:                     0
% 3.79/1.00  sim_light_normalised:                   0
% 3.79/1.00  sim_joinable_taut:                      0
% 3.79/1.00  sim_joinable_simp:                      0
% 3.79/1.00  sim_ac_normalised:                      0
% 3.79/1.00  sim_smt_subsumption:                    0
% 3.79/1.00  
%------------------------------------------------------------------------------
