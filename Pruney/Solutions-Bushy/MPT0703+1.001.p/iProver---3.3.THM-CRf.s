%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0703+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:56 EST 2020

% Result     : Theorem 2.01s
% Output     : CNFRefutation 2.01s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 345 expanded)
%              Number of clauses        :   59 (  96 expanded)
%              Number of leaves         :   10 (  72 expanded)
%              Depth                    :   22
%              Number of atoms          :  427 (1651 expanded)
%              Number of equality atoms :  103 ( 208 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f18,plain,(
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

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f18])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f20])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(X0,k2_relat_1(X2))
          & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( r1_tarski(X0,k2_relat_1(X2))
            & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f28,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & r1_tarski(X0,k2_relat_1(X2))
        & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(sK5,sK6)
      & r1_tarski(sK5,k2_relat_1(sK7))
      & r1_tarski(k10_relat_1(sK7,sK5),k10_relat_1(sK7,sK6))
      & v1_funct_1(sK7)
      & v1_relat_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ~ r1_tarski(sK5,sK6)
    & r1_tarski(sK5,k2_relat_1(sK7))
    & r1_tarski(k10_relat_1(sK7,sK5),k10_relat_1(sK7,sK6))
    & v1_funct_1(sK7)
    & v1_relat_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f12,f28])).

fof(f48,plain,(
    r1_tarski(sK5,k2_relat_1(sK7)) ),
    inference(cnf_transformation,[],[f29])).

fof(f36,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X2
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ? [X7] :
                      ( k1_funct_1(X0,X7) = X5
                      & r2_hidden(X7,k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f22])).

fof(f26,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X5)) = X5
        & r2_hidden(sK4(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X1)) = X2
        & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k1_funct_1(X0,X3) != X2
                | ~ r2_hidden(X3,k1_relat_1(X0)) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( k1_funct_1(X0,X4) = X2
                & r2_hidden(X4,k1_relat_1(X0)) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( k1_funct_1(X0,X3) != sK2(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK2(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK2(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK2(X0,X1),X1) )
              & ( ( k1_funct_1(X0,sK3(X0,X1)) = sK2(X0,X1)
                  & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK2(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK4(X0,X5)) = X5
                    & r2_hidden(sK4(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f23,f26,f25,f24])).

fof(f40,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK4(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f55,plain,(
    ! [X0,X5] :
      ( k1_funct_1(X0,sK4(X0,X5)) = X5
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f40])).

fof(f46,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f29])).

fof(f45,plain,(
    v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f29])).

fof(f49,plain,(
    ~ r1_tarski(sK5,sK6) ),
    inference(cnf_transformation,[],[f29])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f6])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0))
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0)) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0))
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0)) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0))
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k1_funct_1(X0,X4),X1)
                  | ~ r2_hidden(X4,k1_relat_1(X0)) )
                & ( ( r2_hidden(k1_funct_1(X0,X4),X1)
                    & r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X4,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f14])).

fof(f16,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
            | ~ r2_hidden(X3,k1_relat_1(X0))
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
              & r2_hidden(X3,k1_relat_1(X0)) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(k1_funct_1(X0,sK0(X0,X1,X2)),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),k1_relat_1(X0))
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( r2_hidden(k1_funct_1(X0,sK0(X0,X1,X2)),X1)
            & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X0)) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ( ( ~ r2_hidden(k1_funct_1(X0,sK0(X0,X1,X2)),X1)
                | ~ r2_hidden(sK0(X0,X1,X2),k1_relat_1(X0))
                | ~ r2_hidden(sK0(X0,X1,X2),X2) )
              & ( ( r2_hidden(k1_funct_1(X0,sK0(X0,X1,X2)),X1)
                  & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X0)) )
                | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k1_funct_1(X0,X4),X1)
                  | ~ r2_hidden(X4,k1_relat_1(X0)) )
                & ( ( r2_hidden(k1_funct_1(X0,X4),X1)
                    & r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X4,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).

fof(f32,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(k1_funct_1(X0,X4),X1)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | k10_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f50,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k10_relat_1(X0,X1))
      | ~ r2_hidden(k1_funct_1(X0,X4),X1)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f32])).

fof(f39,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK4(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f56,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK4(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f39])).

fof(f47,plain,(
    r1_tarski(k10_relat_1(sK7,sK5),k10_relat_1(sK7,sK6)) ),
    inference(cnf_transformation,[],[f29])).

fof(f31,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X4),X1)
      | ~ r2_hidden(X4,X2)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f51,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X4),X1)
      | ~ r2_hidden(X4,k10_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f31])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_7,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1149,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_16,negated_conjecture,
    ( r1_tarski(sK5,k2_relat_1(sK7)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1146,plain,
    ( r1_tarski(sK5,k2_relat_1(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1148,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1655,plain,
    ( r2_hidden(X0,k2_relat_1(sK7)) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1146,c_1148])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | k1_funct_1(X1,sK4(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_18,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_438,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK4(X1,X0)) = X0
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_18])).

cnf(c_439,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK7))
    | ~ v1_relat_1(sK7)
    | k1_funct_1(sK7,sK4(sK7,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_438])).

cnf(c_19,negated_conjecture,
    ( v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_443,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK7))
    | k1_funct_1(sK7,sK4(sK7,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_439,c_19])).

cnf(c_1138,plain,
    ( k1_funct_1(sK7,sK4(sK7,X0)) = X0
    | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_443])).

cnf(c_1748,plain,
    ( k1_funct_1(sK7,sK4(sK7,X0)) = X0
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1655,c_1138])).

cnf(c_2562,plain,
    ( k1_funct_1(sK7,sK4(sK7,sK1(sK5,X0))) = sK1(sK5,X0)
    | r1_tarski(sK5,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1149,c_1748])).

cnf(c_15,negated_conjecture,
    ( ~ r1_tarski(sK5,sK6) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1147,plain,
    ( r1_tarski(sK5,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3462,plain,
    ( k1_funct_1(sK7,sK4(sK7,sK1(sK5,sK6))) = sK1(sK5,sK6) ),
    inference(superposition,[status(thm)],[c_2562,c_1147])).

cnf(c_3,plain,
    ( r2_hidden(X0,k10_relat_1(X1,X2))
    | ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k1_funct_1(X1,X0),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_534,plain,
    ( r2_hidden(X0,k10_relat_1(X1,X2))
    | ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k1_funct_1(X1,X0),X2)
    | ~ v1_relat_1(X1)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_18])).

cnf(c_535,plain,
    ( r2_hidden(X0,k10_relat_1(sK7,X1))
    | ~ r2_hidden(X0,k1_relat_1(sK7))
    | ~ r2_hidden(k1_funct_1(sK7,X0),X1)
    | ~ v1_relat_1(sK7) ),
    inference(unflattening,[status(thm)],[c_534])).

cnf(c_539,plain,
    ( ~ r2_hidden(k1_funct_1(sK7,X0),X1)
    | ~ r2_hidden(X0,k1_relat_1(sK7))
    | r2_hidden(X0,k10_relat_1(sK7,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_535,c_19])).

cnf(c_540,plain,
    ( r2_hidden(X0,k10_relat_1(sK7,X1))
    | ~ r2_hidden(X0,k1_relat_1(sK7))
    | ~ r2_hidden(k1_funct_1(sK7,X0),X1) ),
    inference(renaming,[status(thm)],[c_539])).

cnf(c_1133,plain,
    ( r2_hidden(X0,k10_relat_1(sK7,X1)) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
    | r2_hidden(k1_funct_1(sK7,X0),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_540])).

cnf(c_3475,plain,
    ( r2_hidden(sK4(sK7,sK1(sK5,sK6)),k10_relat_1(sK7,X0)) = iProver_top
    | r2_hidden(sK4(sK7,sK1(sK5,sK6)),k1_relat_1(sK7)) != iProver_top
    | r2_hidden(sK1(sK5,sK6),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3462,c_1133])).

cnf(c_23,plain,
    ( r1_tarski(sK5,k2_relat_1(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_244,plain,
    ( r2_hidden(sK1(X0,X1),X0)
    | sK6 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_15])).

cnf(c_245,plain,
    ( r2_hidden(sK1(sK5,sK6),sK5) ),
    inference(unflattening,[status(thm)],[c_244])).

cnf(c_246,plain,
    ( r2_hidden(sK1(sK5,sK6),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_245])).

cnf(c_1301,plain,
    ( ~ r1_tarski(sK5,X0)
    | r2_hidden(sK1(sK5,sK6),X0)
    | ~ r2_hidden(sK1(sK5,sK6),sK5) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1329,plain,
    ( ~ r1_tarski(sK5,k2_relat_1(sK7))
    | r2_hidden(sK1(sK5,sK6),k2_relat_1(sK7))
    | ~ r2_hidden(sK1(sK5,sK6),sK5) ),
    inference(instantiation,[status(thm)],[c_1301])).

cnf(c_1330,plain,
    ( r1_tarski(sK5,k2_relat_1(sK7)) != iProver_top
    | r2_hidden(sK1(sK5,sK6),k2_relat_1(sK7)) = iProver_top
    | r2_hidden(sK1(sK5,sK6),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1329])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK4(X1,X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_420,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK4(X1,X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_18])).

cnf(c_421,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK7))
    | r2_hidden(sK4(sK7,X0),k1_relat_1(sK7))
    | ~ v1_relat_1(sK7) ),
    inference(unflattening,[status(thm)],[c_420])).

cnf(c_425,plain,
    ( r2_hidden(sK4(sK7,X0),k1_relat_1(sK7))
    | ~ r2_hidden(X0,k2_relat_1(sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_421,c_19])).

cnf(c_426,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK7))
    | r2_hidden(sK4(sK7,X0),k1_relat_1(sK7)) ),
    inference(renaming,[status(thm)],[c_425])).

cnf(c_1404,plain,
    ( r2_hidden(sK4(sK7,sK1(sK5,sK6)),k1_relat_1(sK7))
    | ~ r2_hidden(sK1(sK5,sK6),k2_relat_1(sK7)) ),
    inference(instantiation,[status(thm)],[c_426])).

cnf(c_1405,plain,
    ( r2_hidden(sK4(sK7,sK1(sK5,sK6)),k1_relat_1(sK7)) = iProver_top
    | r2_hidden(sK1(sK5,sK6),k2_relat_1(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1404])).

cnf(c_3888,plain,
    ( r2_hidden(sK4(sK7,sK1(sK5,sK6)),k10_relat_1(sK7,X0)) = iProver_top
    | r2_hidden(sK1(sK5,sK6),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3475,c_23,c_246,c_1330,c_1405])).

cnf(c_17,negated_conjecture,
    ( r1_tarski(k10_relat_1(sK7,sK5),k10_relat_1(sK7,sK6)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1145,plain,
    ( r1_tarski(k10_relat_1(sK7,sK5),k10_relat_1(sK7,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1656,plain,
    ( r2_hidden(X0,k10_relat_1(sK7,sK6)) = iProver_top
    | r2_hidden(X0,k10_relat_1(sK7,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1145,c_1148])).

cnf(c_3896,plain,
    ( r2_hidden(sK4(sK7,sK1(sK5,sK6)),k10_relat_1(sK7,sK6)) = iProver_top
    | r2_hidden(sK1(sK5,sK6),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3888,c_1656])).

cnf(c_4049,plain,
    ( r2_hidden(sK4(sK7,sK1(sK5,sK6)),k10_relat_1(sK7,sK6)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3896,c_246])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(k1_funct_1(X1,X0),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_516,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(k1_funct_1(X1,X0),X2)
    | ~ v1_relat_1(X1)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_18])).

cnf(c_517,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK7,X1))
    | r2_hidden(k1_funct_1(sK7,X0),X1)
    | ~ v1_relat_1(sK7) ),
    inference(unflattening,[status(thm)],[c_516])).

cnf(c_521,plain,
    ( r2_hidden(k1_funct_1(sK7,X0),X1)
    | ~ r2_hidden(X0,k10_relat_1(sK7,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_517,c_19])).

cnf(c_522,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK7,X1))
    | r2_hidden(k1_funct_1(sK7,X0),X1) ),
    inference(renaming,[status(thm)],[c_521])).

cnf(c_1134,plain,
    ( r2_hidden(X0,k10_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(k1_funct_1(sK7,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_522])).

cnf(c_4054,plain,
    ( r2_hidden(k1_funct_1(sK7,sK4(sK7,sK1(sK5,sK6))),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_4049,c_1134])).

cnf(c_4057,plain,
    ( r2_hidden(sK1(sK5,sK6),sK6) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4054,c_3462])).

cnf(c_6,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_251,plain,
    ( ~ r2_hidden(sK1(X0,X1),X1)
    | sK6 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_15])).

cnf(c_252,plain,
    ( ~ r2_hidden(sK1(sK5,sK6),sK6) ),
    inference(unflattening,[status(thm)],[c_251])).

cnf(c_253,plain,
    ( r2_hidden(sK1(sK5,sK6),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_252])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4057,c_253])).


%------------------------------------------------------------------------------
