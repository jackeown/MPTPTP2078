%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:52:53 EST 2020

% Result     : Theorem 7.65s
% Output     : CNFRefutation 7.65s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 530 expanded)
%              Number of clauses        :   50 ( 128 expanded)
%              Number of leaves         :   12 ( 138 expanded)
%              Depth                    :   20
%              Number of atoms          :  431 (3723 expanded)
%              Number of equality atoms :  104 ( 212 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ! [X2] :
              ( r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))
            <=> ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                & r1_tarski(X2,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ! [X2] :
                ( r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))
              <=> ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                  & r1_tarski(X2,k1_relat_1(X0)) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))
            <~> ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                & r1_tarski(X2,k1_relat_1(X0)) ) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))
            <~> ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                & r1_tarski(X2,k1_relat_1(X0)) ) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                | ~ r1_tarski(X2,k1_relat_1(X0))
                | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) )
              & ( ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                  & r1_tarski(X2,k1_relat_1(X0)) )
                | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) ) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                | ~ r1_tarski(X2,k1_relat_1(X0))
                | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) )
              & ( ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                  & r1_tarski(X2,k1_relat_1(X0)) )
                | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) ) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
            | ~ r1_tarski(X2,k1_relat_1(X0))
            | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) )
          & ( ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
              & r1_tarski(X2,k1_relat_1(X0)) )
            | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) ) )
     => ( ( ~ r1_tarski(k9_relat_1(X0,sK4),k1_relat_1(X1))
          | ~ r1_tarski(sK4,k1_relat_1(X0))
          | ~ r1_tarski(sK4,k1_relat_1(k5_relat_1(X0,X1))) )
        & ( ( r1_tarski(k9_relat_1(X0,sK4),k1_relat_1(X1))
            & r1_tarski(sK4,k1_relat_1(X0)) )
          | r1_tarski(sK4,k1_relat_1(k5_relat_1(X0,X1))) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                | ~ r1_tarski(X2,k1_relat_1(X0))
                | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) )
              & ( ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                  & r1_tarski(X2,k1_relat_1(X0)) )
                | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) ) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ? [X2] :
            ( ( ~ r1_tarski(k9_relat_1(X0,X2),k1_relat_1(sK3))
              | ~ r1_tarski(X2,k1_relat_1(X0))
              | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(X0,sK3))) )
            & ( ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(sK3))
                & r1_tarski(X2,k1_relat_1(X0)) )
              | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,sK3))) ) )
        & v1_funct_1(sK3)
        & v1_relat_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                  | ~ r1_tarski(X2,k1_relat_1(X0))
                  | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) )
                & ( ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                    & r1_tarski(X2,k1_relat_1(X0)) )
                  | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) ) )
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_tarski(k9_relat_1(sK2,X2),k1_relat_1(X1))
                | ~ r1_tarski(X2,k1_relat_1(sK2))
                | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(sK2,X1))) )
              & ( ( r1_tarski(k9_relat_1(sK2,X2),k1_relat_1(X1))
                  & r1_tarski(X2,k1_relat_1(sK2)) )
                | r1_tarski(X2,k1_relat_1(k5_relat_1(sK2,X1))) ) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ( ~ r1_tarski(k9_relat_1(sK2,sK4),k1_relat_1(sK3))
      | ~ r1_tarski(sK4,k1_relat_1(sK2))
      | ~ r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3))) )
    & ( ( r1_tarski(k9_relat_1(sK2,sK4),k1_relat_1(sK3))
        & r1_tarski(sK4,k1_relat_1(sK2)) )
      | r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3))) )
    & v1_funct_1(sK3)
    & v1_relat_1(sK3)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f36,f39,f38,f37])).

fof(f62,plain,
    ( r1_tarski(k9_relat_1(sK2,sK4),k1_relat_1(sK3))
    | r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f40])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
          & r1_tarski(X0,k1_relat_1(X2)) )
       => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f57,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f59,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f58,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f61,plain,
    ( r1_tarski(sK4,k1_relat_1(sK2))
    | r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f40])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
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

fof(f14,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
            | ~ r2_hidden(X3,k1_relat_1(X0))
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
              & r2_hidden(X3,k1_relat_1(X0)) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(k1_funct_1(X0,sK1(X0,X1,X2)),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),k1_relat_1(X0))
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ( r2_hidden(k1_funct_1(X0,sK1(X0,X1,X2)),X1)
            & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X0)) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ( ( ~ r2_hidden(k1_funct_1(X0,sK1(X0,X1,X2)),X1)
                | ~ r2_hidden(sK1(X0,X1,X2),k1_relat_1(X0))
                | ~ r2_hidden(sK1(X0,X1,X2),X2) )
              & ( ( r2_hidden(k1_funct_1(X0,sK1(X0,X1,X2)),X1)
                  & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X0)) )
                | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f31])).

fof(f46,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X4,X2)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f66,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X4,k10_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f63,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,sK4),k1_relat_1(sK3))
    | ~ r1_tarski(sK4,k1_relat_1(sK2))
    | ~ r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_17,negated_conjecture,
    ( r1_tarski(k9_relat_1(sK2,sK4),k1_relat_1(sK3))
    | r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_643,plain,
    ( r1_tarski(k9_relat_1(sK2,sK4),k1_relat_1(sK3)) = iProver_top
    | r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_12,plain,
    ( r1_tarski(X0,k10_relat_1(X1,X2))
    | ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ r1_tarski(k9_relat_1(X1,X0),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_648,plain,
    ( r1_tarski(X0,k10_relat_1(X1,X2)) = iProver_top
    | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
    | r1_tarski(k9_relat_1(X1,X0),X2) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1656,plain,
    ( r1_tarski(sK4,k10_relat_1(sK2,k1_relat_1(sK3))) = iProver_top
    | r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3))) = iProver_top
    | r1_tarski(sK4,k1_relat_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_643,c_648])).

cnf(c_22,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_638,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_20,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_640,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X1,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_656,plain,
    ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1148,plain,
    ( k10_relat_1(X0,k1_relat_1(sK3)) = k1_relat_1(k5_relat_1(X0,sK3))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_640,c_656])).

cnf(c_1197,plain,
    ( k10_relat_1(sK2,k1_relat_1(sK3)) = k1_relat_1(k5_relat_1(sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_638,c_1148])).

cnf(c_1658,plain,
    ( r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3))) = iProver_top
    | r1_tarski(sK4,k1_relat_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1656,c_1197])).

cnf(c_23,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_21,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_24,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_18,negated_conjecture,
    ( r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3)))
    | r1_tarski(sK4,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_27,plain,
    ( r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3))) = iProver_top
    | r1_tarski(sK4,k1_relat_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2248,plain,
    ( r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1658,c_23,c_24,c_27])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_657,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_11,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_649,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1257,plain,
    ( r1_tarski(k9_relat_1(sK2,k1_relat_1(k5_relat_1(sK2,sK3))),k1_relat_1(sK3)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1197,c_649])).

cnf(c_1748,plain,
    ( r1_tarski(k9_relat_1(sK2,k1_relat_1(k5_relat_1(sK2,sK3))),k1_relat_1(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1257,c_23,c_24])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_659,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_658,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1086,plain,
    ( r2_hidden(sK0(X0,X1),X2) = iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_659,c_658])).

cnf(c_2982,plain,
    ( r2_hidden(sK0(X0,X1),X2) = iProver_top
    | r1_tarski(X0,X3) != iProver_top
    | r1_tarski(X3,X2) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1086,c_658])).

cnf(c_8242,plain,
    ( r2_hidden(sK0(X0,X1),k1_relat_1(sK3)) = iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k9_relat_1(sK2,k1_relat_1(k5_relat_1(sK2,sK3)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1748,c_2982])).

cnf(c_8551,plain,
    ( r2_hidden(sK0(k9_relat_1(sK2,X0),X1),k1_relat_1(sK3)) = iProver_top
    | r1_tarski(X0,k1_relat_1(k5_relat_1(sK2,sK3))) != iProver_top
    | r1_tarski(k9_relat_1(sK2,X0),X1) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_657,c_8242])).

cnf(c_18535,plain,
    ( r1_tarski(k9_relat_1(sK2,X0),X1) = iProver_top
    | r1_tarski(X0,k1_relat_1(k5_relat_1(sK2,sK3))) != iProver_top
    | r2_hidden(sK0(k9_relat_1(sK2,X0),X1),k1_relat_1(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8551,c_23])).

cnf(c_18536,plain,
    ( r2_hidden(sK0(k9_relat_1(sK2,X0),X1),k1_relat_1(sK3)) = iProver_top
    | r1_tarski(X0,k1_relat_1(k5_relat_1(sK2,sK3))) != iProver_top
    | r1_tarski(k9_relat_1(sK2,X0),X1) = iProver_top ),
    inference(renaming,[status(thm)],[c_18535])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_660,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_18541,plain,
    ( r1_tarski(X0,k1_relat_1(k5_relat_1(sK2,sK3))) != iProver_top
    | r1_tarski(k9_relat_1(sK2,X0),k1_relat_1(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_18536,c_660])).

cnf(c_18551,plain,
    ( r1_tarski(k9_relat_1(sK2,sK4),k1_relat_1(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2248,c_18541])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_650,plain,
    ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
    | r2_hidden(X0,k1_relat_1(X1)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1569,plain,
    ( r2_hidden(X0,k1_relat_1(k5_relat_1(sK2,sK3))) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1197,c_650])).

cnf(c_1857,plain,
    ( r2_hidden(X0,k1_relat_1(k5_relat_1(sK2,sK3))) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1569,c_23,c_24])).

cnf(c_2990,plain,
    ( r2_hidden(sK0(X0,X1),k1_relat_1(sK2)) = iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k1_relat_1(k5_relat_1(sK2,sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1086,c_1857])).

cnf(c_3548,plain,
    ( r2_hidden(sK0(sK4,X0),k1_relat_1(sK2)) = iProver_top
    | r1_tarski(sK4,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2248,c_2990])).

cnf(c_3623,plain,
    ( r1_tarski(sK4,k1_relat_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3548,c_660])).

cnf(c_16,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(sK2,sK4),k1_relat_1(sK3))
    | ~ r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3)))
    | ~ r1_tarski(sK4,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_29,plain,
    ( r1_tarski(k9_relat_1(sK2,sK4),k1_relat_1(sK3)) != iProver_top
    | r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3))) != iProver_top
    | r1_tarski(sK4,k1_relat_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_18551,c_3623,c_2248,c_29])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:12:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 7.65/1.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.65/1.50  
% 7.65/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.65/1.50  
% 7.65/1.50  ------  iProver source info
% 7.65/1.50  
% 7.65/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.65/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.65/1.50  git: non_committed_changes: false
% 7.65/1.50  git: last_make_outside_of_git: false
% 7.65/1.50  
% 7.65/1.50  ------ 
% 7.65/1.50  
% 7.65/1.50  ------ Input Options
% 7.65/1.50  
% 7.65/1.50  --out_options                           all
% 7.65/1.50  --tptp_safe_out                         true
% 7.65/1.50  --problem_path                          ""
% 7.65/1.50  --include_path                          ""
% 7.65/1.50  --clausifier                            res/vclausify_rel
% 7.65/1.50  --clausifier_options                    ""
% 7.65/1.50  --stdin                                 false
% 7.65/1.50  --stats_out                             all
% 7.65/1.50  
% 7.65/1.50  ------ General Options
% 7.65/1.50  
% 7.65/1.50  --fof                                   false
% 7.65/1.50  --time_out_real                         305.
% 7.65/1.50  --time_out_virtual                      -1.
% 7.65/1.50  --symbol_type_check                     false
% 7.65/1.50  --clausify_out                          false
% 7.65/1.50  --sig_cnt_out                           false
% 7.65/1.50  --trig_cnt_out                          false
% 7.65/1.50  --trig_cnt_out_tolerance                1.
% 7.65/1.50  --trig_cnt_out_sk_spl                   false
% 7.65/1.50  --abstr_cl_out                          false
% 7.65/1.50  
% 7.65/1.50  ------ Global Options
% 7.65/1.50  
% 7.65/1.50  --schedule                              default
% 7.65/1.50  --add_important_lit                     false
% 7.65/1.50  --prop_solver_per_cl                    1000
% 7.65/1.50  --min_unsat_core                        false
% 7.65/1.50  --soft_assumptions                      false
% 7.65/1.50  --soft_lemma_size                       3
% 7.65/1.50  --prop_impl_unit_size                   0
% 7.65/1.50  --prop_impl_unit                        []
% 7.65/1.50  --share_sel_clauses                     true
% 7.65/1.50  --reset_solvers                         false
% 7.65/1.50  --bc_imp_inh                            [conj_cone]
% 7.65/1.50  --conj_cone_tolerance                   3.
% 7.65/1.50  --extra_neg_conj                        none
% 7.65/1.50  --large_theory_mode                     true
% 7.65/1.50  --prolific_symb_bound                   200
% 7.65/1.50  --lt_threshold                          2000
% 7.65/1.50  --clause_weak_htbl                      true
% 7.65/1.50  --gc_record_bc_elim                     false
% 7.65/1.50  
% 7.65/1.50  ------ Preprocessing Options
% 7.65/1.50  
% 7.65/1.50  --preprocessing_flag                    true
% 7.65/1.50  --time_out_prep_mult                    0.1
% 7.65/1.50  --splitting_mode                        input
% 7.65/1.50  --splitting_grd                         true
% 7.65/1.50  --splitting_cvd                         false
% 7.65/1.50  --splitting_cvd_svl                     false
% 7.65/1.50  --splitting_nvd                         32
% 7.65/1.50  --sub_typing                            true
% 7.65/1.50  --prep_gs_sim                           true
% 7.65/1.50  --prep_unflatten                        true
% 7.65/1.50  --prep_res_sim                          true
% 7.65/1.50  --prep_upred                            true
% 7.65/1.50  --prep_sem_filter                       exhaustive
% 7.65/1.50  --prep_sem_filter_out                   false
% 7.65/1.50  --pred_elim                             true
% 7.65/1.50  --res_sim_input                         true
% 7.65/1.50  --eq_ax_congr_red                       true
% 7.65/1.50  --pure_diseq_elim                       true
% 7.65/1.50  --brand_transform                       false
% 7.65/1.50  --non_eq_to_eq                          false
% 7.65/1.50  --prep_def_merge                        true
% 7.65/1.50  --prep_def_merge_prop_impl              false
% 7.65/1.50  --prep_def_merge_mbd                    true
% 7.65/1.50  --prep_def_merge_tr_red                 false
% 7.65/1.50  --prep_def_merge_tr_cl                  false
% 7.65/1.50  --smt_preprocessing                     true
% 7.65/1.50  --smt_ac_axioms                         fast
% 7.65/1.50  --preprocessed_out                      false
% 7.65/1.50  --preprocessed_stats                    false
% 7.65/1.50  
% 7.65/1.50  ------ Abstraction refinement Options
% 7.65/1.50  
% 7.65/1.50  --abstr_ref                             []
% 7.65/1.50  --abstr_ref_prep                        false
% 7.65/1.50  --abstr_ref_until_sat                   false
% 7.65/1.50  --abstr_ref_sig_restrict                funpre
% 7.65/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.65/1.50  --abstr_ref_under                       []
% 7.65/1.50  
% 7.65/1.50  ------ SAT Options
% 7.65/1.50  
% 7.65/1.50  --sat_mode                              false
% 7.65/1.50  --sat_fm_restart_options                ""
% 7.65/1.50  --sat_gr_def                            false
% 7.65/1.50  --sat_epr_types                         true
% 7.65/1.50  --sat_non_cyclic_types                  false
% 7.65/1.50  --sat_finite_models                     false
% 7.65/1.50  --sat_fm_lemmas                         false
% 7.65/1.50  --sat_fm_prep                           false
% 7.65/1.50  --sat_fm_uc_incr                        true
% 7.65/1.50  --sat_out_model                         small
% 7.65/1.50  --sat_out_clauses                       false
% 7.65/1.50  
% 7.65/1.50  ------ QBF Options
% 7.65/1.50  
% 7.65/1.50  --qbf_mode                              false
% 7.65/1.50  --qbf_elim_univ                         false
% 7.65/1.50  --qbf_dom_inst                          none
% 7.65/1.50  --qbf_dom_pre_inst                      false
% 7.65/1.50  --qbf_sk_in                             false
% 7.65/1.50  --qbf_pred_elim                         true
% 7.65/1.50  --qbf_split                             512
% 7.65/1.50  
% 7.65/1.50  ------ BMC1 Options
% 7.65/1.50  
% 7.65/1.50  --bmc1_incremental                      false
% 7.65/1.50  --bmc1_axioms                           reachable_all
% 7.65/1.50  --bmc1_min_bound                        0
% 7.65/1.50  --bmc1_max_bound                        -1
% 7.65/1.50  --bmc1_max_bound_default                -1
% 7.65/1.50  --bmc1_symbol_reachability              true
% 7.65/1.50  --bmc1_property_lemmas                  false
% 7.65/1.50  --bmc1_k_induction                      false
% 7.65/1.50  --bmc1_non_equiv_states                 false
% 7.65/1.50  --bmc1_deadlock                         false
% 7.65/1.50  --bmc1_ucm                              false
% 7.65/1.50  --bmc1_add_unsat_core                   none
% 7.65/1.50  --bmc1_unsat_core_children              false
% 7.65/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.65/1.50  --bmc1_out_stat                         full
% 7.65/1.50  --bmc1_ground_init                      false
% 7.65/1.50  --bmc1_pre_inst_next_state              false
% 7.65/1.50  --bmc1_pre_inst_state                   false
% 7.65/1.50  --bmc1_pre_inst_reach_state             false
% 7.65/1.50  --bmc1_out_unsat_core                   false
% 7.65/1.50  --bmc1_aig_witness_out                  false
% 7.65/1.50  --bmc1_verbose                          false
% 7.65/1.50  --bmc1_dump_clauses_tptp                false
% 7.65/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.65/1.50  --bmc1_dump_file                        -
% 7.65/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.65/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.65/1.50  --bmc1_ucm_extend_mode                  1
% 7.65/1.50  --bmc1_ucm_init_mode                    2
% 7.65/1.50  --bmc1_ucm_cone_mode                    none
% 7.65/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.65/1.50  --bmc1_ucm_relax_model                  4
% 7.65/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.65/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.65/1.50  --bmc1_ucm_layered_model                none
% 7.65/1.50  --bmc1_ucm_max_lemma_size               10
% 7.65/1.50  
% 7.65/1.50  ------ AIG Options
% 7.65/1.50  
% 7.65/1.50  --aig_mode                              false
% 7.65/1.50  
% 7.65/1.50  ------ Instantiation Options
% 7.65/1.50  
% 7.65/1.50  --instantiation_flag                    true
% 7.65/1.50  --inst_sos_flag                         true
% 7.65/1.50  --inst_sos_phase                        true
% 7.65/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.65/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.65/1.50  --inst_lit_sel_side                     num_symb
% 7.65/1.50  --inst_solver_per_active                1400
% 7.65/1.50  --inst_solver_calls_frac                1.
% 7.65/1.50  --inst_passive_queue_type               priority_queues
% 7.65/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.65/1.50  --inst_passive_queues_freq              [25;2]
% 7.65/1.50  --inst_dismatching                      true
% 7.65/1.50  --inst_eager_unprocessed_to_passive     true
% 7.65/1.50  --inst_prop_sim_given                   true
% 7.65/1.50  --inst_prop_sim_new                     false
% 7.65/1.50  --inst_subs_new                         false
% 7.65/1.50  --inst_eq_res_simp                      false
% 7.65/1.50  --inst_subs_given                       false
% 7.65/1.50  --inst_orphan_elimination               true
% 7.65/1.50  --inst_learning_loop_flag               true
% 7.65/1.50  --inst_learning_start                   3000
% 7.65/1.50  --inst_learning_factor                  2
% 7.65/1.50  --inst_start_prop_sim_after_learn       3
% 7.65/1.50  --inst_sel_renew                        solver
% 7.65/1.50  --inst_lit_activity_flag                true
% 7.65/1.50  --inst_restr_to_given                   false
% 7.65/1.50  --inst_activity_threshold               500
% 7.65/1.50  --inst_out_proof                        true
% 7.65/1.50  
% 7.65/1.50  ------ Resolution Options
% 7.65/1.50  
% 7.65/1.50  --resolution_flag                       true
% 7.65/1.50  --res_lit_sel                           adaptive
% 7.65/1.50  --res_lit_sel_side                      none
% 7.65/1.50  --res_ordering                          kbo
% 7.65/1.50  --res_to_prop_solver                    active
% 7.65/1.50  --res_prop_simpl_new                    false
% 7.65/1.50  --res_prop_simpl_given                  true
% 7.65/1.50  --res_passive_queue_type                priority_queues
% 7.65/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.65/1.50  --res_passive_queues_freq               [15;5]
% 7.65/1.50  --res_forward_subs                      full
% 7.65/1.50  --res_backward_subs                     full
% 7.65/1.50  --res_forward_subs_resolution           true
% 7.65/1.50  --res_backward_subs_resolution          true
% 7.65/1.50  --res_orphan_elimination                true
% 7.65/1.50  --res_time_limit                        2.
% 7.65/1.50  --res_out_proof                         true
% 7.65/1.50  
% 7.65/1.50  ------ Superposition Options
% 7.65/1.50  
% 7.65/1.50  --superposition_flag                    true
% 7.65/1.50  --sup_passive_queue_type                priority_queues
% 7.65/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.65/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.65/1.50  --demod_completeness_check              fast
% 7.65/1.50  --demod_use_ground                      true
% 7.65/1.50  --sup_to_prop_solver                    passive
% 7.65/1.50  --sup_prop_simpl_new                    true
% 7.65/1.50  --sup_prop_simpl_given                  true
% 7.65/1.50  --sup_fun_splitting                     true
% 7.65/1.50  --sup_smt_interval                      50000
% 7.65/1.50  
% 7.65/1.50  ------ Superposition Simplification Setup
% 7.65/1.50  
% 7.65/1.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.65/1.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.65/1.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.65/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.65/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.65/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.65/1.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.65/1.50  --sup_immed_triv                        [TrivRules]
% 7.65/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.65/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.65/1.50  --sup_immed_bw_main                     []
% 7.65/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.65/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.65/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.65/1.50  --sup_input_bw                          []
% 7.65/1.50  
% 7.65/1.50  ------ Combination Options
% 7.65/1.50  
% 7.65/1.50  --comb_res_mult                         3
% 7.65/1.50  --comb_sup_mult                         2
% 7.65/1.50  --comb_inst_mult                        10
% 7.65/1.50  
% 7.65/1.50  ------ Debug Options
% 7.65/1.50  
% 7.65/1.50  --dbg_backtrace                         false
% 7.65/1.50  --dbg_dump_prop_clauses                 false
% 7.65/1.50  --dbg_dump_prop_clauses_file            -
% 7.65/1.50  --dbg_out_stat                          false
% 7.65/1.50  ------ Parsing...
% 7.65/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.65/1.50  
% 7.65/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.65/1.50  
% 7.65/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.65/1.50  
% 7.65/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.65/1.50  ------ Proving...
% 7.65/1.50  ------ Problem Properties 
% 7.65/1.50  
% 7.65/1.50  
% 7.65/1.50  clauses                                 23
% 7.65/1.50  conjectures                             7
% 7.65/1.50  EPR                                     5
% 7.65/1.50  Horn                                    18
% 7.65/1.50  unary                                   4
% 7.65/1.50  binary                                  4
% 7.65/1.50  lits                                    80
% 7.65/1.50  lits eq                                 4
% 7.65/1.50  fd_pure                                 0
% 7.65/1.50  fd_pseudo                               0
% 7.65/1.50  fd_cond                                 0
% 7.65/1.50  fd_pseudo_cond                          3
% 7.65/1.50  AC symbols                              0
% 7.65/1.50  
% 7.65/1.50  ------ Schedule dynamic 5 is on 
% 7.65/1.50  
% 7.65/1.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.65/1.50  
% 7.65/1.50  
% 7.65/1.50  ------ 
% 7.65/1.50  Current options:
% 7.65/1.50  ------ 
% 7.65/1.50  
% 7.65/1.50  ------ Input Options
% 7.65/1.50  
% 7.65/1.50  --out_options                           all
% 7.65/1.50  --tptp_safe_out                         true
% 7.65/1.50  --problem_path                          ""
% 7.65/1.50  --include_path                          ""
% 7.65/1.50  --clausifier                            res/vclausify_rel
% 7.65/1.50  --clausifier_options                    ""
% 7.65/1.50  --stdin                                 false
% 7.65/1.50  --stats_out                             all
% 7.65/1.50  
% 7.65/1.50  ------ General Options
% 7.65/1.50  
% 7.65/1.50  --fof                                   false
% 7.65/1.50  --time_out_real                         305.
% 7.65/1.50  --time_out_virtual                      -1.
% 7.65/1.50  --symbol_type_check                     false
% 7.65/1.50  --clausify_out                          false
% 7.65/1.50  --sig_cnt_out                           false
% 7.65/1.50  --trig_cnt_out                          false
% 7.65/1.50  --trig_cnt_out_tolerance                1.
% 7.65/1.50  --trig_cnt_out_sk_spl                   false
% 7.65/1.50  --abstr_cl_out                          false
% 7.65/1.50  
% 7.65/1.50  ------ Global Options
% 7.65/1.50  
% 7.65/1.50  --schedule                              default
% 7.65/1.50  --add_important_lit                     false
% 7.65/1.50  --prop_solver_per_cl                    1000
% 7.65/1.50  --min_unsat_core                        false
% 7.65/1.50  --soft_assumptions                      false
% 7.65/1.50  --soft_lemma_size                       3
% 7.65/1.50  --prop_impl_unit_size                   0
% 7.65/1.50  --prop_impl_unit                        []
% 7.65/1.50  --share_sel_clauses                     true
% 7.65/1.50  --reset_solvers                         false
% 7.65/1.50  --bc_imp_inh                            [conj_cone]
% 7.65/1.50  --conj_cone_tolerance                   3.
% 7.65/1.50  --extra_neg_conj                        none
% 7.65/1.50  --large_theory_mode                     true
% 7.65/1.50  --prolific_symb_bound                   200
% 7.65/1.50  --lt_threshold                          2000
% 7.65/1.50  --clause_weak_htbl                      true
% 7.65/1.50  --gc_record_bc_elim                     false
% 7.65/1.50  
% 7.65/1.50  ------ Preprocessing Options
% 7.65/1.50  
% 7.65/1.50  --preprocessing_flag                    true
% 7.65/1.50  --time_out_prep_mult                    0.1
% 7.65/1.50  --splitting_mode                        input
% 7.65/1.50  --splitting_grd                         true
% 7.65/1.50  --splitting_cvd                         false
% 7.65/1.50  --splitting_cvd_svl                     false
% 7.65/1.50  --splitting_nvd                         32
% 7.65/1.50  --sub_typing                            true
% 7.65/1.50  --prep_gs_sim                           true
% 7.65/1.50  --prep_unflatten                        true
% 7.65/1.50  --prep_res_sim                          true
% 7.65/1.50  --prep_upred                            true
% 7.65/1.50  --prep_sem_filter                       exhaustive
% 7.65/1.50  --prep_sem_filter_out                   false
% 7.65/1.50  --pred_elim                             true
% 7.65/1.50  --res_sim_input                         true
% 7.65/1.50  --eq_ax_congr_red                       true
% 7.65/1.50  --pure_diseq_elim                       true
% 7.65/1.50  --brand_transform                       false
% 7.65/1.50  --non_eq_to_eq                          false
% 7.65/1.50  --prep_def_merge                        true
% 7.65/1.50  --prep_def_merge_prop_impl              false
% 7.65/1.50  --prep_def_merge_mbd                    true
% 7.65/1.50  --prep_def_merge_tr_red                 false
% 7.65/1.50  --prep_def_merge_tr_cl                  false
% 7.65/1.50  --smt_preprocessing                     true
% 7.65/1.50  --smt_ac_axioms                         fast
% 7.65/1.50  --preprocessed_out                      false
% 7.65/1.50  --preprocessed_stats                    false
% 7.65/1.50  
% 7.65/1.50  ------ Abstraction refinement Options
% 7.65/1.50  
% 7.65/1.50  --abstr_ref                             []
% 7.65/1.50  --abstr_ref_prep                        false
% 7.65/1.50  --abstr_ref_until_sat                   false
% 7.65/1.50  --abstr_ref_sig_restrict                funpre
% 7.65/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.65/1.50  --abstr_ref_under                       []
% 7.65/1.50  
% 7.65/1.50  ------ SAT Options
% 7.65/1.50  
% 7.65/1.50  --sat_mode                              false
% 7.65/1.50  --sat_fm_restart_options                ""
% 7.65/1.50  --sat_gr_def                            false
% 7.65/1.50  --sat_epr_types                         true
% 7.65/1.50  --sat_non_cyclic_types                  false
% 7.65/1.50  --sat_finite_models                     false
% 7.65/1.50  --sat_fm_lemmas                         false
% 7.65/1.50  --sat_fm_prep                           false
% 7.65/1.50  --sat_fm_uc_incr                        true
% 7.65/1.50  --sat_out_model                         small
% 7.65/1.50  --sat_out_clauses                       false
% 7.65/1.50  
% 7.65/1.50  ------ QBF Options
% 7.65/1.50  
% 7.65/1.50  --qbf_mode                              false
% 7.65/1.50  --qbf_elim_univ                         false
% 7.65/1.50  --qbf_dom_inst                          none
% 7.65/1.50  --qbf_dom_pre_inst                      false
% 7.65/1.50  --qbf_sk_in                             false
% 7.65/1.50  --qbf_pred_elim                         true
% 7.65/1.50  --qbf_split                             512
% 7.65/1.50  
% 7.65/1.50  ------ BMC1 Options
% 7.65/1.50  
% 7.65/1.50  --bmc1_incremental                      false
% 7.65/1.50  --bmc1_axioms                           reachable_all
% 7.65/1.50  --bmc1_min_bound                        0
% 7.65/1.50  --bmc1_max_bound                        -1
% 7.65/1.50  --bmc1_max_bound_default                -1
% 7.65/1.50  --bmc1_symbol_reachability              true
% 7.65/1.50  --bmc1_property_lemmas                  false
% 7.65/1.50  --bmc1_k_induction                      false
% 7.65/1.50  --bmc1_non_equiv_states                 false
% 7.65/1.50  --bmc1_deadlock                         false
% 7.65/1.50  --bmc1_ucm                              false
% 7.65/1.50  --bmc1_add_unsat_core                   none
% 7.65/1.50  --bmc1_unsat_core_children              false
% 7.65/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.65/1.50  --bmc1_out_stat                         full
% 7.65/1.50  --bmc1_ground_init                      false
% 7.65/1.50  --bmc1_pre_inst_next_state              false
% 7.65/1.50  --bmc1_pre_inst_state                   false
% 7.65/1.50  --bmc1_pre_inst_reach_state             false
% 7.65/1.50  --bmc1_out_unsat_core                   false
% 7.65/1.50  --bmc1_aig_witness_out                  false
% 7.65/1.50  --bmc1_verbose                          false
% 7.65/1.50  --bmc1_dump_clauses_tptp                false
% 7.65/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.65/1.50  --bmc1_dump_file                        -
% 7.65/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.65/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.65/1.50  --bmc1_ucm_extend_mode                  1
% 7.65/1.50  --bmc1_ucm_init_mode                    2
% 7.65/1.50  --bmc1_ucm_cone_mode                    none
% 7.65/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.65/1.50  --bmc1_ucm_relax_model                  4
% 7.65/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.65/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.65/1.50  --bmc1_ucm_layered_model                none
% 7.65/1.50  --bmc1_ucm_max_lemma_size               10
% 7.65/1.50  
% 7.65/1.50  ------ AIG Options
% 7.65/1.50  
% 7.65/1.50  --aig_mode                              false
% 7.65/1.50  
% 7.65/1.50  ------ Instantiation Options
% 7.65/1.50  
% 7.65/1.50  --instantiation_flag                    true
% 7.65/1.50  --inst_sos_flag                         true
% 7.65/1.50  --inst_sos_phase                        true
% 7.65/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.65/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.65/1.50  --inst_lit_sel_side                     none
% 7.65/1.50  --inst_solver_per_active                1400
% 7.65/1.50  --inst_solver_calls_frac                1.
% 7.65/1.50  --inst_passive_queue_type               priority_queues
% 7.65/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.65/1.50  --inst_passive_queues_freq              [25;2]
% 7.65/1.50  --inst_dismatching                      true
% 7.65/1.50  --inst_eager_unprocessed_to_passive     true
% 7.65/1.50  --inst_prop_sim_given                   true
% 7.65/1.50  --inst_prop_sim_new                     false
% 7.65/1.50  --inst_subs_new                         false
% 7.65/1.50  --inst_eq_res_simp                      false
% 7.65/1.50  --inst_subs_given                       false
% 7.65/1.50  --inst_orphan_elimination               true
% 7.65/1.50  --inst_learning_loop_flag               true
% 7.65/1.50  --inst_learning_start                   3000
% 7.65/1.50  --inst_learning_factor                  2
% 7.65/1.50  --inst_start_prop_sim_after_learn       3
% 7.65/1.50  --inst_sel_renew                        solver
% 7.65/1.50  --inst_lit_activity_flag                true
% 7.65/1.50  --inst_restr_to_given                   false
% 7.65/1.50  --inst_activity_threshold               500
% 7.65/1.50  --inst_out_proof                        true
% 7.65/1.50  
% 7.65/1.50  ------ Resolution Options
% 7.65/1.50  
% 7.65/1.50  --resolution_flag                       false
% 7.65/1.50  --res_lit_sel                           adaptive
% 7.65/1.50  --res_lit_sel_side                      none
% 7.65/1.50  --res_ordering                          kbo
% 7.65/1.50  --res_to_prop_solver                    active
% 7.65/1.50  --res_prop_simpl_new                    false
% 7.65/1.50  --res_prop_simpl_given                  true
% 7.65/1.50  --res_passive_queue_type                priority_queues
% 7.65/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.65/1.50  --res_passive_queues_freq               [15;5]
% 7.65/1.50  --res_forward_subs                      full
% 7.65/1.50  --res_backward_subs                     full
% 7.65/1.50  --res_forward_subs_resolution           true
% 7.65/1.50  --res_backward_subs_resolution          true
% 7.65/1.50  --res_orphan_elimination                true
% 7.65/1.50  --res_time_limit                        2.
% 7.65/1.50  --res_out_proof                         true
% 7.65/1.50  
% 7.65/1.50  ------ Superposition Options
% 7.65/1.50  
% 7.65/1.50  --superposition_flag                    true
% 7.65/1.50  --sup_passive_queue_type                priority_queues
% 7.65/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.65/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.65/1.50  --demod_completeness_check              fast
% 7.65/1.50  --demod_use_ground                      true
% 7.65/1.50  --sup_to_prop_solver                    passive
% 7.65/1.50  --sup_prop_simpl_new                    true
% 7.65/1.50  --sup_prop_simpl_given                  true
% 7.65/1.50  --sup_fun_splitting                     true
% 7.65/1.50  --sup_smt_interval                      50000
% 7.65/1.50  
% 7.65/1.50  ------ Superposition Simplification Setup
% 7.65/1.50  
% 7.65/1.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.65/1.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.65/1.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.65/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.65/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.65/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.65/1.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.65/1.50  --sup_immed_triv                        [TrivRules]
% 7.65/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.65/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.65/1.50  --sup_immed_bw_main                     []
% 7.65/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.65/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.65/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.65/1.50  --sup_input_bw                          []
% 7.65/1.50  
% 7.65/1.50  ------ Combination Options
% 7.65/1.50  
% 7.65/1.50  --comb_res_mult                         3
% 7.65/1.50  --comb_sup_mult                         2
% 7.65/1.50  --comb_inst_mult                        10
% 7.65/1.50  
% 7.65/1.50  ------ Debug Options
% 7.65/1.50  
% 7.65/1.50  --dbg_backtrace                         false
% 7.65/1.50  --dbg_dump_prop_clauses                 false
% 7.65/1.50  --dbg_dump_prop_clauses_file            -
% 7.65/1.50  --dbg_out_stat                          false
% 7.65/1.50  
% 7.65/1.50  
% 7.65/1.50  
% 7.65/1.50  
% 7.65/1.50  ------ Proving...
% 7.65/1.50  
% 7.65/1.50  
% 7.65/1.50  % SZS status Theorem for theBenchmark.p
% 7.65/1.50  
% 7.65/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.65/1.50  
% 7.65/1.50  fof(f8,conjecture,(
% 7.65/1.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <=> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))))))),
% 7.65/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f9,negated_conjecture,(
% 7.65/1.50    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <=> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))))))),
% 7.65/1.50    inference(negated_conjecture,[],[f8])).
% 7.65/1.50  
% 7.65/1.50  fof(f22,plain,(
% 7.65/1.50    ? [X0] : (? [X1] : (? [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <~> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0)))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 7.65/1.50    inference(ennf_transformation,[],[f9])).
% 7.65/1.50  
% 7.65/1.50  fof(f23,plain,(
% 7.65/1.50    ? [X0] : (? [X1] : (? [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <~> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0)))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 7.65/1.50    inference(flattening,[],[f22])).
% 7.65/1.50  
% 7.65/1.50  fof(f35,plain,(
% 7.65/1.50    ? [X0] : (? [X1] : (? [X2] : (((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0))) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 7.65/1.50    inference(nnf_transformation,[],[f23])).
% 7.65/1.50  
% 7.65/1.50  fof(f36,plain,(
% 7.65/1.50    ? [X0] : (? [X1] : (? [X2] : ((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 7.65/1.50    inference(flattening,[],[f35])).
% 7.65/1.50  
% 7.65/1.50  fof(f39,plain,(
% 7.65/1.50    ( ! [X0,X1] : (? [X2] : ((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) => ((~r1_tarski(k9_relat_1(X0,sK4),k1_relat_1(X1)) | ~r1_tarski(sK4,k1_relat_1(X0)) | ~r1_tarski(sK4,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,sK4),k1_relat_1(X1)) & r1_tarski(sK4,k1_relat_1(X0))) | r1_tarski(sK4,k1_relat_1(k5_relat_1(X0,X1)))))) )),
% 7.65/1.50    introduced(choice_axiom,[])).
% 7.65/1.50  
% 7.65/1.50  fof(f38,plain,(
% 7.65/1.50    ( ! [X0] : (? [X1] : (? [X2] : ((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) => (? [X2] : ((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(sK3)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,sK3)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(sK3)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,sK3))))) & v1_funct_1(sK3) & v1_relat_1(sK3))) )),
% 7.65/1.50    introduced(choice_axiom,[])).
% 7.65/1.50  
% 7.65/1.50  fof(f37,plain,(
% 7.65/1.50    ? [X0] : (? [X1] : (? [X2] : ((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (? [X2] : ((~r1_tarski(k9_relat_1(sK2,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(sK2)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(sK2,X1)))) & ((r1_tarski(k9_relat_1(sK2,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(sK2))) | r1_tarski(X2,k1_relat_1(k5_relat_1(sK2,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 7.65/1.50    introduced(choice_axiom,[])).
% 7.65/1.50  
% 7.65/1.50  fof(f40,plain,(
% 7.65/1.50    (((~r1_tarski(k9_relat_1(sK2,sK4),k1_relat_1(sK3)) | ~r1_tarski(sK4,k1_relat_1(sK2)) | ~r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3)))) & ((r1_tarski(k9_relat_1(sK2,sK4),k1_relat_1(sK3)) & r1_tarski(sK4,k1_relat_1(sK2))) | r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3))))) & v1_funct_1(sK3) & v1_relat_1(sK3)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 7.65/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f36,f39,f38,f37])).
% 7.65/1.50  
% 7.65/1.50  fof(f62,plain,(
% 7.65/1.50    r1_tarski(k9_relat_1(sK2,sK4),k1_relat_1(sK3)) | r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3)))),
% 7.65/1.50    inference(cnf_transformation,[],[f40])).
% 7.65/1.50  
% 7.65/1.50  fof(f6,axiom,(
% 7.65/1.50    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 7.65/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f18,plain,(
% 7.65/1.50    ! [X0,X1,X2] : ((r1_tarski(X0,k10_relat_1(X2,X1)) | (~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 7.65/1.50    inference(ennf_transformation,[],[f6])).
% 7.65/1.50  
% 7.65/1.50  fof(f19,plain,(
% 7.65/1.50    ! [X0,X1,X2] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 7.65/1.50    inference(flattening,[],[f18])).
% 7.65/1.50  
% 7.65/1.50  fof(f53,plain,(
% 7.65/1.50    ( ! [X2,X0,X1] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 7.65/1.50    inference(cnf_transformation,[],[f19])).
% 7.65/1.50  
% 7.65/1.50  fof(f57,plain,(
% 7.65/1.50    v1_relat_1(sK2)),
% 7.65/1.50    inference(cnf_transformation,[],[f40])).
% 7.65/1.50  
% 7.65/1.50  fof(f59,plain,(
% 7.65/1.50    v1_relat_1(sK3)),
% 7.65/1.50    inference(cnf_transformation,[],[f40])).
% 7.65/1.50  
% 7.65/1.50  fof(f3,axiom,(
% 7.65/1.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 7.65/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f13,plain,(
% 7.65/1.50    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.65/1.50    inference(ennf_transformation,[],[f3])).
% 7.65/1.50  
% 7.65/1.50  fof(f45,plain,(
% 7.65/1.50    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.65/1.50    inference(cnf_transformation,[],[f13])).
% 7.65/1.50  
% 7.65/1.50  fof(f58,plain,(
% 7.65/1.50    v1_funct_1(sK2)),
% 7.65/1.50    inference(cnf_transformation,[],[f40])).
% 7.65/1.50  
% 7.65/1.50  fof(f61,plain,(
% 7.65/1.50    r1_tarski(sK4,k1_relat_1(sK2)) | r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3)))),
% 7.65/1.50    inference(cnf_transformation,[],[f40])).
% 7.65/1.50  
% 7.65/1.50  fof(f2,axiom,(
% 7.65/1.50    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 7.65/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f11,plain,(
% 7.65/1.50    ! [X0,X1,X2] : ((r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 7.65/1.50    inference(ennf_transformation,[],[f2])).
% 7.65/1.50  
% 7.65/1.50  fof(f12,plain,(
% 7.65/1.50    ! [X0,X1,X2] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 7.65/1.50    inference(flattening,[],[f11])).
% 7.65/1.50  
% 7.65/1.50  fof(f44,plain,(
% 7.65/1.50    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 7.65/1.50    inference(cnf_transformation,[],[f12])).
% 7.65/1.50  
% 7.65/1.50  fof(f5,axiom,(
% 7.65/1.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 7.65/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f16,plain,(
% 7.65/1.50    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 7.65/1.50    inference(ennf_transformation,[],[f5])).
% 7.65/1.50  
% 7.65/1.50  fof(f17,plain,(
% 7.65/1.50    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 7.65/1.50    inference(flattening,[],[f16])).
% 7.65/1.50  
% 7.65/1.50  fof(f52,plain,(
% 7.65/1.50    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.65/1.50    inference(cnf_transformation,[],[f17])).
% 7.65/1.50  
% 7.65/1.50  fof(f1,axiom,(
% 7.65/1.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.65/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f10,plain,(
% 7.65/1.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 7.65/1.50    inference(ennf_transformation,[],[f1])).
% 7.65/1.50  
% 7.65/1.50  fof(f24,plain,(
% 7.65/1.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 7.65/1.50    inference(nnf_transformation,[],[f10])).
% 7.65/1.50  
% 7.65/1.50  fof(f25,plain,(
% 7.65/1.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.65/1.50    inference(rectify,[],[f24])).
% 7.65/1.50  
% 7.65/1.50  fof(f26,plain,(
% 7.65/1.50    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.65/1.50    introduced(choice_axiom,[])).
% 7.65/1.50  
% 7.65/1.50  fof(f27,plain,(
% 7.65/1.50    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.65/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).
% 7.65/1.50  
% 7.65/1.50  fof(f42,plain,(
% 7.65/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 7.65/1.50    inference(cnf_transformation,[],[f27])).
% 7.65/1.50  
% 7.65/1.50  fof(f41,plain,(
% 7.65/1.50    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 7.65/1.50    inference(cnf_transformation,[],[f27])).
% 7.65/1.50  
% 7.65/1.50  fof(f43,plain,(
% 7.65/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 7.65/1.50    inference(cnf_transformation,[],[f27])).
% 7.65/1.50  
% 7.65/1.50  fof(f4,axiom,(
% 7.65/1.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))))),
% 7.65/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f14,plain,(
% 7.65/1.50    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.65/1.50    inference(ennf_transformation,[],[f4])).
% 7.65/1.50  
% 7.65/1.50  fof(f15,plain,(
% 7.65/1.50    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.65/1.50    inference(flattening,[],[f14])).
% 7.65/1.50  
% 7.65/1.50  fof(f28,plain,(
% 7.65/1.50    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : (((~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0)))) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X3,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.65/1.50    inference(nnf_transformation,[],[f15])).
% 7.65/1.50  
% 7.65/1.50  fof(f29,plain,(
% 7.65/1.50    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0))) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X3,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.65/1.50    inference(flattening,[],[f28])).
% 7.65/1.50  
% 7.65/1.50  fof(f30,plain,(
% 7.65/1.50    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k1_funct_1(X0,X4),X1) | ~r2_hidden(X4,k1_relat_1(X0))) & ((r2_hidden(k1_funct_1(X0,X4),X1) & r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X4,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.65/1.50    inference(rectify,[],[f29])).
% 7.65/1.50  
% 7.65/1.50  fof(f31,plain,(
% 7.65/1.50    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X3,X2))) => ((~r2_hidden(k1_funct_1(X0,sK1(X0,X1,X2)),X1) | ~r2_hidden(sK1(X0,X1,X2),k1_relat_1(X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(k1_funct_1(X0,sK1(X0,X1,X2)),X1) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X0))) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 7.65/1.50    introduced(choice_axiom,[])).
% 7.65/1.50  
% 7.65/1.50  fof(f32,plain,(
% 7.65/1.50    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ((~r2_hidden(k1_funct_1(X0,sK1(X0,X1,X2)),X1) | ~r2_hidden(sK1(X0,X1,X2),k1_relat_1(X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(k1_funct_1(X0,sK1(X0,X1,X2)),X1) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X0))) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k1_funct_1(X0,X4),X1) | ~r2_hidden(X4,k1_relat_1(X0))) & ((r2_hidden(k1_funct_1(X0,X4),X1) & r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X4,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.65/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f31])).
% 7.65/1.50  
% 7.65/1.50  fof(f46,plain,(
% 7.65/1.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X4,X2) | k10_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.65/1.50    inference(cnf_transformation,[],[f32])).
% 7.65/1.50  
% 7.65/1.50  fof(f66,plain,(
% 7.65/1.50    ( ! [X4,X0,X1] : (r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X4,k10_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.65/1.50    inference(equality_resolution,[],[f46])).
% 7.65/1.50  
% 7.65/1.50  fof(f63,plain,(
% 7.65/1.50    ~r1_tarski(k9_relat_1(sK2,sK4),k1_relat_1(sK3)) | ~r1_tarski(sK4,k1_relat_1(sK2)) | ~r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3)))),
% 7.65/1.50    inference(cnf_transformation,[],[f40])).
% 7.65/1.50  
% 7.65/1.50  cnf(c_17,negated_conjecture,
% 7.65/1.50      ( r1_tarski(k9_relat_1(sK2,sK4),k1_relat_1(sK3))
% 7.65/1.50      | r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3))) ),
% 7.65/1.50      inference(cnf_transformation,[],[f62]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_643,plain,
% 7.65/1.50      ( r1_tarski(k9_relat_1(sK2,sK4),k1_relat_1(sK3)) = iProver_top
% 7.65/1.50      | r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3))) = iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_12,plain,
% 7.65/1.50      ( r1_tarski(X0,k10_relat_1(X1,X2))
% 7.65/1.50      | ~ r1_tarski(X0,k1_relat_1(X1))
% 7.65/1.50      | ~ r1_tarski(k9_relat_1(X1,X0),X2)
% 7.65/1.50      | ~ v1_funct_1(X1)
% 7.65/1.50      | ~ v1_relat_1(X1) ),
% 7.65/1.50      inference(cnf_transformation,[],[f53]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_648,plain,
% 7.65/1.50      ( r1_tarski(X0,k10_relat_1(X1,X2)) = iProver_top
% 7.65/1.50      | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
% 7.65/1.50      | r1_tarski(k9_relat_1(X1,X0),X2) != iProver_top
% 7.65/1.50      | v1_funct_1(X1) != iProver_top
% 7.65/1.50      | v1_relat_1(X1) != iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1656,plain,
% 7.65/1.50      ( r1_tarski(sK4,k10_relat_1(sK2,k1_relat_1(sK3))) = iProver_top
% 7.65/1.50      | r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3))) = iProver_top
% 7.65/1.50      | r1_tarski(sK4,k1_relat_1(sK2)) != iProver_top
% 7.65/1.50      | v1_funct_1(sK2) != iProver_top
% 7.65/1.50      | v1_relat_1(sK2) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_643,c_648]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_22,negated_conjecture,
% 7.65/1.50      ( v1_relat_1(sK2) ),
% 7.65/1.50      inference(cnf_transformation,[],[f57]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_638,plain,
% 7.65/1.50      ( v1_relat_1(sK2) = iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_20,negated_conjecture,
% 7.65/1.50      ( v1_relat_1(sK3) ),
% 7.65/1.50      inference(cnf_transformation,[],[f59]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_640,plain,
% 7.65/1.50      ( v1_relat_1(sK3) = iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_4,plain,
% 7.65/1.50      ( ~ v1_relat_1(X0)
% 7.65/1.50      | ~ v1_relat_1(X1)
% 7.65/1.50      | k10_relat_1(X1,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(X1,X0)) ),
% 7.65/1.50      inference(cnf_transformation,[],[f45]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_656,plain,
% 7.65/1.50      ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
% 7.65/1.50      | v1_relat_1(X0) != iProver_top
% 7.65/1.50      | v1_relat_1(X1) != iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1148,plain,
% 7.65/1.50      ( k10_relat_1(X0,k1_relat_1(sK3)) = k1_relat_1(k5_relat_1(X0,sK3))
% 7.65/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_640,c_656]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1197,plain,
% 7.65/1.50      ( k10_relat_1(sK2,k1_relat_1(sK3)) = k1_relat_1(k5_relat_1(sK2,sK3)) ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_638,c_1148]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1658,plain,
% 7.65/1.50      ( r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3))) = iProver_top
% 7.65/1.50      | r1_tarski(sK4,k1_relat_1(sK2)) != iProver_top
% 7.65/1.50      | v1_funct_1(sK2) != iProver_top
% 7.65/1.50      | v1_relat_1(sK2) != iProver_top ),
% 7.65/1.50      inference(light_normalisation,[status(thm)],[c_1656,c_1197]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_23,plain,
% 7.65/1.50      ( v1_relat_1(sK2) = iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_21,negated_conjecture,
% 7.65/1.50      ( v1_funct_1(sK2) ),
% 7.65/1.50      inference(cnf_transformation,[],[f58]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_24,plain,
% 7.65/1.50      ( v1_funct_1(sK2) = iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_18,negated_conjecture,
% 7.65/1.50      ( r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3)))
% 7.65/1.50      | r1_tarski(sK4,k1_relat_1(sK2)) ),
% 7.65/1.50      inference(cnf_transformation,[],[f61]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_27,plain,
% 7.65/1.50      ( r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3))) = iProver_top
% 7.65/1.50      | r1_tarski(sK4,k1_relat_1(sK2)) = iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_2248,plain,
% 7.65/1.50      ( r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3))) = iProver_top ),
% 7.65/1.50      inference(global_propositional_subsumption,
% 7.65/1.50                [status(thm)],
% 7.65/1.50                [c_1658,c_23,c_24,c_27]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_3,plain,
% 7.65/1.50      ( ~ r1_tarski(X0,X1)
% 7.65/1.50      | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
% 7.65/1.50      | ~ v1_relat_1(X2) ),
% 7.65/1.50      inference(cnf_transformation,[],[f44]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_657,plain,
% 7.65/1.50      ( r1_tarski(X0,X1) != iProver_top
% 7.65/1.50      | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = iProver_top
% 7.65/1.50      | v1_relat_1(X2) != iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_11,plain,
% 7.65/1.50      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
% 7.65/1.50      | ~ v1_funct_1(X0)
% 7.65/1.50      | ~ v1_relat_1(X0) ),
% 7.65/1.50      inference(cnf_transformation,[],[f52]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_649,plain,
% 7.65/1.50      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1) = iProver_top
% 7.65/1.50      | v1_funct_1(X0) != iProver_top
% 7.65/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1257,plain,
% 7.65/1.50      ( r1_tarski(k9_relat_1(sK2,k1_relat_1(k5_relat_1(sK2,sK3))),k1_relat_1(sK3)) = iProver_top
% 7.65/1.50      | v1_funct_1(sK2) != iProver_top
% 7.65/1.50      | v1_relat_1(sK2) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_1197,c_649]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1748,plain,
% 7.65/1.50      ( r1_tarski(k9_relat_1(sK2,k1_relat_1(k5_relat_1(sK2,sK3))),k1_relat_1(sK3)) = iProver_top ),
% 7.65/1.50      inference(global_propositional_subsumption,
% 7.65/1.50                [status(thm)],
% 7.65/1.50                [c_1257,c_23,c_24]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1,plain,
% 7.65/1.50      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 7.65/1.50      inference(cnf_transformation,[],[f42]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_659,plain,
% 7.65/1.50      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 7.65/1.50      | r1_tarski(X0,X1) = iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_2,plain,
% 7.65/1.50      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 7.65/1.50      inference(cnf_transformation,[],[f41]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_658,plain,
% 7.65/1.50      ( r2_hidden(X0,X1) != iProver_top
% 7.65/1.50      | r2_hidden(X0,X2) = iProver_top
% 7.65/1.50      | r1_tarski(X1,X2) != iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1086,plain,
% 7.65/1.50      ( r2_hidden(sK0(X0,X1),X2) = iProver_top
% 7.65/1.50      | r1_tarski(X0,X2) != iProver_top
% 7.65/1.50      | r1_tarski(X0,X1) = iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_659,c_658]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_2982,plain,
% 7.65/1.50      ( r2_hidden(sK0(X0,X1),X2) = iProver_top
% 7.65/1.50      | r1_tarski(X0,X3) != iProver_top
% 7.65/1.50      | r1_tarski(X3,X2) != iProver_top
% 7.65/1.50      | r1_tarski(X0,X1) = iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_1086,c_658]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_8242,plain,
% 7.65/1.50      ( r2_hidden(sK0(X0,X1),k1_relat_1(sK3)) = iProver_top
% 7.65/1.50      | r1_tarski(X0,X1) = iProver_top
% 7.65/1.50      | r1_tarski(X0,k9_relat_1(sK2,k1_relat_1(k5_relat_1(sK2,sK3)))) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_1748,c_2982]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_8551,plain,
% 7.65/1.50      ( r2_hidden(sK0(k9_relat_1(sK2,X0),X1),k1_relat_1(sK3)) = iProver_top
% 7.65/1.50      | r1_tarski(X0,k1_relat_1(k5_relat_1(sK2,sK3))) != iProver_top
% 7.65/1.50      | r1_tarski(k9_relat_1(sK2,X0),X1) = iProver_top
% 7.65/1.50      | v1_relat_1(sK2) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_657,c_8242]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_18535,plain,
% 7.65/1.50      ( r1_tarski(k9_relat_1(sK2,X0),X1) = iProver_top
% 7.65/1.50      | r1_tarski(X0,k1_relat_1(k5_relat_1(sK2,sK3))) != iProver_top
% 7.65/1.50      | r2_hidden(sK0(k9_relat_1(sK2,X0),X1),k1_relat_1(sK3)) = iProver_top ),
% 7.65/1.50      inference(global_propositional_subsumption,
% 7.65/1.50                [status(thm)],
% 7.65/1.50                [c_8551,c_23]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_18536,plain,
% 7.65/1.50      ( r2_hidden(sK0(k9_relat_1(sK2,X0),X1),k1_relat_1(sK3)) = iProver_top
% 7.65/1.50      | r1_tarski(X0,k1_relat_1(k5_relat_1(sK2,sK3))) != iProver_top
% 7.65/1.50      | r1_tarski(k9_relat_1(sK2,X0),X1) = iProver_top ),
% 7.65/1.50      inference(renaming,[status(thm)],[c_18535]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_0,plain,
% 7.65/1.50      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 7.65/1.50      inference(cnf_transformation,[],[f43]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_660,plain,
% 7.65/1.50      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 7.65/1.50      | r1_tarski(X0,X1) = iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_18541,plain,
% 7.65/1.50      ( r1_tarski(X0,k1_relat_1(k5_relat_1(sK2,sK3))) != iProver_top
% 7.65/1.50      | r1_tarski(k9_relat_1(sK2,X0),k1_relat_1(sK3)) = iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_18536,c_660]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_18551,plain,
% 7.65/1.50      ( r1_tarski(k9_relat_1(sK2,sK4),k1_relat_1(sK3)) = iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_2248,c_18541]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_10,plain,
% 7.65/1.50      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 7.65/1.50      | r2_hidden(X0,k1_relat_1(X1))
% 7.65/1.50      | ~ v1_funct_1(X1)
% 7.65/1.50      | ~ v1_relat_1(X1) ),
% 7.65/1.50      inference(cnf_transformation,[],[f66]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_650,plain,
% 7.65/1.50      ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
% 7.65/1.50      | r2_hidden(X0,k1_relat_1(X1)) = iProver_top
% 7.65/1.50      | v1_funct_1(X1) != iProver_top
% 7.65/1.50      | v1_relat_1(X1) != iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1569,plain,
% 7.65/1.50      ( r2_hidden(X0,k1_relat_1(k5_relat_1(sK2,sK3))) != iProver_top
% 7.65/1.50      | r2_hidden(X0,k1_relat_1(sK2)) = iProver_top
% 7.65/1.50      | v1_funct_1(sK2) != iProver_top
% 7.65/1.50      | v1_relat_1(sK2) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_1197,c_650]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1857,plain,
% 7.65/1.50      ( r2_hidden(X0,k1_relat_1(k5_relat_1(sK2,sK3))) != iProver_top
% 7.65/1.50      | r2_hidden(X0,k1_relat_1(sK2)) = iProver_top ),
% 7.65/1.50      inference(global_propositional_subsumption,
% 7.65/1.50                [status(thm)],
% 7.65/1.50                [c_1569,c_23,c_24]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_2990,plain,
% 7.65/1.50      ( r2_hidden(sK0(X0,X1),k1_relat_1(sK2)) = iProver_top
% 7.65/1.50      | r1_tarski(X0,X1) = iProver_top
% 7.65/1.50      | r1_tarski(X0,k1_relat_1(k5_relat_1(sK2,sK3))) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_1086,c_1857]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_3548,plain,
% 7.65/1.50      ( r2_hidden(sK0(sK4,X0),k1_relat_1(sK2)) = iProver_top
% 7.65/1.50      | r1_tarski(sK4,X0) = iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_2248,c_2990]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_3623,plain,
% 7.65/1.50      ( r1_tarski(sK4,k1_relat_1(sK2)) = iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_3548,c_660]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_16,negated_conjecture,
% 7.65/1.50      ( ~ r1_tarski(k9_relat_1(sK2,sK4),k1_relat_1(sK3))
% 7.65/1.50      | ~ r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3)))
% 7.65/1.50      | ~ r1_tarski(sK4,k1_relat_1(sK2)) ),
% 7.65/1.50      inference(cnf_transformation,[],[f63]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_29,plain,
% 7.65/1.50      ( r1_tarski(k9_relat_1(sK2,sK4),k1_relat_1(sK3)) != iProver_top
% 7.65/1.50      | r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3))) != iProver_top
% 7.65/1.50      | r1_tarski(sK4,k1_relat_1(sK2)) != iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(contradiction,plain,
% 7.65/1.50      ( $false ),
% 7.65/1.50      inference(minisat,[status(thm)],[c_18551,c_3623,c_2248,c_29]) ).
% 7.65/1.50  
% 7.65/1.50  
% 7.65/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.65/1.50  
% 7.65/1.50  ------                               Statistics
% 7.65/1.50  
% 7.65/1.50  ------ General
% 7.65/1.50  
% 7.65/1.50  abstr_ref_over_cycles:                  0
% 7.65/1.50  abstr_ref_under_cycles:                 0
% 7.65/1.50  gc_basic_clause_elim:                   0
% 7.65/1.50  forced_gc_time:                         0
% 7.65/1.50  parsing_time:                           0.01
% 7.65/1.50  unif_index_cands_time:                  0.
% 7.65/1.50  unif_index_add_time:                    0.
% 7.65/1.50  orderings_time:                         0.
% 7.65/1.50  out_proof_time:                         0.012
% 7.65/1.50  total_time:                             0.727
% 7.65/1.50  num_of_symbols:                         45
% 7.65/1.50  num_of_terms:                           16474
% 7.65/1.50  
% 7.65/1.50  ------ Preprocessing
% 7.65/1.50  
% 7.65/1.50  num_of_splits:                          0
% 7.65/1.50  num_of_split_atoms:                     0
% 7.65/1.50  num_of_reused_defs:                     0
% 7.65/1.50  num_eq_ax_congr_red:                    14
% 7.65/1.50  num_of_sem_filtered_clauses:            1
% 7.65/1.50  num_of_subtypes:                        0
% 7.65/1.50  monotx_restored_types:                  0
% 7.65/1.50  sat_num_of_epr_types:                   0
% 7.65/1.50  sat_num_of_non_cyclic_types:            0
% 7.65/1.50  sat_guarded_non_collapsed_types:        0
% 7.65/1.50  num_pure_diseq_elim:                    0
% 7.65/1.50  simp_replaced_by:                       0
% 7.65/1.50  res_preprocessed:                       92
% 7.65/1.50  prep_upred:                             0
% 7.65/1.50  prep_unflattend:                        0
% 7.65/1.50  smt_new_axioms:                         0
% 7.65/1.50  pred_elim_cands:                        4
% 7.65/1.50  pred_elim:                              0
% 7.65/1.50  pred_elim_cl:                           0
% 7.65/1.50  pred_elim_cycles:                       1
% 7.65/1.50  merged_defs:                            0
% 7.65/1.50  merged_defs_ncl:                        0
% 7.65/1.50  bin_hyper_res:                          0
% 7.65/1.50  prep_cycles:                            3
% 7.65/1.50  pred_elim_time:                         0.
% 7.65/1.50  splitting_time:                         0.
% 7.65/1.50  sem_filter_time:                        0.
% 7.65/1.50  monotx_time:                            0.001
% 7.65/1.50  subtype_inf_time:                       0.
% 7.65/1.50  
% 7.65/1.50  ------ Problem properties
% 7.65/1.50  
% 7.65/1.50  clauses:                                23
% 7.65/1.50  conjectures:                            7
% 7.65/1.50  epr:                                    5
% 7.65/1.50  horn:                                   18
% 7.65/1.50  ground:                                 7
% 7.65/1.50  unary:                                  4
% 7.65/1.50  binary:                                 4
% 7.65/1.50  lits:                                   80
% 7.65/1.50  lits_eq:                                4
% 7.65/1.50  fd_pure:                                0
% 7.65/1.50  fd_pseudo:                              0
% 7.65/1.50  fd_cond:                                0
% 7.65/1.50  fd_pseudo_cond:                         3
% 7.65/1.50  ac_symbols:                             0
% 7.65/1.50  
% 7.65/1.50  ------ Propositional Solver
% 7.65/1.50  
% 7.65/1.50  prop_solver_calls:                      33
% 7.65/1.50  prop_fast_solver_calls:                 1377
% 7.65/1.50  smt_solver_calls:                       0
% 7.65/1.50  smt_fast_solver_calls:                  0
% 7.65/1.50  prop_num_of_clauses:                    7219
% 7.65/1.50  prop_preprocess_simplified:             11826
% 7.65/1.50  prop_fo_subsumed:                       47
% 7.65/1.50  prop_solver_time:                       0.
% 7.65/1.50  smt_solver_time:                        0.
% 7.65/1.50  smt_fast_solver_time:                   0.
% 7.65/1.50  prop_fast_solver_time:                  0.
% 7.65/1.50  prop_unsat_core_time:                   0.
% 7.65/1.50  
% 7.65/1.50  ------ QBF
% 7.65/1.50  
% 7.65/1.50  qbf_q_res:                              0
% 7.65/1.50  qbf_num_tautologies:                    0
% 7.65/1.50  qbf_prep_cycles:                        0
% 7.65/1.50  
% 7.65/1.50  ------ BMC1
% 7.65/1.50  
% 7.65/1.50  bmc1_current_bound:                     -1
% 7.65/1.50  bmc1_last_solved_bound:                 -1
% 7.65/1.50  bmc1_unsat_core_size:                   -1
% 7.65/1.50  bmc1_unsat_core_parents_size:           -1
% 7.65/1.50  bmc1_merge_next_fun:                    0
% 7.65/1.50  bmc1_unsat_core_clauses_time:           0.
% 7.65/1.50  
% 7.65/1.50  ------ Instantiation
% 7.65/1.50  
% 7.65/1.50  inst_num_of_clauses:                    1700
% 7.65/1.50  inst_num_in_passive:                    430
% 7.65/1.50  inst_num_in_active:                     816
% 7.65/1.50  inst_num_in_unprocessed:                454
% 7.65/1.50  inst_num_of_loops:                      1090
% 7.65/1.50  inst_num_of_learning_restarts:          0
% 7.65/1.50  inst_num_moves_active_passive:          266
% 7.65/1.50  inst_lit_activity:                      0
% 7.65/1.50  inst_lit_activity_moves:                0
% 7.65/1.50  inst_num_tautologies:                   0
% 7.65/1.50  inst_num_prop_implied:                  0
% 7.65/1.50  inst_num_existing_simplified:           0
% 7.65/1.50  inst_num_eq_res_simplified:             0
% 7.65/1.50  inst_num_child_elim:                    0
% 7.65/1.50  inst_num_of_dismatching_blockings:      2495
% 7.65/1.50  inst_num_of_non_proper_insts:           2825
% 7.65/1.50  inst_num_of_duplicates:                 0
% 7.65/1.50  inst_inst_num_from_inst_to_res:         0
% 7.65/1.50  inst_dismatching_checking_time:         0.
% 7.65/1.50  
% 7.65/1.50  ------ Resolution
% 7.65/1.50  
% 7.65/1.50  res_num_of_clauses:                     0
% 7.65/1.50  res_num_in_passive:                     0
% 7.65/1.50  res_num_in_active:                      0
% 7.65/1.50  res_num_of_loops:                       95
% 7.65/1.50  res_forward_subset_subsumed:            34
% 7.65/1.50  res_backward_subset_subsumed:           0
% 7.65/1.50  res_forward_subsumed:                   0
% 7.65/1.50  res_backward_subsumed:                  0
% 7.65/1.50  res_forward_subsumption_resolution:     0
% 7.65/1.50  res_backward_subsumption_resolution:    0
% 7.65/1.50  res_clause_to_clause_subsumption:       4727
% 7.65/1.50  res_orphan_elimination:                 0
% 7.65/1.50  res_tautology_del:                      336
% 7.65/1.50  res_num_eq_res_simplified:              0
% 7.65/1.50  res_num_sel_changes:                    0
% 7.65/1.50  res_moves_from_active_to_pass:          0
% 7.65/1.50  
% 7.65/1.50  ------ Superposition
% 7.65/1.50  
% 7.65/1.50  sup_time_total:                         0.
% 7.65/1.50  sup_time_generating:                    0.
% 7.65/1.50  sup_time_sim_full:                      0.
% 7.65/1.50  sup_time_sim_immed:                     0.
% 7.65/1.50  
% 7.65/1.50  sup_num_of_clauses:                     711
% 7.65/1.50  sup_num_in_active:                      215
% 7.65/1.50  sup_num_in_passive:                     496
% 7.65/1.50  sup_num_of_loops:                       217
% 7.65/1.50  sup_fw_superposition:                   157
% 7.65/1.50  sup_bw_superposition:                   803
% 7.65/1.50  sup_immediate_simplified:               209
% 7.65/1.50  sup_given_eliminated:                   0
% 7.65/1.50  comparisons_done:                       0
% 7.65/1.50  comparisons_avoided:                    0
% 7.65/1.50  
% 7.65/1.50  ------ Simplifications
% 7.65/1.50  
% 7.65/1.50  
% 7.65/1.50  sim_fw_subset_subsumed:                 58
% 7.65/1.50  sim_bw_subset_subsumed:                 2
% 7.65/1.50  sim_fw_subsumed:                        132
% 7.65/1.50  sim_bw_subsumed:                        8
% 7.65/1.50  sim_fw_subsumption_res:                 0
% 7.65/1.50  sim_bw_subsumption_res:                 0
% 7.65/1.50  sim_tautology_del:                      2
% 7.65/1.50  sim_eq_tautology_del:                   0
% 7.65/1.50  sim_eq_res_simp:                        8
% 7.65/1.50  sim_fw_demodulated:                     0
% 7.65/1.50  sim_bw_demodulated:                     0
% 7.65/1.50  sim_light_normalised:                   79
% 7.65/1.50  sim_joinable_taut:                      0
% 7.65/1.50  sim_joinable_simp:                      0
% 7.65/1.50  sim_ac_normalised:                      0
% 7.65/1.50  sim_smt_subsumption:                    0
% 7.65/1.50  
%------------------------------------------------------------------------------
