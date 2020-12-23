%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:52:52 EST 2020

% Result     : Theorem 3.89s
% Output     : CNFRefutation 3.89s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 312 expanded)
%              Number of clauses        :   54 (  81 expanded)
%              Number of leaves         :   14 (  77 expanded)
%              Depth                    :   19
%              Number of atoms          :  489 (2140 expanded)
%              Number of equality atoms :   73 ( 109 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f9,conjecture,(
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

fof(f10,negated_conjecture,(
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
    inference(negated_conjecture,[],[f9])).

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
    inference(ennf_transformation,[],[f10])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

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
    inference(nnf_transformation,[],[f24])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f40,plain,(
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

fof(f39,plain,(
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

fof(f38,plain,
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

fof(f41,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f37,f40,f39,f38])).

fof(f59,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f61,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f6,axiom,(
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

fof(f17,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f33,plain,(
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
    inference(rectify,[],[f32])).

fof(f34,plain,(
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

fof(f35,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f33,f34])).

fof(f51,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X4,X2)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f70,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X4,k10_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f51])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f64,plain,
    ( r1_tarski(k9_relat_1(sK2,sK4),k1_relat_1(sK3))
    | r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f41])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
          & r1_tarski(X0,k1_relat_1(X2)) )
       => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f60,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f63,plain,
    ( r1_tarski(sK4,k1_relat_1(sK2))
    | r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f41])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( ( r1_tarski(X0,X1)
              & r1_tarski(X2,X3) )
           => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1))
          | ~ r1_tarski(X0,X1)
          | ~ r1_tarski(X2,X3)
          | ~ v1_relat_1(X3) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1))
          | ~ r1_tarski(X0,X1)
          | ~ r1_tarski(X2,X3)
          | ~ v1_relat_1(X3) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1))
      | ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X2,X3)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f29])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f67,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f45])).

fof(f65,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,sK4),k1_relat_1(sK3))
    | ~ r1_tarski(sK4,k1_relat_1(sK2))
    | ~ r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_988,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(k9_relat_1(X2,X3),X0)
    | r1_tarski(k9_relat_1(X2,X3),X1) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1634,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(k9_relat_1(X2,sK4),X0)
    | r1_tarski(k9_relat_1(X2,sK4),X1) ),
    inference(instantiation,[status(thm)],[c_988])).

cnf(c_8169,plain,
    ( ~ r1_tarski(k9_relat_1(X0,k1_relat_1(k5_relat_1(sK2,sK3))),X1)
    | r1_tarski(k9_relat_1(X2,sK4),X1)
    | ~ r1_tarski(k9_relat_1(X2,sK4),k9_relat_1(X0,k1_relat_1(k5_relat_1(sK2,sK3)))) ),
    inference(instantiation,[status(thm)],[c_1634])).

cnf(c_11888,plain,
    ( ~ r1_tarski(k9_relat_1(X0,k1_relat_1(k5_relat_1(sK2,sK3))),k1_relat_1(sK3))
    | ~ r1_tarski(k9_relat_1(sK2,sK4),k9_relat_1(X0,k1_relat_1(k5_relat_1(sK2,sK3))))
    | r1_tarski(k9_relat_1(sK2,sK4),k1_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_8169])).

cnf(c_11890,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k1_relat_1(k5_relat_1(sK2,sK3))),k1_relat_1(sK3))
    | ~ r1_tarski(k9_relat_1(sK2,sK4),k9_relat_1(sK2,k1_relat_1(k5_relat_1(sK2,sK3))))
    | r1_tarski(k9_relat_1(sK2,sK4),k1_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_11888])).

cnf(c_23,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_691,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_21,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_693,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X1,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_706,plain,
    ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1515,plain,
    ( k10_relat_1(X0,k1_relat_1(sK3)) = k1_relat_1(k5_relat_1(X0,sK3))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_693,c_706])).

cnf(c_2464,plain,
    ( k10_relat_1(sK2,k1_relat_1(sK3)) = k1_relat_1(k5_relat_1(sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_691,c_1515])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_712,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_700,plain,
    ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
    | r2_hidden(X0,k1_relat_1(X1)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1679,plain,
    ( r2_hidden(sK0(k10_relat_1(X0,X1),X2),k1_relat_1(X0)) = iProver_top
    | r1_tarski(k10_relat_1(X0,X1),X2) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_712,c_700])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_713,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_8636,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1679,c_713])).

cnf(c_8903,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(sK2,sK3)),k1_relat_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2464,c_8636])).

cnf(c_8950,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(sK2,sK3)),k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_8903])).

cnf(c_18,negated_conjecture,
    ( r1_tarski(k9_relat_1(sK2,sK4),k1_relat_1(sK3))
    | r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_696,plain,
    ( r1_tarski(k9_relat_1(sK2,sK4),k1_relat_1(sK3)) = iProver_top
    | r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_16,plain,
    ( r1_tarski(X0,k10_relat_1(X1,X2))
    | ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ r1_tarski(k9_relat_1(X1,X0),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_698,plain,
    ( r1_tarski(X0,k10_relat_1(X1,X2)) = iProver_top
    | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
    | r1_tarski(k9_relat_1(X1,X0),X2) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1537,plain,
    ( r1_tarski(sK4,k10_relat_1(sK2,k1_relat_1(sK3))) = iProver_top
    | r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3))) = iProver_top
    | r1_tarski(sK4,k1_relat_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_696,c_698])).

cnf(c_5384,plain,
    ( r1_tarski(sK4,k10_relat_1(sK2,k1_relat_1(sK3)))
    | r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3)))
    | ~ r1_tarski(sK4,k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[status(thm)],[c_16,c_18])).

cnf(c_22,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_19,negated_conjecture,
    ( r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3)))
    | r1_tarski(sK4,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1563,plain,
    ( r1_tarski(sK4,k10_relat_1(sK2,k1_relat_1(sK3)))
    | r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3)))
    | ~ r1_tarski(sK4,k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1537])).

cnf(c_5778,plain,
    ( r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3)))
    | r1_tarski(sK4,k10_relat_1(sK2,k1_relat_1(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5384,c_23,c_22,c_19,c_1563])).

cnf(c_5779,plain,
    ( r1_tarski(sK4,k10_relat_1(sK2,k1_relat_1(sK3)))
    | r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3))) ),
    inference(renaming,[status(thm)],[c_5778])).

cnf(c_5780,plain,
    ( r1_tarski(sK4,k10_relat_1(sK2,k1_relat_1(sK3))) = iProver_top
    | r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5779])).

cnf(c_8000,plain,
    ( r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3))) = iProver_top
    | r1_tarski(sK4,k10_relat_1(sK2,k1_relat_1(sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1537,c_5780])).

cnf(c_8001,plain,
    ( r1_tarski(sK4,k10_relat_1(sK2,k1_relat_1(sK3))) = iProver_top
    | r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3))) = iProver_top ),
    inference(renaming,[status(thm)],[c_8000])).

cnf(c_8004,plain,
    ( r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8001,c_2464])).

cnf(c_8006,plain,
    ( r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_8004])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X3)
    | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1665,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k9_relat_1(X0,sK4),k9_relat_1(X1,X2))
    | ~ r1_tarski(sK4,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_3447,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k9_relat_1(X0,sK4),k9_relat_1(X1,k1_relat_1(k5_relat_1(sK2,sK3))))
    | ~ r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3)))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_1665])).

cnf(c_3449,plain,
    ( r1_tarski(k9_relat_1(sK2,sK4),k9_relat_1(sK2,k1_relat_1(k5_relat_1(sK2,sK3))))
    | ~ r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3)))
    | ~ r1_tarski(sK2,sK2)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_3447])).

cnf(c_15,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_699,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2733,plain,
    ( r1_tarski(k9_relat_1(sK2,k1_relat_1(k5_relat_1(sK2,sK3))),k1_relat_1(sK3)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2464,c_699])).

cnf(c_2758,plain,
    ( r1_tarski(k9_relat_1(sK2,k1_relat_1(k5_relat_1(sK2,sK3))),k1_relat_1(sK3))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2733])).

cnf(c_939,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK2))
    | ~ r1_tarski(sK4,X0)
    | r1_tarski(sK4,k1_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1230,plain,
    ( ~ r1_tarski(k1_relat_1(k5_relat_1(sK2,sK3)),k1_relat_1(sK2))
    | ~ r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3)))
    | r1_tarski(sK4,k1_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_939])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_63,plain,
    ( r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_17,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(sK2,sK4),k1_relat_1(sK3))
    | ~ r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3)))
    | ~ r1_tarski(sK4,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f65])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11890,c_8950,c_8006,c_3449,c_2758,c_1230,c_63,c_17,c_22,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:44:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.89/0.94  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.89/0.94  
% 3.89/0.94  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.89/0.94  
% 3.89/0.94  ------  iProver source info
% 3.89/0.94  
% 3.89/0.94  git: date: 2020-06-30 10:37:57 +0100
% 3.89/0.94  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.89/0.94  git: non_committed_changes: false
% 3.89/0.94  git: last_make_outside_of_git: false
% 3.89/0.94  
% 3.89/0.94  ------ 
% 3.89/0.94  
% 3.89/0.94  ------ Input Options
% 3.89/0.94  
% 3.89/0.94  --out_options                           all
% 3.89/0.94  --tptp_safe_out                         true
% 3.89/0.94  --problem_path                          ""
% 3.89/0.94  --include_path                          ""
% 3.89/0.94  --clausifier                            res/vclausify_rel
% 3.89/0.94  --clausifier_options                    --mode clausify
% 3.89/0.94  --stdin                                 false
% 3.89/0.94  --stats_out                             sel
% 3.89/0.94  
% 3.89/0.94  ------ General Options
% 3.89/0.94  
% 3.89/0.94  --fof                                   false
% 3.89/0.94  --time_out_real                         604.99
% 3.89/0.94  --time_out_virtual                      -1.
% 3.89/0.94  --symbol_type_check                     false
% 3.89/0.94  --clausify_out                          false
% 3.89/0.94  --sig_cnt_out                           false
% 3.89/0.94  --trig_cnt_out                          false
% 3.89/0.94  --trig_cnt_out_tolerance                1.
% 3.89/0.94  --trig_cnt_out_sk_spl                   false
% 3.89/0.94  --abstr_cl_out                          false
% 3.89/0.94  
% 3.89/0.94  ------ Global Options
% 3.89/0.94  
% 3.89/0.94  --schedule                              none
% 3.89/0.94  --add_important_lit                     false
% 3.89/0.94  --prop_solver_per_cl                    1000
% 3.89/0.94  --min_unsat_core                        false
% 3.89/0.94  --soft_assumptions                      false
% 3.89/0.94  --soft_lemma_size                       3
% 3.89/0.94  --prop_impl_unit_size                   0
% 3.89/0.94  --prop_impl_unit                        []
% 3.89/0.94  --share_sel_clauses                     true
% 3.89/0.94  --reset_solvers                         false
% 3.89/0.94  --bc_imp_inh                            [conj_cone]
% 3.89/0.94  --conj_cone_tolerance                   3.
% 3.89/0.94  --extra_neg_conj                        none
% 3.89/0.94  --large_theory_mode                     true
% 3.89/0.94  --prolific_symb_bound                   200
% 3.89/0.94  --lt_threshold                          2000
% 3.89/0.94  --clause_weak_htbl                      true
% 3.89/0.94  --gc_record_bc_elim                     false
% 3.89/0.94  
% 3.89/0.94  ------ Preprocessing Options
% 3.89/0.94  
% 3.89/0.94  --preprocessing_flag                    true
% 3.89/0.94  --time_out_prep_mult                    0.1
% 3.89/0.94  --splitting_mode                        input
% 3.89/0.94  --splitting_grd                         true
% 3.89/0.94  --splitting_cvd                         false
% 3.89/0.94  --splitting_cvd_svl                     false
% 3.89/0.94  --splitting_nvd                         32
% 3.89/0.94  --sub_typing                            true
% 3.89/0.94  --prep_gs_sim                           false
% 3.89/0.94  --prep_unflatten                        true
% 3.89/0.94  --prep_res_sim                          true
% 3.89/0.94  --prep_upred                            true
% 3.89/0.94  --prep_sem_filter                       exhaustive
% 3.89/0.94  --prep_sem_filter_out                   false
% 3.89/0.94  --pred_elim                             false
% 3.89/0.94  --res_sim_input                         true
% 3.89/0.94  --eq_ax_congr_red                       true
% 3.89/0.94  --pure_diseq_elim                       true
% 3.89/0.94  --brand_transform                       false
% 3.89/0.94  --non_eq_to_eq                          false
% 3.89/0.94  --prep_def_merge                        true
% 3.89/0.94  --prep_def_merge_prop_impl              false
% 3.89/0.94  --prep_def_merge_mbd                    true
% 3.89/0.94  --prep_def_merge_tr_red                 false
% 3.89/0.94  --prep_def_merge_tr_cl                  false
% 3.89/0.94  --smt_preprocessing                     true
% 3.89/0.94  --smt_ac_axioms                         fast
% 3.89/0.94  --preprocessed_out                      false
% 3.89/0.94  --preprocessed_stats                    false
% 3.89/0.94  
% 3.89/0.94  ------ Abstraction refinement Options
% 3.89/0.94  
% 3.89/0.94  --abstr_ref                             []
% 3.89/0.94  --abstr_ref_prep                        false
% 3.89/0.94  --abstr_ref_until_sat                   false
% 3.89/0.94  --abstr_ref_sig_restrict                funpre
% 3.89/0.94  --abstr_ref_af_restrict_to_split_sk     false
% 3.89/0.94  --abstr_ref_under                       []
% 3.89/0.94  
% 3.89/0.94  ------ SAT Options
% 3.89/0.94  
% 3.89/0.94  --sat_mode                              false
% 3.89/0.94  --sat_fm_restart_options                ""
% 3.89/0.94  --sat_gr_def                            false
% 3.89/0.94  --sat_epr_types                         true
% 3.89/0.94  --sat_non_cyclic_types                  false
% 3.89/0.94  --sat_finite_models                     false
% 3.89/0.94  --sat_fm_lemmas                         false
% 3.89/0.94  --sat_fm_prep                           false
% 3.89/0.94  --sat_fm_uc_incr                        true
% 3.89/0.94  --sat_out_model                         small
% 3.89/0.94  --sat_out_clauses                       false
% 3.89/0.94  
% 3.89/0.94  ------ QBF Options
% 3.89/0.94  
% 3.89/0.94  --qbf_mode                              false
% 3.89/0.94  --qbf_elim_univ                         false
% 3.89/0.94  --qbf_dom_inst                          none
% 3.89/0.94  --qbf_dom_pre_inst                      false
% 3.89/0.94  --qbf_sk_in                             false
% 3.89/0.94  --qbf_pred_elim                         true
% 3.89/0.94  --qbf_split                             512
% 3.89/0.94  
% 3.89/0.94  ------ BMC1 Options
% 3.89/0.94  
% 3.89/0.94  --bmc1_incremental                      false
% 3.89/0.94  --bmc1_axioms                           reachable_all
% 3.89/0.94  --bmc1_min_bound                        0
% 3.89/0.94  --bmc1_max_bound                        -1
% 3.89/0.94  --bmc1_max_bound_default                -1
% 3.89/0.94  --bmc1_symbol_reachability              true
% 3.89/0.94  --bmc1_property_lemmas                  false
% 3.89/0.94  --bmc1_k_induction                      false
% 3.89/0.94  --bmc1_non_equiv_states                 false
% 3.89/0.94  --bmc1_deadlock                         false
% 3.89/0.94  --bmc1_ucm                              false
% 3.89/0.94  --bmc1_add_unsat_core                   none
% 3.89/0.94  --bmc1_unsat_core_children              false
% 3.89/0.94  --bmc1_unsat_core_extrapolate_axioms    false
% 3.89/0.94  --bmc1_out_stat                         full
% 3.89/0.94  --bmc1_ground_init                      false
% 3.89/0.94  --bmc1_pre_inst_next_state              false
% 3.89/0.94  --bmc1_pre_inst_state                   false
% 3.89/0.94  --bmc1_pre_inst_reach_state             false
% 3.89/0.94  --bmc1_out_unsat_core                   false
% 3.89/0.94  --bmc1_aig_witness_out                  false
% 3.89/0.94  --bmc1_verbose                          false
% 3.89/0.94  --bmc1_dump_clauses_tptp                false
% 3.89/0.94  --bmc1_dump_unsat_core_tptp             false
% 3.89/0.94  --bmc1_dump_file                        -
% 3.89/0.94  --bmc1_ucm_expand_uc_limit              128
% 3.89/0.94  --bmc1_ucm_n_expand_iterations          6
% 3.89/0.94  --bmc1_ucm_extend_mode                  1
% 3.89/0.94  --bmc1_ucm_init_mode                    2
% 3.89/0.94  --bmc1_ucm_cone_mode                    none
% 3.89/0.94  --bmc1_ucm_reduced_relation_type        0
% 3.89/0.94  --bmc1_ucm_relax_model                  4
% 3.89/0.94  --bmc1_ucm_full_tr_after_sat            true
% 3.89/0.94  --bmc1_ucm_expand_neg_assumptions       false
% 3.89/0.94  --bmc1_ucm_layered_model                none
% 3.89/0.94  --bmc1_ucm_max_lemma_size               10
% 3.89/0.94  
% 3.89/0.94  ------ AIG Options
% 3.89/0.94  
% 3.89/0.94  --aig_mode                              false
% 3.89/0.94  
% 3.89/0.94  ------ Instantiation Options
% 3.89/0.94  
% 3.89/0.94  --instantiation_flag                    true
% 3.89/0.94  --inst_sos_flag                         false
% 3.89/0.94  --inst_sos_phase                        true
% 3.89/0.94  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.89/0.94  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.89/0.94  --inst_lit_sel_side                     num_symb
% 3.89/0.94  --inst_solver_per_active                1400
% 3.89/0.94  --inst_solver_calls_frac                1.
% 3.89/0.94  --inst_passive_queue_type               priority_queues
% 3.89/0.94  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.89/0.94  --inst_passive_queues_freq              [25;2]
% 3.89/0.94  --inst_dismatching                      true
% 3.89/0.94  --inst_eager_unprocessed_to_passive     true
% 3.89/0.94  --inst_prop_sim_given                   true
% 3.89/0.94  --inst_prop_sim_new                     false
% 3.89/0.94  --inst_subs_new                         false
% 3.89/0.94  --inst_eq_res_simp                      false
% 3.89/0.94  --inst_subs_given                       false
% 3.89/0.94  --inst_orphan_elimination               true
% 3.89/0.94  --inst_learning_loop_flag               true
% 3.89/0.94  --inst_learning_start                   3000
% 3.89/0.94  --inst_learning_factor                  2
% 3.89/0.94  --inst_start_prop_sim_after_learn       3
% 3.89/0.94  --inst_sel_renew                        solver
% 3.89/0.94  --inst_lit_activity_flag                true
% 3.89/0.94  --inst_restr_to_given                   false
% 3.89/0.94  --inst_activity_threshold               500
% 3.89/0.94  --inst_out_proof                        true
% 3.89/0.94  
% 3.89/0.94  ------ Resolution Options
% 3.89/0.94  
% 3.89/0.94  --resolution_flag                       true
% 3.89/0.94  --res_lit_sel                           adaptive
% 3.89/0.94  --res_lit_sel_side                      none
% 3.89/0.94  --res_ordering                          kbo
% 3.89/0.94  --res_to_prop_solver                    active
% 3.89/0.94  --res_prop_simpl_new                    false
% 3.89/0.94  --res_prop_simpl_given                  true
% 3.89/0.94  --res_passive_queue_type                priority_queues
% 3.89/0.94  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.89/0.94  --res_passive_queues_freq               [15;5]
% 3.89/0.94  --res_forward_subs                      full
% 3.89/0.94  --res_backward_subs                     full
% 3.89/0.94  --res_forward_subs_resolution           true
% 3.89/0.94  --res_backward_subs_resolution          true
% 3.89/0.94  --res_orphan_elimination                true
% 3.89/0.94  --res_time_limit                        2.
% 3.89/0.94  --res_out_proof                         true
% 3.89/0.94  
% 3.89/0.94  ------ Superposition Options
% 3.89/0.94  
% 3.89/0.94  --superposition_flag                    true
% 3.89/0.94  --sup_passive_queue_type                priority_queues
% 3.89/0.94  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.89/0.94  --sup_passive_queues_freq               [1;4]
% 3.89/0.94  --demod_completeness_check              fast
% 3.89/0.94  --demod_use_ground                      true
% 3.89/0.94  --sup_to_prop_solver                    passive
% 3.89/0.94  --sup_prop_simpl_new                    true
% 3.89/0.94  --sup_prop_simpl_given                  true
% 3.89/0.94  --sup_fun_splitting                     false
% 3.89/0.94  --sup_smt_interval                      50000
% 3.89/0.94  
% 3.89/0.94  ------ Superposition Simplification Setup
% 3.89/0.94  
% 3.89/0.94  --sup_indices_passive                   []
% 3.89/0.94  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.89/0.94  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.89/0.94  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.89/0.94  --sup_full_triv                         [TrivRules;PropSubs]
% 3.89/0.94  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.89/0.94  --sup_full_bw                           [BwDemod]
% 3.89/0.94  --sup_immed_triv                        [TrivRules]
% 3.89/0.94  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.89/0.94  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.89/0.94  --sup_immed_bw_main                     []
% 3.89/0.94  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.89/0.94  --sup_input_triv                        [Unflattening;TrivRules]
% 3.89/0.94  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.89/0.94  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.89/0.94  
% 3.89/0.94  ------ Combination Options
% 3.89/0.94  
% 3.89/0.94  --comb_res_mult                         3
% 3.89/0.94  --comb_sup_mult                         2
% 3.89/0.94  --comb_inst_mult                        10
% 3.89/0.94  
% 3.89/0.94  ------ Debug Options
% 3.89/0.94  
% 3.89/0.94  --dbg_backtrace                         false
% 3.89/0.94  --dbg_dump_prop_clauses                 false
% 3.89/0.94  --dbg_dump_prop_clauses_file            -
% 3.89/0.94  --dbg_out_stat                          false
% 3.89/0.94  ------ Parsing...
% 3.89/0.94  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.89/0.94  
% 3.89/0.94  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 3.89/0.94  
% 3.89/0.94  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.89/0.94  
% 3.89/0.94  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.89/0.94  ------ Proving...
% 3.89/0.94  ------ Problem Properties 
% 3.89/0.94  
% 3.89/0.94  
% 3.89/0.94  clauses                                 23
% 3.89/0.94  conjectures                             7
% 3.89/0.94  EPR                                     8
% 3.89/0.94  Horn                                    18
% 3.89/0.94  unary                                   5
% 3.89/0.94  binary                                  4
% 3.89/0.94  lits                                    70
% 3.89/0.94  lits eq                                 5
% 3.89/0.94  fd_pure                                 0
% 3.89/0.94  fd_pseudo                               0
% 3.89/0.94  fd_cond                                 0
% 3.89/0.94  fd_pseudo_cond                          4
% 3.89/0.94  AC symbols                              0
% 3.89/0.94  
% 3.89/0.94  ------ Input Options Time Limit: Unbounded
% 3.89/0.94  
% 3.89/0.94  
% 3.89/0.94  ------ 
% 3.89/0.94  Current options:
% 3.89/0.94  ------ 
% 3.89/0.94  
% 3.89/0.94  ------ Input Options
% 3.89/0.94  
% 3.89/0.94  --out_options                           all
% 3.89/0.94  --tptp_safe_out                         true
% 3.89/0.94  --problem_path                          ""
% 3.89/0.94  --include_path                          ""
% 3.89/0.94  --clausifier                            res/vclausify_rel
% 3.89/0.94  --clausifier_options                    --mode clausify
% 3.89/0.94  --stdin                                 false
% 3.89/0.94  --stats_out                             sel
% 3.89/0.94  
% 3.89/0.94  ------ General Options
% 3.89/0.94  
% 3.89/0.94  --fof                                   false
% 3.89/0.94  --time_out_real                         604.99
% 3.89/0.94  --time_out_virtual                      -1.
% 3.89/0.94  --symbol_type_check                     false
% 3.89/0.94  --clausify_out                          false
% 3.89/0.94  --sig_cnt_out                           false
% 3.89/0.94  --trig_cnt_out                          false
% 3.89/0.94  --trig_cnt_out_tolerance                1.
% 3.89/0.94  --trig_cnt_out_sk_spl                   false
% 3.89/0.94  --abstr_cl_out                          false
% 3.89/0.94  
% 3.89/0.94  ------ Global Options
% 3.89/0.94  
% 3.89/0.94  --schedule                              none
% 3.89/0.94  --add_important_lit                     false
% 3.89/0.94  --prop_solver_per_cl                    1000
% 3.89/0.94  --min_unsat_core                        false
% 3.89/0.94  --soft_assumptions                      false
% 3.89/0.94  --soft_lemma_size                       3
% 3.89/0.94  --prop_impl_unit_size                   0
% 3.89/0.94  --prop_impl_unit                        []
% 3.89/0.94  --share_sel_clauses                     true
% 3.89/0.94  --reset_solvers                         false
% 3.89/0.94  --bc_imp_inh                            [conj_cone]
% 3.89/0.94  --conj_cone_tolerance                   3.
% 3.89/0.94  --extra_neg_conj                        none
% 3.89/0.94  --large_theory_mode                     true
% 3.89/0.94  --prolific_symb_bound                   200
% 3.89/0.94  --lt_threshold                          2000
% 3.89/0.94  --clause_weak_htbl                      true
% 3.89/0.94  --gc_record_bc_elim                     false
% 3.89/0.94  
% 3.89/0.94  ------ Preprocessing Options
% 3.89/0.94  
% 3.89/0.94  --preprocessing_flag                    true
% 3.89/0.94  --time_out_prep_mult                    0.1
% 3.89/0.94  --splitting_mode                        input
% 3.89/0.94  --splitting_grd                         true
% 3.89/0.94  --splitting_cvd                         false
% 3.89/0.94  --splitting_cvd_svl                     false
% 3.89/0.94  --splitting_nvd                         32
% 3.89/0.94  --sub_typing                            true
% 3.89/0.94  --prep_gs_sim                           false
% 3.89/0.94  --prep_unflatten                        true
% 3.89/0.94  --prep_res_sim                          true
% 3.89/0.94  --prep_upred                            true
% 3.89/0.94  --prep_sem_filter                       exhaustive
% 3.89/0.94  --prep_sem_filter_out                   false
% 3.89/0.94  --pred_elim                             false
% 3.89/0.94  --res_sim_input                         true
% 3.89/0.94  --eq_ax_congr_red                       true
% 3.89/0.94  --pure_diseq_elim                       true
% 3.89/0.94  --brand_transform                       false
% 3.89/0.94  --non_eq_to_eq                          false
% 3.89/0.94  --prep_def_merge                        true
% 3.89/0.94  --prep_def_merge_prop_impl              false
% 3.89/0.94  --prep_def_merge_mbd                    true
% 3.89/0.94  --prep_def_merge_tr_red                 false
% 3.89/0.94  --prep_def_merge_tr_cl                  false
% 3.89/0.94  --smt_preprocessing                     true
% 3.89/0.94  --smt_ac_axioms                         fast
% 3.89/0.94  --preprocessed_out                      false
% 3.89/0.94  --preprocessed_stats                    false
% 3.89/0.94  
% 3.89/0.94  ------ Abstraction refinement Options
% 3.89/0.94  
% 3.89/0.94  --abstr_ref                             []
% 3.89/0.94  --abstr_ref_prep                        false
% 3.89/0.94  --abstr_ref_until_sat                   false
% 3.89/0.94  --abstr_ref_sig_restrict                funpre
% 3.89/0.94  --abstr_ref_af_restrict_to_split_sk     false
% 3.89/0.94  --abstr_ref_under                       []
% 3.89/0.94  
% 3.89/0.94  ------ SAT Options
% 3.89/0.94  
% 3.89/0.94  --sat_mode                              false
% 3.89/0.94  --sat_fm_restart_options                ""
% 3.89/0.94  --sat_gr_def                            false
% 3.89/0.94  --sat_epr_types                         true
% 3.89/0.94  --sat_non_cyclic_types                  false
% 3.89/0.94  --sat_finite_models                     false
% 3.89/0.94  --sat_fm_lemmas                         false
% 3.89/0.94  --sat_fm_prep                           false
% 3.89/0.94  --sat_fm_uc_incr                        true
% 3.89/0.94  --sat_out_model                         small
% 3.89/0.94  --sat_out_clauses                       false
% 3.89/0.94  
% 3.89/0.94  ------ QBF Options
% 3.89/0.94  
% 3.89/0.94  --qbf_mode                              false
% 3.89/0.94  --qbf_elim_univ                         false
% 3.89/0.94  --qbf_dom_inst                          none
% 3.89/0.94  --qbf_dom_pre_inst                      false
% 3.89/0.94  --qbf_sk_in                             false
% 3.89/0.94  --qbf_pred_elim                         true
% 3.89/0.94  --qbf_split                             512
% 3.89/0.94  
% 3.89/0.94  ------ BMC1 Options
% 3.89/0.94  
% 3.89/0.94  --bmc1_incremental                      false
% 3.89/0.94  --bmc1_axioms                           reachable_all
% 3.89/0.94  --bmc1_min_bound                        0
% 3.89/0.94  --bmc1_max_bound                        -1
% 3.89/0.94  --bmc1_max_bound_default                -1
% 3.89/0.94  --bmc1_symbol_reachability              true
% 3.89/0.94  --bmc1_property_lemmas                  false
% 3.89/0.94  --bmc1_k_induction                      false
% 3.89/0.94  --bmc1_non_equiv_states                 false
% 3.89/0.94  --bmc1_deadlock                         false
% 3.89/0.94  --bmc1_ucm                              false
% 3.89/0.94  --bmc1_add_unsat_core                   none
% 3.89/0.94  --bmc1_unsat_core_children              false
% 3.89/0.94  --bmc1_unsat_core_extrapolate_axioms    false
% 3.89/0.94  --bmc1_out_stat                         full
% 3.89/0.94  --bmc1_ground_init                      false
% 3.89/0.94  --bmc1_pre_inst_next_state              false
% 3.89/0.94  --bmc1_pre_inst_state                   false
% 3.89/0.94  --bmc1_pre_inst_reach_state             false
% 3.89/0.94  --bmc1_out_unsat_core                   false
% 3.89/0.94  --bmc1_aig_witness_out                  false
% 3.89/0.94  --bmc1_verbose                          false
% 3.89/0.94  --bmc1_dump_clauses_tptp                false
% 3.89/0.94  --bmc1_dump_unsat_core_tptp             false
% 3.89/0.94  --bmc1_dump_file                        -
% 3.89/0.94  --bmc1_ucm_expand_uc_limit              128
% 3.89/0.94  --bmc1_ucm_n_expand_iterations          6
% 3.89/0.94  --bmc1_ucm_extend_mode                  1
% 3.89/0.94  --bmc1_ucm_init_mode                    2
% 3.89/0.94  --bmc1_ucm_cone_mode                    none
% 3.89/0.94  --bmc1_ucm_reduced_relation_type        0
% 3.89/0.94  --bmc1_ucm_relax_model                  4
% 3.89/0.94  --bmc1_ucm_full_tr_after_sat            true
% 3.89/0.94  --bmc1_ucm_expand_neg_assumptions       false
% 3.89/0.94  --bmc1_ucm_layered_model                none
% 3.89/0.94  --bmc1_ucm_max_lemma_size               10
% 3.89/0.94  
% 3.89/0.94  ------ AIG Options
% 3.89/0.94  
% 3.89/0.94  --aig_mode                              false
% 3.89/0.94  
% 3.89/0.94  ------ Instantiation Options
% 3.89/0.94  
% 3.89/0.94  --instantiation_flag                    true
% 3.89/0.94  --inst_sos_flag                         false
% 3.89/0.94  --inst_sos_phase                        true
% 3.89/0.94  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.89/0.94  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.89/0.94  --inst_lit_sel_side                     num_symb
% 3.89/0.94  --inst_solver_per_active                1400
% 3.89/0.94  --inst_solver_calls_frac                1.
% 3.89/0.94  --inst_passive_queue_type               priority_queues
% 3.89/0.94  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.89/0.94  --inst_passive_queues_freq              [25;2]
% 3.89/0.94  --inst_dismatching                      true
% 3.89/0.94  --inst_eager_unprocessed_to_passive     true
% 3.89/0.94  --inst_prop_sim_given                   true
% 3.89/0.94  --inst_prop_sim_new                     false
% 3.89/0.94  --inst_subs_new                         false
% 3.89/0.94  --inst_eq_res_simp                      false
% 3.89/0.94  --inst_subs_given                       false
% 3.89/0.94  --inst_orphan_elimination               true
% 3.89/0.94  --inst_learning_loop_flag               true
% 3.89/0.94  --inst_learning_start                   3000
% 3.89/0.94  --inst_learning_factor                  2
% 3.89/0.94  --inst_start_prop_sim_after_learn       3
% 3.89/0.94  --inst_sel_renew                        solver
% 3.89/0.94  --inst_lit_activity_flag                true
% 3.89/0.94  --inst_restr_to_given                   false
% 3.89/0.94  --inst_activity_threshold               500
% 3.89/0.94  --inst_out_proof                        true
% 3.89/0.94  
% 3.89/0.94  ------ Resolution Options
% 3.89/0.94  
% 3.89/0.94  --resolution_flag                       true
% 3.89/0.94  --res_lit_sel                           adaptive
% 3.89/0.94  --res_lit_sel_side                      none
% 3.89/0.94  --res_ordering                          kbo
% 3.89/0.94  --res_to_prop_solver                    active
% 3.89/0.94  --res_prop_simpl_new                    false
% 3.89/0.94  --res_prop_simpl_given                  true
% 3.89/0.94  --res_passive_queue_type                priority_queues
% 3.89/0.94  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.89/0.94  --res_passive_queues_freq               [15;5]
% 3.89/0.94  --res_forward_subs                      full
% 3.89/0.94  --res_backward_subs                     full
% 3.89/0.94  --res_forward_subs_resolution           true
% 3.89/0.94  --res_backward_subs_resolution          true
% 3.89/0.94  --res_orphan_elimination                true
% 3.89/0.94  --res_time_limit                        2.
% 3.89/0.94  --res_out_proof                         true
% 3.89/0.94  
% 3.89/0.94  ------ Superposition Options
% 3.89/0.94  
% 3.89/0.94  --superposition_flag                    true
% 3.89/0.94  --sup_passive_queue_type                priority_queues
% 3.89/0.94  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.89/0.94  --sup_passive_queues_freq               [1;4]
% 3.89/0.94  --demod_completeness_check              fast
% 3.89/0.94  --demod_use_ground                      true
% 3.89/0.94  --sup_to_prop_solver                    passive
% 3.89/0.94  --sup_prop_simpl_new                    true
% 3.89/0.94  --sup_prop_simpl_given                  true
% 3.89/0.94  --sup_fun_splitting                     false
% 3.89/0.94  --sup_smt_interval                      50000
% 3.89/0.94  
% 3.89/0.94  ------ Superposition Simplification Setup
% 3.89/0.94  
% 3.89/0.94  --sup_indices_passive                   []
% 3.89/0.94  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.89/0.94  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.89/0.94  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.89/0.94  --sup_full_triv                         [TrivRules;PropSubs]
% 3.89/0.94  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.89/0.94  --sup_full_bw                           [BwDemod]
% 3.89/0.94  --sup_immed_triv                        [TrivRules]
% 3.89/0.94  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.89/0.94  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.89/0.94  --sup_immed_bw_main                     []
% 3.89/0.94  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.89/0.94  --sup_input_triv                        [Unflattening;TrivRules]
% 3.89/0.94  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.89/0.94  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.89/0.94  
% 3.89/0.94  ------ Combination Options
% 3.89/0.94  
% 3.89/0.94  --comb_res_mult                         3
% 3.89/0.94  --comb_sup_mult                         2
% 3.89/0.94  --comb_inst_mult                        10
% 3.89/0.94  
% 3.89/0.94  ------ Debug Options
% 3.89/0.94  
% 3.89/0.94  --dbg_backtrace                         false
% 3.89/0.94  --dbg_dump_prop_clauses                 false
% 3.89/0.94  --dbg_dump_prop_clauses_file            -
% 3.89/0.94  --dbg_out_stat                          false
% 3.89/0.94  
% 3.89/0.94  
% 3.89/0.94  
% 3.89/0.94  
% 3.89/0.94  ------ Proving...
% 3.89/0.94  
% 3.89/0.94  
% 3.89/0.94  % SZS status Theorem for theBenchmark.p
% 3.89/0.94  
% 3.89/0.94  % SZS output start CNFRefutation for theBenchmark.p
% 3.89/0.94  
% 3.89/0.94  fof(f3,axiom,(
% 3.89/0.94    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 3.89/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.89/0.94  
% 3.89/0.94  fof(f12,plain,(
% 3.89/0.94    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.89/0.94    inference(ennf_transformation,[],[f3])).
% 3.89/0.94  
% 3.89/0.94  fof(f13,plain,(
% 3.89/0.94    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 3.89/0.94    inference(flattening,[],[f12])).
% 3.89/0.94  
% 3.89/0.94  fof(f48,plain,(
% 3.89/0.94    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 3.89/0.94    inference(cnf_transformation,[],[f13])).
% 3.89/0.94  
% 3.89/0.94  fof(f9,conjecture,(
% 3.89/0.94    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <=> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))))))),
% 3.89/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.89/0.94  
% 3.89/0.94  fof(f10,negated_conjecture,(
% 3.89/0.94    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <=> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))))))),
% 3.89/0.94    inference(negated_conjecture,[],[f9])).
% 3.89/0.94  
% 3.89/0.94  fof(f23,plain,(
% 3.89/0.94    ? [X0] : (? [X1] : (? [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <~> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0)))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 3.89/0.94    inference(ennf_transformation,[],[f10])).
% 3.89/0.94  
% 3.89/0.94  fof(f24,plain,(
% 3.89/0.94    ? [X0] : (? [X1] : (? [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <~> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0)))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 3.89/0.94    inference(flattening,[],[f23])).
% 3.89/0.94  
% 3.89/0.94  fof(f36,plain,(
% 3.89/0.94    ? [X0] : (? [X1] : (? [X2] : (((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0))) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 3.89/0.94    inference(nnf_transformation,[],[f24])).
% 3.89/0.94  
% 3.89/0.94  fof(f37,plain,(
% 3.89/0.94    ? [X0] : (? [X1] : (? [X2] : ((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 3.89/0.94    inference(flattening,[],[f36])).
% 3.89/0.94  
% 3.89/0.94  fof(f40,plain,(
% 3.89/0.94    ( ! [X0,X1] : (? [X2] : ((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) => ((~r1_tarski(k9_relat_1(X0,sK4),k1_relat_1(X1)) | ~r1_tarski(sK4,k1_relat_1(X0)) | ~r1_tarski(sK4,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,sK4),k1_relat_1(X1)) & r1_tarski(sK4,k1_relat_1(X0))) | r1_tarski(sK4,k1_relat_1(k5_relat_1(X0,X1)))))) )),
% 3.89/0.94    introduced(choice_axiom,[])).
% 3.89/0.94  
% 3.89/0.94  fof(f39,plain,(
% 3.89/0.94    ( ! [X0] : (? [X1] : (? [X2] : ((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) => (? [X2] : ((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(sK3)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,sK3)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(sK3)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,sK3))))) & v1_funct_1(sK3) & v1_relat_1(sK3))) )),
% 3.89/0.94    introduced(choice_axiom,[])).
% 3.89/0.94  
% 3.89/0.94  fof(f38,plain,(
% 3.89/0.94    ? [X0] : (? [X1] : (? [X2] : ((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (? [X2] : ((~r1_tarski(k9_relat_1(sK2,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(sK2)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(sK2,X1)))) & ((r1_tarski(k9_relat_1(sK2,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(sK2))) | r1_tarski(X2,k1_relat_1(k5_relat_1(sK2,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 3.89/0.94    introduced(choice_axiom,[])).
% 3.89/0.94  
% 3.89/0.94  fof(f41,plain,(
% 3.89/0.94    (((~r1_tarski(k9_relat_1(sK2,sK4),k1_relat_1(sK3)) | ~r1_tarski(sK4,k1_relat_1(sK2)) | ~r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3)))) & ((r1_tarski(k9_relat_1(sK2,sK4),k1_relat_1(sK3)) & r1_tarski(sK4,k1_relat_1(sK2))) | r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3))))) & v1_funct_1(sK3) & v1_relat_1(sK3)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 3.89/0.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f37,f40,f39,f38])).
% 3.89/0.94  
% 3.89/0.94  fof(f59,plain,(
% 3.89/0.94    v1_relat_1(sK2)),
% 3.89/0.94    inference(cnf_transformation,[],[f41])).
% 3.89/0.94  
% 3.89/0.94  fof(f61,plain,(
% 3.89/0.94    v1_relat_1(sK3)),
% 3.89/0.94    inference(cnf_transformation,[],[f41])).
% 3.89/0.94  
% 3.89/0.94  fof(f5,axiom,(
% 3.89/0.94    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 3.89/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.89/0.94  
% 3.89/0.94  fof(f16,plain,(
% 3.89/0.94    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.89/0.94    inference(ennf_transformation,[],[f5])).
% 3.89/0.94  
% 3.89/0.94  fof(f50,plain,(
% 3.89/0.94    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.89/0.94    inference(cnf_transformation,[],[f16])).
% 3.89/0.94  
% 3.89/0.94  fof(f1,axiom,(
% 3.89/0.94    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.89/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.89/0.94  
% 3.89/0.94  fof(f11,plain,(
% 3.89/0.94    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.89/0.94    inference(ennf_transformation,[],[f1])).
% 3.89/0.94  
% 3.89/0.94  fof(f25,plain,(
% 3.89/0.94    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.89/0.94    inference(nnf_transformation,[],[f11])).
% 3.89/0.94  
% 3.89/0.94  fof(f26,plain,(
% 3.89/0.94    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.89/0.94    inference(rectify,[],[f25])).
% 3.89/0.94  
% 3.89/0.94  fof(f27,plain,(
% 3.89/0.94    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.89/0.94    introduced(choice_axiom,[])).
% 3.89/0.94  
% 3.89/0.94  fof(f28,plain,(
% 3.89/0.94    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.89/0.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).
% 3.89/0.94  
% 3.89/0.94  fof(f43,plain,(
% 3.89/0.94    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.89/0.94    inference(cnf_transformation,[],[f28])).
% 3.89/0.94  
% 3.89/0.94  fof(f6,axiom,(
% 3.89/0.94    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))))),
% 3.89/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.89/0.94  
% 3.89/0.94  fof(f17,plain,(
% 3.89/0.94    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.89/0.94    inference(ennf_transformation,[],[f6])).
% 3.89/0.94  
% 3.89/0.94  fof(f18,plain,(
% 3.89/0.94    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.89/0.94    inference(flattening,[],[f17])).
% 3.89/0.94  
% 3.89/0.94  fof(f31,plain,(
% 3.89/0.94    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : (((~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0)))) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X3,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.89/0.94    inference(nnf_transformation,[],[f18])).
% 3.89/0.94  
% 3.89/0.94  fof(f32,plain,(
% 3.89/0.94    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0))) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X3,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.89/0.94    inference(flattening,[],[f31])).
% 3.89/0.94  
% 3.89/0.94  fof(f33,plain,(
% 3.89/0.94    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k1_funct_1(X0,X4),X1) | ~r2_hidden(X4,k1_relat_1(X0))) & ((r2_hidden(k1_funct_1(X0,X4),X1) & r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X4,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.89/0.94    inference(rectify,[],[f32])).
% 3.89/0.94  
% 3.89/0.94  fof(f34,plain,(
% 3.89/0.94    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X3,X2))) => ((~r2_hidden(k1_funct_1(X0,sK1(X0,X1,X2)),X1) | ~r2_hidden(sK1(X0,X1,X2),k1_relat_1(X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(k1_funct_1(X0,sK1(X0,X1,X2)),X1) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X0))) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 3.89/0.94    introduced(choice_axiom,[])).
% 3.89/0.94  
% 3.89/0.94  fof(f35,plain,(
% 3.89/0.94    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ((~r2_hidden(k1_funct_1(X0,sK1(X0,X1,X2)),X1) | ~r2_hidden(sK1(X0,X1,X2),k1_relat_1(X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(k1_funct_1(X0,sK1(X0,X1,X2)),X1) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X0))) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k1_funct_1(X0,X4),X1) | ~r2_hidden(X4,k1_relat_1(X0))) & ((r2_hidden(k1_funct_1(X0,X4),X1) & r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X4,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.89/0.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f33,f34])).
% 3.89/0.94  
% 3.89/0.94  fof(f51,plain,(
% 3.89/0.94    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X4,X2) | k10_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.89/0.94    inference(cnf_transformation,[],[f35])).
% 3.89/0.94  
% 3.89/0.94  fof(f70,plain,(
% 3.89/0.94    ( ! [X4,X0,X1] : (r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X4,k10_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.89/0.94    inference(equality_resolution,[],[f51])).
% 3.89/0.94  
% 3.89/0.94  fof(f44,plain,(
% 3.89/0.94    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 3.89/0.94    inference(cnf_transformation,[],[f28])).
% 3.89/0.94  
% 3.89/0.94  fof(f64,plain,(
% 3.89/0.94    r1_tarski(k9_relat_1(sK2,sK4),k1_relat_1(sK3)) | r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3)))),
% 3.89/0.94    inference(cnf_transformation,[],[f41])).
% 3.89/0.94  
% 3.89/0.94  fof(f8,axiom,(
% 3.89/0.94    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 3.89/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.89/0.94  
% 3.89/0.94  fof(f21,plain,(
% 3.89/0.94    ! [X0,X1,X2] : ((r1_tarski(X0,k10_relat_1(X2,X1)) | (~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.89/0.94    inference(ennf_transformation,[],[f8])).
% 3.89/0.94  
% 3.89/0.94  fof(f22,plain,(
% 3.89/0.94    ! [X0,X1,X2] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.89/0.94    inference(flattening,[],[f21])).
% 3.89/0.94  
% 3.89/0.94  fof(f58,plain,(
% 3.89/0.94    ( ! [X2,X0,X1] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.89/0.94    inference(cnf_transformation,[],[f22])).
% 3.89/0.94  
% 3.89/0.94  fof(f60,plain,(
% 3.89/0.94    v1_funct_1(sK2)),
% 3.89/0.94    inference(cnf_transformation,[],[f41])).
% 3.89/0.94  
% 3.89/0.94  fof(f63,plain,(
% 3.89/0.94    r1_tarski(sK4,k1_relat_1(sK2)) | r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3)))),
% 3.89/0.94    inference(cnf_transformation,[],[f41])).
% 3.89/0.94  
% 3.89/0.94  fof(f4,axiom,(
% 3.89/0.94    ! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)))))),
% 3.89/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.89/0.94  
% 3.89/0.94  fof(f14,plain,(
% 3.89/0.94    ! [X0,X1,X2] : (! [X3] : ((r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) | (~r1_tarski(X0,X1) | ~r1_tarski(X2,X3))) | ~v1_relat_1(X3)) | ~v1_relat_1(X2))),
% 3.89/0.94    inference(ennf_transformation,[],[f4])).
% 3.89/0.94  
% 3.89/0.94  fof(f15,plain,(
% 3.89/0.94    ! [X0,X1,X2] : (! [X3] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) | ~r1_tarski(X0,X1) | ~r1_tarski(X2,X3) | ~v1_relat_1(X3)) | ~v1_relat_1(X2))),
% 3.89/0.94    inference(flattening,[],[f14])).
% 3.89/0.94  
% 3.89/0.94  fof(f49,plain,(
% 3.89/0.94    ( ! [X2,X0,X3,X1] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) | ~r1_tarski(X0,X1) | ~r1_tarski(X2,X3) | ~v1_relat_1(X3) | ~v1_relat_1(X2)) )),
% 3.89/0.94    inference(cnf_transformation,[],[f15])).
% 3.89/0.94  
% 3.89/0.94  fof(f7,axiom,(
% 3.89/0.94    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 3.89/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.89/0.94  
% 3.89/0.94  fof(f19,plain,(
% 3.89/0.94    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.89/0.94    inference(ennf_transformation,[],[f7])).
% 3.89/0.94  
% 3.89/0.94  fof(f20,plain,(
% 3.89/0.94    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.89/0.94    inference(flattening,[],[f19])).
% 3.89/0.94  
% 3.89/0.94  fof(f57,plain,(
% 3.89/0.94    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.89/0.94    inference(cnf_transformation,[],[f20])).
% 3.89/0.94  
% 3.89/0.94  fof(f2,axiom,(
% 3.89/0.94    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.89/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.89/0.94  
% 3.89/0.94  fof(f29,plain,(
% 3.89/0.94    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.89/0.94    inference(nnf_transformation,[],[f2])).
% 3.89/0.94  
% 3.89/0.94  fof(f30,plain,(
% 3.89/0.94    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.89/0.94    inference(flattening,[],[f29])).
% 3.89/0.94  
% 3.89/0.94  fof(f45,plain,(
% 3.89/0.94    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.89/0.94    inference(cnf_transformation,[],[f30])).
% 3.89/0.94  
% 3.89/0.94  fof(f67,plain,(
% 3.89/0.94    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.89/0.94    inference(equality_resolution,[],[f45])).
% 3.89/0.94  
% 3.89/0.94  fof(f65,plain,(
% 3.89/0.94    ~r1_tarski(k9_relat_1(sK2,sK4),k1_relat_1(sK3)) | ~r1_tarski(sK4,k1_relat_1(sK2)) | ~r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3)))),
% 3.89/0.94    inference(cnf_transformation,[],[f41])).
% 3.89/0.94  
% 3.89/0.94  cnf(c_6,plain,
% 3.89/0.94      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 3.89/0.94      inference(cnf_transformation,[],[f48]) ).
% 3.89/0.94  
% 3.89/0.94  cnf(c_988,plain,
% 3.89/0.94      ( ~ r1_tarski(X0,X1)
% 3.89/0.94      | ~ r1_tarski(k9_relat_1(X2,X3),X0)
% 3.89/0.94      | r1_tarski(k9_relat_1(X2,X3),X1) ),
% 3.89/0.94      inference(instantiation,[status(thm)],[c_6]) ).
% 3.89/0.94  
% 3.89/0.94  cnf(c_1634,plain,
% 3.89/0.94      ( ~ r1_tarski(X0,X1)
% 3.89/0.94      | ~ r1_tarski(k9_relat_1(X2,sK4),X0)
% 3.89/0.94      | r1_tarski(k9_relat_1(X2,sK4),X1) ),
% 3.89/0.94      inference(instantiation,[status(thm)],[c_988]) ).
% 3.89/0.94  
% 3.89/0.94  cnf(c_8169,plain,
% 3.89/0.94      ( ~ r1_tarski(k9_relat_1(X0,k1_relat_1(k5_relat_1(sK2,sK3))),X1)
% 3.89/0.94      | r1_tarski(k9_relat_1(X2,sK4),X1)
% 3.89/0.94      | ~ r1_tarski(k9_relat_1(X2,sK4),k9_relat_1(X0,k1_relat_1(k5_relat_1(sK2,sK3)))) ),
% 3.89/0.94      inference(instantiation,[status(thm)],[c_1634]) ).
% 3.89/0.94  
% 3.89/0.94  cnf(c_11888,plain,
% 3.89/0.94      ( ~ r1_tarski(k9_relat_1(X0,k1_relat_1(k5_relat_1(sK2,sK3))),k1_relat_1(sK3))
% 3.89/0.94      | ~ r1_tarski(k9_relat_1(sK2,sK4),k9_relat_1(X0,k1_relat_1(k5_relat_1(sK2,sK3))))
% 3.89/0.94      | r1_tarski(k9_relat_1(sK2,sK4),k1_relat_1(sK3)) ),
% 3.89/0.94      inference(instantiation,[status(thm)],[c_8169]) ).
% 3.89/0.94  
% 3.89/0.94  cnf(c_11890,plain,
% 3.89/0.94      ( ~ r1_tarski(k9_relat_1(sK2,k1_relat_1(k5_relat_1(sK2,sK3))),k1_relat_1(sK3))
% 3.89/0.94      | ~ r1_tarski(k9_relat_1(sK2,sK4),k9_relat_1(sK2,k1_relat_1(k5_relat_1(sK2,sK3))))
% 3.89/0.94      | r1_tarski(k9_relat_1(sK2,sK4),k1_relat_1(sK3)) ),
% 3.89/0.94      inference(instantiation,[status(thm)],[c_11888]) ).
% 3.89/0.94  
% 3.89/0.94  cnf(c_23,negated_conjecture,
% 3.89/0.94      ( v1_relat_1(sK2) ),
% 3.89/0.94      inference(cnf_transformation,[],[f59]) ).
% 3.89/0.94  
% 3.89/0.94  cnf(c_691,plain,
% 3.89/0.94      ( v1_relat_1(sK2) = iProver_top ),
% 3.89/0.94      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.89/0.94  
% 3.89/0.94  cnf(c_21,negated_conjecture,
% 3.89/0.94      ( v1_relat_1(sK3) ),
% 3.89/0.94      inference(cnf_transformation,[],[f61]) ).
% 3.89/0.94  
% 3.89/0.94  cnf(c_693,plain,
% 3.89/0.94      ( v1_relat_1(sK3) = iProver_top ),
% 3.89/0.94      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.89/0.94  
% 3.89/0.94  cnf(c_8,plain,
% 3.89/0.94      ( ~ v1_relat_1(X0)
% 3.89/0.94      | ~ v1_relat_1(X1)
% 3.89/0.94      | k10_relat_1(X1,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(X1,X0)) ),
% 3.89/0.94      inference(cnf_transformation,[],[f50]) ).
% 3.89/0.94  
% 3.89/0.94  cnf(c_706,plain,
% 3.89/0.94      ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
% 3.89/0.94      | v1_relat_1(X0) != iProver_top
% 3.89/0.94      | v1_relat_1(X1) != iProver_top ),
% 3.89/0.94      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.89/0.94  
% 3.89/0.94  cnf(c_1515,plain,
% 3.89/0.94      ( k10_relat_1(X0,k1_relat_1(sK3)) = k1_relat_1(k5_relat_1(X0,sK3))
% 3.89/0.94      | v1_relat_1(X0) != iProver_top ),
% 3.89/0.94      inference(superposition,[status(thm)],[c_693,c_706]) ).
% 3.89/0.94  
% 3.89/0.94  cnf(c_2464,plain,
% 3.89/0.94      ( k10_relat_1(sK2,k1_relat_1(sK3)) = k1_relat_1(k5_relat_1(sK2,sK3)) ),
% 3.89/0.94      inference(superposition,[status(thm)],[c_691,c_1515]) ).
% 3.89/0.94  
% 3.89/0.94  cnf(c_1,plain,
% 3.89/0.94      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.89/0.94      inference(cnf_transformation,[],[f43]) ).
% 3.89/0.94  
% 3.89/0.94  cnf(c_712,plain,
% 3.89/0.94      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 3.89/0.94      | r1_tarski(X0,X1) = iProver_top ),
% 3.89/0.94      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.89/0.94  
% 3.89/0.94  cnf(c_14,plain,
% 3.89/0.94      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 3.89/0.94      | r2_hidden(X0,k1_relat_1(X1))
% 3.89/0.94      | ~ v1_funct_1(X1)
% 3.89/0.94      | ~ v1_relat_1(X1) ),
% 3.89/0.94      inference(cnf_transformation,[],[f70]) ).
% 3.89/0.94  
% 3.89/0.94  cnf(c_700,plain,
% 3.89/0.94      ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
% 3.89/0.94      | r2_hidden(X0,k1_relat_1(X1)) = iProver_top
% 3.89/0.94      | v1_funct_1(X1) != iProver_top
% 3.89/0.94      | v1_relat_1(X1) != iProver_top ),
% 3.89/0.94      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.89/0.94  
% 3.89/0.94  cnf(c_1679,plain,
% 3.89/0.94      ( r2_hidden(sK0(k10_relat_1(X0,X1),X2),k1_relat_1(X0)) = iProver_top
% 3.89/0.94      | r1_tarski(k10_relat_1(X0,X1),X2) = iProver_top
% 3.89/0.94      | v1_funct_1(X0) != iProver_top
% 3.89/0.94      | v1_relat_1(X0) != iProver_top ),
% 3.89/0.94      inference(superposition,[status(thm)],[c_712,c_700]) ).
% 3.89/0.94  
% 3.89/0.94  cnf(c_0,plain,
% 3.89/0.94      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 3.89/0.94      inference(cnf_transformation,[],[f44]) ).
% 3.89/0.94  
% 3.89/0.94  cnf(c_713,plain,
% 3.89/0.94      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 3.89/0.94      | r1_tarski(X0,X1) = iProver_top ),
% 3.89/0.94      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.89/0.94  
% 3.89/0.94  cnf(c_8636,plain,
% 3.89/0.94      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) = iProver_top
% 3.89/0.94      | v1_funct_1(X0) != iProver_top
% 3.89/0.94      | v1_relat_1(X0) != iProver_top ),
% 3.89/0.94      inference(superposition,[status(thm)],[c_1679,c_713]) ).
% 3.89/0.94  
% 3.89/0.94  cnf(c_8903,plain,
% 3.89/0.94      ( r1_tarski(k1_relat_1(k5_relat_1(sK2,sK3)),k1_relat_1(sK2)) = iProver_top
% 3.89/0.94      | v1_funct_1(sK2) != iProver_top
% 3.89/0.94      | v1_relat_1(sK2) != iProver_top ),
% 3.89/0.94      inference(superposition,[status(thm)],[c_2464,c_8636]) ).
% 3.89/0.94  
% 3.89/0.94  cnf(c_8950,plain,
% 3.89/0.94      ( r1_tarski(k1_relat_1(k5_relat_1(sK2,sK3)),k1_relat_1(sK2))
% 3.89/0.94      | ~ v1_funct_1(sK2)
% 3.89/0.94      | ~ v1_relat_1(sK2) ),
% 3.89/0.94      inference(predicate_to_equality_rev,[status(thm)],[c_8903]) ).
% 3.89/0.94  
% 3.89/0.94  cnf(c_18,negated_conjecture,
% 3.89/0.94      ( r1_tarski(k9_relat_1(sK2,sK4),k1_relat_1(sK3))
% 3.89/0.94      | r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3))) ),
% 3.89/0.94      inference(cnf_transformation,[],[f64]) ).
% 3.89/0.94  
% 3.89/0.94  cnf(c_696,plain,
% 3.89/0.94      ( r1_tarski(k9_relat_1(sK2,sK4),k1_relat_1(sK3)) = iProver_top
% 3.89/0.94      | r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3))) = iProver_top ),
% 3.89/0.94      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.89/0.94  
% 3.89/0.94  cnf(c_16,plain,
% 3.89/0.94      ( r1_tarski(X0,k10_relat_1(X1,X2))
% 3.89/0.94      | ~ r1_tarski(X0,k1_relat_1(X1))
% 3.89/0.94      | ~ r1_tarski(k9_relat_1(X1,X0),X2)
% 3.89/0.94      | ~ v1_funct_1(X1)
% 3.89/0.94      | ~ v1_relat_1(X1) ),
% 3.89/0.94      inference(cnf_transformation,[],[f58]) ).
% 3.89/0.94  
% 3.89/0.94  cnf(c_698,plain,
% 3.89/0.94      ( r1_tarski(X0,k10_relat_1(X1,X2)) = iProver_top
% 3.89/0.94      | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
% 3.89/0.94      | r1_tarski(k9_relat_1(X1,X0),X2) != iProver_top
% 3.89/0.94      | v1_funct_1(X1) != iProver_top
% 3.89/0.94      | v1_relat_1(X1) != iProver_top ),
% 3.89/0.94      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.89/0.94  
% 3.89/0.94  cnf(c_1537,plain,
% 3.89/0.94      ( r1_tarski(sK4,k10_relat_1(sK2,k1_relat_1(sK3))) = iProver_top
% 3.89/0.94      | r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3))) = iProver_top
% 3.89/0.94      | r1_tarski(sK4,k1_relat_1(sK2)) != iProver_top
% 3.89/0.94      | v1_funct_1(sK2) != iProver_top
% 3.89/0.94      | v1_relat_1(sK2) != iProver_top ),
% 3.89/0.94      inference(superposition,[status(thm)],[c_696,c_698]) ).
% 3.89/0.94  
% 3.89/0.94  cnf(c_5384,plain,
% 3.89/0.94      ( r1_tarski(sK4,k10_relat_1(sK2,k1_relat_1(sK3)))
% 3.89/0.94      | r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3)))
% 3.89/0.94      | ~ r1_tarski(sK4,k1_relat_1(sK2))
% 3.89/0.94      | ~ v1_funct_1(sK2)
% 3.89/0.94      | ~ v1_relat_1(sK2) ),
% 3.89/0.94      inference(resolution,[status(thm)],[c_16,c_18]) ).
% 3.89/0.94  
% 3.89/0.94  cnf(c_22,negated_conjecture,
% 3.89/0.94      ( v1_funct_1(sK2) ),
% 3.89/0.94      inference(cnf_transformation,[],[f60]) ).
% 3.89/0.94  
% 3.89/0.94  cnf(c_19,negated_conjecture,
% 3.89/0.94      ( r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3)))
% 3.89/0.94      | r1_tarski(sK4,k1_relat_1(sK2)) ),
% 3.89/0.94      inference(cnf_transformation,[],[f63]) ).
% 3.89/0.94  
% 3.89/0.94  cnf(c_1563,plain,
% 3.89/0.94      ( r1_tarski(sK4,k10_relat_1(sK2,k1_relat_1(sK3)))
% 3.89/0.94      | r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3)))
% 3.89/0.94      | ~ r1_tarski(sK4,k1_relat_1(sK2))
% 3.89/0.94      | ~ v1_funct_1(sK2)
% 3.89/0.94      | ~ v1_relat_1(sK2) ),
% 3.89/0.94      inference(predicate_to_equality_rev,[status(thm)],[c_1537]) ).
% 3.89/0.94  
% 3.89/0.94  cnf(c_5778,plain,
% 3.89/0.94      ( r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3)))
% 3.89/0.94      | r1_tarski(sK4,k10_relat_1(sK2,k1_relat_1(sK3))) ),
% 3.89/0.94      inference(global_propositional_subsumption,
% 3.89/0.94                [status(thm)],
% 3.89/0.94                [c_5384,c_23,c_22,c_19,c_1563]) ).
% 3.89/0.94  
% 3.89/0.94  cnf(c_5779,plain,
% 3.89/0.94      ( r1_tarski(sK4,k10_relat_1(sK2,k1_relat_1(sK3)))
% 3.89/0.94      | r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3))) ),
% 3.89/0.94      inference(renaming,[status(thm)],[c_5778]) ).
% 3.89/0.94  
% 3.89/0.94  cnf(c_5780,plain,
% 3.89/0.94      ( r1_tarski(sK4,k10_relat_1(sK2,k1_relat_1(sK3))) = iProver_top
% 3.89/0.94      | r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3))) = iProver_top ),
% 3.89/0.94      inference(predicate_to_equality,[status(thm)],[c_5779]) ).
% 3.89/0.94  
% 3.89/0.94  cnf(c_8000,plain,
% 3.89/0.94      ( r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3))) = iProver_top
% 3.89/0.94      | r1_tarski(sK4,k10_relat_1(sK2,k1_relat_1(sK3))) = iProver_top ),
% 3.89/0.94      inference(global_propositional_subsumption,
% 3.89/0.94                [status(thm)],
% 3.89/0.94                [c_1537,c_5780]) ).
% 3.89/0.94  
% 3.89/0.94  cnf(c_8001,plain,
% 3.89/0.94      ( r1_tarski(sK4,k10_relat_1(sK2,k1_relat_1(sK3))) = iProver_top
% 3.89/0.94      | r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3))) = iProver_top ),
% 3.89/0.94      inference(renaming,[status(thm)],[c_8000]) ).
% 3.89/0.94  
% 3.89/0.94  cnf(c_8004,plain,
% 3.89/0.94      ( r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3))) = iProver_top ),
% 3.89/0.94      inference(light_normalisation,[status(thm)],[c_8001,c_2464]) ).
% 3.89/0.94  
% 3.89/0.94  cnf(c_8006,plain,
% 3.89/0.94      ( r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3))) ),
% 3.89/0.94      inference(predicate_to_equality_rev,[status(thm)],[c_8004]) ).
% 3.89/0.94  
% 3.89/0.94  cnf(c_7,plain,
% 3.89/0.94      ( ~ r1_tarski(X0,X1)
% 3.89/0.94      | ~ r1_tarski(X2,X3)
% 3.89/0.94      | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1))
% 3.89/0.94      | ~ v1_relat_1(X3)
% 3.89/0.94      | ~ v1_relat_1(X2) ),
% 3.89/0.94      inference(cnf_transformation,[],[f49]) ).
% 3.89/0.94  
% 3.89/0.94  cnf(c_1665,plain,
% 3.89/0.94      ( ~ r1_tarski(X0,X1)
% 3.89/0.94      | r1_tarski(k9_relat_1(X0,sK4),k9_relat_1(X1,X2))
% 3.89/0.94      | ~ r1_tarski(sK4,X2)
% 3.89/0.94      | ~ v1_relat_1(X1)
% 3.89/0.94      | ~ v1_relat_1(X0) ),
% 3.89/0.94      inference(instantiation,[status(thm)],[c_7]) ).
% 3.89/0.94  
% 3.89/0.94  cnf(c_3447,plain,
% 3.89/0.94      ( ~ r1_tarski(X0,X1)
% 3.89/0.94      | r1_tarski(k9_relat_1(X0,sK4),k9_relat_1(X1,k1_relat_1(k5_relat_1(sK2,sK3))))
% 3.89/0.94      | ~ r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3)))
% 3.89/0.94      | ~ v1_relat_1(X1)
% 3.89/0.94      | ~ v1_relat_1(X0) ),
% 3.89/0.94      inference(instantiation,[status(thm)],[c_1665]) ).
% 3.89/0.94  
% 3.89/0.94  cnf(c_3449,plain,
% 3.89/0.94      ( r1_tarski(k9_relat_1(sK2,sK4),k9_relat_1(sK2,k1_relat_1(k5_relat_1(sK2,sK3))))
% 3.89/0.94      | ~ r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3)))
% 3.89/0.94      | ~ r1_tarski(sK2,sK2)
% 3.89/0.94      | ~ v1_relat_1(sK2) ),
% 3.89/0.94      inference(instantiation,[status(thm)],[c_3447]) ).
% 3.89/0.94  
% 3.89/0.94  cnf(c_15,plain,
% 3.89/0.94      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
% 3.89/0.94      | ~ v1_funct_1(X0)
% 3.89/0.94      | ~ v1_relat_1(X0) ),
% 3.89/0.94      inference(cnf_transformation,[],[f57]) ).
% 3.89/0.94  
% 3.89/0.94  cnf(c_699,plain,
% 3.89/0.94      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1) = iProver_top
% 3.89/0.94      | v1_funct_1(X0) != iProver_top
% 3.89/0.94      | v1_relat_1(X0) != iProver_top ),
% 3.89/0.94      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.89/0.94  
% 3.89/0.94  cnf(c_2733,plain,
% 3.89/0.94      ( r1_tarski(k9_relat_1(sK2,k1_relat_1(k5_relat_1(sK2,sK3))),k1_relat_1(sK3)) = iProver_top
% 3.89/0.94      | v1_funct_1(sK2) != iProver_top
% 3.89/0.94      | v1_relat_1(sK2) != iProver_top ),
% 3.89/0.94      inference(superposition,[status(thm)],[c_2464,c_699]) ).
% 3.89/0.94  
% 3.89/0.94  cnf(c_2758,plain,
% 3.89/0.94      ( r1_tarski(k9_relat_1(sK2,k1_relat_1(k5_relat_1(sK2,sK3))),k1_relat_1(sK3))
% 3.89/0.94      | ~ v1_funct_1(sK2)
% 3.89/0.94      | ~ v1_relat_1(sK2) ),
% 3.89/0.94      inference(predicate_to_equality_rev,[status(thm)],[c_2733]) ).
% 3.89/0.94  
% 3.89/0.94  cnf(c_939,plain,
% 3.89/0.94      ( ~ r1_tarski(X0,k1_relat_1(sK2))
% 3.89/0.94      | ~ r1_tarski(sK4,X0)
% 3.89/0.94      | r1_tarski(sK4,k1_relat_1(sK2)) ),
% 3.89/0.94      inference(instantiation,[status(thm)],[c_6]) ).
% 3.89/0.94  
% 3.89/0.94  cnf(c_1230,plain,
% 3.89/0.94      ( ~ r1_tarski(k1_relat_1(k5_relat_1(sK2,sK3)),k1_relat_1(sK2))
% 3.89/0.94      | ~ r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3)))
% 3.89/0.94      | r1_tarski(sK4,k1_relat_1(sK2)) ),
% 3.89/0.94      inference(instantiation,[status(thm)],[c_939]) ).
% 3.89/0.94  
% 3.89/0.94  cnf(c_5,plain,
% 3.89/0.94      ( r1_tarski(X0,X0) ),
% 3.89/0.94      inference(cnf_transformation,[],[f67]) ).
% 3.89/0.94  
% 3.89/0.94  cnf(c_63,plain,
% 3.89/0.94      ( r1_tarski(sK2,sK2) ),
% 3.89/0.94      inference(instantiation,[status(thm)],[c_5]) ).
% 3.89/0.94  
% 3.89/0.94  cnf(c_17,negated_conjecture,
% 3.89/0.94      ( ~ r1_tarski(k9_relat_1(sK2,sK4),k1_relat_1(sK3))
% 3.89/0.94      | ~ r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3)))
% 3.89/0.94      | ~ r1_tarski(sK4,k1_relat_1(sK2)) ),
% 3.89/0.94      inference(cnf_transformation,[],[f65]) ).
% 3.89/0.94  
% 3.89/0.94  cnf(contradiction,plain,
% 3.89/0.94      ( $false ),
% 3.89/0.94      inference(minisat,
% 3.89/0.94                [status(thm)],
% 3.89/0.94                [c_11890,c_8950,c_8006,c_3449,c_2758,c_1230,c_63,c_17,
% 3.89/0.95                 c_22,c_23]) ).
% 3.89/0.95  
% 3.89/0.95  
% 3.89/0.95  % SZS output end CNFRefutation for theBenchmark.p
% 3.89/0.95  
% 3.89/0.95  ------                               Statistics
% 3.89/0.95  
% 3.89/0.95  ------ Selected
% 3.89/0.95  
% 3.89/0.95  total_time:                             0.314
% 3.89/0.95  
%------------------------------------------------------------------------------
