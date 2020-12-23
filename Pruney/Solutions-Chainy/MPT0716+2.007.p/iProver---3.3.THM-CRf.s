%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:52:53 EST 2020

% Result     : Theorem 43.46s
% Output     : CNFRefutation 43.46s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 596 expanded)
%              Number of clauses        :   75 ( 147 expanded)
%              Number of leaves         :   16 ( 152 expanded)
%              Depth                    :   22
%              Number of atoms          :  513 (4083 expanded)
%              Number of equality atoms :   82 ( 189 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

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

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

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

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

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
    inference(nnf_transformation,[],[f18])).

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
    inference(flattening,[],[f29])).

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
    inference(rectify,[],[f30])).

fof(f32,plain,(
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

fof(f33,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f32])).

fof(f48,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X4),X1)
      | ~ r2_hidden(X4,X2)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f63,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X4),X1)
      | ~ r2_hidden(X4,k10_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f48])).

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

fof(f34,plain,(
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
    inference(flattening,[],[f34])).

fof(f38,plain,(
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

fof(f37,plain,(
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

fof(f36,plain,
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

fof(f39,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f35,f38,f37,f36])).

fof(f60,plain,
    ( r1_tarski(k9_relat_1(sK2,sK4),k1_relat_1(sK3))
    | r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f39])).

fof(f55,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f57,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f39])).

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

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f56,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f59,plain,
    ( r1_tarski(sK4,k1_relat_1(sK2))
    | r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f39])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f47,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X4,X2)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f64,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X4,k10_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f47])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f61,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,sK4),k1_relat_1(sK3))
    | ~ r1_tarski(sK4,k1_relat_1(sK2))
    | ~ r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_146024,plain,
    ( r2_hidden(sK0(k9_relat_1(sK2,sK4),k1_relat_1(sK3)),X0)
    | ~ r2_hidden(sK0(k9_relat_1(sK2,sK4),k1_relat_1(sK3)),k9_relat_1(sK2,sK4))
    | ~ r1_tarski(k9_relat_1(sK2,sK4),X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_156588,plain,
    ( r2_hidden(sK0(k9_relat_1(sK2,sK4),k1_relat_1(sK3)),k9_relat_1(X0,k10_relat_1(X0,k1_relat_1(sK3))))
    | ~ r2_hidden(sK0(k9_relat_1(sK2,sK4),k1_relat_1(sK3)),k9_relat_1(sK2,sK4))
    | ~ r1_tarski(k9_relat_1(sK2,sK4),k9_relat_1(X0,k10_relat_1(X0,k1_relat_1(sK3)))) ),
    inference(instantiation,[status(thm)],[c_146024])).

cnf(c_156590,plain,
    ( r2_hidden(sK0(k9_relat_1(sK2,sK4),k1_relat_1(sK3)),k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(sK3))))
    | ~ r2_hidden(sK0(k9_relat_1(sK2,sK4),k1_relat_1(sK3)),k9_relat_1(sK2,sK4))
    | ~ r1_tarski(k9_relat_1(sK2,sK4),k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(sK3)))) ),
    inference(instantiation,[status(thm)],[c_156588])).

cnf(c_146233,plain,
    ( ~ r2_hidden(sK0(k9_relat_1(sK2,sK4),k1_relat_1(sK3)),X0)
    | r2_hidden(sK0(k9_relat_1(sK2,sK4),k1_relat_1(sK3)),X1)
    | ~ r1_tarski(X0,X1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_146582,plain,
    ( ~ r2_hidden(sK0(k9_relat_1(sK2,sK4),k1_relat_1(sK3)),X0)
    | r2_hidden(sK0(k9_relat_1(sK2,sK4),k1_relat_1(sK3)),k1_relat_1(sK3))
    | ~ r1_tarski(X0,k1_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_146233])).

cnf(c_152961,plain,
    ( ~ r2_hidden(sK0(k9_relat_1(sK2,sK4),k1_relat_1(sK3)),k9_relat_1(X0,k10_relat_1(X0,k1_relat_1(sK3))))
    | r2_hidden(sK0(k9_relat_1(sK2,sK4),k1_relat_1(sK3)),k1_relat_1(sK3))
    | ~ r1_tarski(k9_relat_1(X0,k10_relat_1(X0,k1_relat_1(sK3))),k1_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_146582])).

cnf(c_152969,plain,
    ( ~ r2_hidden(sK0(k9_relat_1(sK2,sK4),k1_relat_1(sK3)),k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(sK3))))
    | r2_hidden(sK0(k9_relat_1(sK2,sK4),k1_relat_1(sK3)),k1_relat_1(sK3))
    | ~ r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(sK3))),k1_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_152961])).

cnf(c_13,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_971,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,k1_relat_1(X1))),k1_relat_1(X1))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_129573,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,k1_relat_1(sK3))),k1_relat_1(sK3))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_971])).

cnf(c_129579,plain,
    ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(sK3))),k1_relat_1(sK3))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_129573])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1593,plain,
    ( r1_tarski(k9_relat_1(sK2,sK4),k9_relat_1(sK2,X0))
    | ~ r1_tarski(sK4,X0)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_8936,plain,
    ( r1_tarski(k9_relat_1(sK2,sK4),k9_relat_1(sK2,k10_relat_1(X0,X1)))
    | ~ r1_tarski(sK4,k10_relat_1(X0,X1))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1593])).

cnf(c_70750,plain,
    ( r1_tarski(k9_relat_1(sK2,sK4),k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(sK3))))
    | ~ r1_tarski(sK4,k10_relat_1(sK2,k1_relat_1(sK3)))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_8936])).

cnf(c_203,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X1,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_3559,plain,
    ( r1_tarski(X0,k10_relat_1(X1,k1_relat_1(X2)))
    | ~ r1_tarski(X3,k1_relat_1(k5_relat_1(X1,X2)))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | X0 != X3 ),
    inference(resolution,[status(thm)],[c_203,c_6])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(k1_funct_1(X1,X0),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_16,negated_conjecture,
    ( r1_tarski(k9_relat_1(sK2,sK4),k1_relat_1(sK3))
    | r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1229,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK2,sK4))
    | r2_hidden(X0,k1_relat_1(sK3))
    | r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3))) ),
    inference(resolution,[status(thm)],[c_2,c_16])).

cnf(c_2259,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,k9_relat_1(sK2,sK4)))
    | r2_hidden(k1_funct_1(X1,X0),k1_relat_1(sK3))
    | r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3)))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(resolution,[status(thm)],[c_11,c_1229])).

cnf(c_2279,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,k10_relat_1(X2,k9_relat_1(sK2,sK4))))
    | r2_hidden(k1_funct_1(X2,k1_funct_1(X1,X0)),k1_relat_1(sK3))
    | r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3)))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(resolution,[status(thm)],[c_2259,c_11])).

cnf(c_21,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_569,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_19,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_571,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_584,plain,
    ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2097,plain,
    ( k10_relat_1(X0,k1_relat_1(sK3)) = k1_relat_1(k5_relat_1(X0,sK3))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_571,c_584])).

cnf(c_2240,plain,
    ( k10_relat_1(sK2,k1_relat_1(sK3)) = k1_relat_1(k5_relat_1(sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_569,c_2097])).

cnf(c_574,plain,
    ( r1_tarski(k9_relat_1(sK2,sK4),k1_relat_1(sK3)) = iProver_top
    | r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_14,plain,
    ( r1_tarski(X0,k10_relat_1(X1,X2))
    | ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ r1_tarski(k9_relat_1(X1,X0),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_576,plain,
    ( r1_tarski(X0,k10_relat_1(X1,X2)) = iProver_top
    | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
    | r1_tarski(k9_relat_1(X1,X0),X2) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_934,plain,
    ( r1_tarski(sK4,k10_relat_1(sK2,k1_relat_1(sK3))) = iProver_top
    | r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3))) = iProver_top
    | r1_tarski(sK4,k1_relat_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_574,c_576])).

cnf(c_22,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_20,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_23,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_17,negated_conjecture,
    ( r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3)))
    | r1_tarski(sK4,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_26,plain,
    ( r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3))) = iProver_top
    | r1_tarski(sK4,k1_relat_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1502,plain,
    ( r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3))) = iProver_top
    | r1_tarski(sK4,k10_relat_1(sK2,k1_relat_1(sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_934,c_22,c_23,c_26])).

cnf(c_1503,plain,
    ( r1_tarski(sK4,k10_relat_1(sK2,k1_relat_1(sK3))) = iProver_top
    | r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3))) = iProver_top ),
    inference(renaming,[status(thm)],[c_1502])).

cnf(c_2424,plain,
    ( r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2240,c_1503])).

cnf(c_2434,plain,
    ( r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2424])).

cnf(c_2456,plain,
    ( r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2279,c_2434])).

cnf(c_18660,plain,
    ( r1_tarski(X0,k10_relat_1(sK2,k1_relat_1(sK3)))
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | X0 != sK4 ),
    inference(resolution,[status(thm)],[c_3559,c_2456])).

cnf(c_19255,plain,
    ( r1_tarski(X0,k10_relat_1(sK2,k1_relat_1(sK3)))
    | X0 != sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_18660,c_21,c_19])).

cnf(c_19671,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k10_relat_1(sK2,k1_relat_1(sK3)))
    | X1 != sK4 ),
    inference(resolution,[status(thm)],[c_19255,c_2])).

cnf(c_201,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_19713,plain,
    ( r2_hidden(X0,k10_relat_1(sK2,k1_relat_1(sK3)))
    | ~ r2_hidden(X0,sK4) ),
    inference(resolution,[status(thm)],[c_19671,c_201])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_20179,plain,
    ( ~ r2_hidden(sK0(X0,k10_relat_1(sK2,k1_relat_1(sK3))),sK4)
    | r1_tarski(X0,k10_relat_1(sK2,k1_relat_1(sK3))) ),
    inference(resolution,[status(thm)],[c_19713,c_0])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_24169,plain,
    ( r1_tarski(sK4,k10_relat_1(sK2,k1_relat_1(sK3))) ),
    inference(resolution,[status(thm)],[c_20179,c_1])).

cnf(c_589,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_578,plain,
    ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
    | r2_hidden(X0,k1_relat_1(X1)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2436,plain,
    ( r2_hidden(X0,k1_relat_1(k5_relat_1(sK2,sK3))) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2240,c_578])).

cnf(c_4528,plain,
    ( r2_hidden(X0,k1_relat_1(k5_relat_1(sK2,sK3))) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2436,c_22,c_23])).

cnf(c_4536,plain,
    ( r2_hidden(sK0(k1_relat_1(k5_relat_1(sK2,sK3)),X0),k1_relat_1(sK2)) = iProver_top
    | r1_tarski(k1_relat_1(k5_relat_1(sK2,sK3)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_589,c_4528])).

cnf(c_590,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_7718,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(sK2,sK3)),k1_relat_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4536,c_590])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_586,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2930,plain,
    ( k2_xboole_0(sK4,k1_relat_1(k5_relat_1(sK2,sK3))) = k1_relat_1(k5_relat_1(sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_2424,c_586])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_587,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_6388,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(sK2,sK3)),X0) != iProver_top
    | r1_tarski(sK4,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2930,c_587])).

cnf(c_14155,plain,
    ( r1_tarski(sK4,k1_relat_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7718,c_6388])).

cnf(c_14163,plain,
    ( r1_tarski(sK4,k1_relat_1(sK2)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_14155])).

cnf(c_8022,plain,
    ( ~ r2_hidden(sK0(k9_relat_1(sK2,sK4),k1_relat_1(sK3)),k1_relat_1(sK3))
    | r1_tarski(k9_relat_1(sK2,sK4),k1_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_847,plain,
    ( r2_hidden(sK0(k9_relat_1(X0,X1),X2),k9_relat_1(X0,X1))
    | r1_tarski(k9_relat_1(X0,X1),X2) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_922,plain,
    ( r2_hidden(sK0(k9_relat_1(sK2,sK4),k1_relat_1(sK3)),k9_relat_1(sK2,sK4))
    | r1_tarski(k9_relat_1(sK2,sK4),k1_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_847])).

cnf(c_15,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(sK2,sK4),k1_relat_1(sK3))
    | ~ r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3)))
    | ~ r1_tarski(sK4,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f61])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_156590,c_152969,c_129579,c_70750,c_24169,c_14163,c_8022,c_2434,c_922,c_15,c_20,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:54:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 43.46/6.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 43.46/6.01  
% 43.46/6.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 43.46/6.01  
% 43.46/6.01  ------  iProver source info
% 43.46/6.01  
% 43.46/6.01  git: date: 2020-06-30 10:37:57 +0100
% 43.46/6.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 43.46/6.01  git: non_committed_changes: false
% 43.46/6.01  git: last_make_outside_of_git: false
% 43.46/6.01  
% 43.46/6.01  ------ 
% 43.46/6.01  ------ Parsing...
% 43.46/6.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 43.46/6.01  
% 43.46/6.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 43.46/6.01  
% 43.46/6.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 43.46/6.01  
% 43.46/6.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 43.46/6.01  ------ Proving...
% 43.46/6.01  ------ Problem Properties 
% 43.46/6.01  
% 43.46/6.01  
% 43.46/6.01  clauses                                 22
% 43.46/6.01  conjectures                             7
% 43.46/6.01  EPR                                     5
% 43.46/6.01  Horn                                    17
% 43.46/6.01  unary                                   4
% 43.46/6.01  binary                                  6
% 43.46/6.01  lits                                    65
% 43.46/6.01  lits eq                                 5
% 43.46/6.01  fd_pure                                 0
% 43.46/6.01  fd_pseudo                               0
% 43.46/6.01  fd_cond                                 0
% 43.46/6.01  fd_pseudo_cond                          3
% 43.46/6.01  AC symbols                              0
% 43.46/6.01  
% 43.46/6.01  ------ Input Options Time Limit: Unbounded
% 43.46/6.01  
% 43.46/6.01  
% 43.46/6.01  ------ 
% 43.46/6.01  Current options:
% 43.46/6.01  ------ 
% 43.46/6.01  
% 43.46/6.01  
% 43.46/6.01  
% 43.46/6.01  
% 43.46/6.01  ------ Proving...
% 43.46/6.01  
% 43.46/6.01  
% 43.46/6.01  % SZS status Theorem for theBenchmark.p
% 43.46/6.01  
% 43.46/6.01  % SZS output start CNFRefutation for theBenchmark.p
% 43.46/6.01  
% 43.46/6.01  fof(f1,axiom,(
% 43.46/6.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 43.46/6.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.46/6.01  
% 43.46/6.01  fof(f11,plain,(
% 43.46/6.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 43.46/6.01    inference(ennf_transformation,[],[f1])).
% 43.46/6.01  
% 43.46/6.01  fof(f25,plain,(
% 43.46/6.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 43.46/6.01    inference(nnf_transformation,[],[f11])).
% 43.46/6.01  
% 43.46/6.01  fof(f26,plain,(
% 43.46/6.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 43.46/6.01    inference(rectify,[],[f25])).
% 43.46/6.01  
% 43.46/6.01  fof(f27,plain,(
% 43.46/6.01    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 43.46/6.01    introduced(choice_axiom,[])).
% 43.46/6.01  
% 43.46/6.01  fof(f28,plain,(
% 43.46/6.01    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 43.46/6.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).
% 43.46/6.01  
% 43.46/6.01  fof(f40,plain,(
% 43.46/6.01    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 43.46/6.01    inference(cnf_transformation,[],[f28])).
% 43.46/6.01  
% 43.46/6.01  fof(f7,axiom,(
% 43.46/6.01    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 43.46/6.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.46/6.01  
% 43.46/6.01  fof(f19,plain,(
% 43.46/6.01    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 43.46/6.01    inference(ennf_transformation,[],[f7])).
% 43.46/6.01  
% 43.46/6.01  fof(f20,plain,(
% 43.46/6.01    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 43.46/6.01    inference(flattening,[],[f19])).
% 43.46/6.01  
% 43.46/6.01  fof(f53,plain,(
% 43.46/6.01    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 43.46/6.01    inference(cnf_transformation,[],[f20])).
% 43.46/6.01  
% 43.46/6.01  fof(f4,axiom,(
% 43.46/6.01    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 43.46/6.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.46/6.01  
% 43.46/6.01  fof(f14,plain,(
% 43.46/6.01    ! [X0,X1,X2] : ((r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 43.46/6.01    inference(ennf_transformation,[],[f4])).
% 43.46/6.01  
% 43.46/6.01  fof(f15,plain,(
% 43.46/6.01    ! [X0,X1,X2] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 43.46/6.01    inference(flattening,[],[f14])).
% 43.46/6.01  
% 43.46/6.01  fof(f45,plain,(
% 43.46/6.01    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 43.46/6.01    inference(cnf_transformation,[],[f15])).
% 43.46/6.01  
% 43.46/6.01  fof(f5,axiom,(
% 43.46/6.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 43.46/6.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.46/6.01  
% 43.46/6.01  fof(f16,plain,(
% 43.46/6.01    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 43.46/6.01    inference(ennf_transformation,[],[f5])).
% 43.46/6.01  
% 43.46/6.01  fof(f46,plain,(
% 43.46/6.01    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 43.46/6.01    inference(cnf_transformation,[],[f16])).
% 43.46/6.01  
% 43.46/6.01  fof(f6,axiom,(
% 43.46/6.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))))),
% 43.46/6.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.46/6.01  
% 43.46/6.01  fof(f17,plain,(
% 43.46/6.01    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 43.46/6.01    inference(ennf_transformation,[],[f6])).
% 43.46/6.01  
% 43.46/6.01  fof(f18,plain,(
% 43.46/6.01    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 43.46/6.01    inference(flattening,[],[f17])).
% 43.46/6.01  
% 43.46/6.01  fof(f29,plain,(
% 43.46/6.01    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : (((~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0)))) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X3,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 43.46/6.01    inference(nnf_transformation,[],[f18])).
% 43.46/6.01  
% 43.46/6.01  fof(f30,plain,(
% 43.46/6.01    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0))) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X3,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 43.46/6.01    inference(flattening,[],[f29])).
% 43.46/6.01  
% 43.46/6.01  fof(f31,plain,(
% 43.46/6.01    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k1_funct_1(X0,X4),X1) | ~r2_hidden(X4,k1_relat_1(X0))) & ((r2_hidden(k1_funct_1(X0,X4),X1) & r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X4,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 43.46/6.01    inference(rectify,[],[f30])).
% 43.46/6.01  
% 43.46/6.01  fof(f32,plain,(
% 43.46/6.01    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X3,X2))) => ((~r2_hidden(k1_funct_1(X0,sK1(X0,X1,X2)),X1) | ~r2_hidden(sK1(X0,X1,X2),k1_relat_1(X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(k1_funct_1(X0,sK1(X0,X1,X2)),X1) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X0))) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 43.46/6.01    introduced(choice_axiom,[])).
% 43.46/6.01  
% 43.46/6.01  fof(f33,plain,(
% 43.46/6.01    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ((~r2_hidden(k1_funct_1(X0,sK1(X0,X1,X2)),X1) | ~r2_hidden(sK1(X0,X1,X2),k1_relat_1(X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(k1_funct_1(X0,sK1(X0,X1,X2)),X1) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X0))) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k1_funct_1(X0,X4),X1) | ~r2_hidden(X4,k1_relat_1(X0))) & ((r2_hidden(k1_funct_1(X0,X4),X1) & r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X4,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 43.46/6.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f32])).
% 43.46/6.01  
% 43.46/6.01  fof(f48,plain,(
% 43.46/6.01    ( ! [X4,X2,X0,X1] : (r2_hidden(k1_funct_1(X0,X4),X1) | ~r2_hidden(X4,X2) | k10_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 43.46/6.01    inference(cnf_transformation,[],[f33])).
% 43.46/6.01  
% 43.46/6.01  fof(f63,plain,(
% 43.46/6.01    ( ! [X4,X0,X1] : (r2_hidden(k1_funct_1(X0,X4),X1) | ~r2_hidden(X4,k10_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 43.46/6.01    inference(equality_resolution,[],[f48])).
% 43.46/6.01  
% 43.46/6.01  fof(f9,conjecture,(
% 43.46/6.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <=> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))))))),
% 43.46/6.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.46/6.01  
% 43.46/6.01  fof(f10,negated_conjecture,(
% 43.46/6.01    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <=> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))))))),
% 43.46/6.01    inference(negated_conjecture,[],[f9])).
% 43.46/6.01  
% 43.46/6.01  fof(f23,plain,(
% 43.46/6.01    ? [X0] : (? [X1] : (? [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <~> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0)))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 43.46/6.01    inference(ennf_transformation,[],[f10])).
% 43.46/6.01  
% 43.46/6.01  fof(f24,plain,(
% 43.46/6.01    ? [X0] : (? [X1] : (? [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <~> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0)))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 43.46/6.01    inference(flattening,[],[f23])).
% 43.46/6.01  
% 43.46/6.01  fof(f34,plain,(
% 43.46/6.01    ? [X0] : (? [X1] : (? [X2] : (((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0))) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 43.46/6.01    inference(nnf_transformation,[],[f24])).
% 43.46/6.01  
% 43.46/6.01  fof(f35,plain,(
% 43.46/6.01    ? [X0] : (? [X1] : (? [X2] : ((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 43.46/6.01    inference(flattening,[],[f34])).
% 43.46/6.01  
% 43.46/6.01  fof(f38,plain,(
% 43.46/6.01    ( ! [X0,X1] : (? [X2] : ((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) => ((~r1_tarski(k9_relat_1(X0,sK4),k1_relat_1(X1)) | ~r1_tarski(sK4,k1_relat_1(X0)) | ~r1_tarski(sK4,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,sK4),k1_relat_1(X1)) & r1_tarski(sK4,k1_relat_1(X0))) | r1_tarski(sK4,k1_relat_1(k5_relat_1(X0,X1)))))) )),
% 43.46/6.01    introduced(choice_axiom,[])).
% 43.46/6.01  
% 43.46/6.01  fof(f37,plain,(
% 43.46/6.01    ( ! [X0] : (? [X1] : (? [X2] : ((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) => (? [X2] : ((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(sK3)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,sK3)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(sK3)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,sK3))))) & v1_funct_1(sK3) & v1_relat_1(sK3))) )),
% 43.46/6.01    introduced(choice_axiom,[])).
% 43.46/6.01  
% 43.46/6.01  fof(f36,plain,(
% 43.46/6.01    ? [X0] : (? [X1] : (? [X2] : ((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (? [X2] : ((~r1_tarski(k9_relat_1(sK2,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(sK2)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(sK2,X1)))) & ((r1_tarski(k9_relat_1(sK2,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(sK2))) | r1_tarski(X2,k1_relat_1(k5_relat_1(sK2,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 43.46/6.01    introduced(choice_axiom,[])).
% 43.46/6.01  
% 43.46/6.01  fof(f39,plain,(
% 43.46/6.01    (((~r1_tarski(k9_relat_1(sK2,sK4),k1_relat_1(sK3)) | ~r1_tarski(sK4,k1_relat_1(sK2)) | ~r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3)))) & ((r1_tarski(k9_relat_1(sK2,sK4),k1_relat_1(sK3)) & r1_tarski(sK4,k1_relat_1(sK2))) | r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3))))) & v1_funct_1(sK3) & v1_relat_1(sK3)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 43.46/6.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f35,f38,f37,f36])).
% 43.46/6.01  
% 43.46/6.01  fof(f60,plain,(
% 43.46/6.01    r1_tarski(k9_relat_1(sK2,sK4),k1_relat_1(sK3)) | r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3)))),
% 43.46/6.01    inference(cnf_transformation,[],[f39])).
% 43.46/6.01  
% 43.46/6.01  fof(f55,plain,(
% 43.46/6.01    v1_relat_1(sK2)),
% 43.46/6.01    inference(cnf_transformation,[],[f39])).
% 43.46/6.01  
% 43.46/6.01  fof(f57,plain,(
% 43.46/6.01    v1_relat_1(sK3)),
% 43.46/6.01    inference(cnf_transformation,[],[f39])).
% 43.46/6.01  
% 43.46/6.01  fof(f8,axiom,(
% 43.46/6.01    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 43.46/6.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.46/6.01  
% 43.46/6.01  fof(f21,plain,(
% 43.46/6.01    ! [X0,X1,X2] : ((r1_tarski(X0,k10_relat_1(X2,X1)) | (~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 43.46/6.01    inference(ennf_transformation,[],[f8])).
% 43.46/6.01  
% 43.46/6.01  fof(f22,plain,(
% 43.46/6.01    ! [X0,X1,X2] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 43.46/6.01    inference(flattening,[],[f21])).
% 43.46/6.01  
% 43.46/6.01  fof(f54,plain,(
% 43.46/6.01    ( ! [X2,X0,X1] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 43.46/6.01    inference(cnf_transformation,[],[f22])).
% 43.46/6.01  
% 43.46/6.01  fof(f56,plain,(
% 43.46/6.01    v1_funct_1(sK2)),
% 43.46/6.01    inference(cnf_transformation,[],[f39])).
% 43.46/6.01  
% 43.46/6.01  fof(f59,plain,(
% 43.46/6.01    r1_tarski(sK4,k1_relat_1(sK2)) | r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3)))),
% 43.46/6.01    inference(cnf_transformation,[],[f39])).
% 43.46/6.01  
% 43.46/6.01  fof(f42,plain,(
% 43.46/6.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 43.46/6.01    inference(cnf_transformation,[],[f28])).
% 43.46/6.01  
% 43.46/6.01  fof(f41,plain,(
% 43.46/6.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 43.46/6.01    inference(cnf_transformation,[],[f28])).
% 43.46/6.01  
% 43.46/6.01  fof(f47,plain,(
% 43.46/6.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X4,X2) | k10_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 43.46/6.01    inference(cnf_transformation,[],[f33])).
% 43.46/6.01  
% 43.46/6.01  fof(f64,plain,(
% 43.46/6.01    ( ! [X4,X0,X1] : (r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X4,k10_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 43.46/6.01    inference(equality_resolution,[],[f47])).
% 43.46/6.01  
% 43.46/6.01  fof(f3,axiom,(
% 43.46/6.01    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 43.46/6.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.46/6.01  
% 43.46/6.01  fof(f13,plain,(
% 43.46/6.01    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 43.46/6.01    inference(ennf_transformation,[],[f3])).
% 43.46/6.01  
% 43.46/6.01  fof(f44,plain,(
% 43.46/6.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 43.46/6.01    inference(cnf_transformation,[],[f13])).
% 43.46/6.01  
% 43.46/6.01  fof(f2,axiom,(
% 43.46/6.01    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 43.46/6.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.46/6.01  
% 43.46/6.01  fof(f12,plain,(
% 43.46/6.01    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 43.46/6.01    inference(ennf_transformation,[],[f2])).
% 43.46/6.01  
% 43.46/6.01  fof(f43,plain,(
% 43.46/6.01    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 43.46/6.01    inference(cnf_transformation,[],[f12])).
% 43.46/6.01  
% 43.46/6.01  fof(f61,plain,(
% 43.46/6.01    ~r1_tarski(k9_relat_1(sK2,sK4),k1_relat_1(sK3)) | ~r1_tarski(sK4,k1_relat_1(sK2)) | ~r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3)))),
% 43.46/6.01    inference(cnf_transformation,[],[f39])).
% 43.46/6.01  
% 43.46/6.01  cnf(c_2,plain,
% 43.46/6.01      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 43.46/6.01      inference(cnf_transformation,[],[f40]) ).
% 43.46/6.01  
% 43.46/6.01  cnf(c_146024,plain,
% 43.46/6.01      ( r2_hidden(sK0(k9_relat_1(sK2,sK4),k1_relat_1(sK3)),X0)
% 43.46/6.01      | ~ r2_hidden(sK0(k9_relat_1(sK2,sK4),k1_relat_1(sK3)),k9_relat_1(sK2,sK4))
% 43.46/6.01      | ~ r1_tarski(k9_relat_1(sK2,sK4),X0) ),
% 43.46/6.01      inference(instantiation,[status(thm)],[c_2]) ).
% 43.46/6.01  
% 43.46/6.01  cnf(c_156588,plain,
% 43.46/6.01      ( r2_hidden(sK0(k9_relat_1(sK2,sK4),k1_relat_1(sK3)),k9_relat_1(X0,k10_relat_1(X0,k1_relat_1(sK3))))
% 43.46/6.01      | ~ r2_hidden(sK0(k9_relat_1(sK2,sK4),k1_relat_1(sK3)),k9_relat_1(sK2,sK4))
% 43.46/6.01      | ~ r1_tarski(k9_relat_1(sK2,sK4),k9_relat_1(X0,k10_relat_1(X0,k1_relat_1(sK3)))) ),
% 43.46/6.01      inference(instantiation,[status(thm)],[c_146024]) ).
% 43.46/6.01  
% 43.46/6.01  cnf(c_156590,plain,
% 43.46/6.01      ( r2_hidden(sK0(k9_relat_1(sK2,sK4),k1_relat_1(sK3)),k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(sK3))))
% 43.46/6.01      | ~ r2_hidden(sK0(k9_relat_1(sK2,sK4),k1_relat_1(sK3)),k9_relat_1(sK2,sK4))
% 43.46/6.01      | ~ r1_tarski(k9_relat_1(sK2,sK4),k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(sK3)))) ),
% 43.46/6.01      inference(instantiation,[status(thm)],[c_156588]) ).
% 43.46/6.01  
% 43.46/6.01  cnf(c_146233,plain,
% 43.46/6.01      ( ~ r2_hidden(sK0(k9_relat_1(sK2,sK4),k1_relat_1(sK3)),X0)
% 43.46/6.01      | r2_hidden(sK0(k9_relat_1(sK2,sK4),k1_relat_1(sK3)),X1)
% 43.46/6.01      | ~ r1_tarski(X0,X1) ),
% 43.46/6.01      inference(instantiation,[status(thm)],[c_2]) ).
% 43.46/6.01  
% 43.46/6.01  cnf(c_146582,plain,
% 43.46/6.01      ( ~ r2_hidden(sK0(k9_relat_1(sK2,sK4),k1_relat_1(sK3)),X0)
% 43.46/6.01      | r2_hidden(sK0(k9_relat_1(sK2,sK4),k1_relat_1(sK3)),k1_relat_1(sK3))
% 43.46/6.01      | ~ r1_tarski(X0,k1_relat_1(sK3)) ),
% 43.46/6.01      inference(instantiation,[status(thm)],[c_146233]) ).
% 43.46/6.01  
% 43.46/6.01  cnf(c_152961,plain,
% 43.46/6.01      ( ~ r2_hidden(sK0(k9_relat_1(sK2,sK4),k1_relat_1(sK3)),k9_relat_1(X0,k10_relat_1(X0,k1_relat_1(sK3))))
% 43.46/6.01      | r2_hidden(sK0(k9_relat_1(sK2,sK4),k1_relat_1(sK3)),k1_relat_1(sK3))
% 43.46/6.01      | ~ r1_tarski(k9_relat_1(X0,k10_relat_1(X0,k1_relat_1(sK3))),k1_relat_1(sK3)) ),
% 43.46/6.01      inference(instantiation,[status(thm)],[c_146582]) ).
% 43.46/6.01  
% 43.46/6.01  cnf(c_152969,plain,
% 43.46/6.01      ( ~ r2_hidden(sK0(k9_relat_1(sK2,sK4),k1_relat_1(sK3)),k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(sK3))))
% 43.46/6.01      | r2_hidden(sK0(k9_relat_1(sK2,sK4),k1_relat_1(sK3)),k1_relat_1(sK3))
% 43.46/6.01      | ~ r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(sK3))),k1_relat_1(sK3)) ),
% 43.46/6.01      inference(instantiation,[status(thm)],[c_152961]) ).
% 43.46/6.01  
% 43.46/6.01  cnf(c_13,plain,
% 43.46/6.01      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
% 43.46/6.01      | ~ v1_funct_1(X0)
% 43.46/6.01      | ~ v1_relat_1(X0) ),
% 43.46/6.01      inference(cnf_transformation,[],[f53]) ).
% 43.46/6.01  
% 43.46/6.01  cnf(c_971,plain,
% 43.46/6.01      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,k1_relat_1(X1))),k1_relat_1(X1))
% 43.46/6.01      | ~ v1_funct_1(X0)
% 43.46/6.01      | ~ v1_relat_1(X0) ),
% 43.46/6.01      inference(instantiation,[status(thm)],[c_13]) ).
% 43.46/6.01  
% 43.46/6.01  cnf(c_129573,plain,
% 43.46/6.01      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,k1_relat_1(sK3))),k1_relat_1(sK3))
% 43.46/6.01      | ~ v1_funct_1(X0)
% 43.46/6.01      | ~ v1_relat_1(X0) ),
% 43.46/6.01      inference(instantiation,[status(thm)],[c_971]) ).
% 43.46/6.01  
% 43.46/6.01  cnf(c_129579,plain,
% 43.46/6.01      ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(sK3))),k1_relat_1(sK3))
% 43.46/6.01      | ~ v1_funct_1(sK2)
% 43.46/6.01      | ~ v1_relat_1(sK2) ),
% 43.46/6.01      inference(instantiation,[status(thm)],[c_129573]) ).
% 43.46/6.01  
% 43.46/6.01  cnf(c_5,plain,
% 43.46/6.01      ( ~ r1_tarski(X0,X1)
% 43.46/6.01      | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
% 43.46/6.01      | ~ v1_relat_1(X2) ),
% 43.46/6.01      inference(cnf_transformation,[],[f45]) ).
% 43.46/6.01  
% 43.46/6.01  cnf(c_1593,plain,
% 43.46/6.01      ( r1_tarski(k9_relat_1(sK2,sK4),k9_relat_1(sK2,X0))
% 43.46/6.01      | ~ r1_tarski(sK4,X0)
% 43.46/6.01      | ~ v1_relat_1(sK2) ),
% 43.46/6.01      inference(instantiation,[status(thm)],[c_5]) ).
% 43.46/6.01  
% 43.46/6.01  cnf(c_8936,plain,
% 43.46/6.01      ( r1_tarski(k9_relat_1(sK2,sK4),k9_relat_1(sK2,k10_relat_1(X0,X1)))
% 43.46/6.01      | ~ r1_tarski(sK4,k10_relat_1(X0,X1))
% 43.46/6.01      | ~ v1_relat_1(sK2) ),
% 43.46/6.01      inference(instantiation,[status(thm)],[c_1593]) ).
% 43.46/6.01  
% 43.46/6.01  cnf(c_70750,plain,
% 43.46/6.01      ( r1_tarski(k9_relat_1(sK2,sK4),k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(sK3))))
% 43.46/6.01      | ~ r1_tarski(sK4,k10_relat_1(sK2,k1_relat_1(sK3)))
% 43.46/6.01      | ~ v1_relat_1(sK2) ),
% 43.46/6.01      inference(instantiation,[status(thm)],[c_8936]) ).
% 43.46/6.01  
% 43.46/6.01  cnf(c_203,plain,
% 43.46/6.01      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 43.46/6.01      theory(equality) ).
% 43.46/6.01  
% 43.46/6.01  cnf(c_6,plain,
% 43.46/6.01      ( ~ v1_relat_1(X0)
% 43.46/6.01      | ~ v1_relat_1(X1)
% 43.46/6.01      | k10_relat_1(X1,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(X1,X0)) ),
% 43.46/6.01      inference(cnf_transformation,[],[f46]) ).
% 43.46/6.01  
% 43.46/6.01  cnf(c_3559,plain,
% 43.46/6.01      ( r1_tarski(X0,k10_relat_1(X1,k1_relat_1(X2)))
% 43.46/6.01      | ~ r1_tarski(X3,k1_relat_1(k5_relat_1(X1,X2)))
% 43.46/6.01      | ~ v1_relat_1(X2)
% 43.46/6.01      | ~ v1_relat_1(X1)
% 43.46/6.01      | X0 != X3 ),
% 43.46/6.01      inference(resolution,[status(thm)],[c_203,c_6]) ).
% 43.46/6.01  
% 43.46/6.01  cnf(c_11,plain,
% 43.46/6.01      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 43.46/6.01      | r2_hidden(k1_funct_1(X1,X0),X2)
% 43.46/6.01      | ~ v1_funct_1(X1)
% 43.46/6.01      | ~ v1_relat_1(X1) ),
% 43.46/6.01      inference(cnf_transformation,[],[f63]) ).
% 43.46/6.01  
% 43.46/6.01  cnf(c_16,negated_conjecture,
% 43.46/6.01      ( r1_tarski(k9_relat_1(sK2,sK4),k1_relat_1(sK3))
% 43.46/6.01      | r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3))) ),
% 43.46/6.01      inference(cnf_transformation,[],[f60]) ).
% 43.46/6.01  
% 43.46/6.01  cnf(c_1229,plain,
% 43.46/6.01      ( ~ r2_hidden(X0,k9_relat_1(sK2,sK4))
% 43.46/6.01      | r2_hidden(X0,k1_relat_1(sK3))
% 43.46/6.01      | r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3))) ),
% 43.46/6.01      inference(resolution,[status(thm)],[c_2,c_16]) ).
% 43.46/6.01  
% 43.46/6.01  cnf(c_2259,plain,
% 43.46/6.01      ( ~ r2_hidden(X0,k10_relat_1(X1,k9_relat_1(sK2,sK4)))
% 43.46/6.01      | r2_hidden(k1_funct_1(X1,X0),k1_relat_1(sK3))
% 43.46/6.01      | r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3)))
% 43.46/6.01      | ~ v1_funct_1(X1)
% 43.46/6.01      | ~ v1_relat_1(X1) ),
% 43.46/6.01      inference(resolution,[status(thm)],[c_11,c_1229]) ).
% 43.46/6.01  
% 43.46/6.01  cnf(c_2279,plain,
% 43.46/6.01      ( ~ r2_hidden(X0,k10_relat_1(X1,k10_relat_1(X2,k9_relat_1(sK2,sK4))))
% 43.46/6.01      | r2_hidden(k1_funct_1(X2,k1_funct_1(X1,X0)),k1_relat_1(sK3))
% 43.46/6.01      | r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3)))
% 43.46/6.01      | ~ v1_funct_1(X1)
% 43.46/6.01      | ~ v1_funct_1(X2)
% 43.46/6.01      | ~ v1_relat_1(X2)
% 43.46/6.01      | ~ v1_relat_1(X1) ),
% 43.46/6.01      inference(resolution,[status(thm)],[c_2259,c_11]) ).
% 43.46/6.01  
% 43.46/6.01  cnf(c_21,negated_conjecture,
% 43.46/6.01      ( v1_relat_1(sK2) ),
% 43.46/6.01      inference(cnf_transformation,[],[f55]) ).
% 43.46/6.01  
% 43.46/6.01  cnf(c_569,plain,
% 43.46/6.01      ( v1_relat_1(sK2) = iProver_top ),
% 43.46/6.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 43.46/6.01  
% 43.46/6.01  cnf(c_19,negated_conjecture,
% 43.46/6.01      ( v1_relat_1(sK3) ),
% 43.46/6.01      inference(cnf_transformation,[],[f57]) ).
% 43.46/6.01  
% 43.46/6.01  cnf(c_571,plain,
% 43.46/6.01      ( v1_relat_1(sK3) = iProver_top ),
% 43.46/6.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 43.46/6.01  
% 43.46/6.01  cnf(c_584,plain,
% 43.46/6.01      ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
% 43.46/6.01      | v1_relat_1(X0) != iProver_top
% 43.46/6.01      | v1_relat_1(X1) != iProver_top ),
% 43.46/6.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 43.46/6.01  
% 43.46/6.01  cnf(c_2097,plain,
% 43.46/6.01      ( k10_relat_1(X0,k1_relat_1(sK3)) = k1_relat_1(k5_relat_1(X0,sK3))
% 43.46/6.01      | v1_relat_1(X0) != iProver_top ),
% 43.46/6.01      inference(superposition,[status(thm)],[c_571,c_584]) ).
% 43.46/6.01  
% 43.46/6.01  cnf(c_2240,plain,
% 43.46/6.01      ( k10_relat_1(sK2,k1_relat_1(sK3)) = k1_relat_1(k5_relat_1(sK2,sK3)) ),
% 43.46/6.01      inference(superposition,[status(thm)],[c_569,c_2097]) ).
% 43.46/6.01  
% 43.46/6.01  cnf(c_574,plain,
% 43.46/6.01      ( r1_tarski(k9_relat_1(sK2,sK4),k1_relat_1(sK3)) = iProver_top
% 43.46/6.01      | r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3))) = iProver_top ),
% 43.46/6.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 43.46/6.01  
% 43.46/6.01  cnf(c_14,plain,
% 43.46/6.01      ( r1_tarski(X0,k10_relat_1(X1,X2))
% 43.46/6.01      | ~ r1_tarski(X0,k1_relat_1(X1))
% 43.46/6.01      | ~ r1_tarski(k9_relat_1(X1,X0),X2)
% 43.46/6.01      | ~ v1_funct_1(X1)
% 43.46/6.01      | ~ v1_relat_1(X1) ),
% 43.46/6.01      inference(cnf_transformation,[],[f54]) ).
% 43.46/6.01  
% 43.46/6.01  cnf(c_576,plain,
% 43.46/6.01      ( r1_tarski(X0,k10_relat_1(X1,X2)) = iProver_top
% 43.46/6.01      | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
% 43.46/6.01      | r1_tarski(k9_relat_1(X1,X0),X2) != iProver_top
% 43.46/6.01      | v1_funct_1(X1) != iProver_top
% 43.46/6.01      | v1_relat_1(X1) != iProver_top ),
% 43.46/6.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 43.46/6.01  
% 43.46/6.01  cnf(c_934,plain,
% 43.46/6.01      ( r1_tarski(sK4,k10_relat_1(sK2,k1_relat_1(sK3))) = iProver_top
% 43.46/6.01      | r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3))) = iProver_top
% 43.46/6.01      | r1_tarski(sK4,k1_relat_1(sK2)) != iProver_top
% 43.46/6.01      | v1_funct_1(sK2) != iProver_top
% 43.46/6.01      | v1_relat_1(sK2) != iProver_top ),
% 43.46/6.01      inference(superposition,[status(thm)],[c_574,c_576]) ).
% 43.46/6.01  
% 43.46/6.01  cnf(c_22,plain,
% 43.46/6.01      ( v1_relat_1(sK2) = iProver_top ),
% 43.46/6.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 43.46/6.01  
% 43.46/6.01  cnf(c_20,negated_conjecture,
% 43.46/6.01      ( v1_funct_1(sK2) ),
% 43.46/6.01      inference(cnf_transformation,[],[f56]) ).
% 43.46/6.01  
% 43.46/6.01  cnf(c_23,plain,
% 43.46/6.01      ( v1_funct_1(sK2) = iProver_top ),
% 43.46/6.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 43.46/6.01  
% 43.46/6.01  cnf(c_17,negated_conjecture,
% 43.46/6.01      ( r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3)))
% 43.46/6.01      | r1_tarski(sK4,k1_relat_1(sK2)) ),
% 43.46/6.01      inference(cnf_transformation,[],[f59]) ).
% 43.46/6.01  
% 43.46/6.01  cnf(c_26,plain,
% 43.46/6.01      ( r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3))) = iProver_top
% 43.46/6.01      | r1_tarski(sK4,k1_relat_1(sK2)) = iProver_top ),
% 43.46/6.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 43.46/6.01  
% 43.46/6.01  cnf(c_1502,plain,
% 43.46/6.01      ( r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3))) = iProver_top
% 43.46/6.01      | r1_tarski(sK4,k10_relat_1(sK2,k1_relat_1(sK3))) = iProver_top ),
% 43.46/6.01      inference(global_propositional_subsumption,
% 43.46/6.01                [status(thm)],
% 43.46/6.01                [c_934,c_22,c_23,c_26]) ).
% 43.46/6.01  
% 43.46/6.01  cnf(c_1503,plain,
% 43.46/6.01      ( r1_tarski(sK4,k10_relat_1(sK2,k1_relat_1(sK3))) = iProver_top
% 43.46/6.01      | r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3))) = iProver_top ),
% 43.46/6.01      inference(renaming,[status(thm)],[c_1502]) ).
% 43.46/6.01  
% 43.46/6.01  cnf(c_2424,plain,
% 43.46/6.01      ( r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3))) = iProver_top ),
% 43.46/6.01      inference(demodulation,[status(thm)],[c_2240,c_1503]) ).
% 43.46/6.01  
% 43.46/6.01  cnf(c_2434,plain,
% 43.46/6.01      ( r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3))) ),
% 43.46/6.01      inference(predicate_to_equality_rev,[status(thm)],[c_2424]) ).
% 43.46/6.01  
% 43.46/6.01  cnf(c_2456,plain,
% 43.46/6.01      ( r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3))) ),
% 43.46/6.01      inference(global_propositional_subsumption,
% 43.46/6.01                [status(thm)],
% 43.46/6.01                [c_2279,c_2434]) ).
% 43.46/6.01  
% 43.46/6.01  cnf(c_18660,plain,
% 43.46/6.01      ( r1_tarski(X0,k10_relat_1(sK2,k1_relat_1(sK3)))
% 43.46/6.01      | ~ v1_relat_1(sK3)
% 43.46/6.01      | ~ v1_relat_1(sK2)
% 43.46/6.01      | X0 != sK4 ),
% 43.46/6.01      inference(resolution,[status(thm)],[c_3559,c_2456]) ).
% 43.46/6.01  
% 43.46/6.01  cnf(c_19255,plain,
% 43.46/6.01      ( r1_tarski(X0,k10_relat_1(sK2,k1_relat_1(sK3))) | X0 != sK4 ),
% 43.46/6.01      inference(global_propositional_subsumption,
% 43.46/6.01                [status(thm)],
% 43.46/6.01                [c_18660,c_21,c_19]) ).
% 43.46/6.01  
% 43.46/6.01  cnf(c_19671,plain,
% 43.46/6.01      ( ~ r2_hidden(X0,X1)
% 43.46/6.01      | r2_hidden(X0,k10_relat_1(sK2,k1_relat_1(sK3)))
% 43.46/6.01      | X1 != sK4 ),
% 43.46/6.01      inference(resolution,[status(thm)],[c_19255,c_2]) ).
% 43.46/6.01  
% 43.46/6.01  cnf(c_201,plain,( X0 = X0 ),theory(equality) ).
% 43.46/6.01  
% 43.46/6.01  cnf(c_19713,plain,
% 43.46/6.01      ( r2_hidden(X0,k10_relat_1(sK2,k1_relat_1(sK3)))
% 43.46/6.01      | ~ r2_hidden(X0,sK4) ),
% 43.46/6.01      inference(resolution,[status(thm)],[c_19671,c_201]) ).
% 43.46/6.01  
% 43.46/6.01  cnf(c_0,plain,
% 43.46/6.01      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 43.46/6.01      inference(cnf_transformation,[],[f42]) ).
% 43.46/6.01  
% 43.46/6.01  cnf(c_20179,plain,
% 43.46/6.01      ( ~ r2_hidden(sK0(X0,k10_relat_1(sK2,k1_relat_1(sK3))),sK4)
% 43.46/6.01      | r1_tarski(X0,k10_relat_1(sK2,k1_relat_1(sK3))) ),
% 43.46/6.01      inference(resolution,[status(thm)],[c_19713,c_0]) ).
% 43.46/6.01  
% 43.46/6.01  cnf(c_1,plain,
% 43.46/6.01      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 43.46/6.01      inference(cnf_transformation,[],[f41]) ).
% 43.46/6.01  
% 43.46/6.01  cnf(c_24169,plain,
% 43.46/6.01      ( r1_tarski(sK4,k10_relat_1(sK2,k1_relat_1(sK3))) ),
% 43.46/6.01      inference(resolution,[status(thm)],[c_20179,c_1]) ).
% 43.46/6.01  
% 43.46/6.01  cnf(c_589,plain,
% 43.46/6.01      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 43.46/6.01      | r1_tarski(X0,X1) = iProver_top ),
% 43.46/6.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 43.46/6.01  
% 43.46/6.01  cnf(c_12,plain,
% 43.46/6.01      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 43.46/6.01      | r2_hidden(X0,k1_relat_1(X1))
% 43.46/6.01      | ~ v1_funct_1(X1)
% 43.46/6.01      | ~ v1_relat_1(X1) ),
% 43.46/6.01      inference(cnf_transformation,[],[f64]) ).
% 43.46/6.01  
% 43.46/6.01  cnf(c_578,plain,
% 43.46/6.01      ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
% 43.46/6.01      | r2_hidden(X0,k1_relat_1(X1)) = iProver_top
% 43.46/6.01      | v1_funct_1(X1) != iProver_top
% 43.46/6.01      | v1_relat_1(X1) != iProver_top ),
% 43.46/6.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 43.46/6.01  
% 43.46/6.01  cnf(c_2436,plain,
% 43.46/6.01      ( r2_hidden(X0,k1_relat_1(k5_relat_1(sK2,sK3))) != iProver_top
% 43.46/6.01      | r2_hidden(X0,k1_relat_1(sK2)) = iProver_top
% 43.46/6.01      | v1_funct_1(sK2) != iProver_top
% 43.46/6.01      | v1_relat_1(sK2) != iProver_top ),
% 43.46/6.01      inference(superposition,[status(thm)],[c_2240,c_578]) ).
% 43.46/6.01  
% 43.46/6.01  cnf(c_4528,plain,
% 43.46/6.01      ( r2_hidden(X0,k1_relat_1(k5_relat_1(sK2,sK3))) != iProver_top
% 43.46/6.01      | r2_hidden(X0,k1_relat_1(sK2)) = iProver_top ),
% 43.46/6.01      inference(global_propositional_subsumption,
% 43.46/6.01                [status(thm)],
% 43.46/6.01                [c_2436,c_22,c_23]) ).
% 43.46/6.01  
% 43.46/6.01  cnf(c_4536,plain,
% 43.46/6.01      ( r2_hidden(sK0(k1_relat_1(k5_relat_1(sK2,sK3)),X0),k1_relat_1(sK2)) = iProver_top
% 43.46/6.01      | r1_tarski(k1_relat_1(k5_relat_1(sK2,sK3)),X0) = iProver_top ),
% 43.46/6.01      inference(superposition,[status(thm)],[c_589,c_4528]) ).
% 43.46/6.01  
% 43.46/6.01  cnf(c_590,plain,
% 43.46/6.01      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 43.46/6.01      | r1_tarski(X0,X1) = iProver_top ),
% 43.46/6.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 43.46/6.01  
% 43.46/6.01  cnf(c_7718,plain,
% 43.46/6.01      ( r1_tarski(k1_relat_1(k5_relat_1(sK2,sK3)),k1_relat_1(sK2)) = iProver_top ),
% 43.46/6.01      inference(superposition,[status(thm)],[c_4536,c_590]) ).
% 43.46/6.01  
% 43.46/6.01  cnf(c_4,plain,
% 43.46/6.01      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 43.46/6.01      inference(cnf_transformation,[],[f44]) ).
% 43.46/6.01  
% 43.46/6.01  cnf(c_586,plain,
% 43.46/6.01      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 43.46/6.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 43.46/6.01  
% 43.46/6.01  cnf(c_2930,plain,
% 43.46/6.01      ( k2_xboole_0(sK4,k1_relat_1(k5_relat_1(sK2,sK3))) = k1_relat_1(k5_relat_1(sK2,sK3)) ),
% 43.46/6.01      inference(superposition,[status(thm)],[c_2424,c_586]) ).
% 43.46/6.01  
% 43.46/6.01  cnf(c_3,plain,
% 43.46/6.01      ( r1_tarski(X0,X1) | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 43.46/6.01      inference(cnf_transformation,[],[f43]) ).
% 43.46/6.01  
% 43.46/6.01  cnf(c_587,plain,
% 43.46/6.01      ( r1_tarski(X0,X1) = iProver_top
% 43.46/6.01      | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
% 43.46/6.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 43.46/6.01  
% 43.46/6.01  cnf(c_6388,plain,
% 43.46/6.01      ( r1_tarski(k1_relat_1(k5_relat_1(sK2,sK3)),X0) != iProver_top
% 43.46/6.01      | r1_tarski(sK4,X0) = iProver_top ),
% 43.46/6.01      inference(superposition,[status(thm)],[c_2930,c_587]) ).
% 43.46/6.01  
% 43.46/6.01  cnf(c_14155,plain,
% 43.46/6.01      ( r1_tarski(sK4,k1_relat_1(sK2)) = iProver_top ),
% 43.46/6.01      inference(superposition,[status(thm)],[c_7718,c_6388]) ).
% 43.46/6.01  
% 43.46/6.01  cnf(c_14163,plain,
% 43.46/6.01      ( r1_tarski(sK4,k1_relat_1(sK2)) ),
% 43.46/6.01      inference(predicate_to_equality_rev,[status(thm)],[c_14155]) ).
% 43.46/6.01  
% 43.46/6.01  cnf(c_8022,plain,
% 43.46/6.01      ( ~ r2_hidden(sK0(k9_relat_1(sK2,sK4),k1_relat_1(sK3)),k1_relat_1(sK3))
% 43.46/6.01      | r1_tarski(k9_relat_1(sK2,sK4),k1_relat_1(sK3)) ),
% 43.46/6.01      inference(instantiation,[status(thm)],[c_0]) ).
% 43.46/6.01  
% 43.46/6.01  cnf(c_847,plain,
% 43.46/6.01      ( r2_hidden(sK0(k9_relat_1(X0,X1),X2),k9_relat_1(X0,X1))
% 43.46/6.01      | r1_tarski(k9_relat_1(X0,X1),X2) ),
% 43.46/6.01      inference(instantiation,[status(thm)],[c_1]) ).
% 43.46/6.01  
% 43.46/6.01  cnf(c_922,plain,
% 43.46/6.01      ( r2_hidden(sK0(k9_relat_1(sK2,sK4),k1_relat_1(sK3)),k9_relat_1(sK2,sK4))
% 43.46/6.01      | r1_tarski(k9_relat_1(sK2,sK4),k1_relat_1(sK3)) ),
% 43.46/6.01      inference(instantiation,[status(thm)],[c_847]) ).
% 43.46/6.01  
% 43.46/6.01  cnf(c_15,negated_conjecture,
% 43.46/6.01      ( ~ r1_tarski(k9_relat_1(sK2,sK4),k1_relat_1(sK3))
% 43.46/6.01      | ~ r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3)))
% 43.46/6.01      | ~ r1_tarski(sK4,k1_relat_1(sK2)) ),
% 43.46/6.01      inference(cnf_transformation,[],[f61]) ).
% 43.46/6.01  
% 43.46/6.01  cnf(contradiction,plain,
% 43.46/6.01      ( $false ),
% 43.46/6.01      inference(minisat,
% 43.46/6.01                [status(thm)],
% 43.46/6.01                [c_156590,c_152969,c_129579,c_70750,c_24169,c_14163,
% 43.46/6.01                 c_8022,c_2434,c_922,c_15,c_20,c_21]) ).
% 43.46/6.01  
% 43.46/6.01  
% 43.46/6.01  % SZS output end CNFRefutation for theBenchmark.p
% 43.46/6.01  
% 43.46/6.01  ------                               Statistics
% 43.46/6.01  
% 43.46/6.01  ------ Selected
% 43.46/6.01  
% 43.46/6.01  total_time:                             5.177
% 43.46/6.01  
%------------------------------------------------------------------------------
