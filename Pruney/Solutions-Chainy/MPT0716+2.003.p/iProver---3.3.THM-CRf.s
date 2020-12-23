%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:52:52 EST 2020

% Result     : Theorem 51.37s
% Output     : CNFRefutation 51.37s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 383 expanded)
%              Number of clauses        :   67 (  92 expanded)
%              Number of leaves         :   14 (  99 expanded)
%              Depth                    :   19
%              Number of atoms          :  458 (2590 expanded)
%              Number of equality atoms :   52 (  74 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( ( r1_tarski(X0,X1)
              & r1_tarski(X2,X3) )
           => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1))
          | ~ r1_tarski(X0,X1)
          | ~ r1_tarski(X2,X3)
          | ~ v1_relat_1(X3) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1))
          | ~ r1_tarski(X0,X1)
          | ~ r1_tarski(X2,X3)
          | ~ v1_relat_1(X3) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1))
      | ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X2,X3)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f26])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
              | ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              | ~ r2_hidden(X0,k1_relat_1(X2)) )
            & ( ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
                & r2_hidden(X0,k1_relat_1(X2)) )
              | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
              | ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              | ~ r2_hidden(X0,k1_relat_1(X2)) )
            & ( ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
                & r2_hidden(X0,k1_relat_1(X2)) )
              | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f10,conjecture,(
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

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

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
    inference(ennf_transformation,[],[f11])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

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
    inference(nnf_transformation,[],[f25])).

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
     => ( ( ~ r1_tarski(k9_relat_1(X0,sK3),k1_relat_1(X1))
          | ~ r1_tarski(sK3,k1_relat_1(X0))
          | ~ r1_tarski(sK3,k1_relat_1(k5_relat_1(X0,X1))) )
        & ( ( r1_tarski(k9_relat_1(X0,sK3),k1_relat_1(X1))
            & r1_tarski(sK3,k1_relat_1(X0)) )
          | r1_tarski(sK3,k1_relat_1(k5_relat_1(X0,X1))) ) ) ) ),
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
            ( ( ~ r1_tarski(k9_relat_1(X0,X2),k1_relat_1(sK2))
              | ~ r1_tarski(X2,k1_relat_1(X0))
              | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(X0,sK2))) )
            & ( ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(sK2))
                & r1_tarski(X2,k1_relat_1(X0)) )
              | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,sK2))) ) )
        & v1_funct_1(sK2)
        & v1_relat_1(sK2) ) ) ),
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
              ( ( ~ r1_tarski(k9_relat_1(sK1,X2),k1_relat_1(X1))
                | ~ r1_tarski(X2,k1_relat_1(sK1))
                | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(sK1,X1))) )
              & ( ( r1_tarski(k9_relat_1(sK1,X2),k1_relat_1(X1))
                  & r1_tarski(X2,k1_relat_1(sK1)) )
                | r1_tarski(X2,k1_relat_1(k5_relat_1(sK1,X1))) ) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ( ~ r1_tarski(k9_relat_1(sK1,sK3),k1_relat_1(sK2))
      | ~ r1_tarski(sK3,k1_relat_1(sK1))
      | ~ r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2))) )
    & ( ( r1_tarski(k9_relat_1(sK1,sK3),k1_relat_1(sK2))
        & r1_tarski(sK3,k1_relat_1(sK1)) )
      | r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2))) )
    & v1_funct_1(sK2)
    & v1_relat_1(sK2)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f35,f38,f37,f36])).

fof(f59,plain,
    ( r1_tarski(sK3,k1_relat_1(sK1))
    | r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f39])).

fof(f55,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f56,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f57,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f58,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f60,plain,
    ( r1_tarski(k9_relat_1(sK1,sK3),k1_relat_1(sK2))
    | r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f39])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
          & r1_tarski(X0,k1_relat_1(X2)) )
       => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f30])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f63,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f43])).

fof(f61,plain,
    ( ~ r1_tarski(k9_relat_1(sK1,sK3),k1_relat_1(sK2))
    | ~ r1_tarski(sK3,k1_relat_1(sK1))
    | ~ r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X3)
    | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_182879,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,k10_relat_1(X1,k1_relat_1(sK2)))
    | r1_tarski(k9_relat_1(X0,X2),k9_relat_1(X1,k10_relat_1(X1,k1_relat_1(sK2))))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_210863,plain,
    ( ~ r1_tarski(X0,sK1)
    | r1_tarski(k9_relat_1(X0,sK3),k9_relat_1(sK1,k10_relat_1(sK1,k1_relat_1(sK2))))
    | ~ r1_tarski(sK3,k10_relat_1(sK1,k1_relat_1(sK2)))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_182879])).

cnf(c_210866,plain,
    ( r1_tarski(k9_relat_1(sK1,sK3),k9_relat_1(sK1,k10_relat_1(sK1,k1_relat_1(sK2))))
    | ~ r1_tarski(sK3,k10_relat_1(sK1,k1_relat_1(sK2)))
    | ~ r1_tarski(sK1,sK1)
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_210863])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_153828,plain,
    ( r2_hidden(sK0(k9_relat_1(sK1,sK3),k1_relat_1(sK2)),X0)
    | ~ r2_hidden(sK0(k9_relat_1(sK1,sK3),k1_relat_1(sK2)),k9_relat_1(sK1,sK3))
    | ~ r1_tarski(k9_relat_1(sK1,sK3),X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_170218,plain,
    ( r2_hidden(sK0(k9_relat_1(sK1,sK3),k1_relat_1(sK2)),k9_relat_1(X0,k10_relat_1(X0,k1_relat_1(sK2))))
    | ~ r2_hidden(sK0(k9_relat_1(sK1,sK3),k1_relat_1(sK2)),k9_relat_1(sK1,sK3))
    | ~ r1_tarski(k9_relat_1(sK1,sK3),k9_relat_1(X0,k10_relat_1(X0,k1_relat_1(sK2)))) ),
    inference(instantiation,[status(thm)],[c_153828])).

cnf(c_170220,plain,
    ( r2_hidden(sK0(k9_relat_1(sK1,sK3),k1_relat_1(sK2)),k9_relat_1(sK1,k10_relat_1(sK1,k1_relat_1(sK2))))
    | ~ r2_hidden(sK0(k9_relat_1(sK1,sK3),k1_relat_1(sK2)),k9_relat_1(sK1,sK3))
    | ~ r1_tarski(k9_relat_1(sK1,sK3),k9_relat_1(sK1,k10_relat_1(sK1,k1_relat_1(sK2)))) ),
    inference(instantiation,[status(thm)],[c_170218])).

cnf(c_8128,plain,
    ( ~ r2_hidden(sK0(k9_relat_1(sK1,sK3),k1_relat_1(sK2)),X0)
    | r2_hidden(sK0(k9_relat_1(sK1,sK3),k1_relat_1(sK2)),X1)
    | ~ r1_tarski(X0,X1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_77140,plain,
    ( ~ r2_hidden(sK0(k9_relat_1(sK1,sK3),k1_relat_1(sK2)),X0)
    | r2_hidden(sK0(k9_relat_1(sK1,sK3),k1_relat_1(sK2)),k1_relat_1(sK2))
    | ~ r1_tarski(X0,k1_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_8128])).

cnf(c_135566,plain,
    ( ~ r2_hidden(sK0(k9_relat_1(sK1,sK3),k1_relat_1(sK2)),k9_relat_1(X0,k10_relat_1(X0,k1_relat_1(sK2))))
    | r2_hidden(sK0(k9_relat_1(sK1,sK3),k1_relat_1(sK2)),k1_relat_1(sK2))
    | ~ r1_tarski(k9_relat_1(X0,k10_relat_1(X0,k1_relat_1(sK2))),k1_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_77140])).

cnf(c_135568,plain,
    ( ~ r2_hidden(sK0(k9_relat_1(sK1,sK3),k1_relat_1(sK2)),k9_relat_1(sK1,k10_relat_1(sK1,k1_relat_1(sK2))))
    | r2_hidden(sK0(k9_relat_1(sK1,sK3),k1_relat_1(sK2)),k1_relat_1(sK2))
    | ~ r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,k1_relat_1(sK2))),k1_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_135566])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_16609,plain,
    ( ~ r2_hidden(sK0(X0,k1_relat_1(X1)),k1_relat_1(X1))
    | r1_tarski(X0,k1_relat_1(X1)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_77141,plain,
    ( ~ r2_hidden(sK0(k9_relat_1(sK1,sK3),k1_relat_1(sK2)),k1_relat_1(sK2))
    | r1_tarski(k9_relat_1(sK1,sK3),k1_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_16609])).

cnf(c_14,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X1,X2)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_17,negated_conjecture,
    ( r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2)))
    | r1_tarski(sK3,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1481,plain,
    ( r2_hidden(X0,k1_relat_1(k5_relat_1(sK1,sK2)))
    | ~ r2_hidden(X0,sK3)
    | r1_tarski(sK3,k1_relat_1(sK1)) ),
    inference(resolution,[status(thm)],[c_2,c_17])).

cnf(c_4537,plain,
    ( r2_hidden(X0,k1_relat_1(sK1))
    | ~ r2_hidden(X0,sK3)
    | r1_tarski(sK3,k1_relat_1(sK1))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[status(thm)],[c_14,c_1481])).

cnf(c_21,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_20,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_19,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_18,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_5663,plain,
    ( r2_hidden(X0,k1_relat_1(sK1))
    | ~ r2_hidden(X0,sK3)
    | r1_tarski(sK3,k1_relat_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4537,c_21,c_20,c_19,c_18])).

cnf(c_5672,plain,
    ( r2_hidden(X0,k1_relat_1(sK1))
    | ~ r2_hidden(X0,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5663,c_2])).

cnf(c_5938,plain,
    ( ~ r2_hidden(sK0(X0,k1_relat_1(sK1)),sK3)
    | r1_tarski(X0,k1_relat_1(sK1)) ),
    inference(resolution,[status(thm)],[c_5672,c_0])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_9966,plain,
    ( r1_tarski(sK3,k1_relat_1(sK1)) ),
    inference(resolution,[status(thm)],[c_5938,c_1])).

cnf(c_10,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1193,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,k1_relat_1(X1))),k1_relat_1(X1))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_8307,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,k1_relat_1(sK2))),k1_relat_1(sK2))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_1193])).

cnf(c_8313,plain,
    ( r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,k1_relat_1(sK2))),k1_relat_1(sK2))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_8307])).

cnf(c_379,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1379,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK3,X2)
    | X2 != X1
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_379])).

cnf(c_2322,plain,
    ( ~ r1_tarski(sK3,X0)
    | r1_tarski(sK3,X1)
    | X1 != X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1379])).

cnf(c_4593,plain,
    ( r1_tarski(sK3,X0)
    | ~ r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2)))
    | X0 != k1_relat_1(k5_relat_1(sK1,sK2))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2322])).

cnf(c_7916,plain,
    ( r1_tarski(sK3,k10_relat_1(sK1,k1_relat_1(sK2)))
    | ~ r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2)))
    | k10_relat_1(sK1,k1_relat_1(sK2)) != k1_relat_1(k5_relat_1(sK1,sK2))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_4593])).

cnf(c_16,negated_conjecture,
    ( r1_tarski(k9_relat_1(sK1,sK3),k1_relat_1(sK2))
    | r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_785,plain,
    ( r1_tarski(k9_relat_1(sK1,sK3),k1_relat_1(sK2)) = iProver_top
    | r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_11,plain,
    ( r1_tarski(X0,k10_relat_1(X1,X2))
    | ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ r1_tarski(k9_relat_1(X1,X0),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_790,plain,
    ( r1_tarski(X0,k10_relat_1(X1,X2)) = iProver_top
    | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
    | r1_tarski(k9_relat_1(X1,X0),X2) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4347,plain,
    ( r1_tarski(sK3,k10_relat_1(sK1,k1_relat_1(sK2))) = iProver_top
    | r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2))) = iProver_top
    | r1_tarski(sK3,k1_relat_1(sK1)) != iProver_top
    | v1_funct_1(sK1) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_785,c_790])).

cnf(c_4497,plain,
    ( r1_tarski(sK3,k10_relat_1(sK1,k1_relat_1(sK2)))
    | r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2)))
    | ~ r1_tarski(sK3,k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[status(thm)],[c_11,c_16])).

cnf(c_4403,plain,
    ( r1_tarski(sK3,k10_relat_1(sK1,k1_relat_1(sK2)))
    | r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2)))
    | ~ r1_tarski(sK3,k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4347])).

cnf(c_4656,plain,
    ( r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2)))
    | r1_tarski(sK3,k10_relat_1(sK1,k1_relat_1(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4497,c_21,c_20,c_17,c_4403])).

cnf(c_4657,plain,
    ( r1_tarski(sK3,k10_relat_1(sK1,k1_relat_1(sK2)))
    | r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2))) ),
    inference(renaming,[status(thm)],[c_4656])).

cnf(c_4658,plain,
    ( r1_tarski(sK3,k10_relat_1(sK1,k1_relat_1(sK2))) = iProver_top
    | r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4657])).

cnf(c_5163,plain,
    ( r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2))) = iProver_top
    | r1_tarski(sK3,k10_relat_1(sK1,k1_relat_1(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4347,c_4658])).

cnf(c_5164,plain,
    ( r1_tarski(sK3,k10_relat_1(sK1,k1_relat_1(sK2))) = iProver_top
    | r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2))) = iProver_top ),
    inference(renaming,[status(thm)],[c_5163])).

cnf(c_780,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_782,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X1,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_792,plain,
    ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4022,plain,
    ( k10_relat_1(X0,k1_relat_1(sK2)) = k1_relat_1(k5_relat_1(X0,sK2))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_782,c_792])).

cnf(c_4647,plain,
    ( k10_relat_1(sK1,k1_relat_1(sK2)) = k1_relat_1(k5_relat_1(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_780,c_4022])).

cnf(c_5167,plain,
    ( r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5164,c_4647])).

cnf(c_5169,plain,
    ( r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5167])).

cnf(c_4033,plain,
    ( k10_relat_1(sK1,k1_relat_1(sK2)) = k1_relat_1(k5_relat_1(sK1,sK2))
    | v1_relat_1(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4022])).

cnf(c_377,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1359,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_377])).

cnf(c_1053,plain,
    ( r2_hidden(sK0(k9_relat_1(X0,X1),X2),k9_relat_1(X0,X1))
    | r1_tarski(k9_relat_1(X0,X1),X2) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1164,plain,
    ( r2_hidden(sK0(k9_relat_1(sK1,sK3),k1_relat_1(sK2)),k9_relat_1(sK1,sK3))
    | r1_tarski(k9_relat_1(sK1,sK3),k1_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_1053])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_57,plain,
    ( r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_15,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(sK1,sK3),k1_relat_1(sK2))
    | ~ r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2)))
    | ~ r1_tarski(sK3,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_22,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_210866,c_170220,c_135568,c_77141,c_9966,c_8313,c_7916,c_5169,c_4033,c_1359,c_1164,c_57,c_15,c_20,c_22,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:13:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 51.37/7.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 51.37/7.00  
% 51.37/7.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 51.37/7.00  
% 51.37/7.00  ------  iProver source info
% 51.37/7.00  
% 51.37/7.00  git: date: 2020-06-30 10:37:57 +0100
% 51.37/7.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 51.37/7.00  git: non_committed_changes: false
% 51.37/7.00  git: last_make_outside_of_git: false
% 51.37/7.00  
% 51.37/7.00  ------ 
% 51.37/7.00  ------ Parsing...
% 51.37/7.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 51.37/7.00  
% 51.37/7.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 51.37/7.00  
% 51.37/7.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 51.37/7.00  
% 51.37/7.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 51.37/7.00  ------ Proving...
% 51.37/7.00  ------ Problem Properties 
% 51.37/7.00  
% 51.37/7.00  
% 51.37/7.00  clauses                                 21
% 51.37/7.00  conjectures                             7
% 51.37/7.00  EPR                                     7
% 51.37/7.00  Horn                                    18
% 51.37/7.00  unary                                   5
% 51.37/7.00  binary                                  6
% 51.37/7.00  lits                                    61
% 51.37/7.00  lits eq                                 3
% 51.37/7.00  fd_pure                                 0
% 51.37/7.00  fd_pseudo                               0
% 51.37/7.00  fd_cond                                 0
% 51.37/7.00  fd_pseudo_cond                          1
% 51.37/7.00  AC symbols                              0
% 51.37/7.00  
% 51.37/7.00  ------ Input Options Time Limit: Unbounded
% 51.37/7.00  
% 51.37/7.00  
% 51.37/7.00  ------ 
% 51.37/7.00  Current options:
% 51.37/7.00  ------ 
% 51.37/7.00  
% 51.37/7.00  
% 51.37/7.00  
% 51.37/7.00  
% 51.37/7.00  ------ Proving...
% 51.37/7.00  
% 51.37/7.00  
% 51.37/7.00  % SZS status Theorem for theBenchmark.p
% 51.37/7.00  
% 51.37/7.00  % SZS output start CNFRefutation for theBenchmark.p
% 51.37/7.00  
% 51.37/7.00  fof(f5,axiom,(
% 51.37/7.00    ! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)))))),
% 51.37/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.37/7.00  
% 51.37/7.00  fof(f15,plain,(
% 51.37/7.00    ! [X0,X1,X2] : (! [X3] : ((r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) | (~r1_tarski(X0,X1) | ~r1_tarski(X2,X3))) | ~v1_relat_1(X3)) | ~v1_relat_1(X2))),
% 51.37/7.00    inference(ennf_transformation,[],[f5])).
% 51.37/7.00  
% 51.37/7.00  fof(f16,plain,(
% 51.37/7.00    ! [X0,X1,X2] : (! [X3] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) | ~r1_tarski(X0,X1) | ~r1_tarski(X2,X3) | ~v1_relat_1(X3)) | ~v1_relat_1(X2))),
% 51.37/7.00    inference(flattening,[],[f15])).
% 51.37/7.00  
% 51.37/7.00  fof(f48,plain,(
% 51.37/7.00    ( ! [X2,X0,X3,X1] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) | ~r1_tarski(X0,X1) | ~r1_tarski(X2,X3) | ~v1_relat_1(X3) | ~v1_relat_1(X2)) )),
% 51.37/7.00    inference(cnf_transformation,[],[f16])).
% 51.37/7.00  
% 51.37/7.00  fof(f1,axiom,(
% 51.37/7.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 51.37/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.37/7.00  
% 51.37/7.00  fof(f12,plain,(
% 51.37/7.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 51.37/7.00    inference(ennf_transformation,[],[f1])).
% 51.37/7.00  
% 51.37/7.00  fof(f26,plain,(
% 51.37/7.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 51.37/7.00    inference(nnf_transformation,[],[f12])).
% 51.37/7.00  
% 51.37/7.00  fof(f27,plain,(
% 51.37/7.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 51.37/7.00    inference(rectify,[],[f26])).
% 51.37/7.00  
% 51.37/7.00  fof(f28,plain,(
% 51.37/7.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 51.37/7.00    introduced(choice_axiom,[])).
% 51.37/7.00  
% 51.37/7.00  fof(f29,plain,(
% 51.37/7.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 51.37/7.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).
% 51.37/7.00  
% 51.37/7.00  fof(f40,plain,(
% 51.37/7.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 51.37/7.00    inference(cnf_transformation,[],[f29])).
% 51.37/7.00  
% 51.37/7.00  fof(f42,plain,(
% 51.37/7.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 51.37/7.00    inference(cnf_transformation,[],[f29])).
% 51.37/7.00  
% 51.37/7.00  fof(f9,axiom,(
% 51.37/7.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))))))),
% 51.37/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.37/7.00  
% 51.37/7.00  fof(f22,plain,(
% 51.37/7.00    ! [X0,X1] : (! [X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 51.37/7.00    inference(ennf_transformation,[],[f9])).
% 51.37/7.00  
% 51.37/7.00  fof(f23,plain,(
% 51.37/7.00    ! [X0,X1] : (! [X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 51.37/7.00    inference(flattening,[],[f22])).
% 51.37/7.00  
% 51.37/7.00  fof(f32,plain,(
% 51.37/7.00    ! [X0,X1] : (! [X2] : (((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | (~r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X2)))) & ((r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 51.37/7.00    inference(nnf_transformation,[],[f23])).
% 51.37/7.00  
% 51.37/7.00  fof(f33,plain,(
% 51.37/7.00    ! [X0,X1] : (! [X2] : (((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X2))) & ((r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 51.37/7.00    inference(flattening,[],[f32])).
% 51.37/7.00  
% 51.37/7.00  fof(f52,plain,(
% 51.37/7.00    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 51.37/7.00    inference(cnf_transformation,[],[f33])).
% 51.37/7.00  
% 51.37/7.00  fof(f10,conjecture,(
% 51.37/7.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <=> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))))))),
% 51.37/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.37/7.00  
% 51.37/7.00  fof(f11,negated_conjecture,(
% 51.37/7.00    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <=> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))))))),
% 51.37/7.00    inference(negated_conjecture,[],[f10])).
% 51.37/7.00  
% 51.37/7.00  fof(f24,plain,(
% 51.37/7.00    ? [X0] : (? [X1] : (? [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <~> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0)))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 51.37/7.00    inference(ennf_transformation,[],[f11])).
% 51.37/7.00  
% 51.37/7.00  fof(f25,plain,(
% 51.37/7.00    ? [X0] : (? [X1] : (? [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <~> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0)))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 51.37/7.00    inference(flattening,[],[f24])).
% 51.37/7.00  
% 51.37/7.00  fof(f34,plain,(
% 51.37/7.00    ? [X0] : (? [X1] : (? [X2] : (((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0))) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 51.37/7.00    inference(nnf_transformation,[],[f25])).
% 51.37/7.00  
% 51.37/7.00  fof(f35,plain,(
% 51.37/7.00    ? [X0] : (? [X1] : (? [X2] : ((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 51.37/7.00    inference(flattening,[],[f34])).
% 51.37/7.00  
% 51.37/7.00  fof(f38,plain,(
% 51.37/7.00    ( ! [X0,X1] : (? [X2] : ((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) => ((~r1_tarski(k9_relat_1(X0,sK3),k1_relat_1(X1)) | ~r1_tarski(sK3,k1_relat_1(X0)) | ~r1_tarski(sK3,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,sK3),k1_relat_1(X1)) & r1_tarski(sK3,k1_relat_1(X0))) | r1_tarski(sK3,k1_relat_1(k5_relat_1(X0,X1)))))) )),
% 51.37/7.00    introduced(choice_axiom,[])).
% 51.37/7.00  
% 51.37/7.00  fof(f37,plain,(
% 51.37/7.00    ( ! [X0] : (? [X1] : (? [X2] : ((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) => (? [X2] : ((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(sK2)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,sK2)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(sK2)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,sK2))))) & v1_funct_1(sK2) & v1_relat_1(sK2))) )),
% 51.37/7.00    introduced(choice_axiom,[])).
% 51.37/7.00  
% 51.37/7.00  fof(f36,plain,(
% 51.37/7.00    ? [X0] : (? [X1] : (? [X2] : ((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (? [X2] : ((~r1_tarski(k9_relat_1(sK1,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(sK1)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(sK1,X1)))) & ((r1_tarski(k9_relat_1(sK1,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(sK1))) | r1_tarski(X2,k1_relat_1(k5_relat_1(sK1,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 51.37/7.00    introduced(choice_axiom,[])).
% 51.37/7.00  
% 51.37/7.00  fof(f39,plain,(
% 51.37/7.00    (((~r1_tarski(k9_relat_1(sK1,sK3),k1_relat_1(sK2)) | ~r1_tarski(sK3,k1_relat_1(sK1)) | ~r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2)))) & ((r1_tarski(k9_relat_1(sK1,sK3),k1_relat_1(sK2)) & r1_tarski(sK3,k1_relat_1(sK1))) | r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2))))) & v1_funct_1(sK2) & v1_relat_1(sK2)) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 51.37/7.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f35,f38,f37,f36])).
% 51.37/7.00  
% 51.37/7.00  fof(f59,plain,(
% 51.37/7.00    r1_tarski(sK3,k1_relat_1(sK1)) | r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2)))),
% 51.37/7.00    inference(cnf_transformation,[],[f39])).
% 51.37/7.00  
% 51.37/7.00  fof(f55,plain,(
% 51.37/7.00    v1_relat_1(sK1)),
% 51.37/7.00    inference(cnf_transformation,[],[f39])).
% 51.37/7.00  
% 51.37/7.00  fof(f56,plain,(
% 51.37/7.00    v1_funct_1(sK1)),
% 51.37/7.00    inference(cnf_transformation,[],[f39])).
% 51.37/7.00  
% 51.37/7.00  fof(f57,plain,(
% 51.37/7.00    v1_relat_1(sK2)),
% 51.37/7.00    inference(cnf_transformation,[],[f39])).
% 51.37/7.00  
% 51.37/7.00  fof(f58,plain,(
% 51.37/7.00    v1_funct_1(sK2)),
% 51.37/7.00    inference(cnf_transformation,[],[f39])).
% 51.37/7.00  
% 51.37/7.00  fof(f41,plain,(
% 51.37/7.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 51.37/7.00    inference(cnf_transformation,[],[f29])).
% 51.37/7.00  
% 51.37/7.00  fof(f7,axiom,(
% 51.37/7.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 51.37/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.37/7.00  
% 51.37/7.00  fof(f18,plain,(
% 51.37/7.00    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 51.37/7.00    inference(ennf_transformation,[],[f7])).
% 51.37/7.00  
% 51.37/7.00  fof(f19,plain,(
% 51.37/7.00    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 51.37/7.00    inference(flattening,[],[f18])).
% 51.37/7.00  
% 51.37/7.00  fof(f50,plain,(
% 51.37/7.00    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 51.37/7.00    inference(cnf_transformation,[],[f19])).
% 51.37/7.00  
% 51.37/7.00  fof(f60,plain,(
% 51.37/7.00    r1_tarski(k9_relat_1(sK1,sK3),k1_relat_1(sK2)) | r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2)))),
% 51.37/7.00    inference(cnf_transformation,[],[f39])).
% 51.37/7.00  
% 51.37/7.00  fof(f8,axiom,(
% 51.37/7.00    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 51.37/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.37/7.00  
% 51.37/7.00  fof(f20,plain,(
% 51.37/7.00    ! [X0,X1,X2] : ((r1_tarski(X0,k10_relat_1(X2,X1)) | (~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 51.37/7.00    inference(ennf_transformation,[],[f8])).
% 51.37/7.00  
% 51.37/7.00  fof(f21,plain,(
% 51.37/7.00    ! [X0,X1,X2] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 51.37/7.00    inference(flattening,[],[f20])).
% 51.37/7.00  
% 51.37/7.00  fof(f51,plain,(
% 51.37/7.00    ( ! [X2,X0,X1] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 51.37/7.00    inference(cnf_transformation,[],[f21])).
% 51.37/7.00  
% 51.37/7.00  fof(f6,axiom,(
% 51.37/7.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 51.37/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.37/7.00  
% 51.37/7.00  fof(f17,plain,(
% 51.37/7.00    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 51.37/7.00    inference(ennf_transformation,[],[f6])).
% 51.37/7.00  
% 51.37/7.00  fof(f49,plain,(
% 51.37/7.00    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 51.37/7.00    inference(cnf_transformation,[],[f17])).
% 51.37/7.00  
% 51.37/7.00  fof(f2,axiom,(
% 51.37/7.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 51.37/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.37/7.00  
% 51.37/7.00  fof(f30,plain,(
% 51.37/7.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 51.37/7.00    inference(nnf_transformation,[],[f2])).
% 51.37/7.00  
% 51.37/7.00  fof(f31,plain,(
% 51.37/7.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 51.37/7.00    inference(flattening,[],[f30])).
% 51.37/7.00  
% 51.37/7.00  fof(f43,plain,(
% 51.37/7.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 51.37/7.00    inference(cnf_transformation,[],[f31])).
% 51.37/7.00  
% 51.37/7.00  fof(f63,plain,(
% 51.37/7.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 51.37/7.00    inference(equality_resolution,[],[f43])).
% 51.37/7.00  
% 51.37/7.00  fof(f61,plain,(
% 51.37/7.00    ~r1_tarski(k9_relat_1(sK1,sK3),k1_relat_1(sK2)) | ~r1_tarski(sK3,k1_relat_1(sK1)) | ~r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2)))),
% 51.37/7.00    inference(cnf_transformation,[],[f39])).
% 51.37/7.00  
% 51.37/7.00  cnf(c_8,plain,
% 51.37/7.00      ( ~ r1_tarski(X0,X1)
% 51.37/7.00      | ~ r1_tarski(X2,X3)
% 51.37/7.00      | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1))
% 51.37/7.00      | ~ v1_relat_1(X3)
% 51.37/7.00      | ~ v1_relat_1(X2) ),
% 51.37/7.00      inference(cnf_transformation,[],[f48]) ).
% 51.37/7.00  
% 51.37/7.00  cnf(c_182879,plain,
% 51.37/7.00      ( ~ r1_tarski(X0,X1)
% 51.37/7.00      | ~ r1_tarski(X2,k10_relat_1(X1,k1_relat_1(sK2)))
% 51.37/7.00      | r1_tarski(k9_relat_1(X0,X2),k9_relat_1(X1,k10_relat_1(X1,k1_relat_1(sK2))))
% 51.37/7.00      | ~ v1_relat_1(X0)
% 51.37/7.00      | ~ v1_relat_1(X1) ),
% 51.37/7.00      inference(instantiation,[status(thm)],[c_8]) ).
% 51.37/7.00  
% 51.37/7.00  cnf(c_210863,plain,
% 51.37/7.00      ( ~ r1_tarski(X0,sK1)
% 51.37/7.00      | r1_tarski(k9_relat_1(X0,sK3),k9_relat_1(sK1,k10_relat_1(sK1,k1_relat_1(sK2))))
% 51.37/7.00      | ~ r1_tarski(sK3,k10_relat_1(sK1,k1_relat_1(sK2)))
% 51.37/7.00      | ~ v1_relat_1(X0)
% 51.37/7.00      | ~ v1_relat_1(sK1) ),
% 51.37/7.00      inference(instantiation,[status(thm)],[c_182879]) ).
% 51.37/7.00  
% 51.37/7.00  cnf(c_210866,plain,
% 51.37/7.00      ( r1_tarski(k9_relat_1(sK1,sK3),k9_relat_1(sK1,k10_relat_1(sK1,k1_relat_1(sK2))))
% 51.37/7.00      | ~ r1_tarski(sK3,k10_relat_1(sK1,k1_relat_1(sK2)))
% 51.37/7.00      | ~ r1_tarski(sK1,sK1)
% 51.37/7.00      | ~ v1_relat_1(sK1) ),
% 51.37/7.00      inference(instantiation,[status(thm)],[c_210863]) ).
% 51.37/7.00  
% 51.37/7.00  cnf(c_2,plain,
% 51.37/7.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 51.37/7.00      inference(cnf_transformation,[],[f40]) ).
% 51.37/7.00  
% 51.37/7.00  cnf(c_153828,plain,
% 51.37/7.00      ( r2_hidden(sK0(k9_relat_1(sK1,sK3),k1_relat_1(sK2)),X0)
% 51.37/7.00      | ~ r2_hidden(sK0(k9_relat_1(sK1,sK3),k1_relat_1(sK2)),k9_relat_1(sK1,sK3))
% 51.37/7.00      | ~ r1_tarski(k9_relat_1(sK1,sK3),X0) ),
% 51.37/7.00      inference(instantiation,[status(thm)],[c_2]) ).
% 51.37/7.00  
% 51.37/7.00  cnf(c_170218,plain,
% 51.37/7.00      ( r2_hidden(sK0(k9_relat_1(sK1,sK3),k1_relat_1(sK2)),k9_relat_1(X0,k10_relat_1(X0,k1_relat_1(sK2))))
% 51.37/7.00      | ~ r2_hidden(sK0(k9_relat_1(sK1,sK3),k1_relat_1(sK2)),k9_relat_1(sK1,sK3))
% 51.37/7.00      | ~ r1_tarski(k9_relat_1(sK1,sK3),k9_relat_1(X0,k10_relat_1(X0,k1_relat_1(sK2)))) ),
% 51.37/7.00      inference(instantiation,[status(thm)],[c_153828]) ).
% 51.37/7.00  
% 51.37/7.00  cnf(c_170220,plain,
% 51.37/7.00      ( r2_hidden(sK0(k9_relat_1(sK1,sK3),k1_relat_1(sK2)),k9_relat_1(sK1,k10_relat_1(sK1,k1_relat_1(sK2))))
% 51.37/7.00      | ~ r2_hidden(sK0(k9_relat_1(sK1,sK3),k1_relat_1(sK2)),k9_relat_1(sK1,sK3))
% 51.37/7.00      | ~ r1_tarski(k9_relat_1(sK1,sK3),k9_relat_1(sK1,k10_relat_1(sK1,k1_relat_1(sK2)))) ),
% 51.37/7.00      inference(instantiation,[status(thm)],[c_170218]) ).
% 51.37/7.00  
% 51.37/7.00  cnf(c_8128,plain,
% 51.37/7.00      ( ~ r2_hidden(sK0(k9_relat_1(sK1,sK3),k1_relat_1(sK2)),X0)
% 51.37/7.00      | r2_hidden(sK0(k9_relat_1(sK1,sK3),k1_relat_1(sK2)),X1)
% 51.37/7.00      | ~ r1_tarski(X0,X1) ),
% 51.37/7.00      inference(instantiation,[status(thm)],[c_2]) ).
% 51.37/7.00  
% 51.37/7.00  cnf(c_77140,plain,
% 51.37/7.00      ( ~ r2_hidden(sK0(k9_relat_1(sK1,sK3),k1_relat_1(sK2)),X0)
% 51.37/7.00      | r2_hidden(sK0(k9_relat_1(sK1,sK3),k1_relat_1(sK2)),k1_relat_1(sK2))
% 51.37/7.00      | ~ r1_tarski(X0,k1_relat_1(sK2)) ),
% 51.37/7.00      inference(instantiation,[status(thm)],[c_8128]) ).
% 51.37/7.00  
% 51.37/7.00  cnf(c_135566,plain,
% 51.37/7.00      ( ~ r2_hidden(sK0(k9_relat_1(sK1,sK3),k1_relat_1(sK2)),k9_relat_1(X0,k10_relat_1(X0,k1_relat_1(sK2))))
% 51.37/7.00      | r2_hidden(sK0(k9_relat_1(sK1,sK3),k1_relat_1(sK2)),k1_relat_1(sK2))
% 51.37/7.00      | ~ r1_tarski(k9_relat_1(X0,k10_relat_1(X0,k1_relat_1(sK2))),k1_relat_1(sK2)) ),
% 51.37/7.00      inference(instantiation,[status(thm)],[c_77140]) ).
% 51.37/7.00  
% 51.37/7.00  cnf(c_135568,plain,
% 51.37/7.00      ( ~ r2_hidden(sK0(k9_relat_1(sK1,sK3),k1_relat_1(sK2)),k9_relat_1(sK1,k10_relat_1(sK1,k1_relat_1(sK2))))
% 51.37/7.00      | r2_hidden(sK0(k9_relat_1(sK1,sK3),k1_relat_1(sK2)),k1_relat_1(sK2))
% 51.37/7.00      | ~ r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,k1_relat_1(sK2))),k1_relat_1(sK2)) ),
% 51.37/7.00      inference(instantiation,[status(thm)],[c_135566]) ).
% 51.37/7.00  
% 51.37/7.00  cnf(c_0,plain,
% 51.37/7.00      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 51.37/7.00      inference(cnf_transformation,[],[f42]) ).
% 51.37/7.00  
% 51.37/7.00  cnf(c_16609,plain,
% 51.37/7.00      ( ~ r2_hidden(sK0(X0,k1_relat_1(X1)),k1_relat_1(X1))
% 51.37/7.00      | r1_tarski(X0,k1_relat_1(X1)) ),
% 51.37/7.00      inference(instantiation,[status(thm)],[c_0]) ).
% 51.37/7.00  
% 51.37/7.00  cnf(c_77141,plain,
% 51.37/7.00      ( ~ r2_hidden(sK0(k9_relat_1(sK1,sK3),k1_relat_1(sK2)),k1_relat_1(sK2))
% 51.37/7.00      | r1_tarski(k9_relat_1(sK1,sK3),k1_relat_1(sK2)) ),
% 51.37/7.00      inference(instantiation,[status(thm)],[c_16609]) ).
% 51.37/7.00  
% 51.37/7.00  cnf(c_14,plain,
% 51.37/7.00      ( r2_hidden(X0,k1_relat_1(X1))
% 51.37/7.00      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X1,X2)))
% 51.37/7.00      | ~ v1_funct_1(X2)
% 51.37/7.00      | ~ v1_funct_1(X1)
% 51.37/7.00      | ~ v1_relat_1(X1)
% 51.37/7.00      | ~ v1_relat_1(X2) ),
% 51.37/7.00      inference(cnf_transformation,[],[f52]) ).
% 51.37/7.00  
% 51.37/7.00  cnf(c_17,negated_conjecture,
% 51.37/7.00      ( r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2)))
% 51.37/7.00      | r1_tarski(sK3,k1_relat_1(sK1)) ),
% 51.37/7.00      inference(cnf_transformation,[],[f59]) ).
% 51.37/7.00  
% 51.37/7.00  cnf(c_1481,plain,
% 51.37/7.00      ( r2_hidden(X0,k1_relat_1(k5_relat_1(sK1,sK2)))
% 51.37/7.00      | ~ r2_hidden(X0,sK3)
% 51.37/7.00      | r1_tarski(sK3,k1_relat_1(sK1)) ),
% 51.37/7.00      inference(resolution,[status(thm)],[c_2,c_17]) ).
% 51.37/7.00  
% 51.37/7.00  cnf(c_4537,plain,
% 51.37/7.00      ( r2_hidden(X0,k1_relat_1(sK1))
% 51.37/7.00      | ~ r2_hidden(X0,sK3)
% 51.37/7.00      | r1_tarski(sK3,k1_relat_1(sK1))
% 51.37/7.00      | ~ v1_funct_1(sK2)
% 51.37/7.00      | ~ v1_funct_1(sK1)
% 51.37/7.00      | ~ v1_relat_1(sK2)
% 51.37/7.00      | ~ v1_relat_1(sK1) ),
% 51.37/7.00      inference(resolution,[status(thm)],[c_14,c_1481]) ).
% 51.37/7.00  
% 51.37/7.00  cnf(c_21,negated_conjecture,
% 51.37/7.00      ( v1_relat_1(sK1) ),
% 51.37/7.00      inference(cnf_transformation,[],[f55]) ).
% 51.37/7.00  
% 51.37/7.00  cnf(c_20,negated_conjecture,
% 51.37/7.00      ( v1_funct_1(sK1) ),
% 51.37/7.00      inference(cnf_transformation,[],[f56]) ).
% 51.37/7.00  
% 51.37/7.00  cnf(c_19,negated_conjecture,
% 51.37/7.00      ( v1_relat_1(sK2) ),
% 51.37/7.00      inference(cnf_transformation,[],[f57]) ).
% 51.37/7.00  
% 51.37/7.00  cnf(c_18,negated_conjecture,
% 51.37/7.00      ( v1_funct_1(sK2) ),
% 51.37/7.00      inference(cnf_transformation,[],[f58]) ).
% 51.37/7.00  
% 51.37/7.00  cnf(c_5663,plain,
% 51.37/7.00      ( r2_hidden(X0,k1_relat_1(sK1))
% 51.37/7.00      | ~ r2_hidden(X0,sK3)
% 51.37/7.00      | r1_tarski(sK3,k1_relat_1(sK1)) ),
% 51.37/7.00      inference(global_propositional_subsumption,
% 51.37/7.00                [status(thm)],
% 51.37/7.00                [c_4537,c_21,c_20,c_19,c_18]) ).
% 51.37/7.00  
% 51.37/7.00  cnf(c_5672,plain,
% 51.37/7.00      ( r2_hidden(X0,k1_relat_1(sK1)) | ~ r2_hidden(X0,sK3) ),
% 51.37/7.00      inference(forward_subsumption_resolution,
% 51.37/7.00                [status(thm)],
% 51.37/7.00                [c_5663,c_2]) ).
% 51.37/7.00  
% 51.37/7.00  cnf(c_5938,plain,
% 51.37/7.00      ( ~ r2_hidden(sK0(X0,k1_relat_1(sK1)),sK3)
% 51.37/7.00      | r1_tarski(X0,k1_relat_1(sK1)) ),
% 51.37/7.00      inference(resolution,[status(thm)],[c_5672,c_0]) ).
% 51.37/7.00  
% 51.37/7.00  cnf(c_1,plain,
% 51.37/7.00      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 51.37/7.00      inference(cnf_transformation,[],[f41]) ).
% 51.37/7.00  
% 51.37/7.00  cnf(c_9966,plain,
% 51.37/7.00      ( r1_tarski(sK3,k1_relat_1(sK1)) ),
% 51.37/7.00      inference(resolution,[status(thm)],[c_5938,c_1]) ).
% 51.37/7.00  
% 51.37/7.00  cnf(c_10,plain,
% 51.37/7.00      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
% 51.37/7.00      | ~ v1_funct_1(X0)
% 51.37/7.00      | ~ v1_relat_1(X0) ),
% 51.37/7.00      inference(cnf_transformation,[],[f50]) ).
% 51.37/7.00  
% 51.37/7.00  cnf(c_1193,plain,
% 51.37/7.00      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,k1_relat_1(X1))),k1_relat_1(X1))
% 51.37/7.00      | ~ v1_funct_1(X0)
% 51.37/7.00      | ~ v1_relat_1(X0) ),
% 51.37/7.00      inference(instantiation,[status(thm)],[c_10]) ).
% 51.37/7.00  
% 51.37/7.00  cnf(c_8307,plain,
% 51.37/7.00      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,k1_relat_1(sK2))),k1_relat_1(sK2))
% 51.37/7.00      | ~ v1_funct_1(X0)
% 51.37/7.00      | ~ v1_relat_1(X0) ),
% 51.37/7.00      inference(instantiation,[status(thm)],[c_1193]) ).
% 51.37/7.00  
% 51.37/7.00  cnf(c_8313,plain,
% 51.37/7.00      ( r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,k1_relat_1(sK2))),k1_relat_1(sK2))
% 51.37/7.00      | ~ v1_funct_1(sK1)
% 51.37/7.00      | ~ v1_relat_1(sK1) ),
% 51.37/7.00      inference(instantiation,[status(thm)],[c_8307]) ).
% 51.37/7.00  
% 51.37/7.00  cnf(c_379,plain,
% 51.37/7.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 51.37/7.00      theory(equality) ).
% 51.37/7.00  
% 51.37/7.00  cnf(c_1379,plain,
% 51.37/7.00      ( ~ r1_tarski(X0,X1) | r1_tarski(sK3,X2) | X2 != X1 | sK3 != X0 ),
% 51.37/7.00      inference(instantiation,[status(thm)],[c_379]) ).
% 51.37/7.00  
% 51.37/7.00  cnf(c_2322,plain,
% 51.37/7.00      ( ~ r1_tarski(sK3,X0) | r1_tarski(sK3,X1) | X1 != X0 | sK3 != sK3 ),
% 51.37/7.00      inference(instantiation,[status(thm)],[c_1379]) ).
% 51.37/7.00  
% 51.37/7.00  cnf(c_4593,plain,
% 51.37/7.00      ( r1_tarski(sK3,X0)
% 51.37/7.00      | ~ r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2)))
% 51.37/7.00      | X0 != k1_relat_1(k5_relat_1(sK1,sK2))
% 51.37/7.00      | sK3 != sK3 ),
% 51.37/7.00      inference(instantiation,[status(thm)],[c_2322]) ).
% 51.37/7.00  
% 51.37/7.00  cnf(c_7916,plain,
% 51.37/7.00      ( r1_tarski(sK3,k10_relat_1(sK1,k1_relat_1(sK2)))
% 51.37/7.00      | ~ r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2)))
% 51.37/7.00      | k10_relat_1(sK1,k1_relat_1(sK2)) != k1_relat_1(k5_relat_1(sK1,sK2))
% 51.37/7.00      | sK3 != sK3 ),
% 51.37/7.00      inference(instantiation,[status(thm)],[c_4593]) ).
% 51.37/7.00  
% 51.37/7.00  cnf(c_16,negated_conjecture,
% 51.37/7.00      ( r1_tarski(k9_relat_1(sK1,sK3),k1_relat_1(sK2))
% 51.37/7.00      | r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2))) ),
% 51.37/7.00      inference(cnf_transformation,[],[f60]) ).
% 51.37/7.00  
% 51.37/7.00  cnf(c_785,plain,
% 51.37/7.00      ( r1_tarski(k9_relat_1(sK1,sK3),k1_relat_1(sK2)) = iProver_top
% 51.37/7.00      | r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2))) = iProver_top ),
% 51.37/7.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 51.37/7.00  
% 51.37/7.00  cnf(c_11,plain,
% 51.37/7.00      ( r1_tarski(X0,k10_relat_1(X1,X2))
% 51.37/7.00      | ~ r1_tarski(X0,k1_relat_1(X1))
% 51.37/7.00      | ~ r1_tarski(k9_relat_1(X1,X0),X2)
% 51.37/7.00      | ~ v1_funct_1(X1)
% 51.37/7.00      | ~ v1_relat_1(X1) ),
% 51.37/7.00      inference(cnf_transformation,[],[f51]) ).
% 51.37/7.00  
% 51.37/7.00  cnf(c_790,plain,
% 51.37/7.00      ( r1_tarski(X0,k10_relat_1(X1,X2)) = iProver_top
% 51.37/7.00      | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
% 51.37/7.00      | r1_tarski(k9_relat_1(X1,X0),X2) != iProver_top
% 51.37/7.00      | v1_funct_1(X1) != iProver_top
% 51.37/7.00      | v1_relat_1(X1) != iProver_top ),
% 51.37/7.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 51.37/7.00  
% 51.37/7.00  cnf(c_4347,plain,
% 51.37/7.00      ( r1_tarski(sK3,k10_relat_1(sK1,k1_relat_1(sK2))) = iProver_top
% 51.37/7.00      | r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2))) = iProver_top
% 51.37/7.00      | r1_tarski(sK3,k1_relat_1(sK1)) != iProver_top
% 51.37/7.00      | v1_funct_1(sK1) != iProver_top
% 51.37/7.00      | v1_relat_1(sK1) != iProver_top ),
% 51.37/7.00      inference(superposition,[status(thm)],[c_785,c_790]) ).
% 51.37/7.00  
% 51.37/7.00  cnf(c_4497,plain,
% 51.37/7.00      ( r1_tarski(sK3,k10_relat_1(sK1,k1_relat_1(sK2)))
% 51.37/7.00      | r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2)))
% 51.37/7.00      | ~ r1_tarski(sK3,k1_relat_1(sK1))
% 51.37/7.00      | ~ v1_funct_1(sK1)
% 51.37/7.00      | ~ v1_relat_1(sK1) ),
% 51.37/7.00      inference(resolution,[status(thm)],[c_11,c_16]) ).
% 51.37/7.00  
% 51.37/7.00  cnf(c_4403,plain,
% 51.37/7.00      ( r1_tarski(sK3,k10_relat_1(sK1,k1_relat_1(sK2)))
% 51.37/7.00      | r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2)))
% 51.37/7.00      | ~ r1_tarski(sK3,k1_relat_1(sK1))
% 51.37/7.00      | ~ v1_funct_1(sK1)
% 51.37/7.00      | ~ v1_relat_1(sK1) ),
% 51.37/7.00      inference(predicate_to_equality_rev,[status(thm)],[c_4347]) ).
% 51.37/7.00  
% 51.37/7.00  cnf(c_4656,plain,
% 51.37/7.00      ( r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2)))
% 51.37/7.00      | r1_tarski(sK3,k10_relat_1(sK1,k1_relat_1(sK2))) ),
% 51.37/7.00      inference(global_propositional_subsumption,
% 51.37/7.00                [status(thm)],
% 51.37/7.00                [c_4497,c_21,c_20,c_17,c_4403]) ).
% 51.37/7.00  
% 51.37/7.00  cnf(c_4657,plain,
% 51.37/7.00      ( r1_tarski(sK3,k10_relat_1(sK1,k1_relat_1(sK2)))
% 51.37/7.00      | r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2))) ),
% 51.37/7.00      inference(renaming,[status(thm)],[c_4656]) ).
% 51.37/7.00  
% 51.37/7.00  cnf(c_4658,plain,
% 51.37/7.00      ( r1_tarski(sK3,k10_relat_1(sK1,k1_relat_1(sK2))) = iProver_top
% 51.37/7.00      | r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2))) = iProver_top ),
% 51.37/7.00      inference(predicate_to_equality,[status(thm)],[c_4657]) ).
% 51.37/7.00  
% 51.37/7.00  cnf(c_5163,plain,
% 51.37/7.00      ( r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2))) = iProver_top
% 51.37/7.00      | r1_tarski(sK3,k10_relat_1(sK1,k1_relat_1(sK2))) = iProver_top ),
% 51.37/7.00      inference(global_propositional_subsumption,
% 51.37/7.00                [status(thm)],
% 51.37/7.00                [c_4347,c_4658]) ).
% 51.37/7.00  
% 51.37/7.00  cnf(c_5164,plain,
% 51.37/7.00      ( r1_tarski(sK3,k10_relat_1(sK1,k1_relat_1(sK2))) = iProver_top
% 51.37/7.00      | r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2))) = iProver_top ),
% 51.37/7.00      inference(renaming,[status(thm)],[c_5163]) ).
% 51.37/7.00  
% 51.37/7.00  cnf(c_780,plain,
% 51.37/7.00      ( v1_relat_1(sK1) = iProver_top ),
% 51.37/7.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 51.37/7.00  
% 51.37/7.00  cnf(c_782,plain,
% 51.37/7.00      ( v1_relat_1(sK2) = iProver_top ),
% 51.37/7.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 51.37/7.00  
% 51.37/7.00  cnf(c_9,plain,
% 51.37/7.00      ( ~ v1_relat_1(X0)
% 51.37/7.00      | ~ v1_relat_1(X1)
% 51.37/7.00      | k10_relat_1(X1,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(X1,X0)) ),
% 51.37/7.00      inference(cnf_transformation,[],[f49]) ).
% 51.37/7.00  
% 51.37/7.00  cnf(c_792,plain,
% 51.37/7.00      ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
% 51.37/7.00      | v1_relat_1(X0) != iProver_top
% 51.37/7.00      | v1_relat_1(X1) != iProver_top ),
% 51.37/7.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 51.37/7.00  
% 51.37/7.00  cnf(c_4022,plain,
% 51.37/7.00      ( k10_relat_1(X0,k1_relat_1(sK2)) = k1_relat_1(k5_relat_1(X0,sK2))
% 51.37/7.00      | v1_relat_1(X0) != iProver_top ),
% 51.37/7.00      inference(superposition,[status(thm)],[c_782,c_792]) ).
% 51.37/7.00  
% 51.37/7.00  cnf(c_4647,plain,
% 51.37/7.00      ( k10_relat_1(sK1,k1_relat_1(sK2)) = k1_relat_1(k5_relat_1(sK1,sK2)) ),
% 51.37/7.00      inference(superposition,[status(thm)],[c_780,c_4022]) ).
% 51.37/7.00  
% 51.37/7.00  cnf(c_5167,plain,
% 51.37/7.00      ( r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2))) = iProver_top ),
% 51.37/7.00      inference(light_normalisation,[status(thm)],[c_5164,c_4647]) ).
% 51.37/7.00  
% 51.37/7.00  cnf(c_5169,plain,
% 51.37/7.00      ( r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2))) ),
% 51.37/7.00      inference(predicate_to_equality_rev,[status(thm)],[c_5167]) ).
% 51.37/7.00  
% 51.37/7.00  cnf(c_4033,plain,
% 51.37/7.00      ( k10_relat_1(sK1,k1_relat_1(sK2)) = k1_relat_1(k5_relat_1(sK1,sK2))
% 51.37/7.00      | v1_relat_1(sK1) != iProver_top ),
% 51.37/7.00      inference(instantiation,[status(thm)],[c_4022]) ).
% 51.37/7.00  
% 51.37/7.00  cnf(c_377,plain,( X0 = X0 ),theory(equality) ).
% 51.37/7.00  
% 51.37/7.00  cnf(c_1359,plain,
% 51.37/7.00      ( sK3 = sK3 ),
% 51.37/7.00      inference(instantiation,[status(thm)],[c_377]) ).
% 51.37/7.00  
% 51.37/7.00  cnf(c_1053,plain,
% 51.37/7.00      ( r2_hidden(sK0(k9_relat_1(X0,X1),X2),k9_relat_1(X0,X1))
% 51.37/7.00      | r1_tarski(k9_relat_1(X0,X1),X2) ),
% 51.37/7.00      inference(instantiation,[status(thm)],[c_1]) ).
% 51.37/7.00  
% 51.37/7.00  cnf(c_1164,plain,
% 51.37/7.00      ( r2_hidden(sK0(k9_relat_1(sK1,sK3),k1_relat_1(sK2)),k9_relat_1(sK1,sK3))
% 51.37/7.00      | r1_tarski(k9_relat_1(sK1,sK3),k1_relat_1(sK2)) ),
% 51.37/7.00      inference(instantiation,[status(thm)],[c_1053]) ).
% 51.37/7.00  
% 51.37/7.00  cnf(c_5,plain,
% 51.37/7.00      ( r1_tarski(X0,X0) ),
% 51.37/7.00      inference(cnf_transformation,[],[f63]) ).
% 51.37/7.00  
% 51.37/7.00  cnf(c_57,plain,
% 51.37/7.00      ( r1_tarski(sK1,sK1) ),
% 51.37/7.00      inference(instantiation,[status(thm)],[c_5]) ).
% 51.37/7.00  
% 51.37/7.00  cnf(c_15,negated_conjecture,
% 51.37/7.00      ( ~ r1_tarski(k9_relat_1(sK1,sK3),k1_relat_1(sK2))
% 51.37/7.00      | ~ r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2)))
% 51.37/7.00      | ~ r1_tarski(sK3,k1_relat_1(sK1)) ),
% 51.37/7.00      inference(cnf_transformation,[],[f61]) ).
% 51.37/7.00  
% 51.37/7.00  cnf(c_22,plain,
% 51.37/7.00      ( v1_relat_1(sK1) = iProver_top ),
% 51.37/7.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 51.37/7.00  
% 51.37/7.00  cnf(contradiction,plain,
% 51.37/7.00      ( $false ),
% 51.37/7.00      inference(minisat,
% 51.37/7.00                [status(thm)],
% 51.37/7.00                [c_210866,c_170220,c_135568,c_77141,c_9966,c_8313,c_7916,
% 51.37/7.00                 c_5169,c_4033,c_1359,c_1164,c_57,c_15,c_20,c_22,c_21]) ).
% 51.37/7.00  
% 51.37/7.00  
% 51.37/7.00  % SZS output end CNFRefutation for theBenchmark.p
% 51.37/7.00  
% 51.37/7.00  ------                               Statistics
% 51.37/7.00  
% 51.37/7.00  ------ Selected
% 51.37/7.00  
% 51.37/7.00  total_time:                             6.38
% 51.37/7.00  
%------------------------------------------------------------------------------
