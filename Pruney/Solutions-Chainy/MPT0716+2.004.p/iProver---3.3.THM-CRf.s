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
% DateTime   : Thu Dec  3 11:52:52 EST 2020

% Result     : Theorem 23.56s
% Output     : CNFRefutation 23.56s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 629 expanded)
%              Number of clauses        :   84 ( 169 expanded)
%              Number of leaves         :   19 ( 162 expanded)
%              Depth                    :   20
%              Number of atoms          :  488 (4319 expanded)
%              Number of equality atoms :  146 ( 267 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f15,conjecture,(
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

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f36])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
            | ~ r1_tarski(X2,k1_relat_1(X0))
            | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) )
          & ( ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
              & r1_tarski(X2,k1_relat_1(X0)) )
            | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) ) )
     => ( ( ~ r1_tarski(k9_relat_1(X0,sK2),k1_relat_1(X1))
          | ~ r1_tarski(sK2,k1_relat_1(X0))
          | ~ r1_tarski(sK2,k1_relat_1(k5_relat_1(X0,X1))) )
        & ( ( r1_tarski(k9_relat_1(X0,sK2),k1_relat_1(X1))
            & r1_tarski(sK2,k1_relat_1(X0)) )
          | r1_tarski(sK2,k1_relat_1(k5_relat_1(X0,X1))) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
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
            ( ( ~ r1_tarski(k9_relat_1(X0,X2),k1_relat_1(sK1))
              | ~ r1_tarski(X2,k1_relat_1(X0))
              | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(X0,sK1))) )
            & ( ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(sK1))
                & r1_tarski(X2,k1_relat_1(X0)) )
              | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,sK1))) ) )
        & v1_funct_1(sK1)
        & v1_relat_1(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
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
              ( ( ~ r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(X1))
                | ~ r1_tarski(X2,k1_relat_1(sK0))
                | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,X1))) )
              & ( ( r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(X1))
                  & r1_tarski(X2,k1_relat_1(sK0)) )
                | r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,X1))) ) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ( ~ r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
      | ~ r1_tarski(sK2,k1_relat_1(sK0))
      | ~ r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) )
    & ( ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
        & r1_tarski(sK2,k1_relat_1(sK0)) )
      | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) )
    & v1_funct_1(sK1)
    & v1_relat_1(sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f40,f43,f42,f41])).

fof(f64,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f62,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f67,plain,
    ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f44])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
          & r1_tarski(X0,k1_relat_1(X2)) )
       => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f63,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f66,plain,
    ( r1_tarski(sK2,k1_relat_1(sK0))
    | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f44])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k5_relat_1(k7_relat_1(X1,X0),X2) = k7_relat_1(k5_relat_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k5_relat_1(k7_relat_1(X1,X0),X2) = k7_relat_1(k5_relat_1(X1,X2),X0)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k7_relat_1(X1,X0),X2) = k7_relat_1(k5_relat_1(X1,X2),X0)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f18,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,X0))
           => r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
      | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f37])).

fof(f47,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f70,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f45])).

fof(f68,plain,
    ( ~ r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | ~ r1_tarski(sK2,k1_relat_1(sK0))
    | ~ r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f44])).

fof(f65,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_13,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k7_relat_1(X0,X1))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_109811,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k7_relat_1(X0,sK2))
    | ~ v1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_109813,plain,
    ( v1_funct_1(k7_relat_1(sK0,sK2))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_109811])).

cnf(c_417,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1016,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,k1_relat_1(X3))
    | X2 != X0
    | k1_relat_1(X3) != X1 ),
    inference(instantiation,[status(thm)],[c_417])).

cnf(c_1097,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | r1_tarski(X2,k1_relat_1(X1))
    | X2 != X0
    | k1_relat_1(X1) != k1_relat_1(X1) ),
    inference(instantiation,[status(thm)],[c_1016])).

cnf(c_1256,plain,
    ( r1_tarski(X0,k1_relat_1(X1))
    | ~ r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),k1_relat_1(X1))
    | X0 != k1_relat_1(k7_relat_1(X1,X2))
    | k1_relat_1(X1) != k1_relat_1(X1) ),
    inference(instantiation,[status(thm)],[c_1097])).

cnf(c_13303,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(X0,sK2)),k1_relat_1(X0))
    | r1_tarski(sK2,k1_relat_1(X0))
    | k1_relat_1(X0) != k1_relat_1(X0)
    | sK2 != k1_relat_1(k7_relat_1(X0,sK2)) ),
    inference(instantiation,[status(thm)],[c_1256])).

cnf(c_13305,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0))
    | r1_tarski(sK2,k1_relat_1(sK0))
    | k1_relat_1(sK0) != k1_relat_1(sK0)
    | sK2 != k1_relat_1(k7_relat_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_13303])).

cnf(c_21,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_800,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_23,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_798,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X1,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_813,plain,
    ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2946,plain,
    ( k10_relat_1(sK0,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(sK0,X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_798,c_813])).

cnf(c_3424,plain,
    ( k10_relat_1(sK0,k1_relat_1(sK1)) = k1_relat_1(k5_relat_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_800,c_2946])).

cnf(c_18,negated_conjecture,
    ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_803,plain,
    ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) = iProver_top
    | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_15,plain,
    ( r1_tarski(X0,k10_relat_1(X1,X2))
    | ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ r1_tarski(k9_relat_1(X1,X0),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_806,plain,
    ( r1_tarski(X0,k10_relat_1(X1,X2)) = iProver_top
    | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
    | r1_tarski(k9_relat_1(X1,X0),X2) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1771,plain,
    ( r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) = iProver_top
    | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top
    | r1_tarski(sK2,k1_relat_1(sK0)) != iProver_top
    | v1_funct_1(sK0) != iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_803,c_806])).

cnf(c_24,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_22,negated_conjecture,
    ( v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_25,plain,
    ( v1_funct_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_19,negated_conjecture,
    ( r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))
    | r1_tarski(sK2,k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_28,plain,
    ( r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top
    | r1_tarski(sK2,k1_relat_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2559,plain,
    ( r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top
    | r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1771,c_24,c_25,c_28])).

cnf(c_2560,plain,
    ( r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) = iProver_top
    | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top ),
    inference(renaming,[status(thm)],[c_2559])).

cnf(c_3447,plain,
    ( r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3424,c_2560])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_809,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_5153,plain,
    ( k1_relat_1(k7_relat_1(k5_relat_1(sK0,sK1),sK2)) = sK2
    | v1_relat_1(k5_relat_1(sK0,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3447,c_809])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k7_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(k7_relat_1(X0,X2),X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_815,plain,
    ( k7_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(k7_relat_1(X0,X2),X1)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2986,plain,
    ( k7_relat_1(k5_relat_1(sK0,X0),X1) = k5_relat_1(k7_relat_1(sK0,X1),X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_798,c_815])).

cnf(c_4601,plain,
    ( k7_relat_1(k5_relat_1(sK0,sK1),X0) = k5_relat_1(k7_relat_1(sK0,X0),sK1) ),
    inference(superposition,[status(thm)],[c_800,c_2986])).

cnf(c_5156,plain,
    ( k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1)) = sK2
    | v1_relat_1(k5_relat_1(sK0,sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5153,c_4601])).

cnf(c_26,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1112,plain,
    ( v1_relat_1(k5_relat_1(sK0,sK1))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1113,plain,
    ( v1_relat_1(k5_relat_1(sK0,sK1)) = iProver_top
    | v1_relat_1(sK1) != iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1112])).

cnf(c_9301,plain,
    ( k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5156,c_24,c_26,c_1113])).

cnf(c_16,plain,
    ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k1_relat_1(k5_relat_1(X0,X1)) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_805,plain,
    ( k1_relat_1(k5_relat_1(X0,X1)) != k1_relat_1(X0)
    | r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_9305,plain,
    ( k1_relat_1(k7_relat_1(sK0,sK2)) != sK2
    | r1_tarski(k2_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1)) = iProver_top
    | v1_funct_1(k7_relat_1(sK0,sK2)) != iProver_top
    | v1_funct_1(sK1) != iProver_top
    | v1_relat_1(k7_relat_1(sK0,sK2)) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_9301,c_805])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_814,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1547,plain,
    ( k2_relat_1(k7_relat_1(sK0,X0)) = k9_relat_1(sK0,X0) ),
    inference(superposition,[status(thm)],[c_798,c_814])).

cnf(c_9331,plain,
    ( k1_relat_1(k7_relat_1(sK0,sK2)) != sK2
    | r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) = iProver_top
    | v1_funct_1(k7_relat_1(sK0,sK2)) != iProver_top
    | v1_funct_1(sK1) != iProver_top
    | v1_relat_1(k7_relat_1(sK0,sK2)) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9305,c_1547])).

cnf(c_9354,plain,
    ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | ~ v1_funct_1(k7_relat_1(sK0,sK2))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(k7_relat_1(sK0,sK2))
    | ~ v1_relat_1(sK1)
    | k1_relat_1(k7_relat_1(sK0,sK2)) != sK2 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_9331])).

cnf(c_8,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_812,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_9304,plain,
    ( r1_tarski(sK2,k1_relat_1(k7_relat_1(sK0,sK2))) = iProver_top
    | v1_relat_1(k7_relat_1(sK0,sK2)) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_9301,c_812])).

cnf(c_10,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),k1_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_8462,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,sK2)),k1_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_8464,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0))
    | ~ v1_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_8462])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_8329,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,sK2)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_8330,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k7_relat_1(X0,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8329])).

cnf(c_8332,plain,
    ( v1_relat_1(k7_relat_1(sK0,sK2)) = iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_8330])).

cnf(c_8331,plain,
    ( v1_relat_1(k7_relat_1(sK0,sK2))
    | ~ v1_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_8329])).

cnf(c_3448,plain,
    ( r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3447])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1693,plain,
    ( ~ r1_tarski(X0,sK2)
    | ~ r1_tarski(sK2,X0)
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_3081,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(X0,sK2)),sK2)
    | ~ r1_tarski(sK2,k1_relat_1(k7_relat_1(X0,sK2)))
    | sK2 = k1_relat_1(k7_relat_1(X0,sK2)) ),
    inference(instantiation,[status(thm)],[c_1693])).

cnf(c_3082,plain,
    ( sK2 = k1_relat_1(k7_relat_1(X0,sK2))
    | r1_tarski(k1_relat_1(k7_relat_1(X0,sK2)),sK2) != iProver_top
    | r1_tarski(sK2,k1_relat_1(k7_relat_1(X0,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3081])).

cnf(c_3084,plain,
    ( sK2 = k1_relat_1(k7_relat_1(sK0,sK2))
    | r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),sK2) != iProver_top
    | r1_tarski(sK2,k1_relat_1(k7_relat_1(sK0,sK2))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3082])).

cnf(c_1488,plain,
    ( ~ r1_tarski(X0,sK2)
    | ~ r1_tarski(sK2,X0)
    | X0 = sK2 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1757,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(X0,sK2)),sK2)
    | ~ r1_tarski(sK2,k1_relat_1(k7_relat_1(X0,sK2)))
    | k1_relat_1(k7_relat_1(X0,sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_1488])).

cnf(c_1758,plain,
    ( k1_relat_1(k7_relat_1(X0,sK2)) = sK2
    | r1_tarski(k1_relat_1(k7_relat_1(X0,sK2)),sK2) != iProver_top
    | r1_tarski(sK2,k1_relat_1(k7_relat_1(X0,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1757])).

cnf(c_1760,plain,
    ( k1_relat_1(k7_relat_1(sK0,sK2)) = sK2
    | r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),sK2) != iProver_top
    | r1_tarski(sK2,k1_relat_1(k7_relat_1(sK0,sK2))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1758])).

cnf(c_9,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1190,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,sK2)),sK2)
    | ~ v1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1195,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,sK2)),sK2) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1190])).

cnf(c_1197,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),sK2) = iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1195])).

cnf(c_423,plain,
    ( X0 != X1
    | k1_relat_1(X0) = k1_relat_1(X1) ),
    theory(equality)).

cnf(c_432,plain,
    ( k1_relat_1(sK0) = k1_relat_1(sK0)
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_423])).

cnf(c_78,plain,
    ( ~ r1_tarski(sK0,sK0)
    | sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_74,plain,
    ( r1_tarski(sK0,sK0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_17,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | ~ r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))
    | ~ r1_tarski(sK2,k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_20,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f65])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_109813,c_13305,c_9354,c_9304,c_8464,c_8332,c_8331,c_3448,c_3084,c_1760,c_1197,c_432,c_78,c_74,c_17,c_20,c_26,c_21,c_22,c_24,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 12:27:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 23.56/3.48  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.56/3.48  
% 23.56/3.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.56/3.48  
% 23.56/3.48  ------  iProver source info
% 23.56/3.48  
% 23.56/3.48  git: date: 2020-06-30 10:37:57 +0100
% 23.56/3.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.56/3.48  git: non_committed_changes: false
% 23.56/3.48  git: last_make_outside_of_git: false
% 23.56/3.48  
% 23.56/3.48  ------ 
% 23.56/3.48  
% 23.56/3.48  ------ Input Options
% 23.56/3.48  
% 23.56/3.48  --out_options                           all
% 23.56/3.48  --tptp_safe_out                         true
% 23.56/3.48  --problem_path                          ""
% 23.56/3.48  --include_path                          ""
% 23.56/3.48  --clausifier                            res/vclausify_rel
% 23.56/3.48  --clausifier_options                    --mode clausify
% 23.56/3.48  --stdin                                 false
% 23.56/3.48  --stats_out                             all
% 23.56/3.48  
% 23.56/3.48  ------ General Options
% 23.56/3.48  
% 23.56/3.48  --fof                                   false
% 23.56/3.48  --time_out_real                         305.
% 23.56/3.48  --time_out_virtual                      -1.
% 23.56/3.48  --symbol_type_check                     false
% 23.56/3.48  --clausify_out                          false
% 23.56/3.48  --sig_cnt_out                           false
% 23.56/3.48  --trig_cnt_out                          false
% 23.56/3.48  --trig_cnt_out_tolerance                1.
% 23.56/3.48  --trig_cnt_out_sk_spl                   false
% 23.56/3.48  --abstr_cl_out                          false
% 23.56/3.48  
% 23.56/3.48  ------ Global Options
% 23.56/3.48  
% 23.56/3.48  --schedule                              default
% 23.56/3.48  --add_important_lit                     false
% 23.56/3.48  --prop_solver_per_cl                    1000
% 23.56/3.48  --min_unsat_core                        false
% 23.56/3.48  --soft_assumptions                      false
% 23.56/3.48  --soft_lemma_size                       3
% 23.56/3.48  --prop_impl_unit_size                   0
% 23.56/3.48  --prop_impl_unit                        []
% 23.56/3.48  --share_sel_clauses                     true
% 23.56/3.48  --reset_solvers                         false
% 23.56/3.48  --bc_imp_inh                            [conj_cone]
% 23.56/3.48  --conj_cone_tolerance                   3.
% 23.56/3.48  --extra_neg_conj                        none
% 23.56/3.48  --large_theory_mode                     true
% 23.56/3.48  --prolific_symb_bound                   200
% 23.56/3.48  --lt_threshold                          2000
% 23.56/3.48  --clause_weak_htbl                      true
% 23.56/3.48  --gc_record_bc_elim                     false
% 23.56/3.48  
% 23.56/3.48  ------ Preprocessing Options
% 23.56/3.48  
% 23.56/3.48  --preprocessing_flag                    true
% 23.56/3.48  --time_out_prep_mult                    0.1
% 23.56/3.48  --splitting_mode                        input
% 23.56/3.48  --splitting_grd                         true
% 23.56/3.48  --splitting_cvd                         false
% 23.56/3.48  --splitting_cvd_svl                     false
% 23.56/3.48  --splitting_nvd                         32
% 23.56/3.48  --sub_typing                            true
% 23.56/3.48  --prep_gs_sim                           true
% 23.56/3.48  --prep_unflatten                        true
% 23.56/3.48  --prep_res_sim                          true
% 23.56/3.48  --prep_upred                            true
% 23.56/3.48  --prep_sem_filter                       exhaustive
% 23.56/3.48  --prep_sem_filter_out                   false
% 23.56/3.48  --pred_elim                             true
% 23.56/3.48  --res_sim_input                         true
% 23.56/3.48  --eq_ax_congr_red                       true
% 23.56/3.48  --pure_diseq_elim                       true
% 23.56/3.48  --brand_transform                       false
% 23.56/3.48  --non_eq_to_eq                          false
% 23.56/3.48  --prep_def_merge                        true
% 23.56/3.48  --prep_def_merge_prop_impl              false
% 23.56/3.48  --prep_def_merge_mbd                    true
% 23.56/3.48  --prep_def_merge_tr_red                 false
% 23.56/3.48  --prep_def_merge_tr_cl                  false
% 23.56/3.48  --smt_preprocessing                     true
% 23.56/3.48  --smt_ac_axioms                         fast
% 23.56/3.48  --preprocessed_out                      false
% 23.56/3.48  --preprocessed_stats                    false
% 23.56/3.48  
% 23.56/3.48  ------ Abstraction refinement Options
% 23.56/3.48  
% 23.56/3.48  --abstr_ref                             []
% 23.56/3.48  --abstr_ref_prep                        false
% 23.56/3.48  --abstr_ref_until_sat                   false
% 23.56/3.48  --abstr_ref_sig_restrict                funpre
% 23.56/3.48  --abstr_ref_af_restrict_to_split_sk     false
% 23.56/3.48  --abstr_ref_under                       []
% 23.56/3.48  
% 23.56/3.48  ------ SAT Options
% 23.56/3.48  
% 23.56/3.48  --sat_mode                              false
% 23.56/3.48  --sat_fm_restart_options                ""
% 23.56/3.48  --sat_gr_def                            false
% 23.56/3.48  --sat_epr_types                         true
% 23.56/3.48  --sat_non_cyclic_types                  false
% 23.56/3.48  --sat_finite_models                     false
% 23.56/3.48  --sat_fm_lemmas                         false
% 23.56/3.48  --sat_fm_prep                           false
% 23.56/3.48  --sat_fm_uc_incr                        true
% 23.56/3.48  --sat_out_model                         small
% 23.56/3.48  --sat_out_clauses                       false
% 23.56/3.48  
% 23.56/3.48  ------ QBF Options
% 23.56/3.48  
% 23.56/3.48  --qbf_mode                              false
% 23.56/3.48  --qbf_elim_univ                         false
% 23.56/3.48  --qbf_dom_inst                          none
% 23.56/3.48  --qbf_dom_pre_inst                      false
% 23.56/3.48  --qbf_sk_in                             false
% 23.56/3.48  --qbf_pred_elim                         true
% 23.56/3.48  --qbf_split                             512
% 23.56/3.48  
% 23.56/3.48  ------ BMC1 Options
% 23.56/3.48  
% 23.56/3.48  --bmc1_incremental                      false
% 23.56/3.48  --bmc1_axioms                           reachable_all
% 23.56/3.48  --bmc1_min_bound                        0
% 23.56/3.48  --bmc1_max_bound                        -1
% 23.56/3.48  --bmc1_max_bound_default                -1
% 23.56/3.48  --bmc1_symbol_reachability              true
% 23.56/3.48  --bmc1_property_lemmas                  false
% 23.56/3.48  --bmc1_k_induction                      false
% 23.56/3.48  --bmc1_non_equiv_states                 false
% 23.56/3.48  --bmc1_deadlock                         false
% 23.56/3.48  --bmc1_ucm                              false
% 23.56/3.48  --bmc1_add_unsat_core                   none
% 23.56/3.48  --bmc1_unsat_core_children              false
% 23.56/3.48  --bmc1_unsat_core_extrapolate_axioms    false
% 23.56/3.48  --bmc1_out_stat                         full
% 23.56/3.48  --bmc1_ground_init                      false
% 23.56/3.48  --bmc1_pre_inst_next_state              false
% 23.56/3.48  --bmc1_pre_inst_state                   false
% 23.56/3.48  --bmc1_pre_inst_reach_state             false
% 23.56/3.48  --bmc1_out_unsat_core                   false
% 23.56/3.48  --bmc1_aig_witness_out                  false
% 23.56/3.48  --bmc1_verbose                          false
% 23.56/3.48  --bmc1_dump_clauses_tptp                false
% 23.56/3.48  --bmc1_dump_unsat_core_tptp             false
% 23.56/3.48  --bmc1_dump_file                        -
% 23.56/3.48  --bmc1_ucm_expand_uc_limit              128
% 23.56/3.48  --bmc1_ucm_n_expand_iterations          6
% 23.56/3.48  --bmc1_ucm_extend_mode                  1
% 23.56/3.48  --bmc1_ucm_init_mode                    2
% 23.56/3.48  --bmc1_ucm_cone_mode                    none
% 23.56/3.48  --bmc1_ucm_reduced_relation_type        0
% 23.56/3.48  --bmc1_ucm_relax_model                  4
% 23.56/3.48  --bmc1_ucm_full_tr_after_sat            true
% 23.56/3.48  --bmc1_ucm_expand_neg_assumptions       false
% 23.56/3.48  --bmc1_ucm_layered_model                none
% 23.56/3.48  --bmc1_ucm_max_lemma_size               10
% 23.56/3.48  
% 23.56/3.48  ------ AIG Options
% 23.56/3.48  
% 23.56/3.48  --aig_mode                              false
% 23.56/3.48  
% 23.56/3.48  ------ Instantiation Options
% 23.56/3.48  
% 23.56/3.48  --instantiation_flag                    true
% 23.56/3.48  --inst_sos_flag                         false
% 23.56/3.48  --inst_sos_phase                        true
% 23.56/3.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.56/3.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.56/3.48  --inst_lit_sel_side                     num_symb
% 23.56/3.48  --inst_solver_per_active                1400
% 23.56/3.48  --inst_solver_calls_frac                1.
% 23.56/3.48  --inst_passive_queue_type               priority_queues
% 23.56/3.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.56/3.48  --inst_passive_queues_freq              [25;2]
% 23.56/3.48  --inst_dismatching                      true
% 23.56/3.48  --inst_eager_unprocessed_to_passive     true
% 23.56/3.48  --inst_prop_sim_given                   true
% 23.56/3.48  --inst_prop_sim_new                     false
% 23.56/3.48  --inst_subs_new                         false
% 23.56/3.48  --inst_eq_res_simp                      false
% 23.56/3.48  --inst_subs_given                       false
% 23.56/3.48  --inst_orphan_elimination               true
% 23.56/3.48  --inst_learning_loop_flag               true
% 23.56/3.48  --inst_learning_start                   3000
% 23.56/3.48  --inst_learning_factor                  2
% 23.56/3.48  --inst_start_prop_sim_after_learn       3
% 23.56/3.48  --inst_sel_renew                        solver
% 23.56/3.48  --inst_lit_activity_flag                true
% 23.56/3.48  --inst_restr_to_given                   false
% 23.56/3.48  --inst_activity_threshold               500
% 23.56/3.48  --inst_out_proof                        true
% 23.56/3.48  
% 23.56/3.48  ------ Resolution Options
% 23.56/3.48  
% 23.56/3.48  --resolution_flag                       true
% 23.56/3.48  --res_lit_sel                           adaptive
% 23.56/3.48  --res_lit_sel_side                      none
% 23.56/3.48  --res_ordering                          kbo
% 23.56/3.48  --res_to_prop_solver                    active
% 23.56/3.48  --res_prop_simpl_new                    false
% 23.56/3.48  --res_prop_simpl_given                  true
% 23.56/3.48  --res_passive_queue_type                priority_queues
% 23.56/3.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.56/3.48  --res_passive_queues_freq               [15;5]
% 23.56/3.48  --res_forward_subs                      full
% 23.56/3.48  --res_backward_subs                     full
% 23.56/3.48  --res_forward_subs_resolution           true
% 23.56/3.48  --res_backward_subs_resolution          true
% 23.56/3.48  --res_orphan_elimination                true
% 23.56/3.48  --res_time_limit                        2.
% 23.56/3.48  --res_out_proof                         true
% 23.56/3.48  
% 23.56/3.48  ------ Superposition Options
% 23.56/3.48  
% 23.56/3.48  --superposition_flag                    true
% 23.56/3.48  --sup_passive_queue_type                priority_queues
% 23.56/3.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.56/3.48  --sup_passive_queues_freq               [8;1;4]
% 23.56/3.48  --demod_completeness_check              fast
% 23.56/3.48  --demod_use_ground                      true
% 23.56/3.48  --sup_to_prop_solver                    passive
% 23.56/3.48  --sup_prop_simpl_new                    true
% 23.56/3.48  --sup_prop_simpl_given                  true
% 23.56/3.48  --sup_fun_splitting                     false
% 23.56/3.48  --sup_smt_interval                      50000
% 23.56/3.48  
% 23.56/3.48  ------ Superposition Simplification Setup
% 23.56/3.48  
% 23.56/3.48  --sup_indices_passive                   []
% 23.56/3.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.56/3.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.56/3.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.56/3.48  --sup_full_triv                         [TrivRules;PropSubs]
% 23.56/3.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.56/3.48  --sup_full_bw                           [BwDemod]
% 23.56/3.48  --sup_immed_triv                        [TrivRules]
% 23.56/3.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.56/3.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.56/3.48  --sup_immed_bw_main                     []
% 23.56/3.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 23.56/3.48  --sup_input_triv                        [Unflattening;TrivRules]
% 23.56/3.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.56/3.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 23.56/3.48  
% 23.56/3.48  ------ Combination Options
% 23.56/3.48  
% 23.56/3.48  --comb_res_mult                         3
% 23.56/3.48  --comb_sup_mult                         2
% 23.56/3.48  --comb_inst_mult                        10
% 23.56/3.48  
% 23.56/3.48  ------ Debug Options
% 23.56/3.48  
% 23.56/3.48  --dbg_backtrace                         false
% 23.56/3.48  --dbg_dump_prop_clauses                 false
% 23.56/3.48  --dbg_dump_prop_clauses_file            -
% 23.56/3.48  --dbg_out_stat                          false
% 23.56/3.48  ------ Parsing...
% 23.56/3.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.56/3.48  
% 23.56/3.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 23.56/3.48  
% 23.56/3.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.56/3.48  
% 23.56/3.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.56/3.48  ------ Proving...
% 23.56/3.48  ------ Problem Properties 
% 23.56/3.48  
% 23.56/3.48  
% 23.56/3.48  clauses                                 22
% 23.56/3.48  conjectures                             7
% 23.56/3.48  EPR                                     6
% 23.56/3.48  Horn                                    20
% 23.56/3.48  unary                                   5
% 23.56/3.48  binary                                  7
% 23.56/3.48  lits                                    54
% 23.56/3.48  lits eq                                 7
% 23.56/3.48  fd_pure                                 0
% 23.56/3.48  fd_pseudo                               0
% 23.56/3.48  fd_cond                                 0
% 23.56/3.48  fd_pseudo_cond                          1
% 23.56/3.48  AC symbols                              0
% 23.56/3.48  
% 23.56/3.48  ------ Schedule dynamic 5 is on 
% 23.56/3.48  
% 23.56/3.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 23.56/3.48  
% 23.56/3.48  
% 23.56/3.48  ------ 
% 23.56/3.48  Current options:
% 23.56/3.48  ------ 
% 23.56/3.48  
% 23.56/3.48  ------ Input Options
% 23.56/3.48  
% 23.56/3.48  --out_options                           all
% 23.56/3.48  --tptp_safe_out                         true
% 23.56/3.48  --problem_path                          ""
% 23.56/3.48  --include_path                          ""
% 23.56/3.48  --clausifier                            res/vclausify_rel
% 23.56/3.48  --clausifier_options                    --mode clausify
% 23.56/3.48  --stdin                                 false
% 23.56/3.48  --stats_out                             all
% 23.56/3.48  
% 23.56/3.48  ------ General Options
% 23.56/3.48  
% 23.56/3.48  --fof                                   false
% 23.56/3.48  --time_out_real                         305.
% 23.56/3.48  --time_out_virtual                      -1.
% 23.56/3.48  --symbol_type_check                     false
% 23.56/3.48  --clausify_out                          false
% 23.56/3.48  --sig_cnt_out                           false
% 23.56/3.48  --trig_cnt_out                          false
% 23.56/3.48  --trig_cnt_out_tolerance                1.
% 23.56/3.48  --trig_cnt_out_sk_spl                   false
% 23.56/3.48  --abstr_cl_out                          false
% 23.56/3.48  
% 23.56/3.48  ------ Global Options
% 23.56/3.48  
% 23.56/3.48  --schedule                              default
% 23.56/3.48  --add_important_lit                     false
% 23.56/3.48  --prop_solver_per_cl                    1000
% 23.56/3.48  --min_unsat_core                        false
% 23.56/3.48  --soft_assumptions                      false
% 23.56/3.48  --soft_lemma_size                       3
% 23.56/3.48  --prop_impl_unit_size                   0
% 23.56/3.48  --prop_impl_unit                        []
% 23.56/3.48  --share_sel_clauses                     true
% 23.56/3.48  --reset_solvers                         false
% 23.56/3.48  --bc_imp_inh                            [conj_cone]
% 23.56/3.48  --conj_cone_tolerance                   3.
% 23.56/3.48  --extra_neg_conj                        none
% 23.56/3.48  --large_theory_mode                     true
% 23.56/3.48  --prolific_symb_bound                   200
% 23.56/3.48  --lt_threshold                          2000
% 23.56/3.48  --clause_weak_htbl                      true
% 23.56/3.48  --gc_record_bc_elim                     false
% 23.56/3.48  
% 23.56/3.48  ------ Preprocessing Options
% 23.56/3.48  
% 23.56/3.48  --preprocessing_flag                    true
% 23.56/3.48  --time_out_prep_mult                    0.1
% 23.56/3.48  --splitting_mode                        input
% 23.56/3.48  --splitting_grd                         true
% 23.56/3.48  --splitting_cvd                         false
% 23.56/3.48  --splitting_cvd_svl                     false
% 23.56/3.48  --splitting_nvd                         32
% 23.56/3.48  --sub_typing                            true
% 23.56/3.48  --prep_gs_sim                           true
% 23.56/3.48  --prep_unflatten                        true
% 23.56/3.48  --prep_res_sim                          true
% 23.56/3.48  --prep_upred                            true
% 23.56/3.48  --prep_sem_filter                       exhaustive
% 23.56/3.48  --prep_sem_filter_out                   false
% 23.56/3.48  --pred_elim                             true
% 23.56/3.48  --res_sim_input                         true
% 23.56/3.48  --eq_ax_congr_red                       true
% 23.56/3.48  --pure_diseq_elim                       true
% 23.56/3.48  --brand_transform                       false
% 23.56/3.48  --non_eq_to_eq                          false
% 23.56/3.48  --prep_def_merge                        true
% 23.56/3.48  --prep_def_merge_prop_impl              false
% 23.56/3.48  --prep_def_merge_mbd                    true
% 23.56/3.48  --prep_def_merge_tr_red                 false
% 23.56/3.48  --prep_def_merge_tr_cl                  false
% 23.56/3.48  --smt_preprocessing                     true
% 23.56/3.48  --smt_ac_axioms                         fast
% 23.56/3.48  --preprocessed_out                      false
% 23.56/3.48  --preprocessed_stats                    false
% 23.56/3.48  
% 23.56/3.48  ------ Abstraction refinement Options
% 23.56/3.48  
% 23.56/3.48  --abstr_ref                             []
% 23.56/3.48  --abstr_ref_prep                        false
% 23.56/3.48  --abstr_ref_until_sat                   false
% 23.56/3.48  --abstr_ref_sig_restrict                funpre
% 23.56/3.48  --abstr_ref_af_restrict_to_split_sk     false
% 23.56/3.48  --abstr_ref_under                       []
% 23.56/3.48  
% 23.56/3.48  ------ SAT Options
% 23.56/3.48  
% 23.56/3.48  --sat_mode                              false
% 23.56/3.48  --sat_fm_restart_options                ""
% 23.56/3.48  --sat_gr_def                            false
% 23.56/3.48  --sat_epr_types                         true
% 23.56/3.48  --sat_non_cyclic_types                  false
% 23.56/3.48  --sat_finite_models                     false
% 23.56/3.48  --sat_fm_lemmas                         false
% 23.56/3.48  --sat_fm_prep                           false
% 23.56/3.48  --sat_fm_uc_incr                        true
% 23.56/3.48  --sat_out_model                         small
% 23.56/3.48  --sat_out_clauses                       false
% 23.56/3.48  
% 23.56/3.48  ------ QBF Options
% 23.56/3.48  
% 23.56/3.48  --qbf_mode                              false
% 23.56/3.48  --qbf_elim_univ                         false
% 23.56/3.48  --qbf_dom_inst                          none
% 23.56/3.48  --qbf_dom_pre_inst                      false
% 23.56/3.48  --qbf_sk_in                             false
% 23.56/3.48  --qbf_pred_elim                         true
% 23.56/3.48  --qbf_split                             512
% 23.56/3.48  
% 23.56/3.48  ------ BMC1 Options
% 23.56/3.48  
% 23.56/3.48  --bmc1_incremental                      false
% 23.56/3.48  --bmc1_axioms                           reachable_all
% 23.56/3.48  --bmc1_min_bound                        0
% 23.56/3.48  --bmc1_max_bound                        -1
% 23.56/3.48  --bmc1_max_bound_default                -1
% 23.56/3.48  --bmc1_symbol_reachability              true
% 23.56/3.48  --bmc1_property_lemmas                  false
% 23.56/3.48  --bmc1_k_induction                      false
% 23.56/3.48  --bmc1_non_equiv_states                 false
% 23.56/3.48  --bmc1_deadlock                         false
% 23.56/3.48  --bmc1_ucm                              false
% 23.56/3.48  --bmc1_add_unsat_core                   none
% 23.56/3.48  --bmc1_unsat_core_children              false
% 23.56/3.48  --bmc1_unsat_core_extrapolate_axioms    false
% 23.56/3.48  --bmc1_out_stat                         full
% 23.56/3.48  --bmc1_ground_init                      false
% 23.56/3.48  --bmc1_pre_inst_next_state              false
% 23.56/3.48  --bmc1_pre_inst_state                   false
% 23.56/3.48  --bmc1_pre_inst_reach_state             false
% 23.56/3.48  --bmc1_out_unsat_core                   false
% 23.56/3.48  --bmc1_aig_witness_out                  false
% 23.56/3.48  --bmc1_verbose                          false
% 23.56/3.48  --bmc1_dump_clauses_tptp                false
% 23.56/3.48  --bmc1_dump_unsat_core_tptp             false
% 23.56/3.48  --bmc1_dump_file                        -
% 23.56/3.48  --bmc1_ucm_expand_uc_limit              128
% 23.56/3.48  --bmc1_ucm_n_expand_iterations          6
% 23.56/3.48  --bmc1_ucm_extend_mode                  1
% 23.56/3.48  --bmc1_ucm_init_mode                    2
% 23.56/3.48  --bmc1_ucm_cone_mode                    none
% 23.56/3.48  --bmc1_ucm_reduced_relation_type        0
% 23.56/3.48  --bmc1_ucm_relax_model                  4
% 23.56/3.48  --bmc1_ucm_full_tr_after_sat            true
% 23.56/3.48  --bmc1_ucm_expand_neg_assumptions       false
% 23.56/3.48  --bmc1_ucm_layered_model                none
% 23.56/3.48  --bmc1_ucm_max_lemma_size               10
% 23.56/3.48  
% 23.56/3.48  ------ AIG Options
% 23.56/3.48  
% 23.56/3.48  --aig_mode                              false
% 23.56/3.48  
% 23.56/3.48  ------ Instantiation Options
% 23.56/3.48  
% 23.56/3.48  --instantiation_flag                    true
% 23.56/3.48  --inst_sos_flag                         false
% 23.56/3.48  --inst_sos_phase                        true
% 23.56/3.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.56/3.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.56/3.48  --inst_lit_sel_side                     none
% 23.56/3.48  --inst_solver_per_active                1400
% 23.56/3.48  --inst_solver_calls_frac                1.
% 23.56/3.48  --inst_passive_queue_type               priority_queues
% 23.56/3.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.56/3.48  --inst_passive_queues_freq              [25;2]
% 23.56/3.48  --inst_dismatching                      true
% 23.56/3.48  --inst_eager_unprocessed_to_passive     true
% 23.56/3.48  --inst_prop_sim_given                   true
% 23.56/3.48  --inst_prop_sim_new                     false
% 23.56/3.48  --inst_subs_new                         false
% 23.56/3.48  --inst_eq_res_simp                      false
% 23.56/3.48  --inst_subs_given                       false
% 23.56/3.48  --inst_orphan_elimination               true
% 23.56/3.48  --inst_learning_loop_flag               true
% 23.56/3.48  --inst_learning_start                   3000
% 23.56/3.48  --inst_learning_factor                  2
% 23.56/3.48  --inst_start_prop_sim_after_learn       3
% 23.56/3.48  --inst_sel_renew                        solver
% 23.56/3.48  --inst_lit_activity_flag                true
% 23.56/3.48  --inst_restr_to_given                   false
% 23.56/3.48  --inst_activity_threshold               500
% 23.56/3.48  --inst_out_proof                        true
% 23.56/3.48  
% 23.56/3.48  ------ Resolution Options
% 23.56/3.48  
% 23.56/3.48  --resolution_flag                       false
% 23.56/3.48  --res_lit_sel                           adaptive
% 23.56/3.48  --res_lit_sel_side                      none
% 23.56/3.48  --res_ordering                          kbo
% 23.56/3.48  --res_to_prop_solver                    active
% 23.56/3.48  --res_prop_simpl_new                    false
% 23.56/3.48  --res_prop_simpl_given                  true
% 23.56/3.48  --res_passive_queue_type                priority_queues
% 23.56/3.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.56/3.48  --res_passive_queues_freq               [15;5]
% 23.56/3.48  --res_forward_subs                      full
% 23.56/3.48  --res_backward_subs                     full
% 23.56/3.48  --res_forward_subs_resolution           true
% 23.56/3.48  --res_backward_subs_resolution          true
% 23.56/3.48  --res_orphan_elimination                true
% 23.56/3.48  --res_time_limit                        2.
% 23.56/3.48  --res_out_proof                         true
% 23.56/3.48  
% 23.56/3.48  ------ Superposition Options
% 23.56/3.48  
% 23.56/3.48  --superposition_flag                    true
% 23.56/3.48  --sup_passive_queue_type                priority_queues
% 23.56/3.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.56/3.48  --sup_passive_queues_freq               [8;1;4]
% 23.56/3.48  --demod_completeness_check              fast
% 23.56/3.48  --demod_use_ground                      true
% 23.56/3.48  --sup_to_prop_solver                    passive
% 23.56/3.48  --sup_prop_simpl_new                    true
% 23.56/3.48  --sup_prop_simpl_given                  true
% 23.56/3.48  --sup_fun_splitting                     false
% 23.56/3.48  --sup_smt_interval                      50000
% 23.56/3.48  
% 23.56/3.48  ------ Superposition Simplification Setup
% 23.56/3.48  
% 23.56/3.48  --sup_indices_passive                   []
% 23.56/3.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.56/3.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.56/3.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.56/3.48  --sup_full_triv                         [TrivRules;PropSubs]
% 23.56/3.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.56/3.48  --sup_full_bw                           [BwDemod]
% 23.56/3.48  --sup_immed_triv                        [TrivRules]
% 23.56/3.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.56/3.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.56/3.48  --sup_immed_bw_main                     []
% 23.56/3.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 23.56/3.48  --sup_input_triv                        [Unflattening;TrivRules]
% 23.56/3.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.56/3.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 23.56/3.48  
% 23.56/3.48  ------ Combination Options
% 23.56/3.48  
% 23.56/3.48  --comb_res_mult                         3
% 23.56/3.48  --comb_sup_mult                         2
% 23.56/3.48  --comb_inst_mult                        10
% 23.56/3.48  
% 23.56/3.48  ------ Debug Options
% 23.56/3.48  
% 23.56/3.48  --dbg_backtrace                         false
% 23.56/3.48  --dbg_dump_prop_clauses                 false
% 23.56/3.48  --dbg_dump_prop_clauses_file            -
% 23.56/3.48  --dbg_out_stat                          false
% 23.56/3.48  
% 23.56/3.48  
% 23.56/3.48  
% 23.56/3.48  
% 23.56/3.48  ------ Proving...
% 23.56/3.48  
% 23.56/3.48  
% 23.56/3.48  % SZS status Theorem for theBenchmark.p
% 23.56/3.48  
% 23.56/3.48  % SZS output start CNFRefutation for theBenchmark.p
% 23.56/3.48  
% 23.56/3.48  fof(f12,axiom,(
% 23.56/3.48    ! [X0,X1] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))))),
% 23.56/3.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.56/3.48  
% 23.56/3.48  fof(f29,plain,(
% 23.56/3.48    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 23.56/3.48    inference(ennf_transformation,[],[f12])).
% 23.56/3.48  
% 23.56/3.48  fof(f30,plain,(
% 23.56/3.48    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 23.56/3.48    inference(flattening,[],[f29])).
% 23.56/3.48  
% 23.56/3.48  fof(f59,plain,(
% 23.56/3.48    ( ! [X0,X1] : (v1_funct_1(k7_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 23.56/3.48    inference(cnf_transformation,[],[f30])).
% 23.56/3.48  
% 23.56/3.48  fof(f15,conjecture,(
% 23.56/3.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <=> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))))))),
% 23.56/3.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.56/3.48  
% 23.56/3.48  fof(f16,negated_conjecture,(
% 23.56/3.48    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <=> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))))))),
% 23.56/3.48    inference(negated_conjecture,[],[f15])).
% 23.56/3.48  
% 23.56/3.48  fof(f35,plain,(
% 23.56/3.48    ? [X0] : (? [X1] : (? [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <~> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0)))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 23.56/3.48    inference(ennf_transformation,[],[f16])).
% 23.56/3.48  
% 23.56/3.48  fof(f36,plain,(
% 23.56/3.48    ? [X0] : (? [X1] : (? [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <~> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0)))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 23.56/3.48    inference(flattening,[],[f35])).
% 23.56/3.48  
% 23.56/3.48  fof(f39,plain,(
% 23.56/3.48    ? [X0] : (? [X1] : (? [X2] : (((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0))) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 23.56/3.48    inference(nnf_transformation,[],[f36])).
% 23.56/3.48  
% 23.56/3.48  fof(f40,plain,(
% 23.56/3.48    ? [X0] : (? [X1] : (? [X2] : ((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 23.56/3.48    inference(flattening,[],[f39])).
% 23.56/3.48  
% 23.56/3.48  fof(f43,plain,(
% 23.56/3.48    ( ! [X0,X1] : (? [X2] : ((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) => ((~r1_tarski(k9_relat_1(X0,sK2),k1_relat_1(X1)) | ~r1_tarski(sK2,k1_relat_1(X0)) | ~r1_tarski(sK2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,sK2),k1_relat_1(X1)) & r1_tarski(sK2,k1_relat_1(X0))) | r1_tarski(sK2,k1_relat_1(k5_relat_1(X0,X1)))))) )),
% 23.56/3.48    introduced(choice_axiom,[])).
% 23.56/3.48  
% 23.56/3.48  fof(f42,plain,(
% 23.56/3.48    ( ! [X0] : (? [X1] : (? [X2] : ((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) => (? [X2] : ((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(sK1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,sK1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(sK1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,sK1))))) & v1_funct_1(sK1) & v1_relat_1(sK1))) )),
% 23.56/3.48    introduced(choice_axiom,[])).
% 23.56/3.48  
% 23.56/3.48  fof(f41,plain,(
% 23.56/3.48    ? [X0] : (? [X1] : (? [X2] : ((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (? [X2] : ((~r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(sK0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,X1)))) & ((r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(sK0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 23.56/3.48    introduced(choice_axiom,[])).
% 23.56/3.48  
% 23.56/3.48  fof(f44,plain,(
% 23.56/3.48    (((~r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | ~r1_tarski(sK2,k1_relat_1(sK0)) | ~r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))) & ((r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) & r1_tarski(sK2,k1_relat_1(sK0))) | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))))) & v1_funct_1(sK1) & v1_relat_1(sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 23.56/3.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f40,f43,f42,f41])).
% 23.56/3.48  
% 23.56/3.48  fof(f64,plain,(
% 23.56/3.48    v1_relat_1(sK1)),
% 23.56/3.48    inference(cnf_transformation,[],[f44])).
% 23.56/3.48  
% 23.56/3.48  fof(f62,plain,(
% 23.56/3.48    v1_relat_1(sK0)),
% 23.56/3.48    inference(cnf_transformation,[],[f44])).
% 23.56/3.48  
% 23.56/3.48  fof(f6,axiom,(
% 23.56/3.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 23.56/3.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.56/3.48  
% 23.56/3.48  fof(f22,plain,(
% 23.56/3.48    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 23.56/3.48    inference(ennf_transformation,[],[f6])).
% 23.56/3.48  
% 23.56/3.48  fof(f52,plain,(
% 23.56/3.48    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 23.56/3.48    inference(cnf_transformation,[],[f22])).
% 23.56/3.48  
% 23.56/3.48  fof(f67,plain,(
% 23.56/3.48    r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 23.56/3.48    inference(cnf_transformation,[],[f44])).
% 23.56/3.48  
% 23.56/3.48  fof(f13,axiom,(
% 23.56/3.48    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 23.56/3.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.56/3.48  
% 23.56/3.48  fof(f31,plain,(
% 23.56/3.48    ! [X0,X1,X2] : ((r1_tarski(X0,k10_relat_1(X2,X1)) | (~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 23.56/3.48    inference(ennf_transformation,[],[f13])).
% 23.56/3.48  
% 23.56/3.48  fof(f32,plain,(
% 23.56/3.48    ! [X0,X1,X2] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 23.56/3.48    inference(flattening,[],[f31])).
% 23.56/3.48  
% 23.56/3.48  fof(f60,plain,(
% 23.56/3.48    ( ! [X2,X0,X1] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 23.56/3.48    inference(cnf_transformation,[],[f32])).
% 23.56/3.48  
% 23.56/3.48  fof(f63,plain,(
% 23.56/3.48    v1_funct_1(sK0)),
% 23.56/3.48    inference(cnf_transformation,[],[f44])).
% 23.56/3.48  
% 23.56/3.48  fof(f66,plain,(
% 23.56/3.48    r1_tarski(sK2,k1_relat_1(sK0)) | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 23.56/3.48    inference(cnf_transformation,[],[f44])).
% 23.56/3.48  
% 23.56/3.48  fof(f10,axiom,(
% 23.56/3.48    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 23.56/3.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.56/3.48  
% 23.56/3.48  fof(f26,plain,(
% 23.56/3.48    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 23.56/3.48    inference(ennf_transformation,[],[f10])).
% 23.56/3.48  
% 23.56/3.48  fof(f27,plain,(
% 23.56/3.48    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 23.56/3.48    inference(flattening,[],[f26])).
% 23.56/3.48  
% 23.56/3.48  fof(f56,plain,(
% 23.56/3.48    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 23.56/3.48    inference(cnf_transformation,[],[f27])).
% 23.56/3.48  
% 23.56/3.48  fof(f4,axiom,(
% 23.56/3.48    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k7_relat_1(X1,X0),X2) = k7_relat_1(k5_relat_1(X1,X2),X0)))),
% 23.56/3.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.56/3.48  
% 23.56/3.48  fof(f20,plain,(
% 23.56/3.48    ! [X0,X1] : (! [X2] : (k5_relat_1(k7_relat_1(X1,X0),X2) = k7_relat_1(k5_relat_1(X1,X2),X0) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 23.56/3.48    inference(ennf_transformation,[],[f4])).
% 23.56/3.48  
% 23.56/3.48  fof(f50,plain,(
% 23.56/3.48    ( ! [X2,X0,X1] : (k5_relat_1(k7_relat_1(X1,X0),X2) = k7_relat_1(k5_relat_1(X1,X2),X0) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 23.56/3.48    inference(cnf_transformation,[],[f20])).
% 23.56/3.48  
% 23.56/3.48  fof(f2,axiom,(
% 23.56/3.48    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 23.56/3.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.56/3.48  
% 23.56/3.48  fof(f17,plain,(
% 23.56/3.48    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 23.56/3.48    inference(ennf_transformation,[],[f2])).
% 23.56/3.48  
% 23.56/3.48  fof(f18,plain,(
% 23.56/3.48    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 23.56/3.48    inference(flattening,[],[f17])).
% 23.56/3.48  
% 23.56/3.48  fof(f48,plain,(
% 23.56/3.48    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 23.56/3.48    inference(cnf_transformation,[],[f18])).
% 23.56/3.48  
% 23.56/3.48  fof(f14,axiom,(
% 23.56/3.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,X0)) => r1_tarski(k2_relat_1(X1),k1_relat_1(X0)))))),
% 23.56/3.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.56/3.48  
% 23.56/3.48  fof(f33,plain,(
% 23.56/3.48    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 23.56/3.48    inference(ennf_transformation,[],[f14])).
% 23.56/3.48  
% 23.56/3.48  fof(f34,plain,(
% 23.56/3.48    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 23.56/3.48    inference(flattening,[],[f33])).
% 23.56/3.48  
% 23.56/3.48  fof(f61,plain,(
% 23.56/3.48    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 23.56/3.48    inference(cnf_transformation,[],[f34])).
% 23.56/3.48  
% 23.56/3.48  fof(f5,axiom,(
% 23.56/3.48    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 23.56/3.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.56/3.48  
% 23.56/3.48  fof(f21,plain,(
% 23.56/3.48    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 23.56/3.48    inference(ennf_transformation,[],[f5])).
% 23.56/3.48  
% 23.56/3.48  fof(f51,plain,(
% 23.56/3.48    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 23.56/3.48    inference(cnf_transformation,[],[f21])).
% 23.56/3.48  
% 23.56/3.48  fof(f7,axiom,(
% 23.56/3.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))))),
% 23.56/3.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.56/3.48  
% 23.56/3.48  fof(f23,plain,(
% 23.56/3.48    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 23.56/3.48    inference(ennf_transformation,[],[f7])).
% 23.56/3.48  
% 23.56/3.48  fof(f53,plain,(
% 23.56/3.48    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 23.56/3.48    inference(cnf_transformation,[],[f23])).
% 23.56/3.48  
% 23.56/3.48  fof(f9,axiom,(
% 23.56/3.48    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)))),
% 23.56/3.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.56/3.48  
% 23.56/3.48  fof(f25,plain,(
% 23.56/3.48    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 23.56/3.48    inference(ennf_transformation,[],[f9])).
% 23.56/3.48  
% 23.56/3.48  fof(f55,plain,(
% 23.56/3.48    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 23.56/3.48    inference(cnf_transformation,[],[f25])).
% 23.56/3.48  
% 23.56/3.48  fof(f3,axiom,(
% 23.56/3.48    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 23.56/3.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.56/3.48  
% 23.56/3.48  fof(f19,plain,(
% 23.56/3.48    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 23.56/3.48    inference(ennf_transformation,[],[f3])).
% 23.56/3.48  
% 23.56/3.48  fof(f49,plain,(
% 23.56/3.48    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 23.56/3.48    inference(cnf_transformation,[],[f19])).
% 23.56/3.48  
% 23.56/3.48  fof(f1,axiom,(
% 23.56/3.48    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 23.56/3.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.56/3.48  
% 23.56/3.48  fof(f37,plain,(
% 23.56/3.48    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 23.56/3.48    inference(nnf_transformation,[],[f1])).
% 23.56/3.48  
% 23.56/3.48  fof(f38,plain,(
% 23.56/3.48    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 23.56/3.48    inference(flattening,[],[f37])).
% 23.56/3.48  
% 23.56/3.48  fof(f47,plain,(
% 23.56/3.48    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 23.56/3.48    inference(cnf_transformation,[],[f38])).
% 23.56/3.48  
% 23.56/3.48  fof(f8,axiom,(
% 23.56/3.48    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 23.56/3.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.56/3.48  
% 23.56/3.48  fof(f24,plain,(
% 23.56/3.48    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 23.56/3.48    inference(ennf_transformation,[],[f8])).
% 23.56/3.48  
% 23.56/3.48  fof(f54,plain,(
% 23.56/3.48    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 23.56/3.48    inference(cnf_transformation,[],[f24])).
% 23.56/3.48  
% 23.56/3.48  fof(f45,plain,(
% 23.56/3.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 23.56/3.48    inference(cnf_transformation,[],[f38])).
% 23.56/3.48  
% 23.56/3.48  fof(f70,plain,(
% 23.56/3.48    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 23.56/3.48    inference(equality_resolution,[],[f45])).
% 23.56/3.49  
% 23.56/3.49  fof(f68,plain,(
% 23.56/3.49    ~r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | ~r1_tarski(sK2,k1_relat_1(sK0)) | ~r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 23.56/3.49    inference(cnf_transformation,[],[f44])).
% 23.56/3.49  
% 23.56/3.49  fof(f65,plain,(
% 23.56/3.49    v1_funct_1(sK1)),
% 23.56/3.49    inference(cnf_transformation,[],[f44])).
% 23.56/3.49  
% 23.56/3.49  cnf(c_13,plain,
% 23.56/3.49      ( ~ v1_funct_1(X0)
% 23.56/3.49      | v1_funct_1(k7_relat_1(X0,X1))
% 23.56/3.49      | ~ v1_relat_1(X0) ),
% 23.56/3.49      inference(cnf_transformation,[],[f59]) ).
% 23.56/3.49  
% 23.56/3.49  cnf(c_109811,plain,
% 23.56/3.49      ( ~ v1_funct_1(X0)
% 23.56/3.49      | v1_funct_1(k7_relat_1(X0,sK2))
% 23.56/3.49      | ~ v1_relat_1(X0) ),
% 23.56/3.49      inference(instantiation,[status(thm)],[c_13]) ).
% 23.56/3.49  
% 23.56/3.49  cnf(c_109813,plain,
% 23.56/3.49      ( v1_funct_1(k7_relat_1(sK0,sK2))
% 23.56/3.49      | ~ v1_funct_1(sK0)
% 23.56/3.49      | ~ v1_relat_1(sK0) ),
% 23.56/3.49      inference(instantiation,[status(thm)],[c_109811]) ).
% 23.56/3.49  
% 23.56/3.49  cnf(c_417,plain,
% 23.56/3.49      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 23.56/3.49      theory(equality) ).
% 23.56/3.49  
% 23.56/3.49  cnf(c_1016,plain,
% 23.56/3.49      ( ~ r1_tarski(X0,X1)
% 23.56/3.49      | r1_tarski(X2,k1_relat_1(X3))
% 23.56/3.49      | X2 != X0
% 23.56/3.49      | k1_relat_1(X3) != X1 ),
% 23.56/3.49      inference(instantiation,[status(thm)],[c_417]) ).
% 23.56/3.49  
% 23.56/3.49  cnf(c_1097,plain,
% 23.56/3.49      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 23.56/3.49      | r1_tarski(X2,k1_relat_1(X1))
% 23.56/3.49      | X2 != X0
% 23.56/3.49      | k1_relat_1(X1) != k1_relat_1(X1) ),
% 23.56/3.49      inference(instantiation,[status(thm)],[c_1016]) ).
% 23.56/3.49  
% 23.56/3.49  cnf(c_1256,plain,
% 23.56/3.49      ( r1_tarski(X0,k1_relat_1(X1))
% 23.56/3.49      | ~ r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),k1_relat_1(X1))
% 23.56/3.49      | X0 != k1_relat_1(k7_relat_1(X1,X2))
% 23.56/3.49      | k1_relat_1(X1) != k1_relat_1(X1) ),
% 23.56/3.49      inference(instantiation,[status(thm)],[c_1097]) ).
% 23.56/3.49  
% 23.56/3.49  cnf(c_13303,plain,
% 23.56/3.49      ( ~ r1_tarski(k1_relat_1(k7_relat_1(X0,sK2)),k1_relat_1(X0))
% 23.56/3.49      | r1_tarski(sK2,k1_relat_1(X0))
% 23.56/3.49      | k1_relat_1(X0) != k1_relat_1(X0)
% 23.56/3.49      | sK2 != k1_relat_1(k7_relat_1(X0,sK2)) ),
% 23.56/3.49      inference(instantiation,[status(thm)],[c_1256]) ).
% 23.56/3.49  
% 23.56/3.49  cnf(c_13305,plain,
% 23.56/3.49      ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0))
% 23.56/3.49      | r1_tarski(sK2,k1_relat_1(sK0))
% 23.56/3.49      | k1_relat_1(sK0) != k1_relat_1(sK0)
% 23.56/3.49      | sK2 != k1_relat_1(k7_relat_1(sK0,sK2)) ),
% 23.56/3.49      inference(instantiation,[status(thm)],[c_13303]) ).
% 23.56/3.49  
% 23.56/3.49  cnf(c_21,negated_conjecture,
% 23.56/3.49      ( v1_relat_1(sK1) ),
% 23.56/3.49      inference(cnf_transformation,[],[f64]) ).
% 23.56/3.49  
% 23.56/3.49  cnf(c_800,plain,
% 23.56/3.49      ( v1_relat_1(sK1) = iProver_top ),
% 23.56/3.49      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 23.56/3.49  
% 23.56/3.49  cnf(c_23,negated_conjecture,
% 23.56/3.49      ( v1_relat_1(sK0) ),
% 23.56/3.49      inference(cnf_transformation,[],[f62]) ).
% 23.56/3.49  
% 23.56/3.49  cnf(c_798,plain,
% 23.56/3.49      ( v1_relat_1(sK0) = iProver_top ),
% 23.56/3.49      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 23.56/3.49  
% 23.56/3.49  cnf(c_7,plain,
% 23.56/3.49      ( ~ v1_relat_1(X0)
% 23.56/3.49      | ~ v1_relat_1(X1)
% 23.56/3.49      | k10_relat_1(X1,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(X1,X0)) ),
% 23.56/3.49      inference(cnf_transformation,[],[f52]) ).
% 23.56/3.49  
% 23.56/3.49  cnf(c_813,plain,
% 23.56/3.49      ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
% 23.56/3.49      | v1_relat_1(X1) != iProver_top
% 23.56/3.49      | v1_relat_1(X0) != iProver_top ),
% 23.56/3.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 23.56/3.49  
% 23.56/3.49  cnf(c_2946,plain,
% 23.56/3.49      ( k10_relat_1(sK0,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(sK0,X0))
% 23.56/3.49      | v1_relat_1(X0) != iProver_top ),
% 23.56/3.49      inference(superposition,[status(thm)],[c_798,c_813]) ).
% 23.56/3.49  
% 23.56/3.49  cnf(c_3424,plain,
% 23.56/3.49      ( k10_relat_1(sK0,k1_relat_1(sK1)) = k1_relat_1(k5_relat_1(sK0,sK1)) ),
% 23.56/3.49      inference(superposition,[status(thm)],[c_800,c_2946]) ).
% 23.56/3.49  
% 23.56/3.49  cnf(c_18,negated_conjecture,
% 23.56/3.49      ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
% 23.56/3.49      | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
% 23.56/3.49      inference(cnf_transformation,[],[f67]) ).
% 23.56/3.49  
% 23.56/3.49  cnf(c_803,plain,
% 23.56/3.49      ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) = iProver_top
% 23.56/3.49      | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top ),
% 23.56/3.49      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 23.56/3.49  
% 23.56/3.49  cnf(c_15,plain,
% 23.56/3.49      ( r1_tarski(X0,k10_relat_1(X1,X2))
% 23.56/3.49      | ~ r1_tarski(X0,k1_relat_1(X1))
% 23.56/3.49      | ~ r1_tarski(k9_relat_1(X1,X0),X2)
% 23.56/3.49      | ~ v1_funct_1(X1)
% 23.56/3.49      | ~ v1_relat_1(X1) ),
% 23.56/3.49      inference(cnf_transformation,[],[f60]) ).
% 23.56/3.49  
% 23.56/3.49  cnf(c_806,plain,
% 23.56/3.49      ( r1_tarski(X0,k10_relat_1(X1,X2)) = iProver_top
% 23.56/3.49      | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
% 23.56/3.49      | r1_tarski(k9_relat_1(X1,X0),X2) != iProver_top
% 23.56/3.49      | v1_funct_1(X1) != iProver_top
% 23.56/3.49      | v1_relat_1(X1) != iProver_top ),
% 23.56/3.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 23.56/3.49  
% 23.56/3.49  cnf(c_1771,plain,
% 23.56/3.49      ( r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) = iProver_top
% 23.56/3.49      | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top
% 23.56/3.49      | r1_tarski(sK2,k1_relat_1(sK0)) != iProver_top
% 23.56/3.49      | v1_funct_1(sK0) != iProver_top
% 23.56/3.49      | v1_relat_1(sK0) != iProver_top ),
% 23.56/3.49      inference(superposition,[status(thm)],[c_803,c_806]) ).
% 23.56/3.49  
% 23.56/3.49  cnf(c_24,plain,
% 23.56/3.49      ( v1_relat_1(sK0) = iProver_top ),
% 23.56/3.49      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 23.56/3.49  
% 23.56/3.49  cnf(c_22,negated_conjecture,
% 23.56/3.49      ( v1_funct_1(sK0) ),
% 23.56/3.49      inference(cnf_transformation,[],[f63]) ).
% 23.56/3.49  
% 23.56/3.49  cnf(c_25,plain,
% 23.56/3.49      ( v1_funct_1(sK0) = iProver_top ),
% 23.56/3.49      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 23.56/3.49  
% 23.56/3.49  cnf(c_19,negated_conjecture,
% 23.56/3.49      ( r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))
% 23.56/3.49      | r1_tarski(sK2,k1_relat_1(sK0)) ),
% 23.56/3.49      inference(cnf_transformation,[],[f66]) ).
% 23.56/3.49  
% 23.56/3.49  cnf(c_28,plain,
% 23.56/3.49      ( r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top
% 23.56/3.49      | r1_tarski(sK2,k1_relat_1(sK0)) = iProver_top ),
% 23.56/3.49      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 23.56/3.49  
% 23.56/3.49  cnf(c_2559,plain,
% 23.56/3.49      ( r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top
% 23.56/3.49      | r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) = iProver_top ),
% 23.56/3.49      inference(global_propositional_subsumption,
% 23.56/3.49                [status(thm)],
% 23.56/3.49                [c_1771,c_24,c_25,c_28]) ).
% 23.56/3.49  
% 23.56/3.49  cnf(c_2560,plain,
% 23.56/3.49      ( r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) = iProver_top
% 23.56/3.49      | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top ),
% 23.56/3.49      inference(renaming,[status(thm)],[c_2559]) ).
% 23.56/3.49  
% 23.56/3.49  cnf(c_3447,plain,
% 23.56/3.49      ( r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top ),
% 23.56/3.49      inference(demodulation,[status(thm)],[c_3424,c_2560]) ).
% 23.56/3.49  
% 23.56/3.49  cnf(c_11,plain,
% 23.56/3.49      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 23.56/3.49      | ~ v1_relat_1(X1)
% 23.56/3.49      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
% 23.56/3.49      inference(cnf_transformation,[],[f56]) ).
% 23.56/3.49  
% 23.56/3.49  cnf(c_809,plain,
% 23.56/3.49      ( k1_relat_1(k7_relat_1(X0,X1)) = X1
% 23.56/3.49      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 23.56/3.49      | v1_relat_1(X0) != iProver_top ),
% 23.56/3.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 23.56/3.49  
% 23.56/3.49  cnf(c_5153,plain,
% 23.56/3.49      ( k1_relat_1(k7_relat_1(k5_relat_1(sK0,sK1),sK2)) = sK2
% 23.56/3.49      | v1_relat_1(k5_relat_1(sK0,sK1)) != iProver_top ),
% 23.56/3.49      inference(superposition,[status(thm)],[c_3447,c_809]) ).
% 23.56/3.49  
% 23.56/3.49  cnf(c_5,plain,
% 23.56/3.49      ( ~ v1_relat_1(X0)
% 23.56/3.49      | ~ v1_relat_1(X1)
% 23.56/3.49      | k7_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(k7_relat_1(X0,X2),X1) ),
% 23.56/3.49      inference(cnf_transformation,[],[f50]) ).
% 23.56/3.49  
% 23.56/3.49  cnf(c_815,plain,
% 23.56/3.49      ( k7_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(k7_relat_1(X0,X2),X1)
% 23.56/3.49      | v1_relat_1(X0) != iProver_top
% 23.56/3.49      | v1_relat_1(X1) != iProver_top ),
% 23.56/3.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 23.56/3.49  
% 23.56/3.49  cnf(c_2986,plain,
% 23.56/3.49      ( k7_relat_1(k5_relat_1(sK0,X0),X1) = k5_relat_1(k7_relat_1(sK0,X1),X0)
% 23.56/3.49      | v1_relat_1(X0) != iProver_top ),
% 23.56/3.49      inference(superposition,[status(thm)],[c_798,c_815]) ).
% 23.56/3.49  
% 23.56/3.49  cnf(c_4601,plain,
% 23.56/3.49      ( k7_relat_1(k5_relat_1(sK0,sK1),X0) = k5_relat_1(k7_relat_1(sK0,X0),sK1) ),
% 23.56/3.49      inference(superposition,[status(thm)],[c_800,c_2986]) ).
% 23.56/3.49  
% 23.56/3.49  cnf(c_5156,plain,
% 23.56/3.49      ( k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1)) = sK2
% 23.56/3.49      | v1_relat_1(k5_relat_1(sK0,sK1)) != iProver_top ),
% 23.56/3.49      inference(demodulation,[status(thm)],[c_5153,c_4601]) ).
% 23.56/3.49  
% 23.56/3.49  cnf(c_26,plain,
% 23.56/3.49      ( v1_relat_1(sK1) = iProver_top ),
% 23.56/3.49      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 23.56/3.49  
% 23.56/3.49  cnf(c_3,plain,
% 23.56/3.49      ( ~ v1_relat_1(X0)
% 23.56/3.49      | ~ v1_relat_1(X1)
% 23.56/3.49      | v1_relat_1(k5_relat_1(X1,X0)) ),
% 23.56/3.49      inference(cnf_transformation,[],[f48]) ).
% 23.56/3.49  
% 23.56/3.49  cnf(c_1112,plain,
% 23.56/3.49      ( v1_relat_1(k5_relat_1(sK0,sK1))
% 23.56/3.49      | ~ v1_relat_1(sK1)
% 23.56/3.49      | ~ v1_relat_1(sK0) ),
% 23.56/3.49      inference(instantiation,[status(thm)],[c_3]) ).
% 23.56/3.49  
% 23.56/3.49  cnf(c_1113,plain,
% 23.56/3.49      ( v1_relat_1(k5_relat_1(sK0,sK1)) = iProver_top
% 23.56/3.49      | v1_relat_1(sK1) != iProver_top
% 23.56/3.49      | v1_relat_1(sK0) != iProver_top ),
% 23.56/3.49      inference(predicate_to_equality,[status(thm)],[c_1112]) ).
% 23.56/3.49  
% 23.56/3.49  cnf(c_9301,plain,
% 23.56/3.49      ( k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1)) = sK2 ),
% 23.56/3.49      inference(global_propositional_subsumption,
% 23.56/3.49                [status(thm)],
% 23.56/3.49                [c_5156,c_24,c_26,c_1113]) ).
% 23.56/3.49  
% 23.56/3.49  cnf(c_16,plain,
% 23.56/3.49      ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
% 23.56/3.49      | ~ v1_funct_1(X1)
% 23.56/3.49      | ~ v1_funct_1(X0)
% 23.56/3.49      | ~ v1_relat_1(X0)
% 23.56/3.49      | ~ v1_relat_1(X1)
% 23.56/3.49      | k1_relat_1(k5_relat_1(X0,X1)) != k1_relat_1(X0) ),
% 23.56/3.49      inference(cnf_transformation,[],[f61]) ).
% 23.56/3.49  
% 23.56/3.49  cnf(c_805,plain,
% 23.56/3.49      ( k1_relat_1(k5_relat_1(X0,X1)) != k1_relat_1(X0)
% 23.56/3.49      | r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) = iProver_top
% 23.56/3.49      | v1_funct_1(X1) != iProver_top
% 23.56/3.49      | v1_funct_1(X0) != iProver_top
% 23.56/3.49      | v1_relat_1(X0) != iProver_top
% 23.56/3.49      | v1_relat_1(X1) != iProver_top ),
% 23.56/3.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 23.56/3.49  
% 23.56/3.49  cnf(c_9305,plain,
% 23.56/3.49      ( k1_relat_1(k7_relat_1(sK0,sK2)) != sK2
% 23.56/3.49      | r1_tarski(k2_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1)) = iProver_top
% 23.56/3.49      | v1_funct_1(k7_relat_1(sK0,sK2)) != iProver_top
% 23.56/3.49      | v1_funct_1(sK1) != iProver_top
% 23.56/3.49      | v1_relat_1(k7_relat_1(sK0,sK2)) != iProver_top
% 23.56/3.49      | v1_relat_1(sK1) != iProver_top ),
% 23.56/3.49      inference(superposition,[status(thm)],[c_9301,c_805]) ).
% 23.56/3.49  
% 23.56/3.49  cnf(c_6,plain,
% 23.56/3.49      ( ~ v1_relat_1(X0)
% 23.56/3.49      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 23.56/3.49      inference(cnf_transformation,[],[f51]) ).
% 23.56/3.49  
% 23.56/3.49  cnf(c_814,plain,
% 23.56/3.49      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 23.56/3.49      | v1_relat_1(X0) != iProver_top ),
% 23.56/3.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 23.56/3.49  
% 23.56/3.49  cnf(c_1547,plain,
% 23.56/3.49      ( k2_relat_1(k7_relat_1(sK0,X0)) = k9_relat_1(sK0,X0) ),
% 23.56/3.49      inference(superposition,[status(thm)],[c_798,c_814]) ).
% 23.56/3.49  
% 23.56/3.49  cnf(c_9331,plain,
% 23.56/3.49      ( k1_relat_1(k7_relat_1(sK0,sK2)) != sK2
% 23.56/3.49      | r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) = iProver_top
% 23.56/3.49      | v1_funct_1(k7_relat_1(sK0,sK2)) != iProver_top
% 23.56/3.49      | v1_funct_1(sK1) != iProver_top
% 23.56/3.49      | v1_relat_1(k7_relat_1(sK0,sK2)) != iProver_top
% 23.56/3.49      | v1_relat_1(sK1) != iProver_top ),
% 23.56/3.49      inference(demodulation,[status(thm)],[c_9305,c_1547]) ).
% 23.56/3.49  
% 23.56/3.49  cnf(c_9354,plain,
% 23.56/3.49      ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
% 23.56/3.49      | ~ v1_funct_1(k7_relat_1(sK0,sK2))
% 23.56/3.49      | ~ v1_funct_1(sK1)
% 23.56/3.49      | ~ v1_relat_1(k7_relat_1(sK0,sK2))
% 23.56/3.49      | ~ v1_relat_1(sK1)
% 23.56/3.49      | k1_relat_1(k7_relat_1(sK0,sK2)) != sK2 ),
% 23.56/3.49      inference(predicate_to_equality_rev,[status(thm)],[c_9331]) ).
% 23.56/3.49  
% 23.56/3.49  cnf(c_8,plain,
% 23.56/3.49      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
% 23.56/3.49      | ~ v1_relat_1(X1)
% 23.56/3.49      | ~ v1_relat_1(X0) ),
% 23.56/3.49      inference(cnf_transformation,[],[f53]) ).
% 23.56/3.49  
% 23.56/3.49  cnf(c_812,plain,
% 23.56/3.49      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) = iProver_top
% 23.56/3.49      | v1_relat_1(X0) != iProver_top
% 23.56/3.49      | v1_relat_1(X1) != iProver_top ),
% 23.56/3.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 23.56/3.49  
% 23.56/3.49  cnf(c_9304,plain,
% 23.56/3.49      ( r1_tarski(sK2,k1_relat_1(k7_relat_1(sK0,sK2))) = iProver_top
% 23.56/3.49      | v1_relat_1(k7_relat_1(sK0,sK2)) != iProver_top
% 23.56/3.49      | v1_relat_1(sK1) != iProver_top ),
% 23.56/3.49      inference(superposition,[status(thm)],[c_9301,c_812]) ).
% 23.56/3.49  
% 23.56/3.49  cnf(c_10,plain,
% 23.56/3.49      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),k1_relat_1(X0))
% 23.56/3.49      | ~ v1_relat_1(X0) ),
% 23.56/3.49      inference(cnf_transformation,[],[f55]) ).
% 23.56/3.49  
% 23.56/3.49  cnf(c_8462,plain,
% 23.56/3.49      ( r1_tarski(k1_relat_1(k7_relat_1(X0,sK2)),k1_relat_1(X0))
% 23.56/3.49      | ~ v1_relat_1(X0) ),
% 23.56/3.49      inference(instantiation,[status(thm)],[c_10]) ).
% 23.56/3.49  
% 23.56/3.49  cnf(c_8464,plain,
% 23.56/3.49      ( r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0))
% 23.56/3.49      | ~ v1_relat_1(sK0) ),
% 23.56/3.49      inference(instantiation,[status(thm)],[c_8462]) ).
% 23.56/3.49  
% 23.56/3.49  cnf(c_4,plain,
% 23.56/3.49      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 23.56/3.49      inference(cnf_transformation,[],[f49]) ).
% 23.56/3.49  
% 23.56/3.49  cnf(c_8329,plain,
% 23.56/3.49      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,sK2)) ),
% 23.56/3.49      inference(instantiation,[status(thm)],[c_4]) ).
% 23.56/3.49  
% 23.56/3.49  cnf(c_8330,plain,
% 23.56/3.49      ( v1_relat_1(X0) != iProver_top
% 23.56/3.49      | v1_relat_1(k7_relat_1(X0,sK2)) = iProver_top ),
% 23.56/3.49      inference(predicate_to_equality,[status(thm)],[c_8329]) ).
% 23.56/3.49  
% 23.56/3.49  cnf(c_8332,plain,
% 23.56/3.49      ( v1_relat_1(k7_relat_1(sK0,sK2)) = iProver_top
% 23.56/3.49      | v1_relat_1(sK0) != iProver_top ),
% 23.56/3.49      inference(instantiation,[status(thm)],[c_8330]) ).
% 23.56/3.49  
% 23.56/3.49  cnf(c_8331,plain,
% 23.56/3.49      ( v1_relat_1(k7_relat_1(sK0,sK2)) | ~ v1_relat_1(sK0) ),
% 23.56/3.49      inference(instantiation,[status(thm)],[c_8329]) ).
% 23.56/3.49  
% 23.56/3.49  cnf(c_3448,plain,
% 23.56/3.49      ( r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
% 23.56/3.49      inference(predicate_to_equality_rev,[status(thm)],[c_3447]) ).
% 23.56/3.49  
% 23.56/3.49  cnf(c_0,plain,
% 23.56/3.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 23.56/3.49      inference(cnf_transformation,[],[f47]) ).
% 23.56/3.49  
% 23.56/3.49  cnf(c_1693,plain,
% 23.56/3.49      ( ~ r1_tarski(X0,sK2) | ~ r1_tarski(sK2,X0) | sK2 = X0 ),
% 23.56/3.49      inference(instantiation,[status(thm)],[c_0]) ).
% 23.56/3.49  
% 23.56/3.49  cnf(c_3081,plain,
% 23.56/3.49      ( ~ r1_tarski(k1_relat_1(k7_relat_1(X0,sK2)),sK2)
% 23.56/3.49      | ~ r1_tarski(sK2,k1_relat_1(k7_relat_1(X0,sK2)))
% 23.56/3.49      | sK2 = k1_relat_1(k7_relat_1(X0,sK2)) ),
% 23.56/3.49      inference(instantiation,[status(thm)],[c_1693]) ).
% 23.56/3.49  
% 23.56/3.49  cnf(c_3082,plain,
% 23.56/3.49      ( sK2 = k1_relat_1(k7_relat_1(X0,sK2))
% 23.56/3.49      | r1_tarski(k1_relat_1(k7_relat_1(X0,sK2)),sK2) != iProver_top
% 23.56/3.49      | r1_tarski(sK2,k1_relat_1(k7_relat_1(X0,sK2))) != iProver_top ),
% 23.56/3.49      inference(predicate_to_equality,[status(thm)],[c_3081]) ).
% 23.56/3.49  
% 23.56/3.49  cnf(c_3084,plain,
% 23.56/3.49      ( sK2 = k1_relat_1(k7_relat_1(sK0,sK2))
% 23.56/3.49      | r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),sK2) != iProver_top
% 23.56/3.49      | r1_tarski(sK2,k1_relat_1(k7_relat_1(sK0,sK2))) != iProver_top ),
% 23.56/3.49      inference(instantiation,[status(thm)],[c_3082]) ).
% 23.56/3.49  
% 23.56/3.49  cnf(c_1488,plain,
% 23.56/3.49      ( ~ r1_tarski(X0,sK2) | ~ r1_tarski(sK2,X0) | X0 = sK2 ),
% 23.56/3.49      inference(instantiation,[status(thm)],[c_0]) ).
% 23.56/3.49  
% 23.56/3.49  cnf(c_1757,plain,
% 23.56/3.49      ( ~ r1_tarski(k1_relat_1(k7_relat_1(X0,sK2)),sK2)
% 23.56/3.49      | ~ r1_tarski(sK2,k1_relat_1(k7_relat_1(X0,sK2)))
% 23.56/3.49      | k1_relat_1(k7_relat_1(X0,sK2)) = sK2 ),
% 23.56/3.49      inference(instantiation,[status(thm)],[c_1488]) ).
% 23.56/3.49  
% 23.56/3.49  cnf(c_1758,plain,
% 23.56/3.49      ( k1_relat_1(k7_relat_1(X0,sK2)) = sK2
% 23.56/3.49      | r1_tarski(k1_relat_1(k7_relat_1(X0,sK2)),sK2) != iProver_top
% 23.56/3.49      | r1_tarski(sK2,k1_relat_1(k7_relat_1(X0,sK2))) != iProver_top ),
% 23.56/3.49      inference(predicate_to_equality,[status(thm)],[c_1757]) ).
% 23.56/3.49  
% 23.56/3.49  cnf(c_1760,plain,
% 23.56/3.49      ( k1_relat_1(k7_relat_1(sK0,sK2)) = sK2
% 23.56/3.49      | r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),sK2) != iProver_top
% 23.56/3.49      | r1_tarski(sK2,k1_relat_1(k7_relat_1(sK0,sK2))) != iProver_top ),
% 23.56/3.49      inference(instantiation,[status(thm)],[c_1758]) ).
% 23.56/3.49  
% 23.56/3.49  cnf(c_9,plain,
% 23.56/3.49      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) | ~ v1_relat_1(X0) ),
% 23.56/3.49      inference(cnf_transformation,[],[f54]) ).
% 23.56/3.49  
% 23.56/3.49  cnf(c_1190,plain,
% 23.56/3.49      ( r1_tarski(k1_relat_1(k7_relat_1(X0,sK2)),sK2)
% 23.56/3.49      | ~ v1_relat_1(X0) ),
% 23.56/3.49      inference(instantiation,[status(thm)],[c_9]) ).
% 23.56/3.49  
% 23.56/3.49  cnf(c_1195,plain,
% 23.56/3.49      ( r1_tarski(k1_relat_1(k7_relat_1(X0,sK2)),sK2) = iProver_top
% 23.56/3.49      | v1_relat_1(X0) != iProver_top ),
% 23.56/3.49      inference(predicate_to_equality,[status(thm)],[c_1190]) ).
% 23.56/3.49  
% 23.56/3.49  cnf(c_1197,plain,
% 23.56/3.49      ( r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),sK2) = iProver_top
% 23.56/3.49      | v1_relat_1(sK0) != iProver_top ),
% 23.56/3.49      inference(instantiation,[status(thm)],[c_1195]) ).
% 23.56/3.49  
% 23.56/3.49  cnf(c_423,plain,
% 23.56/3.49      ( X0 != X1 | k1_relat_1(X0) = k1_relat_1(X1) ),
% 23.56/3.49      theory(equality) ).
% 23.56/3.49  
% 23.56/3.49  cnf(c_432,plain,
% 23.56/3.49      ( k1_relat_1(sK0) = k1_relat_1(sK0) | sK0 != sK0 ),
% 23.56/3.49      inference(instantiation,[status(thm)],[c_423]) ).
% 23.56/3.49  
% 23.56/3.49  cnf(c_78,plain,
% 23.56/3.49      ( ~ r1_tarski(sK0,sK0) | sK0 = sK0 ),
% 23.56/3.49      inference(instantiation,[status(thm)],[c_0]) ).
% 23.56/3.49  
% 23.56/3.49  cnf(c_2,plain,
% 23.56/3.49      ( r1_tarski(X0,X0) ),
% 23.56/3.49      inference(cnf_transformation,[],[f70]) ).
% 23.56/3.49  
% 23.56/3.49  cnf(c_74,plain,
% 23.56/3.49      ( r1_tarski(sK0,sK0) ),
% 23.56/3.49      inference(instantiation,[status(thm)],[c_2]) ).
% 23.56/3.49  
% 23.56/3.49  cnf(c_17,negated_conjecture,
% 23.56/3.49      ( ~ r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
% 23.56/3.49      | ~ r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))
% 23.56/3.49      | ~ r1_tarski(sK2,k1_relat_1(sK0)) ),
% 23.56/3.49      inference(cnf_transformation,[],[f68]) ).
% 23.56/3.49  
% 23.56/3.49  cnf(c_20,negated_conjecture,
% 23.56/3.49      ( v1_funct_1(sK1) ),
% 23.56/3.49      inference(cnf_transformation,[],[f65]) ).
% 23.56/3.49  
% 23.56/3.49  cnf(contradiction,plain,
% 23.56/3.49      ( $false ),
% 23.56/3.49      inference(minisat,
% 23.56/3.49                [status(thm)],
% 23.56/3.49                [c_109813,c_13305,c_9354,c_9304,c_8464,c_8332,c_8331,
% 23.56/3.49                 c_3448,c_3084,c_1760,c_1197,c_432,c_78,c_74,c_17,c_20,
% 23.56/3.49                 c_26,c_21,c_22,c_24,c_23]) ).
% 23.56/3.49  
% 23.56/3.49  
% 23.56/3.49  % SZS output end CNFRefutation for theBenchmark.p
% 23.56/3.49  
% 23.56/3.49  ------                               Statistics
% 23.56/3.49  
% 23.56/3.49  ------ General
% 23.56/3.49  
% 23.56/3.49  abstr_ref_over_cycles:                  0
% 23.56/3.49  abstr_ref_under_cycles:                 0
% 23.56/3.49  gc_basic_clause_elim:                   0
% 23.56/3.49  forced_gc_time:                         0
% 23.56/3.49  parsing_time:                           0.009
% 23.56/3.49  unif_index_cands_time:                  0.
% 23.56/3.49  unif_index_add_time:                    0.
% 23.56/3.49  orderings_time:                         0.
% 23.56/3.49  out_proof_time:                         0.013
% 23.56/3.49  total_time:                             2.865
% 23.56/3.49  num_of_symbols:                         43
% 23.56/3.49  num_of_terms:                           98783
% 23.56/3.49  
% 23.56/3.49  ------ Preprocessing
% 23.56/3.49  
% 23.56/3.49  num_of_splits:                          0
% 23.56/3.49  num_of_split_atoms:                     0
% 23.56/3.49  num_of_reused_defs:                     0
% 23.56/3.49  num_eq_ax_congr_red:                    3
% 23.56/3.49  num_of_sem_filtered_clauses:            1
% 23.56/3.49  num_of_subtypes:                        0
% 23.56/3.49  monotx_restored_types:                  0
% 23.56/3.49  sat_num_of_epr_types:                   0
% 23.56/3.49  sat_num_of_non_cyclic_types:            0
% 23.56/3.49  sat_guarded_non_collapsed_types:        0
% 23.56/3.49  num_pure_diseq_elim:                    0
% 23.56/3.49  simp_replaced_by:                       0
% 23.56/3.49  res_preprocessed:                       111
% 23.56/3.49  prep_upred:                             0
% 23.56/3.49  prep_unflattend:                        0
% 23.56/3.49  smt_new_axioms:                         0
% 23.56/3.49  pred_elim_cands:                        3
% 23.56/3.49  pred_elim:                              0
% 23.56/3.49  pred_elim_cl:                           0
% 23.56/3.49  pred_elim_cycles:                       2
% 23.56/3.49  merged_defs:                            0
% 23.56/3.49  merged_defs_ncl:                        0
% 23.56/3.49  bin_hyper_res:                          0
% 23.56/3.49  prep_cycles:                            4
% 23.56/3.49  pred_elim_time:                         0.
% 23.56/3.49  splitting_time:                         0.
% 23.56/3.49  sem_filter_time:                        0.
% 23.56/3.49  monotx_time:                            0.
% 23.56/3.49  subtype_inf_time:                       0.
% 23.56/3.49  
% 23.56/3.49  ------ Problem properties
% 23.56/3.49  
% 23.56/3.49  clauses:                                22
% 23.56/3.49  conjectures:                            7
% 23.56/3.49  epr:                                    6
% 23.56/3.49  horn:                                   20
% 23.56/3.49  ground:                                 7
% 23.56/3.49  unary:                                  5
% 23.56/3.49  binary:                                 7
% 23.56/3.49  lits:                                   54
% 23.56/3.49  lits_eq:                                7
% 23.56/3.49  fd_pure:                                0
% 23.56/3.49  fd_pseudo:                              0
% 23.56/3.49  fd_cond:                                0
% 23.56/3.49  fd_pseudo_cond:                         1
% 23.56/3.49  ac_symbols:                             0
% 23.56/3.49  
% 23.56/3.49  ------ Propositional Solver
% 23.56/3.49  
% 23.56/3.49  prop_solver_calls:                      33
% 23.56/3.49  prop_fast_solver_calls:                 1380
% 23.56/3.49  smt_solver_calls:                       0
% 23.56/3.49  smt_fast_solver_calls:                  0
% 23.56/3.49  prop_num_of_clauses:                    32984
% 23.56/3.49  prop_preprocess_simplified:             45663
% 23.56/3.49  prop_fo_subsumed:                       64
% 23.56/3.49  prop_solver_time:                       0.
% 23.56/3.49  smt_solver_time:                        0.
% 23.56/3.49  smt_fast_solver_time:                   0.
% 23.56/3.49  prop_fast_solver_time:                  0.
% 23.56/3.49  prop_unsat_core_time:                   0.004
% 23.56/3.49  
% 23.56/3.49  ------ QBF
% 23.56/3.49  
% 23.56/3.49  qbf_q_res:                              0
% 23.56/3.49  qbf_num_tautologies:                    0
% 23.56/3.49  qbf_prep_cycles:                        0
% 23.56/3.49  
% 23.56/3.49  ------ BMC1
% 23.56/3.49  
% 23.56/3.49  bmc1_current_bound:                     -1
% 23.56/3.49  bmc1_last_solved_bound:                 -1
% 23.56/3.49  bmc1_unsat_core_size:                   -1
% 23.56/3.49  bmc1_unsat_core_parents_size:           -1
% 23.56/3.49  bmc1_merge_next_fun:                    0
% 23.56/3.49  bmc1_unsat_core_clauses_time:           0.
% 23.56/3.49  
% 23.56/3.49  ------ Instantiation
% 23.56/3.49  
% 23.56/3.49  inst_num_of_clauses:                    7689
% 23.56/3.49  inst_num_in_passive:                    2403
% 23.56/3.49  inst_num_in_active:                     2229
% 23.56/3.49  inst_num_in_unprocessed:                3057
% 23.56/3.49  inst_num_of_loops:                      2349
% 23.56/3.49  inst_num_of_learning_restarts:          0
% 23.56/3.49  inst_num_moves_active_passive:          115
% 23.56/3.49  inst_lit_activity:                      0
% 23.56/3.49  inst_lit_activity_moves:                0
% 23.56/3.49  inst_num_tautologies:                   0
% 23.56/3.49  inst_num_prop_implied:                  0
% 23.56/3.49  inst_num_existing_simplified:           0
% 23.56/3.49  inst_num_eq_res_simplified:             0
% 23.56/3.49  inst_num_child_elim:                    0
% 23.56/3.49  inst_num_of_dismatching_blockings:      23202
% 23.56/3.49  inst_num_of_non_proper_insts:           16355
% 23.56/3.49  inst_num_of_duplicates:                 0
% 23.56/3.49  inst_inst_num_from_inst_to_res:         0
% 23.56/3.49  inst_dismatching_checking_time:         0.
% 23.56/3.49  
% 23.56/3.49  ------ Resolution
% 23.56/3.49  
% 23.56/3.49  res_num_of_clauses:                     0
% 23.56/3.49  res_num_in_passive:                     0
% 23.56/3.49  res_num_in_active:                      0
% 23.56/3.49  res_num_of_loops:                       115
% 23.56/3.49  res_forward_subset_subsumed:            735
% 23.56/3.49  res_backward_subset_subsumed:           4
% 23.56/3.49  res_forward_subsumed:                   0
% 23.56/3.49  res_backward_subsumed:                  0
% 23.56/3.49  res_forward_subsumption_resolution:     0
% 23.56/3.49  res_backward_subsumption_resolution:    0
% 23.56/3.49  res_clause_to_clause_subsumption:       9801
% 23.56/3.49  res_orphan_elimination:                 0
% 23.56/3.49  res_tautology_del:                      1282
% 23.56/3.49  res_num_eq_res_simplified:              0
% 23.56/3.49  res_num_sel_changes:                    0
% 23.56/3.49  res_moves_from_active_to_pass:          0
% 23.56/3.49  
% 23.56/3.49  ------ Superposition
% 23.56/3.49  
% 23.56/3.49  sup_time_total:                         0.
% 23.56/3.49  sup_time_generating:                    0.
% 23.56/3.49  sup_time_sim_full:                      0.
% 23.56/3.49  sup_time_sim_immed:                     0.
% 23.56/3.49  
% 23.56/3.49  sup_num_of_clauses:                     3073
% 23.56/3.49  sup_num_in_active:                      437
% 23.56/3.49  sup_num_in_passive:                     2636
% 23.56/3.49  sup_num_of_loops:                       468
% 23.56/3.49  sup_fw_superposition:                   1945
% 23.56/3.49  sup_bw_superposition:                   2244
% 23.56/3.49  sup_immediate_simplified:               1347
% 23.56/3.49  sup_given_eliminated:                   0
% 23.56/3.49  comparisons_done:                       0
% 23.56/3.49  comparisons_avoided:                    0
% 23.56/3.49  
% 23.56/3.49  ------ Simplifications
% 23.56/3.49  
% 23.56/3.49  
% 23.56/3.49  sim_fw_subset_subsumed:                 87
% 23.56/3.49  sim_bw_subset_subsumed:                 135
% 23.56/3.49  sim_fw_subsumed:                        150
% 23.56/3.49  sim_bw_subsumed:                        0
% 23.56/3.49  sim_fw_subsumption_res:                 2
% 23.56/3.49  sim_bw_subsumption_res:                 0
% 23.56/3.49  sim_tautology_del:                      90
% 23.56/3.49  sim_eq_tautology_del:                   336
% 23.56/3.49  sim_eq_res_simp:                        0
% 23.56/3.49  sim_fw_demodulated:                     269
% 23.56/3.49  sim_bw_demodulated:                     19
% 23.56/3.49  sim_light_normalised:                   972
% 23.56/3.49  sim_joinable_taut:                      0
% 23.56/3.49  sim_joinable_simp:                      0
% 23.56/3.49  sim_ac_normalised:                      0
% 23.56/3.49  sim_smt_subsumption:                    0
% 23.56/3.49  
%------------------------------------------------------------------------------
