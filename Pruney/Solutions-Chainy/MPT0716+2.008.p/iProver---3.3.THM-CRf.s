%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:52:53 EST 2020

% Result     : Theorem 3.69s
% Output     : CNFRefutation 3.69s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 363 expanded)
%              Number of clauses        :   68 (  97 expanded)
%              Number of leaves         :   15 (  93 expanded)
%              Depth                    :   21
%              Number of atoms          :  479 (2536 expanded)
%              Number of equality atoms :   67 (  90 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

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

fof(f33,plain,(
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
    inference(flattening,[],[f33])).

fof(f37,plain,(
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

fof(f36,plain,(
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

fof(f35,plain,
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

fof(f38,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f34,f37,f36,f35])).

fof(f53,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f55,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

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

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
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

fof(f16,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

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
    inference(flattening,[],[f16])).

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
    inference(nnf_transformation,[],[f17])).

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

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X4,X2)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f62,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X4,k10_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f45])).

fof(f54,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f58,plain,
    ( r1_tarski(k9_relat_1(sK2,sK4),k1_relat_1(sK3))
    | r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f38])).

fof(f7,axiom,(
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
    inference(ennf_transformation,[],[f7])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f57,plain,
    ( r1_tarski(sK4,k1_relat_1(sK2))
    | r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f38])).

fof(f6,axiom,(
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
    inference(ennf_transformation,[],[f6])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f59,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,sK4),k1_relat_1(sK3))
    | ~ r1_tarski(sK4,k1_relat_1(sK2))
    | ~ r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1548,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,k1_relat_1(sK3))
    | r1_tarski(X0,k1_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2156,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK3))
    | ~ r1_tarski(k9_relat_1(sK2,X1),X0)
    | r1_tarski(k9_relat_1(sK2,X1),k1_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_1548])).

cnf(c_4213,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(sK3))))
    | r1_tarski(k9_relat_1(sK2,X0),k1_relat_1(sK3))
    | ~ r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(sK3))),k1_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_2156])).

cnf(c_13364,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(sK3))),k1_relat_1(sK3))
    | ~ r1_tarski(k9_relat_1(sK2,sK4),k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(sK3))))
    | r1_tarski(k9_relat_1(sK2,sK4),k1_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_4213])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1414,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2908,plain,
    ( r1_tarski(k9_relat_1(sK2,sK4),k9_relat_1(sK2,X0))
    | ~ r1_tarski(sK4,X0)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1414])).

cnf(c_13363,plain,
    ( r1_tarski(k9_relat_1(sK2,sK4),k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(sK3))))
    | ~ r1_tarski(sK4,k10_relat_1(sK2,k1_relat_1(sK3)))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_2908])).

cnf(c_608,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2421,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK4,X2)
    | X2 != X1
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_608])).

cnf(c_3114,plain,
    ( ~ r1_tarski(sK4,X0)
    | r1_tarski(sK4,X1)
    | X1 != X0
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_2421])).

cnf(c_5633,plain,
    ( r1_tarski(sK4,X0)
    | ~ r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3)))
    | X0 != k1_relat_1(k5_relat_1(sK2,sK3))
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_3114])).

cnf(c_9521,plain,
    ( r1_tarski(sK4,k10_relat_1(sK2,k1_relat_1(sK3)))
    | ~ r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3)))
    | k10_relat_1(sK2,k1_relat_1(sK3)) != k1_relat_1(k5_relat_1(sK2,sK3))
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_5633])).

cnf(c_20,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1107,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_18,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1108,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X1,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1112,plain,
    ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2661,plain,
    ( k10_relat_1(X0,k1_relat_1(sK3)) = k1_relat_1(k5_relat_1(X0,sK3))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1108,c_1112])).

cnf(c_2967,plain,
    ( k10_relat_1(sK2,k1_relat_1(sK3)) = k1_relat_1(k5_relat_1(sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_1107,c_2661])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1116,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_19,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_490,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_19])).

cnf(c_491,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK2,X1))
    | r2_hidden(X0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_490])).

cnf(c_495,plain,
    ( r2_hidden(X0,k1_relat_1(sK2))
    | ~ r2_hidden(X0,k10_relat_1(sK2,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_491,c_20])).

cnf(c_496,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK2,X1))
    | r2_hidden(X0,k1_relat_1(sK2)) ),
    inference(renaming,[status(thm)],[c_495])).

cnf(c_1093,plain,
    ( r2_hidden(X0,k10_relat_1(sK2,X1)) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_496])).

cnf(c_1595,plain,
    ( r2_hidden(sK0(k10_relat_1(sK2,X0),X1),k1_relat_1(sK2)) = iProver_top
    | r1_tarski(k10_relat_1(sK2,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1116,c_1093])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1117,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_6334,plain,
    ( r1_tarski(k10_relat_1(sK2,X0),k1_relat_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1595,c_1117])).

cnf(c_6357,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(sK2,sK3)),k1_relat_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2967,c_6334])).

cnf(c_6369,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(sK2,sK3)),k1_relat_1(sK2)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6357])).

cnf(c_15,negated_conjecture,
    ( r1_tarski(k9_relat_1(sK2,sK4),k1_relat_1(sK3))
    | r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1110,plain,
    ( r1_tarski(k9_relat_1(sK2,sK4),k1_relat_1(sK3)) = iProver_top
    | r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_13,plain,
    ( r1_tarski(X0,k10_relat_1(X1,X2))
    | ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ r1_tarski(k9_relat_1(X1,X0),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_469,plain,
    ( r1_tarski(X0,k10_relat_1(X1,X2))
    | ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ r1_tarski(k9_relat_1(X1,X0),X2)
    | ~ v1_relat_1(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_19])).

cnf(c_470,plain,
    ( r1_tarski(X0,k10_relat_1(sK2,X1))
    | ~ r1_tarski(X0,k1_relat_1(sK2))
    | ~ r1_tarski(k9_relat_1(sK2,X0),X1)
    | ~ v1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_469])).

cnf(c_474,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,X0),X1)
    | ~ r1_tarski(X0,k1_relat_1(sK2))
    | r1_tarski(X0,k10_relat_1(sK2,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_470,c_20])).

cnf(c_475,plain,
    ( r1_tarski(X0,k10_relat_1(sK2,X1))
    | ~ r1_tarski(X0,k1_relat_1(sK2))
    | ~ r1_tarski(k9_relat_1(sK2,X0),X1) ),
    inference(renaming,[status(thm)],[c_474])).

cnf(c_1094,plain,
    ( r1_tarski(X0,k10_relat_1(sK2,X1)) = iProver_top
    | r1_tarski(X0,k1_relat_1(sK2)) != iProver_top
    | r1_tarski(k9_relat_1(sK2,X0),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_475])).

cnf(c_2207,plain,
    ( r1_tarski(sK4,k10_relat_1(sK2,k1_relat_1(sK3))) = iProver_top
    | r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3))) = iProver_top
    | r1_tarski(sK4,k1_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1110,c_1094])).

cnf(c_1497,plain,
    ( r1_tarski(sK4,k10_relat_1(sK2,k1_relat_1(sK3)))
    | r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3)))
    | ~ r1_tarski(sK4,k1_relat_1(sK2)) ),
    inference(resolution,[status(thm)],[c_475,c_15])).

cnf(c_16,negated_conjecture,
    ( r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3)))
    | r1_tarski(sK4,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2246,plain,
    ( r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3)))
    | r1_tarski(sK4,k10_relat_1(sK2,k1_relat_1(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1497,c_16])).

cnf(c_2247,plain,
    ( r1_tarski(sK4,k10_relat_1(sK2,k1_relat_1(sK3)))
    | r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3))) ),
    inference(renaming,[status(thm)],[c_2246])).

cnf(c_2248,plain,
    ( r1_tarski(sK4,k10_relat_1(sK2,k1_relat_1(sK3))) = iProver_top
    | r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2247])).

cnf(c_5692,plain,
    ( r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3))) = iProver_top
    | r1_tarski(sK4,k10_relat_1(sK2,k1_relat_1(sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2207,c_2248])).

cnf(c_5693,plain,
    ( r1_tarski(sK4,k10_relat_1(sK2,k1_relat_1(sK3))) = iProver_top
    | r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3))) = iProver_top ),
    inference(renaming,[status(thm)],[c_5692])).

cnf(c_5696,plain,
    ( r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5693,c_2967])).

cnf(c_5698,plain,
    ( r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5696])).

cnf(c_2672,plain,
    ( k10_relat_1(sK2,k1_relat_1(sK3)) = k1_relat_1(k5_relat_1(sK2,sK3))
    | v1_relat_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2661])).

cnf(c_1393,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK2))
    | ~ r1_tarski(sK4,X0)
    | r1_tarski(sK4,k1_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2418,plain,
    ( ~ r1_tarski(k1_relat_1(k5_relat_1(sK2,sK3)),k1_relat_1(sK2))
    | ~ r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3)))
    | r1_tarski(sK4,k1_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_1393])).

cnf(c_12,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_310,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_19])).

cnf(c_311,plain,
    ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0)),X0)
    | ~ v1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_310])).

cnf(c_315,plain,
    ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0)),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_311,c_20])).

cnf(c_1565,plain,
    ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(sK3))),k1_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_315])).

cnf(c_606,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1537,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_606])).

cnf(c_14,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(sK2,sK4),k1_relat_1(sK3))
    | ~ r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3)))
    | ~ r1_tarski(sK4,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_21,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13364,c_13363,c_9521,c_6369,c_5698,c_2672,c_2418,c_1565,c_1537,c_14,c_21,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:50:11 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.69/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.69/0.99  
% 3.69/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.69/0.99  
% 3.69/0.99  ------  iProver source info
% 3.69/0.99  
% 3.69/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.69/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.69/0.99  git: non_committed_changes: false
% 3.69/0.99  git: last_make_outside_of_git: false
% 3.69/0.99  
% 3.69/0.99  ------ 
% 3.69/0.99  ------ Parsing...
% 3.69/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.69/0.99  
% 3.69/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e 
% 3.69/0.99  
% 3.69/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.69/0.99  
% 3.69/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.69/0.99  ------ Proving...
% 3.69/0.99  ------ Problem Properties 
% 3.69/0.99  
% 3.69/0.99  
% 3.69/0.99  clauses                                 27
% 3.69/0.99  conjectures                             5
% 3.69/0.99  EPR                                     4
% 3.69/0.99  Horn                                    20
% 3.69/0.99  unary                                   4
% 3.69/0.99  binary                                  8
% 3.69/0.99  lits                                    67
% 3.69/0.99  lits eq                                 7
% 3.69/0.99  fd_pure                                 0
% 3.69/0.99  fd_pseudo                               0
% 3.69/0.99  fd_cond                                 0
% 3.69/0.99  fd_pseudo_cond                          6
% 3.69/0.99  AC symbols                              0
% 3.69/0.99  
% 3.69/0.99  ------ Input Options Time Limit: Unbounded
% 3.69/0.99  
% 3.69/0.99  
% 3.69/0.99  ------ 
% 3.69/0.99  Current options:
% 3.69/0.99  ------ 
% 3.69/0.99  
% 3.69/0.99  
% 3.69/0.99  
% 3.69/0.99  
% 3.69/0.99  ------ Proving...
% 3.69/0.99  
% 3.69/0.99  
% 3.69/0.99  % SZS status Theorem for theBenchmark.p
% 3.69/0.99  
% 3.69/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.69/0.99  
% 3.69/0.99  fof(f2,axiom,(
% 3.69/0.99    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 3.69/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.69/0.99  
% 3.69/0.99  fof(f11,plain,(
% 3.69/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.69/0.99    inference(ennf_transformation,[],[f2])).
% 3.69/0.99  
% 3.69/0.99  fof(f12,plain,(
% 3.69/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 3.69/0.99    inference(flattening,[],[f11])).
% 3.69/0.99  
% 3.69/0.99  fof(f42,plain,(
% 3.69/0.99    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 3.69/0.99    inference(cnf_transformation,[],[f12])).
% 3.69/0.99  
% 3.69/0.99  fof(f3,axiom,(
% 3.69/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 3.69/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.69/0.99  
% 3.69/0.99  fof(f13,plain,(
% 3.69/0.99    ! [X0,X1,X2] : ((r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 3.69/0.99    inference(ennf_transformation,[],[f3])).
% 3.69/0.99  
% 3.69/0.99  fof(f14,plain,(
% 3.69/0.99    ! [X0,X1,X2] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 3.69/0.99    inference(flattening,[],[f13])).
% 3.69/0.99  
% 3.69/0.99  fof(f43,plain,(
% 3.69/0.99    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 3.69/0.99    inference(cnf_transformation,[],[f14])).
% 3.69/0.99  
% 3.69/0.99  fof(f8,conjecture,(
% 3.69/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <=> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))))))),
% 3.69/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.69/0.99  
% 3.69/0.99  fof(f9,negated_conjecture,(
% 3.69/0.99    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <=> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))))))),
% 3.69/0.99    inference(negated_conjecture,[],[f8])).
% 3.69/0.99  
% 3.69/0.99  fof(f22,plain,(
% 3.69/0.99    ? [X0] : (? [X1] : (? [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <~> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0)))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 3.69/0.99    inference(ennf_transformation,[],[f9])).
% 3.69/0.99  
% 3.69/0.99  fof(f23,plain,(
% 3.69/0.99    ? [X0] : (? [X1] : (? [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <~> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0)))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 3.69/0.99    inference(flattening,[],[f22])).
% 3.69/0.99  
% 3.69/0.99  fof(f33,plain,(
% 3.69/0.99    ? [X0] : (? [X1] : (? [X2] : (((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0))) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 3.69/0.99    inference(nnf_transformation,[],[f23])).
% 3.69/0.99  
% 3.69/0.99  fof(f34,plain,(
% 3.69/0.99    ? [X0] : (? [X1] : (? [X2] : ((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 3.69/0.99    inference(flattening,[],[f33])).
% 3.69/0.99  
% 3.69/0.99  fof(f37,plain,(
% 3.69/0.99    ( ! [X0,X1] : (? [X2] : ((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) => ((~r1_tarski(k9_relat_1(X0,sK4),k1_relat_1(X1)) | ~r1_tarski(sK4,k1_relat_1(X0)) | ~r1_tarski(sK4,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,sK4),k1_relat_1(X1)) & r1_tarski(sK4,k1_relat_1(X0))) | r1_tarski(sK4,k1_relat_1(k5_relat_1(X0,X1)))))) )),
% 3.69/0.99    introduced(choice_axiom,[])).
% 3.69/0.99  
% 3.69/0.99  fof(f36,plain,(
% 3.69/0.99    ( ! [X0] : (? [X1] : (? [X2] : ((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) => (? [X2] : ((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(sK3)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,sK3)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(sK3)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,sK3))))) & v1_funct_1(sK3) & v1_relat_1(sK3))) )),
% 3.69/0.99    introduced(choice_axiom,[])).
% 3.69/0.99  
% 3.69/0.99  fof(f35,plain,(
% 3.69/0.99    ? [X0] : (? [X1] : (? [X2] : ((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (? [X2] : ((~r1_tarski(k9_relat_1(sK2,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(sK2)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(sK2,X1)))) & ((r1_tarski(k9_relat_1(sK2,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(sK2))) | r1_tarski(X2,k1_relat_1(k5_relat_1(sK2,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 3.69/0.99    introduced(choice_axiom,[])).
% 3.69/0.99  
% 3.69/0.99  fof(f38,plain,(
% 3.69/0.99    (((~r1_tarski(k9_relat_1(sK2,sK4),k1_relat_1(sK3)) | ~r1_tarski(sK4,k1_relat_1(sK2)) | ~r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3)))) & ((r1_tarski(k9_relat_1(sK2,sK4),k1_relat_1(sK3)) & r1_tarski(sK4,k1_relat_1(sK2))) | r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3))))) & v1_funct_1(sK3) & v1_relat_1(sK3)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 3.69/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f34,f37,f36,f35])).
% 3.69/0.99  
% 3.69/0.99  fof(f53,plain,(
% 3.69/0.99    v1_relat_1(sK2)),
% 3.69/0.99    inference(cnf_transformation,[],[f38])).
% 3.69/0.99  
% 3.69/0.99  fof(f55,plain,(
% 3.69/0.99    v1_relat_1(sK3)),
% 3.69/0.99    inference(cnf_transformation,[],[f38])).
% 3.69/0.99  
% 3.69/0.99  fof(f4,axiom,(
% 3.69/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 3.69/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.69/0.99  
% 3.69/0.99  fof(f15,plain,(
% 3.69/0.99    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.69/0.99    inference(ennf_transformation,[],[f4])).
% 3.69/0.99  
% 3.69/0.99  fof(f44,plain,(
% 3.69/0.99    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.69/0.99    inference(cnf_transformation,[],[f15])).
% 3.69/0.99  
% 3.69/0.99  fof(f1,axiom,(
% 3.69/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.69/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.69/0.99  
% 3.69/0.99  fof(f10,plain,(
% 3.69/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.69/0.99    inference(ennf_transformation,[],[f1])).
% 3.69/0.99  
% 3.69/0.99  fof(f24,plain,(
% 3.69/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.69/0.99    inference(nnf_transformation,[],[f10])).
% 3.69/0.99  
% 3.69/0.99  fof(f25,plain,(
% 3.69/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.69/0.99    inference(rectify,[],[f24])).
% 3.69/0.99  
% 3.69/0.99  fof(f26,plain,(
% 3.69/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.69/0.99    introduced(choice_axiom,[])).
% 3.69/0.99  
% 3.69/0.99  fof(f27,plain,(
% 3.69/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.69/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).
% 3.69/0.99  
% 3.69/0.99  fof(f40,plain,(
% 3.69/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.69/0.99    inference(cnf_transformation,[],[f27])).
% 3.69/0.99  
% 3.69/0.99  fof(f5,axiom,(
% 3.69/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))))),
% 3.69/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.69/0.99  
% 3.69/0.99  fof(f16,plain,(
% 3.69/0.99    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.69/0.99    inference(ennf_transformation,[],[f5])).
% 3.69/0.99  
% 3.69/0.99  fof(f17,plain,(
% 3.69/0.99    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.69/0.99    inference(flattening,[],[f16])).
% 3.69/0.99  
% 3.69/0.99  fof(f28,plain,(
% 3.69/0.99    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : (((~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0)))) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X3,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.69/0.99    inference(nnf_transformation,[],[f17])).
% 3.69/0.99  
% 3.69/0.99  fof(f29,plain,(
% 3.69/0.99    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0))) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X3,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.69/0.99    inference(flattening,[],[f28])).
% 3.69/0.99  
% 3.69/0.99  fof(f30,plain,(
% 3.69/0.99    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k1_funct_1(X0,X4),X1) | ~r2_hidden(X4,k1_relat_1(X0))) & ((r2_hidden(k1_funct_1(X0,X4),X1) & r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X4,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.69/0.99    inference(rectify,[],[f29])).
% 3.69/0.99  
% 3.69/0.99  fof(f31,plain,(
% 3.69/0.99    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X3,X2))) => ((~r2_hidden(k1_funct_1(X0,sK1(X0,X1,X2)),X1) | ~r2_hidden(sK1(X0,X1,X2),k1_relat_1(X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(k1_funct_1(X0,sK1(X0,X1,X2)),X1) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X0))) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 3.69/0.99    introduced(choice_axiom,[])).
% 3.69/0.99  
% 3.69/0.99  fof(f32,plain,(
% 3.69/0.99    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ((~r2_hidden(k1_funct_1(X0,sK1(X0,X1,X2)),X1) | ~r2_hidden(sK1(X0,X1,X2),k1_relat_1(X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(k1_funct_1(X0,sK1(X0,X1,X2)),X1) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X0))) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k1_funct_1(X0,X4),X1) | ~r2_hidden(X4,k1_relat_1(X0))) & ((r2_hidden(k1_funct_1(X0,X4),X1) & r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X4,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.69/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f31])).
% 3.69/0.99  
% 3.69/0.99  fof(f45,plain,(
% 3.69/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X4,X2) | k10_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.69/0.99    inference(cnf_transformation,[],[f32])).
% 3.69/0.99  
% 3.69/0.99  fof(f62,plain,(
% 3.69/0.99    ( ! [X4,X0,X1] : (r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X4,k10_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.69/0.99    inference(equality_resolution,[],[f45])).
% 3.69/0.99  
% 3.69/0.99  fof(f54,plain,(
% 3.69/0.99    v1_funct_1(sK2)),
% 3.69/0.99    inference(cnf_transformation,[],[f38])).
% 3.69/0.99  
% 3.69/0.99  fof(f41,plain,(
% 3.69/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 3.69/0.99    inference(cnf_transformation,[],[f27])).
% 3.69/0.99  
% 3.69/0.99  fof(f58,plain,(
% 3.69/0.99    r1_tarski(k9_relat_1(sK2,sK4),k1_relat_1(sK3)) | r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3)))),
% 3.69/0.99    inference(cnf_transformation,[],[f38])).
% 3.69/0.99  
% 3.69/0.99  fof(f7,axiom,(
% 3.69/0.99    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 3.69/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.69/0.99  
% 3.69/0.99  fof(f20,plain,(
% 3.69/0.99    ! [X0,X1,X2] : ((r1_tarski(X0,k10_relat_1(X2,X1)) | (~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.69/0.99    inference(ennf_transformation,[],[f7])).
% 3.69/0.99  
% 3.69/0.99  fof(f21,plain,(
% 3.69/0.99    ! [X0,X1,X2] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.69/0.99    inference(flattening,[],[f20])).
% 3.69/0.99  
% 3.69/0.99  fof(f52,plain,(
% 3.69/0.99    ( ! [X2,X0,X1] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.69/0.99    inference(cnf_transformation,[],[f21])).
% 3.69/0.99  
% 3.69/0.99  fof(f57,plain,(
% 3.69/0.99    r1_tarski(sK4,k1_relat_1(sK2)) | r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3)))),
% 3.69/0.99    inference(cnf_transformation,[],[f38])).
% 3.69/0.99  
% 3.69/0.99  fof(f6,axiom,(
% 3.69/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 3.69/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.69/0.99  
% 3.69/0.99  fof(f18,plain,(
% 3.69/0.99    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.69/0.99    inference(ennf_transformation,[],[f6])).
% 3.69/0.99  
% 3.69/0.99  fof(f19,plain,(
% 3.69/0.99    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.69/0.99    inference(flattening,[],[f18])).
% 3.69/0.99  
% 3.69/0.99  fof(f51,plain,(
% 3.69/0.99    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.69/0.99    inference(cnf_transformation,[],[f19])).
% 3.69/0.99  
% 3.69/0.99  fof(f59,plain,(
% 3.69/0.99    ~r1_tarski(k9_relat_1(sK2,sK4),k1_relat_1(sK3)) | ~r1_tarski(sK4,k1_relat_1(sK2)) | ~r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3)))),
% 3.69/0.99    inference(cnf_transformation,[],[f38])).
% 3.69/0.99  
% 3.69/0.99  cnf(c_3,plain,
% 3.69/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 3.69/0.99      inference(cnf_transformation,[],[f42]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_1548,plain,
% 3.69/0.99      ( ~ r1_tarski(X0,X1)
% 3.69/0.99      | ~ r1_tarski(X1,k1_relat_1(sK3))
% 3.69/0.99      | r1_tarski(X0,k1_relat_1(sK3)) ),
% 3.69/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_2156,plain,
% 3.69/0.99      ( ~ r1_tarski(X0,k1_relat_1(sK3))
% 3.69/0.99      | ~ r1_tarski(k9_relat_1(sK2,X1),X0)
% 3.69/0.99      | r1_tarski(k9_relat_1(sK2,X1),k1_relat_1(sK3)) ),
% 3.69/0.99      inference(instantiation,[status(thm)],[c_1548]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_4213,plain,
% 3.69/0.99      ( ~ r1_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(sK3))))
% 3.69/0.99      | r1_tarski(k9_relat_1(sK2,X0),k1_relat_1(sK3))
% 3.69/0.99      | ~ r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(sK3))),k1_relat_1(sK3)) ),
% 3.69/0.99      inference(instantiation,[status(thm)],[c_2156]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_13364,plain,
% 3.69/0.99      ( ~ r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(sK3))),k1_relat_1(sK3))
% 3.69/0.99      | ~ r1_tarski(k9_relat_1(sK2,sK4),k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(sK3))))
% 3.69/0.99      | r1_tarski(k9_relat_1(sK2,sK4),k1_relat_1(sK3)) ),
% 3.69/0.99      inference(instantiation,[status(thm)],[c_4213]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_4,plain,
% 3.69/0.99      ( ~ r1_tarski(X0,X1)
% 3.69/0.99      | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
% 3.69/0.99      | ~ v1_relat_1(X2) ),
% 3.69/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_1414,plain,
% 3.69/0.99      ( ~ r1_tarski(X0,X1)
% 3.69/0.99      | r1_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))
% 3.69/0.99      | ~ v1_relat_1(sK2) ),
% 3.69/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_2908,plain,
% 3.69/0.99      ( r1_tarski(k9_relat_1(sK2,sK4),k9_relat_1(sK2,X0))
% 3.69/0.99      | ~ r1_tarski(sK4,X0)
% 3.69/0.99      | ~ v1_relat_1(sK2) ),
% 3.69/0.99      inference(instantiation,[status(thm)],[c_1414]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_13363,plain,
% 3.69/0.99      ( r1_tarski(k9_relat_1(sK2,sK4),k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(sK3))))
% 3.69/0.99      | ~ r1_tarski(sK4,k10_relat_1(sK2,k1_relat_1(sK3)))
% 3.69/0.99      | ~ v1_relat_1(sK2) ),
% 3.69/0.99      inference(instantiation,[status(thm)],[c_2908]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_608,plain,
% 3.69/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.69/0.99      theory(equality) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_2421,plain,
% 3.69/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(sK4,X2) | X2 != X1 | sK4 != X0 ),
% 3.69/0.99      inference(instantiation,[status(thm)],[c_608]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_3114,plain,
% 3.69/0.99      ( ~ r1_tarski(sK4,X0) | r1_tarski(sK4,X1) | X1 != X0 | sK4 != sK4 ),
% 3.69/0.99      inference(instantiation,[status(thm)],[c_2421]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_5633,plain,
% 3.69/0.99      ( r1_tarski(sK4,X0)
% 3.69/0.99      | ~ r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3)))
% 3.69/0.99      | X0 != k1_relat_1(k5_relat_1(sK2,sK3))
% 3.69/0.99      | sK4 != sK4 ),
% 3.69/0.99      inference(instantiation,[status(thm)],[c_3114]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_9521,plain,
% 3.69/0.99      ( r1_tarski(sK4,k10_relat_1(sK2,k1_relat_1(sK3)))
% 3.69/0.99      | ~ r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3)))
% 3.69/0.99      | k10_relat_1(sK2,k1_relat_1(sK3)) != k1_relat_1(k5_relat_1(sK2,sK3))
% 3.69/0.99      | sK4 != sK4 ),
% 3.69/0.99      inference(instantiation,[status(thm)],[c_5633]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_20,negated_conjecture,
% 3.69/0.99      ( v1_relat_1(sK2) ),
% 3.69/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_1107,plain,
% 3.69/0.99      ( v1_relat_1(sK2) = iProver_top ),
% 3.69/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_18,negated_conjecture,
% 3.69/0.99      ( v1_relat_1(sK3) ),
% 3.69/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_1108,plain,
% 3.69/0.99      ( v1_relat_1(sK3) = iProver_top ),
% 3.69/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_5,plain,
% 3.69/0.99      ( ~ v1_relat_1(X0)
% 3.69/0.99      | ~ v1_relat_1(X1)
% 3.69/0.99      | k10_relat_1(X1,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(X1,X0)) ),
% 3.69/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_1112,plain,
% 3.69/0.99      ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
% 3.69/0.99      | v1_relat_1(X0) != iProver_top
% 3.69/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.69/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_2661,plain,
% 3.69/0.99      ( k10_relat_1(X0,k1_relat_1(sK3)) = k1_relat_1(k5_relat_1(X0,sK3))
% 3.69/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.69/0.99      inference(superposition,[status(thm)],[c_1108,c_1112]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_2967,plain,
% 3.69/0.99      ( k10_relat_1(sK2,k1_relat_1(sK3)) = k1_relat_1(k5_relat_1(sK2,sK3)) ),
% 3.69/0.99      inference(superposition,[status(thm)],[c_1107,c_2661]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_1,plain,
% 3.69/0.99      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.69/0.99      inference(cnf_transformation,[],[f40]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_1116,plain,
% 3.69/0.99      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 3.69/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.69/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_11,plain,
% 3.69/0.99      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 3.69/0.99      | r2_hidden(X0,k1_relat_1(X1))
% 3.69/0.99      | ~ v1_funct_1(X1)
% 3.69/0.99      | ~ v1_relat_1(X1) ),
% 3.69/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_19,negated_conjecture,
% 3.69/0.99      ( v1_funct_1(sK2) ),
% 3.69/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_490,plain,
% 3.69/0.99      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 3.69/0.99      | r2_hidden(X0,k1_relat_1(X1))
% 3.69/0.99      | ~ v1_relat_1(X1)
% 3.69/0.99      | sK2 != X1 ),
% 3.69/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_19]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_491,plain,
% 3.69/0.99      ( ~ r2_hidden(X0,k10_relat_1(sK2,X1))
% 3.69/0.99      | r2_hidden(X0,k1_relat_1(sK2))
% 3.69/0.99      | ~ v1_relat_1(sK2) ),
% 3.69/0.99      inference(unflattening,[status(thm)],[c_490]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_495,plain,
% 3.69/0.99      ( r2_hidden(X0,k1_relat_1(sK2))
% 3.69/0.99      | ~ r2_hidden(X0,k10_relat_1(sK2,X1)) ),
% 3.69/0.99      inference(global_propositional_subsumption,
% 3.69/0.99                [status(thm)],
% 3.69/0.99                [c_491,c_20]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_496,plain,
% 3.69/0.99      ( ~ r2_hidden(X0,k10_relat_1(sK2,X1))
% 3.69/0.99      | r2_hidden(X0,k1_relat_1(sK2)) ),
% 3.69/0.99      inference(renaming,[status(thm)],[c_495]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_1093,plain,
% 3.69/0.99      ( r2_hidden(X0,k10_relat_1(sK2,X1)) != iProver_top
% 3.69/0.99      | r2_hidden(X0,k1_relat_1(sK2)) = iProver_top ),
% 3.69/0.99      inference(predicate_to_equality,[status(thm)],[c_496]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_1595,plain,
% 3.69/0.99      ( r2_hidden(sK0(k10_relat_1(sK2,X0),X1),k1_relat_1(sK2)) = iProver_top
% 3.69/0.99      | r1_tarski(k10_relat_1(sK2,X0),X1) = iProver_top ),
% 3.69/0.99      inference(superposition,[status(thm)],[c_1116,c_1093]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_0,plain,
% 3.69/0.99      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 3.69/0.99      inference(cnf_transformation,[],[f41]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_1117,plain,
% 3.69/0.99      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 3.69/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.69/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_6334,plain,
% 3.69/0.99      ( r1_tarski(k10_relat_1(sK2,X0),k1_relat_1(sK2)) = iProver_top ),
% 3.69/0.99      inference(superposition,[status(thm)],[c_1595,c_1117]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_6357,plain,
% 3.69/0.99      ( r1_tarski(k1_relat_1(k5_relat_1(sK2,sK3)),k1_relat_1(sK2)) = iProver_top ),
% 3.69/0.99      inference(superposition,[status(thm)],[c_2967,c_6334]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_6369,plain,
% 3.69/0.99      ( r1_tarski(k1_relat_1(k5_relat_1(sK2,sK3)),k1_relat_1(sK2)) ),
% 3.69/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_6357]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_15,negated_conjecture,
% 3.69/0.99      ( r1_tarski(k9_relat_1(sK2,sK4),k1_relat_1(sK3))
% 3.69/0.99      | r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3))) ),
% 3.69/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_1110,plain,
% 3.69/0.99      ( r1_tarski(k9_relat_1(sK2,sK4),k1_relat_1(sK3)) = iProver_top
% 3.69/0.99      | r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3))) = iProver_top ),
% 3.69/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_13,plain,
% 3.69/0.99      ( r1_tarski(X0,k10_relat_1(X1,X2))
% 3.69/0.99      | ~ r1_tarski(X0,k1_relat_1(X1))
% 3.69/0.99      | ~ r1_tarski(k9_relat_1(X1,X0),X2)
% 3.69/0.99      | ~ v1_funct_1(X1)
% 3.69/0.99      | ~ v1_relat_1(X1) ),
% 3.69/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_469,plain,
% 3.69/0.99      ( r1_tarski(X0,k10_relat_1(X1,X2))
% 3.69/0.99      | ~ r1_tarski(X0,k1_relat_1(X1))
% 3.69/0.99      | ~ r1_tarski(k9_relat_1(X1,X0),X2)
% 3.69/0.99      | ~ v1_relat_1(X1)
% 3.69/0.99      | sK2 != X1 ),
% 3.69/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_19]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_470,plain,
% 3.69/0.99      ( r1_tarski(X0,k10_relat_1(sK2,X1))
% 3.69/0.99      | ~ r1_tarski(X0,k1_relat_1(sK2))
% 3.69/0.99      | ~ r1_tarski(k9_relat_1(sK2,X0),X1)
% 3.69/0.99      | ~ v1_relat_1(sK2) ),
% 3.69/0.99      inference(unflattening,[status(thm)],[c_469]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_474,plain,
% 3.69/0.99      ( ~ r1_tarski(k9_relat_1(sK2,X0),X1)
% 3.69/0.99      | ~ r1_tarski(X0,k1_relat_1(sK2))
% 3.69/0.99      | r1_tarski(X0,k10_relat_1(sK2,X1)) ),
% 3.69/0.99      inference(global_propositional_subsumption,
% 3.69/0.99                [status(thm)],
% 3.69/0.99                [c_470,c_20]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_475,plain,
% 3.69/0.99      ( r1_tarski(X0,k10_relat_1(sK2,X1))
% 3.69/0.99      | ~ r1_tarski(X0,k1_relat_1(sK2))
% 3.69/0.99      | ~ r1_tarski(k9_relat_1(sK2,X0),X1) ),
% 3.69/0.99      inference(renaming,[status(thm)],[c_474]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_1094,plain,
% 3.69/0.99      ( r1_tarski(X0,k10_relat_1(sK2,X1)) = iProver_top
% 3.69/0.99      | r1_tarski(X0,k1_relat_1(sK2)) != iProver_top
% 3.69/0.99      | r1_tarski(k9_relat_1(sK2,X0),X1) != iProver_top ),
% 3.69/0.99      inference(predicate_to_equality,[status(thm)],[c_475]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_2207,plain,
% 3.69/0.99      ( r1_tarski(sK4,k10_relat_1(sK2,k1_relat_1(sK3))) = iProver_top
% 3.69/0.99      | r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3))) = iProver_top
% 3.69/0.99      | r1_tarski(sK4,k1_relat_1(sK2)) != iProver_top ),
% 3.69/0.99      inference(superposition,[status(thm)],[c_1110,c_1094]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_1497,plain,
% 3.69/0.99      ( r1_tarski(sK4,k10_relat_1(sK2,k1_relat_1(sK3)))
% 3.69/0.99      | r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3)))
% 3.69/0.99      | ~ r1_tarski(sK4,k1_relat_1(sK2)) ),
% 3.69/0.99      inference(resolution,[status(thm)],[c_475,c_15]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_16,negated_conjecture,
% 3.69/0.99      ( r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3)))
% 3.69/0.99      | r1_tarski(sK4,k1_relat_1(sK2)) ),
% 3.69/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_2246,plain,
% 3.69/0.99      ( r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3)))
% 3.69/0.99      | r1_tarski(sK4,k10_relat_1(sK2,k1_relat_1(sK3))) ),
% 3.69/0.99      inference(global_propositional_subsumption,
% 3.69/0.99                [status(thm)],
% 3.69/0.99                [c_1497,c_16]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_2247,plain,
% 3.69/0.99      ( r1_tarski(sK4,k10_relat_1(sK2,k1_relat_1(sK3)))
% 3.69/0.99      | r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3))) ),
% 3.69/0.99      inference(renaming,[status(thm)],[c_2246]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_2248,plain,
% 3.69/0.99      ( r1_tarski(sK4,k10_relat_1(sK2,k1_relat_1(sK3))) = iProver_top
% 3.69/0.99      | r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3))) = iProver_top ),
% 3.69/0.99      inference(predicate_to_equality,[status(thm)],[c_2247]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_5692,plain,
% 3.69/0.99      ( r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3))) = iProver_top
% 3.69/0.99      | r1_tarski(sK4,k10_relat_1(sK2,k1_relat_1(sK3))) = iProver_top ),
% 3.69/0.99      inference(global_propositional_subsumption,
% 3.69/0.99                [status(thm)],
% 3.69/0.99                [c_2207,c_2248]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_5693,plain,
% 3.69/0.99      ( r1_tarski(sK4,k10_relat_1(sK2,k1_relat_1(sK3))) = iProver_top
% 3.69/0.99      | r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3))) = iProver_top ),
% 3.69/0.99      inference(renaming,[status(thm)],[c_5692]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_5696,plain,
% 3.69/0.99      ( r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3))) = iProver_top ),
% 3.69/0.99      inference(light_normalisation,[status(thm)],[c_5693,c_2967]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_5698,plain,
% 3.69/0.99      ( r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3))) ),
% 3.69/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_5696]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_2672,plain,
% 3.69/0.99      ( k10_relat_1(sK2,k1_relat_1(sK3)) = k1_relat_1(k5_relat_1(sK2,sK3))
% 3.69/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.69/0.99      inference(instantiation,[status(thm)],[c_2661]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_1393,plain,
% 3.69/0.99      ( ~ r1_tarski(X0,k1_relat_1(sK2))
% 3.69/0.99      | ~ r1_tarski(sK4,X0)
% 3.69/0.99      | r1_tarski(sK4,k1_relat_1(sK2)) ),
% 3.69/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_2418,plain,
% 3.69/0.99      ( ~ r1_tarski(k1_relat_1(k5_relat_1(sK2,sK3)),k1_relat_1(sK2))
% 3.69/0.99      | ~ r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3)))
% 3.69/0.99      | r1_tarski(sK4,k1_relat_1(sK2)) ),
% 3.69/0.99      inference(instantiation,[status(thm)],[c_1393]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_12,plain,
% 3.69/0.99      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
% 3.69/0.99      | ~ v1_funct_1(X0)
% 3.69/0.99      | ~ v1_relat_1(X0) ),
% 3.69/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_310,plain,
% 3.69/0.99      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
% 3.69/0.99      | ~ v1_relat_1(X0)
% 3.69/0.99      | sK2 != X0 ),
% 3.69/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_19]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_311,plain,
% 3.69/0.99      ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0)),X0)
% 3.69/0.99      | ~ v1_relat_1(sK2) ),
% 3.69/0.99      inference(unflattening,[status(thm)],[c_310]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_315,plain,
% 3.69/0.99      ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0)),X0) ),
% 3.69/0.99      inference(global_propositional_subsumption,
% 3.69/0.99                [status(thm)],
% 3.69/0.99                [c_311,c_20]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_1565,plain,
% 3.69/0.99      ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(sK3))),k1_relat_1(sK3)) ),
% 3.69/0.99      inference(instantiation,[status(thm)],[c_315]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_606,plain,( X0 = X0 ),theory(equality) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_1537,plain,
% 3.69/0.99      ( sK4 = sK4 ),
% 3.69/0.99      inference(instantiation,[status(thm)],[c_606]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_14,negated_conjecture,
% 3.69/0.99      ( ~ r1_tarski(k9_relat_1(sK2,sK4),k1_relat_1(sK3))
% 3.69/0.99      | ~ r1_tarski(sK4,k1_relat_1(k5_relat_1(sK2,sK3)))
% 3.69/0.99      | ~ r1_tarski(sK4,k1_relat_1(sK2)) ),
% 3.69/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_21,plain,
% 3.69/0.99      ( v1_relat_1(sK2) = iProver_top ),
% 3.69/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(contradiction,plain,
% 3.69/0.99      ( $false ),
% 3.69/0.99      inference(minisat,
% 3.69/0.99                [status(thm)],
% 3.69/0.99                [c_13364,c_13363,c_9521,c_6369,c_5698,c_2672,c_2418,
% 3.69/0.99                 c_1565,c_1537,c_14,c_21,c_20]) ).
% 3.69/0.99  
% 3.69/0.99  
% 3.69/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.69/0.99  
% 3.69/0.99  ------                               Statistics
% 3.69/0.99  
% 3.69/0.99  ------ Selected
% 3.69/0.99  
% 3.69/0.99  total_time:                             0.39
% 3.69/0.99  
%------------------------------------------------------------------------------
