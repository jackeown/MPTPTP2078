%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0669+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:51 EST 2020

% Result     : Theorem 0.73s
% Output     : CNFRefutation 0.73s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 185 expanded)
%              Number of clauses        :   39 (  51 expanded)
%              Number of leaves         :    9 (  37 expanded)
%              Depth                    :   16
%              Number of atoms          :  369 (1123 expanded)
%              Number of equality atoms :   53 (  94 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,plain,(
    ! [X2,X1,X0] :
      ( sP0(X2,X1,X0)
    <=> ( ! [X3] :
            ( k1_funct_1(X1,X3) = k1_funct_1(X2,X3)
            | ~ r2_hidden(X3,k1_relat_1(X1)) )
        & ! [X4] :
            ( r2_hidden(X4,k1_relat_1(X1))
          <=> ( r2_hidden(k1_funct_1(X2,X4),X0)
              & r2_hidden(X4,k1_relat_1(X2)) ) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f18,plain,(
    ! [X2,X1,X0] :
      ( ( sP0(X2,X1,X0)
        | ? [X3] :
            ( k1_funct_1(X1,X3) != k1_funct_1(X2,X3)
            & r2_hidden(X3,k1_relat_1(X1)) )
        | ? [X4] :
            ( ( ~ r2_hidden(k1_funct_1(X2,X4),X0)
              | ~ r2_hidden(X4,k1_relat_1(X2))
              | ~ r2_hidden(X4,k1_relat_1(X1)) )
            & ( ( r2_hidden(k1_funct_1(X2,X4),X0)
                & r2_hidden(X4,k1_relat_1(X2)) )
              | r2_hidden(X4,k1_relat_1(X1)) ) ) )
      & ( ( ! [X3] :
              ( k1_funct_1(X1,X3) = k1_funct_1(X2,X3)
              | ~ r2_hidden(X3,k1_relat_1(X1)) )
          & ! [X4] :
              ( ( r2_hidden(X4,k1_relat_1(X1))
                | ~ r2_hidden(k1_funct_1(X2,X4),X0)
                | ~ r2_hidden(X4,k1_relat_1(X2)) )
              & ( ( r2_hidden(k1_funct_1(X2,X4),X0)
                  & r2_hidden(X4,k1_relat_1(X2)) )
                | ~ r2_hidden(X4,k1_relat_1(X1)) ) ) )
        | ~ sP0(X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f19,plain,(
    ! [X2,X1,X0] :
      ( ( sP0(X2,X1,X0)
        | ? [X3] :
            ( k1_funct_1(X1,X3) != k1_funct_1(X2,X3)
            & r2_hidden(X3,k1_relat_1(X1)) )
        | ? [X4] :
            ( ( ~ r2_hidden(k1_funct_1(X2,X4),X0)
              | ~ r2_hidden(X4,k1_relat_1(X2))
              | ~ r2_hidden(X4,k1_relat_1(X1)) )
            & ( ( r2_hidden(k1_funct_1(X2,X4),X0)
                & r2_hidden(X4,k1_relat_1(X2)) )
              | r2_hidden(X4,k1_relat_1(X1)) ) ) )
      & ( ( ! [X3] :
              ( k1_funct_1(X1,X3) = k1_funct_1(X2,X3)
              | ~ r2_hidden(X3,k1_relat_1(X1)) )
          & ! [X4] :
              ( ( r2_hidden(X4,k1_relat_1(X1))
                | ~ r2_hidden(k1_funct_1(X2,X4),X0)
                | ~ r2_hidden(X4,k1_relat_1(X2)) )
              & ( ( r2_hidden(k1_funct_1(X2,X4),X0)
                  & r2_hidden(X4,k1_relat_1(X2)) )
                | ~ r2_hidden(X4,k1_relat_1(X1)) ) ) )
        | ~ sP0(X2,X1,X0) ) ) ),
    inference(flattening,[],[f18])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( k1_funct_1(X0,X3) != k1_funct_1(X1,X3)
            & r2_hidden(X3,k1_relat_1(X1)) )
        | ? [X4] :
            ( ( ~ r2_hidden(k1_funct_1(X0,X4),X2)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X4,k1_relat_1(X1)) )
            & ( ( r2_hidden(k1_funct_1(X0,X4),X2)
                & r2_hidden(X4,k1_relat_1(X0)) )
              | r2_hidden(X4,k1_relat_1(X1)) ) ) )
      & ( ( ! [X5] :
              ( k1_funct_1(X0,X5) = k1_funct_1(X1,X5)
              | ~ r2_hidden(X5,k1_relat_1(X1)) )
          & ! [X6] :
              ( ( r2_hidden(X6,k1_relat_1(X1))
                | ~ r2_hidden(k1_funct_1(X0,X6),X2)
                | ~ r2_hidden(X6,k1_relat_1(X0)) )
              & ( ( r2_hidden(k1_funct_1(X0,X6),X2)
                  & r2_hidden(X6,k1_relat_1(X0)) )
                | ~ r2_hidden(X6,k1_relat_1(X1)) ) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f19])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( ( ~ r2_hidden(k1_funct_1(X0,X4),X2)
            | ~ r2_hidden(X4,k1_relat_1(X0))
            | ~ r2_hidden(X4,k1_relat_1(X1)) )
          & ( ( r2_hidden(k1_funct_1(X0,X4),X2)
              & r2_hidden(X4,k1_relat_1(X0)) )
            | r2_hidden(X4,k1_relat_1(X1)) ) )
     => ( ( ~ r2_hidden(k1_funct_1(X0,sK3(X0,X1,X2)),X2)
          | ~ r2_hidden(sK3(X0,X1,X2),k1_relat_1(X0))
          | ~ r2_hidden(sK3(X0,X1,X2),k1_relat_1(X1)) )
        & ( ( r2_hidden(k1_funct_1(X0,sK3(X0,X1,X2)),X2)
            & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X0)) )
          | r2_hidden(sK3(X0,X1,X2),k1_relat_1(X1)) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( k1_funct_1(X0,X3) != k1_funct_1(X1,X3)
          & r2_hidden(X3,k1_relat_1(X1)) )
     => ( k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1))
        & r2_hidden(sK2(X0,X1),k1_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1))
          & r2_hidden(sK2(X0,X1),k1_relat_1(X1)) )
        | ( ( ~ r2_hidden(k1_funct_1(X0,sK3(X0,X1,X2)),X2)
            | ~ r2_hidden(sK3(X0,X1,X2),k1_relat_1(X0))
            | ~ r2_hidden(sK3(X0,X1,X2),k1_relat_1(X1)) )
          & ( ( r2_hidden(k1_funct_1(X0,sK3(X0,X1,X2)),X2)
              & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X0)) )
            | r2_hidden(sK3(X0,X1,X2),k1_relat_1(X1)) ) ) )
      & ( ( ! [X5] :
              ( k1_funct_1(X0,X5) = k1_funct_1(X1,X5)
              | ~ r2_hidden(X5,k1_relat_1(X1)) )
          & ! [X6] :
              ( ( r2_hidden(X6,k1_relat_1(X1))
                | ~ r2_hidden(k1_funct_1(X0,X6),X2)
                | ~ r2_hidden(X6,k1_relat_1(X0)) )
              & ( ( r2_hidden(k1_funct_1(X0,X6),X2)
                  & r2_hidden(X6,k1_relat_1(X0)) )
                | ~ r2_hidden(X6,k1_relat_1(X1)) ) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f20,f22,f21])).

fof(f35,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,k1_relat_1(X1))
      | ~ r2_hidden(k1_funct_1(X0,X6),X2)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
        <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
            & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      <~> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      <~> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
        | ~ r2_hidden(X0,k1_relat_1(X2))
        | ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) )
      & ( ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) )
        | r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) )
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
        | ~ r2_hidden(X0,k1_relat_1(X2))
        | ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) )
      & ( ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) )
        | r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) )
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f26,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) )
        & ( ( r2_hidden(k1_funct_1(X2,X0),X1)
            & r2_hidden(X0,k1_relat_1(X2)) )
          | r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) )
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ( ~ r2_hidden(k1_funct_1(sK6,sK4),sK5)
        | ~ r2_hidden(sK4,k1_relat_1(sK6))
        | ~ r2_hidden(sK4,k1_relat_1(k8_relat_1(sK5,sK6))) )
      & ( ( r2_hidden(k1_funct_1(sK6,sK4),sK5)
          & r2_hidden(sK4,k1_relat_1(sK6)) )
        | r2_hidden(sK4,k1_relat_1(k8_relat_1(sK5,sK6))) )
      & v1_funct_1(sK6)
      & v1_relat_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ( ~ r2_hidden(k1_funct_1(sK6,sK4),sK5)
      | ~ r2_hidden(sK4,k1_relat_1(sK6))
      | ~ r2_hidden(sK4,k1_relat_1(k8_relat_1(sK5,sK6))) )
    & ( ( r2_hidden(k1_funct_1(sK6,sK4),sK5)
        & r2_hidden(sK4,k1_relat_1(sK6)) )
      | r2_hidden(sK4,k1_relat_1(k8_relat_1(sK5,sK6))) )
    & v1_funct_1(sK6)
    & v1_relat_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f25,f26])).

fof(f48,plain,
    ( ~ r2_hidden(k1_funct_1(sK6,sK4),sK5)
    | ~ r2_hidden(sK4,k1_relat_1(sK6))
    | ~ r2_hidden(sK4,k1_relat_1(k8_relat_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f27])).

fof(f44,plain,(
    v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f27])).

fof(f45,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f27])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( k8_relat_1(X0,X2) = X1
          <=> ( ! [X3] :
                  ( r2_hidden(X3,k1_relat_1(X1))
                 => k1_funct_1(X1,X3) = k1_funct_1(X2,X3) )
              & ! [X3] :
                  ( r2_hidden(X3,k1_relat_1(X1))
                <=> ( r2_hidden(k1_funct_1(X2,X3),X0)
                    & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( k8_relat_1(X0,X2) = X1
          <=> ( ! [X3] :
                  ( r2_hidden(X3,k1_relat_1(X1))
                 => k1_funct_1(X1,X3) = k1_funct_1(X2,X3) )
              & ! [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                <=> ( r2_hidden(k1_funct_1(X2,X4),X0)
                    & r2_hidden(X4,k1_relat_1(X2)) ) ) ) ) ) ) ),
    inference(rectify,[],[f3])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k8_relat_1(X0,X2) = X1
          <=> ( ! [X3] :
                  ( k1_funct_1(X1,X3) = k1_funct_1(X2,X3)
                  | ~ r2_hidden(X3,k1_relat_1(X1)) )
              & ! [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                <=> ( r2_hidden(k1_funct_1(X2,X4),X0)
                    & r2_hidden(X4,k1_relat_1(X2)) ) ) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k8_relat_1(X0,X2) = X1
          <=> ( ! [X3] :
                  ( k1_funct_1(X1,X3) = k1_funct_1(X2,X3)
                  | ~ r2_hidden(X3,k1_relat_1(X1)) )
              & ! [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                <=> ( r2_hidden(k1_funct_1(X2,X4),X0)
                    & r2_hidden(X4,k1_relat_1(X2)) ) ) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f10])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relat_1(X0,X2) = X1
      <=> sP0(X2,X1,X0) )
      | ~ sP1(X0,X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( sP1(X0,X1,X2)
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_folding,[],[f11,f15,f14])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( ( k8_relat_1(X0,X2) = X1
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | k8_relat_1(X0,X2) != X1 ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X1,X0)
      | k8_relat_1(X0,X2) != X1
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f49,plain,(
    ! [X2,X0] :
      ( sP0(X2,k8_relat_1(X0,X2),X0)
      | ~ sP1(X0,k8_relat_1(X0,X2),X2) ) ),
    inference(equality_resolution,[],[f31])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v1_funct_1(k8_relat_1(X0,X1))
        & v1_relat_1(k8_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k8_relat_1(X0,X1))
        & v1_relat_1(k8_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k8_relat_1(X0,X1))
        & v1_relat_1(k8_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f8])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k8_relat_1(X0,X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f33,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,k1_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f34,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X2)
      | ~ r2_hidden(X6,k1_relat_1(X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f47,plain,
    ( r2_hidden(k1_funct_1(sK6,sK4),sK5)
    | r2_hidden(sK4,k1_relat_1(k8_relat_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f27])).

fof(f46,plain,
    ( r2_hidden(sK4,k1_relat_1(sK6))
    | r2_hidden(sK4,k1_relat_1(k8_relat_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_12,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | r2_hidden(X3,k1_relat_1(X1))
    | ~ r2_hidden(k1_funct_1(X0,X3),X2) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_2285,plain,
    ( ~ sP0(X0_41,X1_41,X0_42)
    | ~ r2_hidden(X0_43,k1_relat_1(X0_41))
    | r2_hidden(X0_43,k1_relat_1(X1_41))
    | ~ r2_hidden(k1_funct_1(X0_41,X0_43),X0_42) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_2981,plain,
    ( ~ sP0(X0_41,k8_relat_1(sK5,sK6),X0_42)
    | ~ r2_hidden(k1_funct_1(X0_41,sK4),X0_42)
    | ~ r2_hidden(sK4,k1_relat_1(X0_41))
    | r2_hidden(sK4,k1_relat_1(k8_relat_1(sK5,sK6))) ),
    inference(instantiation,[status(thm)],[c_2285])).

cnf(c_2983,plain,
    ( ~ sP0(sK6,k8_relat_1(sK5,sK6),sK5)
    | ~ r2_hidden(k1_funct_1(sK6,sK4),sK5)
    | r2_hidden(sK4,k1_relat_1(k8_relat_1(sK5,sK6)))
    | ~ r2_hidden(sK4,k1_relat_1(sK6)) ),
    inference(instantiation,[status(thm)],[c_2981])).

cnf(c_16,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(sK6,sK4),sK5)
    | ~ r2_hidden(sK4,k1_relat_1(k8_relat_1(sK5,sK6)))
    | ~ r2_hidden(sK4,k1_relat_1(sK6)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2282,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(sK6,sK4),sK5)
    | ~ r2_hidden(sK4,k1_relat_1(k8_relat_1(sK5,sK6)))
    | ~ r2_hidden(sK4,k1_relat_1(sK6)) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_2679,plain,
    ( r2_hidden(k1_funct_1(sK6,sK4),sK5) != iProver_top
    | r2_hidden(sK4,k1_relat_1(k8_relat_1(sK5,sK6))) != iProver_top
    | r2_hidden(sK4,k1_relat_1(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2282])).

cnf(c_20,negated_conjecture,
    ( v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_21,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_19,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_22,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_25,plain,
    ( r2_hidden(k1_funct_1(sK6,sK4),sK5) != iProver_top
    | r2_hidden(sK4,k1_relat_1(k8_relat_1(sK5,sK6))) != iProver_top
    | r2_hidden(sK4,k1_relat_1(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_15,plain,
    ( sP1(X0,X1,X2)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_4,plain,
    ( ~ sP1(X0,k8_relat_1(X0,X1),X1)
    | sP0(X1,k8_relat_1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_253,plain,
    ( sP0(X0,k8_relat_1(X1,X0),X1)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | X0 != X3
    | X1 != X4
    | k8_relat_1(X1,X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_4])).

cnf(c_254,plain,
    ( sP0(X0,k8_relat_1(X1,X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k8_relat_1(X1,X0))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(k8_relat_1(X1,X0)) ),
    inference(unflattening,[status(thm)],[c_253])).

cnf(c_1,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k8_relat_1(X1,X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k8_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_258,plain,
    ( ~ v1_relat_1(X0)
    | sP0(X0,k8_relat_1(X1,X0),X1)
    | ~ v1_funct_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_254,c_1,c_0])).

cnf(c_259,plain,
    ( sP0(X0,k8_relat_1(X1,X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(renaming,[status(thm)],[c_258])).

cnf(c_2276,plain,
    ( sP0(X0_41,k8_relat_1(X0_42,X0_41),X0_42)
    | ~ v1_funct_1(X0_41)
    | ~ v1_relat_1(X0_41) ),
    inference(subtyping,[status(esa)],[c_259])).

cnf(c_2359,plain,
    ( sP0(X0_41,k8_relat_1(X0_42,X0_41),X0_42) = iProver_top
    | v1_funct_1(X0_41) != iProver_top
    | v1_relat_1(X0_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2276])).

cnf(c_2361,plain,
    ( sP0(sK6,k8_relat_1(sK5,sK6),sK5) = iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2359])).

cnf(c_14,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,k1_relat_1(X1))
    | r2_hidden(X3,k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_2283,plain,
    ( ~ sP0(X0_41,X1_41,X0_42)
    | ~ r2_hidden(X0_43,k1_relat_1(X1_41))
    | r2_hidden(X0_43,k1_relat_1(X0_41)) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_2856,plain,
    ( ~ sP0(X0_41,k8_relat_1(sK5,sK6),X0_42)
    | r2_hidden(sK4,k1_relat_1(X0_41))
    | ~ r2_hidden(sK4,k1_relat_1(k8_relat_1(sK5,sK6))) ),
    inference(instantiation,[status(thm)],[c_2283])).

cnf(c_2857,plain,
    ( sP0(X0_41,k8_relat_1(sK5,sK6),X0_42) != iProver_top
    | r2_hidden(sK4,k1_relat_1(X0_41)) = iProver_top
    | r2_hidden(sK4,k1_relat_1(k8_relat_1(sK5,sK6))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2856])).

cnf(c_2859,plain,
    ( sP0(sK6,k8_relat_1(sK5,sK6),sK5) != iProver_top
    | r2_hidden(sK4,k1_relat_1(k8_relat_1(sK5,sK6))) != iProver_top
    | r2_hidden(sK4,k1_relat_1(sK6)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2857])).

cnf(c_13,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X0,X3),X2) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_2284,plain,
    ( ~ sP0(X0_41,X1_41,X0_42)
    | ~ r2_hidden(X0_43,k1_relat_1(X1_41))
    | r2_hidden(k1_funct_1(X0_41,X0_43),X0_42) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_2861,plain,
    ( ~ sP0(X0_41,k8_relat_1(sK5,sK6),X0_42)
    | r2_hidden(k1_funct_1(X0_41,sK4),X0_42)
    | ~ r2_hidden(sK4,k1_relat_1(k8_relat_1(sK5,sK6))) ),
    inference(instantiation,[status(thm)],[c_2284])).

cnf(c_2862,plain,
    ( sP0(X0_41,k8_relat_1(sK5,sK6),X0_42) != iProver_top
    | r2_hidden(k1_funct_1(X0_41,sK4),X0_42) = iProver_top
    | r2_hidden(sK4,k1_relat_1(k8_relat_1(sK5,sK6))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2861])).

cnf(c_2864,plain,
    ( sP0(sK6,k8_relat_1(sK5,sK6),sK5) != iProver_top
    | r2_hidden(k1_funct_1(sK6,sK4),sK5) = iProver_top
    | r2_hidden(sK4,k1_relat_1(k8_relat_1(sK5,sK6))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2862])).

cnf(c_2898,plain,
    ( r2_hidden(sK4,k1_relat_1(k8_relat_1(sK5,sK6))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2679,c_21,c_22,c_25,c_2361,c_2859,c_2864])).

cnf(c_2900,plain,
    ( ~ r2_hidden(sK4,k1_relat_1(k8_relat_1(sK5,sK6))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2898])).

cnf(c_2360,plain,
    ( sP0(sK6,k8_relat_1(sK5,sK6),sK5)
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_2276])).

cnf(c_17,negated_conjecture,
    ( r2_hidden(k1_funct_1(sK6,sK4),sK5)
    | r2_hidden(sK4,k1_relat_1(k8_relat_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_18,negated_conjecture,
    ( r2_hidden(sK4,k1_relat_1(k8_relat_1(sK5,sK6)))
    | r2_hidden(sK4,k1_relat_1(sK6)) ),
    inference(cnf_transformation,[],[f46])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2983,c_2900,c_2360,c_17,c_18,c_19,c_20])).


%------------------------------------------------------------------------------
