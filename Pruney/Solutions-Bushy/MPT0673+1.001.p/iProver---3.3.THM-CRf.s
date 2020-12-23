%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0673+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:52 EST 2020

% Result     : Theorem 3.46s
% Output     : CNFRefutation 3.46s
% Verified   : 
% Statistics : Number of formulae       :  169 (1952 expanded)
%              Number of clauses        :  117 ( 687 expanded)
%              Number of leaves         :   13 ( 372 expanded)
%              Depth                    :   32
%              Number of atoms          :  688 (9320 expanded)
%              Number of equality atoms :  262 (1846 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
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

fof(f7,plain,(
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
    inference(rectify,[],[f4])).

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relat_1(X0,X2) = X1
      <=> sP0(X2,X1,X0) )
      | ~ sP1(X0,X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f17,plain,(
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

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( sP1(X0,X1,X2)
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_folding,[],[f14,f18,f17])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( ( k8_relat_1(X0,X2) = X1
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | k8_relat_1(X0,X2) != X1 ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X1,X0)
      | k8_relat_1(X0,X2) != X1
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f58,plain,(
    ! [X2,X0] :
      ( sP0(X2,k8_relat_1(X0,X2),X0)
      | ~ sP1(X0,k8_relat_1(X0,X2),X2) ) ),
    inference(equality_resolution,[],[f41])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v1_funct_1(k8_relat_1(X0,X1))
        & v1_relat_1(k8_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k8_relat_1(X0,X1))
        & v1_relat_1(k8_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k8_relat_1(X0,X1))
        & v1_relat_1(k8_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k8_relat_1(X0,X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f27,plain,(
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
    inference(rectify,[],[f26])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( ( ~ r2_hidden(k1_funct_1(X0,X4),X2)
            | ~ r2_hidden(X4,k1_relat_1(X0))
            | ~ r2_hidden(X4,k1_relat_1(X1)) )
          & ( ( r2_hidden(k1_funct_1(X0,X4),X2)
              & r2_hidden(X4,k1_relat_1(X0)) )
            | r2_hidden(X4,k1_relat_1(X1)) ) )
     => ( ( ~ r2_hidden(k1_funct_1(X0,sK5(X0,X1,X2)),X2)
          | ~ r2_hidden(sK5(X0,X1,X2),k1_relat_1(X0))
          | ~ r2_hidden(sK5(X0,X1,X2),k1_relat_1(X1)) )
        & ( ( r2_hidden(k1_funct_1(X0,sK5(X0,X1,X2)),X2)
            & r2_hidden(sK5(X0,X1,X2),k1_relat_1(X0)) )
          | r2_hidden(sK5(X0,X1,X2),k1_relat_1(X1)) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( k1_funct_1(X0,X3) != k1_funct_1(X1,X3)
          & r2_hidden(X3,k1_relat_1(X1)) )
     => ( k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
        & r2_hidden(sK4(X0,X1),k1_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
          & r2_hidden(sK4(X0,X1),k1_relat_1(X1)) )
        | ( ( ~ r2_hidden(k1_funct_1(X0,sK5(X0,X1,X2)),X2)
            | ~ r2_hidden(sK5(X0,X1,X2),k1_relat_1(X0))
            | ~ r2_hidden(sK5(X0,X1,X2),k1_relat_1(X1)) )
          & ( ( r2_hidden(k1_funct_1(X0,sK5(X0,X1,X2)),X2)
              & r2_hidden(sK5(X0,X1,X2),k1_relat_1(X0)) )
            | r2_hidden(sK5(X0,X1,X2),k1_relat_1(X1)) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f27,f29,f28])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
      | r2_hidden(sK5(X0,X1,X2),k1_relat_1(X0))
      | r2_hidden(sK5(X0,X1,X2),k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f46,plain,(
    ! [X2,X0,X5,X1] :
      ( k1_funct_1(X0,X5) = k1_funct_1(X1,X5)
      | ~ r2_hidden(X5,k1_relat_1(X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f9,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f20,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X1,X2] :
              ( X1 = X2
              | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
              | ~ r2_hidden(X2,k1_relat_1(X0))
              | ~ r2_hidden(X1,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f21,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f20])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( X1 != X2
          & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
          & r2_hidden(X2,k1_relat_1(X0))
          & r2_hidden(X1,k1_relat_1(X0)) )
     => ( sK2(X0) != sK3(X0)
        & k1_funct_1(X0,sK2(X0)) = k1_funct_1(X0,sK3(X0))
        & r2_hidden(sK3(X0),k1_relat_1(X0))
        & r2_hidden(sK2(X0),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ( sK2(X0) != sK3(X0)
            & k1_funct_1(X0,sK2(X0)) = k1_funct_1(X0,sK3(X0))
            & r2_hidden(sK3(X0),k1_relat_1(X0))
            & r2_hidden(sK2(X0),k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f21,f22])).

fof(f36,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | k1_funct_1(X0,sK2(X0)) = k1_funct_1(X0,sK3(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => v2_funct_1(k8_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( v2_funct_1(X1)
         => v2_funct_1(k8_relat_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ~ v2_funct_1(k8_relat_1(X0,X1))
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ~ v2_funct_1(k8_relat_1(X0,X1))
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f31,plain,
    ( ? [X0,X1] :
        ( ~ v2_funct_1(k8_relat_1(X0,X1))
        & v2_funct_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ~ v2_funct_1(k8_relat_1(sK6,sK7))
      & v2_funct_1(sK7)
      & v1_funct_1(sK7)
      & v1_relat_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ~ v2_funct_1(k8_relat_1(sK6,sK7))
    & v2_funct_1(sK7)
    & v1_funct_1(sK7)
    & v1_relat_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f16,f31])).

fof(f57,plain,(
    ~ v2_funct_1(k8_relat_1(sK6,sK7)) ),
    inference(cnf_transformation,[],[f32])).

fof(f54,plain,(
    v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f32])).

fof(f55,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f32])).

fof(f35,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | r2_hidden(sK3(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f43,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,k1_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f44,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X2)
      | ~ r2_hidden(X6,k1_relat_1(X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f45,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,k1_relat_1(X1))
      | ~ r2_hidden(k1_funct_1(X0,X6),X2)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f34,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | r2_hidden(sK2(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f33,plain,(
    ! [X4,X0,X3] :
      ( X3 = X4
      | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f37,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | sK2(X0) != sK3(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f56,plain,(
    v2_funct_1(sK7) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_20,plain,
    ( sP1(X0,X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_9,plain,
    ( ~ sP1(X0,k8_relat_1(X0,X1),X1)
    | sP0(X1,k8_relat_1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_289,plain,
    ( sP0(X0,k8_relat_1(X1,X0),X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | X0 != X3
    | X1 != X4
    | k8_relat_1(X1,X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_9])).

cnf(c_290,plain,
    ( sP0(X0,k8_relat_1(X1,X0),X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(k8_relat_1(X1,X0))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k8_relat_1(X1,X0)) ),
    inference(unflattening,[status(thm)],[c_289])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k8_relat_1(X1,X0))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k8_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_294,plain,
    ( ~ v1_funct_1(X0)
    | sP0(X0,k8_relat_1(X1,X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_290,c_7,c_6])).

cnf(c_295,plain,
    ( sP0(X0,k8_relat_1(X1,X0),X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(renaming,[status(thm)],[c_294])).

cnf(c_2788,plain,
    ( sP0(X0_43,k8_relat_1(X0_44,X0_43),X0_44)
    | ~ v1_relat_1(X0_43)
    | ~ v1_funct_1(X0_43) ),
    inference(subtyping,[status(esa)],[c_295])).

cnf(c_3270,plain,
    ( sP0(X0_43,k8_relat_1(X0_44,X0_43),X0_44) = iProver_top
    | v1_relat_1(X0_43) != iProver_top
    | v1_funct_1(X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2788])).

cnf(c_12,plain,
    ( sP0(X0,X1,X2)
    | r2_hidden(sK5(X0,X1,X2),k1_relat_1(X0))
    | r2_hidden(sK5(X0,X1,X2),k1_relat_1(X1))
    | k1_funct_1(X1,sK4(X0,X1)) != k1_funct_1(X0,sK4(X0,X1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2801,plain,
    ( sP0(X0_43,X1_43,X0_44)
    | r2_hidden(sK5(X0_43,X1_43,X0_44),k1_relat_1(X0_43))
    | r2_hidden(sK5(X0_43,X1_43,X0_44),k1_relat_1(X1_43))
    | k1_funct_1(X1_43,sK4(X0_43,X1_43)) != k1_funct_1(X0_43,sK4(X0_43,X1_43)) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_3257,plain,
    ( k1_funct_1(X0_43,sK4(X1_43,X0_43)) != k1_funct_1(X1_43,sK4(X1_43,X0_43))
    | sP0(X1_43,X0_43,X0_44) = iProver_top
    | r2_hidden(sK5(X1_43,X0_43,X0_44),k1_relat_1(X1_43)) = iProver_top
    | r2_hidden(sK5(X1_43,X0_43,X0_44),k1_relat_1(X0_43)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2801])).

cnf(c_4724,plain,
    ( sP0(X0_43,X0_43,X0_44) = iProver_top
    | r2_hidden(sK5(X0_43,X0_43,X0_44),k1_relat_1(X0_43)) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3257])).

cnf(c_16,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,k1_relat_1(X1))
    | k1_funct_1(X1,X3) = k1_funct_1(X0,X3) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_2797,plain,
    ( ~ sP0(X0_43,X1_43,X0_44)
    | ~ r2_hidden(X0_45,k1_relat_1(X1_43))
    | k1_funct_1(X1_43,X0_45) = k1_funct_1(X0_43,X0_45) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_3261,plain,
    ( k1_funct_1(X0_43,X0_45) = k1_funct_1(X1_43,X0_45)
    | sP0(X1_43,X0_43,X0_44) != iProver_top
    | r2_hidden(X0_45,k1_relat_1(X0_43)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2797])).

cnf(c_4834,plain,
    ( k1_funct_1(X0_43,sK5(X1_43,X1_43,X0_44)) = k1_funct_1(X1_43,sK5(X1_43,X1_43,X0_44))
    | sP0(X0_43,X1_43,X1_44) != iProver_top
    | sP0(X1_43,X1_43,X0_44) = iProver_top ),
    inference(superposition,[status(thm)],[c_4724,c_3261])).

cnf(c_5001,plain,
    ( k1_funct_1(k8_relat_1(X0_44,X0_43),sK5(k8_relat_1(X0_44,X0_43),k8_relat_1(X0_44,X0_43),X1_44)) = k1_funct_1(X0_43,sK5(k8_relat_1(X0_44,X0_43),k8_relat_1(X0_44,X0_43),X1_44))
    | sP0(k8_relat_1(X0_44,X0_43),k8_relat_1(X0_44,X0_43),X1_44) = iProver_top
    | v1_relat_1(X0_43) != iProver_top
    | v1_funct_1(X0_43) != iProver_top ),
    inference(superposition,[status(thm)],[c_3270,c_4834])).

cnf(c_2804,plain,
    ( ~ v1_relat_1(X0_43)
    | ~ v1_funct_1(X0_43)
    | v1_funct_1(k8_relat_1(X0_44,X0_43)) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_3254,plain,
    ( v1_relat_1(X0_43) != iProver_top
    | v1_funct_1(X0_43) != iProver_top
    | v1_funct_1(k8_relat_1(X0_44,X0_43)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2804])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k8_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_2805,plain,
    ( ~ v1_relat_1(X0_43)
    | v1_relat_1(k8_relat_1(X0_44,X0_43)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_3253,plain,
    ( v1_relat_1(X0_43) != iProver_top
    | v1_relat_1(k8_relat_1(X0_44,X0_43)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2805])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | k1_funct_1(X0,sK3(X0)) = k1_funct_1(X0,sK2(X0)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_2809,plain,
    ( ~ v1_relat_1(X0_43)
    | ~ v1_funct_1(X0_43)
    | v2_funct_1(X0_43)
    | k1_funct_1(X0_43,sK3(X0_43)) = k1_funct_1(X0_43,sK2(X0_43)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_3249,plain,
    ( k1_funct_1(X0_43,sK3(X0_43)) = k1_funct_1(X0_43,sK2(X0_43))
    | v1_relat_1(X0_43) != iProver_top
    | v1_funct_1(X0_43) != iProver_top
    | v2_funct_1(X0_43) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2809])).

cnf(c_4200,plain,
    ( k1_funct_1(k8_relat_1(X0_44,X0_43),sK2(k8_relat_1(X0_44,X0_43))) = k1_funct_1(k8_relat_1(X0_44,X0_43),sK3(k8_relat_1(X0_44,X0_43)))
    | v1_relat_1(X0_43) != iProver_top
    | v1_funct_1(k8_relat_1(X0_44,X0_43)) != iProver_top
    | v2_funct_1(k8_relat_1(X0_44,X0_43)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3253,c_3249])).

cnf(c_5760,plain,
    ( k1_funct_1(k8_relat_1(X0_44,X0_43),sK2(k8_relat_1(X0_44,X0_43))) = k1_funct_1(k8_relat_1(X0_44,X0_43),sK3(k8_relat_1(X0_44,X0_43)))
    | v1_relat_1(X0_43) != iProver_top
    | v1_funct_1(X0_43) != iProver_top
    | v2_funct_1(k8_relat_1(X0_44,X0_43)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3254,c_4200])).

cnf(c_21,negated_conjecture,
    ( ~ v2_funct_1(k8_relat_1(sK6,sK7)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2793,negated_conjecture,
    ( ~ v2_funct_1(k8_relat_1(sK6,sK7)) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_3265,plain,
    ( v2_funct_1(k8_relat_1(sK6,sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2793])).

cnf(c_5864,plain,
    ( k1_funct_1(k8_relat_1(sK6,sK7),sK2(k8_relat_1(sK6,sK7))) = k1_funct_1(k8_relat_1(sK6,sK7),sK3(k8_relat_1(sK6,sK7)))
    | v1_relat_1(sK7) != iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_5760,c_3265])).

cnf(c_24,negated_conjecture,
    ( v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_25,plain,
    ( v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_23,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_26,plain,
    ( v1_funct_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_28,plain,
    ( v2_funct_1(k8_relat_1(sK6,sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2843,plain,
    ( v1_relat_1(X0_43) != iProver_top
    | v1_funct_1(X0_43) != iProver_top
    | v1_funct_1(k8_relat_1(X0_44,X0_43)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2804])).

cnf(c_2845,plain,
    ( v1_relat_1(sK7) != iProver_top
    | v1_funct_1(k8_relat_1(sK6,sK7)) = iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2843])).

cnf(c_4210,plain,
    ( k1_funct_1(k8_relat_1(sK6,sK7),sK2(k8_relat_1(sK6,sK7))) = k1_funct_1(k8_relat_1(sK6,sK7),sK3(k8_relat_1(sK6,sK7)))
    | v1_relat_1(sK7) != iProver_top
    | v1_funct_1(k8_relat_1(sK6,sK7)) != iProver_top
    | v2_funct_1(k8_relat_1(sK6,sK7)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4200])).

cnf(c_5867,plain,
    ( k1_funct_1(k8_relat_1(sK6,sK7),sK2(k8_relat_1(sK6,sK7))) = k1_funct_1(k8_relat_1(sK6,sK7),sK3(k8_relat_1(sK6,sK7))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5864,c_25,c_26,c_28,c_2845,c_4210])).

cnf(c_2,plain,
    ( r2_hidden(sK3(X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_2808,plain,
    ( r2_hidden(sK3(X0_43),k1_relat_1(X0_43))
    | ~ v1_relat_1(X0_43)
    | ~ v1_funct_1(X0_43)
    | v2_funct_1(X0_43) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_3250,plain,
    ( r2_hidden(sK3(X0_43),k1_relat_1(X0_43)) = iProver_top
    | v1_relat_1(X0_43) != iProver_top
    | v1_funct_1(X0_43) != iProver_top
    | v2_funct_1(X0_43) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2808])).

cnf(c_19,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,k1_relat_1(X1))
    | r2_hidden(X3,k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_2794,plain,
    ( ~ sP0(X0_43,X1_43,X0_44)
    | ~ r2_hidden(X0_45,k1_relat_1(X1_43))
    | r2_hidden(X0_45,k1_relat_1(X0_43)) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_3264,plain,
    ( sP0(X0_43,X1_43,X0_44) != iProver_top
    | r2_hidden(X0_45,k1_relat_1(X1_43)) != iProver_top
    | r2_hidden(X0_45,k1_relat_1(X0_43)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2794])).

cnf(c_3841,plain,
    ( sP0(X0_43,X1_43,X0_44) != iProver_top
    | r2_hidden(sK3(X1_43),k1_relat_1(X0_43)) = iProver_top
    | v1_relat_1(X1_43) != iProver_top
    | v1_funct_1(X1_43) != iProver_top
    | v2_funct_1(X1_43) = iProver_top ),
    inference(superposition,[status(thm)],[c_3250,c_3264])).

cnf(c_5167,plain,
    ( r2_hidden(sK3(k8_relat_1(X0_44,X0_43)),k1_relat_1(X0_43)) = iProver_top
    | v1_relat_1(X0_43) != iProver_top
    | v1_relat_1(k8_relat_1(X0_44,X0_43)) != iProver_top
    | v1_funct_1(X0_43) != iProver_top
    | v1_funct_1(k8_relat_1(X0_44,X0_43)) != iProver_top
    | v2_funct_1(k8_relat_1(X0_44,X0_43)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3270,c_3841])).

cnf(c_2840,plain,
    ( v1_relat_1(X0_43) != iProver_top
    | v1_relat_1(k8_relat_1(X0_44,X0_43)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2805])).

cnf(c_6919,plain,
    ( v1_funct_1(X0_43) != iProver_top
    | r2_hidden(sK3(k8_relat_1(X0_44,X0_43)),k1_relat_1(X0_43)) = iProver_top
    | v1_relat_1(X0_43) != iProver_top
    | v2_funct_1(k8_relat_1(X0_44,X0_43)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5167,c_2840,c_2843])).

cnf(c_6920,plain,
    ( r2_hidden(sK3(k8_relat_1(X0_44,X0_43)),k1_relat_1(X0_43)) = iProver_top
    | v1_relat_1(X0_43) != iProver_top
    | v1_funct_1(X0_43) != iProver_top
    | v2_funct_1(k8_relat_1(X0_44,X0_43)) = iProver_top ),
    inference(renaming,[status(thm)],[c_6919])).

cnf(c_18,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X0,X3),X2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_2795,plain,
    ( ~ sP0(X0_43,X1_43,X0_44)
    | ~ r2_hidden(X0_45,k1_relat_1(X1_43))
    | r2_hidden(k1_funct_1(X0_43,X0_45),X0_44) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_3263,plain,
    ( sP0(X0_43,X1_43,X0_44) != iProver_top
    | r2_hidden(X0_45,k1_relat_1(X1_43)) != iProver_top
    | r2_hidden(k1_funct_1(X0_43,X0_45),X0_44) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2795])).

cnf(c_6929,plain,
    ( sP0(X0_43,X1_43,X0_44) != iProver_top
    | r2_hidden(k1_funct_1(X0_43,sK3(k8_relat_1(X1_44,X1_43))),X0_44) = iProver_top
    | v1_relat_1(X1_43) != iProver_top
    | v1_funct_1(X1_43) != iProver_top
    | v2_funct_1(k8_relat_1(X1_44,X1_43)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6920,c_3263])).

cnf(c_7110,plain,
    ( sP0(k8_relat_1(sK6,sK7),sK7,X0_44) != iProver_top
    | r2_hidden(k1_funct_1(k8_relat_1(sK6,sK7),sK2(k8_relat_1(sK6,sK7))),X0_44) = iProver_top
    | v1_relat_1(sK7) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v2_funct_1(k8_relat_1(sK6,sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5867,c_6929])).

cnf(c_7189,plain,
    ( r2_hidden(k1_funct_1(k8_relat_1(sK6,sK7),sK2(k8_relat_1(sK6,sK7))),X0_44) = iProver_top
    | sP0(k8_relat_1(sK6,sK7),sK7,X0_44) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7110,c_25,c_26,c_28])).

cnf(c_7190,plain,
    ( sP0(k8_relat_1(sK6,sK7),sK7,X0_44) != iProver_top
    | r2_hidden(k1_funct_1(k8_relat_1(sK6,sK7),sK2(k8_relat_1(sK6,sK7))),X0_44) = iProver_top ),
    inference(renaming,[status(thm)],[c_7189])).

cnf(c_17,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | r2_hidden(X3,k1_relat_1(X1))
    | ~ r2_hidden(k1_funct_1(X0,X3),X2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_2796,plain,
    ( ~ sP0(X0_43,X1_43,X0_44)
    | ~ r2_hidden(X0_45,k1_relat_1(X0_43))
    | r2_hidden(X0_45,k1_relat_1(X1_43))
    | ~ r2_hidden(k1_funct_1(X0_43,X0_45),X0_44) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_3262,plain,
    ( sP0(X0_43,X1_43,X0_44) != iProver_top
    | r2_hidden(X0_45,k1_relat_1(X0_43)) != iProver_top
    | r2_hidden(X0_45,k1_relat_1(X1_43)) = iProver_top
    | r2_hidden(k1_funct_1(X0_43,X0_45),X0_44) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2796])).

cnf(c_7200,plain,
    ( sP0(k8_relat_1(sK6,sK7),X0_43,X0_44) != iProver_top
    | sP0(k8_relat_1(sK6,sK7),sK7,X0_44) != iProver_top
    | r2_hidden(sK2(k8_relat_1(sK6,sK7)),k1_relat_1(X0_43)) = iProver_top
    | r2_hidden(sK2(k8_relat_1(sK6,sK7)),k1_relat_1(k8_relat_1(sK6,sK7))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7190,c_3262])).

cnf(c_3,plain,
    ( r2_hidden(sK2(X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_429,plain,
    ( r2_hidden(sK2(X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k8_relat_1(sK6,sK7) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_21])).

cnf(c_430,plain,
    ( r2_hidden(sK2(k8_relat_1(sK6,sK7)),k1_relat_1(k8_relat_1(sK6,sK7)))
    | ~ v1_relat_1(k8_relat_1(sK6,sK7))
    | ~ v1_funct_1(k8_relat_1(sK6,sK7)) ),
    inference(unflattening,[status(thm)],[c_429])).

cnf(c_431,plain,
    ( r2_hidden(sK2(k8_relat_1(sK6,sK7)),k1_relat_1(k8_relat_1(sK6,sK7))) = iProver_top
    | v1_relat_1(k8_relat_1(sK6,sK7)) != iProver_top
    | v1_funct_1(k8_relat_1(sK6,sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_430])).

cnf(c_2842,plain,
    ( v1_relat_1(k8_relat_1(sK6,sK7)) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2840])).

cnf(c_7773,plain,
    ( r2_hidden(sK2(k8_relat_1(sK6,sK7)),k1_relat_1(X0_43)) = iProver_top
    | sP0(k8_relat_1(sK6,sK7),sK7,X0_44) != iProver_top
    | sP0(k8_relat_1(sK6,sK7),X0_43,X0_44) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7200,c_25,c_26,c_431,c_2842,c_2845])).

cnf(c_7774,plain,
    ( sP0(k8_relat_1(sK6,sK7),X0_43,X0_44) != iProver_top
    | sP0(k8_relat_1(sK6,sK7),sK7,X0_44) != iProver_top
    | r2_hidden(sK2(k8_relat_1(sK6,sK7)),k1_relat_1(X0_43)) = iProver_top ),
    inference(renaming,[status(thm)],[c_7773])).

cnf(c_9481,plain,
    ( k1_funct_1(k8_relat_1(sK6,sK7),sK5(k8_relat_1(sK6,sK7),k8_relat_1(sK6,sK7),X0_44)) = k1_funct_1(sK7,sK5(k8_relat_1(sK6,sK7),k8_relat_1(sK6,sK7),X0_44))
    | sP0(k8_relat_1(sK6,sK7),sK7,X0_44) != iProver_top
    | r2_hidden(sK2(k8_relat_1(sK6,sK7)),k1_relat_1(k8_relat_1(sK6,sK7))) = iProver_top
    | v1_relat_1(sK7) != iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_5001,c_7774])).

cnf(c_13372,plain,
    ( r2_hidden(sK2(k8_relat_1(sK6,sK7)),k1_relat_1(k8_relat_1(sK6,sK7))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9481,c_25,c_26,c_431,c_2842,c_2845])).

cnf(c_13379,plain,
    ( k1_funct_1(k8_relat_1(sK6,sK7),sK2(k8_relat_1(sK6,sK7))) = k1_funct_1(X0_43,sK2(k8_relat_1(sK6,sK7)))
    | sP0(X0_43,k8_relat_1(sK6,sK7),X0_44) != iProver_top ),
    inference(superposition,[status(thm)],[c_13372,c_3261])).

cnf(c_5871,plain,
    ( sP0(k8_relat_1(sK6,sK7),X0_43,X0_44) != iProver_top
    | r2_hidden(k1_funct_1(k8_relat_1(sK6,sK7),sK2(k8_relat_1(sK6,sK7))),X0_44) != iProver_top
    | r2_hidden(sK3(k8_relat_1(sK6,sK7)),k1_relat_1(X0_43)) = iProver_top
    | r2_hidden(sK3(k8_relat_1(sK6,sK7)),k1_relat_1(k8_relat_1(sK6,sK7))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5867,c_3262])).

cnf(c_442,plain,
    ( r2_hidden(sK3(X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k8_relat_1(sK6,sK7) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_21])).

cnf(c_443,plain,
    ( r2_hidden(sK3(k8_relat_1(sK6,sK7)),k1_relat_1(k8_relat_1(sK6,sK7)))
    | ~ v1_relat_1(k8_relat_1(sK6,sK7))
    | ~ v1_funct_1(k8_relat_1(sK6,sK7)) ),
    inference(unflattening,[status(thm)],[c_442])).

cnf(c_444,plain,
    ( r2_hidden(sK3(k8_relat_1(sK6,sK7)),k1_relat_1(k8_relat_1(sK6,sK7))) = iProver_top
    | v1_relat_1(k8_relat_1(sK6,sK7)) != iProver_top
    | v1_funct_1(k8_relat_1(sK6,sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_443])).

cnf(c_5992,plain,
    ( r2_hidden(sK3(k8_relat_1(sK6,sK7)),k1_relat_1(X0_43)) = iProver_top
    | r2_hidden(k1_funct_1(k8_relat_1(sK6,sK7),sK2(k8_relat_1(sK6,sK7))),X0_44) != iProver_top
    | sP0(k8_relat_1(sK6,sK7),X0_43,X0_44) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5871,c_25,c_26,c_444,c_2842,c_2845])).

cnf(c_5993,plain,
    ( sP0(k8_relat_1(sK6,sK7),X0_43,X0_44) != iProver_top
    | r2_hidden(k1_funct_1(k8_relat_1(sK6,sK7),sK2(k8_relat_1(sK6,sK7))),X0_44) != iProver_top
    | r2_hidden(sK3(k8_relat_1(sK6,sK7)),k1_relat_1(X0_43)) = iProver_top ),
    inference(renaming,[status(thm)],[c_5992])).

cnf(c_7201,plain,
    ( sP0(k8_relat_1(sK6,sK7),X0_43,X0_44) != iProver_top
    | sP0(k8_relat_1(sK6,sK7),sK7,X0_44) != iProver_top
    | r2_hidden(sK3(k8_relat_1(sK6,sK7)),k1_relat_1(X0_43)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7190,c_5993])).

cnf(c_7358,plain,
    ( sP0(k8_relat_1(sK6,sK7),sK7,X0_44) != iProver_top
    | r2_hidden(sK3(k8_relat_1(sK6,sK7)),k1_relat_1(k8_relat_1(X0_44,k8_relat_1(sK6,sK7)))) = iProver_top
    | v1_relat_1(k8_relat_1(sK6,sK7)) != iProver_top
    | v1_funct_1(k8_relat_1(sK6,sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3270,c_7201])).

cnf(c_7787,plain,
    ( sP0(k8_relat_1(sK6,sK7),sK7,X0_44) != iProver_top
    | r2_hidden(sK3(k8_relat_1(sK6,sK7)),k1_relat_1(k8_relat_1(X0_44,k8_relat_1(sK6,sK7)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7358,c_25,c_26,c_2842,c_2845])).

cnf(c_7796,plain,
    ( sP0(X0_43,k8_relat_1(X0_44,k8_relat_1(sK6,sK7)),X1_44) != iProver_top
    | sP0(k8_relat_1(sK6,sK7),sK7,X0_44) != iProver_top
    | r2_hidden(sK3(k8_relat_1(sK6,sK7)),k1_relat_1(X0_43)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7787,c_3264])).

cnf(c_7967,plain,
    ( sP0(k8_relat_1(sK6,sK7),sK7,X0_44) != iProver_top
    | r2_hidden(sK3(k8_relat_1(sK6,sK7)),k1_relat_1(k8_relat_1(sK6,sK7))) = iProver_top
    | v1_relat_1(k8_relat_1(sK6,sK7)) != iProver_top
    | v1_funct_1(k8_relat_1(sK6,sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3270,c_7796])).

cnf(c_8949,plain,
    ( r2_hidden(sK3(k8_relat_1(sK6,sK7)),k1_relat_1(k8_relat_1(sK6,sK7))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7967,c_25,c_26,c_444,c_2842,c_2845])).

cnf(c_8956,plain,
    ( k1_funct_1(k8_relat_1(sK6,sK7),sK3(k8_relat_1(sK6,sK7))) = k1_funct_1(X0_43,sK3(k8_relat_1(sK6,sK7)))
    | sP0(X0_43,k8_relat_1(sK6,sK7),X0_44) != iProver_top ),
    inference(superposition,[status(thm)],[c_8949,c_3261])).

cnf(c_8959,plain,
    ( k1_funct_1(k8_relat_1(sK6,sK7),sK2(k8_relat_1(sK6,sK7))) = k1_funct_1(X0_43,sK3(k8_relat_1(sK6,sK7)))
    | sP0(X0_43,k8_relat_1(sK6,sK7),X0_44) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8956,c_5867])).

cnf(c_8982,plain,
    ( k1_funct_1(k8_relat_1(sK6,sK7),sK2(k8_relat_1(sK6,sK7))) = k1_funct_1(sK7,sK3(k8_relat_1(sK6,sK7)))
    | v1_relat_1(sK7) != iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_3270,c_8959])).

cnf(c_2879,plain,
    ( sP0(X0_43,k8_relat_1(X0_44,X0_43),X0_44) = iProver_top
    | v1_relat_1(X0_43) != iProver_top
    | v1_funct_1(X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2788])).

cnf(c_2881,plain,
    ( sP0(sK7,k8_relat_1(sK6,sK7),sK6) = iProver_top
    | v1_relat_1(sK7) != iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2879])).

cnf(c_8977,plain,
    ( k1_funct_1(k8_relat_1(sK6,sK7),sK2(k8_relat_1(sK6,sK7))) = k1_funct_1(sK7,sK3(k8_relat_1(sK6,sK7)))
    | sP0(sK7,k8_relat_1(sK6,sK7),sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_8959])).

cnf(c_9054,plain,
    ( k1_funct_1(k8_relat_1(sK6,sK7),sK2(k8_relat_1(sK6,sK7))) = k1_funct_1(sK7,sK3(k8_relat_1(sK6,sK7))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8982,c_25,c_26,c_2881,c_8977])).

cnf(c_13382,plain,
    ( k1_funct_1(X0_43,sK2(k8_relat_1(sK6,sK7))) = k1_funct_1(sK7,sK3(k8_relat_1(sK6,sK7)))
    | sP0(X0_43,k8_relat_1(sK6,sK7),X0_44) != iProver_top ),
    inference(demodulation,[status(thm)],[c_13379,c_9054])).

cnf(c_13400,plain,
    ( k1_funct_1(sK7,sK2(k8_relat_1(sK6,sK7))) = k1_funct_1(sK7,sK3(k8_relat_1(sK6,sK7)))
    | sP0(sK7,k8_relat_1(sK6,sK7),sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_13382])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | X0 = X2
    | k1_funct_1(X1,X0) != k1_funct_1(X1,X2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_2806,plain,
    ( ~ r2_hidden(X0_45,k1_relat_1(X0_43))
    | ~ r2_hidden(X1_45,k1_relat_1(X0_43))
    | ~ v1_relat_1(X0_43)
    | ~ v1_funct_1(X0_43)
    | ~ v2_funct_1(X0_43)
    | X0_45 = X1_45
    | k1_funct_1(X0_43,X0_45) != k1_funct_1(X0_43,X1_45) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_3815,plain,
    ( ~ r2_hidden(X0_45,k1_relat_1(X0_43))
    | ~ r2_hidden(sK3(k8_relat_1(sK6,sK7)),k1_relat_1(X0_43))
    | ~ v1_relat_1(X0_43)
    | ~ v1_funct_1(X0_43)
    | ~ v2_funct_1(X0_43)
    | X0_45 = sK3(k8_relat_1(sK6,sK7))
    | k1_funct_1(X0_43,X0_45) != k1_funct_1(X0_43,sK3(k8_relat_1(sK6,sK7))) ),
    inference(instantiation,[status(thm)],[c_2806])).

cnf(c_4651,plain,
    ( ~ r2_hidden(sK3(k8_relat_1(sK6,sK7)),k1_relat_1(X0_43))
    | ~ r2_hidden(sK2(k8_relat_1(sK6,sK7)),k1_relat_1(X0_43))
    | ~ v1_relat_1(X0_43)
    | ~ v1_funct_1(X0_43)
    | ~ v2_funct_1(X0_43)
    | k1_funct_1(X0_43,sK2(k8_relat_1(sK6,sK7))) != k1_funct_1(X0_43,sK3(k8_relat_1(sK6,sK7)))
    | sK2(k8_relat_1(sK6,sK7)) = sK3(k8_relat_1(sK6,sK7)) ),
    inference(instantiation,[status(thm)],[c_3815])).

cnf(c_4653,plain,
    ( ~ r2_hidden(sK3(k8_relat_1(sK6,sK7)),k1_relat_1(sK7))
    | ~ r2_hidden(sK2(k8_relat_1(sK6,sK7)),k1_relat_1(sK7))
    | ~ v1_relat_1(sK7)
    | ~ v1_funct_1(sK7)
    | ~ v2_funct_1(sK7)
    | k1_funct_1(sK7,sK2(k8_relat_1(sK6,sK7))) != k1_funct_1(sK7,sK3(k8_relat_1(sK6,sK7)))
    | sK2(k8_relat_1(sK6,sK7)) = sK3(k8_relat_1(sK6,sK7)) ),
    inference(instantiation,[status(thm)],[c_4651])).

cnf(c_2814,plain,
    ( X0_45 = X0_45 ),
    theory(equality)).

cnf(c_3685,plain,
    ( sK3(k8_relat_1(sK6,sK7)) = sK3(k8_relat_1(sK6,sK7)) ),
    inference(instantiation,[status(thm)],[c_2814])).

cnf(c_2816,plain,
    ( X0_45 != X1_45
    | X2_45 != X1_45
    | X2_45 = X0_45 ),
    theory(equality)).

cnf(c_3613,plain,
    ( sK3(k8_relat_1(sK6,sK7)) != X0_45
    | sK3(k8_relat_1(sK6,sK7)) = sK2(k8_relat_1(sK6,sK7))
    | sK2(k8_relat_1(sK6,sK7)) != X0_45 ),
    inference(instantiation,[status(thm)],[c_2816])).

cnf(c_3684,plain,
    ( sK3(k8_relat_1(sK6,sK7)) != sK3(k8_relat_1(sK6,sK7))
    | sK3(k8_relat_1(sK6,sK7)) = sK2(k8_relat_1(sK6,sK7))
    | sK2(k8_relat_1(sK6,sK7)) != sK3(k8_relat_1(sK6,sK7)) ),
    inference(instantiation,[status(thm)],[c_3613])).

cnf(c_3589,plain,
    ( ~ sP0(X0_43,k8_relat_1(sK6,sK7),X0_44)
    | r2_hidden(sK3(k8_relat_1(sK6,sK7)),k1_relat_1(X0_43))
    | ~ r2_hidden(sK3(k8_relat_1(sK6,sK7)),k1_relat_1(k8_relat_1(sK6,sK7))) ),
    inference(instantiation,[status(thm)],[c_2794])).

cnf(c_3591,plain,
    ( ~ sP0(sK7,k8_relat_1(sK6,sK7),sK6)
    | ~ r2_hidden(sK3(k8_relat_1(sK6,sK7)),k1_relat_1(k8_relat_1(sK6,sK7)))
    | r2_hidden(sK3(k8_relat_1(sK6,sK7)),k1_relat_1(sK7)) ),
    inference(instantiation,[status(thm)],[c_3589])).

cnf(c_3569,plain,
    ( ~ sP0(X0_43,k8_relat_1(sK6,sK7),X0_44)
    | r2_hidden(sK2(k8_relat_1(sK6,sK7)),k1_relat_1(X0_43))
    | ~ r2_hidden(sK2(k8_relat_1(sK6,sK7)),k1_relat_1(k8_relat_1(sK6,sK7))) ),
    inference(instantiation,[status(thm)],[c_2794])).

cnf(c_3571,plain,
    ( ~ sP0(sK7,k8_relat_1(sK6,sK7),sK6)
    | ~ r2_hidden(sK2(k8_relat_1(sK6,sK7)),k1_relat_1(k8_relat_1(sK6,sK7)))
    | r2_hidden(sK2(k8_relat_1(sK6,sK7)),k1_relat_1(sK7)) ),
    inference(instantiation,[status(thm)],[c_3569])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | sK3(X0) != sK2(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_2810,plain,
    ( ~ v1_relat_1(X0_43)
    | ~ v1_funct_1(X0_43)
    | v2_funct_1(X0_43)
    | sK3(X0_43) != sK2(X0_43) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_3497,plain,
    ( ~ v1_relat_1(k8_relat_1(sK6,sK7))
    | ~ v1_funct_1(k8_relat_1(sK6,sK7))
    | v2_funct_1(k8_relat_1(sK6,sK7))
    | sK3(k8_relat_1(sK6,sK7)) != sK2(k8_relat_1(sK6,sK7)) ),
    inference(instantiation,[status(thm)],[c_2810])).

cnf(c_2880,plain,
    ( sP0(sK7,k8_relat_1(sK6,sK7),sK6)
    | ~ v1_relat_1(sK7)
    | ~ v1_funct_1(sK7) ),
    inference(instantiation,[status(thm)],[c_2788])).

cnf(c_2844,plain,
    ( ~ v1_relat_1(sK7)
    | v1_funct_1(k8_relat_1(sK6,sK7))
    | ~ v1_funct_1(sK7) ),
    inference(instantiation,[status(thm)],[c_2804])).

cnf(c_2841,plain,
    ( v1_relat_1(k8_relat_1(sK6,sK7))
    | ~ v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_2805])).

cnf(c_22,negated_conjecture,
    ( v2_funct_1(sK7) ),
    inference(cnf_transformation,[],[f56])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13400,c_4653,c_3685,c_3684,c_3591,c_3571,c_3497,c_2881,c_2880,c_2844,c_2841,c_443,c_430,c_21,c_22,c_26,c_23,c_25,c_24])).


%------------------------------------------------------------------------------
