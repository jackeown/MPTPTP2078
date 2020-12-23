%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0795+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:08 EST 2020

% Result     : Theorem 2.46s
% Output     : CNFRefutation 2.46s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 556 expanded)
%              Number of clauses        :   71 ( 231 expanded)
%              Number of leaves         :   11 ( 117 expanded)
%              Depth                    :   20
%              Number of atoms          :  513 (2450 expanded)
%              Number of equality atoms :  227 ( 635 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   24 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f15,plain,(
    ! [X1,X2,X0] :
      ( sP0(X1,X2,X0)
    <=> ( ! [X3,X4] :
            ( r2_hidden(k4_tarski(X3,X4),X0)
          <=> ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
              & r2_hidden(X4,k3_relat_1(X0))
              & r2_hidden(X3,k3_relat_1(X0)) ) )
        & v2_funct_1(X2)
        & k3_relat_1(X1) = k2_relat_1(X2)
        & k1_relat_1(X2) = k3_relat_1(X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f20,plain,(
    ! [X1,X2,X0] :
      ( ( sP0(X1,X2,X0)
        | ? [X3,X4] :
            ( ( ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
              | ~ r2_hidden(X4,k3_relat_1(X0))
              | ~ r2_hidden(X3,k3_relat_1(X0))
              | ~ r2_hidden(k4_tarski(X3,X4),X0) )
            & ( ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                & r2_hidden(X4,k3_relat_1(X0))
                & r2_hidden(X3,k3_relat_1(X0)) )
              | r2_hidden(k4_tarski(X3,X4),X0) ) )
        | ~ v2_funct_1(X2)
        | k3_relat_1(X1) != k2_relat_1(X2)
        | k1_relat_1(X2) != k3_relat_1(X0) )
      & ( ( ! [X3,X4] :
              ( ( r2_hidden(k4_tarski(X3,X4),X0)
                | ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                | ~ r2_hidden(X4,k3_relat_1(X0))
                | ~ r2_hidden(X3,k3_relat_1(X0)) )
              & ( ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                  & r2_hidden(X4,k3_relat_1(X0))
                  & r2_hidden(X3,k3_relat_1(X0)) )
                | ~ r2_hidden(k4_tarski(X3,X4),X0) ) )
          & v2_funct_1(X2)
          & k3_relat_1(X1) = k2_relat_1(X2)
          & k1_relat_1(X2) = k3_relat_1(X0) )
        | ~ sP0(X1,X2,X0) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f21,plain,(
    ! [X1,X2,X0] :
      ( ( sP0(X1,X2,X0)
        | ? [X3,X4] :
            ( ( ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
              | ~ r2_hidden(X4,k3_relat_1(X0))
              | ~ r2_hidden(X3,k3_relat_1(X0))
              | ~ r2_hidden(k4_tarski(X3,X4),X0) )
            & ( ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                & r2_hidden(X4,k3_relat_1(X0))
                & r2_hidden(X3,k3_relat_1(X0)) )
              | r2_hidden(k4_tarski(X3,X4),X0) ) )
        | ~ v2_funct_1(X2)
        | k3_relat_1(X1) != k2_relat_1(X2)
        | k1_relat_1(X2) != k3_relat_1(X0) )
      & ( ( ! [X3,X4] :
              ( ( r2_hidden(k4_tarski(X3,X4),X0)
                | ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                | ~ r2_hidden(X4,k3_relat_1(X0))
                | ~ r2_hidden(X3,k3_relat_1(X0)) )
              & ( ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                  & r2_hidden(X4,k3_relat_1(X0))
                  & r2_hidden(X3,k3_relat_1(X0)) )
                | ~ r2_hidden(k4_tarski(X3,X4),X0) ) )
          & v2_funct_1(X2)
          & k3_relat_1(X1) = k2_relat_1(X2)
          & k1_relat_1(X2) = k3_relat_1(X0) )
        | ~ sP0(X1,X2,X0) ) ) ),
    inference(flattening,[],[f20])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3,X4] :
            ( ( ~ r2_hidden(k4_tarski(k1_funct_1(X1,X3),k1_funct_1(X1,X4)),X0)
              | ~ r2_hidden(X4,k3_relat_1(X2))
              | ~ r2_hidden(X3,k3_relat_1(X2))
              | ~ r2_hidden(k4_tarski(X3,X4),X2) )
            & ( ( r2_hidden(k4_tarski(k1_funct_1(X1,X3),k1_funct_1(X1,X4)),X0)
                & r2_hidden(X4,k3_relat_1(X2))
                & r2_hidden(X3,k3_relat_1(X2)) )
              | r2_hidden(k4_tarski(X3,X4),X2) ) )
        | ~ v2_funct_1(X1)
        | k3_relat_1(X0) != k2_relat_1(X1)
        | k1_relat_1(X1) != k3_relat_1(X2) )
      & ( ( ! [X5,X6] :
              ( ( r2_hidden(k4_tarski(X5,X6),X2)
                | ~ r2_hidden(k4_tarski(k1_funct_1(X1,X5),k1_funct_1(X1,X6)),X0)
                | ~ r2_hidden(X6,k3_relat_1(X2))
                | ~ r2_hidden(X5,k3_relat_1(X2)) )
              & ( ( r2_hidden(k4_tarski(k1_funct_1(X1,X5),k1_funct_1(X1,X6)),X0)
                  & r2_hidden(X6,k3_relat_1(X2))
                  & r2_hidden(X5,k3_relat_1(X2)) )
                | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
          & v2_funct_1(X1)
          & k3_relat_1(X0) = k2_relat_1(X1)
          & k1_relat_1(X1) = k3_relat_1(X2) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f21])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ r2_hidden(k4_tarski(k1_funct_1(X1,X3),k1_funct_1(X1,X4)),X0)
            | ~ r2_hidden(X4,k3_relat_1(X2))
            | ~ r2_hidden(X3,k3_relat_1(X2))
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ( r2_hidden(k4_tarski(k1_funct_1(X1,X3),k1_funct_1(X1,X4)),X0)
              & r2_hidden(X4,k3_relat_1(X2))
              & r2_hidden(X3,k3_relat_1(X2)) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(k1_funct_1(X1,sK2(X0,X1,X2)),k1_funct_1(X1,sK3(X0,X1,X2))),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),k3_relat_1(X2))
          | ~ r2_hidden(sK2(X0,X1,X2),k3_relat_1(X2))
          | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) )
        & ( ( r2_hidden(k4_tarski(k1_funct_1(X1,sK2(X0,X1,X2)),k1_funct_1(X1,sK3(X0,X1,X2))),X0)
            & r2_hidden(sK3(X0,X1,X2),k3_relat_1(X2))
            & r2_hidden(sK2(X0,X1,X2),k3_relat_1(X2)) )
          | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ~ r2_hidden(k4_tarski(k1_funct_1(X1,sK2(X0,X1,X2)),k1_funct_1(X1,sK3(X0,X1,X2))),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),k3_relat_1(X2))
            | ~ r2_hidden(sK2(X0,X1,X2),k3_relat_1(X2))
            | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) )
          & ( ( r2_hidden(k4_tarski(k1_funct_1(X1,sK2(X0,X1,X2)),k1_funct_1(X1,sK3(X0,X1,X2))),X0)
              & r2_hidden(sK3(X0,X1,X2),k3_relat_1(X2))
              & r2_hidden(sK2(X0,X1,X2),k3_relat_1(X2)) )
            | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) ) )
        | ~ v2_funct_1(X1)
        | k3_relat_1(X0) != k2_relat_1(X1)
        | k1_relat_1(X1) != k3_relat_1(X2) )
      & ( ( ! [X5,X6] :
              ( ( r2_hidden(k4_tarski(X5,X6),X2)
                | ~ r2_hidden(k4_tarski(k1_funct_1(X1,X5),k1_funct_1(X1,X6)),X0)
                | ~ r2_hidden(X6,k3_relat_1(X2))
                | ~ r2_hidden(X5,k3_relat_1(X2)) )
              & ( ( r2_hidden(k4_tarski(k1_funct_1(X1,X5),k1_funct_1(X1,X6)),X0)
                  & r2_hidden(X6,k3_relat_1(X2))
                  & r2_hidden(X5,k3_relat_1(X2)) )
                | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
          & v2_funct_1(X1)
          & k3_relat_1(X0) = k2_relat_1(X1)
          & k1_relat_1(X1) = k3_relat_1(X2) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f22,f23])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | r2_hidden(sK3(X0,X1,X2),k3_relat_1(X2))
      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)
      | ~ v2_funct_1(X1)
      | k3_relat_1(X0) != k2_relat_1(X1)
      | k1_relat_1(X1) != k3_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f49,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f3,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k3_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f7,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r3_wellord1(X0,X0,k6_relat_1(k3_relat_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => r3_wellord1(X0,X0,k6_relat_1(k3_relat_1(X0))) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f14,plain,(
    ? [X0] :
      ( ~ r3_wellord1(X0,X0,k6_relat_1(k3_relat_1(X0)))
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,
    ( ? [X0] :
        ( ~ r3_wellord1(X0,X0,k6_relat_1(k3_relat_1(X0)))
        & v1_relat_1(X0) )
   => ( ~ r3_wellord1(sK4,sK4,k6_relat_1(k3_relat_1(sK4)))
      & v1_relat_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ~ r3_wellord1(sK4,sK4,k6_relat_1(k3_relat_1(sK4)))
    & v1_relat_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f14,f25])).

fof(f50,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f26])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ( r3_wellord1(X0,X1,X2)
              <=> ( ! [X3,X4] :
                      ( r2_hidden(k4_tarski(X3,X4),X0)
                    <=> ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                        & r2_hidden(X4,k3_relat_1(X0))
                        & r2_hidden(X3,k3_relat_1(X0)) ) )
                  & v2_funct_1(X2)
                  & k3_relat_1(X1) = k2_relat_1(X2)
                  & k1_relat_1(X2) = k3_relat_1(X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_wellord1(X0,X1,X2)
              <=> ( ! [X3,X4] :
                      ( r2_hidden(k4_tarski(X3,X4),X0)
                    <=> ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                        & r2_hidden(X4,k3_relat_1(X0))
                        & r2_hidden(X3,k3_relat_1(X0)) ) )
                  & v2_funct_1(X2)
                  & k3_relat_1(X1) = k2_relat_1(X2)
                  & k1_relat_1(X2) = k3_relat_1(X0) ) )
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_wellord1(X0,X1,X2)
              <=> ( ! [X3,X4] :
                      ( r2_hidden(k4_tarski(X3,X4),X0)
                    <=> ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                        & r2_hidden(X4,k3_relat_1(X0))
                        & r2_hidden(X3,k3_relat_1(X0)) ) )
                  & v2_funct_1(X2)
                  & k3_relat_1(X1) = k2_relat_1(X2)
                  & k1_relat_1(X2) = k3_relat_1(X0) ) )
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f16,plain,(
    ! [X0,X2,X1] :
      ( ( r3_wellord1(X0,X1,X2)
      <=> sP0(X1,X2,X0) )
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP1(X0,X2,X1)
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f10,f16,f15])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X2,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f41,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f18,plain,(
    ! [X0,X2,X1] :
      ( ( ( r3_wellord1(X0,X1,X2)
          | ~ sP0(X1,X2,X0) )
        & ( sP0(X1,X2,X0)
          | ~ r3_wellord1(X0,X1,X2) ) )
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_wellord1(X0,X2,X1)
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | ~ r3_wellord1(X0,X2,X1) ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f18])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r3_wellord1(X0,X2,X1)
      | ~ sP0(X2,X1,X0)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f51,plain,(
    ~ r3_wellord1(sK4,sK4,k6_relat_1(k3_relat_1(sK4))) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k1_funct_1(k6_relat_1(X1),X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( k1_funct_1(k6_relat_1(X1),X0) = X0
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_funct_1(k6_relat_1(X1),X0) = X0
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | r2_hidden(k4_tarski(k1_funct_1(X1,sK2(X0,X1,X2)),k1_funct_1(X1,sK3(X0,X1,X2))),X0)
      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)
      | ~ v2_funct_1(X1)
      | k3_relat_1(X0) != k2_relat_1(X1)
      | k1_relat_1(X1) != k3_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | r2_hidden(sK2(X0,X1,X2),k3_relat_1(X2))
      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)
      | ~ v2_funct_1(X1)
      | k3_relat_1(X0) != k2_relat_1(X1)
      | k1_relat_1(X1) != k3_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k3_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | ~ r2_hidden(k4_tarski(k1_funct_1(X1,sK2(X0,X1,X2)),k1_funct_1(X1,sK3(X0,X1,X2))),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),k3_relat_1(X2))
      | ~ r2_hidden(sK2(X0,X1,X2),k3_relat_1(X2))
      | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)
      | ~ v2_funct_1(X1)
      | k3_relat_1(X0) != k2_relat_1(X1)
      | k1_relat_1(X1) != k3_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_22,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_4,plain,
    ( sP0(X0,X1,X2)
    | r2_hidden(sK3(X0,X1,X2),k3_relat_1(X2))
    | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)
    | ~ v2_funct_1(X1)
    | k1_relat_1(X1) != k3_relat_1(X2)
    | k2_relat_1(X1) != k3_relat_1(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_2620,plain,
    ( k1_relat_1(X0) != k3_relat_1(X1)
    | k2_relat_1(X0) != k3_relat_1(X2)
    | sP0(X2,X0,X1) = iProver_top
    | r2_hidden(sK3(X2,X0,X1),k3_relat_1(X1)) = iProver_top
    | r2_hidden(k4_tarski(sK2(X2,X0,X1),sK3(X2,X0,X1)),X1) = iProver_top
    | v2_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3785,plain,
    ( k2_relat_1(k6_relat_1(X0)) != k3_relat_1(X1)
    | k3_relat_1(X2) != X0
    | sP0(X1,k6_relat_1(X0),X2) = iProver_top
    | r2_hidden(sK3(X1,k6_relat_1(X0),X2),k3_relat_1(X2)) = iProver_top
    | r2_hidden(k4_tarski(sK2(X1,k6_relat_1(X0),X2),sK3(X1,k6_relat_1(X0),X2)),X2) = iProver_top
    | v2_funct_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_22,c_2620])).

cnf(c_21,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_3786,plain,
    ( k3_relat_1(X0) != X1
    | k3_relat_1(X2) != X1
    | sP0(X2,k6_relat_1(X1),X0) = iProver_top
    | r2_hidden(sK3(X2,k6_relat_1(X1),X0),k3_relat_1(X0)) = iProver_top
    | r2_hidden(k4_tarski(sK2(X2,k6_relat_1(X1),X0),sK3(X2,k6_relat_1(X1),X0)),X0) = iProver_top
    | v2_funct_1(k6_relat_1(X1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3785,c_21])).

cnf(c_16,plain,
    ( v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_2611,plain,
    ( v2_funct_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3843,plain,
    ( k3_relat_1(X0) != X1
    | k3_relat_1(X2) != X1
    | sP0(X2,k6_relat_1(X1),X0) = iProver_top
    | r2_hidden(sK3(X2,k6_relat_1(X1),X0),k3_relat_1(X0)) = iProver_top
    | r2_hidden(k4_tarski(sK2(X2,k6_relat_1(X1),X0),sK3(X2,k6_relat_1(X1),X0)),X0) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3786,c_2611])).

cnf(c_3847,plain,
    ( k3_relat_1(X0) != k3_relat_1(X1)
    | sP0(X0,k6_relat_1(k3_relat_1(X1)),X1) = iProver_top
    | r2_hidden(sK3(X0,k6_relat_1(k3_relat_1(X1)),X1),k3_relat_1(X1)) = iProver_top
    | r2_hidden(k4_tarski(sK2(X0,k6_relat_1(k3_relat_1(X1)),X1),sK3(X0,k6_relat_1(k3_relat_1(X1)),X1)),X1) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3843])).

cnf(c_4484,plain,
    ( sP0(X0,k6_relat_1(k3_relat_1(X0)),X0) = iProver_top
    | r2_hidden(sK3(X0,k6_relat_1(k3_relat_1(X0)),X0),k3_relat_1(X0)) = iProver_top
    | r2_hidden(k4_tarski(sK2(X0,k6_relat_1(k3_relat_1(X0)),X0),sK3(X0,k6_relat_1(k3_relat_1(X0)),X0)),X0) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3847])).

cnf(c_18,plain,
    ( r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_24,negated_conjecture,
    ( v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_354,plain,
    ( r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_24])).

cnf(c_355,plain,
    ( r2_hidden(X0,k3_relat_1(sK4))
    | ~ r2_hidden(k4_tarski(X1,X0),sK4) ),
    inference(unflattening,[status(thm)],[c_354])).

cnf(c_2605,plain,
    ( r2_hidden(X0,k3_relat_1(sK4)) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_355])).

cnf(c_4981,plain,
    ( sP0(sK4,k6_relat_1(k3_relat_1(sK4)),sK4) = iProver_top
    | r2_hidden(sK3(sK4,k6_relat_1(k3_relat_1(sK4)),sK4),k3_relat_1(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4484,c_2605])).

cnf(c_13,plain,
    ( sP1(X0,X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_14,plain,
    ( v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_261,plain,
    ( sP1(X0,X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X0)
    | k6_relat_1(X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_14])).

cnf(c_262,plain,
    ( sP1(X0,k6_relat_1(X1),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(k6_relat_1(X1)) ),
    inference(unflattening,[status(thm)],[c_261])).

cnf(c_15,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_274,plain,
    ( sP1(X0,k6_relat_1(X1),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_262,c_15])).

cnf(c_0,plain,
    ( ~ sP1(X0,X1,X2)
    | ~ sP0(X2,X1,X0)
    | r3_wellord1(X0,X2,X1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_23,negated_conjecture,
    ( ~ r3_wellord1(sK4,sK4,k6_relat_1(k3_relat_1(sK4))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_286,plain,
    ( ~ sP1(X0,X1,X2)
    | ~ sP0(X2,X1,X0)
    | k6_relat_1(k3_relat_1(sK4)) != X1
    | sK4 != X2
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_23])).

cnf(c_287,plain,
    ( ~ sP1(sK4,k6_relat_1(k3_relat_1(sK4)),sK4)
    | ~ sP0(sK4,k6_relat_1(k3_relat_1(sK4)),sK4) ),
    inference(unflattening,[status(thm)],[c_286])).

cnf(c_299,plain,
    ( ~ sP0(sK4,k6_relat_1(k3_relat_1(sK4)),sK4)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k6_relat_1(k3_relat_1(sK4)) != k6_relat_1(X2)
    | sK4 != X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_274,c_287])).

cnf(c_300,plain,
    ( ~ sP0(sK4,k6_relat_1(k3_relat_1(sK4)),sK4)
    | ~ v1_relat_1(sK4)
    | k6_relat_1(k3_relat_1(sK4)) != k6_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_299])).

cnf(c_304,plain,
    ( ~ sP0(sK4,k6_relat_1(k3_relat_1(sK4)),sK4)
    | k6_relat_1(k3_relat_1(sK4)) != k6_relat_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_300,c_24])).

cnf(c_2609,plain,
    ( k6_relat_1(k3_relat_1(sK4)) != k6_relat_1(X0)
    | sP0(sK4,k6_relat_1(k3_relat_1(sK4)),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_304])).

cnf(c_2798,plain,
    ( sP0(sK4,k6_relat_1(k3_relat_1(sK4)),sK4) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2609])).

cnf(c_5176,plain,
    ( r2_hidden(sK3(sK4,k6_relat_1(k3_relat_1(sK4)),sK4),k3_relat_1(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4981,c_2798])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_funct_1(k6_relat_1(X1),X0) = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2610,plain,
    ( k1_funct_1(k6_relat_1(X0),X1) = X1
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_5181,plain,
    ( k1_funct_1(k6_relat_1(k3_relat_1(sK4)),sK3(sK4,k6_relat_1(k3_relat_1(sK4)),sK4)) = sK3(sK4,k6_relat_1(k3_relat_1(sK4)),sK4) ),
    inference(superposition,[status(thm)],[c_5176,c_2610])).

cnf(c_3,plain,
    ( sP0(X0,X1,X2)
    | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)
    | r2_hidden(k4_tarski(k1_funct_1(X1,sK2(X0,X1,X2)),k1_funct_1(X1,sK3(X0,X1,X2))),X0)
    | ~ v2_funct_1(X1)
    | k1_relat_1(X1) != k3_relat_1(X2)
    | k2_relat_1(X1) != k3_relat_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_2621,plain,
    ( k1_relat_1(X0) != k3_relat_1(X1)
    | k2_relat_1(X0) != k3_relat_1(X2)
    | sP0(X2,X0,X1) = iProver_top
    | r2_hidden(k4_tarski(sK2(X2,X0,X1),sK3(X2,X0,X1)),X1) = iProver_top
    | r2_hidden(k4_tarski(k1_funct_1(X0,sK2(X2,X0,X1)),k1_funct_1(X0,sK3(X2,X0,X1))),X2) = iProver_top
    | v2_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3858,plain,
    ( k2_relat_1(k6_relat_1(X0)) != k3_relat_1(X1)
    | k3_relat_1(X2) != X0
    | sP0(X1,k6_relat_1(X0),X2) = iProver_top
    | r2_hidden(k4_tarski(sK2(X1,k6_relat_1(X0),X2),sK3(X1,k6_relat_1(X0),X2)),X2) = iProver_top
    | r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(X0),sK2(X1,k6_relat_1(X0),X2)),k1_funct_1(k6_relat_1(X0),sK3(X1,k6_relat_1(X0),X2))),X1) = iProver_top
    | v2_funct_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_22,c_2621])).

cnf(c_3859,plain,
    ( k3_relat_1(X0) != X1
    | k3_relat_1(X2) != X1
    | sP0(X2,k6_relat_1(X1),X0) = iProver_top
    | r2_hidden(k4_tarski(sK2(X2,k6_relat_1(X1),X0),sK3(X2,k6_relat_1(X1),X0)),X0) = iProver_top
    | r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(X1),sK2(X2,k6_relat_1(X1),X0)),k1_funct_1(k6_relat_1(X1),sK3(X2,k6_relat_1(X1),X0))),X2) = iProver_top
    | v2_funct_1(k6_relat_1(X1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3858,c_21])).

cnf(c_4495,plain,
    ( k3_relat_1(X0) != X1
    | k3_relat_1(X2) != X1
    | sP0(X2,k6_relat_1(X1),X0) = iProver_top
    | r2_hidden(k4_tarski(sK2(X2,k6_relat_1(X1),X0),sK3(X2,k6_relat_1(X1),X0)),X0) = iProver_top
    | r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(X1),sK2(X2,k6_relat_1(X1),X0)),k1_funct_1(k6_relat_1(X1),sK3(X2,k6_relat_1(X1),X0))),X2) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3859,c_2611])).

cnf(c_4499,plain,
    ( k3_relat_1(X0) != k3_relat_1(X1)
    | sP0(X0,k6_relat_1(k3_relat_1(X1)),X1) = iProver_top
    | r2_hidden(k4_tarski(sK2(X0,k6_relat_1(k3_relat_1(X1)),X1),sK3(X0,k6_relat_1(k3_relat_1(X1)),X1)),X1) = iProver_top
    | r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(X1)),sK2(X0,k6_relat_1(k3_relat_1(X1)),X1)),k1_funct_1(k6_relat_1(k3_relat_1(X1)),sK3(X0,k6_relat_1(k3_relat_1(X1)),X1))),X0) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4495])).

cnf(c_5497,plain,
    ( sP0(X0,k6_relat_1(k3_relat_1(X0)),X0) = iProver_top
    | r2_hidden(k4_tarski(sK2(X0,k6_relat_1(k3_relat_1(X0)),X0),sK3(X0,k6_relat_1(k3_relat_1(X0)),X0)),X0) = iProver_top
    | r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(X0)),sK2(X0,k6_relat_1(k3_relat_1(X0)),X0)),k1_funct_1(k6_relat_1(k3_relat_1(X0)),sK3(X0,k6_relat_1(k3_relat_1(X0)),X0))),X0) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4499])).

cnf(c_6232,plain,
    ( sP0(sK4,k6_relat_1(k3_relat_1(sK4)),sK4) = iProver_top
    | r2_hidden(k4_tarski(sK2(sK4,k6_relat_1(k3_relat_1(sK4)),sK4),sK3(sK4,k6_relat_1(k3_relat_1(sK4)),sK4)),sK4) = iProver_top
    | r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(sK4)),sK2(sK4,k6_relat_1(k3_relat_1(sK4)),sK4)),sK3(sK4,k6_relat_1(k3_relat_1(sK4)),sK4)),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_5181,c_5497])).

cnf(c_5,plain,
    ( sP0(X0,X1,X2)
    | r2_hidden(sK2(X0,X1,X2),k3_relat_1(X2))
    | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)
    | ~ v2_funct_1(X1)
    | k1_relat_1(X1) != k3_relat_1(X2)
    | k2_relat_1(X1) != k3_relat_1(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_2619,plain,
    ( k1_relat_1(X0) != k3_relat_1(X1)
    | k2_relat_1(X0) != k3_relat_1(X2)
    | sP0(X2,X0,X1) = iProver_top
    | r2_hidden(sK2(X2,X0,X1),k3_relat_1(X1)) = iProver_top
    | r2_hidden(k4_tarski(sK2(X2,X0,X1),sK3(X2,X0,X1)),X1) = iProver_top
    | v2_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3683,plain,
    ( k2_relat_1(k6_relat_1(X0)) != k3_relat_1(X1)
    | k3_relat_1(X2) != X0
    | sP0(X1,k6_relat_1(X0),X2) = iProver_top
    | r2_hidden(sK2(X1,k6_relat_1(X0),X2),k3_relat_1(X2)) = iProver_top
    | r2_hidden(k4_tarski(sK2(X1,k6_relat_1(X0),X2),sK3(X1,k6_relat_1(X0),X2)),X2) = iProver_top
    | v2_funct_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_22,c_2619])).

cnf(c_3684,plain,
    ( k3_relat_1(X0) != X1
    | k3_relat_1(X2) != X1
    | sP0(X2,k6_relat_1(X1),X0) = iProver_top
    | r2_hidden(sK2(X2,k6_relat_1(X1),X0),k3_relat_1(X0)) = iProver_top
    | r2_hidden(k4_tarski(sK2(X2,k6_relat_1(X1),X0),sK3(X2,k6_relat_1(X1),X0)),X0) = iProver_top
    | v2_funct_1(k6_relat_1(X1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3683,c_21])).

cnf(c_3797,plain,
    ( k3_relat_1(X0) != X1
    | k3_relat_1(X2) != X1
    | sP0(X2,k6_relat_1(X1),X0) = iProver_top
    | r2_hidden(sK2(X2,k6_relat_1(X1),X0),k3_relat_1(X0)) = iProver_top
    | r2_hidden(k4_tarski(sK2(X2,k6_relat_1(X1),X0),sK3(X2,k6_relat_1(X1),X0)),X0) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3684,c_2611])).

cnf(c_3801,plain,
    ( k3_relat_1(X0) != k3_relat_1(X1)
    | sP0(X0,k6_relat_1(k3_relat_1(X1)),X1) = iProver_top
    | r2_hidden(sK2(X0,k6_relat_1(k3_relat_1(X1)),X1),k3_relat_1(X1)) = iProver_top
    | r2_hidden(k4_tarski(sK2(X0,k6_relat_1(k3_relat_1(X1)),X1),sK3(X0,k6_relat_1(k3_relat_1(X1)),X1)),X1) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3797])).

cnf(c_3933,plain,
    ( sP0(X0,k6_relat_1(k3_relat_1(X0)),X0) = iProver_top
    | r2_hidden(sK2(X0,k6_relat_1(k3_relat_1(X0)),X0),k3_relat_1(X0)) = iProver_top
    | r2_hidden(k4_tarski(sK2(X0,k6_relat_1(k3_relat_1(X0)),X0),sK3(X0,k6_relat_1(k3_relat_1(X0)),X0)),X0) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3801])).

cnf(c_19,plain,
    ( r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_342,plain,
    ( r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_24])).

cnf(c_343,plain,
    ( r2_hidden(X0,k3_relat_1(sK4))
    | ~ r2_hidden(k4_tarski(X0,X1),sK4) ),
    inference(unflattening,[status(thm)],[c_342])).

cnf(c_2606,plain,
    ( r2_hidden(X0,k3_relat_1(sK4)) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_343])).

cnf(c_3947,plain,
    ( sP0(sK4,k6_relat_1(k3_relat_1(sK4)),sK4) = iProver_top
    | r2_hidden(sK2(sK4,k6_relat_1(k3_relat_1(sK4)),sK4),k3_relat_1(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3933,c_2606])).

cnf(c_4013,plain,
    ( r2_hidden(sK2(sK4,k6_relat_1(k3_relat_1(sK4)),sK4),k3_relat_1(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3947,c_2798])).

cnf(c_4018,plain,
    ( k1_funct_1(k6_relat_1(k3_relat_1(sK4)),sK2(sK4,k6_relat_1(k3_relat_1(sK4)),sK4)) = sK2(sK4,k6_relat_1(k3_relat_1(sK4)),sK4) ),
    inference(superposition,[status(thm)],[c_4013,c_2610])).

cnf(c_6308,plain,
    ( sP0(sK4,k6_relat_1(k3_relat_1(sK4)),sK4) = iProver_top
    | r2_hidden(k4_tarski(sK2(sK4,k6_relat_1(k3_relat_1(sK4)),sK4),sK3(sK4,k6_relat_1(k3_relat_1(sK4)),sK4)),sK4) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6232,c_4018])).

cnf(c_2,plain,
    ( sP0(X0,X1,X2)
    | ~ r2_hidden(sK3(X0,X1,X2),k3_relat_1(X2))
    | ~ r2_hidden(sK2(X0,X1,X2),k3_relat_1(X2))
    | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)
    | ~ r2_hidden(k4_tarski(k1_funct_1(X1,sK2(X0,X1,X2)),k1_funct_1(X1,sK3(X0,X1,X2))),X0)
    | ~ v2_funct_1(X1)
    | k1_relat_1(X1) != k3_relat_1(X2)
    | k2_relat_1(X1) != k3_relat_1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_2622,plain,
    ( k1_relat_1(X0) != k3_relat_1(X1)
    | k2_relat_1(X0) != k3_relat_1(X2)
    | sP0(X2,X0,X1) = iProver_top
    | r2_hidden(sK3(X2,X0,X1),k3_relat_1(X1)) != iProver_top
    | r2_hidden(sK2(X2,X0,X1),k3_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(sK2(X2,X0,X1),sK3(X2,X0,X1)),X1) != iProver_top
    | r2_hidden(k4_tarski(k1_funct_1(X0,sK2(X2,X0,X1)),k1_funct_1(X0,sK3(X2,X0,X1))),X2) != iProver_top
    | v2_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3373,plain,
    ( k2_relat_1(k6_relat_1(X0)) != k3_relat_1(X1)
    | k3_relat_1(X2) != X0
    | sP0(X1,k6_relat_1(X0),X2) = iProver_top
    | r2_hidden(sK3(X1,k6_relat_1(X0),X2),k3_relat_1(X2)) != iProver_top
    | r2_hidden(sK2(X1,k6_relat_1(X0),X2),k3_relat_1(X2)) != iProver_top
    | r2_hidden(k4_tarski(sK2(X1,k6_relat_1(X0),X2),sK3(X1,k6_relat_1(X0),X2)),X2) != iProver_top
    | r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(X0),sK2(X1,k6_relat_1(X0),X2)),k1_funct_1(k6_relat_1(X0),sK3(X1,k6_relat_1(X0),X2))),X1) != iProver_top
    | v2_funct_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_22,c_2622])).

cnf(c_3374,plain,
    ( k3_relat_1(X0) != X1
    | k3_relat_1(X2) != X1
    | sP0(X2,k6_relat_1(X1),X0) = iProver_top
    | r2_hidden(sK3(X2,k6_relat_1(X1),X0),k3_relat_1(X0)) != iProver_top
    | r2_hidden(sK2(X2,k6_relat_1(X1),X0),k3_relat_1(X0)) != iProver_top
    | r2_hidden(k4_tarski(sK2(X2,k6_relat_1(X1),X0),sK3(X2,k6_relat_1(X1),X0)),X0) != iProver_top
    | r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(X1),sK2(X2,k6_relat_1(X1),X0)),k1_funct_1(k6_relat_1(X1),sK3(X2,k6_relat_1(X1),X0))),X2) != iProver_top
    | v2_funct_1(k6_relat_1(X1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3373,c_21])).

cnf(c_3528,plain,
    ( k3_relat_1(X0) != X1
    | k3_relat_1(X2) != X1
    | sP0(X2,k6_relat_1(X1),X0) = iProver_top
    | r2_hidden(sK3(X2,k6_relat_1(X1),X0),k3_relat_1(X0)) != iProver_top
    | r2_hidden(sK2(X2,k6_relat_1(X1),X0),k3_relat_1(X0)) != iProver_top
    | r2_hidden(k4_tarski(sK2(X2,k6_relat_1(X1),X0),sK3(X2,k6_relat_1(X1),X0)),X0) != iProver_top
    | r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(X1),sK2(X2,k6_relat_1(X1),X0)),k1_funct_1(k6_relat_1(X1),sK3(X2,k6_relat_1(X1),X0))),X2) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3374,c_2611])).

cnf(c_3532,plain,
    ( k3_relat_1(X0) != k3_relat_1(X1)
    | sP0(X0,k6_relat_1(k3_relat_1(X1)),X1) = iProver_top
    | r2_hidden(sK3(X0,k6_relat_1(k3_relat_1(X1)),X1),k3_relat_1(X1)) != iProver_top
    | r2_hidden(sK2(X0,k6_relat_1(k3_relat_1(X1)),X1),k3_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(sK2(X0,k6_relat_1(k3_relat_1(X1)),X1),sK3(X0,k6_relat_1(k3_relat_1(X1)),X1)),X1) != iProver_top
    | r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(X1)),sK2(X0,k6_relat_1(k3_relat_1(X1)),X1)),k1_funct_1(k6_relat_1(k3_relat_1(X1)),sK3(X0,k6_relat_1(k3_relat_1(X1)),X1))),X0) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3528])).

cnf(c_3543,plain,
    ( sP0(X0,k6_relat_1(k3_relat_1(X0)),X0) = iProver_top
    | r2_hidden(sK3(X0,k6_relat_1(k3_relat_1(X0)),X0),k3_relat_1(X0)) != iProver_top
    | r2_hidden(sK2(X0,k6_relat_1(k3_relat_1(X0)),X0),k3_relat_1(X0)) != iProver_top
    | r2_hidden(k4_tarski(sK2(X0,k6_relat_1(k3_relat_1(X0)),X0),sK3(X0,k6_relat_1(k3_relat_1(X0)),X0)),X0) != iProver_top
    | r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(X0)),sK2(X0,k6_relat_1(k3_relat_1(X0)),X0)),k1_funct_1(k6_relat_1(k3_relat_1(X0)),sK3(X0,k6_relat_1(k3_relat_1(X0)),X0))),X0) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3532])).

cnf(c_4022,plain,
    ( sP0(sK4,k6_relat_1(k3_relat_1(sK4)),sK4) = iProver_top
    | r2_hidden(sK3(sK4,k6_relat_1(k3_relat_1(sK4)),sK4),k3_relat_1(sK4)) != iProver_top
    | r2_hidden(sK2(sK4,k6_relat_1(k3_relat_1(sK4)),sK4),k3_relat_1(sK4)) != iProver_top
    | r2_hidden(k4_tarski(sK2(sK4,k6_relat_1(k3_relat_1(sK4)),sK4),sK3(sK4,k6_relat_1(k3_relat_1(sK4)),sK4)),sK4) != iProver_top
    | r2_hidden(k4_tarski(sK2(sK4,k6_relat_1(k3_relat_1(sK4)),sK4),k1_funct_1(k6_relat_1(k3_relat_1(sK4)),sK3(sK4,k6_relat_1(k3_relat_1(sK4)),sK4))),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4018,c_3543])).

cnf(c_4294,plain,
    ( r2_hidden(sK3(sK4,k6_relat_1(k3_relat_1(sK4)),sK4),k3_relat_1(sK4)) != iProver_top
    | r2_hidden(k4_tarski(sK2(sK4,k6_relat_1(k3_relat_1(sK4)),sK4),sK3(sK4,k6_relat_1(k3_relat_1(sK4)),sK4)),sK4) != iProver_top
    | r2_hidden(k4_tarski(sK2(sK4,k6_relat_1(k3_relat_1(sK4)),sK4),k1_funct_1(k6_relat_1(k3_relat_1(sK4)),sK3(sK4,k6_relat_1(k3_relat_1(sK4)),sK4))),sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4022,c_2798,c_3947])).

cnf(c_4301,plain,
    ( r2_hidden(k4_tarski(sK2(sK4,k6_relat_1(k3_relat_1(sK4)),sK4),sK3(sK4,k6_relat_1(k3_relat_1(sK4)),sK4)),sK4) != iProver_top
    | r2_hidden(k4_tarski(sK2(sK4,k6_relat_1(k3_relat_1(sK4)),sK4),k1_funct_1(k6_relat_1(k3_relat_1(sK4)),sK3(sK4,k6_relat_1(k3_relat_1(sK4)),sK4))),sK4) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4294,c_2605])).

cnf(c_5183,plain,
    ( r2_hidden(k4_tarski(sK2(sK4,k6_relat_1(k3_relat_1(sK4)),sK4),sK3(sK4,k6_relat_1(k3_relat_1(sK4)),sK4)),sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5181,c_4301])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6308,c_5183,c_2798])).


%------------------------------------------------------------------------------
