%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0709+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:57 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 228 expanded)
%              Number of clauses        :   51 (  62 expanded)
%              Number of leaves         :   10 (  45 expanded)
%              Depth                    :   17
%              Number of atoms          :  485 (1292 expanded)
%              Number of equality atoms :   87 ( 218 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( ( v2_funct_1(X1)
            & r1_tarski(X0,k1_relat_1(X1)) )
         => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f15,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
      & v2_funct_1(X1)
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f16,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
      & v2_funct_1(X1)
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f28,plain,
    ( ? [X0,X1] :
        ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
        & v2_funct_1(X1)
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k10_relat_1(sK5,k9_relat_1(sK5,sK4)) != sK4
      & v2_funct_1(sK5)
      & r1_tarski(sK4,k1_relat_1(sK5))
      & v1_funct_1(sK5)
      & v1_relat_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( k10_relat_1(sK5,k9_relat_1(sK5,sK4)) != sK4
    & v2_funct_1(sK5)
    & r1_tarski(sK4,k1_relat_1(sK5))
    & v1_funct_1(sK5)
    & v1_relat_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f16,f28])).

fof(f49,plain,(
    v2_funct_1(sK5) ),
    inference(cnf_transformation,[],[f29])).

fof(f46,plain,(
    v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f29])).

fof(f47,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f29])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f23,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f25,plain,(
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
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
            | ~ r2_hidden(X3,k1_relat_1(X0))
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
              & r2_hidden(X3,k1_relat_1(X0)) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(k1_funct_1(X0,sK3(X0,X1,X2)),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),k1_relat_1(X0))
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( r2_hidden(k1_funct_1(X0,sK3(X0,X1,X2)),X1)
            & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X0)) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ( ( ~ r2_hidden(k1_funct_1(X0,sK3(X0,X1,X2)),X1)
                | ~ r2_hidden(sK3(X0,X1,X2),k1_relat_1(X0))
                | ~ r2_hidden(sK3(X0,X1,X2),X2) )
              & ( ( r2_hidden(k1_funct_1(X0,sK3(X0,X1,X2)),X1)
                  & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X0)) )
                | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f26])).

fof(f40,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(k1_funct_1(X0,X4),X1)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | k10_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f56,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k10_relat_1(X0,X1))
      | ~ r2_hidden(k1_funct_1(X0,X4),X1)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f40])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X3
                      & r2_hidden(X4,X1)
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) ) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X3
                      & r2_hidden(X4,X1)
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( k1_funct_1(X0,X5) = X3
                      & r2_hidden(X5,X1)
                      & r2_hidden(X5,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( k1_funct_1(X0,X7) != X6
                      | ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
                & ( ? [X8] :
                      ( k1_funct_1(X0,X8) = X6
                      & r2_hidden(X8,X1)
                      & r2_hidden(X8,k1_relat_1(X0)) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f17])).

fof(f21,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( k1_funct_1(X0,X8) = X6
          & r2_hidden(X8,X1)
          & r2_hidden(X8,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X1,X6)) = X6
        & r2_hidden(sK2(X0,X1,X6),X1)
        & r2_hidden(sK2(X0,X1,X6),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( k1_funct_1(X0,X5) = X3
          & r2_hidden(X5,X1)
          & r2_hidden(X5,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK1(X0,X1,X2)) = X3
        & r2_hidden(sK1(X0,X1,X2),X1)
        & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( k1_funct_1(X0,X4) != X3
                | ~ r2_hidden(X4,X1)
                | ~ r2_hidden(X4,k1_relat_1(X0)) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( k1_funct_1(X0,X5) = X3
                & r2_hidden(X5,X1)
                & r2_hidden(X5,k1_relat_1(X0)) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( k1_funct_1(X0,X4) != sK0(X0,X1,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,k1_relat_1(X0)) )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( k1_funct_1(X0,X5) = sK0(X0,X1,X2)
              & r2_hidden(X5,X1)
              & r2_hidden(X5,k1_relat_1(X0)) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( k1_funct_1(X0,X4) != sK0(X0,X1,X2)
                    | ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(X4,k1_relat_1(X0)) )
                | ~ r2_hidden(sK0(X0,X1,X2),X2) )
              & ( ( k1_funct_1(X0,sK1(X0,X1,X2)) = sK0(X0,X1,X2)
                  & r2_hidden(sK1(X0,X1,X2),X1)
                  & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X0)) )
                | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( k1_funct_1(X0,X7) != X6
                      | ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK2(X0,X1,X6)) = X6
                    & r2_hidden(sK2(X0,X1,X6),X1)
                    & r2_hidden(sK2(X0,X1,X6),k1_relat_1(X0)) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f21,f20,f19])).

fof(f33,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | k1_funct_1(X0,X7) != X6
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X7,k1_relat_1(X0))
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f51,plain,(
    ! [X2,X0,X7,X1] :
      ( r2_hidden(k1_funct_1(X0,X7),X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X7,k1_relat_1(X0))
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f33])).

fof(f52,plain,(
    ! [X0,X7,X1] :
      ( r2_hidden(k1_funct_1(X0,X7),k9_relat_1(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X7,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f51])).

fof(f48,plain,(
    r1_tarski(sK4,k1_relat_1(sK5)) ),
    inference(cnf_transformation,[],[f29])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X0,X1) = X2
      | ~ r2_hidden(k1_funct_1(X0,sK3(X0,X1,X2)),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),k1_relat_1(X0))
      | ~ r2_hidden(sK3(X0,X1,X2),X2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X0,X1) = X2
      | r2_hidden(k1_funct_1(X0,sK3(X0,X1,X2)),X1)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),k1_relat_1(X0))
      | r2_hidden(sK3(X0,X1,X2),X2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f50,plain,(
    k10_relat_1(sK5,k9_relat_1(sK5,sK4)) != sK4 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_14,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_15,plain,
    ( r1_tarski(k10_relat_1(X0,k9_relat_1(X0,X1)),X1)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_17,negated_conjecture,
    ( v2_funct_1(sK5) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_223,plain,
    ( r1_tarski(k10_relat_1(X0,k9_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_17])).

cnf(c_224,plain,
    ( r1_tarski(k10_relat_1(sK5,k9_relat_1(sK5,X0)),X0)
    | ~ v1_relat_1(sK5)
    | ~ v1_funct_1(sK5) ),
    inference(unflattening,[status(thm)],[c_223])).

cnf(c_20,negated_conjecture,
    ( v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_19,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_228,plain,
    ( r1_tarski(k10_relat_1(sK5,k9_relat_1(sK5,X0)),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_224,c_20,c_19])).

cnf(c_252,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | X3 != X2
    | k10_relat_1(sK5,k9_relat_1(sK5,X3)) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_228])).

cnf(c_253,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k10_relat_1(sK5,k9_relat_1(sK5,X1))) ),
    inference(unflattening,[status(thm)],[c_252])).

cnf(c_1266,plain,
    ( r2_hidden(sK3(sK5,k9_relat_1(sK5,sK4),sK4),X0)
    | ~ r2_hidden(sK3(sK5,k9_relat_1(sK5,sK4),sK4),k10_relat_1(sK5,k9_relat_1(sK5,X0))) ),
    inference(instantiation,[status(thm)],[c_253])).

cnf(c_1742,plain,
    ( ~ r2_hidden(sK3(sK5,k9_relat_1(sK5,sK4),sK4),k10_relat_1(sK5,k9_relat_1(sK5,sK4)))
    | r2_hidden(sK3(sK5,k9_relat_1(sK5,sK4),sK4),sK4) ),
    inference(instantiation,[status(thm)],[c_1266])).

cnf(c_11,plain,
    ( r2_hidden(X0,k10_relat_1(X1,X2))
    | ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k1_funct_1(X1,X0),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_483,plain,
    ( r2_hidden(X0,k10_relat_1(X1,X2))
    | ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k1_funct_1(X1,X0),X2)
    | ~ v1_relat_1(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_19])).

cnf(c_484,plain,
    ( r2_hidden(X0,k10_relat_1(sK5,X1))
    | ~ r2_hidden(X0,k1_relat_1(sK5))
    | ~ r2_hidden(k1_funct_1(sK5,X0),X1)
    | ~ v1_relat_1(sK5) ),
    inference(unflattening,[status(thm)],[c_483])).

cnf(c_488,plain,
    ( ~ r2_hidden(k1_funct_1(sK5,X0),X1)
    | ~ r2_hidden(X0,k1_relat_1(sK5))
    | r2_hidden(X0,k10_relat_1(sK5,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_484,c_20])).

cnf(c_489,plain,
    ( r2_hidden(X0,k10_relat_1(sK5,X1))
    | ~ r2_hidden(X0,k1_relat_1(sK5))
    | ~ r2_hidden(k1_funct_1(sK5,X0),X1) ),
    inference(renaming,[status(thm)],[c_488])).

cnf(c_1208,plain,
    ( r2_hidden(sK3(sK5,k9_relat_1(sK5,sK4),sK4),k10_relat_1(sK5,X0))
    | ~ r2_hidden(sK3(sK5,k9_relat_1(sK5,sK4),sK4),k1_relat_1(sK5))
    | ~ r2_hidden(k1_funct_1(sK5,sK3(sK5,k9_relat_1(sK5,sK4),sK4)),X0) ),
    inference(instantiation,[status(thm)],[c_489])).

cnf(c_1265,plain,
    ( r2_hidden(sK3(sK5,k9_relat_1(sK5,sK4),sK4),k10_relat_1(sK5,k9_relat_1(sK5,X0)))
    | ~ r2_hidden(sK3(sK5,k9_relat_1(sK5,sK4),sK4),k1_relat_1(sK5))
    | ~ r2_hidden(k1_funct_1(sK5,sK3(sK5,k9_relat_1(sK5,sK4),sK4)),k9_relat_1(sK5,X0)) ),
    inference(instantiation,[status(thm)],[c_1208])).

cnf(c_1450,plain,
    ( r2_hidden(sK3(sK5,k9_relat_1(sK5,sK4),sK4),k10_relat_1(sK5,k9_relat_1(sK5,sK4)))
    | ~ r2_hidden(sK3(sK5,k9_relat_1(sK5,sK4),sK4),k1_relat_1(sK5))
    | ~ r2_hidden(k1_funct_1(sK5,sK3(sK5,k9_relat_1(sK5,sK4),sK4)),k9_relat_1(sK5,sK4)) ),
    inference(instantiation,[status(thm)],[c_1265])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(X2))
    | r2_hidden(k1_funct_1(X2,X0),k9_relat_1(X2,X1))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_399,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(X2))
    | r2_hidden(k1_funct_1(X2,X0),k9_relat_1(X2,X1))
    | ~ v1_relat_1(X2)
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_19])).

cnf(c_400,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(sK5))
    | r2_hidden(k1_funct_1(sK5,X0),k9_relat_1(sK5,X1))
    | ~ v1_relat_1(sK5) ),
    inference(unflattening,[status(thm)],[c_399])).

cnf(c_404,plain,
    ( r2_hidden(k1_funct_1(sK5,X0),k9_relat_1(sK5,X1))
    | ~ r2_hidden(X0,k1_relat_1(sK5))
    | ~ r2_hidden(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_400,c_20])).

cnf(c_405,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(sK5))
    | r2_hidden(k1_funct_1(sK5,X0),k9_relat_1(sK5,X1)) ),
    inference(renaming,[status(thm)],[c_404])).

cnf(c_1209,plain,
    ( ~ r2_hidden(sK3(sK5,k9_relat_1(sK5,sK4),sK4),X0)
    | ~ r2_hidden(sK3(sK5,k9_relat_1(sK5,sK4),sK4),k1_relat_1(sK5))
    | r2_hidden(k1_funct_1(sK5,sK3(sK5,k9_relat_1(sK5,sK4),sK4)),k9_relat_1(sK5,X0)) ),
    inference(instantiation,[status(thm)],[c_405])).

cnf(c_1305,plain,
    ( ~ r2_hidden(sK3(sK5,k9_relat_1(sK5,sK4),sK4),k1_relat_1(sK5))
    | ~ r2_hidden(sK3(sK5,k9_relat_1(sK5,sK4),sK4),sK4)
    | r2_hidden(k1_funct_1(sK5,sK3(sK5,k9_relat_1(sK5,sK4),sK4)),k9_relat_1(sK5,sK4)) ),
    inference(instantiation,[status(thm)],[c_1209])).

cnf(c_18,negated_conjecture,
    ( r1_tarski(sK4,k1_relat_1(sK5)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_240,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | k1_relat_1(sK5) != X2
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_18])).

cnf(c_241,plain,
    ( r2_hidden(X0,k1_relat_1(sK5))
    | ~ r2_hidden(X0,sK4) ),
    inference(unflattening,[status(thm)],[c_240])).

cnf(c_1166,plain,
    ( r2_hidden(sK3(sK5,k9_relat_1(sK5,sK4),sK4),k1_relat_1(sK5))
    | ~ r2_hidden(sK3(sK5,k9_relat_1(sK5,sK4),sK4),sK4) ),
    inference(instantiation,[status(thm)],[c_241])).

cnf(c_8,plain,
    ( ~ r2_hidden(sK3(X0,X1,X2),X2)
    | ~ r2_hidden(sK3(X0,X1,X2),k1_relat_1(X0))
    | ~ r2_hidden(k1_funct_1(X0,sK3(X0,X1,X2)),X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k10_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_312,plain,
    ( ~ r2_hidden(sK3(X0,X1,X2),X2)
    | ~ r2_hidden(sK3(X0,X1,X2),k1_relat_1(X0))
    | ~ r2_hidden(k1_funct_1(X0,sK3(X0,X1,X2)),X1)
    | ~ v1_relat_1(X0)
    | k10_relat_1(X0,X1) = X2
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_19])).

cnf(c_313,plain,
    ( ~ r2_hidden(sK3(sK5,X0,X1),X1)
    | ~ r2_hidden(sK3(sK5,X0,X1),k1_relat_1(sK5))
    | ~ r2_hidden(k1_funct_1(sK5,sK3(sK5,X0,X1)),X0)
    | ~ v1_relat_1(sK5)
    | k10_relat_1(sK5,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_312])).

cnf(c_317,plain,
    ( ~ r2_hidden(k1_funct_1(sK5,sK3(sK5,X0,X1)),X0)
    | ~ r2_hidden(sK3(sK5,X0,X1),k1_relat_1(sK5))
    | ~ r2_hidden(sK3(sK5,X0,X1),X1)
    | k10_relat_1(sK5,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_313,c_20])).

cnf(c_318,plain,
    ( ~ r2_hidden(sK3(sK5,X0,X1),X1)
    | ~ r2_hidden(sK3(sK5,X0,X1),k1_relat_1(sK5))
    | ~ r2_hidden(k1_funct_1(sK5,sK3(sK5,X0,X1)),X0)
    | k10_relat_1(sK5,X0) = X1 ),
    inference(renaming,[status(thm)],[c_317])).

cnf(c_1150,plain,
    ( ~ r2_hidden(sK3(sK5,k9_relat_1(sK5,sK4),sK4),k1_relat_1(sK5))
    | ~ r2_hidden(sK3(sK5,k9_relat_1(sK5,sK4),sK4),sK4)
    | ~ r2_hidden(k1_funct_1(sK5,sK3(sK5,k9_relat_1(sK5,sK4),sK4)),k9_relat_1(sK5,sK4))
    | k10_relat_1(sK5,k9_relat_1(sK5,sK4)) = sK4 ),
    inference(instantiation,[status(thm)],[c_318])).

cnf(c_9,plain,
    ( r2_hidden(sK3(X0,X1,X2),X2)
    | r2_hidden(k1_funct_1(X0,sK3(X0,X1,X2)),X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k10_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_291,plain,
    ( r2_hidden(sK3(X0,X1,X2),X2)
    | r2_hidden(k1_funct_1(X0,sK3(X0,X1,X2)),X1)
    | ~ v1_relat_1(X0)
    | k10_relat_1(X0,X1) = X2
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_19])).

cnf(c_292,plain,
    ( r2_hidden(sK3(sK5,X0,X1),X1)
    | r2_hidden(k1_funct_1(sK5,sK3(sK5,X0,X1)),X0)
    | ~ v1_relat_1(sK5)
    | k10_relat_1(sK5,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_291])).

cnf(c_296,plain,
    ( r2_hidden(k1_funct_1(sK5,sK3(sK5,X0,X1)),X0)
    | r2_hidden(sK3(sK5,X0,X1),X1)
    | k10_relat_1(sK5,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_292,c_20])).

cnf(c_297,plain,
    ( r2_hidden(sK3(sK5,X0,X1),X1)
    | r2_hidden(k1_funct_1(sK5,sK3(sK5,X0,X1)),X0)
    | k10_relat_1(sK5,X0) = X1 ),
    inference(renaming,[status(thm)],[c_296])).

cnf(c_1147,plain,
    ( r2_hidden(sK3(sK5,k9_relat_1(sK5,sK4),sK4),sK4)
    | r2_hidden(k1_funct_1(sK5,sK3(sK5,k9_relat_1(sK5,sK4),sK4)),k9_relat_1(sK5,sK4))
    | k10_relat_1(sK5,k9_relat_1(sK5,sK4)) = sK4 ),
    inference(instantiation,[status(thm)],[c_297])).

cnf(c_10,plain,
    ( r2_hidden(sK3(X0,X1,X2),X2)
    | r2_hidden(sK3(X0,X1,X2),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k10_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_270,plain,
    ( r2_hidden(sK3(X0,X1,X2),X2)
    | r2_hidden(sK3(X0,X1,X2),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | k10_relat_1(X0,X1) = X2
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_19])).

cnf(c_271,plain,
    ( r2_hidden(sK3(sK5,X0,X1),X1)
    | r2_hidden(sK3(sK5,X0,X1),k1_relat_1(sK5))
    | ~ v1_relat_1(sK5)
    | k10_relat_1(sK5,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_270])).

cnf(c_275,plain,
    ( r2_hidden(sK3(sK5,X0,X1),k1_relat_1(sK5))
    | r2_hidden(sK3(sK5,X0,X1),X1)
    | k10_relat_1(sK5,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_271,c_20])).

cnf(c_276,plain,
    ( r2_hidden(sK3(sK5,X0,X1),X1)
    | r2_hidden(sK3(sK5,X0,X1),k1_relat_1(sK5))
    | k10_relat_1(sK5,X0) = X1 ),
    inference(renaming,[status(thm)],[c_275])).

cnf(c_1140,plain,
    ( r2_hidden(sK3(sK5,k9_relat_1(sK5,sK4),sK4),k1_relat_1(sK5))
    | r2_hidden(sK3(sK5,k9_relat_1(sK5,sK4),sK4),sK4)
    | k10_relat_1(sK5,k9_relat_1(sK5,sK4)) = sK4 ),
    inference(instantiation,[status(thm)],[c_276])).

cnf(c_16,negated_conjecture,
    ( k10_relat_1(sK5,k9_relat_1(sK5,sK4)) != sK4 ),
    inference(cnf_transformation,[],[f50])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1742,c_1450,c_1305,c_1166,c_1150,c_1147,c_1140,c_16])).


%------------------------------------------------------------------------------
