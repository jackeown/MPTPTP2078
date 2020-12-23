%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0692+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:55 EST 2020

% Result     : Theorem 27.54s
% Output     : CNFRefutation 27.54s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 272 expanded)
%              Number of clauses        :   67 (  84 expanded)
%              Number of leaves         :   16 (  63 expanded)
%              Depth                    :   16
%              Number of atoms          :  612 (1468 expanded)
%              Number of equality atoms :  173 ( 397 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f46,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(k1_funct_1(X0,X4),X1)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | k10_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f66,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k10_relat_1(X0,X1))
      | ~ r2_hidden(k1_funct_1(X0,X4),X1)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( r1_tarski(X0,k2_relat_1(X1))
         => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f15,plain,(
    ? [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) != X0
      & r1_tarski(X0,k2_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f16,plain,(
    ? [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) != X0
      & r1_tarski(X0,k2_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f34,plain,
    ( ? [X0,X1] :
        ( k9_relat_1(X1,k10_relat_1(X1,X0)) != X0
        & r1_tarski(X0,k2_relat_1(X1))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k9_relat_1(sK8,k10_relat_1(sK8,sK7)) != sK7
      & r1_tarski(sK7,k2_relat_1(sK8))
      & v1_funct_1(sK8)
      & v1_relat_1(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( k9_relat_1(sK8,k10_relat_1(sK8,sK7)) != sK7
    & r1_tarski(sK7,k2_relat_1(sK8))
    & v1_funct_1(sK8)
    & v1_relat_1(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f16,f34])).

fof(f58,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f35])).

fof(f57,plain,(
    v1_relat_1(sK8) ),
    inference(cnf_transformation,[],[f35])).

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

fof(f43,plain,(
    ! [X4,X2,X0,X1] :
      ( k9_relat_1(X0,X1) = X2
      | k1_funct_1(X0,X4) != sK0(X0,X1,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(sK0(X0,X1,X2),X2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X2
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ? [X7] :
                      ( k1_funct_1(X0,X7) = X5
                      & r2_hidden(X7,k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f28])).

fof(f32,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK6(X0,X5)) = X5
        & r2_hidden(sK6(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK5(X0,X1)) = X2
        & r2_hidden(sK5(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k1_funct_1(X0,X3) != X2
                | ~ r2_hidden(X3,k1_relat_1(X0)) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( k1_funct_1(X0,X4) = X2
                & r2_hidden(X4,k1_relat_1(X0)) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( k1_funct_1(X0,X3) != sK4(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK4(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK4(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK4(X0,X1),X1) )
              & ( ( k1_funct_1(X0,sK5(X0,X1)) = sK4(X0,X1)
                  & r2_hidden(sK5(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK4(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK6(X0,X5)) = X5
                    & r2_hidden(sK6(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f29,f32,f31,f30])).

fof(f52,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK6(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f71,plain,(
    ! [X0,X5] :
      ( k1_funct_1(X0,sK6(X0,X5)) = X5
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f52])).

fof(f51,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK6(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f72,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK6(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f51])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X4),X1)
      | ~ r2_hidden(X4,X2)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f67,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X4),X1)
      | ~ r2_hidden(X4,k10_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f45])).

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

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f59,plain,(
    r1_tarski(sK7,k2_relat_1(sK8)) ),
    inference(cnf_transformation,[],[f35])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X0,X1) = X2
      | k1_funct_1(X0,sK1(X0,X1,X2)) = sK0(X0,X1,X2)
      | r2_hidden(sK0(X0,X1,X2),X2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f60,plain,(
    k9_relat_1(sK8,k10_relat_1(sK8,sK7)) != sK7 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_924,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1338,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,sK7)
    | X2 != X0
    | sK7 != X1 ),
    inference(instantiation,[status(thm)],[c_924])).

cnf(c_1397,plain,
    ( ~ r2_hidden(X0,sK7)
    | r2_hidden(X1,sK7)
    | X1 != X0
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_1338])).

cnf(c_2403,plain,
    ( r2_hidden(X0,sK7)
    | ~ r2_hidden(k1_funct_1(sK8,sK1(sK8,k10_relat_1(sK8,sK7),sK7)),sK7)
    | X0 != k1_funct_1(sK8,sK1(sK8,k10_relat_1(sK8,sK7),sK7))
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_1397])).

cnf(c_61156,plain,
    ( r2_hidden(sK0(sK8,k10_relat_1(sK8,sK7),sK7),sK7)
    | ~ r2_hidden(k1_funct_1(sK8,sK1(sK8,k10_relat_1(sK8,sK7),sK7)),sK7)
    | sK0(sK8,k10_relat_1(sK8,sK7),sK7) != k1_funct_1(sK8,sK1(sK8,k10_relat_1(sK8,sK7),sK7))
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_2403])).

cnf(c_920,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_4560,plain,
    ( X0 != X1
    | sK0(sK8,k10_relat_1(sK8,sK7),sK7) != X1
    | sK0(sK8,k10_relat_1(sK8,sK7),sK7) = X0 ),
    inference(instantiation,[status(thm)],[c_920])).

cnf(c_10461,plain,
    ( X0 != sK0(X1,k10_relat_1(sK8,sK7),sK7)
    | sK0(sK8,k10_relat_1(sK8,sK7),sK7) = X0
    | sK0(sK8,k10_relat_1(sK8,sK7),sK7) != sK0(X1,k10_relat_1(sK8,sK7),sK7) ),
    inference(instantiation,[status(thm)],[c_4560])).

cnf(c_26815,plain,
    ( sK0(sK8,k10_relat_1(sK8,sK7),sK7) != sK0(sK8,k10_relat_1(sK8,sK7),sK7)
    | sK0(sK8,k10_relat_1(sK8,sK7),sK7) = k1_funct_1(sK8,sK1(sK8,k10_relat_1(sK8,sK7),sK7))
    | k1_funct_1(sK8,sK1(sK8,k10_relat_1(sK8,sK7),sK7)) != sK0(sK8,k10_relat_1(sK8,sK7),sK7) ),
    inference(instantiation,[status(thm)],[c_10461])).

cnf(c_11,plain,
    ( r2_hidden(X0,k10_relat_1(X1,X2))
    | ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k1_funct_1(X1,X0),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_23,negated_conjecture,
    ( v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_616,plain,
    ( r2_hidden(X0,k10_relat_1(X1,X2))
    | ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k1_funct_1(X1,X0),X2)
    | ~ v1_relat_1(X1)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_23])).

cnf(c_617,plain,
    ( r2_hidden(X0,k10_relat_1(sK8,X1))
    | ~ r2_hidden(X0,k1_relat_1(sK8))
    | ~ r2_hidden(k1_funct_1(sK8,X0),X1)
    | ~ v1_relat_1(sK8) ),
    inference(unflattening,[status(thm)],[c_616])).

cnf(c_24,negated_conjecture,
    ( v1_relat_1(sK8) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_621,plain,
    ( ~ r2_hidden(k1_funct_1(sK8,X0),X1)
    | ~ r2_hidden(X0,k1_relat_1(sK8))
    | r2_hidden(X0,k10_relat_1(sK8,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_617,c_24])).

cnf(c_622,plain,
    ( r2_hidden(X0,k10_relat_1(sK8,X1))
    | ~ r2_hidden(X0,k1_relat_1(sK8))
    | ~ r2_hidden(k1_funct_1(sK8,X0),X1) ),
    inference(renaming,[status(thm)],[c_621])).

cnf(c_1784,plain,
    ( r2_hidden(sK6(sK8,sK0(sK8,k10_relat_1(sK8,sK7),sK7)),k10_relat_1(sK8,X0))
    | ~ r2_hidden(sK6(sK8,sK0(sK8,k10_relat_1(sK8,sK7),sK7)),k1_relat_1(sK8))
    | ~ r2_hidden(k1_funct_1(sK8,sK6(sK8,sK0(sK8,k10_relat_1(sK8,sK7),sK7))),X0) ),
    inference(instantiation,[status(thm)],[c_622])).

cnf(c_16343,plain,
    ( r2_hidden(sK6(sK8,sK0(sK8,k10_relat_1(sK8,sK7),sK7)),k10_relat_1(sK8,sK7))
    | ~ r2_hidden(sK6(sK8,sK0(sK8,k10_relat_1(sK8,sK7),sK7)),k1_relat_1(sK8))
    | ~ r2_hidden(k1_funct_1(sK8,sK6(sK8,sK0(sK8,k10_relat_1(sK8,sK7),sK7))),sK7) ),
    inference(instantiation,[status(thm)],[c_1784])).

cnf(c_15904,plain,
    ( sK0(sK8,k10_relat_1(sK8,sK7),sK7) != sK0(sK8,k10_relat_1(sK8,sK7),sK7)
    | sK0(sK8,k10_relat_1(sK8,sK7),sK7) = k1_funct_1(sK8,sK6(sK8,sK0(sK8,k10_relat_1(sK8,sK7),sK7)))
    | k1_funct_1(sK8,sK6(sK8,sK0(sK8,k10_relat_1(sK8,sK7),sK7))) != sK0(sK8,k10_relat_1(sK8,sK7),sK7) ),
    inference(instantiation,[status(thm)],[c_10461])).

cnf(c_919,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3359,plain,
    ( sK0(sK8,k10_relat_1(sK8,sK7),sK7) = sK0(sK8,k10_relat_1(sK8,sK7),sK7) ),
    inference(instantiation,[status(thm)],[c_919])).

cnf(c_1556,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK0(sK8,k10_relat_1(sK8,sK7),sK7),sK7)
    | X0 != sK0(sK8,k10_relat_1(sK8,sK7),sK7)
    | X1 != sK7 ),
    inference(instantiation,[status(thm)],[c_924])).

cnf(c_2020,plain,
    ( r2_hidden(X0,sK7)
    | ~ r2_hidden(sK0(sK8,k10_relat_1(sK8,sK7),sK7),sK7)
    | X0 != sK0(sK8,k10_relat_1(sK8,sK7),sK7)
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_1556])).

cnf(c_3027,plain,
    ( ~ r2_hidden(sK0(sK8,k10_relat_1(sK8,sK7),sK7),sK7)
    | r2_hidden(k1_funct_1(sK8,sK6(sK8,sK0(sK8,k10_relat_1(sK8,sK7),sK7))),sK7)
    | k1_funct_1(sK8,sK6(sK8,sK0(sK8,k10_relat_1(sK8,sK7),sK7))) != sK0(sK8,k10_relat_1(sK8,sK7),sK7)
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_2020])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(X2))
    | ~ r2_hidden(sK0(X2,X1,X3),X3)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | sK0(X2,X1,X3) != k1_funct_1(X2,X0)
    | k9_relat_1(X2,X1) = X3 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_475,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(X2))
    | ~ r2_hidden(sK0(X2,X1,X3),X3)
    | ~ v1_relat_1(X2)
    | sK0(X2,X1,X3) != k1_funct_1(X2,X0)
    | k9_relat_1(X2,X1) = X3
    | sK8 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_23])).

cnf(c_476,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(sK8))
    | ~ r2_hidden(sK0(sK8,X1,X2),X2)
    | ~ v1_relat_1(sK8)
    | sK0(sK8,X1,X2) != k1_funct_1(sK8,X0)
    | k9_relat_1(sK8,X1) = X2 ),
    inference(unflattening,[status(thm)],[c_475])).

cnf(c_480,plain,
    ( ~ r2_hidden(sK0(sK8,X1,X2),X2)
    | ~ r2_hidden(X0,k1_relat_1(sK8))
    | ~ r2_hidden(X0,X1)
    | sK0(sK8,X1,X2) != k1_funct_1(sK8,X0)
    | k9_relat_1(sK8,X1) = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_476,c_24])).

cnf(c_481,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(sK8))
    | ~ r2_hidden(sK0(sK8,X1,X2),X2)
    | sK0(sK8,X1,X2) != k1_funct_1(sK8,X0)
    | k9_relat_1(sK8,X1) = X2 ),
    inference(renaming,[status(thm)],[c_480])).

cnf(c_1385,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK8,sK7))
    | ~ r2_hidden(X0,k1_relat_1(sK8))
    | ~ r2_hidden(sK0(sK8,k10_relat_1(sK8,sK7),sK7),sK7)
    | sK0(sK8,k10_relat_1(sK8,sK7),sK7) != k1_funct_1(sK8,X0)
    | k9_relat_1(sK8,k10_relat_1(sK8,sK7)) = sK7 ),
    inference(instantiation,[status(thm)],[c_481])).

cnf(c_1783,plain,
    ( ~ r2_hidden(sK0(sK8,k10_relat_1(sK8,sK7),sK7),sK7)
    | ~ r2_hidden(sK6(sK8,sK0(sK8,k10_relat_1(sK8,sK7),sK7)),k10_relat_1(sK8,sK7))
    | ~ r2_hidden(sK6(sK8,sK0(sK8,k10_relat_1(sK8,sK7),sK7)),k1_relat_1(sK8))
    | sK0(sK8,k10_relat_1(sK8,sK7),sK7) != k1_funct_1(sK8,sK6(sK8,sK0(sK8,k10_relat_1(sK8,sK7),sK7)))
    | k9_relat_1(sK8,k10_relat_1(sK8,sK7)) = sK7 ),
    inference(instantiation,[status(thm)],[c_1385])).

cnf(c_1528,plain,
    ( sK7 = sK7 ),
    inference(instantiation,[status(thm)],[c_919])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | k1_funct_1(X1,sK6(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_520,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK6(X1,X0)) = X0
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_23])).

cnf(c_521,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK8))
    | ~ v1_relat_1(sK8)
    | k1_funct_1(sK8,sK6(sK8,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_520])).

cnf(c_525,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK8))
    | k1_funct_1(sK8,sK6(sK8,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_521,c_24])).

cnf(c_1463,plain,
    ( ~ r2_hidden(sK0(sK8,k10_relat_1(sK8,sK7),sK7),k2_relat_1(sK8))
    | k1_funct_1(sK8,sK6(sK8,sK0(sK8,k10_relat_1(sK8,sK7),sK7))) = sK0(sK8,k10_relat_1(sK8,sK7),sK7) ),
    inference(instantiation,[status(thm)],[c_525])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK6(X1,X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_502,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK6(X1,X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_23])).

cnf(c_503,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK8))
    | r2_hidden(sK6(sK8,X0),k1_relat_1(sK8))
    | ~ v1_relat_1(sK8) ),
    inference(unflattening,[status(thm)],[c_502])).

cnf(c_507,plain,
    ( r2_hidden(sK6(sK8,X0),k1_relat_1(sK8))
    | ~ r2_hidden(X0,k2_relat_1(sK8)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_503,c_24])).

cnf(c_508,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK8))
    | r2_hidden(sK6(sK8,X0),k1_relat_1(sK8)) ),
    inference(renaming,[status(thm)],[c_507])).

cnf(c_1464,plain,
    ( ~ r2_hidden(sK0(sK8,k10_relat_1(sK8,sK7),sK7),k2_relat_1(sK8))
    | r2_hidden(sK6(sK8,sK0(sK8,k10_relat_1(sK8,sK7),sK7)),k1_relat_1(sK8)) ),
    inference(instantiation,[status(thm)],[c_508])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(k1_funct_1(X1,X0),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_598,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(k1_funct_1(X1,X0),X2)
    | ~ v1_relat_1(X1)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_23])).

cnf(c_599,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK8,X1))
    | r2_hidden(k1_funct_1(sK8,X0),X1)
    | ~ v1_relat_1(sK8) ),
    inference(unflattening,[status(thm)],[c_598])).

cnf(c_603,plain,
    ( r2_hidden(k1_funct_1(sK8,X0),X1)
    | ~ r2_hidden(X0,k10_relat_1(sK8,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_599,c_24])).

cnf(c_604,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK8,X1))
    | r2_hidden(k1_funct_1(sK8,X0),X1) ),
    inference(renaming,[status(thm)],[c_603])).

cnf(c_1421,plain,
    ( ~ r2_hidden(sK1(sK8,k10_relat_1(sK8,sK7),sK7),k10_relat_1(sK8,sK7))
    | r2_hidden(k1_funct_1(sK8,sK1(sK8,k10_relat_1(sK8,sK7),sK7)),sK7) ),
    inference(instantiation,[status(thm)],[c_604])).

cnf(c_14,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_22,negated_conjecture,
    ( r1_tarski(sK7,k2_relat_1(sK8)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_268,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | k2_relat_1(sK8) != X2
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_22])).

cnf(c_269,plain,
    ( r2_hidden(X0,k2_relat_1(sK8))
    | ~ r2_hidden(X0,sK7) ),
    inference(unflattening,[status(thm)],[c_268])).

cnf(c_1390,plain,
    ( r2_hidden(sK0(sK8,k10_relat_1(sK8,sK7),sK7),k2_relat_1(sK8))
    | ~ r2_hidden(sK0(sK8,k10_relat_1(sK8,sK7),sK7),sK7) ),
    inference(instantiation,[status(thm)],[c_269])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1,X2),X2)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_funct_1(X0,sK1(X0,X1,X2)) = sK0(X0,X1,X2)
    | k9_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_433,plain,
    ( r2_hidden(sK0(X0,X1,X2),X2)
    | ~ v1_relat_1(X0)
    | k1_funct_1(X0,sK1(X0,X1,X2)) = sK0(X0,X1,X2)
    | k9_relat_1(X0,X1) = X2
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_23])).

cnf(c_434,plain,
    ( r2_hidden(sK0(sK8,X0,X1),X1)
    | ~ v1_relat_1(sK8)
    | k1_funct_1(sK8,sK1(sK8,X0,X1)) = sK0(sK8,X0,X1)
    | k9_relat_1(sK8,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_433])).

cnf(c_438,plain,
    ( r2_hidden(sK0(sK8,X0,X1),X1)
    | k1_funct_1(sK8,sK1(sK8,X0,X1)) = sK0(sK8,X0,X1)
    | k9_relat_1(sK8,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_434,c_24])).

cnf(c_1376,plain,
    ( r2_hidden(sK0(sK8,k10_relat_1(sK8,sK7),sK7),sK7)
    | k1_funct_1(sK8,sK1(sK8,k10_relat_1(sK8,sK7),sK7)) = sK0(sK8,k10_relat_1(sK8,sK7),sK7)
    | k9_relat_1(sK8,k10_relat_1(sK8,sK7)) = sK7 ),
    inference(instantiation,[status(thm)],[c_438])).

cnf(c_2,plain,
    ( r2_hidden(sK1(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k9_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_412,plain,
    ( r2_hidden(sK1(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | ~ v1_relat_1(X0)
    | k9_relat_1(X0,X1) = X2
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_23])).

cnf(c_413,plain,
    ( r2_hidden(sK1(sK8,X0,X1),X0)
    | r2_hidden(sK0(sK8,X0,X1),X1)
    | ~ v1_relat_1(sK8)
    | k9_relat_1(sK8,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_412])).

cnf(c_417,plain,
    ( r2_hidden(sK0(sK8,X0,X1),X1)
    | r2_hidden(sK1(sK8,X0,X1),X0)
    | k9_relat_1(sK8,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_413,c_24])).

cnf(c_418,plain,
    ( r2_hidden(sK1(sK8,X0,X1),X0)
    | r2_hidden(sK0(sK8,X0,X1),X1)
    | k9_relat_1(sK8,X0) = X1 ),
    inference(renaming,[status(thm)],[c_417])).

cnf(c_1373,plain,
    ( r2_hidden(sK1(sK8,k10_relat_1(sK8,sK7),sK7),k10_relat_1(sK8,sK7))
    | r2_hidden(sK0(sK8,k10_relat_1(sK8,sK7),sK7),sK7)
    | k9_relat_1(sK8,k10_relat_1(sK8,sK7)) = sK7 ),
    inference(instantiation,[status(thm)],[c_418])).

cnf(c_21,negated_conjecture,
    ( k9_relat_1(sK8,k10_relat_1(sK8,sK7)) != sK7 ),
    inference(cnf_transformation,[],[f60])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_61156,c_26815,c_16343,c_15904,c_3359,c_3027,c_1783,c_1528,c_1463,c_1464,c_1421,c_1390,c_1376,c_1373,c_21])).


%------------------------------------------------------------------------------
