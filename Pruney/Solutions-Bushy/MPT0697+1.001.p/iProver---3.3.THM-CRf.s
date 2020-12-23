%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0697+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:55 EST 2020

% Result     : Theorem 3.60s
% Output     : CNFRefutation 3.60s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 300 expanded)
%              Number of clauses        :   58 (  78 expanded)
%              Number of leaves         :   15 (  68 expanded)
%              Depth                    :   15
%              Number of atoms          :  545 (1579 expanded)
%              Number of equality atoms :  126 ( 259 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
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

fof(f13,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f14,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( X1 != X2
          & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
          & r2_hidden(X2,k1_relat_1(X0))
          & r2_hidden(X1,k1_relat_1(X0)) )
     => ( sK5(X0) != sK6(X0)
        & k1_funct_1(X0,sK5(X0)) = k1_funct_1(X0,sK6(X0))
        & r2_hidden(sK6(X0),k1_relat_1(X0))
        & r2_hidden(sK5(X0),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ( sK5(X0) != sK6(X0)
            & k1_funct_1(X0,sK5(X0)) = k1_funct_1(X0,sK6(X0))
            & r2_hidden(sK6(X0),k1_relat_1(X0))
            & r2_hidden(sK5(X0),k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f31,f32])).

fof(f52,plain,(
    ! [X4,X0,X3] :
      ( X3 = X4
      | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( v2_funct_1(X1)
         => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f34,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
        & v2_funct_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k10_relat_1(sK8,k9_relat_1(sK8,sK7)),sK7)
      & v2_funct_1(sK8)
      & v1_funct_1(sK8)
      & v1_relat_1(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ~ r1_tarski(k10_relat_1(sK8,k9_relat_1(sK8,sK7)),sK7)
    & v2_funct_1(sK8)
    & v1_funct_1(sK8)
    & v1_relat_1(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f16,f34])).

fof(f58,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f35])).

fof(f59,plain,(
    v2_funct_1(sK8) ),
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f38,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_funct_1(X0,sK2(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f63,plain,(
    ! [X6,X0,X1] :
      ( k1_funct_1(X0,sK2(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f38])).

fof(f37,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f64,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X6),X1)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f37])).

fof(f36,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f65,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f36])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f44,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X4,X2)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f68,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X4,k10_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f44])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f12,f28])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK4(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f60,plain,(
    ~ r1_tarski(k10_relat_1(sK8,k9_relat_1(sK8,sK7)),sK7) ),
    inference(cnf_transformation,[],[f35])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_951,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3757,plain,
    ( k1_funct_1(sK8,sK2(sK8,sK7,k1_funct_1(sK8,sK4(k10_relat_1(sK8,k9_relat_1(sK8,sK7)),sK7)))) != X0
    | k1_funct_1(sK8,sK4(k10_relat_1(sK8,k9_relat_1(sK8,sK7)),sK7)) != X0
    | k1_funct_1(sK8,sK4(k10_relat_1(sK8,k9_relat_1(sK8,sK7)),sK7)) = k1_funct_1(sK8,sK2(sK8,sK7,k1_funct_1(sK8,sK4(k10_relat_1(sK8,k9_relat_1(sK8,sK7)),sK7)))) ),
    inference(instantiation,[status(thm)],[c_951])).

cnf(c_8965,plain,
    ( k1_funct_1(sK8,sK2(sK8,sK7,k1_funct_1(sK8,sK4(k10_relat_1(sK8,k9_relat_1(sK8,sK7)),sK7)))) != k1_funct_1(sK8,sK4(k10_relat_1(sK8,k9_relat_1(sK8,sK7)),sK7))
    | k1_funct_1(sK8,sK4(k10_relat_1(sK8,k9_relat_1(sK8,sK7)),sK7)) = k1_funct_1(sK8,sK2(sK8,sK7,k1_funct_1(sK8,sK4(k10_relat_1(sK8,k9_relat_1(sK8,sK7)),sK7))))
    | k1_funct_1(sK8,sK4(k10_relat_1(sK8,k9_relat_1(sK8,sK7)),sK7)) != k1_funct_1(sK8,sK4(k10_relat_1(sK8,k9_relat_1(sK8,sK7)),sK7)) ),
    inference(instantiation,[status(thm)],[c_3757])).

cnf(c_950,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_4652,plain,
    ( k1_funct_1(sK8,sK4(k10_relat_1(sK8,k9_relat_1(sK8,sK7)),sK7)) = k1_funct_1(sK8,sK4(k10_relat_1(sK8,k9_relat_1(sK8,sK7)),sK7)) ),
    inference(instantiation,[status(thm)],[c_950])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | X2 = X0
    | k1_funct_1(X1,X2) != k1_funct_1(X1,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_23,negated_conjecture,
    ( v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_639,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | X2 = X0
    | k1_funct_1(X1,X2) != k1_funct_1(X1,X0)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_23])).

cnf(c_640,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK8))
    | ~ r2_hidden(X1,k1_relat_1(sK8))
    | ~ v2_funct_1(sK8)
    | ~ v1_relat_1(sK8)
    | X0 = X1
    | k1_funct_1(sK8,X0) != k1_funct_1(sK8,X1) ),
    inference(unflattening,[status(thm)],[c_639])).

cnf(c_22,negated_conjecture,
    ( v2_funct_1(sK8) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_398,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | X2 = X0
    | k1_funct_1(X1,X2) != k1_funct_1(X1,X0)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_22])).

cnf(c_399,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK8))
    | ~ r2_hidden(X1,k1_relat_1(sK8))
    | ~ v1_relat_1(sK8)
    | ~ v1_funct_1(sK8)
    | X0 = X1
    | k1_funct_1(sK8,X0) != k1_funct_1(sK8,X1) ),
    inference(unflattening,[status(thm)],[c_398])).

cnf(c_24,negated_conjecture,
    ( v1_relat_1(sK8) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_403,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK8))
    | ~ r2_hidden(X1,k1_relat_1(sK8))
    | X0 = X1
    | k1_funct_1(sK8,X0) != k1_funct_1(sK8,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_399,c_24,c_23])).

cnf(c_642,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK8))
    | ~ r2_hidden(X1,k1_relat_1(sK8))
    | X0 = X1
    | k1_funct_1(sK8,X0) != k1_funct_1(sK8,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_640,c_24,c_23,c_399])).

cnf(c_1694,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK8))
    | ~ r2_hidden(sK2(sK8,sK7,k1_funct_1(sK8,sK4(k10_relat_1(sK8,k9_relat_1(sK8,sK7)),sK7))),k1_relat_1(sK8))
    | X0 = sK2(sK8,sK7,k1_funct_1(sK8,sK4(k10_relat_1(sK8,k9_relat_1(sK8,sK7)),sK7)))
    | k1_funct_1(sK8,X0) != k1_funct_1(sK8,sK2(sK8,sK7,k1_funct_1(sK8,sK4(k10_relat_1(sK8,k9_relat_1(sK8,sK7)),sK7)))) ),
    inference(instantiation,[status(thm)],[c_642])).

cnf(c_2535,plain,
    ( ~ r2_hidden(sK2(sK8,sK7,k1_funct_1(sK8,sK4(k10_relat_1(sK8,k9_relat_1(sK8,sK7)),sK7))),k1_relat_1(sK8))
    | ~ r2_hidden(sK4(k10_relat_1(sK8,k9_relat_1(sK8,sK7)),sK7),k1_relat_1(sK8))
    | sK4(k10_relat_1(sK8,k9_relat_1(sK8,sK7)),sK7) = sK2(sK8,sK7,k1_funct_1(sK8,sK4(k10_relat_1(sK8,k9_relat_1(sK8,sK7)),sK7)))
    | k1_funct_1(sK8,sK4(k10_relat_1(sK8,k9_relat_1(sK8,sK7)),sK7)) != k1_funct_1(sK8,sK2(sK8,sK7,k1_funct_1(sK8,sK4(k10_relat_1(sK8,k9_relat_1(sK8,sK7)),sK7)))) ),
    inference(instantiation,[status(thm)],[c_1694])).

cnf(c_1626,plain,
    ( sK7 = sK7 ),
    inference(instantiation,[status(thm)],[c_950])).

cnf(c_955,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1285,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK4(k10_relat_1(sK8,k9_relat_1(sK8,sK7)),sK7),sK7)
    | sK4(k10_relat_1(sK8,k9_relat_1(sK8,sK7)),sK7) != X0
    | sK7 != X1 ),
    inference(instantiation,[status(thm)],[c_955])).

cnf(c_1400,plain,
    ( ~ r2_hidden(sK2(sK8,sK7,k1_funct_1(sK8,sK4(k10_relat_1(sK8,k9_relat_1(sK8,sK7)),sK7))),sK7)
    | r2_hidden(sK4(k10_relat_1(sK8,k9_relat_1(sK8,sK7)),sK7),sK7)
    | sK4(k10_relat_1(sK8,k9_relat_1(sK8,sK7)),sK7) != sK2(sK8,sK7,k1_funct_1(sK8,sK4(k10_relat_1(sK8,k9_relat_1(sK8,sK7)),sK7)))
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_1285])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | k1_funct_1(X1,sK2(X1,X2,X0)) = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_752,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK2(X1,X2,X0)) = X0
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_23])).

cnf(c_753,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK8,X1))
    | ~ v1_relat_1(sK8)
    | k1_funct_1(sK8,sK2(sK8,X1,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_752])).

cnf(c_757,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK8,X1))
    | k1_funct_1(sK8,sK2(sK8,X1,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_753,c_24])).

cnf(c_1327,plain,
    ( ~ r2_hidden(k1_funct_1(sK8,sK4(k10_relat_1(sK8,k9_relat_1(sK8,sK7)),sK7)),k9_relat_1(sK8,sK7))
    | k1_funct_1(sK8,sK2(sK8,sK7,k1_funct_1(sK8,sK4(k10_relat_1(sK8,k9_relat_1(sK8,sK7)),sK7)))) = k1_funct_1(sK8,sK4(k10_relat_1(sK8,k9_relat_1(sK8,sK7)),sK7)) ),
    inference(instantiation,[status(thm)],[c_757])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK2(X1,X2,X0),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_734,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK2(X1,X2,X0),X2)
    | ~ v1_relat_1(X1)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_23])).

cnf(c_735,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK8,X1))
    | r2_hidden(sK2(sK8,X1,X0),X1)
    | ~ v1_relat_1(sK8) ),
    inference(unflattening,[status(thm)],[c_734])).

cnf(c_739,plain,
    ( r2_hidden(sK2(sK8,X1,X0),X1)
    | ~ r2_hidden(X0,k9_relat_1(sK8,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_735,c_24])).

cnf(c_740,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK8,X1))
    | r2_hidden(sK2(sK8,X1,X0),X1) ),
    inference(renaming,[status(thm)],[c_739])).

cnf(c_1328,plain,
    ( r2_hidden(sK2(sK8,sK7,k1_funct_1(sK8,sK4(k10_relat_1(sK8,k9_relat_1(sK8,sK7)),sK7))),sK7)
    | ~ r2_hidden(k1_funct_1(sK8,sK4(k10_relat_1(sK8,k9_relat_1(sK8,sK7)),sK7)),k9_relat_1(sK8,sK7)) ),
    inference(instantiation,[status(thm)],[c_740])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK2(X1,X2,X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_716,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK2(X1,X2,X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_23])).

cnf(c_717,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK8,X1))
    | r2_hidden(sK2(sK8,X1,X0),k1_relat_1(sK8))
    | ~ v1_relat_1(sK8) ),
    inference(unflattening,[status(thm)],[c_716])).

cnf(c_721,plain,
    ( r2_hidden(sK2(sK8,X1,X0),k1_relat_1(sK8))
    | ~ r2_hidden(X0,k9_relat_1(sK8,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_717,c_24])).

cnf(c_722,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK8,X1))
    | r2_hidden(sK2(sK8,X1,X0),k1_relat_1(sK8)) ),
    inference(renaming,[status(thm)],[c_721])).

cnf(c_1329,plain,
    ( r2_hidden(sK2(sK8,sK7,k1_funct_1(sK8,sK4(k10_relat_1(sK8,k9_relat_1(sK8,sK7)),sK7))),k1_relat_1(sK8))
    | ~ r2_hidden(k1_funct_1(sK8,sK4(k10_relat_1(sK8,k9_relat_1(sK8,sK7)),sK7)),k9_relat_1(sK8,sK7)) ),
    inference(instantiation,[status(thm)],[c_722])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(k1_funct_1(X1,X0),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_677,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(k1_funct_1(X1,X0),X2)
    | ~ v1_relat_1(X1)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_23])).

cnf(c_678,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK8,X1))
    | r2_hidden(k1_funct_1(sK8,X0),X1)
    | ~ v1_relat_1(sK8) ),
    inference(unflattening,[status(thm)],[c_677])).

cnf(c_682,plain,
    ( r2_hidden(k1_funct_1(sK8,X0),X1)
    | ~ r2_hidden(X0,k10_relat_1(sK8,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_678,c_24])).

cnf(c_683,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK8,X1))
    | r2_hidden(k1_funct_1(sK8,X0),X1) ),
    inference(renaming,[status(thm)],[c_682])).

cnf(c_1298,plain,
    ( ~ r2_hidden(sK4(k10_relat_1(sK8,k9_relat_1(sK8,sK7)),sK7),k10_relat_1(sK8,k9_relat_1(sK8,sK7)))
    | r2_hidden(k1_funct_1(sK8,sK4(k10_relat_1(sK8,k9_relat_1(sK8,sK7)),sK7)),k9_relat_1(sK8,sK7)) ),
    inference(instantiation,[status(thm)],[c_683])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_659,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_23])).

cnf(c_660,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK8,X1))
    | r2_hidden(X0,k1_relat_1(sK8))
    | ~ v1_relat_1(sK8) ),
    inference(unflattening,[status(thm)],[c_659])).

cnf(c_664,plain,
    ( r2_hidden(X0,k1_relat_1(sK8))
    | ~ r2_hidden(X0,k10_relat_1(sK8,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_660,c_24])).

cnf(c_665,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK8,X1))
    | r2_hidden(X0,k1_relat_1(sK8)) ),
    inference(renaming,[status(thm)],[c_664])).

cnf(c_1290,plain,
    ( ~ r2_hidden(sK4(k10_relat_1(sK8,k9_relat_1(sK8,sK7)),sK7),k10_relat_1(sK8,k9_relat_1(sK8,sK7)))
    | r2_hidden(sK4(k10_relat_1(sK8,k9_relat_1(sK8,sK7)),sK7),k1_relat_1(sK8)) ),
    inference(instantiation,[status(thm)],[c_665])).

cnf(c_14,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK4(X0,X1),X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_21,negated_conjecture,
    ( ~ r1_tarski(k10_relat_1(sK8,k9_relat_1(sK8,sK7)),sK7) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_279,plain,
    ( ~ r2_hidden(sK4(X0,X1),X1)
    | k10_relat_1(sK8,k9_relat_1(sK8,sK7)) != X0
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_21])).

cnf(c_280,plain,
    ( ~ r2_hidden(sK4(k10_relat_1(sK8,k9_relat_1(sK8,sK7)),sK7),sK7) ),
    inference(unflattening,[status(thm)],[c_279])).

cnf(c_15,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK4(X0,X1),X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_272,plain,
    ( r2_hidden(sK4(X0,X1),X0)
    | k10_relat_1(sK8,k9_relat_1(sK8,sK7)) != X0
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_21])).

cnf(c_273,plain,
    ( r2_hidden(sK4(k10_relat_1(sK8,k9_relat_1(sK8,sK7)),sK7),k10_relat_1(sK8,k9_relat_1(sK8,sK7))) ),
    inference(unflattening,[status(thm)],[c_272])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8965,c_4652,c_2535,c_1626,c_1400,c_1327,c_1328,c_1329,c_1298,c_1290,c_280,c_273])).


%------------------------------------------------------------------------------
