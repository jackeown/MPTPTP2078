%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1032+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:42 EST 2020

% Result     : Theorem 7.50s
% Output     : CNFRefutation 7.50s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 351 expanded)
%              Number of clauses        :   48 ( 105 expanded)
%              Number of leaves         :   14 (  90 expanded)
%              Depth                    :   15
%              Number of atoms          :  467 (1986 expanded)
%              Number of equality atoms :  160 ( 578 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f19])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f20,f21])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k1_funct_2(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r1_tarski(k2_relat_1(X4),X1)
              & k1_relat_1(X4) = X0
              & X3 = X4
              & v1_funct_1(X4)
              & v1_relat_1(X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r1_tarski(k2_relat_1(X4),X1)
              & k1_relat_1(X4) = X0
              & X3 = X4
              & v1_funct_1(X4)
              & v1_relat_1(X4) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_2(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f1,f8])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k1_funct_2(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k1_funct_2(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f67,plain,(
    ! [X0,X1] : sP0(X1,X0,k1_funct_2(X0,X1)) ),
    inference(equality_resolution,[],[f44])).

fof(f12,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ! [X4] :
                  ( ~ r1_tarski(k2_relat_1(X4),X1)
                  | k1_relat_1(X4) != X0
                  | X3 != X4
                  | ~ v1_funct_1(X4)
                  | ~ v1_relat_1(X4) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X4] :
                  ( r1_tarski(k2_relat_1(X4),X1)
                  & k1_relat_1(X4) = X0
                  & X3 = X4
                  & v1_funct_1(X4)
                  & v1_relat_1(X4) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ! [X4] :
                  ( ~ r1_tarski(k2_relat_1(X4),X1)
                  | k1_relat_1(X4) != X0
                  | X3 != X4
                  | ~ v1_funct_1(X4)
                  | ~ v1_relat_1(X4) ) )
            & ( ? [X4] :
                  ( r1_tarski(k2_relat_1(X4),X1)
                  & k1_relat_1(X4) = X0
                  & X3 = X4
                  & v1_funct_1(X4)
                  & v1_relat_1(X4) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ! [X4] :
                  ( ~ r1_tarski(k2_relat_1(X4),X0)
                  | k1_relat_1(X4) != X1
                  | X3 != X4
                  | ~ v1_funct_1(X4)
                  | ~ v1_relat_1(X4) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X5] :
                  ( r1_tarski(k2_relat_1(X5),X0)
                  & k1_relat_1(X5) = X1
                  & X3 = X5
                  & v1_funct_1(X5)
                  & v1_relat_1(X5) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X2)
              | ! [X7] :
                  ( ~ r1_tarski(k2_relat_1(X7),X0)
                  | k1_relat_1(X7) != X1
                  | X6 != X7
                  | ~ v1_funct_1(X7)
                  | ~ v1_relat_1(X7) ) )
            & ( ? [X8] :
                  ( r1_tarski(k2_relat_1(X8),X0)
                  & k1_relat_1(X8) = X1
                  & X6 = X8
                  & v1_funct_1(X8)
                  & v1_relat_1(X8) )
              | ~ r2_hidden(X6,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f12])).

fof(f16,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r1_tarski(k2_relat_1(X8),X0)
          & k1_relat_1(X8) = X1
          & X6 = X8
          & v1_funct_1(X8)
          & v1_relat_1(X8) )
     => ( r1_tarski(k2_relat_1(sK4(X0,X1,X6)),X0)
        & k1_relat_1(sK4(X0,X1,X6)) = X1
        & sK4(X0,X1,X6) = X6
        & v1_funct_1(sK4(X0,X1,X6))
        & v1_relat_1(sK4(X0,X1,X6)) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r1_tarski(k2_relat_1(X5),X0)
          & k1_relat_1(X5) = X1
          & X3 = X5
          & v1_funct_1(X5)
          & v1_relat_1(X5) )
     => ( r1_tarski(k2_relat_1(sK3(X0,X1,X2)),X0)
        & k1_relat_1(sK3(X0,X1,X2)) = X1
        & sK3(X0,X1,X2) = X3
        & v1_funct_1(sK3(X0,X1,X2))
        & v1_relat_1(sK3(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r1_tarski(k2_relat_1(X4),X0)
                | k1_relat_1(X4) != X1
                | X3 != X4
                | ~ v1_funct_1(X4)
                | ~ v1_relat_1(X4) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r1_tarski(k2_relat_1(X5),X0)
                & k1_relat_1(X5) = X1
                & X3 = X5
                & v1_funct_1(X5)
                & v1_relat_1(X5) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( ~ r1_tarski(k2_relat_1(X4),X0)
              | k1_relat_1(X4) != X1
              | sK2(X0,X1,X2) != X4
              | ~ v1_funct_1(X4)
              | ~ v1_relat_1(X4) )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r1_tarski(k2_relat_1(X5),X0)
              & k1_relat_1(X5) = X1
              & sK2(X0,X1,X2) = X5
              & v1_funct_1(X5)
              & v1_relat_1(X5) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ! [X4] :
                ( ~ r1_tarski(k2_relat_1(X4),X0)
                | k1_relat_1(X4) != X1
                | sK2(X0,X1,X2) != X4
                | ~ v1_funct_1(X4)
                | ~ v1_relat_1(X4) )
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( r1_tarski(k2_relat_1(sK3(X0,X1,X2)),X0)
              & k1_relat_1(sK3(X0,X1,X2)) = X1
              & sK2(X0,X1,X2) = sK3(X0,X1,X2)
              & v1_funct_1(sK3(X0,X1,X2))
              & v1_relat_1(sK3(X0,X1,X2)) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X2)
              | ! [X7] :
                  ( ~ r1_tarski(k2_relat_1(X7),X0)
                  | k1_relat_1(X7) != X1
                  | X6 != X7
                  | ~ v1_funct_1(X7)
                  | ~ v1_relat_1(X7) ) )
            & ( ( r1_tarski(k2_relat_1(sK4(X0,X1,X6)),X0)
                & k1_relat_1(sK4(X0,X1,X6)) = X1
                & sK4(X0,X1,X6) = X6
                & v1_funct_1(sK4(X0,X1,X6))
                & v1_relat_1(sK4(X0,X1,X6)) )
              | ~ r2_hidden(X6,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f13,f16,f15,f14])).

fof(f34,plain,(
    ! [X6,X2,X0,X1] :
      ( sK4(X0,X1,X6) = X6
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,conjecture,(
    ! [X0,X1] : r1_tarski(k1_funct_2(X0,X1),k4_partfun1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] : r1_tarski(k1_funct_2(X0,X1),k4_partfun1(X0,X1)) ),
    inference(negated_conjecture,[],[f4])).

fof(f7,plain,(
    ? [X0,X1] : ~ r1_tarski(k1_funct_2(X0,X1),k4_partfun1(X0,X1)) ),
    inference(ennf_transformation,[],[f5])).

fof(f30,plain,
    ( ? [X0,X1] : ~ r1_tarski(k1_funct_2(X0,X1),k4_partfun1(X0,X1))
   => ~ r1_tarski(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ~ r1_tarski(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10])],[f7,f30])).

fof(f63,plain,(
    ~ r1_tarski(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)) ),
    inference(cnf_transformation,[],[f31])).

fof(f36,plain,(
    ! [X6,X2,X0,X1] :
      ( r1_tarski(k2_relat_1(sK4(X0,X1,X6)),X0)
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_partfun1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r1_tarski(k2_relat_1(X4),X1)
              & r1_tarski(k1_relat_1(X4),X0)
              & X3 = X4
              & v1_funct_1(X4)
              & v1_relat_1(X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X1,X0,X2] :
      ( sP1(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r1_tarski(k2_relat_1(X4),X1)
              & r1_tarski(k1_relat_1(X4),X0)
              & X3 = X4
              & v1_funct_1(X4)
              & v1_relat_1(X4) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( k4_partfun1(X0,X1) = X2
    <=> sP1(X1,X0,X2) ) ),
    inference(definition_folding,[],[f3,f10])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k4_partfun1(X0,X1) = X2
        | ~ sP1(X1,X0,X2) )
      & ( sP1(X1,X0,X2)
        | k4_partfun1(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( sP1(X1,X0,X2)
      | k4_partfun1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f70,plain,(
    ! [X0,X1] : sP1(X1,X0,k4_partfun1(X0,X1)) ),
    inference(equality_resolution,[],[f61])).

fof(f23,plain,(
    ! [X1,X0,X2] :
      ( ( sP1(X1,X0,X2)
        | ? [X3] :
            ( ( ! [X4] :
                  ( ~ r1_tarski(k2_relat_1(X4),X1)
                  | ~ r1_tarski(k1_relat_1(X4),X0)
                  | X3 != X4
                  | ~ v1_funct_1(X4)
                  | ~ v1_relat_1(X4) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X4] :
                  ( r1_tarski(k2_relat_1(X4),X1)
                  & r1_tarski(k1_relat_1(X4),X0)
                  & X3 = X4
                  & v1_funct_1(X4)
                  & v1_relat_1(X4) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ! [X4] :
                  ( ~ r1_tarski(k2_relat_1(X4),X1)
                  | ~ r1_tarski(k1_relat_1(X4),X0)
                  | X3 != X4
                  | ~ v1_funct_1(X4)
                  | ~ v1_relat_1(X4) ) )
            & ( ? [X4] :
                  ( r1_tarski(k2_relat_1(X4),X1)
                  & r1_tarski(k1_relat_1(X4),X0)
                  & X3 = X4
                  & v1_funct_1(X4)
                  & v1_relat_1(X4) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP1(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ! [X4] :
                  ( ~ r1_tarski(k2_relat_1(X4),X0)
                  | ~ r1_tarski(k1_relat_1(X4),X1)
                  | X3 != X4
                  | ~ v1_funct_1(X4)
                  | ~ v1_relat_1(X4) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X5] :
                  ( r1_tarski(k2_relat_1(X5),X0)
                  & r1_tarski(k1_relat_1(X5),X1)
                  & X3 = X5
                  & v1_funct_1(X5)
                  & v1_relat_1(X5) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X2)
              | ! [X7] :
                  ( ~ r1_tarski(k2_relat_1(X7),X0)
                  | ~ r1_tarski(k1_relat_1(X7),X1)
                  | X6 != X7
                  | ~ v1_funct_1(X7)
                  | ~ v1_relat_1(X7) ) )
            & ( ? [X8] :
                  ( r1_tarski(k2_relat_1(X8),X0)
                  & r1_tarski(k1_relat_1(X8),X1)
                  & X6 = X8
                  & v1_funct_1(X8)
                  & v1_relat_1(X8) )
              | ~ r2_hidden(X6,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f23])).

fof(f27,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r1_tarski(k2_relat_1(X8),X0)
          & r1_tarski(k1_relat_1(X8),X1)
          & X6 = X8
          & v1_funct_1(X8)
          & v1_relat_1(X8) )
     => ( r1_tarski(k2_relat_1(sK8(X0,X1,X6)),X0)
        & r1_tarski(k1_relat_1(sK8(X0,X1,X6)),X1)
        & sK8(X0,X1,X6) = X6
        & v1_funct_1(sK8(X0,X1,X6))
        & v1_relat_1(sK8(X0,X1,X6)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r1_tarski(k2_relat_1(X5),X0)
          & r1_tarski(k1_relat_1(X5),X1)
          & X3 = X5
          & v1_funct_1(X5)
          & v1_relat_1(X5) )
     => ( r1_tarski(k2_relat_1(sK7(X0,X1,X2)),X0)
        & r1_tarski(k1_relat_1(sK7(X0,X1,X2)),X1)
        & sK7(X0,X1,X2) = X3
        & v1_funct_1(sK7(X0,X1,X2))
        & v1_relat_1(sK7(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r1_tarski(k2_relat_1(X4),X0)
                | ~ r1_tarski(k1_relat_1(X4),X1)
                | X3 != X4
                | ~ v1_funct_1(X4)
                | ~ v1_relat_1(X4) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r1_tarski(k2_relat_1(X5),X0)
                & r1_tarski(k1_relat_1(X5),X1)
                & X3 = X5
                & v1_funct_1(X5)
                & v1_relat_1(X5) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( ~ r1_tarski(k2_relat_1(X4),X0)
              | ~ r1_tarski(k1_relat_1(X4),X1)
              | sK6(X0,X1,X2) != X4
              | ~ v1_funct_1(X4)
              | ~ v1_relat_1(X4) )
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r1_tarski(k2_relat_1(X5),X0)
              & r1_tarski(k1_relat_1(X5),X1)
              & sK6(X0,X1,X2) = X5
              & v1_funct_1(X5)
              & v1_relat_1(X5) )
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ( ! [X4] :
                ( ~ r1_tarski(k2_relat_1(X4),X0)
                | ~ r1_tarski(k1_relat_1(X4),X1)
                | sK6(X0,X1,X2) != X4
                | ~ v1_funct_1(X4)
                | ~ v1_relat_1(X4) )
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( ( r1_tarski(k2_relat_1(sK7(X0,X1,X2)),X0)
              & r1_tarski(k1_relat_1(sK7(X0,X1,X2)),X1)
              & sK6(X0,X1,X2) = sK7(X0,X1,X2)
              & v1_funct_1(sK7(X0,X1,X2))
              & v1_relat_1(sK7(X0,X1,X2)) )
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X2)
              | ! [X7] :
                  ( ~ r1_tarski(k2_relat_1(X7),X0)
                  | ~ r1_tarski(k1_relat_1(X7),X1)
                  | X6 != X7
                  | ~ v1_funct_1(X7)
                  | ~ v1_relat_1(X7) ) )
            & ( ( r1_tarski(k2_relat_1(sK8(X0,X1,X6)),X0)
                & r1_tarski(k1_relat_1(sK8(X0,X1,X6)),X1)
                & sK8(X0,X1,X6) = X6
                & v1_funct_1(sK8(X0,X1,X6))
                & v1_relat_1(sK8(X0,X1,X6)) )
              | ~ r2_hidden(X6,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f24,f27,f26,f25])).

fof(f54,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r1_tarski(k2_relat_1(X7),X0)
      | ~ r1_tarski(k1_relat_1(X7),X1)
      | X6 != X7
      | ~ v1_funct_1(X7)
      | ~ v1_relat_1(X7)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f69,plain,(
    ! [X2,X0,X7,X1] :
      ( r2_hidden(X7,X2)
      | ~ r1_tarski(k2_relat_1(X7),X0)
      | ~ r1_tarski(k1_relat_1(X7),X1)
      | ~ v1_funct_1(X7)
      | ~ v1_relat_1(X7)
      | ~ sP1(X0,X1,X2) ) ),
    inference(equality_resolution,[],[f54])).

fof(f35,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_relat_1(sK4(X0,X1,X6)) = X1
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f33,plain,(
    ! [X6,X2,X0,X1] :
      ( v1_funct_1(sK4(X0,X1,X6))
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f32,plain,(
    ! [X6,X2,X0,X1] :
      ( v1_relat_1(sK4(X0,X1,X6))
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_15,plain,
    ( r2_hidden(sK5(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_4183,plain,
    ( r2_hidden(sK5(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_14,plain,
    ( ~ r2_hidden(sK5(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_4184,plain,
    ( r2_hidden(sK5(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_4674,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4183,c_4184])).

cnf(c_13,plain,
    ( sP0(X0,X1,k1_funct_2(X1,X0)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_4185,plain,
    ( sP0(X0,X1,k1_funct_2(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_9,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,X2)
    | sK4(X0,X1,X3) = X3 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_4189,plain,
    ( sK4(X0,X1,X2) = X2
    | sP0(X0,X1,X3) != iProver_top
    | r2_hidden(X2,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4730,plain,
    ( sK4(X0,X1,X2) = X2
    | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4185,c_4189])).

cnf(c_4739,plain,
    ( sK4(X0,X1,sK5(k1_funct_2(X1,X0),X2)) = sK5(k1_funct_2(X1,X0),X2)
    | r1_tarski(k1_funct_2(X1,X0),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4183,c_4730])).

cnf(c_31,negated_conjecture,
    ( ~ r1_tarski(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_4167,plain,
    ( r1_tarski(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_9132,plain,
    ( sK4(sK10,sK9,sK5(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10))) = sK5(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)) ),
    inference(superposition,[status(thm)],[c_4739,c_4167])).

cnf(c_7,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,X2)
    | r1_tarski(k2_relat_1(sK4(X0,X1,X3)),X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_4191,plain,
    ( sP0(X0,X1,X2) != iProver_top
    | r2_hidden(X3,X2) != iProver_top
    | r1_tarski(k2_relat_1(sK4(X0,X1,X3)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_5737,plain,
    ( r2_hidden(X0,k1_funct_2(X1,X2)) != iProver_top
    | r1_tarski(k2_relat_1(sK4(X2,X1,X0)),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4185,c_4191])).

cnf(c_9221,plain,
    ( r2_hidden(sK5(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)),k1_funct_2(sK9,sK10)) != iProver_top
    | r1_tarski(k2_relat_1(sK5(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10))),sK10) = iProver_top ),
    inference(superposition,[status(thm)],[c_9132,c_5737])).

cnf(c_32,plain,
    ( r1_tarski(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_4232,plain,
    ( r2_hidden(sK5(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)),k1_funct_2(sK9,sK10))
    | r1_tarski(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_4233,plain,
    ( r2_hidden(sK5(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)),k1_funct_2(sK9,sK10)) = iProver_top
    | r1_tarski(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4232])).

cnf(c_9601,plain,
    ( r1_tarski(k2_relat_1(sK5(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10))),sK10) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9221,c_32,c_4233])).

cnf(c_30,plain,
    ( sP1(X0,X1,k4_partfun1(X1,X0)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_4168,plain,
    ( sP1(X0,X1,k4_partfun1(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_23,plain,
    ( ~ sP1(X0,X1,X2)
    | r2_hidden(X3,X2)
    | ~ r1_tarski(k2_relat_1(X3),X0)
    | ~ r1_tarski(k1_relat_1(X3),X1)
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_4175,plain,
    ( sP1(X0,X1,X2) != iProver_top
    | r2_hidden(X3,X2) = iProver_top
    | r1_tarski(k2_relat_1(X3),X0) != iProver_top
    | r1_tarski(k1_relat_1(X3),X1) != iProver_top
    | v1_relat_1(X3) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_6053,plain,
    ( r2_hidden(X0,k4_partfun1(X1,X2)) = iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4168,c_4175])).

cnf(c_6596,plain,
    ( r1_tarski(X0,k4_partfun1(X1,X2)) = iProver_top
    | r1_tarski(k2_relat_1(sK5(X0,k4_partfun1(X1,X2))),X2) != iProver_top
    | r1_tarski(k1_relat_1(sK5(X0,k4_partfun1(X1,X2))),X1) != iProver_top
    | v1_relat_1(sK5(X0,k4_partfun1(X1,X2))) != iProver_top
    | v1_funct_1(sK5(X0,k4_partfun1(X1,X2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6053,c_4184])).

cnf(c_27400,plain,
    ( r1_tarski(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)) = iProver_top
    | r1_tarski(k1_relat_1(sK5(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10))),sK9) != iProver_top
    | v1_relat_1(sK5(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10))) != iProver_top
    | v1_funct_1(sK5(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10))) != iProver_top ),
    inference(superposition,[status(thm)],[c_9601,c_6596])).

cnf(c_8,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,X2)
    | k1_relat_1(sK4(X0,X1,X3)) = X1 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_4190,plain,
    ( k1_relat_1(sK4(X0,X1,X2)) = X1
    | sP0(X0,X1,X3) != iProver_top
    | r2_hidden(X2,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_5306,plain,
    ( k1_relat_1(sK4(X0,X1,X2)) = X1
    | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4185,c_4190])).

cnf(c_5524,plain,
    ( k1_relat_1(sK4(X0,X1,sK5(k1_funct_2(X1,X0),X2))) = X1
    | r1_tarski(k1_funct_2(X1,X0),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4183,c_5306])).

cnf(c_8574,plain,
    ( k1_relat_1(sK4(sK10,sK9,sK5(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)))) = sK9 ),
    inference(superposition,[status(thm)],[c_5524,c_4167])).

cnf(c_9199,plain,
    ( k1_relat_1(sK5(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10))) = sK9 ),
    inference(demodulation,[status(thm)],[c_9132,c_8574])).

cnf(c_27401,plain,
    ( r1_tarski(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)) = iProver_top
    | r1_tarski(sK9,sK9) != iProver_top
    | v1_relat_1(sK5(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10))) != iProver_top
    | v1_funct_1(sK5(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_27400,c_9199])).

cnf(c_10,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,X2)
    | v1_funct_1(sK4(X0,X1,X3)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_4188,plain,
    ( sP0(X0,X1,X2) != iProver_top
    | r2_hidden(X3,X2) != iProver_top
    | v1_funct_1(sK4(X0,X1,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_5189,plain,
    ( r2_hidden(X0,k1_funct_2(X1,X2)) != iProver_top
    | v1_funct_1(sK4(X2,X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4185,c_4188])).

cnf(c_5433,plain,
    ( r1_tarski(k1_funct_2(X0,X1),X2) = iProver_top
    | v1_funct_1(sK4(X1,X0,sK5(k1_funct_2(X0,X1),X2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4183,c_5189])).

cnf(c_9222,plain,
    ( r1_tarski(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)) = iProver_top
    | v1_funct_1(sK5(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10))) = iProver_top ),
    inference(superposition,[status(thm)],[c_9132,c_5433])).

cnf(c_11,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,X2)
    | v1_relat_1(sK4(X0,X1,X3)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_4187,plain,
    ( sP0(X0,X1,X2) != iProver_top
    | r2_hidden(X3,X2) != iProver_top
    | v1_relat_1(sK4(X0,X1,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_5186,plain,
    ( r2_hidden(X0,k1_funct_2(X1,X2)) != iProver_top
    | v1_relat_1(sK4(X2,X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4185,c_4187])).

cnf(c_5424,plain,
    ( r1_tarski(k1_funct_2(X0,X1),X2) = iProver_top
    | v1_relat_1(sK4(X1,X0,sK5(k1_funct_2(X0,X1),X2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4183,c_5186])).

cnf(c_9223,plain,
    ( r1_tarski(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)) = iProver_top
    | v1_relat_1(sK5(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10))) = iProver_top ),
    inference(superposition,[status(thm)],[c_9132,c_5424])).

cnf(c_28205,plain,
    ( r1_tarski(sK9,sK9) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_27401,c_32,c_9222,c_9223])).

cnf(c_28209,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_4674,c_28205])).


%------------------------------------------------------------------------------
