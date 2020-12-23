%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:08:28 EST 2020

% Result     : Theorem 3.84s
% Output     : CNFRefutation 3.84s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 897 expanded)
%              Number of clauses        :   75 ( 276 expanded)
%              Number of leaves         :   15 ( 232 expanded)
%              Depth                    :   23
%              Number of atoms          :  564 (5378 expanded)
%              Number of equality atoms :  220 (1601 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
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

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k4_partfun1(X0,X1) = X2
    <=> sP1(X1,X0,X2) ) ),
    inference(definition_folding,[],[f4,f11])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( k4_partfun1(X0,X1) = X2
        | ~ sP1(X1,X0,X2) )
      & ( sP1(X1,X0,X2)
        | k4_partfun1(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( sP1(X1,X0,X2)
      | k4_partfun1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f78,plain,(
    ! [X0,X1] : sP1(X1,X0,k4_partfun1(X0,X1)) ),
    inference(equality_resolution,[],[f67])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f27,plain,(
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
    inference(rectify,[],[f26])).

fof(f30,plain,(
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

fof(f29,plain,(
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

fof(f28,plain,(
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

fof(f31,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f27,f30,f29,f28])).

fof(f60,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r1_tarski(k2_relat_1(X7),X0)
      | ~ r1_tarski(k1_relat_1(X7),X1)
      | X6 != X7
      | ~ v1_funct_1(X7)
      | ~ v1_relat_1(X7)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f77,plain,(
    ! [X2,X0,X7,X1] :
      ( r2_hidden(X7,X2)
      | ~ r1_tarski(k2_relat_1(X7),X0)
      | ~ r1_tarski(k1_relat_1(X7),X1)
      | ~ v1_funct_1(X7)
      | ~ v1_relat_1(X7)
      | ~ sP1(X0,X1,X2) ) ),
    inference(equality_resolution,[],[f60])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f17])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f71,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f38])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f13])).

fof(f15,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f14,f15])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f3,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
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

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_2(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f3,f9])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k1_funct_2(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k1_funct_2(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f75,plain,(
    ! [X0,X1] : sP0(X1,X0,k1_funct_2(X0,X1)) ),
    inference(equality_resolution,[],[f53])).

fof(f19,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f20,plain,(
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
    inference(rectify,[],[f19])).

fof(f23,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r1_tarski(k2_relat_1(X8),X0)
          & k1_relat_1(X8) = X1
          & X6 = X8
          & v1_funct_1(X8)
          & v1_relat_1(X8) )
     => ( r1_tarski(k2_relat_1(sK5(X0,X1,X6)),X0)
        & k1_relat_1(sK5(X0,X1,X6)) = X1
        & sK5(X0,X1,X6) = X6
        & v1_funct_1(sK5(X0,X1,X6))
        & v1_relat_1(sK5(X0,X1,X6)) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r1_tarski(k2_relat_1(X5),X0)
          & k1_relat_1(X5) = X1
          & X3 = X5
          & v1_funct_1(X5)
          & v1_relat_1(X5) )
     => ( r1_tarski(k2_relat_1(sK4(X0,X1,X2)),X0)
        & k1_relat_1(sK4(X0,X1,X2)) = X1
        & sK4(X0,X1,X2) = X3
        & v1_funct_1(sK4(X0,X1,X2))
        & v1_relat_1(sK4(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
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
              | sK3(X0,X1,X2) != X4
              | ~ v1_funct_1(X4)
              | ~ v1_relat_1(X4) )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r1_tarski(k2_relat_1(X5),X0)
              & k1_relat_1(X5) = X1
              & sK3(X0,X1,X2) = X5
              & v1_funct_1(X5)
              & v1_relat_1(X5) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ! [X4] :
                ( ~ r1_tarski(k2_relat_1(X4),X0)
                | k1_relat_1(X4) != X1
                | sK3(X0,X1,X2) != X4
                | ~ v1_funct_1(X4)
                | ~ v1_relat_1(X4) )
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( r1_tarski(k2_relat_1(sK4(X0,X1,X2)),X0)
              & k1_relat_1(sK4(X0,X1,X2)) = X1
              & sK3(X0,X1,X2) = sK4(X0,X1,X2)
              & v1_funct_1(sK4(X0,X1,X2))
              & v1_relat_1(sK4(X0,X1,X2)) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X2)
              | ! [X7] :
                  ( ~ r1_tarski(k2_relat_1(X7),X0)
                  | k1_relat_1(X7) != X1
                  | X6 != X7
                  | ~ v1_funct_1(X7)
                  | ~ v1_relat_1(X7) ) )
            & ( ( r1_tarski(k2_relat_1(sK5(X0,X1,X6)),X0)
                & k1_relat_1(sK5(X0,X1,X6)) = X1
                & sK5(X0,X1,X6) = X6
                & v1_funct_1(sK5(X0,X1,X6))
                & v1_relat_1(sK5(X0,X1,X6)) )
              | ~ r2_hidden(X6,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f20,f23,f22,f21])).

fof(f43,plain,(
    ! [X6,X2,X0,X1] :
      ( sK5(X0,X1,X6) = X6
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f5,conjecture,(
    ! [X0,X1] : r1_tarski(k1_funct_2(X0,X1),k4_partfun1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] : r1_tarski(k1_funct_2(X0,X1),k4_partfun1(X0,X1)) ),
    inference(negated_conjecture,[],[f5])).

fof(f8,plain,(
    ? [X0,X1] : ~ r1_tarski(k1_funct_2(X0,X1),k4_partfun1(X0,X1)) ),
    inference(ennf_transformation,[],[f6])).

fof(f33,plain,
    ( ? [X0,X1] : ~ r1_tarski(k1_funct_2(X0,X1),k4_partfun1(X0,X1))
   => ~ r1_tarski(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ~ r1_tarski(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10])],[f8,f33])).

fof(f69,plain,(
    ~ r1_tarski(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)) ),
    inference(cnf_transformation,[],[f34])).

fof(f44,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_relat_1(sK5(X0,X1,X6)) = X1
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f45,plain,(
    ! [X6,X2,X0,X1] :
      ( r1_tarski(k2_relat_1(sK5(X0,X1,X6)),X0)
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f57,plain,(
    ! [X6,X2,X0,X1] :
      ( sK8(X0,X1,X6) = X6
      | ~ r2_hidden(X6,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f41,plain,(
    ! [X6,X2,X0,X1] :
      ( v1_relat_1(sK5(X0,X1,X6))
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f42,plain,(
    ! [X6,X2,X0,X1] :
      ( v1_funct_1(sK5(X0,X1,X6))
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f59,plain,(
    ! [X6,X2,X0,X1] :
      ( r1_tarski(k2_relat_1(sK8(X0,X1,X6)),X0)
      | ~ r2_hidden(X6,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f40,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_33,plain,
    ( sP1(X0,X1,k4_partfun1(X1,X0)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_7458,plain,
    ( sP1(X0,X1,k4_partfun1(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_26,plain,
    ( ~ sP1(X0,X1,X2)
    | r2_hidden(X3,X2)
    | ~ r1_tarski(k2_relat_1(X3),X0)
    | ~ r1_tarski(k1_relat_1(X3),X1)
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_7465,plain,
    ( sP1(X0,X1,X2) != iProver_top
    | r2_hidden(X3,X2) = iProver_top
    | r1_tarski(k2_relat_1(X3),X0) != iProver_top
    | r1_tarski(k1_relat_1(X3),X1) != iProver_top
    | v1_relat_1(X3) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_9230,plain,
    ( r2_hidden(X0,k4_partfun1(X1,X2)) = iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7458,c_7465])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_7486,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1,plain,
    ( r2_hidden(sK2(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_7489,plain,
    ( r2_hidden(sK2(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_19,plain,
    ( sP0(X0,X1,k1_funct_2(X1,X0)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_7472,plain,
    ( sP0(X0,X1,k1_funct_2(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_15,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,X2)
    | sK5(X0,X1,X3) = X3 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_7476,plain,
    ( sK5(X0,X1,X2) = X2
    | sP0(X0,X1,X3) != iProver_top
    | r2_hidden(X2,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_8142,plain,
    ( sK5(X0,X1,X2) = X2
    | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7472,c_7476])).

cnf(c_8145,plain,
    ( sK5(X0,X1,sK2(k1_funct_2(X1,X0),X2)) = sK2(k1_funct_2(X1,X0),X2)
    | r1_tarski(k1_funct_2(X1,X0),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_7489,c_8142])).

cnf(c_34,negated_conjecture,
    ( ~ r1_tarski(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_7457,plain,
    ( r1_tarski(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_12643,plain,
    ( sK5(sK10,sK9,sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10))) = sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)) ),
    inference(superposition,[status(thm)],[c_8145,c_7457])).

cnf(c_14,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,X2)
    | k1_relat_1(sK5(X0,X1,X3)) = X1 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_7477,plain,
    ( k1_relat_1(sK5(X0,X1,X2)) = X1
    | sP0(X0,X1,X3) != iProver_top
    | r2_hidden(X2,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_8697,plain,
    ( k1_relat_1(sK5(X0,X1,X2)) = X1
    | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7472,c_7477])).

cnf(c_8940,plain,
    ( k1_relat_1(sK5(X0,X1,sK2(k1_funct_2(X1,X0),X2))) = X1
    | r1_tarski(k1_funct_2(X1,X0),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_7489,c_8697])).

cnf(c_11904,plain,
    ( k1_relat_1(sK5(sK10,sK9,sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)))) = sK9 ),
    inference(superposition,[status(thm)],[c_8940,c_7457])).

cnf(c_13,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,X2)
    | r1_tarski(k2_relat_1(sK5(X0,X1,X3)),X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_7478,plain,
    ( sP0(X0,X1,X2) != iProver_top
    | r2_hidden(X3,X2) != iProver_top
    | r1_tarski(k2_relat_1(sK5(X0,X1,X3)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_9063,plain,
    ( r2_hidden(X0,k1_funct_2(X1,X2)) != iProver_top
    | r1_tarski(k2_relat_1(sK5(X2,X1,X0)),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_7472,c_7478])).

cnf(c_29,plain,
    ( ~ sP1(X0,X1,X2)
    | ~ r2_hidden(X3,X2)
    | sK8(X0,X1,X3) = X3 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_7462,plain,
    ( sK8(X0,X1,X2) = X2
    | sP1(X0,X1,X3) != iProver_top
    | r2_hidden(X2,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_8094,plain,
    ( sK8(X0,X1,X2) = X2
    | r2_hidden(X2,k4_partfun1(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7458,c_7462])).

cnf(c_10563,plain,
    ( sK8(X0,X1,X2) = X2
    | r1_tarski(k2_relat_1(X2),X0) != iProver_top
    | r1_tarski(k1_relat_1(X2),X1) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_9230,c_8094])).

cnf(c_10613,plain,
    ( sK8(X0,X1,sK5(X0,X2,X3)) = sK5(X0,X2,X3)
    | r2_hidden(X3,k1_funct_2(X2,X0)) != iProver_top
    | r1_tarski(k1_relat_1(sK5(X0,X2,X3)),X1) != iProver_top
    | v1_relat_1(sK5(X0,X2,X3)) != iProver_top
    | v1_funct_1(sK5(X0,X2,X3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9063,c_10563])).

cnf(c_11983,plain,
    ( sK8(sK10,X0,sK5(sK10,sK9,sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)))) = sK5(sK10,sK9,sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)))
    | r2_hidden(sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)),k1_funct_2(sK9,sK10)) != iProver_top
    | r1_tarski(sK9,X0) != iProver_top
    | v1_relat_1(sK5(sK10,sK9,sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)))) != iProver_top
    | v1_funct_1(sK5(sK10,sK9,sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_11904,c_10613])).

cnf(c_35,plain,
    ( r1_tarski(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_7526,plain,
    ( r2_hidden(sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)),k1_funct_2(sK9,sK10))
    | r1_tarski(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_7527,plain,
    ( r2_hidden(sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)),k1_funct_2(sK9,sK10)) = iProver_top
    | r1_tarski(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7526])).

cnf(c_17,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,X2)
    | v1_relat_1(sK5(X0,X1,X3)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_8158,plain,
    ( ~ sP0(X0,X1,k1_funct_2(sK9,sK10))
    | ~ r2_hidden(sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)),k1_funct_2(sK9,sK10))
    | v1_relat_1(sK5(X0,X1,sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)))) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_8454,plain,
    ( ~ sP0(sK10,sK9,k1_funct_2(sK9,sK10))
    | ~ r2_hidden(sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)),k1_funct_2(sK9,sK10))
    | v1_relat_1(sK5(sK10,sK9,sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)))) ),
    inference(instantiation,[status(thm)],[c_8158])).

cnf(c_8455,plain,
    ( sP0(sK10,sK9,k1_funct_2(sK9,sK10)) != iProver_top
    | r2_hidden(sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)),k1_funct_2(sK9,sK10)) != iProver_top
    | v1_relat_1(sK5(sK10,sK9,sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8454])).

cnf(c_9350,plain,
    ( sP0(sK10,sK9,k1_funct_2(sK9,sK10)) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_9351,plain,
    ( sP0(sK10,sK9,k1_funct_2(sK9,sK10)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9350])).

cnf(c_12549,plain,
    ( r1_tarski(sK9,X0) != iProver_top
    | sK8(sK10,X0,sK5(sK10,sK9,sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)))) = sK5(sK10,sK9,sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)))
    | v1_funct_1(sK5(sK10,sK9,sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11983,c_35,c_7527,c_8455,c_9351])).

cnf(c_12550,plain,
    ( sK8(sK10,X0,sK5(sK10,sK9,sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)))) = sK5(sK10,sK9,sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)))
    | r1_tarski(sK9,X0) != iProver_top
    | v1_funct_1(sK5(sK10,sK9,sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_12549])).

cnf(c_12821,plain,
    ( sK8(sK10,X0,sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10))) = sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10))
    | r1_tarski(sK9,X0) != iProver_top
    | v1_funct_1(sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_12643,c_12550])).

cnf(c_16,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,X2)
    | v1_funct_1(sK5(X0,X1,X3)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_7475,plain,
    ( sP0(X0,X1,X2) != iProver_top
    | r2_hidden(X3,X2) != iProver_top
    | v1_funct_1(sK5(X0,X1,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_8588,plain,
    ( r2_hidden(X0,k1_funct_2(X1,X2)) != iProver_top
    | v1_funct_1(sK5(X2,X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7472,c_7475])).

cnf(c_8815,plain,
    ( r1_tarski(k1_funct_2(X0,X1),X2) = iProver_top
    | v1_funct_1(sK5(X1,X0,sK2(k1_funct_2(X0,X1),X2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_7489,c_8588])).

cnf(c_12851,plain,
    ( r1_tarski(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)) = iProver_top
    | v1_funct_1(sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10))) = iProver_top ),
    inference(superposition,[status(thm)],[c_12643,c_8815])).

cnf(c_13270,plain,
    ( r1_tarski(sK9,X0) != iProver_top
    | sK8(sK10,X0,sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10))) = sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12821,c_35,c_12851])).

cnf(c_13271,plain,
    ( sK8(sK10,X0,sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10))) = sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10))
    | r1_tarski(sK9,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_13270])).

cnf(c_13276,plain,
    ( sK8(sK10,sK9,sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10))) = sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)) ),
    inference(superposition,[status(thm)],[c_7486,c_13271])).

cnf(c_27,plain,
    ( ~ sP1(X0,X1,X2)
    | ~ r2_hidden(X3,X2)
    | r1_tarski(k2_relat_1(sK8(X0,X1,X3)),X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_7464,plain,
    ( sP1(X0,X1,X2) != iProver_top
    | r2_hidden(X3,X2) != iProver_top
    | r1_tarski(k2_relat_1(sK8(X0,X1,X3)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_8498,plain,
    ( r2_hidden(X0,k4_partfun1(X1,X2)) != iProver_top
    | r1_tarski(k2_relat_1(sK8(X2,X1,X0)),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_7458,c_7464])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_7487,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_8945,plain,
    ( k2_relat_1(sK8(X0,X1,X2)) = X0
    | r2_hidden(X2,k4_partfun1(X1,X0)) != iProver_top
    | r1_tarski(X0,k2_relat_1(sK8(X0,X1,X2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8498,c_7487])).

cnf(c_13662,plain,
    ( k2_relat_1(sK8(sK10,sK9,sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)))) = sK10
    | r2_hidden(sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)),k4_partfun1(sK9,sK10)) != iProver_top
    | r1_tarski(sK10,k2_relat_1(sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_13276,c_8945])).

cnf(c_13670,plain,
    ( k2_relat_1(sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10))) = sK10
    | r2_hidden(sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)),k4_partfun1(sK9,sK10)) != iProver_top
    | r1_tarski(sK10,k2_relat_1(sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13662,c_13276])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK2(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_7525,plain,
    ( ~ r2_hidden(sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)),k4_partfun1(sK9,sK10))
    | r1_tarski(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_7529,plain,
    ( r2_hidden(sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)),k4_partfun1(sK9,sK10)) != iProver_top
    | r1_tarski(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7525])).

cnf(c_18772,plain,
    ( r2_hidden(sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)),k4_partfun1(sK9,sK10)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13670,c_35,c_7529])).

cnf(c_18776,plain,
    ( r1_tarski(k2_relat_1(sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10))),sK10) != iProver_top
    | r1_tarski(k1_relat_1(sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10))),sK9) != iProver_top
    | v1_relat_1(sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10))) != iProver_top
    | v1_funct_1(sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10))) != iProver_top ),
    inference(superposition,[status(thm)],[c_9230,c_18772])).

cnf(c_12827,plain,
    ( k1_relat_1(sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10))) = sK9 ),
    inference(demodulation,[status(thm)],[c_12643,c_11904])).

cnf(c_18780,plain,
    ( r1_tarski(k2_relat_1(sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10))),sK10) != iProver_top
    | r1_tarski(sK9,sK9) != iProver_top
    | v1_relat_1(sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10))) != iProver_top
    | v1_funct_1(sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_18776,c_12827])).

cnf(c_15251,plain,
    ( r1_tarski(sK9,sK9) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_15252,plain,
    ( r1_tarski(sK9,sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15251])).

cnf(c_7474,plain,
    ( sP0(X0,X1,X2) != iProver_top
    | r2_hidden(X3,X2) != iProver_top
    | v1_relat_1(sK5(X0,X1,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_8585,plain,
    ( r2_hidden(X0,k1_funct_2(X1,X2)) != iProver_top
    | v1_relat_1(sK5(X2,X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7472,c_7474])).

cnf(c_8810,plain,
    ( r1_tarski(k1_funct_2(X0,X1),X2) = iProver_top
    | v1_relat_1(sK5(X1,X0,sK2(k1_funct_2(X0,X1),X2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_7489,c_8585])).

cnf(c_12852,plain,
    ( r1_tarski(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)) = iProver_top
    | v1_relat_1(sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10))) = iProver_top ),
    inference(superposition,[status(thm)],[c_12643,c_8810])).

cnf(c_12850,plain,
    ( r2_hidden(sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)),k1_funct_2(sK9,sK10)) != iProver_top
    | r1_tarski(k2_relat_1(sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10))),sK10) = iProver_top ),
    inference(superposition,[status(thm)],[c_12643,c_9063])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_18780,c_15252,c_12852,c_12851,c_12850,c_7527,c_35])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 20:40:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.84/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.84/1.00  
% 3.84/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.84/1.00  
% 3.84/1.00  ------  iProver source info
% 3.84/1.00  
% 3.84/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.84/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.84/1.00  git: non_committed_changes: false
% 3.84/1.00  git: last_make_outside_of_git: false
% 3.84/1.00  
% 3.84/1.00  ------ 
% 3.84/1.00  
% 3.84/1.00  ------ Input Options
% 3.84/1.00  
% 3.84/1.00  --out_options                           all
% 3.84/1.00  --tptp_safe_out                         true
% 3.84/1.00  --problem_path                          ""
% 3.84/1.00  --include_path                          ""
% 3.84/1.00  --clausifier                            res/vclausify_rel
% 3.84/1.00  --clausifier_options                    ""
% 3.84/1.00  --stdin                                 false
% 3.84/1.00  --stats_out                             all
% 3.84/1.00  
% 3.84/1.00  ------ General Options
% 3.84/1.00  
% 3.84/1.00  --fof                                   false
% 3.84/1.00  --time_out_real                         305.
% 3.84/1.00  --time_out_virtual                      -1.
% 3.84/1.00  --symbol_type_check                     false
% 3.84/1.00  --clausify_out                          false
% 3.84/1.00  --sig_cnt_out                           false
% 3.84/1.00  --trig_cnt_out                          false
% 3.84/1.00  --trig_cnt_out_tolerance                1.
% 3.84/1.00  --trig_cnt_out_sk_spl                   false
% 3.84/1.00  --abstr_cl_out                          false
% 3.84/1.00  
% 3.84/1.00  ------ Global Options
% 3.84/1.00  
% 3.84/1.00  --schedule                              default
% 3.84/1.00  --add_important_lit                     false
% 3.84/1.00  --prop_solver_per_cl                    1000
% 3.84/1.00  --min_unsat_core                        false
% 3.84/1.00  --soft_assumptions                      false
% 3.84/1.00  --soft_lemma_size                       3
% 3.84/1.00  --prop_impl_unit_size                   0
% 3.84/1.00  --prop_impl_unit                        []
% 3.84/1.00  --share_sel_clauses                     true
% 3.84/1.00  --reset_solvers                         false
% 3.84/1.00  --bc_imp_inh                            [conj_cone]
% 3.84/1.00  --conj_cone_tolerance                   3.
% 3.84/1.00  --extra_neg_conj                        none
% 3.84/1.00  --large_theory_mode                     true
% 3.84/1.00  --prolific_symb_bound                   200
% 3.84/1.00  --lt_threshold                          2000
% 3.84/1.00  --clause_weak_htbl                      true
% 3.84/1.00  --gc_record_bc_elim                     false
% 3.84/1.00  
% 3.84/1.00  ------ Preprocessing Options
% 3.84/1.00  
% 3.84/1.00  --preprocessing_flag                    true
% 3.84/1.00  --time_out_prep_mult                    0.1
% 3.84/1.00  --splitting_mode                        input
% 3.84/1.00  --splitting_grd                         true
% 3.84/1.00  --splitting_cvd                         false
% 3.84/1.00  --splitting_cvd_svl                     false
% 3.84/1.00  --splitting_nvd                         32
% 3.84/1.00  --sub_typing                            true
% 3.84/1.00  --prep_gs_sim                           true
% 3.84/1.00  --prep_unflatten                        true
% 3.84/1.00  --prep_res_sim                          true
% 3.84/1.00  --prep_upred                            true
% 3.84/1.00  --prep_sem_filter                       exhaustive
% 3.84/1.00  --prep_sem_filter_out                   false
% 3.84/1.00  --pred_elim                             true
% 3.84/1.00  --res_sim_input                         true
% 3.84/1.00  --eq_ax_congr_red                       true
% 3.84/1.00  --pure_diseq_elim                       true
% 3.84/1.00  --brand_transform                       false
% 3.84/1.00  --non_eq_to_eq                          false
% 3.84/1.00  --prep_def_merge                        true
% 3.84/1.00  --prep_def_merge_prop_impl              false
% 3.84/1.00  --prep_def_merge_mbd                    true
% 3.84/1.00  --prep_def_merge_tr_red                 false
% 3.84/1.00  --prep_def_merge_tr_cl                  false
% 3.84/1.00  --smt_preprocessing                     true
% 3.84/1.00  --smt_ac_axioms                         fast
% 3.84/1.00  --preprocessed_out                      false
% 3.84/1.00  --preprocessed_stats                    false
% 3.84/1.00  
% 3.84/1.00  ------ Abstraction refinement Options
% 3.84/1.00  
% 3.84/1.00  --abstr_ref                             []
% 3.84/1.00  --abstr_ref_prep                        false
% 3.84/1.00  --abstr_ref_until_sat                   false
% 3.84/1.00  --abstr_ref_sig_restrict                funpre
% 3.84/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.84/1.00  --abstr_ref_under                       []
% 3.84/1.00  
% 3.84/1.00  ------ SAT Options
% 3.84/1.00  
% 3.84/1.00  --sat_mode                              false
% 3.84/1.00  --sat_fm_restart_options                ""
% 3.84/1.00  --sat_gr_def                            false
% 3.84/1.00  --sat_epr_types                         true
% 3.84/1.00  --sat_non_cyclic_types                  false
% 3.84/1.00  --sat_finite_models                     false
% 3.84/1.00  --sat_fm_lemmas                         false
% 3.84/1.00  --sat_fm_prep                           false
% 3.84/1.00  --sat_fm_uc_incr                        true
% 3.84/1.00  --sat_out_model                         small
% 3.84/1.00  --sat_out_clauses                       false
% 3.84/1.00  
% 3.84/1.00  ------ QBF Options
% 3.84/1.00  
% 3.84/1.00  --qbf_mode                              false
% 3.84/1.00  --qbf_elim_univ                         false
% 3.84/1.00  --qbf_dom_inst                          none
% 3.84/1.00  --qbf_dom_pre_inst                      false
% 3.84/1.00  --qbf_sk_in                             false
% 3.84/1.00  --qbf_pred_elim                         true
% 3.84/1.00  --qbf_split                             512
% 3.84/1.00  
% 3.84/1.00  ------ BMC1 Options
% 3.84/1.00  
% 3.84/1.00  --bmc1_incremental                      false
% 3.84/1.00  --bmc1_axioms                           reachable_all
% 3.84/1.00  --bmc1_min_bound                        0
% 3.84/1.00  --bmc1_max_bound                        -1
% 3.84/1.00  --bmc1_max_bound_default                -1
% 3.84/1.00  --bmc1_symbol_reachability              true
% 3.84/1.00  --bmc1_property_lemmas                  false
% 3.84/1.00  --bmc1_k_induction                      false
% 3.84/1.00  --bmc1_non_equiv_states                 false
% 3.84/1.00  --bmc1_deadlock                         false
% 3.84/1.00  --bmc1_ucm                              false
% 3.84/1.00  --bmc1_add_unsat_core                   none
% 3.84/1.00  --bmc1_unsat_core_children              false
% 3.84/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.84/1.00  --bmc1_out_stat                         full
% 3.84/1.00  --bmc1_ground_init                      false
% 3.84/1.00  --bmc1_pre_inst_next_state              false
% 3.84/1.00  --bmc1_pre_inst_state                   false
% 3.84/1.00  --bmc1_pre_inst_reach_state             false
% 3.84/1.00  --bmc1_out_unsat_core                   false
% 3.84/1.00  --bmc1_aig_witness_out                  false
% 3.84/1.00  --bmc1_verbose                          false
% 3.84/1.00  --bmc1_dump_clauses_tptp                false
% 3.84/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.84/1.00  --bmc1_dump_file                        -
% 3.84/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.84/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.84/1.00  --bmc1_ucm_extend_mode                  1
% 3.84/1.00  --bmc1_ucm_init_mode                    2
% 3.84/1.00  --bmc1_ucm_cone_mode                    none
% 3.84/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.84/1.00  --bmc1_ucm_relax_model                  4
% 3.84/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.84/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.84/1.00  --bmc1_ucm_layered_model                none
% 3.84/1.00  --bmc1_ucm_max_lemma_size               10
% 3.84/1.00  
% 3.84/1.00  ------ AIG Options
% 3.84/1.00  
% 3.84/1.00  --aig_mode                              false
% 3.84/1.00  
% 3.84/1.00  ------ Instantiation Options
% 3.84/1.00  
% 3.84/1.00  --instantiation_flag                    true
% 3.84/1.00  --inst_sos_flag                         true
% 3.84/1.00  --inst_sos_phase                        true
% 3.84/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.84/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.84/1.00  --inst_lit_sel_side                     num_symb
% 3.84/1.00  --inst_solver_per_active                1400
% 3.84/1.00  --inst_solver_calls_frac                1.
% 3.84/1.00  --inst_passive_queue_type               priority_queues
% 3.84/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.84/1.00  --inst_passive_queues_freq              [25;2]
% 3.84/1.00  --inst_dismatching                      true
% 3.84/1.00  --inst_eager_unprocessed_to_passive     true
% 3.84/1.00  --inst_prop_sim_given                   true
% 3.84/1.00  --inst_prop_sim_new                     false
% 3.84/1.00  --inst_subs_new                         false
% 3.84/1.00  --inst_eq_res_simp                      false
% 3.84/1.00  --inst_subs_given                       false
% 3.84/1.00  --inst_orphan_elimination               true
% 3.84/1.00  --inst_learning_loop_flag               true
% 3.84/1.00  --inst_learning_start                   3000
% 3.84/1.00  --inst_learning_factor                  2
% 3.84/1.00  --inst_start_prop_sim_after_learn       3
% 3.84/1.00  --inst_sel_renew                        solver
% 3.84/1.00  --inst_lit_activity_flag                true
% 3.84/1.00  --inst_restr_to_given                   false
% 3.84/1.00  --inst_activity_threshold               500
% 3.84/1.00  --inst_out_proof                        true
% 3.84/1.00  
% 3.84/1.00  ------ Resolution Options
% 3.84/1.00  
% 3.84/1.00  --resolution_flag                       true
% 3.84/1.00  --res_lit_sel                           adaptive
% 3.84/1.00  --res_lit_sel_side                      none
% 3.84/1.00  --res_ordering                          kbo
% 3.84/1.00  --res_to_prop_solver                    active
% 3.84/1.00  --res_prop_simpl_new                    false
% 3.84/1.00  --res_prop_simpl_given                  true
% 3.84/1.00  --res_passive_queue_type                priority_queues
% 3.84/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.84/1.00  --res_passive_queues_freq               [15;5]
% 3.84/1.00  --res_forward_subs                      full
% 3.84/1.00  --res_backward_subs                     full
% 3.84/1.00  --res_forward_subs_resolution           true
% 3.84/1.00  --res_backward_subs_resolution          true
% 3.84/1.00  --res_orphan_elimination                true
% 3.84/1.00  --res_time_limit                        2.
% 3.84/1.00  --res_out_proof                         true
% 3.84/1.00  
% 3.84/1.00  ------ Superposition Options
% 3.84/1.00  
% 3.84/1.00  --superposition_flag                    true
% 3.84/1.00  --sup_passive_queue_type                priority_queues
% 3.84/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.84/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.84/1.00  --demod_completeness_check              fast
% 3.84/1.00  --demod_use_ground                      true
% 3.84/1.00  --sup_to_prop_solver                    passive
% 3.84/1.00  --sup_prop_simpl_new                    true
% 3.84/1.00  --sup_prop_simpl_given                  true
% 3.84/1.00  --sup_fun_splitting                     true
% 3.84/1.00  --sup_smt_interval                      50000
% 3.84/1.00  
% 3.84/1.00  ------ Superposition Simplification Setup
% 3.84/1.00  
% 3.84/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.84/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.84/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.84/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.84/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.84/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.84/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.84/1.00  --sup_immed_triv                        [TrivRules]
% 3.84/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.84/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.84/1.00  --sup_immed_bw_main                     []
% 3.84/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.84/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.84/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.84/1.00  --sup_input_bw                          []
% 3.84/1.00  
% 3.84/1.00  ------ Combination Options
% 3.84/1.00  
% 3.84/1.00  --comb_res_mult                         3
% 3.84/1.00  --comb_sup_mult                         2
% 3.84/1.00  --comb_inst_mult                        10
% 3.84/1.00  
% 3.84/1.00  ------ Debug Options
% 3.84/1.00  
% 3.84/1.00  --dbg_backtrace                         false
% 3.84/1.00  --dbg_dump_prop_clauses                 false
% 3.84/1.00  --dbg_dump_prop_clauses_file            -
% 3.84/1.00  --dbg_out_stat                          false
% 3.84/1.00  ------ Parsing...
% 3.84/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.84/1.00  
% 3.84/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.84/1.00  
% 3.84/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.84/1.00  
% 3.84/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.84/1.00  ------ Proving...
% 3.84/1.00  ------ Problem Properties 
% 3.84/1.00  
% 3.84/1.00  
% 3.84/1.00  clauses                                 34
% 3.84/1.00  conjectures                             1
% 3.84/1.00  EPR                                     3
% 3.84/1.00  Horn                                    23
% 3.84/1.00  unary                                   4
% 3.84/1.00  binary                                  4
% 3.84/1.00  lits                                    101
% 3.84/1.00  lits eq                                 10
% 3.84/1.00  fd_pure                                 0
% 3.84/1.00  fd_pseudo                               0
% 3.84/1.00  fd_cond                                 0
% 3.84/1.00  fd_pseudo_cond                          3
% 3.84/1.00  AC symbols                              0
% 3.84/1.00  
% 3.84/1.00  ------ Schedule dynamic 5 is on 
% 3.84/1.00  
% 3.84/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.84/1.00  
% 3.84/1.00  
% 3.84/1.00  ------ 
% 3.84/1.00  Current options:
% 3.84/1.00  ------ 
% 3.84/1.00  
% 3.84/1.00  ------ Input Options
% 3.84/1.00  
% 3.84/1.00  --out_options                           all
% 3.84/1.00  --tptp_safe_out                         true
% 3.84/1.00  --problem_path                          ""
% 3.84/1.00  --include_path                          ""
% 3.84/1.00  --clausifier                            res/vclausify_rel
% 3.84/1.00  --clausifier_options                    ""
% 3.84/1.00  --stdin                                 false
% 3.84/1.00  --stats_out                             all
% 3.84/1.00  
% 3.84/1.00  ------ General Options
% 3.84/1.00  
% 3.84/1.00  --fof                                   false
% 3.84/1.00  --time_out_real                         305.
% 3.84/1.00  --time_out_virtual                      -1.
% 3.84/1.00  --symbol_type_check                     false
% 3.84/1.00  --clausify_out                          false
% 3.84/1.00  --sig_cnt_out                           false
% 3.84/1.00  --trig_cnt_out                          false
% 3.84/1.00  --trig_cnt_out_tolerance                1.
% 3.84/1.00  --trig_cnt_out_sk_spl                   false
% 3.84/1.00  --abstr_cl_out                          false
% 3.84/1.00  
% 3.84/1.00  ------ Global Options
% 3.84/1.00  
% 3.84/1.00  --schedule                              default
% 3.84/1.00  --add_important_lit                     false
% 3.84/1.00  --prop_solver_per_cl                    1000
% 3.84/1.00  --min_unsat_core                        false
% 3.84/1.00  --soft_assumptions                      false
% 3.84/1.00  --soft_lemma_size                       3
% 3.84/1.00  --prop_impl_unit_size                   0
% 3.84/1.00  --prop_impl_unit                        []
% 3.84/1.00  --share_sel_clauses                     true
% 3.84/1.00  --reset_solvers                         false
% 3.84/1.00  --bc_imp_inh                            [conj_cone]
% 3.84/1.00  --conj_cone_tolerance                   3.
% 3.84/1.00  --extra_neg_conj                        none
% 3.84/1.00  --large_theory_mode                     true
% 3.84/1.00  --prolific_symb_bound                   200
% 3.84/1.00  --lt_threshold                          2000
% 3.84/1.00  --clause_weak_htbl                      true
% 3.84/1.00  --gc_record_bc_elim                     false
% 3.84/1.00  
% 3.84/1.00  ------ Preprocessing Options
% 3.84/1.00  
% 3.84/1.00  --preprocessing_flag                    true
% 3.84/1.00  --time_out_prep_mult                    0.1
% 3.84/1.00  --splitting_mode                        input
% 3.84/1.00  --splitting_grd                         true
% 3.84/1.00  --splitting_cvd                         false
% 3.84/1.00  --splitting_cvd_svl                     false
% 3.84/1.00  --splitting_nvd                         32
% 3.84/1.00  --sub_typing                            true
% 3.84/1.00  --prep_gs_sim                           true
% 3.84/1.00  --prep_unflatten                        true
% 3.84/1.00  --prep_res_sim                          true
% 3.84/1.00  --prep_upred                            true
% 3.84/1.00  --prep_sem_filter                       exhaustive
% 3.84/1.00  --prep_sem_filter_out                   false
% 3.84/1.00  --pred_elim                             true
% 3.84/1.00  --res_sim_input                         true
% 3.84/1.00  --eq_ax_congr_red                       true
% 3.84/1.00  --pure_diseq_elim                       true
% 3.84/1.00  --brand_transform                       false
% 3.84/1.00  --non_eq_to_eq                          false
% 3.84/1.00  --prep_def_merge                        true
% 3.84/1.00  --prep_def_merge_prop_impl              false
% 3.84/1.00  --prep_def_merge_mbd                    true
% 3.84/1.00  --prep_def_merge_tr_red                 false
% 3.84/1.00  --prep_def_merge_tr_cl                  false
% 3.84/1.00  --smt_preprocessing                     true
% 3.84/1.00  --smt_ac_axioms                         fast
% 3.84/1.00  --preprocessed_out                      false
% 3.84/1.00  --preprocessed_stats                    false
% 3.84/1.00  
% 3.84/1.00  ------ Abstraction refinement Options
% 3.84/1.00  
% 3.84/1.00  --abstr_ref                             []
% 3.84/1.00  --abstr_ref_prep                        false
% 3.84/1.00  --abstr_ref_until_sat                   false
% 3.84/1.00  --abstr_ref_sig_restrict                funpre
% 3.84/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.84/1.00  --abstr_ref_under                       []
% 3.84/1.00  
% 3.84/1.00  ------ SAT Options
% 3.84/1.00  
% 3.84/1.00  --sat_mode                              false
% 3.84/1.00  --sat_fm_restart_options                ""
% 3.84/1.00  --sat_gr_def                            false
% 3.84/1.00  --sat_epr_types                         true
% 3.84/1.00  --sat_non_cyclic_types                  false
% 3.84/1.00  --sat_finite_models                     false
% 3.84/1.00  --sat_fm_lemmas                         false
% 3.84/1.00  --sat_fm_prep                           false
% 3.84/1.00  --sat_fm_uc_incr                        true
% 3.84/1.00  --sat_out_model                         small
% 3.84/1.00  --sat_out_clauses                       false
% 3.84/1.00  
% 3.84/1.00  ------ QBF Options
% 3.84/1.00  
% 3.84/1.00  --qbf_mode                              false
% 3.84/1.00  --qbf_elim_univ                         false
% 3.84/1.00  --qbf_dom_inst                          none
% 3.84/1.00  --qbf_dom_pre_inst                      false
% 3.84/1.00  --qbf_sk_in                             false
% 3.84/1.00  --qbf_pred_elim                         true
% 3.84/1.00  --qbf_split                             512
% 3.84/1.00  
% 3.84/1.00  ------ BMC1 Options
% 3.84/1.00  
% 3.84/1.00  --bmc1_incremental                      false
% 3.84/1.00  --bmc1_axioms                           reachable_all
% 3.84/1.00  --bmc1_min_bound                        0
% 3.84/1.00  --bmc1_max_bound                        -1
% 3.84/1.00  --bmc1_max_bound_default                -1
% 3.84/1.00  --bmc1_symbol_reachability              true
% 3.84/1.00  --bmc1_property_lemmas                  false
% 3.84/1.00  --bmc1_k_induction                      false
% 3.84/1.00  --bmc1_non_equiv_states                 false
% 3.84/1.00  --bmc1_deadlock                         false
% 3.84/1.00  --bmc1_ucm                              false
% 3.84/1.00  --bmc1_add_unsat_core                   none
% 3.84/1.00  --bmc1_unsat_core_children              false
% 3.84/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.84/1.00  --bmc1_out_stat                         full
% 3.84/1.00  --bmc1_ground_init                      false
% 3.84/1.00  --bmc1_pre_inst_next_state              false
% 3.84/1.00  --bmc1_pre_inst_state                   false
% 3.84/1.00  --bmc1_pre_inst_reach_state             false
% 3.84/1.00  --bmc1_out_unsat_core                   false
% 3.84/1.00  --bmc1_aig_witness_out                  false
% 3.84/1.00  --bmc1_verbose                          false
% 3.84/1.00  --bmc1_dump_clauses_tptp                false
% 3.84/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.84/1.00  --bmc1_dump_file                        -
% 3.84/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.84/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.84/1.00  --bmc1_ucm_extend_mode                  1
% 3.84/1.00  --bmc1_ucm_init_mode                    2
% 3.84/1.00  --bmc1_ucm_cone_mode                    none
% 3.84/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.84/1.00  --bmc1_ucm_relax_model                  4
% 3.84/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.84/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.84/1.00  --bmc1_ucm_layered_model                none
% 3.84/1.00  --bmc1_ucm_max_lemma_size               10
% 3.84/1.00  
% 3.84/1.00  ------ AIG Options
% 3.84/1.00  
% 3.84/1.00  --aig_mode                              false
% 3.84/1.00  
% 3.84/1.00  ------ Instantiation Options
% 3.84/1.00  
% 3.84/1.00  --instantiation_flag                    true
% 3.84/1.00  --inst_sos_flag                         true
% 3.84/1.00  --inst_sos_phase                        true
% 3.84/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.84/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.84/1.00  --inst_lit_sel_side                     none
% 3.84/1.00  --inst_solver_per_active                1400
% 3.84/1.00  --inst_solver_calls_frac                1.
% 3.84/1.00  --inst_passive_queue_type               priority_queues
% 3.84/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.84/1.00  --inst_passive_queues_freq              [25;2]
% 3.84/1.00  --inst_dismatching                      true
% 3.84/1.00  --inst_eager_unprocessed_to_passive     true
% 3.84/1.00  --inst_prop_sim_given                   true
% 3.84/1.00  --inst_prop_sim_new                     false
% 3.84/1.00  --inst_subs_new                         false
% 3.84/1.00  --inst_eq_res_simp                      false
% 3.84/1.00  --inst_subs_given                       false
% 3.84/1.00  --inst_orphan_elimination               true
% 3.84/1.00  --inst_learning_loop_flag               true
% 3.84/1.00  --inst_learning_start                   3000
% 3.84/1.00  --inst_learning_factor                  2
% 3.84/1.00  --inst_start_prop_sim_after_learn       3
% 3.84/1.00  --inst_sel_renew                        solver
% 3.84/1.00  --inst_lit_activity_flag                true
% 3.84/1.00  --inst_restr_to_given                   false
% 3.84/1.00  --inst_activity_threshold               500
% 3.84/1.00  --inst_out_proof                        true
% 3.84/1.00  
% 3.84/1.00  ------ Resolution Options
% 3.84/1.00  
% 3.84/1.00  --resolution_flag                       false
% 3.84/1.00  --res_lit_sel                           adaptive
% 3.84/1.00  --res_lit_sel_side                      none
% 3.84/1.00  --res_ordering                          kbo
% 3.84/1.00  --res_to_prop_solver                    active
% 3.84/1.00  --res_prop_simpl_new                    false
% 3.84/1.00  --res_prop_simpl_given                  true
% 3.84/1.00  --res_passive_queue_type                priority_queues
% 3.84/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.84/1.00  --res_passive_queues_freq               [15;5]
% 3.84/1.00  --res_forward_subs                      full
% 3.84/1.00  --res_backward_subs                     full
% 3.84/1.00  --res_forward_subs_resolution           true
% 3.84/1.00  --res_backward_subs_resolution          true
% 3.84/1.00  --res_orphan_elimination                true
% 3.84/1.00  --res_time_limit                        2.
% 3.84/1.00  --res_out_proof                         true
% 3.84/1.00  
% 3.84/1.00  ------ Superposition Options
% 3.84/1.00  
% 3.84/1.00  --superposition_flag                    true
% 3.84/1.00  --sup_passive_queue_type                priority_queues
% 3.84/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.84/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.84/1.00  --demod_completeness_check              fast
% 3.84/1.00  --demod_use_ground                      true
% 3.84/1.00  --sup_to_prop_solver                    passive
% 3.84/1.00  --sup_prop_simpl_new                    true
% 3.84/1.00  --sup_prop_simpl_given                  true
% 3.84/1.00  --sup_fun_splitting                     true
% 3.84/1.00  --sup_smt_interval                      50000
% 3.84/1.00  
% 3.84/1.00  ------ Superposition Simplification Setup
% 3.84/1.00  
% 3.84/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.84/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.84/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.84/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.84/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.84/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.84/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.84/1.00  --sup_immed_triv                        [TrivRules]
% 3.84/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.84/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.84/1.00  --sup_immed_bw_main                     []
% 3.84/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.84/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.84/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.84/1.00  --sup_input_bw                          []
% 3.84/1.00  
% 3.84/1.00  ------ Combination Options
% 3.84/1.00  
% 3.84/1.00  --comb_res_mult                         3
% 3.84/1.00  --comb_sup_mult                         2
% 3.84/1.00  --comb_inst_mult                        10
% 3.84/1.00  
% 3.84/1.00  ------ Debug Options
% 3.84/1.00  
% 3.84/1.00  --dbg_backtrace                         false
% 3.84/1.00  --dbg_dump_prop_clauses                 false
% 3.84/1.00  --dbg_dump_prop_clauses_file            -
% 3.84/1.00  --dbg_out_stat                          false
% 3.84/1.00  
% 3.84/1.00  
% 3.84/1.00  
% 3.84/1.00  
% 3.84/1.00  ------ Proving...
% 3.84/1.00  
% 3.84/1.00  
% 3.84/1.00  % SZS status Theorem for theBenchmark.p
% 3.84/1.00  
% 3.84/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.84/1.00  
% 3.84/1.00  fof(f4,axiom,(
% 3.84/1.00    ! [X0,X1,X2] : (k4_partfun1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r1_tarski(k2_relat_1(X4),X1) & r1_tarski(k1_relat_1(X4),X0) & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4))))),
% 3.84/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/1.00  
% 3.84/1.00  fof(f11,plain,(
% 3.84/1.00    ! [X1,X0,X2] : (sP1(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r1_tarski(k2_relat_1(X4),X1) & r1_tarski(k1_relat_1(X4),X0) & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4))))),
% 3.84/1.00    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 3.84/1.00  
% 3.84/1.00  fof(f12,plain,(
% 3.84/1.00    ! [X0,X1,X2] : (k4_partfun1(X0,X1) = X2 <=> sP1(X1,X0,X2))),
% 3.84/1.00    inference(definition_folding,[],[f4,f11])).
% 3.84/1.00  
% 3.84/1.00  fof(f32,plain,(
% 3.84/1.00    ! [X0,X1,X2] : ((k4_partfun1(X0,X1) = X2 | ~sP1(X1,X0,X2)) & (sP1(X1,X0,X2) | k4_partfun1(X0,X1) != X2))),
% 3.84/1.00    inference(nnf_transformation,[],[f12])).
% 3.84/1.00  
% 3.84/1.00  fof(f67,plain,(
% 3.84/1.00    ( ! [X2,X0,X1] : (sP1(X1,X0,X2) | k4_partfun1(X0,X1) != X2) )),
% 3.84/1.00    inference(cnf_transformation,[],[f32])).
% 3.84/1.00  
% 3.84/1.00  fof(f78,plain,(
% 3.84/1.00    ( ! [X0,X1] : (sP1(X1,X0,k4_partfun1(X0,X1))) )),
% 3.84/1.00    inference(equality_resolution,[],[f67])).
% 3.84/1.00  
% 3.84/1.00  fof(f26,plain,(
% 3.84/1.00    ! [X1,X0,X2] : ((sP1(X1,X0,X2) | ? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | ~r1_tarski(k1_relat_1(X4),X0) | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X4] : (r1_tarski(k2_relat_1(X4),X1) & r1_tarski(k1_relat_1(X4),X0) & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | ~r1_tarski(k1_relat_1(X4),X0) | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4))) & (? [X4] : (r1_tarski(k2_relat_1(X4),X1) & r1_tarski(k1_relat_1(X4),X0) & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4)) | ~r2_hidden(X3,X2))) | ~sP1(X1,X0,X2)))),
% 3.84/1.00    inference(nnf_transformation,[],[f11])).
% 3.84/1.00  
% 3.84/1.00  fof(f27,plain,(
% 3.84/1.00    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X0) | ~r1_tarski(k1_relat_1(X4),X1) | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X0) & r1_tarski(k1_relat_1(X5),X1) & X3 = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r1_tarski(k2_relat_1(X7),X0) | ~r1_tarski(k1_relat_1(X7),X1) | X6 != X7 | ~v1_funct_1(X7) | ~v1_relat_1(X7))) & (? [X8] : (r1_tarski(k2_relat_1(X8),X0) & r1_tarski(k1_relat_1(X8),X1) & X6 = X8 & v1_funct_1(X8) & v1_relat_1(X8)) | ~r2_hidden(X6,X2))) | ~sP1(X0,X1,X2)))),
% 3.84/1.00    inference(rectify,[],[f26])).
% 3.84/1.00  
% 3.84/1.00  fof(f30,plain,(
% 3.84/1.00    ! [X6,X1,X0] : (? [X8] : (r1_tarski(k2_relat_1(X8),X0) & r1_tarski(k1_relat_1(X8),X1) & X6 = X8 & v1_funct_1(X8) & v1_relat_1(X8)) => (r1_tarski(k2_relat_1(sK8(X0,X1,X6)),X0) & r1_tarski(k1_relat_1(sK8(X0,X1,X6)),X1) & sK8(X0,X1,X6) = X6 & v1_funct_1(sK8(X0,X1,X6)) & v1_relat_1(sK8(X0,X1,X6))))),
% 3.84/1.00    introduced(choice_axiom,[])).
% 3.84/1.00  
% 3.84/1.00  fof(f29,plain,(
% 3.84/1.00    ( ! [X3] : (! [X2,X1,X0] : (? [X5] : (r1_tarski(k2_relat_1(X5),X0) & r1_tarski(k1_relat_1(X5),X1) & X3 = X5 & v1_funct_1(X5) & v1_relat_1(X5)) => (r1_tarski(k2_relat_1(sK7(X0,X1,X2)),X0) & r1_tarski(k1_relat_1(sK7(X0,X1,X2)),X1) & sK7(X0,X1,X2) = X3 & v1_funct_1(sK7(X0,X1,X2)) & v1_relat_1(sK7(X0,X1,X2))))) )),
% 3.84/1.00    introduced(choice_axiom,[])).
% 3.84/1.00  
% 3.84/1.00  fof(f28,plain,(
% 3.84/1.00    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X0) | ~r1_tarski(k1_relat_1(X4),X1) | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X0) & r1_tarski(k1_relat_1(X5),X1) & X3 = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(X3,X2))) => ((! [X4] : (~r1_tarski(k2_relat_1(X4),X0) | ~r1_tarski(k1_relat_1(X4),X1) | sK6(X0,X1,X2) != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X0) & r1_tarski(k1_relat_1(X5),X1) & sK6(X0,X1,X2) = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(sK6(X0,X1,X2),X2))))),
% 3.84/1.00    introduced(choice_axiom,[])).
% 3.84/1.00  
% 3.84/1.00  fof(f31,plain,(
% 3.84/1.00    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ((! [X4] : (~r1_tarski(k2_relat_1(X4),X0) | ~r1_tarski(k1_relat_1(X4),X1) | sK6(X0,X1,X2) != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((r1_tarski(k2_relat_1(sK7(X0,X1,X2)),X0) & r1_tarski(k1_relat_1(sK7(X0,X1,X2)),X1) & sK6(X0,X1,X2) = sK7(X0,X1,X2) & v1_funct_1(sK7(X0,X1,X2)) & v1_relat_1(sK7(X0,X1,X2))) | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r1_tarski(k2_relat_1(X7),X0) | ~r1_tarski(k1_relat_1(X7),X1) | X6 != X7 | ~v1_funct_1(X7) | ~v1_relat_1(X7))) & ((r1_tarski(k2_relat_1(sK8(X0,X1,X6)),X0) & r1_tarski(k1_relat_1(sK8(X0,X1,X6)),X1) & sK8(X0,X1,X6) = X6 & v1_funct_1(sK8(X0,X1,X6)) & v1_relat_1(sK8(X0,X1,X6))) | ~r2_hidden(X6,X2))) | ~sP1(X0,X1,X2)))),
% 3.84/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f27,f30,f29,f28])).
% 3.84/1.00  
% 3.84/1.00  fof(f60,plain,(
% 3.84/1.00    ( ! [X6,X2,X0,X7,X1] : (r2_hidden(X6,X2) | ~r1_tarski(k2_relat_1(X7),X0) | ~r1_tarski(k1_relat_1(X7),X1) | X6 != X7 | ~v1_funct_1(X7) | ~v1_relat_1(X7) | ~sP1(X0,X1,X2)) )),
% 3.84/1.00    inference(cnf_transformation,[],[f31])).
% 3.84/1.00  
% 3.84/1.00  fof(f77,plain,(
% 3.84/1.00    ( ! [X2,X0,X7,X1] : (r2_hidden(X7,X2) | ~r1_tarski(k2_relat_1(X7),X0) | ~r1_tarski(k1_relat_1(X7),X1) | ~v1_funct_1(X7) | ~v1_relat_1(X7) | ~sP1(X0,X1,X2)) )),
% 3.84/1.00    inference(equality_resolution,[],[f60])).
% 3.84/1.00  
% 3.84/1.00  fof(f2,axiom,(
% 3.84/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.84/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/1.00  
% 3.84/1.00  fof(f17,plain,(
% 3.84/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.84/1.00    inference(nnf_transformation,[],[f2])).
% 3.84/1.00  
% 3.84/1.00  fof(f18,plain,(
% 3.84/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.84/1.00    inference(flattening,[],[f17])).
% 3.84/1.00  
% 3.84/1.00  fof(f38,plain,(
% 3.84/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.84/1.00    inference(cnf_transformation,[],[f18])).
% 3.84/1.00  
% 3.84/1.00  fof(f71,plain,(
% 3.84/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.84/1.00    inference(equality_resolution,[],[f38])).
% 3.84/1.00  
% 3.84/1.00  fof(f1,axiom,(
% 3.84/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.84/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/1.00  
% 3.84/1.00  fof(f7,plain,(
% 3.84/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.84/1.00    inference(ennf_transformation,[],[f1])).
% 3.84/1.00  
% 3.84/1.00  fof(f13,plain,(
% 3.84/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.84/1.00    inference(nnf_transformation,[],[f7])).
% 3.84/1.00  
% 3.84/1.00  fof(f14,plain,(
% 3.84/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.84/1.00    inference(rectify,[],[f13])).
% 3.84/1.00  
% 3.84/1.00  fof(f15,plain,(
% 3.84/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 3.84/1.00    introduced(choice_axiom,[])).
% 3.84/1.00  
% 3.84/1.00  fof(f16,plain,(
% 3.84/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.84/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f14,f15])).
% 3.84/1.00  
% 3.84/1.00  fof(f36,plain,(
% 3.84/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK2(X0,X1),X0)) )),
% 3.84/1.00    inference(cnf_transformation,[],[f16])).
% 3.84/1.00  
% 3.84/1.00  fof(f3,axiom,(
% 3.84/1.00    ! [X0,X1,X2] : (k1_funct_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4))))),
% 3.84/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/1.00  
% 3.84/1.00  fof(f9,plain,(
% 3.84/1.00    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4))))),
% 3.84/1.00    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 3.84/1.00  
% 3.84/1.00  fof(f10,plain,(
% 3.84/1.00    ! [X0,X1,X2] : (k1_funct_2(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 3.84/1.00    inference(definition_folding,[],[f3,f9])).
% 3.84/1.00  
% 3.84/1.00  fof(f25,plain,(
% 3.84/1.00    ! [X0,X1,X2] : ((k1_funct_2(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k1_funct_2(X0,X1) != X2))),
% 3.84/1.00    inference(nnf_transformation,[],[f10])).
% 3.84/1.00  
% 3.84/1.00  fof(f53,plain,(
% 3.84/1.00    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k1_funct_2(X0,X1) != X2) )),
% 3.84/1.00    inference(cnf_transformation,[],[f25])).
% 3.84/1.00  
% 3.84/1.00  fof(f75,plain,(
% 3.84/1.00    ( ! [X0,X1] : (sP0(X1,X0,k1_funct_2(X0,X1))) )),
% 3.84/1.00    inference(equality_resolution,[],[f53])).
% 3.84/1.00  
% 3.84/1.00  fof(f19,plain,(
% 3.84/1.00    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4))) & (? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 3.84/1.00    inference(nnf_transformation,[],[f9])).
% 3.84/1.00  
% 3.84/1.00  fof(f20,plain,(
% 3.84/1.00    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X0) | k1_relat_1(X4) != X1 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X0) & k1_relat_1(X5) = X1 & X3 = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r1_tarski(k2_relat_1(X7),X0) | k1_relat_1(X7) != X1 | X6 != X7 | ~v1_funct_1(X7) | ~v1_relat_1(X7))) & (? [X8] : (r1_tarski(k2_relat_1(X8),X0) & k1_relat_1(X8) = X1 & X6 = X8 & v1_funct_1(X8) & v1_relat_1(X8)) | ~r2_hidden(X6,X2))) | ~sP0(X0,X1,X2)))),
% 3.84/1.00    inference(rectify,[],[f19])).
% 3.84/1.00  
% 3.84/1.00  fof(f23,plain,(
% 3.84/1.00    ! [X6,X1,X0] : (? [X8] : (r1_tarski(k2_relat_1(X8),X0) & k1_relat_1(X8) = X1 & X6 = X8 & v1_funct_1(X8) & v1_relat_1(X8)) => (r1_tarski(k2_relat_1(sK5(X0,X1,X6)),X0) & k1_relat_1(sK5(X0,X1,X6)) = X1 & sK5(X0,X1,X6) = X6 & v1_funct_1(sK5(X0,X1,X6)) & v1_relat_1(sK5(X0,X1,X6))))),
% 3.84/1.00    introduced(choice_axiom,[])).
% 3.84/1.00  
% 3.84/1.00  fof(f22,plain,(
% 3.84/1.00    ( ! [X3] : (! [X2,X1,X0] : (? [X5] : (r1_tarski(k2_relat_1(X5),X0) & k1_relat_1(X5) = X1 & X3 = X5 & v1_funct_1(X5) & v1_relat_1(X5)) => (r1_tarski(k2_relat_1(sK4(X0,X1,X2)),X0) & k1_relat_1(sK4(X0,X1,X2)) = X1 & sK4(X0,X1,X2) = X3 & v1_funct_1(sK4(X0,X1,X2)) & v1_relat_1(sK4(X0,X1,X2))))) )),
% 3.84/1.00    introduced(choice_axiom,[])).
% 3.84/1.00  
% 3.84/1.00  fof(f21,plain,(
% 3.84/1.00    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X0) | k1_relat_1(X4) != X1 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X0) & k1_relat_1(X5) = X1 & X3 = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(X3,X2))) => ((! [X4] : (~r1_tarski(k2_relat_1(X4),X0) | k1_relat_1(X4) != X1 | sK3(X0,X1,X2) != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X0) & k1_relat_1(X5) = X1 & sK3(X0,X1,X2) = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 3.84/1.00    introduced(choice_axiom,[])).
% 3.84/1.00  
% 3.84/1.00  fof(f24,plain,(
% 3.84/1.00    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((! [X4] : (~r1_tarski(k2_relat_1(X4),X0) | k1_relat_1(X4) != X1 | sK3(X0,X1,X2) != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r1_tarski(k2_relat_1(sK4(X0,X1,X2)),X0) & k1_relat_1(sK4(X0,X1,X2)) = X1 & sK3(X0,X1,X2) = sK4(X0,X1,X2) & v1_funct_1(sK4(X0,X1,X2)) & v1_relat_1(sK4(X0,X1,X2))) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r1_tarski(k2_relat_1(X7),X0) | k1_relat_1(X7) != X1 | X6 != X7 | ~v1_funct_1(X7) | ~v1_relat_1(X7))) & ((r1_tarski(k2_relat_1(sK5(X0,X1,X6)),X0) & k1_relat_1(sK5(X0,X1,X6)) = X1 & sK5(X0,X1,X6) = X6 & v1_funct_1(sK5(X0,X1,X6)) & v1_relat_1(sK5(X0,X1,X6))) | ~r2_hidden(X6,X2))) | ~sP0(X0,X1,X2)))),
% 3.84/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f20,f23,f22,f21])).
% 3.84/1.00  
% 3.84/1.00  fof(f43,plain,(
% 3.84/1.00    ( ! [X6,X2,X0,X1] : (sK5(X0,X1,X6) = X6 | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 3.84/1.00    inference(cnf_transformation,[],[f24])).
% 3.84/1.00  
% 3.84/1.00  fof(f5,conjecture,(
% 3.84/1.00    ! [X0,X1] : r1_tarski(k1_funct_2(X0,X1),k4_partfun1(X0,X1))),
% 3.84/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/1.00  
% 3.84/1.00  fof(f6,negated_conjecture,(
% 3.84/1.00    ~! [X0,X1] : r1_tarski(k1_funct_2(X0,X1),k4_partfun1(X0,X1))),
% 3.84/1.00    inference(negated_conjecture,[],[f5])).
% 3.84/1.00  
% 3.84/1.00  fof(f8,plain,(
% 3.84/1.00    ? [X0,X1] : ~r1_tarski(k1_funct_2(X0,X1),k4_partfun1(X0,X1))),
% 3.84/1.00    inference(ennf_transformation,[],[f6])).
% 3.84/1.00  
% 3.84/1.00  fof(f33,plain,(
% 3.84/1.00    ? [X0,X1] : ~r1_tarski(k1_funct_2(X0,X1),k4_partfun1(X0,X1)) => ~r1_tarski(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10))),
% 3.84/1.00    introduced(choice_axiom,[])).
% 3.84/1.00  
% 3.84/1.00  fof(f34,plain,(
% 3.84/1.00    ~r1_tarski(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10))),
% 3.84/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10])],[f8,f33])).
% 3.84/1.00  
% 3.84/1.00  fof(f69,plain,(
% 3.84/1.00    ~r1_tarski(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10))),
% 3.84/1.00    inference(cnf_transformation,[],[f34])).
% 3.84/1.00  
% 3.84/1.00  fof(f44,plain,(
% 3.84/1.00    ( ! [X6,X2,X0,X1] : (k1_relat_1(sK5(X0,X1,X6)) = X1 | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 3.84/1.00    inference(cnf_transformation,[],[f24])).
% 3.84/1.00  
% 3.84/1.00  fof(f45,plain,(
% 3.84/1.00    ( ! [X6,X2,X0,X1] : (r1_tarski(k2_relat_1(sK5(X0,X1,X6)),X0) | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 3.84/1.00    inference(cnf_transformation,[],[f24])).
% 3.84/1.00  
% 3.84/1.00  fof(f57,plain,(
% 3.84/1.00    ( ! [X6,X2,X0,X1] : (sK8(X0,X1,X6) = X6 | ~r2_hidden(X6,X2) | ~sP1(X0,X1,X2)) )),
% 3.84/1.00    inference(cnf_transformation,[],[f31])).
% 3.84/1.00  
% 3.84/1.00  fof(f41,plain,(
% 3.84/1.00    ( ! [X6,X2,X0,X1] : (v1_relat_1(sK5(X0,X1,X6)) | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 3.84/1.00    inference(cnf_transformation,[],[f24])).
% 3.84/1.00  
% 3.84/1.00  fof(f42,plain,(
% 3.84/1.00    ( ! [X6,X2,X0,X1] : (v1_funct_1(sK5(X0,X1,X6)) | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 3.84/1.00    inference(cnf_transformation,[],[f24])).
% 3.84/1.00  
% 3.84/1.00  fof(f59,plain,(
% 3.84/1.00    ( ! [X6,X2,X0,X1] : (r1_tarski(k2_relat_1(sK8(X0,X1,X6)),X0) | ~r2_hidden(X6,X2) | ~sP1(X0,X1,X2)) )),
% 3.84/1.00    inference(cnf_transformation,[],[f31])).
% 3.84/1.00  
% 3.84/1.00  fof(f40,plain,(
% 3.84/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.84/1.00    inference(cnf_transformation,[],[f18])).
% 3.84/1.00  
% 3.84/1.00  fof(f37,plain,(
% 3.84/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK2(X0,X1),X1)) )),
% 3.84/1.00    inference(cnf_transformation,[],[f16])).
% 3.84/1.00  
% 3.84/1.00  cnf(c_33,plain,
% 3.84/1.00      ( sP1(X0,X1,k4_partfun1(X1,X0)) ),
% 3.84/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_7458,plain,
% 3.84/1.00      ( sP1(X0,X1,k4_partfun1(X1,X0)) = iProver_top ),
% 3.84/1.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_26,plain,
% 3.84/1.00      ( ~ sP1(X0,X1,X2)
% 3.84/1.00      | r2_hidden(X3,X2)
% 3.84/1.00      | ~ r1_tarski(k2_relat_1(X3),X0)
% 3.84/1.00      | ~ r1_tarski(k1_relat_1(X3),X1)
% 3.84/1.00      | ~ v1_relat_1(X3)
% 3.84/1.00      | ~ v1_funct_1(X3) ),
% 3.84/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_7465,plain,
% 3.84/1.00      ( sP1(X0,X1,X2) != iProver_top
% 3.84/1.00      | r2_hidden(X3,X2) = iProver_top
% 3.84/1.00      | r1_tarski(k2_relat_1(X3),X0) != iProver_top
% 3.84/1.00      | r1_tarski(k1_relat_1(X3),X1) != iProver_top
% 3.84/1.00      | v1_relat_1(X3) != iProver_top
% 3.84/1.00      | v1_funct_1(X3) != iProver_top ),
% 3.84/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_9230,plain,
% 3.84/1.00      ( r2_hidden(X0,k4_partfun1(X1,X2)) = iProver_top
% 3.84/1.00      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 3.84/1.00      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 3.84/1.00      | v1_relat_1(X0) != iProver_top
% 3.84/1.00      | v1_funct_1(X0) != iProver_top ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_7458,c_7465]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_5,plain,
% 3.84/1.00      ( r1_tarski(X0,X0) ),
% 3.84/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_7486,plain,
% 3.84/1.00      ( r1_tarski(X0,X0) = iProver_top ),
% 3.84/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_1,plain,
% 3.84/1.00      ( r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.84/1.00      inference(cnf_transformation,[],[f36]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_7489,plain,
% 3.84/1.00      ( r2_hidden(sK2(X0,X1),X0) = iProver_top
% 3.84/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.84/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_19,plain,
% 3.84/1.00      ( sP0(X0,X1,k1_funct_2(X1,X0)) ),
% 3.84/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_7472,plain,
% 3.84/1.00      ( sP0(X0,X1,k1_funct_2(X1,X0)) = iProver_top ),
% 3.84/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_15,plain,
% 3.84/1.00      ( ~ sP0(X0,X1,X2) | ~ r2_hidden(X3,X2) | sK5(X0,X1,X3) = X3 ),
% 3.84/1.00      inference(cnf_transformation,[],[f43]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_7476,plain,
% 3.84/1.00      ( sK5(X0,X1,X2) = X2
% 3.84/1.00      | sP0(X0,X1,X3) != iProver_top
% 3.84/1.00      | r2_hidden(X2,X3) != iProver_top ),
% 3.84/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_8142,plain,
% 3.84/1.00      ( sK5(X0,X1,X2) = X2
% 3.84/1.00      | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_7472,c_7476]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_8145,plain,
% 3.84/1.00      ( sK5(X0,X1,sK2(k1_funct_2(X1,X0),X2)) = sK2(k1_funct_2(X1,X0),X2)
% 3.84/1.00      | r1_tarski(k1_funct_2(X1,X0),X2) = iProver_top ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_7489,c_8142]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_34,negated_conjecture,
% 3.84/1.00      ( ~ r1_tarski(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)) ),
% 3.84/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_7457,plain,
% 3.84/1.00      ( r1_tarski(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)) != iProver_top ),
% 3.84/1.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_12643,plain,
% 3.84/1.00      ( sK5(sK10,sK9,sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10))) = sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)) ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_8145,c_7457]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_14,plain,
% 3.84/1.00      ( ~ sP0(X0,X1,X2)
% 3.84/1.00      | ~ r2_hidden(X3,X2)
% 3.84/1.00      | k1_relat_1(sK5(X0,X1,X3)) = X1 ),
% 3.84/1.00      inference(cnf_transformation,[],[f44]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_7477,plain,
% 3.84/1.00      ( k1_relat_1(sK5(X0,X1,X2)) = X1
% 3.84/1.00      | sP0(X0,X1,X3) != iProver_top
% 3.84/1.00      | r2_hidden(X2,X3) != iProver_top ),
% 3.84/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_8697,plain,
% 3.84/1.00      ( k1_relat_1(sK5(X0,X1,X2)) = X1
% 3.84/1.00      | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_7472,c_7477]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_8940,plain,
% 3.84/1.00      ( k1_relat_1(sK5(X0,X1,sK2(k1_funct_2(X1,X0),X2))) = X1
% 3.84/1.00      | r1_tarski(k1_funct_2(X1,X0),X2) = iProver_top ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_7489,c_8697]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_11904,plain,
% 3.84/1.00      ( k1_relat_1(sK5(sK10,sK9,sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)))) = sK9 ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_8940,c_7457]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_13,plain,
% 3.84/1.00      ( ~ sP0(X0,X1,X2)
% 3.84/1.00      | ~ r2_hidden(X3,X2)
% 3.84/1.00      | r1_tarski(k2_relat_1(sK5(X0,X1,X3)),X0) ),
% 3.84/1.00      inference(cnf_transformation,[],[f45]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_7478,plain,
% 3.84/1.00      ( sP0(X0,X1,X2) != iProver_top
% 3.84/1.00      | r2_hidden(X3,X2) != iProver_top
% 3.84/1.00      | r1_tarski(k2_relat_1(sK5(X0,X1,X3)),X0) = iProver_top ),
% 3.84/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_9063,plain,
% 3.84/1.00      ( r2_hidden(X0,k1_funct_2(X1,X2)) != iProver_top
% 3.84/1.00      | r1_tarski(k2_relat_1(sK5(X2,X1,X0)),X2) = iProver_top ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_7472,c_7478]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_29,plain,
% 3.84/1.00      ( ~ sP1(X0,X1,X2) | ~ r2_hidden(X3,X2) | sK8(X0,X1,X3) = X3 ),
% 3.84/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_7462,plain,
% 3.84/1.00      ( sK8(X0,X1,X2) = X2
% 3.84/1.00      | sP1(X0,X1,X3) != iProver_top
% 3.84/1.00      | r2_hidden(X2,X3) != iProver_top ),
% 3.84/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_8094,plain,
% 3.84/1.00      ( sK8(X0,X1,X2) = X2
% 3.84/1.00      | r2_hidden(X2,k4_partfun1(X1,X0)) != iProver_top ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_7458,c_7462]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_10563,plain,
% 3.84/1.00      ( sK8(X0,X1,X2) = X2
% 3.84/1.00      | r1_tarski(k2_relat_1(X2),X0) != iProver_top
% 3.84/1.00      | r1_tarski(k1_relat_1(X2),X1) != iProver_top
% 3.84/1.00      | v1_relat_1(X2) != iProver_top
% 3.84/1.00      | v1_funct_1(X2) != iProver_top ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_9230,c_8094]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_10613,plain,
% 3.84/1.00      ( sK8(X0,X1,sK5(X0,X2,X3)) = sK5(X0,X2,X3)
% 3.84/1.00      | r2_hidden(X3,k1_funct_2(X2,X0)) != iProver_top
% 3.84/1.00      | r1_tarski(k1_relat_1(sK5(X0,X2,X3)),X1) != iProver_top
% 3.84/1.00      | v1_relat_1(sK5(X0,X2,X3)) != iProver_top
% 3.84/1.00      | v1_funct_1(sK5(X0,X2,X3)) != iProver_top ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_9063,c_10563]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_11983,plain,
% 3.84/1.00      ( sK8(sK10,X0,sK5(sK10,sK9,sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)))) = sK5(sK10,sK9,sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)))
% 3.84/1.00      | r2_hidden(sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)),k1_funct_2(sK9,sK10)) != iProver_top
% 3.84/1.00      | r1_tarski(sK9,X0) != iProver_top
% 3.84/1.00      | v1_relat_1(sK5(sK10,sK9,sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)))) != iProver_top
% 3.84/1.00      | v1_funct_1(sK5(sK10,sK9,sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)))) != iProver_top ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_11904,c_10613]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_35,plain,
% 3.84/1.00      ( r1_tarski(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)) != iProver_top ),
% 3.84/1.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_7526,plain,
% 3.84/1.00      ( r2_hidden(sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)),k1_funct_2(sK9,sK10))
% 3.84/1.00      | r1_tarski(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)) ),
% 3.84/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_7527,plain,
% 3.84/1.00      ( r2_hidden(sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)),k1_funct_2(sK9,sK10)) = iProver_top
% 3.84/1.00      | r1_tarski(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)) = iProver_top ),
% 3.84/1.00      inference(predicate_to_equality,[status(thm)],[c_7526]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_17,plain,
% 3.84/1.00      ( ~ sP0(X0,X1,X2)
% 3.84/1.00      | ~ r2_hidden(X3,X2)
% 3.84/1.00      | v1_relat_1(sK5(X0,X1,X3)) ),
% 3.84/1.00      inference(cnf_transformation,[],[f41]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_8158,plain,
% 3.84/1.00      ( ~ sP0(X0,X1,k1_funct_2(sK9,sK10))
% 3.84/1.00      | ~ r2_hidden(sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)),k1_funct_2(sK9,sK10))
% 3.84/1.00      | v1_relat_1(sK5(X0,X1,sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)))) ),
% 3.84/1.00      inference(instantiation,[status(thm)],[c_17]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_8454,plain,
% 3.84/1.00      ( ~ sP0(sK10,sK9,k1_funct_2(sK9,sK10))
% 3.84/1.00      | ~ r2_hidden(sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)),k1_funct_2(sK9,sK10))
% 3.84/1.00      | v1_relat_1(sK5(sK10,sK9,sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)))) ),
% 3.84/1.00      inference(instantiation,[status(thm)],[c_8158]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_8455,plain,
% 3.84/1.00      ( sP0(sK10,sK9,k1_funct_2(sK9,sK10)) != iProver_top
% 3.84/1.00      | r2_hidden(sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)),k1_funct_2(sK9,sK10)) != iProver_top
% 3.84/1.00      | v1_relat_1(sK5(sK10,sK9,sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)))) = iProver_top ),
% 3.84/1.00      inference(predicate_to_equality,[status(thm)],[c_8454]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_9350,plain,
% 3.84/1.00      ( sP0(sK10,sK9,k1_funct_2(sK9,sK10)) ),
% 3.84/1.00      inference(instantiation,[status(thm)],[c_19]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_9351,plain,
% 3.84/1.00      ( sP0(sK10,sK9,k1_funct_2(sK9,sK10)) = iProver_top ),
% 3.84/1.00      inference(predicate_to_equality,[status(thm)],[c_9350]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_12549,plain,
% 3.84/1.00      ( r1_tarski(sK9,X0) != iProver_top
% 3.84/1.00      | sK8(sK10,X0,sK5(sK10,sK9,sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)))) = sK5(sK10,sK9,sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)))
% 3.84/1.00      | v1_funct_1(sK5(sK10,sK9,sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)))) != iProver_top ),
% 3.84/1.00      inference(global_propositional_subsumption,
% 3.84/1.00                [status(thm)],
% 3.84/1.00                [c_11983,c_35,c_7527,c_8455,c_9351]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_12550,plain,
% 3.84/1.00      ( sK8(sK10,X0,sK5(sK10,sK9,sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)))) = sK5(sK10,sK9,sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)))
% 3.84/1.00      | r1_tarski(sK9,X0) != iProver_top
% 3.84/1.00      | v1_funct_1(sK5(sK10,sK9,sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)))) != iProver_top ),
% 3.84/1.00      inference(renaming,[status(thm)],[c_12549]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_12821,plain,
% 3.84/1.00      ( sK8(sK10,X0,sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10))) = sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10))
% 3.84/1.00      | r1_tarski(sK9,X0) != iProver_top
% 3.84/1.00      | v1_funct_1(sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10))) != iProver_top ),
% 3.84/1.00      inference(demodulation,[status(thm)],[c_12643,c_12550]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_16,plain,
% 3.84/1.00      ( ~ sP0(X0,X1,X2)
% 3.84/1.00      | ~ r2_hidden(X3,X2)
% 3.84/1.00      | v1_funct_1(sK5(X0,X1,X3)) ),
% 3.84/1.00      inference(cnf_transformation,[],[f42]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_7475,plain,
% 3.84/1.00      ( sP0(X0,X1,X2) != iProver_top
% 3.84/1.00      | r2_hidden(X3,X2) != iProver_top
% 3.84/1.00      | v1_funct_1(sK5(X0,X1,X3)) = iProver_top ),
% 3.84/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_8588,plain,
% 3.84/1.00      ( r2_hidden(X0,k1_funct_2(X1,X2)) != iProver_top
% 3.84/1.00      | v1_funct_1(sK5(X2,X1,X0)) = iProver_top ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_7472,c_7475]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_8815,plain,
% 3.84/1.00      ( r1_tarski(k1_funct_2(X0,X1),X2) = iProver_top
% 3.84/1.00      | v1_funct_1(sK5(X1,X0,sK2(k1_funct_2(X0,X1),X2))) = iProver_top ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_7489,c_8588]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_12851,plain,
% 3.84/1.00      ( r1_tarski(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)) = iProver_top
% 3.84/1.00      | v1_funct_1(sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10))) = iProver_top ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_12643,c_8815]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_13270,plain,
% 3.84/1.00      ( r1_tarski(sK9,X0) != iProver_top
% 3.84/1.00      | sK8(sK10,X0,sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10))) = sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)) ),
% 3.84/1.00      inference(global_propositional_subsumption,
% 3.84/1.00                [status(thm)],
% 3.84/1.00                [c_12821,c_35,c_12851]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_13271,plain,
% 3.84/1.00      ( sK8(sK10,X0,sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10))) = sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10))
% 3.84/1.00      | r1_tarski(sK9,X0) != iProver_top ),
% 3.84/1.00      inference(renaming,[status(thm)],[c_13270]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_13276,plain,
% 3.84/1.00      ( sK8(sK10,sK9,sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10))) = sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)) ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_7486,c_13271]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_27,plain,
% 3.84/1.00      ( ~ sP1(X0,X1,X2)
% 3.84/1.00      | ~ r2_hidden(X3,X2)
% 3.84/1.00      | r1_tarski(k2_relat_1(sK8(X0,X1,X3)),X0) ),
% 3.84/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_7464,plain,
% 3.84/1.00      ( sP1(X0,X1,X2) != iProver_top
% 3.84/1.00      | r2_hidden(X3,X2) != iProver_top
% 3.84/1.00      | r1_tarski(k2_relat_1(sK8(X0,X1,X3)),X0) = iProver_top ),
% 3.84/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_8498,plain,
% 3.84/1.00      ( r2_hidden(X0,k4_partfun1(X1,X2)) != iProver_top
% 3.84/1.00      | r1_tarski(k2_relat_1(sK8(X2,X1,X0)),X2) = iProver_top ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_7458,c_7464]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_3,plain,
% 3.84/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.84/1.00      inference(cnf_transformation,[],[f40]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_7487,plain,
% 3.84/1.00      ( X0 = X1
% 3.84/1.00      | r1_tarski(X1,X0) != iProver_top
% 3.84/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 3.84/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_8945,plain,
% 3.84/1.00      ( k2_relat_1(sK8(X0,X1,X2)) = X0
% 3.84/1.00      | r2_hidden(X2,k4_partfun1(X1,X0)) != iProver_top
% 3.84/1.00      | r1_tarski(X0,k2_relat_1(sK8(X0,X1,X2))) != iProver_top ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_8498,c_7487]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_13662,plain,
% 3.84/1.00      ( k2_relat_1(sK8(sK10,sK9,sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)))) = sK10
% 3.84/1.00      | r2_hidden(sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)),k4_partfun1(sK9,sK10)) != iProver_top
% 3.84/1.00      | r1_tarski(sK10,k2_relat_1(sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)))) != iProver_top ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_13276,c_8945]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_13670,plain,
% 3.84/1.00      ( k2_relat_1(sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10))) = sK10
% 3.84/1.00      | r2_hidden(sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)),k4_partfun1(sK9,sK10)) != iProver_top
% 3.84/1.00      | r1_tarski(sK10,k2_relat_1(sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)))) != iProver_top ),
% 3.84/1.00      inference(light_normalisation,[status(thm)],[c_13662,c_13276]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_0,plain,
% 3.84/1.00      ( ~ r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1) ),
% 3.84/1.00      inference(cnf_transformation,[],[f37]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_7525,plain,
% 3.84/1.00      ( ~ r2_hidden(sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)),k4_partfun1(sK9,sK10))
% 3.84/1.00      | r1_tarski(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)) ),
% 3.84/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_7529,plain,
% 3.84/1.00      ( r2_hidden(sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)),k4_partfun1(sK9,sK10)) != iProver_top
% 3.84/1.00      | r1_tarski(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)) = iProver_top ),
% 3.84/1.00      inference(predicate_to_equality,[status(thm)],[c_7525]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_18772,plain,
% 3.84/1.00      ( r2_hidden(sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)),k4_partfun1(sK9,sK10)) != iProver_top ),
% 3.84/1.00      inference(global_propositional_subsumption,
% 3.84/1.00                [status(thm)],
% 3.84/1.00                [c_13670,c_35,c_7529]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_18776,plain,
% 3.84/1.00      ( r1_tarski(k2_relat_1(sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10))),sK10) != iProver_top
% 3.84/1.00      | r1_tarski(k1_relat_1(sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10))),sK9) != iProver_top
% 3.84/1.00      | v1_relat_1(sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10))) != iProver_top
% 3.84/1.00      | v1_funct_1(sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10))) != iProver_top ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_9230,c_18772]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_12827,plain,
% 3.84/1.00      ( k1_relat_1(sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10))) = sK9 ),
% 3.84/1.00      inference(demodulation,[status(thm)],[c_12643,c_11904]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_18780,plain,
% 3.84/1.00      ( r1_tarski(k2_relat_1(sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10))),sK10) != iProver_top
% 3.84/1.00      | r1_tarski(sK9,sK9) != iProver_top
% 3.84/1.00      | v1_relat_1(sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10))) != iProver_top
% 3.84/1.00      | v1_funct_1(sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10))) != iProver_top ),
% 3.84/1.00      inference(light_normalisation,[status(thm)],[c_18776,c_12827]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_15251,plain,
% 3.84/1.00      ( r1_tarski(sK9,sK9) ),
% 3.84/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_15252,plain,
% 3.84/1.00      ( r1_tarski(sK9,sK9) = iProver_top ),
% 3.84/1.00      inference(predicate_to_equality,[status(thm)],[c_15251]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_7474,plain,
% 3.84/1.00      ( sP0(X0,X1,X2) != iProver_top
% 3.84/1.00      | r2_hidden(X3,X2) != iProver_top
% 3.84/1.00      | v1_relat_1(sK5(X0,X1,X3)) = iProver_top ),
% 3.84/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_8585,plain,
% 3.84/1.00      ( r2_hidden(X0,k1_funct_2(X1,X2)) != iProver_top
% 3.84/1.00      | v1_relat_1(sK5(X2,X1,X0)) = iProver_top ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_7472,c_7474]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_8810,plain,
% 3.84/1.00      ( r1_tarski(k1_funct_2(X0,X1),X2) = iProver_top
% 3.84/1.00      | v1_relat_1(sK5(X1,X0,sK2(k1_funct_2(X0,X1),X2))) = iProver_top ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_7489,c_8585]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_12852,plain,
% 3.84/1.00      ( r1_tarski(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)) = iProver_top
% 3.84/1.00      | v1_relat_1(sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10))) = iProver_top ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_12643,c_8810]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_12850,plain,
% 3.84/1.00      ( r2_hidden(sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10)),k1_funct_2(sK9,sK10)) != iProver_top
% 3.84/1.00      | r1_tarski(k2_relat_1(sK2(k1_funct_2(sK9,sK10),k4_partfun1(sK9,sK10))),sK10) = iProver_top ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_12643,c_9063]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(contradiction,plain,
% 3.84/1.00      ( $false ),
% 3.84/1.00      inference(minisat,
% 3.84/1.00                [status(thm)],
% 3.84/1.00                [c_18780,c_15252,c_12852,c_12851,c_12850,c_7527,c_35]) ).
% 3.84/1.00  
% 3.84/1.00  
% 3.84/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.84/1.00  
% 3.84/1.00  ------                               Statistics
% 3.84/1.00  
% 3.84/1.00  ------ General
% 3.84/1.00  
% 3.84/1.00  abstr_ref_over_cycles:                  0
% 3.84/1.00  abstr_ref_under_cycles:                 0
% 3.84/1.00  gc_basic_clause_elim:                   0
% 3.84/1.00  forced_gc_time:                         0
% 3.84/1.00  parsing_time:                           0.007
% 3.84/1.00  unif_index_cands_time:                  0.
% 3.84/1.00  unif_index_add_time:                    0.
% 3.84/1.00  orderings_time:                         0.
% 3.84/1.00  out_proof_time:                         0.009
% 3.84/1.00  total_time:                             0.416
% 3.84/1.00  num_of_symbols:                         50
% 3.84/1.00  num_of_terms:                           16389
% 3.84/1.00  
% 3.84/1.00  ------ Preprocessing
% 3.84/1.00  
% 3.84/1.00  num_of_splits:                          0
% 3.84/1.00  num_of_split_atoms:                     0
% 3.84/1.00  num_of_reused_defs:                     0
% 3.84/1.00  num_eq_ax_congr_red:                    69
% 3.84/1.00  num_of_sem_filtered_clauses:            1
% 3.84/1.00  num_of_subtypes:                        0
% 3.84/1.00  monotx_restored_types:                  0
% 3.84/1.00  sat_num_of_epr_types:                   0
% 3.84/1.00  sat_num_of_non_cyclic_types:            0
% 3.84/1.00  sat_guarded_non_collapsed_types:        0
% 3.84/1.00  num_pure_diseq_elim:                    0
% 3.84/1.00  simp_replaced_by:                       0
% 3.84/1.00  res_preprocessed:                       163
% 3.84/1.00  prep_upred:                             0
% 3.84/1.00  prep_unflattend:                        198
% 3.84/1.00  smt_new_axioms:                         0
% 3.84/1.00  pred_elim_cands:                        6
% 3.84/1.00  pred_elim:                              0
% 3.84/1.00  pred_elim_cl:                           0
% 3.84/1.00  pred_elim_cycles:                       8
% 3.84/1.00  merged_defs:                            0
% 3.84/1.00  merged_defs_ncl:                        0
% 3.84/1.00  bin_hyper_res:                          0
% 3.84/1.00  prep_cycles:                            4
% 3.84/1.00  pred_elim_time:                         0.063
% 3.84/1.00  splitting_time:                         0.
% 3.84/1.00  sem_filter_time:                        0.
% 3.84/1.00  monotx_time:                            0.
% 3.84/1.00  subtype_inf_time:                       0.
% 3.84/1.00  
% 3.84/1.00  ------ Problem properties
% 3.84/1.00  
% 3.84/1.00  clauses:                                34
% 3.84/1.00  conjectures:                            1
% 3.84/1.00  epr:                                    3
% 3.84/1.00  horn:                                   23
% 3.84/1.00  ground:                                 1
% 3.84/1.00  unary:                                  4
% 3.84/1.00  binary:                                 4
% 3.84/1.00  lits:                                   101
% 3.84/1.00  lits_eq:                                10
% 3.84/1.00  fd_pure:                                0
% 3.84/1.00  fd_pseudo:                              0
% 3.84/1.00  fd_cond:                                0
% 3.84/1.00  fd_pseudo_cond:                         3
% 3.84/1.00  ac_symbols:                             0
% 3.84/1.00  
% 3.84/1.00  ------ Propositional Solver
% 3.84/1.00  
% 3.84/1.00  prop_solver_calls:                      31
% 3.84/1.00  prop_fast_solver_calls:                 3058
% 3.84/1.00  smt_solver_calls:                       0
% 3.84/1.00  smt_fast_solver_calls:                  0
% 3.84/1.00  prop_num_of_clauses:                    6573
% 3.84/1.00  prop_preprocess_simplified:             14914
% 3.84/1.00  prop_fo_subsumed:                       93
% 3.84/1.00  prop_solver_time:                       0.
% 3.84/1.00  smt_solver_time:                        0.
% 3.84/1.00  smt_fast_solver_time:                   0.
% 3.84/1.00  prop_fast_solver_time:                  0.
% 3.84/1.00  prop_unsat_core_time:                   0.
% 3.84/1.00  
% 3.84/1.00  ------ QBF
% 3.84/1.00  
% 3.84/1.00  qbf_q_res:                              0
% 3.84/1.00  qbf_num_tautologies:                    0
% 3.84/1.00  qbf_prep_cycles:                        0
% 3.84/1.00  
% 3.84/1.00  ------ BMC1
% 3.84/1.00  
% 3.84/1.00  bmc1_current_bound:                     -1
% 3.84/1.00  bmc1_last_solved_bound:                 -1
% 3.84/1.00  bmc1_unsat_core_size:                   -1
% 3.84/1.00  bmc1_unsat_core_parents_size:           -1
% 3.84/1.00  bmc1_merge_next_fun:                    0
% 3.84/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.84/1.00  
% 3.84/1.00  ------ Instantiation
% 3.84/1.00  
% 3.84/1.00  inst_num_of_clauses:                    1254
% 3.84/1.00  inst_num_in_passive:                    733
% 3.84/1.00  inst_num_in_active:                     417
% 3.84/1.00  inst_num_in_unprocessed:                104
% 3.84/1.00  inst_num_of_loops:                      740
% 3.84/1.00  inst_num_of_learning_restarts:          0
% 3.84/1.00  inst_num_moves_active_passive:          320
% 3.84/1.00  inst_lit_activity:                      0
% 3.84/1.00  inst_lit_activity_moves:                0
% 3.84/1.00  inst_num_tautologies:                   0
% 3.84/1.00  inst_num_prop_implied:                  0
% 3.84/1.00  inst_num_existing_simplified:           0
% 3.84/1.00  inst_num_eq_res_simplified:             0
% 3.84/1.00  inst_num_child_elim:                    0
% 3.84/1.00  inst_num_of_dismatching_blockings:      713
% 3.84/1.00  inst_num_of_non_proper_insts:           1636
% 3.84/1.00  inst_num_of_duplicates:                 0
% 3.84/1.00  inst_inst_num_from_inst_to_res:         0
% 3.84/1.00  inst_dismatching_checking_time:         0.
% 3.84/1.00  
% 3.84/1.00  ------ Resolution
% 3.84/1.00  
% 3.84/1.00  res_num_of_clauses:                     0
% 3.84/1.00  res_num_in_passive:                     0
% 3.84/1.00  res_num_in_active:                      0
% 3.84/1.00  res_num_of_loops:                       167
% 3.84/1.00  res_forward_subset_subsumed:            271
% 3.84/1.00  res_backward_subset_subsumed:           0
% 3.84/1.00  res_forward_subsumed:                   0
% 3.84/1.00  res_backward_subsumed:                  0
% 3.84/1.00  res_forward_subsumption_resolution:     8
% 3.84/1.00  res_backward_subsumption_resolution:    0
% 3.84/1.00  res_clause_to_clause_subsumption:       2048
% 3.84/1.00  res_orphan_elimination:                 0
% 3.84/1.00  res_tautology_del:                      110
% 3.84/1.00  res_num_eq_res_simplified:              0
% 3.84/1.00  res_num_sel_changes:                    0
% 3.84/1.00  res_moves_from_active_to_pass:          0
% 3.84/1.00  
% 3.84/1.00  ------ Superposition
% 3.84/1.00  
% 3.84/1.00  sup_time_total:                         0.
% 3.84/1.00  sup_time_generating:                    0.
% 3.84/1.00  sup_time_sim_full:                      0.
% 3.84/1.00  sup_time_sim_immed:                     0.
% 3.84/1.00  
% 3.84/1.00  sup_num_of_clauses:                     463
% 3.84/1.00  sup_num_in_active:                      139
% 3.84/1.00  sup_num_in_passive:                     324
% 3.84/1.00  sup_num_of_loops:                       146
% 3.84/1.00  sup_fw_superposition:                   199
% 3.84/1.00  sup_bw_superposition:                   330
% 3.84/1.00  sup_immediate_simplified:               48
% 3.84/1.00  sup_given_eliminated:                   0
% 3.84/1.00  comparisons_done:                       0
% 3.84/1.00  comparisons_avoided:                    5
% 3.84/1.00  
% 3.84/1.00  ------ Simplifications
% 3.84/1.00  
% 3.84/1.00  
% 3.84/1.00  sim_fw_subset_subsumed:                 10
% 3.84/1.00  sim_bw_subset_subsumed:                 13
% 3.84/1.00  sim_fw_subsumed:                        6
% 3.84/1.00  sim_bw_subsumed:                        0
% 3.84/1.00  sim_fw_subsumption_res:                 0
% 3.84/1.00  sim_bw_subsumption_res:                 0
% 3.84/1.00  sim_tautology_del:                      7
% 3.84/1.00  sim_eq_tautology_del:                   22
% 3.84/1.00  sim_eq_res_simp:                        0
% 3.84/1.00  sim_fw_demodulated:                     5
% 3.84/1.00  sim_bw_demodulated:                     8
% 3.84/1.00  sim_light_normalised:                   41
% 3.84/1.00  sim_joinable_taut:                      0
% 3.84/1.00  sim_joinable_simp:                      0
% 3.84/1.00  sim_ac_normalised:                      0
% 3.84/1.00  sim_smt_subsumption:                    0
% 3.84/1.00  
%------------------------------------------------------------------------------
