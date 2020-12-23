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
% DateTime   : Thu Dec  3 12:08:16 EST 2020

% Result     : Theorem 7.31s
% Output     : CNFRefutation 7.31s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 726 expanded)
%              Number of clauses        :   84 ( 249 expanded)
%              Number of leaves         :   19 ( 196 expanded)
%              Depth                    :   18
%              Number of atoms          :  674 (4845 expanded)
%              Number of equality atoms :  249 (1465 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f9,plain,(
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
    inference(flattening,[],[f8])).

fof(f19,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f20,plain,(
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
    inference(rectify,[],[f19])).

fof(f23,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X5)) = X5
        & r2_hidden(sK4(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X1)) = X2
        & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
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
              ( k1_funct_1(X0,X3) != sK2(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK2(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK2(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK2(X0,X1),X1) )
              & ( ( k1_funct_1(X0,sK3(X0,X1)) = sK2(X0,X1)
                  & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK2(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK4(X0,X5)) = X5
                    & r2_hidden(sK4(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f20,f23,f22,f21])).

fof(f41,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f67,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f68,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f67])).

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

fof(f15,plain,(
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

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f15])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f17])).

fof(f36,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
     => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X2,k1_funct_2(X0,X1))
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2) )
      & r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f34,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2) )
        & r2_hidden(X2,k1_funct_2(X0,X1)) )
   => ( ( ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10)))
        | ~ v1_funct_2(sK11,sK9,sK10)
        | ~ v1_funct_1(sK11) )
      & r2_hidden(sK11,k1_funct_2(sK9,sK10)) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ( ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10)))
      | ~ v1_funct_2(sK11,sK9,sK10)
      | ~ v1_funct_1(sK11) )
    & r2_hidden(sK11,k1_funct_2(sK9,sK10)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11])],[f12,f34])).

fof(f65,plain,(
    r2_hidden(sK11,k1_funct_2(sK9,sK10)) ),
    inference(cnf_transformation,[],[f35])).

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

fof(f13,plain,(
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

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_2(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f3,f13])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k1_funct_2(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k1_funct_2(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f74,plain,(
    ! [X0,X1] : sP0(X1,X0,k1_funct_2(X0,X1)) ),
    inference(equality_resolution,[],[f57])).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f26,plain,(
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
    inference(rectify,[],[f25])).

fof(f29,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r1_tarski(k2_relat_1(X8),X0)
          & k1_relat_1(X8) = X1
          & X6 = X8
          & v1_funct_1(X8)
          & v1_relat_1(X8) )
     => ( r1_tarski(k2_relat_1(sK7(X0,X1,X6)),X0)
        & k1_relat_1(sK7(X0,X1,X6)) = X1
        & sK7(X0,X1,X6) = X6
        & v1_funct_1(sK7(X0,X1,X6))
        & v1_relat_1(sK7(X0,X1,X6)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r1_tarski(k2_relat_1(X5),X0)
          & k1_relat_1(X5) = X1
          & X3 = X5
          & v1_funct_1(X5)
          & v1_relat_1(X5) )
     => ( r1_tarski(k2_relat_1(sK6(X0,X1,X2)),X0)
        & k1_relat_1(sK6(X0,X1,X2)) = X1
        & sK6(X0,X1,X2) = X3
        & v1_funct_1(sK6(X0,X1,X2))
        & v1_relat_1(sK6(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
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
              | sK5(X0,X1,X2) != X4
              | ~ v1_funct_1(X4)
              | ~ v1_relat_1(X4) )
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r1_tarski(k2_relat_1(X5),X0)
              & k1_relat_1(X5) = X1
              & sK5(X0,X1,X2) = X5
              & v1_funct_1(X5)
              & v1_relat_1(X5) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ! [X4] :
                ( ~ r1_tarski(k2_relat_1(X4),X0)
                | k1_relat_1(X4) != X1
                | sK5(X0,X1,X2) != X4
                | ~ v1_funct_1(X4)
                | ~ v1_relat_1(X4) )
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( ( r1_tarski(k2_relat_1(sK6(X0,X1,X2)),X0)
              & k1_relat_1(sK6(X0,X1,X2)) = X1
              & sK5(X0,X1,X2) = sK6(X0,X1,X2)
              & v1_funct_1(sK6(X0,X1,X2))
              & v1_relat_1(sK6(X0,X1,X2)) )
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X2)
              | ! [X7] :
                  ( ~ r1_tarski(k2_relat_1(X7),X0)
                  | k1_relat_1(X7) != X1
                  | X6 != X7
                  | ~ v1_funct_1(X7)
                  | ~ v1_relat_1(X7) ) )
            & ( ( r1_tarski(k2_relat_1(sK7(X0,X1,X6)),X0)
                & k1_relat_1(sK7(X0,X1,X6)) = X1
                & sK7(X0,X1,X6) = X6
                & v1_funct_1(sK7(X0,X1,X6))
                & v1_relat_1(sK7(X0,X1,X6)) )
              | ~ r2_hidden(X6,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f26,f29,f28,f27])).

fof(f48,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_relat_1(sK7(X0,X1,X6)) = X1
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f47,plain,(
    ! [X6,X2,X0,X1] :
      ( sK7(X0,X1,X6) = X6
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( ! [X3] :
              ( r2_hidden(X3,X0)
             => r2_hidden(k1_funct_1(X2,X3),X1) )
          & k1_relat_1(X2) = X0 )
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(k1_funct_1(X2,sK8(X0,X1,X2)),X1)
        & r2_hidden(sK8(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ( ~ r2_hidden(k1_funct_1(X2,sK8(X0,X1,X2)),X1)
        & r2_hidden(sK8(X0,X1,X2),X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f11,f32])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ r2_hidden(k1_funct_1(X2,sK8(X0,X1,X2)),X1)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f77,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_relat_1(X2),X1)
      | ~ r2_hidden(k1_funct_1(X2,sK8(k1_relat_1(X2),X1,X2)),X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f62])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(k1_funct_1(X2,sK8(X0,X1,X2)),X1)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f75,plain,(
    ! [X2,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))
      | ~ r2_hidden(k1_funct_1(X2,sK8(k1_relat_1(X2),X1,X2)),X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f64])).

fof(f66,plain,
    ( ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10)))
    | ~ v1_funct_2(sK11,sK9,sK10)
    | ~ v1_funct_1(sK11) ),
    inference(cnf_transformation,[],[f35])).

fof(f46,plain,(
    ! [X6,X2,X0,X1] :
      ( v1_funct_1(sK7(X0,X1,X6))
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f45,plain,(
    ! [X6,X2,X0,X1] :
      ( v1_relat_1(sK7(X0,X1,X6))
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f49,plain,(
    ! [X6,X2,X0,X1] :
      ( r1_tarski(k2_relat_1(sK7(X0,X1,X6)),X0)
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_hidden(sK8(X0,X1,X2),X0)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f76,plain,(
    ! [X2,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))
      | r2_hidden(sK8(k1_relat_1(X2),X1,X2),k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f63])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | r2_hidden(sK8(X0,X1,X2),X0)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f78,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_relat_1(X2),X1)
      | r2_hidden(sK8(k1_relat_1(X2),X1,X2),k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f61])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_6986,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_6990,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_9633,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k1_funct_1(X1,X0),X2) = iProver_top
    | r1_tarski(k2_relat_1(X1),X2) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_6986,c_6990])).

cnf(c_30,negated_conjecture,
    ( r2_hidden(sK11,k1_funct_2(sK9,sK10)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_6969,plain,
    ( r2_hidden(sK11,k1_funct_2(sK9,sK10)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_22,plain,
    ( sP0(X0,X1,k1_funct_2(X1,X0)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_6970,plain,
    ( sP0(X0,X1,k1_funct_2(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_17,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,X2)
    | k1_relat_1(sK7(X0,X1,X3)) = X1 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_6975,plain,
    ( k1_relat_1(sK7(X0,X1,X2)) = X1
    | sP0(X0,X1,X3) != iProver_top
    | r2_hidden(X2,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_7931,plain,
    ( k1_relat_1(sK7(X0,X1,X2)) = X1
    | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6970,c_6975])).

cnf(c_8368,plain,
    ( k1_relat_1(sK7(sK10,sK9,sK11)) = sK9 ),
    inference(superposition,[status(thm)],[c_6969,c_7931])).

cnf(c_18,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,X2)
    | sK7(X0,X1,X3) = X3 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_6974,plain,
    ( sK7(X0,X1,X2) = X2
    | sP0(X0,X1,X3) != iProver_top
    | r2_hidden(X2,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_7697,plain,
    ( sK7(X0,X1,X2) = X2
    | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6970,c_6974])).

cnf(c_7745,plain,
    ( sK7(sK10,sK9,sK11) = sK11 ),
    inference(superposition,[status(thm)],[c_6969,c_7697])).

cnf(c_8370,plain,
    ( k1_relat_1(sK11) = sK9 ),
    inference(light_normalisation,[status(thm)],[c_8368,c_7745])).

cnf(c_25,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r2_hidden(k1_funct_1(X0,sK8(k1_relat_1(X0),X1,X0)),X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_23,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r2_hidden(k1_funct_1(X0,sK8(k1_relat_1(X0),X1,X0)),X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_29,negated_conjecture,
    ( ~ v1_funct_2(sK11,sK9,sK10)
    | ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10)))
    | ~ v1_funct_1(sK11) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_363,plain,
    ( ~ v1_funct_2(sK11,sK9,sK10)
    | ~ r2_hidden(k1_funct_1(X0,sK8(k1_relat_1(X0),X1,X0)),X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK11)
    | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)) != k1_zfmisc_1(k2_zfmisc_1(sK9,sK10))
    | sK11 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_29])).

cnf(c_364,plain,
    ( ~ v1_funct_2(sK11,sK9,sK10)
    | ~ r2_hidden(k1_funct_1(sK11,sK8(k1_relat_1(sK11),X0,sK11)),X0)
    | ~ v1_relat_1(sK11)
    | ~ v1_funct_1(sK11)
    | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK11),X0)) != k1_zfmisc_1(k2_zfmisc_1(sK9,sK10)) ),
    inference(unflattening,[status(thm)],[c_363])).

cnf(c_444,plain,
    ( ~ r2_hidden(k1_funct_1(X0,sK8(k1_relat_1(X0),X1,X0)),X1)
    | ~ r2_hidden(k1_funct_1(sK11,sK8(k1_relat_1(sK11),X2,sK11)),X2)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK11)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK11)
    | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK11),X2)) != k1_zfmisc_1(k2_zfmisc_1(sK9,sK10))
    | k1_relat_1(X0) != sK9
    | sK10 != X1
    | sK11 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_364])).

cnf(c_445,plain,
    ( ~ r2_hidden(k1_funct_1(sK11,sK8(k1_relat_1(sK11),X0,sK11)),X0)
    | ~ r2_hidden(k1_funct_1(sK11,sK8(k1_relat_1(sK11),sK10,sK11)),sK10)
    | ~ v1_relat_1(sK11)
    | ~ v1_funct_1(sK11)
    | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK11),X0)) != k1_zfmisc_1(k2_zfmisc_1(sK9,sK10))
    | k1_relat_1(sK11) != sK9 ),
    inference(unflattening,[status(thm)],[c_444])).

cnf(c_6425,plain,
    ( ~ r2_hidden(k1_funct_1(sK11,sK8(k1_relat_1(sK11),X0,sK11)),X0)
    | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK11),X0)) != k1_zfmisc_1(k2_zfmisc_1(sK9,sK10))
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_445])).

cnf(c_6964,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK11),X0)) != k1_zfmisc_1(k2_zfmisc_1(sK9,sK10))
    | r2_hidden(k1_funct_1(sK11,sK8(k1_relat_1(sK11),X0,sK11)),X0) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6425])).

cnf(c_8405,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK9,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK9,sK10))
    | r2_hidden(k1_funct_1(sK11,sK8(sK9,X0,sK11)),X0) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(demodulation,[status(thm)],[c_8370,c_6964])).

cnf(c_8613,plain,
    ( r2_hidden(k1_funct_1(sK11,sK8(sK9,sK10,sK11)),sK10) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_8405])).

cnf(c_31,plain,
    ( r2_hidden(sK11,k1_funct_2(sK9,sK10)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_6430,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_6459,plain,
    ( sK11 = sK11 ),
    inference(instantiation,[status(thm)],[c_6430])).

cnf(c_19,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,X2)
    | v1_funct_1(sK7(X0,X1,X3)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_7281,plain,
    ( ~ sP0(X0,X1,k1_funct_2(sK9,sK10))
    | ~ r2_hidden(sK11,k1_funct_2(sK9,sK10))
    | v1_funct_1(sK7(X0,X1,sK11)) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_7381,plain,
    ( ~ sP0(sK10,sK9,k1_funct_2(sK9,sK10))
    | ~ r2_hidden(sK11,k1_funct_2(sK9,sK10))
    | v1_funct_1(sK7(sK10,sK9,sK11)) ),
    inference(instantiation,[status(thm)],[c_7281])).

cnf(c_7383,plain,
    ( sP0(sK10,sK9,k1_funct_2(sK9,sK10)) != iProver_top
    | r2_hidden(sK11,k1_funct_2(sK9,sK10)) != iProver_top
    | v1_funct_1(sK7(sK10,sK9,sK11)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7381])).

cnf(c_7382,plain,
    ( sP0(sK10,sK9,k1_funct_2(sK9,sK10)) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_7385,plain,
    ( sP0(sK10,sK9,k1_funct_2(sK9,sK10)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7382])).

cnf(c_20,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,X2)
    | v1_relat_1(sK7(X0,X1,X3)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_7286,plain,
    ( ~ sP0(X0,X1,k1_funct_2(sK9,sK10))
    | ~ r2_hidden(sK11,k1_funct_2(sK9,sK10))
    | v1_relat_1(sK7(X0,X1,sK11)) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_7452,plain,
    ( ~ sP0(sK10,sK9,k1_funct_2(sK9,sK10))
    | ~ r2_hidden(sK11,k1_funct_2(sK9,sK10))
    | v1_relat_1(sK7(sK10,sK9,sK11)) ),
    inference(instantiation,[status(thm)],[c_7286])).

cnf(c_7454,plain,
    ( sP0(sK10,sK9,k1_funct_2(sK9,sK10)) != iProver_top
    | r2_hidden(sK11,k1_funct_2(sK9,sK10)) != iProver_top
    | v1_relat_1(sK7(sK10,sK9,sK11)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7452])).

cnf(c_7316,plain,
    ( ~ sP0(X0,X1,k1_funct_2(sK9,sK10))
    | ~ r2_hidden(sK11,k1_funct_2(sK9,sK10))
    | sK7(X0,X1,sK11) = sK11 ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_7451,plain,
    ( ~ sP0(sK10,sK9,k1_funct_2(sK9,sK10))
    | ~ r2_hidden(sK11,k1_funct_2(sK9,sK10))
    | sK7(sK10,sK9,sK11) = sK11 ),
    inference(instantiation,[status(thm)],[c_7316])).

cnf(c_6437,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_7462,plain,
    ( v1_funct_1(X0)
    | ~ v1_funct_1(sK7(sK10,sK9,sK11))
    | X0 != sK7(sK10,sK9,sK11) ),
    inference(instantiation,[status(thm)],[c_6437])).

cnf(c_7463,plain,
    ( X0 != sK7(sK10,sK9,sK11)
    | v1_funct_1(X0) = iProver_top
    | v1_funct_1(sK7(sK10,sK9,sK11)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7462])).

cnf(c_7465,plain,
    ( sK11 != sK7(sK10,sK9,sK11)
    | v1_funct_1(sK7(sK10,sK9,sK11)) != iProver_top
    | v1_funct_1(sK11) = iProver_top ),
    inference(instantiation,[status(thm)],[c_7463])).

cnf(c_6438,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_7626,plain,
    ( v1_relat_1(X0)
    | ~ v1_relat_1(sK7(sK10,sK9,sK11))
    | X0 != sK7(sK10,sK9,sK11) ),
    inference(instantiation,[status(thm)],[c_6438])).

cnf(c_7627,plain,
    ( X0 != sK7(sK10,sK9,sK11)
    | v1_relat_1(X0) = iProver_top
    | v1_relat_1(sK7(sK10,sK9,sK11)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7626])).

cnf(c_7629,plain,
    ( sK11 != sK7(sK10,sK9,sK11)
    | v1_relat_1(sK7(sK10,sK9,sK11)) != iProver_top
    | v1_relat_1(sK11) = iProver_top ),
    inference(instantiation,[status(thm)],[c_7627])).

cnf(c_6431,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_7710,plain,
    ( X0 != X1
    | X0 = sK7(sK10,sK9,sK11)
    | sK7(sK10,sK9,sK11) != X1 ),
    inference(instantiation,[status(thm)],[c_6431])).

cnf(c_7711,plain,
    ( sK7(sK10,sK9,sK11) != sK11
    | sK11 = sK7(sK10,sK9,sK11)
    | sK11 != sK11 ),
    inference(instantiation,[status(thm)],[c_7710])).

cnf(c_6426,plain,
    ( ~ r2_hidden(k1_funct_1(sK11,sK8(k1_relat_1(sK11),sK10,sK11)),sK10)
    | ~ v1_relat_1(sK11)
    | ~ v1_funct_1(sK11)
    | sP1_iProver_split
    | k1_relat_1(sK11) != sK9 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_445])).

cnf(c_6963,plain,
    ( k1_relat_1(sK11) != sK9
    | r2_hidden(k1_funct_1(sK11,sK8(k1_relat_1(sK11),sK10,sK11)),sK10) != iProver_top
    | v1_relat_1(sK11) != iProver_top
    | v1_funct_1(sK11) != iProver_top
    | sP1_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6426])).

cnf(c_8403,plain,
    ( sK9 != sK9
    | r2_hidden(k1_funct_1(sK11,sK8(sK9,sK10,sK11)),sK10) != iProver_top
    | v1_relat_1(sK11) != iProver_top
    | v1_funct_1(sK11) != iProver_top
    | sP1_iProver_split = iProver_top ),
    inference(demodulation,[status(thm)],[c_8370,c_6963])).

cnf(c_8428,plain,
    ( r2_hidden(k1_funct_1(sK11,sK8(sK9,sK10,sK11)),sK10) != iProver_top
    | v1_relat_1(sK11) != iProver_top
    | v1_funct_1(sK11) != iProver_top
    | sP1_iProver_split = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_8403])).

cnf(c_9238,plain,
    ( r2_hidden(k1_funct_1(sK11,sK8(sK9,sK10,sK11)),sK10) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8613,c_30,c_31,c_6459,c_7383,c_7382,c_7385,c_7454,c_7451,c_7465,c_7629,c_7711,c_8428])).

cnf(c_37573,plain,
    ( r2_hidden(sK8(sK9,sK10,sK11),k1_relat_1(sK11)) != iProver_top
    | r1_tarski(k2_relat_1(sK11),sK10) != iProver_top
    | v1_relat_1(sK11) != iProver_top
    | v1_funct_1(sK11) != iProver_top ),
    inference(superposition,[status(thm)],[c_9633,c_9238])).

cnf(c_37648,plain,
    ( r2_hidden(sK8(sK9,sK10,sK11),sK9) != iProver_top
    | r1_tarski(k2_relat_1(sK11),sK10) != iProver_top
    | v1_relat_1(sK11) != iProver_top
    | v1_funct_1(sK11) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_37573,c_8370])).

cnf(c_16,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,X2)
    | r1_tarski(k2_relat_1(sK7(X0,X1,X3)),X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_6976,plain,
    ( sP0(X0,X1,X2) != iProver_top
    | r2_hidden(X3,X2) != iProver_top
    | r1_tarski(k2_relat_1(sK7(X0,X1,X3)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_8762,plain,
    ( r2_hidden(X0,k1_funct_2(X1,X2)) != iProver_top
    | r1_tarski(k2_relat_1(sK7(X2,X1,X0)),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_6970,c_6976])).

cnf(c_10927,plain,
    ( r2_hidden(sK11,k1_funct_2(sK9,sK10)) != iProver_top
    | r1_tarski(k2_relat_1(sK11),sK10) = iProver_top ),
    inference(superposition,[status(thm)],[c_7745,c_8762])).

cnf(c_24,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | r2_hidden(sK8(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_342,plain,
    ( ~ v1_funct_2(sK11,sK9,sK10)
    | r2_hidden(sK8(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK11)
    | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)) != k1_zfmisc_1(k2_zfmisc_1(sK9,sK10))
    | sK11 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_29])).

cnf(c_343,plain,
    ( ~ v1_funct_2(sK11,sK9,sK10)
    | r2_hidden(sK8(k1_relat_1(sK11),X0,sK11),k1_relat_1(sK11))
    | ~ v1_relat_1(sK11)
    | ~ v1_funct_1(sK11)
    | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK11),X0)) != k1_zfmisc_1(k2_zfmisc_1(sK9,sK10)) ),
    inference(unflattening,[status(thm)],[c_342])).

cnf(c_468,plain,
    ( r2_hidden(sK8(k1_relat_1(sK11),X0,sK11),k1_relat_1(sK11))
    | ~ r2_hidden(k1_funct_1(X1,sK8(k1_relat_1(X1),X2,X1)),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(sK11)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(sK11)
    | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK11),X0)) != k1_zfmisc_1(k2_zfmisc_1(sK9,sK10))
    | k1_relat_1(X1) != sK9
    | sK10 != X2
    | sK11 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_343])).

cnf(c_469,plain,
    ( r2_hidden(sK8(k1_relat_1(sK11),X0,sK11),k1_relat_1(sK11))
    | ~ r2_hidden(k1_funct_1(sK11,sK8(k1_relat_1(sK11),sK10,sK11)),sK10)
    | ~ v1_relat_1(sK11)
    | ~ v1_funct_1(sK11)
    | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK11),X0)) != k1_zfmisc_1(k2_zfmisc_1(sK9,sK10))
    | k1_relat_1(sK11) != sK9 ),
    inference(unflattening,[status(thm)],[c_468])).

cnf(c_6423,plain,
    ( r2_hidden(sK8(k1_relat_1(sK11),X0,sK11),k1_relat_1(sK11))
    | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK11),X0)) != k1_zfmisc_1(k2_zfmisc_1(sK9,sK10))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_469])).

cnf(c_6962,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK11),X0)) != k1_zfmisc_1(k2_zfmisc_1(sK9,sK10))
    | r2_hidden(sK8(k1_relat_1(sK11),X0,sK11),k1_relat_1(sK11)) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6423])).

cnf(c_8406,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK9,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK9,sK10))
    | r2_hidden(sK8(sK9,X0,sK11),sK9) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(demodulation,[status(thm)],[c_8370,c_6962])).

cnf(c_8607,plain,
    ( r2_hidden(sK8(sK9,sK10,sK11),sK9) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_8406])).

cnf(c_26,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | r2_hidden(sK8(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_420,plain,
    ( r2_hidden(sK8(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
    | r2_hidden(sK8(k1_relat_1(sK11),X2,sK11),k1_relat_1(sK11))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK11)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK11)
    | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK11),X2)) != k1_zfmisc_1(k2_zfmisc_1(sK9,sK10))
    | k1_relat_1(X0) != sK9
    | sK10 != X1
    | sK11 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_343])).

cnf(c_421,plain,
    ( r2_hidden(sK8(k1_relat_1(sK11),X0,sK11),k1_relat_1(sK11))
    | r2_hidden(sK8(k1_relat_1(sK11),sK10,sK11),k1_relat_1(sK11))
    | ~ v1_relat_1(sK11)
    | ~ v1_funct_1(sK11)
    | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK11),X0)) != k1_zfmisc_1(k2_zfmisc_1(sK9,sK10))
    | k1_relat_1(sK11) != sK9 ),
    inference(unflattening,[status(thm)],[c_420])).

cnf(c_6427,plain,
    ( r2_hidden(sK8(k1_relat_1(sK11),sK10,sK11),k1_relat_1(sK11))
    | ~ v1_relat_1(sK11)
    | ~ v1_funct_1(sK11)
    | sP0_iProver_split
    | k1_relat_1(sK11) != sK9 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_421])).

cnf(c_6965,plain,
    ( k1_relat_1(sK11) != sK9
    | r2_hidden(sK8(k1_relat_1(sK11),sK10,sK11),k1_relat_1(sK11)) = iProver_top
    | v1_relat_1(sK11) != iProver_top
    | v1_funct_1(sK11) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6427])).

cnf(c_8402,plain,
    ( sK9 != sK9
    | r2_hidden(sK8(sK9,sK10,sK11),sK9) = iProver_top
    | v1_relat_1(sK11) != iProver_top
    | v1_funct_1(sK11) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(demodulation,[status(thm)],[c_8370,c_6965])).

cnf(c_8437,plain,
    ( r2_hidden(sK8(sK9,sK10,sK11),sK9) = iProver_top
    | v1_relat_1(sK11) != iProver_top
    | v1_funct_1(sK11) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_8402])).

cnf(c_8749,plain,
    ( r2_hidden(sK8(sK9,sK10,sK11),sK9) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8607,c_30,c_31,c_6459,c_7383,c_7382,c_7385,c_7454,c_7451,c_7465,c_7629,c_7711,c_8437])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_37648,c_10927,c_8749,c_7711,c_7629,c_7465,c_7451,c_7454,c_7385,c_7382,c_7383,c_6459,c_31,c_30])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:03:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 7.31/1.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.31/1.50  
% 7.31/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.31/1.50  
% 7.31/1.50  ------  iProver source info
% 7.31/1.50  
% 7.31/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.31/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.31/1.50  git: non_committed_changes: false
% 7.31/1.50  git: last_make_outside_of_git: false
% 7.31/1.50  
% 7.31/1.50  ------ 
% 7.31/1.50  
% 7.31/1.50  ------ Input Options
% 7.31/1.50  
% 7.31/1.50  --out_options                           all
% 7.31/1.50  --tptp_safe_out                         true
% 7.31/1.50  --problem_path                          ""
% 7.31/1.50  --include_path                          ""
% 7.31/1.50  --clausifier                            res/vclausify_rel
% 7.31/1.50  --clausifier_options                    --mode clausify
% 7.31/1.50  --stdin                                 false
% 7.31/1.50  --stats_out                             all
% 7.31/1.50  
% 7.31/1.50  ------ General Options
% 7.31/1.50  
% 7.31/1.50  --fof                                   false
% 7.31/1.50  --time_out_real                         305.
% 7.31/1.50  --time_out_virtual                      -1.
% 7.31/1.50  --symbol_type_check                     false
% 7.31/1.50  --clausify_out                          false
% 7.31/1.50  --sig_cnt_out                           false
% 7.31/1.50  --trig_cnt_out                          false
% 7.31/1.50  --trig_cnt_out_tolerance                1.
% 7.31/1.50  --trig_cnt_out_sk_spl                   false
% 7.31/1.50  --abstr_cl_out                          false
% 7.31/1.50  
% 7.31/1.50  ------ Global Options
% 7.31/1.50  
% 7.31/1.50  --schedule                              default
% 7.31/1.50  --add_important_lit                     false
% 7.31/1.50  --prop_solver_per_cl                    1000
% 7.31/1.50  --min_unsat_core                        false
% 7.31/1.50  --soft_assumptions                      false
% 7.31/1.50  --soft_lemma_size                       3
% 7.31/1.50  --prop_impl_unit_size                   0
% 7.31/1.50  --prop_impl_unit                        []
% 7.31/1.50  --share_sel_clauses                     true
% 7.31/1.50  --reset_solvers                         false
% 7.31/1.50  --bc_imp_inh                            [conj_cone]
% 7.31/1.50  --conj_cone_tolerance                   3.
% 7.31/1.50  --extra_neg_conj                        none
% 7.31/1.50  --large_theory_mode                     true
% 7.31/1.50  --prolific_symb_bound                   200
% 7.31/1.50  --lt_threshold                          2000
% 7.31/1.50  --clause_weak_htbl                      true
% 7.31/1.50  --gc_record_bc_elim                     false
% 7.31/1.50  
% 7.31/1.50  ------ Preprocessing Options
% 7.31/1.50  
% 7.31/1.50  --preprocessing_flag                    true
% 7.31/1.50  --time_out_prep_mult                    0.1
% 7.31/1.50  --splitting_mode                        input
% 7.31/1.50  --splitting_grd                         true
% 7.31/1.50  --splitting_cvd                         false
% 7.31/1.50  --splitting_cvd_svl                     false
% 7.31/1.50  --splitting_nvd                         32
% 7.31/1.50  --sub_typing                            true
% 7.31/1.50  --prep_gs_sim                           true
% 7.31/1.50  --prep_unflatten                        true
% 7.31/1.50  --prep_res_sim                          true
% 7.31/1.50  --prep_upred                            true
% 7.31/1.50  --prep_sem_filter                       exhaustive
% 7.31/1.50  --prep_sem_filter_out                   false
% 7.31/1.50  --pred_elim                             true
% 7.31/1.50  --res_sim_input                         true
% 7.31/1.50  --eq_ax_congr_red                       true
% 7.31/1.50  --pure_diseq_elim                       true
% 7.31/1.50  --brand_transform                       false
% 7.31/1.50  --non_eq_to_eq                          false
% 7.31/1.50  --prep_def_merge                        true
% 7.31/1.50  --prep_def_merge_prop_impl              false
% 7.31/1.50  --prep_def_merge_mbd                    true
% 7.31/1.50  --prep_def_merge_tr_red                 false
% 7.31/1.50  --prep_def_merge_tr_cl                  false
% 7.31/1.50  --smt_preprocessing                     true
% 7.31/1.50  --smt_ac_axioms                         fast
% 7.31/1.50  --preprocessed_out                      false
% 7.31/1.50  --preprocessed_stats                    false
% 7.31/1.50  
% 7.31/1.50  ------ Abstraction refinement Options
% 7.31/1.50  
% 7.31/1.50  --abstr_ref                             []
% 7.31/1.50  --abstr_ref_prep                        false
% 7.31/1.50  --abstr_ref_until_sat                   false
% 7.31/1.50  --abstr_ref_sig_restrict                funpre
% 7.31/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.31/1.50  --abstr_ref_under                       []
% 7.31/1.50  
% 7.31/1.50  ------ SAT Options
% 7.31/1.50  
% 7.31/1.50  --sat_mode                              false
% 7.31/1.50  --sat_fm_restart_options                ""
% 7.31/1.50  --sat_gr_def                            false
% 7.31/1.50  --sat_epr_types                         true
% 7.31/1.50  --sat_non_cyclic_types                  false
% 7.31/1.50  --sat_finite_models                     false
% 7.31/1.50  --sat_fm_lemmas                         false
% 7.31/1.50  --sat_fm_prep                           false
% 7.31/1.50  --sat_fm_uc_incr                        true
% 7.31/1.50  --sat_out_model                         small
% 7.31/1.50  --sat_out_clauses                       false
% 7.31/1.50  
% 7.31/1.50  ------ QBF Options
% 7.31/1.50  
% 7.31/1.50  --qbf_mode                              false
% 7.31/1.50  --qbf_elim_univ                         false
% 7.31/1.50  --qbf_dom_inst                          none
% 7.31/1.50  --qbf_dom_pre_inst                      false
% 7.31/1.50  --qbf_sk_in                             false
% 7.31/1.50  --qbf_pred_elim                         true
% 7.31/1.50  --qbf_split                             512
% 7.31/1.50  
% 7.31/1.50  ------ BMC1 Options
% 7.31/1.50  
% 7.31/1.50  --bmc1_incremental                      false
% 7.31/1.50  --bmc1_axioms                           reachable_all
% 7.31/1.50  --bmc1_min_bound                        0
% 7.31/1.50  --bmc1_max_bound                        -1
% 7.31/1.50  --bmc1_max_bound_default                -1
% 7.31/1.50  --bmc1_symbol_reachability              true
% 7.31/1.50  --bmc1_property_lemmas                  false
% 7.31/1.50  --bmc1_k_induction                      false
% 7.31/1.50  --bmc1_non_equiv_states                 false
% 7.31/1.50  --bmc1_deadlock                         false
% 7.31/1.50  --bmc1_ucm                              false
% 7.31/1.50  --bmc1_add_unsat_core                   none
% 7.31/1.50  --bmc1_unsat_core_children              false
% 7.31/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.31/1.50  --bmc1_out_stat                         full
% 7.31/1.50  --bmc1_ground_init                      false
% 7.31/1.50  --bmc1_pre_inst_next_state              false
% 7.31/1.50  --bmc1_pre_inst_state                   false
% 7.31/1.50  --bmc1_pre_inst_reach_state             false
% 7.31/1.50  --bmc1_out_unsat_core                   false
% 7.31/1.50  --bmc1_aig_witness_out                  false
% 7.31/1.50  --bmc1_verbose                          false
% 7.31/1.50  --bmc1_dump_clauses_tptp                false
% 7.31/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.31/1.50  --bmc1_dump_file                        -
% 7.31/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.31/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.31/1.50  --bmc1_ucm_extend_mode                  1
% 7.31/1.50  --bmc1_ucm_init_mode                    2
% 7.31/1.50  --bmc1_ucm_cone_mode                    none
% 7.31/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.31/1.50  --bmc1_ucm_relax_model                  4
% 7.31/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.31/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.31/1.50  --bmc1_ucm_layered_model                none
% 7.31/1.50  --bmc1_ucm_max_lemma_size               10
% 7.31/1.50  
% 7.31/1.50  ------ AIG Options
% 7.31/1.50  
% 7.31/1.50  --aig_mode                              false
% 7.31/1.50  
% 7.31/1.50  ------ Instantiation Options
% 7.31/1.50  
% 7.31/1.50  --instantiation_flag                    true
% 7.31/1.50  --inst_sos_flag                         false
% 7.31/1.50  --inst_sos_phase                        true
% 7.31/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.31/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.31/1.50  --inst_lit_sel_side                     num_symb
% 7.31/1.50  --inst_solver_per_active                1400
% 7.31/1.50  --inst_solver_calls_frac                1.
% 7.31/1.50  --inst_passive_queue_type               priority_queues
% 7.31/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.31/1.50  --inst_passive_queues_freq              [25;2]
% 7.31/1.50  --inst_dismatching                      true
% 7.31/1.50  --inst_eager_unprocessed_to_passive     true
% 7.31/1.50  --inst_prop_sim_given                   true
% 7.31/1.50  --inst_prop_sim_new                     false
% 7.31/1.50  --inst_subs_new                         false
% 7.31/1.50  --inst_eq_res_simp                      false
% 7.31/1.50  --inst_subs_given                       false
% 7.31/1.50  --inst_orphan_elimination               true
% 7.31/1.50  --inst_learning_loop_flag               true
% 7.31/1.50  --inst_learning_start                   3000
% 7.31/1.50  --inst_learning_factor                  2
% 7.31/1.50  --inst_start_prop_sim_after_learn       3
% 7.31/1.50  --inst_sel_renew                        solver
% 7.31/1.50  --inst_lit_activity_flag                true
% 7.31/1.50  --inst_restr_to_given                   false
% 7.31/1.50  --inst_activity_threshold               500
% 7.31/1.50  --inst_out_proof                        true
% 7.31/1.50  
% 7.31/1.50  ------ Resolution Options
% 7.31/1.50  
% 7.31/1.50  --resolution_flag                       true
% 7.31/1.50  --res_lit_sel                           adaptive
% 7.31/1.50  --res_lit_sel_side                      none
% 7.31/1.50  --res_ordering                          kbo
% 7.31/1.50  --res_to_prop_solver                    active
% 7.31/1.50  --res_prop_simpl_new                    false
% 7.31/1.50  --res_prop_simpl_given                  true
% 7.31/1.50  --res_passive_queue_type                priority_queues
% 7.31/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.31/1.50  --res_passive_queues_freq               [15;5]
% 7.31/1.50  --res_forward_subs                      full
% 7.31/1.50  --res_backward_subs                     full
% 7.31/1.50  --res_forward_subs_resolution           true
% 7.31/1.50  --res_backward_subs_resolution          true
% 7.31/1.50  --res_orphan_elimination                true
% 7.31/1.50  --res_time_limit                        2.
% 7.31/1.50  --res_out_proof                         true
% 7.31/1.50  
% 7.31/1.50  ------ Superposition Options
% 7.31/1.50  
% 7.31/1.50  --superposition_flag                    true
% 7.31/1.50  --sup_passive_queue_type                priority_queues
% 7.31/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.31/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.31/1.50  --demod_completeness_check              fast
% 7.31/1.50  --demod_use_ground                      true
% 7.31/1.50  --sup_to_prop_solver                    passive
% 7.31/1.50  --sup_prop_simpl_new                    true
% 7.31/1.50  --sup_prop_simpl_given                  true
% 7.31/1.50  --sup_fun_splitting                     false
% 7.31/1.50  --sup_smt_interval                      50000
% 7.31/1.50  
% 7.31/1.50  ------ Superposition Simplification Setup
% 7.31/1.50  
% 7.31/1.50  --sup_indices_passive                   []
% 7.31/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.31/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.31/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.31/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.31/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.31/1.50  --sup_full_bw                           [BwDemod]
% 7.31/1.50  --sup_immed_triv                        [TrivRules]
% 7.31/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.31/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.31/1.50  --sup_immed_bw_main                     []
% 7.31/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.31/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.31/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.31/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.31/1.50  
% 7.31/1.50  ------ Combination Options
% 7.31/1.50  
% 7.31/1.50  --comb_res_mult                         3
% 7.31/1.50  --comb_sup_mult                         2
% 7.31/1.50  --comb_inst_mult                        10
% 7.31/1.50  
% 7.31/1.50  ------ Debug Options
% 7.31/1.50  
% 7.31/1.50  --dbg_backtrace                         false
% 7.31/1.50  --dbg_dump_prop_clauses                 false
% 7.31/1.50  --dbg_dump_prop_clauses_file            -
% 7.31/1.50  --dbg_out_stat                          false
% 7.31/1.50  ------ Parsing...
% 7.31/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.31/1.50  
% 7.31/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 7.31/1.50  
% 7.31/1.50  ------ Preprocessing... gs_s  sp: 4 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.31/1.50  
% 7.31/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.31/1.50  ------ Proving...
% 7.31/1.50  ------ Problem Properties 
% 7.31/1.50  
% 7.31/1.50  
% 7.31/1.50  clauses                                 32
% 7.31/1.50  conjectures                             1
% 7.31/1.50  EPR                                     1
% 7.31/1.50  Horn                                    22
% 7.31/1.50  unary                                   2
% 7.31/1.50  binary                                  3
% 7.31/1.50  lits                                    112
% 7.31/1.50  lits eq                                 20
% 7.31/1.50  fd_pure                                 0
% 7.31/1.50  fd_pseudo                               0
% 7.31/1.50  fd_cond                                 0
% 7.31/1.50  fd_pseudo_cond                          4
% 7.31/1.50  AC symbols                              0
% 7.31/1.50  
% 7.31/1.50  ------ Schedule dynamic 5 is on 
% 7.31/1.50  
% 7.31/1.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.31/1.50  
% 7.31/1.50  
% 7.31/1.50  ------ 
% 7.31/1.50  Current options:
% 7.31/1.50  ------ 
% 7.31/1.50  
% 7.31/1.50  ------ Input Options
% 7.31/1.50  
% 7.31/1.50  --out_options                           all
% 7.31/1.50  --tptp_safe_out                         true
% 7.31/1.50  --problem_path                          ""
% 7.31/1.50  --include_path                          ""
% 7.31/1.50  --clausifier                            res/vclausify_rel
% 7.31/1.50  --clausifier_options                    --mode clausify
% 7.31/1.50  --stdin                                 false
% 7.31/1.50  --stats_out                             all
% 7.31/1.50  
% 7.31/1.50  ------ General Options
% 7.31/1.50  
% 7.31/1.50  --fof                                   false
% 7.31/1.50  --time_out_real                         305.
% 7.31/1.50  --time_out_virtual                      -1.
% 7.31/1.50  --symbol_type_check                     false
% 7.31/1.50  --clausify_out                          false
% 7.31/1.50  --sig_cnt_out                           false
% 7.31/1.50  --trig_cnt_out                          false
% 7.31/1.50  --trig_cnt_out_tolerance                1.
% 7.31/1.50  --trig_cnt_out_sk_spl                   false
% 7.31/1.50  --abstr_cl_out                          false
% 7.31/1.50  
% 7.31/1.50  ------ Global Options
% 7.31/1.50  
% 7.31/1.50  --schedule                              default
% 7.31/1.50  --add_important_lit                     false
% 7.31/1.50  --prop_solver_per_cl                    1000
% 7.31/1.50  --min_unsat_core                        false
% 7.31/1.50  --soft_assumptions                      false
% 7.31/1.50  --soft_lemma_size                       3
% 7.31/1.50  --prop_impl_unit_size                   0
% 7.31/1.50  --prop_impl_unit                        []
% 7.31/1.50  --share_sel_clauses                     true
% 7.31/1.50  --reset_solvers                         false
% 7.31/1.50  --bc_imp_inh                            [conj_cone]
% 7.31/1.50  --conj_cone_tolerance                   3.
% 7.31/1.50  --extra_neg_conj                        none
% 7.31/1.50  --large_theory_mode                     true
% 7.31/1.50  --prolific_symb_bound                   200
% 7.31/1.50  --lt_threshold                          2000
% 7.31/1.50  --clause_weak_htbl                      true
% 7.31/1.50  --gc_record_bc_elim                     false
% 7.31/1.50  
% 7.31/1.50  ------ Preprocessing Options
% 7.31/1.50  
% 7.31/1.50  --preprocessing_flag                    true
% 7.31/1.50  --time_out_prep_mult                    0.1
% 7.31/1.50  --splitting_mode                        input
% 7.31/1.50  --splitting_grd                         true
% 7.31/1.50  --splitting_cvd                         false
% 7.31/1.50  --splitting_cvd_svl                     false
% 7.31/1.50  --splitting_nvd                         32
% 7.31/1.50  --sub_typing                            true
% 7.31/1.50  --prep_gs_sim                           true
% 7.31/1.50  --prep_unflatten                        true
% 7.31/1.50  --prep_res_sim                          true
% 7.31/1.50  --prep_upred                            true
% 7.31/1.50  --prep_sem_filter                       exhaustive
% 7.31/1.50  --prep_sem_filter_out                   false
% 7.31/1.50  --pred_elim                             true
% 7.31/1.50  --res_sim_input                         true
% 7.31/1.50  --eq_ax_congr_red                       true
% 7.31/1.50  --pure_diseq_elim                       true
% 7.31/1.50  --brand_transform                       false
% 7.31/1.50  --non_eq_to_eq                          false
% 7.31/1.50  --prep_def_merge                        true
% 7.31/1.50  --prep_def_merge_prop_impl              false
% 7.31/1.50  --prep_def_merge_mbd                    true
% 7.31/1.50  --prep_def_merge_tr_red                 false
% 7.31/1.50  --prep_def_merge_tr_cl                  false
% 7.31/1.50  --smt_preprocessing                     true
% 7.31/1.50  --smt_ac_axioms                         fast
% 7.31/1.50  --preprocessed_out                      false
% 7.31/1.50  --preprocessed_stats                    false
% 7.31/1.50  
% 7.31/1.50  ------ Abstraction refinement Options
% 7.31/1.50  
% 7.31/1.50  --abstr_ref                             []
% 7.31/1.50  --abstr_ref_prep                        false
% 7.31/1.50  --abstr_ref_until_sat                   false
% 7.31/1.50  --abstr_ref_sig_restrict                funpre
% 7.31/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.31/1.50  --abstr_ref_under                       []
% 7.31/1.50  
% 7.31/1.50  ------ SAT Options
% 7.31/1.50  
% 7.31/1.50  --sat_mode                              false
% 7.31/1.50  --sat_fm_restart_options                ""
% 7.31/1.51  --sat_gr_def                            false
% 7.31/1.51  --sat_epr_types                         true
% 7.31/1.51  --sat_non_cyclic_types                  false
% 7.31/1.51  --sat_finite_models                     false
% 7.31/1.51  --sat_fm_lemmas                         false
% 7.31/1.51  --sat_fm_prep                           false
% 7.31/1.51  --sat_fm_uc_incr                        true
% 7.31/1.51  --sat_out_model                         small
% 7.31/1.51  --sat_out_clauses                       false
% 7.31/1.51  
% 7.31/1.51  ------ QBF Options
% 7.31/1.51  
% 7.31/1.51  --qbf_mode                              false
% 7.31/1.51  --qbf_elim_univ                         false
% 7.31/1.51  --qbf_dom_inst                          none
% 7.31/1.51  --qbf_dom_pre_inst                      false
% 7.31/1.51  --qbf_sk_in                             false
% 7.31/1.51  --qbf_pred_elim                         true
% 7.31/1.51  --qbf_split                             512
% 7.31/1.51  
% 7.31/1.51  ------ BMC1 Options
% 7.31/1.51  
% 7.31/1.51  --bmc1_incremental                      false
% 7.31/1.51  --bmc1_axioms                           reachable_all
% 7.31/1.51  --bmc1_min_bound                        0
% 7.31/1.51  --bmc1_max_bound                        -1
% 7.31/1.51  --bmc1_max_bound_default                -1
% 7.31/1.51  --bmc1_symbol_reachability              true
% 7.31/1.51  --bmc1_property_lemmas                  false
% 7.31/1.51  --bmc1_k_induction                      false
% 7.31/1.51  --bmc1_non_equiv_states                 false
% 7.31/1.51  --bmc1_deadlock                         false
% 7.31/1.51  --bmc1_ucm                              false
% 7.31/1.51  --bmc1_add_unsat_core                   none
% 7.31/1.51  --bmc1_unsat_core_children              false
% 7.31/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.31/1.51  --bmc1_out_stat                         full
% 7.31/1.51  --bmc1_ground_init                      false
% 7.31/1.51  --bmc1_pre_inst_next_state              false
% 7.31/1.51  --bmc1_pre_inst_state                   false
% 7.31/1.51  --bmc1_pre_inst_reach_state             false
% 7.31/1.51  --bmc1_out_unsat_core                   false
% 7.31/1.51  --bmc1_aig_witness_out                  false
% 7.31/1.51  --bmc1_verbose                          false
% 7.31/1.51  --bmc1_dump_clauses_tptp                false
% 7.31/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.31/1.51  --bmc1_dump_file                        -
% 7.31/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.31/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.31/1.51  --bmc1_ucm_extend_mode                  1
% 7.31/1.51  --bmc1_ucm_init_mode                    2
% 7.31/1.51  --bmc1_ucm_cone_mode                    none
% 7.31/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.31/1.51  --bmc1_ucm_relax_model                  4
% 7.31/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.31/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.31/1.51  --bmc1_ucm_layered_model                none
% 7.31/1.51  --bmc1_ucm_max_lemma_size               10
% 7.31/1.51  
% 7.31/1.51  ------ AIG Options
% 7.31/1.51  
% 7.31/1.51  --aig_mode                              false
% 7.31/1.51  
% 7.31/1.51  ------ Instantiation Options
% 7.31/1.51  
% 7.31/1.51  --instantiation_flag                    true
% 7.31/1.51  --inst_sos_flag                         false
% 7.31/1.51  --inst_sos_phase                        true
% 7.31/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.31/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.31/1.51  --inst_lit_sel_side                     none
% 7.31/1.51  --inst_solver_per_active                1400
% 7.31/1.51  --inst_solver_calls_frac                1.
% 7.31/1.51  --inst_passive_queue_type               priority_queues
% 7.31/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.31/1.51  --inst_passive_queues_freq              [25;2]
% 7.31/1.51  --inst_dismatching                      true
% 7.31/1.51  --inst_eager_unprocessed_to_passive     true
% 7.31/1.51  --inst_prop_sim_given                   true
% 7.31/1.51  --inst_prop_sim_new                     false
% 7.31/1.51  --inst_subs_new                         false
% 7.31/1.51  --inst_eq_res_simp                      false
% 7.31/1.51  --inst_subs_given                       false
% 7.31/1.51  --inst_orphan_elimination               true
% 7.31/1.51  --inst_learning_loop_flag               true
% 7.31/1.51  --inst_learning_start                   3000
% 7.31/1.51  --inst_learning_factor                  2
% 7.31/1.51  --inst_start_prop_sim_after_learn       3
% 7.31/1.51  --inst_sel_renew                        solver
% 7.31/1.51  --inst_lit_activity_flag                true
% 7.31/1.51  --inst_restr_to_given                   false
% 7.31/1.51  --inst_activity_threshold               500
% 7.31/1.51  --inst_out_proof                        true
% 7.31/1.51  
% 7.31/1.51  ------ Resolution Options
% 7.31/1.51  
% 7.31/1.51  --resolution_flag                       false
% 7.31/1.51  --res_lit_sel                           adaptive
% 7.31/1.51  --res_lit_sel_side                      none
% 7.31/1.51  --res_ordering                          kbo
% 7.31/1.51  --res_to_prop_solver                    active
% 7.31/1.51  --res_prop_simpl_new                    false
% 7.31/1.51  --res_prop_simpl_given                  true
% 7.31/1.51  --res_passive_queue_type                priority_queues
% 7.31/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.31/1.51  --res_passive_queues_freq               [15;5]
% 7.31/1.51  --res_forward_subs                      full
% 7.31/1.51  --res_backward_subs                     full
% 7.31/1.51  --res_forward_subs_resolution           true
% 7.31/1.51  --res_backward_subs_resolution          true
% 7.31/1.51  --res_orphan_elimination                true
% 7.31/1.51  --res_time_limit                        2.
% 7.31/1.51  --res_out_proof                         true
% 7.31/1.51  
% 7.31/1.51  ------ Superposition Options
% 7.31/1.51  
% 7.31/1.51  --superposition_flag                    true
% 7.31/1.51  --sup_passive_queue_type                priority_queues
% 7.31/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.31/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.31/1.51  --demod_completeness_check              fast
% 7.31/1.51  --demod_use_ground                      true
% 7.31/1.51  --sup_to_prop_solver                    passive
% 7.31/1.51  --sup_prop_simpl_new                    true
% 7.31/1.51  --sup_prop_simpl_given                  true
% 7.31/1.51  --sup_fun_splitting                     false
% 7.31/1.51  --sup_smt_interval                      50000
% 7.31/1.51  
% 7.31/1.51  ------ Superposition Simplification Setup
% 7.31/1.51  
% 7.31/1.51  --sup_indices_passive                   []
% 7.31/1.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.31/1.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.31/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.31/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.31/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.31/1.51  --sup_full_bw                           [BwDemod]
% 7.31/1.51  --sup_immed_triv                        [TrivRules]
% 7.31/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.31/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.31/1.51  --sup_immed_bw_main                     []
% 7.31/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.31/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.31/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.31/1.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.31/1.51  
% 7.31/1.51  ------ Combination Options
% 7.31/1.51  
% 7.31/1.51  --comb_res_mult                         3
% 7.31/1.51  --comb_sup_mult                         2
% 7.31/1.51  --comb_inst_mult                        10
% 7.31/1.51  
% 7.31/1.51  ------ Debug Options
% 7.31/1.51  
% 7.31/1.51  --dbg_backtrace                         false
% 7.31/1.51  --dbg_dump_prop_clauses                 false
% 7.31/1.51  --dbg_dump_prop_clauses_file            -
% 7.31/1.51  --dbg_out_stat                          false
% 7.31/1.51  
% 7.31/1.51  
% 7.31/1.51  
% 7.31/1.51  
% 7.31/1.51  ------ Proving...
% 7.31/1.51  
% 7.31/1.51  
% 7.31/1.51  % SZS status Theorem for theBenchmark.p
% 7.31/1.51  
% 7.31/1.51  % SZS output start CNFRefutation for theBenchmark.p
% 7.31/1.51  
% 7.31/1.51  fof(f2,axiom,(
% 7.31/1.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 7.31/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.31/1.51  
% 7.31/1.51  fof(f8,plain,(
% 7.31/1.51    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.31/1.51    inference(ennf_transformation,[],[f2])).
% 7.31/1.51  
% 7.31/1.51  fof(f9,plain,(
% 7.31/1.51    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.31/1.51    inference(flattening,[],[f8])).
% 7.31/1.51  
% 7.31/1.51  fof(f19,plain,(
% 7.31/1.51    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.31/1.51    inference(nnf_transformation,[],[f9])).
% 7.31/1.51  
% 7.31/1.51  fof(f20,plain,(
% 7.31/1.51    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.31/1.51    inference(rectify,[],[f19])).
% 7.31/1.51  
% 7.31/1.51  fof(f23,plain,(
% 7.31/1.51    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK4(X0,X5)) = X5 & r2_hidden(sK4(X0,X5),k1_relat_1(X0))))),
% 7.31/1.51    introduced(choice_axiom,[])).
% 7.31/1.51  
% 7.31/1.51  fof(f22,plain,(
% 7.31/1.51    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X1)) = X2 & r2_hidden(sK3(X0,X1),k1_relat_1(X0))))) )),
% 7.31/1.51    introduced(choice_axiom,[])).
% 7.31/1.51  
% 7.31/1.51  fof(f21,plain,(
% 7.31/1.51    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK2(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK2(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK2(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK2(X0,X1),X1))))),
% 7.31/1.51    introduced(choice_axiom,[])).
% 7.31/1.51  
% 7.31/1.51  fof(f24,plain,(
% 7.31/1.51    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK2(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK2(X0,X1),X1)) & ((k1_funct_1(X0,sK3(X0,X1)) = sK2(X0,X1) & r2_hidden(sK3(X0,X1),k1_relat_1(X0))) | r2_hidden(sK2(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK4(X0,X5)) = X5 & r2_hidden(sK4(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.31/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f20,f23,f22,f21])).
% 7.31/1.51  
% 7.31/1.51  fof(f41,plain,(
% 7.31/1.51    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.31/1.51    inference(cnf_transformation,[],[f24])).
% 7.31/1.51  
% 7.31/1.51  fof(f67,plain,(
% 7.31/1.51    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.31/1.51    inference(equality_resolution,[],[f41])).
% 7.31/1.51  
% 7.31/1.51  fof(f68,plain,(
% 7.31/1.51    ( ! [X6,X0] : (r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~r2_hidden(X6,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.31/1.51    inference(equality_resolution,[],[f67])).
% 7.31/1.51  
% 7.31/1.51  fof(f1,axiom,(
% 7.31/1.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.31/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.31/1.51  
% 7.31/1.51  fof(f7,plain,(
% 7.31/1.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 7.31/1.51    inference(ennf_transformation,[],[f1])).
% 7.31/1.51  
% 7.31/1.51  fof(f15,plain,(
% 7.31/1.51    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 7.31/1.51    inference(nnf_transformation,[],[f7])).
% 7.31/1.51  
% 7.31/1.51  fof(f16,plain,(
% 7.31/1.51    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.31/1.51    inference(rectify,[],[f15])).
% 7.31/1.51  
% 7.31/1.51  fof(f17,plain,(
% 7.31/1.51    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 7.31/1.51    introduced(choice_axiom,[])).
% 7.31/1.51  
% 7.31/1.51  fof(f18,plain,(
% 7.31/1.51    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.31/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f17])).
% 7.31/1.51  
% 7.31/1.51  fof(f36,plain,(
% 7.31/1.51    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 7.31/1.51    inference(cnf_transformation,[],[f18])).
% 7.31/1.51  
% 7.31/1.51  fof(f5,conjecture,(
% 7.31/1.51    ! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 7.31/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.31/1.51  
% 7.31/1.51  fof(f6,negated_conjecture,(
% 7.31/1.51    ~! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 7.31/1.51    inference(negated_conjecture,[],[f5])).
% 7.31/1.51  
% 7.31/1.51  fof(f12,plain,(
% 7.31/1.51    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & r2_hidden(X2,k1_funct_2(X0,X1)))),
% 7.31/1.51    inference(ennf_transformation,[],[f6])).
% 7.31/1.51  
% 7.31/1.51  fof(f34,plain,(
% 7.31/1.51    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & r2_hidden(X2,k1_funct_2(X0,X1))) => ((~m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10))) | ~v1_funct_2(sK11,sK9,sK10) | ~v1_funct_1(sK11)) & r2_hidden(sK11,k1_funct_2(sK9,sK10)))),
% 7.31/1.51    introduced(choice_axiom,[])).
% 7.31/1.51  
% 7.31/1.51  fof(f35,plain,(
% 7.31/1.51    (~m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10))) | ~v1_funct_2(sK11,sK9,sK10) | ~v1_funct_1(sK11)) & r2_hidden(sK11,k1_funct_2(sK9,sK10))),
% 7.31/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11])],[f12,f34])).
% 7.31/1.51  
% 7.31/1.51  fof(f65,plain,(
% 7.31/1.51    r2_hidden(sK11,k1_funct_2(sK9,sK10))),
% 7.31/1.51    inference(cnf_transformation,[],[f35])).
% 7.31/1.51  
% 7.31/1.51  fof(f3,axiom,(
% 7.31/1.51    ! [X0,X1,X2] : (k1_funct_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4))))),
% 7.31/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.31/1.51  
% 7.31/1.51  fof(f13,plain,(
% 7.31/1.51    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4))))),
% 7.31/1.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 7.31/1.51  
% 7.31/1.51  fof(f14,plain,(
% 7.31/1.51    ! [X0,X1,X2] : (k1_funct_2(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 7.31/1.51    inference(definition_folding,[],[f3,f13])).
% 7.31/1.51  
% 7.31/1.51  fof(f31,plain,(
% 7.31/1.51    ! [X0,X1,X2] : ((k1_funct_2(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k1_funct_2(X0,X1) != X2))),
% 7.31/1.51    inference(nnf_transformation,[],[f14])).
% 7.31/1.51  
% 7.31/1.51  fof(f57,plain,(
% 7.31/1.51    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k1_funct_2(X0,X1) != X2) )),
% 7.31/1.51    inference(cnf_transformation,[],[f31])).
% 7.31/1.51  
% 7.31/1.51  fof(f74,plain,(
% 7.31/1.51    ( ! [X0,X1] : (sP0(X1,X0,k1_funct_2(X0,X1))) )),
% 7.31/1.51    inference(equality_resolution,[],[f57])).
% 7.31/1.51  
% 7.31/1.51  fof(f25,plain,(
% 7.31/1.51    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4))) & (? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 7.31/1.51    inference(nnf_transformation,[],[f13])).
% 7.31/1.51  
% 7.31/1.51  fof(f26,plain,(
% 7.31/1.51    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X0) | k1_relat_1(X4) != X1 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X0) & k1_relat_1(X5) = X1 & X3 = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r1_tarski(k2_relat_1(X7),X0) | k1_relat_1(X7) != X1 | X6 != X7 | ~v1_funct_1(X7) | ~v1_relat_1(X7))) & (? [X8] : (r1_tarski(k2_relat_1(X8),X0) & k1_relat_1(X8) = X1 & X6 = X8 & v1_funct_1(X8) & v1_relat_1(X8)) | ~r2_hidden(X6,X2))) | ~sP0(X0,X1,X2)))),
% 7.31/1.51    inference(rectify,[],[f25])).
% 7.31/1.51  
% 7.31/1.51  fof(f29,plain,(
% 7.31/1.51    ! [X6,X1,X0] : (? [X8] : (r1_tarski(k2_relat_1(X8),X0) & k1_relat_1(X8) = X1 & X6 = X8 & v1_funct_1(X8) & v1_relat_1(X8)) => (r1_tarski(k2_relat_1(sK7(X0,X1,X6)),X0) & k1_relat_1(sK7(X0,X1,X6)) = X1 & sK7(X0,X1,X6) = X6 & v1_funct_1(sK7(X0,X1,X6)) & v1_relat_1(sK7(X0,X1,X6))))),
% 7.31/1.51    introduced(choice_axiom,[])).
% 7.31/1.51  
% 7.31/1.51  fof(f28,plain,(
% 7.31/1.51    ( ! [X3] : (! [X2,X1,X0] : (? [X5] : (r1_tarski(k2_relat_1(X5),X0) & k1_relat_1(X5) = X1 & X3 = X5 & v1_funct_1(X5) & v1_relat_1(X5)) => (r1_tarski(k2_relat_1(sK6(X0,X1,X2)),X0) & k1_relat_1(sK6(X0,X1,X2)) = X1 & sK6(X0,X1,X2) = X3 & v1_funct_1(sK6(X0,X1,X2)) & v1_relat_1(sK6(X0,X1,X2))))) )),
% 7.31/1.51    introduced(choice_axiom,[])).
% 7.31/1.51  
% 7.31/1.51  fof(f27,plain,(
% 7.31/1.51    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X0) | k1_relat_1(X4) != X1 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X0) & k1_relat_1(X5) = X1 & X3 = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(X3,X2))) => ((! [X4] : (~r1_tarski(k2_relat_1(X4),X0) | k1_relat_1(X4) != X1 | sK5(X0,X1,X2) != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X0) & k1_relat_1(X5) = X1 & sK5(X0,X1,X2) = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 7.31/1.51    introduced(choice_axiom,[])).
% 7.31/1.51  
% 7.31/1.51  fof(f30,plain,(
% 7.31/1.51    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((! [X4] : (~r1_tarski(k2_relat_1(X4),X0) | k1_relat_1(X4) != X1 | sK5(X0,X1,X2) != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((r1_tarski(k2_relat_1(sK6(X0,X1,X2)),X0) & k1_relat_1(sK6(X0,X1,X2)) = X1 & sK5(X0,X1,X2) = sK6(X0,X1,X2) & v1_funct_1(sK6(X0,X1,X2)) & v1_relat_1(sK6(X0,X1,X2))) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r1_tarski(k2_relat_1(X7),X0) | k1_relat_1(X7) != X1 | X6 != X7 | ~v1_funct_1(X7) | ~v1_relat_1(X7))) & ((r1_tarski(k2_relat_1(sK7(X0,X1,X6)),X0) & k1_relat_1(sK7(X0,X1,X6)) = X1 & sK7(X0,X1,X6) = X6 & v1_funct_1(sK7(X0,X1,X6)) & v1_relat_1(sK7(X0,X1,X6))) | ~r2_hidden(X6,X2))) | ~sP0(X0,X1,X2)))),
% 7.31/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f26,f29,f28,f27])).
% 7.31/1.51  
% 7.31/1.51  fof(f48,plain,(
% 7.31/1.51    ( ! [X6,X2,X0,X1] : (k1_relat_1(sK7(X0,X1,X6)) = X1 | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 7.31/1.51    inference(cnf_transformation,[],[f30])).
% 7.31/1.51  
% 7.31/1.51  fof(f47,plain,(
% 7.31/1.51    ( ! [X6,X2,X0,X1] : (sK7(X0,X1,X6) = X6 | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 7.31/1.51    inference(cnf_transformation,[],[f30])).
% 7.31/1.51  
% 7.31/1.51  fof(f4,axiom,(
% 7.31/1.51    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,X0) => r2_hidden(k1_funct_1(X2,X3),X1)) & k1_relat_1(X2) = X0) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 7.31/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.31/1.51  
% 7.31/1.51  fof(f10,plain,(
% 7.31/1.51    ! [X0,X1,X2] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 7.31/1.51    inference(ennf_transformation,[],[f4])).
% 7.31/1.51  
% 7.31/1.51  fof(f11,plain,(
% 7.31/1.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 7.31/1.51    inference(flattening,[],[f10])).
% 7.31/1.51  
% 7.31/1.51  fof(f32,plain,(
% 7.31/1.51    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) => (~r2_hidden(k1_funct_1(X2,sK8(X0,X1,X2)),X1) & r2_hidden(sK8(X0,X1,X2),X0)))),
% 7.31/1.51    introduced(choice_axiom,[])).
% 7.31/1.51  
% 7.31/1.51  fof(f33,plain,(
% 7.31/1.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~r2_hidden(k1_funct_1(X2,sK8(X0,X1,X2)),X1) & r2_hidden(sK8(X0,X1,X2),X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 7.31/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f11,f32])).
% 7.31/1.51  
% 7.31/1.51  fof(f62,plain,(
% 7.31/1.51    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~r2_hidden(k1_funct_1(X2,sK8(X0,X1,X2)),X1) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 7.31/1.51    inference(cnf_transformation,[],[f33])).
% 7.31/1.51  
% 7.31/1.51  fof(f77,plain,(
% 7.31/1.51    ( ! [X2,X1] : (v1_funct_2(X2,k1_relat_1(X2),X1) | ~r2_hidden(k1_funct_1(X2,sK8(k1_relat_1(X2),X1,X2)),X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 7.31/1.51    inference(equality_resolution,[],[f62])).
% 7.31/1.51  
% 7.31/1.51  fof(f64,plain,(
% 7.31/1.51    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(k1_funct_1(X2,sK8(X0,X1,X2)),X1) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 7.31/1.51    inference(cnf_transformation,[],[f33])).
% 7.31/1.51  
% 7.31/1.51  fof(f75,plain,(
% 7.31/1.51    ( ! [X2,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) | ~r2_hidden(k1_funct_1(X2,sK8(k1_relat_1(X2),X1,X2)),X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 7.31/1.51    inference(equality_resolution,[],[f64])).
% 7.31/1.51  
% 7.31/1.51  fof(f66,plain,(
% 7.31/1.51    ~m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10))) | ~v1_funct_2(sK11,sK9,sK10) | ~v1_funct_1(sK11)),
% 7.31/1.51    inference(cnf_transformation,[],[f35])).
% 7.31/1.51  
% 7.31/1.51  fof(f46,plain,(
% 7.31/1.51    ( ! [X6,X2,X0,X1] : (v1_funct_1(sK7(X0,X1,X6)) | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 7.31/1.51    inference(cnf_transformation,[],[f30])).
% 7.31/1.51  
% 7.31/1.51  fof(f45,plain,(
% 7.31/1.51    ( ! [X6,X2,X0,X1] : (v1_relat_1(sK7(X0,X1,X6)) | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 7.31/1.51    inference(cnf_transformation,[],[f30])).
% 7.31/1.51  
% 7.31/1.51  fof(f49,plain,(
% 7.31/1.51    ( ! [X6,X2,X0,X1] : (r1_tarski(k2_relat_1(sK7(X0,X1,X6)),X0) | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 7.31/1.51    inference(cnf_transformation,[],[f30])).
% 7.31/1.51  
% 7.31/1.51  fof(f63,plain,(
% 7.31/1.51    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_hidden(sK8(X0,X1,X2),X0) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 7.31/1.51    inference(cnf_transformation,[],[f33])).
% 7.31/1.51  
% 7.31/1.51  fof(f76,plain,(
% 7.31/1.51    ( ! [X2,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) | r2_hidden(sK8(k1_relat_1(X2),X1,X2),k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 7.31/1.51    inference(equality_resolution,[],[f63])).
% 7.31/1.51  
% 7.31/1.51  fof(f61,plain,(
% 7.31/1.51    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | r2_hidden(sK8(X0,X1,X2),X0) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 7.31/1.51    inference(cnf_transformation,[],[f33])).
% 7.31/1.51  
% 7.31/1.51  fof(f78,plain,(
% 7.31/1.51    ( ! [X2,X1] : (v1_funct_2(X2,k1_relat_1(X2),X1) | r2_hidden(sK8(k1_relat_1(X2),X1,X2),k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 7.31/1.51    inference(equality_resolution,[],[f61])).
% 7.31/1.51  
% 7.31/1.51  cnf(c_6,plain,
% 7.31/1.51      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 7.31/1.51      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 7.31/1.51      | ~ v1_relat_1(X1)
% 7.31/1.51      | ~ v1_funct_1(X1) ),
% 7.31/1.51      inference(cnf_transformation,[],[f68]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_6986,plain,
% 7.31/1.51      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 7.31/1.51      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
% 7.31/1.51      | v1_relat_1(X1) != iProver_top
% 7.31/1.51      | v1_funct_1(X1) != iProver_top ),
% 7.31/1.51      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_2,plain,
% 7.31/1.51      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 7.31/1.51      inference(cnf_transformation,[],[f36]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_6990,plain,
% 7.31/1.51      ( r2_hidden(X0,X1) != iProver_top
% 7.31/1.51      | r2_hidden(X0,X2) = iProver_top
% 7.31/1.51      | r1_tarski(X1,X2) != iProver_top ),
% 7.31/1.51      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_9633,plain,
% 7.31/1.51      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 7.31/1.51      | r2_hidden(k1_funct_1(X1,X0),X2) = iProver_top
% 7.31/1.51      | r1_tarski(k2_relat_1(X1),X2) != iProver_top
% 7.31/1.51      | v1_relat_1(X1) != iProver_top
% 7.31/1.51      | v1_funct_1(X1) != iProver_top ),
% 7.31/1.51      inference(superposition,[status(thm)],[c_6986,c_6990]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_30,negated_conjecture,
% 7.31/1.51      ( r2_hidden(sK11,k1_funct_2(sK9,sK10)) ),
% 7.31/1.51      inference(cnf_transformation,[],[f65]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_6969,plain,
% 7.31/1.51      ( r2_hidden(sK11,k1_funct_2(sK9,sK10)) = iProver_top ),
% 7.31/1.51      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_22,plain,
% 7.31/1.51      ( sP0(X0,X1,k1_funct_2(X1,X0)) ),
% 7.31/1.51      inference(cnf_transformation,[],[f74]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_6970,plain,
% 7.31/1.51      ( sP0(X0,X1,k1_funct_2(X1,X0)) = iProver_top ),
% 7.31/1.51      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_17,plain,
% 7.31/1.51      ( ~ sP0(X0,X1,X2)
% 7.31/1.51      | ~ r2_hidden(X3,X2)
% 7.31/1.51      | k1_relat_1(sK7(X0,X1,X3)) = X1 ),
% 7.31/1.51      inference(cnf_transformation,[],[f48]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_6975,plain,
% 7.31/1.51      ( k1_relat_1(sK7(X0,X1,X2)) = X1
% 7.31/1.51      | sP0(X0,X1,X3) != iProver_top
% 7.31/1.51      | r2_hidden(X2,X3) != iProver_top ),
% 7.31/1.51      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_7931,plain,
% 7.31/1.51      ( k1_relat_1(sK7(X0,X1,X2)) = X1
% 7.31/1.51      | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
% 7.31/1.51      inference(superposition,[status(thm)],[c_6970,c_6975]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_8368,plain,
% 7.31/1.51      ( k1_relat_1(sK7(sK10,sK9,sK11)) = sK9 ),
% 7.31/1.51      inference(superposition,[status(thm)],[c_6969,c_7931]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_18,plain,
% 7.31/1.51      ( ~ sP0(X0,X1,X2) | ~ r2_hidden(X3,X2) | sK7(X0,X1,X3) = X3 ),
% 7.31/1.51      inference(cnf_transformation,[],[f47]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_6974,plain,
% 7.31/1.51      ( sK7(X0,X1,X2) = X2
% 7.31/1.51      | sP0(X0,X1,X3) != iProver_top
% 7.31/1.51      | r2_hidden(X2,X3) != iProver_top ),
% 7.31/1.51      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_7697,plain,
% 7.31/1.51      ( sK7(X0,X1,X2) = X2
% 7.31/1.51      | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
% 7.31/1.51      inference(superposition,[status(thm)],[c_6970,c_6974]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_7745,plain,
% 7.31/1.51      ( sK7(sK10,sK9,sK11) = sK11 ),
% 7.31/1.51      inference(superposition,[status(thm)],[c_6969,c_7697]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_8370,plain,
% 7.31/1.51      ( k1_relat_1(sK11) = sK9 ),
% 7.31/1.51      inference(light_normalisation,[status(thm)],[c_8368,c_7745]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_25,plain,
% 7.31/1.51      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 7.31/1.51      | ~ r2_hidden(k1_funct_1(X0,sK8(k1_relat_1(X0),X1,X0)),X1)
% 7.31/1.51      | ~ v1_relat_1(X0)
% 7.31/1.51      | ~ v1_funct_1(X0) ),
% 7.31/1.51      inference(cnf_transformation,[],[f77]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_23,plain,
% 7.31/1.51      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 7.31/1.51      | ~ r2_hidden(k1_funct_1(X0,sK8(k1_relat_1(X0),X1,X0)),X1)
% 7.31/1.51      | ~ v1_relat_1(X0)
% 7.31/1.51      | ~ v1_funct_1(X0) ),
% 7.31/1.51      inference(cnf_transformation,[],[f75]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_29,negated_conjecture,
% 7.31/1.51      ( ~ v1_funct_2(sK11,sK9,sK10)
% 7.31/1.51      | ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10)))
% 7.31/1.51      | ~ v1_funct_1(sK11) ),
% 7.31/1.51      inference(cnf_transformation,[],[f66]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_363,plain,
% 7.31/1.51      ( ~ v1_funct_2(sK11,sK9,sK10)
% 7.31/1.51      | ~ r2_hidden(k1_funct_1(X0,sK8(k1_relat_1(X0),X1,X0)),X1)
% 7.31/1.51      | ~ v1_relat_1(X0)
% 7.31/1.51      | ~ v1_funct_1(X0)
% 7.31/1.51      | ~ v1_funct_1(sK11)
% 7.31/1.51      | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)) != k1_zfmisc_1(k2_zfmisc_1(sK9,sK10))
% 7.31/1.51      | sK11 != X0 ),
% 7.31/1.51      inference(resolution_lifted,[status(thm)],[c_23,c_29]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_364,plain,
% 7.31/1.51      ( ~ v1_funct_2(sK11,sK9,sK10)
% 7.31/1.51      | ~ r2_hidden(k1_funct_1(sK11,sK8(k1_relat_1(sK11),X0,sK11)),X0)
% 7.31/1.51      | ~ v1_relat_1(sK11)
% 7.31/1.51      | ~ v1_funct_1(sK11)
% 7.31/1.51      | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK11),X0)) != k1_zfmisc_1(k2_zfmisc_1(sK9,sK10)) ),
% 7.31/1.51      inference(unflattening,[status(thm)],[c_363]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_444,plain,
% 7.31/1.51      ( ~ r2_hidden(k1_funct_1(X0,sK8(k1_relat_1(X0),X1,X0)),X1)
% 7.31/1.51      | ~ r2_hidden(k1_funct_1(sK11,sK8(k1_relat_1(sK11),X2,sK11)),X2)
% 7.31/1.51      | ~ v1_relat_1(X0)
% 7.31/1.51      | ~ v1_relat_1(sK11)
% 7.31/1.51      | ~ v1_funct_1(X0)
% 7.31/1.51      | ~ v1_funct_1(sK11)
% 7.31/1.51      | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK11),X2)) != k1_zfmisc_1(k2_zfmisc_1(sK9,sK10))
% 7.31/1.51      | k1_relat_1(X0) != sK9
% 7.31/1.51      | sK10 != X1
% 7.31/1.51      | sK11 != X0 ),
% 7.31/1.51      inference(resolution_lifted,[status(thm)],[c_25,c_364]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_445,plain,
% 7.31/1.51      ( ~ r2_hidden(k1_funct_1(sK11,sK8(k1_relat_1(sK11),X0,sK11)),X0)
% 7.31/1.51      | ~ r2_hidden(k1_funct_1(sK11,sK8(k1_relat_1(sK11),sK10,sK11)),sK10)
% 7.31/1.51      | ~ v1_relat_1(sK11)
% 7.31/1.51      | ~ v1_funct_1(sK11)
% 7.31/1.51      | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK11),X0)) != k1_zfmisc_1(k2_zfmisc_1(sK9,sK10))
% 7.31/1.51      | k1_relat_1(sK11) != sK9 ),
% 7.31/1.51      inference(unflattening,[status(thm)],[c_444]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_6425,plain,
% 7.31/1.51      ( ~ r2_hidden(k1_funct_1(sK11,sK8(k1_relat_1(sK11),X0,sK11)),X0)
% 7.31/1.51      | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK11),X0)) != k1_zfmisc_1(k2_zfmisc_1(sK9,sK10))
% 7.31/1.51      | ~ sP1_iProver_split ),
% 7.31/1.51      inference(splitting,
% 7.31/1.51                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 7.31/1.51                [c_445]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_6964,plain,
% 7.31/1.51      ( k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK11),X0)) != k1_zfmisc_1(k2_zfmisc_1(sK9,sK10))
% 7.31/1.51      | r2_hidden(k1_funct_1(sK11,sK8(k1_relat_1(sK11),X0,sK11)),X0) != iProver_top
% 7.31/1.51      | sP1_iProver_split != iProver_top ),
% 7.31/1.51      inference(predicate_to_equality,[status(thm)],[c_6425]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_8405,plain,
% 7.31/1.51      ( k1_zfmisc_1(k2_zfmisc_1(sK9,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK9,sK10))
% 7.31/1.51      | r2_hidden(k1_funct_1(sK11,sK8(sK9,X0,sK11)),X0) != iProver_top
% 7.31/1.51      | sP1_iProver_split != iProver_top ),
% 7.31/1.51      inference(demodulation,[status(thm)],[c_8370,c_6964]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_8613,plain,
% 7.31/1.51      ( r2_hidden(k1_funct_1(sK11,sK8(sK9,sK10,sK11)),sK10) != iProver_top
% 7.31/1.51      | sP1_iProver_split != iProver_top ),
% 7.31/1.51      inference(equality_resolution,[status(thm)],[c_8405]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_31,plain,
% 7.31/1.51      ( r2_hidden(sK11,k1_funct_2(sK9,sK10)) = iProver_top ),
% 7.31/1.51      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_6430,plain,( X0 = X0 ),theory(equality) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_6459,plain,
% 7.31/1.51      ( sK11 = sK11 ),
% 7.31/1.51      inference(instantiation,[status(thm)],[c_6430]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_19,plain,
% 7.31/1.51      ( ~ sP0(X0,X1,X2)
% 7.31/1.51      | ~ r2_hidden(X3,X2)
% 7.31/1.51      | v1_funct_1(sK7(X0,X1,X3)) ),
% 7.31/1.51      inference(cnf_transformation,[],[f46]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_7281,plain,
% 7.31/1.51      ( ~ sP0(X0,X1,k1_funct_2(sK9,sK10))
% 7.31/1.51      | ~ r2_hidden(sK11,k1_funct_2(sK9,sK10))
% 7.31/1.51      | v1_funct_1(sK7(X0,X1,sK11)) ),
% 7.31/1.51      inference(instantiation,[status(thm)],[c_19]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_7381,plain,
% 7.31/1.51      ( ~ sP0(sK10,sK9,k1_funct_2(sK9,sK10))
% 7.31/1.51      | ~ r2_hidden(sK11,k1_funct_2(sK9,sK10))
% 7.31/1.51      | v1_funct_1(sK7(sK10,sK9,sK11)) ),
% 7.31/1.51      inference(instantiation,[status(thm)],[c_7281]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_7383,plain,
% 7.31/1.51      ( sP0(sK10,sK9,k1_funct_2(sK9,sK10)) != iProver_top
% 7.31/1.51      | r2_hidden(sK11,k1_funct_2(sK9,sK10)) != iProver_top
% 7.31/1.51      | v1_funct_1(sK7(sK10,sK9,sK11)) = iProver_top ),
% 7.31/1.51      inference(predicate_to_equality,[status(thm)],[c_7381]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_7382,plain,
% 7.31/1.51      ( sP0(sK10,sK9,k1_funct_2(sK9,sK10)) ),
% 7.31/1.51      inference(instantiation,[status(thm)],[c_22]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_7385,plain,
% 7.31/1.51      ( sP0(sK10,sK9,k1_funct_2(sK9,sK10)) = iProver_top ),
% 7.31/1.51      inference(predicate_to_equality,[status(thm)],[c_7382]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_20,plain,
% 7.31/1.51      ( ~ sP0(X0,X1,X2)
% 7.31/1.51      | ~ r2_hidden(X3,X2)
% 7.31/1.51      | v1_relat_1(sK7(X0,X1,X3)) ),
% 7.31/1.51      inference(cnf_transformation,[],[f45]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_7286,plain,
% 7.31/1.51      ( ~ sP0(X0,X1,k1_funct_2(sK9,sK10))
% 7.31/1.51      | ~ r2_hidden(sK11,k1_funct_2(sK9,sK10))
% 7.31/1.51      | v1_relat_1(sK7(X0,X1,sK11)) ),
% 7.31/1.51      inference(instantiation,[status(thm)],[c_20]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_7452,plain,
% 7.31/1.51      ( ~ sP0(sK10,sK9,k1_funct_2(sK9,sK10))
% 7.31/1.51      | ~ r2_hidden(sK11,k1_funct_2(sK9,sK10))
% 7.31/1.51      | v1_relat_1(sK7(sK10,sK9,sK11)) ),
% 7.31/1.51      inference(instantiation,[status(thm)],[c_7286]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_7454,plain,
% 7.31/1.51      ( sP0(sK10,sK9,k1_funct_2(sK9,sK10)) != iProver_top
% 7.31/1.51      | r2_hidden(sK11,k1_funct_2(sK9,sK10)) != iProver_top
% 7.31/1.51      | v1_relat_1(sK7(sK10,sK9,sK11)) = iProver_top ),
% 7.31/1.51      inference(predicate_to_equality,[status(thm)],[c_7452]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_7316,plain,
% 7.31/1.51      ( ~ sP0(X0,X1,k1_funct_2(sK9,sK10))
% 7.31/1.51      | ~ r2_hidden(sK11,k1_funct_2(sK9,sK10))
% 7.31/1.51      | sK7(X0,X1,sK11) = sK11 ),
% 7.31/1.51      inference(instantiation,[status(thm)],[c_18]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_7451,plain,
% 7.31/1.51      ( ~ sP0(sK10,sK9,k1_funct_2(sK9,sK10))
% 7.31/1.51      | ~ r2_hidden(sK11,k1_funct_2(sK9,sK10))
% 7.31/1.51      | sK7(sK10,sK9,sK11) = sK11 ),
% 7.31/1.51      inference(instantiation,[status(thm)],[c_7316]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_6437,plain,
% 7.31/1.51      ( ~ v1_funct_1(X0) | v1_funct_1(X1) | X1 != X0 ),
% 7.31/1.51      theory(equality) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_7462,plain,
% 7.31/1.51      ( v1_funct_1(X0)
% 7.31/1.51      | ~ v1_funct_1(sK7(sK10,sK9,sK11))
% 7.31/1.51      | X0 != sK7(sK10,sK9,sK11) ),
% 7.31/1.51      inference(instantiation,[status(thm)],[c_6437]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_7463,plain,
% 7.31/1.51      ( X0 != sK7(sK10,sK9,sK11)
% 7.31/1.51      | v1_funct_1(X0) = iProver_top
% 7.31/1.51      | v1_funct_1(sK7(sK10,sK9,sK11)) != iProver_top ),
% 7.31/1.51      inference(predicate_to_equality,[status(thm)],[c_7462]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_7465,plain,
% 7.31/1.51      ( sK11 != sK7(sK10,sK9,sK11)
% 7.31/1.51      | v1_funct_1(sK7(sK10,sK9,sK11)) != iProver_top
% 7.31/1.51      | v1_funct_1(sK11) = iProver_top ),
% 7.31/1.51      inference(instantiation,[status(thm)],[c_7463]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_6438,plain,
% 7.31/1.51      ( ~ v1_relat_1(X0) | v1_relat_1(X1) | X1 != X0 ),
% 7.31/1.51      theory(equality) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_7626,plain,
% 7.31/1.51      ( v1_relat_1(X0)
% 7.31/1.51      | ~ v1_relat_1(sK7(sK10,sK9,sK11))
% 7.31/1.51      | X0 != sK7(sK10,sK9,sK11) ),
% 7.31/1.51      inference(instantiation,[status(thm)],[c_6438]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_7627,plain,
% 7.31/1.51      ( X0 != sK7(sK10,sK9,sK11)
% 7.31/1.51      | v1_relat_1(X0) = iProver_top
% 7.31/1.51      | v1_relat_1(sK7(sK10,sK9,sK11)) != iProver_top ),
% 7.31/1.51      inference(predicate_to_equality,[status(thm)],[c_7626]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_7629,plain,
% 7.31/1.51      ( sK11 != sK7(sK10,sK9,sK11)
% 7.31/1.51      | v1_relat_1(sK7(sK10,sK9,sK11)) != iProver_top
% 7.31/1.51      | v1_relat_1(sK11) = iProver_top ),
% 7.31/1.51      inference(instantiation,[status(thm)],[c_7627]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_6431,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_7710,plain,
% 7.31/1.51      ( X0 != X1 | X0 = sK7(sK10,sK9,sK11) | sK7(sK10,sK9,sK11) != X1 ),
% 7.31/1.51      inference(instantiation,[status(thm)],[c_6431]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_7711,plain,
% 7.31/1.51      ( sK7(sK10,sK9,sK11) != sK11
% 7.31/1.51      | sK11 = sK7(sK10,sK9,sK11)
% 7.31/1.51      | sK11 != sK11 ),
% 7.31/1.51      inference(instantiation,[status(thm)],[c_7710]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_6426,plain,
% 7.31/1.51      ( ~ r2_hidden(k1_funct_1(sK11,sK8(k1_relat_1(sK11),sK10,sK11)),sK10)
% 7.31/1.51      | ~ v1_relat_1(sK11)
% 7.31/1.51      | ~ v1_funct_1(sK11)
% 7.31/1.51      | sP1_iProver_split
% 7.31/1.51      | k1_relat_1(sK11) != sK9 ),
% 7.31/1.51      inference(splitting,
% 7.31/1.51                [splitting(split),new_symbols(definition,[])],
% 7.31/1.51                [c_445]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_6963,plain,
% 7.31/1.51      ( k1_relat_1(sK11) != sK9
% 7.31/1.51      | r2_hidden(k1_funct_1(sK11,sK8(k1_relat_1(sK11),sK10,sK11)),sK10) != iProver_top
% 7.31/1.51      | v1_relat_1(sK11) != iProver_top
% 7.31/1.51      | v1_funct_1(sK11) != iProver_top
% 7.31/1.51      | sP1_iProver_split = iProver_top ),
% 7.31/1.51      inference(predicate_to_equality,[status(thm)],[c_6426]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_8403,plain,
% 7.31/1.51      ( sK9 != sK9
% 7.31/1.51      | r2_hidden(k1_funct_1(sK11,sK8(sK9,sK10,sK11)),sK10) != iProver_top
% 7.31/1.51      | v1_relat_1(sK11) != iProver_top
% 7.31/1.51      | v1_funct_1(sK11) != iProver_top
% 7.31/1.51      | sP1_iProver_split = iProver_top ),
% 7.31/1.51      inference(demodulation,[status(thm)],[c_8370,c_6963]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_8428,plain,
% 7.31/1.51      ( r2_hidden(k1_funct_1(sK11,sK8(sK9,sK10,sK11)),sK10) != iProver_top
% 7.31/1.51      | v1_relat_1(sK11) != iProver_top
% 7.31/1.51      | v1_funct_1(sK11) != iProver_top
% 7.31/1.51      | sP1_iProver_split = iProver_top ),
% 7.31/1.51      inference(equality_resolution_simp,[status(thm)],[c_8403]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_9238,plain,
% 7.31/1.51      ( r2_hidden(k1_funct_1(sK11,sK8(sK9,sK10,sK11)),sK10) != iProver_top ),
% 7.31/1.51      inference(global_propositional_subsumption,
% 7.31/1.51                [status(thm)],
% 7.31/1.51                [c_8613,c_30,c_31,c_6459,c_7383,c_7382,c_7385,c_7454,
% 7.31/1.51                 c_7451,c_7465,c_7629,c_7711,c_8428]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_37573,plain,
% 7.31/1.51      ( r2_hidden(sK8(sK9,sK10,sK11),k1_relat_1(sK11)) != iProver_top
% 7.31/1.51      | r1_tarski(k2_relat_1(sK11),sK10) != iProver_top
% 7.31/1.51      | v1_relat_1(sK11) != iProver_top
% 7.31/1.51      | v1_funct_1(sK11) != iProver_top ),
% 7.31/1.51      inference(superposition,[status(thm)],[c_9633,c_9238]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_37648,plain,
% 7.31/1.51      ( r2_hidden(sK8(sK9,sK10,sK11),sK9) != iProver_top
% 7.31/1.51      | r1_tarski(k2_relat_1(sK11),sK10) != iProver_top
% 7.31/1.51      | v1_relat_1(sK11) != iProver_top
% 7.31/1.51      | v1_funct_1(sK11) != iProver_top ),
% 7.31/1.51      inference(light_normalisation,[status(thm)],[c_37573,c_8370]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_16,plain,
% 7.31/1.51      ( ~ sP0(X0,X1,X2)
% 7.31/1.51      | ~ r2_hidden(X3,X2)
% 7.31/1.51      | r1_tarski(k2_relat_1(sK7(X0,X1,X3)),X0) ),
% 7.31/1.51      inference(cnf_transformation,[],[f49]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_6976,plain,
% 7.31/1.51      ( sP0(X0,X1,X2) != iProver_top
% 7.31/1.51      | r2_hidden(X3,X2) != iProver_top
% 7.31/1.51      | r1_tarski(k2_relat_1(sK7(X0,X1,X3)),X0) = iProver_top ),
% 7.31/1.51      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_8762,plain,
% 7.31/1.51      ( r2_hidden(X0,k1_funct_2(X1,X2)) != iProver_top
% 7.31/1.51      | r1_tarski(k2_relat_1(sK7(X2,X1,X0)),X2) = iProver_top ),
% 7.31/1.51      inference(superposition,[status(thm)],[c_6970,c_6976]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_10927,plain,
% 7.31/1.51      ( r2_hidden(sK11,k1_funct_2(sK9,sK10)) != iProver_top
% 7.31/1.51      | r1_tarski(k2_relat_1(sK11),sK10) = iProver_top ),
% 7.31/1.51      inference(superposition,[status(thm)],[c_7745,c_8762]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_24,plain,
% 7.31/1.51      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 7.31/1.51      | r2_hidden(sK8(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
% 7.31/1.51      | ~ v1_relat_1(X0)
% 7.31/1.51      | ~ v1_funct_1(X0) ),
% 7.31/1.51      inference(cnf_transformation,[],[f76]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_342,plain,
% 7.31/1.51      ( ~ v1_funct_2(sK11,sK9,sK10)
% 7.31/1.51      | r2_hidden(sK8(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
% 7.31/1.51      | ~ v1_relat_1(X0)
% 7.31/1.51      | ~ v1_funct_1(X0)
% 7.31/1.51      | ~ v1_funct_1(sK11)
% 7.31/1.51      | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)) != k1_zfmisc_1(k2_zfmisc_1(sK9,sK10))
% 7.31/1.51      | sK11 != X0 ),
% 7.31/1.51      inference(resolution_lifted,[status(thm)],[c_24,c_29]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_343,plain,
% 7.31/1.51      ( ~ v1_funct_2(sK11,sK9,sK10)
% 7.31/1.51      | r2_hidden(sK8(k1_relat_1(sK11),X0,sK11),k1_relat_1(sK11))
% 7.31/1.51      | ~ v1_relat_1(sK11)
% 7.31/1.51      | ~ v1_funct_1(sK11)
% 7.31/1.51      | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK11),X0)) != k1_zfmisc_1(k2_zfmisc_1(sK9,sK10)) ),
% 7.31/1.51      inference(unflattening,[status(thm)],[c_342]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_468,plain,
% 7.31/1.51      ( r2_hidden(sK8(k1_relat_1(sK11),X0,sK11),k1_relat_1(sK11))
% 7.31/1.51      | ~ r2_hidden(k1_funct_1(X1,sK8(k1_relat_1(X1),X2,X1)),X2)
% 7.31/1.51      | ~ v1_relat_1(X1)
% 7.31/1.51      | ~ v1_relat_1(sK11)
% 7.31/1.51      | ~ v1_funct_1(X1)
% 7.31/1.51      | ~ v1_funct_1(sK11)
% 7.31/1.51      | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK11),X0)) != k1_zfmisc_1(k2_zfmisc_1(sK9,sK10))
% 7.31/1.51      | k1_relat_1(X1) != sK9
% 7.31/1.51      | sK10 != X2
% 7.31/1.51      | sK11 != X1 ),
% 7.31/1.51      inference(resolution_lifted,[status(thm)],[c_25,c_343]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_469,plain,
% 7.31/1.51      ( r2_hidden(sK8(k1_relat_1(sK11),X0,sK11),k1_relat_1(sK11))
% 7.31/1.51      | ~ r2_hidden(k1_funct_1(sK11,sK8(k1_relat_1(sK11),sK10,sK11)),sK10)
% 7.31/1.51      | ~ v1_relat_1(sK11)
% 7.31/1.51      | ~ v1_funct_1(sK11)
% 7.31/1.51      | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK11),X0)) != k1_zfmisc_1(k2_zfmisc_1(sK9,sK10))
% 7.31/1.51      | k1_relat_1(sK11) != sK9 ),
% 7.31/1.51      inference(unflattening,[status(thm)],[c_468]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_6423,plain,
% 7.31/1.51      ( r2_hidden(sK8(k1_relat_1(sK11),X0,sK11),k1_relat_1(sK11))
% 7.31/1.51      | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK11),X0)) != k1_zfmisc_1(k2_zfmisc_1(sK9,sK10))
% 7.31/1.51      | ~ sP0_iProver_split ),
% 7.31/1.51      inference(splitting,
% 7.31/1.51                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 7.31/1.51                [c_469]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_6962,plain,
% 7.31/1.51      ( k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK11),X0)) != k1_zfmisc_1(k2_zfmisc_1(sK9,sK10))
% 7.31/1.51      | r2_hidden(sK8(k1_relat_1(sK11),X0,sK11),k1_relat_1(sK11)) = iProver_top
% 7.31/1.51      | sP0_iProver_split != iProver_top ),
% 7.31/1.51      inference(predicate_to_equality,[status(thm)],[c_6423]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_8406,plain,
% 7.31/1.51      ( k1_zfmisc_1(k2_zfmisc_1(sK9,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK9,sK10))
% 7.31/1.51      | r2_hidden(sK8(sK9,X0,sK11),sK9) = iProver_top
% 7.31/1.51      | sP0_iProver_split != iProver_top ),
% 7.31/1.51      inference(demodulation,[status(thm)],[c_8370,c_6962]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_8607,plain,
% 7.31/1.51      ( r2_hidden(sK8(sK9,sK10,sK11),sK9) = iProver_top
% 7.31/1.51      | sP0_iProver_split != iProver_top ),
% 7.31/1.51      inference(equality_resolution,[status(thm)],[c_8406]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_26,plain,
% 7.31/1.51      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 7.31/1.51      | r2_hidden(sK8(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
% 7.31/1.51      | ~ v1_relat_1(X0)
% 7.31/1.51      | ~ v1_funct_1(X0) ),
% 7.31/1.51      inference(cnf_transformation,[],[f78]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_420,plain,
% 7.31/1.51      ( r2_hidden(sK8(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
% 7.31/1.51      | r2_hidden(sK8(k1_relat_1(sK11),X2,sK11),k1_relat_1(sK11))
% 7.31/1.51      | ~ v1_relat_1(X0)
% 7.31/1.51      | ~ v1_relat_1(sK11)
% 7.31/1.51      | ~ v1_funct_1(X0)
% 7.31/1.51      | ~ v1_funct_1(sK11)
% 7.31/1.51      | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK11),X2)) != k1_zfmisc_1(k2_zfmisc_1(sK9,sK10))
% 7.31/1.51      | k1_relat_1(X0) != sK9
% 7.31/1.51      | sK10 != X1
% 7.31/1.51      | sK11 != X0 ),
% 7.31/1.51      inference(resolution_lifted,[status(thm)],[c_26,c_343]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_421,plain,
% 7.31/1.51      ( r2_hidden(sK8(k1_relat_1(sK11),X0,sK11),k1_relat_1(sK11))
% 7.31/1.51      | r2_hidden(sK8(k1_relat_1(sK11),sK10,sK11),k1_relat_1(sK11))
% 7.31/1.51      | ~ v1_relat_1(sK11)
% 7.31/1.51      | ~ v1_funct_1(sK11)
% 7.31/1.51      | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK11),X0)) != k1_zfmisc_1(k2_zfmisc_1(sK9,sK10))
% 7.31/1.51      | k1_relat_1(sK11) != sK9 ),
% 7.31/1.51      inference(unflattening,[status(thm)],[c_420]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_6427,plain,
% 7.31/1.51      ( r2_hidden(sK8(k1_relat_1(sK11),sK10,sK11),k1_relat_1(sK11))
% 7.31/1.51      | ~ v1_relat_1(sK11)
% 7.31/1.51      | ~ v1_funct_1(sK11)
% 7.31/1.51      | sP0_iProver_split
% 7.31/1.51      | k1_relat_1(sK11) != sK9 ),
% 7.31/1.51      inference(splitting,
% 7.31/1.51                [splitting(split),new_symbols(definition,[])],
% 7.31/1.51                [c_421]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_6965,plain,
% 7.31/1.51      ( k1_relat_1(sK11) != sK9
% 7.31/1.51      | r2_hidden(sK8(k1_relat_1(sK11),sK10,sK11),k1_relat_1(sK11)) = iProver_top
% 7.31/1.51      | v1_relat_1(sK11) != iProver_top
% 7.31/1.51      | v1_funct_1(sK11) != iProver_top
% 7.31/1.51      | sP0_iProver_split = iProver_top ),
% 7.31/1.51      inference(predicate_to_equality,[status(thm)],[c_6427]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_8402,plain,
% 7.31/1.51      ( sK9 != sK9
% 7.31/1.51      | r2_hidden(sK8(sK9,sK10,sK11),sK9) = iProver_top
% 7.31/1.51      | v1_relat_1(sK11) != iProver_top
% 7.31/1.51      | v1_funct_1(sK11) != iProver_top
% 7.31/1.51      | sP0_iProver_split = iProver_top ),
% 7.31/1.51      inference(demodulation,[status(thm)],[c_8370,c_6965]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_8437,plain,
% 7.31/1.51      ( r2_hidden(sK8(sK9,sK10,sK11),sK9) = iProver_top
% 7.31/1.51      | v1_relat_1(sK11) != iProver_top
% 7.31/1.51      | v1_funct_1(sK11) != iProver_top
% 7.31/1.51      | sP0_iProver_split = iProver_top ),
% 7.31/1.51      inference(equality_resolution_simp,[status(thm)],[c_8402]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_8749,plain,
% 7.31/1.51      ( r2_hidden(sK8(sK9,sK10,sK11),sK9) = iProver_top ),
% 7.31/1.51      inference(global_propositional_subsumption,
% 7.31/1.51                [status(thm)],
% 7.31/1.51                [c_8607,c_30,c_31,c_6459,c_7383,c_7382,c_7385,c_7454,
% 7.31/1.51                 c_7451,c_7465,c_7629,c_7711,c_8437]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(contradiction,plain,
% 7.31/1.51      ( $false ),
% 7.31/1.51      inference(minisat,
% 7.31/1.51                [status(thm)],
% 7.31/1.51                [c_37648,c_10927,c_8749,c_7711,c_7629,c_7465,c_7451,
% 7.31/1.51                 c_7454,c_7385,c_7382,c_7383,c_6459,c_31,c_30]) ).
% 7.31/1.51  
% 7.31/1.51  
% 7.31/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 7.31/1.51  
% 7.31/1.51  ------                               Statistics
% 7.31/1.51  
% 7.31/1.51  ------ General
% 7.31/1.51  
% 7.31/1.51  abstr_ref_over_cycles:                  0
% 7.31/1.51  abstr_ref_under_cycles:                 0
% 7.31/1.51  gc_basic_clause_elim:                   0
% 7.31/1.51  forced_gc_time:                         0
% 7.31/1.51  parsing_time:                           0.009
% 7.31/1.51  unif_index_cands_time:                  0.
% 7.31/1.51  unif_index_add_time:                    0.
% 7.31/1.51  orderings_time:                         0.
% 7.31/1.51  out_proof_time:                         0.016
% 7.31/1.51  total_time:                             0.974
% 7.31/1.51  num_of_symbols:                         57
% 7.31/1.51  num_of_terms:                           29252
% 7.31/1.51  
% 7.31/1.51  ------ Preprocessing
% 7.31/1.51  
% 7.31/1.51  num_of_splits:                          4
% 7.31/1.51  num_of_split_atoms:                     2
% 7.31/1.51  num_of_reused_defs:                     2
% 7.31/1.51  num_eq_ax_congr_red:                    57
% 7.31/1.51  num_of_sem_filtered_clauses:            1
% 7.31/1.51  num_of_subtypes:                        0
% 7.31/1.51  monotx_restored_types:                  0
% 7.31/1.51  sat_num_of_epr_types:                   0
% 7.31/1.51  sat_num_of_non_cyclic_types:            0
% 7.31/1.51  sat_guarded_non_collapsed_types:        0
% 7.31/1.51  num_pure_diseq_elim:                    0
% 7.31/1.51  simp_replaced_by:                       0
% 7.31/1.51  res_preprocessed:                       148
% 7.31/1.51  prep_upred:                             0
% 7.31/1.51  prep_unflattend:                        222
% 7.31/1.51  smt_new_axioms:                         0
% 7.31/1.51  pred_elim_cands:                        5
% 7.31/1.51  pred_elim:                              2
% 7.31/1.51  pred_elim_cl:                           1
% 7.31/1.51  pred_elim_cycles:                       10
% 7.31/1.51  merged_defs:                            0
% 7.31/1.51  merged_defs_ncl:                        0
% 7.31/1.51  bin_hyper_res:                          0
% 7.31/1.51  prep_cycles:                            4
% 7.31/1.51  pred_elim_time:                         0.091
% 7.31/1.51  splitting_time:                         0.
% 7.31/1.51  sem_filter_time:                        0.
% 7.31/1.51  monotx_time:                            0.001
% 7.31/1.51  subtype_inf_time:                       0.
% 7.31/1.51  
% 7.31/1.51  ------ Problem properties
% 7.31/1.51  
% 7.31/1.51  clauses:                                32
% 7.31/1.51  conjectures:                            1
% 7.31/1.51  epr:                                    1
% 7.31/1.51  horn:                                   22
% 7.31/1.51  ground:                                 5
% 7.31/1.51  unary:                                  2
% 7.31/1.51  binary:                                 3
% 7.31/1.51  lits:                                   112
% 7.31/1.51  lits_eq:                                20
% 7.31/1.51  fd_pure:                                0
% 7.31/1.51  fd_pseudo:                              0
% 7.31/1.51  fd_cond:                                0
% 7.31/1.51  fd_pseudo_cond:                         4
% 7.31/1.51  ac_symbols:                             0
% 7.31/1.51  
% 7.31/1.51  ------ Propositional Solver
% 7.31/1.51  
% 7.31/1.51  prop_solver_calls:                      31
% 7.31/1.51  prop_fast_solver_calls:                 3325
% 7.31/1.51  smt_solver_calls:                       0
% 7.31/1.51  smt_fast_solver_calls:                  0
% 7.31/1.51  prop_num_of_clauses:                    11073
% 7.31/1.51  prop_preprocess_simplified:             19297
% 7.31/1.51  prop_fo_subsumed:                       110
% 7.31/1.51  prop_solver_time:                       0.
% 7.31/1.51  smt_solver_time:                        0.
% 7.31/1.51  smt_fast_solver_time:                   0.
% 7.31/1.51  prop_fast_solver_time:                  0.
% 7.31/1.51  prop_unsat_core_time:                   0.
% 7.31/1.51  
% 7.31/1.51  ------ QBF
% 7.31/1.51  
% 7.31/1.51  qbf_q_res:                              0
% 7.31/1.51  qbf_num_tautologies:                    0
% 7.31/1.51  qbf_prep_cycles:                        0
% 7.31/1.51  
% 7.31/1.51  ------ BMC1
% 7.31/1.51  
% 7.31/1.51  bmc1_current_bound:                     -1
% 7.31/1.51  bmc1_last_solved_bound:                 -1
% 7.31/1.51  bmc1_unsat_core_size:                   -1
% 7.31/1.51  bmc1_unsat_core_parents_size:           -1
% 7.31/1.51  bmc1_merge_next_fun:                    0
% 7.31/1.51  bmc1_unsat_core_clauses_time:           0.
% 7.31/1.51  
% 7.31/1.51  ------ Instantiation
% 7.31/1.51  
% 7.31/1.51  inst_num_of_clauses:                    2100
% 7.31/1.51  inst_num_in_passive:                    729
% 7.31/1.51  inst_num_in_active:                     831
% 7.31/1.51  inst_num_in_unprocessed:                540
% 7.31/1.51  inst_num_of_loops:                      1130
% 7.31/1.51  inst_num_of_learning_restarts:          0
% 7.31/1.51  inst_num_moves_active_passive:          294
% 7.31/1.51  inst_lit_activity:                      0
% 7.31/1.51  inst_lit_activity_moves:                0
% 7.31/1.51  inst_num_tautologies:                   0
% 7.31/1.51  inst_num_prop_implied:                  0
% 7.31/1.51  inst_num_existing_simplified:           0
% 7.31/1.51  inst_num_eq_res_simplified:             0
% 7.31/1.51  inst_num_child_elim:                    0
% 7.31/1.51  inst_num_of_dismatching_blockings:      2441
% 7.31/1.51  inst_num_of_non_proper_insts:           2891
% 7.31/1.51  inst_num_of_duplicates:                 0
% 7.31/1.51  inst_inst_num_from_inst_to_res:         0
% 7.31/1.51  inst_dismatching_checking_time:         0.
% 7.31/1.51  
% 7.31/1.51  ------ Resolution
% 7.31/1.51  
% 7.31/1.51  res_num_of_clauses:                     0
% 7.31/1.51  res_num_in_passive:                     0
% 7.31/1.51  res_num_in_active:                      0
% 7.31/1.51  res_num_of_loops:                       152
% 7.31/1.51  res_forward_subset_subsumed:            114
% 7.31/1.51  res_backward_subset_subsumed:           10
% 7.31/1.51  res_forward_subsumed:                   0
% 7.31/1.51  res_backward_subsumed:                  0
% 7.31/1.51  res_forward_subsumption_resolution:     2
% 7.31/1.51  res_backward_subsumption_resolution:    0
% 7.31/1.51  res_clause_to_clause_subsumption:       4752
% 7.31/1.51  res_orphan_elimination:                 0
% 7.31/1.51  res_tautology_del:                      156
% 7.31/1.51  res_num_eq_res_simplified:              0
% 7.31/1.51  res_num_sel_changes:                    0
% 7.31/1.51  res_moves_from_active_to_pass:          0
% 7.31/1.51  
% 7.31/1.51  ------ Superposition
% 7.31/1.51  
% 7.31/1.51  sup_time_total:                         0.
% 7.31/1.51  sup_time_generating:                    0.
% 7.31/1.51  sup_time_sim_full:                      0.
% 7.31/1.51  sup_time_sim_immed:                     0.
% 7.31/1.51  
% 7.31/1.51  sup_num_of_clauses:                     1128
% 7.31/1.51  sup_num_in_active:                      219
% 7.31/1.51  sup_num_in_passive:                     909
% 7.31/1.51  sup_num_of_loops:                       225
% 7.31/1.51  sup_fw_superposition:                   565
% 7.31/1.51  sup_bw_superposition:                   677
% 7.31/1.51  sup_immediate_simplified:               90
% 7.31/1.51  sup_given_eliminated:                   0
% 7.31/1.51  comparisons_done:                       0
% 7.31/1.51  comparisons_avoided:                    193
% 7.31/1.51  
% 7.31/1.51  ------ Simplifications
% 7.31/1.51  
% 7.31/1.51  
% 7.31/1.51  sim_fw_subset_subsumed:                 20
% 7.31/1.51  sim_bw_subset_subsumed:                 15
% 7.31/1.51  sim_fw_subsumed:                        15
% 7.31/1.51  sim_bw_subsumed:                        5
% 7.31/1.51  sim_fw_subsumption_res:                 0
% 7.31/1.51  sim_bw_subsumption_res:                 0
% 7.31/1.51  sim_tautology_del:                      33
% 7.31/1.51  sim_eq_tautology_del:                   13
% 7.31/1.51  sim_eq_res_simp:                        7
% 7.31/1.51  sim_fw_demodulated:                     0
% 7.31/1.51  sim_bw_demodulated:                     7
% 7.31/1.51  sim_light_normalised:                   42
% 7.31/1.51  sim_joinable_taut:                      0
% 7.31/1.51  sim_joinable_simp:                      0
% 7.31/1.51  sim_ac_normalised:                      0
% 7.31/1.51  sim_smt_subsumption:                    0
% 7.31/1.51  
%------------------------------------------------------------------------------
