%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:08:14 EST 2020

% Result     : Theorem 27.19s
% Output     : CNFRefutation 27.19s
% Verified   : 
% Statistics : Number of formulae       :  278 (4206 expanded)
%              Number of clauses        :  185 (1428 expanded)
%              Number of leaves         :   30 (1074 expanded)
%              Depth                    :   23
%              Number of atoms          :  993 (25630 expanded)
%              Number of equality atoms :  394 (7787 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
     => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X2,k1_funct_2(X0,X1))
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f35,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2) )
      & r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f59,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2) )
        & r2_hidden(X2,k1_funct_2(X0,X1)) )
   => ( ( ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9)))
        | ~ v1_funct_2(sK10,sK8,sK9)
        | ~ v1_funct_1(sK10) )
      & r2_hidden(sK10,k1_funct_2(sK8,sK9)) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,
    ( ( ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9)))
      | ~ v1_funct_2(sK10,sK8,sK9)
      | ~ v1_funct_1(sK10) )
    & r2_hidden(sK10,k1_funct_2(sK8,sK9)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f35,f59])).

fof(f105,plain,(
    r2_hidden(sK10,k1_funct_2(sK8,sK9)) ),
    inference(cnf_transformation,[],[f60])).

fof(f13,axiom,(
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

fof(f36,plain,(
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

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_2(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f13,f36])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( ( k1_funct_2(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k1_funct_2(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f58])).

fof(f116,plain,(
    ! [X0,X1] : sP0(X1,X0,k1_funct_2(X0,X1)) ),
    inference(equality_resolution,[],[f98])).

fof(f52,plain,(
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
    inference(nnf_transformation,[],[f36])).

fof(f53,plain,(
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
    inference(rectify,[],[f52])).

fof(f56,plain,(
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

fof(f55,plain,(
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

fof(f54,plain,(
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

fof(f57,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f53,f56,f55,f54])).

fof(f89,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_relat_1(sK7(X0,X1,X6)) = X1
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f88,plain,(
    ! [X6,X2,X0,X1] :
      ( sK7(X0,X1,X6) = X6
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f6,axiom,(
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

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f47,plain,(
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
    inference(rectify,[],[f46])).

fof(f50,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X5)) = X5
        & r2_hidden(sK4(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X1)) = X2
        & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
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

fof(f51,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f47,f50,f49,f48])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | r2_hidden(sK3(X0,X1),k1_relat_1(X0))
      | r2_hidden(sK2(X0,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f42])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f108,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f64])).

fof(f66,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f87,plain,(
    ! [X6,X2,X0,X1] :
      ( v1_funct_1(sK7(X0,X1,X6))
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f86,plain,(
    ! [X6,X2,X0,X1] :
      ( v1_relat_1(sK7(X0,X1,X6))
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f90,plain,(
    ! [X6,X2,X0,X1] :
      ( r1_tarski(k2_relat_1(sK7(X0,X1,X6)),X0)
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f74,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f109,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f74])).

fof(f110,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f109])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f31])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f15,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f34,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f103,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f104,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f29])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f106,plain,
    ( ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9)))
    | ~ v1_funct_2(sK10,sK8,sK9)
    | ~ v1_funct_1(sK10) ),
    inference(cnf_transformation,[],[f60])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f107,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f65])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f38])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f39,f40])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f14,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f101,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f100,plain,(
    ! [X0] : v1_partfun1(k6_partfun1(X0),X0) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_20,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_126212,plain,
    ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9)))
    | ~ r1_tarski(k1_relat_1(sK10),sK8)
    | ~ r1_tarski(k2_relat_1(sK10),sK9)
    | ~ v1_relat_1(sK10) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_7117,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_11699,plain,
    ( ~ r1_tarski(X0,sK10)
    | r1_tarski(k6_partfun1(sK8),sK10)
    | k6_partfun1(sK8) != X0 ),
    inference(instantiation,[status(thm)],[c_7117])).

cnf(c_107811,plain,
    ( ~ r1_tarski(k6_partfun1(X0),sK10)
    | r1_tarski(k6_partfun1(sK8),sK10)
    | k6_partfun1(sK8) != k6_partfun1(X0) ),
    inference(instantiation,[status(thm)],[c_11699])).

cnf(c_107813,plain,
    ( r1_tarski(k6_partfun1(sK8),sK10)
    | ~ r1_tarski(k6_partfun1(sK10),sK10)
    | k6_partfun1(sK8) != k6_partfun1(sK10) ),
    inference(instantiation,[status(thm)],[c_107811])).

cnf(c_45,negated_conjecture,
    ( r2_hidden(sK10,k1_funct_2(sK8,sK9)) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_7990,plain,
    ( r2_hidden(sK10,k1_funct_2(sK8,sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_38,plain,
    ( sP0(X0,X1,k1_funct_2(X1,X0)) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_7993,plain,
    ( sP0(X0,X1,k1_funct_2(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_33,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,X2)
    | k1_relat_1(sK7(X0,X1,X3)) = X1 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_7998,plain,
    ( k1_relat_1(sK7(X0,X1,X2)) = X1
    | sP0(X0,X1,X3) != iProver_top
    | r2_hidden(X2,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_9765,plain,
    ( k1_relat_1(sK7(X0,X1,X2)) = X1
    | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7993,c_7998])).

cnf(c_12292,plain,
    ( k1_relat_1(sK7(sK9,sK8,sK10)) = sK8 ),
    inference(superposition,[status(thm)],[c_7990,c_9765])).

cnf(c_34,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,X2)
    | sK7(X0,X1,X3) = X3 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_7997,plain,
    ( sK7(X0,X1,X2) = X2
    | sP0(X0,X1,X3) != iProver_top
    | r2_hidden(X2,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_9260,plain,
    ( sK7(X0,X1,X2) = X2
    | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7993,c_7997])).

cnf(c_10428,plain,
    ( sK7(sK9,sK8,sK10) = sK10 ),
    inference(superposition,[status(thm)],[c_7990,c_9260])).

cnf(c_12294,plain,
    ( k1_relat_1(sK10) = sK8 ),
    inference(light_normalisation,[status(thm)],[c_12292,c_10428])).

cnf(c_13,plain,
    ( r2_hidden(sK3(X0,X1),k1_relat_1(X0))
    | r2_hidden(sK2(X0,X1),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_8013,plain,
    ( k2_relat_1(X0) = X1
    | r2_hidden(sK3(X0,X1),k1_relat_1(X0)) = iProver_top
    | r2_hidden(sK2(X0,X1),X1) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_12892,plain,
    ( k2_relat_1(sK10) = X0
    | r2_hidden(sK3(sK10,X0),sK8) = iProver_top
    | r2_hidden(sK2(sK10,X0),X0) = iProver_top
    | v1_funct_1(sK10) != iProver_top
    | v1_relat_1(sK10) != iProver_top ),
    inference(superposition,[status(thm)],[c_12294,c_8013])).

cnf(c_46,plain,
    ( r2_hidden(sK10,k1_funct_2(sK8,sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_155,plain,
    ( r1_tarski(sK10,sK10) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_159,plain,
    ( ~ r1_tarski(sK10,sK10)
    | sK10 = sK10 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_35,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,X2)
    | v1_funct_1(sK7(X0,X1,X3)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_8377,plain,
    ( ~ sP0(X0,X1,k1_funct_2(sK8,sK9))
    | ~ r2_hidden(sK10,k1_funct_2(sK8,sK9))
    | v1_funct_1(sK7(X0,X1,sK10)) ),
    inference(instantiation,[status(thm)],[c_35])).

cnf(c_8484,plain,
    ( ~ sP0(sK9,sK8,k1_funct_2(sK8,sK9))
    | ~ r2_hidden(sK10,k1_funct_2(sK8,sK9))
    | v1_funct_1(sK7(sK9,sK8,sK10)) ),
    inference(instantiation,[status(thm)],[c_8377])).

cnf(c_8486,plain,
    ( sP0(sK9,sK8,k1_funct_2(sK8,sK9)) != iProver_top
    | r2_hidden(sK10,k1_funct_2(sK8,sK9)) != iProver_top
    | v1_funct_1(sK7(sK9,sK8,sK10)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8484])).

cnf(c_8485,plain,
    ( sP0(sK9,sK8,k1_funct_2(sK8,sK9)) ),
    inference(instantiation,[status(thm)],[c_38])).

cnf(c_8488,plain,
    ( sP0(sK9,sK8,k1_funct_2(sK8,sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8485])).

cnf(c_7126,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_8635,plain,
    ( v1_funct_1(X0)
    | ~ v1_funct_1(sK7(sK9,sK8,sK10))
    | X0 != sK7(sK9,sK8,sK10) ),
    inference(instantiation,[status(thm)],[c_7126])).

cnf(c_8636,plain,
    ( X0 != sK7(sK9,sK8,sK10)
    | v1_funct_1(X0) = iProver_top
    | v1_funct_1(sK7(sK9,sK8,sK10)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8635])).

cnf(c_8638,plain,
    ( sK10 != sK7(sK9,sK8,sK10)
    | v1_funct_1(sK7(sK9,sK8,sK10)) != iProver_top
    | v1_funct_1(sK10) = iProver_top ),
    inference(instantiation,[status(thm)],[c_8636])).

cnf(c_8412,plain,
    ( ~ sP0(X0,X1,k1_funct_2(sK8,sK9))
    | ~ r2_hidden(sK10,k1_funct_2(sK8,sK9))
    | sK7(X0,X1,sK10) = sK10 ),
    inference(instantiation,[status(thm)],[c_34])).

cnf(c_8682,plain,
    ( ~ sP0(sK9,sK8,k1_funct_2(sK8,sK9))
    | ~ r2_hidden(sK10,k1_funct_2(sK8,sK9))
    | sK7(sK9,sK8,sK10) = sK10 ),
    inference(instantiation,[status(thm)],[c_8412])).

cnf(c_7116,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_8834,plain,
    ( X0 != X1
    | X0 = sK7(sK9,sK8,sK10)
    | sK7(sK9,sK8,sK10) != X1 ),
    inference(instantiation,[status(thm)],[c_7116])).

cnf(c_8835,plain,
    ( sK7(sK9,sK8,sK10) != sK10
    | sK10 = sK7(sK9,sK8,sK10)
    | sK10 != sK10 ),
    inference(instantiation,[status(thm)],[c_8834])).

cnf(c_36,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,X2)
    | v1_relat_1(sK7(X0,X1,X3)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_7995,plain,
    ( sP0(X0,X1,X2) != iProver_top
    | r2_hidden(X3,X2) != iProver_top
    | v1_relat_1(sK7(X0,X1,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_9724,plain,
    ( r2_hidden(X0,k1_funct_2(X1,X2)) != iProver_top
    | v1_relat_1(sK7(X2,X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7993,c_7995])).

cnf(c_11552,plain,
    ( v1_relat_1(sK7(sK9,sK8,sK10)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7990,c_9724])).

cnf(c_11554,plain,
    ( v1_relat_1(sK10) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11552,c_10428])).

cnf(c_13512,plain,
    ( k2_relat_1(sK10) = X0
    | r2_hidden(sK3(sK10,X0),sK8) = iProver_top
    | r2_hidden(sK2(sK10,X0),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12892,c_45,c_46,c_155,c_159,c_8486,c_8485,c_8488,c_8638,c_8682,c_8835,c_11554])).

cnf(c_32,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,X2)
    | r1_tarski(k2_relat_1(sK7(X0,X1,X3)),X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_7999,plain,
    ( sP0(X0,X1,X2) != iProver_top
    | r2_hidden(X3,X2) != iProver_top
    | r1_tarski(k2_relat_1(sK7(X0,X1,X3)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_10487,plain,
    ( r2_hidden(X0,k1_funct_2(X1,X2)) != iProver_top
    | r1_tarski(k2_relat_1(sK7(X2,X1,X0)),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_7993,c_7999])).

cnf(c_16334,plain,
    ( r2_hidden(sK10,k1_funct_2(sK8,sK9)) != iProver_top
    | r1_tarski(k2_relat_1(sK10),sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_10428,c_10487])).

cnf(c_17008,plain,
    ( r1_tarski(k2_relat_1(sK10),sK9) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16334,c_46])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_8012,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_6,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_350,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_6])).

cnf(c_351,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_350])).

cnf(c_431,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(bin_hyper_res,[status(thm)],[c_8,c_351])).

cnf(c_7989,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | v1_xboole_0(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_431])).

cnf(c_12088,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r1_tarski(k2_relat_1(X1),X2) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_xboole_0(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_8012,c_7989])).

cnf(c_91260,plain,
    ( r2_hidden(X0,sK8) != iProver_top
    | r1_tarski(k2_relat_1(sK10),X1) != iProver_top
    | v1_funct_1(sK10) != iProver_top
    | v1_relat_1(sK10) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_12294,c_12088])).

cnf(c_91905,plain,
    ( r2_hidden(X0,sK8) != iProver_top
    | r1_tarski(k2_relat_1(sK10),X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_91260,c_45,c_46,c_155,c_159,c_8486,c_8485,c_8488,c_8638,c_8682,c_8835,c_11554])).

cnf(c_91924,plain,
    ( r2_hidden(X0,sK8) != iProver_top
    | v1_xboole_0(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_17008,c_91905])).

cnf(c_8007,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_42,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_645,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(X3)
    | v1_xboole_0(X2)
    | X3 != X0
    | k1_relat_1(X3) != X1
    | k2_relat_1(X3) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_42])).

cnf(c_646,plain,
    ( v1_partfun1(X0,k1_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_xboole_0(k2_relat_1(X0)) ),
    inference(unflattening,[status(thm)],[c_645])).

cnf(c_41,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_650,plain,
    ( v1_partfun1(X0,k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_xboole_0(k2_relat_1(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_646,c_41])).

cnf(c_21,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_44,negated_conjecture,
    ( ~ v1_funct_2(sK10,sK8,sK9)
    | ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9)))
    | ~ v1_funct_1(sK10) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_669,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK10)
    | sK9 != X2
    | sK8 != X1
    | sK10 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_44])).

cnf(c_670,plain,
    ( ~ v1_partfun1(sK10,sK8)
    | ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9)))
    | ~ v1_funct_1(sK10) ),
    inference(unflattening,[status(thm)],[c_669])).

cnf(c_728,plain,
    ( ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK10)
    | ~ v1_relat_1(X0)
    | v1_xboole_0(k2_relat_1(X0))
    | k1_relat_1(X0) != sK8
    | sK10 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_650,c_670])).

cnf(c_729,plain,
    ( ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9)))
    | ~ v1_funct_1(sK10)
    | ~ v1_relat_1(sK10)
    | v1_xboole_0(k2_relat_1(sK10))
    | k1_relat_1(sK10) != sK8 ),
    inference(unflattening,[status(thm)],[c_728])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_741,plain,
    ( ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9)))
    | ~ v1_funct_1(sK10)
    | v1_xboole_0(k2_relat_1(sK10))
    | k1_relat_1(sK10) != sK8 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_729,c_17])).

cnf(c_7985,plain,
    ( k1_relat_1(sK10) != sK8
    | m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))) != iProver_top
    | v1_funct_1(sK10) != iProver_top
    | v1_xboole_0(k2_relat_1(sK10)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_741])).

cnf(c_12339,plain,
    ( sK8 != sK8
    | m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))) != iProver_top
    | v1_funct_1(sK10) != iProver_top
    | v1_xboole_0(k2_relat_1(sK10)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_12294,c_7985])).

cnf(c_12348,plain,
    ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))) != iProver_top
    | v1_funct_1(sK10) != iProver_top
    | v1_xboole_0(k2_relat_1(sK10)) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_12339])).

cnf(c_730,plain,
    ( k1_relat_1(sK10) != sK8
    | m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))) != iProver_top
    | v1_funct_1(sK10) != iProver_top
    | v1_relat_1(sK10) != iProver_top
    | v1_xboole_0(k2_relat_1(sK10)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_729])).

cnf(c_13965,plain,
    ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))) != iProver_top
    | v1_xboole_0(k2_relat_1(sK10)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12348,c_45,c_46,c_155,c_159,c_730,c_8486,c_8485,c_8488,c_8638,c_8682,c_8835,c_11554,c_12294])).

cnf(c_13972,plain,
    ( r1_tarski(k1_relat_1(sK10),sK8) != iProver_top
    | r1_tarski(k2_relat_1(sK10),sK9) != iProver_top
    | v1_relat_1(sK10) != iProver_top
    | v1_xboole_0(k2_relat_1(sK10)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8007,c_13965])).

cnf(c_13977,plain,
    ( r1_tarski(k2_relat_1(sK10),sK9) != iProver_top
    | r1_tarski(sK8,sK8) != iProver_top
    | v1_relat_1(sK10) != iProver_top
    | v1_xboole_0(k2_relat_1(sK10)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13972,c_12294])).

cnf(c_14123,plain,
    ( r1_tarski(sK8,sK8) != iProver_top
    | r1_tarski(k2_relat_1(sK10),sK9) != iProver_top
    | v1_xboole_0(k2_relat_1(sK10)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13977,c_11554])).

cnf(c_14124,plain,
    ( r1_tarski(k2_relat_1(sK10),sK9) != iProver_top
    | r1_tarski(sK8,sK8) != iProver_top
    | v1_xboole_0(k2_relat_1(sK10)) = iProver_top ),
    inference(renaming,[status(thm)],[c_14123])).

cnf(c_4,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_8018,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_14130,plain,
    ( r1_tarski(k2_relat_1(sK10),sK9) != iProver_top
    | v1_xboole_0(k2_relat_1(sK10)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_14124,c_8018])).

cnf(c_91915,plain,
    ( r2_hidden(X0,sK8) != iProver_top
    | v1_xboole_0(k2_relat_1(sK10)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8018,c_91905])).

cnf(c_92161,plain,
    ( r2_hidden(X0,sK8) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_91924,c_46,c_14130,c_16334,c_91915])).

cnf(c_92197,plain,
    ( k2_relat_1(sK10) = sK8
    | r2_hidden(sK3(sK10,sK8),sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_13512,c_92161])).

cnf(c_92254,plain,
    ( k2_relat_1(sK10) = sK8 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_92197,c_92161])).

cnf(c_1,plain,
    ( r2_hidden(sK1(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_8021,plain,
    ( r2_hidden(sK1(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_91226,plain,
    ( r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_xboole_0(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_8021,c_12088])).

cnf(c_91794,plain,
    ( r1_tarski(k1_relat_1(sK10),sK10) = iProver_top
    | r1_tarski(k2_relat_1(sK10),sK10) != iProver_top
    | v1_funct_1(sK10) != iProver_top
    | v1_relat_1(sK10) != iProver_top
    | v1_xboole_0(sK10) != iProver_top ),
    inference(instantiation,[status(thm)],[c_91226])).

cnf(c_91162,plain,
    ( ~ r2_hidden(sK1(sK10,k6_partfun1(sK8)),sK10)
    | ~ r1_tarski(sK10,X0)
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_431])).

cnf(c_91177,plain,
    ( ~ r2_hidden(sK1(sK10,k6_partfun1(sK8)),sK10)
    | ~ r1_tarski(sK10,sK10)
    | ~ v1_xboole_0(sK10) ),
    inference(instantiation,[status(thm)],[c_91162])).

cnf(c_19089,plain,
    ( X0 != X1
    | X0 = k1_relat_1(sK7(sK9,sK8,sK10))
    | k1_relat_1(sK7(sK9,sK8,sK10)) != X1 ),
    inference(instantiation,[status(thm)],[c_7116])).

cnf(c_84625,plain,
    ( X0 = k1_relat_1(sK7(sK9,sK8,sK10))
    | X0 != k2_relat_1(X1)
    | k1_relat_1(sK7(sK9,sK8,sK10)) != k2_relat_1(X1) ),
    inference(instantiation,[status(thm)],[c_19089])).

cnf(c_84629,plain,
    ( k1_relat_1(sK7(sK9,sK8,sK10)) != k2_relat_1(sK10)
    | sK10 = k1_relat_1(sK7(sK9,sK8,sK10))
    | sK10 != k2_relat_1(sK10) ),
    inference(instantiation,[status(thm)],[c_84625])).

cnf(c_11792,plain,
    ( X0 != X1
    | sK8 != X1
    | sK8 = X0 ),
    inference(instantiation,[status(thm)],[c_7116])).

cnf(c_70134,plain,
    ( X0 != k1_relat_1(sK7(sK9,sK8,sK10))
    | sK8 = X0
    | sK8 != k1_relat_1(sK7(sK9,sK8,sK10)) ),
    inference(instantiation,[status(thm)],[c_11792])).

cnf(c_70135,plain,
    ( sK8 != k1_relat_1(sK7(sK9,sK8,sK10))
    | sK8 = sK10
    | sK10 != k1_relat_1(sK7(sK9,sK8,sK10)) ),
    inference(instantiation,[status(thm)],[c_70134])).

cnf(c_23324,plain,
    ( X0 != sK8
    | sK8 = X0
    | sK8 != sK8 ),
    inference(instantiation,[status(thm)],[c_11792])).

cnf(c_60264,plain,
    ( k1_relat_1(sK7(sK9,sK8,sK10)) != sK8
    | sK8 = k1_relat_1(sK7(sK9,sK8,sK10))
    | sK8 != sK8 ),
    inference(instantiation,[status(thm)],[c_23324])).

cnf(c_57169,plain,
    ( ~ r2_hidden(sK1(k1_relat_1(sK10),sK8),k1_relat_1(sK10))
    | ~ r1_tarski(k1_relat_1(sK10),X0)
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_431])).

cnf(c_57186,plain,
    ( ~ r2_hidden(sK1(k1_relat_1(sK10),sK8),k1_relat_1(sK10))
    | ~ r1_tarski(k1_relat_1(sK10),sK10)
    | ~ v1_xboole_0(sK10) ),
    inference(instantiation,[status(thm)],[c_57169])).

cnf(c_52443,plain,
    ( ~ r2_hidden(sK1(X0,k1_relat_1(X1)),X0)
    | ~ r1_tarski(X0,X2)
    | ~ v1_xboole_0(X2) ),
    inference(instantiation,[status(thm)],[c_431])).

cnf(c_52457,plain,
    ( r2_hidden(sK1(X0,k1_relat_1(X1)),X0) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | v1_xboole_0(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_52443])).

cnf(c_52459,plain,
    ( r2_hidden(sK1(sK10,k1_relat_1(sK10)),sK10) != iProver_top
    | r1_tarski(sK10,sK10) != iProver_top
    | v1_xboole_0(sK10) != iProver_top ),
    inference(instantiation,[status(thm)],[c_52457])).

cnf(c_31466,plain,
    ( ~ r2_hidden(sK2(X0,X1),X1)
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(instantiation,[status(thm)],[c_431])).

cnf(c_31480,plain,
    ( r2_hidden(sK2(X0,X1),X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | v1_xboole_0(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31466])).

cnf(c_31482,plain,
    ( r2_hidden(sK2(sK10,sK10),sK10) != iProver_top
    | r1_tarski(sK10,sK10) != iProver_top
    | v1_xboole_0(sK10) != iProver_top ),
    inference(instantiation,[status(thm)],[c_31480])).

cnf(c_29247,plain,
    ( X0 != X1
    | X0 = k2_relat_1(X2)
    | k2_relat_1(X2) != X1 ),
    inference(instantiation,[status(thm)],[c_7116])).

cnf(c_29248,plain,
    ( k2_relat_1(sK10) != sK10
    | sK10 = k2_relat_1(sK10)
    | sK10 != sK10 ),
    inference(instantiation,[status(thm)],[c_29247])).

cnf(c_20178,plain,
    ( r2_hidden(sK1(sK10,k6_partfun1(sK8)),sK10)
    | r1_tarski(sK10,k6_partfun1(sK8)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_18835,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(X2),X1)
    | k1_relat_1(X2) != X0 ),
    inference(instantiation,[status(thm)],[c_7117])).

cnf(c_18837,plain,
    ( r1_tarski(k1_relat_1(sK10),sK10)
    | ~ r1_tarski(sK10,sK10)
    | k1_relat_1(sK10) != sK10 ),
    inference(instantiation,[status(thm)],[c_18835])).

cnf(c_10851,plain,
    ( X0 != X1
    | k1_relat_1(sK7(sK9,sK8,sK10)) != X1
    | k1_relat_1(sK7(sK9,sK8,sK10)) = X0 ),
    inference(instantiation,[status(thm)],[c_7116])).

cnf(c_16252,plain,
    ( X0 != sK8
    | k1_relat_1(sK7(sK9,sK8,sK10)) = X0
    | k1_relat_1(sK7(sK9,sK8,sK10)) != sK8 ),
    inference(instantiation,[status(thm)],[c_10851])).

cnf(c_18021,plain,
    ( k1_relat_1(sK7(sK9,sK8,sK10)) = k2_relat_1(X0)
    | k1_relat_1(sK7(sK9,sK8,sK10)) != sK8
    | k2_relat_1(X0) != sK8 ),
    inference(instantiation,[status(thm)],[c_16252])).

cnf(c_18023,plain,
    ( k1_relat_1(sK7(sK9,sK8,sK10)) = k2_relat_1(sK10)
    | k1_relat_1(sK7(sK9,sK8,sK10)) != sK8
    | k2_relat_1(sK10) != sK8 ),
    inference(instantiation,[status(thm)],[c_18021])).

cnf(c_16386,plain,
    ( ~ r2_hidden(sK10,k1_funct_2(sK8,sK9))
    | r1_tarski(k2_relat_1(sK10),sK9) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_16334])).

cnf(c_8017,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_8008,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_9165,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_8017,c_8008])).

cnf(c_16022,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8018,c_9165])).

cnf(c_16068,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_zfmisc_1(X1,X0)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_16022])).

cnf(c_16070,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK10,sK10))
    | ~ v1_xboole_0(sK10) ),
    inference(instantiation,[status(thm)],[c_16068])).

cnf(c_15631,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ r1_tarski(k1_relat_1(X1),X0)
    | k1_relat_1(X1) = X0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_15632,plain,
    ( k1_relat_1(X0) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15631])).

cnf(c_15634,plain,
    ( k1_relat_1(sK10) = sK10
    | r1_tarski(k1_relat_1(sK10),sK10) != iProver_top
    | r1_tarski(sK10,k1_relat_1(sK10)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_15632])).

cnf(c_9042,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,X2) = iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_8021,c_7989])).

cnf(c_14550,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8018,c_9042])).

cnf(c_18,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_10,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_578,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_18,c_10])).

cnf(c_582,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_578,c_17])).

cnf(c_583,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_582])).

cnf(c_7988,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_583])).

cnf(c_8526,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_8017,c_7988])).

cnf(c_14815,plain,
    ( r1_tarski(k2_relat_1(X0),X1) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_14550,c_8526])).

cnf(c_14861,plain,
    ( r1_tarski(k2_relat_1(sK10),sK10) = iProver_top
    | v1_xboole_0(sK10) != iProver_top ),
    inference(instantiation,[status(thm)],[c_14815])).

cnf(c_39,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_7992,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_8016,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_8434,plain,
    ( r1_tarski(k6_partfun1(X0),k2_zfmisc_1(X0,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7992,c_8016])).

cnf(c_14552,plain,
    ( r1_tarski(k6_partfun1(X0),X1) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(X0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8434,c_9042])).

cnf(c_14606,plain,
    ( r1_tarski(k6_partfun1(X0),X1)
    | ~ v1_xboole_0(k2_zfmisc_1(X0,X0)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_14552])).

cnf(c_14608,plain,
    ( r1_tarski(k6_partfun1(sK10),sK10)
    | ~ v1_xboole_0(k2_zfmisc_1(sK10,sK10)) ),
    inference(instantiation,[status(thm)],[c_14606])).

cnf(c_14131,plain,
    ( ~ r1_tarski(k2_relat_1(sK10),sK9)
    | v1_xboole_0(k2_relat_1(sK10)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_14130])).

cnf(c_13829,plain,
    ( r2_hidden(sK1(X0,k1_relat_1(X1)),X0)
    | r1_tarski(X0,k1_relat_1(X1)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_13840,plain,
    ( r2_hidden(sK1(X0,k1_relat_1(X1)),X0) = iProver_top
    | r1_tarski(X0,k1_relat_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13829])).

cnf(c_13842,plain,
    ( r2_hidden(sK1(sK10,k1_relat_1(sK10)),sK10) = iProver_top
    | r1_tarski(sK10,k1_relat_1(sK10)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_13840])).

cnf(c_12901,plain,
    ( k2_relat_1(X0) = X1
    | r2_hidden(sK2(X0,X1),X1) = iProver_top
    | r1_tarski(k1_relat_1(X0),X2) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_xboole_0(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_8013,c_7989])).

cnf(c_13040,plain,
    ( k2_relat_1(sK10) = sK10
    | r2_hidden(sK2(sK10,sK10),sK10) = iProver_top
    | r1_tarski(k1_relat_1(sK10),sK10) != iProver_top
    | v1_funct_1(sK10) != iProver_top
    | v1_relat_1(sK10) != iProver_top
    | v1_xboole_0(sK10) != iProver_top ),
    inference(instantiation,[status(thm)],[c_12901])).

cnf(c_7991,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_12357,plain,
    ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,k2_relat_1(sK10)))) = iProver_top
    | v1_funct_1(sK10) != iProver_top
    | v1_relat_1(sK10) != iProver_top ),
    inference(superposition,[status(thm)],[c_12294,c_7991])).

cnf(c_12446,plain,
    ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,k2_relat_1(sK10)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12357,c_45,c_46,c_155,c_159,c_8486,c_8485,c_8488,c_8638,c_8682,c_8835,c_11554])).

cnf(c_12452,plain,
    ( v1_xboole_0(k2_relat_1(sK10)) != iProver_top
    | v1_xboole_0(sK10) = iProver_top ),
    inference(superposition,[status(thm)],[c_12446,c_8008])).

cnf(c_12463,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK10))
    | v1_xboole_0(sK10) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_12452])).

cnf(c_7115,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_12403,plain,
    ( sK8 = sK8 ),
    inference(instantiation,[status(thm)],[c_7115])).

cnf(c_7131,plain,
    ( X0 != X1
    | k6_partfun1(X0) = k6_partfun1(X1) ),
    theory(equality)).

cnf(c_11814,plain,
    ( k6_partfun1(sK8) = k6_partfun1(X0)
    | sK8 != X0 ),
    inference(instantiation,[status(thm)],[c_7131])).

cnf(c_11816,plain,
    ( k6_partfun1(sK8) = k6_partfun1(sK10)
    | sK8 != sK10 ),
    inference(instantiation,[status(thm)],[c_11814])).

cnf(c_11676,plain,
    ( r2_hidden(sK1(k1_relat_1(sK10),sK8),k1_relat_1(sK10))
    | r1_tarski(k1_relat_1(sK10),sK8) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_11598,plain,
    ( v1_relat_1(sK10) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_11554])).

cnf(c_9744,plain,
    ( ~ r1_tarski(k6_partfun1(sK8),sK10)
    | ~ r1_tarski(sK10,k6_partfun1(sK8))
    | k6_partfun1(sK8) = sK10 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_8407,plain,
    ( ~ sP0(X0,X1,k1_funct_2(sK8,sK9))
    | ~ r2_hidden(sK10,k1_funct_2(sK8,sK9))
    | k1_relat_1(sK7(X0,X1,sK10)) = X1 ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_8680,plain,
    ( ~ sP0(sK9,sK8,k1_funct_2(sK8,sK9))
    | ~ r2_hidden(sK10,k1_funct_2(sK8,sK9))
    | k1_relat_1(sK7(sK9,sK8,sK10)) = sK8 ),
    inference(instantiation,[status(thm)],[c_8407])).

cnf(c_8637,plain,
    ( ~ v1_funct_1(sK7(sK9,sK8,sK10))
    | v1_funct_1(sK10)
    | sK10 != sK7(sK9,sK8,sK10) ),
    inference(instantiation,[status(thm)],[c_8635])).

cnf(c_40,plain,
    ( v1_partfun1(k6_partfun1(X0),X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_715,plain,
    ( ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9)))
    | ~ v1_funct_1(sK10)
    | k6_partfun1(X0) != sK10
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_40,c_670])).

cnf(c_716,plain,
    ( ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9)))
    | ~ v1_funct_1(sK10)
    | k6_partfun1(sK8) != sK10 ),
    inference(unflattening,[status(thm)],[c_715])).

cnf(c_154,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_156,plain,
    ( r1_tarski(sK10,sK10) = iProver_top ),
    inference(instantiation,[status(thm)],[c_154])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_126212,c_107813,c_92254,c_91794,c_91177,c_84629,c_70135,c_60264,c_57186,c_52459,c_31482,c_29248,c_20178,c_18837,c_18023,c_16386,c_16334,c_16070,c_15634,c_14861,c_14608,c_14131,c_14130,c_13842,c_13040,c_12463,c_12452,c_12403,c_11816,c_11676,c_11598,c_11554,c_9744,c_8835,c_8680,c_8682,c_8638,c_8637,c_8488,c_8485,c_8486,c_8484,c_716,c_159,c_156,c_155,c_46,c_45])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 19:07:38 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 27.19/3.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.19/3.98  
% 27.19/3.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 27.19/3.98  
% 27.19/3.98  ------  iProver source info
% 27.19/3.98  
% 27.19/3.98  git: date: 2020-06-30 10:37:57 +0100
% 27.19/3.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 27.19/3.98  git: non_committed_changes: false
% 27.19/3.98  git: last_make_outside_of_git: false
% 27.19/3.98  
% 27.19/3.98  ------ 
% 27.19/3.98  
% 27.19/3.98  ------ Input Options
% 27.19/3.98  
% 27.19/3.98  --out_options                           all
% 27.19/3.98  --tptp_safe_out                         true
% 27.19/3.98  --problem_path                          ""
% 27.19/3.98  --include_path                          ""
% 27.19/3.98  --clausifier                            res/vclausify_rel
% 27.19/3.98  --clausifier_options                    --mode clausify
% 27.19/3.98  --stdin                                 false
% 27.19/3.98  --stats_out                             all
% 27.19/3.98  
% 27.19/3.98  ------ General Options
% 27.19/3.98  
% 27.19/3.98  --fof                                   false
% 27.19/3.98  --time_out_real                         305.
% 27.19/3.98  --time_out_virtual                      -1.
% 27.19/3.98  --symbol_type_check                     false
% 27.19/3.98  --clausify_out                          false
% 27.19/3.98  --sig_cnt_out                           false
% 27.19/3.98  --trig_cnt_out                          false
% 27.19/3.98  --trig_cnt_out_tolerance                1.
% 27.19/3.98  --trig_cnt_out_sk_spl                   false
% 27.19/3.98  --abstr_cl_out                          false
% 27.19/3.98  
% 27.19/3.98  ------ Global Options
% 27.19/3.98  
% 27.19/3.98  --schedule                              default
% 27.19/3.98  --add_important_lit                     false
% 27.19/3.98  --prop_solver_per_cl                    1000
% 27.19/3.98  --min_unsat_core                        false
% 27.19/3.98  --soft_assumptions                      false
% 27.19/3.98  --soft_lemma_size                       3
% 27.19/3.98  --prop_impl_unit_size                   0
% 27.19/3.98  --prop_impl_unit                        []
% 27.19/3.98  --share_sel_clauses                     true
% 27.19/3.98  --reset_solvers                         false
% 27.19/3.98  --bc_imp_inh                            [conj_cone]
% 27.19/3.98  --conj_cone_tolerance                   3.
% 27.19/3.98  --extra_neg_conj                        none
% 27.19/3.98  --large_theory_mode                     true
% 27.19/3.98  --prolific_symb_bound                   200
% 27.19/3.98  --lt_threshold                          2000
% 27.19/3.98  --clause_weak_htbl                      true
% 27.19/3.98  --gc_record_bc_elim                     false
% 27.19/3.98  
% 27.19/3.98  ------ Preprocessing Options
% 27.19/3.98  
% 27.19/3.98  --preprocessing_flag                    true
% 27.19/3.98  --time_out_prep_mult                    0.1
% 27.19/3.98  --splitting_mode                        input
% 27.19/3.98  --splitting_grd                         true
% 27.19/3.98  --splitting_cvd                         false
% 27.19/3.98  --splitting_cvd_svl                     false
% 27.19/3.98  --splitting_nvd                         32
% 27.19/3.98  --sub_typing                            true
% 27.19/3.98  --prep_gs_sim                           true
% 27.19/3.98  --prep_unflatten                        true
% 27.19/3.98  --prep_res_sim                          true
% 27.19/3.98  --prep_upred                            true
% 27.19/3.98  --prep_sem_filter                       exhaustive
% 27.19/3.98  --prep_sem_filter_out                   false
% 27.19/3.98  --pred_elim                             true
% 27.19/3.98  --res_sim_input                         true
% 27.19/3.98  --eq_ax_congr_red                       true
% 27.19/3.98  --pure_diseq_elim                       true
% 27.19/3.98  --brand_transform                       false
% 27.19/3.98  --non_eq_to_eq                          false
% 27.19/3.98  --prep_def_merge                        true
% 27.19/3.98  --prep_def_merge_prop_impl              false
% 27.19/3.98  --prep_def_merge_mbd                    true
% 27.19/3.98  --prep_def_merge_tr_red                 false
% 27.19/3.98  --prep_def_merge_tr_cl                  false
% 27.19/3.98  --smt_preprocessing                     true
% 27.19/3.98  --smt_ac_axioms                         fast
% 27.19/3.98  --preprocessed_out                      false
% 27.19/3.98  --preprocessed_stats                    false
% 27.19/3.98  
% 27.19/3.98  ------ Abstraction refinement Options
% 27.19/3.98  
% 27.19/3.98  --abstr_ref                             []
% 27.19/3.98  --abstr_ref_prep                        false
% 27.19/3.98  --abstr_ref_until_sat                   false
% 27.19/3.98  --abstr_ref_sig_restrict                funpre
% 27.19/3.98  --abstr_ref_af_restrict_to_split_sk     false
% 27.19/3.98  --abstr_ref_under                       []
% 27.19/3.98  
% 27.19/3.98  ------ SAT Options
% 27.19/3.98  
% 27.19/3.98  --sat_mode                              false
% 27.19/3.98  --sat_fm_restart_options                ""
% 27.19/3.98  --sat_gr_def                            false
% 27.19/3.98  --sat_epr_types                         true
% 27.19/3.98  --sat_non_cyclic_types                  false
% 27.19/3.98  --sat_finite_models                     false
% 27.19/3.98  --sat_fm_lemmas                         false
% 27.19/3.98  --sat_fm_prep                           false
% 27.19/3.98  --sat_fm_uc_incr                        true
% 27.19/3.98  --sat_out_model                         small
% 27.19/3.98  --sat_out_clauses                       false
% 27.19/3.98  
% 27.19/3.98  ------ QBF Options
% 27.19/3.98  
% 27.19/3.98  --qbf_mode                              false
% 27.19/3.98  --qbf_elim_univ                         false
% 27.19/3.98  --qbf_dom_inst                          none
% 27.19/3.98  --qbf_dom_pre_inst                      false
% 27.19/3.98  --qbf_sk_in                             false
% 27.19/3.98  --qbf_pred_elim                         true
% 27.19/3.98  --qbf_split                             512
% 27.19/3.98  
% 27.19/3.98  ------ BMC1 Options
% 27.19/3.98  
% 27.19/3.98  --bmc1_incremental                      false
% 27.19/3.98  --bmc1_axioms                           reachable_all
% 27.19/3.98  --bmc1_min_bound                        0
% 27.19/3.98  --bmc1_max_bound                        -1
% 27.19/3.98  --bmc1_max_bound_default                -1
% 27.19/3.98  --bmc1_symbol_reachability              true
% 27.19/3.98  --bmc1_property_lemmas                  false
% 27.19/3.98  --bmc1_k_induction                      false
% 27.19/3.98  --bmc1_non_equiv_states                 false
% 27.19/3.98  --bmc1_deadlock                         false
% 27.19/3.98  --bmc1_ucm                              false
% 27.19/3.98  --bmc1_add_unsat_core                   none
% 27.19/3.98  --bmc1_unsat_core_children              false
% 27.19/3.98  --bmc1_unsat_core_extrapolate_axioms    false
% 27.19/3.98  --bmc1_out_stat                         full
% 27.19/3.98  --bmc1_ground_init                      false
% 27.19/3.98  --bmc1_pre_inst_next_state              false
% 27.19/3.98  --bmc1_pre_inst_state                   false
% 27.19/3.98  --bmc1_pre_inst_reach_state             false
% 27.19/3.98  --bmc1_out_unsat_core                   false
% 27.19/3.98  --bmc1_aig_witness_out                  false
% 27.19/3.98  --bmc1_verbose                          false
% 27.19/3.98  --bmc1_dump_clauses_tptp                false
% 27.19/3.98  --bmc1_dump_unsat_core_tptp             false
% 27.19/3.98  --bmc1_dump_file                        -
% 27.19/3.98  --bmc1_ucm_expand_uc_limit              128
% 27.19/3.98  --bmc1_ucm_n_expand_iterations          6
% 27.19/3.98  --bmc1_ucm_extend_mode                  1
% 27.19/3.98  --bmc1_ucm_init_mode                    2
% 27.19/3.98  --bmc1_ucm_cone_mode                    none
% 27.19/3.98  --bmc1_ucm_reduced_relation_type        0
% 27.19/3.98  --bmc1_ucm_relax_model                  4
% 27.19/3.98  --bmc1_ucm_full_tr_after_sat            true
% 27.19/3.98  --bmc1_ucm_expand_neg_assumptions       false
% 27.19/3.98  --bmc1_ucm_layered_model                none
% 27.19/3.98  --bmc1_ucm_max_lemma_size               10
% 27.19/3.98  
% 27.19/3.98  ------ AIG Options
% 27.19/3.98  
% 27.19/3.98  --aig_mode                              false
% 27.19/3.98  
% 27.19/3.98  ------ Instantiation Options
% 27.19/3.98  
% 27.19/3.98  --instantiation_flag                    true
% 27.19/3.98  --inst_sos_flag                         false
% 27.19/3.98  --inst_sos_phase                        true
% 27.19/3.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.19/3.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.19/3.98  --inst_lit_sel_side                     num_symb
% 27.19/3.98  --inst_solver_per_active                1400
% 27.19/3.98  --inst_solver_calls_frac                1.
% 27.19/3.98  --inst_passive_queue_type               priority_queues
% 27.19/3.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.19/3.98  --inst_passive_queues_freq              [25;2]
% 27.19/3.98  --inst_dismatching                      true
% 27.19/3.98  --inst_eager_unprocessed_to_passive     true
% 27.19/3.98  --inst_prop_sim_given                   true
% 27.19/3.98  --inst_prop_sim_new                     false
% 27.19/3.98  --inst_subs_new                         false
% 27.19/3.98  --inst_eq_res_simp                      false
% 27.19/3.98  --inst_subs_given                       false
% 27.19/3.98  --inst_orphan_elimination               true
% 27.19/3.98  --inst_learning_loop_flag               true
% 27.19/3.98  --inst_learning_start                   3000
% 27.19/3.98  --inst_learning_factor                  2
% 27.19/3.98  --inst_start_prop_sim_after_learn       3
% 27.19/3.98  --inst_sel_renew                        solver
% 27.19/3.98  --inst_lit_activity_flag                true
% 27.19/3.98  --inst_restr_to_given                   false
% 27.19/3.98  --inst_activity_threshold               500
% 27.19/3.98  --inst_out_proof                        true
% 27.19/3.98  
% 27.19/3.98  ------ Resolution Options
% 27.19/3.98  
% 27.19/3.98  --resolution_flag                       true
% 27.19/3.98  --res_lit_sel                           adaptive
% 27.19/3.98  --res_lit_sel_side                      none
% 27.19/3.98  --res_ordering                          kbo
% 27.19/3.98  --res_to_prop_solver                    active
% 27.19/3.98  --res_prop_simpl_new                    false
% 27.19/3.98  --res_prop_simpl_given                  true
% 27.19/3.98  --res_passive_queue_type                priority_queues
% 27.19/3.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.19/3.98  --res_passive_queues_freq               [15;5]
% 27.19/3.98  --res_forward_subs                      full
% 27.19/3.98  --res_backward_subs                     full
% 27.19/3.98  --res_forward_subs_resolution           true
% 27.19/3.98  --res_backward_subs_resolution          true
% 27.19/3.98  --res_orphan_elimination                true
% 27.19/3.98  --res_time_limit                        2.
% 27.19/3.98  --res_out_proof                         true
% 27.19/3.98  
% 27.19/3.98  ------ Superposition Options
% 27.19/3.98  
% 27.19/3.98  --superposition_flag                    true
% 27.19/3.98  --sup_passive_queue_type                priority_queues
% 27.19/3.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.19/3.98  --sup_passive_queues_freq               [8;1;4]
% 27.19/3.98  --demod_completeness_check              fast
% 27.19/3.98  --demod_use_ground                      true
% 27.19/3.98  --sup_to_prop_solver                    passive
% 27.19/3.98  --sup_prop_simpl_new                    true
% 27.19/3.98  --sup_prop_simpl_given                  true
% 27.19/3.98  --sup_fun_splitting                     false
% 27.19/3.98  --sup_smt_interval                      50000
% 27.19/3.98  
% 27.19/3.98  ------ Superposition Simplification Setup
% 27.19/3.98  
% 27.19/3.98  --sup_indices_passive                   []
% 27.19/3.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.19/3.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.19/3.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.19/3.98  --sup_full_triv                         [TrivRules;PropSubs]
% 27.19/3.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.19/3.98  --sup_full_bw                           [BwDemod]
% 27.19/3.98  --sup_immed_triv                        [TrivRules]
% 27.19/3.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.19/3.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.19/3.98  --sup_immed_bw_main                     []
% 27.19/3.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.19/3.98  --sup_input_triv                        [Unflattening;TrivRules]
% 27.19/3.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.19/3.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.19/3.98  
% 27.19/3.98  ------ Combination Options
% 27.19/3.98  
% 27.19/3.98  --comb_res_mult                         3
% 27.19/3.98  --comb_sup_mult                         2
% 27.19/3.98  --comb_inst_mult                        10
% 27.19/3.98  
% 27.19/3.98  ------ Debug Options
% 27.19/3.98  
% 27.19/3.98  --dbg_backtrace                         false
% 27.19/3.98  --dbg_dump_prop_clauses                 false
% 27.19/3.98  --dbg_dump_prop_clauses_file            -
% 27.19/3.98  --dbg_out_stat                          false
% 27.19/3.98  ------ Parsing...
% 27.19/3.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 27.19/3.98  
% 27.19/3.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 27.19/3.98  
% 27.19/3.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 27.19/3.98  
% 27.19/3.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.19/3.98  ------ Proving...
% 27.19/3.98  ------ Problem Properties 
% 27.19/3.98  
% 27.19/3.98  
% 27.19/3.98  clauses                                 38
% 27.19/3.98  conjectures                             1
% 27.19/3.98  EPR                                     4
% 27.19/3.98  Horn                                    30
% 27.19/3.98  unary                                   4
% 27.19/3.98  binary                                  7
% 27.19/3.98  lits                                    117
% 27.19/3.98  lits eq                                 17
% 27.19/3.98  fd_pure                                 0
% 27.19/3.98  fd_pseudo                               0
% 27.19/3.98  fd_cond                                 0
% 27.19/3.98  fd_pseudo_cond                          5
% 27.19/3.98  AC symbols                              0
% 27.19/3.98  
% 27.19/3.98  ------ Schedule dynamic 5 is on 
% 27.19/3.98  
% 27.19/3.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 27.19/3.98  
% 27.19/3.98  
% 27.19/3.98  ------ 
% 27.19/3.98  Current options:
% 27.19/3.98  ------ 
% 27.19/3.98  
% 27.19/3.98  ------ Input Options
% 27.19/3.98  
% 27.19/3.98  --out_options                           all
% 27.19/3.98  --tptp_safe_out                         true
% 27.19/3.98  --problem_path                          ""
% 27.19/3.98  --include_path                          ""
% 27.19/3.98  --clausifier                            res/vclausify_rel
% 27.19/3.98  --clausifier_options                    --mode clausify
% 27.19/3.98  --stdin                                 false
% 27.19/3.98  --stats_out                             all
% 27.19/3.98  
% 27.19/3.98  ------ General Options
% 27.19/3.98  
% 27.19/3.98  --fof                                   false
% 27.19/3.98  --time_out_real                         305.
% 27.19/3.98  --time_out_virtual                      -1.
% 27.19/3.98  --symbol_type_check                     false
% 27.19/3.98  --clausify_out                          false
% 27.19/3.98  --sig_cnt_out                           false
% 27.19/3.98  --trig_cnt_out                          false
% 27.19/3.98  --trig_cnt_out_tolerance                1.
% 27.19/3.98  --trig_cnt_out_sk_spl                   false
% 27.19/3.98  --abstr_cl_out                          false
% 27.19/3.98  
% 27.19/3.98  ------ Global Options
% 27.19/3.98  
% 27.19/3.98  --schedule                              default
% 27.19/3.98  --add_important_lit                     false
% 27.19/3.98  --prop_solver_per_cl                    1000
% 27.19/3.98  --min_unsat_core                        false
% 27.19/3.98  --soft_assumptions                      false
% 27.19/3.98  --soft_lemma_size                       3
% 27.19/3.98  --prop_impl_unit_size                   0
% 27.19/3.98  --prop_impl_unit                        []
% 27.19/3.98  --share_sel_clauses                     true
% 27.19/3.98  --reset_solvers                         false
% 27.19/3.98  --bc_imp_inh                            [conj_cone]
% 27.19/3.98  --conj_cone_tolerance                   3.
% 27.19/3.98  --extra_neg_conj                        none
% 27.19/3.98  --large_theory_mode                     true
% 27.19/3.98  --prolific_symb_bound                   200
% 27.19/3.98  --lt_threshold                          2000
% 27.19/3.98  --clause_weak_htbl                      true
% 27.19/3.98  --gc_record_bc_elim                     false
% 27.19/3.98  
% 27.19/3.98  ------ Preprocessing Options
% 27.19/3.98  
% 27.19/3.98  --preprocessing_flag                    true
% 27.19/3.98  --time_out_prep_mult                    0.1
% 27.19/3.98  --splitting_mode                        input
% 27.19/3.98  --splitting_grd                         true
% 27.19/3.98  --splitting_cvd                         false
% 27.19/3.98  --splitting_cvd_svl                     false
% 27.19/3.98  --splitting_nvd                         32
% 27.19/3.98  --sub_typing                            true
% 27.19/3.98  --prep_gs_sim                           true
% 27.19/3.98  --prep_unflatten                        true
% 27.19/3.98  --prep_res_sim                          true
% 27.19/3.98  --prep_upred                            true
% 27.19/3.98  --prep_sem_filter                       exhaustive
% 27.19/3.98  --prep_sem_filter_out                   false
% 27.19/3.98  --pred_elim                             true
% 27.19/3.98  --res_sim_input                         true
% 27.19/3.98  --eq_ax_congr_red                       true
% 27.19/3.98  --pure_diseq_elim                       true
% 27.19/3.98  --brand_transform                       false
% 27.19/3.98  --non_eq_to_eq                          false
% 27.19/3.98  --prep_def_merge                        true
% 27.19/3.98  --prep_def_merge_prop_impl              false
% 27.19/3.98  --prep_def_merge_mbd                    true
% 27.19/3.98  --prep_def_merge_tr_red                 false
% 27.19/3.98  --prep_def_merge_tr_cl                  false
% 27.19/3.98  --smt_preprocessing                     true
% 27.19/3.98  --smt_ac_axioms                         fast
% 27.19/3.98  --preprocessed_out                      false
% 27.19/3.98  --preprocessed_stats                    false
% 27.19/3.98  
% 27.19/3.98  ------ Abstraction refinement Options
% 27.19/3.98  
% 27.19/3.98  --abstr_ref                             []
% 27.19/3.98  --abstr_ref_prep                        false
% 27.19/3.98  --abstr_ref_until_sat                   false
% 27.19/3.98  --abstr_ref_sig_restrict                funpre
% 27.19/3.98  --abstr_ref_af_restrict_to_split_sk     false
% 27.19/3.98  --abstr_ref_under                       []
% 27.19/3.98  
% 27.19/3.98  ------ SAT Options
% 27.19/3.98  
% 27.19/3.98  --sat_mode                              false
% 27.19/3.98  --sat_fm_restart_options                ""
% 27.19/3.98  --sat_gr_def                            false
% 27.19/3.98  --sat_epr_types                         true
% 27.19/3.98  --sat_non_cyclic_types                  false
% 27.19/3.98  --sat_finite_models                     false
% 27.19/3.98  --sat_fm_lemmas                         false
% 27.19/3.98  --sat_fm_prep                           false
% 27.19/3.98  --sat_fm_uc_incr                        true
% 27.19/3.98  --sat_out_model                         small
% 27.19/3.98  --sat_out_clauses                       false
% 27.19/3.98  
% 27.19/3.98  ------ QBF Options
% 27.19/3.98  
% 27.19/3.98  --qbf_mode                              false
% 27.19/3.98  --qbf_elim_univ                         false
% 27.19/3.98  --qbf_dom_inst                          none
% 27.19/3.98  --qbf_dom_pre_inst                      false
% 27.19/3.98  --qbf_sk_in                             false
% 27.19/3.98  --qbf_pred_elim                         true
% 27.19/3.98  --qbf_split                             512
% 27.19/3.98  
% 27.19/3.98  ------ BMC1 Options
% 27.19/3.98  
% 27.19/3.98  --bmc1_incremental                      false
% 27.19/3.98  --bmc1_axioms                           reachable_all
% 27.19/3.98  --bmc1_min_bound                        0
% 27.19/3.98  --bmc1_max_bound                        -1
% 27.19/3.98  --bmc1_max_bound_default                -1
% 27.19/3.98  --bmc1_symbol_reachability              true
% 27.19/3.98  --bmc1_property_lemmas                  false
% 27.19/3.98  --bmc1_k_induction                      false
% 27.19/3.98  --bmc1_non_equiv_states                 false
% 27.19/3.98  --bmc1_deadlock                         false
% 27.19/3.98  --bmc1_ucm                              false
% 27.19/3.98  --bmc1_add_unsat_core                   none
% 27.19/3.98  --bmc1_unsat_core_children              false
% 27.19/3.98  --bmc1_unsat_core_extrapolate_axioms    false
% 27.19/3.98  --bmc1_out_stat                         full
% 27.19/3.98  --bmc1_ground_init                      false
% 27.19/3.98  --bmc1_pre_inst_next_state              false
% 27.19/3.98  --bmc1_pre_inst_state                   false
% 27.19/3.98  --bmc1_pre_inst_reach_state             false
% 27.19/3.98  --bmc1_out_unsat_core                   false
% 27.19/3.98  --bmc1_aig_witness_out                  false
% 27.19/3.98  --bmc1_verbose                          false
% 27.19/3.98  --bmc1_dump_clauses_tptp                false
% 27.19/3.98  --bmc1_dump_unsat_core_tptp             false
% 27.19/3.98  --bmc1_dump_file                        -
% 27.19/3.98  --bmc1_ucm_expand_uc_limit              128
% 27.19/3.98  --bmc1_ucm_n_expand_iterations          6
% 27.19/3.98  --bmc1_ucm_extend_mode                  1
% 27.19/3.98  --bmc1_ucm_init_mode                    2
% 27.19/3.98  --bmc1_ucm_cone_mode                    none
% 27.19/3.98  --bmc1_ucm_reduced_relation_type        0
% 27.19/3.98  --bmc1_ucm_relax_model                  4
% 27.19/3.98  --bmc1_ucm_full_tr_after_sat            true
% 27.19/3.98  --bmc1_ucm_expand_neg_assumptions       false
% 27.19/3.98  --bmc1_ucm_layered_model                none
% 27.19/3.98  --bmc1_ucm_max_lemma_size               10
% 27.19/3.98  
% 27.19/3.98  ------ AIG Options
% 27.19/3.98  
% 27.19/3.98  --aig_mode                              false
% 27.19/3.98  
% 27.19/3.98  ------ Instantiation Options
% 27.19/3.98  
% 27.19/3.98  --instantiation_flag                    true
% 27.19/3.98  --inst_sos_flag                         false
% 27.19/3.98  --inst_sos_phase                        true
% 27.19/3.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.19/3.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.19/3.98  --inst_lit_sel_side                     none
% 27.19/3.98  --inst_solver_per_active                1400
% 27.19/3.98  --inst_solver_calls_frac                1.
% 27.19/3.98  --inst_passive_queue_type               priority_queues
% 27.19/3.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.19/3.98  --inst_passive_queues_freq              [25;2]
% 27.19/3.98  --inst_dismatching                      true
% 27.19/3.98  --inst_eager_unprocessed_to_passive     true
% 27.19/3.98  --inst_prop_sim_given                   true
% 27.19/3.98  --inst_prop_sim_new                     false
% 27.19/3.98  --inst_subs_new                         false
% 27.19/3.98  --inst_eq_res_simp                      false
% 27.19/3.98  --inst_subs_given                       false
% 27.19/3.98  --inst_orphan_elimination               true
% 27.19/3.98  --inst_learning_loop_flag               true
% 27.19/3.98  --inst_learning_start                   3000
% 27.19/3.98  --inst_learning_factor                  2
% 27.19/3.98  --inst_start_prop_sim_after_learn       3
% 27.19/3.98  --inst_sel_renew                        solver
% 27.19/3.98  --inst_lit_activity_flag                true
% 27.19/3.98  --inst_restr_to_given                   false
% 27.19/3.98  --inst_activity_threshold               500
% 27.19/3.98  --inst_out_proof                        true
% 27.19/3.98  
% 27.19/3.98  ------ Resolution Options
% 27.19/3.98  
% 27.19/3.98  --resolution_flag                       false
% 27.19/3.98  --res_lit_sel                           adaptive
% 27.19/3.98  --res_lit_sel_side                      none
% 27.19/3.98  --res_ordering                          kbo
% 27.19/3.98  --res_to_prop_solver                    active
% 27.19/3.98  --res_prop_simpl_new                    false
% 27.19/3.98  --res_prop_simpl_given                  true
% 27.19/3.98  --res_passive_queue_type                priority_queues
% 27.19/3.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.19/3.98  --res_passive_queues_freq               [15;5]
% 27.19/3.98  --res_forward_subs                      full
% 27.19/3.98  --res_backward_subs                     full
% 27.19/3.98  --res_forward_subs_resolution           true
% 27.19/3.98  --res_backward_subs_resolution          true
% 27.19/3.98  --res_orphan_elimination                true
% 27.19/3.98  --res_time_limit                        2.
% 27.19/3.98  --res_out_proof                         true
% 27.19/3.98  
% 27.19/3.98  ------ Superposition Options
% 27.19/3.98  
% 27.19/3.98  --superposition_flag                    true
% 27.19/3.98  --sup_passive_queue_type                priority_queues
% 27.19/3.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.19/3.98  --sup_passive_queues_freq               [8;1;4]
% 27.19/3.98  --demod_completeness_check              fast
% 27.19/3.98  --demod_use_ground                      true
% 27.19/3.98  --sup_to_prop_solver                    passive
% 27.19/3.98  --sup_prop_simpl_new                    true
% 27.19/3.98  --sup_prop_simpl_given                  true
% 27.19/3.98  --sup_fun_splitting                     false
% 27.19/3.98  --sup_smt_interval                      50000
% 27.19/3.98  
% 27.19/3.98  ------ Superposition Simplification Setup
% 27.19/3.98  
% 27.19/3.98  --sup_indices_passive                   []
% 27.19/3.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.19/3.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.19/3.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.19/3.98  --sup_full_triv                         [TrivRules;PropSubs]
% 27.19/3.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.19/3.98  --sup_full_bw                           [BwDemod]
% 27.19/3.98  --sup_immed_triv                        [TrivRules]
% 27.19/3.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.19/3.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.19/3.98  --sup_immed_bw_main                     []
% 27.19/3.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.19/3.98  --sup_input_triv                        [Unflattening;TrivRules]
% 27.19/3.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.19/3.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.19/3.98  
% 27.19/3.98  ------ Combination Options
% 27.19/3.98  
% 27.19/3.98  --comb_res_mult                         3
% 27.19/3.98  --comb_sup_mult                         2
% 27.19/3.98  --comb_inst_mult                        10
% 27.19/3.98  
% 27.19/3.98  ------ Debug Options
% 27.19/3.98  
% 27.19/3.98  --dbg_backtrace                         false
% 27.19/3.98  --dbg_dump_prop_clauses                 false
% 27.19/3.98  --dbg_dump_prop_clauses_file            -
% 27.19/3.98  --dbg_out_stat                          false
% 27.19/3.98  
% 27.19/3.98  
% 27.19/3.98  
% 27.19/3.98  
% 27.19/3.98  ------ Proving...
% 27.19/3.98  
% 27.19/3.98  
% 27.19/3.98  % SZS status Theorem for theBenchmark.p
% 27.19/3.98  
% 27.19/3.98  % SZS output start CNFRefutation for theBenchmark.p
% 27.19/3.98  
% 27.19/3.98  fof(f10,axiom,(
% 27.19/3.98    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 27.19/3.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.19/3.98  
% 27.19/3.98  fof(f27,plain,(
% 27.19/3.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 27.19/3.98    inference(ennf_transformation,[],[f10])).
% 27.19/3.98  
% 27.19/3.98  fof(f28,plain,(
% 27.19/3.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 27.19/3.98    inference(flattening,[],[f27])).
% 27.19/3.98  
% 27.19/3.98  fof(f81,plain,(
% 27.19/3.98    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 27.19/3.98    inference(cnf_transformation,[],[f28])).
% 27.19/3.98  
% 27.19/3.98  fof(f16,conjecture,(
% 27.19/3.98    ! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 27.19/3.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.19/3.98  
% 27.19/3.98  fof(f17,negated_conjecture,(
% 27.19/3.98    ~! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 27.19/3.98    inference(negated_conjecture,[],[f16])).
% 27.19/3.98  
% 27.19/3.98  fof(f35,plain,(
% 27.19/3.98    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & r2_hidden(X2,k1_funct_2(X0,X1)))),
% 27.19/3.98    inference(ennf_transformation,[],[f17])).
% 27.19/3.98  
% 27.19/3.98  fof(f59,plain,(
% 27.19/3.98    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & r2_hidden(X2,k1_funct_2(X0,X1))) => ((~m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))) | ~v1_funct_2(sK10,sK8,sK9) | ~v1_funct_1(sK10)) & r2_hidden(sK10,k1_funct_2(sK8,sK9)))),
% 27.19/3.98    introduced(choice_axiom,[])).
% 27.19/3.98  
% 27.19/3.98  fof(f60,plain,(
% 27.19/3.98    (~m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))) | ~v1_funct_2(sK10,sK8,sK9) | ~v1_funct_1(sK10)) & r2_hidden(sK10,k1_funct_2(sK8,sK9))),
% 27.19/3.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f35,f59])).
% 27.19/3.98  
% 27.19/3.98  fof(f105,plain,(
% 27.19/3.98    r2_hidden(sK10,k1_funct_2(sK8,sK9))),
% 27.19/3.98    inference(cnf_transformation,[],[f60])).
% 27.19/3.98  
% 27.19/3.98  fof(f13,axiom,(
% 27.19/3.98    ! [X0,X1,X2] : (k1_funct_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4))))),
% 27.19/3.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.19/3.98  
% 27.19/3.98  fof(f36,plain,(
% 27.19/3.98    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4))))),
% 27.19/3.98    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 27.19/3.98  
% 27.19/3.98  fof(f37,plain,(
% 27.19/3.98    ! [X0,X1,X2] : (k1_funct_2(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 27.19/3.98    inference(definition_folding,[],[f13,f36])).
% 27.19/3.98  
% 27.19/3.98  fof(f58,plain,(
% 27.19/3.98    ! [X0,X1,X2] : ((k1_funct_2(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k1_funct_2(X0,X1) != X2))),
% 27.19/3.98    inference(nnf_transformation,[],[f37])).
% 27.19/3.98  
% 27.19/3.98  fof(f98,plain,(
% 27.19/3.98    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k1_funct_2(X0,X1) != X2) )),
% 27.19/3.98    inference(cnf_transformation,[],[f58])).
% 27.19/3.98  
% 27.19/3.98  fof(f116,plain,(
% 27.19/3.98    ( ! [X0,X1] : (sP0(X1,X0,k1_funct_2(X0,X1))) )),
% 27.19/3.98    inference(equality_resolution,[],[f98])).
% 27.19/3.98  
% 27.19/3.98  fof(f52,plain,(
% 27.19/3.98    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4))) & (? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 27.19/3.98    inference(nnf_transformation,[],[f36])).
% 27.19/3.98  
% 27.19/3.98  fof(f53,plain,(
% 27.19/3.98    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X0) | k1_relat_1(X4) != X1 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X0) & k1_relat_1(X5) = X1 & X3 = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r1_tarski(k2_relat_1(X7),X0) | k1_relat_1(X7) != X1 | X6 != X7 | ~v1_funct_1(X7) | ~v1_relat_1(X7))) & (? [X8] : (r1_tarski(k2_relat_1(X8),X0) & k1_relat_1(X8) = X1 & X6 = X8 & v1_funct_1(X8) & v1_relat_1(X8)) | ~r2_hidden(X6,X2))) | ~sP0(X0,X1,X2)))),
% 27.19/3.98    inference(rectify,[],[f52])).
% 27.19/3.98  
% 27.19/3.98  fof(f56,plain,(
% 27.19/3.98    ! [X6,X1,X0] : (? [X8] : (r1_tarski(k2_relat_1(X8),X0) & k1_relat_1(X8) = X1 & X6 = X8 & v1_funct_1(X8) & v1_relat_1(X8)) => (r1_tarski(k2_relat_1(sK7(X0,X1,X6)),X0) & k1_relat_1(sK7(X0,X1,X6)) = X1 & sK7(X0,X1,X6) = X6 & v1_funct_1(sK7(X0,X1,X6)) & v1_relat_1(sK7(X0,X1,X6))))),
% 27.19/3.98    introduced(choice_axiom,[])).
% 27.19/3.98  
% 27.19/3.98  fof(f55,plain,(
% 27.19/3.98    ( ! [X3] : (! [X2,X1,X0] : (? [X5] : (r1_tarski(k2_relat_1(X5),X0) & k1_relat_1(X5) = X1 & X3 = X5 & v1_funct_1(X5) & v1_relat_1(X5)) => (r1_tarski(k2_relat_1(sK6(X0,X1,X2)),X0) & k1_relat_1(sK6(X0,X1,X2)) = X1 & sK6(X0,X1,X2) = X3 & v1_funct_1(sK6(X0,X1,X2)) & v1_relat_1(sK6(X0,X1,X2))))) )),
% 27.19/3.98    introduced(choice_axiom,[])).
% 27.19/3.98  
% 27.19/3.98  fof(f54,plain,(
% 27.19/3.98    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X0) | k1_relat_1(X4) != X1 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X0) & k1_relat_1(X5) = X1 & X3 = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(X3,X2))) => ((! [X4] : (~r1_tarski(k2_relat_1(X4),X0) | k1_relat_1(X4) != X1 | sK5(X0,X1,X2) != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X0) & k1_relat_1(X5) = X1 & sK5(X0,X1,X2) = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 27.19/3.98    introduced(choice_axiom,[])).
% 27.19/3.98  
% 27.19/3.98  fof(f57,plain,(
% 27.19/3.98    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((! [X4] : (~r1_tarski(k2_relat_1(X4),X0) | k1_relat_1(X4) != X1 | sK5(X0,X1,X2) != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((r1_tarski(k2_relat_1(sK6(X0,X1,X2)),X0) & k1_relat_1(sK6(X0,X1,X2)) = X1 & sK5(X0,X1,X2) = sK6(X0,X1,X2) & v1_funct_1(sK6(X0,X1,X2)) & v1_relat_1(sK6(X0,X1,X2))) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r1_tarski(k2_relat_1(X7),X0) | k1_relat_1(X7) != X1 | X6 != X7 | ~v1_funct_1(X7) | ~v1_relat_1(X7))) & ((r1_tarski(k2_relat_1(sK7(X0,X1,X6)),X0) & k1_relat_1(sK7(X0,X1,X6)) = X1 & sK7(X0,X1,X6) = X6 & v1_funct_1(sK7(X0,X1,X6)) & v1_relat_1(sK7(X0,X1,X6))) | ~r2_hidden(X6,X2))) | ~sP0(X0,X1,X2)))),
% 27.19/3.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f53,f56,f55,f54])).
% 27.19/3.98  
% 27.19/3.98  fof(f89,plain,(
% 27.19/3.98    ( ! [X6,X2,X0,X1] : (k1_relat_1(sK7(X0,X1,X6)) = X1 | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 27.19/3.98    inference(cnf_transformation,[],[f57])).
% 27.19/3.98  
% 27.19/3.98  fof(f88,plain,(
% 27.19/3.98    ( ! [X6,X2,X0,X1] : (sK7(X0,X1,X6) = X6 | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 27.19/3.98    inference(cnf_transformation,[],[f57])).
% 27.19/3.98  
% 27.19/3.98  fof(f6,axiom,(
% 27.19/3.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 27.19/3.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.19/3.98  
% 27.19/3.98  fof(f22,plain,(
% 27.19/3.98    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 27.19/3.98    inference(ennf_transformation,[],[f6])).
% 27.19/3.98  
% 27.19/3.98  fof(f23,plain,(
% 27.19/3.98    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 27.19/3.98    inference(flattening,[],[f22])).
% 27.19/3.98  
% 27.19/3.98  fof(f46,plain,(
% 27.19/3.98    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 27.19/3.98    inference(nnf_transformation,[],[f23])).
% 27.19/3.98  
% 27.19/3.98  fof(f47,plain,(
% 27.19/3.98    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 27.19/3.98    inference(rectify,[],[f46])).
% 27.19/3.98  
% 27.19/3.98  fof(f50,plain,(
% 27.19/3.98    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK4(X0,X5)) = X5 & r2_hidden(sK4(X0,X5),k1_relat_1(X0))))),
% 27.19/3.98    introduced(choice_axiom,[])).
% 27.19/3.98  
% 27.19/3.98  fof(f49,plain,(
% 27.19/3.98    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X1)) = X2 & r2_hidden(sK3(X0,X1),k1_relat_1(X0))))) )),
% 27.19/3.98    introduced(choice_axiom,[])).
% 27.19/3.98  
% 27.19/3.98  fof(f48,plain,(
% 27.19/3.98    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK2(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK2(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK2(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK2(X0,X1),X1))))),
% 27.19/3.98    introduced(choice_axiom,[])).
% 27.19/3.98  
% 27.19/3.98  fof(f51,plain,(
% 27.19/3.98    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK2(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK2(X0,X1),X1)) & ((k1_funct_1(X0,sK3(X0,X1)) = sK2(X0,X1) & r2_hidden(sK3(X0,X1),k1_relat_1(X0))) | r2_hidden(sK2(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK4(X0,X5)) = X5 & r2_hidden(sK4(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 27.19/3.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f47,f50,f49,f48])).
% 27.19/3.98  
% 27.19/3.98  fof(f75,plain,(
% 27.19/3.98    ( ! [X0,X1] : (k2_relat_1(X0) = X1 | r2_hidden(sK3(X0,X1),k1_relat_1(X0)) | r2_hidden(sK2(X0,X1),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 27.19/3.98    inference(cnf_transformation,[],[f51])).
% 27.19/3.98  
% 27.19/3.98  fof(f2,axiom,(
% 27.19/3.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 27.19/3.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.19/3.98  
% 27.19/3.98  fof(f42,plain,(
% 27.19/3.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 27.19/3.98    inference(nnf_transformation,[],[f2])).
% 27.19/3.98  
% 27.19/3.98  fof(f43,plain,(
% 27.19/3.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 27.19/3.98    inference(flattening,[],[f42])).
% 27.19/3.98  
% 27.19/3.98  fof(f64,plain,(
% 27.19/3.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 27.19/3.98    inference(cnf_transformation,[],[f43])).
% 27.19/3.98  
% 27.19/3.98  fof(f108,plain,(
% 27.19/3.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 27.19/3.98    inference(equality_resolution,[],[f64])).
% 27.19/3.98  
% 27.19/3.98  fof(f66,plain,(
% 27.19/3.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 27.19/3.98    inference(cnf_transformation,[],[f43])).
% 27.19/3.98  
% 27.19/3.98  fof(f87,plain,(
% 27.19/3.98    ( ! [X6,X2,X0,X1] : (v1_funct_1(sK7(X0,X1,X6)) | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 27.19/3.98    inference(cnf_transformation,[],[f57])).
% 27.19/3.98  
% 27.19/3.98  fof(f86,plain,(
% 27.19/3.98    ( ! [X6,X2,X0,X1] : (v1_relat_1(sK7(X0,X1,X6)) | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 27.19/3.98    inference(cnf_transformation,[],[f57])).
% 27.19/3.98  
% 27.19/3.98  fof(f90,plain,(
% 27.19/3.98    ( ! [X6,X2,X0,X1] : (r1_tarski(k2_relat_1(sK7(X0,X1,X6)),X0) | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 27.19/3.98    inference(cnf_transformation,[],[f57])).
% 27.19/3.98  
% 27.19/3.98  fof(f74,plain,(
% 27.19/3.98    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 27.19/3.98    inference(cnf_transformation,[],[f51])).
% 27.19/3.98  
% 27.19/3.98  fof(f109,plain,(
% 27.19/3.98    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 27.19/3.98    inference(equality_resolution,[],[f74])).
% 27.19/3.98  
% 27.19/3.98  fof(f110,plain,(
% 27.19/3.98    ( ! [X6,X0] : (r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~r2_hidden(X6,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 27.19/3.98    inference(equality_resolution,[],[f109])).
% 27.19/3.98  
% 27.19/3.98  fof(f4,axiom,(
% 27.19/3.98    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 27.19/3.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.19/3.98  
% 27.19/3.98  fof(f20,plain,(
% 27.19/3.98    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 27.19/3.98    inference(ennf_transformation,[],[f4])).
% 27.19/3.98  
% 27.19/3.98  fof(f69,plain,(
% 27.19/3.98    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 27.19/3.98    inference(cnf_transformation,[],[f20])).
% 27.19/3.98  
% 27.19/3.98  fof(f3,axiom,(
% 27.19/3.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 27.19/3.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.19/3.98  
% 27.19/3.98  fof(f44,plain,(
% 27.19/3.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 27.19/3.98    inference(nnf_transformation,[],[f3])).
% 27.19/3.98  
% 27.19/3.98  fof(f68,plain,(
% 27.19/3.98    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 27.19/3.98    inference(cnf_transformation,[],[f44])).
% 27.19/3.98  
% 27.19/3.98  fof(f12,axiom,(
% 27.19/3.98    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 27.19/3.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.19/3.98  
% 27.19/3.98  fof(f31,plain,(
% 27.19/3.98    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 27.19/3.98    inference(ennf_transformation,[],[f12])).
% 27.19/3.98  
% 27.19/3.98  fof(f32,plain,(
% 27.19/3.98    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 27.19/3.98    inference(flattening,[],[f31])).
% 27.19/3.98  
% 27.19/3.98  fof(f85,plain,(
% 27.19/3.98    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 27.19/3.98    inference(cnf_transformation,[],[f32])).
% 27.19/3.98  
% 27.19/3.98  fof(f15,axiom,(
% 27.19/3.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 27.19/3.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.19/3.98  
% 27.19/3.98  fof(f33,plain,(
% 27.19/3.98    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 27.19/3.98    inference(ennf_transformation,[],[f15])).
% 27.19/3.98  
% 27.19/3.98  fof(f34,plain,(
% 27.19/3.98    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 27.19/3.98    inference(flattening,[],[f33])).
% 27.19/3.98  
% 27.19/3.98  fof(f103,plain,(
% 27.19/3.98    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 27.19/3.98    inference(cnf_transformation,[],[f34])).
% 27.19/3.98  
% 27.19/3.98  fof(f104,plain,(
% 27.19/3.98    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 27.19/3.98    inference(cnf_transformation,[],[f34])).
% 27.19/3.98  
% 27.19/3.98  fof(f11,axiom,(
% 27.19/3.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 27.19/3.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.19/3.98  
% 27.19/3.98  fof(f29,plain,(
% 27.19/3.98    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 27.19/3.98    inference(ennf_transformation,[],[f11])).
% 27.19/3.98  
% 27.19/3.98  fof(f30,plain,(
% 27.19/3.98    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 27.19/3.98    inference(flattening,[],[f29])).
% 27.19/3.98  
% 27.19/3.98  fof(f83,plain,(
% 27.19/3.98    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 27.19/3.98    inference(cnf_transformation,[],[f30])).
% 27.19/3.98  
% 27.19/3.98  fof(f106,plain,(
% 27.19/3.98    ~m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))) | ~v1_funct_2(sK10,sK8,sK9) | ~v1_funct_1(sK10)),
% 27.19/3.98    inference(cnf_transformation,[],[f60])).
% 27.19/3.98  
% 27.19/3.98  fof(f7,axiom,(
% 27.19/3.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 27.19/3.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.19/3.98  
% 27.19/3.98  fof(f24,plain,(
% 27.19/3.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 27.19/3.98    inference(ennf_transformation,[],[f7])).
% 27.19/3.98  
% 27.19/3.98  fof(f78,plain,(
% 27.19/3.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 27.19/3.98    inference(cnf_transformation,[],[f24])).
% 27.19/3.98  
% 27.19/3.98  fof(f65,plain,(
% 27.19/3.98    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 27.19/3.98    inference(cnf_transformation,[],[f43])).
% 27.19/3.98  
% 27.19/3.98  fof(f107,plain,(
% 27.19/3.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 27.19/3.98    inference(equality_resolution,[],[f65])).
% 27.19/3.98  
% 27.19/3.98  fof(f1,axiom,(
% 27.19/3.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 27.19/3.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.19/3.98  
% 27.19/3.98  fof(f19,plain,(
% 27.19/3.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 27.19/3.98    inference(ennf_transformation,[],[f1])).
% 27.19/3.98  
% 27.19/3.98  fof(f38,plain,(
% 27.19/3.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 27.19/3.98    inference(nnf_transformation,[],[f19])).
% 27.19/3.98  
% 27.19/3.98  fof(f39,plain,(
% 27.19/3.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 27.19/3.98    inference(rectify,[],[f38])).
% 27.19/3.98  
% 27.19/3.98  fof(f40,plain,(
% 27.19/3.98    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 27.19/3.98    introduced(choice_axiom,[])).
% 27.19/3.98  
% 27.19/3.98  fof(f41,plain,(
% 27.19/3.98    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 27.19/3.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f39,f40])).
% 27.19/3.98  
% 27.19/3.98  fof(f62,plain,(
% 27.19/3.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 27.19/3.98    inference(cnf_transformation,[],[f41])).
% 27.19/3.98  
% 27.19/3.98  fof(f9,axiom,(
% 27.19/3.98    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 27.19/3.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.19/3.98  
% 27.19/3.98  fof(f26,plain,(
% 27.19/3.98    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 27.19/3.98    inference(ennf_transformation,[],[f9])).
% 27.19/3.98  
% 27.19/3.98  fof(f80,plain,(
% 27.19/3.98    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 27.19/3.98    inference(cnf_transformation,[],[f26])).
% 27.19/3.98  
% 27.19/3.98  fof(f8,axiom,(
% 27.19/3.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 27.19/3.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.19/3.98  
% 27.19/3.98  fof(f18,plain,(
% 27.19/3.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 27.19/3.98    inference(pure_predicate_removal,[],[f8])).
% 27.19/3.98  
% 27.19/3.98  fof(f25,plain,(
% 27.19/3.98    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 27.19/3.98    inference(ennf_transformation,[],[f18])).
% 27.19/3.98  
% 27.19/3.98  fof(f79,plain,(
% 27.19/3.98    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 27.19/3.98    inference(cnf_transformation,[],[f25])).
% 27.19/3.98  
% 27.19/3.98  fof(f5,axiom,(
% 27.19/3.98    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 27.19/3.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.19/3.98  
% 27.19/3.98  fof(f21,plain,(
% 27.19/3.98    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 27.19/3.98    inference(ennf_transformation,[],[f5])).
% 27.19/3.98  
% 27.19/3.98  fof(f45,plain,(
% 27.19/3.98    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 27.19/3.98    inference(nnf_transformation,[],[f21])).
% 27.19/3.98  
% 27.19/3.98  fof(f70,plain,(
% 27.19/3.98    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 27.19/3.98    inference(cnf_transformation,[],[f45])).
% 27.19/3.98  
% 27.19/3.98  fof(f14,axiom,(
% 27.19/3.98    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 27.19/3.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.19/3.98  
% 27.19/3.98  fof(f101,plain,(
% 27.19/3.98    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 27.19/3.98    inference(cnf_transformation,[],[f14])).
% 27.19/3.98  
% 27.19/3.98  fof(f67,plain,(
% 27.19/3.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 27.19/3.98    inference(cnf_transformation,[],[f44])).
% 27.19/3.98  
% 27.19/3.98  fof(f100,plain,(
% 27.19/3.98    ( ! [X0] : (v1_partfun1(k6_partfun1(X0),X0)) )),
% 27.19/3.98    inference(cnf_transformation,[],[f14])).
% 27.19/3.98  
% 27.19/3.98  cnf(c_20,plain,
% 27.19/3.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 27.19/3.98      | ~ r1_tarski(k1_relat_1(X0),X1)
% 27.19/3.98      | ~ r1_tarski(k2_relat_1(X0),X2)
% 27.19/3.98      | ~ v1_relat_1(X0) ),
% 27.19/3.98      inference(cnf_transformation,[],[f81]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_126212,plain,
% 27.19/3.98      ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9)))
% 27.19/3.98      | ~ r1_tarski(k1_relat_1(sK10),sK8)
% 27.19/3.98      | ~ r1_tarski(k2_relat_1(sK10),sK9)
% 27.19/3.98      | ~ v1_relat_1(sK10) ),
% 27.19/3.98      inference(instantiation,[status(thm)],[c_20]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_7117,plain,
% 27.19/3.98      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 27.19/3.98      theory(equality) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_11699,plain,
% 27.19/3.98      ( ~ r1_tarski(X0,sK10)
% 27.19/3.98      | r1_tarski(k6_partfun1(sK8),sK10)
% 27.19/3.98      | k6_partfun1(sK8) != X0 ),
% 27.19/3.98      inference(instantiation,[status(thm)],[c_7117]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_107811,plain,
% 27.19/3.98      ( ~ r1_tarski(k6_partfun1(X0),sK10)
% 27.19/3.98      | r1_tarski(k6_partfun1(sK8),sK10)
% 27.19/3.98      | k6_partfun1(sK8) != k6_partfun1(X0) ),
% 27.19/3.98      inference(instantiation,[status(thm)],[c_11699]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_107813,plain,
% 27.19/3.98      ( r1_tarski(k6_partfun1(sK8),sK10)
% 27.19/3.98      | ~ r1_tarski(k6_partfun1(sK10),sK10)
% 27.19/3.98      | k6_partfun1(sK8) != k6_partfun1(sK10) ),
% 27.19/3.98      inference(instantiation,[status(thm)],[c_107811]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_45,negated_conjecture,
% 27.19/3.98      ( r2_hidden(sK10,k1_funct_2(sK8,sK9)) ),
% 27.19/3.98      inference(cnf_transformation,[],[f105]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_7990,plain,
% 27.19/3.98      ( r2_hidden(sK10,k1_funct_2(sK8,sK9)) = iProver_top ),
% 27.19/3.98      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_38,plain,
% 27.19/3.98      ( sP0(X0,X1,k1_funct_2(X1,X0)) ),
% 27.19/3.98      inference(cnf_transformation,[],[f116]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_7993,plain,
% 27.19/3.98      ( sP0(X0,X1,k1_funct_2(X1,X0)) = iProver_top ),
% 27.19/3.98      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_33,plain,
% 27.19/3.98      ( ~ sP0(X0,X1,X2)
% 27.19/3.98      | ~ r2_hidden(X3,X2)
% 27.19/3.98      | k1_relat_1(sK7(X0,X1,X3)) = X1 ),
% 27.19/3.98      inference(cnf_transformation,[],[f89]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_7998,plain,
% 27.19/3.98      ( k1_relat_1(sK7(X0,X1,X2)) = X1
% 27.19/3.98      | sP0(X0,X1,X3) != iProver_top
% 27.19/3.98      | r2_hidden(X2,X3) != iProver_top ),
% 27.19/3.98      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_9765,plain,
% 27.19/3.98      ( k1_relat_1(sK7(X0,X1,X2)) = X1
% 27.19/3.98      | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
% 27.19/3.98      inference(superposition,[status(thm)],[c_7993,c_7998]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_12292,plain,
% 27.19/3.98      ( k1_relat_1(sK7(sK9,sK8,sK10)) = sK8 ),
% 27.19/3.98      inference(superposition,[status(thm)],[c_7990,c_9765]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_34,plain,
% 27.19/3.98      ( ~ sP0(X0,X1,X2) | ~ r2_hidden(X3,X2) | sK7(X0,X1,X3) = X3 ),
% 27.19/3.98      inference(cnf_transformation,[],[f88]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_7997,plain,
% 27.19/3.98      ( sK7(X0,X1,X2) = X2
% 27.19/3.98      | sP0(X0,X1,X3) != iProver_top
% 27.19/3.98      | r2_hidden(X2,X3) != iProver_top ),
% 27.19/3.98      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_9260,plain,
% 27.19/3.98      ( sK7(X0,X1,X2) = X2
% 27.19/3.98      | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
% 27.19/3.98      inference(superposition,[status(thm)],[c_7993,c_7997]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_10428,plain,
% 27.19/3.98      ( sK7(sK9,sK8,sK10) = sK10 ),
% 27.19/3.98      inference(superposition,[status(thm)],[c_7990,c_9260]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_12294,plain,
% 27.19/3.98      ( k1_relat_1(sK10) = sK8 ),
% 27.19/3.98      inference(light_normalisation,[status(thm)],[c_12292,c_10428]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_13,plain,
% 27.19/3.98      ( r2_hidden(sK3(X0,X1),k1_relat_1(X0))
% 27.19/3.98      | r2_hidden(sK2(X0,X1),X1)
% 27.19/3.98      | ~ v1_funct_1(X0)
% 27.19/3.98      | ~ v1_relat_1(X0)
% 27.19/3.98      | k2_relat_1(X0) = X1 ),
% 27.19/3.98      inference(cnf_transformation,[],[f75]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_8013,plain,
% 27.19/3.98      ( k2_relat_1(X0) = X1
% 27.19/3.98      | r2_hidden(sK3(X0,X1),k1_relat_1(X0)) = iProver_top
% 27.19/3.98      | r2_hidden(sK2(X0,X1),X1) = iProver_top
% 27.19/3.98      | v1_funct_1(X0) != iProver_top
% 27.19/3.98      | v1_relat_1(X0) != iProver_top ),
% 27.19/3.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_12892,plain,
% 27.19/3.98      ( k2_relat_1(sK10) = X0
% 27.19/3.98      | r2_hidden(sK3(sK10,X0),sK8) = iProver_top
% 27.19/3.98      | r2_hidden(sK2(sK10,X0),X0) = iProver_top
% 27.19/3.98      | v1_funct_1(sK10) != iProver_top
% 27.19/3.98      | v1_relat_1(sK10) != iProver_top ),
% 27.19/3.98      inference(superposition,[status(thm)],[c_12294,c_8013]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_46,plain,
% 27.19/3.98      ( r2_hidden(sK10,k1_funct_2(sK8,sK9)) = iProver_top ),
% 27.19/3.98      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_5,plain,
% 27.19/3.98      ( r1_tarski(X0,X0) ),
% 27.19/3.98      inference(cnf_transformation,[],[f108]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_155,plain,
% 27.19/3.98      ( r1_tarski(sK10,sK10) ),
% 27.19/3.98      inference(instantiation,[status(thm)],[c_5]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_3,plain,
% 27.19/3.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 27.19/3.98      inference(cnf_transformation,[],[f66]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_159,plain,
% 27.19/3.98      ( ~ r1_tarski(sK10,sK10) | sK10 = sK10 ),
% 27.19/3.98      inference(instantiation,[status(thm)],[c_3]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_35,plain,
% 27.19/3.98      ( ~ sP0(X0,X1,X2)
% 27.19/3.98      | ~ r2_hidden(X3,X2)
% 27.19/3.98      | v1_funct_1(sK7(X0,X1,X3)) ),
% 27.19/3.98      inference(cnf_transformation,[],[f87]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_8377,plain,
% 27.19/3.98      ( ~ sP0(X0,X1,k1_funct_2(sK8,sK9))
% 27.19/3.98      | ~ r2_hidden(sK10,k1_funct_2(sK8,sK9))
% 27.19/3.98      | v1_funct_1(sK7(X0,X1,sK10)) ),
% 27.19/3.98      inference(instantiation,[status(thm)],[c_35]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_8484,plain,
% 27.19/3.98      ( ~ sP0(sK9,sK8,k1_funct_2(sK8,sK9))
% 27.19/3.98      | ~ r2_hidden(sK10,k1_funct_2(sK8,sK9))
% 27.19/3.98      | v1_funct_1(sK7(sK9,sK8,sK10)) ),
% 27.19/3.98      inference(instantiation,[status(thm)],[c_8377]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_8486,plain,
% 27.19/3.98      ( sP0(sK9,sK8,k1_funct_2(sK8,sK9)) != iProver_top
% 27.19/3.98      | r2_hidden(sK10,k1_funct_2(sK8,sK9)) != iProver_top
% 27.19/3.98      | v1_funct_1(sK7(sK9,sK8,sK10)) = iProver_top ),
% 27.19/3.98      inference(predicate_to_equality,[status(thm)],[c_8484]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_8485,plain,
% 27.19/3.98      ( sP0(sK9,sK8,k1_funct_2(sK8,sK9)) ),
% 27.19/3.98      inference(instantiation,[status(thm)],[c_38]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_8488,plain,
% 27.19/3.98      ( sP0(sK9,sK8,k1_funct_2(sK8,sK9)) = iProver_top ),
% 27.19/3.98      inference(predicate_to_equality,[status(thm)],[c_8485]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_7126,plain,
% 27.19/3.98      ( ~ v1_funct_1(X0) | v1_funct_1(X1) | X1 != X0 ),
% 27.19/3.98      theory(equality) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_8635,plain,
% 27.19/3.98      ( v1_funct_1(X0)
% 27.19/3.98      | ~ v1_funct_1(sK7(sK9,sK8,sK10))
% 27.19/3.98      | X0 != sK7(sK9,sK8,sK10) ),
% 27.19/3.98      inference(instantiation,[status(thm)],[c_7126]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_8636,plain,
% 27.19/3.98      ( X0 != sK7(sK9,sK8,sK10)
% 27.19/3.98      | v1_funct_1(X0) = iProver_top
% 27.19/3.98      | v1_funct_1(sK7(sK9,sK8,sK10)) != iProver_top ),
% 27.19/3.98      inference(predicate_to_equality,[status(thm)],[c_8635]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_8638,plain,
% 27.19/3.98      ( sK10 != sK7(sK9,sK8,sK10)
% 27.19/3.98      | v1_funct_1(sK7(sK9,sK8,sK10)) != iProver_top
% 27.19/3.98      | v1_funct_1(sK10) = iProver_top ),
% 27.19/3.98      inference(instantiation,[status(thm)],[c_8636]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_8412,plain,
% 27.19/3.98      ( ~ sP0(X0,X1,k1_funct_2(sK8,sK9))
% 27.19/3.98      | ~ r2_hidden(sK10,k1_funct_2(sK8,sK9))
% 27.19/3.98      | sK7(X0,X1,sK10) = sK10 ),
% 27.19/3.98      inference(instantiation,[status(thm)],[c_34]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_8682,plain,
% 27.19/3.98      ( ~ sP0(sK9,sK8,k1_funct_2(sK8,sK9))
% 27.19/3.98      | ~ r2_hidden(sK10,k1_funct_2(sK8,sK9))
% 27.19/3.98      | sK7(sK9,sK8,sK10) = sK10 ),
% 27.19/3.98      inference(instantiation,[status(thm)],[c_8412]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_7116,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_8834,plain,
% 27.19/3.98      ( X0 != X1 | X0 = sK7(sK9,sK8,sK10) | sK7(sK9,sK8,sK10) != X1 ),
% 27.19/3.98      inference(instantiation,[status(thm)],[c_7116]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_8835,plain,
% 27.19/3.98      ( sK7(sK9,sK8,sK10) != sK10
% 27.19/3.98      | sK10 = sK7(sK9,sK8,sK10)
% 27.19/3.98      | sK10 != sK10 ),
% 27.19/3.98      inference(instantiation,[status(thm)],[c_8834]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_36,plain,
% 27.19/3.98      ( ~ sP0(X0,X1,X2)
% 27.19/3.98      | ~ r2_hidden(X3,X2)
% 27.19/3.98      | v1_relat_1(sK7(X0,X1,X3)) ),
% 27.19/3.98      inference(cnf_transformation,[],[f86]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_7995,plain,
% 27.19/3.98      ( sP0(X0,X1,X2) != iProver_top
% 27.19/3.98      | r2_hidden(X3,X2) != iProver_top
% 27.19/3.98      | v1_relat_1(sK7(X0,X1,X3)) = iProver_top ),
% 27.19/3.98      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_9724,plain,
% 27.19/3.98      ( r2_hidden(X0,k1_funct_2(X1,X2)) != iProver_top
% 27.19/3.98      | v1_relat_1(sK7(X2,X1,X0)) = iProver_top ),
% 27.19/3.98      inference(superposition,[status(thm)],[c_7993,c_7995]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_11552,plain,
% 27.19/3.98      ( v1_relat_1(sK7(sK9,sK8,sK10)) = iProver_top ),
% 27.19/3.98      inference(superposition,[status(thm)],[c_7990,c_9724]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_11554,plain,
% 27.19/3.98      ( v1_relat_1(sK10) = iProver_top ),
% 27.19/3.98      inference(light_normalisation,[status(thm)],[c_11552,c_10428]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_13512,plain,
% 27.19/3.98      ( k2_relat_1(sK10) = X0
% 27.19/3.98      | r2_hidden(sK3(sK10,X0),sK8) = iProver_top
% 27.19/3.98      | r2_hidden(sK2(sK10,X0),X0) = iProver_top ),
% 27.19/3.98      inference(global_propositional_subsumption,
% 27.19/3.98                [status(thm)],
% 27.19/3.98                [c_12892,c_45,c_46,c_155,c_159,c_8486,c_8485,c_8488,
% 27.19/3.98                 c_8638,c_8682,c_8835,c_11554]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_32,plain,
% 27.19/3.98      ( ~ sP0(X0,X1,X2)
% 27.19/3.98      | ~ r2_hidden(X3,X2)
% 27.19/3.98      | r1_tarski(k2_relat_1(sK7(X0,X1,X3)),X0) ),
% 27.19/3.98      inference(cnf_transformation,[],[f90]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_7999,plain,
% 27.19/3.98      ( sP0(X0,X1,X2) != iProver_top
% 27.19/3.98      | r2_hidden(X3,X2) != iProver_top
% 27.19/3.98      | r1_tarski(k2_relat_1(sK7(X0,X1,X3)),X0) = iProver_top ),
% 27.19/3.98      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_10487,plain,
% 27.19/3.98      ( r2_hidden(X0,k1_funct_2(X1,X2)) != iProver_top
% 27.19/3.98      | r1_tarski(k2_relat_1(sK7(X2,X1,X0)),X2) = iProver_top ),
% 27.19/3.98      inference(superposition,[status(thm)],[c_7993,c_7999]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_16334,plain,
% 27.19/3.98      ( r2_hidden(sK10,k1_funct_2(sK8,sK9)) != iProver_top
% 27.19/3.98      | r1_tarski(k2_relat_1(sK10),sK9) = iProver_top ),
% 27.19/3.98      inference(superposition,[status(thm)],[c_10428,c_10487]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_17008,plain,
% 27.19/3.98      ( r1_tarski(k2_relat_1(sK10),sK9) = iProver_top ),
% 27.19/3.98      inference(global_propositional_subsumption,
% 27.19/3.98                [status(thm)],
% 27.19/3.98                [c_16334,c_46]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_14,plain,
% 27.19/3.98      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 27.19/3.98      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 27.19/3.98      | ~ v1_funct_1(X1)
% 27.19/3.98      | ~ v1_relat_1(X1) ),
% 27.19/3.98      inference(cnf_transformation,[],[f110]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_8012,plain,
% 27.19/3.98      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 27.19/3.98      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
% 27.19/3.98      | v1_funct_1(X1) != iProver_top
% 27.19/3.98      | v1_relat_1(X1) != iProver_top ),
% 27.19/3.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_8,plain,
% 27.19/3.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 27.19/3.98      | ~ r2_hidden(X2,X0)
% 27.19/3.98      | ~ v1_xboole_0(X1) ),
% 27.19/3.98      inference(cnf_transformation,[],[f69]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_6,plain,
% 27.19/3.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 27.19/3.98      inference(cnf_transformation,[],[f68]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_350,plain,
% 27.19/3.98      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 27.19/3.98      inference(prop_impl,[status(thm)],[c_6]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_351,plain,
% 27.19/3.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 27.19/3.98      inference(renaming,[status(thm)],[c_350]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_431,plain,
% 27.19/3.98      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X2) | ~ v1_xboole_0(X2) ),
% 27.19/3.98      inference(bin_hyper_res,[status(thm)],[c_8,c_351]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_7989,plain,
% 27.19/3.98      ( r2_hidden(X0,X1) != iProver_top
% 27.19/3.98      | r1_tarski(X1,X2) != iProver_top
% 27.19/3.98      | v1_xboole_0(X2) != iProver_top ),
% 27.19/3.98      inference(predicate_to_equality,[status(thm)],[c_431]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_12088,plain,
% 27.19/3.98      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 27.19/3.98      | r1_tarski(k2_relat_1(X1),X2) != iProver_top
% 27.19/3.98      | v1_funct_1(X1) != iProver_top
% 27.19/3.98      | v1_relat_1(X1) != iProver_top
% 27.19/3.98      | v1_xboole_0(X2) != iProver_top ),
% 27.19/3.98      inference(superposition,[status(thm)],[c_8012,c_7989]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_91260,plain,
% 27.19/3.98      ( r2_hidden(X0,sK8) != iProver_top
% 27.19/3.98      | r1_tarski(k2_relat_1(sK10),X1) != iProver_top
% 27.19/3.98      | v1_funct_1(sK10) != iProver_top
% 27.19/3.98      | v1_relat_1(sK10) != iProver_top
% 27.19/3.98      | v1_xboole_0(X1) != iProver_top ),
% 27.19/3.98      inference(superposition,[status(thm)],[c_12294,c_12088]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_91905,plain,
% 27.19/3.98      ( r2_hidden(X0,sK8) != iProver_top
% 27.19/3.98      | r1_tarski(k2_relat_1(sK10),X1) != iProver_top
% 27.19/3.98      | v1_xboole_0(X1) != iProver_top ),
% 27.19/3.98      inference(global_propositional_subsumption,
% 27.19/3.98                [status(thm)],
% 27.19/3.98                [c_91260,c_45,c_46,c_155,c_159,c_8486,c_8485,c_8488,
% 27.19/3.98                 c_8638,c_8682,c_8835,c_11554]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_91924,plain,
% 27.19/3.98      ( r2_hidden(X0,sK8) != iProver_top
% 27.19/3.98      | v1_xboole_0(sK9) != iProver_top ),
% 27.19/3.98      inference(superposition,[status(thm)],[c_17008,c_91905]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_8007,plain,
% 27.19/3.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 27.19/3.98      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 27.19/3.98      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 27.19/3.98      | v1_relat_1(X0) != iProver_top ),
% 27.19/3.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_23,plain,
% 27.19/3.98      ( ~ v1_funct_2(X0,X1,X2)
% 27.19/3.98      | v1_partfun1(X0,X1)
% 27.19/3.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 27.19/3.98      | ~ v1_funct_1(X0)
% 27.19/3.98      | v1_xboole_0(X2) ),
% 27.19/3.98      inference(cnf_transformation,[],[f85]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_42,plain,
% 27.19/3.98      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 27.19/3.98      | ~ v1_funct_1(X0)
% 27.19/3.98      | ~ v1_relat_1(X0) ),
% 27.19/3.98      inference(cnf_transformation,[],[f103]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_645,plain,
% 27.19/3.98      ( v1_partfun1(X0,X1)
% 27.19/3.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 27.19/3.98      | ~ v1_funct_1(X0)
% 27.19/3.98      | ~ v1_funct_1(X3)
% 27.19/3.98      | ~ v1_relat_1(X3)
% 27.19/3.98      | v1_xboole_0(X2)
% 27.19/3.98      | X3 != X0
% 27.19/3.98      | k1_relat_1(X3) != X1
% 27.19/3.98      | k2_relat_1(X3) != X2 ),
% 27.19/3.98      inference(resolution_lifted,[status(thm)],[c_23,c_42]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_646,plain,
% 27.19/3.98      ( v1_partfun1(X0,k1_relat_1(X0))
% 27.19/3.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 27.19/3.98      | ~ v1_funct_1(X0)
% 27.19/3.98      | ~ v1_relat_1(X0)
% 27.19/3.98      | v1_xboole_0(k2_relat_1(X0)) ),
% 27.19/3.98      inference(unflattening,[status(thm)],[c_645]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_41,plain,
% 27.19/3.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 27.19/3.98      | ~ v1_funct_1(X0)
% 27.19/3.98      | ~ v1_relat_1(X0) ),
% 27.19/3.98      inference(cnf_transformation,[],[f104]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_650,plain,
% 27.19/3.98      ( v1_partfun1(X0,k1_relat_1(X0))
% 27.19/3.98      | ~ v1_funct_1(X0)
% 27.19/3.98      | ~ v1_relat_1(X0)
% 27.19/3.98      | v1_xboole_0(k2_relat_1(X0)) ),
% 27.19/3.98      inference(global_propositional_subsumption,
% 27.19/3.98                [status(thm)],
% 27.19/3.98                [c_646,c_41]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_21,plain,
% 27.19/3.98      ( v1_funct_2(X0,X1,X2)
% 27.19/3.98      | ~ v1_partfun1(X0,X1)
% 27.19/3.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 27.19/3.98      | ~ v1_funct_1(X0) ),
% 27.19/3.98      inference(cnf_transformation,[],[f83]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_44,negated_conjecture,
% 27.19/3.98      ( ~ v1_funct_2(sK10,sK8,sK9)
% 27.19/3.98      | ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9)))
% 27.19/3.98      | ~ v1_funct_1(sK10) ),
% 27.19/3.98      inference(cnf_transformation,[],[f106]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_669,plain,
% 27.19/3.98      ( ~ v1_partfun1(X0,X1)
% 27.19/3.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 27.19/3.98      | ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9)))
% 27.19/3.98      | ~ v1_funct_1(X0)
% 27.19/3.98      | ~ v1_funct_1(sK10)
% 27.19/3.98      | sK9 != X2
% 27.19/3.98      | sK8 != X1
% 27.19/3.98      | sK10 != X0 ),
% 27.19/3.98      inference(resolution_lifted,[status(thm)],[c_21,c_44]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_670,plain,
% 27.19/3.98      ( ~ v1_partfun1(sK10,sK8)
% 27.19/3.98      | ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9)))
% 27.19/3.98      | ~ v1_funct_1(sK10) ),
% 27.19/3.98      inference(unflattening,[status(thm)],[c_669]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_728,plain,
% 27.19/3.98      ( ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9)))
% 27.19/3.98      | ~ v1_funct_1(X0)
% 27.19/3.98      | ~ v1_funct_1(sK10)
% 27.19/3.98      | ~ v1_relat_1(X0)
% 27.19/3.98      | v1_xboole_0(k2_relat_1(X0))
% 27.19/3.98      | k1_relat_1(X0) != sK8
% 27.19/3.98      | sK10 != X0 ),
% 27.19/3.98      inference(resolution_lifted,[status(thm)],[c_650,c_670]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_729,plain,
% 27.19/3.98      ( ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9)))
% 27.19/3.98      | ~ v1_funct_1(sK10)
% 27.19/3.98      | ~ v1_relat_1(sK10)
% 27.19/3.98      | v1_xboole_0(k2_relat_1(sK10))
% 27.19/3.98      | k1_relat_1(sK10) != sK8 ),
% 27.19/3.98      inference(unflattening,[status(thm)],[c_728]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_17,plain,
% 27.19/3.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 27.19/3.98      | v1_relat_1(X0) ),
% 27.19/3.98      inference(cnf_transformation,[],[f78]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_741,plain,
% 27.19/3.98      ( ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9)))
% 27.19/3.98      | ~ v1_funct_1(sK10)
% 27.19/3.98      | v1_xboole_0(k2_relat_1(sK10))
% 27.19/3.98      | k1_relat_1(sK10) != sK8 ),
% 27.19/3.98      inference(forward_subsumption_resolution,
% 27.19/3.98                [status(thm)],
% 27.19/3.98                [c_729,c_17]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_7985,plain,
% 27.19/3.98      ( k1_relat_1(sK10) != sK8
% 27.19/3.98      | m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))) != iProver_top
% 27.19/3.98      | v1_funct_1(sK10) != iProver_top
% 27.19/3.98      | v1_xboole_0(k2_relat_1(sK10)) = iProver_top ),
% 27.19/3.98      inference(predicate_to_equality,[status(thm)],[c_741]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_12339,plain,
% 27.19/3.98      ( sK8 != sK8
% 27.19/3.98      | m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))) != iProver_top
% 27.19/3.98      | v1_funct_1(sK10) != iProver_top
% 27.19/3.98      | v1_xboole_0(k2_relat_1(sK10)) = iProver_top ),
% 27.19/3.98      inference(demodulation,[status(thm)],[c_12294,c_7985]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_12348,plain,
% 27.19/3.98      ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))) != iProver_top
% 27.19/3.98      | v1_funct_1(sK10) != iProver_top
% 27.19/3.98      | v1_xboole_0(k2_relat_1(sK10)) = iProver_top ),
% 27.19/3.98      inference(equality_resolution_simp,[status(thm)],[c_12339]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_730,plain,
% 27.19/3.98      ( k1_relat_1(sK10) != sK8
% 27.19/3.98      | m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))) != iProver_top
% 27.19/3.98      | v1_funct_1(sK10) != iProver_top
% 27.19/3.98      | v1_relat_1(sK10) != iProver_top
% 27.19/3.98      | v1_xboole_0(k2_relat_1(sK10)) = iProver_top ),
% 27.19/3.98      inference(predicate_to_equality,[status(thm)],[c_729]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_13965,plain,
% 27.19/3.98      ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))) != iProver_top
% 27.19/3.98      | v1_xboole_0(k2_relat_1(sK10)) = iProver_top ),
% 27.19/3.98      inference(global_propositional_subsumption,
% 27.19/3.98                [status(thm)],
% 27.19/3.98                [c_12348,c_45,c_46,c_155,c_159,c_730,c_8486,c_8485,
% 27.19/3.98                 c_8488,c_8638,c_8682,c_8835,c_11554,c_12294]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_13972,plain,
% 27.19/3.98      ( r1_tarski(k1_relat_1(sK10),sK8) != iProver_top
% 27.19/3.98      | r1_tarski(k2_relat_1(sK10),sK9) != iProver_top
% 27.19/3.98      | v1_relat_1(sK10) != iProver_top
% 27.19/3.98      | v1_xboole_0(k2_relat_1(sK10)) = iProver_top ),
% 27.19/3.98      inference(superposition,[status(thm)],[c_8007,c_13965]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_13977,plain,
% 27.19/3.98      ( r1_tarski(k2_relat_1(sK10),sK9) != iProver_top
% 27.19/3.98      | r1_tarski(sK8,sK8) != iProver_top
% 27.19/3.98      | v1_relat_1(sK10) != iProver_top
% 27.19/3.98      | v1_xboole_0(k2_relat_1(sK10)) = iProver_top ),
% 27.19/3.98      inference(light_normalisation,[status(thm)],[c_13972,c_12294]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_14123,plain,
% 27.19/3.98      ( r1_tarski(sK8,sK8) != iProver_top
% 27.19/3.98      | r1_tarski(k2_relat_1(sK10),sK9) != iProver_top
% 27.19/3.98      | v1_xboole_0(k2_relat_1(sK10)) = iProver_top ),
% 27.19/3.98      inference(global_propositional_subsumption,
% 27.19/3.98                [status(thm)],
% 27.19/3.98                [c_13977,c_11554]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_14124,plain,
% 27.19/3.98      ( r1_tarski(k2_relat_1(sK10),sK9) != iProver_top
% 27.19/3.98      | r1_tarski(sK8,sK8) != iProver_top
% 27.19/3.98      | v1_xboole_0(k2_relat_1(sK10)) = iProver_top ),
% 27.19/3.98      inference(renaming,[status(thm)],[c_14123]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_4,plain,
% 27.19/3.98      ( r1_tarski(X0,X0) ),
% 27.19/3.98      inference(cnf_transformation,[],[f107]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_8018,plain,
% 27.19/3.98      ( r1_tarski(X0,X0) = iProver_top ),
% 27.19/3.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_14130,plain,
% 27.19/3.98      ( r1_tarski(k2_relat_1(sK10),sK9) != iProver_top
% 27.19/3.98      | v1_xboole_0(k2_relat_1(sK10)) = iProver_top ),
% 27.19/3.98      inference(forward_subsumption_resolution,
% 27.19/3.98                [status(thm)],
% 27.19/3.98                [c_14124,c_8018]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_91915,plain,
% 27.19/3.98      ( r2_hidden(X0,sK8) != iProver_top
% 27.19/3.98      | v1_xboole_0(k2_relat_1(sK10)) != iProver_top ),
% 27.19/3.98      inference(superposition,[status(thm)],[c_8018,c_91905]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_92161,plain,
% 27.19/3.98      ( r2_hidden(X0,sK8) != iProver_top ),
% 27.19/3.98      inference(global_propositional_subsumption,
% 27.19/3.98                [status(thm)],
% 27.19/3.98                [c_91924,c_46,c_14130,c_16334,c_91915]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_92197,plain,
% 27.19/3.98      ( k2_relat_1(sK10) = sK8
% 27.19/3.98      | r2_hidden(sK3(sK10,sK8),sK8) = iProver_top ),
% 27.19/3.98      inference(superposition,[status(thm)],[c_13512,c_92161]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_92254,plain,
% 27.19/3.98      ( k2_relat_1(sK10) = sK8 ),
% 27.19/3.98      inference(forward_subsumption_resolution,
% 27.19/3.98                [status(thm)],
% 27.19/3.98                [c_92197,c_92161]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_1,plain,
% 27.19/3.98      ( r2_hidden(sK1(X0,X1),X0) | r1_tarski(X0,X1) ),
% 27.19/3.98      inference(cnf_transformation,[],[f62]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_8021,plain,
% 27.19/3.98      ( r2_hidden(sK1(X0,X1),X0) = iProver_top
% 27.19/3.98      | r1_tarski(X0,X1) = iProver_top ),
% 27.19/3.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_91226,plain,
% 27.19/3.98      ( r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 27.19/3.98      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 27.19/3.98      | v1_funct_1(X0) != iProver_top
% 27.19/3.98      | v1_relat_1(X0) != iProver_top
% 27.19/3.98      | v1_xboole_0(X2) != iProver_top ),
% 27.19/3.98      inference(superposition,[status(thm)],[c_8021,c_12088]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_91794,plain,
% 27.19/3.98      ( r1_tarski(k1_relat_1(sK10),sK10) = iProver_top
% 27.19/3.98      | r1_tarski(k2_relat_1(sK10),sK10) != iProver_top
% 27.19/3.98      | v1_funct_1(sK10) != iProver_top
% 27.19/3.98      | v1_relat_1(sK10) != iProver_top
% 27.19/3.98      | v1_xboole_0(sK10) != iProver_top ),
% 27.19/3.98      inference(instantiation,[status(thm)],[c_91226]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_91162,plain,
% 27.19/3.98      ( ~ r2_hidden(sK1(sK10,k6_partfun1(sK8)),sK10)
% 27.19/3.98      | ~ r1_tarski(sK10,X0)
% 27.19/3.98      | ~ v1_xboole_0(X0) ),
% 27.19/3.98      inference(instantiation,[status(thm)],[c_431]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_91177,plain,
% 27.19/3.98      ( ~ r2_hidden(sK1(sK10,k6_partfun1(sK8)),sK10)
% 27.19/3.98      | ~ r1_tarski(sK10,sK10)
% 27.19/3.98      | ~ v1_xboole_0(sK10) ),
% 27.19/3.98      inference(instantiation,[status(thm)],[c_91162]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_19089,plain,
% 27.19/3.98      ( X0 != X1
% 27.19/3.98      | X0 = k1_relat_1(sK7(sK9,sK8,sK10))
% 27.19/3.98      | k1_relat_1(sK7(sK9,sK8,sK10)) != X1 ),
% 27.19/3.98      inference(instantiation,[status(thm)],[c_7116]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_84625,plain,
% 27.19/3.98      ( X0 = k1_relat_1(sK7(sK9,sK8,sK10))
% 27.19/3.98      | X0 != k2_relat_1(X1)
% 27.19/3.98      | k1_relat_1(sK7(sK9,sK8,sK10)) != k2_relat_1(X1) ),
% 27.19/3.98      inference(instantiation,[status(thm)],[c_19089]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_84629,plain,
% 27.19/3.98      ( k1_relat_1(sK7(sK9,sK8,sK10)) != k2_relat_1(sK10)
% 27.19/3.98      | sK10 = k1_relat_1(sK7(sK9,sK8,sK10))
% 27.19/3.98      | sK10 != k2_relat_1(sK10) ),
% 27.19/3.98      inference(instantiation,[status(thm)],[c_84625]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_11792,plain,
% 27.19/3.98      ( X0 != X1 | sK8 != X1 | sK8 = X0 ),
% 27.19/3.98      inference(instantiation,[status(thm)],[c_7116]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_70134,plain,
% 27.19/3.98      ( X0 != k1_relat_1(sK7(sK9,sK8,sK10))
% 27.19/3.98      | sK8 = X0
% 27.19/3.98      | sK8 != k1_relat_1(sK7(sK9,sK8,sK10)) ),
% 27.19/3.98      inference(instantiation,[status(thm)],[c_11792]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_70135,plain,
% 27.19/3.98      ( sK8 != k1_relat_1(sK7(sK9,sK8,sK10))
% 27.19/3.98      | sK8 = sK10
% 27.19/3.98      | sK10 != k1_relat_1(sK7(sK9,sK8,sK10)) ),
% 27.19/3.98      inference(instantiation,[status(thm)],[c_70134]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_23324,plain,
% 27.19/3.98      ( X0 != sK8 | sK8 = X0 | sK8 != sK8 ),
% 27.19/3.98      inference(instantiation,[status(thm)],[c_11792]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_60264,plain,
% 27.19/3.98      ( k1_relat_1(sK7(sK9,sK8,sK10)) != sK8
% 27.19/3.98      | sK8 = k1_relat_1(sK7(sK9,sK8,sK10))
% 27.19/3.98      | sK8 != sK8 ),
% 27.19/3.98      inference(instantiation,[status(thm)],[c_23324]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_57169,plain,
% 27.19/3.98      ( ~ r2_hidden(sK1(k1_relat_1(sK10),sK8),k1_relat_1(sK10))
% 27.19/3.98      | ~ r1_tarski(k1_relat_1(sK10),X0)
% 27.19/3.98      | ~ v1_xboole_0(X0) ),
% 27.19/3.98      inference(instantiation,[status(thm)],[c_431]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_57186,plain,
% 27.19/3.98      ( ~ r2_hidden(sK1(k1_relat_1(sK10),sK8),k1_relat_1(sK10))
% 27.19/3.98      | ~ r1_tarski(k1_relat_1(sK10),sK10)
% 27.19/3.98      | ~ v1_xboole_0(sK10) ),
% 27.19/3.98      inference(instantiation,[status(thm)],[c_57169]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_52443,plain,
% 27.19/3.98      ( ~ r2_hidden(sK1(X0,k1_relat_1(X1)),X0)
% 27.19/3.98      | ~ r1_tarski(X0,X2)
% 27.19/3.98      | ~ v1_xboole_0(X2) ),
% 27.19/3.98      inference(instantiation,[status(thm)],[c_431]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_52457,plain,
% 27.19/3.98      ( r2_hidden(sK1(X0,k1_relat_1(X1)),X0) != iProver_top
% 27.19/3.98      | r1_tarski(X0,X2) != iProver_top
% 27.19/3.98      | v1_xboole_0(X2) != iProver_top ),
% 27.19/3.98      inference(predicate_to_equality,[status(thm)],[c_52443]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_52459,plain,
% 27.19/3.98      ( r2_hidden(sK1(sK10,k1_relat_1(sK10)),sK10) != iProver_top
% 27.19/3.98      | r1_tarski(sK10,sK10) != iProver_top
% 27.19/3.98      | v1_xboole_0(sK10) != iProver_top ),
% 27.19/3.98      inference(instantiation,[status(thm)],[c_52457]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_31466,plain,
% 27.19/3.98      ( ~ r2_hidden(sK2(X0,X1),X1)
% 27.19/3.98      | ~ r1_tarski(X1,X2)
% 27.19/3.98      | ~ v1_xboole_0(X2) ),
% 27.19/3.98      inference(instantiation,[status(thm)],[c_431]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_31480,plain,
% 27.19/3.98      ( r2_hidden(sK2(X0,X1),X1) != iProver_top
% 27.19/3.98      | r1_tarski(X1,X2) != iProver_top
% 27.19/3.98      | v1_xboole_0(X2) != iProver_top ),
% 27.19/3.98      inference(predicate_to_equality,[status(thm)],[c_31466]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_31482,plain,
% 27.19/3.98      ( r2_hidden(sK2(sK10,sK10),sK10) != iProver_top
% 27.19/3.98      | r1_tarski(sK10,sK10) != iProver_top
% 27.19/3.98      | v1_xboole_0(sK10) != iProver_top ),
% 27.19/3.98      inference(instantiation,[status(thm)],[c_31480]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_29247,plain,
% 27.19/3.98      ( X0 != X1 | X0 = k2_relat_1(X2) | k2_relat_1(X2) != X1 ),
% 27.19/3.98      inference(instantiation,[status(thm)],[c_7116]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_29248,plain,
% 27.19/3.98      ( k2_relat_1(sK10) != sK10
% 27.19/3.98      | sK10 = k2_relat_1(sK10)
% 27.19/3.98      | sK10 != sK10 ),
% 27.19/3.98      inference(instantiation,[status(thm)],[c_29247]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_20178,plain,
% 27.19/3.98      ( r2_hidden(sK1(sK10,k6_partfun1(sK8)),sK10)
% 27.19/3.98      | r1_tarski(sK10,k6_partfun1(sK8)) ),
% 27.19/3.98      inference(instantiation,[status(thm)],[c_1]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_18835,plain,
% 27.19/3.98      ( ~ r1_tarski(X0,X1)
% 27.19/3.98      | r1_tarski(k1_relat_1(X2),X1)
% 27.19/3.98      | k1_relat_1(X2) != X0 ),
% 27.19/3.98      inference(instantiation,[status(thm)],[c_7117]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_18837,plain,
% 27.19/3.98      ( r1_tarski(k1_relat_1(sK10),sK10)
% 27.19/3.98      | ~ r1_tarski(sK10,sK10)
% 27.19/3.98      | k1_relat_1(sK10) != sK10 ),
% 27.19/3.98      inference(instantiation,[status(thm)],[c_18835]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_10851,plain,
% 27.19/3.98      ( X0 != X1
% 27.19/3.98      | k1_relat_1(sK7(sK9,sK8,sK10)) != X1
% 27.19/3.98      | k1_relat_1(sK7(sK9,sK8,sK10)) = X0 ),
% 27.19/3.98      inference(instantiation,[status(thm)],[c_7116]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_16252,plain,
% 27.19/3.98      ( X0 != sK8
% 27.19/3.98      | k1_relat_1(sK7(sK9,sK8,sK10)) = X0
% 27.19/3.98      | k1_relat_1(sK7(sK9,sK8,sK10)) != sK8 ),
% 27.19/3.98      inference(instantiation,[status(thm)],[c_10851]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_18021,plain,
% 27.19/3.98      ( k1_relat_1(sK7(sK9,sK8,sK10)) = k2_relat_1(X0)
% 27.19/3.98      | k1_relat_1(sK7(sK9,sK8,sK10)) != sK8
% 27.19/3.98      | k2_relat_1(X0) != sK8 ),
% 27.19/3.98      inference(instantiation,[status(thm)],[c_16252]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_18023,plain,
% 27.19/3.98      ( k1_relat_1(sK7(sK9,sK8,sK10)) = k2_relat_1(sK10)
% 27.19/3.98      | k1_relat_1(sK7(sK9,sK8,sK10)) != sK8
% 27.19/3.98      | k2_relat_1(sK10) != sK8 ),
% 27.19/3.98      inference(instantiation,[status(thm)],[c_18021]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_16386,plain,
% 27.19/3.98      ( ~ r2_hidden(sK10,k1_funct_2(sK8,sK9))
% 27.19/3.98      | r1_tarski(k2_relat_1(sK10),sK9) ),
% 27.19/3.98      inference(predicate_to_equality_rev,[status(thm)],[c_16334]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_8017,plain,
% 27.19/3.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 27.19/3.98      | r1_tarski(X0,X1) != iProver_top ),
% 27.19/3.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_19,plain,
% 27.19/3.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 27.19/3.98      | ~ v1_xboole_0(X2)
% 27.19/3.98      | v1_xboole_0(X0) ),
% 27.19/3.98      inference(cnf_transformation,[],[f80]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_8008,plain,
% 27.19/3.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 27.19/3.98      | v1_xboole_0(X2) != iProver_top
% 27.19/3.98      | v1_xboole_0(X0) = iProver_top ),
% 27.19/3.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_9165,plain,
% 27.19/3.98      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 27.19/3.98      | v1_xboole_0(X2) != iProver_top
% 27.19/3.98      | v1_xboole_0(X0) = iProver_top ),
% 27.19/3.98      inference(superposition,[status(thm)],[c_8017,c_8008]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_16022,plain,
% 27.19/3.98      ( v1_xboole_0(X0) != iProver_top
% 27.19/3.98      | v1_xboole_0(k2_zfmisc_1(X1,X0)) = iProver_top ),
% 27.19/3.98      inference(superposition,[status(thm)],[c_8018,c_9165]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_16068,plain,
% 27.19/3.98      ( ~ v1_xboole_0(X0) | v1_xboole_0(k2_zfmisc_1(X1,X0)) ),
% 27.19/3.98      inference(predicate_to_equality_rev,[status(thm)],[c_16022]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_16070,plain,
% 27.19/3.98      ( v1_xboole_0(k2_zfmisc_1(sK10,sK10)) | ~ v1_xboole_0(sK10) ),
% 27.19/3.98      inference(instantiation,[status(thm)],[c_16068]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_15631,plain,
% 27.19/3.98      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 27.19/3.98      | ~ r1_tarski(k1_relat_1(X1),X0)
% 27.19/3.98      | k1_relat_1(X1) = X0 ),
% 27.19/3.98      inference(instantiation,[status(thm)],[c_3]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_15632,plain,
% 27.19/3.98      ( k1_relat_1(X0) = X1
% 27.19/3.98      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 27.19/3.98      | r1_tarski(k1_relat_1(X0),X1) != iProver_top ),
% 27.19/3.98      inference(predicate_to_equality,[status(thm)],[c_15631]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_15634,plain,
% 27.19/3.98      ( k1_relat_1(sK10) = sK10
% 27.19/3.98      | r1_tarski(k1_relat_1(sK10),sK10) != iProver_top
% 27.19/3.98      | r1_tarski(sK10,k1_relat_1(sK10)) != iProver_top ),
% 27.19/3.98      inference(instantiation,[status(thm)],[c_15632]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_9042,plain,
% 27.19/3.98      ( r1_tarski(X0,X1) != iProver_top
% 27.19/3.98      | r1_tarski(X0,X2) = iProver_top
% 27.19/3.98      | v1_xboole_0(X1) != iProver_top ),
% 27.19/3.98      inference(superposition,[status(thm)],[c_8021,c_7989]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_14550,plain,
% 27.19/3.98      ( r1_tarski(X0,X1) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 27.19/3.98      inference(superposition,[status(thm)],[c_8018,c_9042]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_18,plain,
% 27.19/3.98      ( v5_relat_1(X0,X1)
% 27.19/3.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 27.19/3.98      inference(cnf_transformation,[],[f79]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_10,plain,
% 27.19/3.98      ( ~ v5_relat_1(X0,X1)
% 27.19/3.98      | r1_tarski(k2_relat_1(X0),X1)
% 27.19/3.98      | ~ v1_relat_1(X0) ),
% 27.19/3.98      inference(cnf_transformation,[],[f70]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_578,plain,
% 27.19/3.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 27.19/3.98      | r1_tarski(k2_relat_1(X0),X2)
% 27.19/3.98      | ~ v1_relat_1(X0) ),
% 27.19/3.98      inference(resolution,[status(thm)],[c_18,c_10]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_582,plain,
% 27.19/3.98      ( r1_tarski(k2_relat_1(X0),X2)
% 27.19/3.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 27.19/3.98      inference(global_propositional_subsumption,
% 27.19/3.98                [status(thm)],
% 27.19/3.98                [c_578,c_17]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_583,plain,
% 27.19/3.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 27.19/3.98      | r1_tarski(k2_relat_1(X0),X2) ),
% 27.19/3.98      inference(renaming,[status(thm)],[c_582]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_7988,plain,
% 27.19/3.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 27.19/3.98      | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
% 27.19/3.98      inference(predicate_to_equality,[status(thm)],[c_583]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_8526,plain,
% 27.19/3.98      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 27.19/3.98      | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
% 27.19/3.98      inference(superposition,[status(thm)],[c_8017,c_7988]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_14815,plain,
% 27.19/3.98      ( r1_tarski(k2_relat_1(X0),X1) = iProver_top
% 27.19/3.98      | v1_xboole_0(X0) != iProver_top ),
% 27.19/3.98      inference(superposition,[status(thm)],[c_14550,c_8526]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_14861,plain,
% 27.19/3.98      ( r1_tarski(k2_relat_1(sK10),sK10) = iProver_top
% 27.19/3.98      | v1_xboole_0(sK10) != iProver_top ),
% 27.19/3.98      inference(instantiation,[status(thm)],[c_14815]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_39,plain,
% 27.19/3.98      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 27.19/3.98      inference(cnf_transformation,[],[f101]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_7992,plain,
% 27.19/3.98      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 27.19/3.98      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_7,plain,
% 27.19/3.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 27.19/3.98      inference(cnf_transformation,[],[f67]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_8016,plain,
% 27.19/3.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 27.19/3.98      | r1_tarski(X0,X1) = iProver_top ),
% 27.19/3.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_8434,plain,
% 27.19/3.98      ( r1_tarski(k6_partfun1(X0),k2_zfmisc_1(X0,X0)) = iProver_top ),
% 27.19/3.98      inference(superposition,[status(thm)],[c_7992,c_8016]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_14552,plain,
% 27.19/3.98      ( r1_tarski(k6_partfun1(X0),X1) = iProver_top
% 27.19/3.98      | v1_xboole_0(k2_zfmisc_1(X0,X0)) != iProver_top ),
% 27.19/3.98      inference(superposition,[status(thm)],[c_8434,c_9042]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_14606,plain,
% 27.19/3.98      ( r1_tarski(k6_partfun1(X0),X1)
% 27.19/3.98      | ~ v1_xboole_0(k2_zfmisc_1(X0,X0)) ),
% 27.19/3.98      inference(predicate_to_equality_rev,[status(thm)],[c_14552]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_14608,plain,
% 27.19/3.98      ( r1_tarski(k6_partfun1(sK10),sK10)
% 27.19/3.98      | ~ v1_xboole_0(k2_zfmisc_1(sK10,sK10)) ),
% 27.19/3.98      inference(instantiation,[status(thm)],[c_14606]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_14131,plain,
% 27.19/3.98      ( ~ r1_tarski(k2_relat_1(sK10),sK9)
% 27.19/3.98      | v1_xboole_0(k2_relat_1(sK10)) ),
% 27.19/3.98      inference(predicate_to_equality_rev,[status(thm)],[c_14130]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_13829,plain,
% 27.19/3.98      ( r2_hidden(sK1(X0,k1_relat_1(X1)),X0)
% 27.19/3.98      | r1_tarski(X0,k1_relat_1(X1)) ),
% 27.19/3.98      inference(instantiation,[status(thm)],[c_1]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_13840,plain,
% 27.19/3.98      ( r2_hidden(sK1(X0,k1_relat_1(X1)),X0) = iProver_top
% 27.19/3.98      | r1_tarski(X0,k1_relat_1(X1)) = iProver_top ),
% 27.19/3.98      inference(predicate_to_equality,[status(thm)],[c_13829]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_13842,plain,
% 27.19/3.98      ( r2_hidden(sK1(sK10,k1_relat_1(sK10)),sK10) = iProver_top
% 27.19/3.98      | r1_tarski(sK10,k1_relat_1(sK10)) = iProver_top ),
% 27.19/3.98      inference(instantiation,[status(thm)],[c_13840]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_12901,plain,
% 27.19/3.98      ( k2_relat_1(X0) = X1
% 27.19/3.98      | r2_hidden(sK2(X0,X1),X1) = iProver_top
% 27.19/3.98      | r1_tarski(k1_relat_1(X0),X2) != iProver_top
% 27.19/3.98      | v1_funct_1(X0) != iProver_top
% 27.19/3.98      | v1_relat_1(X0) != iProver_top
% 27.19/3.98      | v1_xboole_0(X2) != iProver_top ),
% 27.19/3.98      inference(superposition,[status(thm)],[c_8013,c_7989]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_13040,plain,
% 27.19/3.98      ( k2_relat_1(sK10) = sK10
% 27.19/3.98      | r2_hidden(sK2(sK10,sK10),sK10) = iProver_top
% 27.19/3.98      | r1_tarski(k1_relat_1(sK10),sK10) != iProver_top
% 27.19/3.98      | v1_funct_1(sK10) != iProver_top
% 27.19/3.98      | v1_relat_1(sK10) != iProver_top
% 27.19/3.98      | v1_xboole_0(sK10) != iProver_top ),
% 27.19/3.98      inference(instantiation,[status(thm)],[c_12901]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_7991,plain,
% 27.19/3.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 27.19/3.98      | v1_funct_1(X0) != iProver_top
% 27.19/3.98      | v1_relat_1(X0) != iProver_top ),
% 27.19/3.98      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_12357,plain,
% 27.19/3.98      ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,k2_relat_1(sK10)))) = iProver_top
% 27.19/3.98      | v1_funct_1(sK10) != iProver_top
% 27.19/3.98      | v1_relat_1(sK10) != iProver_top ),
% 27.19/3.98      inference(superposition,[status(thm)],[c_12294,c_7991]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_12446,plain,
% 27.19/3.98      ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,k2_relat_1(sK10)))) = iProver_top ),
% 27.19/3.98      inference(global_propositional_subsumption,
% 27.19/3.98                [status(thm)],
% 27.19/3.98                [c_12357,c_45,c_46,c_155,c_159,c_8486,c_8485,c_8488,
% 27.19/3.98                 c_8638,c_8682,c_8835,c_11554]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_12452,plain,
% 27.19/3.98      ( v1_xboole_0(k2_relat_1(sK10)) != iProver_top
% 27.19/3.98      | v1_xboole_0(sK10) = iProver_top ),
% 27.19/3.98      inference(superposition,[status(thm)],[c_12446,c_8008]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_12463,plain,
% 27.19/3.98      ( ~ v1_xboole_0(k2_relat_1(sK10)) | v1_xboole_0(sK10) ),
% 27.19/3.98      inference(predicate_to_equality_rev,[status(thm)],[c_12452]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_7115,plain,( X0 = X0 ),theory(equality) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_12403,plain,
% 27.19/3.98      ( sK8 = sK8 ),
% 27.19/3.98      inference(instantiation,[status(thm)],[c_7115]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_7131,plain,
% 27.19/3.98      ( X0 != X1 | k6_partfun1(X0) = k6_partfun1(X1) ),
% 27.19/3.98      theory(equality) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_11814,plain,
% 27.19/3.98      ( k6_partfun1(sK8) = k6_partfun1(X0) | sK8 != X0 ),
% 27.19/3.98      inference(instantiation,[status(thm)],[c_7131]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_11816,plain,
% 27.19/3.98      ( k6_partfun1(sK8) = k6_partfun1(sK10) | sK8 != sK10 ),
% 27.19/3.98      inference(instantiation,[status(thm)],[c_11814]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_11676,plain,
% 27.19/3.98      ( r2_hidden(sK1(k1_relat_1(sK10),sK8),k1_relat_1(sK10))
% 27.19/3.98      | r1_tarski(k1_relat_1(sK10),sK8) ),
% 27.19/3.98      inference(instantiation,[status(thm)],[c_1]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_11598,plain,
% 27.19/3.98      ( v1_relat_1(sK10) ),
% 27.19/3.98      inference(predicate_to_equality_rev,[status(thm)],[c_11554]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_9744,plain,
% 27.19/3.98      ( ~ r1_tarski(k6_partfun1(sK8),sK10)
% 27.19/3.98      | ~ r1_tarski(sK10,k6_partfun1(sK8))
% 27.19/3.98      | k6_partfun1(sK8) = sK10 ),
% 27.19/3.98      inference(instantiation,[status(thm)],[c_3]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_8407,plain,
% 27.19/3.98      ( ~ sP0(X0,X1,k1_funct_2(sK8,sK9))
% 27.19/3.98      | ~ r2_hidden(sK10,k1_funct_2(sK8,sK9))
% 27.19/3.98      | k1_relat_1(sK7(X0,X1,sK10)) = X1 ),
% 27.19/3.98      inference(instantiation,[status(thm)],[c_33]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_8680,plain,
% 27.19/3.98      ( ~ sP0(sK9,sK8,k1_funct_2(sK8,sK9))
% 27.19/3.98      | ~ r2_hidden(sK10,k1_funct_2(sK8,sK9))
% 27.19/3.98      | k1_relat_1(sK7(sK9,sK8,sK10)) = sK8 ),
% 27.19/3.98      inference(instantiation,[status(thm)],[c_8407]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_8637,plain,
% 27.19/3.98      ( ~ v1_funct_1(sK7(sK9,sK8,sK10))
% 27.19/3.98      | v1_funct_1(sK10)
% 27.19/3.98      | sK10 != sK7(sK9,sK8,sK10) ),
% 27.19/3.98      inference(instantiation,[status(thm)],[c_8635]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_40,plain,
% 27.19/3.98      ( v1_partfun1(k6_partfun1(X0),X0) ),
% 27.19/3.98      inference(cnf_transformation,[],[f100]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_715,plain,
% 27.19/3.98      ( ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9)))
% 27.19/3.98      | ~ v1_funct_1(sK10)
% 27.19/3.98      | k6_partfun1(X0) != sK10
% 27.19/3.98      | sK8 != X0 ),
% 27.19/3.98      inference(resolution_lifted,[status(thm)],[c_40,c_670]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_716,plain,
% 27.19/3.98      ( ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9)))
% 27.19/3.98      | ~ v1_funct_1(sK10)
% 27.19/3.98      | k6_partfun1(sK8) != sK10 ),
% 27.19/3.98      inference(unflattening,[status(thm)],[c_715]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_154,plain,
% 27.19/3.98      ( r1_tarski(X0,X0) = iProver_top ),
% 27.19/3.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(c_156,plain,
% 27.19/3.98      ( r1_tarski(sK10,sK10) = iProver_top ),
% 27.19/3.98      inference(instantiation,[status(thm)],[c_154]) ).
% 27.19/3.98  
% 27.19/3.98  cnf(contradiction,plain,
% 27.19/3.98      ( $false ),
% 27.19/3.98      inference(minisat,
% 27.19/3.98                [status(thm)],
% 27.19/3.98                [c_126212,c_107813,c_92254,c_91794,c_91177,c_84629,
% 27.19/3.98                 c_70135,c_60264,c_57186,c_52459,c_31482,c_29248,c_20178,
% 27.19/3.98                 c_18837,c_18023,c_16386,c_16334,c_16070,c_15634,c_14861,
% 27.19/3.98                 c_14608,c_14131,c_14130,c_13842,c_13040,c_12463,c_12452,
% 27.19/3.98                 c_12403,c_11816,c_11676,c_11598,c_11554,c_9744,c_8835,
% 27.19/3.98                 c_8680,c_8682,c_8638,c_8637,c_8488,c_8485,c_8486,c_8484,
% 27.19/3.98                 c_716,c_159,c_156,c_155,c_46,c_45]) ).
% 27.19/3.98  
% 27.19/3.98  
% 27.19/3.98  % SZS output end CNFRefutation for theBenchmark.p
% 27.19/3.98  
% 27.19/3.98  ------                               Statistics
% 27.19/3.98  
% 27.19/3.98  ------ General
% 27.19/3.98  
% 27.19/3.98  abstr_ref_over_cycles:                  0
% 27.19/3.98  abstr_ref_under_cycles:                 0
% 27.19/3.98  gc_basic_clause_elim:                   0
% 27.19/3.98  forced_gc_time:                         0
% 27.19/3.98  parsing_time:                           0.01
% 27.19/3.98  unif_index_cands_time:                  0.
% 27.19/3.98  unif_index_add_time:                    0.
% 27.19/3.98  orderings_time:                         0.
% 27.19/3.98  out_proof_time:                         0.022
% 27.19/3.98  total_time:                             3.173
% 27.19/3.98  num_of_symbols:                         58
% 27.19/3.98  num_of_terms:                           80321
% 27.19/3.98  
% 27.19/3.98  ------ Preprocessing
% 27.19/3.98  
% 27.19/3.98  num_of_splits:                          0
% 27.19/3.98  num_of_split_atoms:                     0
% 27.19/3.98  num_of_reused_defs:                     0
% 27.19/3.98  num_eq_ax_congr_red:                    62
% 27.19/3.98  num_of_sem_filtered_clauses:            1
% 27.19/3.98  num_of_subtypes:                        0
% 27.19/3.98  monotx_restored_types:                  0
% 27.19/3.98  sat_num_of_epr_types:                   0
% 27.19/3.98  sat_num_of_non_cyclic_types:            0
% 27.19/3.98  sat_guarded_non_collapsed_types:        0
% 27.19/3.98  num_pure_diseq_elim:                    0
% 27.19/3.98  simp_replaced_by:                       0
% 27.19/3.98  res_preprocessed:                       191
% 27.19/3.98  prep_upred:                             0
% 27.19/3.98  prep_unflattend:                        249
% 27.19/3.98  smt_new_axioms:                         0
% 27.19/3.98  pred_elim_cands:                        7
% 27.19/3.98  pred_elim:                              3
% 27.19/3.98  pred_elim_cl:                           4
% 27.19/3.98  pred_elim_cycles:                       12
% 27.19/3.98  merged_defs:                            8
% 27.19/3.98  merged_defs_ncl:                        0
% 27.19/3.98  bin_hyper_res:                          9
% 27.19/3.98  prep_cycles:                            4
% 27.19/3.98  pred_elim_time:                         0.087
% 27.19/3.98  splitting_time:                         0.
% 27.19/3.98  sem_filter_time:                        0.
% 27.19/3.98  monotx_time:                            0.
% 27.19/3.98  subtype_inf_time:                       0.
% 27.19/3.98  
% 27.19/3.98  ------ Problem properties
% 27.19/3.98  
% 27.19/3.98  clauses:                                38
% 27.19/3.98  conjectures:                            1
% 27.19/3.98  epr:                                    4
% 27.19/3.98  horn:                                   30
% 27.19/3.98  ground:                                 4
% 27.19/3.98  unary:                                  4
% 27.19/3.98  binary:                                 7
% 27.19/3.98  lits:                                   117
% 27.19/3.98  lits_eq:                                17
% 27.19/3.98  fd_pure:                                0
% 27.19/3.98  fd_pseudo:                              0
% 27.19/3.98  fd_cond:                                0
% 27.19/3.98  fd_pseudo_cond:                         5
% 27.19/3.98  ac_symbols:                             0
% 27.19/3.98  
% 27.19/3.98  ------ Propositional Solver
% 27.19/3.98  
% 27.19/3.98  prop_solver_calls:                      40
% 27.19/3.98  prop_fast_solver_calls:                 5001
% 27.19/3.98  smt_solver_calls:                       0
% 27.19/3.98  smt_fast_solver_calls:                  0
% 27.19/3.98  prop_num_of_clauses:                    37646
% 27.19/3.98  prop_preprocess_simplified:             46815
% 27.19/3.98  prop_fo_subsumed:                       231
% 27.19/3.98  prop_solver_time:                       0.
% 27.19/3.98  smt_solver_time:                        0.
% 27.19/3.98  smt_fast_solver_time:                   0.
% 27.19/3.98  prop_fast_solver_time:                  0.
% 27.19/3.98  prop_unsat_core_time:                   0.004
% 27.19/3.98  
% 27.19/3.98  ------ QBF
% 27.19/3.98  
% 27.19/3.98  qbf_q_res:                              0
% 27.19/3.98  qbf_num_tautologies:                    0
% 27.19/3.98  qbf_prep_cycles:                        0
% 27.19/3.98  
% 27.19/3.98  ------ BMC1
% 27.19/3.98  
% 27.19/3.98  bmc1_current_bound:                     -1
% 27.19/3.98  bmc1_last_solved_bound:                 -1
% 27.19/3.98  bmc1_unsat_core_size:                   -1
% 27.19/3.98  bmc1_unsat_core_parents_size:           -1
% 27.19/3.98  bmc1_merge_next_fun:                    0
% 27.19/3.98  bmc1_unsat_core_clauses_time:           0.
% 27.19/3.98  
% 27.19/3.98  ------ Instantiation
% 27.19/3.98  
% 27.19/3.98  inst_num_of_clauses:                    59
% 27.19/3.98  inst_num_in_passive:                    32
% 27.19/3.98  inst_num_in_active:                     1974
% 27.19/3.98  inst_num_in_unprocessed:                4
% 27.19/3.98  inst_num_of_loops:                      3023
% 27.19/3.98  inst_num_of_learning_restarts:          1
% 27.19/3.98  inst_num_moves_active_passive:          1045
% 27.19/3.98  inst_lit_activity:                      0
% 27.19/3.98  inst_lit_activity_moves:                0
% 27.19/3.98  inst_num_tautologies:                   0
% 27.19/3.98  inst_num_prop_implied:                  0
% 27.19/3.98  inst_num_existing_simplified:           0
% 27.19/3.98  inst_num_eq_res_simplified:             0
% 27.19/3.98  inst_num_child_elim:                    0
% 27.19/3.98  inst_num_of_dismatching_blockings:      6772
% 27.19/3.98  inst_num_of_non_proper_insts:           6669
% 27.19/3.98  inst_num_of_duplicates:                 0
% 27.19/3.98  inst_inst_num_from_inst_to_res:         0
% 27.19/3.98  inst_dismatching_checking_time:         0.
% 27.19/3.98  
% 27.19/3.98  ------ Resolution
% 27.19/3.98  
% 27.19/3.98  res_num_of_clauses:                     55
% 27.19/3.98  res_num_in_passive:                     55
% 27.19/3.98  res_num_in_active:                      0
% 27.19/3.98  res_num_of_loops:                       195
% 27.19/3.98  res_forward_subset_subsumed:            403
% 27.19/3.98  res_backward_subset_subsumed:           6
% 27.19/3.98  res_forward_subsumed:                   0
% 27.19/3.98  res_backward_subsumed:                  0
% 27.19/3.98  res_forward_subsumption_resolution:     4
% 27.19/3.98  res_backward_subsumption_resolution:    0
% 27.19/3.98  res_clause_to_clause_subsumption:       21139
% 27.19/3.98  res_orphan_elimination:                 0
% 27.19/3.98  res_tautology_del:                      548
% 27.19/3.98  res_num_eq_res_simplified:              0
% 27.19/3.98  res_num_sel_changes:                    0
% 27.19/3.98  res_moves_from_active_to_pass:          0
% 27.19/3.98  
% 27.19/3.98  ------ Superposition
% 27.19/3.98  
% 27.19/3.98  sup_time_total:                         0.
% 27.19/3.98  sup_time_generating:                    0.
% 27.19/3.98  sup_time_sim_full:                      0.
% 27.19/3.98  sup_time_sim_immed:                     0.
% 27.19/3.98  
% 27.19/3.98  sup_num_of_clauses:                     4874
% 27.19/3.98  sup_num_in_active:                      410
% 27.19/3.98  sup_num_in_passive:                     4464
% 27.19/3.98  sup_num_of_loops:                       604
% 27.19/3.98  sup_fw_superposition:                   3666
% 27.19/3.98  sup_bw_superposition:                   2896
% 27.19/3.98  sup_immediate_simplified:               1239
% 27.19/3.98  sup_given_eliminated:                   2
% 27.19/3.98  comparisons_done:                       0
% 27.19/3.98  comparisons_avoided:                    231
% 27.19/3.98  
% 27.19/3.98  ------ Simplifications
% 27.19/3.98  
% 27.19/3.98  
% 27.19/3.98  sim_fw_subset_subsumed:                 360
% 27.19/3.98  sim_bw_subset_subsumed:                 115
% 27.19/3.98  sim_fw_subsumed:                        576
% 27.19/3.98  sim_bw_subsumed:                        70
% 27.19/3.98  sim_fw_subsumption_res:                 33
% 27.19/3.98  sim_bw_subsumption_res:                 1
% 27.19/3.98  sim_tautology_del:                      49
% 27.19/3.98  sim_eq_tautology_del:                   136
% 27.19/3.98  sim_eq_res_simp:                        2
% 27.19/3.98  sim_fw_demodulated:                     8
% 27.19/3.98  sim_bw_demodulated:                     180
% 27.19/3.98  sim_light_normalised:                   244
% 27.19/3.98  sim_joinable_taut:                      0
% 27.19/3.98  sim_joinable_simp:                      0
% 27.19/3.98  sim_ac_normalised:                      0
% 27.19/3.98  sim_smt_subsumption:                    0
% 27.19/3.98  
%------------------------------------------------------------------------------
