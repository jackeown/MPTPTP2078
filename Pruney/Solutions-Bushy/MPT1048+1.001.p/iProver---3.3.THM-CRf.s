%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1048+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:46 EST 2020

% Result     : Theorem 3.07s
% Output     : CNFRefutation 3.07s
% Verified   : 
% Statistics : Number of formulae       :  127 (1178 expanded)
%              Number of clauses        :   76 ( 326 expanded)
%              Number of leaves         :   13 ( 322 expanded)
%              Depth                    :   19
%              Number of atoms          :  559 (6990 expanded)
%              Number of equality atoms :  185 ( 989 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
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
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f9,f19])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
         => ( r1_relset_1(X0,X1,X3,X2)
           => r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_1(X3) )
           => ( r1_relset_1(X0,X1,X3,X2)
             => r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3)) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3))
          & r1_relset_1(X0,X1,X3,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3))
          & r1_relset_1(X0,X1,X3,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3))
          & r1_relset_1(X0,X1,X3,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
     => ( ~ r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,sK9))
        & r1_relset_1(X0,X1,sK9,X2)
        & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(sK9) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3))
            & r1_relset_1(X0,X1,X3,X2)
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ~ r1_tarski(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,X3))
          & r1_relset_1(sK6,sK7,X3,sK8)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
          & v1_funct_1(X3) )
      & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
      & v1_funct_1(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ~ r1_tarski(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9))
    & r1_relset_1(sK6,sK7,sK9,sK8)
    & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
    & v1_funct_1(sK9)
    & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
    & v1_funct_1(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f15,f30,f29])).

fof(f56,plain,(
    ~ r1_tarski(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)) ),
    inference(cnf_transformation,[],[f31])).

fof(f17,plain,(
    ! [X1,X0,X2] :
      ( ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> sP0(X2,X0,X1,X3) )
      | ~ sP1(X1,X0,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f21,plain,(
    ! [X1,X0,X2] :
      ( ! [X3] :
          ( ( k5_partfun1(X0,X1,X2) = X3
            | ~ sP0(X2,X0,X1,X3) )
          & ( sP0(X2,X0,X1,X3)
            | k5_partfun1(X0,X1,X2) != X3 ) )
      | ~ sP1(X1,X0,X2) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k5_partfun1(X1,X0,X2) = X3
            | ~ sP0(X2,X1,X0,X3) )
          & ( sP0(X2,X1,X0,X3)
            | k5_partfun1(X1,X0,X2) != X3 ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f21])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X2,X1,X0,X3)
      | k5_partfun1(X1,X0,X2) != X3
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X1,X0,k5_partfun1(X1,X0,X2))
      | ~ sP1(X0,X1,X2) ) ),
    inference(equality_resolution,[],[f35])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f16,plain,(
    ! [X2,X0,X1,X3] :
      ( sP0(X2,X0,X1,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ? [X5] :
              ( r1_partfun1(X2,X5)
              & v1_partfun1(X5,X0)
              & X4 = X5
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_1(X5) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( sP1(X1,X0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(definition_folding,[],[f11,f17,f16])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( sP1(X1,X0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f23,plain,(
    ! [X2,X0,X1,X3] :
      ( ( sP0(X2,X0,X1,X3)
        | ? [X4] :
            ( ( ! [X5] :
                  ( ~ r1_partfun1(X2,X5)
                  | ~ v1_partfun1(X5,X0)
                  | X4 != X5
                  | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  | ~ v1_funct_1(X5) )
              | ~ r2_hidden(X4,X3) )
            & ( ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) )
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ! [X5] :
                  ( ~ r1_partfun1(X2,X5)
                  | ~ v1_partfun1(X5,X0)
                  | X4 != X5
                  | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  | ~ v1_funct_1(X5) ) )
            & ( ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) )
              | ~ r2_hidden(X4,X3) ) )
        | ~ sP0(X2,X0,X1,X3) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ! [X5] :
                  ( ~ r1_partfun1(X0,X5)
                  | ~ v1_partfun1(X5,X1)
                  | X4 != X5
                  | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  | ~ v1_funct_1(X5) )
              | ~ r2_hidden(X4,X3) )
            & ( ? [X6] :
                  ( r1_partfun1(X0,X6)
                  & v1_partfun1(X6,X1)
                  & X4 = X6
                  & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  & v1_funct_1(X6) )
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X3)
              | ! [X8] :
                  ( ~ r1_partfun1(X0,X8)
                  | ~ v1_partfun1(X8,X1)
                  | X7 != X8
                  | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  | ~ v1_funct_1(X8) ) )
            & ( ? [X9] :
                  ( r1_partfun1(X0,X9)
                  & v1_partfun1(X9,X1)
                  & X7 = X9
                  & m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  & v1_funct_1(X9) )
              | ~ r2_hidden(X7,X3) ) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f23])).

fof(f27,plain,(
    ! [X7,X2,X1,X0] :
      ( ? [X9] :
          ( r1_partfun1(X0,X9)
          & v1_partfun1(X9,X1)
          & X7 = X9
          & m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_1(X9) )
     => ( r1_partfun1(X0,sK5(X0,X1,X2,X7))
        & v1_partfun1(sK5(X0,X1,X2,X7),X1)
        & sK5(X0,X1,X2,X7) = X7
        & m1_subset_1(sK5(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(sK5(X0,X1,X2,X7)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( r1_partfun1(X0,X6)
          & v1_partfun1(X6,X1)
          & X4 = X6
          & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_1(X6) )
     => ( r1_partfun1(X0,sK4(X0,X1,X2,X3))
        & v1_partfun1(sK4(X0,X1,X2,X3),X1)
        & sK4(X0,X1,X2,X3) = X4
        & m1_subset_1(sK4(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(sK4(X0,X1,X2,X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ! [X5] :
                ( ~ r1_partfun1(X0,X5)
                | ~ v1_partfun1(X5,X1)
                | X4 != X5
                | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                | ~ v1_funct_1(X5) )
            | ~ r2_hidden(X4,X3) )
          & ( ? [X6] :
                ( r1_partfun1(X0,X6)
                & v1_partfun1(X6,X1)
                & X4 = X6
                & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                & v1_funct_1(X6) )
            | r2_hidden(X4,X3) ) )
     => ( ( ! [X5] :
              ( ~ r1_partfun1(X0,X5)
              | ~ v1_partfun1(X5,X1)
              | sK3(X0,X1,X2,X3) != X5
              | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              | ~ v1_funct_1(X5) )
          | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) )
        & ( ? [X6] :
              ( r1_partfun1(X0,X6)
              & v1_partfun1(X6,X1)
              & sK3(X0,X1,X2,X3) = X6
              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_1(X6) )
          | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ( ( ! [X5] :
                ( ~ r1_partfun1(X0,X5)
                | ~ v1_partfun1(X5,X1)
                | sK3(X0,X1,X2,X3) != X5
                | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                | ~ v1_funct_1(X5) )
            | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) )
          & ( ( r1_partfun1(X0,sK4(X0,X1,X2,X3))
              & v1_partfun1(sK4(X0,X1,X2,X3),X1)
              & sK3(X0,X1,X2,X3) = sK4(X0,X1,X2,X3)
              & m1_subset_1(sK4(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_1(sK4(X0,X1,X2,X3)) )
            | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X3)
              | ! [X8] :
                  ( ~ r1_partfun1(X0,X8)
                  | ~ v1_partfun1(X8,X1)
                  | X7 != X8
                  | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  | ~ v1_funct_1(X8) ) )
            & ( ( r1_partfun1(X0,sK5(X0,X1,X2,X7))
                & v1_partfun1(sK5(X0,X1,X2,X7),X1)
                & sK5(X0,X1,X2,X7) = X7
                & m1_subset_1(sK5(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                & v1_funct_1(sK5(X0,X1,X2,X7)) )
              | ~ r2_hidden(X7,X3) ) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f24,f27,f26,f25])).

fof(f39,plain,(
    ! [X2,X0,X7,X3,X1] :
      ( sK5(X0,X1,X2,X7) = X7
      | ~ r2_hidden(X7,X3)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f51,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f31])).

fof(f52,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) ),
    inference(cnf_transformation,[],[f31])).

fof(f41,plain,(
    ! [X2,X0,X7,X3,X1] :
      ( r1_partfun1(X0,sK5(X0,X1,X2,X7))
      | ~ r2_hidden(X7,X3)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
         => ! [X4] :
              ( ( v1_funct_1(X4)
                & v1_relat_1(X4) )
             => ( ( r1_relset_1(X0,X1,X3,X2)
                  & r1_partfun1(X2,X4) )
               => r1_partfun1(X3,X4) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( r1_partfun1(X3,X4)
              | ~ r1_relset_1(X0,X1,X3,X2)
              | ~ r1_partfun1(X2,X4)
              | ~ v1_funct_1(X4)
              | ~ v1_relat_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( r1_partfun1(X3,X4)
              | ~ r1_relset_1(X0,X1,X3,X2)
              | ~ r1_partfun1(X2,X4)
              | ~ v1_funct_1(X4)
              | ~ v1_relat_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f50,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r1_partfun1(X3,X4)
      | ~ r1_relset_1(X0,X1,X3,X2)
      | ~ r1_partfun1(X2,X4)
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f55,plain,(
    r1_relset_1(sK6,sK7,sK9,sK8) ),
    inference(cnf_transformation,[],[f31])).

fof(f53,plain,(
    v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f31])).

fof(f54,plain,(
    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) ),
    inference(cnf_transformation,[],[f31])).

fof(f37,plain,(
    ! [X2,X0,X7,X3,X1] :
      ( v1_funct_1(sK5(X0,X1,X2,X7))
      | ~ r2_hidden(X7,X3)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f38,plain,(
    ! [X2,X0,X7,X3,X1] :
      ( m1_subset_1(sK5(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r2_hidden(X7,X3)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f42,plain,(
    ! [X2,X0,X8,X7,X3,X1] :
      ( r2_hidden(X7,X3)
      | ~ r1_partfun1(X0,X8)
      | ~ v1_partfun1(X8,X1)
      | X7 != X8
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X8)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f59,plain,(
    ! [X2,X0,X8,X3,X1] :
      ( r2_hidden(X8,X3)
      | ~ r1_partfun1(X0,X8)
      | ~ v1_partfun1(X8,X1)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X8)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(equality_resolution,[],[f42])).

fof(f40,plain,(
    ! [X2,X0,X7,X3,X1] :
      ( v1_partfun1(sK5(X0,X1,X2,X7),X1)
      | ~ r2_hidden(X7,X3)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_2,plain,
    ( r2_hidden(sK2(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_19,negated_conjecture,
    ( ~ r1_tarski(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_279,plain,
    ( r2_hidden(sK2(X0,X1),X0)
    | k5_partfun1(sK6,sK7,sK9) != X1
    | k5_partfun1(sK6,sK7,sK8) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_19])).

cnf(c_280,plain,
    ( r2_hidden(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),k5_partfun1(sK6,sK7,sK8)) ),
    inference(unflattening,[status(thm)],[c_279])).

cnf(c_7691,plain,
    ( r2_hidden(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),k5_partfun1(sK6,sK7,sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_280])).

cnf(c_4,plain,
    ( sP0(X0,X1,X2,k5_partfun1(X1,X2,X0))
    | ~ sP1(X2,X1,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_17,plain,
    ( sP1(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_297,plain,
    ( sP0(X0,X1,X2,k5_partfun1(X1,X2,X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X3)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_17])).

cnf(c_298,plain,
    ( sP0(X0,X1,X2,k5_partfun1(X1,X2,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(unflattening,[status(thm)],[c_297])).

cnf(c_7689,plain,
    ( sP0(X0,X1,X2,k5_partfun1(X1,X2,X0)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_298])).

cnf(c_14,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | ~ r2_hidden(X4,X3)
    | sK5(X0,X1,X2,X4) = X4 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_7698,plain,
    ( sK5(X0,X1,X2,X3) = X3
    | sP0(X0,X1,X2,X4) != iProver_top
    | r2_hidden(X3,X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_8426,plain,
    ( sK5(X0,X1,X2,X3) = X3
    | r2_hidden(X3,k5_partfun1(X1,X2,X0)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7689,c_7698])).

cnf(c_8538,plain,
    ( sK5(sK8,sK6,sK7,sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9))) = sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9))
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) != iProver_top
    | v1_funct_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_7691,c_8426])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_25,plain,
    ( v1_funct_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_26,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_8636,plain,
    ( sK5(sK8,sK6,sK7,sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9))) = sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8538,c_25,c_26])).

cnf(c_12,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | r1_partfun1(X0,sK5(X0,X1,X2,X4))
    | ~ r2_hidden(X4,X3) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_7700,plain,
    ( sP0(X0,X1,X2,X3) != iProver_top
    | r1_partfun1(X0,sK5(X0,X1,X2,X4)) = iProver_top
    | r2_hidden(X4,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_8423,plain,
    ( r1_partfun1(X0,sK5(X0,X1,X2,X3)) = iProver_top
    | r2_hidden(X3,k5_partfun1(X1,X2,X0)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7689,c_7700])).

cnf(c_10271,plain,
    ( r1_partfun1(sK8,sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9))) = iProver_top
    | r2_hidden(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),k5_partfun1(sK6,sK7,sK8)) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) != iProver_top
    | v1_funct_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_8636,c_8423])).

cnf(c_281,plain,
    ( r2_hidden(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),k5_partfun1(sK6,sK7,sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_280])).

cnf(c_12113,plain,
    ( r1_partfun1(sK8,sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10271,c_25,c_26,c_281])).

cnf(c_18,plain,
    ( ~ r1_relset_1(X0,X1,X2,X3)
    | ~ r1_partfun1(X3,X4)
    | r1_partfun1(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X4) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_20,negated_conjecture,
    ( r1_relset_1(sK6,sK7,sK9,sK8) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_339,plain,
    ( ~ r1_partfun1(X0,X1)
    | r1_partfun1(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X1)
    | sK9 != X2
    | sK8 != X0
    | sK7 != X4
    | sK6 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_20])).

cnf(c_340,plain,
    ( r1_partfun1(sK9,X0)
    | ~ r1_partfun1(sK8,X0)
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK9)
    | ~ v1_funct_1(sK8)
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_339])).

cnf(c_22,negated_conjecture,
    ( v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_344,plain,
    ( r1_partfun1(sK9,X0)
    | ~ r1_partfun1(sK8,X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_340,c_24,c_23,c_22,c_21])).

cnf(c_7687,plain,
    ( r1_partfun1(sK9,X0) = iProver_top
    | r1_partfun1(sK8,X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_344])).

cnf(c_12118,plain,
    ( r1_partfun1(sK9,sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9))) = iProver_top
    | v1_funct_1(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9))) != iProver_top
    | v1_relat_1(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9))) != iProver_top ),
    inference(superposition,[status(thm)],[c_12113,c_7687])).

cnf(c_16,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | ~ r2_hidden(X4,X3)
    | v1_funct_1(sK5(X0,X1,X2,X4)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_7696,plain,
    ( sP0(X0,X1,X2,X3) != iProver_top
    | r2_hidden(X4,X3) != iProver_top
    | v1_funct_1(sK5(X0,X1,X2,X4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_8425,plain,
    ( r2_hidden(X0,k5_partfun1(X1,X2,X3)) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(sK5(X3,X1,X2,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7689,c_7696])).

cnf(c_10463,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) != iProver_top
    | v1_funct_1(sK5(sK8,sK6,sK7,sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)))) = iProver_top
    | v1_funct_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_7691,c_8425])).

cnf(c_10582,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) != iProver_top
    | v1_funct_1(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9))) = iProver_top
    | v1_funct_1(sK8) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10463,c_8636])).

cnf(c_15,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | ~ r2_hidden(X4,X3)
    | m1_subset_1(sK5(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_7697,plain,
    ( sP0(X0,X1,X2,X3) != iProver_top
    | r2_hidden(X4,X3) != iProver_top
    | m1_subset_1(sK5(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_8531,plain,
    ( r2_hidden(X0,k5_partfun1(X1,X2,X3)) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(sK5(X3,X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(superposition,[status(thm)],[c_7689,c_7697])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_7708,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_10853,plain,
    ( r2_hidden(X0,k5_partfun1(X1,X2,X3)) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_relat_1(sK5(X3,X1,X2,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8531,c_7708])).

cnf(c_10957,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) != iProver_top
    | v1_funct_1(sK8) != iProver_top
    | v1_relat_1(sK5(sK8,sK6,sK7,sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_7691,c_10853])).

cnf(c_11076,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) != iProver_top
    | v1_funct_1(sK8) != iProver_top
    | v1_relat_1(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10957,c_8636])).

cnf(c_10272,plain,
    ( r1_partfun1(sK9,sK5(sK8,X0,X1,X2)) = iProver_top
    | r2_hidden(X2,k5_partfun1(X0,X1,sK8)) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(sK5(sK8,X0,X1,X2)) != iProver_top
    | v1_funct_1(sK8) != iProver_top
    | v1_relat_1(sK5(sK8,X0,X1,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8423,c_7687])).

cnf(c_11940,plain,
    ( v1_funct_1(sK5(sK8,X0,X1,X2)) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | r2_hidden(X2,k5_partfun1(X0,X1,sK8)) != iProver_top
    | r1_partfun1(sK9,sK5(sK8,X0,X1,X2)) = iProver_top
    | v1_relat_1(sK5(sK8,X0,X1,X2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10272,c_25])).

cnf(c_11941,plain,
    ( r1_partfun1(sK9,sK5(sK8,X0,X1,X2)) = iProver_top
    | r2_hidden(X2,k5_partfun1(X0,X1,sK8)) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(sK5(sK8,X0,X1,X2)) != iProver_top
    | v1_relat_1(sK5(sK8,X0,X1,X2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_11940])).

cnf(c_11951,plain,
    ( r1_partfun1(sK9,sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9))) = iProver_top
    | r2_hidden(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),k5_partfun1(sK6,sK7,sK8)) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) != iProver_top
    | v1_funct_1(sK5(sK8,sK6,sK7,sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)))) != iProver_top
    | v1_relat_1(sK5(sK8,sK6,sK7,sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8636,c_11941])).

cnf(c_11952,plain,
    ( r1_partfun1(sK9,sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9))) = iProver_top
    | r2_hidden(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),k5_partfun1(sK6,sK7,sK8)) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) != iProver_top
    | v1_funct_1(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9))) != iProver_top
    | v1_relat_1(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11951,c_8636])).

cnf(c_12121,plain,
    ( r1_partfun1(sK9,sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12118,c_25,c_26,c_281,c_10582,c_11076,c_11952])).

cnf(c_10852,plain,
    ( r2_hidden(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),k5_partfun1(sK6,sK7,sK8)) != iProver_top
    | m1_subset_1(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) = iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) != iProver_top
    | v1_funct_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_8636,c_8531])).

cnf(c_12205,plain,
    ( m1_subset_1(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10852,c_25,c_26,c_281])).

cnf(c_11,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | ~ v1_partfun1(X4,X1)
    | ~ r1_partfun1(X0,X4)
    | r2_hidden(X4,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X4) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_7701,plain,
    ( sP0(X0,X1,X2,X3) != iProver_top
    | v1_partfun1(X4,X1) != iProver_top
    | r1_partfun1(X0,X4) != iProver_top
    | r2_hidden(X4,X3) = iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_12211,plain,
    ( sP0(X0,sK6,sK7,X1) != iProver_top
    | v1_partfun1(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),sK6) != iProver_top
    | r1_partfun1(X0,sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9))) != iProver_top
    | r2_hidden(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),X1) = iProver_top
    | v1_funct_1(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9))) != iProver_top ),
    inference(superposition,[status(thm)],[c_12205,c_7701])).

cnf(c_13,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | v1_partfun1(sK5(X0,X1,X2,X4),X1)
    | ~ r2_hidden(X4,X3) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_7699,plain,
    ( sP0(X0,X1,X2,X3) != iProver_top
    | v1_partfun1(sK5(X0,X1,X2,X4),X1) = iProver_top
    | r2_hidden(X4,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_8424,plain,
    ( v1_partfun1(sK5(X0,X1,X2,X3),X1) = iProver_top
    | r2_hidden(X3,k5_partfun1(X1,X2,X0)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7689,c_7699])).

cnf(c_10677,plain,
    ( v1_partfun1(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),sK6) = iProver_top
    | r2_hidden(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),k5_partfun1(sK6,sK7,sK8)) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) != iProver_top
    | v1_funct_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_8636,c_8424])).

cnf(c_13101,plain,
    ( r2_hidden(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),X1) = iProver_top
    | r1_partfun1(X0,sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9))) != iProver_top
    | sP0(X0,sK6,sK7,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12211,c_25,c_26,c_281,c_10582,c_10677])).

cnf(c_13102,plain,
    ( sP0(X0,sK6,sK7,X1) != iProver_top
    | r1_partfun1(X0,sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9))) != iProver_top
    | r2_hidden(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),X1) = iProver_top ),
    inference(renaming,[status(thm)],[c_13101])).

cnf(c_13111,plain,
    ( sP0(sK9,sK6,sK7,X0) != iProver_top
    | r2_hidden(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_12121,c_13102])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK2(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_286,plain,
    ( ~ r2_hidden(sK2(X0,X1),X1)
    | k5_partfun1(sK6,sK7,sK9) != X1
    | k5_partfun1(sK6,sK7,sK8) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_19])).

cnf(c_287,plain,
    ( ~ r2_hidden(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),k5_partfun1(sK6,sK7,sK9)) ),
    inference(unflattening,[status(thm)],[c_286])).

cnf(c_7690,plain,
    ( r2_hidden(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),k5_partfun1(sK6,sK7,sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_287])).

cnf(c_13129,plain,
    ( sP0(sK9,sK6,sK7,k5_partfun1(sK6,sK7,sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13111,c_7690])).

cnf(c_7920,plain,
    ( sP0(sK9,X0,X1,k5_partfun1(X0,X1,sK9))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK9) ),
    inference(instantiation,[status(thm)],[c_298])).

cnf(c_7999,plain,
    ( sP0(sK9,sK6,sK7,k5_partfun1(sK6,sK7,sK9))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
    | ~ v1_funct_1(sK9) ),
    inference(instantiation,[status(thm)],[c_7920])).

cnf(c_8000,plain,
    ( sP0(sK9,sK6,sK7,k5_partfun1(sK6,sK7,sK9)) = iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) != iProver_top
    | v1_funct_1(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7999])).

cnf(c_28,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_27,plain,
    ( v1_funct_1(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13129,c_8000,c_28,c_27])).


%------------------------------------------------------------------------------
