%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:08:53 EST 2020

% Result     : Theorem 3.52s
% Output     : CNFRefutation 3.52s
% Verified   : 
% Statistics : Number of formulae       :  144 (1464 expanded)
%              Number of clauses        :   91 ( 409 expanded)
%              Number of leaves         :   14 ( 397 expanded)
%              Depth                    :   21
%              Number of atoms          :  584 (8870 expanded)
%              Number of equality atoms :  212 (1273 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f9,f20])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f18,plain,(
    ! [X1,X0,X2] :
      ( ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> sP0(X2,X0,X1,X3) )
      | ~ sP1(X1,X0,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f22,plain,(
    ! [X1,X0,X2] :
      ( ! [X3] :
          ( ( k5_partfun1(X0,X1,X2) = X3
            | ~ sP0(X2,X0,X1,X3) )
          & ( sP0(X2,X0,X1,X3)
            | k5_partfun1(X0,X1,X2) != X3 ) )
      | ~ sP1(X1,X0,X2) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k5_partfun1(X1,X0,X2) = X3
            | ~ sP0(X2,X1,X0,X3) )
          & ( sP0(X2,X1,X0,X3)
            | k5_partfun1(X1,X0,X2) != X3 ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f22])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X2,X1,X0,X3)
      | k5_partfun1(X1,X0,X2) != X3
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X1,X0,k5_partfun1(X1,X0,X2))
      | ~ sP1(X0,X1,X2) ) ),
    inference(equality_resolution,[],[f37])).

fof(f17,plain,(
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

fof(f24,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f25,plain,(
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
    inference(rectify,[],[f24])).

fof(f28,plain,(
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

fof(f27,plain,(
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

fof(f26,plain,(
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

fof(f29,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f25,f28,f27,f26])).

fof(f41,plain,(
    ! [X2,X0,X7,X3,X1] :
      ( sK5(X0,X1,X2,X7) = X7
      | ~ r2_hidden(X7,X3)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
         => ( r1_relset_1(X0,X1,X3,X2)
           => r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_1(X3) )
           => ( r1_relset_1(X0,X1,X3,X2)
             => r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3)) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3))
          & r1_relset_1(X0,X1,X3,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3))
          & r1_relset_1(X0,X1,X3,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f31,plain,(
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

fof(f30,plain,
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

fof(f32,plain,
    ( ~ r1_tarski(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9))
    & r1_relset_1(sK6,sK7,sK9,sK8)
    & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
    & v1_funct_1(sK9)
    & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
    & v1_funct_1(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f16,f31,f30])).

fof(f58,plain,(
    ~ r1_tarski(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)) ),
    inference(cnf_transformation,[],[f32])).

fof(f53,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f32])).

fof(f54,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) ),
    inference(cnf_transformation,[],[f32])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f4])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( sP1(X1,X0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(definition_folding,[],[f12,f18,f17])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( sP1(X1,X0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f43,plain,(
    ! [X2,X0,X7,X3,X1] :
      ( r1_partfun1(X0,sK5(X0,X1,X2,X7))
      | ~ r2_hidden(X7,X3)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f56,plain,(
    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) ),
    inference(cnf_transformation,[],[f32])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f5])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f52,plain,(
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
    inference(cnf_transformation,[],[f14])).

fof(f55,plain,(
    v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f32])).

fof(f57,plain,(
    r1_relset_1(sK6,sK7,sK9,sK8) ),
    inference(cnf_transformation,[],[f32])).

fof(f39,plain,(
    ! [X2,X0,X7,X3,X1] :
      ( v1_funct_1(sK5(X0,X1,X2,X7))
      | ~ r2_hidden(X7,X3)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f40,plain,(
    ! [X2,X0,X7,X3,X1] :
      ( m1_subset_1(sK5(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r2_hidden(X7,X3)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f44,plain,(
    ! [X2,X0,X8,X7,X3,X1] :
      ( r2_hidden(X7,X3)
      | ~ r1_partfun1(X0,X8)
      | ~ v1_partfun1(X8,X1)
      | X7 != X8
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X8)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f61,plain,(
    ! [X2,X0,X8,X3,X1] :
      ( r2_hidden(X8,X3)
      | ~ r1_partfun1(X0,X8)
      | ~ v1_partfun1(X8,X1)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X8)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(equality_resolution,[],[f44])).

fof(f42,plain,(
    ! [X2,X0,X7,X3,X1] :
      ( v1_partfun1(sK5(X0,X1,X2,X7),X1)
      | ~ r2_hidden(X7,X3)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_1,plain,
    ( r2_hidden(sK2(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_741,plain,
    ( r2_hidden(sK2(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_5,plain,
    ( sP0(X0,X1,X2,k5_partfun1(X1,X2,X0))
    | ~ sP1(X2,X1,X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_737,plain,
    ( sP0(X0,X1,X2,k5_partfun1(X1,X2,X0)) = iProver_top
    | sP1(X2,X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_15,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | ~ r2_hidden(X4,X3)
    | sK5(X0,X1,X2,X4) = X4 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_727,plain,
    ( sK5(X0,X1,X2,X3) = X3
    | sP0(X0,X1,X2,X4) != iProver_top
    | r2_hidden(X3,X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1982,plain,
    ( sK5(X0,X1,X2,X3) = X3
    | sP1(X2,X1,X0) != iProver_top
    | r2_hidden(X3,k5_partfun1(X1,X2,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_737,c_727])).

cnf(c_2145,plain,
    ( sK5(X0,X1,X2,sK2(k5_partfun1(X1,X2,X0),X3)) = sK2(k5_partfun1(X1,X2,X0),X3)
    | sP1(X2,X1,X0) != iProver_top
    | r1_tarski(k5_partfun1(X1,X2,X0),X3) = iProver_top ),
    inference(superposition,[status(thm)],[c_741,c_1982])).

cnf(c_20,negated_conjecture,
    ( ~ r1_tarski(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_722,plain,
    ( r1_tarski(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4064,plain,
    ( sK5(sK8,sK6,sK7,sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9))) = sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9))
    | sP1(sK7,sK6,sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_2145,c_722])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_18,plain,
    ( sP1(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1001,plain,
    ( sP1(X0,X1,sK8)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_1(sK8) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1140,plain,
    ( sP1(sK7,sK6,sK8)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
    | ~ v1_funct_1(sK8) ),
    inference(instantiation,[status(thm)],[c_1001])).

cnf(c_1321,plain,
    ( sP0(sK8,sK6,sK7,k5_partfun1(sK6,sK7,sK8))
    | ~ sP1(sK7,sK6,sK8) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2041,plain,
    ( r2_hidden(sK2(k5_partfun1(sK6,sK7,sK8),X0),k5_partfun1(sK6,sK7,sK8))
    | r1_tarski(k5_partfun1(sK6,sK7,sK8),X0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2524,plain,
    ( r2_hidden(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),k5_partfun1(sK6,sK7,sK8))
    | r1_tarski(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)) ),
    inference(instantiation,[status(thm)],[c_2041])).

cnf(c_1103,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | ~ r2_hidden(sK2(X3,X4),X3)
    | sK5(X0,X1,X2,sK2(X3,X4)) = sK2(X3,X4) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1673,plain,
    ( ~ sP0(sK8,sK6,sK7,k5_partfun1(sK6,sK7,sK8))
    | ~ r2_hidden(sK2(k5_partfun1(sK6,sK7,sK8),X0),k5_partfun1(sK6,sK7,sK8))
    | sK5(sK8,sK6,sK7,sK2(k5_partfun1(sK6,sK7,sK8),X0)) = sK2(k5_partfun1(sK6,sK7,sK8),X0) ),
    inference(instantiation,[status(thm)],[c_1103])).

cnf(c_2837,plain,
    ( ~ sP0(sK8,sK6,sK7,k5_partfun1(sK6,sK7,sK8))
    | ~ r2_hidden(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),k5_partfun1(sK6,sK7,sK8))
    | sK5(sK8,sK6,sK7,sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9))) = sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)) ),
    inference(instantiation,[status(thm)],[c_1673])).

cnf(c_4067,plain,
    ( sK5(sK8,sK6,sK7,sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9))) = sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4064,c_25,c_24,c_20,c_1140,c_1321,c_2524,c_2837])).

cnf(c_13,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | r1_partfun1(X0,sK5(X0,X1,X2,X4))
    | ~ r2_hidden(X4,X3) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_729,plain,
    ( sP0(X0,X1,X2,X3) != iProver_top
    | r1_partfun1(X0,sK5(X0,X1,X2,X4)) = iProver_top
    | r2_hidden(X4,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2065,plain,
    ( sP1(X0,X1,X2) != iProver_top
    | r1_partfun1(X2,sK5(X2,X1,X0,X3)) = iProver_top
    | r2_hidden(X3,k5_partfun1(X1,X0,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_737,c_729])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_720,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_718,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_19,plain,
    ( ~ r1_relset_1(X0,X1,X2,X3)
    | ~ r1_partfun1(X3,X4)
    | r1_partfun1(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X4) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_723,plain,
    ( r1_relset_1(X0,X1,X2,X3) != iProver_top
    | r1_partfun1(X3,X4) != iProver_top
    | r1_partfun1(X2,X4) = iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_relat_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1190,plain,
    ( r1_relset_1(sK6,sK7,X0,sK8) != iProver_top
    | r1_partfun1(X0,X1) = iProver_top
    | r1_partfun1(sK8,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK8) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_718,c_723])).

cnf(c_26,plain,
    ( v1_funct_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_1774,plain,
    ( v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) != iProver_top
    | r1_partfun1(sK8,X1) != iProver_top
    | r1_partfun1(X0,X1) = iProver_top
    | r1_relset_1(sK6,sK7,X0,sK8) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1190,c_26])).

cnf(c_1775,plain,
    ( r1_relset_1(sK6,sK7,X0,sK8) != iProver_top
    | r1_partfun1(X0,X1) = iProver_top
    | r1_partfun1(sK8,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_1774])).

cnf(c_1787,plain,
    ( r1_relset_1(sK6,sK7,sK9,sK8) != iProver_top
    | r1_partfun1(sK9,X0) = iProver_top
    | r1_partfun1(sK8,X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK9) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_720,c_1775])).

cnf(c_23,negated_conjecture,
    ( v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_28,plain,
    ( v1_funct_1(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_21,negated_conjecture,
    ( r1_relset_1(sK6,sK7,sK9,sK8) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_30,plain,
    ( r1_relset_1(sK6,sK7,sK9,sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1888,plain,
    ( v1_funct_1(X0) != iProver_top
    | r1_partfun1(sK8,X0) != iProver_top
    | r1_partfun1(sK9,X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1787,c_28,c_30])).

cnf(c_1889,plain,
    ( r1_partfun1(sK9,X0) = iProver_top
    | r1_partfun1(sK8,X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_1888])).

cnf(c_2367,plain,
    ( sP1(X0,X1,sK8) != iProver_top
    | r1_partfun1(sK9,sK5(sK8,X1,X0,X2)) = iProver_top
    | r2_hidden(X2,k5_partfun1(X1,X0,sK8)) != iProver_top
    | v1_funct_1(sK5(sK8,X1,X0,X2)) != iProver_top
    | v1_relat_1(sK5(sK8,X1,X0,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2065,c_1889])).

cnf(c_17,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | ~ r2_hidden(X4,X3)
    | v1_funct_1(sK5(X0,X1,X2,X4)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_725,plain,
    ( sP0(X0,X1,X2,X3) != iProver_top
    | r2_hidden(X4,X3) != iProver_top
    | v1_funct_1(sK5(X0,X1,X2,X4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1902,plain,
    ( sP1(X0,X1,X2) != iProver_top
    | r2_hidden(X3,k5_partfun1(X1,X0,X2)) != iProver_top
    | v1_funct_1(sK5(X2,X1,X0,X3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_737,c_725])).

cnf(c_2377,plain,
    ( sP1(X0,X1,sK8) != iProver_top
    | r1_partfun1(sK9,sK5(sK8,X1,X0,X2)) = iProver_top
    | r2_hidden(X2,k5_partfun1(X1,X0,sK8)) != iProver_top
    | v1_relat_1(sK5(sK8,X1,X0,X2)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2367,c_1902])).

cnf(c_4074,plain,
    ( sP1(sK7,sK6,sK8) != iProver_top
    | r1_partfun1(sK9,sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9))) = iProver_top
    | r2_hidden(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),k5_partfun1(sK6,sK7,sK8)) != iProver_top
    | v1_relat_1(sK5(sK8,sK6,sK7,sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4067,c_2377])).

cnf(c_4079,plain,
    ( sP1(sK7,sK6,sK8) != iProver_top
    | r1_partfun1(sK9,sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9))) = iProver_top
    | r2_hidden(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),k5_partfun1(sK6,sK7,sK8)) != iProver_top
    | v1_relat_1(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4074,c_4067])).

cnf(c_3,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1328,plain,
    ( v1_relat_1(k2_zfmisc_1(sK6,sK7)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1329,plain,
    ( v1_relat_1(k2_zfmisc_1(sK6,sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1328])).

cnf(c_4071,plain,
    ( sP1(sK7,sK6,sK8) != iProver_top
    | r1_partfun1(sK8,sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9))) = iProver_top
    | r2_hidden(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),k5_partfun1(sK6,sK7,sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4067,c_2065])).

cnf(c_27,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_31,plain,
    ( r1_tarski(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1141,plain,
    ( sP1(sK7,sK6,sK8) = iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) != iProver_top
    | v1_funct_1(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1140])).

cnf(c_2525,plain,
    ( r2_hidden(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),k5_partfun1(sK6,sK7,sK8)) = iProver_top
    | r1_tarski(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2524])).

cnf(c_4276,plain,
    ( r1_partfun1(sK8,sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4071,c_26,c_27,c_31,c_1141,c_2525])).

cnf(c_4281,plain,
    ( r1_partfun1(sK9,sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9))) = iProver_top
    | v1_funct_1(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9))) != iProver_top
    | v1_relat_1(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4276,c_1889])).

cnf(c_2277,plain,
    ( sP1(X0,X1,X2) != iProver_top
    | r1_tarski(k5_partfun1(X1,X0,X2),X3) = iProver_top
    | v1_funct_1(sK5(X2,X1,X0,sK2(k5_partfun1(X1,X0,X2),X3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_741,c_1902])).

cnf(c_4073,plain,
    ( sP1(sK7,sK6,sK8) != iProver_top
    | r1_tarski(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)) = iProver_top
    | v1_funct_1(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4067,c_2277])).

cnf(c_4541,plain,
    ( r1_partfun1(sK9,sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9))) = iProver_top
    | v1_relat_1(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4281,c_26,c_27,c_31,c_1141,c_4073])).

cnf(c_16,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | m1_subset_1(sK5(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X4,X3) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_726,plain,
    ( sP0(X0,X1,X2,X3) != iProver_top
    | m1_subset_1(sK5(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r2_hidden(X4,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2555,plain,
    ( sP1(X0,X1,X2) != iProver_top
    | m1_subset_1(sK5(X2,X1,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
    | r2_hidden(X3,k5_partfun1(X1,X0,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_737,c_726])).

cnf(c_4070,plain,
    ( sP1(sK7,sK6,sK8) != iProver_top
    | m1_subset_1(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) = iProver_top
    | r2_hidden(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),k5_partfun1(sK6,sK7,sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4067,c_2555])).

cnf(c_4548,plain,
    ( m1_subset_1(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4070,c_26,c_27,c_31,c_1141,c_2525])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_740,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4553,plain,
    ( v1_relat_1(k2_zfmisc_1(sK6,sK7)) != iProver_top
    | v1_relat_1(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4548,c_740])).

cnf(c_4726,plain,
    ( r1_partfun1(sK9,sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4079,c_1329,c_4541,c_4553])).

cnf(c_12,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | ~ v1_partfun1(X4,X1)
    | ~ r1_partfun1(X0,X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r2_hidden(X4,X3)
    | ~ v1_funct_1(X4) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_730,plain,
    ( sP0(X0,X1,X2,X3) != iProver_top
    | v1_partfun1(X4,X1) != iProver_top
    | r1_partfun1(X0,X4) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r2_hidden(X4,X3) = iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4554,plain,
    ( sP0(X0,sK6,sK7,X1) != iProver_top
    | v1_partfun1(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),sK6) != iProver_top
    | r1_partfun1(X0,sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9))) != iProver_top
    | r2_hidden(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),X1) = iProver_top
    | v1_funct_1(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4548,c_730])).

cnf(c_14,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | v1_partfun1(sK5(X0,X1,X2,X4),X1)
    | ~ r2_hidden(X4,X3) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_728,plain,
    ( sP0(X0,X1,X2,X3) != iProver_top
    | v1_partfun1(sK5(X0,X1,X2,X4),X1) = iProver_top
    | r2_hidden(X4,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2057,plain,
    ( sP1(X0,X1,X2) != iProver_top
    | v1_partfun1(sK5(X2,X1,X0,X3),X1) = iProver_top
    | r2_hidden(X3,k5_partfun1(X1,X0,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_737,c_728])).

cnf(c_4072,plain,
    ( sP1(sK7,sK6,sK8) != iProver_top
    | v1_partfun1(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),sK6) = iProver_top
    | r2_hidden(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),k5_partfun1(sK6,sK7,sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4067,c_2057])).

cnf(c_6900,plain,
    ( r2_hidden(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),X1) = iProver_top
    | r1_partfun1(X0,sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9))) != iProver_top
    | sP0(X0,sK6,sK7,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4554,c_26,c_27,c_31,c_1141,c_2525,c_4072,c_4073])).

cnf(c_6901,plain,
    ( sP0(X0,sK6,sK7,X1) != iProver_top
    | r1_partfun1(X0,sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9))) != iProver_top
    | r2_hidden(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),X1) = iProver_top ),
    inference(renaming,[status(thm)],[c_6900])).

cnf(c_6910,plain,
    ( sP0(sK9,sK6,sK7,X0) != iProver_top
    | r2_hidden(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4726,c_6901])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK2(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_742,plain,
    ( r2_hidden(sK2(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_7156,plain,
    ( sP0(sK9,sK6,sK7,k5_partfun1(sK6,sK7,sK9)) != iProver_top
    | r1_tarski(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6910,c_742])).

cnf(c_1313,plain,
    ( sP0(sK9,sK6,sK7,k5_partfun1(sK6,sK7,sK9))
    | ~ sP1(sK7,sK6,sK9) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1314,plain,
    ( sP0(sK9,sK6,sK7,k5_partfun1(sK6,sK7,sK9)) = iProver_top
    | sP1(sK7,sK6,sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1313])).

cnf(c_996,plain,
    ( sP1(X0,X1,sK9)
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_1(sK9) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1137,plain,
    ( sP1(sK7,sK6,sK9)
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
    | ~ v1_funct_1(sK9) ),
    inference(instantiation,[status(thm)],[c_996])).

cnf(c_1138,plain,
    ( sP1(sK7,sK6,sK9) = iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) != iProver_top
    | v1_funct_1(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1137])).

cnf(c_29,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7156,c_1314,c_1138,c_31,c_29,c_28])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:25:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.52/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.52/1.00  
% 3.52/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.52/1.00  
% 3.52/1.00  ------  iProver source info
% 3.52/1.00  
% 3.52/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.52/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.52/1.00  git: non_committed_changes: false
% 3.52/1.00  git: last_make_outside_of_git: false
% 3.52/1.00  
% 3.52/1.00  ------ 
% 3.52/1.00  ------ Parsing...
% 3.52/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.52/1.00  
% 3.52/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.52/1.00  
% 3.52/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.52/1.00  
% 3.52/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.52/1.00  ------ Proving...
% 3.52/1.00  ------ Problem Properties 
% 3.52/1.00  
% 3.52/1.00  
% 3.52/1.00  clauses                                 26
% 3.52/1.00  conjectures                             6
% 3.52/1.00  EPR                                     3
% 3.52/1.00  Horn                                    20
% 3.52/1.00  unary                                   7
% 3.52/1.00  binary                                  3
% 3.52/1.00  lits                                    73
% 3.52/1.00  lits eq                                 3
% 3.52/1.00  fd_pure                                 0
% 3.52/1.00  fd_pseudo                               0
% 3.52/1.00  fd_cond                                 0
% 3.52/1.00  fd_pseudo_cond                          1
% 3.52/1.00  AC symbols                              0
% 3.52/1.00  
% 3.52/1.00  ------ Input Options Time Limit: Unbounded
% 3.52/1.00  
% 3.52/1.00  
% 3.52/1.00  ------ 
% 3.52/1.00  Current options:
% 3.52/1.00  ------ 
% 3.52/1.00  
% 3.52/1.00  
% 3.52/1.00  
% 3.52/1.00  
% 3.52/1.00  ------ Proving...
% 3.52/1.00  
% 3.52/1.00  
% 3.52/1.00  % SZS status Theorem for theBenchmark.p
% 3.52/1.00  
% 3.52/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.52/1.00  
% 3.52/1.00  fof(f1,axiom,(
% 3.52/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.52/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f8,plain,(
% 3.52/1.00    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 3.52/1.00    inference(unused_predicate_definition_removal,[],[f1])).
% 3.52/1.00  
% 3.52/1.00  fof(f9,plain,(
% 3.52/1.00    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 3.52/1.00    inference(ennf_transformation,[],[f8])).
% 3.52/1.00  
% 3.52/1.00  fof(f20,plain,(
% 3.52/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 3.52/1.00    introduced(choice_axiom,[])).
% 3.52/1.00  
% 3.52/1.00  fof(f21,plain,(
% 3.52/1.00    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 3.52/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f9,f20])).
% 3.52/1.00  
% 3.52/1.00  fof(f33,plain,(
% 3.52/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK2(X0,X1),X0)) )),
% 3.52/1.00    inference(cnf_transformation,[],[f21])).
% 3.52/1.00  
% 3.52/1.00  fof(f18,plain,(
% 3.52/1.00    ! [X1,X0,X2] : (! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> sP0(X2,X0,X1,X3)) | ~sP1(X1,X0,X2))),
% 3.52/1.00    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 3.52/1.00  
% 3.52/1.00  fof(f22,plain,(
% 3.52/1.00    ! [X1,X0,X2] : (! [X3] : ((k5_partfun1(X0,X1,X2) = X3 | ~sP0(X2,X0,X1,X3)) & (sP0(X2,X0,X1,X3) | k5_partfun1(X0,X1,X2) != X3)) | ~sP1(X1,X0,X2))),
% 3.52/1.00    inference(nnf_transformation,[],[f18])).
% 3.52/1.00  
% 3.52/1.00  fof(f23,plain,(
% 3.52/1.00    ! [X0,X1,X2] : (! [X3] : ((k5_partfun1(X1,X0,X2) = X3 | ~sP0(X2,X1,X0,X3)) & (sP0(X2,X1,X0,X3) | k5_partfun1(X1,X0,X2) != X3)) | ~sP1(X0,X1,X2))),
% 3.52/1.00    inference(rectify,[],[f22])).
% 3.52/1.00  
% 3.52/1.00  fof(f37,plain,(
% 3.52/1.00    ( ! [X2,X0,X3,X1] : (sP0(X2,X1,X0,X3) | k5_partfun1(X1,X0,X2) != X3 | ~sP1(X0,X1,X2)) )),
% 3.52/1.00    inference(cnf_transformation,[],[f23])).
% 3.52/1.00  
% 3.52/1.00  fof(f59,plain,(
% 3.52/1.00    ( ! [X2,X0,X1] : (sP0(X2,X1,X0,k5_partfun1(X1,X0,X2)) | ~sP1(X0,X1,X2)) )),
% 3.52/1.00    inference(equality_resolution,[],[f37])).
% 3.52/1.00  
% 3.52/1.00  fof(f17,plain,(
% 3.52/1.00    ! [X2,X0,X1,X3] : (sP0(X2,X0,X1,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5))))),
% 3.52/1.00    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 3.52/1.00  
% 3.52/1.00  fof(f24,plain,(
% 3.52/1.00    ! [X2,X0,X1,X3] : ((sP0(X2,X0,X1,X3) | ? [X4] : ((! [X5] : (~r1_partfun1(X2,X5) | ~v1_partfun1(X5,X0) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5)) | ~r2_hidden(X4,X3)) & (? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | ! [X5] : (~r1_partfun1(X2,X5) | ~v1_partfun1(X5,X0) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5))) & (? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)) | ~r2_hidden(X4,X3))) | ~sP0(X2,X0,X1,X3)))),
% 3.52/1.00    inference(nnf_transformation,[],[f17])).
% 3.52/1.00  
% 3.52/1.00  fof(f25,plain,(
% 3.52/1.00    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ? [X4] : ((! [X5] : (~r1_partfun1(X0,X5) | ~v1_partfun1(X5,X1) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X5)) | ~r2_hidden(X4,X3)) & (? [X6] : (r1_partfun1(X0,X6) & v1_partfun1(X6,X1) & X4 = X6 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X6)) | r2_hidden(X4,X3)))) & (! [X7] : ((r2_hidden(X7,X3) | ! [X8] : (~r1_partfun1(X0,X8) | ~v1_partfun1(X8,X1) | X7 != X8 | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X8))) & (? [X9] : (r1_partfun1(X0,X9) & v1_partfun1(X9,X1) & X7 = X9 & m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X9)) | ~r2_hidden(X7,X3))) | ~sP0(X0,X1,X2,X3)))),
% 3.52/1.00    inference(rectify,[],[f24])).
% 3.52/1.00  
% 3.52/1.00  fof(f28,plain,(
% 3.52/1.00    ! [X7,X2,X1,X0] : (? [X9] : (r1_partfun1(X0,X9) & v1_partfun1(X9,X1) & X7 = X9 & m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X9)) => (r1_partfun1(X0,sK5(X0,X1,X2,X7)) & v1_partfun1(sK5(X0,X1,X2,X7),X1) & sK5(X0,X1,X2,X7) = X7 & m1_subset_1(sK5(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(sK5(X0,X1,X2,X7))))),
% 3.52/1.00    introduced(choice_axiom,[])).
% 3.52/1.00  
% 3.52/1.00  fof(f27,plain,(
% 3.52/1.00    ( ! [X4] : (! [X3,X2,X1,X0] : (? [X6] : (r1_partfun1(X0,X6) & v1_partfun1(X6,X1) & X4 = X6 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X6)) => (r1_partfun1(X0,sK4(X0,X1,X2,X3)) & v1_partfun1(sK4(X0,X1,X2,X3),X1) & sK4(X0,X1,X2,X3) = X4 & m1_subset_1(sK4(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(sK4(X0,X1,X2,X3))))) )),
% 3.52/1.00    introduced(choice_axiom,[])).
% 3.52/1.00  
% 3.52/1.00  fof(f26,plain,(
% 3.52/1.00    ! [X3,X2,X1,X0] : (? [X4] : ((! [X5] : (~r1_partfun1(X0,X5) | ~v1_partfun1(X5,X1) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X5)) | ~r2_hidden(X4,X3)) & (? [X6] : (r1_partfun1(X0,X6) & v1_partfun1(X6,X1) & X4 = X6 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X6)) | r2_hidden(X4,X3))) => ((! [X5] : (~r1_partfun1(X0,X5) | ~v1_partfun1(X5,X1) | sK3(X0,X1,X2,X3) != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X5)) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & (? [X6] : (r1_partfun1(X0,X6) & v1_partfun1(X6,X1) & sK3(X0,X1,X2,X3) = X6 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X6)) | r2_hidden(sK3(X0,X1,X2,X3),X3))))),
% 3.52/1.00    introduced(choice_axiom,[])).
% 3.52/1.00  
% 3.52/1.00  fof(f29,plain,(
% 3.52/1.00    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ((! [X5] : (~r1_partfun1(X0,X5) | ~v1_partfun1(X5,X1) | sK3(X0,X1,X2,X3) != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X5)) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & ((r1_partfun1(X0,sK4(X0,X1,X2,X3)) & v1_partfun1(sK4(X0,X1,X2,X3),X1) & sK3(X0,X1,X2,X3) = sK4(X0,X1,X2,X3) & m1_subset_1(sK4(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(sK4(X0,X1,X2,X3))) | r2_hidden(sK3(X0,X1,X2,X3),X3)))) & (! [X7] : ((r2_hidden(X7,X3) | ! [X8] : (~r1_partfun1(X0,X8) | ~v1_partfun1(X8,X1) | X7 != X8 | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X8))) & ((r1_partfun1(X0,sK5(X0,X1,X2,X7)) & v1_partfun1(sK5(X0,X1,X2,X7),X1) & sK5(X0,X1,X2,X7) = X7 & m1_subset_1(sK5(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(sK5(X0,X1,X2,X7))) | ~r2_hidden(X7,X3))) | ~sP0(X0,X1,X2,X3)))),
% 3.52/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f25,f28,f27,f26])).
% 3.52/1.00  
% 3.52/1.00  fof(f41,plain,(
% 3.52/1.00    ( ! [X2,X0,X7,X3,X1] : (sK5(X0,X1,X2,X7) = X7 | ~r2_hidden(X7,X3) | ~sP0(X0,X1,X2,X3)) )),
% 3.52/1.00    inference(cnf_transformation,[],[f29])).
% 3.52/1.00  
% 3.52/1.00  fof(f6,conjecture,(
% 3.52/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => (r1_relset_1(X0,X1,X3,X2) => r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3)))))),
% 3.52/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f7,negated_conjecture,(
% 3.52/1.00    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => (r1_relset_1(X0,X1,X3,X2) => r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3)))))),
% 3.52/1.00    inference(negated_conjecture,[],[f6])).
% 3.52/1.00  
% 3.52/1.00  fof(f15,plain,(
% 3.52/1.00    ? [X0,X1,X2] : (? [X3] : ((~r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3)) & r1_relset_1(X0,X1,X3,X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 3.52/1.00    inference(ennf_transformation,[],[f7])).
% 3.52/1.00  
% 3.52/1.00  fof(f16,plain,(
% 3.52/1.00    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3)) & r1_relset_1(X0,X1,X3,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 3.52/1.00    inference(flattening,[],[f15])).
% 3.52/1.00  
% 3.52/1.00  fof(f31,plain,(
% 3.52/1.00    ( ! [X2,X0,X1] : (? [X3] : (~r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3)) & r1_relset_1(X0,X1,X3,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => (~r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,sK9)) & r1_relset_1(X0,X1,sK9,X2) & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(sK9))) )),
% 3.52/1.00    introduced(choice_axiom,[])).
% 3.52/1.00  
% 3.52/1.00  fof(f30,plain,(
% 3.52/1.00    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3)) & r1_relset_1(X0,X1,X3,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (? [X3] : (~r1_tarski(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,X3)) & r1_relset_1(sK6,sK7,X3,sK8) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) & v1_funct_1(X3)) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) & v1_funct_1(sK8))),
% 3.52/1.00    introduced(choice_axiom,[])).
% 3.52/1.00  
% 3.52/1.00  fof(f32,plain,(
% 3.52/1.00    (~r1_tarski(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)) & r1_relset_1(sK6,sK7,sK9,sK8) & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) & v1_funct_1(sK9)) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) & v1_funct_1(sK8)),
% 3.52/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f16,f31,f30])).
% 3.52/1.00  
% 3.52/1.00  fof(f58,plain,(
% 3.52/1.00    ~r1_tarski(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9))),
% 3.52/1.00    inference(cnf_transformation,[],[f32])).
% 3.52/1.00  
% 3.52/1.00  fof(f53,plain,(
% 3.52/1.00    v1_funct_1(sK8)),
% 3.52/1.00    inference(cnf_transformation,[],[f32])).
% 3.52/1.00  
% 3.52/1.00  fof(f54,plain,(
% 3.52/1.00    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))),
% 3.52/1.00    inference(cnf_transformation,[],[f32])).
% 3.52/1.00  
% 3.52/1.00  fof(f4,axiom,(
% 3.52/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)))))),
% 3.52/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f11,plain,(
% 3.52/1.00    ! [X0,X1,X2] : (! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.52/1.00    inference(ennf_transformation,[],[f4])).
% 3.52/1.00  
% 3.52/1.00  fof(f12,plain,(
% 3.52/1.00    ! [X0,X1,X2] : (! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.52/1.00    inference(flattening,[],[f11])).
% 3.52/1.00  
% 3.52/1.00  fof(f19,plain,(
% 3.52/1.00    ! [X0,X1,X2] : (sP1(X1,X0,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.52/1.00    inference(definition_folding,[],[f12,f18,f17])).
% 3.52/1.00  
% 3.52/1.00  fof(f51,plain,(
% 3.52/1.00    ( ! [X2,X0,X1] : (sP1(X1,X0,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.52/1.00    inference(cnf_transformation,[],[f19])).
% 3.52/1.00  
% 3.52/1.00  fof(f43,plain,(
% 3.52/1.00    ( ! [X2,X0,X7,X3,X1] : (r1_partfun1(X0,sK5(X0,X1,X2,X7)) | ~r2_hidden(X7,X3) | ~sP0(X0,X1,X2,X3)) )),
% 3.52/1.00    inference(cnf_transformation,[],[f29])).
% 3.52/1.00  
% 3.52/1.00  fof(f56,plain,(
% 3.52/1.00    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))),
% 3.52/1.00    inference(cnf_transformation,[],[f32])).
% 3.52/1.00  
% 3.52/1.00  fof(f5,axiom,(
% 3.52/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ! [X4] : ((v1_funct_1(X4) & v1_relat_1(X4)) => ((r1_relset_1(X0,X1,X3,X2) & r1_partfun1(X2,X4)) => r1_partfun1(X3,X4)))))),
% 3.52/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f13,plain,(
% 3.52/1.00    ! [X0,X1,X2] : (! [X3] : (! [X4] : ((r1_partfun1(X3,X4) | (~r1_relset_1(X0,X1,X3,X2) | ~r1_partfun1(X2,X4))) | (~v1_funct_1(X4) | ~v1_relat_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.52/1.00    inference(ennf_transformation,[],[f5])).
% 3.52/1.00  
% 3.52/1.00  fof(f14,plain,(
% 3.52/1.00    ! [X0,X1,X2] : (! [X3] : (! [X4] : (r1_partfun1(X3,X4) | ~r1_relset_1(X0,X1,X3,X2) | ~r1_partfun1(X2,X4) | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.52/1.00    inference(flattening,[],[f13])).
% 3.52/1.00  
% 3.52/1.00  fof(f52,plain,(
% 3.52/1.00    ( ! [X4,X2,X0,X3,X1] : (r1_partfun1(X3,X4) | ~r1_relset_1(X0,X1,X3,X2) | ~r1_partfun1(X2,X4) | ~v1_funct_1(X4) | ~v1_relat_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.52/1.00    inference(cnf_transformation,[],[f14])).
% 3.52/1.00  
% 3.52/1.00  fof(f55,plain,(
% 3.52/1.00    v1_funct_1(sK9)),
% 3.52/1.00    inference(cnf_transformation,[],[f32])).
% 3.52/1.00  
% 3.52/1.00  fof(f57,plain,(
% 3.52/1.00    r1_relset_1(sK6,sK7,sK9,sK8)),
% 3.52/1.00    inference(cnf_transformation,[],[f32])).
% 3.52/1.00  
% 3.52/1.00  fof(f39,plain,(
% 3.52/1.00    ( ! [X2,X0,X7,X3,X1] : (v1_funct_1(sK5(X0,X1,X2,X7)) | ~r2_hidden(X7,X3) | ~sP0(X0,X1,X2,X3)) )),
% 3.52/1.00    inference(cnf_transformation,[],[f29])).
% 3.52/1.00  
% 3.52/1.00  fof(f3,axiom,(
% 3.52/1.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.52/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f36,plain,(
% 3.52/1.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.52/1.00    inference(cnf_transformation,[],[f3])).
% 3.52/1.00  
% 3.52/1.00  fof(f40,plain,(
% 3.52/1.00    ( ! [X2,X0,X7,X3,X1] : (m1_subset_1(sK5(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r2_hidden(X7,X3) | ~sP0(X0,X1,X2,X3)) )),
% 3.52/1.00    inference(cnf_transformation,[],[f29])).
% 3.52/1.00  
% 3.52/1.00  fof(f2,axiom,(
% 3.52/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.52/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f10,plain,(
% 3.52/1.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.52/1.00    inference(ennf_transformation,[],[f2])).
% 3.52/1.00  
% 3.52/1.00  fof(f35,plain,(
% 3.52/1.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.52/1.00    inference(cnf_transformation,[],[f10])).
% 3.52/1.00  
% 3.52/1.00  fof(f44,plain,(
% 3.52/1.00    ( ! [X2,X0,X8,X7,X3,X1] : (r2_hidden(X7,X3) | ~r1_partfun1(X0,X8) | ~v1_partfun1(X8,X1) | X7 != X8 | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X8) | ~sP0(X0,X1,X2,X3)) )),
% 3.52/1.00    inference(cnf_transformation,[],[f29])).
% 3.52/1.00  
% 3.52/1.00  fof(f61,plain,(
% 3.52/1.00    ( ! [X2,X0,X8,X3,X1] : (r2_hidden(X8,X3) | ~r1_partfun1(X0,X8) | ~v1_partfun1(X8,X1) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X8) | ~sP0(X0,X1,X2,X3)) )),
% 3.52/1.00    inference(equality_resolution,[],[f44])).
% 3.52/1.00  
% 3.52/1.00  fof(f42,plain,(
% 3.52/1.00    ( ! [X2,X0,X7,X3,X1] : (v1_partfun1(sK5(X0,X1,X2,X7),X1) | ~r2_hidden(X7,X3) | ~sP0(X0,X1,X2,X3)) )),
% 3.52/1.00    inference(cnf_transformation,[],[f29])).
% 3.52/1.00  
% 3.52/1.00  fof(f34,plain,(
% 3.52/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK2(X0,X1),X1)) )),
% 3.52/1.00    inference(cnf_transformation,[],[f21])).
% 3.52/1.00  
% 3.52/1.00  cnf(c_1,plain,
% 3.52/1.00      ( r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.52/1.00      inference(cnf_transformation,[],[f33]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_741,plain,
% 3.52/1.00      ( r2_hidden(sK2(X0,X1),X0) = iProver_top
% 3.52/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_5,plain,
% 3.52/1.00      ( sP0(X0,X1,X2,k5_partfun1(X1,X2,X0)) | ~ sP1(X2,X1,X0) ),
% 3.52/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_737,plain,
% 3.52/1.00      ( sP0(X0,X1,X2,k5_partfun1(X1,X2,X0)) = iProver_top
% 3.52/1.00      | sP1(X2,X1,X0) != iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_15,plain,
% 3.52/1.00      ( ~ sP0(X0,X1,X2,X3) | ~ r2_hidden(X4,X3) | sK5(X0,X1,X2,X4) = X4 ),
% 3.52/1.00      inference(cnf_transformation,[],[f41]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_727,plain,
% 3.52/1.00      ( sK5(X0,X1,X2,X3) = X3
% 3.52/1.00      | sP0(X0,X1,X2,X4) != iProver_top
% 3.52/1.00      | r2_hidden(X3,X4) != iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_1982,plain,
% 3.52/1.00      ( sK5(X0,X1,X2,X3) = X3
% 3.52/1.00      | sP1(X2,X1,X0) != iProver_top
% 3.52/1.00      | r2_hidden(X3,k5_partfun1(X1,X2,X0)) != iProver_top ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_737,c_727]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_2145,plain,
% 3.52/1.00      ( sK5(X0,X1,X2,sK2(k5_partfun1(X1,X2,X0),X3)) = sK2(k5_partfun1(X1,X2,X0),X3)
% 3.52/1.00      | sP1(X2,X1,X0) != iProver_top
% 3.52/1.00      | r1_tarski(k5_partfun1(X1,X2,X0),X3) = iProver_top ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_741,c_1982]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_20,negated_conjecture,
% 3.52/1.00      ( ~ r1_tarski(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)) ),
% 3.52/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_722,plain,
% 3.52/1.00      ( r1_tarski(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)) != iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_4064,plain,
% 3.52/1.00      ( sK5(sK8,sK6,sK7,sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9))) = sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9))
% 3.52/1.00      | sP1(sK7,sK6,sK8) != iProver_top ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_2145,c_722]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_25,negated_conjecture,
% 3.52/1.00      ( v1_funct_1(sK8) ),
% 3.52/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_24,negated_conjecture,
% 3.52/1.00      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) ),
% 3.52/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_18,plain,
% 3.52/1.00      ( sP1(X0,X1,X2)
% 3.52/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.52/1.00      | ~ v1_funct_1(X2) ),
% 3.52/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_1001,plain,
% 3.52/1.00      ( sP1(X0,X1,sK8)
% 3.52/1.00      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.52/1.00      | ~ v1_funct_1(sK8) ),
% 3.52/1.00      inference(instantiation,[status(thm)],[c_18]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_1140,plain,
% 3.52/1.00      ( sP1(sK7,sK6,sK8)
% 3.52/1.00      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
% 3.52/1.00      | ~ v1_funct_1(sK8) ),
% 3.52/1.00      inference(instantiation,[status(thm)],[c_1001]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_1321,plain,
% 3.52/1.00      ( sP0(sK8,sK6,sK7,k5_partfun1(sK6,sK7,sK8)) | ~ sP1(sK7,sK6,sK8) ),
% 3.52/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_2041,plain,
% 3.52/1.00      ( r2_hidden(sK2(k5_partfun1(sK6,sK7,sK8),X0),k5_partfun1(sK6,sK7,sK8))
% 3.52/1.00      | r1_tarski(k5_partfun1(sK6,sK7,sK8),X0) ),
% 3.52/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_2524,plain,
% 3.52/1.00      ( r2_hidden(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),k5_partfun1(sK6,sK7,sK8))
% 3.52/1.00      | r1_tarski(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)) ),
% 3.52/1.00      inference(instantiation,[status(thm)],[c_2041]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_1103,plain,
% 3.52/1.00      ( ~ sP0(X0,X1,X2,X3)
% 3.52/1.00      | ~ r2_hidden(sK2(X3,X4),X3)
% 3.52/1.00      | sK5(X0,X1,X2,sK2(X3,X4)) = sK2(X3,X4) ),
% 3.52/1.00      inference(instantiation,[status(thm)],[c_15]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_1673,plain,
% 3.52/1.00      ( ~ sP0(sK8,sK6,sK7,k5_partfun1(sK6,sK7,sK8))
% 3.52/1.00      | ~ r2_hidden(sK2(k5_partfun1(sK6,sK7,sK8),X0),k5_partfun1(sK6,sK7,sK8))
% 3.52/1.00      | sK5(sK8,sK6,sK7,sK2(k5_partfun1(sK6,sK7,sK8),X0)) = sK2(k5_partfun1(sK6,sK7,sK8),X0) ),
% 3.52/1.00      inference(instantiation,[status(thm)],[c_1103]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_2837,plain,
% 3.52/1.00      ( ~ sP0(sK8,sK6,sK7,k5_partfun1(sK6,sK7,sK8))
% 3.52/1.00      | ~ r2_hidden(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),k5_partfun1(sK6,sK7,sK8))
% 3.52/1.00      | sK5(sK8,sK6,sK7,sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9))) = sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)) ),
% 3.52/1.00      inference(instantiation,[status(thm)],[c_1673]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_4067,plain,
% 3.52/1.00      ( sK5(sK8,sK6,sK7,sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9))) = sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)) ),
% 3.52/1.00      inference(global_propositional_subsumption,
% 3.52/1.00                [status(thm)],
% 3.52/1.00                [c_4064,c_25,c_24,c_20,c_1140,c_1321,c_2524,c_2837]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_13,plain,
% 3.52/1.00      ( ~ sP0(X0,X1,X2,X3)
% 3.52/1.00      | r1_partfun1(X0,sK5(X0,X1,X2,X4))
% 3.52/1.00      | ~ r2_hidden(X4,X3) ),
% 3.52/1.00      inference(cnf_transformation,[],[f43]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_729,plain,
% 3.52/1.00      ( sP0(X0,X1,X2,X3) != iProver_top
% 3.52/1.00      | r1_partfun1(X0,sK5(X0,X1,X2,X4)) = iProver_top
% 3.52/1.00      | r2_hidden(X4,X3) != iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_2065,plain,
% 3.52/1.00      ( sP1(X0,X1,X2) != iProver_top
% 3.52/1.00      | r1_partfun1(X2,sK5(X2,X1,X0,X3)) = iProver_top
% 3.52/1.00      | r2_hidden(X3,k5_partfun1(X1,X0,X2)) != iProver_top ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_737,c_729]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_22,negated_conjecture,
% 3.52/1.00      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) ),
% 3.52/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_720,plain,
% 3.52/1.00      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) = iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_718,plain,
% 3.52/1.00      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) = iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_19,plain,
% 3.52/1.00      ( ~ r1_relset_1(X0,X1,X2,X3)
% 3.52/1.00      | ~ r1_partfun1(X3,X4)
% 3.52/1.00      | r1_partfun1(X2,X4)
% 3.52/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.52/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.52/1.00      | ~ v1_funct_1(X3)
% 3.52/1.00      | ~ v1_funct_1(X4)
% 3.52/1.00      | ~ v1_funct_1(X2)
% 3.52/1.00      | ~ v1_relat_1(X4) ),
% 3.52/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_723,plain,
% 3.52/1.00      ( r1_relset_1(X0,X1,X2,X3) != iProver_top
% 3.52/1.00      | r1_partfun1(X3,X4) != iProver_top
% 3.52/1.00      | r1_partfun1(X2,X4) = iProver_top
% 3.52/1.00      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.52/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.52/1.00      | v1_funct_1(X3) != iProver_top
% 3.52/1.00      | v1_funct_1(X4) != iProver_top
% 3.52/1.00      | v1_funct_1(X2) != iProver_top
% 3.52/1.00      | v1_relat_1(X4) != iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_1190,plain,
% 3.52/1.00      ( r1_relset_1(sK6,sK7,X0,sK8) != iProver_top
% 3.52/1.00      | r1_partfun1(X0,X1) = iProver_top
% 3.52/1.00      | r1_partfun1(sK8,X1) != iProver_top
% 3.52/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) != iProver_top
% 3.52/1.00      | v1_funct_1(X0) != iProver_top
% 3.52/1.00      | v1_funct_1(X1) != iProver_top
% 3.52/1.00      | v1_funct_1(sK8) != iProver_top
% 3.52/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_718,c_723]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_26,plain,
% 3.52/1.00      ( v1_funct_1(sK8) = iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_1774,plain,
% 3.52/1.00      ( v1_funct_1(X1) != iProver_top
% 3.52/1.00      | v1_funct_1(X0) != iProver_top
% 3.52/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) != iProver_top
% 3.52/1.00      | r1_partfun1(sK8,X1) != iProver_top
% 3.52/1.00      | r1_partfun1(X0,X1) = iProver_top
% 3.52/1.00      | r1_relset_1(sK6,sK7,X0,sK8) != iProver_top
% 3.52/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.52/1.00      inference(global_propositional_subsumption,
% 3.52/1.00                [status(thm)],
% 3.52/1.00                [c_1190,c_26]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_1775,plain,
% 3.52/1.00      ( r1_relset_1(sK6,sK7,X0,sK8) != iProver_top
% 3.52/1.00      | r1_partfun1(X0,X1) = iProver_top
% 3.52/1.00      | r1_partfun1(sK8,X1) != iProver_top
% 3.52/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) != iProver_top
% 3.52/1.00      | v1_funct_1(X0) != iProver_top
% 3.52/1.00      | v1_funct_1(X1) != iProver_top
% 3.52/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.52/1.00      inference(renaming,[status(thm)],[c_1774]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_1787,plain,
% 3.52/1.00      ( r1_relset_1(sK6,sK7,sK9,sK8) != iProver_top
% 3.52/1.00      | r1_partfun1(sK9,X0) = iProver_top
% 3.52/1.00      | r1_partfun1(sK8,X0) != iProver_top
% 3.52/1.00      | v1_funct_1(X0) != iProver_top
% 3.52/1.00      | v1_funct_1(sK9) != iProver_top
% 3.52/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_720,c_1775]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_23,negated_conjecture,
% 3.52/1.00      ( v1_funct_1(sK9) ),
% 3.52/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_28,plain,
% 3.52/1.00      ( v1_funct_1(sK9) = iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_21,negated_conjecture,
% 3.52/1.00      ( r1_relset_1(sK6,sK7,sK9,sK8) ),
% 3.52/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_30,plain,
% 3.52/1.00      ( r1_relset_1(sK6,sK7,sK9,sK8) = iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_1888,plain,
% 3.52/1.00      ( v1_funct_1(X0) != iProver_top
% 3.52/1.00      | r1_partfun1(sK8,X0) != iProver_top
% 3.52/1.00      | r1_partfun1(sK9,X0) = iProver_top
% 3.52/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.52/1.00      inference(global_propositional_subsumption,
% 3.52/1.00                [status(thm)],
% 3.52/1.00                [c_1787,c_28,c_30]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_1889,plain,
% 3.52/1.00      ( r1_partfun1(sK9,X0) = iProver_top
% 3.52/1.00      | r1_partfun1(sK8,X0) != iProver_top
% 3.52/1.00      | v1_funct_1(X0) != iProver_top
% 3.52/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.52/1.00      inference(renaming,[status(thm)],[c_1888]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_2367,plain,
% 3.52/1.00      ( sP1(X0,X1,sK8) != iProver_top
% 3.52/1.00      | r1_partfun1(sK9,sK5(sK8,X1,X0,X2)) = iProver_top
% 3.52/1.00      | r2_hidden(X2,k5_partfun1(X1,X0,sK8)) != iProver_top
% 3.52/1.00      | v1_funct_1(sK5(sK8,X1,X0,X2)) != iProver_top
% 3.52/1.00      | v1_relat_1(sK5(sK8,X1,X0,X2)) != iProver_top ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_2065,c_1889]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_17,plain,
% 3.52/1.00      ( ~ sP0(X0,X1,X2,X3)
% 3.52/1.00      | ~ r2_hidden(X4,X3)
% 3.52/1.00      | v1_funct_1(sK5(X0,X1,X2,X4)) ),
% 3.52/1.00      inference(cnf_transformation,[],[f39]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_725,plain,
% 3.52/1.00      ( sP0(X0,X1,X2,X3) != iProver_top
% 3.52/1.00      | r2_hidden(X4,X3) != iProver_top
% 3.52/1.00      | v1_funct_1(sK5(X0,X1,X2,X4)) = iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_1902,plain,
% 3.52/1.00      ( sP1(X0,X1,X2) != iProver_top
% 3.52/1.00      | r2_hidden(X3,k5_partfun1(X1,X0,X2)) != iProver_top
% 3.52/1.00      | v1_funct_1(sK5(X2,X1,X0,X3)) = iProver_top ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_737,c_725]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_2377,plain,
% 3.52/1.00      ( sP1(X0,X1,sK8) != iProver_top
% 3.52/1.00      | r1_partfun1(sK9,sK5(sK8,X1,X0,X2)) = iProver_top
% 3.52/1.00      | r2_hidden(X2,k5_partfun1(X1,X0,sK8)) != iProver_top
% 3.52/1.00      | v1_relat_1(sK5(sK8,X1,X0,X2)) != iProver_top ),
% 3.52/1.00      inference(forward_subsumption_resolution,
% 3.52/1.00                [status(thm)],
% 3.52/1.00                [c_2367,c_1902]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_4074,plain,
% 3.52/1.00      ( sP1(sK7,sK6,sK8) != iProver_top
% 3.52/1.00      | r1_partfun1(sK9,sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9))) = iProver_top
% 3.52/1.00      | r2_hidden(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),k5_partfun1(sK6,sK7,sK8)) != iProver_top
% 3.52/1.00      | v1_relat_1(sK5(sK8,sK6,sK7,sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)))) != iProver_top ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_4067,c_2377]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_4079,plain,
% 3.52/1.00      ( sP1(sK7,sK6,sK8) != iProver_top
% 3.52/1.00      | r1_partfun1(sK9,sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9))) = iProver_top
% 3.52/1.00      | r2_hidden(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),k5_partfun1(sK6,sK7,sK8)) != iProver_top
% 3.52/1.00      | v1_relat_1(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9))) != iProver_top ),
% 3.52/1.00      inference(light_normalisation,[status(thm)],[c_4074,c_4067]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_3,plain,
% 3.52/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.52/1.00      inference(cnf_transformation,[],[f36]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_1328,plain,
% 3.52/1.00      ( v1_relat_1(k2_zfmisc_1(sK6,sK7)) ),
% 3.52/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_1329,plain,
% 3.52/1.00      ( v1_relat_1(k2_zfmisc_1(sK6,sK7)) = iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_1328]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_4071,plain,
% 3.52/1.00      ( sP1(sK7,sK6,sK8) != iProver_top
% 3.52/1.00      | r1_partfun1(sK8,sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9))) = iProver_top
% 3.52/1.00      | r2_hidden(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),k5_partfun1(sK6,sK7,sK8)) != iProver_top ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_4067,c_2065]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_27,plain,
% 3.52/1.00      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) = iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_31,plain,
% 3.52/1.00      ( r1_tarski(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)) != iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_1141,plain,
% 3.52/1.00      ( sP1(sK7,sK6,sK8) = iProver_top
% 3.52/1.00      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) != iProver_top
% 3.52/1.00      | v1_funct_1(sK8) != iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_1140]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_2525,plain,
% 3.52/1.00      ( r2_hidden(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),k5_partfun1(sK6,sK7,sK8)) = iProver_top
% 3.52/1.00      | r1_tarski(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)) = iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_2524]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_4276,plain,
% 3.52/1.00      ( r1_partfun1(sK8,sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9))) = iProver_top ),
% 3.52/1.00      inference(global_propositional_subsumption,
% 3.52/1.00                [status(thm)],
% 3.52/1.00                [c_4071,c_26,c_27,c_31,c_1141,c_2525]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_4281,plain,
% 3.52/1.00      ( r1_partfun1(sK9,sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9))) = iProver_top
% 3.52/1.00      | v1_funct_1(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9))) != iProver_top
% 3.52/1.00      | v1_relat_1(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9))) != iProver_top ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_4276,c_1889]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_2277,plain,
% 3.52/1.00      ( sP1(X0,X1,X2) != iProver_top
% 3.52/1.00      | r1_tarski(k5_partfun1(X1,X0,X2),X3) = iProver_top
% 3.52/1.00      | v1_funct_1(sK5(X2,X1,X0,sK2(k5_partfun1(X1,X0,X2),X3))) = iProver_top ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_741,c_1902]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_4073,plain,
% 3.52/1.00      ( sP1(sK7,sK6,sK8) != iProver_top
% 3.52/1.00      | r1_tarski(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)) = iProver_top
% 3.52/1.00      | v1_funct_1(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9))) = iProver_top ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_4067,c_2277]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_4541,plain,
% 3.52/1.00      ( r1_partfun1(sK9,sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9))) = iProver_top
% 3.52/1.00      | v1_relat_1(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9))) != iProver_top ),
% 3.52/1.00      inference(global_propositional_subsumption,
% 3.52/1.00                [status(thm)],
% 3.52/1.00                [c_4281,c_26,c_27,c_31,c_1141,c_4073]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_16,plain,
% 3.52/1.00      ( ~ sP0(X0,X1,X2,X3)
% 3.52/1.00      | m1_subset_1(sK5(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.52/1.00      | ~ r2_hidden(X4,X3) ),
% 3.52/1.00      inference(cnf_transformation,[],[f40]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_726,plain,
% 3.52/1.00      ( sP0(X0,X1,X2,X3) != iProver_top
% 3.52/1.00      | m1_subset_1(sK5(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 3.52/1.00      | r2_hidden(X4,X3) != iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_2555,plain,
% 3.52/1.00      ( sP1(X0,X1,X2) != iProver_top
% 3.52/1.00      | m1_subset_1(sK5(X2,X1,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
% 3.52/1.00      | r2_hidden(X3,k5_partfun1(X1,X0,X2)) != iProver_top ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_737,c_726]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_4070,plain,
% 3.52/1.00      ( sP1(sK7,sK6,sK8) != iProver_top
% 3.52/1.00      | m1_subset_1(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) = iProver_top
% 3.52/1.00      | r2_hidden(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),k5_partfun1(sK6,sK7,sK8)) != iProver_top ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_4067,c_2555]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_4548,plain,
% 3.52/1.00      ( m1_subset_1(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) = iProver_top ),
% 3.52/1.00      inference(global_propositional_subsumption,
% 3.52/1.00                [status(thm)],
% 3.52/1.00                [c_4070,c_26,c_27,c_31,c_1141,c_2525]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_2,plain,
% 3.52/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.52/1.00      | ~ v1_relat_1(X1)
% 3.52/1.00      | v1_relat_1(X0) ),
% 3.52/1.00      inference(cnf_transformation,[],[f35]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_740,plain,
% 3.52/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.52/1.00      | v1_relat_1(X1) != iProver_top
% 3.52/1.00      | v1_relat_1(X0) = iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_4553,plain,
% 3.52/1.00      ( v1_relat_1(k2_zfmisc_1(sK6,sK7)) != iProver_top
% 3.52/1.00      | v1_relat_1(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9))) = iProver_top ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_4548,c_740]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_4726,plain,
% 3.52/1.00      ( r1_partfun1(sK9,sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9))) = iProver_top ),
% 3.52/1.00      inference(global_propositional_subsumption,
% 3.52/1.00                [status(thm)],
% 3.52/1.00                [c_4079,c_1329,c_4541,c_4553]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_12,plain,
% 3.52/1.00      ( ~ sP0(X0,X1,X2,X3)
% 3.52/1.00      | ~ v1_partfun1(X4,X1)
% 3.52/1.00      | ~ r1_partfun1(X0,X4)
% 3.52/1.00      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.52/1.00      | r2_hidden(X4,X3)
% 3.52/1.00      | ~ v1_funct_1(X4) ),
% 3.52/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_730,plain,
% 3.52/1.00      ( sP0(X0,X1,X2,X3) != iProver_top
% 3.52/1.00      | v1_partfun1(X4,X1) != iProver_top
% 3.52/1.00      | r1_partfun1(X0,X4) != iProver_top
% 3.52/1.00      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.52/1.00      | r2_hidden(X4,X3) = iProver_top
% 3.52/1.00      | v1_funct_1(X4) != iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_4554,plain,
% 3.52/1.00      ( sP0(X0,sK6,sK7,X1) != iProver_top
% 3.52/1.00      | v1_partfun1(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),sK6) != iProver_top
% 3.52/1.00      | r1_partfun1(X0,sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9))) != iProver_top
% 3.52/1.00      | r2_hidden(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),X1) = iProver_top
% 3.52/1.00      | v1_funct_1(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9))) != iProver_top ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_4548,c_730]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_14,plain,
% 3.52/1.00      ( ~ sP0(X0,X1,X2,X3)
% 3.52/1.00      | v1_partfun1(sK5(X0,X1,X2,X4),X1)
% 3.52/1.00      | ~ r2_hidden(X4,X3) ),
% 3.52/1.00      inference(cnf_transformation,[],[f42]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_728,plain,
% 3.52/1.00      ( sP0(X0,X1,X2,X3) != iProver_top
% 3.52/1.00      | v1_partfun1(sK5(X0,X1,X2,X4),X1) = iProver_top
% 3.52/1.00      | r2_hidden(X4,X3) != iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_2057,plain,
% 3.52/1.00      ( sP1(X0,X1,X2) != iProver_top
% 3.52/1.00      | v1_partfun1(sK5(X2,X1,X0,X3),X1) = iProver_top
% 3.52/1.00      | r2_hidden(X3,k5_partfun1(X1,X0,X2)) != iProver_top ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_737,c_728]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_4072,plain,
% 3.52/1.00      ( sP1(sK7,sK6,sK8) != iProver_top
% 3.52/1.00      | v1_partfun1(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),sK6) = iProver_top
% 3.52/1.00      | r2_hidden(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),k5_partfun1(sK6,sK7,sK8)) != iProver_top ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_4067,c_2057]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_6900,plain,
% 3.52/1.00      ( r2_hidden(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),X1) = iProver_top
% 3.52/1.00      | r1_partfun1(X0,sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9))) != iProver_top
% 3.52/1.00      | sP0(X0,sK6,sK7,X1) != iProver_top ),
% 3.52/1.00      inference(global_propositional_subsumption,
% 3.52/1.00                [status(thm)],
% 3.52/1.00                [c_4554,c_26,c_27,c_31,c_1141,c_2525,c_4072,c_4073]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_6901,plain,
% 3.52/1.00      ( sP0(X0,sK6,sK7,X1) != iProver_top
% 3.52/1.00      | r1_partfun1(X0,sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9))) != iProver_top
% 3.52/1.00      | r2_hidden(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),X1) = iProver_top ),
% 3.52/1.00      inference(renaming,[status(thm)],[c_6900]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_6910,plain,
% 3.52/1.00      ( sP0(sK9,sK6,sK7,X0) != iProver_top
% 3.52/1.00      | r2_hidden(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),X0) = iProver_top ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_4726,c_6901]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_0,plain,
% 3.52/1.00      ( ~ r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1) ),
% 3.52/1.00      inference(cnf_transformation,[],[f34]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_742,plain,
% 3.52/1.00      ( r2_hidden(sK2(X0,X1),X1) != iProver_top
% 3.52/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_7156,plain,
% 3.52/1.00      ( sP0(sK9,sK6,sK7,k5_partfun1(sK6,sK7,sK9)) != iProver_top
% 3.52/1.00      | r1_tarski(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)) = iProver_top ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_6910,c_742]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_1313,plain,
% 3.52/1.00      ( sP0(sK9,sK6,sK7,k5_partfun1(sK6,sK7,sK9)) | ~ sP1(sK7,sK6,sK9) ),
% 3.52/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_1314,plain,
% 3.52/1.00      ( sP0(sK9,sK6,sK7,k5_partfun1(sK6,sK7,sK9)) = iProver_top
% 3.52/1.00      | sP1(sK7,sK6,sK9) != iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_1313]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_996,plain,
% 3.52/1.00      ( sP1(X0,X1,sK9)
% 3.52/1.00      | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.52/1.00      | ~ v1_funct_1(sK9) ),
% 3.52/1.00      inference(instantiation,[status(thm)],[c_18]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_1137,plain,
% 3.52/1.00      ( sP1(sK7,sK6,sK9)
% 3.52/1.00      | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
% 3.52/1.00      | ~ v1_funct_1(sK9) ),
% 3.52/1.00      inference(instantiation,[status(thm)],[c_996]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_1138,plain,
% 3.52/1.00      ( sP1(sK7,sK6,sK9) = iProver_top
% 3.52/1.00      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) != iProver_top
% 3.52/1.00      | v1_funct_1(sK9) != iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_1137]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_29,plain,
% 3.52/1.00      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) = iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(contradiction,plain,
% 3.52/1.00      ( $false ),
% 3.52/1.00      inference(minisat,
% 3.52/1.00                [status(thm)],
% 3.52/1.00                [c_7156,c_1314,c_1138,c_31,c_29,c_28]) ).
% 3.52/1.00  
% 3.52/1.00  
% 3.52/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.52/1.00  
% 3.52/1.00  ------                               Statistics
% 3.52/1.00  
% 3.52/1.00  ------ Selected
% 3.52/1.00  
% 3.52/1.00  total_time:                             0.271
% 3.52/1.00  
%------------------------------------------------------------------------------
