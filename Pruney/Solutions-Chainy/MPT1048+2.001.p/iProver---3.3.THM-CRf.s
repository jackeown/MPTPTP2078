%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:08:53 EST 2020

% Result     : Theorem 3.98s
% Output     : CNFRefutation 3.98s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 472 expanded)
%              Number of clauses        :   69 ( 129 expanded)
%              Number of leaves         :   15 ( 124 expanded)
%              Depth                    :   19
%              Number of atoms          :  589 (2649 expanded)
%              Number of equality atoms :  102 ( 218 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f10,f25])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
         => ( r1_relset_1(X0,X1,X3,X2)
           => r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_1(X3) )
           => ( r1_relset_1(X0,X1,X3,X2)
             => r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3)) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3))
          & r1_relset_1(X0,X1,X3,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3))
          & r1_relset_1(X0,X1,X3,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f36,plain,(
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

fof(f35,plain,
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

fof(f37,plain,
    ( ~ r1_tarski(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9))
    & r1_relset_1(sK6,sK7,sK9,sK8)
    & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
    & v1_funct_1(sK9)
    & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
    & v1_funct_1(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f21,f36,f35])).

fof(f65,plain,(
    ~ r1_tarski(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)) ),
    inference(cnf_transformation,[],[f37])).

fof(f22,plain,(
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

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f33,plain,(
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

fof(f32,plain,(
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

fof(f31,plain,(
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

fof(f34,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f30,f33,f32,f31])).

fof(f48,plain,(
    ! [X2,X0,X8,X7,X3,X1] :
      ( r2_hidden(X7,X3)
      | ~ r1_partfun1(X0,X8)
      | ~ v1_partfun1(X8,X1)
      | X7 != X8
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X8)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f68,plain,(
    ! [X2,X0,X8,X3,X1] :
      ( r2_hidden(X8,X3)
      | ~ r1_partfun1(X0,X8)
      | ~ v1_partfun1(X8,X1)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X8)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(equality_resolution,[],[f48])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
         => ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f60,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f37])).

fof(f61,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) ),
    inference(cnf_transformation,[],[f37])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(X3)
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
         => ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
           => v1_partfun1(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( v1_partfun1(X3,X0)
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( v1_partfun1(X3,X0)
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_partfun1(X3,X0)
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f4])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f56,plain,(
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
    inference(cnf_transformation,[],[f15])).

fof(f64,plain,(
    r1_relset_1(sK6,sK7,sK9,sK8) ),
    inference(cnf_transformation,[],[f37])).

fof(f62,plain,(
    v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f37])).

fof(f63,plain,(
    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) ),
    inference(cnf_transformation,[],[f37])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f11])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f3])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f23,plain,(
    ! [X1,X0,X2] :
      ( ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> sP0(X2,X0,X1,X3) )
      | ~ sP1(X1,X0,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( sP1(X1,X0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(definition_folding,[],[f13,f23,f22])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( sP1(X1,X0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f27,plain,(
    ! [X1,X0,X2] :
      ( ! [X3] :
          ( ( k5_partfun1(X0,X1,X2) = X3
            | ~ sP0(X2,X0,X1,X3) )
          & ( sP0(X2,X0,X1,X3)
            | k5_partfun1(X0,X1,X2) != X3 ) )
      | ~ sP1(X1,X0,X2) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k5_partfun1(X1,X0,X2) = X3
            | ~ sP0(X2,X1,X0,X3) )
          & ( sP0(X2,X1,X0,X3)
            | k5_partfun1(X1,X0,X2) != X3 ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f27])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X2,X1,X0,X3)
      | k5_partfun1(X1,X0,X2) != X3
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X1,X0,k5_partfun1(X1,X0,X2))
      | ~ sP1(X0,X1,X2) ) ),
    inference(equality_resolution,[],[f41])).

fof(f45,plain,(
    ! [X2,X0,X7,X3,X1] :
      ( sK5(X0,X1,X2,X7) = X7
      | ~ r2_hidden(X7,X3)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f47,plain,(
    ! [X2,X0,X7,X3,X1] :
      ( r1_partfun1(X0,sK5(X0,X1,X2,X7))
      | ~ r2_hidden(X7,X3)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK2(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_22,negated_conjecture,
    ( ~ r1_tarski(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_315,plain,
    ( ~ r2_hidden(sK2(X0,X1),X1)
    | k5_partfun1(sK6,sK7,sK9) != X1
    | k5_partfun1(sK6,sK7,sK8) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_22])).

cnf(c_316,plain,
    ( ~ r2_hidden(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),k5_partfun1(sK6,sK7,sK9)) ),
    inference(unflattening,[status(thm)],[c_315])).

cnf(c_11,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | ~ v1_partfun1(X4,X1)
    | ~ r1_partfun1(X0,X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r2_hidden(X4,X3)
    | ~ v1_funct_1(X4) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1,plain,
    ( r2_hidden(sK2(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_308,plain,
    ( r2_hidden(sK2(X0,X1),X0)
    | k5_partfun1(sK6,sK7,sK9) != X1
    | k5_partfun1(sK6,sK7,sK8) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_22])).

cnf(c_309,plain,
    ( r2_hidden(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),k5_partfun1(sK6,sK7,sK8)) ),
    inference(unflattening,[status(thm)],[c_308])).

cnf(c_11043,plain,
    ( m1_subset_1(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
    | ~ v1_funct_1(sK8) ),
    inference(resolution,[status(thm)],[c_19,c_309])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_7308,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X0,k5_partfun1(X1,X2,sK8))
    | ~ v1_funct_1(sK8) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_7471,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
    | ~ r2_hidden(X0,k5_partfun1(sK6,sK7,sK8))
    | ~ v1_funct_1(sK8) ),
    inference(instantiation,[status(thm)],[c_7308])).

cnf(c_7578,plain,
    ( m1_subset_1(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
    | ~ r2_hidden(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),k5_partfun1(sK6,sK7,sK8))
    | ~ v1_funct_1(sK8) ),
    inference(instantiation,[status(thm)],[c_7471])).

cnf(c_11396,plain,
    ( m1_subset_1(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11043,c_27,c_26,c_309,c_7578])).

cnf(c_12248,plain,
    ( ~ sP0(X0,sK6,sK7,X1)
    | ~ v1_partfun1(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),sK6)
    | ~ r1_partfun1(X0,sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)))
    | r2_hidden(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),X1)
    | ~ v1_funct_1(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9))) ),
    inference(resolution,[status(thm)],[c_11,c_11396])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
    | ~ v1_funct_1(X0)
    | v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_7285,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ r2_hidden(X2,k5_partfun1(X0,X1,sK8))
    | v1_funct_1(X2)
    | ~ v1_funct_1(sK8) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_7460,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
    | ~ r2_hidden(X0,k5_partfun1(sK6,sK7,sK8))
    | v1_funct_1(X0)
    | ~ v1_funct_1(sK8) ),
    inference(instantiation,[status(thm)],[c_7285])).

cnf(c_7575,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
    | ~ r2_hidden(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),k5_partfun1(sK6,sK7,sK8))
    | v1_funct_1(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)))
    | ~ v1_funct_1(sK8) ),
    inference(instantiation,[status(thm)],[c_7460])).

cnf(c_21,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ r2_hidden(X0,k5_partfun1(X1,X3,X2))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_7887,plain,
    ( v1_partfun1(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
    | ~ m1_subset_1(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
    | ~ r2_hidden(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),k5_partfun1(X0,X2,X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9))) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_9352,plain,
    ( v1_partfun1(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),sK6)
    | ~ m1_subset_1(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
    | ~ r2_hidden(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),k5_partfun1(sK6,sK7,sK8))
    | ~ v1_funct_1(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)))
    | ~ v1_funct_1(sK8) ),
    inference(instantiation,[status(thm)],[c_7887])).

cnf(c_6994,plain,
    ( r2_hidden(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),k5_partfun1(sK6,sK7,sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_309])).

cnf(c_6996,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_7001,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r2_hidden(X3,k5_partfun1(X1,X2,X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_8361,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) = iProver_top
    | r2_hidden(X0,k5_partfun1(sK6,sK7,sK8)) != iProver_top
    | v1_funct_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_6996,c_7001])).

cnf(c_28,plain,
    ( v1_funct_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_8982,plain,
    ( r2_hidden(X0,k5_partfun1(sK6,sK7,sK8)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8361,c_28])).

cnf(c_8983,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) = iProver_top
    | r2_hidden(X0,k5_partfun1(sK6,sK7,sK8)) != iProver_top ),
    inference(renaming,[status(thm)],[c_8982])).

cnf(c_8994,plain,
    ( m1_subset_1(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) = iProver_top ),
    inference(superposition,[status(thm)],[c_6994,c_8983])).

cnf(c_7007,plain,
    ( sP0(X0,X1,X2,X3) != iProver_top
    | v1_partfun1(X4,X1) != iProver_top
    | r1_partfun1(X0,X4) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r2_hidden(X4,X3) = iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_9390,plain,
    ( sP0(X0,sK6,sK7,X1) != iProver_top
    | v1_partfun1(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),sK6) != iProver_top
    | r1_partfun1(X0,sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9))) != iProver_top
    | r2_hidden(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),X1) = iProver_top
    | v1_funct_1(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8994,c_7007])).

cnf(c_9427,plain,
    ( ~ sP0(X0,sK6,sK7,X1)
    | ~ v1_partfun1(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),sK6)
    | ~ r1_partfun1(X0,sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)))
    | r2_hidden(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),X1)
    | ~ v1_funct_1(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_9390])).

cnf(c_12751,plain,
    ( r2_hidden(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),X1)
    | ~ r1_partfun1(X0,sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)))
    | ~ sP0(X0,sK6,sK7,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12248,c_27,c_26,c_309,c_7575,c_7578,c_9352,c_9427])).

cnf(c_12752,plain,
    ( ~ sP0(X0,sK6,sK7,X1)
    | ~ r1_partfun1(X0,sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)))
    | r2_hidden(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),X1) ),
    inference(renaming,[status(thm)],[c_12751])).

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
    inference(cnf_transformation,[],[f56])).

cnf(c_23,negated_conjecture,
    ( r1_relset_1(sK6,sK7,sK9,sK8) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_368,plain,
    ( ~ r1_partfun1(X0,X1)
    | r1_partfun1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X1)
    | sK9 != X2
    | sK8 != X0
    | sK7 != X4
    | sK6 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_23])).

cnf(c_369,plain,
    ( r1_partfun1(sK9,X0)
    | ~ r1_partfun1(sK8,X0)
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK9)
    | ~ v1_funct_1(sK8)
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_368])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_373,plain,
    ( r1_partfun1(sK9,X0)
    | ~ r1_partfun1(sK8,X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_369,c_27,c_26,c_25,c_24])).

cnf(c_12773,plain,
    ( ~ sP0(sK9,sK6,sK7,X0)
    | ~ r1_partfun1(sK8,sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)))
    | r2_hidden(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),X0)
    | ~ v1_funct_1(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)))
    | ~ v1_relat_1(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9))) ),
    inference(resolution,[status(thm)],[c_12752,c_373])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_7917,plain,
    ( ~ m1_subset_1(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
    | v1_relat_1(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9))) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_17,plain,
    ( sP1(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_4,plain,
    ( sP0(X0,X1,X2,k5_partfun1(X1,X2,X0))
    | ~ sP1(X2,X1,X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_326,plain,
    ( sP0(X0,X1,X2,k5_partfun1(X1,X2,X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X3)
    | X0 != X3
    | X1 != X4
    | X2 != X5 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_4])).

cnf(c_327,plain,
    ( sP0(X0,X1,X2,k5_partfun1(X1,X2,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(unflattening,[status(thm)],[c_326])).

cnf(c_6992,plain,
    ( sP0(X0,X1,X2,k5_partfun1(X1,X2,X0)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_327])).

cnf(c_14,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | ~ r2_hidden(X4,X3)
    | sK5(X0,X1,X2,X4) = X4 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_7004,plain,
    ( sK5(X0,X1,X2,X3) = X3
    | sP0(X0,X1,X2,X4) != iProver_top
    | r2_hidden(X3,X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_7980,plain,
    ( sK5(X0,X1,X2,X3) = X3
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r2_hidden(X3,k5_partfun1(X1,X2,X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6992,c_7004])).

cnf(c_11158,plain,
    ( sK5(sK8,sK6,sK7,X0) = X0
    | r2_hidden(X0,k5_partfun1(sK6,sK7,sK8)) != iProver_top
    | v1_funct_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_6996,c_7980])).

cnf(c_11463,plain,
    ( r2_hidden(X0,k5_partfun1(sK6,sK7,sK8)) != iProver_top
    | sK5(sK8,sK6,sK7,X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11158,c_28])).

cnf(c_11464,plain,
    ( sK5(sK8,sK6,sK7,X0) = X0
    | r2_hidden(X0,k5_partfun1(sK6,sK7,sK8)) != iProver_top ),
    inference(renaming,[status(thm)],[c_11463])).

cnf(c_11477,plain,
    ( sK5(sK8,sK6,sK7,sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9))) = sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)) ),
    inference(superposition,[status(thm)],[c_6994,c_11464])).

cnf(c_12,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | r1_partfun1(X0,sK5(X0,X1,X2,X4))
    | ~ r2_hidden(X4,X3) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_7006,plain,
    ( sP0(X0,X1,X2,X3) != iProver_top
    | r1_partfun1(X0,sK5(X0,X1,X2,X4)) = iProver_top
    | r2_hidden(X4,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_7977,plain,
    ( r1_partfun1(X0,sK5(X0,X1,X2,X3)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r2_hidden(X3,k5_partfun1(X1,X2,X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6992,c_7006])).

cnf(c_12137,plain,
    ( r1_partfun1(sK8,sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9))) = iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) != iProver_top
    | r2_hidden(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),k5_partfun1(sK6,sK7,sK8)) != iProver_top
    | v1_funct_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_11477,c_7977])).

cnf(c_12159,plain,
    ( r1_partfun1(sK8,sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
    | ~ r2_hidden(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),k5_partfun1(sK6,sK7,sK8))
    | ~ v1_funct_1(sK8) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_12137])).

cnf(c_12876,plain,
    ( ~ sP0(sK9,sK6,sK7,X0)
    | r2_hidden(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12773,c_27,c_26,c_309,c_7575,c_7578,c_7917,c_12159])).

cnf(c_12902,plain,
    ( ~ sP0(sK9,sK6,sK7,k5_partfun1(sK6,sK7,sK9)) ),
    inference(resolution,[status(thm)],[c_316,c_12876])).

cnf(c_7293,plain,
    ( sP0(sK9,X0,X1,k5_partfun1(X0,X1,sK9))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK9) ),
    inference(instantiation,[status(thm)],[c_327])).

cnf(c_7465,plain,
    ( sP0(sK9,sK6,sK7,k5_partfun1(sK6,sK7,sK9))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
    | ~ v1_funct_1(sK9) ),
    inference(instantiation,[status(thm)],[c_7293])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12902,c_7465,c_24,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:17:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.98/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.98/0.99  
% 3.98/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.98/0.99  
% 3.98/0.99  ------  iProver source info
% 3.98/0.99  
% 3.98/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.98/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.98/0.99  git: non_committed_changes: false
% 3.98/0.99  git: last_make_outside_of_git: false
% 3.98/0.99  
% 3.98/0.99  ------ 
% 3.98/0.99  ------ Parsing...
% 3.98/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.98/0.99  
% 3.98/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.98/0.99  
% 3.98/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.98/0.99  
% 3.98/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.98/0.99  ------ Proving...
% 3.98/0.99  ------ Problem Properties 
% 3.98/0.99  
% 3.98/0.99  
% 3.98/0.99  clauses                                 25
% 3.98/0.99  conjectures                             4
% 3.98/0.99  EPR                                     3
% 3.98/0.99  Horn                                    20
% 3.98/0.99  unary                                   6
% 3.98/0.99  binary                                  1
% 3.98/0.99  lits                                    75
% 3.98/0.99  lits eq                                 3
% 3.98/0.99  fd_pure                                 0
% 3.98/0.99  fd_pseudo                               0
% 3.98/0.99  fd_cond                                 0
% 3.98/0.99  fd_pseudo_cond                          1
% 3.98/0.99  AC symbols                              0
% 3.98/0.99  
% 3.98/0.99  ------ Input Options Time Limit: Unbounded
% 3.98/0.99  
% 3.98/0.99  
% 3.98/0.99  ------ 
% 3.98/0.99  Current options:
% 3.98/0.99  ------ 
% 3.98/0.99  
% 3.98/0.99  
% 3.98/0.99  
% 3.98/0.99  
% 3.98/0.99  ------ Proving...
% 3.98/0.99  
% 3.98/0.99  
% 3.98/0.99  % SZS status Theorem for theBenchmark.p
% 3.98/0.99  
% 3.98/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.98/0.99  
% 3.98/0.99  fof(f1,axiom,(
% 3.98/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.98/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.98/0.99  
% 3.98/0.99  fof(f9,plain,(
% 3.98/0.99    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 3.98/0.99    inference(unused_predicate_definition_removal,[],[f1])).
% 3.98/0.99  
% 3.98/0.99  fof(f10,plain,(
% 3.98/0.99    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 3.98/0.99    inference(ennf_transformation,[],[f9])).
% 3.98/0.99  
% 3.98/0.99  fof(f25,plain,(
% 3.98/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 3.98/0.99    introduced(choice_axiom,[])).
% 3.98/0.99  
% 3.98/0.99  fof(f26,plain,(
% 3.98/0.99    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 3.98/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f10,f25])).
% 3.98/0.99  
% 3.98/0.99  fof(f39,plain,(
% 3.98/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK2(X0,X1),X1)) )),
% 3.98/0.99    inference(cnf_transformation,[],[f26])).
% 3.98/0.99  
% 3.98/0.99  fof(f7,conjecture,(
% 3.98/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => (r1_relset_1(X0,X1,X3,X2) => r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3)))))),
% 3.98/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.98/0.99  
% 3.98/0.99  fof(f8,negated_conjecture,(
% 3.98/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => (r1_relset_1(X0,X1,X3,X2) => r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3)))))),
% 3.98/0.99    inference(negated_conjecture,[],[f7])).
% 3.98/0.99  
% 3.98/0.99  fof(f20,plain,(
% 3.98/0.99    ? [X0,X1,X2] : (? [X3] : ((~r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3)) & r1_relset_1(X0,X1,X3,X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 3.98/0.99    inference(ennf_transformation,[],[f8])).
% 3.98/0.99  
% 3.98/0.99  fof(f21,plain,(
% 3.98/0.99    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3)) & r1_relset_1(X0,X1,X3,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 3.98/0.99    inference(flattening,[],[f20])).
% 3.98/0.99  
% 3.98/0.99  fof(f36,plain,(
% 3.98/0.99    ( ! [X2,X0,X1] : (? [X3] : (~r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3)) & r1_relset_1(X0,X1,X3,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => (~r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,sK9)) & r1_relset_1(X0,X1,sK9,X2) & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(sK9))) )),
% 3.98/0.99    introduced(choice_axiom,[])).
% 3.98/0.99  
% 3.98/0.99  fof(f35,plain,(
% 3.98/0.99    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3)) & r1_relset_1(X0,X1,X3,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (? [X3] : (~r1_tarski(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,X3)) & r1_relset_1(sK6,sK7,X3,sK8) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) & v1_funct_1(X3)) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) & v1_funct_1(sK8))),
% 3.98/0.99    introduced(choice_axiom,[])).
% 3.98/0.99  
% 3.98/0.99  fof(f37,plain,(
% 3.98/0.99    (~r1_tarski(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)) & r1_relset_1(sK6,sK7,sK9,sK8) & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) & v1_funct_1(sK9)) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) & v1_funct_1(sK8)),
% 3.98/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f21,f36,f35])).
% 3.98/0.99  
% 3.98/0.99  fof(f65,plain,(
% 3.98/0.99    ~r1_tarski(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9))),
% 3.98/0.99    inference(cnf_transformation,[],[f37])).
% 3.98/0.99  
% 3.98/0.99  fof(f22,plain,(
% 3.98/0.99    ! [X2,X0,X1,X3] : (sP0(X2,X0,X1,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5))))),
% 3.98/0.99    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 3.98/0.99  
% 3.98/0.99  fof(f29,plain,(
% 3.98/0.99    ! [X2,X0,X1,X3] : ((sP0(X2,X0,X1,X3) | ? [X4] : ((! [X5] : (~r1_partfun1(X2,X5) | ~v1_partfun1(X5,X0) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5)) | ~r2_hidden(X4,X3)) & (? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | ! [X5] : (~r1_partfun1(X2,X5) | ~v1_partfun1(X5,X0) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5))) & (? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)) | ~r2_hidden(X4,X3))) | ~sP0(X2,X0,X1,X3)))),
% 3.98/0.99    inference(nnf_transformation,[],[f22])).
% 3.98/0.99  
% 3.98/0.99  fof(f30,plain,(
% 3.98/0.99    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ? [X4] : ((! [X5] : (~r1_partfun1(X0,X5) | ~v1_partfun1(X5,X1) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X5)) | ~r2_hidden(X4,X3)) & (? [X6] : (r1_partfun1(X0,X6) & v1_partfun1(X6,X1) & X4 = X6 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X6)) | r2_hidden(X4,X3)))) & (! [X7] : ((r2_hidden(X7,X3) | ! [X8] : (~r1_partfun1(X0,X8) | ~v1_partfun1(X8,X1) | X7 != X8 | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X8))) & (? [X9] : (r1_partfun1(X0,X9) & v1_partfun1(X9,X1) & X7 = X9 & m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X9)) | ~r2_hidden(X7,X3))) | ~sP0(X0,X1,X2,X3)))),
% 3.98/0.99    inference(rectify,[],[f29])).
% 3.98/0.99  
% 3.98/0.99  fof(f33,plain,(
% 3.98/0.99    ! [X7,X2,X1,X0] : (? [X9] : (r1_partfun1(X0,X9) & v1_partfun1(X9,X1) & X7 = X9 & m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X9)) => (r1_partfun1(X0,sK5(X0,X1,X2,X7)) & v1_partfun1(sK5(X0,X1,X2,X7),X1) & sK5(X0,X1,X2,X7) = X7 & m1_subset_1(sK5(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(sK5(X0,X1,X2,X7))))),
% 3.98/0.99    introduced(choice_axiom,[])).
% 3.98/0.99  
% 3.98/0.99  fof(f32,plain,(
% 3.98/0.99    ( ! [X4] : (! [X3,X2,X1,X0] : (? [X6] : (r1_partfun1(X0,X6) & v1_partfun1(X6,X1) & X4 = X6 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X6)) => (r1_partfun1(X0,sK4(X0,X1,X2,X3)) & v1_partfun1(sK4(X0,X1,X2,X3),X1) & sK4(X0,X1,X2,X3) = X4 & m1_subset_1(sK4(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(sK4(X0,X1,X2,X3))))) )),
% 3.98/0.99    introduced(choice_axiom,[])).
% 3.98/0.99  
% 3.98/0.99  fof(f31,plain,(
% 3.98/0.99    ! [X3,X2,X1,X0] : (? [X4] : ((! [X5] : (~r1_partfun1(X0,X5) | ~v1_partfun1(X5,X1) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X5)) | ~r2_hidden(X4,X3)) & (? [X6] : (r1_partfun1(X0,X6) & v1_partfun1(X6,X1) & X4 = X6 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X6)) | r2_hidden(X4,X3))) => ((! [X5] : (~r1_partfun1(X0,X5) | ~v1_partfun1(X5,X1) | sK3(X0,X1,X2,X3) != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X5)) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & (? [X6] : (r1_partfun1(X0,X6) & v1_partfun1(X6,X1) & sK3(X0,X1,X2,X3) = X6 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X6)) | r2_hidden(sK3(X0,X1,X2,X3),X3))))),
% 3.98/0.99    introduced(choice_axiom,[])).
% 3.98/0.99  
% 3.98/0.99  fof(f34,plain,(
% 3.98/0.99    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ((! [X5] : (~r1_partfun1(X0,X5) | ~v1_partfun1(X5,X1) | sK3(X0,X1,X2,X3) != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X5)) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & ((r1_partfun1(X0,sK4(X0,X1,X2,X3)) & v1_partfun1(sK4(X0,X1,X2,X3),X1) & sK3(X0,X1,X2,X3) = sK4(X0,X1,X2,X3) & m1_subset_1(sK4(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(sK4(X0,X1,X2,X3))) | r2_hidden(sK3(X0,X1,X2,X3),X3)))) & (! [X7] : ((r2_hidden(X7,X3) | ! [X8] : (~r1_partfun1(X0,X8) | ~v1_partfun1(X8,X1) | X7 != X8 | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X8))) & ((r1_partfun1(X0,sK5(X0,X1,X2,X7)) & v1_partfun1(sK5(X0,X1,X2,X7),X1) & sK5(X0,X1,X2,X7) = X7 & m1_subset_1(sK5(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(sK5(X0,X1,X2,X7))) | ~r2_hidden(X7,X3))) | ~sP0(X0,X1,X2,X3)))),
% 3.98/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f30,f33,f32,f31])).
% 3.98/0.99  
% 3.98/0.99  fof(f48,plain,(
% 3.98/0.99    ( ! [X2,X0,X8,X7,X3,X1] : (r2_hidden(X7,X3) | ~r1_partfun1(X0,X8) | ~v1_partfun1(X8,X1) | X7 != X8 | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X8) | ~sP0(X0,X1,X2,X3)) )),
% 3.98/0.99    inference(cnf_transformation,[],[f34])).
% 3.98/0.99  
% 3.98/0.99  fof(f68,plain,(
% 3.98/0.99    ( ! [X2,X0,X8,X3,X1] : (r2_hidden(X8,X3) | ~r1_partfun1(X0,X8) | ~v1_partfun1(X8,X1) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X8) | ~sP0(X0,X1,X2,X3)) )),
% 3.98/0.99    inference(equality_resolution,[],[f48])).
% 3.98/0.99  
% 3.98/0.99  fof(f5,axiom,(
% 3.98/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : (r2_hidden(X3,k5_partfun1(X0,X1,X2)) => (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3))))),
% 3.98/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.98/0.99  
% 3.98/0.99  fof(f16,plain,(
% 3.98/0.99    ! [X0,X1,X2] : (! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.98/0.99    inference(ennf_transformation,[],[f5])).
% 3.98/0.99  
% 3.98/0.99  fof(f17,plain,(
% 3.98/0.99    ! [X0,X1,X2] : (! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.98/0.99    inference(flattening,[],[f16])).
% 3.98/0.99  
% 3.98/0.99  fof(f58,plain,(
% 3.98/0.99    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.98/0.99    inference(cnf_transformation,[],[f17])).
% 3.98/0.99  
% 3.98/0.99  fof(f38,plain,(
% 3.98/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK2(X0,X1),X0)) )),
% 3.98/0.99    inference(cnf_transformation,[],[f26])).
% 3.98/0.99  
% 3.98/0.99  fof(f60,plain,(
% 3.98/0.99    v1_funct_1(sK8)),
% 3.98/0.99    inference(cnf_transformation,[],[f37])).
% 3.98/0.99  
% 3.98/0.99  fof(f61,plain,(
% 3.98/0.99    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))),
% 3.98/0.99    inference(cnf_transformation,[],[f37])).
% 3.98/0.99  
% 3.98/0.99  fof(f57,plain,(
% 3.98/0.99    ( ! [X2,X0,X3,X1] : (v1_funct_1(X3) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.98/0.99    inference(cnf_transformation,[],[f17])).
% 3.98/0.99  
% 3.98/0.99  fof(f6,axiom,(
% 3.98/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => (r2_hidden(X3,k5_partfun1(X0,X1,X2)) => v1_partfun1(X3,X0))))),
% 3.98/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.98/0.99  
% 3.98/0.99  fof(f18,plain,(
% 3.98/0.99    ! [X0,X1,X2] : (! [X3] : ((v1_partfun1(X3,X0) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.98/0.99    inference(ennf_transformation,[],[f6])).
% 3.98/0.99  
% 3.98/0.99  fof(f19,plain,(
% 3.98/0.99    ! [X0,X1,X2] : (! [X3] : (v1_partfun1(X3,X0) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.98/0.99    inference(flattening,[],[f18])).
% 3.98/0.99  
% 3.98/0.99  fof(f59,plain,(
% 3.98/0.99    ( ! [X2,X0,X3,X1] : (v1_partfun1(X3,X0) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.98/0.99    inference(cnf_transformation,[],[f19])).
% 3.98/0.99  
% 3.98/0.99  fof(f4,axiom,(
% 3.98/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ! [X4] : ((v1_funct_1(X4) & v1_relat_1(X4)) => ((r1_relset_1(X0,X1,X3,X2) & r1_partfun1(X2,X4)) => r1_partfun1(X3,X4)))))),
% 3.98/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.98/0.99  
% 3.98/0.99  fof(f14,plain,(
% 3.98/0.99    ! [X0,X1,X2] : (! [X3] : (! [X4] : ((r1_partfun1(X3,X4) | (~r1_relset_1(X0,X1,X3,X2) | ~r1_partfun1(X2,X4))) | (~v1_funct_1(X4) | ~v1_relat_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.98/0.99    inference(ennf_transformation,[],[f4])).
% 3.98/0.99  
% 3.98/0.99  fof(f15,plain,(
% 3.98/0.99    ! [X0,X1,X2] : (! [X3] : (! [X4] : (r1_partfun1(X3,X4) | ~r1_relset_1(X0,X1,X3,X2) | ~r1_partfun1(X2,X4) | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.98/0.99    inference(flattening,[],[f14])).
% 3.98/0.99  
% 3.98/0.99  fof(f56,plain,(
% 3.98/0.99    ( ! [X4,X2,X0,X3,X1] : (r1_partfun1(X3,X4) | ~r1_relset_1(X0,X1,X3,X2) | ~r1_partfun1(X2,X4) | ~v1_funct_1(X4) | ~v1_relat_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.98/0.99    inference(cnf_transformation,[],[f15])).
% 3.98/0.99  
% 3.98/0.99  fof(f64,plain,(
% 3.98/0.99    r1_relset_1(sK6,sK7,sK9,sK8)),
% 3.98/0.99    inference(cnf_transformation,[],[f37])).
% 3.98/0.99  
% 3.98/0.99  fof(f62,plain,(
% 3.98/0.99    v1_funct_1(sK9)),
% 3.98/0.99    inference(cnf_transformation,[],[f37])).
% 3.98/0.99  
% 3.98/0.99  fof(f63,plain,(
% 3.98/0.99    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))),
% 3.98/0.99    inference(cnf_transformation,[],[f37])).
% 3.98/0.99  
% 3.98/0.99  fof(f2,axiom,(
% 3.98/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.98/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.98/0.99  
% 3.98/0.99  fof(f11,plain,(
% 3.98/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.98/0.99    inference(ennf_transformation,[],[f2])).
% 3.98/0.99  
% 3.98/0.99  fof(f40,plain,(
% 3.98/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.98/0.99    inference(cnf_transformation,[],[f11])).
% 3.98/0.99  
% 3.98/0.99  fof(f3,axiom,(
% 3.98/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)))))),
% 3.98/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.98/0.99  
% 3.98/0.99  fof(f12,plain,(
% 3.98/0.99    ! [X0,X1,X2] : (! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.98/0.99    inference(ennf_transformation,[],[f3])).
% 3.98/0.99  
% 3.98/0.99  fof(f13,plain,(
% 3.98/0.99    ! [X0,X1,X2] : (! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.98/0.99    inference(flattening,[],[f12])).
% 3.98/0.99  
% 3.98/0.99  fof(f23,plain,(
% 3.98/0.99    ! [X1,X0,X2] : (! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> sP0(X2,X0,X1,X3)) | ~sP1(X1,X0,X2))),
% 3.98/0.99    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 3.98/0.99  
% 3.98/0.99  fof(f24,plain,(
% 3.98/0.99    ! [X0,X1,X2] : (sP1(X1,X0,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.98/0.99    inference(definition_folding,[],[f13,f23,f22])).
% 3.98/0.99  
% 3.98/0.99  fof(f55,plain,(
% 3.98/0.99    ( ! [X2,X0,X1] : (sP1(X1,X0,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.98/0.99    inference(cnf_transformation,[],[f24])).
% 3.98/0.99  
% 3.98/0.99  fof(f27,plain,(
% 3.98/0.99    ! [X1,X0,X2] : (! [X3] : ((k5_partfun1(X0,X1,X2) = X3 | ~sP0(X2,X0,X1,X3)) & (sP0(X2,X0,X1,X3) | k5_partfun1(X0,X1,X2) != X3)) | ~sP1(X1,X0,X2))),
% 3.98/0.99    inference(nnf_transformation,[],[f23])).
% 3.98/0.99  
% 3.98/0.99  fof(f28,plain,(
% 3.98/0.99    ! [X0,X1,X2] : (! [X3] : ((k5_partfun1(X1,X0,X2) = X3 | ~sP0(X2,X1,X0,X3)) & (sP0(X2,X1,X0,X3) | k5_partfun1(X1,X0,X2) != X3)) | ~sP1(X0,X1,X2))),
% 3.98/0.99    inference(rectify,[],[f27])).
% 3.98/0.99  
% 3.98/0.99  fof(f41,plain,(
% 3.98/0.99    ( ! [X2,X0,X3,X1] : (sP0(X2,X1,X0,X3) | k5_partfun1(X1,X0,X2) != X3 | ~sP1(X0,X1,X2)) )),
% 3.98/0.99    inference(cnf_transformation,[],[f28])).
% 3.98/0.99  
% 3.98/0.99  fof(f66,plain,(
% 3.98/0.99    ( ! [X2,X0,X1] : (sP0(X2,X1,X0,k5_partfun1(X1,X0,X2)) | ~sP1(X0,X1,X2)) )),
% 3.98/0.99    inference(equality_resolution,[],[f41])).
% 3.98/0.99  
% 3.98/0.99  fof(f45,plain,(
% 3.98/0.99    ( ! [X2,X0,X7,X3,X1] : (sK5(X0,X1,X2,X7) = X7 | ~r2_hidden(X7,X3) | ~sP0(X0,X1,X2,X3)) )),
% 3.98/0.99    inference(cnf_transformation,[],[f34])).
% 3.98/0.99  
% 3.98/0.99  fof(f47,plain,(
% 3.98/0.99    ( ! [X2,X0,X7,X3,X1] : (r1_partfun1(X0,sK5(X0,X1,X2,X7)) | ~r2_hidden(X7,X3) | ~sP0(X0,X1,X2,X3)) )),
% 3.98/0.99    inference(cnf_transformation,[],[f34])).
% 3.98/0.99  
% 3.98/0.99  cnf(c_0,plain,
% 3.98/0.99      ( ~ r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1) ),
% 3.98/0.99      inference(cnf_transformation,[],[f39]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_22,negated_conjecture,
% 3.98/0.99      ( ~ r1_tarski(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)) ),
% 3.98/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_315,plain,
% 3.98/0.99      ( ~ r2_hidden(sK2(X0,X1),X1)
% 3.98/0.99      | k5_partfun1(sK6,sK7,sK9) != X1
% 3.98/0.99      | k5_partfun1(sK6,sK7,sK8) != X0 ),
% 3.98/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_22]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_316,plain,
% 3.98/0.99      ( ~ r2_hidden(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),k5_partfun1(sK6,sK7,sK9)) ),
% 3.98/0.99      inference(unflattening,[status(thm)],[c_315]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_11,plain,
% 3.98/0.99      ( ~ sP0(X0,X1,X2,X3)
% 3.98/0.99      | ~ v1_partfun1(X4,X1)
% 3.98/0.99      | ~ r1_partfun1(X0,X4)
% 3.98/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.98/0.99      | r2_hidden(X4,X3)
% 3.98/0.99      | ~ v1_funct_1(X4) ),
% 3.98/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_19,plain,
% 3.98/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.98/0.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.98/0.99      | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
% 3.98/0.99      | ~ v1_funct_1(X0) ),
% 3.98/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_1,plain,
% 3.98/0.99      ( r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.98/0.99      inference(cnf_transformation,[],[f38]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_308,plain,
% 3.98/0.99      ( r2_hidden(sK2(X0,X1),X0)
% 3.98/0.99      | k5_partfun1(sK6,sK7,sK9) != X1
% 3.98/0.99      | k5_partfun1(sK6,sK7,sK8) != X0 ),
% 3.98/0.99      inference(resolution_lifted,[status(thm)],[c_1,c_22]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_309,plain,
% 3.98/0.99      ( r2_hidden(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),k5_partfun1(sK6,sK7,sK8)) ),
% 3.98/0.99      inference(unflattening,[status(thm)],[c_308]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_11043,plain,
% 3.98/0.99      ( m1_subset_1(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
% 3.98/0.99      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
% 3.98/0.99      | ~ v1_funct_1(sK8) ),
% 3.98/0.99      inference(resolution,[status(thm)],[c_19,c_309]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_27,negated_conjecture,
% 3.98/0.99      ( v1_funct_1(sK8) ),
% 3.98/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_26,negated_conjecture,
% 3.98/0.99      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) ),
% 3.98/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_7308,plain,
% 3.98/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.98/0.99      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.98/0.99      | ~ r2_hidden(X0,k5_partfun1(X1,X2,sK8))
% 3.98/0.99      | ~ v1_funct_1(sK8) ),
% 3.98/0.99      inference(instantiation,[status(thm)],[c_19]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_7471,plain,
% 3.98/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
% 3.98/0.99      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
% 3.98/0.99      | ~ r2_hidden(X0,k5_partfun1(sK6,sK7,sK8))
% 3.98/0.99      | ~ v1_funct_1(sK8) ),
% 3.98/0.99      inference(instantiation,[status(thm)],[c_7308]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_7578,plain,
% 3.98/0.99      ( m1_subset_1(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
% 3.98/0.99      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
% 3.98/0.99      | ~ r2_hidden(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),k5_partfun1(sK6,sK7,sK8))
% 3.98/0.99      | ~ v1_funct_1(sK8) ),
% 3.98/0.99      inference(instantiation,[status(thm)],[c_7471]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_11396,plain,
% 3.98/0.99      ( m1_subset_1(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) ),
% 3.98/0.99      inference(global_propositional_subsumption,
% 3.98/0.99                [status(thm)],
% 3.98/0.99                [c_11043,c_27,c_26,c_309,c_7578]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_12248,plain,
% 3.98/0.99      ( ~ sP0(X0,sK6,sK7,X1)
% 3.98/0.99      | ~ v1_partfun1(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),sK6)
% 3.98/0.99      | ~ r1_partfun1(X0,sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)))
% 3.98/0.99      | r2_hidden(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),X1)
% 3.98/0.99      | ~ v1_funct_1(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9))) ),
% 3.98/0.99      inference(resolution,[status(thm)],[c_11,c_11396]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_20,plain,
% 3.98/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.98/0.99      | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
% 3.98/0.99      | ~ v1_funct_1(X0)
% 3.98/0.99      | v1_funct_1(X3) ),
% 3.98/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_7285,plain,
% 3.98/0.99      ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.98/0.99      | ~ r2_hidden(X2,k5_partfun1(X0,X1,sK8))
% 3.98/0.99      | v1_funct_1(X2)
% 3.98/0.99      | ~ v1_funct_1(sK8) ),
% 3.98/0.99      inference(instantiation,[status(thm)],[c_20]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_7460,plain,
% 3.98/0.99      ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
% 3.98/0.99      | ~ r2_hidden(X0,k5_partfun1(sK6,sK7,sK8))
% 3.98/0.99      | v1_funct_1(X0)
% 3.98/0.99      | ~ v1_funct_1(sK8) ),
% 3.98/0.99      inference(instantiation,[status(thm)],[c_7285]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_7575,plain,
% 3.98/0.99      ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
% 3.98/0.99      | ~ r2_hidden(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),k5_partfun1(sK6,sK7,sK8))
% 3.98/0.99      | v1_funct_1(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)))
% 3.98/0.99      | ~ v1_funct_1(sK8) ),
% 3.98/0.99      inference(instantiation,[status(thm)],[c_7460]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_21,plain,
% 3.98/0.99      ( v1_partfun1(X0,X1)
% 3.98/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 3.98/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 3.98/0.99      | ~ r2_hidden(X0,k5_partfun1(X1,X3,X2))
% 3.98/0.99      | ~ v1_funct_1(X2)
% 3.98/0.99      | ~ v1_funct_1(X0) ),
% 3.98/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_7887,plain,
% 3.98/0.99      ( v1_partfun1(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),X0)
% 3.98/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
% 3.98/0.99      | ~ m1_subset_1(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
% 3.98/0.99      | ~ r2_hidden(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),k5_partfun1(X0,X2,X1))
% 3.98/0.99      | ~ v1_funct_1(X1)
% 3.98/0.99      | ~ v1_funct_1(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9))) ),
% 3.98/0.99      inference(instantiation,[status(thm)],[c_21]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_9352,plain,
% 3.98/0.99      ( v1_partfun1(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),sK6)
% 3.98/0.99      | ~ m1_subset_1(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
% 3.98/0.99      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
% 3.98/0.99      | ~ r2_hidden(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),k5_partfun1(sK6,sK7,sK8))
% 3.98/0.99      | ~ v1_funct_1(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)))
% 3.98/0.99      | ~ v1_funct_1(sK8) ),
% 3.98/0.99      inference(instantiation,[status(thm)],[c_7887]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_6994,plain,
% 3.98/0.99      ( r2_hidden(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),k5_partfun1(sK6,sK7,sK8)) = iProver_top ),
% 3.98/0.99      inference(predicate_to_equality,[status(thm)],[c_309]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_6996,plain,
% 3.98/0.99      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) = iProver_top ),
% 3.98/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_7001,plain,
% 3.98/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.98/0.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 3.98/0.99      | r2_hidden(X3,k5_partfun1(X1,X2,X0)) != iProver_top
% 3.98/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.98/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_8361,plain,
% 3.98/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) = iProver_top
% 3.98/0.99      | r2_hidden(X0,k5_partfun1(sK6,sK7,sK8)) != iProver_top
% 3.98/0.99      | v1_funct_1(sK8) != iProver_top ),
% 3.98/0.99      inference(superposition,[status(thm)],[c_6996,c_7001]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_28,plain,
% 3.98/0.99      ( v1_funct_1(sK8) = iProver_top ),
% 3.98/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_8982,plain,
% 3.98/0.99      ( r2_hidden(X0,k5_partfun1(sK6,sK7,sK8)) != iProver_top
% 3.98/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) = iProver_top ),
% 3.98/0.99      inference(global_propositional_subsumption,
% 3.98/0.99                [status(thm)],
% 3.98/0.99                [c_8361,c_28]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_8983,plain,
% 3.98/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) = iProver_top
% 3.98/0.99      | r2_hidden(X0,k5_partfun1(sK6,sK7,sK8)) != iProver_top ),
% 3.98/0.99      inference(renaming,[status(thm)],[c_8982]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_8994,plain,
% 3.98/0.99      ( m1_subset_1(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) = iProver_top ),
% 3.98/0.99      inference(superposition,[status(thm)],[c_6994,c_8983]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_7007,plain,
% 3.98/0.99      ( sP0(X0,X1,X2,X3) != iProver_top
% 3.98/0.99      | v1_partfun1(X4,X1) != iProver_top
% 3.98/0.99      | r1_partfun1(X0,X4) != iProver_top
% 3.98/0.99      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.98/0.99      | r2_hidden(X4,X3) = iProver_top
% 3.98/0.99      | v1_funct_1(X4) != iProver_top ),
% 3.98/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_9390,plain,
% 3.98/0.99      ( sP0(X0,sK6,sK7,X1) != iProver_top
% 3.98/0.99      | v1_partfun1(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),sK6) != iProver_top
% 3.98/0.99      | r1_partfun1(X0,sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9))) != iProver_top
% 3.98/0.99      | r2_hidden(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),X1) = iProver_top
% 3.98/0.99      | v1_funct_1(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9))) != iProver_top ),
% 3.98/0.99      inference(superposition,[status(thm)],[c_8994,c_7007]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_9427,plain,
% 3.98/0.99      ( ~ sP0(X0,sK6,sK7,X1)
% 3.98/0.99      | ~ v1_partfun1(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),sK6)
% 3.98/0.99      | ~ r1_partfun1(X0,sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)))
% 3.98/0.99      | r2_hidden(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),X1)
% 3.98/0.99      | ~ v1_funct_1(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9))) ),
% 3.98/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_9390]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_12751,plain,
% 3.98/0.99      ( r2_hidden(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),X1)
% 3.98/0.99      | ~ r1_partfun1(X0,sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)))
% 3.98/0.99      | ~ sP0(X0,sK6,sK7,X1) ),
% 3.98/0.99      inference(global_propositional_subsumption,
% 3.98/0.99                [status(thm)],
% 3.98/0.99                [c_12248,c_27,c_26,c_309,c_7575,c_7578,c_9352,c_9427]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_12752,plain,
% 3.98/0.99      ( ~ sP0(X0,sK6,sK7,X1)
% 3.98/0.99      | ~ r1_partfun1(X0,sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)))
% 3.98/0.99      | r2_hidden(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),X1) ),
% 3.98/0.99      inference(renaming,[status(thm)],[c_12751]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_18,plain,
% 3.98/0.99      ( ~ r1_relset_1(X0,X1,X2,X3)
% 3.98/0.99      | ~ r1_partfun1(X3,X4)
% 3.98/0.99      | r1_partfun1(X2,X4)
% 3.98/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.98/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.98/0.99      | ~ v1_funct_1(X3)
% 3.98/0.99      | ~ v1_funct_1(X4)
% 3.98/0.99      | ~ v1_funct_1(X2)
% 3.98/0.99      | ~ v1_relat_1(X4) ),
% 3.98/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_23,negated_conjecture,
% 3.98/0.99      ( r1_relset_1(sK6,sK7,sK9,sK8) ),
% 3.98/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_368,plain,
% 3.98/0.99      ( ~ r1_partfun1(X0,X1)
% 3.98/0.99      | r1_partfun1(X2,X1)
% 3.98/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 3.98/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 3.98/0.99      | ~ v1_funct_1(X1)
% 3.98/0.99      | ~ v1_funct_1(X2)
% 3.98/0.99      | ~ v1_funct_1(X0)
% 3.98/0.99      | ~ v1_relat_1(X1)
% 3.98/0.99      | sK9 != X2
% 3.98/0.99      | sK8 != X0
% 3.98/0.99      | sK7 != X4
% 3.98/0.99      | sK6 != X3 ),
% 3.98/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_23]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_369,plain,
% 3.98/0.99      ( r1_partfun1(sK9,X0)
% 3.98/0.99      | ~ r1_partfun1(sK8,X0)
% 3.98/0.99      | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
% 3.98/0.99      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
% 3.98/0.99      | ~ v1_funct_1(X0)
% 3.98/0.99      | ~ v1_funct_1(sK9)
% 3.98/0.99      | ~ v1_funct_1(sK8)
% 3.98/0.99      | ~ v1_relat_1(X0) ),
% 3.98/0.99      inference(unflattening,[status(thm)],[c_368]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_25,negated_conjecture,
% 3.98/0.99      ( v1_funct_1(sK9) ),
% 3.98/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_24,negated_conjecture,
% 3.98/0.99      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) ),
% 3.98/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_373,plain,
% 3.98/0.99      ( r1_partfun1(sK9,X0)
% 3.98/0.99      | ~ r1_partfun1(sK8,X0)
% 3.98/0.99      | ~ v1_funct_1(X0)
% 3.98/0.99      | ~ v1_relat_1(X0) ),
% 3.98/0.99      inference(global_propositional_subsumption,
% 3.98/0.99                [status(thm)],
% 3.98/0.99                [c_369,c_27,c_26,c_25,c_24]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_12773,plain,
% 3.98/0.99      ( ~ sP0(sK9,sK6,sK7,X0)
% 3.98/0.99      | ~ r1_partfun1(sK8,sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)))
% 3.98/0.99      | r2_hidden(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),X0)
% 3.98/0.99      | ~ v1_funct_1(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)))
% 3.98/0.99      | ~ v1_relat_1(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9))) ),
% 3.98/0.99      inference(resolution,[status(thm)],[c_12752,c_373]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_2,plain,
% 3.98/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.98/0.99      | v1_relat_1(X0) ),
% 3.98/0.99      inference(cnf_transformation,[],[f40]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_7917,plain,
% 3.98/0.99      ( ~ m1_subset_1(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
% 3.98/0.99      | v1_relat_1(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9))) ),
% 3.98/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_17,plain,
% 3.98/0.99      ( sP1(X0,X1,X2)
% 3.98/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.98/0.99      | ~ v1_funct_1(X2) ),
% 3.98/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_4,plain,
% 3.98/0.99      ( sP0(X0,X1,X2,k5_partfun1(X1,X2,X0)) | ~ sP1(X2,X1,X0) ),
% 3.98/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_326,plain,
% 3.98/0.99      ( sP0(X0,X1,X2,k5_partfun1(X1,X2,X0))
% 3.98/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.98/0.99      | ~ v1_funct_1(X3)
% 3.98/0.99      | X0 != X3
% 3.98/0.99      | X1 != X4
% 3.98/0.99      | X2 != X5 ),
% 3.98/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_4]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_327,plain,
% 3.98/0.99      ( sP0(X0,X1,X2,k5_partfun1(X1,X2,X0))
% 3.98/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.98/0.99      | ~ v1_funct_1(X0) ),
% 3.98/0.99      inference(unflattening,[status(thm)],[c_326]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_6992,plain,
% 3.98/0.99      ( sP0(X0,X1,X2,k5_partfun1(X1,X2,X0)) = iProver_top
% 3.98/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.98/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.98/0.99      inference(predicate_to_equality,[status(thm)],[c_327]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_14,plain,
% 3.98/0.99      ( ~ sP0(X0,X1,X2,X3) | ~ r2_hidden(X4,X3) | sK5(X0,X1,X2,X4) = X4 ),
% 3.98/0.99      inference(cnf_transformation,[],[f45]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_7004,plain,
% 3.98/0.99      ( sK5(X0,X1,X2,X3) = X3
% 3.98/0.99      | sP0(X0,X1,X2,X4) != iProver_top
% 3.98/0.99      | r2_hidden(X3,X4) != iProver_top ),
% 3.98/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_7980,plain,
% 3.98/0.99      ( sK5(X0,X1,X2,X3) = X3
% 3.98/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.98/0.99      | r2_hidden(X3,k5_partfun1(X1,X2,X0)) != iProver_top
% 3.98/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.98/0.99      inference(superposition,[status(thm)],[c_6992,c_7004]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_11158,plain,
% 3.98/0.99      ( sK5(sK8,sK6,sK7,X0) = X0
% 3.98/0.99      | r2_hidden(X0,k5_partfun1(sK6,sK7,sK8)) != iProver_top
% 3.98/0.99      | v1_funct_1(sK8) != iProver_top ),
% 3.98/0.99      inference(superposition,[status(thm)],[c_6996,c_7980]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_11463,plain,
% 3.98/0.99      ( r2_hidden(X0,k5_partfun1(sK6,sK7,sK8)) != iProver_top
% 3.98/0.99      | sK5(sK8,sK6,sK7,X0) = X0 ),
% 3.98/0.99      inference(global_propositional_subsumption,
% 3.98/0.99                [status(thm)],
% 3.98/0.99                [c_11158,c_28]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_11464,plain,
% 3.98/0.99      ( sK5(sK8,sK6,sK7,X0) = X0
% 3.98/0.99      | r2_hidden(X0,k5_partfun1(sK6,sK7,sK8)) != iProver_top ),
% 3.98/0.99      inference(renaming,[status(thm)],[c_11463]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_11477,plain,
% 3.98/0.99      ( sK5(sK8,sK6,sK7,sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9))) = sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)) ),
% 3.98/0.99      inference(superposition,[status(thm)],[c_6994,c_11464]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_12,plain,
% 3.98/0.99      ( ~ sP0(X0,X1,X2,X3)
% 3.98/0.99      | r1_partfun1(X0,sK5(X0,X1,X2,X4))
% 3.98/0.99      | ~ r2_hidden(X4,X3) ),
% 3.98/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_7006,plain,
% 3.98/0.99      ( sP0(X0,X1,X2,X3) != iProver_top
% 3.98/0.99      | r1_partfun1(X0,sK5(X0,X1,X2,X4)) = iProver_top
% 3.98/0.99      | r2_hidden(X4,X3) != iProver_top ),
% 3.98/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_7977,plain,
% 3.98/0.99      ( r1_partfun1(X0,sK5(X0,X1,X2,X3)) = iProver_top
% 3.98/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.98/0.99      | r2_hidden(X3,k5_partfun1(X1,X2,X0)) != iProver_top
% 3.98/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.98/0.99      inference(superposition,[status(thm)],[c_6992,c_7006]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_12137,plain,
% 3.98/0.99      ( r1_partfun1(sK8,sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9))) = iProver_top
% 3.98/0.99      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) != iProver_top
% 3.98/0.99      | r2_hidden(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),k5_partfun1(sK6,sK7,sK8)) != iProver_top
% 3.98/0.99      | v1_funct_1(sK8) != iProver_top ),
% 3.98/0.99      inference(superposition,[status(thm)],[c_11477,c_7977]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_12159,plain,
% 3.98/0.99      ( r1_partfun1(sK8,sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)))
% 3.98/0.99      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
% 3.98/0.99      | ~ r2_hidden(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),k5_partfun1(sK6,sK7,sK8))
% 3.98/0.99      | ~ v1_funct_1(sK8) ),
% 3.98/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_12137]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_12876,plain,
% 3.98/0.99      ( ~ sP0(sK9,sK6,sK7,X0)
% 3.98/0.99      | r2_hidden(sK2(k5_partfun1(sK6,sK7,sK8),k5_partfun1(sK6,sK7,sK9)),X0) ),
% 3.98/0.99      inference(global_propositional_subsumption,
% 3.98/0.99                [status(thm)],
% 3.98/0.99                [c_12773,c_27,c_26,c_309,c_7575,c_7578,c_7917,c_12159]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_12902,plain,
% 3.98/0.99      ( ~ sP0(sK9,sK6,sK7,k5_partfun1(sK6,sK7,sK9)) ),
% 3.98/0.99      inference(resolution,[status(thm)],[c_316,c_12876]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_7293,plain,
% 3.98/0.99      ( sP0(sK9,X0,X1,k5_partfun1(X0,X1,sK9))
% 3.98/0.99      | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.98/0.99      | ~ v1_funct_1(sK9) ),
% 3.98/0.99      inference(instantiation,[status(thm)],[c_327]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_7465,plain,
% 3.98/0.99      ( sP0(sK9,sK6,sK7,k5_partfun1(sK6,sK7,sK9))
% 3.98/0.99      | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
% 3.98/0.99      | ~ v1_funct_1(sK9) ),
% 3.98/0.99      inference(instantiation,[status(thm)],[c_7293]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(contradiction,plain,
% 3.98/0.99      ( $false ),
% 3.98/0.99      inference(minisat,[status(thm)],[c_12902,c_7465,c_24,c_25]) ).
% 3.98/0.99  
% 3.98/0.99  
% 3.98/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.98/0.99  
% 3.98/0.99  ------                               Statistics
% 3.98/0.99  
% 3.98/0.99  ------ Selected
% 3.98/0.99  
% 3.98/0.99  total_time:                             0.294
% 3.98/0.99  
%------------------------------------------------------------------------------
