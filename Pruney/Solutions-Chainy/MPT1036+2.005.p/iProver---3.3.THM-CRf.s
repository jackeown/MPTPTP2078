%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:08:42 EST 2020

% Result     : Theorem 2.27s
% Output     : CNFRefutation 2.27s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 449 expanded)
%              Number of clauses        :   82 ( 132 expanded)
%              Number of leaves         :   15 ( 106 expanded)
%              Depth                    :   20
%              Number of atoms          :  534 (3110 expanded)
%              Number of equality atoms :  160 ( 651 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
           => ( r1_partfun1(X0,X1)
            <=> ! [X2] :
                  ( r2_hidden(X2,k1_relat_1(X0))
                 => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_partfun1(X0,X1)
          <=> ! [X2] :
                ( k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
                | ~ r2_hidden(X2,k1_relat_1(X0)) ) )
          | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_partfun1(X0,X1)
          <=> ! [X2] :
                ( k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
                | ~ r2_hidden(X2,k1_relat_1(X0)) ) )
          | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_partfun1(X0,X1)
              | ? [X2] :
                  ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
                  & r2_hidden(X2,k1_relat_1(X0)) ) )
            & ( ! [X2] :
                  ( k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
                  | ~ r2_hidden(X2,k1_relat_1(X0)) )
              | ~ r1_partfun1(X0,X1) ) )
          | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_partfun1(X0,X1)
              | ? [X2] :
                  ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
                  & r2_hidden(X2,k1_relat_1(X0)) ) )
            & ( ! [X3] :
                  ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                  | ~ r2_hidden(X3,k1_relat_1(X0)) )
              | ~ r1_partfun1(X0,X1) ) )
          | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f20])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1))
        & r2_hidden(sK0(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_partfun1(X0,X1)
              | ( k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1))
                & r2_hidden(sK0(X0,X1),k1_relat_1(X0)) ) )
            & ( ! [X3] :
                  ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                  | ~ r2_hidden(X3,k1_relat_1(X0)) )
              | ~ r1_partfun1(X0,X1) ) )
          | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).

fof(f35,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ r1_partfun1(X0,X1)
      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
         => ( r1_partfun1(X1,X2)
          <=> ! [X3] :
                ( r2_hidden(X3,k1_relset_1(X0,X0,X1))
               => k1_funct_1(X1,X3) = k1_funct_1(X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_2(X2,X0,X0)
              & v1_funct_1(X2) )
           => ( r1_partfun1(X1,X2)
            <=> ! [X3] :
                  ( r2_hidden(X3,k1_relset_1(X0,X0,X1))
                 => k1_funct_1(X1,X3) = k1_funct_1(X2,X3) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_partfun1(X1,X2)
          <~> ! [X3] :
                ( k1_funct_1(X1,X3) = k1_funct_1(X2,X3)
                | ~ r2_hidden(X3,k1_relset_1(X0,X0,X1)) ) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_partfun1(X1,X2)
          <~> ! [X3] :
                ( k1_funct_1(X1,X3) = k1_funct_1(X2,X3)
                | ~ r2_hidden(X3,k1_relset_1(X0,X0,X1)) ) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f24,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( k1_funct_1(X1,X3) != k1_funct_1(X2,X3)
                & r2_hidden(X3,k1_relset_1(X0,X0,X1)) )
            | ~ r1_partfun1(X1,X2) )
          & ( ! [X3] :
                ( k1_funct_1(X1,X3) = k1_funct_1(X2,X3)
                | ~ r2_hidden(X3,k1_relset_1(X0,X0,X1)) )
            | r1_partfun1(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_1(X1) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( k1_funct_1(X1,X3) != k1_funct_1(X2,X3)
                & r2_hidden(X3,k1_relset_1(X0,X0,X1)) )
            | ~ r1_partfun1(X1,X2) )
          & ( ! [X3] :
                ( k1_funct_1(X1,X3) = k1_funct_1(X2,X3)
                | ~ r2_hidden(X3,k1_relset_1(X0,X0,X1)) )
            | r1_partfun1(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( k1_funct_1(X1,X3) != k1_funct_1(X2,X3)
                & r2_hidden(X3,k1_relset_1(X0,X0,X1)) )
            | ~ r1_partfun1(X1,X2) )
          & ( ! [X4] :
                ( k1_funct_1(X1,X4) = k1_funct_1(X2,X4)
                | ~ r2_hidden(X4,k1_relset_1(X0,X0,X1)) )
            | r1_partfun1(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_1(X1) ) ),
    inference(rectify,[],[f25])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( k1_funct_1(X1,X3) != k1_funct_1(X2,X3)
          & r2_hidden(X3,k1_relset_1(X0,X0,X1)) )
     => ( k1_funct_1(X1,sK4) != k1_funct_1(X2,sK4)
        & r2_hidden(sK4,k1_relset_1(X0,X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( k1_funct_1(X1,X3) != k1_funct_1(X2,X3)
                & r2_hidden(X3,k1_relset_1(X0,X0,X1)) )
            | ~ r1_partfun1(X1,X2) )
          & ( ! [X4] :
                ( k1_funct_1(X1,X4) = k1_funct_1(X2,X4)
                | ~ r2_hidden(X4,k1_relset_1(X0,X0,X1)) )
            | r1_partfun1(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
     => ( ( ? [X3] :
              ( k1_funct_1(sK3,X3) != k1_funct_1(X1,X3)
              & r2_hidden(X3,k1_relset_1(X0,X0,X1)) )
          | ~ r1_partfun1(X1,sK3) )
        & ( ! [X4] :
              ( k1_funct_1(sK3,X4) = k1_funct_1(X1,X4)
              | ~ r2_hidden(X4,k1_relset_1(X0,X0,X1)) )
          | r1_partfun1(X1,sK3) )
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(sK3,X0,X0)
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ? [X3] :
                  ( k1_funct_1(X1,X3) != k1_funct_1(X2,X3)
                  & r2_hidden(X3,k1_relset_1(X0,X0,X1)) )
              | ~ r1_partfun1(X1,X2) )
            & ( ! [X4] :
                  ( k1_funct_1(X1,X4) = k1_funct_1(X2,X4)
                  | ~ r2_hidden(X4,k1_relset_1(X0,X0,X1)) )
              | r1_partfun1(X1,X2) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_1(X1) )
   => ( ? [X2] :
          ( ( ? [X3] :
                ( k1_funct_1(sK2,X3) != k1_funct_1(X2,X3)
                & r2_hidden(X3,k1_relset_1(sK1,sK1,sK2)) )
            | ~ r1_partfun1(sK2,X2) )
          & ( ! [X4] :
                ( k1_funct_1(sK2,X4) = k1_funct_1(X2,X4)
                | ~ r2_hidden(X4,k1_relset_1(sK1,sK1,sK2)) )
            | r1_partfun1(sK2,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
          & v1_funct_2(X2,sK1,sK1)
          & v1_funct_1(X2) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ( ( k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4)
        & r2_hidden(sK4,k1_relset_1(sK1,sK1,sK2)) )
      | ~ r1_partfun1(sK2,sK3) )
    & ( ! [X4] :
          ( k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)
          | ~ r2_hidden(X4,k1_relset_1(sK1,sK1,sK2)) )
      | r1_partfun1(sK2,sK3) )
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    & v1_funct_2(sK3,sK1,sK1)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f26,f29,f28,f27])).

fof(f43,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f30])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f42,plain,(
    v1_funct_2(sK3,sK1,sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f41,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f30])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_partfun1(X0,X1)
      | r2_hidden(sK0(X0,X1),k1_relat_1(X0))
      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

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

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f40,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f30])).

fof(f44,plain,(
    ! [X4] :
      ( k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)
      | ~ r2_hidden(X4,k1_relset_1(sK1,sK1,sK2))
      | r1_partfun1(sK2,sK3) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f45,plain,
    ( r2_hidden(sK4,k1_relset_1(sK1,sK1,sK2))
    | ~ r1_partfun1(sK2,sK3) ),
    inference(cnf_transformation,[],[f30])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_partfun1(X0,X1)
      | k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1))
      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f46,plain,
    ( k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4)
    | ~ r1_partfun1(sK2,sK3) ),
    inference(cnf_transformation,[],[f30])).

fof(f39,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r1_partfun1(X1,X2)
    | ~ r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X2,X0) = k1_funct_1(X1,X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_244,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r1_partfun1(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X1,X0) = k1_funct_1(X2,X0)
    | k1_relat_1(X2) != X4
    | k1_relat_1(X1) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_6])).

cnf(c_245,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r1_partfun1(X1,X2)
    | ~ m1_subset_1(k1_relat_1(X1),k1_zfmisc_1(k1_relat_1(X2)))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X1,X0) = k1_funct_1(X2,X0) ),
    inference(unflattening,[status(thm)],[c_244])).

cnf(c_1165,plain,
    ( ~ r2_hidden(X0_45,k1_relat_1(X0_46))
    | ~ r1_partfun1(X0_46,X1_46)
    | ~ m1_subset_1(k1_relat_1(X0_46),k1_zfmisc_1(k1_relat_1(X1_46)))
    | ~ v1_funct_1(X1_46)
    | ~ v1_funct_1(X0_46)
    | ~ v1_relat_1(X1_46)
    | ~ v1_relat_1(X0_46)
    | k1_funct_1(X0_46,X0_45) = k1_funct_1(X1_46,X0_45) ),
    inference(subtyping,[status(esa)],[c_245])).

cnf(c_3038,plain,
    ( ~ r2_hidden(sK4,k1_relat_1(sK2))
    | ~ r1_partfun1(sK2,sK3)
    | ~ m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(k1_relat_1(sK3)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | k1_funct_1(sK2,sK4) = k1_funct_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1165])).

cnf(c_1187,plain,
    ( ~ m1_subset_1(X0_46,X0_47)
    | m1_subset_1(X1_46,X1_47)
    | X1_47 != X0_47
    | X1_46 != X0_46 ),
    theory(equality)).

cnf(c_1976,plain,
    ( m1_subset_1(X0_46,X0_47)
    | ~ m1_subset_1(X1_46,k1_zfmisc_1(sK1))
    | X0_47 != k1_zfmisc_1(sK1)
    | X0_46 != X1_46 ),
    inference(instantiation,[status(thm)],[c_1187])).

cnf(c_2243,plain,
    ( m1_subset_1(X0_46,k1_zfmisc_1(X1_46))
    | ~ m1_subset_1(X2_46,k1_zfmisc_1(sK1))
    | k1_zfmisc_1(X1_46) != k1_zfmisc_1(sK1)
    | X0_46 != X2_46 ),
    inference(instantiation,[status(thm)],[c_1976])).

cnf(c_2485,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(sK1))
    | m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(k1_relat_1(sK3)))
    | k1_zfmisc_1(k1_relat_1(sK3)) != k1_zfmisc_1(sK1)
    | k1_relat_1(sK2) != X0_46 ),
    inference(instantiation,[status(thm)],[c_2243])).

cnf(c_2929,plain,
    ( ~ m1_subset_1(k1_relset_1(sK1,sK1,sK2),k1_zfmisc_1(sK1))
    | m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(k1_relat_1(sK3)))
    | k1_zfmisc_1(k1_relat_1(sK3)) != k1_zfmisc_1(sK1)
    | k1_relat_1(sK2) != k1_relset_1(sK1,sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_2485])).

cnf(c_11,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1172,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1465,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1172])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1176,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X1_46,X2_46)))
    | k1_relset_1(X1_46,X2_46,X0_46) = k1_relat_1(X0_46) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1461,plain,
    ( k1_relset_1(X0_46,X1_46,X2_46) = k1_relat_1(X2_46)
    | m1_subset_1(X2_46,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1176])).

cnf(c_1741,plain,
    ( k1_relset_1(sK1,sK1,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1465,c_1461])).

cnf(c_7,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k1_relset_1(X1,X1,X0) = X1 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_12,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_181,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k1_relset_1(X1,X1,X0) = X1
    | sK1 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_12])).

cnf(c_182,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK3)
    | k1_relset_1(sK1,sK1,sK3) = sK1 ),
    inference(unflattening,[status(thm)],[c_181])).

cnf(c_13,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_184,plain,
    ( k1_relset_1(sK1,sK1,sK3) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_182,c_13,c_11])).

cnf(c_1168,plain,
    ( k1_relset_1(sK1,sK1,sK3) = sK1 ),
    inference(subtyping,[status(esa)],[c_184])).

cnf(c_1746,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_1741,c_1168])).

cnf(c_5,plain,
    ( r2_hidden(sK0(X0,X1),k1_relat_1(X0))
    | r1_partfun1(X0,X1)
    | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_190,plain,
    ( r2_hidden(sK0(X0,X1),k1_relat_1(X0))
    | r1_partfun1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k1_relat_1(X1) != X3
    | k1_relat_1(X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_5])).

cnf(c_191,plain,
    ( r2_hidden(sK0(X0,X1),k1_relat_1(X0))
    | r1_partfun1(X0,X1)
    | ~ m1_subset_1(k1_relat_1(X0),k1_zfmisc_1(k1_relat_1(X1)))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_190])).

cnf(c_1167,plain,
    ( r2_hidden(sK0(X0_46,X1_46),k1_relat_1(X0_46))
    | r1_partfun1(X0_46,X1_46)
    | ~ m1_subset_1(k1_relat_1(X0_46),k1_zfmisc_1(k1_relat_1(X1_46)))
    | ~ v1_funct_1(X1_46)
    | ~ v1_funct_1(X0_46)
    | ~ v1_relat_1(X1_46)
    | ~ v1_relat_1(X0_46) ),
    inference(subtyping,[status(esa)],[c_191])).

cnf(c_1469,plain,
    ( r2_hidden(sK0(X0_46,X1_46),k1_relat_1(X0_46)) = iProver_top
    | r1_partfun1(X0_46,X1_46) = iProver_top
    | m1_subset_1(k1_relat_1(X0_46),k1_zfmisc_1(k1_relat_1(X1_46))) != iProver_top
    | v1_funct_1(X1_46) != iProver_top
    | v1_funct_1(X0_46) != iProver_top
    | v1_relat_1(X0_46) != iProver_top
    | v1_relat_1(X1_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1167])).

cnf(c_2193,plain,
    ( r2_hidden(sK0(X0_46,sK3),k1_relat_1(X0_46)) = iProver_top
    | r1_partfun1(X0_46,sK3) = iProver_top
    | m1_subset_1(k1_relat_1(X0_46),k1_zfmisc_1(sK1)) != iProver_top
    | v1_funct_1(X0_46) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(X0_46) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1746,c_1469])).

cnf(c_18,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_20,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_1178,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X1_46,X2_46)))
    | v1_relat_1(X0_46) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1586,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1178])).

cnf(c_1587,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1586])).

cnf(c_2422,plain,
    ( v1_relat_1(X0_46) != iProver_top
    | r2_hidden(sK0(X0_46,sK3),k1_relat_1(X0_46)) = iProver_top
    | r1_partfun1(X0_46,sK3) = iProver_top
    | m1_subset_1(k1_relat_1(X0_46),k1_zfmisc_1(sK1)) != iProver_top
    | v1_funct_1(X0_46) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2193,c_18,c_20,c_1587])).

cnf(c_2423,plain,
    ( r2_hidden(sK0(X0_46,sK3),k1_relat_1(X0_46)) = iProver_top
    | r1_partfun1(X0_46,sK3) = iProver_top
    | m1_subset_1(k1_relat_1(X0_46),k1_zfmisc_1(sK1)) != iProver_top
    | v1_funct_1(X0_46) != iProver_top
    | v1_relat_1(X0_46) != iProver_top ),
    inference(renaming,[status(thm)],[c_2422])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1170,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1467,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1170])).

cnf(c_1742,plain,
    ( k1_relset_1(sK1,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1467,c_1461])).

cnf(c_10,negated_conjecture,
    ( ~ r2_hidden(X0,k1_relset_1(sK1,sK1,sK2))
    | r1_partfun1(sK2,sK3)
    | k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1173,negated_conjecture,
    ( ~ r2_hidden(X0_45,k1_relset_1(sK1,sK1,sK2))
    | r1_partfun1(sK2,sK3)
    | k1_funct_1(sK2,X0_45) = k1_funct_1(sK3,X0_45) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1464,plain,
    ( k1_funct_1(sK2,X0_45) = k1_funct_1(sK3,X0_45)
    | r2_hidden(X0_45,k1_relset_1(sK1,sK1,sK2)) != iProver_top
    | r1_partfun1(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1173])).

cnf(c_1955,plain,
    ( k1_funct_1(sK3,X0_45) = k1_funct_1(sK2,X0_45)
    | r2_hidden(X0_45,k1_relat_1(sK2)) != iProver_top
    | r1_partfun1(sK2,sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1742,c_1464])).

cnf(c_2434,plain,
    ( k1_funct_1(sK2,sK0(sK2,sK3)) = k1_funct_1(sK3,sK0(sK2,sK3))
    | r1_partfun1(sK2,sK3) = iProver_top
    | m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK1)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2423,c_1955])).

cnf(c_2445,plain,
    ( r1_partfun1(sK2,sK3)
    | ~ m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK1))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_funct_1(sK2,sK0(sK2,sK3)) = k1_funct_1(sK3,sK0(sK2,sK3)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2434])).

cnf(c_1181,plain,
    ( X0_46 = X0_46 ),
    theory(equality)).

cnf(c_2385,plain,
    ( k1_relat_1(sK2) = k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1181])).

cnf(c_1184,plain,
    ( X0_46 != X1_46
    | X2_46 != X1_46
    | X2_46 = X0_46 ),
    theory(equality)).

cnf(c_1871,plain,
    ( X0_46 != X1_46
    | X0_46 = k1_relset_1(sK1,sK1,sK2)
    | k1_relset_1(sK1,sK1,sK2) != X1_46 ),
    inference(instantiation,[status(thm)],[c_1184])).

cnf(c_2159,plain,
    ( X0_46 = k1_relset_1(sK1,sK1,sK2)
    | X0_46 != k1_relat_1(sK2)
    | k1_relset_1(sK1,sK1,sK2) != k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1871])).

cnf(c_2384,plain,
    ( k1_relset_1(sK1,sK1,sK2) != k1_relat_1(sK2)
    | k1_relat_1(sK2) = k1_relset_1(sK1,sK1,sK2)
    | k1_relat_1(sK2) != k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_2159])).

cnf(c_1186,plain,
    ( k1_zfmisc_1(X0_46) = k1_zfmisc_1(X1_46)
    | X0_46 != X1_46 ),
    theory(equality)).

cnf(c_1776,plain,
    ( k1_zfmisc_1(X0_46) = k1_zfmisc_1(sK1)
    | X0_46 != sK1 ),
    inference(instantiation,[status(thm)],[c_1186])).

cnf(c_2073,plain,
    ( k1_zfmisc_1(k1_relat_1(sK3)) = k1_zfmisc_1(sK1)
    | k1_relat_1(sK3) != sK1 ),
    inference(instantiation,[status(thm)],[c_1776])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1177,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X1_46,X2_46)))
    | m1_subset_1(k1_relset_1(X1_46,X2_46,X0_46),k1_zfmisc_1(X1_46)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1460,plain,
    ( m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X1_46,X2_46))) != iProver_top
    | m1_subset_1(k1_relset_1(X1_46,X2_46,X0_46),k1_zfmisc_1(X1_46)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1177])).

cnf(c_1971,plain,
    ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK1)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1742,c_1460])).

cnf(c_1972,plain,
    ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1971])).

cnf(c_9,negated_conjecture,
    ( r2_hidden(sK4,k1_relset_1(sK1,sK1,sK2))
    | ~ r1_partfun1(sK2,sK3) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1174,negated_conjecture,
    ( r2_hidden(sK4,k1_relset_1(sK1,sK1,sK2))
    | ~ r1_partfun1(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1463,plain,
    ( r2_hidden(sK4,k1_relset_1(sK1,sK1,sK2)) = iProver_top
    | r1_partfun1(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1174])).

cnf(c_1956,plain,
    ( r2_hidden(sK4,k1_relat_1(sK2)) = iProver_top
    | r1_partfun1(sK2,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1742,c_1463])).

cnf(c_1970,plain,
    ( r2_hidden(sK4,k1_relat_1(sK2))
    | ~ r1_partfun1(sK2,sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1956])).

cnf(c_4,plain,
    ( r1_partfun1(X0,X1)
    | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k1_funct_1(X1,sK0(X0,X1)) != k1_funct_1(X0,sK0(X0,X1)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_217,plain,
    ( r1_partfun1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1))
    | k1_relat_1(X1) != X3
    | k1_relat_1(X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_4])).

cnf(c_218,plain,
    ( r1_partfun1(X0,X1)
    | ~ m1_subset_1(k1_relat_1(X0),k1_zfmisc_1(k1_relat_1(X1)))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_217])).

cnf(c_1166,plain,
    ( r1_partfun1(X0_46,X1_46)
    | ~ m1_subset_1(k1_relat_1(X0_46),k1_zfmisc_1(k1_relat_1(X1_46)))
    | ~ v1_funct_1(X1_46)
    | ~ v1_funct_1(X0_46)
    | ~ v1_relat_1(X1_46)
    | ~ v1_relat_1(X0_46)
    | k1_funct_1(X0_46,sK0(X0_46,X1_46)) != k1_funct_1(X1_46,sK0(X0_46,X1_46)) ),
    inference(subtyping,[status(esa)],[c_218])).

cnf(c_1637,plain,
    ( r1_partfun1(X0_46,sK3)
    | ~ m1_subset_1(k1_relat_1(X0_46),k1_zfmisc_1(k1_relat_1(sK3)))
    | ~ v1_funct_1(X0_46)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(X0_46)
    | ~ v1_relat_1(sK3)
    | k1_funct_1(X0_46,sK0(X0_46,sK3)) != k1_funct_1(sK3,sK0(X0_46,sK3)) ),
    inference(instantiation,[status(thm)],[c_1166])).

cnf(c_1706,plain,
    ( r1_partfun1(sK2,sK3)
    | ~ m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(k1_relat_1(sK3)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | k1_funct_1(sK2,sK0(sK2,sK3)) != k1_funct_1(sK3,sK0(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_1637])).

cnf(c_1611,plain,
    ( m1_subset_1(k1_relset_1(sK1,sK1,sK2),k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(instantiation,[status(thm)],[c_1177])).

cnf(c_1605,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | k1_relset_1(sK1,sK1,sK2) = k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1176])).

cnf(c_1589,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1178])).

cnf(c_8,negated_conjecture,
    ( ~ r1_partfun1(sK2,sK3)
    | k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1175,negated_conjecture,
    ( ~ r1_partfun1(sK2,sK3)
    | k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_15,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f39])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3038,c_2929,c_2445,c_2385,c_2384,c_2073,c_1972,c_1970,c_1746,c_1706,c_1611,c_1605,c_1589,c_1586,c_1175,c_11,c_13,c_14,c_15])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:06:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 2.27/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/0.99  
% 2.27/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.27/0.99  
% 2.27/0.99  ------  iProver source info
% 2.27/0.99  
% 2.27/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.27/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.27/0.99  git: non_committed_changes: false
% 2.27/0.99  git: last_make_outside_of_git: false
% 2.27/0.99  
% 2.27/0.99  ------ 
% 2.27/0.99  
% 2.27/0.99  ------ Input Options
% 2.27/0.99  
% 2.27/0.99  --out_options                           all
% 2.27/0.99  --tptp_safe_out                         true
% 2.27/0.99  --problem_path                          ""
% 2.27/0.99  --include_path                          ""
% 2.27/0.99  --clausifier                            res/vclausify_rel
% 2.27/0.99  --clausifier_options                    --mode clausify
% 2.27/0.99  --stdin                                 false
% 2.27/0.99  --stats_out                             all
% 2.27/0.99  
% 2.27/0.99  ------ General Options
% 2.27/0.99  
% 2.27/0.99  --fof                                   false
% 2.27/0.99  --time_out_real                         305.
% 2.27/0.99  --time_out_virtual                      -1.
% 2.27/0.99  --symbol_type_check                     false
% 2.27/0.99  --clausify_out                          false
% 2.27/0.99  --sig_cnt_out                           false
% 2.27/0.99  --trig_cnt_out                          false
% 2.27/0.99  --trig_cnt_out_tolerance                1.
% 2.27/0.99  --trig_cnt_out_sk_spl                   false
% 2.27/0.99  --abstr_cl_out                          false
% 2.27/0.99  
% 2.27/0.99  ------ Global Options
% 2.27/0.99  
% 2.27/0.99  --schedule                              default
% 2.27/0.99  --add_important_lit                     false
% 2.27/0.99  --prop_solver_per_cl                    1000
% 2.27/0.99  --min_unsat_core                        false
% 2.27/0.99  --soft_assumptions                      false
% 2.27/0.99  --soft_lemma_size                       3
% 2.27/0.99  --prop_impl_unit_size                   0
% 2.27/0.99  --prop_impl_unit                        []
% 2.27/0.99  --share_sel_clauses                     true
% 2.27/0.99  --reset_solvers                         false
% 2.27/0.99  --bc_imp_inh                            [conj_cone]
% 2.27/0.99  --conj_cone_tolerance                   3.
% 2.27/0.99  --extra_neg_conj                        none
% 2.27/0.99  --large_theory_mode                     true
% 2.27/0.99  --prolific_symb_bound                   200
% 2.27/0.99  --lt_threshold                          2000
% 2.27/0.99  --clause_weak_htbl                      true
% 2.27/0.99  --gc_record_bc_elim                     false
% 2.27/0.99  
% 2.27/0.99  ------ Preprocessing Options
% 2.27/0.99  
% 2.27/0.99  --preprocessing_flag                    true
% 2.27/0.99  --time_out_prep_mult                    0.1
% 2.27/0.99  --splitting_mode                        input
% 2.27/0.99  --splitting_grd                         true
% 2.27/0.99  --splitting_cvd                         false
% 2.27/0.99  --splitting_cvd_svl                     false
% 2.27/0.99  --splitting_nvd                         32
% 2.27/0.99  --sub_typing                            true
% 2.27/0.99  --prep_gs_sim                           true
% 2.27/0.99  --prep_unflatten                        true
% 2.27/0.99  --prep_res_sim                          true
% 2.27/0.99  --prep_upred                            true
% 2.27/0.99  --prep_sem_filter                       exhaustive
% 2.27/0.99  --prep_sem_filter_out                   false
% 2.27/0.99  --pred_elim                             true
% 2.27/0.99  --res_sim_input                         true
% 2.27/0.99  --eq_ax_congr_red                       true
% 2.27/0.99  --pure_diseq_elim                       true
% 2.27/0.99  --brand_transform                       false
% 2.27/0.99  --non_eq_to_eq                          false
% 2.27/0.99  --prep_def_merge                        true
% 2.27/0.99  --prep_def_merge_prop_impl              false
% 2.27/0.99  --prep_def_merge_mbd                    true
% 2.27/0.99  --prep_def_merge_tr_red                 false
% 2.27/0.99  --prep_def_merge_tr_cl                  false
% 2.27/0.99  --smt_preprocessing                     true
% 2.27/0.99  --smt_ac_axioms                         fast
% 2.27/0.99  --preprocessed_out                      false
% 2.27/0.99  --preprocessed_stats                    false
% 2.27/0.99  
% 2.27/0.99  ------ Abstraction refinement Options
% 2.27/0.99  
% 2.27/0.99  --abstr_ref                             []
% 2.27/0.99  --abstr_ref_prep                        false
% 2.27/0.99  --abstr_ref_until_sat                   false
% 2.27/0.99  --abstr_ref_sig_restrict                funpre
% 2.27/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.27/0.99  --abstr_ref_under                       []
% 2.27/0.99  
% 2.27/0.99  ------ SAT Options
% 2.27/0.99  
% 2.27/0.99  --sat_mode                              false
% 2.27/0.99  --sat_fm_restart_options                ""
% 2.27/0.99  --sat_gr_def                            false
% 2.27/0.99  --sat_epr_types                         true
% 2.27/0.99  --sat_non_cyclic_types                  false
% 2.27/0.99  --sat_finite_models                     false
% 2.27/0.99  --sat_fm_lemmas                         false
% 2.27/0.99  --sat_fm_prep                           false
% 2.27/0.99  --sat_fm_uc_incr                        true
% 2.27/0.99  --sat_out_model                         small
% 2.27/0.99  --sat_out_clauses                       false
% 2.27/0.99  
% 2.27/0.99  ------ QBF Options
% 2.27/0.99  
% 2.27/0.99  --qbf_mode                              false
% 2.27/0.99  --qbf_elim_univ                         false
% 2.27/0.99  --qbf_dom_inst                          none
% 2.27/0.99  --qbf_dom_pre_inst                      false
% 2.27/0.99  --qbf_sk_in                             false
% 2.27/0.99  --qbf_pred_elim                         true
% 2.27/0.99  --qbf_split                             512
% 2.27/0.99  
% 2.27/0.99  ------ BMC1 Options
% 2.27/0.99  
% 2.27/0.99  --bmc1_incremental                      false
% 2.27/0.99  --bmc1_axioms                           reachable_all
% 2.27/0.99  --bmc1_min_bound                        0
% 2.27/0.99  --bmc1_max_bound                        -1
% 2.27/0.99  --bmc1_max_bound_default                -1
% 2.27/0.99  --bmc1_symbol_reachability              true
% 2.27/0.99  --bmc1_property_lemmas                  false
% 2.27/0.99  --bmc1_k_induction                      false
% 2.27/0.99  --bmc1_non_equiv_states                 false
% 2.27/0.99  --bmc1_deadlock                         false
% 2.27/0.99  --bmc1_ucm                              false
% 2.27/0.99  --bmc1_add_unsat_core                   none
% 2.27/0.99  --bmc1_unsat_core_children              false
% 2.27/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.27/0.99  --bmc1_out_stat                         full
% 2.27/0.99  --bmc1_ground_init                      false
% 2.27/0.99  --bmc1_pre_inst_next_state              false
% 2.27/0.99  --bmc1_pre_inst_state                   false
% 2.27/0.99  --bmc1_pre_inst_reach_state             false
% 2.27/0.99  --bmc1_out_unsat_core                   false
% 2.27/0.99  --bmc1_aig_witness_out                  false
% 2.27/0.99  --bmc1_verbose                          false
% 2.27/0.99  --bmc1_dump_clauses_tptp                false
% 2.27/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.27/0.99  --bmc1_dump_file                        -
% 2.27/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.27/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.27/0.99  --bmc1_ucm_extend_mode                  1
% 2.27/0.99  --bmc1_ucm_init_mode                    2
% 2.27/0.99  --bmc1_ucm_cone_mode                    none
% 2.27/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.27/0.99  --bmc1_ucm_relax_model                  4
% 2.27/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.27/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.27/0.99  --bmc1_ucm_layered_model                none
% 2.27/0.99  --bmc1_ucm_max_lemma_size               10
% 2.27/0.99  
% 2.27/0.99  ------ AIG Options
% 2.27/0.99  
% 2.27/0.99  --aig_mode                              false
% 2.27/0.99  
% 2.27/0.99  ------ Instantiation Options
% 2.27/0.99  
% 2.27/0.99  --instantiation_flag                    true
% 2.27/0.99  --inst_sos_flag                         false
% 2.27/0.99  --inst_sos_phase                        true
% 2.27/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.27/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.27/0.99  --inst_lit_sel_side                     num_symb
% 2.27/0.99  --inst_solver_per_active                1400
% 2.27/0.99  --inst_solver_calls_frac                1.
% 2.27/0.99  --inst_passive_queue_type               priority_queues
% 2.27/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.27/0.99  --inst_passive_queues_freq              [25;2]
% 2.27/0.99  --inst_dismatching                      true
% 2.27/0.99  --inst_eager_unprocessed_to_passive     true
% 2.27/0.99  --inst_prop_sim_given                   true
% 2.27/0.99  --inst_prop_sim_new                     false
% 2.27/0.99  --inst_subs_new                         false
% 2.27/0.99  --inst_eq_res_simp                      false
% 2.27/0.99  --inst_subs_given                       false
% 2.27/0.99  --inst_orphan_elimination               true
% 2.27/0.99  --inst_learning_loop_flag               true
% 2.27/0.99  --inst_learning_start                   3000
% 2.27/0.99  --inst_learning_factor                  2
% 2.27/0.99  --inst_start_prop_sim_after_learn       3
% 2.27/0.99  --inst_sel_renew                        solver
% 2.27/0.99  --inst_lit_activity_flag                true
% 2.27/0.99  --inst_restr_to_given                   false
% 2.27/0.99  --inst_activity_threshold               500
% 2.27/0.99  --inst_out_proof                        true
% 2.27/0.99  
% 2.27/0.99  ------ Resolution Options
% 2.27/0.99  
% 2.27/0.99  --resolution_flag                       true
% 2.27/0.99  --res_lit_sel                           adaptive
% 2.27/0.99  --res_lit_sel_side                      none
% 2.27/0.99  --res_ordering                          kbo
% 2.27/0.99  --res_to_prop_solver                    active
% 2.27/0.99  --res_prop_simpl_new                    false
% 2.27/0.99  --res_prop_simpl_given                  true
% 2.27/0.99  --res_passive_queue_type                priority_queues
% 2.27/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.27/0.99  --res_passive_queues_freq               [15;5]
% 2.27/0.99  --res_forward_subs                      full
% 2.27/0.99  --res_backward_subs                     full
% 2.27/0.99  --res_forward_subs_resolution           true
% 2.27/0.99  --res_backward_subs_resolution          true
% 2.27/0.99  --res_orphan_elimination                true
% 2.27/0.99  --res_time_limit                        2.
% 2.27/0.99  --res_out_proof                         true
% 2.27/0.99  
% 2.27/0.99  ------ Superposition Options
% 2.27/0.99  
% 2.27/0.99  --superposition_flag                    true
% 2.27/0.99  --sup_passive_queue_type                priority_queues
% 2.27/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.27/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.27/0.99  --demod_completeness_check              fast
% 2.27/0.99  --demod_use_ground                      true
% 2.27/0.99  --sup_to_prop_solver                    passive
% 2.27/0.99  --sup_prop_simpl_new                    true
% 2.27/0.99  --sup_prop_simpl_given                  true
% 2.27/0.99  --sup_fun_splitting                     false
% 2.27/0.99  --sup_smt_interval                      50000
% 2.27/0.99  
% 2.27/0.99  ------ Superposition Simplification Setup
% 2.27/0.99  
% 2.27/0.99  --sup_indices_passive                   []
% 2.27/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.27/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.27/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.27/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.27/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.27/0.99  --sup_full_bw                           [BwDemod]
% 2.27/0.99  --sup_immed_triv                        [TrivRules]
% 2.27/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.27/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.27/0.99  --sup_immed_bw_main                     []
% 2.27/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.27/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.27/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.27/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.27/0.99  
% 2.27/0.99  ------ Combination Options
% 2.27/0.99  
% 2.27/0.99  --comb_res_mult                         3
% 2.27/0.99  --comb_sup_mult                         2
% 2.27/0.99  --comb_inst_mult                        10
% 2.27/0.99  
% 2.27/0.99  ------ Debug Options
% 2.27/0.99  
% 2.27/0.99  --dbg_backtrace                         false
% 2.27/0.99  --dbg_dump_prop_clauses                 false
% 2.27/0.99  --dbg_dump_prop_clauses_file            -
% 2.27/0.99  --dbg_out_stat                          false
% 2.27/0.99  ------ Parsing...
% 2.27/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.27/0.99  
% 2.27/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.27/0.99  
% 2.27/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.27/0.99  
% 2.27/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.27/0.99  ------ Proving...
% 2.27/0.99  ------ Problem Properties 
% 2.27/0.99  
% 2.27/0.99  
% 2.27/0.99  clauses                                 14
% 2.27/0.99  conjectures                             7
% 2.27/0.99  EPR                                     2
% 2.27/0.99  Horn                                    12
% 2.27/0.99  unary                                   5
% 2.27/0.99  binary                                  5
% 2.27/0.99  lits                                    40
% 2.27/0.99  lits eq                                 6
% 2.27/0.99  fd_pure                                 0
% 2.27/0.99  fd_pseudo                               0
% 2.27/0.99  fd_cond                                 0
% 2.27/0.99  fd_pseudo_cond                          0
% 2.27/0.99  AC symbols                              0
% 2.27/0.99  
% 2.27/0.99  ------ Schedule dynamic 5 is on 
% 2.27/0.99  
% 2.27/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.27/0.99  
% 2.27/0.99  
% 2.27/0.99  ------ 
% 2.27/0.99  Current options:
% 2.27/0.99  ------ 
% 2.27/0.99  
% 2.27/0.99  ------ Input Options
% 2.27/0.99  
% 2.27/0.99  --out_options                           all
% 2.27/0.99  --tptp_safe_out                         true
% 2.27/0.99  --problem_path                          ""
% 2.27/0.99  --include_path                          ""
% 2.27/0.99  --clausifier                            res/vclausify_rel
% 2.27/0.99  --clausifier_options                    --mode clausify
% 2.27/0.99  --stdin                                 false
% 2.27/0.99  --stats_out                             all
% 2.27/0.99  
% 2.27/0.99  ------ General Options
% 2.27/0.99  
% 2.27/0.99  --fof                                   false
% 2.27/0.99  --time_out_real                         305.
% 2.27/0.99  --time_out_virtual                      -1.
% 2.27/0.99  --symbol_type_check                     false
% 2.27/0.99  --clausify_out                          false
% 2.27/0.99  --sig_cnt_out                           false
% 2.27/0.99  --trig_cnt_out                          false
% 2.27/0.99  --trig_cnt_out_tolerance                1.
% 2.27/0.99  --trig_cnt_out_sk_spl                   false
% 2.27/0.99  --abstr_cl_out                          false
% 2.27/0.99  
% 2.27/0.99  ------ Global Options
% 2.27/0.99  
% 2.27/0.99  --schedule                              default
% 2.27/0.99  --add_important_lit                     false
% 2.27/0.99  --prop_solver_per_cl                    1000
% 2.27/0.99  --min_unsat_core                        false
% 2.27/0.99  --soft_assumptions                      false
% 2.27/0.99  --soft_lemma_size                       3
% 2.27/0.99  --prop_impl_unit_size                   0
% 2.27/0.99  --prop_impl_unit                        []
% 2.27/0.99  --share_sel_clauses                     true
% 2.27/0.99  --reset_solvers                         false
% 2.27/0.99  --bc_imp_inh                            [conj_cone]
% 2.27/0.99  --conj_cone_tolerance                   3.
% 2.27/0.99  --extra_neg_conj                        none
% 2.27/0.99  --large_theory_mode                     true
% 2.27/0.99  --prolific_symb_bound                   200
% 2.27/0.99  --lt_threshold                          2000
% 2.27/0.99  --clause_weak_htbl                      true
% 2.27/0.99  --gc_record_bc_elim                     false
% 2.27/0.99  
% 2.27/0.99  ------ Preprocessing Options
% 2.27/0.99  
% 2.27/0.99  --preprocessing_flag                    true
% 2.27/0.99  --time_out_prep_mult                    0.1
% 2.27/0.99  --splitting_mode                        input
% 2.27/0.99  --splitting_grd                         true
% 2.27/0.99  --splitting_cvd                         false
% 2.27/0.99  --splitting_cvd_svl                     false
% 2.27/0.99  --splitting_nvd                         32
% 2.27/0.99  --sub_typing                            true
% 2.27/0.99  --prep_gs_sim                           true
% 2.27/0.99  --prep_unflatten                        true
% 2.27/0.99  --prep_res_sim                          true
% 2.27/0.99  --prep_upred                            true
% 2.27/0.99  --prep_sem_filter                       exhaustive
% 2.27/0.99  --prep_sem_filter_out                   false
% 2.27/0.99  --pred_elim                             true
% 2.27/0.99  --res_sim_input                         true
% 2.27/0.99  --eq_ax_congr_red                       true
% 2.27/0.99  --pure_diseq_elim                       true
% 2.27/0.99  --brand_transform                       false
% 2.27/0.99  --non_eq_to_eq                          false
% 2.27/0.99  --prep_def_merge                        true
% 2.27/0.99  --prep_def_merge_prop_impl              false
% 2.27/0.99  --prep_def_merge_mbd                    true
% 2.27/0.99  --prep_def_merge_tr_red                 false
% 2.27/0.99  --prep_def_merge_tr_cl                  false
% 2.27/0.99  --smt_preprocessing                     true
% 2.27/0.99  --smt_ac_axioms                         fast
% 2.27/0.99  --preprocessed_out                      false
% 2.27/0.99  --preprocessed_stats                    false
% 2.27/0.99  
% 2.27/0.99  ------ Abstraction refinement Options
% 2.27/0.99  
% 2.27/0.99  --abstr_ref                             []
% 2.27/0.99  --abstr_ref_prep                        false
% 2.27/0.99  --abstr_ref_until_sat                   false
% 2.27/0.99  --abstr_ref_sig_restrict                funpre
% 2.27/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.27/0.99  --abstr_ref_under                       []
% 2.27/0.99  
% 2.27/0.99  ------ SAT Options
% 2.27/0.99  
% 2.27/0.99  --sat_mode                              false
% 2.27/0.99  --sat_fm_restart_options                ""
% 2.27/0.99  --sat_gr_def                            false
% 2.27/0.99  --sat_epr_types                         true
% 2.27/0.99  --sat_non_cyclic_types                  false
% 2.27/0.99  --sat_finite_models                     false
% 2.27/0.99  --sat_fm_lemmas                         false
% 2.27/0.99  --sat_fm_prep                           false
% 2.27/0.99  --sat_fm_uc_incr                        true
% 2.27/0.99  --sat_out_model                         small
% 2.27/0.99  --sat_out_clauses                       false
% 2.27/0.99  
% 2.27/0.99  ------ QBF Options
% 2.27/0.99  
% 2.27/0.99  --qbf_mode                              false
% 2.27/0.99  --qbf_elim_univ                         false
% 2.27/0.99  --qbf_dom_inst                          none
% 2.27/0.99  --qbf_dom_pre_inst                      false
% 2.27/0.99  --qbf_sk_in                             false
% 2.27/0.99  --qbf_pred_elim                         true
% 2.27/0.99  --qbf_split                             512
% 2.27/0.99  
% 2.27/0.99  ------ BMC1 Options
% 2.27/0.99  
% 2.27/0.99  --bmc1_incremental                      false
% 2.27/0.99  --bmc1_axioms                           reachable_all
% 2.27/0.99  --bmc1_min_bound                        0
% 2.27/0.99  --bmc1_max_bound                        -1
% 2.27/0.99  --bmc1_max_bound_default                -1
% 2.27/0.99  --bmc1_symbol_reachability              true
% 2.27/0.99  --bmc1_property_lemmas                  false
% 2.27/0.99  --bmc1_k_induction                      false
% 2.27/0.99  --bmc1_non_equiv_states                 false
% 2.27/0.99  --bmc1_deadlock                         false
% 2.27/0.99  --bmc1_ucm                              false
% 2.27/0.99  --bmc1_add_unsat_core                   none
% 2.27/0.99  --bmc1_unsat_core_children              false
% 2.27/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.27/0.99  --bmc1_out_stat                         full
% 2.27/0.99  --bmc1_ground_init                      false
% 2.27/0.99  --bmc1_pre_inst_next_state              false
% 2.27/0.99  --bmc1_pre_inst_state                   false
% 2.27/0.99  --bmc1_pre_inst_reach_state             false
% 2.27/0.99  --bmc1_out_unsat_core                   false
% 2.27/0.99  --bmc1_aig_witness_out                  false
% 2.27/0.99  --bmc1_verbose                          false
% 2.27/0.99  --bmc1_dump_clauses_tptp                false
% 2.27/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.27/0.99  --bmc1_dump_file                        -
% 2.27/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.27/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.27/0.99  --bmc1_ucm_extend_mode                  1
% 2.27/0.99  --bmc1_ucm_init_mode                    2
% 2.27/0.99  --bmc1_ucm_cone_mode                    none
% 2.27/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.27/0.99  --bmc1_ucm_relax_model                  4
% 2.27/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.27/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.27/0.99  --bmc1_ucm_layered_model                none
% 2.27/0.99  --bmc1_ucm_max_lemma_size               10
% 2.27/0.99  
% 2.27/0.99  ------ AIG Options
% 2.27/0.99  
% 2.27/0.99  --aig_mode                              false
% 2.27/0.99  
% 2.27/0.99  ------ Instantiation Options
% 2.27/0.99  
% 2.27/0.99  --instantiation_flag                    true
% 2.27/0.99  --inst_sos_flag                         false
% 2.27/0.99  --inst_sos_phase                        true
% 2.27/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.27/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.27/0.99  --inst_lit_sel_side                     none
% 2.27/0.99  --inst_solver_per_active                1400
% 2.27/0.99  --inst_solver_calls_frac                1.
% 2.27/0.99  --inst_passive_queue_type               priority_queues
% 2.27/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.27/0.99  --inst_passive_queues_freq              [25;2]
% 2.27/0.99  --inst_dismatching                      true
% 2.27/0.99  --inst_eager_unprocessed_to_passive     true
% 2.27/0.99  --inst_prop_sim_given                   true
% 2.27/0.99  --inst_prop_sim_new                     false
% 2.27/0.99  --inst_subs_new                         false
% 2.27/0.99  --inst_eq_res_simp                      false
% 2.27/0.99  --inst_subs_given                       false
% 2.27/0.99  --inst_orphan_elimination               true
% 2.27/0.99  --inst_learning_loop_flag               true
% 2.27/0.99  --inst_learning_start                   3000
% 2.27/0.99  --inst_learning_factor                  2
% 2.27/0.99  --inst_start_prop_sim_after_learn       3
% 2.27/0.99  --inst_sel_renew                        solver
% 2.27/0.99  --inst_lit_activity_flag                true
% 2.27/0.99  --inst_restr_to_given                   false
% 2.27/0.99  --inst_activity_threshold               500
% 2.27/0.99  --inst_out_proof                        true
% 2.27/0.99  
% 2.27/0.99  ------ Resolution Options
% 2.27/0.99  
% 2.27/0.99  --resolution_flag                       false
% 2.27/0.99  --res_lit_sel                           adaptive
% 2.27/0.99  --res_lit_sel_side                      none
% 2.27/0.99  --res_ordering                          kbo
% 2.27/0.99  --res_to_prop_solver                    active
% 2.27/0.99  --res_prop_simpl_new                    false
% 2.27/0.99  --res_prop_simpl_given                  true
% 2.27/0.99  --res_passive_queue_type                priority_queues
% 2.27/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.27/0.99  --res_passive_queues_freq               [15;5]
% 2.27/0.99  --res_forward_subs                      full
% 2.27/0.99  --res_backward_subs                     full
% 2.27/0.99  --res_forward_subs_resolution           true
% 2.27/0.99  --res_backward_subs_resolution          true
% 2.27/0.99  --res_orphan_elimination                true
% 2.27/0.99  --res_time_limit                        2.
% 2.27/0.99  --res_out_proof                         true
% 2.27/0.99  
% 2.27/0.99  ------ Superposition Options
% 2.27/0.99  
% 2.27/0.99  --superposition_flag                    true
% 2.27/0.99  --sup_passive_queue_type                priority_queues
% 2.27/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.27/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.27/0.99  --demod_completeness_check              fast
% 2.27/0.99  --demod_use_ground                      true
% 2.27/0.99  --sup_to_prop_solver                    passive
% 2.27/0.99  --sup_prop_simpl_new                    true
% 2.27/0.99  --sup_prop_simpl_given                  true
% 2.27/0.99  --sup_fun_splitting                     false
% 2.27/0.99  --sup_smt_interval                      50000
% 2.27/0.99  
% 2.27/0.99  ------ Superposition Simplification Setup
% 2.27/0.99  
% 2.27/0.99  --sup_indices_passive                   []
% 2.27/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.27/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.27/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.27/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.27/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.27/0.99  --sup_full_bw                           [BwDemod]
% 2.27/0.99  --sup_immed_triv                        [TrivRules]
% 2.27/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.27/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.27/0.99  --sup_immed_bw_main                     []
% 2.27/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.27/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.27/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.27/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.27/0.99  
% 2.27/0.99  ------ Combination Options
% 2.27/0.99  
% 2.27/0.99  --comb_res_mult                         3
% 2.27/0.99  --comb_sup_mult                         2
% 2.27/0.99  --comb_inst_mult                        10
% 2.27/0.99  
% 2.27/0.99  ------ Debug Options
% 2.27/0.99  
% 2.27/0.99  --dbg_backtrace                         false
% 2.27/0.99  --dbg_dump_prop_clauses                 false
% 2.27/0.99  --dbg_dump_prop_clauses_file            -
% 2.27/0.99  --dbg_out_stat                          false
% 2.27/0.99  
% 2.27/0.99  
% 2.27/0.99  
% 2.27/0.99  
% 2.27/0.99  ------ Proving...
% 2.27/0.99  
% 2.27/0.99  
% 2.27/0.99  % SZS status Theorem for theBenchmark.p
% 2.27/0.99  
% 2.27/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.27/0.99  
% 2.27/0.99  fof(f1,axiom,(
% 2.27/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.27/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.27/0.99  
% 2.27/0.99  fof(f9,plain,(
% 2.27/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 2.27/0.99    inference(unused_predicate_definition_removal,[],[f1])).
% 2.27/0.99  
% 2.27/0.99  fof(f10,plain,(
% 2.27/0.99    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 2.27/0.99    inference(ennf_transformation,[],[f9])).
% 2.27/0.99  
% 2.27/0.99  fof(f31,plain,(
% 2.27/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.27/0.99    inference(cnf_transformation,[],[f10])).
% 2.27/0.99  
% 2.27/0.99  fof(f5,axiom,(
% 2.27/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) => (r1_partfun1(X0,X1) <=> ! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2))))))),
% 2.27/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.27/0.99  
% 2.27/0.99  fof(f14,plain,(
% 2.27/0.99    ! [X0] : (! [X1] : (((r1_partfun1(X0,X1) <=> ! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0)))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.27/0.99    inference(ennf_transformation,[],[f5])).
% 2.27/0.99  
% 2.27/0.99  fof(f15,plain,(
% 2.27/0.99    ! [X0] : (! [X1] : ((r1_partfun1(X0,X1) <=> ! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0)))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.27/0.99    inference(flattening,[],[f14])).
% 2.27/0.99  
% 2.27/0.99  fof(f20,plain,(
% 2.27/0.99    ! [X0] : (! [X1] : (((r1_partfun1(X0,X1) | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0)))) & (! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0))) | ~r1_partfun1(X0,X1))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.27/0.99    inference(nnf_transformation,[],[f15])).
% 2.27/0.99  
% 2.27/0.99  fof(f21,plain,(
% 2.27/0.99    ! [X0] : (! [X1] : (((r1_partfun1(X0,X1) | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0)))) & (! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r1_partfun1(X0,X1))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.27/0.99    inference(rectify,[],[f20])).
% 2.27/0.99  
% 2.27/0.99  fof(f22,plain,(
% 2.27/0.99    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1)) & r2_hidden(sK0(X0,X1),k1_relat_1(X0))))),
% 2.27/0.99    introduced(choice_axiom,[])).
% 2.27/0.99  
% 2.27/0.99  fof(f23,plain,(
% 2.27/0.99    ! [X0] : (! [X1] : (((r1_partfun1(X0,X1) | (k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1)) & r2_hidden(sK0(X0,X1),k1_relat_1(X0)))) & (! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r1_partfun1(X0,X1))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.27/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).
% 2.27/0.99  
% 2.27/0.99  fof(f35,plain,(
% 2.27/0.99    ( ! [X0,X3,X1] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r1_partfun1(X0,X1) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.27/0.99    inference(cnf_transformation,[],[f23])).
% 2.27/0.99  
% 2.27/0.99  fof(f7,conjecture,(
% 2.27/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r1_partfun1(X1,X2) <=> ! [X3] : (r2_hidden(X3,k1_relset_1(X0,X0,X1)) => k1_funct_1(X1,X3) = k1_funct_1(X2,X3)))))),
% 2.27/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.27/0.99  
% 2.27/0.99  fof(f8,negated_conjecture,(
% 2.27/0.99    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r1_partfun1(X1,X2) <=> ! [X3] : (r2_hidden(X3,k1_relset_1(X0,X0,X1)) => k1_funct_1(X1,X3) = k1_funct_1(X2,X3)))))),
% 2.27/0.99    inference(negated_conjecture,[],[f7])).
% 2.27/0.99  
% 2.27/0.99  fof(f18,plain,(
% 2.27/0.99    ? [X0,X1] : (? [X2] : ((r1_partfun1(X1,X2) <~> ! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(X2,X3) | ~r2_hidden(X3,k1_relset_1(X0,X0,X1)))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1)))),
% 2.27/0.99    inference(ennf_transformation,[],[f8])).
% 2.27/0.99  
% 2.27/0.99  fof(f19,plain,(
% 2.27/0.99    ? [X0,X1] : (? [X2] : ((r1_partfun1(X1,X2) <~> ! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(X2,X3) | ~r2_hidden(X3,k1_relset_1(X0,X0,X1)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1))),
% 2.27/0.99    inference(flattening,[],[f18])).
% 2.27/0.99  
% 2.27/0.99  fof(f24,plain,(
% 2.27/0.99    ? [X0,X1] : (? [X2] : (((? [X3] : (k1_funct_1(X1,X3) != k1_funct_1(X2,X3) & r2_hidden(X3,k1_relset_1(X0,X0,X1))) | ~r1_partfun1(X1,X2)) & (! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(X2,X3) | ~r2_hidden(X3,k1_relset_1(X0,X0,X1))) | r1_partfun1(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1))),
% 2.27/0.99    inference(nnf_transformation,[],[f19])).
% 2.27/0.99  
% 2.27/0.99  fof(f25,plain,(
% 2.27/0.99    ? [X0,X1] : (? [X2] : ((? [X3] : (k1_funct_1(X1,X3) != k1_funct_1(X2,X3) & r2_hidden(X3,k1_relset_1(X0,X0,X1))) | ~r1_partfun1(X1,X2)) & (! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(X2,X3) | ~r2_hidden(X3,k1_relset_1(X0,X0,X1))) | r1_partfun1(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1))),
% 2.27/0.99    inference(flattening,[],[f24])).
% 2.27/0.99  
% 2.27/0.99  fof(f26,plain,(
% 2.27/0.99    ? [X0,X1] : (? [X2] : ((? [X3] : (k1_funct_1(X1,X3) != k1_funct_1(X2,X3) & r2_hidden(X3,k1_relset_1(X0,X0,X1))) | ~r1_partfun1(X1,X2)) & (! [X4] : (k1_funct_1(X1,X4) = k1_funct_1(X2,X4) | ~r2_hidden(X4,k1_relset_1(X0,X0,X1))) | r1_partfun1(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1))),
% 2.27/0.99    inference(rectify,[],[f25])).
% 2.27/0.99  
% 2.27/0.99  fof(f29,plain,(
% 2.27/0.99    ( ! [X2,X0,X1] : (? [X3] : (k1_funct_1(X1,X3) != k1_funct_1(X2,X3) & r2_hidden(X3,k1_relset_1(X0,X0,X1))) => (k1_funct_1(X1,sK4) != k1_funct_1(X2,sK4) & r2_hidden(sK4,k1_relset_1(X0,X0,X1)))) )),
% 2.27/0.99    introduced(choice_axiom,[])).
% 2.27/0.99  
% 2.27/0.99  fof(f28,plain,(
% 2.27/0.99    ( ! [X0,X1] : (? [X2] : ((? [X3] : (k1_funct_1(X1,X3) != k1_funct_1(X2,X3) & r2_hidden(X3,k1_relset_1(X0,X0,X1))) | ~r1_partfun1(X1,X2)) & (! [X4] : (k1_funct_1(X1,X4) = k1_funct_1(X2,X4) | ~r2_hidden(X4,k1_relset_1(X0,X0,X1))) | r1_partfun1(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((? [X3] : (k1_funct_1(sK3,X3) != k1_funct_1(X1,X3) & r2_hidden(X3,k1_relset_1(X0,X0,X1))) | ~r1_partfun1(X1,sK3)) & (! [X4] : (k1_funct_1(sK3,X4) = k1_funct_1(X1,X4) | ~r2_hidden(X4,k1_relset_1(X0,X0,X1))) | r1_partfun1(X1,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(sK3,X0,X0) & v1_funct_1(sK3))) )),
% 2.27/0.99    introduced(choice_axiom,[])).
% 2.27/0.99  
% 2.27/0.99  fof(f27,plain,(
% 2.27/0.99    ? [X0,X1] : (? [X2] : ((? [X3] : (k1_funct_1(X1,X3) != k1_funct_1(X2,X3) & r2_hidden(X3,k1_relset_1(X0,X0,X1))) | ~r1_partfun1(X1,X2)) & (! [X4] : (k1_funct_1(X1,X4) = k1_funct_1(X2,X4) | ~r2_hidden(X4,k1_relset_1(X0,X0,X1))) | r1_partfun1(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1)) => (? [X2] : ((? [X3] : (k1_funct_1(sK2,X3) != k1_funct_1(X2,X3) & r2_hidden(X3,k1_relset_1(sK1,sK1,sK2))) | ~r1_partfun1(sK2,X2)) & (! [X4] : (k1_funct_1(sK2,X4) = k1_funct_1(X2,X4) | ~r2_hidden(X4,k1_relset_1(sK1,sK1,sK2))) | r1_partfun1(sK2,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v1_funct_2(X2,sK1,sK1) & v1_funct_1(X2)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v1_funct_1(sK2))),
% 2.27/0.99    introduced(choice_axiom,[])).
% 2.27/0.99  
% 2.27/0.99  fof(f30,plain,(
% 2.27/0.99    (((k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4) & r2_hidden(sK4,k1_relset_1(sK1,sK1,sK2))) | ~r1_partfun1(sK2,sK3)) & (! [X4] : (k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) | ~r2_hidden(X4,k1_relset_1(sK1,sK1,sK2))) | r1_partfun1(sK2,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v1_funct_2(sK3,sK1,sK1) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v1_funct_1(sK2)),
% 2.27/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f26,f29,f28,f27])).
% 2.27/0.99  
% 2.27/0.99  fof(f43,plain,(
% 2.27/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))),
% 2.27/0.99    inference(cnf_transformation,[],[f30])).
% 2.27/0.99  
% 2.27/0.99  fof(f4,axiom,(
% 2.27/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 2.27/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.27/0.99  
% 2.27/0.99  fof(f13,plain,(
% 2.27/0.99    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.27/0.99    inference(ennf_transformation,[],[f4])).
% 2.27/0.99  
% 2.27/0.99  fof(f34,plain,(
% 2.27/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.27/0.99    inference(cnf_transformation,[],[f13])).
% 2.27/0.99  
% 2.27/0.99  fof(f6,axiom,(
% 2.27/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 2.27/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.27/0.99  
% 2.27/0.99  fof(f16,plain,(
% 2.27/0.99    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 2.27/0.99    inference(ennf_transformation,[],[f6])).
% 2.27/0.99  
% 2.27/0.99  fof(f17,plain,(
% 2.27/0.99    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 2.27/0.99    inference(flattening,[],[f16])).
% 2.27/0.99  
% 2.27/0.99  fof(f38,plain,(
% 2.27/0.99    ( ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 2.27/0.99    inference(cnf_transformation,[],[f17])).
% 2.27/0.99  
% 2.27/0.99  fof(f42,plain,(
% 2.27/0.99    v1_funct_2(sK3,sK1,sK1)),
% 2.27/0.99    inference(cnf_transformation,[],[f30])).
% 2.27/0.99  
% 2.27/0.99  fof(f41,plain,(
% 2.27/0.99    v1_funct_1(sK3)),
% 2.27/0.99    inference(cnf_transformation,[],[f30])).
% 2.27/0.99  
% 2.27/0.99  fof(f36,plain,(
% 2.27/0.99    ( ! [X0,X1] : (r1_partfun1(X0,X1) | r2_hidden(sK0(X0,X1),k1_relat_1(X0)) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.27/0.99    inference(cnf_transformation,[],[f23])).
% 2.27/0.99  
% 2.27/0.99  fof(f2,axiom,(
% 2.27/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.27/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.27/0.99  
% 2.27/0.99  fof(f11,plain,(
% 2.27/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.27/0.99    inference(ennf_transformation,[],[f2])).
% 2.27/0.99  
% 2.27/0.99  fof(f32,plain,(
% 2.27/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.27/0.99    inference(cnf_transformation,[],[f11])).
% 2.27/0.99  
% 2.27/0.99  fof(f40,plain,(
% 2.27/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))),
% 2.27/0.99    inference(cnf_transformation,[],[f30])).
% 2.27/0.99  
% 2.27/0.99  fof(f44,plain,(
% 2.27/0.99    ( ! [X4] : (k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) | ~r2_hidden(X4,k1_relset_1(sK1,sK1,sK2)) | r1_partfun1(sK2,sK3)) )),
% 2.27/0.99    inference(cnf_transformation,[],[f30])).
% 2.27/0.99  
% 2.27/0.99  fof(f3,axiom,(
% 2.27/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 2.27/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.27/0.99  
% 2.27/0.99  fof(f12,plain,(
% 2.27/0.99    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.27/0.99    inference(ennf_transformation,[],[f3])).
% 2.27/0.99  
% 2.27/0.99  fof(f33,plain,(
% 2.27/0.99    ( ! [X2,X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.27/0.99    inference(cnf_transformation,[],[f12])).
% 2.27/0.99  
% 2.27/0.99  fof(f45,plain,(
% 2.27/0.99    r2_hidden(sK4,k1_relset_1(sK1,sK1,sK2)) | ~r1_partfun1(sK2,sK3)),
% 2.27/0.99    inference(cnf_transformation,[],[f30])).
% 2.27/0.99  
% 2.27/0.99  fof(f37,plain,(
% 2.27/0.99    ( ! [X0,X1] : (r1_partfun1(X0,X1) | k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1)) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.27/0.99    inference(cnf_transformation,[],[f23])).
% 2.27/0.99  
% 2.27/0.99  fof(f46,plain,(
% 2.27/0.99    k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4) | ~r1_partfun1(sK2,sK3)),
% 2.27/0.99    inference(cnf_transformation,[],[f30])).
% 2.27/0.99  
% 2.27/0.99  fof(f39,plain,(
% 2.27/0.99    v1_funct_1(sK2)),
% 2.27/0.99    inference(cnf_transformation,[],[f30])).
% 2.27/0.99  
% 2.27/0.99  cnf(c_0,plain,
% 2.27/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.27/0.99      inference(cnf_transformation,[],[f31]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_6,plain,
% 2.27/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.27/0.99      | ~ r1_partfun1(X1,X2)
% 2.27/0.99      | ~ r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
% 2.27/0.99      | ~ v1_funct_1(X2)
% 2.27/0.99      | ~ v1_funct_1(X1)
% 2.27/0.99      | ~ v1_relat_1(X2)
% 2.27/0.99      | ~ v1_relat_1(X1)
% 2.27/0.99      | k1_funct_1(X2,X0) = k1_funct_1(X1,X0) ),
% 2.27/0.99      inference(cnf_transformation,[],[f35]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_244,plain,
% 2.27/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.27/0.99      | ~ r1_partfun1(X1,X2)
% 2.27/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
% 2.27/0.99      | ~ v1_funct_1(X1)
% 2.27/0.99      | ~ v1_funct_1(X2)
% 2.27/0.99      | ~ v1_relat_1(X1)
% 2.27/0.99      | ~ v1_relat_1(X2)
% 2.27/0.99      | k1_funct_1(X1,X0) = k1_funct_1(X2,X0)
% 2.27/0.99      | k1_relat_1(X2) != X4
% 2.27/0.99      | k1_relat_1(X1) != X3 ),
% 2.27/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_6]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_245,plain,
% 2.27/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.27/0.99      | ~ r1_partfun1(X1,X2)
% 2.27/0.99      | ~ m1_subset_1(k1_relat_1(X1),k1_zfmisc_1(k1_relat_1(X2)))
% 2.27/0.99      | ~ v1_funct_1(X1)
% 2.27/0.99      | ~ v1_funct_1(X2)
% 2.27/0.99      | ~ v1_relat_1(X1)
% 2.27/0.99      | ~ v1_relat_1(X2)
% 2.27/0.99      | k1_funct_1(X1,X0) = k1_funct_1(X2,X0) ),
% 2.27/0.99      inference(unflattening,[status(thm)],[c_244]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_1165,plain,
% 2.27/0.99      ( ~ r2_hidden(X0_45,k1_relat_1(X0_46))
% 2.27/0.99      | ~ r1_partfun1(X0_46,X1_46)
% 2.27/0.99      | ~ m1_subset_1(k1_relat_1(X0_46),k1_zfmisc_1(k1_relat_1(X1_46)))
% 2.27/0.99      | ~ v1_funct_1(X1_46)
% 2.27/0.99      | ~ v1_funct_1(X0_46)
% 2.27/0.99      | ~ v1_relat_1(X1_46)
% 2.27/0.99      | ~ v1_relat_1(X0_46)
% 2.27/0.99      | k1_funct_1(X0_46,X0_45) = k1_funct_1(X1_46,X0_45) ),
% 2.27/0.99      inference(subtyping,[status(esa)],[c_245]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_3038,plain,
% 2.27/0.99      ( ~ r2_hidden(sK4,k1_relat_1(sK2))
% 2.27/0.99      | ~ r1_partfun1(sK2,sK3)
% 2.27/0.99      | ~ m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(k1_relat_1(sK3)))
% 2.27/0.99      | ~ v1_funct_1(sK3)
% 2.27/0.99      | ~ v1_funct_1(sK2)
% 2.27/0.99      | ~ v1_relat_1(sK3)
% 2.27/0.99      | ~ v1_relat_1(sK2)
% 2.27/0.99      | k1_funct_1(sK2,sK4) = k1_funct_1(sK3,sK4) ),
% 2.27/0.99      inference(instantiation,[status(thm)],[c_1165]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_1187,plain,
% 2.27/0.99      ( ~ m1_subset_1(X0_46,X0_47)
% 2.27/0.99      | m1_subset_1(X1_46,X1_47)
% 2.27/0.99      | X1_47 != X0_47
% 2.27/0.99      | X1_46 != X0_46 ),
% 2.27/0.99      theory(equality) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_1976,plain,
% 2.27/0.99      ( m1_subset_1(X0_46,X0_47)
% 2.27/0.99      | ~ m1_subset_1(X1_46,k1_zfmisc_1(sK1))
% 2.27/0.99      | X0_47 != k1_zfmisc_1(sK1)
% 2.27/0.99      | X0_46 != X1_46 ),
% 2.27/0.99      inference(instantiation,[status(thm)],[c_1187]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_2243,plain,
% 2.27/0.99      ( m1_subset_1(X0_46,k1_zfmisc_1(X1_46))
% 2.27/0.99      | ~ m1_subset_1(X2_46,k1_zfmisc_1(sK1))
% 2.27/0.99      | k1_zfmisc_1(X1_46) != k1_zfmisc_1(sK1)
% 2.27/0.99      | X0_46 != X2_46 ),
% 2.27/0.99      inference(instantiation,[status(thm)],[c_1976]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_2485,plain,
% 2.27/0.99      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(sK1))
% 2.27/0.99      | m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(k1_relat_1(sK3)))
% 2.27/0.99      | k1_zfmisc_1(k1_relat_1(sK3)) != k1_zfmisc_1(sK1)
% 2.27/0.99      | k1_relat_1(sK2) != X0_46 ),
% 2.27/0.99      inference(instantiation,[status(thm)],[c_2243]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_2929,plain,
% 2.27/0.99      ( ~ m1_subset_1(k1_relset_1(sK1,sK1,sK2),k1_zfmisc_1(sK1))
% 2.27/0.99      | m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(k1_relat_1(sK3)))
% 2.27/0.99      | k1_zfmisc_1(k1_relat_1(sK3)) != k1_zfmisc_1(sK1)
% 2.27/0.99      | k1_relat_1(sK2) != k1_relset_1(sK1,sK1,sK2) ),
% 2.27/0.99      inference(instantiation,[status(thm)],[c_2485]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_11,negated_conjecture,
% 2.27/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 2.27/0.99      inference(cnf_transformation,[],[f43]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_1172,negated_conjecture,
% 2.27/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 2.27/0.99      inference(subtyping,[status(esa)],[c_11]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_1465,plain,
% 2.27/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 2.27/0.99      inference(predicate_to_equality,[status(thm)],[c_1172]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_3,plain,
% 2.27/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.27/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.27/0.99      inference(cnf_transformation,[],[f34]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_1176,plain,
% 2.27/0.99      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X1_46,X2_46)))
% 2.27/0.99      | k1_relset_1(X1_46,X2_46,X0_46) = k1_relat_1(X0_46) ),
% 2.27/0.99      inference(subtyping,[status(esa)],[c_3]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_1461,plain,
% 2.27/0.99      ( k1_relset_1(X0_46,X1_46,X2_46) = k1_relat_1(X2_46)
% 2.27/0.99      | m1_subset_1(X2_46,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46))) != iProver_top ),
% 2.27/0.99      inference(predicate_to_equality,[status(thm)],[c_1176]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_1741,plain,
% 2.27/0.99      ( k1_relset_1(sK1,sK1,sK3) = k1_relat_1(sK3) ),
% 2.27/0.99      inference(superposition,[status(thm)],[c_1465,c_1461]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_7,plain,
% 2.27/0.99      ( ~ v1_funct_2(X0,X1,X1)
% 2.27/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 2.27/0.99      | ~ v1_funct_1(X0)
% 2.27/0.99      | k1_relset_1(X1,X1,X0) = X1 ),
% 2.27/0.99      inference(cnf_transformation,[],[f38]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_12,negated_conjecture,
% 2.27/0.99      ( v1_funct_2(sK3,sK1,sK1) ),
% 2.27/0.99      inference(cnf_transformation,[],[f42]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_181,plain,
% 2.27/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 2.27/0.99      | ~ v1_funct_1(X0)
% 2.27/0.99      | k1_relset_1(X1,X1,X0) = X1
% 2.27/0.99      | sK1 != X1
% 2.27/0.99      | sK3 != X0 ),
% 2.27/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_12]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_182,plain,
% 2.27/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 2.27/0.99      | ~ v1_funct_1(sK3)
% 2.27/0.99      | k1_relset_1(sK1,sK1,sK3) = sK1 ),
% 2.27/0.99      inference(unflattening,[status(thm)],[c_181]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_13,negated_conjecture,
% 2.27/0.99      ( v1_funct_1(sK3) ),
% 2.27/0.99      inference(cnf_transformation,[],[f41]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_184,plain,
% 2.27/0.99      ( k1_relset_1(sK1,sK1,sK3) = sK1 ),
% 2.27/0.99      inference(global_propositional_subsumption,
% 2.27/0.99                [status(thm)],
% 2.27/0.99                [c_182,c_13,c_11]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_1168,plain,
% 2.27/0.99      ( k1_relset_1(sK1,sK1,sK3) = sK1 ),
% 2.27/0.99      inference(subtyping,[status(esa)],[c_184]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_1746,plain,
% 2.27/0.99      ( k1_relat_1(sK3) = sK1 ),
% 2.27/0.99      inference(light_normalisation,[status(thm)],[c_1741,c_1168]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_5,plain,
% 2.27/0.99      ( r2_hidden(sK0(X0,X1),k1_relat_1(X0))
% 2.27/0.99      | r1_partfun1(X0,X1)
% 2.27/0.99      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 2.27/0.99      | ~ v1_funct_1(X1)
% 2.27/0.99      | ~ v1_funct_1(X0)
% 2.27/0.99      | ~ v1_relat_1(X1)
% 2.27/0.99      | ~ v1_relat_1(X0) ),
% 2.27/0.99      inference(cnf_transformation,[],[f36]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_190,plain,
% 2.27/0.99      ( r2_hidden(sK0(X0,X1),k1_relat_1(X0))
% 2.27/0.99      | r1_partfun1(X0,X1)
% 2.27/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
% 2.27/0.99      | ~ v1_funct_1(X0)
% 2.27/0.99      | ~ v1_funct_1(X1)
% 2.27/0.99      | ~ v1_relat_1(X0)
% 2.27/0.99      | ~ v1_relat_1(X1)
% 2.27/0.99      | k1_relat_1(X1) != X3
% 2.27/0.99      | k1_relat_1(X0) != X2 ),
% 2.27/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_5]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_191,plain,
% 2.27/0.99      ( r2_hidden(sK0(X0,X1),k1_relat_1(X0))
% 2.27/0.99      | r1_partfun1(X0,X1)
% 2.27/0.99      | ~ m1_subset_1(k1_relat_1(X0),k1_zfmisc_1(k1_relat_1(X1)))
% 2.27/0.99      | ~ v1_funct_1(X1)
% 2.27/0.99      | ~ v1_funct_1(X0)
% 2.27/0.99      | ~ v1_relat_1(X1)
% 2.27/0.99      | ~ v1_relat_1(X0) ),
% 2.27/0.99      inference(unflattening,[status(thm)],[c_190]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_1167,plain,
% 2.27/0.99      ( r2_hidden(sK0(X0_46,X1_46),k1_relat_1(X0_46))
% 2.27/0.99      | r1_partfun1(X0_46,X1_46)
% 2.27/0.99      | ~ m1_subset_1(k1_relat_1(X0_46),k1_zfmisc_1(k1_relat_1(X1_46)))
% 2.27/0.99      | ~ v1_funct_1(X1_46)
% 2.27/0.99      | ~ v1_funct_1(X0_46)
% 2.27/0.99      | ~ v1_relat_1(X1_46)
% 2.27/0.99      | ~ v1_relat_1(X0_46) ),
% 2.27/0.99      inference(subtyping,[status(esa)],[c_191]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_1469,plain,
% 2.27/0.99      ( r2_hidden(sK0(X0_46,X1_46),k1_relat_1(X0_46)) = iProver_top
% 2.27/0.99      | r1_partfun1(X0_46,X1_46) = iProver_top
% 2.27/0.99      | m1_subset_1(k1_relat_1(X0_46),k1_zfmisc_1(k1_relat_1(X1_46))) != iProver_top
% 2.27/0.99      | v1_funct_1(X1_46) != iProver_top
% 2.27/0.99      | v1_funct_1(X0_46) != iProver_top
% 2.27/0.99      | v1_relat_1(X0_46) != iProver_top
% 2.27/0.99      | v1_relat_1(X1_46) != iProver_top ),
% 2.27/0.99      inference(predicate_to_equality,[status(thm)],[c_1167]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_2193,plain,
% 2.27/0.99      ( r2_hidden(sK0(X0_46,sK3),k1_relat_1(X0_46)) = iProver_top
% 2.27/0.99      | r1_partfun1(X0_46,sK3) = iProver_top
% 2.27/0.99      | m1_subset_1(k1_relat_1(X0_46),k1_zfmisc_1(sK1)) != iProver_top
% 2.27/0.99      | v1_funct_1(X0_46) != iProver_top
% 2.27/0.99      | v1_funct_1(sK3) != iProver_top
% 2.27/0.99      | v1_relat_1(X0_46) != iProver_top
% 2.27/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.27/0.99      inference(superposition,[status(thm)],[c_1746,c_1469]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_18,plain,
% 2.27/0.99      ( v1_funct_1(sK3) = iProver_top ),
% 2.27/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_20,plain,
% 2.27/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 2.27/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_1,plain,
% 2.27/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.27/0.99      | v1_relat_1(X0) ),
% 2.27/0.99      inference(cnf_transformation,[],[f32]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_1178,plain,
% 2.27/0.99      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X1_46,X2_46)))
% 2.27/0.99      | v1_relat_1(X0_46) ),
% 2.27/0.99      inference(subtyping,[status(esa)],[c_1]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_1586,plain,
% 2.27/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 2.27/0.99      | v1_relat_1(sK3) ),
% 2.27/0.99      inference(instantiation,[status(thm)],[c_1178]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_1587,plain,
% 2.27/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 2.27/0.99      | v1_relat_1(sK3) = iProver_top ),
% 2.27/0.99      inference(predicate_to_equality,[status(thm)],[c_1586]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_2422,plain,
% 2.27/0.99      ( v1_relat_1(X0_46) != iProver_top
% 2.27/0.99      | r2_hidden(sK0(X0_46,sK3),k1_relat_1(X0_46)) = iProver_top
% 2.27/0.99      | r1_partfun1(X0_46,sK3) = iProver_top
% 2.27/0.99      | m1_subset_1(k1_relat_1(X0_46),k1_zfmisc_1(sK1)) != iProver_top
% 2.27/0.99      | v1_funct_1(X0_46) != iProver_top ),
% 2.27/0.99      inference(global_propositional_subsumption,
% 2.27/0.99                [status(thm)],
% 2.27/0.99                [c_2193,c_18,c_20,c_1587]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_2423,plain,
% 2.27/0.99      ( r2_hidden(sK0(X0_46,sK3),k1_relat_1(X0_46)) = iProver_top
% 2.27/0.99      | r1_partfun1(X0_46,sK3) = iProver_top
% 2.27/0.99      | m1_subset_1(k1_relat_1(X0_46),k1_zfmisc_1(sK1)) != iProver_top
% 2.27/0.99      | v1_funct_1(X0_46) != iProver_top
% 2.27/0.99      | v1_relat_1(X0_46) != iProver_top ),
% 2.27/0.99      inference(renaming,[status(thm)],[c_2422]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_14,negated_conjecture,
% 2.27/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 2.27/0.99      inference(cnf_transformation,[],[f40]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_1170,negated_conjecture,
% 2.27/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 2.27/0.99      inference(subtyping,[status(esa)],[c_14]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_1467,plain,
% 2.27/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 2.27/0.99      inference(predicate_to_equality,[status(thm)],[c_1170]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_1742,plain,
% 2.27/0.99      ( k1_relset_1(sK1,sK1,sK2) = k1_relat_1(sK2) ),
% 2.27/0.99      inference(superposition,[status(thm)],[c_1467,c_1461]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_10,negated_conjecture,
% 2.27/0.99      ( ~ r2_hidden(X0,k1_relset_1(sK1,sK1,sK2))
% 2.27/0.99      | r1_partfun1(sK2,sK3)
% 2.27/0.99      | k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0) ),
% 2.27/0.99      inference(cnf_transformation,[],[f44]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_1173,negated_conjecture,
% 2.27/0.99      ( ~ r2_hidden(X0_45,k1_relset_1(sK1,sK1,sK2))
% 2.27/0.99      | r1_partfun1(sK2,sK3)
% 2.27/0.99      | k1_funct_1(sK2,X0_45) = k1_funct_1(sK3,X0_45) ),
% 2.27/0.99      inference(subtyping,[status(esa)],[c_10]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_1464,plain,
% 2.27/0.99      ( k1_funct_1(sK2,X0_45) = k1_funct_1(sK3,X0_45)
% 2.27/0.99      | r2_hidden(X0_45,k1_relset_1(sK1,sK1,sK2)) != iProver_top
% 2.27/0.99      | r1_partfun1(sK2,sK3) = iProver_top ),
% 2.27/0.99      inference(predicate_to_equality,[status(thm)],[c_1173]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_1955,plain,
% 2.27/0.99      ( k1_funct_1(sK3,X0_45) = k1_funct_1(sK2,X0_45)
% 2.27/0.99      | r2_hidden(X0_45,k1_relat_1(sK2)) != iProver_top
% 2.27/0.99      | r1_partfun1(sK2,sK3) = iProver_top ),
% 2.27/0.99      inference(demodulation,[status(thm)],[c_1742,c_1464]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_2434,plain,
% 2.27/0.99      ( k1_funct_1(sK2,sK0(sK2,sK3)) = k1_funct_1(sK3,sK0(sK2,sK3))
% 2.27/0.99      | r1_partfun1(sK2,sK3) = iProver_top
% 2.27/0.99      | m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK1)) != iProver_top
% 2.27/0.99      | v1_funct_1(sK2) != iProver_top
% 2.27/0.99      | v1_relat_1(sK2) != iProver_top ),
% 2.27/0.99      inference(superposition,[status(thm)],[c_2423,c_1955]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_2445,plain,
% 2.27/0.99      ( r1_partfun1(sK2,sK3)
% 2.27/0.99      | ~ m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK1))
% 2.27/0.99      | ~ v1_funct_1(sK2)
% 2.27/0.99      | ~ v1_relat_1(sK2)
% 2.27/0.99      | k1_funct_1(sK2,sK0(sK2,sK3)) = k1_funct_1(sK3,sK0(sK2,sK3)) ),
% 2.27/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_2434]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_1181,plain,( X0_46 = X0_46 ),theory(equality) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_2385,plain,
% 2.27/0.99      ( k1_relat_1(sK2) = k1_relat_1(sK2) ),
% 2.27/0.99      inference(instantiation,[status(thm)],[c_1181]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_1184,plain,
% 2.27/0.99      ( X0_46 != X1_46 | X2_46 != X1_46 | X2_46 = X0_46 ),
% 2.27/0.99      theory(equality) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_1871,plain,
% 2.27/0.99      ( X0_46 != X1_46
% 2.27/0.99      | X0_46 = k1_relset_1(sK1,sK1,sK2)
% 2.27/0.99      | k1_relset_1(sK1,sK1,sK2) != X1_46 ),
% 2.27/0.99      inference(instantiation,[status(thm)],[c_1184]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_2159,plain,
% 2.27/0.99      ( X0_46 = k1_relset_1(sK1,sK1,sK2)
% 2.27/0.99      | X0_46 != k1_relat_1(sK2)
% 2.27/0.99      | k1_relset_1(sK1,sK1,sK2) != k1_relat_1(sK2) ),
% 2.27/0.99      inference(instantiation,[status(thm)],[c_1871]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_2384,plain,
% 2.27/0.99      ( k1_relset_1(sK1,sK1,sK2) != k1_relat_1(sK2)
% 2.27/0.99      | k1_relat_1(sK2) = k1_relset_1(sK1,sK1,sK2)
% 2.27/0.99      | k1_relat_1(sK2) != k1_relat_1(sK2) ),
% 2.27/0.99      inference(instantiation,[status(thm)],[c_2159]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_1186,plain,
% 2.27/0.99      ( k1_zfmisc_1(X0_46) = k1_zfmisc_1(X1_46) | X0_46 != X1_46 ),
% 2.27/0.99      theory(equality) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_1776,plain,
% 2.27/0.99      ( k1_zfmisc_1(X0_46) = k1_zfmisc_1(sK1) | X0_46 != sK1 ),
% 2.27/0.99      inference(instantiation,[status(thm)],[c_1186]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_2073,plain,
% 2.27/0.99      ( k1_zfmisc_1(k1_relat_1(sK3)) = k1_zfmisc_1(sK1)
% 2.27/0.99      | k1_relat_1(sK3) != sK1 ),
% 2.27/0.99      inference(instantiation,[status(thm)],[c_1776]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_2,plain,
% 2.27/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.27/0.99      | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 2.27/0.99      inference(cnf_transformation,[],[f33]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_1177,plain,
% 2.27/0.99      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X1_46,X2_46)))
% 2.27/0.99      | m1_subset_1(k1_relset_1(X1_46,X2_46,X0_46),k1_zfmisc_1(X1_46)) ),
% 2.27/0.99      inference(subtyping,[status(esa)],[c_2]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_1460,plain,
% 2.27/0.99      ( m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X1_46,X2_46))) != iProver_top
% 2.27/0.99      | m1_subset_1(k1_relset_1(X1_46,X2_46,X0_46),k1_zfmisc_1(X1_46)) = iProver_top ),
% 2.27/0.99      inference(predicate_to_equality,[status(thm)],[c_1177]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_1971,plain,
% 2.27/0.99      ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK1)) = iProver_top
% 2.27/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
% 2.27/0.99      inference(superposition,[status(thm)],[c_1742,c_1460]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_1972,plain,
% 2.27/0.99      ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK1))
% 2.27/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 2.27/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_1971]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_9,negated_conjecture,
% 2.27/0.99      ( r2_hidden(sK4,k1_relset_1(sK1,sK1,sK2))
% 2.27/0.99      | ~ r1_partfun1(sK2,sK3) ),
% 2.27/0.99      inference(cnf_transformation,[],[f45]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_1174,negated_conjecture,
% 2.27/0.99      ( r2_hidden(sK4,k1_relset_1(sK1,sK1,sK2))
% 2.27/0.99      | ~ r1_partfun1(sK2,sK3) ),
% 2.27/0.99      inference(subtyping,[status(esa)],[c_9]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_1463,plain,
% 2.27/0.99      ( r2_hidden(sK4,k1_relset_1(sK1,sK1,sK2)) = iProver_top
% 2.27/0.99      | r1_partfun1(sK2,sK3) != iProver_top ),
% 2.27/0.99      inference(predicate_to_equality,[status(thm)],[c_1174]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_1956,plain,
% 2.27/0.99      ( r2_hidden(sK4,k1_relat_1(sK2)) = iProver_top
% 2.27/0.99      | r1_partfun1(sK2,sK3) != iProver_top ),
% 2.27/0.99      inference(demodulation,[status(thm)],[c_1742,c_1463]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_1970,plain,
% 2.27/0.99      ( r2_hidden(sK4,k1_relat_1(sK2)) | ~ r1_partfun1(sK2,sK3) ),
% 2.27/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_1956]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_4,plain,
% 2.27/0.99      ( r1_partfun1(X0,X1)
% 2.27/0.99      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 2.27/0.99      | ~ v1_funct_1(X1)
% 2.27/0.99      | ~ v1_funct_1(X0)
% 2.27/0.99      | ~ v1_relat_1(X1)
% 2.27/0.99      | ~ v1_relat_1(X0)
% 2.27/0.99      | k1_funct_1(X1,sK0(X0,X1)) != k1_funct_1(X0,sK0(X0,X1)) ),
% 2.27/0.99      inference(cnf_transformation,[],[f37]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_217,plain,
% 2.27/0.99      ( r1_partfun1(X0,X1)
% 2.27/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
% 2.27/0.99      | ~ v1_funct_1(X0)
% 2.27/0.99      | ~ v1_funct_1(X1)
% 2.27/0.99      | ~ v1_relat_1(X0)
% 2.27/0.99      | ~ v1_relat_1(X1)
% 2.27/0.99      | k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1))
% 2.27/0.99      | k1_relat_1(X1) != X3
% 2.27/0.99      | k1_relat_1(X0) != X2 ),
% 2.27/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_4]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_218,plain,
% 2.27/0.99      ( r1_partfun1(X0,X1)
% 2.27/0.99      | ~ m1_subset_1(k1_relat_1(X0),k1_zfmisc_1(k1_relat_1(X1)))
% 2.27/0.99      | ~ v1_funct_1(X1)
% 2.27/0.99      | ~ v1_funct_1(X0)
% 2.27/0.99      | ~ v1_relat_1(X1)
% 2.27/0.99      | ~ v1_relat_1(X0)
% 2.27/0.99      | k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1)) ),
% 2.27/0.99      inference(unflattening,[status(thm)],[c_217]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_1166,plain,
% 2.27/0.99      ( r1_partfun1(X0_46,X1_46)
% 2.27/0.99      | ~ m1_subset_1(k1_relat_1(X0_46),k1_zfmisc_1(k1_relat_1(X1_46)))
% 2.27/0.99      | ~ v1_funct_1(X1_46)
% 2.27/0.99      | ~ v1_funct_1(X0_46)
% 2.27/0.99      | ~ v1_relat_1(X1_46)
% 2.27/0.99      | ~ v1_relat_1(X0_46)
% 2.27/0.99      | k1_funct_1(X0_46,sK0(X0_46,X1_46)) != k1_funct_1(X1_46,sK0(X0_46,X1_46)) ),
% 2.27/0.99      inference(subtyping,[status(esa)],[c_218]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_1637,plain,
% 2.27/0.99      ( r1_partfun1(X0_46,sK3)
% 2.27/0.99      | ~ m1_subset_1(k1_relat_1(X0_46),k1_zfmisc_1(k1_relat_1(sK3)))
% 2.27/0.99      | ~ v1_funct_1(X0_46)
% 2.27/0.99      | ~ v1_funct_1(sK3)
% 2.27/0.99      | ~ v1_relat_1(X0_46)
% 2.27/0.99      | ~ v1_relat_1(sK3)
% 2.27/0.99      | k1_funct_1(X0_46,sK0(X0_46,sK3)) != k1_funct_1(sK3,sK0(X0_46,sK3)) ),
% 2.27/0.99      inference(instantiation,[status(thm)],[c_1166]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_1706,plain,
% 2.27/0.99      ( r1_partfun1(sK2,sK3)
% 2.27/0.99      | ~ m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(k1_relat_1(sK3)))
% 2.27/0.99      | ~ v1_funct_1(sK3)
% 2.27/0.99      | ~ v1_funct_1(sK2)
% 2.27/0.99      | ~ v1_relat_1(sK3)
% 2.27/0.99      | ~ v1_relat_1(sK2)
% 2.27/0.99      | k1_funct_1(sK2,sK0(sK2,sK3)) != k1_funct_1(sK3,sK0(sK2,sK3)) ),
% 2.27/0.99      inference(instantiation,[status(thm)],[c_1637]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_1611,plain,
% 2.27/0.99      ( m1_subset_1(k1_relset_1(sK1,sK1,sK2),k1_zfmisc_1(sK1))
% 2.27/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 2.27/0.99      inference(instantiation,[status(thm)],[c_1177]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_1605,plain,
% 2.27/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 2.27/0.99      | k1_relset_1(sK1,sK1,sK2) = k1_relat_1(sK2) ),
% 2.27/0.99      inference(instantiation,[status(thm)],[c_1176]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_1589,plain,
% 2.27/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 2.27/0.99      | v1_relat_1(sK2) ),
% 2.27/0.99      inference(instantiation,[status(thm)],[c_1178]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_8,negated_conjecture,
% 2.27/0.99      ( ~ r1_partfun1(sK2,sK3)
% 2.27/0.99      | k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4) ),
% 2.27/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_1175,negated_conjecture,
% 2.27/0.99      ( ~ r1_partfun1(sK2,sK3)
% 2.27/0.99      | k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4) ),
% 2.27/0.99      inference(subtyping,[status(esa)],[c_8]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_15,negated_conjecture,
% 2.27/0.99      ( v1_funct_1(sK2) ),
% 2.27/0.99      inference(cnf_transformation,[],[f39]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(contradiction,plain,
% 2.27/1.00      ( $false ),
% 2.27/1.00      inference(minisat,
% 2.27/1.00                [status(thm)],
% 2.27/1.00                [c_3038,c_2929,c_2445,c_2385,c_2384,c_2073,c_1972,c_1970,
% 2.27/1.00                 c_1746,c_1706,c_1611,c_1605,c_1589,c_1586,c_1175,c_11,
% 2.27/1.00                 c_13,c_14,c_15]) ).
% 2.27/1.00  
% 2.27/1.00  
% 2.27/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.27/1.00  
% 2.27/1.00  ------                               Statistics
% 2.27/1.00  
% 2.27/1.00  ------ General
% 2.27/1.00  
% 2.27/1.00  abstr_ref_over_cycles:                  0
% 2.27/1.00  abstr_ref_under_cycles:                 0
% 2.27/1.00  gc_basic_clause_elim:                   0
% 2.27/1.00  forced_gc_time:                         0
% 2.27/1.00  parsing_time:                           0.009
% 2.27/1.00  unif_index_cands_time:                  0.
% 2.27/1.00  unif_index_add_time:                    0.
% 2.27/1.00  orderings_time:                         0.
% 2.27/1.00  out_proof_time:                         0.013
% 2.27/1.00  total_time:                             0.142
% 2.27/1.00  num_of_symbols:                         52
% 2.27/1.00  num_of_terms:                           2440
% 2.27/1.00  
% 2.27/1.00  ------ Preprocessing
% 2.27/1.00  
% 2.27/1.00  num_of_splits:                          0
% 2.27/1.00  num_of_split_atoms:                     0
% 2.27/1.00  num_of_reused_defs:                     0
% 2.27/1.00  num_eq_ax_congr_red:                    12
% 2.27/1.00  num_of_sem_filtered_clauses:            1
% 2.27/1.00  num_of_subtypes:                        4
% 2.27/1.00  monotx_restored_types:                  0
% 2.27/1.00  sat_num_of_epr_types:                   0
% 2.27/1.00  sat_num_of_non_cyclic_types:            0
% 2.27/1.00  sat_guarded_non_collapsed_types:        0
% 2.27/1.00  num_pure_diseq_elim:                    0
% 2.27/1.00  simp_replaced_by:                       0
% 2.27/1.00  res_preprocessed:                       87
% 2.27/1.00  prep_upred:                             0
% 2.27/1.00  prep_unflattend:                        44
% 2.27/1.00  smt_new_axioms:                         0
% 2.27/1.00  pred_elim_cands:                        5
% 2.27/1.00  pred_elim:                              2
% 2.27/1.00  pred_elim_cl:                           2
% 2.27/1.00  pred_elim_cycles:                       6
% 2.27/1.00  merged_defs:                            0
% 2.27/1.00  merged_defs_ncl:                        0
% 2.27/1.00  bin_hyper_res:                          0
% 2.27/1.00  prep_cycles:                            4
% 2.27/1.00  pred_elim_time:                         0.018
% 2.27/1.00  splitting_time:                         0.
% 2.27/1.00  sem_filter_time:                        0.
% 2.27/1.00  monotx_time:                            0.
% 2.27/1.00  subtype_inf_time:                       0.
% 2.27/1.00  
% 2.27/1.00  ------ Problem properties
% 2.27/1.00  
% 2.27/1.00  clauses:                                14
% 2.27/1.00  conjectures:                            7
% 2.27/1.00  epr:                                    2
% 2.27/1.00  horn:                                   12
% 2.27/1.00  ground:                                 7
% 2.27/1.00  unary:                                  5
% 2.27/1.00  binary:                                 5
% 2.27/1.00  lits:                                   40
% 2.27/1.00  lits_eq:                                6
% 2.27/1.00  fd_pure:                                0
% 2.27/1.00  fd_pseudo:                              0
% 2.27/1.00  fd_cond:                                0
% 2.27/1.00  fd_pseudo_cond:                         0
% 2.27/1.00  ac_symbols:                             0
% 2.27/1.00  
% 2.27/1.00  ------ Propositional Solver
% 2.27/1.00  
% 2.27/1.00  prop_solver_calls:                      29
% 2.27/1.00  prop_fast_solver_calls:                 894
% 2.27/1.00  smt_solver_calls:                       0
% 2.27/1.00  smt_fast_solver_calls:                  0
% 2.27/1.00  prop_num_of_clauses:                    789
% 2.27/1.00  prop_preprocess_simplified:             3167
% 2.27/1.00  prop_fo_subsumed:                       41
% 2.27/1.00  prop_solver_time:                       0.
% 2.27/1.00  smt_solver_time:                        0.
% 2.27/1.00  smt_fast_solver_time:                   0.
% 2.27/1.00  prop_fast_solver_time:                  0.
% 2.27/1.00  prop_unsat_core_time:                   0.
% 2.27/1.00  
% 2.27/1.00  ------ QBF
% 2.27/1.00  
% 2.27/1.00  qbf_q_res:                              0
% 2.27/1.00  qbf_num_tautologies:                    0
% 2.27/1.00  qbf_prep_cycles:                        0
% 2.27/1.00  
% 2.27/1.00  ------ BMC1
% 2.27/1.00  
% 2.27/1.00  bmc1_current_bound:                     -1
% 2.27/1.00  bmc1_last_solved_bound:                 -1
% 2.27/1.00  bmc1_unsat_core_size:                   -1
% 2.27/1.00  bmc1_unsat_core_parents_size:           -1
% 2.27/1.00  bmc1_merge_next_fun:                    0
% 2.27/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.27/1.00  
% 2.27/1.00  ------ Instantiation
% 2.27/1.00  
% 2.27/1.00  inst_num_of_clauses:                    247
% 2.27/1.00  inst_num_in_passive:                    63
% 2.27/1.00  inst_num_in_active:                     181
% 2.27/1.00  inst_num_in_unprocessed:                3
% 2.27/1.00  inst_num_of_loops:                      202
% 2.27/1.00  inst_num_of_learning_restarts:          0
% 2.27/1.00  inst_num_moves_active_passive:          15
% 2.27/1.00  inst_lit_activity:                      0
% 2.27/1.00  inst_lit_activity_moves:                0
% 2.27/1.00  inst_num_tautologies:                   0
% 2.27/1.00  inst_num_prop_implied:                  0
% 2.27/1.00  inst_num_existing_simplified:           0
% 2.27/1.00  inst_num_eq_res_simplified:             0
% 2.27/1.00  inst_num_child_elim:                    0
% 2.27/1.00  inst_num_of_dismatching_blockings:      85
% 2.27/1.00  inst_num_of_non_proper_insts:           297
% 2.27/1.00  inst_num_of_duplicates:                 0
% 2.27/1.00  inst_inst_num_from_inst_to_res:         0
% 2.27/1.00  inst_dismatching_checking_time:         0.
% 2.27/1.00  
% 2.27/1.00  ------ Resolution
% 2.27/1.00  
% 2.27/1.00  res_num_of_clauses:                     0
% 2.27/1.00  res_num_in_passive:                     0
% 2.27/1.00  res_num_in_active:                      0
% 2.27/1.00  res_num_of_loops:                       91
% 2.27/1.00  res_forward_subset_subsumed:            31
% 2.27/1.00  res_backward_subset_subsumed:           4
% 2.27/1.00  res_forward_subsumed:                   0
% 2.27/1.00  res_backward_subsumed:                  0
% 2.27/1.00  res_forward_subsumption_resolution:     0
% 2.27/1.00  res_backward_subsumption_resolution:    0
% 2.27/1.00  res_clause_to_clause_subsumption:       139
% 2.27/1.00  res_orphan_elimination:                 0
% 2.27/1.00  res_tautology_del:                      32
% 2.27/1.00  res_num_eq_res_simplified:              0
% 2.27/1.00  res_num_sel_changes:                    0
% 2.27/1.00  res_moves_from_active_to_pass:          0
% 2.27/1.00  
% 2.27/1.00  ------ Superposition
% 2.27/1.00  
% 2.27/1.00  sup_time_total:                         0.
% 2.27/1.00  sup_time_generating:                    0.
% 2.27/1.00  sup_time_sim_full:                      0.
% 2.27/1.00  sup_time_sim_immed:                     0.
% 2.27/1.00  
% 2.27/1.00  sup_num_of_clauses:                     42
% 2.27/1.00  sup_num_in_active:                      38
% 2.27/1.00  sup_num_in_passive:                     4
% 2.27/1.00  sup_num_of_loops:                       40
% 2.27/1.00  sup_fw_superposition:                   27
% 2.27/1.00  sup_bw_superposition:                   4
% 2.27/1.00  sup_immediate_simplified:               4
% 2.27/1.00  sup_given_eliminated:                   0
% 2.27/1.00  comparisons_done:                       0
% 2.27/1.00  comparisons_avoided:                    0
% 2.27/1.00  
% 2.27/1.00  ------ Simplifications
% 2.27/1.00  
% 2.27/1.00  
% 2.27/1.00  sim_fw_subset_subsumed:                 1
% 2.27/1.00  sim_bw_subset_subsumed:                 0
% 2.27/1.00  sim_fw_subsumed:                        0
% 2.27/1.00  sim_bw_subsumed:                        0
% 2.27/1.00  sim_fw_subsumption_res:                 0
% 2.27/1.00  sim_bw_subsumption_res:                 0
% 2.27/1.00  sim_tautology_del:                      1
% 2.27/1.00  sim_eq_tautology_del:                   2
% 2.27/1.00  sim_eq_res_simp:                        0
% 2.27/1.00  sim_fw_demodulated:                     0
% 2.27/1.00  sim_bw_demodulated:                     2
% 2.27/1.00  sim_light_normalised:                   3
% 2.27/1.00  sim_joinable_taut:                      0
% 2.27/1.00  sim_joinable_simp:                      0
% 2.27/1.00  sim_ac_normalised:                      0
% 2.27/1.00  sim_smt_subsumption:                    0
% 2.27/1.00  
%------------------------------------------------------------------------------
