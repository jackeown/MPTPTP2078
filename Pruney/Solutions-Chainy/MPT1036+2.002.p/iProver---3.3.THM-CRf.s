%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:08:41 EST 2020

% Result     : Theorem 1.62s
% Output     : CNFRefutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :  134 (1237 expanded)
%              Number of clauses        :   87 ( 333 expanded)
%              Number of leaves         :   14 ( 300 expanded)
%              Depth                    :   24
%              Number of atoms          :  530 (8872 expanded)
%              Number of equality atoms :  197 (1903 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f21,plain,(
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

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1))
        & r2_hidden(sK0(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_partfun1(X0,X1)
      | k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1))
      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f13])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(nnf_transformation,[],[f19])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f27,plain,(
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
    inference(rectify,[],[f26])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( k1_funct_1(X1,X3) != k1_funct_1(X2,X3)
          & r2_hidden(X3,k1_relset_1(X0,X0,X1)) )
     => ( k1_funct_1(X1,sK4) != k1_funct_1(X2,sK4)
        & r2_hidden(sK4,k1_relset_1(X0,X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
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

fof(f28,plain,
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

fof(f31,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f27,f30,f29,f28])).

fof(f45,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f31])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f44,plain,(
    v1_funct_2(sK3,sK1,sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f43,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_partfun1(X0,X1)
      | r2_hidden(sK0(X0,X1),k1_relat_1(X0))
      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f42,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f31])).

fof(f46,plain,(
    ! [X4] :
      ( k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)
      | ~ r2_hidden(X4,k1_relset_1(sK1,sK1,sK2))
      | r1_partfun1(sK2,sK3) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f47,plain,
    ( r2_hidden(sK4,k1_relset_1(sK1,sK1,sK2))
    | ~ r1_partfun1(sK2,sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f41,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f48,plain,
    ( k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4)
    | ~ r1_partfun1(sK2,sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f37,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ r1_partfun1(X0,X1)
      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_5,plain,
    ( r1_partfun1(X0,X1)
    | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k1_funct_1(X1,sK0(X0,X1)) != k1_funct_1(X0,sK0(X0,X1)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1662,plain,
    ( r1_partfun1(X0_47,X1_47)
    | ~ r1_tarski(k1_relat_1(X0_47),k1_relat_1(X1_47))
    | ~ v1_funct_1(X1_47)
    | ~ v1_funct_1(X0_47)
    | ~ v1_relat_1(X1_47)
    | ~ v1_relat_1(X0_47)
    | k1_funct_1(X1_47,sK0(X0_47,X1_47)) != k1_funct_1(X0_47,sK0(X0_47,X1_47)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_2821,plain,
    ( r1_partfun1(X0_47,sK3)
    | ~ r1_tarski(k1_relat_1(X0_47),k1_relat_1(sK3))
    | ~ v1_funct_1(X0_47)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(X0_47)
    | ~ v1_relat_1(sK3)
    | k1_funct_1(sK3,sK0(X0_47,sK3)) != k1_funct_1(X0_47,sK0(X0_47,sK3)) ),
    inference(instantiation,[status(thm)],[c_1662])).

cnf(c_2828,plain,
    ( r1_partfun1(sK2,sK3)
    | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | k1_funct_1(sK3,sK0(sK2,sK3)) != k1_funct_1(sK2,sK0(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_2821])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_200,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_12])).

cnf(c_201,plain,
    ( k1_relset_1(X0,X1,sK3) = k1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) ),
    inference(unflattening,[status(thm)],[c_200])).

cnf(c_1653,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
    | k1_relset_1(X0_46,X1_46,sK3) = k1_relat_1(sK3) ),
    inference(subtyping,[status(esa)],[c_201])).

cnf(c_2079,plain,
    ( k1_relset_1(sK1,sK1,sK3) = k1_relat_1(sK3) ),
    inference(equality_resolution,[status(thm)],[c_1653])).

cnf(c_8,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k1_relset_1(X1,X1,X0) = X1 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_13,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_191,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k1_relset_1(X1,X1,X0) = X1
    | sK1 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_13])).

cnf(c_192,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK3)
    | k1_relset_1(sK1,sK1,sK3) = sK1 ),
    inference(unflattening,[status(thm)],[c_191])).

cnf(c_14,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_194,plain,
    ( k1_relset_1(sK1,sK1,sK3) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_192,c_14,c_12])).

cnf(c_1654,plain,
    ( k1_relset_1(sK1,sK1,sK3) = sK1 ),
    inference(subtyping,[status(esa)],[c_194])).

cnf(c_2080,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2079,c_1654])).

cnf(c_6,plain,
    ( r2_hidden(sK0(X0,X1),k1_relat_1(X0))
    | r1_partfun1(X0,X1)
    | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1661,plain,
    ( r2_hidden(sK0(X0_47,X1_47),k1_relat_1(X0_47))
    | r1_partfun1(X0_47,X1_47)
    | ~ r1_tarski(k1_relat_1(X0_47),k1_relat_1(X1_47))
    | ~ v1_funct_1(X1_47)
    | ~ v1_funct_1(X0_47)
    | ~ v1_relat_1(X1_47)
    | ~ v1_relat_1(X0_47) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1911,plain,
    ( r2_hidden(sK0(X0_47,X1_47),k1_relat_1(X0_47)) = iProver_top
    | r1_partfun1(X0_47,X1_47) = iProver_top
    | r1_tarski(k1_relat_1(X0_47),k1_relat_1(X1_47)) != iProver_top
    | v1_funct_1(X1_47) != iProver_top
    | v1_funct_1(X0_47) != iProver_top
    | v1_relat_1(X0_47) != iProver_top
    | v1_relat_1(X1_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1661])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_233,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_15])).

cnf(c_234,plain,
    ( k1_relset_1(X0,X1,sK2) = k1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) ),
    inference(unflattening,[status(thm)],[c_233])).

cnf(c_1651,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
    | k1_relset_1(X0_46,X1_46,sK2) = k1_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_234])).

cnf(c_2066,plain,
    ( k1_relset_1(sK1,sK1,sK2) = k1_relat_1(sK2) ),
    inference(equality_resolution,[status(thm)],[c_1651])).

cnf(c_11,negated_conjecture,
    ( ~ r2_hidden(X0,k1_relset_1(sK1,sK1,sK2))
    | r1_partfun1(sK2,sK3)
    | k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1657,negated_conjecture,
    ( ~ r2_hidden(X0_50,k1_relset_1(sK1,sK1,sK2))
    | r1_partfun1(sK2,sK3)
    | k1_funct_1(sK2,X0_50) = k1_funct_1(sK3,X0_50) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1915,plain,
    ( k1_funct_1(sK2,X0_50) = k1_funct_1(sK3,X0_50)
    | r2_hidden(X0_50,k1_relset_1(sK1,sK1,sK2)) != iProver_top
    | r1_partfun1(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1657])).

cnf(c_2343,plain,
    ( k1_funct_1(sK3,X0_50) = k1_funct_1(sK2,X0_50)
    | r2_hidden(X0_50,k1_relat_1(sK2)) != iProver_top
    | r1_partfun1(sK2,sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2066,c_1915])).

cnf(c_10,negated_conjecture,
    ( r2_hidden(sK4,k1_relset_1(sK1,sK1,sK2))
    | ~ r1_partfun1(sK2,sK3) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1658,negated_conjecture,
    ( r2_hidden(sK4,k1_relset_1(sK1,sK1,sK2))
    | ~ r1_partfun1(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1914,plain,
    ( r2_hidden(sK4,k1_relset_1(sK1,sK1,sK2)) = iProver_top
    | r1_partfun1(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1658])).

cnf(c_2344,plain,
    ( r2_hidden(sK4,k1_relat_1(sK2)) = iProver_top
    | r1_partfun1(sK2,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2066,c_1914])).

cnf(c_16,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_17,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_19,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_9,negated_conjecture,
    ( ~ r1_partfun1(sK2,sK3)
    | k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1659,negated_conjecture,
    ( ~ r1_partfun1(sK2,sK3)
    | k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1695,plain,
    ( k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4)
    | r1_partfun1(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1659])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_221,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_12])).

cnf(c_222,plain,
    ( v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) ),
    inference(unflattening,[status(thm)],[c_221])).

cnf(c_1652,plain,
    ( v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) ),
    inference(subtyping,[status(esa)],[c_222])).

cnf(c_1703,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1652])).

cnf(c_1705,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
    | v1_relat_1(sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1703])).

cnf(c_254,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_15])).

cnf(c_255,plain,
    ( v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) ),
    inference(unflattening,[status(thm)],[c_254])).

cnf(c_1650,plain,
    ( v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) ),
    inference(subtyping,[status(esa)],[c_255])).

cnf(c_1707,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1650])).

cnf(c_1709,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
    | v1_relat_1(sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1707])).

cnf(c_1,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v4_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_242,plain,
    ( v4_relat_1(X0,X1)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_15])).

cnf(c_243,plain,
    ( v4_relat_1(sK2,X0)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) ),
    inference(unflattening,[status(thm)],[c_242])).

cnf(c_301,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | X2 != X1
    | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_243])).

cnf(c_302,plain,
    ( r1_tarski(k1_relat_1(sK2),X0)
    | ~ v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) ),
    inference(unflattening,[status(thm)],[c_301])).

cnf(c_306,plain,
    ( r1_tarski(k1_relat_1(sK2),X0)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_302,c_255])).

cnf(c_1648,plain,
    ( r1_tarski(k1_relat_1(sK2),X0_46)
    | k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) ),
    inference(subtyping,[status(esa)],[c_306])).

cnf(c_1713,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
    | r1_tarski(k1_relat_1(sK2),X0_46) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1648])).

cnf(c_1715,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
    | r1_tarski(k1_relat_1(sK2),sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1713])).

cnf(c_1665,plain,
    ( X0_48 = X0_48 ),
    theory(equality)).

cnf(c_2040,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) ),
    inference(instantiation,[status(thm)],[c_1665])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r1_partfun1(X1,X2)
    | ~ r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X2,X0) = k1_funct_1(X1,X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1660,plain,
    ( ~ r2_hidden(X0_50,k1_relat_1(X0_47))
    | ~ r1_partfun1(X0_47,X1_47)
    | ~ r1_tarski(k1_relat_1(X0_47),k1_relat_1(X1_47))
    | ~ v1_funct_1(X1_47)
    | ~ v1_funct_1(X0_47)
    | ~ v1_relat_1(X1_47)
    | ~ v1_relat_1(X0_47)
    | k1_funct_1(X1_47,X0_50) = k1_funct_1(X0_47,X0_50) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1912,plain,
    ( k1_funct_1(X0_47,X0_50) = k1_funct_1(X1_47,X0_50)
    | r2_hidden(X0_50,k1_relat_1(X1_47)) != iProver_top
    | r1_partfun1(X1_47,X0_47) != iProver_top
    | r1_tarski(k1_relat_1(X1_47),k1_relat_1(X0_47)) != iProver_top
    | v1_funct_1(X0_47) != iProver_top
    | v1_funct_1(X1_47) != iProver_top
    | v1_relat_1(X1_47) != iProver_top
    | v1_relat_1(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1660])).

cnf(c_2274,plain,
    ( k1_funct_1(X0_47,X0_50) = k1_funct_1(sK3,X0_50)
    | r2_hidden(X0_50,k1_relat_1(X0_47)) != iProver_top
    | r1_partfun1(X0_47,sK3) != iProver_top
    | r1_tarski(k1_relat_1(X0_47),sK1) != iProver_top
    | v1_funct_1(X0_47) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(X0_47) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2080,c_1912])).

cnf(c_2334,plain,
    ( k1_funct_1(sK2,sK4) = k1_funct_1(sK3,sK4)
    | r2_hidden(sK4,k1_relat_1(sK2)) != iProver_top
    | r1_partfun1(sK2,sK3) != iProver_top
    | r1_tarski(k1_relat_1(sK2),sK1) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2274])).

cnf(c_2422,plain,
    ( r1_partfun1(sK2,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2344,c_17,c_19,c_1695,c_1705,c_1709,c_1715,c_2040,c_2334])).

cnf(c_2572,plain,
    ( r2_hidden(X0_50,k1_relat_1(sK2)) != iProver_top
    | k1_funct_1(sK3,X0_50) = k1_funct_1(sK2,X0_50) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2343,c_17,c_19,c_1695,c_1705,c_1709,c_1715,c_2040,c_2334,c_2344])).

cnf(c_2573,plain,
    ( k1_funct_1(sK3,X0_50) = k1_funct_1(sK2,X0_50)
    | r2_hidden(X0_50,k1_relat_1(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2572])).

cnf(c_2580,plain,
    ( k1_funct_1(sK3,sK0(sK2,X0_47)) = k1_funct_1(sK2,sK0(sK2,X0_47))
    | r1_partfun1(sK2,X0_47) = iProver_top
    | r1_tarski(k1_relat_1(sK2),k1_relat_1(X0_47)) != iProver_top
    | v1_funct_1(X0_47) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(X0_47) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1911,c_2573])).

cnf(c_2782,plain,
    ( v1_relat_1(X0_47) != iProver_top
    | k1_funct_1(sK3,sK0(sK2,X0_47)) = k1_funct_1(sK2,sK0(sK2,X0_47))
    | r1_partfun1(sK2,X0_47) = iProver_top
    | r1_tarski(k1_relat_1(sK2),k1_relat_1(X0_47)) != iProver_top
    | v1_funct_1(X0_47) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2580,c_17,c_1709,c_2040])).

cnf(c_2783,plain,
    ( k1_funct_1(sK3,sK0(sK2,X0_47)) = k1_funct_1(sK2,sK0(sK2,X0_47))
    | r1_partfun1(sK2,X0_47) = iProver_top
    | r1_tarski(k1_relat_1(sK2),k1_relat_1(X0_47)) != iProver_top
    | v1_funct_1(X0_47) != iProver_top
    | v1_relat_1(X0_47) != iProver_top ),
    inference(renaming,[status(thm)],[c_2782])).

cnf(c_2791,plain,
    ( k1_funct_1(sK3,sK0(sK2,sK3)) = k1_funct_1(sK2,sK0(sK2,sK3))
    | r1_partfun1(sK2,sK3) = iProver_top
    | r1_tarski(k1_relat_1(sK2),sK1) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2080,c_2783])).

cnf(c_1671,plain,
    ( ~ r1_tarski(X0_46,X1_46)
    | r1_tarski(X2_46,X3_46)
    | X2_46 != X0_46
    | X3_46 != X1_46 ),
    theory(equality)).

cnf(c_2067,plain,
    ( r1_tarski(X0_46,X1_46)
    | ~ r1_tarski(k1_relat_1(sK2),X2_46)
    | X1_46 != X2_46
    | X0_46 != k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1671])).

cnf(c_2148,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),X0_46)
    | r1_tarski(k1_relat_1(sK2),X1_46)
    | X1_46 != X0_46
    | k1_relat_1(sK2) != k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_2067])).

cnf(c_2222,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),X0_46)
    | r1_tarski(k1_relat_1(sK2),k1_relat_1(X0_47))
    | k1_relat_1(X0_47) != X0_46
    | k1_relat_1(sK2) != k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_2148])).

cnf(c_2524,plain,
    ( r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3))
    | ~ r1_tarski(k1_relat_1(sK2),sK1)
    | k1_relat_1(sK3) != sK1
    | k1_relat_1(sK2) != k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_2222])).

cnf(c_2424,plain,
    ( ~ r1_partfun1(sK2,sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2422])).

cnf(c_1664,plain,
    ( X0_46 = X0_46 ),
    theory(equality)).

cnf(c_2149,plain,
    ( k1_relat_1(sK2) = k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1664])).

cnf(c_1714,plain,
    ( r1_tarski(k1_relat_1(sK2),sK1)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) ),
    inference(instantiation,[status(thm)],[c_1648])).

cnf(c_1708,plain,
    ( v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) ),
    inference(instantiation,[status(thm)],[c_1650])).

cnf(c_1704,plain,
    ( v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) ),
    inference(instantiation,[status(thm)],[c_1652])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2828,c_2791,c_2524,c_2424,c_2422,c_2149,c_2080,c_2040,c_1715,c_1714,c_1708,c_1705,c_1704,c_19,c_14,c_16])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n025.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:56:35 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.62/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/0.98  
% 1.62/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.62/0.98  
% 1.62/0.98  ------  iProver source info
% 1.62/0.98  
% 1.62/0.98  git: date: 2020-06-30 10:37:57 +0100
% 1.62/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.62/0.98  git: non_committed_changes: false
% 1.62/0.98  git: last_make_outside_of_git: false
% 1.62/0.98  
% 1.62/0.98  ------ 
% 1.62/0.98  
% 1.62/0.98  ------ Input Options
% 1.62/0.98  
% 1.62/0.98  --out_options                           all
% 1.62/0.98  --tptp_safe_out                         true
% 1.62/0.98  --problem_path                          ""
% 1.62/0.98  --include_path                          ""
% 1.62/0.98  --clausifier                            res/vclausify_rel
% 1.62/0.98  --clausifier_options                    --mode clausify
% 1.62/0.98  --stdin                                 false
% 1.62/0.98  --stats_out                             all
% 1.62/0.98  
% 1.62/0.98  ------ General Options
% 1.62/0.98  
% 1.62/0.98  --fof                                   false
% 1.62/0.98  --time_out_real                         305.
% 1.62/0.98  --time_out_virtual                      -1.
% 1.62/0.98  --symbol_type_check                     false
% 1.62/0.98  --clausify_out                          false
% 1.62/0.98  --sig_cnt_out                           false
% 1.62/0.98  --trig_cnt_out                          false
% 1.62/0.98  --trig_cnt_out_tolerance                1.
% 1.62/0.98  --trig_cnt_out_sk_spl                   false
% 1.62/0.98  --abstr_cl_out                          false
% 1.62/0.98  
% 1.62/0.98  ------ Global Options
% 1.62/0.98  
% 1.62/0.98  --schedule                              default
% 1.62/0.98  --add_important_lit                     false
% 1.62/0.98  --prop_solver_per_cl                    1000
% 1.62/0.98  --min_unsat_core                        false
% 1.62/0.98  --soft_assumptions                      false
% 1.62/0.98  --soft_lemma_size                       3
% 1.62/0.98  --prop_impl_unit_size                   0
% 1.62/0.98  --prop_impl_unit                        []
% 1.62/0.98  --share_sel_clauses                     true
% 1.62/0.98  --reset_solvers                         false
% 1.62/0.98  --bc_imp_inh                            [conj_cone]
% 1.62/0.98  --conj_cone_tolerance                   3.
% 1.62/0.98  --extra_neg_conj                        none
% 1.62/0.98  --large_theory_mode                     true
% 1.62/0.98  --prolific_symb_bound                   200
% 1.62/0.98  --lt_threshold                          2000
% 1.62/0.98  --clause_weak_htbl                      true
% 1.62/0.98  --gc_record_bc_elim                     false
% 1.62/0.98  
% 1.62/0.98  ------ Preprocessing Options
% 1.62/0.98  
% 1.62/0.98  --preprocessing_flag                    true
% 1.62/0.98  --time_out_prep_mult                    0.1
% 1.62/0.98  --splitting_mode                        input
% 1.62/0.98  --splitting_grd                         true
% 1.62/0.98  --splitting_cvd                         false
% 1.62/0.98  --splitting_cvd_svl                     false
% 1.62/0.98  --splitting_nvd                         32
% 1.62/0.98  --sub_typing                            true
% 1.62/0.98  --prep_gs_sim                           true
% 1.62/0.98  --prep_unflatten                        true
% 1.62/0.98  --prep_res_sim                          true
% 1.62/0.98  --prep_upred                            true
% 1.62/0.98  --prep_sem_filter                       exhaustive
% 1.62/0.98  --prep_sem_filter_out                   false
% 1.62/0.98  --pred_elim                             true
% 1.62/0.98  --res_sim_input                         true
% 1.62/0.98  --eq_ax_congr_red                       true
% 1.62/0.98  --pure_diseq_elim                       true
% 1.62/0.98  --brand_transform                       false
% 1.62/0.98  --non_eq_to_eq                          false
% 1.62/0.98  --prep_def_merge                        true
% 1.62/0.98  --prep_def_merge_prop_impl              false
% 1.62/0.98  --prep_def_merge_mbd                    true
% 1.62/0.98  --prep_def_merge_tr_red                 false
% 1.62/0.98  --prep_def_merge_tr_cl                  false
% 1.62/0.98  --smt_preprocessing                     true
% 1.62/0.98  --smt_ac_axioms                         fast
% 1.62/0.98  --preprocessed_out                      false
% 1.62/0.98  --preprocessed_stats                    false
% 1.62/0.98  
% 1.62/0.98  ------ Abstraction refinement Options
% 1.62/0.98  
% 1.62/0.98  --abstr_ref                             []
% 1.62/0.98  --abstr_ref_prep                        false
% 1.62/0.98  --abstr_ref_until_sat                   false
% 1.62/0.98  --abstr_ref_sig_restrict                funpre
% 1.62/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.62/0.98  --abstr_ref_under                       []
% 1.62/0.98  
% 1.62/0.98  ------ SAT Options
% 1.62/0.98  
% 1.62/0.98  --sat_mode                              false
% 1.62/0.98  --sat_fm_restart_options                ""
% 1.62/0.98  --sat_gr_def                            false
% 1.62/0.98  --sat_epr_types                         true
% 1.62/0.98  --sat_non_cyclic_types                  false
% 1.62/0.98  --sat_finite_models                     false
% 1.62/0.98  --sat_fm_lemmas                         false
% 1.62/0.98  --sat_fm_prep                           false
% 1.62/0.98  --sat_fm_uc_incr                        true
% 1.62/0.98  --sat_out_model                         small
% 1.62/0.98  --sat_out_clauses                       false
% 1.62/0.98  
% 1.62/0.98  ------ QBF Options
% 1.62/0.98  
% 1.62/0.98  --qbf_mode                              false
% 1.62/0.98  --qbf_elim_univ                         false
% 1.62/0.98  --qbf_dom_inst                          none
% 1.62/0.98  --qbf_dom_pre_inst                      false
% 1.62/0.98  --qbf_sk_in                             false
% 1.62/0.98  --qbf_pred_elim                         true
% 1.62/0.98  --qbf_split                             512
% 1.62/0.98  
% 1.62/0.98  ------ BMC1 Options
% 1.62/0.98  
% 1.62/0.98  --bmc1_incremental                      false
% 1.62/0.98  --bmc1_axioms                           reachable_all
% 1.62/0.98  --bmc1_min_bound                        0
% 1.62/0.98  --bmc1_max_bound                        -1
% 1.62/0.98  --bmc1_max_bound_default                -1
% 1.62/0.98  --bmc1_symbol_reachability              true
% 1.62/0.98  --bmc1_property_lemmas                  false
% 1.62/0.98  --bmc1_k_induction                      false
% 1.62/0.98  --bmc1_non_equiv_states                 false
% 1.62/0.98  --bmc1_deadlock                         false
% 1.62/0.98  --bmc1_ucm                              false
% 1.62/0.98  --bmc1_add_unsat_core                   none
% 1.62/0.98  --bmc1_unsat_core_children              false
% 1.62/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.62/0.98  --bmc1_out_stat                         full
% 1.62/0.98  --bmc1_ground_init                      false
% 1.62/0.98  --bmc1_pre_inst_next_state              false
% 1.62/0.98  --bmc1_pre_inst_state                   false
% 1.62/0.98  --bmc1_pre_inst_reach_state             false
% 1.62/0.98  --bmc1_out_unsat_core                   false
% 1.62/0.98  --bmc1_aig_witness_out                  false
% 1.62/0.98  --bmc1_verbose                          false
% 1.62/0.98  --bmc1_dump_clauses_tptp                false
% 1.62/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.62/0.98  --bmc1_dump_file                        -
% 1.62/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.62/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.62/0.98  --bmc1_ucm_extend_mode                  1
% 1.62/0.98  --bmc1_ucm_init_mode                    2
% 1.62/0.98  --bmc1_ucm_cone_mode                    none
% 1.62/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.62/0.98  --bmc1_ucm_relax_model                  4
% 1.62/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.62/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.62/0.98  --bmc1_ucm_layered_model                none
% 1.62/0.98  --bmc1_ucm_max_lemma_size               10
% 1.62/0.98  
% 1.62/0.98  ------ AIG Options
% 1.62/0.98  
% 1.62/0.98  --aig_mode                              false
% 1.62/0.98  
% 1.62/0.98  ------ Instantiation Options
% 1.62/0.98  
% 1.62/0.98  --instantiation_flag                    true
% 1.62/0.98  --inst_sos_flag                         false
% 1.62/0.98  --inst_sos_phase                        true
% 1.62/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.62/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.62/0.98  --inst_lit_sel_side                     num_symb
% 1.62/0.98  --inst_solver_per_active                1400
% 1.62/0.98  --inst_solver_calls_frac                1.
% 1.62/0.98  --inst_passive_queue_type               priority_queues
% 1.62/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.62/0.98  --inst_passive_queues_freq              [25;2]
% 1.62/0.98  --inst_dismatching                      true
% 1.62/0.98  --inst_eager_unprocessed_to_passive     true
% 1.62/0.98  --inst_prop_sim_given                   true
% 1.62/0.98  --inst_prop_sim_new                     false
% 1.62/0.98  --inst_subs_new                         false
% 1.62/0.98  --inst_eq_res_simp                      false
% 1.62/0.98  --inst_subs_given                       false
% 1.62/0.98  --inst_orphan_elimination               true
% 1.62/0.98  --inst_learning_loop_flag               true
% 1.62/0.98  --inst_learning_start                   3000
% 1.62/0.98  --inst_learning_factor                  2
% 1.62/0.98  --inst_start_prop_sim_after_learn       3
% 1.62/0.98  --inst_sel_renew                        solver
% 1.62/0.98  --inst_lit_activity_flag                true
% 1.62/0.98  --inst_restr_to_given                   false
% 1.62/0.98  --inst_activity_threshold               500
% 1.62/0.98  --inst_out_proof                        true
% 1.62/0.98  
% 1.62/0.98  ------ Resolution Options
% 1.62/0.98  
% 1.62/0.98  --resolution_flag                       true
% 1.62/0.98  --res_lit_sel                           adaptive
% 1.62/0.98  --res_lit_sel_side                      none
% 1.62/0.98  --res_ordering                          kbo
% 1.62/0.98  --res_to_prop_solver                    active
% 1.62/0.98  --res_prop_simpl_new                    false
% 1.62/0.98  --res_prop_simpl_given                  true
% 1.62/0.98  --res_passive_queue_type                priority_queues
% 1.62/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.62/0.98  --res_passive_queues_freq               [15;5]
% 1.62/0.98  --res_forward_subs                      full
% 1.62/0.98  --res_backward_subs                     full
% 1.62/0.98  --res_forward_subs_resolution           true
% 1.62/0.98  --res_backward_subs_resolution          true
% 1.62/0.98  --res_orphan_elimination                true
% 1.62/0.98  --res_time_limit                        2.
% 1.62/0.98  --res_out_proof                         true
% 1.62/0.98  
% 1.62/0.98  ------ Superposition Options
% 1.62/0.98  
% 1.62/0.98  --superposition_flag                    true
% 1.62/0.98  --sup_passive_queue_type                priority_queues
% 1.62/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.62/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.62/0.98  --demod_completeness_check              fast
% 1.62/0.98  --demod_use_ground                      true
% 1.62/0.98  --sup_to_prop_solver                    passive
% 1.62/0.98  --sup_prop_simpl_new                    true
% 1.62/0.98  --sup_prop_simpl_given                  true
% 1.62/0.98  --sup_fun_splitting                     false
% 1.62/0.98  --sup_smt_interval                      50000
% 1.62/0.98  
% 1.62/0.98  ------ Superposition Simplification Setup
% 1.62/0.98  
% 1.62/0.98  --sup_indices_passive                   []
% 1.62/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.62/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.62/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.62/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.62/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.62/0.98  --sup_full_bw                           [BwDemod]
% 1.62/0.98  --sup_immed_triv                        [TrivRules]
% 1.62/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.62/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.62/0.98  --sup_immed_bw_main                     []
% 1.62/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.62/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.62/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.62/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.62/0.98  
% 1.62/0.98  ------ Combination Options
% 1.62/0.98  
% 1.62/0.98  --comb_res_mult                         3
% 1.62/0.98  --comb_sup_mult                         2
% 1.62/0.98  --comb_inst_mult                        10
% 1.62/0.98  
% 1.62/0.98  ------ Debug Options
% 1.62/0.98  
% 1.62/0.98  --dbg_backtrace                         false
% 1.62/0.98  --dbg_dump_prop_clauses                 false
% 1.62/0.98  --dbg_dump_prop_clauses_file            -
% 1.62/0.98  --dbg_out_stat                          false
% 1.62/0.98  ------ Parsing...
% 1.62/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.62/0.98  
% 1.62/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 1.62/0.98  
% 1.62/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.62/0.98  
% 1.62/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.62/0.98  ------ Proving...
% 1.62/0.98  ------ Problem Properties 
% 1.62/0.98  
% 1.62/0.98  
% 1.62/0.98  clauses                                 15
% 1.62/0.98  conjectures                             5
% 1.62/0.98  EPR                                     2
% 1.62/0.98  Horn                                    13
% 1.62/0.98  unary                                   3
% 1.62/0.98  binary                                  8
% 1.62/0.98  lits                                    44
% 1.62/0.98  lits eq                                 13
% 1.62/0.98  fd_pure                                 0
% 1.62/0.98  fd_pseudo                               0
% 1.62/0.98  fd_cond                                 0
% 1.62/0.98  fd_pseudo_cond                          0
% 1.62/0.98  AC symbols                              0
% 1.62/0.98  
% 1.62/0.98  ------ Schedule dynamic 5 is on 
% 1.62/0.98  
% 1.62/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.62/0.98  
% 1.62/0.98  
% 1.62/0.98  ------ 
% 1.62/0.98  Current options:
% 1.62/0.98  ------ 
% 1.62/0.98  
% 1.62/0.98  ------ Input Options
% 1.62/0.98  
% 1.62/0.98  --out_options                           all
% 1.62/0.98  --tptp_safe_out                         true
% 1.62/0.98  --problem_path                          ""
% 1.62/0.98  --include_path                          ""
% 1.62/0.98  --clausifier                            res/vclausify_rel
% 1.62/0.98  --clausifier_options                    --mode clausify
% 1.62/0.98  --stdin                                 false
% 1.62/0.98  --stats_out                             all
% 1.62/0.98  
% 1.62/0.98  ------ General Options
% 1.62/0.98  
% 1.62/0.98  --fof                                   false
% 1.62/0.98  --time_out_real                         305.
% 1.62/0.98  --time_out_virtual                      -1.
% 1.62/0.98  --symbol_type_check                     false
% 1.62/0.98  --clausify_out                          false
% 1.62/0.98  --sig_cnt_out                           false
% 1.62/0.98  --trig_cnt_out                          false
% 1.62/0.98  --trig_cnt_out_tolerance                1.
% 1.62/0.98  --trig_cnt_out_sk_spl                   false
% 1.62/0.98  --abstr_cl_out                          false
% 1.62/0.98  
% 1.62/0.98  ------ Global Options
% 1.62/0.98  
% 1.62/0.98  --schedule                              default
% 1.62/0.98  --add_important_lit                     false
% 1.62/0.98  --prop_solver_per_cl                    1000
% 1.62/0.98  --min_unsat_core                        false
% 1.62/0.98  --soft_assumptions                      false
% 1.62/0.98  --soft_lemma_size                       3
% 1.62/0.98  --prop_impl_unit_size                   0
% 1.62/0.98  --prop_impl_unit                        []
% 1.62/0.98  --share_sel_clauses                     true
% 1.62/0.98  --reset_solvers                         false
% 1.62/0.98  --bc_imp_inh                            [conj_cone]
% 1.62/0.98  --conj_cone_tolerance                   3.
% 1.62/0.98  --extra_neg_conj                        none
% 1.62/0.98  --large_theory_mode                     true
% 1.62/0.98  --prolific_symb_bound                   200
% 1.62/0.98  --lt_threshold                          2000
% 1.62/0.98  --clause_weak_htbl                      true
% 1.62/0.98  --gc_record_bc_elim                     false
% 1.62/0.98  
% 1.62/0.98  ------ Preprocessing Options
% 1.62/0.98  
% 1.62/0.98  --preprocessing_flag                    true
% 1.62/0.98  --time_out_prep_mult                    0.1
% 1.62/0.98  --splitting_mode                        input
% 1.62/0.98  --splitting_grd                         true
% 1.62/0.98  --splitting_cvd                         false
% 1.62/0.98  --splitting_cvd_svl                     false
% 1.62/0.98  --splitting_nvd                         32
% 1.62/0.98  --sub_typing                            true
% 1.62/0.98  --prep_gs_sim                           true
% 1.62/0.98  --prep_unflatten                        true
% 1.62/0.98  --prep_res_sim                          true
% 1.62/0.98  --prep_upred                            true
% 1.62/0.98  --prep_sem_filter                       exhaustive
% 1.62/0.98  --prep_sem_filter_out                   false
% 1.62/0.98  --pred_elim                             true
% 1.62/0.98  --res_sim_input                         true
% 1.62/0.98  --eq_ax_congr_red                       true
% 1.62/0.98  --pure_diseq_elim                       true
% 1.62/0.98  --brand_transform                       false
% 1.62/0.98  --non_eq_to_eq                          false
% 1.62/0.98  --prep_def_merge                        true
% 1.62/0.98  --prep_def_merge_prop_impl              false
% 1.62/0.98  --prep_def_merge_mbd                    true
% 1.62/0.98  --prep_def_merge_tr_red                 false
% 1.62/0.98  --prep_def_merge_tr_cl                  false
% 1.62/0.98  --smt_preprocessing                     true
% 1.62/0.98  --smt_ac_axioms                         fast
% 1.62/0.98  --preprocessed_out                      false
% 1.62/0.98  --preprocessed_stats                    false
% 1.62/0.98  
% 1.62/0.98  ------ Abstraction refinement Options
% 1.62/0.98  
% 1.62/0.98  --abstr_ref                             []
% 1.62/0.98  --abstr_ref_prep                        false
% 1.62/0.98  --abstr_ref_until_sat                   false
% 1.62/0.98  --abstr_ref_sig_restrict                funpre
% 1.62/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.62/0.98  --abstr_ref_under                       []
% 1.62/0.98  
% 1.62/0.98  ------ SAT Options
% 1.62/0.98  
% 1.62/0.98  --sat_mode                              false
% 1.62/0.98  --sat_fm_restart_options                ""
% 1.62/0.98  --sat_gr_def                            false
% 1.62/0.98  --sat_epr_types                         true
% 1.62/0.98  --sat_non_cyclic_types                  false
% 1.62/0.98  --sat_finite_models                     false
% 1.62/0.98  --sat_fm_lemmas                         false
% 1.62/0.98  --sat_fm_prep                           false
% 1.62/0.98  --sat_fm_uc_incr                        true
% 1.62/0.98  --sat_out_model                         small
% 1.62/0.98  --sat_out_clauses                       false
% 1.62/0.98  
% 1.62/0.98  ------ QBF Options
% 1.62/0.98  
% 1.62/0.98  --qbf_mode                              false
% 1.62/0.98  --qbf_elim_univ                         false
% 1.62/0.98  --qbf_dom_inst                          none
% 1.62/0.98  --qbf_dom_pre_inst                      false
% 1.62/0.98  --qbf_sk_in                             false
% 1.62/0.98  --qbf_pred_elim                         true
% 1.62/0.98  --qbf_split                             512
% 1.62/0.98  
% 1.62/0.98  ------ BMC1 Options
% 1.62/0.98  
% 1.62/0.98  --bmc1_incremental                      false
% 1.62/0.98  --bmc1_axioms                           reachable_all
% 1.62/0.98  --bmc1_min_bound                        0
% 1.62/0.98  --bmc1_max_bound                        -1
% 1.62/0.98  --bmc1_max_bound_default                -1
% 1.62/0.98  --bmc1_symbol_reachability              true
% 1.62/0.98  --bmc1_property_lemmas                  false
% 1.62/0.98  --bmc1_k_induction                      false
% 1.62/0.98  --bmc1_non_equiv_states                 false
% 1.62/0.98  --bmc1_deadlock                         false
% 1.62/0.98  --bmc1_ucm                              false
% 1.62/0.98  --bmc1_add_unsat_core                   none
% 1.62/0.98  --bmc1_unsat_core_children              false
% 1.62/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.62/0.98  --bmc1_out_stat                         full
% 1.62/0.98  --bmc1_ground_init                      false
% 1.62/0.98  --bmc1_pre_inst_next_state              false
% 1.62/0.98  --bmc1_pre_inst_state                   false
% 1.62/0.98  --bmc1_pre_inst_reach_state             false
% 1.62/0.98  --bmc1_out_unsat_core                   false
% 1.62/0.98  --bmc1_aig_witness_out                  false
% 1.62/0.98  --bmc1_verbose                          false
% 1.62/0.98  --bmc1_dump_clauses_tptp                false
% 1.62/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.62/0.98  --bmc1_dump_file                        -
% 1.62/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.62/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.62/0.98  --bmc1_ucm_extend_mode                  1
% 1.62/0.98  --bmc1_ucm_init_mode                    2
% 1.62/0.98  --bmc1_ucm_cone_mode                    none
% 1.62/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.62/0.98  --bmc1_ucm_relax_model                  4
% 1.62/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.62/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.62/0.98  --bmc1_ucm_layered_model                none
% 1.62/0.98  --bmc1_ucm_max_lemma_size               10
% 1.62/0.98  
% 1.62/0.98  ------ AIG Options
% 1.62/0.98  
% 1.62/0.98  --aig_mode                              false
% 1.62/0.98  
% 1.62/0.98  ------ Instantiation Options
% 1.62/0.98  
% 1.62/0.98  --instantiation_flag                    true
% 1.62/0.98  --inst_sos_flag                         false
% 1.62/0.98  --inst_sos_phase                        true
% 1.62/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.62/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.62/0.98  --inst_lit_sel_side                     none
% 1.62/0.98  --inst_solver_per_active                1400
% 1.62/0.98  --inst_solver_calls_frac                1.
% 1.62/0.98  --inst_passive_queue_type               priority_queues
% 1.62/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.62/0.98  --inst_passive_queues_freq              [25;2]
% 1.62/0.98  --inst_dismatching                      true
% 1.62/0.98  --inst_eager_unprocessed_to_passive     true
% 1.62/0.98  --inst_prop_sim_given                   true
% 1.62/0.98  --inst_prop_sim_new                     false
% 1.62/0.98  --inst_subs_new                         false
% 1.62/0.98  --inst_eq_res_simp                      false
% 1.62/0.98  --inst_subs_given                       false
% 1.62/0.98  --inst_orphan_elimination               true
% 1.62/0.98  --inst_learning_loop_flag               true
% 1.62/0.98  --inst_learning_start                   3000
% 1.62/0.98  --inst_learning_factor                  2
% 1.62/0.98  --inst_start_prop_sim_after_learn       3
% 1.62/0.98  --inst_sel_renew                        solver
% 1.62/0.98  --inst_lit_activity_flag                true
% 1.62/0.98  --inst_restr_to_given                   false
% 1.62/0.98  --inst_activity_threshold               500
% 1.62/0.98  --inst_out_proof                        true
% 1.62/0.98  
% 1.62/0.98  ------ Resolution Options
% 1.62/0.98  
% 1.62/0.98  --resolution_flag                       false
% 1.62/0.98  --res_lit_sel                           adaptive
% 1.62/0.98  --res_lit_sel_side                      none
% 1.62/0.98  --res_ordering                          kbo
% 1.62/0.98  --res_to_prop_solver                    active
% 1.62/0.98  --res_prop_simpl_new                    false
% 1.62/0.98  --res_prop_simpl_given                  true
% 1.62/0.98  --res_passive_queue_type                priority_queues
% 1.62/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.62/0.98  --res_passive_queues_freq               [15;5]
% 1.62/0.98  --res_forward_subs                      full
% 1.62/0.98  --res_backward_subs                     full
% 1.62/0.98  --res_forward_subs_resolution           true
% 1.62/0.98  --res_backward_subs_resolution          true
% 1.62/0.98  --res_orphan_elimination                true
% 1.62/0.98  --res_time_limit                        2.
% 1.62/0.98  --res_out_proof                         true
% 1.62/0.98  
% 1.62/0.98  ------ Superposition Options
% 1.62/0.98  
% 1.62/0.98  --superposition_flag                    true
% 1.62/0.98  --sup_passive_queue_type                priority_queues
% 1.62/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.62/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.62/0.98  --demod_completeness_check              fast
% 1.62/0.98  --demod_use_ground                      true
% 1.62/0.98  --sup_to_prop_solver                    passive
% 1.62/0.98  --sup_prop_simpl_new                    true
% 1.62/0.98  --sup_prop_simpl_given                  true
% 1.62/0.98  --sup_fun_splitting                     false
% 1.62/0.98  --sup_smt_interval                      50000
% 1.62/0.98  
% 1.62/0.98  ------ Superposition Simplification Setup
% 1.62/0.98  
% 1.62/0.98  --sup_indices_passive                   []
% 1.62/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.62/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.62/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.62/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.62/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.62/0.98  --sup_full_bw                           [BwDemod]
% 1.62/0.98  --sup_immed_triv                        [TrivRules]
% 1.62/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.62/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.62/0.98  --sup_immed_bw_main                     []
% 1.62/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.62/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.62/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.62/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.62/0.98  
% 1.62/0.98  ------ Combination Options
% 1.62/0.98  
% 1.62/0.98  --comb_res_mult                         3
% 1.62/0.98  --comb_sup_mult                         2
% 1.62/0.98  --comb_inst_mult                        10
% 1.62/0.98  
% 1.62/0.98  ------ Debug Options
% 1.62/0.98  
% 1.62/0.98  --dbg_backtrace                         false
% 1.62/0.98  --dbg_dump_prop_clauses                 false
% 1.62/0.98  --dbg_dump_prop_clauses_file            -
% 1.62/0.98  --dbg_out_stat                          false
% 1.62/0.98  
% 1.62/0.98  
% 1.62/0.98  
% 1.62/0.98  
% 1.62/0.98  ------ Proving...
% 1.62/0.98  
% 1.62/0.98  
% 1.62/0.98  % SZS status Theorem for theBenchmark.p
% 1.62/0.98  
% 1.62/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 1.62/0.98  
% 1.62/0.98  fof(f5,axiom,(
% 1.62/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) => (r1_partfun1(X0,X1) <=> ! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2))))))),
% 1.62/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.62/0.98  
% 1.62/0.98  fof(f14,plain,(
% 1.62/0.98    ! [X0] : (! [X1] : (((r1_partfun1(X0,X1) <=> ! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0)))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.62/0.98    inference(ennf_transformation,[],[f5])).
% 1.62/0.98  
% 1.62/0.98  fof(f15,plain,(
% 1.62/0.98    ! [X0] : (! [X1] : ((r1_partfun1(X0,X1) <=> ! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0)))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.62/0.98    inference(flattening,[],[f14])).
% 1.62/0.98  
% 1.62/0.98  fof(f21,plain,(
% 1.62/0.98    ! [X0] : (! [X1] : (((r1_partfun1(X0,X1) | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0)))) & (! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0))) | ~r1_partfun1(X0,X1))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.62/0.98    inference(nnf_transformation,[],[f15])).
% 1.62/0.98  
% 1.62/0.98  fof(f22,plain,(
% 1.62/0.98    ! [X0] : (! [X1] : (((r1_partfun1(X0,X1) | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0)))) & (! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r1_partfun1(X0,X1))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.62/0.98    inference(rectify,[],[f21])).
% 1.62/0.98  
% 1.62/0.98  fof(f23,plain,(
% 1.62/0.98    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1)) & r2_hidden(sK0(X0,X1),k1_relat_1(X0))))),
% 1.62/0.98    introduced(choice_axiom,[])).
% 1.62/0.98  
% 1.62/0.98  fof(f24,plain,(
% 1.62/0.98    ! [X0] : (! [X1] : (((r1_partfun1(X0,X1) | (k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1)) & r2_hidden(sK0(X0,X1),k1_relat_1(X0)))) & (! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r1_partfun1(X0,X1))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.62/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).
% 1.62/0.98  
% 1.62/0.98  fof(f39,plain,(
% 1.62/0.98    ( ! [X0,X1] : (r1_partfun1(X0,X1) | k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1)) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.62/0.98    inference(cnf_transformation,[],[f24])).
% 1.62/0.98  
% 1.62/0.98  fof(f4,axiom,(
% 1.62/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 1.62/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.62/0.98  
% 1.62/0.98  fof(f13,plain,(
% 1.62/0.98    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.62/0.98    inference(ennf_transformation,[],[f4])).
% 1.62/0.99  
% 1.62/0.99  fof(f36,plain,(
% 1.62/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.62/0.99    inference(cnf_transformation,[],[f13])).
% 1.62/0.99  
% 1.62/0.99  fof(f7,conjecture,(
% 1.62/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r1_partfun1(X1,X2) <=> ! [X3] : (r2_hidden(X3,k1_relset_1(X0,X0,X1)) => k1_funct_1(X1,X3) = k1_funct_1(X2,X3)))))),
% 1.62/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.62/0.99  
% 1.62/0.99  fof(f8,negated_conjecture,(
% 1.62/0.99    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r1_partfun1(X1,X2) <=> ! [X3] : (r2_hidden(X3,k1_relset_1(X0,X0,X1)) => k1_funct_1(X1,X3) = k1_funct_1(X2,X3)))))),
% 1.62/0.99    inference(negated_conjecture,[],[f7])).
% 1.62/0.99  
% 1.62/0.99  fof(f18,plain,(
% 1.62/0.99    ? [X0,X1] : (? [X2] : ((r1_partfun1(X1,X2) <~> ! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(X2,X3) | ~r2_hidden(X3,k1_relset_1(X0,X0,X1)))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1)))),
% 1.62/0.99    inference(ennf_transformation,[],[f8])).
% 1.62/0.99  
% 1.62/0.99  fof(f19,plain,(
% 1.62/0.99    ? [X0,X1] : (? [X2] : ((r1_partfun1(X1,X2) <~> ! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(X2,X3) | ~r2_hidden(X3,k1_relset_1(X0,X0,X1)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1))),
% 1.62/0.99    inference(flattening,[],[f18])).
% 1.62/0.99  
% 1.62/0.99  fof(f25,plain,(
% 1.62/0.99    ? [X0,X1] : (? [X2] : (((? [X3] : (k1_funct_1(X1,X3) != k1_funct_1(X2,X3) & r2_hidden(X3,k1_relset_1(X0,X0,X1))) | ~r1_partfun1(X1,X2)) & (! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(X2,X3) | ~r2_hidden(X3,k1_relset_1(X0,X0,X1))) | r1_partfun1(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1))),
% 1.62/0.99    inference(nnf_transformation,[],[f19])).
% 1.62/0.99  
% 1.62/0.99  fof(f26,plain,(
% 1.62/0.99    ? [X0,X1] : (? [X2] : ((? [X3] : (k1_funct_1(X1,X3) != k1_funct_1(X2,X3) & r2_hidden(X3,k1_relset_1(X0,X0,X1))) | ~r1_partfun1(X1,X2)) & (! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(X2,X3) | ~r2_hidden(X3,k1_relset_1(X0,X0,X1))) | r1_partfun1(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1))),
% 1.62/0.99    inference(flattening,[],[f25])).
% 1.62/0.99  
% 1.62/0.99  fof(f27,plain,(
% 1.62/0.99    ? [X0,X1] : (? [X2] : ((? [X3] : (k1_funct_1(X1,X3) != k1_funct_1(X2,X3) & r2_hidden(X3,k1_relset_1(X0,X0,X1))) | ~r1_partfun1(X1,X2)) & (! [X4] : (k1_funct_1(X1,X4) = k1_funct_1(X2,X4) | ~r2_hidden(X4,k1_relset_1(X0,X0,X1))) | r1_partfun1(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1))),
% 1.62/0.99    inference(rectify,[],[f26])).
% 1.62/0.99  
% 1.62/0.99  fof(f30,plain,(
% 1.62/0.99    ( ! [X2,X0,X1] : (? [X3] : (k1_funct_1(X1,X3) != k1_funct_1(X2,X3) & r2_hidden(X3,k1_relset_1(X0,X0,X1))) => (k1_funct_1(X1,sK4) != k1_funct_1(X2,sK4) & r2_hidden(sK4,k1_relset_1(X0,X0,X1)))) )),
% 1.62/0.99    introduced(choice_axiom,[])).
% 1.62/0.99  
% 1.62/0.99  fof(f29,plain,(
% 1.62/0.99    ( ! [X0,X1] : (? [X2] : ((? [X3] : (k1_funct_1(X1,X3) != k1_funct_1(X2,X3) & r2_hidden(X3,k1_relset_1(X0,X0,X1))) | ~r1_partfun1(X1,X2)) & (! [X4] : (k1_funct_1(X1,X4) = k1_funct_1(X2,X4) | ~r2_hidden(X4,k1_relset_1(X0,X0,X1))) | r1_partfun1(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((? [X3] : (k1_funct_1(sK3,X3) != k1_funct_1(X1,X3) & r2_hidden(X3,k1_relset_1(X0,X0,X1))) | ~r1_partfun1(X1,sK3)) & (! [X4] : (k1_funct_1(sK3,X4) = k1_funct_1(X1,X4) | ~r2_hidden(X4,k1_relset_1(X0,X0,X1))) | r1_partfun1(X1,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(sK3,X0,X0) & v1_funct_1(sK3))) )),
% 1.62/0.99    introduced(choice_axiom,[])).
% 1.62/0.99  
% 1.62/0.99  fof(f28,plain,(
% 1.62/0.99    ? [X0,X1] : (? [X2] : ((? [X3] : (k1_funct_1(X1,X3) != k1_funct_1(X2,X3) & r2_hidden(X3,k1_relset_1(X0,X0,X1))) | ~r1_partfun1(X1,X2)) & (! [X4] : (k1_funct_1(X1,X4) = k1_funct_1(X2,X4) | ~r2_hidden(X4,k1_relset_1(X0,X0,X1))) | r1_partfun1(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1)) => (? [X2] : ((? [X3] : (k1_funct_1(sK2,X3) != k1_funct_1(X2,X3) & r2_hidden(X3,k1_relset_1(sK1,sK1,sK2))) | ~r1_partfun1(sK2,X2)) & (! [X4] : (k1_funct_1(sK2,X4) = k1_funct_1(X2,X4) | ~r2_hidden(X4,k1_relset_1(sK1,sK1,sK2))) | r1_partfun1(sK2,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v1_funct_2(X2,sK1,sK1) & v1_funct_1(X2)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v1_funct_1(sK2))),
% 1.62/0.99    introduced(choice_axiom,[])).
% 1.62/0.99  
% 1.62/0.99  fof(f31,plain,(
% 1.62/0.99    (((k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4) & r2_hidden(sK4,k1_relset_1(sK1,sK1,sK2))) | ~r1_partfun1(sK2,sK3)) & (! [X4] : (k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) | ~r2_hidden(X4,k1_relset_1(sK1,sK1,sK2))) | r1_partfun1(sK2,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v1_funct_2(sK3,sK1,sK1) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v1_funct_1(sK2)),
% 1.62/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f27,f30,f29,f28])).
% 1.62/0.99  
% 1.62/0.99  fof(f45,plain,(
% 1.62/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))),
% 1.62/0.99    inference(cnf_transformation,[],[f31])).
% 1.62/0.99  
% 1.62/0.99  fof(f6,axiom,(
% 1.62/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 1.62/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.62/0.99  
% 1.62/0.99  fof(f16,plain,(
% 1.62/0.99    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 1.62/0.99    inference(ennf_transformation,[],[f6])).
% 1.62/0.99  
% 1.62/0.99  fof(f17,plain,(
% 1.62/0.99    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 1.62/0.99    inference(flattening,[],[f16])).
% 1.62/0.99  
% 1.62/0.99  fof(f40,plain,(
% 1.62/0.99    ( ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 1.62/0.99    inference(cnf_transformation,[],[f17])).
% 1.62/0.99  
% 1.62/0.99  fof(f44,plain,(
% 1.62/0.99    v1_funct_2(sK3,sK1,sK1)),
% 1.62/0.99    inference(cnf_transformation,[],[f31])).
% 1.62/0.99  
% 1.62/0.99  fof(f43,plain,(
% 1.62/0.99    v1_funct_1(sK3)),
% 1.62/0.99    inference(cnf_transformation,[],[f31])).
% 1.62/0.99  
% 1.62/0.99  fof(f38,plain,(
% 1.62/0.99    ( ! [X0,X1] : (r1_partfun1(X0,X1) | r2_hidden(sK0(X0,X1),k1_relat_1(X0)) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.62/0.99    inference(cnf_transformation,[],[f24])).
% 1.62/0.99  
% 1.62/0.99  fof(f42,plain,(
% 1.62/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))),
% 1.62/0.99    inference(cnf_transformation,[],[f31])).
% 1.62/0.99  
% 1.62/0.99  fof(f46,plain,(
% 1.62/0.99    ( ! [X4] : (k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) | ~r2_hidden(X4,k1_relset_1(sK1,sK1,sK2)) | r1_partfun1(sK2,sK3)) )),
% 1.62/0.99    inference(cnf_transformation,[],[f31])).
% 1.62/0.99  
% 1.62/0.99  fof(f47,plain,(
% 1.62/0.99    r2_hidden(sK4,k1_relset_1(sK1,sK1,sK2)) | ~r1_partfun1(sK2,sK3)),
% 1.62/0.99    inference(cnf_transformation,[],[f31])).
% 1.62/0.99  
% 1.62/0.99  fof(f41,plain,(
% 1.62/0.99    v1_funct_1(sK2)),
% 1.62/0.99    inference(cnf_transformation,[],[f31])).
% 1.62/0.99  
% 1.62/0.99  fof(f48,plain,(
% 1.62/0.99    k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4) | ~r1_partfun1(sK2,sK3)),
% 1.62/0.99    inference(cnf_transformation,[],[f31])).
% 1.62/0.99  
% 1.62/0.99  fof(f2,axiom,(
% 1.62/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.62/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.62/0.99  
% 1.62/0.99  fof(f11,plain,(
% 1.62/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.62/0.99    inference(ennf_transformation,[],[f2])).
% 1.62/0.99  
% 1.62/0.99  fof(f34,plain,(
% 1.62/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.62/0.99    inference(cnf_transformation,[],[f11])).
% 1.62/0.99  
% 1.62/0.99  fof(f1,axiom,(
% 1.62/0.99    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.62/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.62/0.99  
% 1.62/0.99  fof(f10,plain,(
% 1.62/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.62/0.99    inference(ennf_transformation,[],[f1])).
% 1.62/0.99  
% 1.62/0.99  fof(f20,plain,(
% 1.62/0.99    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.62/0.99    inference(nnf_transformation,[],[f10])).
% 1.62/0.99  
% 1.62/0.99  fof(f32,plain,(
% 1.62/0.99    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.62/0.99    inference(cnf_transformation,[],[f20])).
% 1.62/0.99  
% 1.62/0.99  fof(f3,axiom,(
% 1.62/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.62/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.62/0.99  
% 1.62/0.99  fof(f9,plain,(
% 1.62/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.62/0.99    inference(pure_predicate_removal,[],[f3])).
% 1.62/0.99  
% 1.62/0.99  fof(f12,plain,(
% 1.62/0.99    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.62/0.99    inference(ennf_transformation,[],[f9])).
% 1.62/0.99  
% 1.62/0.99  fof(f35,plain,(
% 1.62/0.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.62/0.99    inference(cnf_transformation,[],[f12])).
% 1.62/0.99  
% 1.62/0.99  fof(f37,plain,(
% 1.62/0.99    ( ! [X0,X3,X1] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r1_partfun1(X0,X1) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.62/0.99    inference(cnf_transformation,[],[f24])).
% 1.62/0.99  
% 1.62/0.99  cnf(c_5,plain,
% 1.62/0.99      ( r1_partfun1(X0,X1)
% 1.62/0.99      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 1.62/0.99      | ~ v1_funct_1(X1)
% 1.62/0.99      | ~ v1_funct_1(X0)
% 1.62/0.99      | ~ v1_relat_1(X1)
% 1.62/0.99      | ~ v1_relat_1(X0)
% 1.62/0.99      | k1_funct_1(X1,sK0(X0,X1)) != k1_funct_1(X0,sK0(X0,X1)) ),
% 1.62/0.99      inference(cnf_transformation,[],[f39]) ).
% 1.62/0.99  
% 1.62/0.99  cnf(c_1662,plain,
% 1.62/0.99      ( r1_partfun1(X0_47,X1_47)
% 1.62/0.99      | ~ r1_tarski(k1_relat_1(X0_47),k1_relat_1(X1_47))
% 1.62/0.99      | ~ v1_funct_1(X1_47)
% 1.62/0.99      | ~ v1_funct_1(X0_47)
% 1.62/0.99      | ~ v1_relat_1(X1_47)
% 1.62/0.99      | ~ v1_relat_1(X0_47)
% 1.62/0.99      | k1_funct_1(X1_47,sK0(X0_47,X1_47)) != k1_funct_1(X0_47,sK0(X0_47,X1_47)) ),
% 1.62/0.99      inference(subtyping,[status(esa)],[c_5]) ).
% 1.62/0.99  
% 1.62/0.99  cnf(c_2821,plain,
% 1.62/0.99      ( r1_partfun1(X0_47,sK3)
% 1.62/0.99      | ~ r1_tarski(k1_relat_1(X0_47),k1_relat_1(sK3))
% 1.62/0.99      | ~ v1_funct_1(X0_47)
% 1.62/0.99      | ~ v1_funct_1(sK3)
% 1.62/0.99      | ~ v1_relat_1(X0_47)
% 1.62/0.99      | ~ v1_relat_1(sK3)
% 1.62/0.99      | k1_funct_1(sK3,sK0(X0_47,sK3)) != k1_funct_1(X0_47,sK0(X0_47,sK3)) ),
% 1.62/0.99      inference(instantiation,[status(thm)],[c_1662]) ).
% 1.62/0.99  
% 1.62/0.99  cnf(c_2828,plain,
% 1.62/0.99      ( r1_partfun1(sK2,sK3)
% 1.62/0.99      | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3))
% 1.62/0.99      | ~ v1_funct_1(sK3)
% 1.62/0.99      | ~ v1_funct_1(sK2)
% 1.62/0.99      | ~ v1_relat_1(sK3)
% 1.62/0.99      | ~ v1_relat_1(sK2)
% 1.62/0.99      | k1_funct_1(sK3,sK0(sK2,sK3)) != k1_funct_1(sK2,sK0(sK2,sK3)) ),
% 1.62/0.99      inference(instantiation,[status(thm)],[c_2821]) ).
% 1.62/0.99  
% 1.62/0.99  cnf(c_4,plain,
% 1.62/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.62/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 1.62/0.99      inference(cnf_transformation,[],[f36]) ).
% 1.62/0.99  
% 1.62/0.99  cnf(c_12,negated_conjecture,
% 1.62/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 1.62/0.99      inference(cnf_transformation,[],[f45]) ).
% 1.62/0.99  
% 1.62/0.99  cnf(c_200,plain,
% 1.62/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 1.62/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
% 1.62/0.99      | sK3 != X2 ),
% 1.62/0.99      inference(resolution_lifted,[status(thm)],[c_4,c_12]) ).
% 1.62/0.99  
% 1.62/0.99  cnf(c_201,plain,
% 1.62/0.99      ( k1_relset_1(X0,X1,sK3) = k1_relat_1(sK3)
% 1.62/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) ),
% 1.62/0.99      inference(unflattening,[status(thm)],[c_200]) ).
% 1.62/0.99  
% 1.62/0.99  cnf(c_1653,plain,
% 1.62/0.99      ( k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
% 1.62/0.99      | k1_relset_1(X0_46,X1_46,sK3) = k1_relat_1(sK3) ),
% 1.62/0.99      inference(subtyping,[status(esa)],[c_201]) ).
% 1.62/0.99  
% 1.62/0.99  cnf(c_2079,plain,
% 1.62/0.99      ( k1_relset_1(sK1,sK1,sK3) = k1_relat_1(sK3) ),
% 1.62/0.99      inference(equality_resolution,[status(thm)],[c_1653]) ).
% 1.62/0.99  
% 1.62/0.99  cnf(c_8,plain,
% 1.62/0.99      ( ~ v1_funct_2(X0,X1,X1)
% 1.62/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.62/0.99      | ~ v1_funct_1(X0)
% 1.62/0.99      | k1_relset_1(X1,X1,X0) = X1 ),
% 1.62/0.99      inference(cnf_transformation,[],[f40]) ).
% 1.62/0.99  
% 1.62/0.99  cnf(c_13,negated_conjecture,
% 1.62/0.99      ( v1_funct_2(sK3,sK1,sK1) ),
% 1.62/0.99      inference(cnf_transformation,[],[f44]) ).
% 1.62/0.99  
% 1.62/0.99  cnf(c_191,plain,
% 1.62/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.62/0.99      | ~ v1_funct_1(X0)
% 1.62/0.99      | k1_relset_1(X1,X1,X0) = X1
% 1.62/0.99      | sK1 != X1
% 1.62/0.99      | sK3 != X0 ),
% 1.62/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_13]) ).
% 1.62/0.99  
% 1.62/0.99  cnf(c_192,plain,
% 1.62/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 1.62/0.99      | ~ v1_funct_1(sK3)
% 1.62/0.99      | k1_relset_1(sK1,sK1,sK3) = sK1 ),
% 1.62/0.99      inference(unflattening,[status(thm)],[c_191]) ).
% 1.62/0.99  
% 1.62/0.99  cnf(c_14,negated_conjecture,
% 1.62/0.99      ( v1_funct_1(sK3) ),
% 1.62/0.99      inference(cnf_transformation,[],[f43]) ).
% 1.62/0.99  
% 1.62/0.99  cnf(c_194,plain,
% 1.62/0.99      ( k1_relset_1(sK1,sK1,sK3) = sK1 ),
% 1.62/0.99      inference(global_propositional_subsumption,
% 1.62/0.99                [status(thm)],
% 1.62/0.99                [c_192,c_14,c_12]) ).
% 1.62/0.99  
% 1.62/0.99  cnf(c_1654,plain,
% 1.62/0.99      ( k1_relset_1(sK1,sK1,sK3) = sK1 ),
% 1.62/0.99      inference(subtyping,[status(esa)],[c_194]) ).
% 1.62/0.99  
% 1.62/0.99  cnf(c_2080,plain,
% 1.62/0.99      ( k1_relat_1(sK3) = sK1 ),
% 1.62/0.99      inference(light_normalisation,[status(thm)],[c_2079,c_1654]) ).
% 1.62/0.99  
% 1.62/0.99  cnf(c_6,plain,
% 1.62/0.99      ( r2_hidden(sK0(X0,X1),k1_relat_1(X0))
% 1.62/0.99      | r1_partfun1(X0,X1)
% 1.62/0.99      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 1.62/0.99      | ~ v1_funct_1(X1)
% 1.62/0.99      | ~ v1_funct_1(X0)
% 1.62/0.99      | ~ v1_relat_1(X1)
% 1.62/0.99      | ~ v1_relat_1(X0) ),
% 1.62/0.99      inference(cnf_transformation,[],[f38]) ).
% 1.62/0.99  
% 1.62/0.99  cnf(c_1661,plain,
% 1.62/0.99      ( r2_hidden(sK0(X0_47,X1_47),k1_relat_1(X0_47))
% 1.62/0.99      | r1_partfun1(X0_47,X1_47)
% 1.62/0.99      | ~ r1_tarski(k1_relat_1(X0_47),k1_relat_1(X1_47))
% 1.62/0.99      | ~ v1_funct_1(X1_47)
% 1.62/0.99      | ~ v1_funct_1(X0_47)
% 1.62/0.99      | ~ v1_relat_1(X1_47)
% 1.62/0.99      | ~ v1_relat_1(X0_47) ),
% 1.62/0.99      inference(subtyping,[status(esa)],[c_6]) ).
% 1.62/0.99  
% 1.62/0.99  cnf(c_1911,plain,
% 1.62/0.99      ( r2_hidden(sK0(X0_47,X1_47),k1_relat_1(X0_47)) = iProver_top
% 1.62/0.99      | r1_partfun1(X0_47,X1_47) = iProver_top
% 1.62/0.99      | r1_tarski(k1_relat_1(X0_47),k1_relat_1(X1_47)) != iProver_top
% 1.62/0.99      | v1_funct_1(X1_47) != iProver_top
% 1.62/0.99      | v1_funct_1(X0_47) != iProver_top
% 1.62/0.99      | v1_relat_1(X0_47) != iProver_top
% 1.62/0.99      | v1_relat_1(X1_47) != iProver_top ),
% 1.62/0.99      inference(predicate_to_equality,[status(thm)],[c_1661]) ).
% 1.62/0.99  
% 1.62/0.99  cnf(c_15,negated_conjecture,
% 1.62/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 1.62/0.99      inference(cnf_transformation,[],[f42]) ).
% 1.62/0.99  
% 1.62/0.99  cnf(c_233,plain,
% 1.62/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 1.62/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
% 1.62/0.99      | sK2 != X2 ),
% 1.62/0.99      inference(resolution_lifted,[status(thm)],[c_4,c_15]) ).
% 1.62/0.99  
% 1.62/0.99  cnf(c_234,plain,
% 1.62/0.99      ( k1_relset_1(X0,X1,sK2) = k1_relat_1(sK2)
% 1.62/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) ),
% 1.62/0.99      inference(unflattening,[status(thm)],[c_233]) ).
% 1.62/0.99  
% 1.62/0.99  cnf(c_1651,plain,
% 1.62/0.99      ( k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
% 1.62/0.99      | k1_relset_1(X0_46,X1_46,sK2) = k1_relat_1(sK2) ),
% 1.62/0.99      inference(subtyping,[status(esa)],[c_234]) ).
% 1.62/0.99  
% 1.62/0.99  cnf(c_2066,plain,
% 1.62/0.99      ( k1_relset_1(sK1,sK1,sK2) = k1_relat_1(sK2) ),
% 1.62/0.99      inference(equality_resolution,[status(thm)],[c_1651]) ).
% 1.62/0.99  
% 1.62/0.99  cnf(c_11,negated_conjecture,
% 1.62/0.99      ( ~ r2_hidden(X0,k1_relset_1(sK1,sK1,sK2))
% 1.62/0.99      | r1_partfun1(sK2,sK3)
% 1.62/0.99      | k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0) ),
% 1.62/0.99      inference(cnf_transformation,[],[f46]) ).
% 1.62/0.99  
% 1.62/0.99  cnf(c_1657,negated_conjecture,
% 1.62/0.99      ( ~ r2_hidden(X0_50,k1_relset_1(sK1,sK1,sK2))
% 1.62/0.99      | r1_partfun1(sK2,sK3)
% 1.62/0.99      | k1_funct_1(sK2,X0_50) = k1_funct_1(sK3,X0_50) ),
% 1.62/0.99      inference(subtyping,[status(esa)],[c_11]) ).
% 1.62/0.99  
% 1.62/0.99  cnf(c_1915,plain,
% 1.62/0.99      ( k1_funct_1(sK2,X0_50) = k1_funct_1(sK3,X0_50)
% 1.62/0.99      | r2_hidden(X0_50,k1_relset_1(sK1,sK1,sK2)) != iProver_top
% 1.62/0.99      | r1_partfun1(sK2,sK3) = iProver_top ),
% 1.62/0.99      inference(predicate_to_equality,[status(thm)],[c_1657]) ).
% 1.62/0.99  
% 1.62/0.99  cnf(c_2343,plain,
% 1.62/0.99      ( k1_funct_1(sK3,X0_50) = k1_funct_1(sK2,X0_50)
% 1.62/0.99      | r2_hidden(X0_50,k1_relat_1(sK2)) != iProver_top
% 1.62/0.99      | r1_partfun1(sK2,sK3) = iProver_top ),
% 1.62/0.99      inference(demodulation,[status(thm)],[c_2066,c_1915]) ).
% 1.62/0.99  
% 1.62/0.99  cnf(c_10,negated_conjecture,
% 1.62/0.99      ( r2_hidden(sK4,k1_relset_1(sK1,sK1,sK2))
% 1.62/0.99      | ~ r1_partfun1(sK2,sK3) ),
% 1.62/0.99      inference(cnf_transformation,[],[f47]) ).
% 1.62/0.99  
% 1.62/0.99  cnf(c_1658,negated_conjecture,
% 1.62/0.99      ( r2_hidden(sK4,k1_relset_1(sK1,sK1,sK2))
% 1.62/0.99      | ~ r1_partfun1(sK2,sK3) ),
% 1.62/0.99      inference(subtyping,[status(esa)],[c_10]) ).
% 1.62/0.99  
% 1.62/0.99  cnf(c_1914,plain,
% 1.62/0.99      ( r2_hidden(sK4,k1_relset_1(sK1,sK1,sK2)) = iProver_top
% 1.62/0.99      | r1_partfun1(sK2,sK3) != iProver_top ),
% 1.62/0.99      inference(predicate_to_equality,[status(thm)],[c_1658]) ).
% 1.62/0.99  
% 1.62/0.99  cnf(c_2344,plain,
% 1.62/0.99      ( r2_hidden(sK4,k1_relat_1(sK2)) = iProver_top
% 1.62/0.99      | r1_partfun1(sK2,sK3) != iProver_top ),
% 1.62/0.99      inference(demodulation,[status(thm)],[c_2066,c_1914]) ).
% 1.62/0.99  
% 1.62/0.99  cnf(c_16,negated_conjecture,
% 1.62/0.99      ( v1_funct_1(sK2) ),
% 1.62/0.99      inference(cnf_transformation,[],[f41]) ).
% 1.62/0.99  
% 1.62/0.99  cnf(c_17,plain,
% 1.62/0.99      ( v1_funct_1(sK2) = iProver_top ),
% 1.62/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 1.62/0.99  
% 1.62/0.99  cnf(c_19,plain,
% 1.62/0.99      ( v1_funct_1(sK3) = iProver_top ),
% 1.62/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 1.62/0.99  
% 1.62/0.99  cnf(c_9,negated_conjecture,
% 1.62/0.99      ( ~ r1_partfun1(sK2,sK3)
% 1.62/0.99      | k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4) ),
% 1.62/0.99      inference(cnf_transformation,[],[f48]) ).
% 1.62/0.99  
% 1.62/0.99  cnf(c_1659,negated_conjecture,
% 1.62/0.99      ( ~ r1_partfun1(sK2,sK3)
% 1.62/0.99      | k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4) ),
% 1.62/0.99      inference(subtyping,[status(esa)],[c_9]) ).
% 1.62/0.99  
% 1.62/0.99  cnf(c_1695,plain,
% 1.62/0.99      ( k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4)
% 1.62/0.99      | r1_partfun1(sK2,sK3) != iProver_top ),
% 1.62/0.99      inference(predicate_to_equality,[status(thm)],[c_1659]) ).
% 1.62/0.99  
% 1.62/0.99  cnf(c_2,plain,
% 1.62/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.62/0.99      | v1_relat_1(X0) ),
% 1.62/0.99      inference(cnf_transformation,[],[f34]) ).
% 1.62/0.99  
% 1.62/0.99  cnf(c_221,plain,
% 1.62/0.99      ( v1_relat_1(X0)
% 1.62/0.99      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
% 1.62/0.99      | sK3 != X0 ),
% 1.62/0.99      inference(resolution_lifted,[status(thm)],[c_2,c_12]) ).
% 1.62/0.99  
% 1.62/0.99  cnf(c_222,plain,
% 1.62/0.99      ( v1_relat_1(sK3)
% 1.62/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) ),
% 1.62/0.99      inference(unflattening,[status(thm)],[c_221]) ).
% 1.62/0.99  
% 1.62/0.99  cnf(c_1652,plain,
% 1.62/0.99      ( v1_relat_1(sK3)
% 1.62/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) ),
% 1.62/0.99      inference(subtyping,[status(esa)],[c_222]) ).
% 1.62/0.99  
% 1.62/0.99  cnf(c_1703,plain,
% 1.62/0.99      ( k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
% 1.62/0.99      | v1_relat_1(sK3) = iProver_top ),
% 1.62/0.99      inference(predicate_to_equality,[status(thm)],[c_1652]) ).
% 1.62/0.99  
% 1.62/0.99  cnf(c_1705,plain,
% 1.62/0.99      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
% 1.62/0.99      | v1_relat_1(sK3) = iProver_top ),
% 1.62/0.99      inference(instantiation,[status(thm)],[c_1703]) ).
% 1.62/0.99  
% 1.62/0.99  cnf(c_254,plain,
% 1.62/0.99      ( v1_relat_1(X0)
% 1.62/0.99      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
% 1.62/0.99      | sK2 != X0 ),
% 1.62/0.99      inference(resolution_lifted,[status(thm)],[c_2,c_15]) ).
% 1.62/0.99  
% 1.62/0.99  cnf(c_255,plain,
% 1.62/0.99      ( v1_relat_1(sK2)
% 1.62/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) ),
% 1.62/0.99      inference(unflattening,[status(thm)],[c_254]) ).
% 1.62/0.99  
% 1.62/0.99  cnf(c_1650,plain,
% 1.62/0.99      ( v1_relat_1(sK2)
% 1.62/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) ),
% 1.62/0.99      inference(subtyping,[status(esa)],[c_255]) ).
% 1.62/0.99  
% 1.62/0.99  cnf(c_1707,plain,
% 1.62/0.99      ( k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
% 1.62/0.99      | v1_relat_1(sK2) = iProver_top ),
% 1.62/0.99      inference(predicate_to_equality,[status(thm)],[c_1650]) ).
% 1.62/0.99  
% 1.62/0.99  cnf(c_1709,plain,
% 1.62/0.99      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
% 1.62/0.99      | v1_relat_1(sK2) = iProver_top ),
% 1.62/0.99      inference(instantiation,[status(thm)],[c_1707]) ).
% 1.62/0.99  
% 1.62/0.99  cnf(c_1,plain,
% 1.62/0.99      ( r1_tarski(k1_relat_1(X0),X1)
% 1.62/0.99      | ~ v4_relat_1(X0,X1)
% 1.62/0.99      | ~ v1_relat_1(X0) ),
% 1.62/0.99      inference(cnf_transformation,[],[f32]) ).
% 1.62/0.99  
% 1.62/0.99  cnf(c_3,plain,
% 1.62/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.62/0.99      | v4_relat_1(X0,X1) ),
% 1.62/0.99      inference(cnf_transformation,[],[f35]) ).
% 1.62/0.99  
% 1.62/0.99  cnf(c_242,plain,
% 1.62/0.99      ( v4_relat_1(X0,X1)
% 1.62/0.99      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
% 1.62/0.99      | sK2 != X0 ),
% 1.62/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_15]) ).
% 1.62/0.99  
% 1.62/0.99  cnf(c_243,plain,
% 1.62/0.99      ( v4_relat_1(sK2,X0)
% 1.62/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) ),
% 1.62/0.99      inference(unflattening,[status(thm)],[c_242]) ).
% 1.62/0.99  
% 1.62/0.99  cnf(c_301,plain,
% 1.62/0.99      ( r1_tarski(k1_relat_1(X0),X1)
% 1.62/0.99      | ~ v1_relat_1(X0)
% 1.62/0.99      | X2 != X1
% 1.62/0.99      | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
% 1.62/0.99      | sK2 != X0 ),
% 1.62/0.99      inference(resolution_lifted,[status(thm)],[c_1,c_243]) ).
% 1.62/0.99  
% 1.62/0.99  cnf(c_302,plain,
% 1.62/0.99      ( r1_tarski(k1_relat_1(sK2),X0)
% 1.62/0.99      | ~ v1_relat_1(sK2)
% 1.62/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) ),
% 1.62/0.99      inference(unflattening,[status(thm)],[c_301]) ).
% 1.62/0.99  
% 1.62/0.99  cnf(c_306,plain,
% 1.62/0.99      ( r1_tarski(k1_relat_1(sK2),X0)
% 1.62/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) ),
% 1.62/0.99      inference(global_propositional_subsumption,
% 1.62/0.99                [status(thm)],
% 1.62/0.99                [c_302,c_255]) ).
% 1.62/0.99  
% 1.62/0.99  cnf(c_1648,plain,
% 1.62/0.99      ( r1_tarski(k1_relat_1(sK2),X0_46)
% 1.62/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) ),
% 1.62/0.99      inference(subtyping,[status(esa)],[c_306]) ).
% 1.62/0.99  
% 1.62/0.99  cnf(c_1713,plain,
% 1.62/0.99      ( k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
% 1.62/0.99      | r1_tarski(k1_relat_1(sK2),X0_46) = iProver_top ),
% 1.62/0.99      inference(predicate_to_equality,[status(thm)],[c_1648]) ).
% 1.62/0.99  
% 1.62/0.99  cnf(c_1715,plain,
% 1.62/0.99      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
% 1.62/0.99      | r1_tarski(k1_relat_1(sK2),sK1) = iProver_top ),
% 1.62/0.99      inference(instantiation,[status(thm)],[c_1713]) ).
% 1.62/0.99  
% 1.62/0.99  cnf(c_1665,plain,( X0_48 = X0_48 ),theory(equality) ).
% 1.62/0.99  
% 1.62/0.99  cnf(c_2040,plain,
% 1.62/0.99      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) ),
% 1.62/0.99      inference(instantiation,[status(thm)],[c_1665]) ).
% 1.62/0.99  
% 1.62/0.99  cnf(c_7,plain,
% 1.62/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 1.62/0.99      | ~ r1_partfun1(X1,X2)
% 1.62/0.99      | ~ r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
% 1.62/0.99      | ~ v1_funct_1(X2)
% 1.62/0.99      | ~ v1_funct_1(X1)
% 1.62/0.99      | ~ v1_relat_1(X2)
% 1.62/0.99      | ~ v1_relat_1(X1)
% 1.62/0.99      | k1_funct_1(X2,X0) = k1_funct_1(X1,X0) ),
% 1.62/0.99      inference(cnf_transformation,[],[f37]) ).
% 1.62/0.99  
% 1.62/0.99  cnf(c_1660,plain,
% 1.62/0.99      ( ~ r2_hidden(X0_50,k1_relat_1(X0_47))
% 1.62/0.99      | ~ r1_partfun1(X0_47,X1_47)
% 1.62/0.99      | ~ r1_tarski(k1_relat_1(X0_47),k1_relat_1(X1_47))
% 1.62/0.99      | ~ v1_funct_1(X1_47)
% 1.62/0.99      | ~ v1_funct_1(X0_47)
% 1.62/0.99      | ~ v1_relat_1(X1_47)
% 1.62/0.99      | ~ v1_relat_1(X0_47)
% 1.62/0.99      | k1_funct_1(X1_47,X0_50) = k1_funct_1(X0_47,X0_50) ),
% 1.62/0.99      inference(subtyping,[status(esa)],[c_7]) ).
% 1.62/0.99  
% 1.62/0.99  cnf(c_1912,plain,
% 1.62/0.99      ( k1_funct_1(X0_47,X0_50) = k1_funct_1(X1_47,X0_50)
% 1.62/0.99      | r2_hidden(X0_50,k1_relat_1(X1_47)) != iProver_top
% 1.62/0.99      | r1_partfun1(X1_47,X0_47) != iProver_top
% 1.62/0.99      | r1_tarski(k1_relat_1(X1_47),k1_relat_1(X0_47)) != iProver_top
% 1.62/0.99      | v1_funct_1(X0_47) != iProver_top
% 1.62/0.99      | v1_funct_1(X1_47) != iProver_top
% 1.62/0.99      | v1_relat_1(X1_47) != iProver_top
% 1.62/0.99      | v1_relat_1(X0_47) != iProver_top ),
% 1.62/0.99      inference(predicate_to_equality,[status(thm)],[c_1660]) ).
% 1.62/0.99  
% 1.62/0.99  cnf(c_2274,plain,
% 1.62/0.99      ( k1_funct_1(X0_47,X0_50) = k1_funct_1(sK3,X0_50)
% 1.62/0.99      | r2_hidden(X0_50,k1_relat_1(X0_47)) != iProver_top
% 1.62/0.99      | r1_partfun1(X0_47,sK3) != iProver_top
% 1.62/0.99      | r1_tarski(k1_relat_1(X0_47),sK1) != iProver_top
% 1.62/0.99      | v1_funct_1(X0_47) != iProver_top
% 1.62/0.99      | v1_funct_1(sK3) != iProver_top
% 1.62/0.99      | v1_relat_1(X0_47) != iProver_top
% 1.62/0.99      | v1_relat_1(sK3) != iProver_top ),
% 1.62/0.99      inference(superposition,[status(thm)],[c_2080,c_1912]) ).
% 1.62/0.99  
% 1.62/0.99  cnf(c_2334,plain,
% 1.62/0.99      ( k1_funct_1(sK2,sK4) = k1_funct_1(sK3,sK4)
% 1.62/0.99      | r2_hidden(sK4,k1_relat_1(sK2)) != iProver_top
% 1.62/0.99      | r1_partfun1(sK2,sK3) != iProver_top
% 1.62/0.99      | r1_tarski(k1_relat_1(sK2),sK1) != iProver_top
% 1.62/0.99      | v1_funct_1(sK3) != iProver_top
% 1.62/0.99      | v1_funct_1(sK2) != iProver_top
% 1.62/0.99      | v1_relat_1(sK3) != iProver_top
% 1.62/0.99      | v1_relat_1(sK2) != iProver_top ),
% 1.62/0.99      inference(instantiation,[status(thm)],[c_2274]) ).
% 1.62/0.99  
% 1.62/0.99  cnf(c_2422,plain,
% 1.62/0.99      ( r1_partfun1(sK2,sK3) != iProver_top ),
% 1.62/0.99      inference(global_propositional_subsumption,
% 1.62/0.99                [status(thm)],
% 1.62/0.99                [c_2344,c_17,c_19,c_1695,c_1705,c_1709,c_1715,c_2040,
% 1.62/0.99                 c_2334]) ).
% 1.62/0.99  
% 1.62/0.99  cnf(c_2572,plain,
% 1.62/0.99      ( r2_hidden(X0_50,k1_relat_1(sK2)) != iProver_top
% 1.62/0.99      | k1_funct_1(sK3,X0_50) = k1_funct_1(sK2,X0_50) ),
% 1.62/0.99      inference(global_propositional_subsumption,
% 1.62/0.99                [status(thm)],
% 1.62/0.99                [c_2343,c_17,c_19,c_1695,c_1705,c_1709,c_1715,c_2040,
% 1.62/0.99                 c_2334,c_2344]) ).
% 1.62/0.99  
% 1.62/0.99  cnf(c_2573,plain,
% 1.62/0.99      ( k1_funct_1(sK3,X0_50) = k1_funct_1(sK2,X0_50)
% 1.62/0.99      | r2_hidden(X0_50,k1_relat_1(sK2)) != iProver_top ),
% 1.62/0.99      inference(renaming,[status(thm)],[c_2572]) ).
% 1.62/0.99  
% 1.62/0.99  cnf(c_2580,plain,
% 1.62/0.99      ( k1_funct_1(sK3,sK0(sK2,X0_47)) = k1_funct_1(sK2,sK0(sK2,X0_47))
% 1.62/0.99      | r1_partfun1(sK2,X0_47) = iProver_top
% 1.62/0.99      | r1_tarski(k1_relat_1(sK2),k1_relat_1(X0_47)) != iProver_top
% 1.62/0.99      | v1_funct_1(X0_47) != iProver_top
% 1.62/0.99      | v1_funct_1(sK2) != iProver_top
% 1.62/0.99      | v1_relat_1(X0_47) != iProver_top
% 1.62/0.99      | v1_relat_1(sK2) != iProver_top ),
% 1.62/0.99      inference(superposition,[status(thm)],[c_1911,c_2573]) ).
% 1.62/0.99  
% 1.62/0.99  cnf(c_2782,plain,
% 1.62/0.99      ( v1_relat_1(X0_47) != iProver_top
% 1.62/0.99      | k1_funct_1(sK3,sK0(sK2,X0_47)) = k1_funct_1(sK2,sK0(sK2,X0_47))
% 1.62/0.99      | r1_partfun1(sK2,X0_47) = iProver_top
% 1.62/0.99      | r1_tarski(k1_relat_1(sK2),k1_relat_1(X0_47)) != iProver_top
% 1.62/0.99      | v1_funct_1(X0_47) != iProver_top ),
% 1.62/0.99      inference(global_propositional_subsumption,
% 1.62/0.99                [status(thm)],
% 1.62/0.99                [c_2580,c_17,c_1709,c_2040]) ).
% 1.62/0.99  
% 1.62/0.99  cnf(c_2783,plain,
% 1.62/0.99      ( k1_funct_1(sK3,sK0(sK2,X0_47)) = k1_funct_1(sK2,sK0(sK2,X0_47))
% 1.62/0.99      | r1_partfun1(sK2,X0_47) = iProver_top
% 1.62/0.99      | r1_tarski(k1_relat_1(sK2),k1_relat_1(X0_47)) != iProver_top
% 1.62/0.99      | v1_funct_1(X0_47) != iProver_top
% 1.62/0.99      | v1_relat_1(X0_47) != iProver_top ),
% 1.62/0.99      inference(renaming,[status(thm)],[c_2782]) ).
% 1.62/0.99  
% 1.62/0.99  cnf(c_2791,plain,
% 1.62/0.99      ( k1_funct_1(sK3,sK0(sK2,sK3)) = k1_funct_1(sK2,sK0(sK2,sK3))
% 1.62/0.99      | r1_partfun1(sK2,sK3) = iProver_top
% 1.62/0.99      | r1_tarski(k1_relat_1(sK2),sK1) != iProver_top
% 1.62/0.99      | v1_funct_1(sK3) != iProver_top
% 1.62/0.99      | v1_relat_1(sK3) != iProver_top ),
% 1.62/0.99      inference(superposition,[status(thm)],[c_2080,c_2783]) ).
% 1.62/0.99  
% 1.62/0.99  cnf(c_1671,plain,
% 1.62/0.99      ( ~ r1_tarski(X0_46,X1_46)
% 1.62/0.99      | r1_tarski(X2_46,X3_46)
% 1.62/0.99      | X2_46 != X0_46
% 1.62/0.99      | X3_46 != X1_46 ),
% 1.62/0.99      theory(equality) ).
% 1.62/0.99  
% 1.62/0.99  cnf(c_2067,plain,
% 1.62/0.99      ( r1_tarski(X0_46,X1_46)
% 1.62/0.99      | ~ r1_tarski(k1_relat_1(sK2),X2_46)
% 1.62/0.99      | X1_46 != X2_46
% 1.62/0.99      | X0_46 != k1_relat_1(sK2) ),
% 1.62/0.99      inference(instantiation,[status(thm)],[c_1671]) ).
% 1.62/0.99  
% 1.62/0.99  cnf(c_2148,plain,
% 1.62/0.99      ( ~ r1_tarski(k1_relat_1(sK2),X0_46)
% 1.62/0.99      | r1_tarski(k1_relat_1(sK2),X1_46)
% 1.62/0.99      | X1_46 != X0_46
% 1.62/0.99      | k1_relat_1(sK2) != k1_relat_1(sK2) ),
% 1.62/0.99      inference(instantiation,[status(thm)],[c_2067]) ).
% 1.62/0.99  
% 1.62/0.99  cnf(c_2222,plain,
% 1.62/0.99      ( ~ r1_tarski(k1_relat_1(sK2),X0_46)
% 1.62/0.99      | r1_tarski(k1_relat_1(sK2),k1_relat_1(X0_47))
% 1.62/0.99      | k1_relat_1(X0_47) != X0_46
% 1.62/0.99      | k1_relat_1(sK2) != k1_relat_1(sK2) ),
% 1.62/0.99      inference(instantiation,[status(thm)],[c_2148]) ).
% 1.62/0.99  
% 1.62/0.99  cnf(c_2524,plain,
% 1.62/0.99      ( r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3))
% 1.62/0.99      | ~ r1_tarski(k1_relat_1(sK2),sK1)
% 1.62/0.99      | k1_relat_1(sK3) != sK1
% 1.62/0.99      | k1_relat_1(sK2) != k1_relat_1(sK2) ),
% 1.62/0.99      inference(instantiation,[status(thm)],[c_2222]) ).
% 1.62/0.99  
% 1.62/0.99  cnf(c_2424,plain,
% 1.62/0.99      ( ~ r1_partfun1(sK2,sK3) ),
% 1.62/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_2422]) ).
% 1.62/0.99  
% 1.62/0.99  cnf(c_1664,plain,( X0_46 = X0_46 ),theory(equality) ).
% 1.62/0.99  
% 1.62/0.99  cnf(c_2149,plain,
% 1.62/0.99      ( k1_relat_1(sK2) = k1_relat_1(sK2) ),
% 1.62/0.99      inference(instantiation,[status(thm)],[c_1664]) ).
% 1.62/0.99  
% 1.62/0.99  cnf(c_1714,plain,
% 1.62/0.99      ( r1_tarski(k1_relat_1(sK2),sK1)
% 1.62/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) ),
% 1.62/0.99      inference(instantiation,[status(thm)],[c_1648]) ).
% 1.62/0.99  
% 1.62/0.99  cnf(c_1708,plain,
% 1.62/0.99      ( v1_relat_1(sK2)
% 1.62/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) ),
% 1.62/0.99      inference(instantiation,[status(thm)],[c_1650]) ).
% 1.62/0.99  
% 1.62/0.99  cnf(c_1704,plain,
% 1.62/0.99      ( v1_relat_1(sK3)
% 1.62/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) ),
% 1.62/0.99      inference(instantiation,[status(thm)],[c_1652]) ).
% 1.62/0.99  
% 1.62/0.99  cnf(contradiction,plain,
% 1.62/0.99      ( $false ),
% 1.62/0.99      inference(minisat,
% 1.62/0.99                [status(thm)],
% 1.62/0.99                [c_2828,c_2791,c_2524,c_2424,c_2422,c_2149,c_2080,c_2040,
% 1.62/0.99                 c_1715,c_1714,c_1708,c_1705,c_1704,c_19,c_14,c_16]) ).
% 1.62/0.99  
% 1.62/0.99  
% 1.62/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 1.62/0.99  
% 1.62/0.99  ------                               Statistics
% 1.62/0.99  
% 1.62/0.99  ------ General
% 1.62/0.99  
% 1.62/0.99  abstr_ref_over_cycles:                  0
% 1.62/0.99  abstr_ref_under_cycles:                 0
% 1.62/0.99  gc_basic_clause_elim:                   0
% 1.62/0.99  forced_gc_time:                         0
% 1.62/0.99  parsing_time:                           0.013
% 1.62/0.99  unif_index_cands_time:                  0.
% 1.62/0.99  unif_index_add_time:                    0.
% 1.62/0.99  orderings_time:                         0.
% 1.62/0.99  out_proof_time:                         0.012
% 1.62/0.99  total_time:                             0.136
% 1.62/0.99  num_of_symbols:                         52
% 1.62/0.99  num_of_terms:                           1789
% 1.62/0.99  
% 1.62/0.99  ------ Preprocessing
% 1.62/0.99  
% 1.62/0.99  num_of_splits:                          0
% 1.62/0.99  num_of_split_atoms:                     0
% 1.62/0.99  num_of_reused_defs:                     0
% 1.62/0.99  num_eq_ax_congr_red:                    19
% 1.62/0.99  num_of_sem_filtered_clauses:            1
% 1.62/0.99  num_of_subtypes:                        6
% 1.62/0.99  monotx_restored_types:                  0
% 1.62/0.99  sat_num_of_epr_types:                   0
% 1.62/0.99  sat_num_of_non_cyclic_types:            0
% 1.62/0.99  sat_guarded_non_collapsed_types:        0
% 1.62/0.99  num_pure_diseq_elim:                    0
% 1.62/0.99  simp_replaced_by:                       0
% 1.62/0.99  res_preprocessed:                       87
% 1.62/0.99  prep_upred:                             0
% 1.62/0.99  prep_unflattend:                        60
% 1.62/0.99  smt_new_axioms:                         0
% 1.62/0.99  pred_elim_cands:                        5
% 1.62/0.99  pred_elim:                              3
% 1.62/0.99  pred_elim_cl:                           2
% 1.62/0.99  pred_elim_cycles:                       9
% 1.62/0.99  merged_defs:                            0
% 1.62/0.99  merged_defs_ncl:                        0
% 1.62/0.99  bin_hyper_res:                          0
% 1.62/0.99  prep_cycles:                            4
% 1.62/0.99  pred_elim_time:                         0.033
% 1.62/0.99  splitting_time:                         0.
% 1.62/0.99  sem_filter_time:                        0.
% 1.62/0.99  monotx_time:                            0.
% 1.62/0.99  subtype_inf_time:                       0.
% 1.62/0.99  
% 1.62/0.99  ------ Problem properties
% 1.62/0.99  
% 1.62/0.99  clauses:                                15
% 1.62/0.99  conjectures:                            5
% 1.62/0.99  epr:                                    2
% 1.62/0.99  horn:                                   13
% 1.62/0.99  ground:                                 5
% 1.62/0.99  unary:                                  3
% 1.62/0.99  binary:                                 8
% 1.62/0.99  lits:                                   44
% 1.62/0.99  lits_eq:                                13
% 1.62/0.99  fd_pure:                                0
% 1.62/0.99  fd_pseudo:                              0
% 1.62/0.99  fd_cond:                                0
% 1.62/0.99  fd_pseudo_cond:                         0
% 1.62/0.99  ac_symbols:                             0
% 1.62/0.99  
% 1.62/0.99  ------ Propositional Solver
% 1.62/0.99  
% 1.62/0.99  prop_solver_calls:                      29
% 1.62/0.99  prop_fast_solver_calls:                 916
% 1.62/0.99  smt_solver_calls:                       0
% 1.62/0.99  smt_fast_solver_calls:                  0
% 1.62/0.99  prop_num_of_clauses:                    574
% 1.62/0.99  prop_preprocess_simplified:             2732
% 1.62/0.99  prop_fo_subsumed:                       30
% 1.62/0.99  prop_solver_time:                       0.
% 1.62/0.99  smt_solver_time:                        0.
% 1.62/0.99  smt_fast_solver_time:                   0.
% 1.62/0.99  prop_fast_solver_time:                  0.
% 1.62/0.99  prop_unsat_core_time:                   0.
% 1.62/0.99  
% 1.62/0.99  ------ QBF
% 1.62/0.99  
% 1.62/0.99  qbf_q_res:                              0
% 1.62/0.99  qbf_num_tautologies:                    0
% 1.62/0.99  qbf_prep_cycles:                        0
% 1.62/0.99  
% 1.62/0.99  ------ BMC1
% 1.62/0.99  
% 1.62/0.99  bmc1_current_bound:                     -1
% 1.62/0.99  bmc1_last_solved_bound:                 -1
% 1.62/0.99  bmc1_unsat_core_size:                   -1
% 1.62/0.99  bmc1_unsat_core_parents_size:           -1
% 1.62/0.99  bmc1_merge_next_fun:                    0
% 1.62/0.99  bmc1_unsat_core_clauses_time:           0.
% 1.62/0.99  
% 1.62/0.99  ------ Instantiation
% 1.62/0.99  
% 1.62/0.99  inst_num_of_clauses:                    146
% 1.62/0.99  inst_num_in_passive:                    27
% 1.62/0.99  inst_num_in_active:                     94
% 1.62/0.99  inst_num_in_unprocessed:                24
% 1.62/0.99  inst_num_of_loops:                      112
% 1.62/0.99  inst_num_of_learning_restarts:          0
% 1.62/0.99  inst_num_moves_active_passive:          12
% 1.62/0.99  inst_lit_activity:                      0
% 1.62/0.99  inst_lit_activity_moves:                0
% 1.62/0.99  inst_num_tautologies:                   0
% 1.62/0.99  inst_num_prop_implied:                  0
% 1.62/0.99  inst_num_existing_simplified:           0
% 1.62/0.99  inst_num_eq_res_simplified:             0
% 1.62/0.99  inst_num_child_elim:                    0
% 1.62/0.99  inst_num_of_dismatching_blockings:      31
% 1.62/0.99  inst_num_of_non_proper_insts:           122
% 1.62/0.99  inst_num_of_duplicates:                 0
% 1.62/0.99  inst_inst_num_from_inst_to_res:         0
% 1.62/0.99  inst_dismatching_checking_time:         0.
% 1.62/0.99  
% 1.62/0.99  ------ Resolution
% 1.62/0.99  
% 1.62/0.99  res_num_of_clauses:                     0
% 1.62/0.99  res_num_in_passive:                     0
% 1.62/0.99  res_num_in_active:                      0
% 1.62/0.99  res_num_of_loops:                       91
% 1.62/0.99  res_forward_subset_subsumed:            21
% 1.62/0.99  res_backward_subset_subsumed:           0
% 1.62/0.99  res_forward_subsumed:                   0
% 1.62/0.99  res_backward_subsumed:                  0
% 1.62/0.99  res_forward_subsumption_resolution:     0
% 1.62/0.99  res_backward_subsumption_resolution:    0
% 1.62/0.99  res_clause_to_clause_subsumption:       41
% 1.62/0.99  res_orphan_elimination:                 0
% 1.62/0.99  res_tautology_del:                      28
% 1.62/0.99  res_num_eq_res_simplified:              0
% 1.62/0.99  res_num_sel_changes:                    0
% 1.62/0.99  res_moves_from_active_to_pass:          0
% 1.62/0.99  
% 1.62/0.99  ------ Superposition
% 1.62/0.99  
% 1.62/0.99  sup_time_total:                         0.
% 1.62/0.99  sup_time_generating:                    0.
% 1.62/0.99  sup_time_sim_full:                      0.
% 1.62/0.99  sup_time_sim_immed:                     0.
% 1.62/0.99  
% 1.62/0.99  sup_num_of_clauses:                     27
% 1.62/0.99  sup_num_in_active:                      19
% 1.62/0.99  sup_num_in_passive:                     8
% 1.62/0.99  sup_num_of_loops:                       22
% 1.62/0.99  sup_fw_superposition:                   3
% 1.62/0.99  sup_bw_superposition:                   5
% 1.62/0.99  sup_immediate_simplified:               3
% 1.62/0.99  sup_given_eliminated:                   0
% 1.62/0.99  comparisons_done:                       0
% 1.62/0.99  comparisons_avoided:                    0
% 1.62/0.99  
% 1.62/0.99  ------ Simplifications
% 1.62/0.99  
% 1.62/0.99  
% 1.62/0.99  sim_fw_subset_subsumed:                 0
% 1.62/0.99  sim_bw_subset_subsumed:                 0
% 1.62/0.99  sim_fw_subsumed:                        0
% 1.62/0.99  sim_bw_subsumed:                        0
% 1.62/0.99  sim_fw_subsumption_res:                 0
% 1.62/0.99  sim_bw_subsumption_res:                 0
% 1.62/0.99  sim_tautology_del:                      1
% 1.62/0.99  sim_eq_tautology_del:                   0
% 1.62/0.99  sim_eq_res_simp:                        0
% 1.62/0.99  sim_fw_demodulated:                     0
% 1.62/0.99  sim_bw_demodulated:                     3
% 1.62/0.99  sim_light_normalised:                   4
% 1.62/0.99  sim_joinable_taut:                      0
% 1.62/0.99  sim_joinable_simp:                      0
% 1.62/0.99  sim_ac_normalised:                      0
% 1.62/0.99  sim_smt_subsumption:                    0
% 1.62/0.99  
%------------------------------------------------------------------------------
