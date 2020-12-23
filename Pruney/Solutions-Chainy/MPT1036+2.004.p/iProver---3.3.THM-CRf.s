%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:08:41 EST 2020

% Result     : Theorem 1.88s
% Output     : CNFRefutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :  138 (1245 expanded)
%              Number of clauses        :   86 ( 363 expanded)
%              Number of leaves         :   15 ( 295 expanded)
%              Depth                    :   25
%              Number of atoms          :  530 (8463 expanded)
%              Number of equality atoms :  203 (1834 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,conjecture,(
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

fof(f9,negated_conjecture,(
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
    inference(negated_conjecture,[],[f8])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( k1_funct_1(X1,X3) != k1_funct_1(X2,X3)
          & r2_hidden(X3,k1_relset_1(X0,X0,X1)) )
     => ( k1_funct_1(X1,sK5) != k1_funct_1(X2,sK5)
        & r2_hidden(sK5,k1_relset_1(X0,X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
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
              ( k1_funct_1(sK4,X3) != k1_funct_1(X1,X3)
              & r2_hidden(X3,k1_relset_1(X0,X0,X1)) )
          | ~ r1_partfun1(X1,sK4) )
        & ( ! [X4] :
              ( k1_funct_1(sK4,X4) = k1_funct_1(X1,X4)
              | ~ r2_hidden(X4,k1_relset_1(X0,X0,X1)) )
          | r1_partfun1(X1,sK4) )
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(sK4,X0,X0)
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
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
                ( k1_funct_1(sK3,X3) != k1_funct_1(X2,X3)
                & r2_hidden(X3,k1_relset_1(sK2,sK2,sK3)) )
            | ~ r1_partfun1(sK3,X2) )
          & ( ! [X4] :
                ( k1_funct_1(sK3,X4) = k1_funct_1(X2,X4)
                | ~ r2_hidden(X4,k1_relset_1(sK2,sK2,sK3)) )
            | r1_partfun1(sK3,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
          & v1_funct_2(X2,sK2,sK2)
          & v1_funct_1(X2) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ( ( k1_funct_1(sK3,sK5) != k1_funct_1(sK4,sK5)
        & r2_hidden(sK5,k1_relset_1(sK2,sK2,sK3)) )
      | ~ r1_partfun1(sK3,sK4) )
    & ( ! [X4] :
          ( k1_funct_1(sK3,X4) = k1_funct_1(sK4,X4)
          | ~ r2_hidden(X4,k1_relset_1(sK2,sK2,sK3)) )
      | r1_partfun1(sK3,sK4) )
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    & v1_funct_2(sK4,sK2,sK2)
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f30,f33,f32,f31])).

fof(f49,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f34])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f48,plain,(
    v1_funct_2(sK4,sK2,sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f47,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f34])).

fof(f6,axiom,(
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

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f24,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f25,plain,(
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
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1))
        & r2_hidden(sK1(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_partfun1(X0,X1)
              | ( k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1))
                & r2_hidden(sK1(X0,X1),k1_relat_1(X0)) ) )
            & ( ! [X3] :
                  ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                  | ~ r2_hidden(X3,k1_relat_1(X0)) )
              | ~ r1_partfun1(X0,X1) ) )
          | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f25,f26])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_partfun1(X0,X1)
      | r2_hidden(sK1(X0,X1),k1_relat_1(X0))
      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f46,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f34])).

fof(f50,plain,(
    ! [X4] :
      ( k1_funct_1(sK3,X4) = k1_funct_1(sK4,X4)
      | ~ r2_hidden(X4,k1_relset_1(sK2,sK2,sK3))
      | r1_partfun1(sK3,sK4) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f45,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f51,plain,
    ( r2_hidden(sK5,k1_relset_1(sK2,sK2,sK3))
    | ~ r1_partfun1(sK3,sK4) ),
    inference(cnf_transformation,[],[f34])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ r1_partfun1(X0,X1)
      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f52,plain,
    ( k1_funct_1(sK3,sK5) != k1_funct_1(sK4,sK5)
    | ~ r1_partfun1(sK3,sK4) ),
    inference(cnf_transformation,[],[f34])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f22])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_partfun1(X0,X1)
      | k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1))
      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1250,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1616,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1250])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1257,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X1_46,X2_46)))
    | k1_relset_1(X1_46,X2_46,X0_46) = k1_relat_1(X0_46) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1609,plain,
    ( k1_relset_1(X0_46,X1_46,X2_46) = k1_relat_1(X2_46)
    | m1_subset_1(X2_46,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1257])).

cnf(c_2003,plain,
    ( k1_relset_1(sK2,sK2,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1616,c_1609])).

cnf(c_9,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k1_relset_1(X1,X1,X0) = X1 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_14,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_202,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k1_relset_1(X1,X1,X0) = X1
    | sK2 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_14])).

cnf(c_203,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(sK4)
    | k1_relset_1(sK2,sK2,sK4) = sK2 ),
    inference(unflattening,[status(thm)],[c_202])).

cnf(c_15,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_205,plain,
    ( k1_relset_1(sK2,sK2,sK4) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_203,c_15,c_13])).

cnf(c_1246,plain,
    ( k1_relset_1(sK2,sK2,sK4) = sK2 ),
    inference(subtyping,[status(esa)],[c_205])).

cnf(c_2008,plain,
    ( k1_relat_1(sK4) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_2003,c_1246])).

cnf(c_7,plain,
    ( r1_partfun1(X0,X1)
    | r2_hidden(sK1(X0,X1),k1_relat_1(X0))
    | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1255,plain,
    ( r1_partfun1(X0_46,X1_46)
    | r2_hidden(sK1(X0_46,X1_46),k1_relat_1(X0_46))
    | ~ r1_tarski(k1_relat_1(X0_46),k1_relat_1(X1_46))
    | ~ v1_funct_1(X1_46)
    | ~ v1_funct_1(X0_46)
    | ~ v1_relat_1(X1_46)
    | ~ v1_relat_1(X0_46) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1611,plain,
    ( r1_partfun1(X0_46,X1_46) = iProver_top
    | r2_hidden(sK1(X0_46,X1_46),k1_relat_1(X0_46)) = iProver_top
    | r1_tarski(k1_relat_1(X0_46),k1_relat_1(X1_46)) != iProver_top
    | v1_funct_1(X1_46) != iProver_top
    | v1_funct_1(X0_46) != iProver_top
    | v1_relat_1(X0_46) != iProver_top
    | v1_relat_1(X1_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1255])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1248,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1618,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1248])).

cnf(c_2004,plain,
    ( k1_relset_1(sK2,sK2,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1618,c_1609])).

cnf(c_12,negated_conjecture,
    ( r1_partfun1(sK3,sK4)
    | ~ r2_hidden(X0,k1_relset_1(sK2,sK2,sK3))
    | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1251,negated_conjecture,
    ( r1_partfun1(sK3,sK4)
    | ~ r2_hidden(X0_48,k1_relset_1(sK2,sK2,sK3))
    | k1_funct_1(sK3,X0_48) = k1_funct_1(sK4,X0_48) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1615,plain,
    ( k1_funct_1(sK3,X0_48) = k1_funct_1(sK4,X0_48)
    | r1_partfun1(sK3,sK4) = iProver_top
    | r2_hidden(X0_48,k1_relset_1(sK2,sK2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1251])).

cnf(c_2119,plain,
    ( k1_funct_1(sK4,X0_48) = k1_funct_1(sK3,X0_48)
    | r1_partfun1(sK3,sK4) = iProver_top
    | r2_hidden(X0_48,k1_relat_1(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2004,c_1615])).

cnf(c_2260,plain,
    ( k1_funct_1(sK3,sK1(sK3,X0_46)) = k1_funct_1(sK4,sK1(sK3,X0_46))
    | r1_partfun1(sK3,X0_46) = iProver_top
    | r1_partfun1(sK3,sK4) = iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0_46)) != iProver_top
    | v1_funct_1(X0_46) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(X0_46) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1611,c_2119])).

cnf(c_17,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_18,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_19,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1259,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X1_46,X2_46)))
    | v1_relat_1(X0_46) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1758,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1259])).

cnf(c_1759,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1758])).

cnf(c_11,negated_conjecture,
    ( ~ r1_partfun1(sK3,sK4)
    | r2_hidden(sK5,k1_relset_1(sK2,sK2,sK3)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1252,negated_conjecture,
    ( ~ r1_partfun1(sK3,sK4)
    | r2_hidden(sK5,k1_relset_1(sK2,sK2,sK3)) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1614,plain,
    ( r1_partfun1(sK3,sK4) != iProver_top
    | r2_hidden(sK5,k1_relset_1(sK2,sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1252])).

cnf(c_2120,plain,
    ( r1_partfun1(sK3,sK4) != iProver_top
    | r2_hidden(sK5,k1_relat_1(sK3)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2004,c_1614])).

cnf(c_8,plain,
    ( ~ r1_partfun1(X0,X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k1_funct_1(X1,X2) = k1_funct_1(X0,X2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1254,plain,
    ( ~ r1_partfun1(X0_46,X1_46)
    | ~ r2_hidden(X0_48,k1_relat_1(X0_46))
    | ~ r1_tarski(k1_relat_1(X0_46),k1_relat_1(X1_46))
    | ~ v1_funct_1(X1_46)
    | ~ v1_funct_1(X0_46)
    | ~ v1_relat_1(X1_46)
    | ~ v1_relat_1(X0_46)
    | k1_funct_1(X1_46,X0_48) = k1_funct_1(X0_46,X0_48) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1612,plain,
    ( k1_funct_1(X0_46,X0_48) = k1_funct_1(X1_46,X0_48)
    | r1_partfun1(X1_46,X0_46) != iProver_top
    | r2_hidden(X0_48,k1_relat_1(X1_46)) != iProver_top
    | r1_tarski(k1_relat_1(X1_46),k1_relat_1(X0_46)) != iProver_top
    | v1_funct_1(X0_46) != iProver_top
    | v1_funct_1(X1_46) != iProver_top
    | v1_relat_1(X1_46) != iProver_top
    | v1_relat_1(X0_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1254])).

cnf(c_2346,plain,
    ( k1_funct_1(X0_46,X0_48) = k1_funct_1(sK4,X0_48)
    | r1_partfun1(X0_46,sK4) != iProver_top
    | r2_hidden(X0_48,k1_relat_1(X0_46)) != iProver_top
    | r1_tarski(k1_relat_1(X0_46),sK2) != iProver_top
    | v1_funct_1(X0_46) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(X0_46) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2008,c_1612])).

cnf(c_20,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_22,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1755,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1259])).

cnf(c_1756,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1755])).

cnf(c_2878,plain,
    ( v1_relat_1(X0_46) != iProver_top
    | k1_funct_1(X0_46,X0_48) = k1_funct_1(sK4,X0_48)
    | r1_partfun1(X0_46,sK4) != iProver_top
    | r2_hidden(X0_48,k1_relat_1(X0_46)) != iProver_top
    | r1_tarski(k1_relat_1(X0_46),sK2) != iProver_top
    | v1_funct_1(X0_46) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2346,c_20,c_22,c_1756])).

cnf(c_2879,plain,
    ( k1_funct_1(X0_46,X0_48) = k1_funct_1(sK4,X0_48)
    | r1_partfun1(X0_46,sK4) != iProver_top
    | r2_hidden(X0_48,k1_relat_1(X0_46)) != iProver_top
    | r1_tarski(k1_relat_1(X0_46),sK2) != iProver_top
    | v1_funct_1(X0_46) != iProver_top
    | v1_relat_1(X0_46) != iProver_top ),
    inference(renaming,[status(thm)],[c_2878])).

cnf(c_2892,plain,
    ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
    | r1_partfun1(sK3,sK4) != iProver_top
    | r1_tarski(k1_relat_1(sK3),sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2120,c_2879])).

cnf(c_10,negated_conjecture,
    ( ~ r1_partfun1(sK3,sK4)
    | k1_funct_1(sK3,sK5) != k1_funct_1(sK4,sK5) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1253,negated_conjecture,
    ( ~ r1_partfun1(sK3,sK4)
    | k1_funct_1(sK3,sK5) != k1_funct_1(sK4,sK5) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1308,plain,
    ( k1_funct_1(sK3,sK5) != k1_funct_1(sK4,sK5)
    | r1_partfun1(sK3,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1253])).

cnf(c_1269,plain,
    ( X0_49 != X1_49
    | X2_49 != X1_49
    | X2_49 = X0_49 ),
    theory(equality)).

cnf(c_1977,plain,
    ( k1_funct_1(sK4,sK5) != X0_49
    | k1_funct_1(sK3,sK5) != X0_49
    | k1_funct_1(sK3,sK5) = k1_funct_1(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_1269])).

cnf(c_2075,plain,
    ( k1_funct_1(sK4,sK5) != k1_funct_1(X0_46,sK5)
    | k1_funct_1(sK3,sK5) != k1_funct_1(X0_46,sK5)
    | k1_funct_1(sK3,sK5) = k1_funct_1(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_1977])).

cnf(c_2484,plain,
    ( k1_funct_1(sK4,sK5) != k1_funct_1(sK3,sK5)
    | k1_funct_1(sK3,sK5) = k1_funct_1(sK4,sK5)
    | k1_funct_1(sK3,sK5) != k1_funct_1(sK3,sK5) ),
    inference(instantiation,[status(thm)],[c_2075])).

cnf(c_1267,plain,
    ( X0_49 = X0_49 ),
    theory(equality)).

cnf(c_2659,plain,
    ( k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK5) ),
    inference(instantiation,[status(thm)],[c_1267])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1261,plain,
    ( r2_hidden(sK0(X0_46,X1_46),X0_46)
    | r1_tarski(X0_46,X1_46) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1605,plain,
    ( r2_hidden(sK0(X0_46,X1_46),X0_46) = iProver_top
    | r1_tarski(X0_46,X1_46) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1261])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1258,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X1_46,X2_46)))
    | m1_subset_1(k1_relset_1(X1_46,X2_46,X0_46),k1_zfmisc_1(X1_46)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1608,plain,
    ( m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X1_46,X2_46))) != iProver_top
    | m1_subset_1(k1_relset_1(X1_46,X2_46,X0_46),k1_zfmisc_1(X1_46)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1258])).

cnf(c_2135,plain,
    ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK2)) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2004,c_1608])).

cnf(c_2507,plain,
    ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2135,c_19])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1260,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(X1_46))
    | ~ r2_hidden(X0_48,X0_46)
    | r2_hidden(X0_48,X1_46) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1606,plain,
    ( m1_subset_1(X0_46,k1_zfmisc_1(X1_46)) != iProver_top
    | r2_hidden(X0_48,X0_46) != iProver_top
    | r2_hidden(X0_48,X1_46) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1260])).

cnf(c_2512,plain,
    ( r2_hidden(X0_48,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(X0_48,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2507,c_1606])).

cnf(c_2788,plain,
    ( r2_hidden(sK0(k1_relat_1(sK3),X0_46),sK2) = iProver_top
    | r1_tarski(k1_relat_1(sK3),X0_46) = iProver_top ),
    inference(superposition,[status(thm)],[c_1605,c_2512])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1262,plain,
    ( ~ r2_hidden(sK0(X0_46,X1_46),X1_46)
    | r1_tarski(X0_46,X1_46) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1604,plain,
    ( r2_hidden(sK0(X0_46,X1_46),X1_46) != iProver_top
    | r1_tarski(X0_46,X1_46) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1262])).

cnf(c_2822,plain,
    ( r1_tarski(k1_relat_1(sK3),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2788,c_1604])).

cnf(c_2994,plain,
    ( r1_partfun1(sK3,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2892,c_18,c_19,c_1308,c_1759,c_2484,c_2659,c_2822])).

cnf(c_3076,plain,
    ( v1_relat_1(X0_46) != iProver_top
    | r1_partfun1(sK3,X0_46) = iProver_top
    | k1_funct_1(sK3,sK1(sK3,X0_46)) = k1_funct_1(sK4,sK1(sK3,X0_46))
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0_46)) != iProver_top
    | v1_funct_1(X0_46) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2260,c_18,c_19,c_1308,c_1759,c_2484,c_2659,c_2822,c_2892])).

cnf(c_3077,plain,
    ( k1_funct_1(sK3,sK1(sK3,X0_46)) = k1_funct_1(sK4,sK1(sK3,X0_46))
    | r1_partfun1(sK3,X0_46) = iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0_46)) != iProver_top
    | v1_funct_1(X0_46) != iProver_top
    | v1_relat_1(X0_46) != iProver_top ),
    inference(renaming,[status(thm)],[c_3076])).

cnf(c_3089,plain,
    ( k1_funct_1(sK3,sK1(sK3,sK4)) = k1_funct_1(sK4,sK1(sK3,sK4))
    | r1_partfun1(sK3,sK4) = iProver_top
    | r1_tarski(k1_relat_1(sK3),sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2008,c_3077])).

cnf(c_3168,plain,
    ( k1_funct_1(sK3,sK1(sK3,sK4)) = k1_funct_1(sK4,sK1(sK3,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3089,c_18,c_19,c_20,c_22,c_1308,c_1756,c_1759,c_2484,c_2659,c_2822,c_2892])).

cnf(c_6,plain,
    ( r1_partfun1(X0,X1)
    | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k1_funct_1(X1,sK1(X0,X1)) != k1_funct_1(X0,sK1(X0,X1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1256,plain,
    ( r1_partfun1(X0_46,X1_46)
    | ~ r1_tarski(k1_relat_1(X0_46),k1_relat_1(X1_46))
    | ~ v1_funct_1(X1_46)
    | ~ v1_funct_1(X0_46)
    | ~ v1_relat_1(X1_46)
    | ~ v1_relat_1(X0_46)
    | k1_funct_1(X1_46,sK1(X0_46,X1_46)) != k1_funct_1(X0_46,sK1(X0_46,X1_46)) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1610,plain,
    ( k1_funct_1(X0_46,sK1(X1_46,X0_46)) != k1_funct_1(X1_46,sK1(X1_46,X0_46))
    | r1_partfun1(X1_46,X0_46) = iProver_top
    | r1_tarski(k1_relat_1(X1_46),k1_relat_1(X0_46)) != iProver_top
    | v1_funct_1(X0_46) != iProver_top
    | v1_funct_1(X1_46) != iProver_top
    | v1_relat_1(X1_46) != iProver_top
    | v1_relat_1(X0_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1256])).

cnf(c_3171,plain,
    ( r1_partfun1(sK3,sK4) = iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3168,c_1610])).

cnf(c_3172,plain,
    ( r1_partfun1(sK3,sK4) = iProver_top
    | r1_tarski(k1_relat_1(sK3),sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3171,c_2008])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3172,c_2994,c_2822,c_1759,c_1756,c_22,c_20,c_19,c_18])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:31:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 1.88/1.02  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.02  
% 1.88/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.88/1.02  
% 1.88/1.02  ------  iProver source info
% 1.88/1.02  
% 1.88/1.02  git: date: 2020-06-30 10:37:57 +0100
% 1.88/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.88/1.02  git: non_committed_changes: false
% 1.88/1.02  git: last_make_outside_of_git: false
% 1.88/1.02  
% 1.88/1.02  ------ 
% 1.88/1.02  
% 1.88/1.02  ------ Input Options
% 1.88/1.02  
% 1.88/1.02  --out_options                           all
% 1.88/1.02  --tptp_safe_out                         true
% 1.88/1.02  --problem_path                          ""
% 1.88/1.02  --include_path                          ""
% 1.88/1.02  --clausifier                            res/vclausify_rel
% 1.88/1.02  --clausifier_options                    --mode clausify
% 1.88/1.02  --stdin                                 false
% 1.88/1.02  --stats_out                             all
% 1.88/1.02  
% 1.88/1.02  ------ General Options
% 1.88/1.02  
% 1.88/1.02  --fof                                   false
% 1.88/1.02  --time_out_real                         305.
% 1.88/1.02  --time_out_virtual                      -1.
% 1.88/1.02  --symbol_type_check                     false
% 1.88/1.02  --clausify_out                          false
% 1.88/1.02  --sig_cnt_out                           false
% 1.88/1.02  --trig_cnt_out                          false
% 1.88/1.02  --trig_cnt_out_tolerance                1.
% 1.88/1.02  --trig_cnt_out_sk_spl                   false
% 1.88/1.02  --abstr_cl_out                          false
% 1.88/1.02  
% 1.88/1.02  ------ Global Options
% 1.88/1.02  
% 1.88/1.02  --schedule                              default
% 1.88/1.02  --add_important_lit                     false
% 1.88/1.02  --prop_solver_per_cl                    1000
% 1.88/1.02  --min_unsat_core                        false
% 1.88/1.02  --soft_assumptions                      false
% 1.88/1.02  --soft_lemma_size                       3
% 1.88/1.02  --prop_impl_unit_size                   0
% 1.88/1.02  --prop_impl_unit                        []
% 1.88/1.02  --share_sel_clauses                     true
% 1.88/1.02  --reset_solvers                         false
% 1.88/1.02  --bc_imp_inh                            [conj_cone]
% 1.88/1.02  --conj_cone_tolerance                   3.
% 1.88/1.02  --extra_neg_conj                        none
% 1.88/1.02  --large_theory_mode                     true
% 1.88/1.02  --prolific_symb_bound                   200
% 1.88/1.02  --lt_threshold                          2000
% 1.88/1.02  --clause_weak_htbl                      true
% 1.88/1.02  --gc_record_bc_elim                     false
% 1.88/1.02  
% 1.88/1.02  ------ Preprocessing Options
% 1.88/1.02  
% 1.88/1.02  --preprocessing_flag                    true
% 1.88/1.02  --time_out_prep_mult                    0.1
% 1.88/1.02  --splitting_mode                        input
% 1.88/1.02  --splitting_grd                         true
% 1.88/1.02  --splitting_cvd                         false
% 1.88/1.02  --splitting_cvd_svl                     false
% 1.88/1.02  --splitting_nvd                         32
% 1.88/1.02  --sub_typing                            true
% 1.88/1.02  --prep_gs_sim                           true
% 1.88/1.02  --prep_unflatten                        true
% 1.88/1.02  --prep_res_sim                          true
% 1.88/1.02  --prep_upred                            true
% 1.88/1.02  --prep_sem_filter                       exhaustive
% 1.88/1.02  --prep_sem_filter_out                   false
% 1.88/1.02  --pred_elim                             true
% 1.88/1.02  --res_sim_input                         true
% 1.88/1.02  --eq_ax_congr_red                       true
% 1.88/1.02  --pure_diseq_elim                       true
% 1.88/1.02  --brand_transform                       false
% 1.88/1.02  --non_eq_to_eq                          false
% 1.88/1.02  --prep_def_merge                        true
% 1.88/1.02  --prep_def_merge_prop_impl              false
% 1.88/1.02  --prep_def_merge_mbd                    true
% 1.88/1.02  --prep_def_merge_tr_red                 false
% 1.88/1.02  --prep_def_merge_tr_cl                  false
% 1.88/1.02  --smt_preprocessing                     true
% 1.88/1.02  --smt_ac_axioms                         fast
% 1.88/1.02  --preprocessed_out                      false
% 1.88/1.02  --preprocessed_stats                    false
% 1.88/1.02  
% 1.88/1.02  ------ Abstraction refinement Options
% 1.88/1.02  
% 1.88/1.02  --abstr_ref                             []
% 1.88/1.02  --abstr_ref_prep                        false
% 1.88/1.02  --abstr_ref_until_sat                   false
% 1.88/1.02  --abstr_ref_sig_restrict                funpre
% 1.88/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 1.88/1.02  --abstr_ref_under                       []
% 1.88/1.02  
% 1.88/1.02  ------ SAT Options
% 1.88/1.02  
% 1.88/1.02  --sat_mode                              false
% 1.88/1.02  --sat_fm_restart_options                ""
% 1.88/1.02  --sat_gr_def                            false
% 1.88/1.02  --sat_epr_types                         true
% 1.88/1.02  --sat_non_cyclic_types                  false
% 1.88/1.02  --sat_finite_models                     false
% 1.88/1.02  --sat_fm_lemmas                         false
% 1.88/1.02  --sat_fm_prep                           false
% 1.88/1.02  --sat_fm_uc_incr                        true
% 1.88/1.02  --sat_out_model                         small
% 1.88/1.02  --sat_out_clauses                       false
% 1.88/1.02  
% 1.88/1.02  ------ QBF Options
% 1.88/1.02  
% 1.88/1.02  --qbf_mode                              false
% 1.88/1.02  --qbf_elim_univ                         false
% 1.88/1.02  --qbf_dom_inst                          none
% 1.88/1.02  --qbf_dom_pre_inst                      false
% 1.88/1.02  --qbf_sk_in                             false
% 1.88/1.02  --qbf_pred_elim                         true
% 1.88/1.02  --qbf_split                             512
% 1.88/1.02  
% 1.88/1.02  ------ BMC1 Options
% 1.88/1.02  
% 1.88/1.02  --bmc1_incremental                      false
% 1.88/1.02  --bmc1_axioms                           reachable_all
% 1.88/1.02  --bmc1_min_bound                        0
% 1.88/1.02  --bmc1_max_bound                        -1
% 1.88/1.02  --bmc1_max_bound_default                -1
% 1.88/1.02  --bmc1_symbol_reachability              true
% 1.88/1.02  --bmc1_property_lemmas                  false
% 1.88/1.02  --bmc1_k_induction                      false
% 1.88/1.02  --bmc1_non_equiv_states                 false
% 1.88/1.02  --bmc1_deadlock                         false
% 1.88/1.02  --bmc1_ucm                              false
% 1.88/1.02  --bmc1_add_unsat_core                   none
% 1.88/1.02  --bmc1_unsat_core_children              false
% 1.88/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 1.88/1.02  --bmc1_out_stat                         full
% 1.88/1.02  --bmc1_ground_init                      false
% 1.88/1.02  --bmc1_pre_inst_next_state              false
% 1.88/1.02  --bmc1_pre_inst_state                   false
% 1.88/1.02  --bmc1_pre_inst_reach_state             false
% 1.88/1.02  --bmc1_out_unsat_core                   false
% 1.88/1.02  --bmc1_aig_witness_out                  false
% 1.88/1.02  --bmc1_verbose                          false
% 1.88/1.02  --bmc1_dump_clauses_tptp                false
% 1.88/1.02  --bmc1_dump_unsat_core_tptp             false
% 1.88/1.02  --bmc1_dump_file                        -
% 1.88/1.02  --bmc1_ucm_expand_uc_limit              128
% 1.88/1.02  --bmc1_ucm_n_expand_iterations          6
% 1.88/1.02  --bmc1_ucm_extend_mode                  1
% 1.88/1.02  --bmc1_ucm_init_mode                    2
% 1.88/1.02  --bmc1_ucm_cone_mode                    none
% 1.88/1.02  --bmc1_ucm_reduced_relation_type        0
% 1.88/1.02  --bmc1_ucm_relax_model                  4
% 1.88/1.02  --bmc1_ucm_full_tr_after_sat            true
% 1.88/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 1.88/1.02  --bmc1_ucm_layered_model                none
% 1.88/1.02  --bmc1_ucm_max_lemma_size               10
% 1.88/1.02  
% 1.88/1.02  ------ AIG Options
% 1.88/1.02  
% 1.88/1.02  --aig_mode                              false
% 1.88/1.02  
% 1.88/1.02  ------ Instantiation Options
% 1.88/1.02  
% 1.88/1.02  --instantiation_flag                    true
% 1.88/1.02  --inst_sos_flag                         false
% 1.88/1.02  --inst_sos_phase                        true
% 1.88/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.88/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.88/1.02  --inst_lit_sel_side                     num_symb
% 1.88/1.02  --inst_solver_per_active                1400
% 1.88/1.02  --inst_solver_calls_frac                1.
% 1.88/1.02  --inst_passive_queue_type               priority_queues
% 1.88/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.88/1.02  --inst_passive_queues_freq              [25;2]
% 1.88/1.02  --inst_dismatching                      true
% 1.88/1.02  --inst_eager_unprocessed_to_passive     true
% 1.88/1.02  --inst_prop_sim_given                   true
% 1.88/1.02  --inst_prop_sim_new                     false
% 1.88/1.02  --inst_subs_new                         false
% 1.88/1.02  --inst_eq_res_simp                      false
% 1.88/1.02  --inst_subs_given                       false
% 1.88/1.02  --inst_orphan_elimination               true
% 1.88/1.02  --inst_learning_loop_flag               true
% 1.88/1.02  --inst_learning_start                   3000
% 1.88/1.02  --inst_learning_factor                  2
% 1.88/1.02  --inst_start_prop_sim_after_learn       3
% 1.88/1.02  --inst_sel_renew                        solver
% 1.88/1.02  --inst_lit_activity_flag                true
% 1.88/1.02  --inst_restr_to_given                   false
% 1.88/1.02  --inst_activity_threshold               500
% 1.88/1.02  --inst_out_proof                        true
% 1.88/1.02  
% 1.88/1.02  ------ Resolution Options
% 1.88/1.02  
% 1.88/1.02  --resolution_flag                       true
% 1.88/1.02  --res_lit_sel                           adaptive
% 1.88/1.02  --res_lit_sel_side                      none
% 1.88/1.02  --res_ordering                          kbo
% 1.88/1.02  --res_to_prop_solver                    active
% 1.88/1.02  --res_prop_simpl_new                    false
% 1.88/1.02  --res_prop_simpl_given                  true
% 1.88/1.02  --res_passive_queue_type                priority_queues
% 1.88/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.88/1.02  --res_passive_queues_freq               [15;5]
% 1.88/1.02  --res_forward_subs                      full
% 1.88/1.02  --res_backward_subs                     full
% 1.88/1.02  --res_forward_subs_resolution           true
% 1.88/1.02  --res_backward_subs_resolution          true
% 1.88/1.02  --res_orphan_elimination                true
% 1.88/1.02  --res_time_limit                        2.
% 1.88/1.02  --res_out_proof                         true
% 1.88/1.02  
% 1.88/1.02  ------ Superposition Options
% 1.88/1.02  
% 1.88/1.02  --superposition_flag                    true
% 1.88/1.02  --sup_passive_queue_type                priority_queues
% 1.88/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.88/1.02  --sup_passive_queues_freq               [8;1;4]
% 1.88/1.02  --demod_completeness_check              fast
% 1.88/1.02  --demod_use_ground                      true
% 1.88/1.02  --sup_to_prop_solver                    passive
% 1.88/1.02  --sup_prop_simpl_new                    true
% 1.88/1.02  --sup_prop_simpl_given                  true
% 1.88/1.02  --sup_fun_splitting                     false
% 1.88/1.02  --sup_smt_interval                      50000
% 1.88/1.02  
% 1.88/1.02  ------ Superposition Simplification Setup
% 1.88/1.02  
% 1.88/1.02  --sup_indices_passive                   []
% 1.88/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.88/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.88/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.88/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 1.88/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.88/1.02  --sup_full_bw                           [BwDemod]
% 1.88/1.02  --sup_immed_triv                        [TrivRules]
% 1.88/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.88/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.88/1.02  --sup_immed_bw_main                     []
% 1.88/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.88/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 1.88/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.88/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.88/1.02  
% 1.88/1.02  ------ Combination Options
% 1.88/1.02  
% 1.88/1.02  --comb_res_mult                         3
% 1.88/1.02  --comb_sup_mult                         2
% 1.88/1.02  --comb_inst_mult                        10
% 1.88/1.02  
% 1.88/1.02  ------ Debug Options
% 1.88/1.02  
% 1.88/1.02  --dbg_backtrace                         false
% 1.88/1.02  --dbg_dump_prop_clauses                 false
% 1.88/1.02  --dbg_dump_prop_clauses_file            -
% 1.88/1.02  --dbg_out_stat                          false
% 1.88/1.02  ------ Parsing...
% 1.88/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.88/1.02  
% 1.88/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 1.88/1.02  
% 1.88/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.88/1.02  
% 1.88/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.88/1.02  ------ Proving...
% 1.88/1.02  ------ Problem Properties 
% 1.88/1.02  
% 1.88/1.02  
% 1.88/1.02  clauses                                 17
% 1.88/1.02  conjectures                             7
% 1.88/1.02  EPR                                     2
% 1.88/1.02  Horn                                    14
% 1.88/1.02  unary                                   5
% 1.88/1.02  binary                                  7
% 1.88/1.02  lits                                    47
% 1.88/1.02  lits eq                                 6
% 1.88/1.02  fd_pure                                 0
% 1.88/1.02  fd_pseudo                               0
% 1.88/1.02  fd_cond                                 0
% 1.88/1.02  fd_pseudo_cond                          0
% 1.88/1.02  AC symbols                              0
% 1.88/1.02  
% 1.88/1.02  ------ Schedule dynamic 5 is on 
% 1.88/1.02  
% 1.88/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.88/1.02  
% 1.88/1.02  
% 1.88/1.02  ------ 
% 1.88/1.02  Current options:
% 1.88/1.02  ------ 
% 1.88/1.02  
% 1.88/1.02  ------ Input Options
% 1.88/1.02  
% 1.88/1.02  --out_options                           all
% 1.88/1.02  --tptp_safe_out                         true
% 1.88/1.02  --problem_path                          ""
% 1.88/1.02  --include_path                          ""
% 1.88/1.02  --clausifier                            res/vclausify_rel
% 1.88/1.02  --clausifier_options                    --mode clausify
% 1.88/1.02  --stdin                                 false
% 1.88/1.02  --stats_out                             all
% 1.88/1.02  
% 1.88/1.02  ------ General Options
% 1.88/1.02  
% 1.88/1.02  --fof                                   false
% 1.88/1.02  --time_out_real                         305.
% 1.88/1.02  --time_out_virtual                      -1.
% 1.88/1.02  --symbol_type_check                     false
% 1.88/1.02  --clausify_out                          false
% 1.88/1.02  --sig_cnt_out                           false
% 1.88/1.02  --trig_cnt_out                          false
% 1.88/1.02  --trig_cnt_out_tolerance                1.
% 1.88/1.02  --trig_cnt_out_sk_spl                   false
% 1.88/1.02  --abstr_cl_out                          false
% 1.88/1.02  
% 1.88/1.02  ------ Global Options
% 1.88/1.02  
% 1.88/1.02  --schedule                              default
% 1.88/1.02  --add_important_lit                     false
% 1.88/1.02  --prop_solver_per_cl                    1000
% 1.88/1.02  --min_unsat_core                        false
% 1.88/1.02  --soft_assumptions                      false
% 1.88/1.02  --soft_lemma_size                       3
% 1.88/1.02  --prop_impl_unit_size                   0
% 1.88/1.02  --prop_impl_unit                        []
% 1.88/1.02  --share_sel_clauses                     true
% 1.88/1.02  --reset_solvers                         false
% 1.88/1.02  --bc_imp_inh                            [conj_cone]
% 1.88/1.02  --conj_cone_tolerance                   3.
% 1.88/1.02  --extra_neg_conj                        none
% 1.88/1.02  --large_theory_mode                     true
% 1.88/1.02  --prolific_symb_bound                   200
% 1.88/1.02  --lt_threshold                          2000
% 1.88/1.02  --clause_weak_htbl                      true
% 1.88/1.02  --gc_record_bc_elim                     false
% 1.88/1.02  
% 1.88/1.02  ------ Preprocessing Options
% 1.88/1.02  
% 1.88/1.02  --preprocessing_flag                    true
% 1.88/1.02  --time_out_prep_mult                    0.1
% 1.88/1.02  --splitting_mode                        input
% 1.88/1.02  --splitting_grd                         true
% 1.88/1.02  --splitting_cvd                         false
% 1.88/1.02  --splitting_cvd_svl                     false
% 1.88/1.02  --splitting_nvd                         32
% 1.88/1.02  --sub_typing                            true
% 1.88/1.02  --prep_gs_sim                           true
% 1.88/1.02  --prep_unflatten                        true
% 1.88/1.02  --prep_res_sim                          true
% 1.88/1.02  --prep_upred                            true
% 1.88/1.02  --prep_sem_filter                       exhaustive
% 1.88/1.02  --prep_sem_filter_out                   false
% 1.88/1.02  --pred_elim                             true
% 1.88/1.02  --res_sim_input                         true
% 1.88/1.02  --eq_ax_congr_red                       true
% 1.88/1.02  --pure_diseq_elim                       true
% 1.88/1.02  --brand_transform                       false
% 1.88/1.02  --non_eq_to_eq                          false
% 1.88/1.02  --prep_def_merge                        true
% 1.88/1.02  --prep_def_merge_prop_impl              false
% 1.88/1.02  --prep_def_merge_mbd                    true
% 1.88/1.02  --prep_def_merge_tr_red                 false
% 1.88/1.02  --prep_def_merge_tr_cl                  false
% 1.88/1.02  --smt_preprocessing                     true
% 1.88/1.02  --smt_ac_axioms                         fast
% 1.88/1.02  --preprocessed_out                      false
% 1.88/1.02  --preprocessed_stats                    false
% 1.88/1.02  
% 1.88/1.02  ------ Abstraction refinement Options
% 1.88/1.02  
% 1.88/1.02  --abstr_ref                             []
% 1.88/1.02  --abstr_ref_prep                        false
% 1.88/1.02  --abstr_ref_until_sat                   false
% 1.88/1.02  --abstr_ref_sig_restrict                funpre
% 1.88/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 1.88/1.02  --abstr_ref_under                       []
% 1.88/1.02  
% 1.88/1.02  ------ SAT Options
% 1.88/1.02  
% 1.88/1.02  --sat_mode                              false
% 1.88/1.02  --sat_fm_restart_options                ""
% 1.88/1.02  --sat_gr_def                            false
% 1.88/1.02  --sat_epr_types                         true
% 1.88/1.02  --sat_non_cyclic_types                  false
% 1.88/1.02  --sat_finite_models                     false
% 1.88/1.02  --sat_fm_lemmas                         false
% 1.88/1.02  --sat_fm_prep                           false
% 1.88/1.02  --sat_fm_uc_incr                        true
% 1.88/1.02  --sat_out_model                         small
% 1.88/1.02  --sat_out_clauses                       false
% 1.88/1.02  
% 1.88/1.02  ------ QBF Options
% 1.88/1.02  
% 1.88/1.02  --qbf_mode                              false
% 1.88/1.02  --qbf_elim_univ                         false
% 1.88/1.02  --qbf_dom_inst                          none
% 1.88/1.02  --qbf_dom_pre_inst                      false
% 1.88/1.02  --qbf_sk_in                             false
% 1.88/1.02  --qbf_pred_elim                         true
% 1.88/1.02  --qbf_split                             512
% 1.88/1.02  
% 1.88/1.02  ------ BMC1 Options
% 1.88/1.02  
% 1.88/1.02  --bmc1_incremental                      false
% 1.88/1.02  --bmc1_axioms                           reachable_all
% 1.88/1.02  --bmc1_min_bound                        0
% 1.88/1.02  --bmc1_max_bound                        -1
% 1.88/1.02  --bmc1_max_bound_default                -1
% 1.88/1.02  --bmc1_symbol_reachability              true
% 1.88/1.02  --bmc1_property_lemmas                  false
% 1.88/1.02  --bmc1_k_induction                      false
% 1.88/1.02  --bmc1_non_equiv_states                 false
% 1.88/1.02  --bmc1_deadlock                         false
% 1.88/1.02  --bmc1_ucm                              false
% 1.88/1.02  --bmc1_add_unsat_core                   none
% 1.88/1.02  --bmc1_unsat_core_children              false
% 1.88/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 1.88/1.02  --bmc1_out_stat                         full
% 1.88/1.02  --bmc1_ground_init                      false
% 1.88/1.02  --bmc1_pre_inst_next_state              false
% 1.88/1.02  --bmc1_pre_inst_state                   false
% 1.88/1.02  --bmc1_pre_inst_reach_state             false
% 1.88/1.02  --bmc1_out_unsat_core                   false
% 1.88/1.02  --bmc1_aig_witness_out                  false
% 1.88/1.02  --bmc1_verbose                          false
% 1.88/1.02  --bmc1_dump_clauses_tptp                false
% 1.88/1.02  --bmc1_dump_unsat_core_tptp             false
% 1.88/1.02  --bmc1_dump_file                        -
% 1.88/1.02  --bmc1_ucm_expand_uc_limit              128
% 1.88/1.02  --bmc1_ucm_n_expand_iterations          6
% 1.88/1.02  --bmc1_ucm_extend_mode                  1
% 1.88/1.02  --bmc1_ucm_init_mode                    2
% 1.88/1.02  --bmc1_ucm_cone_mode                    none
% 1.88/1.02  --bmc1_ucm_reduced_relation_type        0
% 1.88/1.02  --bmc1_ucm_relax_model                  4
% 1.88/1.02  --bmc1_ucm_full_tr_after_sat            true
% 1.88/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 1.88/1.02  --bmc1_ucm_layered_model                none
% 1.88/1.02  --bmc1_ucm_max_lemma_size               10
% 1.88/1.02  
% 1.88/1.02  ------ AIG Options
% 1.88/1.02  
% 1.88/1.02  --aig_mode                              false
% 1.88/1.02  
% 1.88/1.02  ------ Instantiation Options
% 1.88/1.02  
% 1.88/1.02  --instantiation_flag                    true
% 1.88/1.02  --inst_sos_flag                         false
% 1.88/1.02  --inst_sos_phase                        true
% 1.88/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.88/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.88/1.02  --inst_lit_sel_side                     none
% 1.88/1.02  --inst_solver_per_active                1400
% 1.88/1.02  --inst_solver_calls_frac                1.
% 1.88/1.02  --inst_passive_queue_type               priority_queues
% 1.88/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.88/1.02  --inst_passive_queues_freq              [25;2]
% 1.88/1.02  --inst_dismatching                      true
% 1.88/1.02  --inst_eager_unprocessed_to_passive     true
% 1.88/1.02  --inst_prop_sim_given                   true
% 1.88/1.02  --inst_prop_sim_new                     false
% 1.88/1.02  --inst_subs_new                         false
% 1.88/1.02  --inst_eq_res_simp                      false
% 1.88/1.02  --inst_subs_given                       false
% 1.88/1.02  --inst_orphan_elimination               true
% 1.88/1.02  --inst_learning_loop_flag               true
% 1.88/1.02  --inst_learning_start                   3000
% 1.88/1.02  --inst_learning_factor                  2
% 1.88/1.02  --inst_start_prop_sim_after_learn       3
% 1.88/1.02  --inst_sel_renew                        solver
% 1.88/1.02  --inst_lit_activity_flag                true
% 1.88/1.02  --inst_restr_to_given                   false
% 1.88/1.02  --inst_activity_threshold               500
% 1.88/1.02  --inst_out_proof                        true
% 1.88/1.02  
% 1.88/1.02  ------ Resolution Options
% 1.88/1.02  
% 1.88/1.02  --resolution_flag                       false
% 1.88/1.02  --res_lit_sel                           adaptive
% 1.88/1.02  --res_lit_sel_side                      none
% 1.88/1.02  --res_ordering                          kbo
% 1.88/1.02  --res_to_prop_solver                    active
% 1.88/1.02  --res_prop_simpl_new                    false
% 1.88/1.02  --res_prop_simpl_given                  true
% 1.88/1.02  --res_passive_queue_type                priority_queues
% 1.88/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.88/1.02  --res_passive_queues_freq               [15;5]
% 1.88/1.02  --res_forward_subs                      full
% 1.88/1.02  --res_backward_subs                     full
% 1.88/1.02  --res_forward_subs_resolution           true
% 1.88/1.02  --res_backward_subs_resolution          true
% 1.88/1.02  --res_orphan_elimination                true
% 1.88/1.02  --res_time_limit                        2.
% 1.88/1.02  --res_out_proof                         true
% 1.88/1.02  
% 1.88/1.02  ------ Superposition Options
% 1.88/1.02  
% 1.88/1.02  --superposition_flag                    true
% 1.88/1.02  --sup_passive_queue_type                priority_queues
% 1.88/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.88/1.02  --sup_passive_queues_freq               [8;1;4]
% 1.88/1.02  --demod_completeness_check              fast
% 1.88/1.02  --demod_use_ground                      true
% 1.88/1.02  --sup_to_prop_solver                    passive
% 1.88/1.02  --sup_prop_simpl_new                    true
% 1.88/1.02  --sup_prop_simpl_given                  true
% 1.88/1.02  --sup_fun_splitting                     false
% 1.88/1.02  --sup_smt_interval                      50000
% 1.88/1.02  
% 1.88/1.02  ------ Superposition Simplification Setup
% 1.88/1.02  
% 1.88/1.02  --sup_indices_passive                   []
% 1.88/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.88/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.88/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.88/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 1.88/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.88/1.02  --sup_full_bw                           [BwDemod]
% 1.88/1.02  --sup_immed_triv                        [TrivRules]
% 1.88/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.88/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.88/1.02  --sup_immed_bw_main                     []
% 1.88/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.88/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 1.88/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.88/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.88/1.02  
% 1.88/1.02  ------ Combination Options
% 1.88/1.02  
% 1.88/1.02  --comb_res_mult                         3
% 1.88/1.02  --comb_sup_mult                         2
% 1.88/1.02  --comb_inst_mult                        10
% 1.88/1.02  
% 1.88/1.02  ------ Debug Options
% 1.88/1.02  
% 1.88/1.02  --dbg_backtrace                         false
% 1.88/1.02  --dbg_dump_prop_clauses                 false
% 1.88/1.02  --dbg_dump_prop_clauses_file            -
% 1.88/1.02  --dbg_out_stat                          false
% 1.88/1.02  
% 1.88/1.02  
% 1.88/1.02  
% 1.88/1.02  
% 1.88/1.02  ------ Proving...
% 1.88/1.02  
% 1.88/1.02  
% 1.88/1.02  % SZS status Theorem for theBenchmark.p
% 1.88/1.02  
% 1.88/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 1.88/1.02  
% 1.88/1.02  fof(f8,conjecture,(
% 1.88/1.02    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r1_partfun1(X1,X2) <=> ! [X3] : (r2_hidden(X3,k1_relset_1(X0,X0,X1)) => k1_funct_1(X1,X3) = k1_funct_1(X2,X3)))))),
% 1.88/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.88/1.02  
% 1.88/1.02  fof(f9,negated_conjecture,(
% 1.88/1.02    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r1_partfun1(X1,X2) <=> ! [X3] : (r2_hidden(X3,k1_relset_1(X0,X0,X1)) => k1_funct_1(X1,X3) = k1_funct_1(X2,X3)))))),
% 1.88/1.02    inference(negated_conjecture,[],[f8])).
% 1.88/1.02  
% 1.88/1.02  fof(f20,plain,(
% 1.88/1.02    ? [X0,X1] : (? [X2] : ((r1_partfun1(X1,X2) <~> ! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(X2,X3) | ~r2_hidden(X3,k1_relset_1(X0,X0,X1)))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1)))),
% 1.88/1.02    inference(ennf_transformation,[],[f9])).
% 1.88/1.02  
% 1.88/1.02  fof(f21,plain,(
% 1.88/1.02    ? [X0,X1] : (? [X2] : ((r1_partfun1(X1,X2) <~> ! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(X2,X3) | ~r2_hidden(X3,k1_relset_1(X0,X0,X1)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1))),
% 1.88/1.02    inference(flattening,[],[f20])).
% 1.88/1.02  
% 1.88/1.02  fof(f28,plain,(
% 1.88/1.02    ? [X0,X1] : (? [X2] : (((? [X3] : (k1_funct_1(X1,X3) != k1_funct_1(X2,X3) & r2_hidden(X3,k1_relset_1(X0,X0,X1))) | ~r1_partfun1(X1,X2)) & (! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(X2,X3) | ~r2_hidden(X3,k1_relset_1(X0,X0,X1))) | r1_partfun1(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1))),
% 1.88/1.02    inference(nnf_transformation,[],[f21])).
% 1.88/1.02  
% 1.88/1.02  fof(f29,plain,(
% 1.88/1.02    ? [X0,X1] : (? [X2] : ((? [X3] : (k1_funct_1(X1,X3) != k1_funct_1(X2,X3) & r2_hidden(X3,k1_relset_1(X0,X0,X1))) | ~r1_partfun1(X1,X2)) & (! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(X2,X3) | ~r2_hidden(X3,k1_relset_1(X0,X0,X1))) | r1_partfun1(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1))),
% 1.88/1.02    inference(flattening,[],[f28])).
% 1.88/1.02  
% 1.88/1.02  fof(f30,plain,(
% 1.88/1.02    ? [X0,X1] : (? [X2] : ((? [X3] : (k1_funct_1(X1,X3) != k1_funct_1(X2,X3) & r2_hidden(X3,k1_relset_1(X0,X0,X1))) | ~r1_partfun1(X1,X2)) & (! [X4] : (k1_funct_1(X1,X4) = k1_funct_1(X2,X4) | ~r2_hidden(X4,k1_relset_1(X0,X0,X1))) | r1_partfun1(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1))),
% 1.88/1.02    inference(rectify,[],[f29])).
% 1.88/1.02  
% 1.88/1.02  fof(f33,plain,(
% 1.88/1.02    ( ! [X2,X0,X1] : (? [X3] : (k1_funct_1(X1,X3) != k1_funct_1(X2,X3) & r2_hidden(X3,k1_relset_1(X0,X0,X1))) => (k1_funct_1(X1,sK5) != k1_funct_1(X2,sK5) & r2_hidden(sK5,k1_relset_1(X0,X0,X1)))) )),
% 1.88/1.02    introduced(choice_axiom,[])).
% 1.88/1.02  
% 1.88/1.02  fof(f32,plain,(
% 1.88/1.03    ( ! [X0,X1] : (? [X2] : ((? [X3] : (k1_funct_1(X1,X3) != k1_funct_1(X2,X3) & r2_hidden(X3,k1_relset_1(X0,X0,X1))) | ~r1_partfun1(X1,X2)) & (! [X4] : (k1_funct_1(X1,X4) = k1_funct_1(X2,X4) | ~r2_hidden(X4,k1_relset_1(X0,X0,X1))) | r1_partfun1(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((? [X3] : (k1_funct_1(sK4,X3) != k1_funct_1(X1,X3) & r2_hidden(X3,k1_relset_1(X0,X0,X1))) | ~r1_partfun1(X1,sK4)) & (! [X4] : (k1_funct_1(sK4,X4) = k1_funct_1(X1,X4) | ~r2_hidden(X4,k1_relset_1(X0,X0,X1))) | r1_partfun1(X1,sK4)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(sK4,X0,X0) & v1_funct_1(sK4))) )),
% 1.88/1.03    introduced(choice_axiom,[])).
% 1.88/1.03  
% 1.88/1.03  fof(f31,plain,(
% 1.88/1.03    ? [X0,X1] : (? [X2] : ((? [X3] : (k1_funct_1(X1,X3) != k1_funct_1(X2,X3) & r2_hidden(X3,k1_relset_1(X0,X0,X1))) | ~r1_partfun1(X1,X2)) & (! [X4] : (k1_funct_1(X1,X4) = k1_funct_1(X2,X4) | ~r2_hidden(X4,k1_relset_1(X0,X0,X1))) | r1_partfun1(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1)) => (? [X2] : ((? [X3] : (k1_funct_1(sK3,X3) != k1_funct_1(X2,X3) & r2_hidden(X3,k1_relset_1(sK2,sK2,sK3))) | ~r1_partfun1(sK3,X2)) & (! [X4] : (k1_funct_1(sK3,X4) = k1_funct_1(X2,X4) | ~r2_hidden(X4,k1_relset_1(sK2,sK2,sK3))) | r1_partfun1(sK3,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(X2,sK2,sK2) & v1_funct_1(X2)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_1(sK3))),
% 1.88/1.03    introduced(choice_axiom,[])).
% 1.88/1.03  
% 1.88/1.03  fof(f34,plain,(
% 1.88/1.03    (((k1_funct_1(sK3,sK5) != k1_funct_1(sK4,sK5) & r2_hidden(sK5,k1_relset_1(sK2,sK2,sK3))) | ~r1_partfun1(sK3,sK4)) & (! [X4] : (k1_funct_1(sK3,X4) = k1_funct_1(sK4,X4) | ~r2_hidden(X4,k1_relset_1(sK2,sK2,sK3))) | r1_partfun1(sK3,sK4)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(sK4,sK2,sK2) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_1(sK3)),
% 1.88/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f30,f33,f32,f31])).
% 1.88/1.03  
% 1.88/1.03  fof(f49,plain,(
% 1.88/1.03    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 1.88/1.03    inference(cnf_transformation,[],[f34])).
% 1.88/1.03  
% 1.88/1.03  fof(f5,axiom,(
% 1.88/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.88/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.88/1.03  
% 1.88/1.03  fof(f15,plain,(
% 1.88/1.03    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.88/1.03    inference(ennf_transformation,[],[f5])).
% 1.88/1.03  
% 1.88/1.03  fof(f40,plain,(
% 1.88/1.03    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.88/1.03    inference(cnf_transformation,[],[f15])).
% 1.88/1.03  
% 1.88/1.03  fof(f7,axiom,(
% 1.88/1.03    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 1.88/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.88/1.03  
% 1.88/1.03  fof(f18,plain,(
% 1.88/1.03    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 1.88/1.03    inference(ennf_transformation,[],[f7])).
% 1.88/1.03  
% 1.88/1.03  fof(f19,plain,(
% 1.88/1.03    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 1.88/1.03    inference(flattening,[],[f18])).
% 1.88/1.03  
% 1.88/1.03  fof(f44,plain,(
% 1.88/1.03    ( ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 1.88/1.03    inference(cnf_transformation,[],[f19])).
% 1.88/1.03  
% 1.88/1.03  fof(f48,plain,(
% 1.88/1.03    v1_funct_2(sK4,sK2,sK2)),
% 1.88/1.03    inference(cnf_transformation,[],[f34])).
% 1.88/1.03  
% 1.88/1.03  fof(f47,plain,(
% 1.88/1.03    v1_funct_1(sK4)),
% 1.88/1.03    inference(cnf_transformation,[],[f34])).
% 1.88/1.03  
% 1.88/1.03  fof(f6,axiom,(
% 1.88/1.03    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) => (r1_partfun1(X0,X1) <=> ! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2))))))),
% 1.88/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.88/1.03  
% 1.88/1.03  fof(f16,plain,(
% 1.88/1.03    ! [X0] : (! [X1] : (((r1_partfun1(X0,X1) <=> ! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0)))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.88/1.03    inference(ennf_transformation,[],[f6])).
% 1.88/1.03  
% 1.88/1.03  fof(f17,plain,(
% 1.88/1.03    ! [X0] : (! [X1] : ((r1_partfun1(X0,X1) <=> ! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0)))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.88/1.03    inference(flattening,[],[f16])).
% 1.88/1.03  
% 1.88/1.03  fof(f24,plain,(
% 1.88/1.03    ! [X0] : (! [X1] : (((r1_partfun1(X0,X1) | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0)))) & (! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0))) | ~r1_partfun1(X0,X1))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.88/1.03    inference(nnf_transformation,[],[f17])).
% 1.88/1.03  
% 1.88/1.03  fof(f25,plain,(
% 1.88/1.03    ! [X0] : (! [X1] : (((r1_partfun1(X0,X1) | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0)))) & (! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r1_partfun1(X0,X1))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.88/1.03    inference(rectify,[],[f24])).
% 1.88/1.03  
% 1.88/1.03  fof(f26,plain,(
% 1.88/1.03    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1)) & r2_hidden(sK1(X0,X1),k1_relat_1(X0))))),
% 1.88/1.03    introduced(choice_axiom,[])).
% 1.88/1.03  
% 1.88/1.03  fof(f27,plain,(
% 1.88/1.03    ! [X0] : (! [X1] : (((r1_partfun1(X0,X1) | (k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1)) & r2_hidden(sK1(X0,X1),k1_relat_1(X0)))) & (! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r1_partfun1(X0,X1))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.88/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f25,f26])).
% 1.88/1.03  
% 1.88/1.03  fof(f42,plain,(
% 1.88/1.03    ( ! [X0,X1] : (r1_partfun1(X0,X1) | r2_hidden(sK1(X0,X1),k1_relat_1(X0)) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.88/1.03    inference(cnf_transformation,[],[f27])).
% 1.88/1.03  
% 1.88/1.03  fof(f46,plain,(
% 1.88/1.03    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 1.88/1.03    inference(cnf_transformation,[],[f34])).
% 1.88/1.03  
% 1.88/1.03  fof(f50,plain,(
% 1.88/1.03    ( ! [X4] : (k1_funct_1(sK3,X4) = k1_funct_1(sK4,X4) | ~r2_hidden(X4,k1_relset_1(sK2,sK2,sK3)) | r1_partfun1(sK3,sK4)) )),
% 1.88/1.03    inference(cnf_transformation,[],[f34])).
% 1.88/1.03  
% 1.88/1.03  fof(f45,plain,(
% 1.88/1.03    v1_funct_1(sK3)),
% 1.88/1.03    inference(cnf_transformation,[],[f34])).
% 1.88/1.03  
% 1.88/1.03  fof(f3,axiom,(
% 1.88/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.88/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.88/1.03  
% 1.88/1.03  fof(f13,plain,(
% 1.88/1.03    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.88/1.03    inference(ennf_transformation,[],[f3])).
% 1.88/1.03  
% 1.88/1.03  fof(f38,plain,(
% 1.88/1.03    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.88/1.03    inference(cnf_transformation,[],[f13])).
% 1.88/1.03  
% 1.88/1.03  fof(f51,plain,(
% 1.88/1.03    r2_hidden(sK5,k1_relset_1(sK2,sK2,sK3)) | ~r1_partfun1(sK3,sK4)),
% 1.88/1.03    inference(cnf_transformation,[],[f34])).
% 1.88/1.03  
% 1.88/1.03  fof(f41,plain,(
% 1.88/1.03    ( ! [X0,X3,X1] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r1_partfun1(X0,X1) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.88/1.03    inference(cnf_transformation,[],[f27])).
% 1.88/1.03  
% 1.88/1.03  fof(f52,plain,(
% 1.88/1.03    k1_funct_1(sK3,sK5) != k1_funct_1(sK4,sK5) | ~r1_partfun1(sK3,sK4)),
% 1.88/1.03    inference(cnf_transformation,[],[f34])).
% 1.88/1.03  
% 1.88/1.03  fof(f1,axiom,(
% 1.88/1.03    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.88/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.88/1.03  
% 1.88/1.03  fof(f10,plain,(
% 1.88/1.03    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 1.88/1.03    inference(unused_predicate_definition_removal,[],[f1])).
% 1.88/1.03  
% 1.88/1.03  fof(f11,plain,(
% 1.88/1.03    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 1.88/1.03    inference(ennf_transformation,[],[f10])).
% 1.88/1.03  
% 1.88/1.03  fof(f22,plain,(
% 1.88/1.03    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 1.88/1.03    introduced(choice_axiom,[])).
% 1.88/1.03  
% 1.88/1.03  fof(f23,plain,(
% 1.88/1.03    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 1.88/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f22])).
% 1.88/1.03  
% 1.88/1.03  fof(f35,plain,(
% 1.88/1.03    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 1.88/1.03    inference(cnf_transformation,[],[f23])).
% 1.88/1.03  
% 1.88/1.03  fof(f4,axiom,(
% 1.88/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 1.88/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.88/1.03  
% 1.88/1.03  fof(f14,plain,(
% 1.88/1.03    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.88/1.03    inference(ennf_transformation,[],[f4])).
% 1.88/1.03  
% 1.88/1.03  fof(f39,plain,(
% 1.88/1.03    ( ! [X2,X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.88/1.03    inference(cnf_transformation,[],[f14])).
% 1.88/1.03  
% 1.88/1.03  fof(f2,axiom,(
% 1.88/1.03    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.88/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.88/1.03  
% 1.88/1.03  fof(f12,plain,(
% 1.88/1.03    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.88/1.03    inference(ennf_transformation,[],[f2])).
% 1.88/1.03  
% 1.88/1.03  fof(f37,plain,(
% 1.88/1.03    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.88/1.03    inference(cnf_transformation,[],[f12])).
% 1.88/1.03  
% 1.88/1.03  fof(f36,plain,(
% 1.88/1.03    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 1.88/1.03    inference(cnf_transformation,[],[f23])).
% 1.88/1.03  
% 1.88/1.03  fof(f43,plain,(
% 1.88/1.03    ( ! [X0,X1] : (r1_partfun1(X0,X1) | k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1)) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.88/1.03    inference(cnf_transformation,[],[f27])).
% 1.88/1.03  
% 1.88/1.03  cnf(c_13,negated_conjecture,
% 1.88/1.03      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
% 1.88/1.03      inference(cnf_transformation,[],[f49]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_1250,negated_conjecture,
% 1.88/1.03      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
% 1.88/1.03      inference(subtyping,[status(esa)],[c_13]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_1616,plain,
% 1.88/1.03      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
% 1.88/1.03      inference(predicate_to_equality,[status(thm)],[c_1250]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_5,plain,
% 1.88/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.88/1.03      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 1.88/1.03      inference(cnf_transformation,[],[f40]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_1257,plain,
% 1.88/1.03      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X1_46,X2_46)))
% 1.88/1.03      | k1_relset_1(X1_46,X2_46,X0_46) = k1_relat_1(X0_46) ),
% 1.88/1.03      inference(subtyping,[status(esa)],[c_5]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_1609,plain,
% 1.88/1.03      ( k1_relset_1(X0_46,X1_46,X2_46) = k1_relat_1(X2_46)
% 1.88/1.03      | m1_subset_1(X2_46,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46))) != iProver_top ),
% 1.88/1.03      inference(predicate_to_equality,[status(thm)],[c_1257]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_2003,plain,
% 1.88/1.03      ( k1_relset_1(sK2,sK2,sK4) = k1_relat_1(sK4) ),
% 1.88/1.03      inference(superposition,[status(thm)],[c_1616,c_1609]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_9,plain,
% 1.88/1.03      ( ~ v1_funct_2(X0,X1,X1)
% 1.88/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.88/1.03      | ~ v1_funct_1(X0)
% 1.88/1.03      | k1_relset_1(X1,X1,X0) = X1 ),
% 1.88/1.03      inference(cnf_transformation,[],[f44]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_14,negated_conjecture,
% 1.88/1.03      ( v1_funct_2(sK4,sK2,sK2) ),
% 1.88/1.03      inference(cnf_transformation,[],[f48]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_202,plain,
% 1.88/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.88/1.03      | ~ v1_funct_1(X0)
% 1.88/1.03      | k1_relset_1(X1,X1,X0) = X1
% 1.88/1.03      | sK2 != X1
% 1.88/1.03      | sK4 != X0 ),
% 1.88/1.03      inference(resolution_lifted,[status(thm)],[c_9,c_14]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_203,plain,
% 1.88/1.03      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
% 1.88/1.03      | ~ v1_funct_1(sK4)
% 1.88/1.03      | k1_relset_1(sK2,sK2,sK4) = sK2 ),
% 1.88/1.03      inference(unflattening,[status(thm)],[c_202]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_15,negated_conjecture,
% 1.88/1.03      ( v1_funct_1(sK4) ),
% 1.88/1.03      inference(cnf_transformation,[],[f47]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_205,plain,
% 1.88/1.03      ( k1_relset_1(sK2,sK2,sK4) = sK2 ),
% 1.88/1.03      inference(global_propositional_subsumption,
% 1.88/1.03                [status(thm)],
% 1.88/1.03                [c_203,c_15,c_13]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_1246,plain,
% 1.88/1.03      ( k1_relset_1(sK2,sK2,sK4) = sK2 ),
% 1.88/1.03      inference(subtyping,[status(esa)],[c_205]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_2008,plain,
% 1.88/1.03      ( k1_relat_1(sK4) = sK2 ),
% 1.88/1.03      inference(light_normalisation,[status(thm)],[c_2003,c_1246]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_7,plain,
% 1.88/1.03      ( r1_partfun1(X0,X1)
% 1.88/1.03      | r2_hidden(sK1(X0,X1),k1_relat_1(X0))
% 1.88/1.03      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 1.88/1.03      | ~ v1_funct_1(X1)
% 1.88/1.03      | ~ v1_funct_1(X0)
% 1.88/1.03      | ~ v1_relat_1(X1)
% 1.88/1.03      | ~ v1_relat_1(X0) ),
% 1.88/1.03      inference(cnf_transformation,[],[f42]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_1255,plain,
% 1.88/1.03      ( r1_partfun1(X0_46,X1_46)
% 1.88/1.03      | r2_hidden(sK1(X0_46,X1_46),k1_relat_1(X0_46))
% 1.88/1.03      | ~ r1_tarski(k1_relat_1(X0_46),k1_relat_1(X1_46))
% 1.88/1.03      | ~ v1_funct_1(X1_46)
% 1.88/1.03      | ~ v1_funct_1(X0_46)
% 1.88/1.03      | ~ v1_relat_1(X1_46)
% 1.88/1.03      | ~ v1_relat_1(X0_46) ),
% 1.88/1.03      inference(subtyping,[status(esa)],[c_7]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_1611,plain,
% 1.88/1.03      ( r1_partfun1(X0_46,X1_46) = iProver_top
% 1.88/1.03      | r2_hidden(sK1(X0_46,X1_46),k1_relat_1(X0_46)) = iProver_top
% 1.88/1.03      | r1_tarski(k1_relat_1(X0_46),k1_relat_1(X1_46)) != iProver_top
% 1.88/1.03      | v1_funct_1(X1_46) != iProver_top
% 1.88/1.03      | v1_funct_1(X0_46) != iProver_top
% 1.88/1.03      | v1_relat_1(X0_46) != iProver_top
% 1.88/1.03      | v1_relat_1(X1_46) != iProver_top ),
% 1.88/1.03      inference(predicate_to_equality,[status(thm)],[c_1255]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_16,negated_conjecture,
% 1.88/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
% 1.88/1.03      inference(cnf_transformation,[],[f46]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_1248,negated_conjecture,
% 1.88/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
% 1.88/1.03      inference(subtyping,[status(esa)],[c_16]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_1618,plain,
% 1.88/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
% 1.88/1.03      inference(predicate_to_equality,[status(thm)],[c_1248]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_2004,plain,
% 1.88/1.03      ( k1_relset_1(sK2,sK2,sK3) = k1_relat_1(sK3) ),
% 1.88/1.03      inference(superposition,[status(thm)],[c_1618,c_1609]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_12,negated_conjecture,
% 1.88/1.03      ( r1_partfun1(sK3,sK4)
% 1.88/1.03      | ~ r2_hidden(X0,k1_relset_1(sK2,sK2,sK3))
% 1.88/1.03      | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0) ),
% 1.88/1.03      inference(cnf_transformation,[],[f50]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_1251,negated_conjecture,
% 1.88/1.03      ( r1_partfun1(sK3,sK4)
% 1.88/1.03      | ~ r2_hidden(X0_48,k1_relset_1(sK2,sK2,sK3))
% 1.88/1.03      | k1_funct_1(sK3,X0_48) = k1_funct_1(sK4,X0_48) ),
% 1.88/1.03      inference(subtyping,[status(esa)],[c_12]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_1615,plain,
% 1.88/1.03      ( k1_funct_1(sK3,X0_48) = k1_funct_1(sK4,X0_48)
% 1.88/1.03      | r1_partfun1(sK3,sK4) = iProver_top
% 1.88/1.03      | r2_hidden(X0_48,k1_relset_1(sK2,sK2,sK3)) != iProver_top ),
% 1.88/1.03      inference(predicate_to_equality,[status(thm)],[c_1251]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_2119,plain,
% 1.88/1.03      ( k1_funct_1(sK4,X0_48) = k1_funct_1(sK3,X0_48)
% 1.88/1.03      | r1_partfun1(sK3,sK4) = iProver_top
% 1.88/1.03      | r2_hidden(X0_48,k1_relat_1(sK3)) != iProver_top ),
% 1.88/1.03      inference(demodulation,[status(thm)],[c_2004,c_1615]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_2260,plain,
% 1.88/1.03      ( k1_funct_1(sK3,sK1(sK3,X0_46)) = k1_funct_1(sK4,sK1(sK3,X0_46))
% 1.88/1.03      | r1_partfun1(sK3,X0_46) = iProver_top
% 1.88/1.03      | r1_partfun1(sK3,sK4) = iProver_top
% 1.88/1.03      | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0_46)) != iProver_top
% 1.88/1.03      | v1_funct_1(X0_46) != iProver_top
% 1.88/1.03      | v1_funct_1(sK3) != iProver_top
% 1.88/1.03      | v1_relat_1(X0_46) != iProver_top
% 1.88/1.03      | v1_relat_1(sK3) != iProver_top ),
% 1.88/1.03      inference(superposition,[status(thm)],[c_1611,c_2119]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_17,negated_conjecture,
% 1.88/1.03      ( v1_funct_1(sK3) ),
% 1.88/1.03      inference(cnf_transformation,[],[f45]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_18,plain,
% 1.88/1.03      ( v1_funct_1(sK3) = iProver_top ),
% 1.88/1.03      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_19,plain,
% 1.88/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
% 1.88/1.03      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_3,plain,
% 1.88/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.88/1.03      | v1_relat_1(X0) ),
% 1.88/1.03      inference(cnf_transformation,[],[f38]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_1259,plain,
% 1.88/1.03      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X1_46,X2_46)))
% 1.88/1.03      | v1_relat_1(X0_46) ),
% 1.88/1.03      inference(subtyping,[status(esa)],[c_3]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_1758,plain,
% 1.88/1.03      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
% 1.88/1.03      | v1_relat_1(sK3) ),
% 1.88/1.03      inference(instantiation,[status(thm)],[c_1259]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_1759,plain,
% 1.88/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
% 1.88/1.03      | v1_relat_1(sK3) = iProver_top ),
% 1.88/1.03      inference(predicate_to_equality,[status(thm)],[c_1758]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_11,negated_conjecture,
% 1.88/1.03      ( ~ r1_partfun1(sK3,sK4)
% 1.88/1.03      | r2_hidden(sK5,k1_relset_1(sK2,sK2,sK3)) ),
% 1.88/1.03      inference(cnf_transformation,[],[f51]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_1252,negated_conjecture,
% 1.88/1.03      ( ~ r1_partfun1(sK3,sK4)
% 1.88/1.03      | r2_hidden(sK5,k1_relset_1(sK2,sK2,sK3)) ),
% 1.88/1.03      inference(subtyping,[status(esa)],[c_11]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_1614,plain,
% 1.88/1.03      ( r1_partfun1(sK3,sK4) != iProver_top
% 1.88/1.03      | r2_hidden(sK5,k1_relset_1(sK2,sK2,sK3)) = iProver_top ),
% 1.88/1.03      inference(predicate_to_equality,[status(thm)],[c_1252]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_2120,plain,
% 1.88/1.03      ( r1_partfun1(sK3,sK4) != iProver_top
% 1.88/1.03      | r2_hidden(sK5,k1_relat_1(sK3)) = iProver_top ),
% 1.88/1.03      inference(demodulation,[status(thm)],[c_2004,c_1614]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_8,plain,
% 1.88/1.03      ( ~ r1_partfun1(X0,X1)
% 1.88/1.03      | ~ r2_hidden(X2,k1_relat_1(X0))
% 1.88/1.03      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 1.88/1.03      | ~ v1_funct_1(X1)
% 1.88/1.03      | ~ v1_funct_1(X0)
% 1.88/1.03      | ~ v1_relat_1(X1)
% 1.88/1.03      | ~ v1_relat_1(X0)
% 1.88/1.03      | k1_funct_1(X1,X2) = k1_funct_1(X0,X2) ),
% 1.88/1.03      inference(cnf_transformation,[],[f41]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_1254,plain,
% 1.88/1.03      ( ~ r1_partfun1(X0_46,X1_46)
% 1.88/1.03      | ~ r2_hidden(X0_48,k1_relat_1(X0_46))
% 1.88/1.03      | ~ r1_tarski(k1_relat_1(X0_46),k1_relat_1(X1_46))
% 1.88/1.03      | ~ v1_funct_1(X1_46)
% 1.88/1.03      | ~ v1_funct_1(X0_46)
% 1.88/1.03      | ~ v1_relat_1(X1_46)
% 1.88/1.03      | ~ v1_relat_1(X0_46)
% 1.88/1.03      | k1_funct_1(X1_46,X0_48) = k1_funct_1(X0_46,X0_48) ),
% 1.88/1.03      inference(subtyping,[status(esa)],[c_8]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_1612,plain,
% 1.88/1.03      ( k1_funct_1(X0_46,X0_48) = k1_funct_1(X1_46,X0_48)
% 1.88/1.03      | r1_partfun1(X1_46,X0_46) != iProver_top
% 1.88/1.03      | r2_hidden(X0_48,k1_relat_1(X1_46)) != iProver_top
% 1.88/1.03      | r1_tarski(k1_relat_1(X1_46),k1_relat_1(X0_46)) != iProver_top
% 1.88/1.03      | v1_funct_1(X0_46) != iProver_top
% 1.88/1.03      | v1_funct_1(X1_46) != iProver_top
% 1.88/1.03      | v1_relat_1(X1_46) != iProver_top
% 1.88/1.03      | v1_relat_1(X0_46) != iProver_top ),
% 1.88/1.03      inference(predicate_to_equality,[status(thm)],[c_1254]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_2346,plain,
% 1.88/1.03      ( k1_funct_1(X0_46,X0_48) = k1_funct_1(sK4,X0_48)
% 1.88/1.03      | r1_partfun1(X0_46,sK4) != iProver_top
% 1.88/1.03      | r2_hidden(X0_48,k1_relat_1(X0_46)) != iProver_top
% 1.88/1.03      | r1_tarski(k1_relat_1(X0_46),sK2) != iProver_top
% 1.88/1.03      | v1_funct_1(X0_46) != iProver_top
% 1.88/1.03      | v1_funct_1(sK4) != iProver_top
% 1.88/1.03      | v1_relat_1(X0_46) != iProver_top
% 1.88/1.03      | v1_relat_1(sK4) != iProver_top ),
% 1.88/1.03      inference(superposition,[status(thm)],[c_2008,c_1612]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_20,plain,
% 1.88/1.03      ( v1_funct_1(sK4) = iProver_top ),
% 1.88/1.03      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_22,plain,
% 1.88/1.03      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
% 1.88/1.03      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_1755,plain,
% 1.88/1.03      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
% 1.88/1.03      | v1_relat_1(sK4) ),
% 1.88/1.03      inference(instantiation,[status(thm)],[c_1259]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_1756,plain,
% 1.88/1.03      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
% 1.88/1.03      | v1_relat_1(sK4) = iProver_top ),
% 1.88/1.03      inference(predicate_to_equality,[status(thm)],[c_1755]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_2878,plain,
% 1.88/1.03      ( v1_relat_1(X0_46) != iProver_top
% 1.88/1.03      | k1_funct_1(X0_46,X0_48) = k1_funct_1(sK4,X0_48)
% 1.88/1.03      | r1_partfun1(X0_46,sK4) != iProver_top
% 1.88/1.03      | r2_hidden(X0_48,k1_relat_1(X0_46)) != iProver_top
% 1.88/1.03      | r1_tarski(k1_relat_1(X0_46),sK2) != iProver_top
% 1.88/1.03      | v1_funct_1(X0_46) != iProver_top ),
% 1.88/1.03      inference(global_propositional_subsumption,
% 1.88/1.03                [status(thm)],
% 1.88/1.03                [c_2346,c_20,c_22,c_1756]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_2879,plain,
% 1.88/1.03      ( k1_funct_1(X0_46,X0_48) = k1_funct_1(sK4,X0_48)
% 1.88/1.03      | r1_partfun1(X0_46,sK4) != iProver_top
% 1.88/1.03      | r2_hidden(X0_48,k1_relat_1(X0_46)) != iProver_top
% 1.88/1.03      | r1_tarski(k1_relat_1(X0_46),sK2) != iProver_top
% 1.88/1.03      | v1_funct_1(X0_46) != iProver_top
% 1.88/1.03      | v1_relat_1(X0_46) != iProver_top ),
% 1.88/1.03      inference(renaming,[status(thm)],[c_2878]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_2892,plain,
% 1.88/1.03      ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
% 1.88/1.03      | r1_partfun1(sK3,sK4) != iProver_top
% 1.88/1.03      | r1_tarski(k1_relat_1(sK3),sK2) != iProver_top
% 1.88/1.03      | v1_funct_1(sK3) != iProver_top
% 1.88/1.03      | v1_relat_1(sK3) != iProver_top ),
% 1.88/1.03      inference(superposition,[status(thm)],[c_2120,c_2879]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_10,negated_conjecture,
% 1.88/1.03      ( ~ r1_partfun1(sK3,sK4)
% 1.88/1.03      | k1_funct_1(sK3,sK5) != k1_funct_1(sK4,sK5) ),
% 1.88/1.03      inference(cnf_transformation,[],[f52]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_1253,negated_conjecture,
% 1.88/1.03      ( ~ r1_partfun1(sK3,sK4)
% 1.88/1.03      | k1_funct_1(sK3,sK5) != k1_funct_1(sK4,sK5) ),
% 1.88/1.03      inference(subtyping,[status(esa)],[c_10]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_1308,plain,
% 1.88/1.03      ( k1_funct_1(sK3,sK5) != k1_funct_1(sK4,sK5)
% 1.88/1.03      | r1_partfun1(sK3,sK4) != iProver_top ),
% 1.88/1.03      inference(predicate_to_equality,[status(thm)],[c_1253]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_1269,plain,
% 1.88/1.03      ( X0_49 != X1_49 | X2_49 != X1_49 | X2_49 = X0_49 ),
% 1.88/1.03      theory(equality) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_1977,plain,
% 1.88/1.03      ( k1_funct_1(sK4,sK5) != X0_49
% 1.88/1.03      | k1_funct_1(sK3,sK5) != X0_49
% 1.88/1.03      | k1_funct_1(sK3,sK5) = k1_funct_1(sK4,sK5) ),
% 1.88/1.03      inference(instantiation,[status(thm)],[c_1269]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_2075,plain,
% 1.88/1.03      ( k1_funct_1(sK4,sK5) != k1_funct_1(X0_46,sK5)
% 1.88/1.03      | k1_funct_1(sK3,sK5) != k1_funct_1(X0_46,sK5)
% 1.88/1.03      | k1_funct_1(sK3,sK5) = k1_funct_1(sK4,sK5) ),
% 1.88/1.03      inference(instantiation,[status(thm)],[c_1977]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_2484,plain,
% 1.88/1.03      ( k1_funct_1(sK4,sK5) != k1_funct_1(sK3,sK5)
% 1.88/1.03      | k1_funct_1(sK3,sK5) = k1_funct_1(sK4,sK5)
% 1.88/1.03      | k1_funct_1(sK3,sK5) != k1_funct_1(sK3,sK5) ),
% 1.88/1.03      inference(instantiation,[status(thm)],[c_2075]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_1267,plain,( X0_49 = X0_49 ),theory(equality) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_2659,plain,
% 1.88/1.03      ( k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK5) ),
% 1.88/1.03      inference(instantiation,[status(thm)],[c_1267]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_1,plain,
% 1.88/1.03      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 1.88/1.03      inference(cnf_transformation,[],[f35]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_1261,plain,
% 1.88/1.03      ( r2_hidden(sK0(X0_46,X1_46),X0_46) | r1_tarski(X0_46,X1_46) ),
% 1.88/1.03      inference(subtyping,[status(esa)],[c_1]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_1605,plain,
% 1.88/1.03      ( r2_hidden(sK0(X0_46,X1_46),X0_46) = iProver_top
% 1.88/1.03      | r1_tarski(X0_46,X1_46) = iProver_top ),
% 1.88/1.03      inference(predicate_to_equality,[status(thm)],[c_1261]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_4,plain,
% 1.88/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.88/1.03      | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 1.88/1.03      inference(cnf_transformation,[],[f39]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_1258,plain,
% 1.88/1.03      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X1_46,X2_46)))
% 1.88/1.03      | m1_subset_1(k1_relset_1(X1_46,X2_46,X0_46),k1_zfmisc_1(X1_46)) ),
% 1.88/1.03      inference(subtyping,[status(esa)],[c_4]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_1608,plain,
% 1.88/1.03      ( m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X1_46,X2_46))) != iProver_top
% 1.88/1.03      | m1_subset_1(k1_relset_1(X1_46,X2_46,X0_46),k1_zfmisc_1(X1_46)) = iProver_top ),
% 1.88/1.03      inference(predicate_to_equality,[status(thm)],[c_1258]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_2135,plain,
% 1.88/1.03      ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK2)) = iProver_top
% 1.88/1.03      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top ),
% 1.88/1.03      inference(superposition,[status(thm)],[c_2004,c_1608]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_2507,plain,
% 1.88/1.03      ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK2)) = iProver_top ),
% 1.88/1.03      inference(global_propositional_subsumption,
% 1.88/1.03                [status(thm)],
% 1.88/1.03                [c_2135,c_19]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_2,plain,
% 1.88/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.88/1.03      | ~ r2_hidden(X2,X0)
% 1.88/1.03      | r2_hidden(X2,X1) ),
% 1.88/1.03      inference(cnf_transformation,[],[f37]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_1260,plain,
% 1.88/1.03      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(X1_46))
% 1.88/1.03      | ~ r2_hidden(X0_48,X0_46)
% 1.88/1.03      | r2_hidden(X0_48,X1_46) ),
% 1.88/1.03      inference(subtyping,[status(esa)],[c_2]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_1606,plain,
% 1.88/1.03      ( m1_subset_1(X0_46,k1_zfmisc_1(X1_46)) != iProver_top
% 1.88/1.03      | r2_hidden(X0_48,X0_46) != iProver_top
% 1.88/1.03      | r2_hidden(X0_48,X1_46) = iProver_top ),
% 1.88/1.03      inference(predicate_to_equality,[status(thm)],[c_1260]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_2512,plain,
% 1.88/1.03      ( r2_hidden(X0_48,k1_relat_1(sK3)) != iProver_top
% 1.88/1.03      | r2_hidden(X0_48,sK2) = iProver_top ),
% 1.88/1.03      inference(superposition,[status(thm)],[c_2507,c_1606]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_2788,plain,
% 1.88/1.03      ( r2_hidden(sK0(k1_relat_1(sK3),X0_46),sK2) = iProver_top
% 1.88/1.03      | r1_tarski(k1_relat_1(sK3),X0_46) = iProver_top ),
% 1.88/1.03      inference(superposition,[status(thm)],[c_1605,c_2512]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_0,plain,
% 1.88/1.03      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 1.88/1.03      inference(cnf_transformation,[],[f36]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_1262,plain,
% 1.88/1.03      ( ~ r2_hidden(sK0(X0_46,X1_46),X1_46) | r1_tarski(X0_46,X1_46) ),
% 1.88/1.03      inference(subtyping,[status(esa)],[c_0]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_1604,plain,
% 1.88/1.03      ( r2_hidden(sK0(X0_46,X1_46),X1_46) != iProver_top
% 1.88/1.03      | r1_tarski(X0_46,X1_46) = iProver_top ),
% 1.88/1.03      inference(predicate_to_equality,[status(thm)],[c_1262]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_2822,plain,
% 1.88/1.03      ( r1_tarski(k1_relat_1(sK3),sK2) = iProver_top ),
% 1.88/1.03      inference(superposition,[status(thm)],[c_2788,c_1604]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_2994,plain,
% 1.88/1.03      ( r1_partfun1(sK3,sK4) != iProver_top ),
% 1.88/1.03      inference(global_propositional_subsumption,
% 1.88/1.03                [status(thm)],
% 1.88/1.03                [c_2892,c_18,c_19,c_1308,c_1759,c_2484,c_2659,c_2822]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_3076,plain,
% 1.88/1.03      ( v1_relat_1(X0_46) != iProver_top
% 1.88/1.03      | r1_partfun1(sK3,X0_46) = iProver_top
% 1.88/1.03      | k1_funct_1(sK3,sK1(sK3,X0_46)) = k1_funct_1(sK4,sK1(sK3,X0_46))
% 1.88/1.03      | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0_46)) != iProver_top
% 1.88/1.03      | v1_funct_1(X0_46) != iProver_top ),
% 1.88/1.03      inference(global_propositional_subsumption,
% 1.88/1.03                [status(thm)],
% 1.88/1.03                [c_2260,c_18,c_19,c_1308,c_1759,c_2484,c_2659,c_2822,
% 1.88/1.03                 c_2892]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_3077,plain,
% 1.88/1.03      ( k1_funct_1(sK3,sK1(sK3,X0_46)) = k1_funct_1(sK4,sK1(sK3,X0_46))
% 1.88/1.03      | r1_partfun1(sK3,X0_46) = iProver_top
% 1.88/1.03      | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0_46)) != iProver_top
% 1.88/1.03      | v1_funct_1(X0_46) != iProver_top
% 1.88/1.03      | v1_relat_1(X0_46) != iProver_top ),
% 1.88/1.03      inference(renaming,[status(thm)],[c_3076]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_3089,plain,
% 1.88/1.03      ( k1_funct_1(sK3,sK1(sK3,sK4)) = k1_funct_1(sK4,sK1(sK3,sK4))
% 1.88/1.03      | r1_partfun1(sK3,sK4) = iProver_top
% 1.88/1.03      | r1_tarski(k1_relat_1(sK3),sK2) != iProver_top
% 1.88/1.03      | v1_funct_1(sK4) != iProver_top
% 1.88/1.03      | v1_relat_1(sK4) != iProver_top ),
% 1.88/1.03      inference(superposition,[status(thm)],[c_2008,c_3077]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_3168,plain,
% 1.88/1.03      ( k1_funct_1(sK3,sK1(sK3,sK4)) = k1_funct_1(sK4,sK1(sK3,sK4)) ),
% 1.88/1.03      inference(global_propositional_subsumption,
% 1.88/1.03                [status(thm)],
% 1.88/1.03                [c_3089,c_18,c_19,c_20,c_22,c_1308,c_1756,c_1759,c_2484,
% 1.88/1.03                 c_2659,c_2822,c_2892]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_6,plain,
% 1.88/1.03      ( r1_partfun1(X0,X1)
% 1.88/1.03      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 1.88/1.03      | ~ v1_funct_1(X1)
% 1.88/1.03      | ~ v1_funct_1(X0)
% 1.88/1.03      | ~ v1_relat_1(X1)
% 1.88/1.03      | ~ v1_relat_1(X0)
% 1.88/1.03      | k1_funct_1(X1,sK1(X0,X1)) != k1_funct_1(X0,sK1(X0,X1)) ),
% 1.88/1.03      inference(cnf_transformation,[],[f43]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_1256,plain,
% 1.88/1.03      ( r1_partfun1(X0_46,X1_46)
% 1.88/1.03      | ~ r1_tarski(k1_relat_1(X0_46),k1_relat_1(X1_46))
% 1.88/1.03      | ~ v1_funct_1(X1_46)
% 1.88/1.03      | ~ v1_funct_1(X0_46)
% 1.88/1.03      | ~ v1_relat_1(X1_46)
% 1.88/1.03      | ~ v1_relat_1(X0_46)
% 1.88/1.03      | k1_funct_1(X1_46,sK1(X0_46,X1_46)) != k1_funct_1(X0_46,sK1(X0_46,X1_46)) ),
% 1.88/1.03      inference(subtyping,[status(esa)],[c_6]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_1610,plain,
% 1.88/1.03      ( k1_funct_1(X0_46,sK1(X1_46,X0_46)) != k1_funct_1(X1_46,sK1(X1_46,X0_46))
% 1.88/1.03      | r1_partfun1(X1_46,X0_46) = iProver_top
% 1.88/1.03      | r1_tarski(k1_relat_1(X1_46),k1_relat_1(X0_46)) != iProver_top
% 1.88/1.03      | v1_funct_1(X0_46) != iProver_top
% 1.88/1.03      | v1_funct_1(X1_46) != iProver_top
% 1.88/1.03      | v1_relat_1(X1_46) != iProver_top
% 1.88/1.03      | v1_relat_1(X0_46) != iProver_top ),
% 1.88/1.03      inference(predicate_to_equality,[status(thm)],[c_1256]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_3171,plain,
% 1.88/1.03      ( r1_partfun1(sK3,sK4) = iProver_top
% 1.88/1.03      | r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4)) != iProver_top
% 1.88/1.03      | v1_funct_1(sK4) != iProver_top
% 1.88/1.03      | v1_funct_1(sK3) != iProver_top
% 1.88/1.03      | v1_relat_1(sK4) != iProver_top
% 1.88/1.03      | v1_relat_1(sK3) != iProver_top ),
% 1.88/1.03      inference(superposition,[status(thm)],[c_3168,c_1610]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_3172,plain,
% 1.88/1.03      ( r1_partfun1(sK3,sK4) = iProver_top
% 1.88/1.03      | r1_tarski(k1_relat_1(sK3),sK2) != iProver_top
% 1.88/1.03      | v1_funct_1(sK4) != iProver_top
% 1.88/1.03      | v1_funct_1(sK3) != iProver_top
% 1.88/1.03      | v1_relat_1(sK4) != iProver_top
% 1.88/1.03      | v1_relat_1(sK3) != iProver_top ),
% 1.88/1.03      inference(light_normalisation,[status(thm)],[c_3171,c_2008]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(contradiction,plain,
% 1.88/1.03      ( $false ),
% 1.88/1.03      inference(minisat,
% 1.88/1.03                [status(thm)],
% 1.88/1.03                [c_3172,c_2994,c_2822,c_1759,c_1756,c_22,c_20,c_19,c_18]) ).
% 1.88/1.03  
% 1.88/1.03  
% 1.88/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 1.88/1.03  
% 1.88/1.03  ------                               Statistics
% 1.88/1.03  
% 1.88/1.03  ------ General
% 1.88/1.03  
% 1.88/1.03  abstr_ref_over_cycles:                  0
% 1.88/1.03  abstr_ref_under_cycles:                 0
% 1.88/1.03  gc_basic_clause_elim:                   0
% 1.88/1.03  forced_gc_time:                         0
% 1.88/1.03  parsing_time:                           0.012
% 1.88/1.03  unif_index_cands_time:                  0.
% 1.88/1.03  unif_index_add_time:                    0.
% 1.88/1.03  orderings_time:                         0.
% 1.88/1.03  out_proof_time:                         0.008
% 1.88/1.03  total_time:                             0.188
% 1.88/1.03  num_of_symbols:                         53
% 1.88/1.03  num_of_terms:                           2181
% 1.88/1.03  
% 1.88/1.03  ------ Preprocessing
% 1.88/1.03  
% 1.88/1.03  num_of_splits:                          0
% 1.88/1.03  num_of_split_atoms:                     0
% 1.88/1.03  num_of_reused_defs:                     0
% 1.88/1.03  num_eq_ax_congr_red:                    18
% 1.88/1.03  num_of_sem_filtered_clauses:            1
% 1.88/1.03  num_of_subtypes:                        4
% 1.88/1.03  monotx_restored_types:                  0
% 1.88/1.03  sat_num_of_epr_types:                   0
% 1.88/1.03  sat_num_of_non_cyclic_types:            0
% 1.88/1.03  sat_guarded_non_collapsed_types:        0
% 1.88/1.03  num_pure_diseq_elim:                    0
% 1.88/1.03  simp_replaced_by:                       0
% 1.88/1.03  res_preprocessed:                       100
% 1.88/1.03  prep_upred:                             0
% 1.88/1.03  prep_unflattend:                        46
% 1.88/1.03  smt_new_axioms:                         0
% 1.88/1.03  pred_elim_cands:                        6
% 1.88/1.03  pred_elim:                              1
% 1.88/1.03  pred_elim_cl:                           1
% 1.88/1.03  pred_elim_cycles:                       5
% 1.88/1.03  merged_defs:                            0
% 1.88/1.03  merged_defs_ncl:                        0
% 1.88/1.03  bin_hyper_res:                          0
% 1.88/1.03  prep_cycles:                            4
% 1.88/1.03  pred_elim_time:                         0.029
% 1.88/1.03  splitting_time:                         0.
% 1.88/1.03  sem_filter_time:                        0.
% 1.88/1.03  monotx_time:                            0.
% 1.88/1.03  subtype_inf_time:                       0.
% 1.88/1.03  
% 1.88/1.03  ------ Problem properties
% 1.88/1.03  
% 1.88/1.03  clauses:                                17
% 1.88/1.03  conjectures:                            7
% 1.88/1.03  epr:                                    2
% 1.88/1.03  horn:                                   14
% 1.88/1.03  ground:                                 7
% 1.88/1.03  unary:                                  5
% 1.88/1.03  binary:                                 7
% 1.88/1.03  lits:                                   47
% 1.88/1.03  lits_eq:                                6
% 1.88/1.03  fd_pure:                                0
% 1.88/1.03  fd_pseudo:                              0
% 1.88/1.03  fd_cond:                                0
% 1.88/1.03  fd_pseudo_cond:                         0
% 1.88/1.03  ac_symbols:                             0
% 1.88/1.03  
% 1.88/1.03  ------ Propositional Solver
% 1.88/1.03  
% 1.88/1.03  prop_solver_calls:                      29
% 1.88/1.03  prop_fast_solver_calls:                 968
% 1.88/1.03  smt_solver_calls:                       0
% 1.88/1.03  smt_fast_solver_calls:                  0
% 1.88/1.03  prop_num_of_clauses:                    779
% 1.88/1.03  prop_preprocess_simplified:             3277
% 1.88/1.03  prop_fo_subsumed:                       42
% 1.88/1.03  prop_solver_time:                       0.
% 1.88/1.03  smt_solver_time:                        0.
% 1.88/1.03  smt_fast_solver_time:                   0.
% 1.88/1.03  prop_fast_solver_time:                  0.
% 1.88/1.03  prop_unsat_core_time:                   0.
% 1.88/1.03  
% 1.88/1.03  ------ QBF
% 1.88/1.03  
% 1.88/1.03  qbf_q_res:                              0
% 1.88/1.03  qbf_num_tautologies:                    0
% 1.88/1.03  qbf_prep_cycles:                        0
% 1.88/1.03  
% 1.88/1.03  ------ BMC1
% 1.88/1.03  
% 1.88/1.03  bmc1_current_bound:                     -1
% 1.88/1.03  bmc1_last_solved_bound:                 -1
% 1.88/1.03  bmc1_unsat_core_size:                   -1
% 1.88/1.03  bmc1_unsat_core_parents_size:           -1
% 1.88/1.03  bmc1_merge_next_fun:                    0
% 1.88/1.03  bmc1_unsat_core_clauses_time:           0.
% 1.88/1.03  
% 1.88/1.03  ------ Instantiation
% 1.88/1.03  
% 1.88/1.03  inst_num_of_clauses:                    241
% 1.88/1.03  inst_num_in_passive:                    38
% 1.88/1.03  inst_num_in_active:                     189
% 1.88/1.03  inst_num_in_unprocessed:                14
% 1.88/1.03  inst_num_of_loops:                      220
% 1.88/1.03  inst_num_of_learning_restarts:          0
% 1.88/1.03  inst_num_moves_active_passive:          25
% 1.88/1.03  inst_lit_activity:                      0
% 1.88/1.03  inst_lit_activity_moves:                0
% 1.88/1.03  inst_num_tautologies:                   0
% 1.88/1.03  inst_num_prop_implied:                  0
% 1.88/1.03  inst_num_existing_simplified:           0
% 1.88/1.03  inst_num_eq_res_simplified:             0
% 1.88/1.03  inst_num_child_elim:                    0
% 1.88/1.03  inst_num_of_dismatching_blockings:      35
% 1.88/1.03  inst_num_of_non_proper_insts:           254
% 1.88/1.03  inst_num_of_duplicates:                 0
% 1.88/1.03  inst_inst_num_from_inst_to_res:         0
% 1.88/1.03  inst_dismatching_checking_time:         0.
% 1.88/1.03  
% 1.88/1.03  ------ Resolution
% 1.88/1.03  
% 1.88/1.03  res_num_of_clauses:                     0
% 1.88/1.03  res_num_in_passive:                     0
% 1.88/1.03  res_num_in_active:                      0
% 1.88/1.03  res_num_of_loops:                       104
% 1.88/1.03  res_forward_subset_subsumed:            56
% 1.88/1.03  res_backward_subset_subsumed:           0
% 1.88/1.03  res_forward_subsumed:                   0
% 1.88/1.03  res_backward_subsumed:                  0
% 1.88/1.03  res_forward_subsumption_resolution:     0
% 1.88/1.03  res_backward_subsumption_resolution:    0
% 1.88/1.03  res_clause_to_clause_subsumption:       112
% 1.88/1.03  res_orphan_elimination:                 0
% 1.88/1.03  res_tautology_del:                      43
% 1.88/1.03  res_num_eq_res_simplified:              0
% 1.88/1.03  res_num_sel_changes:                    0
% 1.88/1.03  res_moves_from_active_to_pass:          0
% 1.88/1.03  
% 1.88/1.03  ------ Superposition
% 1.88/1.03  
% 1.88/1.03  sup_time_total:                         0.
% 1.88/1.03  sup_time_generating:                    0.
% 1.88/1.03  sup_time_sim_full:                      0.
% 1.88/1.03  sup_time_sim_immed:                     0.
% 1.88/1.03  
% 1.88/1.03  sup_num_of_clauses:                     55
% 1.88/1.03  sup_num_in_active:                      39
% 1.88/1.03  sup_num_in_passive:                     16
% 1.88/1.03  sup_num_of_loops:                       42
% 1.88/1.03  sup_fw_superposition:                   29
% 1.88/1.03  sup_bw_superposition:                   13
% 1.88/1.03  sup_immediate_simplified:               4
% 1.88/1.03  sup_given_eliminated:                   0
% 1.88/1.03  comparisons_done:                       0
% 1.88/1.03  comparisons_avoided:                    0
% 1.88/1.03  
% 1.88/1.03  ------ Simplifications
% 1.88/1.03  
% 1.88/1.03  
% 1.88/1.03  sim_fw_subset_subsumed:                 0
% 1.88/1.03  sim_bw_subset_subsumed:                 2
% 1.88/1.03  sim_fw_subsumed:                        0
% 1.88/1.03  sim_bw_subsumed:                        0
% 1.88/1.03  sim_fw_subsumption_res:                 0
% 1.88/1.03  sim_bw_subsumption_res:                 0
% 1.88/1.03  sim_tautology_del:                      2
% 1.88/1.03  sim_eq_tautology_del:                   2
% 1.88/1.03  sim_eq_res_simp:                        0
% 1.88/1.03  sim_fw_demodulated:                     0
% 1.88/1.03  sim_bw_demodulated:                     2
% 1.88/1.03  sim_light_normalised:                   5
% 1.88/1.03  sim_joinable_taut:                      0
% 1.88/1.03  sim_joinable_simp:                      0
% 1.88/1.03  sim_ac_normalised:                      0
% 1.88/1.03  sim_smt_subsumption:                    0
% 1.88/1.03  
%------------------------------------------------------------------------------
