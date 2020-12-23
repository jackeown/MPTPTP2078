%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:08:41 EST 2020

% Result     : Theorem 1.35s
% Output     : CNFRefutation 1.35s
% Verified   : 
% Statistics : Number of formulae       :  170 (22988 expanded)
%              Number of clauses        :  118 (6500 expanded)
%              Number of leaves         :   14 (5462 expanded)
%              Depth                    :   41
%              Number of atoms          :  710 (162562 expanded)
%              Number of equality atoms :  389 (39584 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( k1_funct_1(X1,X3) != k1_funct_1(X2,X3)
          & r2_hidden(X3,k1_relset_1(X0,X0,X1)) )
     => ( k1_funct_1(X1,sK4) != k1_funct_1(X2,sK4)
        & r2_hidden(sK4,k1_relset_1(X0,X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
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

fof(f29,plain,
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

fof(f32,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f28,f31,f30,f29])).

fof(f48,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f32])).

fof(f53,plain,
    ( r2_hidden(sK4,k1_relset_1(sK1,sK1,sK2))
    | ~ r1_partfun1(sK2,sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f50,plain,(
    v1_funct_2(sK3,sK1,sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f14])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f51,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f32])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f22,plain,(
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

fof(f23,plain,(
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
    inference(rectify,[],[f22])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1))
        & r2_hidden(sK0(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_partfun1(X0,X1)
      | r2_hidden(sK0(X0,X1),k1_relat_1(X0))
      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f52,plain,(
    ! [X4] :
      ( k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)
      | ~ r2_hidden(X4,k1_relset_1(sK1,sK1,sK2))
      | r1_partfun1(sK2,sK3) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f47,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f32])).

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

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f49,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ r1_partfun1(X0,X1)
      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_partfun1(X0,X1)
      | k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1))
      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f54,plain,
    ( k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4)
    | ~ r1_partfun1(sK2,sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f59,plain,(
    ! [X2,X1] :
      ( k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f39])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f57,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f42])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_634,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_20])).

cnf(c_635,plain,
    ( k1_relset_1(X0,X1,sK2) = k1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) ),
    inference(unflattening,[status(thm)],[c_634])).

cnf(c_2129,plain,
    ( k1_relset_1(sK1,sK1,sK2) = k1_relat_1(sK2) ),
    inference(equality_resolution,[status(thm)],[c_635])).

cnf(c_15,negated_conjecture,
    ( r2_hidden(sK4,k1_relset_1(sK1,sK1,sK2))
    | ~ r1_partfun1(sK2,sK3) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1882,plain,
    ( r2_hidden(sK4,k1_relset_1(sK1,sK1,sK2)) = iProver_top
    | r1_partfun1(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2398,plain,
    ( r2_hidden(sK4,k1_relat_1(sK2)) = iProver_top
    | r1_partfun1(sK2,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2129,c_1882])).

cnf(c_18,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_10,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_529,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_17])).

cnf(c_530,plain,
    ( ~ v1_funct_2(sK3,X0,X1)
    | k1_relset_1(X0,X1,sK3) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_529])).

cnf(c_1383,plain,
    ( k1_relset_1(X0,X1,sK3) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
    | sK1 != X0
    | sK1 != X1
    | sK3 != sK3
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_530])).

cnf(c_1384,plain,
    ( k1_relset_1(sK1,sK1,sK3) = sK1
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_1383])).

cnf(c_1923,plain,
    ( k1_relset_1(sK1,sK1,sK3) = sK1
    | k1_xboole_0 = sK1 ),
    inference(equality_resolution_simp,[status(thm)],[c_1384])).

cnf(c_565,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_17])).

cnf(c_566,plain,
    ( k1_relset_1(X0,X1,sK3) = k1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) ),
    inference(unflattening,[status(thm)],[c_565])).

cnf(c_2126,plain,
    ( k1_relset_1(sK1,sK1,sK3) = k1_relat_1(sK3) ),
    inference(equality_resolution,[status(thm)],[c_566])).

cnf(c_2738,plain,
    ( k1_relat_1(sK3) = sK1
    | sK1 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1923,c_2126])).

cnf(c_12,plain,
    ( r2_hidden(sK0(X0,X1),k1_relat_1(X0))
    | r1_partfun1(X0,X1)
    | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1885,plain,
    ( r2_hidden(sK0(X0,X1),k1_relat_1(X0)) = iProver_top
    | r1_partfun1(X0,X1) = iProver_top
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_16,negated_conjecture,
    ( ~ r2_hidden(X0,k1_relset_1(sK1,sK1,sK2))
    | r1_partfun1(sK2,sK3)
    | k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1881,plain,
    ( k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0)
    | r2_hidden(X0,k1_relset_1(sK1,sK1,sK2)) != iProver_top
    | r1_partfun1(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2397,plain,
    ( k1_funct_1(sK3,X0) = k1_funct_1(sK2,X0)
    | r2_hidden(X0,k1_relat_1(sK2)) != iProver_top
    | r1_partfun1(sK2,sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2129,c_1881])).

cnf(c_2598,plain,
    ( k1_funct_1(sK2,sK0(sK2,X0)) = k1_funct_1(sK3,sK0(sK2,X0))
    | r1_partfun1(sK2,X0) = iProver_top
    | r1_partfun1(sK2,sK3) = iProver_top
    | r1_tarski(k1_relat_1(sK2),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1885,c_2397])).

cnf(c_21,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_22,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1604,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2092,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) ),
    inference(instantiation,[status(thm)],[c_1604])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_643,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_20])).

cnf(c_644,plain,
    ( v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) ),
    inference(unflattening,[status(thm)],[c_643])).

cnf(c_2097,plain,
    ( v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) ),
    inference(instantiation,[status(thm)],[c_644])).

cnf(c_2101,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2097])).

cnf(c_2711,plain,
    ( v1_relat_1(X0) != iProver_top
    | k1_funct_1(sK2,sK0(sK2,X0)) = k1_funct_1(sK3,sK0(sK2,X0))
    | r1_partfun1(sK2,X0) = iProver_top
    | r1_partfun1(sK2,sK3) = iProver_top
    | r1_tarski(k1_relat_1(sK2),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2598,c_22,c_2092,c_2101])).

cnf(c_2712,plain,
    ( k1_funct_1(sK2,sK0(sK2,X0)) = k1_funct_1(sK3,sK0(sK2,X0))
    | r1_partfun1(sK2,X0) = iProver_top
    | r1_partfun1(sK2,sK3) = iProver_top
    | r1_tarski(k1_relat_1(sK2),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2711])).

cnf(c_2741,plain,
    ( k1_funct_1(sK3,sK0(sK2,sK3)) = k1_funct_1(sK2,sK0(sK2,sK3))
    | sK1 = k1_xboole_0
    | r1_partfun1(sK2,sK3) = iProver_top
    | r1_tarski(k1_relat_1(sK2),sK1) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2738,c_2712])).

cnf(c_19,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_24,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_574,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_17])).

cnf(c_575,plain,
    ( v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) ),
    inference(unflattening,[status(thm)],[c_574])).

cnf(c_2098,plain,
    ( v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) ),
    inference(instantiation,[status(thm)],[c_575])).

cnf(c_2099,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2098])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v4_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_246,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_3,c_1])).

cnf(c_250,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_246,c_2])).

cnf(c_251,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_250])).

cnf(c_586,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_251,c_20])).

cnf(c_587,plain,
    ( r1_tarski(k1_relat_1(sK2),X0)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) ),
    inference(unflattening,[status(thm)],[c_586])).

cnf(c_2095,plain,
    ( r1_tarski(k1_relat_1(sK2),sK1)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) ),
    inference(instantiation,[status(thm)],[c_587])).

cnf(c_2105,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
    | r1_tarski(k1_relat_1(sK2),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2095])).

cnf(c_3016,plain,
    ( r1_partfun1(sK2,sK3) = iProver_top
    | sK1 = k1_xboole_0
    | k1_funct_1(sK3,sK0(sK2,sK3)) = k1_funct_1(sK2,sK0(sK2,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2741,c_24,c_2092,c_2099,c_2105])).

cnf(c_3017,plain,
    ( k1_funct_1(sK3,sK0(sK2,sK3)) = k1_funct_1(sK2,sK0(sK2,sK3))
    | sK1 = k1_xboole_0
    | r1_partfun1(sK2,sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_3016])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r1_partfun1(X1,X2)
    | ~ r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X2,X0) = k1_funct_1(X1,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1884,plain,
    ( k1_funct_1(X0,X1) = k1_funct_1(X2,X1)
    | r2_hidden(X1,k1_relat_1(X2)) != iProver_top
    | r1_partfun1(X2,X0) != iProver_top
    | r1_tarski(k1_relat_1(X2),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2744,plain,
    ( k1_funct_1(X0,X1) = k1_funct_1(sK3,X1)
    | sK1 = k1_xboole_0
    | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
    | r1_partfun1(X0,sK3) != iProver_top
    | r1_tarski(k1_relat_1(X0),sK1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2738,c_1884])).

cnf(c_3107,plain,
    ( v1_relat_1(X0) != iProver_top
    | k1_funct_1(X0,X1) = k1_funct_1(sK3,X1)
    | sK1 = k1_xboole_0
    | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
    | r1_partfun1(X0,sK3) != iProver_top
    | r1_tarski(k1_relat_1(X0),sK1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2744,c_24,c_2092,c_2099])).

cnf(c_3108,plain,
    ( k1_funct_1(X0,X1) = k1_funct_1(sK3,X1)
    | sK1 = k1_xboole_0
    | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
    | r1_partfun1(X0,sK3) != iProver_top
    | r1_tarski(k1_relat_1(X0),sK1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3107])).

cnf(c_3121,plain,
    ( k1_funct_1(sK3,sK4) = k1_funct_1(sK2,sK4)
    | sK1 = k1_xboole_0
    | r1_partfun1(sK2,sK3) != iProver_top
    | r1_tarski(k1_relat_1(sK2),sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2398,c_3108])).

cnf(c_3289,plain,
    ( r1_partfun1(sK2,sK3) != iProver_top
    | sK1 = k1_xboole_0
    | k1_funct_1(sK3,sK4) = k1_funct_1(sK2,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3121,c_22,c_2092,c_2101,c_2105])).

cnf(c_3290,plain,
    ( k1_funct_1(sK3,sK4) = k1_funct_1(sK2,sK4)
    | sK1 = k1_xboole_0
    | r1_partfun1(sK2,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_3289])).

cnf(c_3296,plain,
    ( k1_funct_1(sK3,sK0(sK2,sK3)) = k1_funct_1(sK2,sK0(sK2,sK3))
    | k1_funct_1(sK3,sK4) = k1_funct_1(sK2,sK4)
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3017,c_3290])).

cnf(c_11,plain,
    ( r1_partfun1(X0,X1)
    | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k1_funct_1(X1,sK0(X0,X1)) != k1_funct_1(X0,sK0(X0,X1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1886,plain,
    ( k1_funct_1(X0,sK0(X1,X0)) != k1_funct_1(X1,sK0(X1,X0))
    | r1_partfun1(X1,X0) = iProver_top
    | r1_tarski(k1_relat_1(X1),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3415,plain,
    ( k1_funct_1(sK3,sK4) = k1_funct_1(sK2,sK4)
    | sK1 = k1_xboole_0
    | r1_partfun1(sK2,sK3) = iProver_top
    | r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3296,c_1886])).

cnf(c_2140,plain,
    ( r1_partfun1(X0,sK3)
    | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(sK3))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK3)
    | k1_funct_1(sK3,sK0(X0,sK3)) != k1_funct_1(X0,sK0(X0,sK3)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2190,plain,
    ( r1_partfun1(sK2,sK3)
    | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | k1_funct_1(sK3,sK0(sK2,sK3)) != k1_funct_1(sK2,sK0(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_2140])).

cnf(c_2191,plain,
    ( k1_funct_1(sK3,sK0(sK2,sK3)) != k1_funct_1(sK2,sK0(sK2,sK3))
    | r1_partfun1(sK2,sK3) = iProver_top
    | r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2190])).

cnf(c_3558,plain,
    ( sK1 = k1_xboole_0
    | r1_partfun1(sK2,sK3) = iProver_top
    | r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3415,c_22,c_24,c_2092,c_2099,c_2101,c_2105,c_2191,c_2741])).

cnf(c_3565,plain,
    ( sK1 = k1_xboole_0
    | r1_partfun1(sK2,sK3) = iProver_top
    | r1_tarski(k1_relat_1(sK2),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2738,c_3558])).

cnf(c_3568,plain,
    ( r1_partfun1(sK2,sK3) = iProver_top
    | sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3565,c_2092,c_2105])).

cnf(c_3569,plain,
    ( sK1 = k1_xboole_0
    | r1_partfun1(sK2,sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_3568])).

cnf(c_3574,plain,
    ( k1_funct_1(sK3,sK4) = k1_funct_1(sK2,sK4)
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3569,c_3290])).

cnf(c_14,negated_conjecture,
    ( ~ r1_partfun1(sK2,sK3)
    | k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1883,plain,
    ( k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4)
    | r1_partfun1(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3614,plain,
    ( sK1 = k1_xboole_0
    | r1_partfun1(sK2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3574,c_1883])).

cnf(c_3617,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3614,c_2092,c_2105,c_3565])).

cnf(c_3635,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_3617,c_2126])).

cnf(c_9,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_725,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_17])).

cnf(c_726,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,X0)
    | k1_relset_1(k1_xboole_0,X0,sK3) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) ),
    inference(unflattening,[status(thm)],[c_725])).

cnf(c_1439,plain,
    ( k1_relset_1(k1_xboole_0,X0,sK3) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
    | sK1 != X0
    | sK1 != k1_xboole_0
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_726])).

cnf(c_1440,plain,
    ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
    | sK1 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_1439])).

cnf(c_3639,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3617,c_1440])).

cnf(c_3650,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_3639])).

cnf(c_3658,plain,
    ( k1_relat_1(sK3) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3635,c_3650])).

cnf(c_3956,plain,
    ( k1_funct_1(X0,X1) = k1_funct_1(sK3,X1)
    | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
    | r1_partfun1(X0,sK3) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3658,c_1884])).

cnf(c_4072,plain,
    ( v1_relat_1(X0) != iProver_top
    | k1_funct_1(X0,X1) = k1_funct_1(sK3,X1)
    | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
    | r1_partfun1(X0,sK3) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3956,c_24,c_2092,c_2099])).

cnf(c_4073,plain,
    ( k1_funct_1(X0,X1) = k1_funct_1(sK3,X1)
    | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
    | r1_partfun1(X0,sK3) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4072])).

cnf(c_4085,plain,
    ( k1_funct_1(sK3,sK4) = k1_funct_1(sK2,sK4)
    | r1_partfun1(sK2,sK3) != iProver_top
    | r1_tarski(k1_relat_1(sK2),k1_xboole_0) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2398,c_4073])).

cnf(c_6,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_707,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
    | sK2 != X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_20])).

cnf(c_708,plain,
    ( ~ v1_funct_2(sK2,X0,k1_xboole_0)
    | k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
    | k1_xboole_0 = X0
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_707])).

cnf(c_1422,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
    | sK1 != X0
    | sK1 != k1_xboole_0
    | sK3 != sK2
    | sK2 = k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_708])).

cnf(c_1423,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
    | sK1 != k1_xboole_0
    | sK3 != sK2
    | sK2 = k1_xboole_0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_1422])).

cnf(c_1627,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1604])).

cnf(c_1605,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2314,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1605])).

cnf(c_2315,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2314])).

cnf(c_2325,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1423,c_1627,c_2315])).

cnf(c_1607,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2201,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k1_relat_1(sK2),sK1)
    | X0 != k1_relat_1(sK2)
    | X1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1607])).

cnf(c_2841,plain,
    ( r1_tarski(k1_relat_1(sK2),X0)
    | ~ r1_tarski(k1_relat_1(sK2),sK1)
    | X0 != sK1
    | k1_relat_1(sK2) != k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_2201])).

cnf(c_2843,plain,
    ( X0 != sK1
    | k1_relat_1(sK2) != k1_relat_1(sK2)
    | r1_tarski(k1_relat_1(sK2),X0) = iProver_top
    | r1_tarski(k1_relat_1(sK2),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2841])).

cnf(c_2845,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK2)
    | k1_xboole_0 != sK1
    | r1_tarski(k1_relat_1(sK2),sK1) != iProver_top
    | r1_tarski(k1_relat_1(sK2),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2843])).

cnf(c_2842,plain,
    ( k1_relat_1(sK2) = k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1604])).

cnf(c_2348,plain,
    ( X0 != X1
    | X0 = sK1
    | sK1 != X1 ),
    inference(instantiation,[status(thm)],[c_1605])).

cnf(c_3476,plain,
    ( k1_relat_1(sK3) != X0
    | k1_relat_1(sK3) = sK1
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_2348])).

cnf(c_3479,plain,
    ( k1_relat_1(sK3) = sK1
    | k1_relat_1(sK3) != k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3476])).

cnf(c_3953,plain,
    ( k1_funct_1(sK3,sK0(sK2,sK3)) = k1_funct_1(sK2,sK0(sK2,sK3))
    | r1_partfun1(sK2,sK3) = iProver_top
    | r1_tarski(k1_relat_1(sK2),k1_xboole_0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3658,c_2712])).

cnf(c_4118,plain,
    ( r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3))
    | ~ r1_tarski(k1_relat_1(sK2),sK1)
    | k1_relat_1(sK3) != sK1
    | k1_relat_1(sK2) != k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_2841])).

cnf(c_4119,plain,
    ( k1_relat_1(sK3) != sK1
    | k1_relat_1(sK2) != k1_relat_1(sK2)
    | r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3)) = iProver_top
    | r1_tarski(k1_relat_1(sK2),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4118])).

cnf(c_4228,plain,
    ( k1_funct_1(sK3,sK4) = k1_funct_1(sK2,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4085,c_22,c_24,c_1627,c_2092,c_2099,c_2101,c_2105,c_2191,c_2315,c_2845,c_2842,c_3479,c_3565,c_3614,c_3658,c_3953,c_4119])).

cnf(c_4231,plain,
    ( k1_funct_1(sK2,sK4) != k1_funct_1(sK2,sK4)
    | r1_partfun1(sK2,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4228,c_1883])).

cnf(c_4233,plain,
    ( r1_partfun1(sK2,sK3) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4231])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4233,c_4119,c_3953,c_3658,c_3617,c_3479,c_2842,c_2845,c_2325,c_2191,c_2105,c_2101,c_2099,c_2092,c_24,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:58:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 1.35/1.10  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.35/1.10  
% 1.35/1.10  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.35/1.10  
% 1.35/1.10  ------  iProver source info
% 1.35/1.10  
% 1.35/1.10  git: date: 2020-06-30 10:37:57 +0100
% 1.35/1.10  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.35/1.10  git: non_committed_changes: false
% 1.35/1.10  git: last_make_outside_of_git: false
% 1.35/1.10  
% 1.35/1.10  ------ 
% 1.35/1.10  
% 1.35/1.10  ------ Input Options
% 1.35/1.10  
% 1.35/1.10  --out_options                           all
% 1.35/1.10  --tptp_safe_out                         true
% 1.35/1.10  --problem_path                          ""
% 1.35/1.10  --include_path                          ""
% 1.35/1.10  --clausifier                            res/vclausify_rel
% 1.35/1.10  --clausifier_options                    --mode clausify
% 1.35/1.10  --stdin                                 false
% 1.35/1.10  --stats_out                             all
% 1.35/1.10  
% 1.35/1.10  ------ General Options
% 1.35/1.10  
% 1.35/1.10  --fof                                   false
% 1.35/1.10  --time_out_real                         305.
% 1.35/1.10  --time_out_virtual                      -1.
% 1.35/1.10  --symbol_type_check                     false
% 1.35/1.10  --clausify_out                          false
% 1.35/1.10  --sig_cnt_out                           false
% 1.35/1.10  --trig_cnt_out                          false
% 1.35/1.10  --trig_cnt_out_tolerance                1.
% 1.35/1.10  --trig_cnt_out_sk_spl                   false
% 1.35/1.10  --abstr_cl_out                          false
% 1.35/1.10  
% 1.35/1.10  ------ Global Options
% 1.35/1.10  
% 1.35/1.10  --schedule                              default
% 1.35/1.10  --add_important_lit                     false
% 1.35/1.10  --prop_solver_per_cl                    1000
% 1.35/1.10  --min_unsat_core                        false
% 1.35/1.10  --soft_assumptions                      false
% 1.35/1.10  --soft_lemma_size                       3
% 1.35/1.10  --prop_impl_unit_size                   0
% 1.35/1.10  --prop_impl_unit                        []
% 1.35/1.10  --share_sel_clauses                     true
% 1.35/1.10  --reset_solvers                         false
% 1.35/1.10  --bc_imp_inh                            [conj_cone]
% 1.35/1.10  --conj_cone_tolerance                   3.
% 1.35/1.10  --extra_neg_conj                        none
% 1.35/1.10  --large_theory_mode                     true
% 1.35/1.10  --prolific_symb_bound                   200
% 1.35/1.10  --lt_threshold                          2000
% 1.35/1.10  --clause_weak_htbl                      true
% 1.35/1.10  --gc_record_bc_elim                     false
% 1.35/1.10  
% 1.35/1.10  ------ Preprocessing Options
% 1.35/1.10  
% 1.35/1.10  --preprocessing_flag                    true
% 1.35/1.10  --time_out_prep_mult                    0.1
% 1.35/1.10  --splitting_mode                        input
% 1.35/1.10  --splitting_grd                         true
% 1.35/1.10  --splitting_cvd                         false
% 1.35/1.10  --splitting_cvd_svl                     false
% 1.35/1.10  --splitting_nvd                         32
% 1.35/1.10  --sub_typing                            true
% 1.35/1.10  --prep_gs_sim                           true
% 1.35/1.10  --prep_unflatten                        true
% 1.35/1.10  --prep_res_sim                          true
% 1.35/1.10  --prep_upred                            true
% 1.35/1.10  --prep_sem_filter                       exhaustive
% 1.35/1.10  --prep_sem_filter_out                   false
% 1.35/1.10  --pred_elim                             true
% 1.35/1.10  --res_sim_input                         true
% 1.35/1.10  --eq_ax_congr_red                       true
% 1.35/1.10  --pure_diseq_elim                       true
% 1.35/1.10  --brand_transform                       false
% 1.35/1.10  --non_eq_to_eq                          false
% 1.35/1.10  --prep_def_merge                        true
% 1.35/1.10  --prep_def_merge_prop_impl              false
% 1.35/1.10  --prep_def_merge_mbd                    true
% 1.35/1.10  --prep_def_merge_tr_red                 false
% 1.35/1.10  --prep_def_merge_tr_cl                  false
% 1.35/1.10  --smt_preprocessing                     true
% 1.35/1.10  --smt_ac_axioms                         fast
% 1.35/1.10  --preprocessed_out                      false
% 1.35/1.10  --preprocessed_stats                    false
% 1.35/1.10  
% 1.35/1.10  ------ Abstraction refinement Options
% 1.35/1.10  
% 1.35/1.10  --abstr_ref                             []
% 1.35/1.10  --abstr_ref_prep                        false
% 1.35/1.10  --abstr_ref_until_sat                   false
% 1.35/1.10  --abstr_ref_sig_restrict                funpre
% 1.35/1.10  --abstr_ref_af_restrict_to_split_sk     false
% 1.35/1.10  --abstr_ref_under                       []
% 1.35/1.10  
% 1.35/1.10  ------ SAT Options
% 1.35/1.10  
% 1.35/1.10  --sat_mode                              false
% 1.35/1.10  --sat_fm_restart_options                ""
% 1.35/1.10  --sat_gr_def                            false
% 1.35/1.10  --sat_epr_types                         true
% 1.35/1.10  --sat_non_cyclic_types                  false
% 1.35/1.10  --sat_finite_models                     false
% 1.35/1.10  --sat_fm_lemmas                         false
% 1.35/1.10  --sat_fm_prep                           false
% 1.35/1.10  --sat_fm_uc_incr                        true
% 1.35/1.10  --sat_out_model                         small
% 1.35/1.10  --sat_out_clauses                       false
% 1.35/1.10  
% 1.35/1.10  ------ QBF Options
% 1.35/1.10  
% 1.35/1.10  --qbf_mode                              false
% 1.35/1.10  --qbf_elim_univ                         false
% 1.35/1.10  --qbf_dom_inst                          none
% 1.35/1.10  --qbf_dom_pre_inst                      false
% 1.35/1.10  --qbf_sk_in                             false
% 1.35/1.10  --qbf_pred_elim                         true
% 1.35/1.10  --qbf_split                             512
% 1.35/1.10  
% 1.35/1.10  ------ BMC1 Options
% 1.35/1.10  
% 1.35/1.10  --bmc1_incremental                      false
% 1.35/1.10  --bmc1_axioms                           reachable_all
% 1.35/1.10  --bmc1_min_bound                        0
% 1.35/1.10  --bmc1_max_bound                        -1
% 1.35/1.10  --bmc1_max_bound_default                -1
% 1.35/1.10  --bmc1_symbol_reachability              true
% 1.35/1.10  --bmc1_property_lemmas                  false
% 1.35/1.10  --bmc1_k_induction                      false
% 1.35/1.10  --bmc1_non_equiv_states                 false
% 1.35/1.10  --bmc1_deadlock                         false
% 1.35/1.10  --bmc1_ucm                              false
% 1.35/1.10  --bmc1_add_unsat_core                   none
% 1.35/1.10  --bmc1_unsat_core_children              false
% 1.35/1.10  --bmc1_unsat_core_extrapolate_axioms    false
% 1.35/1.10  --bmc1_out_stat                         full
% 1.35/1.10  --bmc1_ground_init                      false
% 1.35/1.10  --bmc1_pre_inst_next_state              false
% 1.35/1.10  --bmc1_pre_inst_state                   false
% 1.35/1.10  --bmc1_pre_inst_reach_state             false
% 1.35/1.10  --bmc1_out_unsat_core                   false
% 1.35/1.10  --bmc1_aig_witness_out                  false
% 1.35/1.10  --bmc1_verbose                          false
% 1.35/1.10  --bmc1_dump_clauses_tptp                false
% 1.35/1.10  --bmc1_dump_unsat_core_tptp             false
% 1.35/1.10  --bmc1_dump_file                        -
% 1.35/1.10  --bmc1_ucm_expand_uc_limit              128
% 1.35/1.10  --bmc1_ucm_n_expand_iterations          6
% 1.35/1.10  --bmc1_ucm_extend_mode                  1
% 1.35/1.10  --bmc1_ucm_init_mode                    2
% 1.35/1.10  --bmc1_ucm_cone_mode                    none
% 1.35/1.10  --bmc1_ucm_reduced_relation_type        0
% 1.35/1.10  --bmc1_ucm_relax_model                  4
% 1.35/1.10  --bmc1_ucm_full_tr_after_sat            true
% 1.35/1.10  --bmc1_ucm_expand_neg_assumptions       false
% 1.35/1.10  --bmc1_ucm_layered_model                none
% 1.35/1.10  --bmc1_ucm_max_lemma_size               10
% 1.35/1.10  
% 1.35/1.10  ------ AIG Options
% 1.35/1.10  
% 1.35/1.10  --aig_mode                              false
% 1.35/1.10  
% 1.35/1.10  ------ Instantiation Options
% 1.35/1.10  
% 1.35/1.10  --instantiation_flag                    true
% 1.35/1.10  --inst_sos_flag                         false
% 1.35/1.10  --inst_sos_phase                        true
% 1.35/1.10  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.35/1.10  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.35/1.10  --inst_lit_sel_side                     num_symb
% 1.35/1.10  --inst_solver_per_active                1400
% 1.35/1.10  --inst_solver_calls_frac                1.
% 1.35/1.10  --inst_passive_queue_type               priority_queues
% 1.35/1.10  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.35/1.10  --inst_passive_queues_freq              [25;2]
% 1.35/1.10  --inst_dismatching                      true
% 1.35/1.10  --inst_eager_unprocessed_to_passive     true
% 1.35/1.10  --inst_prop_sim_given                   true
% 1.35/1.10  --inst_prop_sim_new                     false
% 1.35/1.10  --inst_subs_new                         false
% 1.35/1.10  --inst_eq_res_simp                      false
% 1.35/1.10  --inst_subs_given                       false
% 1.35/1.10  --inst_orphan_elimination               true
% 1.35/1.10  --inst_learning_loop_flag               true
% 1.35/1.10  --inst_learning_start                   3000
% 1.35/1.10  --inst_learning_factor                  2
% 1.35/1.10  --inst_start_prop_sim_after_learn       3
% 1.35/1.10  --inst_sel_renew                        solver
% 1.35/1.10  --inst_lit_activity_flag                true
% 1.35/1.10  --inst_restr_to_given                   false
% 1.35/1.10  --inst_activity_threshold               500
% 1.35/1.10  --inst_out_proof                        true
% 1.35/1.10  
% 1.35/1.10  ------ Resolution Options
% 1.35/1.10  
% 1.35/1.10  --resolution_flag                       true
% 1.35/1.10  --res_lit_sel                           adaptive
% 1.35/1.10  --res_lit_sel_side                      none
% 1.35/1.10  --res_ordering                          kbo
% 1.35/1.10  --res_to_prop_solver                    active
% 1.35/1.10  --res_prop_simpl_new                    false
% 1.35/1.10  --res_prop_simpl_given                  true
% 1.35/1.10  --res_passive_queue_type                priority_queues
% 1.35/1.10  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.35/1.10  --res_passive_queues_freq               [15;5]
% 1.35/1.10  --res_forward_subs                      full
% 1.35/1.10  --res_backward_subs                     full
% 1.35/1.10  --res_forward_subs_resolution           true
% 1.35/1.10  --res_backward_subs_resolution          true
% 1.35/1.10  --res_orphan_elimination                true
% 1.35/1.10  --res_time_limit                        2.
% 1.35/1.10  --res_out_proof                         true
% 1.35/1.10  
% 1.35/1.10  ------ Superposition Options
% 1.35/1.10  
% 1.35/1.10  --superposition_flag                    true
% 1.35/1.10  --sup_passive_queue_type                priority_queues
% 1.35/1.10  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.35/1.10  --sup_passive_queues_freq               [8;1;4]
% 1.35/1.10  --demod_completeness_check              fast
% 1.35/1.10  --demod_use_ground                      true
% 1.35/1.10  --sup_to_prop_solver                    passive
% 1.35/1.10  --sup_prop_simpl_new                    true
% 1.35/1.10  --sup_prop_simpl_given                  true
% 1.35/1.10  --sup_fun_splitting                     false
% 1.35/1.10  --sup_smt_interval                      50000
% 1.35/1.10  
% 1.35/1.10  ------ Superposition Simplification Setup
% 1.35/1.10  
% 1.35/1.10  --sup_indices_passive                   []
% 1.35/1.10  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.35/1.10  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.35/1.10  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.35/1.10  --sup_full_triv                         [TrivRules;PropSubs]
% 1.35/1.10  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.35/1.10  --sup_full_bw                           [BwDemod]
% 1.35/1.10  --sup_immed_triv                        [TrivRules]
% 1.35/1.10  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.35/1.10  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.35/1.10  --sup_immed_bw_main                     []
% 1.35/1.10  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.35/1.10  --sup_input_triv                        [Unflattening;TrivRules]
% 1.35/1.10  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.35/1.10  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.35/1.10  
% 1.35/1.10  ------ Combination Options
% 1.35/1.10  
% 1.35/1.10  --comb_res_mult                         3
% 1.35/1.10  --comb_sup_mult                         2
% 1.35/1.10  --comb_inst_mult                        10
% 1.35/1.10  
% 1.35/1.10  ------ Debug Options
% 1.35/1.10  
% 1.35/1.10  --dbg_backtrace                         false
% 1.35/1.10  --dbg_dump_prop_clauses                 false
% 1.35/1.10  --dbg_dump_prop_clauses_file            -
% 1.35/1.10  --dbg_out_stat                          false
% 1.35/1.10  ------ Parsing...
% 1.35/1.10  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.35/1.10  
% 1.35/1.10  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 1.35/1.10  
% 1.35/1.10  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.35/1.10  
% 1.35/1.10  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.35/1.10  ------ Proving...
% 1.35/1.10  ------ Problem Properties 
% 1.35/1.10  
% 1.35/1.10  
% 1.35/1.10  clauses                                 24
% 1.35/1.10  conjectures                             5
% 1.35/1.10  EPR                                     2
% 1.35/1.10  Horn                                    16
% 1.35/1.10  unary                                   2
% 1.35/1.10  binary                                  8
% 1.35/1.10  lits                                    84
% 1.35/1.10  lits eq                                 53
% 1.35/1.10  fd_pure                                 0
% 1.35/1.10  fd_pseudo                               0
% 1.35/1.10  fd_cond                                 0
% 1.35/1.10  fd_pseudo_cond                          0
% 1.35/1.10  AC symbols                              0
% 1.35/1.10  
% 1.35/1.10  ------ Schedule dynamic 5 is on 
% 1.35/1.10  
% 1.35/1.10  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.35/1.10  
% 1.35/1.10  
% 1.35/1.10  ------ 
% 1.35/1.10  Current options:
% 1.35/1.10  ------ 
% 1.35/1.10  
% 1.35/1.10  ------ Input Options
% 1.35/1.10  
% 1.35/1.10  --out_options                           all
% 1.35/1.10  --tptp_safe_out                         true
% 1.35/1.10  --problem_path                          ""
% 1.35/1.10  --include_path                          ""
% 1.35/1.10  --clausifier                            res/vclausify_rel
% 1.35/1.10  --clausifier_options                    --mode clausify
% 1.35/1.10  --stdin                                 false
% 1.35/1.10  --stats_out                             all
% 1.35/1.10  
% 1.35/1.10  ------ General Options
% 1.35/1.10  
% 1.35/1.10  --fof                                   false
% 1.35/1.10  --time_out_real                         305.
% 1.35/1.10  --time_out_virtual                      -1.
% 1.35/1.10  --symbol_type_check                     false
% 1.35/1.10  --clausify_out                          false
% 1.35/1.10  --sig_cnt_out                           false
% 1.35/1.10  --trig_cnt_out                          false
% 1.35/1.10  --trig_cnt_out_tolerance                1.
% 1.35/1.10  --trig_cnt_out_sk_spl                   false
% 1.35/1.10  --abstr_cl_out                          false
% 1.35/1.10  
% 1.35/1.10  ------ Global Options
% 1.35/1.10  
% 1.35/1.10  --schedule                              default
% 1.35/1.10  --add_important_lit                     false
% 1.35/1.10  --prop_solver_per_cl                    1000
% 1.35/1.10  --min_unsat_core                        false
% 1.35/1.10  --soft_assumptions                      false
% 1.35/1.10  --soft_lemma_size                       3
% 1.35/1.10  --prop_impl_unit_size                   0
% 1.35/1.10  --prop_impl_unit                        []
% 1.35/1.10  --share_sel_clauses                     true
% 1.35/1.10  --reset_solvers                         false
% 1.35/1.10  --bc_imp_inh                            [conj_cone]
% 1.35/1.10  --conj_cone_tolerance                   3.
% 1.35/1.10  --extra_neg_conj                        none
% 1.35/1.10  --large_theory_mode                     true
% 1.35/1.10  --prolific_symb_bound                   200
% 1.35/1.10  --lt_threshold                          2000
% 1.35/1.10  --clause_weak_htbl                      true
% 1.35/1.10  --gc_record_bc_elim                     false
% 1.35/1.10  
% 1.35/1.10  ------ Preprocessing Options
% 1.35/1.10  
% 1.35/1.10  --preprocessing_flag                    true
% 1.35/1.10  --time_out_prep_mult                    0.1
% 1.35/1.10  --splitting_mode                        input
% 1.35/1.10  --splitting_grd                         true
% 1.35/1.10  --splitting_cvd                         false
% 1.35/1.10  --splitting_cvd_svl                     false
% 1.35/1.10  --splitting_nvd                         32
% 1.35/1.10  --sub_typing                            true
% 1.35/1.10  --prep_gs_sim                           true
% 1.35/1.10  --prep_unflatten                        true
% 1.35/1.10  --prep_res_sim                          true
% 1.35/1.10  --prep_upred                            true
% 1.35/1.10  --prep_sem_filter                       exhaustive
% 1.35/1.10  --prep_sem_filter_out                   false
% 1.35/1.10  --pred_elim                             true
% 1.35/1.10  --res_sim_input                         true
% 1.35/1.10  --eq_ax_congr_red                       true
% 1.35/1.10  --pure_diseq_elim                       true
% 1.35/1.10  --brand_transform                       false
% 1.35/1.10  --non_eq_to_eq                          false
% 1.35/1.10  --prep_def_merge                        true
% 1.35/1.10  --prep_def_merge_prop_impl              false
% 1.35/1.10  --prep_def_merge_mbd                    true
% 1.35/1.10  --prep_def_merge_tr_red                 false
% 1.35/1.10  --prep_def_merge_tr_cl                  false
% 1.35/1.10  --smt_preprocessing                     true
% 1.35/1.10  --smt_ac_axioms                         fast
% 1.35/1.10  --preprocessed_out                      false
% 1.35/1.10  --preprocessed_stats                    false
% 1.35/1.10  
% 1.35/1.10  ------ Abstraction refinement Options
% 1.35/1.10  
% 1.35/1.10  --abstr_ref                             []
% 1.35/1.10  --abstr_ref_prep                        false
% 1.35/1.10  --abstr_ref_until_sat                   false
% 1.35/1.10  --abstr_ref_sig_restrict                funpre
% 1.35/1.10  --abstr_ref_af_restrict_to_split_sk     false
% 1.35/1.10  --abstr_ref_under                       []
% 1.35/1.10  
% 1.35/1.10  ------ SAT Options
% 1.35/1.10  
% 1.35/1.10  --sat_mode                              false
% 1.35/1.10  --sat_fm_restart_options                ""
% 1.35/1.10  --sat_gr_def                            false
% 1.35/1.10  --sat_epr_types                         true
% 1.35/1.10  --sat_non_cyclic_types                  false
% 1.35/1.10  --sat_finite_models                     false
% 1.35/1.10  --sat_fm_lemmas                         false
% 1.35/1.10  --sat_fm_prep                           false
% 1.35/1.10  --sat_fm_uc_incr                        true
% 1.35/1.10  --sat_out_model                         small
% 1.35/1.10  --sat_out_clauses                       false
% 1.35/1.10  
% 1.35/1.10  ------ QBF Options
% 1.35/1.10  
% 1.35/1.10  --qbf_mode                              false
% 1.35/1.10  --qbf_elim_univ                         false
% 1.35/1.10  --qbf_dom_inst                          none
% 1.35/1.10  --qbf_dom_pre_inst                      false
% 1.35/1.10  --qbf_sk_in                             false
% 1.35/1.10  --qbf_pred_elim                         true
% 1.35/1.10  --qbf_split                             512
% 1.35/1.10  
% 1.35/1.10  ------ BMC1 Options
% 1.35/1.10  
% 1.35/1.10  --bmc1_incremental                      false
% 1.35/1.10  --bmc1_axioms                           reachable_all
% 1.35/1.10  --bmc1_min_bound                        0
% 1.35/1.10  --bmc1_max_bound                        -1
% 1.35/1.10  --bmc1_max_bound_default                -1
% 1.35/1.10  --bmc1_symbol_reachability              true
% 1.35/1.10  --bmc1_property_lemmas                  false
% 1.35/1.10  --bmc1_k_induction                      false
% 1.35/1.10  --bmc1_non_equiv_states                 false
% 1.35/1.10  --bmc1_deadlock                         false
% 1.35/1.10  --bmc1_ucm                              false
% 1.35/1.10  --bmc1_add_unsat_core                   none
% 1.35/1.10  --bmc1_unsat_core_children              false
% 1.35/1.10  --bmc1_unsat_core_extrapolate_axioms    false
% 1.35/1.10  --bmc1_out_stat                         full
% 1.35/1.10  --bmc1_ground_init                      false
% 1.35/1.10  --bmc1_pre_inst_next_state              false
% 1.35/1.10  --bmc1_pre_inst_state                   false
% 1.35/1.10  --bmc1_pre_inst_reach_state             false
% 1.35/1.10  --bmc1_out_unsat_core                   false
% 1.35/1.10  --bmc1_aig_witness_out                  false
% 1.35/1.10  --bmc1_verbose                          false
% 1.35/1.10  --bmc1_dump_clauses_tptp                false
% 1.35/1.10  --bmc1_dump_unsat_core_tptp             false
% 1.35/1.10  --bmc1_dump_file                        -
% 1.35/1.10  --bmc1_ucm_expand_uc_limit              128
% 1.35/1.10  --bmc1_ucm_n_expand_iterations          6
% 1.35/1.10  --bmc1_ucm_extend_mode                  1
% 1.35/1.10  --bmc1_ucm_init_mode                    2
% 1.35/1.10  --bmc1_ucm_cone_mode                    none
% 1.35/1.10  --bmc1_ucm_reduced_relation_type        0
% 1.35/1.10  --bmc1_ucm_relax_model                  4
% 1.35/1.10  --bmc1_ucm_full_tr_after_sat            true
% 1.35/1.10  --bmc1_ucm_expand_neg_assumptions       false
% 1.35/1.10  --bmc1_ucm_layered_model                none
% 1.35/1.10  --bmc1_ucm_max_lemma_size               10
% 1.35/1.10  
% 1.35/1.10  ------ AIG Options
% 1.35/1.10  
% 1.35/1.10  --aig_mode                              false
% 1.35/1.10  
% 1.35/1.10  ------ Instantiation Options
% 1.35/1.10  
% 1.35/1.10  --instantiation_flag                    true
% 1.35/1.10  --inst_sos_flag                         false
% 1.35/1.10  --inst_sos_phase                        true
% 1.35/1.10  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.35/1.10  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.35/1.10  --inst_lit_sel_side                     none
% 1.35/1.10  --inst_solver_per_active                1400
% 1.35/1.10  --inst_solver_calls_frac                1.
% 1.35/1.10  --inst_passive_queue_type               priority_queues
% 1.35/1.10  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.35/1.10  --inst_passive_queues_freq              [25;2]
% 1.35/1.10  --inst_dismatching                      true
% 1.35/1.10  --inst_eager_unprocessed_to_passive     true
% 1.35/1.10  --inst_prop_sim_given                   true
% 1.35/1.10  --inst_prop_sim_new                     false
% 1.35/1.10  --inst_subs_new                         false
% 1.35/1.10  --inst_eq_res_simp                      false
% 1.35/1.10  --inst_subs_given                       false
% 1.35/1.10  --inst_orphan_elimination               true
% 1.35/1.10  --inst_learning_loop_flag               true
% 1.35/1.10  --inst_learning_start                   3000
% 1.35/1.10  --inst_learning_factor                  2
% 1.35/1.10  --inst_start_prop_sim_after_learn       3
% 1.35/1.10  --inst_sel_renew                        solver
% 1.35/1.10  --inst_lit_activity_flag                true
% 1.35/1.10  --inst_restr_to_given                   false
% 1.35/1.10  --inst_activity_threshold               500
% 1.35/1.10  --inst_out_proof                        true
% 1.35/1.10  
% 1.35/1.10  ------ Resolution Options
% 1.35/1.10  
% 1.35/1.10  --resolution_flag                       false
% 1.35/1.10  --res_lit_sel                           adaptive
% 1.35/1.10  --res_lit_sel_side                      none
% 1.35/1.10  --res_ordering                          kbo
% 1.35/1.10  --res_to_prop_solver                    active
% 1.35/1.10  --res_prop_simpl_new                    false
% 1.35/1.10  --res_prop_simpl_given                  true
% 1.35/1.10  --res_passive_queue_type                priority_queues
% 1.35/1.10  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.35/1.10  --res_passive_queues_freq               [15;5]
% 1.35/1.10  --res_forward_subs                      full
% 1.35/1.10  --res_backward_subs                     full
% 1.35/1.10  --res_forward_subs_resolution           true
% 1.35/1.10  --res_backward_subs_resolution          true
% 1.35/1.10  --res_orphan_elimination                true
% 1.35/1.10  --res_time_limit                        2.
% 1.35/1.10  --res_out_proof                         true
% 1.35/1.10  
% 1.35/1.10  ------ Superposition Options
% 1.35/1.10  
% 1.35/1.10  --superposition_flag                    true
% 1.35/1.10  --sup_passive_queue_type                priority_queues
% 1.35/1.10  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.35/1.10  --sup_passive_queues_freq               [8;1;4]
% 1.35/1.10  --demod_completeness_check              fast
% 1.35/1.10  --demod_use_ground                      true
% 1.35/1.10  --sup_to_prop_solver                    passive
% 1.35/1.10  --sup_prop_simpl_new                    true
% 1.35/1.10  --sup_prop_simpl_given                  true
% 1.35/1.10  --sup_fun_splitting                     false
% 1.35/1.10  --sup_smt_interval                      50000
% 1.35/1.10  
% 1.35/1.10  ------ Superposition Simplification Setup
% 1.35/1.10  
% 1.35/1.10  --sup_indices_passive                   []
% 1.35/1.10  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.35/1.10  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.35/1.10  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.35/1.10  --sup_full_triv                         [TrivRules;PropSubs]
% 1.35/1.10  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.35/1.10  --sup_full_bw                           [BwDemod]
% 1.35/1.10  --sup_immed_triv                        [TrivRules]
% 1.35/1.10  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.35/1.10  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.35/1.10  --sup_immed_bw_main                     []
% 1.35/1.10  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.35/1.10  --sup_input_triv                        [Unflattening;TrivRules]
% 1.35/1.10  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.35/1.10  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.35/1.10  
% 1.35/1.10  ------ Combination Options
% 1.35/1.10  
% 1.35/1.10  --comb_res_mult                         3
% 1.35/1.10  --comb_sup_mult                         2
% 1.35/1.10  --comb_inst_mult                        10
% 1.35/1.10  
% 1.35/1.10  ------ Debug Options
% 1.35/1.10  
% 1.35/1.10  --dbg_backtrace                         false
% 1.35/1.10  --dbg_dump_prop_clauses                 false
% 1.35/1.10  --dbg_dump_prop_clauses_file            -
% 1.35/1.10  --dbg_out_stat                          false
% 1.35/1.10  
% 1.35/1.10  
% 1.35/1.10  
% 1.35/1.10  
% 1.35/1.10  ------ Proving...
% 1.35/1.10  
% 1.35/1.10  
% 1.35/1.10  % SZS status Theorem for theBenchmark.p
% 1.35/1.10  
% 1.35/1.10  % SZS output start CNFRefutation for theBenchmark.p
% 1.35/1.10  
% 1.35/1.10  fof(f4,axiom,(
% 1.35/1.10    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 1.35/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.35/1.10  
% 1.35/1.10  fof(f13,plain,(
% 1.35/1.10    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.35/1.10    inference(ennf_transformation,[],[f4])).
% 1.35/1.10  
% 1.35/1.10  fof(f37,plain,(
% 1.35/1.10    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.35/1.10    inference(cnf_transformation,[],[f13])).
% 1.35/1.10  
% 1.35/1.10  fof(f7,conjecture,(
% 1.35/1.10    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r1_partfun1(X1,X2) <=> ! [X3] : (r2_hidden(X3,k1_relset_1(X0,X0,X1)) => k1_funct_1(X1,X3) = k1_funct_1(X2,X3)))))),
% 1.35/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.35/1.10  
% 1.35/1.10  fof(f8,negated_conjecture,(
% 1.35/1.10    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r1_partfun1(X1,X2) <=> ! [X3] : (r2_hidden(X3,k1_relset_1(X0,X0,X1)) => k1_funct_1(X1,X3) = k1_funct_1(X2,X3)))))),
% 1.35/1.10    inference(negated_conjecture,[],[f7])).
% 1.35/1.10  
% 1.35/1.10  fof(f18,plain,(
% 1.35/1.10    ? [X0,X1] : (? [X2] : ((r1_partfun1(X1,X2) <~> ! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(X2,X3) | ~r2_hidden(X3,k1_relset_1(X0,X0,X1)))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1)))),
% 1.35/1.10    inference(ennf_transformation,[],[f8])).
% 1.35/1.10  
% 1.35/1.10  fof(f19,plain,(
% 1.35/1.10    ? [X0,X1] : (? [X2] : ((r1_partfun1(X1,X2) <~> ! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(X2,X3) | ~r2_hidden(X3,k1_relset_1(X0,X0,X1)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1))),
% 1.35/1.10    inference(flattening,[],[f18])).
% 1.35/1.10  
% 1.35/1.10  fof(f26,plain,(
% 1.35/1.10    ? [X0,X1] : (? [X2] : (((? [X3] : (k1_funct_1(X1,X3) != k1_funct_1(X2,X3) & r2_hidden(X3,k1_relset_1(X0,X0,X1))) | ~r1_partfun1(X1,X2)) & (! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(X2,X3) | ~r2_hidden(X3,k1_relset_1(X0,X0,X1))) | r1_partfun1(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1))),
% 1.35/1.10    inference(nnf_transformation,[],[f19])).
% 1.35/1.10  
% 1.35/1.10  fof(f27,plain,(
% 1.35/1.10    ? [X0,X1] : (? [X2] : ((? [X3] : (k1_funct_1(X1,X3) != k1_funct_1(X2,X3) & r2_hidden(X3,k1_relset_1(X0,X0,X1))) | ~r1_partfun1(X1,X2)) & (! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(X2,X3) | ~r2_hidden(X3,k1_relset_1(X0,X0,X1))) | r1_partfun1(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1))),
% 1.35/1.10    inference(flattening,[],[f26])).
% 1.35/1.10  
% 1.35/1.10  fof(f28,plain,(
% 1.35/1.10    ? [X0,X1] : (? [X2] : ((? [X3] : (k1_funct_1(X1,X3) != k1_funct_1(X2,X3) & r2_hidden(X3,k1_relset_1(X0,X0,X1))) | ~r1_partfun1(X1,X2)) & (! [X4] : (k1_funct_1(X1,X4) = k1_funct_1(X2,X4) | ~r2_hidden(X4,k1_relset_1(X0,X0,X1))) | r1_partfun1(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1))),
% 1.35/1.10    inference(rectify,[],[f27])).
% 1.35/1.10  
% 1.35/1.10  fof(f31,plain,(
% 1.35/1.10    ( ! [X2,X0,X1] : (? [X3] : (k1_funct_1(X1,X3) != k1_funct_1(X2,X3) & r2_hidden(X3,k1_relset_1(X0,X0,X1))) => (k1_funct_1(X1,sK4) != k1_funct_1(X2,sK4) & r2_hidden(sK4,k1_relset_1(X0,X0,X1)))) )),
% 1.35/1.10    introduced(choice_axiom,[])).
% 1.35/1.10  
% 1.35/1.10  fof(f30,plain,(
% 1.35/1.10    ( ! [X0,X1] : (? [X2] : ((? [X3] : (k1_funct_1(X1,X3) != k1_funct_1(X2,X3) & r2_hidden(X3,k1_relset_1(X0,X0,X1))) | ~r1_partfun1(X1,X2)) & (! [X4] : (k1_funct_1(X1,X4) = k1_funct_1(X2,X4) | ~r2_hidden(X4,k1_relset_1(X0,X0,X1))) | r1_partfun1(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((? [X3] : (k1_funct_1(sK3,X3) != k1_funct_1(X1,X3) & r2_hidden(X3,k1_relset_1(X0,X0,X1))) | ~r1_partfun1(X1,sK3)) & (! [X4] : (k1_funct_1(sK3,X4) = k1_funct_1(X1,X4) | ~r2_hidden(X4,k1_relset_1(X0,X0,X1))) | r1_partfun1(X1,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(sK3,X0,X0) & v1_funct_1(sK3))) )),
% 1.35/1.10    introduced(choice_axiom,[])).
% 1.35/1.10  
% 1.35/1.10  fof(f29,plain,(
% 1.35/1.10    ? [X0,X1] : (? [X2] : ((? [X3] : (k1_funct_1(X1,X3) != k1_funct_1(X2,X3) & r2_hidden(X3,k1_relset_1(X0,X0,X1))) | ~r1_partfun1(X1,X2)) & (! [X4] : (k1_funct_1(X1,X4) = k1_funct_1(X2,X4) | ~r2_hidden(X4,k1_relset_1(X0,X0,X1))) | r1_partfun1(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1)) => (? [X2] : ((? [X3] : (k1_funct_1(sK2,X3) != k1_funct_1(X2,X3) & r2_hidden(X3,k1_relset_1(sK1,sK1,sK2))) | ~r1_partfun1(sK2,X2)) & (! [X4] : (k1_funct_1(sK2,X4) = k1_funct_1(X2,X4) | ~r2_hidden(X4,k1_relset_1(sK1,sK1,sK2))) | r1_partfun1(sK2,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v1_funct_2(X2,sK1,sK1) & v1_funct_1(X2)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v1_funct_1(sK2))),
% 1.35/1.10    introduced(choice_axiom,[])).
% 1.35/1.10  
% 1.35/1.10  fof(f32,plain,(
% 1.35/1.10    (((k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4) & r2_hidden(sK4,k1_relset_1(sK1,sK1,sK2))) | ~r1_partfun1(sK2,sK3)) & (! [X4] : (k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) | ~r2_hidden(X4,k1_relset_1(sK1,sK1,sK2))) | r1_partfun1(sK2,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v1_funct_2(sK3,sK1,sK1) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v1_funct_1(sK2)),
% 1.35/1.10    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f28,f31,f30,f29])).
% 1.35/1.10  
% 1.35/1.10  fof(f48,plain,(
% 1.35/1.10    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))),
% 1.35/1.10    inference(cnf_transformation,[],[f32])).
% 1.35/1.10  
% 1.35/1.10  fof(f53,plain,(
% 1.35/1.10    r2_hidden(sK4,k1_relset_1(sK1,sK1,sK2)) | ~r1_partfun1(sK2,sK3)),
% 1.35/1.10    inference(cnf_transformation,[],[f32])).
% 1.35/1.10  
% 1.35/1.10  fof(f50,plain,(
% 1.35/1.10    v1_funct_2(sK3,sK1,sK1)),
% 1.35/1.10    inference(cnf_transformation,[],[f32])).
% 1.35/1.10  
% 1.35/1.10  fof(f5,axiom,(
% 1.35/1.10    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.35/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.35/1.10  
% 1.35/1.10  fof(f14,plain,(
% 1.35/1.10    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.35/1.10    inference(ennf_transformation,[],[f5])).
% 1.35/1.10  
% 1.35/1.10  fof(f15,plain,(
% 1.35/1.10    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.35/1.10    inference(flattening,[],[f14])).
% 1.35/1.10  
% 1.35/1.10  fof(f21,plain,(
% 1.35/1.10    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.35/1.10    inference(nnf_transformation,[],[f15])).
% 1.35/1.10  
% 1.35/1.10  fof(f38,plain,(
% 1.35/1.10    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.35/1.10    inference(cnf_transformation,[],[f21])).
% 1.35/1.10  
% 1.35/1.10  fof(f51,plain,(
% 1.35/1.10    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))),
% 1.35/1.10    inference(cnf_transformation,[],[f32])).
% 1.35/1.10  
% 1.35/1.10  fof(f6,axiom,(
% 1.35/1.10    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) => (r1_partfun1(X0,X1) <=> ! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2))))))),
% 1.35/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.35/1.10  
% 1.35/1.10  fof(f16,plain,(
% 1.35/1.10    ! [X0] : (! [X1] : (((r1_partfun1(X0,X1) <=> ! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0)))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.35/1.10    inference(ennf_transformation,[],[f6])).
% 1.35/1.10  
% 1.35/1.10  fof(f17,plain,(
% 1.35/1.10    ! [X0] : (! [X1] : ((r1_partfun1(X0,X1) <=> ! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0)))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.35/1.10    inference(flattening,[],[f16])).
% 1.35/1.10  
% 1.35/1.10  fof(f22,plain,(
% 1.35/1.10    ! [X0] : (! [X1] : (((r1_partfun1(X0,X1) | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0)))) & (! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0))) | ~r1_partfun1(X0,X1))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.35/1.10    inference(nnf_transformation,[],[f17])).
% 1.35/1.10  
% 1.35/1.10  fof(f23,plain,(
% 1.35/1.10    ! [X0] : (! [X1] : (((r1_partfun1(X0,X1) | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0)))) & (! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r1_partfun1(X0,X1))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.35/1.10    inference(rectify,[],[f22])).
% 1.35/1.10  
% 1.35/1.10  fof(f24,plain,(
% 1.35/1.10    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1)) & r2_hidden(sK0(X0,X1),k1_relat_1(X0))))),
% 1.35/1.10    introduced(choice_axiom,[])).
% 1.35/1.10  
% 1.35/1.10  fof(f25,plain,(
% 1.35/1.10    ! [X0] : (! [X1] : (((r1_partfun1(X0,X1) | (k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1)) & r2_hidden(sK0(X0,X1),k1_relat_1(X0)))) & (! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r1_partfun1(X0,X1))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.35/1.10    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).
% 1.35/1.10  
% 1.35/1.10  fof(f45,plain,(
% 1.35/1.10    ( ! [X0,X1] : (r1_partfun1(X0,X1) | r2_hidden(sK0(X0,X1),k1_relat_1(X0)) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.35/1.10    inference(cnf_transformation,[],[f25])).
% 1.35/1.10  
% 1.35/1.10  fof(f52,plain,(
% 1.35/1.10    ( ! [X4] : (k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) | ~r2_hidden(X4,k1_relset_1(sK1,sK1,sK2)) | r1_partfun1(sK2,sK3)) )),
% 1.35/1.10    inference(cnf_transformation,[],[f32])).
% 1.35/1.10  
% 1.35/1.10  fof(f47,plain,(
% 1.35/1.10    v1_funct_1(sK2)),
% 1.35/1.10    inference(cnf_transformation,[],[f32])).
% 1.35/1.10  
% 1.35/1.10  fof(f2,axiom,(
% 1.35/1.10    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.35/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.35/1.10  
% 1.35/1.10  fof(f11,plain,(
% 1.35/1.10    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.35/1.10    inference(ennf_transformation,[],[f2])).
% 1.35/1.10  
% 1.35/1.10  fof(f35,plain,(
% 1.35/1.10    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.35/1.10    inference(cnf_transformation,[],[f11])).
% 1.35/1.10  
% 1.35/1.10  fof(f49,plain,(
% 1.35/1.10    v1_funct_1(sK3)),
% 1.35/1.10    inference(cnf_transformation,[],[f32])).
% 1.35/1.10  
% 1.35/1.10  fof(f3,axiom,(
% 1.35/1.10    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.35/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.35/1.10  
% 1.35/1.10  fof(f9,plain,(
% 1.35/1.10    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.35/1.10    inference(pure_predicate_removal,[],[f3])).
% 1.35/1.10  
% 1.35/1.10  fof(f12,plain,(
% 1.35/1.10    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.35/1.10    inference(ennf_transformation,[],[f9])).
% 1.35/1.10  
% 1.35/1.10  fof(f36,plain,(
% 1.35/1.10    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.35/1.10    inference(cnf_transformation,[],[f12])).
% 1.35/1.10  
% 1.35/1.10  fof(f1,axiom,(
% 1.35/1.10    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.35/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.35/1.10  
% 1.35/1.10  fof(f10,plain,(
% 1.35/1.10    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.35/1.10    inference(ennf_transformation,[],[f1])).
% 1.35/1.10  
% 1.35/1.10  fof(f20,plain,(
% 1.35/1.10    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.35/1.10    inference(nnf_transformation,[],[f10])).
% 1.35/1.10  
% 1.35/1.10  fof(f33,plain,(
% 1.35/1.10    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.35/1.10    inference(cnf_transformation,[],[f20])).
% 1.35/1.10  
% 1.35/1.10  fof(f44,plain,(
% 1.35/1.10    ( ! [X0,X3,X1] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r1_partfun1(X0,X1) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.35/1.10    inference(cnf_transformation,[],[f25])).
% 1.35/1.10  
% 1.35/1.10  fof(f46,plain,(
% 1.35/1.10    ( ! [X0,X1] : (r1_partfun1(X0,X1) | k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1)) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.35/1.10    inference(cnf_transformation,[],[f25])).
% 1.35/1.10  
% 1.35/1.10  fof(f54,plain,(
% 1.35/1.10    k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4) | ~r1_partfun1(sK2,sK3)),
% 1.35/1.10    inference(cnf_transformation,[],[f32])).
% 1.35/1.10  
% 1.35/1.10  fof(f39,plain,(
% 1.35/1.10    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.35/1.10    inference(cnf_transformation,[],[f21])).
% 1.35/1.10  
% 1.35/1.10  fof(f59,plain,(
% 1.35/1.10    ( ! [X2,X1] : (k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0 | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 1.35/1.10    inference(equality_resolution,[],[f39])).
% 1.35/1.10  
% 1.35/1.10  fof(f42,plain,(
% 1.35/1.10    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.35/1.10    inference(cnf_transformation,[],[f21])).
% 1.35/1.10  
% 1.35/1.10  fof(f57,plain,(
% 1.35/1.10    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 1.35/1.10    inference(equality_resolution,[],[f42])).
% 1.35/1.10  
% 1.35/1.10  cnf(c_4,plain,
% 1.35/1.10      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.35/1.10      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 1.35/1.10      inference(cnf_transformation,[],[f37]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_20,negated_conjecture,
% 1.35/1.11      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 1.35/1.11      inference(cnf_transformation,[],[f48]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_634,plain,
% 1.35/1.11      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 1.35/1.11      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
% 1.35/1.11      | sK2 != X2 ),
% 1.35/1.11      inference(resolution_lifted,[status(thm)],[c_4,c_20]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_635,plain,
% 1.35/1.11      ( k1_relset_1(X0,X1,sK2) = k1_relat_1(sK2)
% 1.35/1.11      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) ),
% 1.35/1.11      inference(unflattening,[status(thm)],[c_634]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_2129,plain,
% 1.35/1.11      ( k1_relset_1(sK1,sK1,sK2) = k1_relat_1(sK2) ),
% 1.35/1.11      inference(equality_resolution,[status(thm)],[c_635]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_15,negated_conjecture,
% 1.35/1.11      ( r2_hidden(sK4,k1_relset_1(sK1,sK1,sK2))
% 1.35/1.11      | ~ r1_partfun1(sK2,sK3) ),
% 1.35/1.11      inference(cnf_transformation,[],[f53]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_1882,plain,
% 1.35/1.11      ( r2_hidden(sK4,k1_relset_1(sK1,sK1,sK2)) = iProver_top
% 1.35/1.11      | r1_partfun1(sK2,sK3) != iProver_top ),
% 1.35/1.11      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_2398,plain,
% 1.35/1.11      ( r2_hidden(sK4,k1_relat_1(sK2)) = iProver_top
% 1.35/1.11      | r1_partfun1(sK2,sK3) != iProver_top ),
% 1.35/1.11      inference(demodulation,[status(thm)],[c_2129,c_1882]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_18,negated_conjecture,
% 1.35/1.11      ( v1_funct_2(sK3,sK1,sK1) ),
% 1.35/1.11      inference(cnf_transformation,[],[f50]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_10,plain,
% 1.35/1.11      ( ~ v1_funct_2(X0,X1,X2)
% 1.35/1.11      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.35/1.11      | k1_relset_1(X1,X2,X0) = X1
% 1.35/1.11      | k1_xboole_0 = X2 ),
% 1.35/1.11      inference(cnf_transformation,[],[f38]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_17,negated_conjecture,
% 1.35/1.11      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 1.35/1.11      inference(cnf_transformation,[],[f51]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_529,plain,
% 1.35/1.11      ( ~ v1_funct_2(X0,X1,X2)
% 1.35/1.11      | k1_relset_1(X1,X2,X0) = X1
% 1.35/1.11      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
% 1.35/1.11      | sK3 != X0
% 1.35/1.11      | k1_xboole_0 = X2 ),
% 1.35/1.11      inference(resolution_lifted,[status(thm)],[c_10,c_17]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_530,plain,
% 1.35/1.11      ( ~ v1_funct_2(sK3,X0,X1)
% 1.35/1.11      | k1_relset_1(X0,X1,sK3) = X0
% 1.35/1.11      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
% 1.35/1.11      | k1_xboole_0 = X1 ),
% 1.35/1.11      inference(unflattening,[status(thm)],[c_529]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_1383,plain,
% 1.35/1.11      ( k1_relset_1(X0,X1,sK3) = X0
% 1.35/1.11      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
% 1.35/1.11      | sK1 != X0
% 1.35/1.11      | sK1 != X1
% 1.35/1.11      | sK3 != sK3
% 1.35/1.11      | k1_xboole_0 = X1 ),
% 1.35/1.11      inference(resolution_lifted,[status(thm)],[c_18,c_530]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_1384,plain,
% 1.35/1.11      ( k1_relset_1(sK1,sK1,sK3) = sK1
% 1.35/1.11      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
% 1.35/1.11      | k1_xboole_0 = sK1 ),
% 1.35/1.11      inference(unflattening,[status(thm)],[c_1383]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_1923,plain,
% 1.35/1.11      ( k1_relset_1(sK1,sK1,sK3) = sK1 | k1_xboole_0 = sK1 ),
% 1.35/1.11      inference(equality_resolution_simp,[status(thm)],[c_1384]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_565,plain,
% 1.35/1.11      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 1.35/1.11      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
% 1.35/1.11      | sK3 != X2 ),
% 1.35/1.11      inference(resolution_lifted,[status(thm)],[c_4,c_17]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_566,plain,
% 1.35/1.11      ( k1_relset_1(X0,X1,sK3) = k1_relat_1(sK3)
% 1.35/1.11      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) ),
% 1.35/1.11      inference(unflattening,[status(thm)],[c_565]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_2126,plain,
% 1.35/1.11      ( k1_relset_1(sK1,sK1,sK3) = k1_relat_1(sK3) ),
% 1.35/1.11      inference(equality_resolution,[status(thm)],[c_566]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_2738,plain,
% 1.35/1.11      ( k1_relat_1(sK3) = sK1 | sK1 = k1_xboole_0 ),
% 1.35/1.11      inference(demodulation,[status(thm)],[c_1923,c_2126]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_12,plain,
% 1.35/1.11      ( r2_hidden(sK0(X0,X1),k1_relat_1(X0))
% 1.35/1.11      | r1_partfun1(X0,X1)
% 1.35/1.11      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 1.35/1.11      | ~ v1_funct_1(X1)
% 1.35/1.11      | ~ v1_funct_1(X0)
% 1.35/1.11      | ~ v1_relat_1(X1)
% 1.35/1.11      | ~ v1_relat_1(X0) ),
% 1.35/1.11      inference(cnf_transformation,[],[f45]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_1885,plain,
% 1.35/1.11      ( r2_hidden(sK0(X0,X1),k1_relat_1(X0)) = iProver_top
% 1.35/1.11      | r1_partfun1(X0,X1) = iProver_top
% 1.35/1.11      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) != iProver_top
% 1.35/1.11      | v1_funct_1(X1) != iProver_top
% 1.35/1.11      | v1_funct_1(X0) != iProver_top
% 1.35/1.11      | v1_relat_1(X1) != iProver_top
% 1.35/1.11      | v1_relat_1(X0) != iProver_top ),
% 1.35/1.11      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_16,negated_conjecture,
% 1.35/1.11      ( ~ r2_hidden(X0,k1_relset_1(sK1,sK1,sK2))
% 1.35/1.11      | r1_partfun1(sK2,sK3)
% 1.35/1.11      | k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0) ),
% 1.35/1.11      inference(cnf_transformation,[],[f52]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_1881,plain,
% 1.35/1.11      ( k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0)
% 1.35/1.11      | r2_hidden(X0,k1_relset_1(sK1,sK1,sK2)) != iProver_top
% 1.35/1.11      | r1_partfun1(sK2,sK3) = iProver_top ),
% 1.35/1.11      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_2397,plain,
% 1.35/1.11      ( k1_funct_1(sK3,X0) = k1_funct_1(sK2,X0)
% 1.35/1.11      | r2_hidden(X0,k1_relat_1(sK2)) != iProver_top
% 1.35/1.11      | r1_partfun1(sK2,sK3) = iProver_top ),
% 1.35/1.11      inference(demodulation,[status(thm)],[c_2129,c_1881]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_2598,plain,
% 1.35/1.11      ( k1_funct_1(sK2,sK0(sK2,X0)) = k1_funct_1(sK3,sK0(sK2,X0))
% 1.35/1.11      | r1_partfun1(sK2,X0) = iProver_top
% 1.35/1.11      | r1_partfun1(sK2,sK3) = iProver_top
% 1.35/1.11      | r1_tarski(k1_relat_1(sK2),k1_relat_1(X0)) != iProver_top
% 1.35/1.11      | v1_funct_1(X0) != iProver_top
% 1.35/1.11      | v1_funct_1(sK2) != iProver_top
% 1.35/1.11      | v1_relat_1(X0) != iProver_top
% 1.35/1.11      | v1_relat_1(sK2) != iProver_top ),
% 1.35/1.11      inference(superposition,[status(thm)],[c_1885,c_2397]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_21,negated_conjecture,
% 1.35/1.11      ( v1_funct_1(sK2) ),
% 1.35/1.11      inference(cnf_transformation,[],[f47]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_22,plain,
% 1.35/1.11      ( v1_funct_1(sK2) = iProver_top ),
% 1.35/1.11      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_1604,plain,( X0 = X0 ),theory(equality) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_2092,plain,
% 1.35/1.11      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) ),
% 1.35/1.11      inference(instantiation,[status(thm)],[c_1604]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_2,plain,
% 1.35/1.11      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.35/1.11      | v1_relat_1(X0) ),
% 1.35/1.11      inference(cnf_transformation,[],[f35]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_643,plain,
% 1.35/1.11      ( v1_relat_1(X0)
% 1.35/1.11      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
% 1.35/1.11      | sK2 != X0 ),
% 1.35/1.11      inference(resolution_lifted,[status(thm)],[c_2,c_20]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_644,plain,
% 1.35/1.11      ( v1_relat_1(sK2)
% 1.35/1.11      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) ),
% 1.35/1.11      inference(unflattening,[status(thm)],[c_643]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_2097,plain,
% 1.35/1.11      ( v1_relat_1(sK2)
% 1.35/1.11      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) ),
% 1.35/1.11      inference(instantiation,[status(thm)],[c_644]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_2101,plain,
% 1.35/1.11      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
% 1.35/1.11      | v1_relat_1(sK2) = iProver_top ),
% 1.35/1.11      inference(predicate_to_equality,[status(thm)],[c_2097]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_2711,plain,
% 1.35/1.11      ( v1_relat_1(X0) != iProver_top
% 1.35/1.11      | k1_funct_1(sK2,sK0(sK2,X0)) = k1_funct_1(sK3,sK0(sK2,X0))
% 1.35/1.11      | r1_partfun1(sK2,X0) = iProver_top
% 1.35/1.11      | r1_partfun1(sK2,sK3) = iProver_top
% 1.35/1.11      | r1_tarski(k1_relat_1(sK2),k1_relat_1(X0)) != iProver_top
% 1.35/1.11      | v1_funct_1(X0) != iProver_top ),
% 1.35/1.11      inference(global_propositional_subsumption,
% 1.35/1.11                [status(thm)],
% 1.35/1.11                [c_2598,c_22,c_2092,c_2101]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_2712,plain,
% 1.35/1.11      ( k1_funct_1(sK2,sK0(sK2,X0)) = k1_funct_1(sK3,sK0(sK2,X0))
% 1.35/1.11      | r1_partfun1(sK2,X0) = iProver_top
% 1.35/1.11      | r1_partfun1(sK2,sK3) = iProver_top
% 1.35/1.11      | r1_tarski(k1_relat_1(sK2),k1_relat_1(X0)) != iProver_top
% 1.35/1.11      | v1_funct_1(X0) != iProver_top
% 1.35/1.11      | v1_relat_1(X0) != iProver_top ),
% 1.35/1.11      inference(renaming,[status(thm)],[c_2711]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_2741,plain,
% 1.35/1.11      ( k1_funct_1(sK3,sK0(sK2,sK3)) = k1_funct_1(sK2,sK0(sK2,sK3))
% 1.35/1.11      | sK1 = k1_xboole_0
% 1.35/1.11      | r1_partfun1(sK2,sK3) = iProver_top
% 1.35/1.11      | r1_tarski(k1_relat_1(sK2),sK1) != iProver_top
% 1.35/1.11      | v1_funct_1(sK3) != iProver_top
% 1.35/1.11      | v1_relat_1(sK3) != iProver_top ),
% 1.35/1.11      inference(superposition,[status(thm)],[c_2738,c_2712]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_19,negated_conjecture,
% 1.35/1.11      ( v1_funct_1(sK3) ),
% 1.35/1.11      inference(cnf_transformation,[],[f49]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_24,plain,
% 1.35/1.11      ( v1_funct_1(sK3) = iProver_top ),
% 1.35/1.11      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_574,plain,
% 1.35/1.11      ( v1_relat_1(X0)
% 1.35/1.11      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
% 1.35/1.11      | sK3 != X0 ),
% 1.35/1.11      inference(resolution_lifted,[status(thm)],[c_2,c_17]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_575,plain,
% 1.35/1.11      ( v1_relat_1(sK3)
% 1.35/1.11      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) ),
% 1.35/1.11      inference(unflattening,[status(thm)],[c_574]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_2098,plain,
% 1.35/1.11      ( v1_relat_1(sK3)
% 1.35/1.11      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) ),
% 1.35/1.11      inference(instantiation,[status(thm)],[c_575]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_2099,plain,
% 1.35/1.11      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
% 1.35/1.11      | v1_relat_1(sK3) = iProver_top ),
% 1.35/1.11      inference(predicate_to_equality,[status(thm)],[c_2098]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_3,plain,
% 1.35/1.11      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.35/1.11      | v4_relat_1(X0,X1) ),
% 1.35/1.11      inference(cnf_transformation,[],[f36]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_1,plain,
% 1.35/1.11      ( r1_tarski(k1_relat_1(X0),X1)
% 1.35/1.11      | ~ v4_relat_1(X0,X1)
% 1.35/1.11      | ~ v1_relat_1(X0) ),
% 1.35/1.11      inference(cnf_transformation,[],[f33]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_246,plain,
% 1.35/1.11      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.35/1.11      | r1_tarski(k1_relat_1(X0),X1)
% 1.35/1.11      | ~ v1_relat_1(X0) ),
% 1.35/1.11      inference(resolution,[status(thm)],[c_3,c_1]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_250,plain,
% 1.35/1.11      ( r1_tarski(k1_relat_1(X0),X1)
% 1.35/1.11      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 1.35/1.11      inference(global_propositional_subsumption,
% 1.35/1.11                [status(thm)],
% 1.35/1.11                [c_246,c_2]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_251,plain,
% 1.35/1.11      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.35/1.11      | r1_tarski(k1_relat_1(X0),X1) ),
% 1.35/1.11      inference(renaming,[status(thm)],[c_250]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_586,plain,
% 1.35/1.11      ( r1_tarski(k1_relat_1(X0),X1)
% 1.35/1.11      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
% 1.35/1.11      | sK2 != X0 ),
% 1.35/1.11      inference(resolution_lifted,[status(thm)],[c_251,c_20]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_587,plain,
% 1.35/1.11      ( r1_tarski(k1_relat_1(sK2),X0)
% 1.35/1.11      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) ),
% 1.35/1.11      inference(unflattening,[status(thm)],[c_586]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_2095,plain,
% 1.35/1.11      ( r1_tarski(k1_relat_1(sK2),sK1)
% 1.35/1.11      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) ),
% 1.35/1.11      inference(instantiation,[status(thm)],[c_587]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_2105,plain,
% 1.35/1.11      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
% 1.35/1.11      | r1_tarski(k1_relat_1(sK2),sK1) = iProver_top ),
% 1.35/1.11      inference(predicate_to_equality,[status(thm)],[c_2095]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_3016,plain,
% 1.35/1.11      ( r1_partfun1(sK2,sK3) = iProver_top
% 1.35/1.11      | sK1 = k1_xboole_0
% 1.35/1.11      | k1_funct_1(sK3,sK0(sK2,sK3)) = k1_funct_1(sK2,sK0(sK2,sK3)) ),
% 1.35/1.11      inference(global_propositional_subsumption,
% 1.35/1.11                [status(thm)],
% 1.35/1.11                [c_2741,c_24,c_2092,c_2099,c_2105]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_3017,plain,
% 1.35/1.11      ( k1_funct_1(sK3,sK0(sK2,sK3)) = k1_funct_1(sK2,sK0(sK2,sK3))
% 1.35/1.11      | sK1 = k1_xboole_0
% 1.35/1.11      | r1_partfun1(sK2,sK3) = iProver_top ),
% 1.35/1.11      inference(renaming,[status(thm)],[c_3016]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_13,plain,
% 1.35/1.11      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 1.35/1.11      | ~ r1_partfun1(X1,X2)
% 1.35/1.11      | ~ r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
% 1.35/1.11      | ~ v1_funct_1(X2)
% 1.35/1.11      | ~ v1_funct_1(X1)
% 1.35/1.11      | ~ v1_relat_1(X2)
% 1.35/1.11      | ~ v1_relat_1(X1)
% 1.35/1.11      | k1_funct_1(X2,X0) = k1_funct_1(X1,X0) ),
% 1.35/1.11      inference(cnf_transformation,[],[f44]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_1884,plain,
% 1.35/1.11      ( k1_funct_1(X0,X1) = k1_funct_1(X2,X1)
% 1.35/1.11      | r2_hidden(X1,k1_relat_1(X2)) != iProver_top
% 1.35/1.11      | r1_partfun1(X2,X0) != iProver_top
% 1.35/1.11      | r1_tarski(k1_relat_1(X2),k1_relat_1(X0)) != iProver_top
% 1.35/1.11      | v1_funct_1(X0) != iProver_top
% 1.35/1.11      | v1_funct_1(X2) != iProver_top
% 1.35/1.11      | v1_relat_1(X0) != iProver_top
% 1.35/1.11      | v1_relat_1(X2) != iProver_top ),
% 1.35/1.11      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_2744,plain,
% 1.35/1.11      ( k1_funct_1(X0,X1) = k1_funct_1(sK3,X1)
% 1.35/1.11      | sK1 = k1_xboole_0
% 1.35/1.11      | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
% 1.35/1.11      | r1_partfun1(X0,sK3) != iProver_top
% 1.35/1.11      | r1_tarski(k1_relat_1(X0),sK1) != iProver_top
% 1.35/1.11      | v1_funct_1(X0) != iProver_top
% 1.35/1.11      | v1_funct_1(sK3) != iProver_top
% 1.35/1.11      | v1_relat_1(X0) != iProver_top
% 1.35/1.11      | v1_relat_1(sK3) != iProver_top ),
% 1.35/1.11      inference(superposition,[status(thm)],[c_2738,c_1884]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_3107,plain,
% 1.35/1.11      ( v1_relat_1(X0) != iProver_top
% 1.35/1.11      | k1_funct_1(X0,X1) = k1_funct_1(sK3,X1)
% 1.35/1.11      | sK1 = k1_xboole_0
% 1.35/1.11      | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
% 1.35/1.11      | r1_partfun1(X0,sK3) != iProver_top
% 1.35/1.11      | r1_tarski(k1_relat_1(X0),sK1) != iProver_top
% 1.35/1.11      | v1_funct_1(X0) != iProver_top ),
% 1.35/1.11      inference(global_propositional_subsumption,
% 1.35/1.11                [status(thm)],
% 1.35/1.11                [c_2744,c_24,c_2092,c_2099]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_3108,plain,
% 1.35/1.11      ( k1_funct_1(X0,X1) = k1_funct_1(sK3,X1)
% 1.35/1.11      | sK1 = k1_xboole_0
% 1.35/1.11      | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
% 1.35/1.11      | r1_partfun1(X0,sK3) != iProver_top
% 1.35/1.11      | r1_tarski(k1_relat_1(X0),sK1) != iProver_top
% 1.35/1.11      | v1_funct_1(X0) != iProver_top
% 1.35/1.11      | v1_relat_1(X0) != iProver_top ),
% 1.35/1.11      inference(renaming,[status(thm)],[c_3107]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_3121,plain,
% 1.35/1.11      ( k1_funct_1(sK3,sK4) = k1_funct_1(sK2,sK4)
% 1.35/1.11      | sK1 = k1_xboole_0
% 1.35/1.11      | r1_partfun1(sK2,sK3) != iProver_top
% 1.35/1.11      | r1_tarski(k1_relat_1(sK2),sK1) != iProver_top
% 1.35/1.11      | v1_funct_1(sK2) != iProver_top
% 1.35/1.11      | v1_relat_1(sK2) != iProver_top ),
% 1.35/1.11      inference(superposition,[status(thm)],[c_2398,c_3108]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_3289,plain,
% 1.35/1.11      ( r1_partfun1(sK2,sK3) != iProver_top
% 1.35/1.11      | sK1 = k1_xboole_0
% 1.35/1.11      | k1_funct_1(sK3,sK4) = k1_funct_1(sK2,sK4) ),
% 1.35/1.11      inference(global_propositional_subsumption,
% 1.35/1.11                [status(thm)],
% 1.35/1.11                [c_3121,c_22,c_2092,c_2101,c_2105]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_3290,plain,
% 1.35/1.11      ( k1_funct_1(sK3,sK4) = k1_funct_1(sK2,sK4)
% 1.35/1.11      | sK1 = k1_xboole_0
% 1.35/1.11      | r1_partfun1(sK2,sK3) != iProver_top ),
% 1.35/1.11      inference(renaming,[status(thm)],[c_3289]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_3296,plain,
% 1.35/1.11      ( k1_funct_1(sK3,sK0(sK2,sK3)) = k1_funct_1(sK2,sK0(sK2,sK3))
% 1.35/1.11      | k1_funct_1(sK3,sK4) = k1_funct_1(sK2,sK4)
% 1.35/1.11      | sK1 = k1_xboole_0 ),
% 1.35/1.11      inference(superposition,[status(thm)],[c_3017,c_3290]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_11,plain,
% 1.35/1.11      ( r1_partfun1(X0,X1)
% 1.35/1.11      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 1.35/1.11      | ~ v1_funct_1(X1)
% 1.35/1.11      | ~ v1_funct_1(X0)
% 1.35/1.11      | ~ v1_relat_1(X1)
% 1.35/1.11      | ~ v1_relat_1(X0)
% 1.35/1.11      | k1_funct_1(X1,sK0(X0,X1)) != k1_funct_1(X0,sK0(X0,X1)) ),
% 1.35/1.11      inference(cnf_transformation,[],[f46]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_1886,plain,
% 1.35/1.11      ( k1_funct_1(X0,sK0(X1,X0)) != k1_funct_1(X1,sK0(X1,X0))
% 1.35/1.11      | r1_partfun1(X1,X0) = iProver_top
% 1.35/1.11      | r1_tarski(k1_relat_1(X1),k1_relat_1(X0)) != iProver_top
% 1.35/1.11      | v1_funct_1(X0) != iProver_top
% 1.35/1.11      | v1_funct_1(X1) != iProver_top
% 1.35/1.11      | v1_relat_1(X0) != iProver_top
% 1.35/1.11      | v1_relat_1(X1) != iProver_top ),
% 1.35/1.11      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_3415,plain,
% 1.35/1.11      ( k1_funct_1(sK3,sK4) = k1_funct_1(sK2,sK4)
% 1.35/1.11      | sK1 = k1_xboole_0
% 1.35/1.11      | r1_partfun1(sK2,sK3) = iProver_top
% 1.35/1.11      | r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3)) != iProver_top
% 1.35/1.11      | v1_funct_1(sK3) != iProver_top
% 1.35/1.11      | v1_funct_1(sK2) != iProver_top
% 1.35/1.11      | v1_relat_1(sK3) != iProver_top
% 1.35/1.11      | v1_relat_1(sK2) != iProver_top ),
% 1.35/1.11      inference(superposition,[status(thm)],[c_3296,c_1886]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_2140,plain,
% 1.35/1.11      ( r1_partfun1(X0,sK3)
% 1.35/1.11      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(sK3))
% 1.35/1.11      | ~ v1_funct_1(X0)
% 1.35/1.11      | ~ v1_funct_1(sK3)
% 1.35/1.11      | ~ v1_relat_1(X0)
% 1.35/1.11      | ~ v1_relat_1(sK3)
% 1.35/1.11      | k1_funct_1(sK3,sK0(X0,sK3)) != k1_funct_1(X0,sK0(X0,sK3)) ),
% 1.35/1.11      inference(instantiation,[status(thm)],[c_11]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_2190,plain,
% 1.35/1.11      ( r1_partfun1(sK2,sK3)
% 1.35/1.11      | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3))
% 1.35/1.11      | ~ v1_funct_1(sK3)
% 1.35/1.11      | ~ v1_funct_1(sK2)
% 1.35/1.11      | ~ v1_relat_1(sK3)
% 1.35/1.11      | ~ v1_relat_1(sK2)
% 1.35/1.11      | k1_funct_1(sK3,sK0(sK2,sK3)) != k1_funct_1(sK2,sK0(sK2,sK3)) ),
% 1.35/1.11      inference(instantiation,[status(thm)],[c_2140]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_2191,plain,
% 1.35/1.11      ( k1_funct_1(sK3,sK0(sK2,sK3)) != k1_funct_1(sK2,sK0(sK2,sK3))
% 1.35/1.11      | r1_partfun1(sK2,sK3) = iProver_top
% 1.35/1.11      | r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3)) != iProver_top
% 1.35/1.11      | v1_funct_1(sK3) != iProver_top
% 1.35/1.11      | v1_funct_1(sK2) != iProver_top
% 1.35/1.11      | v1_relat_1(sK3) != iProver_top
% 1.35/1.11      | v1_relat_1(sK2) != iProver_top ),
% 1.35/1.11      inference(predicate_to_equality,[status(thm)],[c_2190]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_3558,plain,
% 1.35/1.11      ( sK1 = k1_xboole_0
% 1.35/1.11      | r1_partfun1(sK2,sK3) = iProver_top
% 1.35/1.11      | r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3)) != iProver_top ),
% 1.35/1.11      inference(global_propositional_subsumption,
% 1.35/1.11                [status(thm)],
% 1.35/1.11                [c_3415,c_22,c_24,c_2092,c_2099,c_2101,c_2105,c_2191,
% 1.35/1.11                 c_2741]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_3565,plain,
% 1.35/1.11      ( sK1 = k1_xboole_0
% 1.35/1.11      | r1_partfun1(sK2,sK3) = iProver_top
% 1.35/1.11      | r1_tarski(k1_relat_1(sK2),sK1) != iProver_top ),
% 1.35/1.11      inference(superposition,[status(thm)],[c_2738,c_3558]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_3568,plain,
% 1.35/1.11      ( r1_partfun1(sK2,sK3) = iProver_top | sK1 = k1_xboole_0 ),
% 1.35/1.11      inference(global_propositional_subsumption,
% 1.35/1.11                [status(thm)],
% 1.35/1.11                [c_3565,c_2092,c_2105]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_3569,plain,
% 1.35/1.11      ( sK1 = k1_xboole_0 | r1_partfun1(sK2,sK3) = iProver_top ),
% 1.35/1.11      inference(renaming,[status(thm)],[c_3568]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_3574,plain,
% 1.35/1.11      ( k1_funct_1(sK3,sK4) = k1_funct_1(sK2,sK4) | sK1 = k1_xboole_0 ),
% 1.35/1.11      inference(superposition,[status(thm)],[c_3569,c_3290]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_14,negated_conjecture,
% 1.35/1.11      ( ~ r1_partfun1(sK2,sK3)
% 1.35/1.11      | k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4) ),
% 1.35/1.11      inference(cnf_transformation,[],[f54]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_1883,plain,
% 1.35/1.11      ( k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4)
% 1.35/1.11      | r1_partfun1(sK2,sK3) != iProver_top ),
% 1.35/1.11      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_3614,plain,
% 1.35/1.11      ( sK1 = k1_xboole_0 | r1_partfun1(sK2,sK3) != iProver_top ),
% 1.35/1.11      inference(superposition,[status(thm)],[c_3574,c_1883]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_3617,plain,
% 1.35/1.11      ( sK1 = k1_xboole_0 ),
% 1.35/1.11      inference(global_propositional_subsumption,
% 1.35/1.11                [status(thm)],
% 1.35/1.11                [c_3614,c_2092,c_2105,c_3565]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_3635,plain,
% 1.35/1.11      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_relat_1(sK3) ),
% 1.35/1.11      inference(demodulation,[status(thm)],[c_3617,c_2126]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_9,plain,
% 1.35/1.11      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 1.35/1.11      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 1.35/1.11      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 1.35/1.11      inference(cnf_transformation,[],[f59]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_725,plain,
% 1.35/1.11      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 1.35/1.11      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 1.35/1.11      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
% 1.35/1.11      | sK3 != X0 ),
% 1.35/1.11      inference(resolution_lifted,[status(thm)],[c_9,c_17]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_726,plain,
% 1.35/1.11      ( ~ v1_funct_2(sK3,k1_xboole_0,X0)
% 1.35/1.11      | k1_relset_1(k1_xboole_0,X0,sK3) = k1_xboole_0
% 1.35/1.11      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) ),
% 1.35/1.11      inference(unflattening,[status(thm)],[c_725]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_1439,plain,
% 1.35/1.11      ( k1_relset_1(k1_xboole_0,X0,sK3) = k1_xboole_0
% 1.35/1.11      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
% 1.35/1.11      | sK1 != X0
% 1.35/1.11      | sK1 != k1_xboole_0
% 1.35/1.11      | sK3 != sK3 ),
% 1.35/1.11      inference(resolution_lifted,[status(thm)],[c_18,c_726]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_1440,plain,
% 1.35/1.11      ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
% 1.35/1.11      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
% 1.35/1.11      | sK1 != k1_xboole_0 ),
% 1.35/1.11      inference(unflattening,[status(thm)],[c_1439]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_3639,plain,
% 1.35/1.11      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
% 1.35/1.11      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
% 1.35/1.11      | k1_xboole_0 != k1_xboole_0 ),
% 1.35/1.11      inference(demodulation,[status(thm)],[c_3617,c_1440]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_3650,plain,
% 1.35/1.11      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0 ),
% 1.35/1.11      inference(equality_resolution_simp,[status(thm)],[c_3639]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_3658,plain,
% 1.35/1.11      ( k1_relat_1(sK3) = k1_xboole_0 ),
% 1.35/1.11      inference(light_normalisation,[status(thm)],[c_3635,c_3650]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_3956,plain,
% 1.35/1.11      ( k1_funct_1(X0,X1) = k1_funct_1(sK3,X1)
% 1.35/1.11      | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
% 1.35/1.11      | r1_partfun1(X0,sK3) != iProver_top
% 1.35/1.11      | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
% 1.35/1.11      | v1_funct_1(X0) != iProver_top
% 1.35/1.11      | v1_funct_1(sK3) != iProver_top
% 1.35/1.11      | v1_relat_1(X0) != iProver_top
% 1.35/1.11      | v1_relat_1(sK3) != iProver_top ),
% 1.35/1.11      inference(superposition,[status(thm)],[c_3658,c_1884]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_4072,plain,
% 1.35/1.11      ( v1_relat_1(X0) != iProver_top
% 1.35/1.11      | k1_funct_1(X0,X1) = k1_funct_1(sK3,X1)
% 1.35/1.11      | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
% 1.35/1.11      | r1_partfun1(X0,sK3) != iProver_top
% 1.35/1.11      | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
% 1.35/1.11      | v1_funct_1(X0) != iProver_top ),
% 1.35/1.11      inference(global_propositional_subsumption,
% 1.35/1.11                [status(thm)],
% 1.35/1.11                [c_3956,c_24,c_2092,c_2099]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_4073,plain,
% 1.35/1.11      ( k1_funct_1(X0,X1) = k1_funct_1(sK3,X1)
% 1.35/1.11      | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
% 1.35/1.11      | r1_partfun1(X0,sK3) != iProver_top
% 1.35/1.11      | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
% 1.35/1.11      | v1_funct_1(X0) != iProver_top
% 1.35/1.11      | v1_relat_1(X0) != iProver_top ),
% 1.35/1.11      inference(renaming,[status(thm)],[c_4072]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_4085,plain,
% 1.35/1.11      ( k1_funct_1(sK3,sK4) = k1_funct_1(sK2,sK4)
% 1.35/1.11      | r1_partfun1(sK2,sK3) != iProver_top
% 1.35/1.11      | r1_tarski(k1_relat_1(sK2),k1_xboole_0) != iProver_top
% 1.35/1.11      | v1_funct_1(sK2) != iProver_top
% 1.35/1.11      | v1_relat_1(sK2) != iProver_top ),
% 1.35/1.11      inference(superposition,[status(thm)],[c_2398,c_4073]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_6,plain,
% 1.35/1.11      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 1.35/1.11      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 1.35/1.11      | k1_xboole_0 = X1
% 1.35/1.11      | k1_xboole_0 = X0 ),
% 1.35/1.11      inference(cnf_transformation,[],[f57]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_707,plain,
% 1.35/1.11      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 1.35/1.11      | k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
% 1.35/1.11      | sK2 != X0
% 1.35/1.11      | k1_xboole_0 = X1
% 1.35/1.11      | k1_xboole_0 = X0 ),
% 1.35/1.11      inference(resolution_lifted,[status(thm)],[c_6,c_20]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_708,plain,
% 1.35/1.11      ( ~ v1_funct_2(sK2,X0,k1_xboole_0)
% 1.35/1.11      | k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
% 1.35/1.11      | k1_xboole_0 = X0
% 1.35/1.11      | k1_xboole_0 = sK2 ),
% 1.35/1.11      inference(unflattening,[status(thm)],[c_707]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_1422,plain,
% 1.35/1.11      ( k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
% 1.35/1.11      | sK1 != X0
% 1.35/1.11      | sK1 != k1_xboole_0
% 1.35/1.11      | sK3 != sK2
% 1.35/1.11      | sK2 = k1_xboole_0
% 1.35/1.11      | k1_xboole_0 = X0 ),
% 1.35/1.11      inference(resolution_lifted,[status(thm)],[c_18,c_708]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_1423,plain,
% 1.35/1.11      ( k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
% 1.35/1.11      | sK1 != k1_xboole_0
% 1.35/1.11      | sK3 != sK2
% 1.35/1.11      | sK2 = k1_xboole_0
% 1.35/1.11      | k1_xboole_0 = sK1 ),
% 1.35/1.11      inference(unflattening,[status(thm)],[c_1422]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_1627,plain,
% 1.35/1.11      ( k1_xboole_0 = k1_xboole_0 ),
% 1.35/1.11      inference(instantiation,[status(thm)],[c_1604]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_1605,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_2314,plain,
% 1.35/1.11      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 1.35/1.11      inference(instantiation,[status(thm)],[c_1605]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_2315,plain,
% 1.35/1.11      ( sK1 != k1_xboole_0
% 1.35/1.11      | k1_xboole_0 = sK1
% 1.35/1.11      | k1_xboole_0 != k1_xboole_0 ),
% 1.35/1.11      inference(instantiation,[status(thm)],[c_2314]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_2325,plain,
% 1.35/1.11      ( sK1 != k1_xboole_0 | k1_xboole_0 = sK1 ),
% 1.35/1.11      inference(global_propositional_subsumption,
% 1.35/1.11                [status(thm)],
% 1.35/1.11                [c_1423,c_1627,c_2315]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_1607,plain,
% 1.35/1.11      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 1.35/1.11      theory(equality) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_2201,plain,
% 1.35/1.11      ( r1_tarski(X0,X1)
% 1.35/1.11      | ~ r1_tarski(k1_relat_1(sK2),sK1)
% 1.35/1.11      | X0 != k1_relat_1(sK2)
% 1.35/1.11      | X1 != sK1 ),
% 1.35/1.11      inference(instantiation,[status(thm)],[c_1607]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_2841,plain,
% 1.35/1.11      ( r1_tarski(k1_relat_1(sK2),X0)
% 1.35/1.11      | ~ r1_tarski(k1_relat_1(sK2),sK1)
% 1.35/1.11      | X0 != sK1
% 1.35/1.11      | k1_relat_1(sK2) != k1_relat_1(sK2) ),
% 1.35/1.11      inference(instantiation,[status(thm)],[c_2201]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_2843,plain,
% 1.35/1.11      ( X0 != sK1
% 1.35/1.11      | k1_relat_1(sK2) != k1_relat_1(sK2)
% 1.35/1.11      | r1_tarski(k1_relat_1(sK2),X0) = iProver_top
% 1.35/1.11      | r1_tarski(k1_relat_1(sK2),sK1) != iProver_top ),
% 1.35/1.11      inference(predicate_to_equality,[status(thm)],[c_2841]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_2845,plain,
% 1.35/1.11      ( k1_relat_1(sK2) != k1_relat_1(sK2)
% 1.35/1.11      | k1_xboole_0 != sK1
% 1.35/1.11      | r1_tarski(k1_relat_1(sK2),sK1) != iProver_top
% 1.35/1.11      | r1_tarski(k1_relat_1(sK2),k1_xboole_0) = iProver_top ),
% 1.35/1.11      inference(instantiation,[status(thm)],[c_2843]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_2842,plain,
% 1.35/1.11      ( k1_relat_1(sK2) = k1_relat_1(sK2) ),
% 1.35/1.11      inference(instantiation,[status(thm)],[c_1604]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_2348,plain,
% 1.35/1.11      ( X0 != X1 | X0 = sK1 | sK1 != X1 ),
% 1.35/1.11      inference(instantiation,[status(thm)],[c_1605]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_3476,plain,
% 1.35/1.11      ( k1_relat_1(sK3) != X0 | k1_relat_1(sK3) = sK1 | sK1 != X0 ),
% 1.35/1.11      inference(instantiation,[status(thm)],[c_2348]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_3479,plain,
% 1.35/1.11      ( k1_relat_1(sK3) = sK1
% 1.35/1.11      | k1_relat_1(sK3) != k1_xboole_0
% 1.35/1.11      | sK1 != k1_xboole_0 ),
% 1.35/1.11      inference(instantiation,[status(thm)],[c_3476]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_3953,plain,
% 1.35/1.11      ( k1_funct_1(sK3,sK0(sK2,sK3)) = k1_funct_1(sK2,sK0(sK2,sK3))
% 1.35/1.11      | r1_partfun1(sK2,sK3) = iProver_top
% 1.35/1.11      | r1_tarski(k1_relat_1(sK2),k1_xboole_0) != iProver_top
% 1.35/1.11      | v1_funct_1(sK3) != iProver_top
% 1.35/1.11      | v1_relat_1(sK3) != iProver_top ),
% 1.35/1.11      inference(superposition,[status(thm)],[c_3658,c_2712]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_4118,plain,
% 1.35/1.11      ( r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3))
% 1.35/1.11      | ~ r1_tarski(k1_relat_1(sK2),sK1)
% 1.35/1.11      | k1_relat_1(sK3) != sK1
% 1.35/1.11      | k1_relat_1(sK2) != k1_relat_1(sK2) ),
% 1.35/1.11      inference(instantiation,[status(thm)],[c_2841]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_4119,plain,
% 1.35/1.11      ( k1_relat_1(sK3) != sK1
% 1.35/1.11      | k1_relat_1(sK2) != k1_relat_1(sK2)
% 1.35/1.11      | r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3)) = iProver_top
% 1.35/1.11      | r1_tarski(k1_relat_1(sK2),sK1) != iProver_top ),
% 1.35/1.11      inference(predicate_to_equality,[status(thm)],[c_4118]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_4228,plain,
% 1.35/1.11      ( k1_funct_1(sK3,sK4) = k1_funct_1(sK2,sK4) ),
% 1.35/1.11      inference(global_propositional_subsumption,
% 1.35/1.11                [status(thm)],
% 1.35/1.11                [c_4085,c_22,c_24,c_1627,c_2092,c_2099,c_2101,c_2105,
% 1.35/1.11                 c_2191,c_2315,c_2845,c_2842,c_3479,c_3565,c_3614,c_3658,
% 1.35/1.11                 c_3953,c_4119]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_4231,plain,
% 1.35/1.11      ( k1_funct_1(sK2,sK4) != k1_funct_1(sK2,sK4)
% 1.35/1.11      | r1_partfun1(sK2,sK3) != iProver_top ),
% 1.35/1.11      inference(demodulation,[status(thm)],[c_4228,c_1883]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(c_4233,plain,
% 1.35/1.11      ( r1_partfun1(sK2,sK3) != iProver_top ),
% 1.35/1.11      inference(equality_resolution_simp,[status(thm)],[c_4231]) ).
% 1.35/1.11  
% 1.35/1.11  cnf(contradiction,plain,
% 1.35/1.11      ( $false ),
% 1.35/1.11      inference(minisat,
% 1.35/1.11                [status(thm)],
% 1.35/1.11                [c_4233,c_4119,c_3953,c_3658,c_3617,c_3479,c_2842,c_2845,
% 1.35/1.11                 c_2325,c_2191,c_2105,c_2101,c_2099,c_2092,c_24,c_22]) ).
% 1.35/1.11  
% 1.35/1.11  
% 1.35/1.11  % SZS output end CNFRefutation for theBenchmark.p
% 1.35/1.11  
% 1.35/1.11  ------                               Statistics
% 1.35/1.11  
% 1.35/1.11  ------ General
% 1.35/1.11  
% 1.35/1.11  abstr_ref_over_cycles:                  0
% 1.35/1.11  abstr_ref_under_cycles:                 0
% 1.35/1.11  gc_basic_clause_elim:                   0
% 1.35/1.11  forced_gc_time:                         0
% 1.35/1.11  parsing_time:                           0.013
% 1.35/1.11  unif_index_cands_time:                  0.
% 1.35/1.11  unif_index_add_time:                    0.
% 1.35/1.11  orderings_time:                         0.
% 1.35/1.11  out_proof_time:                         0.012
% 1.35/1.11  total_time:                             0.137
% 1.35/1.11  num_of_symbols:                         50
% 1.35/1.11  num_of_terms:                           2340
% 1.35/1.11  
% 1.35/1.11  ------ Preprocessing
% 1.35/1.11  
% 1.35/1.11  num_of_splits:                          0
% 1.35/1.11  num_of_split_atoms:                     0
% 1.35/1.11  num_of_reused_defs:                     0
% 1.35/1.11  num_eq_ax_congr_red:                    8
% 1.35/1.11  num_of_sem_filtered_clauses:            1
% 1.35/1.11  num_of_subtypes:                        0
% 1.35/1.11  monotx_restored_types:                  0
% 1.35/1.11  sat_num_of_epr_types:                   0
% 1.35/1.11  sat_num_of_non_cyclic_types:            0
% 1.35/1.11  sat_guarded_non_collapsed_types:        0
% 1.35/1.11  num_pure_diseq_elim:                    0
% 1.35/1.11  simp_replaced_by:                       0
% 1.35/1.11  res_preprocessed:                       95
% 1.35/1.11  prep_upred:                             0
% 1.35/1.11  prep_unflattend:                        109
% 1.35/1.11  smt_new_axioms:                         0
% 1.35/1.11  pred_elim_cands:                        8
% 1.35/1.11  pred_elim:                              3
% 1.35/1.11  pred_elim_cl:                           -2
% 1.35/1.11  pred_elim_cycles:                       8
% 1.35/1.11  merged_defs:                            0
% 1.35/1.11  merged_defs_ncl:                        0
% 1.35/1.11  bin_hyper_res:                          0
% 1.35/1.11  prep_cycles:                            3
% 1.35/1.11  pred_elim_time:                         0.028
% 1.35/1.11  splitting_time:                         0.
% 1.35/1.11  sem_filter_time:                        0.
% 1.35/1.11  monotx_time:                            0.
% 1.35/1.11  subtype_inf_time:                       0.
% 1.35/1.11  
% 1.35/1.11  ------ Problem properties
% 1.35/1.11  
% 1.35/1.11  clauses:                                24
% 1.35/1.11  conjectures:                            5
% 1.35/1.11  epr:                                    2
% 1.35/1.11  horn:                                   16
% 1.35/1.11  ground:                                 10
% 1.35/1.11  unary:                                  2
% 1.35/1.11  binary:                                 8
% 1.35/1.11  lits:                                   84
% 1.35/1.11  lits_eq:                                53
% 1.35/1.11  fd_pure:                                0
% 1.35/1.11  fd_pseudo:                              0
% 1.35/1.11  fd_cond:                                0
% 1.35/1.11  fd_pseudo_cond:                         0
% 1.35/1.11  ac_symbols:                             0
% 1.35/1.11  
% 1.35/1.11  ------ Propositional Solver
% 1.35/1.11  
% 1.35/1.11  prop_solver_calls:                      23
% 1.35/1.11  prop_fast_solver_calls:                 1226
% 1.35/1.11  smt_solver_calls:                       0
% 1.35/1.11  smt_fast_solver_calls:                  0
% 1.35/1.11  prop_num_of_clauses:                    1009
% 1.35/1.11  prop_preprocess_simplified:             3254
% 1.35/1.11  prop_fo_subsumed:                       54
% 1.35/1.11  prop_solver_time:                       0.
% 1.35/1.11  smt_solver_time:                        0.
% 1.35/1.11  smt_fast_solver_time:                   0.
% 1.35/1.11  prop_fast_solver_time:                  0.
% 1.35/1.11  prop_unsat_core_time:                   0.
% 1.35/1.11  
% 1.35/1.11  ------ QBF
% 1.35/1.11  
% 1.35/1.11  qbf_q_res:                              0
% 1.35/1.11  qbf_num_tautologies:                    0
% 1.35/1.11  qbf_prep_cycles:                        0
% 1.35/1.11  
% 1.35/1.11  ------ BMC1
% 1.35/1.11  
% 1.35/1.11  bmc1_current_bound:                     -1
% 1.35/1.11  bmc1_last_solved_bound:                 -1
% 1.35/1.11  bmc1_unsat_core_size:                   -1
% 1.35/1.11  bmc1_unsat_core_parents_size:           -1
% 1.35/1.11  bmc1_merge_next_fun:                    0
% 1.35/1.11  bmc1_unsat_core_clauses_time:           0.
% 1.35/1.11  
% 1.35/1.11  ------ Instantiation
% 1.35/1.11  
% 1.35/1.11  inst_num_of_clauses:                    317
% 1.35/1.11  inst_num_in_passive:                    40
% 1.35/1.11  inst_num_in_active:                     234
% 1.35/1.11  inst_num_in_unprocessed:                43
% 1.35/1.11  inst_num_of_loops:                      310
% 1.35/1.11  inst_num_of_learning_restarts:          0
% 1.35/1.11  inst_num_moves_active_passive:          72
% 1.35/1.11  inst_lit_activity:                      0
% 1.35/1.11  inst_lit_activity_moves:                0
% 1.35/1.11  inst_num_tautologies:                   0
% 1.35/1.11  inst_num_prop_implied:                  0
% 1.35/1.11  inst_num_existing_simplified:           0
% 1.35/1.11  inst_num_eq_res_simplified:             0
% 1.35/1.11  inst_num_child_elim:                    0
% 1.35/1.11  inst_num_of_dismatching_blockings:      77
% 1.35/1.11  inst_num_of_non_proper_insts:           384
% 1.35/1.11  inst_num_of_duplicates:                 0
% 1.35/1.11  inst_inst_num_from_inst_to_res:         0
% 1.35/1.11  inst_dismatching_checking_time:         0.
% 1.35/1.11  
% 1.35/1.11  ------ Resolution
% 1.35/1.11  
% 1.35/1.11  res_num_of_clauses:                     0
% 1.35/1.11  res_num_in_passive:                     0
% 1.35/1.11  res_num_in_active:                      0
% 1.35/1.11  res_num_of_loops:                       98
% 1.35/1.11  res_forward_subset_subsumed:            48
% 1.35/1.11  res_backward_subset_subsumed:           2
% 1.35/1.11  res_forward_subsumed:                   4
% 1.35/1.11  res_backward_subsumed:                  0
% 1.35/1.11  res_forward_subsumption_resolution:     0
% 1.35/1.11  res_backward_subsumption_resolution:    0
% 1.35/1.11  res_clause_to_clause_subsumption:       150
% 1.35/1.11  res_orphan_elimination:                 0
% 1.35/1.11  res_tautology_del:                      80
% 1.35/1.11  res_num_eq_res_simplified:              2
% 1.35/1.11  res_num_sel_changes:                    0
% 1.35/1.11  res_moves_from_active_to_pass:          0
% 1.35/1.11  
% 1.35/1.11  ------ Superposition
% 1.35/1.11  
% 1.35/1.11  sup_time_total:                         0.
% 1.35/1.11  sup_time_generating:                    0.
% 1.35/1.11  sup_time_sim_full:                      0.
% 1.35/1.11  sup_time_sim_immed:                     0.
% 1.35/1.11  
% 1.35/1.11  sup_num_of_clauses:                     35
% 1.35/1.11  sup_num_in_active:                      28
% 1.35/1.11  sup_num_in_passive:                     7
% 1.35/1.11  sup_num_of_loops:                       61
% 1.35/1.11  sup_fw_superposition:                   19
% 1.35/1.11  sup_bw_superposition:                   15
% 1.35/1.11  sup_immediate_simplified:               13
% 1.35/1.11  sup_given_eliminated:                   0
% 1.35/1.11  comparisons_done:                       0
% 1.35/1.11  comparisons_avoided:                    24
% 1.35/1.11  
% 1.35/1.11  ------ Simplifications
% 1.35/1.11  
% 1.35/1.11  
% 1.35/1.11  sim_fw_subset_subsumed:                 1
% 1.35/1.11  sim_bw_subset_subsumed:                 9
% 1.35/1.11  sim_fw_subsumed:                        2
% 1.35/1.11  sim_bw_subsumed:                        0
% 1.35/1.11  sim_fw_subsumption_res:                 1
% 1.35/1.11  sim_bw_subsumption_res:                 0
% 1.35/1.11  sim_tautology_del:                      6
% 1.35/1.11  sim_eq_tautology_del:                   11
% 1.35/1.11  sim_eq_res_simp:                        5
% 1.35/1.11  sim_fw_demodulated:                     4
% 1.35/1.11  sim_bw_demodulated:                     27
% 1.35/1.11  sim_light_normalised:                   8
% 1.35/1.11  sim_joinable_taut:                      0
% 1.35/1.11  sim_joinable_simp:                      0
% 1.35/1.11  sim_ac_normalised:                      0
% 1.35/1.11  sim_smt_subsumption:                    0
% 1.35/1.11  
%------------------------------------------------------------------------------
