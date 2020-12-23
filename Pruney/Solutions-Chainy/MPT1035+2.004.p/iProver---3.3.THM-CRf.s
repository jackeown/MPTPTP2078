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
% DateTime   : Thu Dec  3 12:08:39 EST 2020

% Result     : Theorem 2.93s
% Output     : CNFRefutation 2.93s
% Verified   : 
% Statistics : Number of formulae       :  220 (99559 expanded)
%              Number of clauses        :  168 (29458 expanded)
%              Number of leaves         :   15 (22594 expanded)
%              Depth                    :   46
%              Number of atoms          :  889 (805452 expanded)
%              Number of equality atoms :  500 (272870 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f10])).

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
    inference(nnf_transformation,[],[f17])).

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

fof(f42,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f20,plain,(
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

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( ( k1_xboole_0 = X1
             => k1_xboole_0 = X0 )
           => ( r1_partfun1(X2,X3)
            <=> ! [X4] :
                  ( r2_hidden(X4,k1_relset_1(X0,X1,X2))
                 => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
           => ( ( k1_xboole_0 = X1
               => k1_xboole_0 = X0 )
             => ( r1_partfun1(X2,X3)
              <=> ! [X4] :
                    ( r2_hidden(X4,k1_relset_1(X0,X1,X2))
                   => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( r1_partfun1(X2,X3)
          <~> ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2)) ) )
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( r1_partfun1(X2,X3)
          <~> ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2)) ) )
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ? [X4] :
                ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
                & r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
            | ~ r1_partfun1(X2,X3) )
          & ( ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
            | r1_partfun1(X2,X3) )
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ? [X4] :
                ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
                & r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
            | ~ r1_partfun1(X2,X3) )
          & ( ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
            | r1_partfun1(X2,X3) )
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ? [X4] :
                ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
                & r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
            | ~ r1_partfun1(X2,X3) )
          & ( ! [X5] :
                ( k1_funct_1(X2,X5) = k1_funct_1(X3,X5)
                | ~ r2_hidden(X5,k1_relset_1(X0,X1,X2)) )
            | r1_partfun1(X2,X3) )
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(rectify,[],[f26])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
          & r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
     => ( k1_funct_1(X2,sK5) != k1_funct_1(X3,sK5)
        & r2_hidden(sK5,k1_relset_1(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ? [X4] :
                ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
                & r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
            | ~ r1_partfun1(X2,X3) )
          & ( ! [X5] :
                ( k1_funct_1(X2,X5) = k1_funct_1(X3,X5)
                | ~ r2_hidden(X5,k1_relset_1(X0,X1,X2)) )
            | r1_partfun1(X2,X3) )
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
     => ( ( ? [X4] :
              ( k1_funct_1(sK4,X4) != k1_funct_1(X2,X4)
              & r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
          | ~ r1_partfun1(X2,sK4) )
        & ( ! [X5] :
              ( k1_funct_1(sK4,X5) = k1_funct_1(X2,X5)
              | ~ r2_hidden(X5,k1_relset_1(X0,X1,X2)) )
          | r1_partfun1(X2,sK4) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(sK4,X0,X1)
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ( ? [X4] :
                  ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
                  & r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
              | ~ r1_partfun1(X2,X3) )
            & ( ! [X5] :
                  ( k1_funct_1(X2,X5) = k1_funct_1(X3,X5)
                  | ~ r2_hidden(X5,k1_relset_1(X0,X1,X2)) )
              | r1_partfun1(X2,X3) )
            & ( k1_xboole_0 = X0
              | k1_xboole_0 != X1 )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ( ? [X4] :
                ( k1_funct_1(sK3,X4) != k1_funct_1(X3,X4)
                & r2_hidden(X4,k1_relset_1(sK1,sK2,sK3)) )
            | ~ r1_partfun1(sK3,X3) )
          & ( ! [X5] :
                ( k1_funct_1(sK3,X5) = k1_funct_1(X3,X5)
                | ~ r2_hidden(X5,k1_relset_1(sK1,sK2,sK3)) )
            | r1_partfun1(sK3,X3) )
          & ( k1_xboole_0 = sK1
            | k1_xboole_0 != sK2 )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
          & v1_funct_2(X3,sK1,sK2)
          & v1_funct_1(X3) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ( ( k1_funct_1(sK3,sK5) != k1_funct_1(sK4,sK5)
        & r2_hidden(sK5,k1_relset_1(sK1,sK2,sK3)) )
      | ~ r1_partfun1(sK3,sK4) )
    & ( ! [X5] :
          ( k1_funct_1(sK3,X5) = k1_funct_1(sK4,X5)
          | ~ r2_hidden(X5,k1_relset_1(sK1,sK2,sK3)) )
      | r1_partfun1(sK3,sK4) )
    & ( k1_xboole_0 = sK1
      | k1_xboole_0 != sK2 )
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK4,sK1,sK2)
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f27,f30,f29,f28])).

fof(f48,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f49,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f31])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_partfun1(X0,X1)
      | r2_hidden(sK0(X0,X1),k1_relat_1(X0))
      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f47,plain,(
    v1_funct_1(sK4) ),
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

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f46,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f31])).

fof(f51,plain,(
    ! [X5] :
      ( k1_funct_1(sK3,X5) = k1_funct_1(sK4,X5)
      | ~ r2_hidden(X5,k1_relset_1(sK1,sK2,sK3))
      | r1_partfun1(sK3,sK4) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f45,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f52,plain,
    ( r2_hidden(sK5,k1_relset_1(sK1,sK2,sK3))
    | ~ r1_partfun1(sK3,sK4) ),
    inference(cnf_transformation,[],[f31])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_partfun1(X0,X1)
      | k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1))
      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f53,plain,
    ( k1_funct_1(sK3,sK5) != k1_funct_1(sK4,sK5)
    | ~ r1_partfun1(sK3,sK4) ),
    inference(cnf_transformation,[],[f31])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f58,plain,(
    ! [X2,X1] :
      ( k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f37])).

fof(f50,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f31])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f56,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f40])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r1_partfun1(X1,X2)
    | ~ r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X2,X0) = k1_funct_1(X1,X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_291,plain,
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
    inference(resolution_lifted,[status(thm)],[c_0,c_12])).

cnf(c_292,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r1_partfun1(X1,X2)
    | ~ m1_subset_1(k1_relat_1(X1),k1_zfmisc_1(k1_relat_1(X2)))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X1,X0) = k1_funct_1(X2,X0) ),
    inference(unflattening,[status(thm)],[c_291])).

cnf(c_1294,plain,
    ( ~ r2_hidden(X0_49,k1_relat_1(X0_47))
    | ~ r1_partfun1(X0_47,X1_47)
    | ~ m1_subset_1(k1_relat_1(X0_47),k1_zfmisc_1(k1_relat_1(X1_47)))
    | ~ v1_funct_1(X1_47)
    | ~ v1_funct_1(X0_47)
    | ~ v1_relat_1(X1_47)
    | ~ v1_relat_1(X0_47)
    | k1_funct_1(X0_47,X0_49) = k1_funct_1(X1_47,X0_49) ),
    inference(subtyping,[status(esa)],[c_292])).

cnf(c_5264,plain,
    ( ~ r2_hidden(sK5,k1_relat_1(sK3))
    | ~ r1_partfun1(sK3,sK4)
    | ~ m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(k1_relat_1(sK4)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK4)
    | ~ v1_relat_1(sK3)
    | k1_funct_1(sK3,sK5) = k1_funct_1(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_1294])).

cnf(c_9,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_18,negated_conjecture,
    ( v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_523,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK2 != X2
    | sK1 != X1
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_18])).

cnf(c_524,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_523])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_526,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_524,c_17])).

cnf(c_1291,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(subtyping,[status(esa)],[c_526])).

cnf(c_1300,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1622,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1300])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1305,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
    | k1_relset_1(X1_47,X2_47,X0_47) = k1_relat_1(X0_47) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1618,plain,
    ( k1_relset_1(X0_47,X1_47,X2_47) = k1_relat_1(X2_47)
    | m1_subset_1(X2_47,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1305])).

cnf(c_1925,plain,
    ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1622,c_1618])).

cnf(c_2144,plain,
    ( k1_relat_1(sK4) = sK1
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1291,c_1925])).

cnf(c_11,plain,
    ( r2_hidden(sK0(X0,X1),k1_relat_1(X0))
    | r1_partfun1(X0,X1)
    | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_237,plain,
    ( r2_hidden(sK0(X0,X1),k1_relat_1(X0))
    | r1_partfun1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k1_relat_1(X1) != X3
    | k1_relat_1(X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_11])).

cnf(c_238,plain,
    ( r2_hidden(sK0(X0,X1),k1_relat_1(X0))
    | r1_partfun1(X0,X1)
    | ~ m1_subset_1(k1_relat_1(X0),k1_zfmisc_1(k1_relat_1(X1)))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_237])).

cnf(c_1296,plain,
    ( r2_hidden(sK0(X0_47,X1_47),k1_relat_1(X0_47))
    | r1_partfun1(X0_47,X1_47)
    | ~ m1_subset_1(k1_relat_1(X0_47),k1_zfmisc_1(k1_relat_1(X1_47)))
    | ~ v1_funct_1(X1_47)
    | ~ v1_funct_1(X0_47)
    | ~ v1_relat_1(X1_47)
    | ~ v1_relat_1(X0_47) ),
    inference(subtyping,[status(esa)],[c_238])).

cnf(c_1626,plain,
    ( r2_hidden(sK0(X0_47,X1_47),k1_relat_1(X0_47)) = iProver_top
    | r1_partfun1(X0_47,X1_47) = iProver_top
    | m1_subset_1(k1_relat_1(X0_47),k1_zfmisc_1(k1_relat_1(X1_47))) != iProver_top
    | v1_funct_1(X0_47) != iProver_top
    | v1_funct_1(X1_47) != iProver_top
    | v1_relat_1(X0_47) != iProver_top
    | v1_relat_1(X1_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1296])).

cnf(c_2312,plain,
    ( sK2 = k1_xboole_0
    | r2_hidden(sK0(X0_47,sK4),k1_relat_1(X0_47)) = iProver_top
    | r1_partfun1(X0_47,sK4) = iProver_top
    | m1_subset_1(k1_relat_1(X0_47),k1_zfmisc_1(sK1)) != iProver_top
    | v1_funct_1(X0_47) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(X0_47) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2144,c_1626])).

cnf(c_19,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_24,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_26,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1307,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
    | v1_relat_1(X0_47) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1769,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1307])).

cnf(c_1770,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1769])).

cnf(c_2596,plain,
    ( v1_relat_1(X0_47) != iProver_top
    | sK2 = k1_xboole_0
    | r2_hidden(sK0(X0_47,sK4),k1_relat_1(X0_47)) = iProver_top
    | r1_partfun1(X0_47,sK4) = iProver_top
    | m1_subset_1(k1_relat_1(X0_47),k1_zfmisc_1(sK1)) != iProver_top
    | v1_funct_1(X0_47) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2312,c_24,c_26,c_1770])).

cnf(c_2597,plain,
    ( sK2 = k1_xboole_0
    | r2_hidden(sK0(X0_47,sK4),k1_relat_1(X0_47)) = iProver_top
    | r1_partfun1(X0_47,sK4) = iProver_top
    | m1_subset_1(k1_relat_1(X0_47),k1_zfmisc_1(sK1)) != iProver_top
    | v1_funct_1(X0_47) != iProver_top
    | v1_relat_1(X0_47) != iProver_top ),
    inference(renaming,[status(thm)],[c_2596])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1298,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1624,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1298])).

cnf(c_1926,plain,
    ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1624,c_1618])).

cnf(c_15,negated_conjecture,
    ( ~ r2_hidden(X0,k1_relset_1(sK1,sK2,sK3))
    | r1_partfun1(sK3,sK4)
    | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1302,negated_conjecture,
    ( ~ r2_hidden(X0_49,k1_relset_1(sK1,sK2,sK3))
    | r1_partfun1(sK3,sK4)
    | k1_funct_1(sK3,X0_49) = k1_funct_1(sK4,X0_49) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1621,plain,
    ( k1_funct_1(sK3,X0_49) = k1_funct_1(sK4,X0_49)
    | r2_hidden(X0_49,k1_relset_1(sK1,sK2,sK3)) != iProver_top
    | r1_partfun1(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1302])).

cnf(c_2157,plain,
    ( k1_funct_1(sK4,X0_49) = k1_funct_1(sK3,X0_49)
    | r2_hidden(X0_49,k1_relat_1(sK3)) != iProver_top
    | r1_partfun1(sK3,sK4) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1926,c_1621])).

cnf(c_2609,plain,
    ( k1_funct_1(sK3,sK0(sK3,sK4)) = k1_funct_1(sK4,sK0(sK3,sK4))
    | sK2 = k1_xboole_0
    | r1_partfun1(sK3,sK4) = iProver_top
    | m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK1)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2597,c_2157])).

cnf(c_21,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_22,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_23,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1772,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1307])).

cnf(c_1773,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1772])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1306,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
    | m1_subset_1(k1_relset_1(X1_47,X2_47,X0_47),k1_zfmisc_1(X1_47)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1617,plain,
    ( m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47))) != iProver_top
    | m1_subset_1(k1_relset_1(X1_47,X2_47,X0_47),k1_zfmisc_1(X1_47)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1306])).

cnf(c_2173,plain,
    ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK1)) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1926,c_1617])).

cnf(c_2686,plain,
    ( r1_partfun1(sK3,sK4) = iProver_top
    | sK2 = k1_xboole_0
    | k1_funct_1(sK3,sK0(sK3,sK4)) = k1_funct_1(sK4,sK0(sK3,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2609,c_22,c_23,c_1773,c_2173])).

cnf(c_2687,plain,
    ( k1_funct_1(sK3,sK0(sK3,sK4)) = k1_funct_1(sK4,sK0(sK3,sK4))
    | sK2 = k1_xboole_0
    | r1_partfun1(sK3,sK4) = iProver_top ),
    inference(renaming,[status(thm)],[c_2686])).

cnf(c_14,negated_conjecture,
    ( r2_hidden(sK5,k1_relset_1(sK1,sK2,sK3))
    | ~ r1_partfun1(sK3,sK4) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1303,negated_conjecture,
    ( r2_hidden(sK5,k1_relset_1(sK1,sK2,sK3))
    | ~ r1_partfun1(sK3,sK4) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1620,plain,
    ( r2_hidden(sK5,k1_relset_1(sK1,sK2,sK3)) = iProver_top
    | r1_partfun1(sK3,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1303])).

cnf(c_2158,plain,
    ( r2_hidden(sK5,k1_relat_1(sK3)) = iProver_top
    | r1_partfun1(sK3,sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1926,c_1620])).

cnf(c_2381,plain,
    ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2173,c_23])).

cnf(c_1628,plain,
    ( k1_funct_1(X0_47,X0_49) = k1_funct_1(X1_47,X0_49)
    | r2_hidden(X0_49,k1_relat_1(X0_47)) != iProver_top
    | r1_partfun1(X0_47,X1_47) != iProver_top
    | m1_subset_1(k1_relat_1(X0_47),k1_zfmisc_1(k1_relat_1(X1_47))) != iProver_top
    | v1_funct_1(X0_47) != iProver_top
    | v1_funct_1(X1_47) != iProver_top
    | v1_relat_1(X0_47) != iProver_top
    | v1_relat_1(X1_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1294])).

cnf(c_2963,plain,
    ( k1_funct_1(X0_47,X0_49) = k1_funct_1(sK4,X0_49)
    | sK2 = k1_xboole_0
    | r2_hidden(X0_49,k1_relat_1(X0_47)) != iProver_top
    | r1_partfun1(X0_47,sK4) != iProver_top
    | m1_subset_1(k1_relat_1(X0_47),k1_zfmisc_1(sK1)) != iProver_top
    | v1_funct_1(X0_47) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(X0_47) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2144,c_1628])).

cnf(c_3065,plain,
    ( v1_relat_1(X0_47) != iProver_top
    | k1_funct_1(X0_47,X0_49) = k1_funct_1(sK4,X0_49)
    | sK2 = k1_xboole_0
    | r2_hidden(X0_49,k1_relat_1(X0_47)) != iProver_top
    | r1_partfun1(X0_47,sK4) != iProver_top
    | m1_subset_1(k1_relat_1(X0_47),k1_zfmisc_1(sK1)) != iProver_top
    | v1_funct_1(X0_47) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2963,c_24,c_26,c_1770])).

cnf(c_3066,plain,
    ( k1_funct_1(X0_47,X0_49) = k1_funct_1(sK4,X0_49)
    | sK2 = k1_xboole_0
    | r2_hidden(X0_49,k1_relat_1(X0_47)) != iProver_top
    | r1_partfun1(X0_47,sK4) != iProver_top
    | m1_subset_1(k1_relat_1(X0_47),k1_zfmisc_1(sK1)) != iProver_top
    | v1_funct_1(X0_47) != iProver_top
    | v1_relat_1(X0_47) != iProver_top ),
    inference(renaming,[status(thm)],[c_3065])).

cnf(c_3079,plain,
    ( k1_funct_1(sK4,X0_49) = k1_funct_1(sK3,X0_49)
    | sK2 = k1_xboole_0
    | r2_hidden(X0_49,k1_relat_1(sK3)) != iProver_top
    | r1_partfun1(sK3,sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2381,c_3066])).

cnf(c_3097,plain,
    ( r2_hidden(X0_49,k1_relat_1(sK3)) != iProver_top
    | sK2 = k1_xboole_0
    | k1_funct_1(sK4,X0_49) = k1_funct_1(sK3,X0_49) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3079,c_22,c_23,c_1773,c_2157])).

cnf(c_3098,plain,
    ( k1_funct_1(sK4,X0_49) = k1_funct_1(sK3,X0_49)
    | sK2 = k1_xboole_0
    | r2_hidden(X0_49,k1_relat_1(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3097])).

cnf(c_3107,plain,
    ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
    | sK2 = k1_xboole_0
    | r1_partfun1(sK3,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2158,c_3098])).

cnf(c_3188,plain,
    ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
    | k1_funct_1(sK3,sK0(sK3,sK4)) = k1_funct_1(sK4,sK0(sK3,sK4))
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2687,c_3107])).

cnf(c_10,plain,
    ( r1_partfun1(X0,X1)
    | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k1_funct_1(X1,sK0(X0,X1)) != k1_funct_1(X0,sK0(X0,X1)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_264,plain,
    ( r1_partfun1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1))
    | k1_relat_1(X1) != X3
    | k1_relat_1(X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_10])).

cnf(c_265,plain,
    ( r1_partfun1(X0,X1)
    | ~ m1_subset_1(k1_relat_1(X0),k1_zfmisc_1(k1_relat_1(X1)))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_264])).

cnf(c_1295,plain,
    ( r1_partfun1(X0_47,X1_47)
    | ~ m1_subset_1(k1_relat_1(X0_47),k1_zfmisc_1(k1_relat_1(X1_47)))
    | ~ v1_funct_1(X1_47)
    | ~ v1_funct_1(X0_47)
    | ~ v1_relat_1(X1_47)
    | ~ v1_relat_1(X0_47)
    | k1_funct_1(X0_47,sK0(X0_47,X1_47)) != k1_funct_1(X1_47,sK0(X0_47,X1_47)) ),
    inference(subtyping,[status(esa)],[c_265])).

cnf(c_1627,plain,
    ( k1_funct_1(X0_47,sK0(X0_47,X1_47)) != k1_funct_1(X1_47,sK0(X0_47,X1_47))
    | r1_partfun1(X0_47,X1_47) = iProver_top
    | m1_subset_1(k1_relat_1(X0_47),k1_zfmisc_1(k1_relat_1(X1_47))) != iProver_top
    | v1_funct_1(X0_47) != iProver_top
    | v1_funct_1(X1_47) != iProver_top
    | v1_relat_1(X0_47) != iProver_top
    | v1_relat_1(X1_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1295])).

cnf(c_3363,plain,
    ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
    | sK2 = k1_xboole_0
    | r1_partfun1(sK3,sK4) = iProver_top
    | m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(k1_relat_1(sK4))) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3188,c_1627])).

cnf(c_1827,plain,
    ( r1_partfun1(X0_47,sK4)
    | ~ m1_subset_1(k1_relat_1(X0_47),k1_zfmisc_1(k1_relat_1(sK4)))
    | ~ v1_funct_1(X0_47)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(X0_47)
    | ~ v1_relat_1(sK4)
    | k1_funct_1(X0_47,sK0(X0_47,sK4)) != k1_funct_1(sK4,sK0(X0_47,sK4)) ),
    inference(instantiation,[status(thm)],[c_1295])).

cnf(c_1887,plain,
    ( r1_partfun1(sK3,sK4)
    | ~ m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(k1_relat_1(sK4)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK4)
    | ~ v1_relat_1(sK3)
    | k1_funct_1(sK3,sK0(sK3,sK4)) != k1_funct_1(sK4,sK0(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_1827])).

cnf(c_1888,plain,
    ( k1_funct_1(sK3,sK0(sK3,sK4)) != k1_funct_1(sK4,sK0(sK3,sK4))
    | r1_partfun1(sK3,sK4) = iProver_top
    | m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(k1_relat_1(sK4))) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1887])).

cnf(c_3366,plain,
    ( sK2 = k1_xboole_0
    | r1_partfun1(sK3,sK4) = iProver_top
    | m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(k1_relat_1(sK4))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3363,c_22,c_23,c_24,c_26,c_1770,c_1773,c_1888,c_2173,c_2609])).

cnf(c_3373,plain,
    ( sK2 = k1_xboole_0
    | r1_partfun1(sK3,sK4) = iProver_top
    | m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2144,c_3366])).

cnf(c_3459,plain,
    ( r1_partfun1(sK3,sK4) = iProver_top
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3373,c_23,c_2173])).

cnf(c_3460,plain,
    ( sK2 = k1_xboole_0
    | r1_partfun1(sK3,sK4) = iProver_top ),
    inference(renaming,[status(thm)],[c_3459])).

cnf(c_3465,plain,
    ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3460,c_3107])).

cnf(c_13,negated_conjecture,
    ( ~ r1_partfun1(sK3,sK4)
    | k1_funct_1(sK3,sK5) != k1_funct_1(sK4,sK5) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1304,negated_conjecture,
    ( ~ r1_partfun1(sK3,sK4)
    | k1_funct_1(sK3,sK5) != k1_funct_1(sK4,sK5) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1619,plain,
    ( k1_funct_1(sK3,sK5) != k1_funct_1(sK4,sK5)
    | r1_partfun1(sK3,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1304])).

cnf(c_3468,plain,
    ( sK2 = k1_xboole_0
    | r1_partfun1(sK3,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3465,c_1619])).

cnf(c_3489,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3468,c_23,c_2173,c_3373])).

cnf(c_8,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_510,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | sK2 != X1
    | sK1 != k1_xboole_0
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_18])).

cnf(c_511,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_510])).

cnf(c_1292,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_511])).

cnf(c_1630,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1292])).

cnf(c_3497,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3489,c_1630])).

cnf(c_16,negated_conjecture,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1301,negated_conjecture,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 = sK1 ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_3503,plain,
    ( sK1 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3489,c_1301])).

cnf(c_3504,plain,
    ( sK1 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_3503])).

cnf(c_3519,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3497,c_3504])).

cnf(c_3520,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3519])).

cnf(c_3499,plain,
    ( k1_relset_1(sK1,k1_xboole_0,sK4) = k1_relat_1(sK4) ),
    inference(demodulation,[status(thm)],[c_3489,c_1925])).

cnf(c_3513,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_relat_1(sK4) ),
    inference(light_normalisation,[status(thm)],[c_3499,c_3504])).

cnf(c_3521,plain,
    ( k1_relat_1(sK4) = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3520,c_3513])).

cnf(c_3502,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3489,c_1622])).

cnf(c_3507,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3502,c_3504])).

cnf(c_3524,plain,
    ( k1_relat_1(sK4) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3521,c_3507])).

cnf(c_4293,plain,
    ( r2_hidden(sK0(X0_47,sK4),k1_relat_1(X0_47)) = iProver_top
    | r1_partfun1(X0_47,sK4) = iProver_top
    | m1_subset_1(k1_relat_1(X0_47),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(X0_47) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(X0_47) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3524,c_1626])).

cnf(c_5119,plain,
    ( v1_relat_1(X0_47) != iProver_top
    | r2_hidden(sK0(X0_47,sK4),k1_relat_1(X0_47)) = iProver_top
    | r1_partfun1(X0_47,sK4) = iProver_top
    | m1_subset_1(k1_relat_1(X0_47),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(X0_47) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4293,c_24,c_26,c_1770])).

cnf(c_5120,plain,
    ( r2_hidden(sK0(X0_47,sK4),k1_relat_1(X0_47)) = iProver_top
    | r1_partfun1(X0_47,sK4) = iProver_top
    | m1_subset_1(k1_relat_1(X0_47),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(X0_47) != iProver_top
    | v1_relat_1(X0_47) != iProver_top ),
    inference(renaming,[status(thm)],[c_5119])).

cnf(c_3533,plain,
    ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3504,c_2381])).

cnf(c_4292,plain,
    ( k1_funct_1(X0_47,X0_49) = k1_funct_1(sK4,X0_49)
    | r2_hidden(X0_49,k1_relat_1(X0_47)) != iProver_top
    | r1_partfun1(X0_47,sK4) != iProver_top
    | m1_subset_1(k1_relat_1(X0_47),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(X0_47) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(X0_47) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3524,c_1628])).

cnf(c_4992,plain,
    ( v1_relat_1(X0_47) != iProver_top
    | k1_funct_1(X0_47,X0_49) = k1_funct_1(sK4,X0_49)
    | r2_hidden(X0_49,k1_relat_1(X0_47)) != iProver_top
    | r1_partfun1(X0_47,sK4) != iProver_top
    | m1_subset_1(k1_relat_1(X0_47),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(X0_47) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4292,c_24,c_26,c_1770])).

cnf(c_4993,plain,
    ( k1_funct_1(X0_47,X0_49) = k1_funct_1(sK4,X0_49)
    | r2_hidden(X0_49,k1_relat_1(X0_47)) != iProver_top
    | r1_partfun1(X0_47,sK4) != iProver_top
    | m1_subset_1(k1_relat_1(X0_47),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(X0_47) != iProver_top
    | v1_relat_1(X0_47) != iProver_top ),
    inference(renaming,[status(thm)],[c_4992])).

cnf(c_5004,plain,
    ( k1_funct_1(sK4,X0_49) = k1_funct_1(sK3,X0_49)
    | r2_hidden(X0_49,k1_relat_1(sK3)) != iProver_top
    | r1_partfun1(sK3,sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3533,c_4993])).

cnf(c_5020,plain,
    ( r2_hidden(X0_49,k1_relat_1(sK3)) != iProver_top
    | k1_funct_1(sK4,X0_49) = k1_funct_1(sK3,X0_49) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5004,c_22,c_23,c_1773,c_2157])).

cnf(c_5021,plain,
    ( k1_funct_1(sK4,X0_49) = k1_funct_1(sK3,X0_49)
    | r2_hidden(X0_49,k1_relat_1(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5020])).

cnf(c_5131,plain,
    ( k1_funct_1(sK3,sK0(sK3,sK4)) = k1_funct_1(sK4,sK0(sK3,sK4))
    | r1_partfun1(sK3,sK4) = iProver_top
    | m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5120,c_5021])).

cnf(c_1790,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1305])).

cnf(c_1793,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1305])).

cnf(c_1799,plain,
    ( m1_subset_1(k1_relset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_1306])).

cnf(c_1800,plain,
    ( m1_subset_1(k1_relset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1)) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1799])).

cnf(c_1313,plain,
    ( X0_47 != X1_47
    | X2_47 != X1_47
    | X2_47 = X0_47 ),
    theory(equality)).

cnf(c_1785,plain,
    ( sK1 != X0_47
    | sK1 = k1_xboole_0
    | k1_xboole_0 != X0_47 ),
    inference(instantiation,[status(thm)],[c_1313])).

cnf(c_1896,plain,
    ( sK1 != sK1
    | sK1 = k1_xboole_0
    | k1_xboole_0 != sK1 ),
    inference(instantiation,[status(thm)],[c_1785])).

cnf(c_1309,plain,
    ( X0_47 = X0_47 ),
    theory(equality)).

cnf(c_1897,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_1309])).

cnf(c_1315,plain,
    ( k1_zfmisc_1(X0_47) = k1_zfmisc_1(X1_47)
    | X0_47 != X1_47 ),
    theory(equality)).

cnf(c_1953,plain,
    ( k1_zfmisc_1(X0_47) = k1_zfmisc_1(sK1)
    | X0_47 != sK1 ),
    inference(instantiation,[status(thm)],[c_1315])).

cnf(c_1958,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(sK1)
    | k1_xboole_0 != sK1 ),
    inference(instantiation,[status(thm)],[c_1953])).

cnf(c_1898,plain,
    ( X0_47 != X1_47
    | sK1 != X1_47
    | sK1 = X0_47 ),
    inference(instantiation,[status(thm)],[c_1313])).

cnf(c_2191,plain,
    ( k1_relset_1(sK1,sK2,sK4) != X0_47
    | sK1 != X0_47
    | sK1 = k1_relset_1(sK1,sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_1898])).

cnf(c_2378,plain,
    ( k1_relset_1(sK1,sK2,sK4) != k1_relat_1(sK4)
    | sK1 = k1_relset_1(sK1,sK2,sK4)
    | sK1 != k1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2191])).

cnf(c_2400,plain,
    ( k1_relat_1(sK4) != X0_47
    | sK1 != X0_47
    | sK1 = k1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1898])).

cnf(c_2401,plain,
    ( k1_relat_1(sK4) != k1_xboole_0
    | sK1 = k1_relat_1(sK4)
    | sK1 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2400])).

cnf(c_5,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_490,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | sK2 != k1_xboole_0
    | sK1 != X1
    | sK4 != X0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_18])).

cnf(c_491,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | sK2 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_490])).

cnf(c_1293,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | sK2 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK4 ),
    inference(subtyping,[status(esa)],[c_491])).

cnf(c_1629,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK4
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1293])).

cnf(c_1332,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1309])).

cnf(c_2298,plain,
    ( sK2 != X0_47
    | k1_xboole_0 != X0_47
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_1313])).

cnf(c_2299,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2298])).

cnf(c_2421,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1629,c_1332,c_1301,c_2299])).

cnf(c_2181,plain,
    ( X0_47 != X1_47
    | X0_47 = k1_relset_1(sK1,sK2,sK4)
    | k1_relset_1(sK1,sK2,sK4) != X1_47 ),
    inference(instantiation,[status(thm)],[c_1313])).

cnf(c_2554,plain,
    ( X0_47 = k1_relset_1(sK1,sK2,sK4)
    | X0_47 != k1_relat_1(sK4)
    | k1_relset_1(sK1,sK2,sK4) != k1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2181])).

cnf(c_2702,plain,
    ( k1_relset_1(sK1,sK2,sK4) != k1_relat_1(sK4)
    | k1_relat_1(sK4) = k1_relset_1(sK1,sK2,sK4)
    | k1_relat_1(sK4) != k1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2554])).

cnf(c_2703,plain,
    ( k1_relat_1(sK4) = k1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1309])).

cnf(c_2253,plain,
    ( X0_47 != X1_47
    | X0_47 = k1_relset_1(sK1,sK2,sK3)
    | k1_relset_1(sK1,sK2,sK3) != X1_47 ),
    inference(instantiation,[status(thm)],[c_1313])).

cnf(c_2583,plain,
    ( X0_47 = k1_relset_1(sK1,sK2,sK3)
    | X0_47 != k1_relat_1(sK3)
    | k1_relset_1(sK1,sK2,sK3) != k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2253])).

cnf(c_2709,plain,
    ( k1_relset_1(sK1,sK2,sK3) != k1_relat_1(sK3)
    | k1_relat_1(sK3) = k1_relset_1(sK1,sK2,sK3)
    | k1_relat_1(sK3) != k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2583])).

cnf(c_2710,plain,
    ( k1_relat_1(sK3) = k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1309])).

cnf(c_1316,plain,
    ( ~ m1_subset_1(X0_47,X0_48)
    | m1_subset_1(X1_47,X1_48)
    | X1_48 != X0_48
    | X1_47 != X0_47 ),
    theory(equality)).

cnf(c_1842,plain,
    ( m1_subset_1(X0_47,X0_48)
    | ~ m1_subset_1(k1_relset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1))
    | X0_48 != k1_zfmisc_1(sK1)
    | X0_47 != k1_relset_1(sK1,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1316])).

cnf(c_2137,plain,
    ( m1_subset_1(X0_47,k1_zfmisc_1(X1_47))
    | ~ m1_subset_1(k1_relset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1))
    | k1_zfmisc_1(X1_47) != k1_zfmisc_1(sK1)
    | X0_47 != k1_relset_1(sK1,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1842])).

cnf(c_3138,plain,
    ( ~ m1_subset_1(k1_relset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1))
    | m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(X0_47))
    | k1_zfmisc_1(X0_47) != k1_zfmisc_1(sK1)
    | k1_relat_1(sK3) != k1_relset_1(sK1,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_2137])).

cnf(c_3142,plain,
    ( k1_zfmisc_1(X0_47) != k1_zfmisc_1(sK1)
    | k1_relat_1(sK3) != k1_relset_1(sK1,sK2,sK3)
    | m1_subset_1(k1_relset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(X0_47)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3138])).

cnf(c_3144,plain,
    ( k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(sK1)
    | k1_relat_1(sK3) != k1_relset_1(sK1,sK2,sK3)
    | m1_subset_1(k1_relset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3142])).

cnf(c_2294,plain,
    ( X0_47 != X1_47
    | X0_47 = sK1
    | sK1 != X1_47 ),
    inference(instantiation,[status(thm)],[c_1313])).

cnf(c_2834,plain,
    ( X0_47 != k1_relset_1(sK1,sK2,sK4)
    | X0_47 = sK1
    | sK1 != k1_relset_1(sK1,sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_2294])).

cnf(c_3233,plain,
    ( k1_relat_1(sK4) != k1_relset_1(sK1,sK2,sK4)
    | k1_relat_1(sK4) = sK1
    | sK1 != k1_relset_1(sK1,sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_2834])).

cnf(c_4032,plain,
    ( ~ m1_subset_1(k1_relset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1))
    | m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(k1_relat_1(sK4)))
    | k1_zfmisc_1(k1_relat_1(sK4)) != k1_zfmisc_1(sK1)
    | k1_relat_1(sK3) != k1_relset_1(sK1,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_3138])).

cnf(c_4033,plain,
    ( k1_zfmisc_1(k1_relat_1(sK4)) != k1_zfmisc_1(sK1)
    | k1_relat_1(sK3) != k1_relset_1(sK1,sK2,sK3)
    | m1_subset_1(k1_relset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(k1_relat_1(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4032])).

cnf(c_4705,plain,
    ( k1_zfmisc_1(k1_relat_1(sK4)) = k1_zfmisc_1(sK1)
    | k1_relat_1(sK4) != sK1 ),
    inference(instantiation,[status(thm)],[c_1953])).

cnf(c_5144,plain,
    ( r1_partfun1(sK3,sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5131,c_22,c_20,c_23,c_24,c_17,c_26,c_1770,c_1773,c_1790,c_1793,c_1800,c_1888,c_1896,c_1897,c_1958,c_2173,c_2378,c_2401,c_2421,c_2702,c_2703,c_2709,c_2710,c_3144,c_3233,c_3373,c_3468,c_3524,c_4033,c_4705])).

cnf(c_5146,plain,
    ( r1_partfun1(sK3,sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5144])).

cnf(c_2172,plain,
    ( r2_hidden(sK5,k1_relat_1(sK3))
    | ~ r1_partfun1(sK3,sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2158])).

cnf(c_1341,plain,
    ( k1_funct_1(sK3,sK5) != k1_funct_1(sK4,sK5)
    | r1_partfun1(sK3,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1304])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5264,c_5146,c_5144,c_4705,c_4032,c_3524,c_3489,c_3233,c_2710,c_2709,c_2703,c_2702,c_2421,c_2401,c_2378,c_2172,c_1897,c_1896,c_1799,c_1793,c_1790,c_1772,c_1769,c_1341,c_17,c_19,c_20,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:29:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.93/1.03  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.93/1.03  
% 2.93/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.93/1.03  
% 2.93/1.03  ------  iProver source info
% 2.93/1.03  
% 2.93/1.03  git: date: 2020-06-30 10:37:57 +0100
% 2.93/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.93/1.03  git: non_committed_changes: false
% 2.93/1.03  git: last_make_outside_of_git: false
% 2.93/1.03  
% 2.93/1.03  ------ 
% 2.93/1.03  
% 2.93/1.03  ------ Input Options
% 2.93/1.03  
% 2.93/1.03  --out_options                           all
% 2.93/1.03  --tptp_safe_out                         true
% 2.93/1.03  --problem_path                          ""
% 2.93/1.03  --include_path                          ""
% 2.93/1.03  --clausifier                            res/vclausify_rel
% 2.93/1.03  --clausifier_options                    --mode clausify
% 2.93/1.03  --stdin                                 false
% 2.93/1.03  --stats_out                             all
% 2.93/1.03  
% 2.93/1.03  ------ General Options
% 2.93/1.03  
% 2.93/1.03  --fof                                   false
% 2.93/1.03  --time_out_real                         305.
% 2.93/1.03  --time_out_virtual                      -1.
% 2.93/1.03  --symbol_type_check                     false
% 2.93/1.03  --clausify_out                          false
% 2.93/1.03  --sig_cnt_out                           false
% 2.93/1.03  --trig_cnt_out                          false
% 2.93/1.03  --trig_cnt_out_tolerance                1.
% 2.93/1.03  --trig_cnt_out_sk_spl                   false
% 2.93/1.03  --abstr_cl_out                          false
% 2.93/1.03  
% 2.93/1.03  ------ Global Options
% 2.93/1.03  
% 2.93/1.03  --schedule                              default
% 2.93/1.03  --add_important_lit                     false
% 2.93/1.03  --prop_solver_per_cl                    1000
% 2.93/1.03  --min_unsat_core                        false
% 2.93/1.03  --soft_assumptions                      false
% 2.93/1.03  --soft_lemma_size                       3
% 2.93/1.03  --prop_impl_unit_size                   0
% 2.93/1.03  --prop_impl_unit                        []
% 2.93/1.03  --share_sel_clauses                     true
% 2.93/1.03  --reset_solvers                         false
% 2.93/1.03  --bc_imp_inh                            [conj_cone]
% 2.93/1.03  --conj_cone_tolerance                   3.
% 2.93/1.03  --extra_neg_conj                        none
% 2.93/1.03  --large_theory_mode                     true
% 2.93/1.03  --prolific_symb_bound                   200
% 2.93/1.03  --lt_threshold                          2000
% 2.93/1.03  --clause_weak_htbl                      true
% 2.93/1.03  --gc_record_bc_elim                     false
% 2.93/1.03  
% 2.93/1.03  ------ Preprocessing Options
% 2.93/1.03  
% 2.93/1.03  --preprocessing_flag                    true
% 2.93/1.03  --time_out_prep_mult                    0.1
% 2.93/1.03  --splitting_mode                        input
% 2.93/1.03  --splitting_grd                         true
% 2.93/1.03  --splitting_cvd                         false
% 2.93/1.03  --splitting_cvd_svl                     false
% 2.93/1.03  --splitting_nvd                         32
% 2.93/1.03  --sub_typing                            true
% 2.93/1.03  --prep_gs_sim                           true
% 2.93/1.03  --prep_unflatten                        true
% 2.93/1.03  --prep_res_sim                          true
% 2.93/1.03  --prep_upred                            true
% 2.93/1.03  --prep_sem_filter                       exhaustive
% 2.93/1.03  --prep_sem_filter_out                   false
% 2.93/1.03  --pred_elim                             true
% 2.93/1.03  --res_sim_input                         true
% 2.93/1.03  --eq_ax_congr_red                       true
% 2.93/1.03  --pure_diseq_elim                       true
% 2.93/1.03  --brand_transform                       false
% 2.93/1.03  --non_eq_to_eq                          false
% 2.93/1.03  --prep_def_merge                        true
% 2.93/1.03  --prep_def_merge_prop_impl              false
% 2.93/1.03  --prep_def_merge_mbd                    true
% 2.93/1.03  --prep_def_merge_tr_red                 false
% 2.93/1.03  --prep_def_merge_tr_cl                  false
% 2.93/1.03  --smt_preprocessing                     true
% 2.93/1.03  --smt_ac_axioms                         fast
% 2.93/1.03  --preprocessed_out                      false
% 2.93/1.03  --preprocessed_stats                    false
% 2.93/1.03  
% 2.93/1.03  ------ Abstraction refinement Options
% 2.93/1.03  
% 2.93/1.03  --abstr_ref                             []
% 2.93/1.03  --abstr_ref_prep                        false
% 2.93/1.03  --abstr_ref_until_sat                   false
% 2.93/1.03  --abstr_ref_sig_restrict                funpre
% 2.93/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.93/1.03  --abstr_ref_under                       []
% 2.93/1.03  
% 2.93/1.03  ------ SAT Options
% 2.93/1.03  
% 2.93/1.03  --sat_mode                              false
% 2.93/1.03  --sat_fm_restart_options                ""
% 2.93/1.03  --sat_gr_def                            false
% 2.93/1.03  --sat_epr_types                         true
% 2.93/1.03  --sat_non_cyclic_types                  false
% 2.93/1.03  --sat_finite_models                     false
% 2.93/1.03  --sat_fm_lemmas                         false
% 2.93/1.03  --sat_fm_prep                           false
% 2.93/1.03  --sat_fm_uc_incr                        true
% 2.93/1.03  --sat_out_model                         small
% 2.93/1.03  --sat_out_clauses                       false
% 2.93/1.03  
% 2.93/1.03  ------ QBF Options
% 2.93/1.03  
% 2.93/1.03  --qbf_mode                              false
% 2.93/1.03  --qbf_elim_univ                         false
% 2.93/1.03  --qbf_dom_inst                          none
% 2.93/1.03  --qbf_dom_pre_inst                      false
% 2.93/1.03  --qbf_sk_in                             false
% 2.93/1.03  --qbf_pred_elim                         true
% 2.93/1.03  --qbf_split                             512
% 2.93/1.03  
% 2.93/1.03  ------ BMC1 Options
% 2.93/1.03  
% 2.93/1.03  --bmc1_incremental                      false
% 2.93/1.03  --bmc1_axioms                           reachable_all
% 2.93/1.03  --bmc1_min_bound                        0
% 2.93/1.03  --bmc1_max_bound                        -1
% 2.93/1.03  --bmc1_max_bound_default                -1
% 2.93/1.03  --bmc1_symbol_reachability              true
% 2.93/1.03  --bmc1_property_lemmas                  false
% 2.93/1.03  --bmc1_k_induction                      false
% 2.93/1.03  --bmc1_non_equiv_states                 false
% 2.93/1.03  --bmc1_deadlock                         false
% 2.93/1.03  --bmc1_ucm                              false
% 2.93/1.03  --bmc1_add_unsat_core                   none
% 2.93/1.03  --bmc1_unsat_core_children              false
% 2.93/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.93/1.03  --bmc1_out_stat                         full
% 2.93/1.03  --bmc1_ground_init                      false
% 2.93/1.03  --bmc1_pre_inst_next_state              false
% 2.93/1.03  --bmc1_pre_inst_state                   false
% 2.93/1.03  --bmc1_pre_inst_reach_state             false
% 2.93/1.03  --bmc1_out_unsat_core                   false
% 2.93/1.03  --bmc1_aig_witness_out                  false
% 2.93/1.03  --bmc1_verbose                          false
% 2.93/1.03  --bmc1_dump_clauses_tptp                false
% 2.93/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.93/1.03  --bmc1_dump_file                        -
% 2.93/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.93/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.93/1.03  --bmc1_ucm_extend_mode                  1
% 2.93/1.03  --bmc1_ucm_init_mode                    2
% 2.93/1.03  --bmc1_ucm_cone_mode                    none
% 2.93/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.93/1.03  --bmc1_ucm_relax_model                  4
% 2.93/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.93/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.93/1.03  --bmc1_ucm_layered_model                none
% 2.93/1.03  --bmc1_ucm_max_lemma_size               10
% 2.93/1.03  
% 2.93/1.03  ------ AIG Options
% 2.93/1.03  
% 2.93/1.03  --aig_mode                              false
% 2.93/1.03  
% 2.93/1.03  ------ Instantiation Options
% 2.93/1.03  
% 2.93/1.03  --instantiation_flag                    true
% 2.93/1.03  --inst_sos_flag                         false
% 2.93/1.03  --inst_sos_phase                        true
% 2.93/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.93/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.93/1.03  --inst_lit_sel_side                     num_symb
% 2.93/1.03  --inst_solver_per_active                1400
% 2.93/1.03  --inst_solver_calls_frac                1.
% 2.93/1.03  --inst_passive_queue_type               priority_queues
% 2.93/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.93/1.03  --inst_passive_queues_freq              [25;2]
% 2.93/1.03  --inst_dismatching                      true
% 2.93/1.03  --inst_eager_unprocessed_to_passive     true
% 2.93/1.03  --inst_prop_sim_given                   true
% 2.93/1.03  --inst_prop_sim_new                     false
% 2.93/1.03  --inst_subs_new                         false
% 2.93/1.03  --inst_eq_res_simp                      false
% 2.93/1.03  --inst_subs_given                       false
% 2.93/1.03  --inst_orphan_elimination               true
% 2.93/1.03  --inst_learning_loop_flag               true
% 2.93/1.03  --inst_learning_start                   3000
% 2.93/1.03  --inst_learning_factor                  2
% 2.93/1.03  --inst_start_prop_sim_after_learn       3
% 2.93/1.03  --inst_sel_renew                        solver
% 2.93/1.03  --inst_lit_activity_flag                true
% 2.93/1.03  --inst_restr_to_given                   false
% 2.93/1.03  --inst_activity_threshold               500
% 2.93/1.03  --inst_out_proof                        true
% 2.93/1.03  
% 2.93/1.03  ------ Resolution Options
% 2.93/1.03  
% 2.93/1.03  --resolution_flag                       true
% 2.93/1.03  --res_lit_sel                           adaptive
% 2.93/1.03  --res_lit_sel_side                      none
% 2.93/1.03  --res_ordering                          kbo
% 2.93/1.03  --res_to_prop_solver                    active
% 2.93/1.03  --res_prop_simpl_new                    false
% 2.93/1.03  --res_prop_simpl_given                  true
% 2.93/1.03  --res_passive_queue_type                priority_queues
% 2.93/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.93/1.03  --res_passive_queues_freq               [15;5]
% 2.93/1.03  --res_forward_subs                      full
% 2.93/1.03  --res_backward_subs                     full
% 2.93/1.03  --res_forward_subs_resolution           true
% 2.93/1.03  --res_backward_subs_resolution          true
% 2.93/1.03  --res_orphan_elimination                true
% 2.93/1.03  --res_time_limit                        2.
% 2.93/1.03  --res_out_proof                         true
% 2.93/1.03  
% 2.93/1.03  ------ Superposition Options
% 2.93/1.03  
% 2.93/1.03  --superposition_flag                    true
% 2.93/1.03  --sup_passive_queue_type                priority_queues
% 2.93/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.93/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.93/1.03  --demod_completeness_check              fast
% 2.93/1.03  --demod_use_ground                      true
% 2.93/1.03  --sup_to_prop_solver                    passive
% 2.93/1.03  --sup_prop_simpl_new                    true
% 2.93/1.03  --sup_prop_simpl_given                  true
% 2.93/1.03  --sup_fun_splitting                     false
% 2.93/1.03  --sup_smt_interval                      50000
% 2.93/1.03  
% 2.93/1.03  ------ Superposition Simplification Setup
% 2.93/1.03  
% 2.93/1.03  --sup_indices_passive                   []
% 2.93/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.93/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.93/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.93/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.93/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.93/1.03  --sup_full_bw                           [BwDemod]
% 2.93/1.03  --sup_immed_triv                        [TrivRules]
% 2.93/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.93/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.93/1.03  --sup_immed_bw_main                     []
% 2.93/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.93/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.93/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.93/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.93/1.03  
% 2.93/1.03  ------ Combination Options
% 2.93/1.03  
% 2.93/1.03  --comb_res_mult                         3
% 2.93/1.03  --comb_sup_mult                         2
% 2.93/1.03  --comb_inst_mult                        10
% 2.93/1.03  
% 2.93/1.03  ------ Debug Options
% 2.93/1.03  
% 2.93/1.03  --dbg_backtrace                         false
% 2.93/1.03  --dbg_dump_prop_clauses                 false
% 2.93/1.03  --dbg_dump_prop_clauses_file            -
% 2.93/1.03  --dbg_out_stat                          false
% 2.93/1.03  ------ Parsing...
% 2.93/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.93/1.03  
% 2.93/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.93/1.03  
% 2.93/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.93/1.03  
% 2.93/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.93/1.03  ------ Proving...
% 2.93/1.03  ------ Problem Properties 
% 2.93/1.03  
% 2.93/1.03  
% 2.93/1.03  clauses                                 17
% 2.93/1.03  conjectures                             8
% 2.93/1.03  EPR                                     3
% 2.93/1.03  Horn                                    13
% 2.93/1.03  unary                                   4
% 2.93/1.03  binary                                  7
% 2.93/1.03  lits                                    50
% 2.93/1.03  lits eq                                 14
% 2.93/1.03  fd_pure                                 0
% 2.93/1.03  fd_pseudo                               0
% 2.93/1.03  fd_cond                                 0
% 2.93/1.03  fd_pseudo_cond                          0
% 2.93/1.03  AC symbols                              0
% 2.93/1.03  
% 2.93/1.03  ------ Schedule dynamic 5 is on 
% 2.93/1.03  
% 2.93/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.93/1.03  
% 2.93/1.03  
% 2.93/1.03  ------ 
% 2.93/1.03  Current options:
% 2.93/1.03  ------ 
% 2.93/1.03  
% 2.93/1.03  ------ Input Options
% 2.93/1.03  
% 2.93/1.03  --out_options                           all
% 2.93/1.03  --tptp_safe_out                         true
% 2.93/1.03  --problem_path                          ""
% 2.93/1.03  --include_path                          ""
% 2.93/1.03  --clausifier                            res/vclausify_rel
% 2.93/1.03  --clausifier_options                    --mode clausify
% 2.93/1.03  --stdin                                 false
% 2.93/1.03  --stats_out                             all
% 2.93/1.03  
% 2.93/1.03  ------ General Options
% 2.93/1.03  
% 2.93/1.03  --fof                                   false
% 2.93/1.03  --time_out_real                         305.
% 2.93/1.03  --time_out_virtual                      -1.
% 2.93/1.03  --symbol_type_check                     false
% 2.93/1.03  --clausify_out                          false
% 2.93/1.03  --sig_cnt_out                           false
% 2.93/1.03  --trig_cnt_out                          false
% 2.93/1.03  --trig_cnt_out_tolerance                1.
% 2.93/1.03  --trig_cnt_out_sk_spl                   false
% 2.93/1.03  --abstr_cl_out                          false
% 2.93/1.03  
% 2.93/1.03  ------ Global Options
% 2.93/1.03  
% 2.93/1.03  --schedule                              default
% 2.93/1.03  --add_important_lit                     false
% 2.93/1.03  --prop_solver_per_cl                    1000
% 2.93/1.03  --min_unsat_core                        false
% 2.93/1.03  --soft_assumptions                      false
% 2.93/1.03  --soft_lemma_size                       3
% 2.93/1.03  --prop_impl_unit_size                   0
% 2.93/1.03  --prop_impl_unit                        []
% 2.93/1.03  --share_sel_clauses                     true
% 2.93/1.03  --reset_solvers                         false
% 2.93/1.03  --bc_imp_inh                            [conj_cone]
% 2.93/1.03  --conj_cone_tolerance                   3.
% 2.93/1.03  --extra_neg_conj                        none
% 2.93/1.03  --large_theory_mode                     true
% 2.93/1.03  --prolific_symb_bound                   200
% 2.93/1.03  --lt_threshold                          2000
% 2.93/1.03  --clause_weak_htbl                      true
% 2.93/1.03  --gc_record_bc_elim                     false
% 2.93/1.03  
% 2.93/1.03  ------ Preprocessing Options
% 2.93/1.03  
% 2.93/1.03  --preprocessing_flag                    true
% 2.93/1.03  --time_out_prep_mult                    0.1
% 2.93/1.03  --splitting_mode                        input
% 2.93/1.03  --splitting_grd                         true
% 2.93/1.03  --splitting_cvd                         false
% 2.93/1.03  --splitting_cvd_svl                     false
% 2.93/1.03  --splitting_nvd                         32
% 2.93/1.03  --sub_typing                            true
% 2.93/1.03  --prep_gs_sim                           true
% 2.93/1.03  --prep_unflatten                        true
% 2.93/1.03  --prep_res_sim                          true
% 2.93/1.03  --prep_upred                            true
% 2.93/1.03  --prep_sem_filter                       exhaustive
% 2.93/1.03  --prep_sem_filter_out                   false
% 2.93/1.03  --pred_elim                             true
% 2.93/1.03  --res_sim_input                         true
% 2.93/1.03  --eq_ax_congr_red                       true
% 2.93/1.03  --pure_diseq_elim                       true
% 2.93/1.03  --brand_transform                       false
% 2.93/1.03  --non_eq_to_eq                          false
% 2.93/1.03  --prep_def_merge                        true
% 2.93/1.03  --prep_def_merge_prop_impl              false
% 2.93/1.03  --prep_def_merge_mbd                    true
% 2.93/1.03  --prep_def_merge_tr_red                 false
% 2.93/1.03  --prep_def_merge_tr_cl                  false
% 2.93/1.03  --smt_preprocessing                     true
% 2.93/1.03  --smt_ac_axioms                         fast
% 2.93/1.03  --preprocessed_out                      false
% 2.93/1.03  --preprocessed_stats                    false
% 2.93/1.03  
% 2.93/1.03  ------ Abstraction refinement Options
% 2.93/1.03  
% 2.93/1.03  --abstr_ref                             []
% 2.93/1.03  --abstr_ref_prep                        false
% 2.93/1.03  --abstr_ref_until_sat                   false
% 2.93/1.03  --abstr_ref_sig_restrict                funpre
% 2.93/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.93/1.03  --abstr_ref_under                       []
% 2.93/1.03  
% 2.93/1.03  ------ SAT Options
% 2.93/1.03  
% 2.93/1.03  --sat_mode                              false
% 2.93/1.03  --sat_fm_restart_options                ""
% 2.93/1.03  --sat_gr_def                            false
% 2.93/1.03  --sat_epr_types                         true
% 2.93/1.03  --sat_non_cyclic_types                  false
% 2.93/1.03  --sat_finite_models                     false
% 2.93/1.03  --sat_fm_lemmas                         false
% 2.93/1.03  --sat_fm_prep                           false
% 2.93/1.03  --sat_fm_uc_incr                        true
% 2.93/1.03  --sat_out_model                         small
% 2.93/1.03  --sat_out_clauses                       false
% 2.93/1.03  
% 2.93/1.03  ------ QBF Options
% 2.93/1.03  
% 2.93/1.03  --qbf_mode                              false
% 2.93/1.03  --qbf_elim_univ                         false
% 2.93/1.03  --qbf_dom_inst                          none
% 2.93/1.03  --qbf_dom_pre_inst                      false
% 2.93/1.03  --qbf_sk_in                             false
% 2.93/1.03  --qbf_pred_elim                         true
% 2.93/1.03  --qbf_split                             512
% 2.93/1.03  
% 2.93/1.03  ------ BMC1 Options
% 2.93/1.03  
% 2.93/1.03  --bmc1_incremental                      false
% 2.93/1.03  --bmc1_axioms                           reachable_all
% 2.93/1.03  --bmc1_min_bound                        0
% 2.93/1.03  --bmc1_max_bound                        -1
% 2.93/1.03  --bmc1_max_bound_default                -1
% 2.93/1.03  --bmc1_symbol_reachability              true
% 2.93/1.03  --bmc1_property_lemmas                  false
% 2.93/1.03  --bmc1_k_induction                      false
% 2.93/1.03  --bmc1_non_equiv_states                 false
% 2.93/1.03  --bmc1_deadlock                         false
% 2.93/1.03  --bmc1_ucm                              false
% 2.93/1.03  --bmc1_add_unsat_core                   none
% 2.93/1.03  --bmc1_unsat_core_children              false
% 2.93/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.93/1.03  --bmc1_out_stat                         full
% 2.93/1.03  --bmc1_ground_init                      false
% 2.93/1.03  --bmc1_pre_inst_next_state              false
% 2.93/1.03  --bmc1_pre_inst_state                   false
% 2.93/1.03  --bmc1_pre_inst_reach_state             false
% 2.93/1.03  --bmc1_out_unsat_core                   false
% 2.93/1.03  --bmc1_aig_witness_out                  false
% 2.93/1.03  --bmc1_verbose                          false
% 2.93/1.03  --bmc1_dump_clauses_tptp                false
% 2.93/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.93/1.03  --bmc1_dump_file                        -
% 2.93/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.93/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.93/1.03  --bmc1_ucm_extend_mode                  1
% 2.93/1.03  --bmc1_ucm_init_mode                    2
% 2.93/1.03  --bmc1_ucm_cone_mode                    none
% 2.93/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.93/1.03  --bmc1_ucm_relax_model                  4
% 2.93/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.93/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.93/1.03  --bmc1_ucm_layered_model                none
% 2.93/1.03  --bmc1_ucm_max_lemma_size               10
% 2.93/1.03  
% 2.93/1.03  ------ AIG Options
% 2.93/1.03  
% 2.93/1.03  --aig_mode                              false
% 2.93/1.03  
% 2.93/1.03  ------ Instantiation Options
% 2.93/1.03  
% 2.93/1.03  --instantiation_flag                    true
% 2.93/1.03  --inst_sos_flag                         false
% 2.93/1.03  --inst_sos_phase                        true
% 2.93/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.93/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.93/1.03  --inst_lit_sel_side                     none
% 2.93/1.03  --inst_solver_per_active                1400
% 2.93/1.03  --inst_solver_calls_frac                1.
% 2.93/1.03  --inst_passive_queue_type               priority_queues
% 2.93/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.93/1.03  --inst_passive_queues_freq              [25;2]
% 2.93/1.03  --inst_dismatching                      true
% 2.93/1.03  --inst_eager_unprocessed_to_passive     true
% 2.93/1.03  --inst_prop_sim_given                   true
% 2.93/1.03  --inst_prop_sim_new                     false
% 2.93/1.03  --inst_subs_new                         false
% 2.93/1.03  --inst_eq_res_simp                      false
% 2.93/1.03  --inst_subs_given                       false
% 2.93/1.03  --inst_orphan_elimination               true
% 2.93/1.03  --inst_learning_loop_flag               true
% 2.93/1.03  --inst_learning_start                   3000
% 2.93/1.03  --inst_learning_factor                  2
% 2.93/1.03  --inst_start_prop_sim_after_learn       3
% 2.93/1.03  --inst_sel_renew                        solver
% 2.93/1.03  --inst_lit_activity_flag                true
% 2.93/1.03  --inst_restr_to_given                   false
% 2.93/1.03  --inst_activity_threshold               500
% 2.93/1.03  --inst_out_proof                        true
% 2.93/1.03  
% 2.93/1.03  ------ Resolution Options
% 2.93/1.03  
% 2.93/1.03  --resolution_flag                       false
% 2.93/1.03  --res_lit_sel                           adaptive
% 2.93/1.03  --res_lit_sel_side                      none
% 2.93/1.03  --res_ordering                          kbo
% 2.93/1.03  --res_to_prop_solver                    active
% 2.93/1.03  --res_prop_simpl_new                    false
% 2.93/1.03  --res_prop_simpl_given                  true
% 2.93/1.03  --res_passive_queue_type                priority_queues
% 2.93/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.93/1.03  --res_passive_queues_freq               [15;5]
% 2.93/1.03  --res_forward_subs                      full
% 2.93/1.03  --res_backward_subs                     full
% 2.93/1.03  --res_forward_subs_resolution           true
% 2.93/1.03  --res_backward_subs_resolution          true
% 2.93/1.03  --res_orphan_elimination                true
% 2.93/1.03  --res_time_limit                        2.
% 2.93/1.03  --res_out_proof                         true
% 2.93/1.03  
% 2.93/1.03  ------ Superposition Options
% 2.93/1.03  
% 2.93/1.03  --superposition_flag                    true
% 2.93/1.03  --sup_passive_queue_type                priority_queues
% 2.93/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.93/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.93/1.03  --demod_completeness_check              fast
% 2.93/1.03  --demod_use_ground                      true
% 2.93/1.03  --sup_to_prop_solver                    passive
% 2.93/1.03  --sup_prop_simpl_new                    true
% 2.93/1.03  --sup_prop_simpl_given                  true
% 2.93/1.03  --sup_fun_splitting                     false
% 2.93/1.03  --sup_smt_interval                      50000
% 2.93/1.03  
% 2.93/1.03  ------ Superposition Simplification Setup
% 2.93/1.03  
% 2.93/1.03  --sup_indices_passive                   []
% 2.93/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.93/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.93/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.93/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.93/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.93/1.03  --sup_full_bw                           [BwDemod]
% 2.93/1.03  --sup_immed_triv                        [TrivRules]
% 2.93/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.93/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.93/1.03  --sup_immed_bw_main                     []
% 2.93/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.93/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.93/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.93/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.93/1.03  
% 2.93/1.03  ------ Combination Options
% 2.93/1.03  
% 2.93/1.03  --comb_res_mult                         3
% 2.93/1.03  --comb_sup_mult                         2
% 2.93/1.03  --comb_inst_mult                        10
% 2.93/1.03  
% 2.93/1.03  ------ Debug Options
% 2.93/1.03  
% 2.93/1.03  --dbg_backtrace                         false
% 2.93/1.03  --dbg_dump_prop_clauses                 false
% 2.93/1.03  --dbg_dump_prop_clauses_file            -
% 2.93/1.03  --dbg_out_stat                          false
% 2.93/1.03  
% 2.93/1.03  
% 2.93/1.03  
% 2.93/1.03  
% 2.93/1.03  ------ Proving...
% 2.93/1.03  
% 2.93/1.03  
% 2.93/1.03  % SZS status Theorem for theBenchmark.p
% 2.93/1.03  
% 2.93/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 2.93/1.03  
% 2.93/1.03  fof(f1,axiom,(
% 2.93/1.03    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.93/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.93/1.03  
% 2.93/1.03  fof(f9,plain,(
% 2.93/1.03    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 2.93/1.03    inference(unused_predicate_definition_removal,[],[f1])).
% 2.93/1.03  
% 2.93/1.03  fof(f10,plain,(
% 2.93/1.03    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 2.93/1.03    inference(ennf_transformation,[],[f9])).
% 2.93/1.03  
% 2.93/1.03  fof(f32,plain,(
% 2.93/1.03    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.93/1.03    inference(cnf_transformation,[],[f10])).
% 2.93/1.03  
% 2.93/1.03  fof(f6,axiom,(
% 2.93/1.03    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) => (r1_partfun1(X0,X1) <=> ! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2))))))),
% 2.93/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.93/1.03  
% 2.93/1.03  fof(f16,plain,(
% 2.93/1.03    ! [X0] : (! [X1] : (((r1_partfun1(X0,X1) <=> ! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0)))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.93/1.03    inference(ennf_transformation,[],[f6])).
% 2.93/1.03  
% 2.93/1.03  fof(f17,plain,(
% 2.93/1.03    ! [X0] : (! [X1] : ((r1_partfun1(X0,X1) <=> ! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0)))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.93/1.03    inference(flattening,[],[f16])).
% 2.93/1.03  
% 2.93/1.03  fof(f21,plain,(
% 2.93/1.03    ! [X0] : (! [X1] : (((r1_partfun1(X0,X1) | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0)))) & (! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0))) | ~r1_partfun1(X0,X1))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.93/1.03    inference(nnf_transformation,[],[f17])).
% 2.93/1.03  
% 2.93/1.03  fof(f22,plain,(
% 2.93/1.03    ! [X0] : (! [X1] : (((r1_partfun1(X0,X1) | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0)))) & (! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r1_partfun1(X0,X1))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.93/1.03    inference(rectify,[],[f21])).
% 2.93/1.03  
% 2.93/1.03  fof(f23,plain,(
% 2.93/1.03    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1)) & r2_hidden(sK0(X0,X1),k1_relat_1(X0))))),
% 2.93/1.03    introduced(choice_axiom,[])).
% 2.93/1.03  
% 2.93/1.03  fof(f24,plain,(
% 2.93/1.03    ! [X0] : (! [X1] : (((r1_partfun1(X0,X1) | (k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1)) & r2_hidden(sK0(X0,X1),k1_relat_1(X0)))) & (! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r1_partfun1(X0,X1))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.93/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).
% 2.93/1.03  
% 2.93/1.03  fof(f42,plain,(
% 2.93/1.03    ( ! [X0,X3,X1] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r1_partfun1(X0,X1) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.93/1.03    inference(cnf_transformation,[],[f24])).
% 2.93/1.03  
% 2.93/1.03  fof(f5,axiom,(
% 2.93/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.93/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.93/1.03  
% 2.93/1.03  fof(f14,plain,(
% 2.93/1.03    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.93/1.03    inference(ennf_transformation,[],[f5])).
% 2.93/1.03  
% 2.93/1.03  fof(f15,plain,(
% 2.93/1.03    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.93/1.03    inference(flattening,[],[f14])).
% 2.93/1.03  
% 2.93/1.03  fof(f20,plain,(
% 2.93/1.03    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.93/1.03    inference(nnf_transformation,[],[f15])).
% 2.93/1.03  
% 2.93/1.03  fof(f36,plain,(
% 2.93/1.03    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.93/1.03    inference(cnf_transformation,[],[f20])).
% 2.93/1.03  
% 2.93/1.03  fof(f7,conjecture,(
% 2.93/1.03    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (r1_partfun1(X2,X3) <=> ! [X4] : (r2_hidden(X4,k1_relset_1(X0,X1,X2)) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4))))))),
% 2.93/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.93/1.03  
% 2.93/1.03  fof(f8,negated_conjecture,(
% 2.93/1.03    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (r1_partfun1(X2,X3) <=> ! [X4] : (r2_hidden(X4,k1_relset_1(X0,X1,X2)) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4))))))),
% 2.93/1.03    inference(negated_conjecture,[],[f7])).
% 2.93/1.03  
% 2.93/1.03  fof(f18,plain,(
% 2.93/1.03    ? [X0,X1,X2] : (? [X3] : (((r1_partfun1(X2,X3) <~> ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,k1_relset_1(X0,X1,X2)))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 2.93/1.03    inference(ennf_transformation,[],[f8])).
% 2.93/1.03  
% 2.93/1.03  fof(f19,plain,(
% 2.93/1.03    ? [X0,X1,X2] : (? [X3] : ((r1_partfun1(X2,X3) <~> ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,k1_relset_1(X0,X1,X2)))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 2.93/1.03    inference(flattening,[],[f18])).
% 2.93/1.03  
% 2.93/1.03  fof(f25,plain,(
% 2.93/1.03    ? [X0,X1,X2] : (? [X3] : (((? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & r2_hidden(X4,k1_relset_1(X0,X1,X2))) | ~r1_partfun1(X2,X3)) & (! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,k1_relset_1(X0,X1,X2))) | r1_partfun1(X2,X3))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 2.93/1.03    inference(nnf_transformation,[],[f19])).
% 2.93/1.03  
% 2.93/1.03  fof(f26,plain,(
% 2.93/1.03    ? [X0,X1,X2] : (? [X3] : ((? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & r2_hidden(X4,k1_relset_1(X0,X1,X2))) | ~r1_partfun1(X2,X3)) & (! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,k1_relset_1(X0,X1,X2))) | r1_partfun1(X2,X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 2.93/1.03    inference(flattening,[],[f25])).
% 2.93/1.03  
% 2.93/1.03  fof(f27,plain,(
% 2.93/1.03    ? [X0,X1,X2] : (? [X3] : ((? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & r2_hidden(X4,k1_relset_1(X0,X1,X2))) | ~r1_partfun1(X2,X3)) & (! [X5] : (k1_funct_1(X2,X5) = k1_funct_1(X3,X5) | ~r2_hidden(X5,k1_relset_1(X0,X1,X2))) | r1_partfun1(X2,X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 2.93/1.03    inference(rectify,[],[f26])).
% 2.93/1.03  
% 2.93/1.03  fof(f30,plain,(
% 2.93/1.03    ( ! [X2,X0,X3,X1] : (? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & r2_hidden(X4,k1_relset_1(X0,X1,X2))) => (k1_funct_1(X2,sK5) != k1_funct_1(X3,sK5) & r2_hidden(sK5,k1_relset_1(X0,X1,X2)))) )),
% 2.93/1.03    introduced(choice_axiom,[])).
% 2.93/1.03  
% 2.93/1.03  fof(f29,plain,(
% 2.93/1.03    ( ! [X2,X0,X1] : (? [X3] : ((? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & r2_hidden(X4,k1_relset_1(X0,X1,X2))) | ~r1_partfun1(X2,X3)) & (! [X5] : (k1_funct_1(X2,X5) = k1_funct_1(X3,X5) | ~r2_hidden(X5,k1_relset_1(X0,X1,X2))) | r1_partfun1(X2,X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((? [X4] : (k1_funct_1(sK4,X4) != k1_funct_1(X2,X4) & r2_hidden(X4,k1_relset_1(X0,X1,X2))) | ~r1_partfun1(X2,sK4)) & (! [X5] : (k1_funct_1(sK4,X5) = k1_funct_1(X2,X5) | ~r2_hidden(X5,k1_relset_1(X0,X1,X2))) | r1_partfun1(X2,sK4)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(sK4,X0,X1) & v1_funct_1(sK4))) )),
% 2.93/1.03    introduced(choice_axiom,[])).
% 2.93/1.03  
% 2.93/1.03  fof(f28,plain,(
% 2.93/1.03    ? [X0,X1,X2] : (? [X3] : ((? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & r2_hidden(X4,k1_relset_1(X0,X1,X2))) | ~r1_partfun1(X2,X3)) & (! [X5] : (k1_funct_1(X2,X5) = k1_funct_1(X3,X5) | ~r2_hidden(X5,k1_relset_1(X0,X1,X2))) | r1_partfun1(X2,X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (? [X3] : ((? [X4] : (k1_funct_1(sK3,X4) != k1_funct_1(X3,X4) & r2_hidden(X4,k1_relset_1(sK1,sK2,sK3))) | ~r1_partfun1(sK3,X3)) & (! [X5] : (k1_funct_1(sK3,X5) = k1_funct_1(X3,X5) | ~r2_hidden(X5,k1_relset_1(sK1,sK2,sK3))) | r1_partfun1(sK3,X3)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X3,sK1,sK2) & v1_funct_1(X3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_1(sK3))),
% 2.93/1.04    introduced(choice_axiom,[])).
% 2.93/1.04  
% 2.93/1.04  fof(f31,plain,(
% 2.93/1.04    (((k1_funct_1(sK3,sK5) != k1_funct_1(sK4,sK5) & r2_hidden(sK5,k1_relset_1(sK1,sK2,sK3))) | ~r1_partfun1(sK3,sK4)) & (! [X5] : (k1_funct_1(sK3,X5) = k1_funct_1(sK4,X5) | ~r2_hidden(X5,k1_relset_1(sK1,sK2,sK3))) | r1_partfun1(sK3,sK4)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK2) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_1(sK3)),
% 2.93/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f27,f30,f29,f28])).
% 2.93/1.04  
% 2.93/1.04  fof(f48,plain,(
% 2.93/1.04    v1_funct_2(sK4,sK1,sK2)),
% 2.93/1.04    inference(cnf_transformation,[],[f31])).
% 2.93/1.04  
% 2.93/1.04  fof(f49,plain,(
% 2.93/1.04    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 2.93/1.04    inference(cnf_transformation,[],[f31])).
% 2.93/1.04  
% 2.93/1.04  fof(f4,axiom,(
% 2.93/1.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 2.93/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.93/1.04  
% 2.93/1.04  fof(f13,plain,(
% 2.93/1.04    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.93/1.04    inference(ennf_transformation,[],[f4])).
% 2.93/1.04  
% 2.93/1.04  fof(f35,plain,(
% 2.93/1.04    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.93/1.04    inference(cnf_transformation,[],[f13])).
% 2.93/1.04  
% 2.93/1.04  fof(f43,plain,(
% 2.93/1.04    ( ! [X0,X1] : (r1_partfun1(X0,X1) | r2_hidden(sK0(X0,X1),k1_relat_1(X0)) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.93/1.04    inference(cnf_transformation,[],[f24])).
% 2.93/1.04  
% 2.93/1.04  fof(f47,plain,(
% 2.93/1.04    v1_funct_1(sK4)),
% 2.93/1.04    inference(cnf_transformation,[],[f31])).
% 2.93/1.04  
% 2.93/1.04  fof(f2,axiom,(
% 2.93/1.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.93/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.93/1.04  
% 2.93/1.04  fof(f11,plain,(
% 2.93/1.04    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.93/1.04    inference(ennf_transformation,[],[f2])).
% 2.93/1.04  
% 2.93/1.04  fof(f33,plain,(
% 2.93/1.04    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.93/1.04    inference(cnf_transformation,[],[f11])).
% 2.93/1.04  
% 2.93/1.04  fof(f46,plain,(
% 2.93/1.04    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 2.93/1.04    inference(cnf_transformation,[],[f31])).
% 2.93/1.04  
% 2.93/1.04  fof(f51,plain,(
% 2.93/1.04    ( ! [X5] : (k1_funct_1(sK3,X5) = k1_funct_1(sK4,X5) | ~r2_hidden(X5,k1_relset_1(sK1,sK2,sK3)) | r1_partfun1(sK3,sK4)) )),
% 2.93/1.04    inference(cnf_transformation,[],[f31])).
% 2.93/1.04  
% 2.93/1.04  fof(f45,plain,(
% 2.93/1.04    v1_funct_1(sK3)),
% 2.93/1.04    inference(cnf_transformation,[],[f31])).
% 2.93/1.04  
% 2.93/1.04  fof(f3,axiom,(
% 2.93/1.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 2.93/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.93/1.04  
% 2.93/1.04  fof(f12,plain,(
% 2.93/1.04    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.93/1.04    inference(ennf_transformation,[],[f3])).
% 2.93/1.04  
% 2.93/1.04  fof(f34,plain,(
% 2.93/1.04    ( ! [X2,X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.93/1.04    inference(cnf_transformation,[],[f12])).
% 2.93/1.04  
% 2.93/1.04  fof(f52,plain,(
% 2.93/1.04    r2_hidden(sK5,k1_relset_1(sK1,sK2,sK3)) | ~r1_partfun1(sK3,sK4)),
% 2.93/1.04    inference(cnf_transformation,[],[f31])).
% 2.93/1.04  
% 2.93/1.04  fof(f44,plain,(
% 2.93/1.04    ( ! [X0,X1] : (r1_partfun1(X0,X1) | k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1)) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.93/1.04    inference(cnf_transformation,[],[f24])).
% 2.93/1.04  
% 2.93/1.04  fof(f53,plain,(
% 2.93/1.04    k1_funct_1(sK3,sK5) != k1_funct_1(sK4,sK5) | ~r1_partfun1(sK3,sK4)),
% 2.93/1.04    inference(cnf_transformation,[],[f31])).
% 2.93/1.04  
% 2.93/1.04  fof(f37,plain,(
% 2.93/1.04    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.93/1.04    inference(cnf_transformation,[],[f20])).
% 2.93/1.04  
% 2.93/1.04  fof(f58,plain,(
% 2.93/1.04    ( ! [X2,X1] : (k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0 | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 2.93/1.04    inference(equality_resolution,[],[f37])).
% 2.93/1.04  
% 2.93/1.04  fof(f50,plain,(
% 2.93/1.04    k1_xboole_0 = sK1 | k1_xboole_0 != sK2),
% 2.93/1.04    inference(cnf_transformation,[],[f31])).
% 2.93/1.04  
% 2.93/1.04  fof(f40,plain,(
% 2.93/1.04    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.93/1.04    inference(cnf_transformation,[],[f20])).
% 2.93/1.04  
% 2.93/1.04  fof(f56,plain,(
% 2.93/1.04    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 2.93/1.04    inference(equality_resolution,[],[f40])).
% 2.93/1.04  
% 2.93/1.04  cnf(c_0,plain,
% 2.93/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.93/1.04      inference(cnf_transformation,[],[f32]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_12,plain,
% 2.93/1.04      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.93/1.04      | ~ r1_partfun1(X1,X2)
% 2.93/1.04      | ~ r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
% 2.93/1.04      | ~ v1_funct_1(X2)
% 2.93/1.04      | ~ v1_funct_1(X1)
% 2.93/1.04      | ~ v1_relat_1(X2)
% 2.93/1.04      | ~ v1_relat_1(X1)
% 2.93/1.04      | k1_funct_1(X2,X0) = k1_funct_1(X1,X0) ),
% 2.93/1.04      inference(cnf_transformation,[],[f42]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_291,plain,
% 2.93/1.04      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.93/1.04      | ~ r1_partfun1(X1,X2)
% 2.93/1.04      | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
% 2.93/1.04      | ~ v1_funct_1(X1)
% 2.93/1.04      | ~ v1_funct_1(X2)
% 2.93/1.04      | ~ v1_relat_1(X1)
% 2.93/1.04      | ~ v1_relat_1(X2)
% 2.93/1.04      | k1_funct_1(X1,X0) = k1_funct_1(X2,X0)
% 2.93/1.04      | k1_relat_1(X2) != X4
% 2.93/1.04      | k1_relat_1(X1) != X3 ),
% 2.93/1.04      inference(resolution_lifted,[status(thm)],[c_0,c_12]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_292,plain,
% 2.93/1.04      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.93/1.04      | ~ r1_partfun1(X1,X2)
% 2.93/1.04      | ~ m1_subset_1(k1_relat_1(X1),k1_zfmisc_1(k1_relat_1(X2)))
% 2.93/1.04      | ~ v1_funct_1(X1)
% 2.93/1.04      | ~ v1_funct_1(X2)
% 2.93/1.04      | ~ v1_relat_1(X1)
% 2.93/1.04      | ~ v1_relat_1(X2)
% 2.93/1.04      | k1_funct_1(X1,X0) = k1_funct_1(X2,X0) ),
% 2.93/1.04      inference(unflattening,[status(thm)],[c_291]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_1294,plain,
% 2.93/1.04      ( ~ r2_hidden(X0_49,k1_relat_1(X0_47))
% 2.93/1.04      | ~ r1_partfun1(X0_47,X1_47)
% 2.93/1.04      | ~ m1_subset_1(k1_relat_1(X0_47),k1_zfmisc_1(k1_relat_1(X1_47)))
% 2.93/1.04      | ~ v1_funct_1(X1_47)
% 2.93/1.04      | ~ v1_funct_1(X0_47)
% 2.93/1.04      | ~ v1_relat_1(X1_47)
% 2.93/1.04      | ~ v1_relat_1(X0_47)
% 2.93/1.04      | k1_funct_1(X0_47,X0_49) = k1_funct_1(X1_47,X0_49) ),
% 2.93/1.04      inference(subtyping,[status(esa)],[c_292]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_5264,plain,
% 2.93/1.04      ( ~ r2_hidden(sK5,k1_relat_1(sK3))
% 2.93/1.04      | ~ r1_partfun1(sK3,sK4)
% 2.93/1.04      | ~ m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(k1_relat_1(sK4)))
% 2.93/1.04      | ~ v1_funct_1(sK4)
% 2.93/1.04      | ~ v1_funct_1(sK3)
% 2.93/1.04      | ~ v1_relat_1(sK4)
% 2.93/1.04      | ~ v1_relat_1(sK3)
% 2.93/1.04      | k1_funct_1(sK3,sK5) = k1_funct_1(sK4,sK5) ),
% 2.93/1.04      inference(instantiation,[status(thm)],[c_1294]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_9,plain,
% 2.93/1.04      ( ~ v1_funct_2(X0,X1,X2)
% 2.93/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.93/1.04      | k1_relset_1(X1,X2,X0) = X1
% 2.93/1.04      | k1_xboole_0 = X2 ),
% 2.93/1.04      inference(cnf_transformation,[],[f36]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_18,negated_conjecture,
% 2.93/1.04      ( v1_funct_2(sK4,sK1,sK2) ),
% 2.93/1.04      inference(cnf_transformation,[],[f48]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_523,plain,
% 2.93/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.93/1.04      | k1_relset_1(X1,X2,X0) = X1
% 2.93/1.04      | sK2 != X2
% 2.93/1.04      | sK1 != X1
% 2.93/1.04      | sK4 != X0
% 2.93/1.04      | k1_xboole_0 = X2 ),
% 2.93/1.04      inference(resolution_lifted,[status(thm)],[c_9,c_18]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_524,plain,
% 2.93/1.04      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.93/1.04      | k1_relset_1(sK1,sK2,sK4) = sK1
% 2.93/1.04      | k1_xboole_0 = sK2 ),
% 2.93/1.04      inference(unflattening,[status(thm)],[c_523]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_17,negated_conjecture,
% 2.93/1.04      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 2.93/1.04      inference(cnf_transformation,[],[f49]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_526,plain,
% 2.93/1.04      ( k1_relset_1(sK1,sK2,sK4) = sK1 | k1_xboole_0 = sK2 ),
% 2.93/1.04      inference(global_propositional_subsumption,
% 2.93/1.04                [status(thm)],
% 2.93/1.04                [c_524,c_17]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_1291,plain,
% 2.93/1.04      ( k1_relset_1(sK1,sK2,sK4) = sK1 | k1_xboole_0 = sK2 ),
% 2.93/1.04      inference(subtyping,[status(esa)],[c_526]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_1300,negated_conjecture,
% 2.93/1.04      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 2.93/1.04      inference(subtyping,[status(esa)],[c_17]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_1622,plain,
% 2.93/1.04      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 2.93/1.04      inference(predicate_to_equality,[status(thm)],[c_1300]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_3,plain,
% 2.93/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.93/1.04      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.93/1.04      inference(cnf_transformation,[],[f35]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_1305,plain,
% 2.93/1.04      ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
% 2.93/1.04      | k1_relset_1(X1_47,X2_47,X0_47) = k1_relat_1(X0_47) ),
% 2.93/1.04      inference(subtyping,[status(esa)],[c_3]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_1618,plain,
% 2.93/1.04      ( k1_relset_1(X0_47,X1_47,X2_47) = k1_relat_1(X2_47)
% 2.93/1.04      | m1_subset_1(X2_47,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top ),
% 2.93/1.04      inference(predicate_to_equality,[status(thm)],[c_1305]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_1925,plain,
% 2.93/1.04      ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
% 2.93/1.04      inference(superposition,[status(thm)],[c_1622,c_1618]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_2144,plain,
% 2.93/1.04      ( k1_relat_1(sK4) = sK1 | sK2 = k1_xboole_0 ),
% 2.93/1.04      inference(superposition,[status(thm)],[c_1291,c_1925]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_11,plain,
% 2.93/1.04      ( r2_hidden(sK0(X0,X1),k1_relat_1(X0))
% 2.93/1.04      | r1_partfun1(X0,X1)
% 2.93/1.04      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 2.93/1.04      | ~ v1_funct_1(X1)
% 2.93/1.04      | ~ v1_funct_1(X0)
% 2.93/1.04      | ~ v1_relat_1(X1)
% 2.93/1.04      | ~ v1_relat_1(X0) ),
% 2.93/1.04      inference(cnf_transformation,[],[f43]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_237,plain,
% 2.93/1.04      ( r2_hidden(sK0(X0,X1),k1_relat_1(X0))
% 2.93/1.04      | r1_partfun1(X0,X1)
% 2.93/1.04      | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
% 2.93/1.04      | ~ v1_funct_1(X0)
% 2.93/1.04      | ~ v1_funct_1(X1)
% 2.93/1.04      | ~ v1_relat_1(X0)
% 2.93/1.04      | ~ v1_relat_1(X1)
% 2.93/1.04      | k1_relat_1(X1) != X3
% 2.93/1.04      | k1_relat_1(X0) != X2 ),
% 2.93/1.04      inference(resolution_lifted,[status(thm)],[c_0,c_11]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_238,plain,
% 2.93/1.04      ( r2_hidden(sK0(X0,X1),k1_relat_1(X0))
% 2.93/1.04      | r1_partfun1(X0,X1)
% 2.93/1.04      | ~ m1_subset_1(k1_relat_1(X0),k1_zfmisc_1(k1_relat_1(X1)))
% 2.93/1.04      | ~ v1_funct_1(X1)
% 2.93/1.04      | ~ v1_funct_1(X0)
% 2.93/1.04      | ~ v1_relat_1(X1)
% 2.93/1.04      | ~ v1_relat_1(X0) ),
% 2.93/1.04      inference(unflattening,[status(thm)],[c_237]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_1296,plain,
% 2.93/1.04      ( r2_hidden(sK0(X0_47,X1_47),k1_relat_1(X0_47))
% 2.93/1.04      | r1_partfun1(X0_47,X1_47)
% 2.93/1.04      | ~ m1_subset_1(k1_relat_1(X0_47),k1_zfmisc_1(k1_relat_1(X1_47)))
% 2.93/1.04      | ~ v1_funct_1(X1_47)
% 2.93/1.04      | ~ v1_funct_1(X0_47)
% 2.93/1.04      | ~ v1_relat_1(X1_47)
% 2.93/1.04      | ~ v1_relat_1(X0_47) ),
% 2.93/1.04      inference(subtyping,[status(esa)],[c_238]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_1626,plain,
% 2.93/1.04      ( r2_hidden(sK0(X0_47,X1_47),k1_relat_1(X0_47)) = iProver_top
% 2.93/1.04      | r1_partfun1(X0_47,X1_47) = iProver_top
% 2.93/1.04      | m1_subset_1(k1_relat_1(X0_47),k1_zfmisc_1(k1_relat_1(X1_47))) != iProver_top
% 2.93/1.04      | v1_funct_1(X0_47) != iProver_top
% 2.93/1.04      | v1_funct_1(X1_47) != iProver_top
% 2.93/1.04      | v1_relat_1(X0_47) != iProver_top
% 2.93/1.04      | v1_relat_1(X1_47) != iProver_top ),
% 2.93/1.04      inference(predicate_to_equality,[status(thm)],[c_1296]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_2312,plain,
% 2.93/1.04      ( sK2 = k1_xboole_0
% 2.93/1.04      | r2_hidden(sK0(X0_47,sK4),k1_relat_1(X0_47)) = iProver_top
% 2.93/1.04      | r1_partfun1(X0_47,sK4) = iProver_top
% 2.93/1.04      | m1_subset_1(k1_relat_1(X0_47),k1_zfmisc_1(sK1)) != iProver_top
% 2.93/1.04      | v1_funct_1(X0_47) != iProver_top
% 2.93/1.04      | v1_funct_1(sK4) != iProver_top
% 2.93/1.04      | v1_relat_1(X0_47) != iProver_top
% 2.93/1.04      | v1_relat_1(sK4) != iProver_top ),
% 2.93/1.04      inference(superposition,[status(thm)],[c_2144,c_1626]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_19,negated_conjecture,
% 2.93/1.04      ( v1_funct_1(sK4) ),
% 2.93/1.04      inference(cnf_transformation,[],[f47]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_24,plain,
% 2.93/1.04      ( v1_funct_1(sK4) = iProver_top ),
% 2.93/1.04      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_26,plain,
% 2.93/1.04      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 2.93/1.04      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_1,plain,
% 2.93/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.93/1.04      | v1_relat_1(X0) ),
% 2.93/1.04      inference(cnf_transformation,[],[f33]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_1307,plain,
% 2.93/1.04      ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
% 2.93/1.04      | v1_relat_1(X0_47) ),
% 2.93/1.04      inference(subtyping,[status(esa)],[c_1]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_1769,plain,
% 2.93/1.04      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.93/1.04      | v1_relat_1(sK4) ),
% 2.93/1.04      inference(instantiation,[status(thm)],[c_1307]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_1770,plain,
% 2.93/1.04      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 2.93/1.04      | v1_relat_1(sK4) = iProver_top ),
% 2.93/1.04      inference(predicate_to_equality,[status(thm)],[c_1769]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_2596,plain,
% 2.93/1.04      ( v1_relat_1(X0_47) != iProver_top
% 2.93/1.04      | sK2 = k1_xboole_0
% 2.93/1.04      | r2_hidden(sK0(X0_47,sK4),k1_relat_1(X0_47)) = iProver_top
% 2.93/1.04      | r1_partfun1(X0_47,sK4) = iProver_top
% 2.93/1.04      | m1_subset_1(k1_relat_1(X0_47),k1_zfmisc_1(sK1)) != iProver_top
% 2.93/1.04      | v1_funct_1(X0_47) != iProver_top ),
% 2.93/1.04      inference(global_propositional_subsumption,
% 2.93/1.04                [status(thm)],
% 2.93/1.04                [c_2312,c_24,c_26,c_1770]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_2597,plain,
% 2.93/1.04      ( sK2 = k1_xboole_0
% 2.93/1.04      | r2_hidden(sK0(X0_47,sK4),k1_relat_1(X0_47)) = iProver_top
% 2.93/1.04      | r1_partfun1(X0_47,sK4) = iProver_top
% 2.93/1.04      | m1_subset_1(k1_relat_1(X0_47),k1_zfmisc_1(sK1)) != iProver_top
% 2.93/1.04      | v1_funct_1(X0_47) != iProver_top
% 2.93/1.04      | v1_relat_1(X0_47) != iProver_top ),
% 2.93/1.04      inference(renaming,[status(thm)],[c_2596]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_20,negated_conjecture,
% 2.93/1.04      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 2.93/1.04      inference(cnf_transformation,[],[f46]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_1298,negated_conjecture,
% 2.93/1.04      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 2.93/1.04      inference(subtyping,[status(esa)],[c_20]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_1624,plain,
% 2.93/1.04      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 2.93/1.04      inference(predicate_to_equality,[status(thm)],[c_1298]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_1926,plain,
% 2.93/1.04      ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
% 2.93/1.04      inference(superposition,[status(thm)],[c_1624,c_1618]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_15,negated_conjecture,
% 2.93/1.04      ( ~ r2_hidden(X0,k1_relset_1(sK1,sK2,sK3))
% 2.93/1.04      | r1_partfun1(sK3,sK4)
% 2.93/1.04      | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0) ),
% 2.93/1.04      inference(cnf_transformation,[],[f51]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_1302,negated_conjecture,
% 2.93/1.04      ( ~ r2_hidden(X0_49,k1_relset_1(sK1,sK2,sK3))
% 2.93/1.04      | r1_partfun1(sK3,sK4)
% 2.93/1.04      | k1_funct_1(sK3,X0_49) = k1_funct_1(sK4,X0_49) ),
% 2.93/1.04      inference(subtyping,[status(esa)],[c_15]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_1621,plain,
% 2.93/1.04      ( k1_funct_1(sK3,X0_49) = k1_funct_1(sK4,X0_49)
% 2.93/1.04      | r2_hidden(X0_49,k1_relset_1(sK1,sK2,sK3)) != iProver_top
% 2.93/1.04      | r1_partfun1(sK3,sK4) = iProver_top ),
% 2.93/1.04      inference(predicate_to_equality,[status(thm)],[c_1302]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_2157,plain,
% 2.93/1.04      ( k1_funct_1(sK4,X0_49) = k1_funct_1(sK3,X0_49)
% 2.93/1.04      | r2_hidden(X0_49,k1_relat_1(sK3)) != iProver_top
% 2.93/1.04      | r1_partfun1(sK3,sK4) = iProver_top ),
% 2.93/1.04      inference(demodulation,[status(thm)],[c_1926,c_1621]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_2609,plain,
% 2.93/1.04      ( k1_funct_1(sK3,sK0(sK3,sK4)) = k1_funct_1(sK4,sK0(sK3,sK4))
% 2.93/1.04      | sK2 = k1_xboole_0
% 2.93/1.04      | r1_partfun1(sK3,sK4) = iProver_top
% 2.93/1.04      | m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK1)) != iProver_top
% 2.93/1.04      | v1_funct_1(sK3) != iProver_top
% 2.93/1.04      | v1_relat_1(sK3) != iProver_top ),
% 2.93/1.04      inference(superposition,[status(thm)],[c_2597,c_2157]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_21,negated_conjecture,
% 2.93/1.04      ( v1_funct_1(sK3) ),
% 2.93/1.04      inference(cnf_transformation,[],[f45]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_22,plain,
% 2.93/1.04      ( v1_funct_1(sK3) = iProver_top ),
% 2.93/1.04      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_23,plain,
% 2.93/1.04      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 2.93/1.04      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_1772,plain,
% 2.93/1.04      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.93/1.04      | v1_relat_1(sK3) ),
% 2.93/1.04      inference(instantiation,[status(thm)],[c_1307]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_1773,plain,
% 2.93/1.04      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 2.93/1.04      | v1_relat_1(sK3) = iProver_top ),
% 2.93/1.04      inference(predicate_to_equality,[status(thm)],[c_1772]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_2,plain,
% 2.93/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.93/1.04      | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 2.93/1.04      inference(cnf_transformation,[],[f34]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_1306,plain,
% 2.93/1.04      ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
% 2.93/1.04      | m1_subset_1(k1_relset_1(X1_47,X2_47,X0_47),k1_zfmisc_1(X1_47)) ),
% 2.93/1.04      inference(subtyping,[status(esa)],[c_2]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_1617,plain,
% 2.93/1.04      ( m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47))) != iProver_top
% 2.93/1.04      | m1_subset_1(k1_relset_1(X1_47,X2_47,X0_47),k1_zfmisc_1(X1_47)) = iProver_top ),
% 2.93/1.04      inference(predicate_to_equality,[status(thm)],[c_1306]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_2173,plain,
% 2.93/1.04      ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK1)) = iProver_top
% 2.93/1.04      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
% 2.93/1.04      inference(superposition,[status(thm)],[c_1926,c_1617]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_2686,plain,
% 2.93/1.04      ( r1_partfun1(sK3,sK4) = iProver_top
% 2.93/1.04      | sK2 = k1_xboole_0
% 2.93/1.04      | k1_funct_1(sK3,sK0(sK3,sK4)) = k1_funct_1(sK4,sK0(sK3,sK4)) ),
% 2.93/1.04      inference(global_propositional_subsumption,
% 2.93/1.04                [status(thm)],
% 2.93/1.04                [c_2609,c_22,c_23,c_1773,c_2173]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_2687,plain,
% 2.93/1.04      ( k1_funct_1(sK3,sK0(sK3,sK4)) = k1_funct_1(sK4,sK0(sK3,sK4))
% 2.93/1.04      | sK2 = k1_xboole_0
% 2.93/1.04      | r1_partfun1(sK3,sK4) = iProver_top ),
% 2.93/1.04      inference(renaming,[status(thm)],[c_2686]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_14,negated_conjecture,
% 2.93/1.04      ( r2_hidden(sK5,k1_relset_1(sK1,sK2,sK3))
% 2.93/1.04      | ~ r1_partfun1(sK3,sK4) ),
% 2.93/1.04      inference(cnf_transformation,[],[f52]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_1303,negated_conjecture,
% 2.93/1.04      ( r2_hidden(sK5,k1_relset_1(sK1,sK2,sK3))
% 2.93/1.04      | ~ r1_partfun1(sK3,sK4) ),
% 2.93/1.04      inference(subtyping,[status(esa)],[c_14]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_1620,plain,
% 2.93/1.04      ( r2_hidden(sK5,k1_relset_1(sK1,sK2,sK3)) = iProver_top
% 2.93/1.04      | r1_partfun1(sK3,sK4) != iProver_top ),
% 2.93/1.04      inference(predicate_to_equality,[status(thm)],[c_1303]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_2158,plain,
% 2.93/1.04      ( r2_hidden(sK5,k1_relat_1(sK3)) = iProver_top
% 2.93/1.04      | r1_partfun1(sK3,sK4) != iProver_top ),
% 2.93/1.04      inference(demodulation,[status(thm)],[c_1926,c_1620]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_2381,plain,
% 2.93/1.04      ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK1)) = iProver_top ),
% 2.93/1.04      inference(global_propositional_subsumption,
% 2.93/1.04                [status(thm)],
% 2.93/1.04                [c_2173,c_23]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_1628,plain,
% 2.93/1.04      ( k1_funct_1(X0_47,X0_49) = k1_funct_1(X1_47,X0_49)
% 2.93/1.04      | r2_hidden(X0_49,k1_relat_1(X0_47)) != iProver_top
% 2.93/1.04      | r1_partfun1(X0_47,X1_47) != iProver_top
% 2.93/1.04      | m1_subset_1(k1_relat_1(X0_47),k1_zfmisc_1(k1_relat_1(X1_47))) != iProver_top
% 2.93/1.04      | v1_funct_1(X0_47) != iProver_top
% 2.93/1.04      | v1_funct_1(X1_47) != iProver_top
% 2.93/1.04      | v1_relat_1(X0_47) != iProver_top
% 2.93/1.04      | v1_relat_1(X1_47) != iProver_top ),
% 2.93/1.04      inference(predicate_to_equality,[status(thm)],[c_1294]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_2963,plain,
% 2.93/1.04      ( k1_funct_1(X0_47,X0_49) = k1_funct_1(sK4,X0_49)
% 2.93/1.04      | sK2 = k1_xboole_0
% 2.93/1.04      | r2_hidden(X0_49,k1_relat_1(X0_47)) != iProver_top
% 2.93/1.04      | r1_partfun1(X0_47,sK4) != iProver_top
% 2.93/1.04      | m1_subset_1(k1_relat_1(X0_47),k1_zfmisc_1(sK1)) != iProver_top
% 2.93/1.04      | v1_funct_1(X0_47) != iProver_top
% 2.93/1.04      | v1_funct_1(sK4) != iProver_top
% 2.93/1.04      | v1_relat_1(X0_47) != iProver_top
% 2.93/1.04      | v1_relat_1(sK4) != iProver_top ),
% 2.93/1.04      inference(superposition,[status(thm)],[c_2144,c_1628]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_3065,plain,
% 2.93/1.04      ( v1_relat_1(X0_47) != iProver_top
% 2.93/1.04      | k1_funct_1(X0_47,X0_49) = k1_funct_1(sK4,X0_49)
% 2.93/1.04      | sK2 = k1_xboole_0
% 2.93/1.04      | r2_hidden(X0_49,k1_relat_1(X0_47)) != iProver_top
% 2.93/1.04      | r1_partfun1(X0_47,sK4) != iProver_top
% 2.93/1.04      | m1_subset_1(k1_relat_1(X0_47),k1_zfmisc_1(sK1)) != iProver_top
% 2.93/1.04      | v1_funct_1(X0_47) != iProver_top ),
% 2.93/1.04      inference(global_propositional_subsumption,
% 2.93/1.04                [status(thm)],
% 2.93/1.04                [c_2963,c_24,c_26,c_1770]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_3066,plain,
% 2.93/1.04      ( k1_funct_1(X0_47,X0_49) = k1_funct_1(sK4,X0_49)
% 2.93/1.04      | sK2 = k1_xboole_0
% 2.93/1.04      | r2_hidden(X0_49,k1_relat_1(X0_47)) != iProver_top
% 2.93/1.04      | r1_partfun1(X0_47,sK4) != iProver_top
% 2.93/1.04      | m1_subset_1(k1_relat_1(X0_47),k1_zfmisc_1(sK1)) != iProver_top
% 2.93/1.04      | v1_funct_1(X0_47) != iProver_top
% 2.93/1.04      | v1_relat_1(X0_47) != iProver_top ),
% 2.93/1.04      inference(renaming,[status(thm)],[c_3065]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_3079,plain,
% 2.93/1.04      ( k1_funct_1(sK4,X0_49) = k1_funct_1(sK3,X0_49)
% 2.93/1.04      | sK2 = k1_xboole_0
% 2.93/1.04      | r2_hidden(X0_49,k1_relat_1(sK3)) != iProver_top
% 2.93/1.04      | r1_partfun1(sK3,sK4) != iProver_top
% 2.93/1.04      | v1_funct_1(sK3) != iProver_top
% 2.93/1.04      | v1_relat_1(sK3) != iProver_top ),
% 2.93/1.04      inference(superposition,[status(thm)],[c_2381,c_3066]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_3097,plain,
% 2.93/1.04      ( r2_hidden(X0_49,k1_relat_1(sK3)) != iProver_top
% 2.93/1.04      | sK2 = k1_xboole_0
% 2.93/1.04      | k1_funct_1(sK4,X0_49) = k1_funct_1(sK3,X0_49) ),
% 2.93/1.04      inference(global_propositional_subsumption,
% 2.93/1.04                [status(thm)],
% 2.93/1.04                [c_3079,c_22,c_23,c_1773,c_2157]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_3098,plain,
% 2.93/1.04      ( k1_funct_1(sK4,X0_49) = k1_funct_1(sK3,X0_49)
% 2.93/1.04      | sK2 = k1_xboole_0
% 2.93/1.04      | r2_hidden(X0_49,k1_relat_1(sK3)) != iProver_top ),
% 2.93/1.04      inference(renaming,[status(thm)],[c_3097]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_3107,plain,
% 2.93/1.04      ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
% 2.93/1.04      | sK2 = k1_xboole_0
% 2.93/1.04      | r1_partfun1(sK3,sK4) != iProver_top ),
% 2.93/1.04      inference(superposition,[status(thm)],[c_2158,c_3098]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_3188,plain,
% 2.93/1.04      ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
% 2.93/1.04      | k1_funct_1(sK3,sK0(sK3,sK4)) = k1_funct_1(sK4,sK0(sK3,sK4))
% 2.93/1.04      | sK2 = k1_xboole_0 ),
% 2.93/1.04      inference(superposition,[status(thm)],[c_2687,c_3107]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_10,plain,
% 2.93/1.04      ( r1_partfun1(X0,X1)
% 2.93/1.04      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 2.93/1.04      | ~ v1_funct_1(X1)
% 2.93/1.04      | ~ v1_funct_1(X0)
% 2.93/1.04      | ~ v1_relat_1(X1)
% 2.93/1.04      | ~ v1_relat_1(X0)
% 2.93/1.04      | k1_funct_1(X1,sK0(X0,X1)) != k1_funct_1(X0,sK0(X0,X1)) ),
% 2.93/1.04      inference(cnf_transformation,[],[f44]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_264,plain,
% 2.93/1.04      ( r1_partfun1(X0,X1)
% 2.93/1.04      | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
% 2.93/1.04      | ~ v1_funct_1(X0)
% 2.93/1.04      | ~ v1_funct_1(X1)
% 2.93/1.04      | ~ v1_relat_1(X0)
% 2.93/1.04      | ~ v1_relat_1(X1)
% 2.93/1.04      | k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1))
% 2.93/1.04      | k1_relat_1(X1) != X3
% 2.93/1.04      | k1_relat_1(X0) != X2 ),
% 2.93/1.04      inference(resolution_lifted,[status(thm)],[c_0,c_10]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_265,plain,
% 2.93/1.04      ( r1_partfun1(X0,X1)
% 2.93/1.04      | ~ m1_subset_1(k1_relat_1(X0),k1_zfmisc_1(k1_relat_1(X1)))
% 2.93/1.04      | ~ v1_funct_1(X1)
% 2.93/1.04      | ~ v1_funct_1(X0)
% 2.93/1.04      | ~ v1_relat_1(X1)
% 2.93/1.04      | ~ v1_relat_1(X0)
% 2.93/1.04      | k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1)) ),
% 2.93/1.04      inference(unflattening,[status(thm)],[c_264]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_1295,plain,
% 2.93/1.04      ( r1_partfun1(X0_47,X1_47)
% 2.93/1.04      | ~ m1_subset_1(k1_relat_1(X0_47),k1_zfmisc_1(k1_relat_1(X1_47)))
% 2.93/1.04      | ~ v1_funct_1(X1_47)
% 2.93/1.04      | ~ v1_funct_1(X0_47)
% 2.93/1.04      | ~ v1_relat_1(X1_47)
% 2.93/1.04      | ~ v1_relat_1(X0_47)
% 2.93/1.04      | k1_funct_1(X0_47,sK0(X0_47,X1_47)) != k1_funct_1(X1_47,sK0(X0_47,X1_47)) ),
% 2.93/1.04      inference(subtyping,[status(esa)],[c_265]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_1627,plain,
% 2.93/1.04      ( k1_funct_1(X0_47,sK0(X0_47,X1_47)) != k1_funct_1(X1_47,sK0(X0_47,X1_47))
% 2.93/1.04      | r1_partfun1(X0_47,X1_47) = iProver_top
% 2.93/1.04      | m1_subset_1(k1_relat_1(X0_47),k1_zfmisc_1(k1_relat_1(X1_47))) != iProver_top
% 2.93/1.04      | v1_funct_1(X0_47) != iProver_top
% 2.93/1.04      | v1_funct_1(X1_47) != iProver_top
% 2.93/1.04      | v1_relat_1(X0_47) != iProver_top
% 2.93/1.04      | v1_relat_1(X1_47) != iProver_top ),
% 2.93/1.04      inference(predicate_to_equality,[status(thm)],[c_1295]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_3363,plain,
% 2.93/1.04      ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
% 2.93/1.04      | sK2 = k1_xboole_0
% 2.93/1.04      | r1_partfun1(sK3,sK4) = iProver_top
% 2.93/1.04      | m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(k1_relat_1(sK4))) != iProver_top
% 2.93/1.04      | v1_funct_1(sK4) != iProver_top
% 2.93/1.04      | v1_funct_1(sK3) != iProver_top
% 2.93/1.04      | v1_relat_1(sK4) != iProver_top
% 2.93/1.04      | v1_relat_1(sK3) != iProver_top ),
% 2.93/1.04      inference(superposition,[status(thm)],[c_3188,c_1627]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_1827,plain,
% 2.93/1.04      ( r1_partfun1(X0_47,sK4)
% 2.93/1.04      | ~ m1_subset_1(k1_relat_1(X0_47),k1_zfmisc_1(k1_relat_1(sK4)))
% 2.93/1.04      | ~ v1_funct_1(X0_47)
% 2.93/1.04      | ~ v1_funct_1(sK4)
% 2.93/1.04      | ~ v1_relat_1(X0_47)
% 2.93/1.04      | ~ v1_relat_1(sK4)
% 2.93/1.04      | k1_funct_1(X0_47,sK0(X0_47,sK4)) != k1_funct_1(sK4,sK0(X0_47,sK4)) ),
% 2.93/1.04      inference(instantiation,[status(thm)],[c_1295]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_1887,plain,
% 2.93/1.04      ( r1_partfun1(sK3,sK4)
% 2.93/1.04      | ~ m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(k1_relat_1(sK4)))
% 2.93/1.04      | ~ v1_funct_1(sK4)
% 2.93/1.04      | ~ v1_funct_1(sK3)
% 2.93/1.04      | ~ v1_relat_1(sK4)
% 2.93/1.04      | ~ v1_relat_1(sK3)
% 2.93/1.04      | k1_funct_1(sK3,sK0(sK3,sK4)) != k1_funct_1(sK4,sK0(sK3,sK4)) ),
% 2.93/1.04      inference(instantiation,[status(thm)],[c_1827]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_1888,plain,
% 2.93/1.04      ( k1_funct_1(sK3,sK0(sK3,sK4)) != k1_funct_1(sK4,sK0(sK3,sK4))
% 2.93/1.04      | r1_partfun1(sK3,sK4) = iProver_top
% 2.93/1.04      | m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(k1_relat_1(sK4))) != iProver_top
% 2.93/1.04      | v1_funct_1(sK4) != iProver_top
% 2.93/1.04      | v1_funct_1(sK3) != iProver_top
% 2.93/1.04      | v1_relat_1(sK4) != iProver_top
% 2.93/1.04      | v1_relat_1(sK3) != iProver_top ),
% 2.93/1.04      inference(predicate_to_equality,[status(thm)],[c_1887]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_3366,plain,
% 2.93/1.04      ( sK2 = k1_xboole_0
% 2.93/1.04      | r1_partfun1(sK3,sK4) = iProver_top
% 2.93/1.04      | m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(k1_relat_1(sK4))) != iProver_top ),
% 2.93/1.04      inference(global_propositional_subsumption,
% 2.93/1.04                [status(thm)],
% 2.93/1.04                [c_3363,c_22,c_23,c_24,c_26,c_1770,c_1773,c_1888,c_2173,
% 2.93/1.04                 c_2609]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_3373,plain,
% 2.93/1.04      ( sK2 = k1_xboole_0
% 2.93/1.04      | r1_partfun1(sK3,sK4) = iProver_top
% 2.93/1.04      | m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK1)) != iProver_top ),
% 2.93/1.04      inference(superposition,[status(thm)],[c_2144,c_3366]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_3459,plain,
% 2.93/1.04      ( r1_partfun1(sK3,sK4) = iProver_top | sK2 = k1_xboole_0 ),
% 2.93/1.04      inference(global_propositional_subsumption,
% 2.93/1.04                [status(thm)],
% 2.93/1.04                [c_3373,c_23,c_2173]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_3460,plain,
% 2.93/1.04      ( sK2 = k1_xboole_0 | r1_partfun1(sK3,sK4) = iProver_top ),
% 2.93/1.04      inference(renaming,[status(thm)],[c_3459]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_3465,plain,
% 2.93/1.04      ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5) | sK2 = k1_xboole_0 ),
% 2.93/1.04      inference(superposition,[status(thm)],[c_3460,c_3107]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_13,negated_conjecture,
% 2.93/1.04      ( ~ r1_partfun1(sK3,sK4)
% 2.93/1.04      | k1_funct_1(sK3,sK5) != k1_funct_1(sK4,sK5) ),
% 2.93/1.04      inference(cnf_transformation,[],[f53]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_1304,negated_conjecture,
% 2.93/1.04      ( ~ r1_partfun1(sK3,sK4)
% 2.93/1.04      | k1_funct_1(sK3,sK5) != k1_funct_1(sK4,sK5) ),
% 2.93/1.04      inference(subtyping,[status(esa)],[c_13]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_1619,plain,
% 2.93/1.04      ( k1_funct_1(sK3,sK5) != k1_funct_1(sK4,sK5)
% 2.93/1.04      | r1_partfun1(sK3,sK4) != iProver_top ),
% 2.93/1.04      inference(predicate_to_equality,[status(thm)],[c_1304]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_3468,plain,
% 2.93/1.04      ( sK2 = k1_xboole_0 | r1_partfun1(sK3,sK4) != iProver_top ),
% 2.93/1.04      inference(superposition,[status(thm)],[c_3465,c_1619]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_3489,plain,
% 2.93/1.04      ( sK2 = k1_xboole_0 ),
% 2.93/1.04      inference(global_propositional_subsumption,
% 2.93/1.04                [status(thm)],
% 2.93/1.04                [c_3468,c_23,c_2173,c_3373]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_8,plain,
% 2.93/1.04      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 2.93/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.93/1.04      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 2.93/1.04      inference(cnf_transformation,[],[f58]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_510,plain,
% 2.93/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.93/1.04      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 2.93/1.04      | sK2 != X1
% 2.93/1.04      | sK1 != k1_xboole_0
% 2.93/1.04      | sK4 != X0 ),
% 2.93/1.04      inference(resolution_lifted,[status(thm)],[c_8,c_18]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_511,plain,
% 2.93/1.04      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
% 2.93/1.04      | k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
% 2.93/1.04      | sK1 != k1_xboole_0 ),
% 2.93/1.04      inference(unflattening,[status(thm)],[c_510]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_1292,plain,
% 2.93/1.04      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
% 2.93/1.04      | k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
% 2.93/1.04      | sK1 != k1_xboole_0 ),
% 2.93/1.04      inference(subtyping,[status(esa)],[c_511]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_1630,plain,
% 2.93/1.04      ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
% 2.93/1.04      | sK1 != k1_xboole_0
% 2.93/1.04      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
% 2.93/1.04      inference(predicate_to_equality,[status(thm)],[c_1292]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_3497,plain,
% 2.93/1.04      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
% 2.93/1.04      | sK1 != k1_xboole_0
% 2.93/1.04      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 2.93/1.04      inference(demodulation,[status(thm)],[c_3489,c_1630]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_16,negated_conjecture,
% 2.93/1.04      ( k1_xboole_0 != sK2 | k1_xboole_0 = sK1 ),
% 2.93/1.04      inference(cnf_transformation,[],[f50]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_1301,negated_conjecture,
% 2.93/1.04      ( k1_xboole_0 != sK2 | k1_xboole_0 = sK1 ),
% 2.93/1.04      inference(subtyping,[status(esa)],[c_16]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_3503,plain,
% 2.93/1.04      ( sK1 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 2.93/1.04      inference(demodulation,[status(thm)],[c_3489,c_1301]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_3504,plain,
% 2.93/1.04      ( sK1 = k1_xboole_0 ),
% 2.93/1.04      inference(equality_resolution_simp,[status(thm)],[c_3503]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_3519,plain,
% 2.93/1.04      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
% 2.93/1.04      | k1_xboole_0 != k1_xboole_0
% 2.93/1.04      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 2.93/1.04      inference(light_normalisation,[status(thm)],[c_3497,c_3504]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_3520,plain,
% 2.93/1.04      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
% 2.93/1.04      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 2.93/1.04      inference(equality_resolution_simp,[status(thm)],[c_3519]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_3499,plain,
% 2.93/1.04      ( k1_relset_1(sK1,k1_xboole_0,sK4) = k1_relat_1(sK4) ),
% 2.93/1.04      inference(demodulation,[status(thm)],[c_3489,c_1925]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_3513,plain,
% 2.93/1.04      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_relat_1(sK4) ),
% 2.93/1.04      inference(light_normalisation,[status(thm)],[c_3499,c_3504]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_3521,plain,
% 2.93/1.04      ( k1_relat_1(sK4) = k1_xboole_0
% 2.93/1.04      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 2.93/1.04      inference(demodulation,[status(thm)],[c_3520,c_3513]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_3502,plain,
% 2.93/1.04      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top ),
% 2.93/1.04      inference(demodulation,[status(thm)],[c_3489,c_1622]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_3507,plain,
% 2.93/1.04      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 2.93/1.04      inference(light_normalisation,[status(thm)],[c_3502,c_3504]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_3524,plain,
% 2.93/1.04      ( k1_relat_1(sK4) = k1_xboole_0 ),
% 2.93/1.04      inference(forward_subsumption_resolution,
% 2.93/1.04                [status(thm)],
% 2.93/1.04                [c_3521,c_3507]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_4293,plain,
% 2.93/1.04      ( r2_hidden(sK0(X0_47,sK4),k1_relat_1(X0_47)) = iProver_top
% 2.93/1.04      | r1_partfun1(X0_47,sK4) = iProver_top
% 2.93/1.04      | m1_subset_1(k1_relat_1(X0_47),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.93/1.04      | v1_funct_1(X0_47) != iProver_top
% 2.93/1.04      | v1_funct_1(sK4) != iProver_top
% 2.93/1.04      | v1_relat_1(X0_47) != iProver_top
% 2.93/1.04      | v1_relat_1(sK4) != iProver_top ),
% 2.93/1.04      inference(superposition,[status(thm)],[c_3524,c_1626]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_5119,plain,
% 2.93/1.04      ( v1_relat_1(X0_47) != iProver_top
% 2.93/1.04      | r2_hidden(sK0(X0_47,sK4),k1_relat_1(X0_47)) = iProver_top
% 2.93/1.04      | r1_partfun1(X0_47,sK4) = iProver_top
% 2.93/1.04      | m1_subset_1(k1_relat_1(X0_47),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.93/1.04      | v1_funct_1(X0_47) != iProver_top ),
% 2.93/1.04      inference(global_propositional_subsumption,
% 2.93/1.04                [status(thm)],
% 2.93/1.04                [c_4293,c_24,c_26,c_1770]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_5120,plain,
% 2.93/1.04      ( r2_hidden(sK0(X0_47,sK4),k1_relat_1(X0_47)) = iProver_top
% 2.93/1.04      | r1_partfun1(X0_47,sK4) = iProver_top
% 2.93/1.04      | m1_subset_1(k1_relat_1(X0_47),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.93/1.04      | v1_funct_1(X0_47) != iProver_top
% 2.93/1.04      | v1_relat_1(X0_47) != iProver_top ),
% 2.93/1.04      inference(renaming,[status(thm)],[c_5119]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_3533,plain,
% 2.93/1.04      ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.93/1.04      inference(demodulation,[status(thm)],[c_3504,c_2381]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_4292,plain,
% 2.93/1.04      ( k1_funct_1(X0_47,X0_49) = k1_funct_1(sK4,X0_49)
% 2.93/1.04      | r2_hidden(X0_49,k1_relat_1(X0_47)) != iProver_top
% 2.93/1.04      | r1_partfun1(X0_47,sK4) != iProver_top
% 2.93/1.04      | m1_subset_1(k1_relat_1(X0_47),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.93/1.04      | v1_funct_1(X0_47) != iProver_top
% 2.93/1.04      | v1_funct_1(sK4) != iProver_top
% 2.93/1.04      | v1_relat_1(X0_47) != iProver_top
% 2.93/1.04      | v1_relat_1(sK4) != iProver_top ),
% 2.93/1.04      inference(superposition,[status(thm)],[c_3524,c_1628]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_4992,plain,
% 2.93/1.04      ( v1_relat_1(X0_47) != iProver_top
% 2.93/1.04      | k1_funct_1(X0_47,X0_49) = k1_funct_1(sK4,X0_49)
% 2.93/1.04      | r2_hidden(X0_49,k1_relat_1(X0_47)) != iProver_top
% 2.93/1.04      | r1_partfun1(X0_47,sK4) != iProver_top
% 2.93/1.04      | m1_subset_1(k1_relat_1(X0_47),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.93/1.04      | v1_funct_1(X0_47) != iProver_top ),
% 2.93/1.04      inference(global_propositional_subsumption,
% 2.93/1.04                [status(thm)],
% 2.93/1.04                [c_4292,c_24,c_26,c_1770]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_4993,plain,
% 2.93/1.04      ( k1_funct_1(X0_47,X0_49) = k1_funct_1(sK4,X0_49)
% 2.93/1.04      | r2_hidden(X0_49,k1_relat_1(X0_47)) != iProver_top
% 2.93/1.04      | r1_partfun1(X0_47,sK4) != iProver_top
% 2.93/1.04      | m1_subset_1(k1_relat_1(X0_47),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.93/1.04      | v1_funct_1(X0_47) != iProver_top
% 2.93/1.04      | v1_relat_1(X0_47) != iProver_top ),
% 2.93/1.04      inference(renaming,[status(thm)],[c_4992]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_5004,plain,
% 2.93/1.04      ( k1_funct_1(sK4,X0_49) = k1_funct_1(sK3,X0_49)
% 2.93/1.04      | r2_hidden(X0_49,k1_relat_1(sK3)) != iProver_top
% 2.93/1.04      | r1_partfun1(sK3,sK4) != iProver_top
% 2.93/1.04      | v1_funct_1(sK3) != iProver_top
% 2.93/1.04      | v1_relat_1(sK3) != iProver_top ),
% 2.93/1.04      inference(superposition,[status(thm)],[c_3533,c_4993]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_5020,plain,
% 2.93/1.04      ( r2_hidden(X0_49,k1_relat_1(sK3)) != iProver_top
% 2.93/1.04      | k1_funct_1(sK4,X0_49) = k1_funct_1(sK3,X0_49) ),
% 2.93/1.04      inference(global_propositional_subsumption,
% 2.93/1.04                [status(thm)],
% 2.93/1.04                [c_5004,c_22,c_23,c_1773,c_2157]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_5021,plain,
% 2.93/1.04      ( k1_funct_1(sK4,X0_49) = k1_funct_1(sK3,X0_49)
% 2.93/1.04      | r2_hidden(X0_49,k1_relat_1(sK3)) != iProver_top ),
% 2.93/1.04      inference(renaming,[status(thm)],[c_5020]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_5131,plain,
% 2.93/1.04      ( k1_funct_1(sK3,sK0(sK3,sK4)) = k1_funct_1(sK4,sK0(sK3,sK4))
% 2.93/1.04      | r1_partfun1(sK3,sK4) = iProver_top
% 2.93/1.04      | m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.93/1.04      | v1_funct_1(sK3) != iProver_top
% 2.93/1.04      | v1_relat_1(sK3) != iProver_top ),
% 2.93/1.04      inference(superposition,[status(thm)],[c_5120,c_5021]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_1790,plain,
% 2.93/1.04      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.93/1.04      | k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
% 2.93/1.04      inference(instantiation,[status(thm)],[c_1305]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_1793,plain,
% 2.93/1.04      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.93/1.04      | k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
% 2.93/1.04      inference(instantiation,[status(thm)],[c_1305]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_1799,plain,
% 2.93/1.04      ( m1_subset_1(k1_relset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1))
% 2.93/1.04      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 2.93/1.04      inference(instantiation,[status(thm)],[c_1306]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_1800,plain,
% 2.93/1.04      ( m1_subset_1(k1_relset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1)) = iProver_top
% 2.93/1.04      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
% 2.93/1.04      inference(predicate_to_equality,[status(thm)],[c_1799]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_1313,plain,
% 2.93/1.04      ( X0_47 != X1_47 | X2_47 != X1_47 | X2_47 = X0_47 ),
% 2.93/1.04      theory(equality) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_1785,plain,
% 2.93/1.04      ( sK1 != X0_47 | sK1 = k1_xboole_0 | k1_xboole_0 != X0_47 ),
% 2.93/1.04      inference(instantiation,[status(thm)],[c_1313]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_1896,plain,
% 2.93/1.04      ( sK1 != sK1 | sK1 = k1_xboole_0 | k1_xboole_0 != sK1 ),
% 2.93/1.04      inference(instantiation,[status(thm)],[c_1785]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_1309,plain,( X0_47 = X0_47 ),theory(equality) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_1897,plain,
% 2.93/1.04      ( sK1 = sK1 ),
% 2.93/1.04      inference(instantiation,[status(thm)],[c_1309]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_1315,plain,
% 2.93/1.04      ( k1_zfmisc_1(X0_47) = k1_zfmisc_1(X1_47) | X0_47 != X1_47 ),
% 2.93/1.04      theory(equality) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_1953,plain,
% 2.93/1.04      ( k1_zfmisc_1(X0_47) = k1_zfmisc_1(sK1) | X0_47 != sK1 ),
% 2.93/1.04      inference(instantiation,[status(thm)],[c_1315]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_1958,plain,
% 2.93/1.04      ( k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(sK1)
% 2.93/1.04      | k1_xboole_0 != sK1 ),
% 2.93/1.04      inference(instantiation,[status(thm)],[c_1953]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_1898,plain,
% 2.93/1.04      ( X0_47 != X1_47 | sK1 != X1_47 | sK1 = X0_47 ),
% 2.93/1.04      inference(instantiation,[status(thm)],[c_1313]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_2191,plain,
% 2.93/1.04      ( k1_relset_1(sK1,sK2,sK4) != X0_47
% 2.93/1.04      | sK1 != X0_47
% 2.93/1.04      | sK1 = k1_relset_1(sK1,sK2,sK4) ),
% 2.93/1.04      inference(instantiation,[status(thm)],[c_1898]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_2378,plain,
% 2.93/1.04      ( k1_relset_1(sK1,sK2,sK4) != k1_relat_1(sK4)
% 2.93/1.04      | sK1 = k1_relset_1(sK1,sK2,sK4)
% 2.93/1.04      | sK1 != k1_relat_1(sK4) ),
% 2.93/1.04      inference(instantiation,[status(thm)],[c_2191]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_2400,plain,
% 2.93/1.04      ( k1_relat_1(sK4) != X0_47 | sK1 != X0_47 | sK1 = k1_relat_1(sK4) ),
% 2.93/1.04      inference(instantiation,[status(thm)],[c_1898]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_2401,plain,
% 2.93/1.04      ( k1_relat_1(sK4) != k1_xboole_0
% 2.93/1.04      | sK1 = k1_relat_1(sK4)
% 2.93/1.04      | sK1 != k1_xboole_0 ),
% 2.93/1.04      inference(instantiation,[status(thm)],[c_2400]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_5,plain,
% 2.93/1.04      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 2.93/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 2.93/1.04      | k1_xboole_0 = X1
% 2.93/1.04      | k1_xboole_0 = X0 ),
% 2.93/1.04      inference(cnf_transformation,[],[f56]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_490,plain,
% 2.93/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 2.93/1.04      | sK2 != k1_xboole_0
% 2.93/1.04      | sK1 != X1
% 2.93/1.04      | sK4 != X0
% 2.93/1.04      | k1_xboole_0 = X0
% 2.93/1.04      | k1_xboole_0 = X1 ),
% 2.93/1.04      inference(resolution_lifted,[status(thm)],[c_5,c_18]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_491,plain,
% 2.93/1.04      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
% 2.93/1.04      | sK2 != k1_xboole_0
% 2.93/1.04      | k1_xboole_0 = sK1
% 2.93/1.04      | k1_xboole_0 = sK4 ),
% 2.93/1.04      inference(unflattening,[status(thm)],[c_490]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_1293,plain,
% 2.93/1.04      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
% 2.93/1.04      | sK2 != k1_xboole_0
% 2.93/1.04      | k1_xboole_0 = sK1
% 2.93/1.04      | k1_xboole_0 = sK4 ),
% 2.93/1.04      inference(subtyping,[status(esa)],[c_491]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_1629,plain,
% 2.93/1.04      ( sK2 != k1_xboole_0
% 2.93/1.04      | k1_xboole_0 = sK1
% 2.93/1.04      | k1_xboole_0 = sK4
% 2.93/1.04      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
% 2.93/1.04      inference(predicate_to_equality,[status(thm)],[c_1293]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_1332,plain,
% 2.93/1.04      ( k1_xboole_0 = k1_xboole_0 ),
% 2.93/1.04      inference(instantiation,[status(thm)],[c_1309]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_2298,plain,
% 2.93/1.04      ( sK2 != X0_47 | k1_xboole_0 != X0_47 | k1_xboole_0 = sK2 ),
% 2.93/1.04      inference(instantiation,[status(thm)],[c_1313]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_2299,plain,
% 2.93/1.04      ( sK2 != k1_xboole_0
% 2.93/1.04      | k1_xboole_0 = sK2
% 2.93/1.04      | k1_xboole_0 != k1_xboole_0 ),
% 2.93/1.04      inference(instantiation,[status(thm)],[c_2298]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_2421,plain,
% 2.93/1.04      ( sK2 != k1_xboole_0 | k1_xboole_0 = sK1 ),
% 2.93/1.04      inference(global_propositional_subsumption,
% 2.93/1.04                [status(thm)],
% 2.93/1.04                [c_1629,c_1332,c_1301,c_2299]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_2181,plain,
% 2.93/1.04      ( X0_47 != X1_47
% 2.93/1.04      | X0_47 = k1_relset_1(sK1,sK2,sK4)
% 2.93/1.04      | k1_relset_1(sK1,sK2,sK4) != X1_47 ),
% 2.93/1.04      inference(instantiation,[status(thm)],[c_1313]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_2554,plain,
% 2.93/1.04      ( X0_47 = k1_relset_1(sK1,sK2,sK4)
% 2.93/1.04      | X0_47 != k1_relat_1(sK4)
% 2.93/1.04      | k1_relset_1(sK1,sK2,sK4) != k1_relat_1(sK4) ),
% 2.93/1.04      inference(instantiation,[status(thm)],[c_2181]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_2702,plain,
% 2.93/1.04      ( k1_relset_1(sK1,sK2,sK4) != k1_relat_1(sK4)
% 2.93/1.04      | k1_relat_1(sK4) = k1_relset_1(sK1,sK2,sK4)
% 2.93/1.04      | k1_relat_1(sK4) != k1_relat_1(sK4) ),
% 2.93/1.04      inference(instantiation,[status(thm)],[c_2554]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_2703,plain,
% 2.93/1.04      ( k1_relat_1(sK4) = k1_relat_1(sK4) ),
% 2.93/1.04      inference(instantiation,[status(thm)],[c_1309]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_2253,plain,
% 2.93/1.04      ( X0_47 != X1_47
% 2.93/1.04      | X0_47 = k1_relset_1(sK1,sK2,sK3)
% 2.93/1.04      | k1_relset_1(sK1,sK2,sK3) != X1_47 ),
% 2.93/1.04      inference(instantiation,[status(thm)],[c_1313]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_2583,plain,
% 2.93/1.04      ( X0_47 = k1_relset_1(sK1,sK2,sK3)
% 2.93/1.04      | X0_47 != k1_relat_1(sK3)
% 2.93/1.04      | k1_relset_1(sK1,sK2,sK3) != k1_relat_1(sK3) ),
% 2.93/1.04      inference(instantiation,[status(thm)],[c_2253]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_2709,plain,
% 2.93/1.04      ( k1_relset_1(sK1,sK2,sK3) != k1_relat_1(sK3)
% 2.93/1.04      | k1_relat_1(sK3) = k1_relset_1(sK1,sK2,sK3)
% 2.93/1.04      | k1_relat_1(sK3) != k1_relat_1(sK3) ),
% 2.93/1.04      inference(instantiation,[status(thm)],[c_2583]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_2710,plain,
% 2.93/1.04      ( k1_relat_1(sK3) = k1_relat_1(sK3) ),
% 2.93/1.04      inference(instantiation,[status(thm)],[c_1309]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_1316,plain,
% 2.93/1.04      ( ~ m1_subset_1(X0_47,X0_48)
% 2.93/1.04      | m1_subset_1(X1_47,X1_48)
% 2.93/1.04      | X1_48 != X0_48
% 2.93/1.04      | X1_47 != X0_47 ),
% 2.93/1.04      theory(equality) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_1842,plain,
% 2.93/1.04      ( m1_subset_1(X0_47,X0_48)
% 2.93/1.04      | ~ m1_subset_1(k1_relset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1))
% 2.93/1.04      | X0_48 != k1_zfmisc_1(sK1)
% 2.93/1.04      | X0_47 != k1_relset_1(sK1,sK2,sK3) ),
% 2.93/1.04      inference(instantiation,[status(thm)],[c_1316]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_2137,plain,
% 2.93/1.04      ( m1_subset_1(X0_47,k1_zfmisc_1(X1_47))
% 2.93/1.04      | ~ m1_subset_1(k1_relset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1))
% 2.93/1.04      | k1_zfmisc_1(X1_47) != k1_zfmisc_1(sK1)
% 2.93/1.04      | X0_47 != k1_relset_1(sK1,sK2,sK3) ),
% 2.93/1.04      inference(instantiation,[status(thm)],[c_1842]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_3138,plain,
% 2.93/1.04      ( ~ m1_subset_1(k1_relset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1))
% 2.93/1.04      | m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(X0_47))
% 2.93/1.04      | k1_zfmisc_1(X0_47) != k1_zfmisc_1(sK1)
% 2.93/1.04      | k1_relat_1(sK3) != k1_relset_1(sK1,sK2,sK3) ),
% 2.93/1.04      inference(instantiation,[status(thm)],[c_2137]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_3142,plain,
% 2.93/1.04      ( k1_zfmisc_1(X0_47) != k1_zfmisc_1(sK1)
% 2.93/1.04      | k1_relat_1(sK3) != k1_relset_1(sK1,sK2,sK3)
% 2.93/1.04      | m1_subset_1(k1_relset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1)) != iProver_top
% 2.93/1.04      | m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(X0_47)) = iProver_top ),
% 2.93/1.04      inference(predicate_to_equality,[status(thm)],[c_3138]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_3144,plain,
% 2.93/1.04      ( k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(sK1)
% 2.93/1.04      | k1_relat_1(sK3) != k1_relset_1(sK1,sK2,sK3)
% 2.93/1.04      | m1_subset_1(k1_relset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1)) != iProver_top
% 2.93/1.04      | m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.93/1.04      inference(instantiation,[status(thm)],[c_3142]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_2294,plain,
% 2.93/1.04      ( X0_47 != X1_47 | X0_47 = sK1 | sK1 != X1_47 ),
% 2.93/1.04      inference(instantiation,[status(thm)],[c_1313]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_2834,plain,
% 2.93/1.04      ( X0_47 != k1_relset_1(sK1,sK2,sK4)
% 2.93/1.04      | X0_47 = sK1
% 2.93/1.04      | sK1 != k1_relset_1(sK1,sK2,sK4) ),
% 2.93/1.04      inference(instantiation,[status(thm)],[c_2294]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_3233,plain,
% 2.93/1.04      ( k1_relat_1(sK4) != k1_relset_1(sK1,sK2,sK4)
% 2.93/1.04      | k1_relat_1(sK4) = sK1
% 2.93/1.04      | sK1 != k1_relset_1(sK1,sK2,sK4) ),
% 2.93/1.04      inference(instantiation,[status(thm)],[c_2834]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_4032,plain,
% 2.93/1.04      ( ~ m1_subset_1(k1_relset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1))
% 2.93/1.04      | m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(k1_relat_1(sK4)))
% 2.93/1.04      | k1_zfmisc_1(k1_relat_1(sK4)) != k1_zfmisc_1(sK1)
% 2.93/1.04      | k1_relat_1(sK3) != k1_relset_1(sK1,sK2,sK3) ),
% 2.93/1.04      inference(instantiation,[status(thm)],[c_3138]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_4033,plain,
% 2.93/1.04      ( k1_zfmisc_1(k1_relat_1(sK4)) != k1_zfmisc_1(sK1)
% 2.93/1.04      | k1_relat_1(sK3) != k1_relset_1(sK1,sK2,sK3)
% 2.93/1.04      | m1_subset_1(k1_relset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1)) != iProver_top
% 2.93/1.04      | m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(k1_relat_1(sK4))) = iProver_top ),
% 2.93/1.04      inference(predicate_to_equality,[status(thm)],[c_4032]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_4705,plain,
% 2.93/1.04      ( k1_zfmisc_1(k1_relat_1(sK4)) = k1_zfmisc_1(sK1)
% 2.93/1.04      | k1_relat_1(sK4) != sK1 ),
% 2.93/1.04      inference(instantiation,[status(thm)],[c_1953]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_5144,plain,
% 2.93/1.04      ( r1_partfun1(sK3,sK4) = iProver_top ),
% 2.93/1.04      inference(global_propositional_subsumption,
% 2.93/1.04                [status(thm)],
% 2.93/1.04                [c_5131,c_22,c_20,c_23,c_24,c_17,c_26,c_1770,c_1773,
% 2.93/1.04                 c_1790,c_1793,c_1800,c_1888,c_1896,c_1897,c_1958,c_2173,
% 2.93/1.04                 c_2378,c_2401,c_2421,c_2702,c_2703,c_2709,c_2710,c_3144,
% 2.93/1.04                 c_3233,c_3373,c_3468,c_3524,c_4033,c_4705]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_5146,plain,
% 2.93/1.04      ( r1_partfun1(sK3,sK4) ),
% 2.93/1.04      inference(predicate_to_equality_rev,[status(thm)],[c_5144]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_2172,plain,
% 2.93/1.04      ( r2_hidden(sK5,k1_relat_1(sK3)) | ~ r1_partfun1(sK3,sK4) ),
% 2.93/1.04      inference(predicate_to_equality_rev,[status(thm)],[c_2158]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(c_1341,plain,
% 2.93/1.04      ( k1_funct_1(sK3,sK5) != k1_funct_1(sK4,sK5)
% 2.93/1.04      | r1_partfun1(sK3,sK4) != iProver_top ),
% 2.93/1.04      inference(predicate_to_equality,[status(thm)],[c_1304]) ).
% 2.93/1.04  
% 2.93/1.04  cnf(contradiction,plain,
% 2.93/1.04      ( $false ),
% 2.93/1.04      inference(minisat,
% 2.93/1.04                [status(thm)],
% 2.93/1.04                [c_5264,c_5146,c_5144,c_4705,c_4032,c_3524,c_3489,c_3233,
% 2.93/1.04                 c_2710,c_2709,c_2703,c_2702,c_2421,c_2401,c_2378,c_2172,
% 2.93/1.04                 c_1897,c_1896,c_1799,c_1793,c_1790,c_1772,c_1769,c_1341,
% 2.93/1.04                 c_17,c_19,c_20,c_21]) ).
% 2.93/1.04  
% 2.93/1.04  
% 2.93/1.04  % SZS output end CNFRefutation for theBenchmark.p
% 2.93/1.04  
% 2.93/1.04  ------                               Statistics
% 2.93/1.04  
% 2.93/1.04  ------ General
% 2.93/1.04  
% 2.93/1.04  abstr_ref_over_cycles:                  0
% 2.93/1.04  abstr_ref_under_cycles:                 0
% 2.93/1.04  gc_basic_clause_elim:                   0
% 2.93/1.04  forced_gc_time:                         0
% 2.93/1.04  parsing_time:                           0.013
% 2.93/1.04  unif_index_cands_time:                  0.
% 2.93/1.04  unif_index_add_time:                    0.
% 2.93/1.04  orderings_time:                         0.
% 2.93/1.04  out_proof_time:                         0.013
% 2.93/1.04  total_time:                             0.224
% 2.93/1.04  num_of_symbols:                         54
% 2.93/1.04  num_of_terms:                           4661
% 2.93/1.04  
% 2.93/1.04  ------ Preprocessing
% 2.93/1.04  
% 2.93/1.04  num_of_splits:                          0
% 2.93/1.04  num_of_split_atoms:                     0
% 2.93/1.04  num_of_reused_defs:                     0
% 2.93/1.04  num_eq_ax_congr_red:                    12
% 2.93/1.04  num_of_sem_filtered_clauses:            1
% 2.93/1.04  num_of_subtypes:                        4
% 2.93/1.04  monotx_restored_types:                  0
% 2.93/1.04  sat_num_of_epr_types:                   0
% 2.93/1.04  sat_num_of_non_cyclic_types:            0
% 2.93/1.04  sat_guarded_non_collapsed_types:        0
% 2.93/1.04  num_pure_diseq_elim:                    0
% 2.93/1.04  simp_replaced_by:                       0
% 2.93/1.04  res_preprocessed:                       102
% 2.93/1.04  prep_upred:                             0
% 2.93/1.04  prep_unflattend:                        69
% 2.93/1.04  smt_new_axioms:                         0
% 2.93/1.04  pred_elim_cands:                        5
% 2.93/1.04  pred_elim:                              2
% 2.93/1.04  pred_elim_cl:                           5
% 2.93/1.04  pred_elim_cycles:                       6
% 2.93/1.04  merged_defs:                            0
% 2.93/1.04  merged_defs_ncl:                        0
% 2.93/1.04  bin_hyper_res:                          0
% 2.93/1.04  prep_cycles:                            4
% 2.93/1.04  pred_elim_time:                         0.025
% 2.93/1.04  splitting_time:                         0.
% 2.93/1.04  sem_filter_time:                        0.
% 2.93/1.04  monotx_time:                            0.
% 2.93/1.04  subtype_inf_time:                       0.
% 2.93/1.04  
% 2.93/1.04  ------ Problem properties
% 2.93/1.04  
% 2.93/1.04  clauses:                                17
% 2.93/1.04  conjectures:                            8
% 2.93/1.04  epr:                                    3
% 2.93/1.04  horn:                                   13
% 2.93/1.04  ground:                                 10
% 2.93/1.04  unary:                                  4
% 2.93/1.04  binary:                                 7
% 2.93/1.04  lits:                                   50
% 2.93/1.04  lits_eq:                                14
% 2.93/1.04  fd_pure:                                0
% 2.93/1.04  fd_pseudo:                              0
% 2.93/1.04  fd_cond:                                0
% 2.93/1.04  fd_pseudo_cond:                         0
% 2.93/1.04  ac_symbols:                             0
% 2.93/1.04  
% 2.93/1.04  ------ Propositional Solver
% 2.93/1.04  
% 2.93/1.04  prop_solver_calls:                      31
% 2.93/1.04  prop_fast_solver_calls:                 1183
% 2.93/1.04  smt_solver_calls:                       0
% 2.93/1.04  smt_fast_solver_calls:                  0
% 2.93/1.04  prop_num_of_clauses:                    1597
% 2.93/1.04  prop_preprocess_simplified:             4112
% 2.93/1.04  prop_fo_subsumed:                       71
% 2.93/1.04  prop_solver_time:                       0.
% 2.93/1.04  smt_solver_time:                        0.
% 2.93/1.04  smt_fast_solver_time:                   0.
% 2.93/1.04  prop_fast_solver_time:                  0.
% 2.93/1.04  prop_unsat_core_time:                   0.
% 2.93/1.04  
% 2.93/1.04  ------ QBF
% 2.93/1.04  
% 2.93/1.04  qbf_q_res:                              0
% 2.93/1.04  qbf_num_tautologies:                    0
% 2.93/1.04  qbf_prep_cycles:                        0
% 2.93/1.04  
% 2.93/1.04  ------ BMC1
% 2.93/1.04  
% 2.93/1.04  bmc1_current_bound:                     -1
% 2.93/1.04  bmc1_last_solved_bound:                 -1
% 2.93/1.04  bmc1_unsat_core_size:                   -1
% 2.93/1.04  bmc1_unsat_core_parents_size:           -1
% 2.93/1.04  bmc1_merge_next_fun:                    0
% 2.93/1.04  bmc1_unsat_core_clauses_time:           0.
% 2.93/1.04  
% 2.93/1.04  ------ Instantiation
% 2.93/1.04  
% 2.93/1.04  inst_num_of_clauses:                    539
% 2.93/1.04  inst_num_in_passive:                    264
% 2.93/1.04  inst_num_in_active:                     272
% 2.93/1.04  inst_num_in_unprocessed:                2
% 2.93/1.04  inst_num_of_loops:                      423
% 2.93/1.04  inst_num_of_learning_restarts:          0
% 2.93/1.04  inst_num_moves_active_passive:          143
% 2.93/1.04  inst_lit_activity:                      0
% 2.93/1.04  inst_lit_activity_moves:                0
% 2.93/1.04  inst_num_tautologies:                   0
% 2.93/1.04  inst_num_prop_implied:                  0
% 2.93/1.04  inst_num_existing_simplified:           0
% 2.93/1.04  inst_num_eq_res_simplified:             0
% 2.93/1.04  inst_num_child_elim:                    0
% 2.93/1.04  inst_num_of_dismatching_blockings:      159
% 2.93/1.04  inst_num_of_non_proper_insts:           573
% 2.93/1.04  inst_num_of_duplicates:                 0
% 2.93/1.04  inst_inst_num_from_inst_to_res:         0
% 2.93/1.04  inst_dismatching_checking_time:         0.
% 2.93/1.04  
% 2.93/1.04  ------ Resolution
% 2.93/1.04  
% 2.93/1.04  res_num_of_clauses:                     0
% 2.93/1.04  res_num_in_passive:                     0
% 2.93/1.04  res_num_in_active:                      0
% 2.93/1.04  res_num_of_loops:                       106
% 2.93/1.04  res_forward_subset_subsumed:            89
% 2.93/1.04  res_backward_subset_subsumed:           0
% 2.93/1.04  res_forward_subsumed:                   0
% 2.93/1.04  res_backward_subsumed:                  0
% 2.93/1.04  res_forward_subsumption_resolution:     0
% 2.93/1.04  res_backward_subsumption_resolution:    0
% 2.93/1.04  res_clause_to_clause_subsumption:       593
% 2.93/1.04  res_orphan_elimination:                 0
% 2.93/1.04  res_tautology_del:                      105
% 2.93/1.04  res_num_eq_res_simplified:              0
% 2.93/1.04  res_num_sel_changes:                    0
% 2.93/1.04  res_moves_from_active_to_pass:          0
% 2.93/1.04  
% 2.93/1.04  ------ Superposition
% 2.93/1.04  
% 2.93/1.04  sup_time_total:                         0.
% 2.93/1.04  sup_time_generating:                    0.
% 2.93/1.04  sup_time_sim_full:                      0.
% 2.93/1.04  sup_time_sim_immed:                     0.
% 2.93/1.04  
% 2.93/1.04  sup_num_of_clauses:                     56
% 2.93/1.04  sup_num_in_active:                      52
% 2.93/1.04  sup_num_in_passive:                     4
% 2.93/1.04  sup_num_of_loops:                       84
% 2.93/1.04  sup_fw_superposition:                   54
% 2.93/1.04  sup_bw_superposition:                   23
% 2.93/1.04  sup_immediate_simplified:               14
% 2.93/1.04  sup_given_eliminated:                   0
% 2.93/1.04  comparisons_done:                       0
% 2.93/1.04  comparisons_avoided:                    27
% 2.93/1.04  
% 2.93/1.04  ------ Simplifications
% 2.93/1.04  
% 2.93/1.04  
% 2.93/1.04  sim_fw_subset_subsumed:                 7
% 2.93/1.04  sim_bw_subset_subsumed:                 14
% 2.93/1.04  sim_fw_subsumed:                        0
% 2.93/1.04  sim_bw_subsumed:                        0
% 2.93/1.04  sim_fw_subsumption_res:                 1
% 2.93/1.04  sim_bw_subsumption_res:                 0
% 2.93/1.04  sim_tautology_del:                      1
% 2.93/1.04  sim_eq_tautology_del:                   9
% 2.93/1.04  sim_eq_res_simp:                        3
% 2.93/1.04  sim_fw_demodulated:                     1
% 2.93/1.04  sim_bw_demodulated:                     20
% 2.93/1.04  sim_light_normalised:                   7
% 2.93/1.04  sim_joinable_taut:                      0
% 2.93/1.04  sim_joinable_simp:                      0
% 2.93/1.04  sim_ac_normalised:                      0
% 2.93/1.04  sim_smt_subsumption:                    0
% 2.93/1.04  
%------------------------------------------------------------------------------
