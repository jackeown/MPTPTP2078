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
% DateTime   : Thu Dec  3 12:08:39 EST 2020

% Result     : Theorem 3.21s
% Output     : CNFRefutation 3.21s
% Verified   : 
% Statistics : Number of formulae       :  191 (92569 expanded)
%              Number of clauses        :  132 (24555 expanded)
%              Number of leaves         :   17 (22408 expanded)
%              Depth                    :   40
%              Number of atoms          :  766 (736667 expanded)
%              Number of equality atoms :  449 (250842 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,conjecture,(
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

fof(f10,negated_conjecture,(
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
    inference(negated_conjecture,[],[f9])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f33,plain,(
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
    inference(rectify,[],[f32])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
          & r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
     => ( k1_funct_1(X2,sK6) != k1_funct_1(X3,sK6)
        & r2_hidden(sK6,k1_relset_1(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
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
              ( k1_funct_1(sK5,X4) != k1_funct_1(X2,X4)
              & r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
          | ~ r1_partfun1(X2,sK5) )
        & ( ! [X5] :
              ( k1_funct_1(sK5,X5) = k1_funct_1(X2,X5)
              | ~ r2_hidden(X5,k1_relset_1(X0,X1,X2)) )
          | r1_partfun1(X2,sK5) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(sK5,X0,X1)
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
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
                ( k1_funct_1(sK4,X4) != k1_funct_1(X3,X4)
                & r2_hidden(X4,k1_relset_1(sK2,sK3,sK4)) )
            | ~ r1_partfun1(sK4,X3) )
          & ( ! [X5] :
                ( k1_funct_1(sK4,X5) = k1_funct_1(X3,X5)
                | ~ r2_hidden(X5,k1_relset_1(sK2,sK3,sK4)) )
            | r1_partfun1(sK4,X3) )
          & ( k1_xboole_0 = sK2
            | k1_xboole_0 != sK3 )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
          & v1_funct_2(X3,sK2,sK3)
          & v1_funct_1(X3) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ( ( k1_funct_1(sK4,sK6) != k1_funct_1(sK5,sK6)
        & r2_hidden(sK6,k1_relset_1(sK2,sK3,sK4)) )
      | ~ r1_partfun1(sK4,sK5) )
    & ( ! [X5] :
          ( k1_funct_1(sK4,X5) = k1_funct_1(sK5,X5)
          | ~ r2_hidden(X5,k1_relset_1(sK2,sK3,sK4)) )
      | r1_partfun1(sK4,sK5) )
    & ( k1_xboole_0 = sK2
      | k1_xboole_0 != sK3 )
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK5,sK2,sK3)
    & v1_funct_1(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f33,f36,f35,f34])).

fof(f58,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f37])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f7,axiom,(
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

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f57,plain,(
    v1_funct_2(sK5,sK2,sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f24])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f55,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f37])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f8,axiom,(
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

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1))
        & r2_hidden(sK1(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f28,f29])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_partfun1(X0,X1)
      | r2_hidden(sK1(X0,X1),k1_relat_1(X0))
      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f60,plain,(
    ! [X5] :
      ( k1_funct_1(sK4,X5) = k1_funct_1(sK5,X5)
      | ~ r2_hidden(X5,k1_relset_1(sK2,sK3,sK4))
      | r1_partfun1(sK4,sK5) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f54,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f37])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f56,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f37])).

fof(f61,plain,
    ( r2_hidden(sK6,k1_relset_1(sK2,sK3,sK4))
    | ~ r1_partfun1(sK4,sK5) ),
    inference(cnf_transformation,[],[f37])).

fof(f51,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ r1_partfun1(X0,X1)
      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f62,plain,
    ( k1_funct_1(sK4,sK6) != k1_funct_1(sK5,sK6)
    | ~ r1_partfun1(sK4,sK5) ),
    inference(cnf_transformation,[],[f37])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_partfun1(X0,X1)
      | k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1))
      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f59,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f37])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f67,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f46])).

fof(f2,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f40,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f13])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1818,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1825,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2469,plain,
    ( k1_relset_1(sK2,sK3,sK5) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_1818,c_1825])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_21,negated_conjecture,
    ( v1_funct_2(sK5,sK2,sK3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_555,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK3 != X2
    | sK2 != X1
    | sK5 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_21])).

cnf(c_556,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | k1_relset_1(sK2,sK3,sK5) = sK2
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_555])).

cnf(c_558,plain,
    ( k1_relset_1(sK2,sK3,sK5) = sK2
    | k1_xboole_0 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_556,c_20])).

cnf(c_2652,plain,
    ( k1_relat_1(sK5) = sK2
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2469,c_558])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1830,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1816,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2470,plain,
    ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1816,c_1825])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1826,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2762,plain,
    ( m1_subset_1(k1_relat_1(sK4),k1_zfmisc_1(sK2)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2470,c_1826])).

cnf(c_26,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3181,plain,
    ( m1_subset_1(k1_relat_1(sK4),k1_zfmisc_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2762,c_26])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1828,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3186,plain,
    ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(X0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3181,c_1828])).

cnf(c_3839,plain,
    ( r2_hidden(sK0(k1_relat_1(sK4),X0),sK2) = iProver_top
    | r1_tarski(k1_relat_1(sK4),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1830,c_3186])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1831,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4302,plain,
    ( r1_tarski(k1_relat_1(sK4),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3839,c_1831])).

cnf(c_14,plain,
    ( r1_partfun1(X0,X1)
    | r2_hidden(sK1(X0,X1),k1_relat_1(X0))
    | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1823,plain,
    ( r1_partfun1(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),k1_relat_1(X0)) = iProver_top
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_18,negated_conjecture,
    ( r1_partfun1(sK4,sK5)
    | ~ r2_hidden(X0,k1_relset_1(sK2,sK3,sK4))
    | k1_funct_1(sK4,X0) = k1_funct_1(sK5,X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1819,plain,
    ( k1_funct_1(sK4,X0) = k1_funct_1(sK5,X0)
    | r1_partfun1(sK4,sK5) = iProver_top
    | r2_hidden(X0,k1_relset_1(sK2,sK3,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2730,plain,
    ( k1_funct_1(sK5,X0) = k1_funct_1(sK4,X0)
    | r1_partfun1(sK4,sK5) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2470,c_1819])).

cnf(c_3002,plain,
    ( k1_funct_1(sK4,sK1(sK4,X0)) = k1_funct_1(sK5,sK1(sK4,X0))
    | r1_partfun1(sK4,X0) = iProver_top
    | r1_partfun1(sK4,sK5) = iProver_top
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1823,c_2730])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_25,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_2000,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2001,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2000])).

cnf(c_3933,plain,
    ( v1_relat_1(X0) != iProver_top
    | k1_funct_1(sK4,sK1(sK4,X0)) = k1_funct_1(sK5,sK1(sK4,X0))
    | r1_partfun1(sK4,X0) = iProver_top
    | r1_partfun1(sK4,sK5) = iProver_top
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3002,c_25,c_26,c_2001])).

cnf(c_3934,plain,
    ( k1_funct_1(sK4,sK1(sK4,X0)) = k1_funct_1(sK5,sK1(sK4,X0))
    | r1_partfun1(sK4,X0) = iProver_top
    | r1_partfun1(sK4,sK5) = iProver_top
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3933])).

cnf(c_3947,plain,
    ( k1_funct_1(sK4,sK1(sK4,sK5)) = k1_funct_1(sK5,sK1(sK4,sK5))
    | sK3 = k1_xboole_0
    | r1_partfun1(sK4,sK5) = iProver_top
    | r1_tarski(k1_relat_1(sK4),sK2) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2652,c_3934])).

cnf(c_22,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_27,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_29,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1997,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1998,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1997])).

cnf(c_3988,plain,
    ( k1_funct_1(sK4,sK1(sK4,sK5)) = k1_funct_1(sK5,sK1(sK4,sK5))
    | sK3 = k1_xboole_0
    | r1_partfun1(sK4,sK5) = iProver_top
    | r1_tarski(k1_relat_1(sK4),sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3947,c_27,c_29,c_1998])).

cnf(c_4376,plain,
    ( k1_funct_1(sK4,sK1(sK4,sK5)) = k1_funct_1(sK5,sK1(sK4,sK5))
    | sK3 = k1_xboole_0
    | r1_partfun1(sK4,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_4302,c_3988])).

cnf(c_17,negated_conjecture,
    ( ~ r1_partfun1(sK4,sK5)
    | r2_hidden(sK6,k1_relset_1(sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1820,plain,
    ( r1_partfun1(sK4,sK5) != iProver_top
    | r2_hidden(sK6,k1_relset_1(sK2,sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2731,plain,
    ( r1_partfun1(sK4,sK5) != iProver_top
    | r2_hidden(sK6,k1_relat_1(sK4)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2470,c_1820])).

cnf(c_15,plain,
    ( ~ r1_partfun1(X0,X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k1_funct_1(X1,X2) = k1_funct_1(X0,X2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1822,plain,
    ( k1_funct_1(X0,X1) = k1_funct_1(X2,X1)
    | r1_partfun1(X2,X0) != iProver_top
    | r2_hidden(X1,k1_relat_1(X2)) != iProver_top
    | r1_tarski(k1_relat_1(X2),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2880,plain,
    ( k1_funct_1(X0,X1) = k1_funct_1(sK5,X1)
    | sK3 = k1_xboole_0
    | r1_partfun1(X0,sK5) != iProver_top
    | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
    | r1_tarski(k1_relat_1(X0),sK2) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2652,c_1822])).

cnf(c_4042,plain,
    ( v1_relat_1(X0) != iProver_top
    | k1_funct_1(X0,X1) = k1_funct_1(sK5,X1)
    | sK3 = k1_xboole_0
    | r1_partfun1(X0,sK5) != iProver_top
    | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
    | r1_tarski(k1_relat_1(X0),sK2) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2880,c_27,c_29,c_1998])).

cnf(c_4043,plain,
    ( k1_funct_1(X0,X1) = k1_funct_1(sK5,X1)
    | sK3 = k1_xboole_0
    | r1_partfun1(X0,sK5) != iProver_top
    | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
    | r1_tarski(k1_relat_1(X0),sK2) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4042])).

cnf(c_4057,plain,
    ( k1_funct_1(sK5,sK6) = k1_funct_1(sK4,sK6)
    | sK3 = k1_xboole_0
    | r1_partfun1(sK4,sK5) != iProver_top
    | r1_tarski(k1_relat_1(sK4),sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2731,c_4043])).

cnf(c_4207,plain,
    ( k1_funct_1(sK5,sK6) = k1_funct_1(sK4,sK6)
    | sK3 = k1_xboole_0
    | r1_partfun1(sK4,sK5) != iProver_top
    | r1_tarski(k1_relat_1(sK4),sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4057,c_25,c_26,c_2001])).

cnf(c_4375,plain,
    ( k1_funct_1(sK5,sK6) = k1_funct_1(sK4,sK6)
    | sK3 = k1_xboole_0
    | r1_partfun1(sK4,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4302,c_4207])).

cnf(c_4709,plain,
    ( k1_funct_1(sK5,sK6) = k1_funct_1(sK4,sK6)
    | k1_funct_1(sK4,sK1(sK4,sK5)) = k1_funct_1(sK5,sK1(sK4,sK5))
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4376,c_4375])).

cnf(c_16,negated_conjecture,
    ( ~ r1_partfun1(sK4,sK5)
    | k1_funct_1(sK4,sK6) != k1_funct_1(sK5,sK6) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_34,plain,
    ( k1_funct_1(sK4,sK6) != k1_funct_1(sK5,sK6)
    | r1_partfun1(sK4,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1445,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2368,plain,
    ( k1_funct_1(sK5,sK6) != X0
    | k1_funct_1(sK4,sK6) != X0
    | k1_funct_1(sK4,sK6) = k1_funct_1(sK5,sK6) ),
    inference(instantiation,[status(thm)],[c_1445])).

cnf(c_2625,plain,
    ( k1_funct_1(sK5,sK6) != k1_funct_1(X0,sK6)
    | k1_funct_1(sK4,sK6) != k1_funct_1(X0,sK6)
    | k1_funct_1(sK4,sK6) = k1_funct_1(sK5,sK6) ),
    inference(instantiation,[status(thm)],[c_2368])).

cnf(c_6166,plain,
    ( k1_funct_1(sK5,sK6) != k1_funct_1(sK4,sK6)
    | k1_funct_1(sK4,sK6) = k1_funct_1(sK5,sK6)
    | k1_funct_1(sK4,sK6) != k1_funct_1(sK4,sK6) ),
    inference(instantiation,[status(thm)],[c_2625])).

cnf(c_1444,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_6167,plain,
    ( k1_funct_1(sK4,sK6) = k1_funct_1(sK4,sK6) ),
    inference(instantiation,[status(thm)],[c_1444])).

cnf(c_6287,plain,
    ( k1_funct_1(sK4,sK1(sK4,sK5)) = k1_funct_1(sK5,sK1(sK4,sK5))
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4709,c_34,c_3988,c_4302,c_6166,c_6167])).

cnf(c_13,plain,
    ( r1_partfun1(X0,X1)
    | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k1_funct_1(X1,sK1(X0,X1)) != k1_funct_1(X0,sK1(X0,X1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1824,plain,
    ( k1_funct_1(X0,sK1(X1,X0)) != k1_funct_1(X1,sK1(X1,X0))
    | r1_partfun1(X1,X0) = iProver_top
    | r1_tarski(k1_relat_1(X1),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_6291,plain,
    ( sK3 = k1_xboole_0
    | r1_partfun1(sK4,sK5) = iProver_top
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(sK5)) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK5) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6287,c_1824])).

cnf(c_4055,plain,
    ( k1_funct_1(X0,sK0(k1_relat_1(X0),X1)) = k1_funct_1(sK5,sK0(k1_relat_1(X0),X1))
    | sK3 = k1_xboole_0
    | r1_partfun1(X0,sK5) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | r1_tarski(k1_relat_1(X0),sK2) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1830,c_4043])).

cnf(c_5781,plain,
    ( k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0)) = k1_funct_1(sK5,sK0(k1_relat_1(sK4),X0))
    | sK3 = k1_xboole_0
    | r1_partfun1(sK4,sK5) != iProver_top
    | r1_tarski(k1_relat_1(sK4),X0) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4302,c_4055])).

cnf(c_6324,plain,
    ( r1_partfun1(sK4,sK5) != iProver_top
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5781,c_34,c_4207,c_4302,c_6166,c_6167])).

cnf(c_6325,plain,
    ( sK3 = k1_xboole_0
    | r1_partfun1(sK4,sK5) != iProver_top ),
    inference(renaming,[status(thm)],[c_6324])).

cnf(c_6446,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6291,c_25,c_26,c_27,c_29,c_1998,c_2001,c_6325])).

cnf(c_6453,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(k1_relat_1(sK4),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2652,c_6446])).

cnf(c_6581,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6453,c_4302])).

cnf(c_19,negated_conjecture,
    ( k1_xboole_0 != sK3
    | k1_xboole_0 = sK2 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_6606,plain,
    ( sK2 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6581,c_19])).

cnf(c_6607,plain,
    ( sK2 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_6606])).

cnf(c_3841,plain,
    ( r1_partfun1(sK4,sK5) != iProver_top
    | r2_hidden(sK6,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2731,c_3186])).

cnf(c_6715,plain,
    ( r1_partfun1(sK4,sK5) != iProver_top
    | r2_hidden(sK6,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6607,c_3841])).

cnf(c_2055,plain,
    ( r1_partfun1(X0,sK5)
    | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(sK5))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK5)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK5)
    | k1_funct_1(sK5,sK1(X0,sK5)) != k1_funct_1(X0,sK1(X0,sK5)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_2131,plain,
    ( r1_partfun1(sK4,sK5)
    | ~ r1_tarski(k1_relat_1(sK4),k1_relat_1(sK5))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK5)
    | ~ v1_relat_1(sK4)
    | k1_funct_1(sK5,sK1(sK4,sK5)) != k1_funct_1(sK4,sK1(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_2055])).

cnf(c_2132,plain,
    ( k1_funct_1(sK5,sK1(sK4,sK5)) != k1_funct_1(sK4,sK1(sK4,sK5))
    | r1_partfun1(sK4,sK5) = iProver_top
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(sK5)) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK5) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2131])).

cnf(c_1446,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2173,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(sK5))
    | k1_relat_1(sK5) != X1
    | k1_relat_1(sK4) != X0 ),
    inference(instantiation,[status(thm)],[c_1446])).

cnf(c_2174,plain,
    ( k1_relat_1(sK5) != X0
    | k1_relat_1(sK4) != X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2173])).

cnf(c_2176,plain,
    ( k1_relat_1(sK5) != k1_xboole_0
    | k1_relat_1(sK4) != k1_xboole_0
    | r1_tarski(k1_relat_1(sK4),k1_relat_1(sK5)) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2174])).

cnf(c_2335,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1830,c_1831])).

cnf(c_2337,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2335])).

cnf(c_6600,plain,
    ( k1_relset_1(sK2,k1_xboole_0,sK5) = k1_relat_1(sK5) ),
    inference(demodulation,[status(thm)],[c_6581,c_2469])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_542,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | sK3 != X1
    | sK2 != k1_xboole_0
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_21])).

cnf(c_543,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)))
    | k1_relset_1(k1_xboole_0,sK3,sK5) = k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_542])).

cnf(c_1813,plain,
    ( k1_relset_1(k1_xboole_0,sK3,sK5) = k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_543])).

cnf(c_6602,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK5) = k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6581,c_1813])).

cnf(c_6616,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK5) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6602,c_6607])).

cnf(c_6617,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK5) = k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_6616])).

cnf(c_6604,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6581,c_1818])).

cnf(c_6613,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6604,c_6607])).

cnf(c_6620,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK5) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6617,c_6613])).

cnf(c_6623,plain,
    ( k1_relat_1(sK5) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_6600,c_6607,c_6620])).

cnf(c_6712,plain,
    ( r1_tarski(k1_relat_1(sK4),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6607,c_4302])).

cnf(c_6834,plain,
    ( k1_funct_1(sK4,sK1(sK4,sK5)) = k1_funct_1(sK5,sK1(sK4,sK5))
    | r1_partfun1(sK4,sK5) = iProver_top
    | r1_tarski(k1_relat_1(sK4),k1_xboole_0) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_6623,c_3934])).

cnf(c_3236,plain,
    ( k1_funct_1(sK5,sK1(sK4,sK5)) != X0
    | k1_funct_1(sK5,sK1(sK4,sK5)) = k1_funct_1(sK4,sK1(sK4,sK5))
    | k1_funct_1(sK4,sK1(sK4,sK5)) != X0 ),
    inference(instantiation,[status(thm)],[c_1445])).

cnf(c_3611,plain,
    ( k1_funct_1(sK5,sK1(sK4,sK5)) != k1_funct_1(X0,sK1(sK4,sK5))
    | k1_funct_1(sK5,sK1(sK4,sK5)) = k1_funct_1(sK4,sK1(sK4,sK5))
    | k1_funct_1(sK4,sK1(sK4,sK5)) != k1_funct_1(X0,sK1(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_3236])).

cnf(c_6921,plain,
    ( k1_funct_1(sK5,sK1(sK4,sK5)) != k1_funct_1(sK5,sK1(sK4,sK5))
    | k1_funct_1(sK5,sK1(sK4,sK5)) = k1_funct_1(sK4,sK1(sK4,sK5))
    | k1_funct_1(sK4,sK1(sK4,sK5)) != k1_funct_1(sK5,sK1(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_3611])).

cnf(c_6922,plain,
    ( k1_funct_1(sK5,sK1(sK4,sK5)) = k1_funct_1(sK5,sK1(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_1444])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1829,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_6927,plain,
    ( k1_relat_1(sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6712,c_1829])).

cnf(c_7536,plain,
    ( r2_hidden(sK6,k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6715,c_25,c_26,c_27,c_29,c_1998,c_2001,c_2132,c_2176,c_2337,c_6623,c_6712,c_6834,c_6921,c_6922,c_6927])).

cnf(c_7164,plain,
    ( k1_funct_1(X0,X1) = k1_funct_1(sK4,X1)
    | r1_partfun1(X0,sK4) != iProver_top
    | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6927,c_1822])).

cnf(c_7740,plain,
    ( v1_relat_1(X0) != iProver_top
    | k1_funct_1(X0,X1) = k1_funct_1(sK4,X1)
    | r1_partfun1(X0,sK4) != iProver_top
    | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7164,c_25,c_26,c_2001])).

cnf(c_7741,plain,
    ( k1_funct_1(X0,X1) = k1_funct_1(sK4,X1)
    | r1_partfun1(X0,sK4) != iProver_top
    | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_7740])).

cnf(c_7755,plain,
    ( k1_funct_1(sK5,X0) = k1_funct_1(sK4,X0)
    | r1_partfun1(sK5,sK4) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top
    | r1_tarski(k1_relat_1(sK5),k1_xboole_0) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_6623,c_7741])).

cnf(c_7763,plain,
    ( k1_funct_1(sK5,X0) = k1_funct_1(sK4,X0)
    | r1_partfun1(sK5,sK4) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7755,c_6623])).

cnf(c_6836,plain,
    ( k1_funct_1(X0,X1) = k1_funct_1(sK5,X1)
    | r1_partfun1(X0,sK5) != iProver_top
    | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_6623,c_1822])).

cnf(c_7281,plain,
    ( v1_relat_1(X0) != iProver_top
    | k1_funct_1(X0,X1) = k1_funct_1(sK5,X1)
    | r1_partfun1(X0,sK5) != iProver_top
    | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6836,c_27,c_29,c_1998])).

cnf(c_7282,plain,
    ( k1_funct_1(X0,X1) = k1_funct_1(sK5,X1)
    | r1_partfun1(X0,sK5) != iProver_top
    | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_7281])).

cnf(c_7297,plain,
    ( k1_funct_1(sK5,X0) = k1_funct_1(sK4,X0)
    | r1_partfun1(sK4,sK5) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top
    | r1_tarski(k1_relat_1(sK4),k1_xboole_0) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6927,c_7282])).

cnf(c_7304,plain,
    ( k1_funct_1(sK5,X0) = k1_funct_1(sK4,X0)
    | r1_partfun1(sK4,sK5) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7297,c_6927])).

cnf(c_8891,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | k1_funct_1(sK5,X0) = k1_funct_1(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7763,c_25,c_26,c_27,c_29,c_1998,c_2001,c_2132,c_2176,c_2337,c_6623,c_6712,c_6834,c_6921,c_6922,c_6927,c_7304])).

cnf(c_8892,plain,
    ( k1_funct_1(sK5,X0) = k1_funct_1(sK4,X0)
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_8891])).

cnf(c_8900,plain,
    ( k1_funct_1(sK5,sK6) = k1_funct_1(sK4,sK6) ),
    inference(superposition,[status(thm)],[c_7536,c_8892])).

cnf(c_7063,plain,
    ( k1_funct_1(sK5,X0) = k1_funct_1(sK4,X0)
    | r1_partfun1(sK4,sK5) = iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6927,c_2730])).

cnf(c_8467,plain,
    ( r1_partfun1(sK4,sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7063,c_25,c_26,c_27,c_29,c_1998,c_2001,c_2132,c_2176,c_2337,c_6623,c_6712,c_6834,c_6921,c_6922,c_6927])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8900,c_8467,c_6167,c_6166,c_34])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:28:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.21/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.21/0.99  
% 3.21/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.21/0.99  
% 3.21/0.99  ------  iProver source info
% 3.21/0.99  
% 3.21/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.21/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.21/0.99  git: non_committed_changes: false
% 3.21/0.99  git: last_make_outside_of_git: false
% 3.21/0.99  
% 3.21/0.99  ------ 
% 3.21/0.99  
% 3.21/0.99  ------ Input Options
% 3.21/0.99  
% 3.21/0.99  --out_options                           all
% 3.21/0.99  --tptp_safe_out                         true
% 3.21/0.99  --problem_path                          ""
% 3.21/0.99  --include_path                          ""
% 3.21/0.99  --clausifier                            res/vclausify_rel
% 3.21/0.99  --clausifier_options                    --mode clausify
% 3.21/0.99  --stdin                                 false
% 3.21/0.99  --stats_out                             all
% 3.21/0.99  
% 3.21/0.99  ------ General Options
% 3.21/0.99  
% 3.21/0.99  --fof                                   false
% 3.21/0.99  --time_out_real                         305.
% 3.21/0.99  --time_out_virtual                      -1.
% 3.21/0.99  --symbol_type_check                     false
% 3.21/0.99  --clausify_out                          false
% 3.21/0.99  --sig_cnt_out                           false
% 3.21/1.00  --trig_cnt_out                          false
% 3.21/1.00  --trig_cnt_out_tolerance                1.
% 3.21/1.00  --trig_cnt_out_sk_spl                   false
% 3.21/1.00  --abstr_cl_out                          false
% 3.21/1.00  
% 3.21/1.00  ------ Global Options
% 3.21/1.00  
% 3.21/1.00  --schedule                              default
% 3.21/1.00  --add_important_lit                     false
% 3.21/1.00  --prop_solver_per_cl                    1000
% 3.21/1.00  --min_unsat_core                        false
% 3.21/1.00  --soft_assumptions                      false
% 3.21/1.00  --soft_lemma_size                       3
% 3.21/1.00  --prop_impl_unit_size                   0
% 3.21/1.00  --prop_impl_unit                        []
% 3.21/1.00  --share_sel_clauses                     true
% 3.21/1.00  --reset_solvers                         false
% 3.21/1.00  --bc_imp_inh                            [conj_cone]
% 3.21/1.00  --conj_cone_tolerance                   3.
% 3.21/1.00  --extra_neg_conj                        none
% 3.21/1.00  --large_theory_mode                     true
% 3.21/1.00  --prolific_symb_bound                   200
% 3.21/1.00  --lt_threshold                          2000
% 3.21/1.00  --clause_weak_htbl                      true
% 3.21/1.00  --gc_record_bc_elim                     false
% 3.21/1.00  
% 3.21/1.00  ------ Preprocessing Options
% 3.21/1.00  
% 3.21/1.00  --preprocessing_flag                    true
% 3.21/1.00  --time_out_prep_mult                    0.1
% 3.21/1.00  --splitting_mode                        input
% 3.21/1.00  --splitting_grd                         true
% 3.21/1.00  --splitting_cvd                         false
% 3.21/1.00  --splitting_cvd_svl                     false
% 3.21/1.00  --splitting_nvd                         32
% 3.21/1.00  --sub_typing                            true
% 3.21/1.00  --prep_gs_sim                           true
% 3.21/1.00  --prep_unflatten                        true
% 3.21/1.00  --prep_res_sim                          true
% 3.21/1.00  --prep_upred                            true
% 3.21/1.00  --prep_sem_filter                       exhaustive
% 3.21/1.00  --prep_sem_filter_out                   false
% 3.21/1.00  --pred_elim                             true
% 3.21/1.00  --res_sim_input                         true
% 3.21/1.00  --eq_ax_congr_red                       true
% 3.21/1.00  --pure_diseq_elim                       true
% 3.21/1.00  --brand_transform                       false
% 3.21/1.00  --non_eq_to_eq                          false
% 3.21/1.00  --prep_def_merge                        true
% 3.21/1.00  --prep_def_merge_prop_impl              false
% 3.21/1.00  --prep_def_merge_mbd                    true
% 3.21/1.00  --prep_def_merge_tr_red                 false
% 3.21/1.00  --prep_def_merge_tr_cl                  false
% 3.21/1.00  --smt_preprocessing                     true
% 3.21/1.00  --smt_ac_axioms                         fast
% 3.21/1.00  --preprocessed_out                      false
% 3.21/1.00  --preprocessed_stats                    false
% 3.21/1.00  
% 3.21/1.00  ------ Abstraction refinement Options
% 3.21/1.00  
% 3.21/1.00  --abstr_ref                             []
% 3.21/1.00  --abstr_ref_prep                        false
% 3.21/1.00  --abstr_ref_until_sat                   false
% 3.21/1.00  --abstr_ref_sig_restrict                funpre
% 3.21/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.21/1.00  --abstr_ref_under                       []
% 3.21/1.00  
% 3.21/1.00  ------ SAT Options
% 3.21/1.00  
% 3.21/1.00  --sat_mode                              false
% 3.21/1.00  --sat_fm_restart_options                ""
% 3.21/1.00  --sat_gr_def                            false
% 3.21/1.00  --sat_epr_types                         true
% 3.21/1.00  --sat_non_cyclic_types                  false
% 3.21/1.00  --sat_finite_models                     false
% 3.21/1.00  --sat_fm_lemmas                         false
% 3.21/1.00  --sat_fm_prep                           false
% 3.21/1.00  --sat_fm_uc_incr                        true
% 3.21/1.00  --sat_out_model                         small
% 3.21/1.00  --sat_out_clauses                       false
% 3.21/1.00  
% 3.21/1.00  ------ QBF Options
% 3.21/1.00  
% 3.21/1.00  --qbf_mode                              false
% 3.21/1.00  --qbf_elim_univ                         false
% 3.21/1.00  --qbf_dom_inst                          none
% 3.21/1.00  --qbf_dom_pre_inst                      false
% 3.21/1.00  --qbf_sk_in                             false
% 3.21/1.00  --qbf_pred_elim                         true
% 3.21/1.00  --qbf_split                             512
% 3.21/1.00  
% 3.21/1.00  ------ BMC1 Options
% 3.21/1.00  
% 3.21/1.00  --bmc1_incremental                      false
% 3.21/1.00  --bmc1_axioms                           reachable_all
% 3.21/1.00  --bmc1_min_bound                        0
% 3.21/1.00  --bmc1_max_bound                        -1
% 3.21/1.00  --bmc1_max_bound_default                -1
% 3.21/1.00  --bmc1_symbol_reachability              true
% 3.21/1.00  --bmc1_property_lemmas                  false
% 3.21/1.00  --bmc1_k_induction                      false
% 3.21/1.00  --bmc1_non_equiv_states                 false
% 3.21/1.00  --bmc1_deadlock                         false
% 3.21/1.00  --bmc1_ucm                              false
% 3.21/1.00  --bmc1_add_unsat_core                   none
% 3.21/1.00  --bmc1_unsat_core_children              false
% 3.21/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.21/1.00  --bmc1_out_stat                         full
% 3.21/1.00  --bmc1_ground_init                      false
% 3.21/1.00  --bmc1_pre_inst_next_state              false
% 3.21/1.00  --bmc1_pre_inst_state                   false
% 3.21/1.00  --bmc1_pre_inst_reach_state             false
% 3.21/1.00  --bmc1_out_unsat_core                   false
% 3.21/1.00  --bmc1_aig_witness_out                  false
% 3.21/1.00  --bmc1_verbose                          false
% 3.21/1.00  --bmc1_dump_clauses_tptp                false
% 3.21/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.21/1.00  --bmc1_dump_file                        -
% 3.21/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.21/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.21/1.00  --bmc1_ucm_extend_mode                  1
% 3.21/1.00  --bmc1_ucm_init_mode                    2
% 3.21/1.00  --bmc1_ucm_cone_mode                    none
% 3.21/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.21/1.00  --bmc1_ucm_relax_model                  4
% 3.21/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.21/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.21/1.00  --bmc1_ucm_layered_model                none
% 3.21/1.00  --bmc1_ucm_max_lemma_size               10
% 3.21/1.00  
% 3.21/1.00  ------ AIG Options
% 3.21/1.00  
% 3.21/1.00  --aig_mode                              false
% 3.21/1.00  
% 3.21/1.00  ------ Instantiation Options
% 3.21/1.00  
% 3.21/1.00  --instantiation_flag                    true
% 3.21/1.00  --inst_sos_flag                         false
% 3.21/1.00  --inst_sos_phase                        true
% 3.21/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.21/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.21/1.00  --inst_lit_sel_side                     num_symb
% 3.21/1.00  --inst_solver_per_active                1400
% 3.21/1.00  --inst_solver_calls_frac                1.
% 3.21/1.00  --inst_passive_queue_type               priority_queues
% 3.21/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.21/1.00  --inst_passive_queues_freq              [25;2]
% 3.21/1.00  --inst_dismatching                      true
% 3.21/1.00  --inst_eager_unprocessed_to_passive     true
% 3.21/1.00  --inst_prop_sim_given                   true
% 3.21/1.00  --inst_prop_sim_new                     false
% 3.21/1.00  --inst_subs_new                         false
% 3.21/1.00  --inst_eq_res_simp                      false
% 3.21/1.00  --inst_subs_given                       false
% 3.21/1.00  --inst_orphan_elimination               true
% 3.21/1.00  --inst_learning_loop_flag               true
% 3.21/1.00  --inst_learning_start                   3000
% 3.21/1.00  --inst_learning_factor                  2
% 3.21/1.00  --inst_start_prop_sim_after_learn       3
% 3.21/1.00  --inst_sel_renew                        solver
% 3.21/1.00  --inst_lit_activity_flag                true
% 3.21/1.00  --inst_restr_to_given                   false
% 3.21/1.00  --inst_activity_threshold               500
% 3.21/1.00  --inst_out_proof                        true
% 3.21/1.00  
% 3.21/1.00  ------ Resolution Options
% 3.21/1.00  
% 3.21/1.00  --resolution_flag                       true
% 3.21/1.00  --res_lit_sel                           adaptive
% 3.21/1.00  --res_lit_sel_side                      none
% 3.21/1.00  --res_ordering                          kbo
% 3.21/1.00  --res_to_prop_solver                    active
% 3.21/1.00  --res_prop_simpl_new                    false
% 3.21/1.00  --res_prop_simpl_given                  true
% 3.21/1.00  --res_passive_queue_type                priority_queues
% 3.21/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.21/1.00  --res_passive_queues_freq               [15;5]
% 3.21/1.00  --res_forward_subs                      full
% 3.21/1.00  --res_backward_subs                     full
% 3.21/1.00  --res_forward_subs_resolution           true
% 3.21/1.00  --res_backward_subs_resolution          true
% 3.21/1.00  --res_orphan_elimination                true
% 3.21/1.00  --res_time_limit                        2.
% 3.21/1.00  --res_out_proof                         true
% 3.21/1.00  
% 3.21/1.00  ------ Superposition Options
% 3.21/1.00  
% 3.21/1.00  --superposition_flag                    true
% 3.21/1.00  --sup_passive_queue_type                priority_queues
% 3.21/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.21/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.21/1.00  --demod_completeness_check              fast
% 3.21/1.00  --demod_use_ground                      true
% 3.21/1.00  --sup_to_prop_solver                    passive
% 3.21/1.00  --sup_prop_simpl_new                    true
% 3.21/1.00  --sup_prop_simpl_given                  true
% 3.21/1.00  --sup_fun_splitting                     false
% 3.21/1.00  --sup_smt_interval                      50000
% 3.21/1.00  
% 3.21/1.00  ------ Superposition Simplification Setup
% 3.21/1.00  
% 3.21/1.00  --sup_indices_passive                   []
% 3.21/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.21/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.21/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.21/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.21/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.21/1.00  --sup_full_bw                           [BwDemod]
% 3.21/1.00  --sup_immed_triv                        [TrivRules]
% 3.21/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.21/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.21/1.00  --sup_immed_bw_main                     []
% 3.21/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.21/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.21/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.21/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.21/1.00  
% 3.21/1.00  ------ Combination Options
% 3.21/1.00  
% 3.21/1.00  --comb_res_mult                         3
% 3.21/1.00  --comb_sup_mult                         2
% 3.21/1.00  --comb_inst_mult                        10
% 3.21/1.00  
% 3.21/1.00  ------ Debug Options
% 3.21/1.00  
% 3.21/1.00  --dbg_backtrace                         false
% 3.21/1.00  --dbg_dump_prop_clauses                 false
% 3.21/1.00  --dbg_dump_prop_clauses_file            -
% 3.21/1.00  --dbg_out_stat                          false
% 3.21/1.00  ------ Parsing...
% 3.21/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.21/1.00  
% 3.21/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.21/1.00  
% 3.21/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.21/1.00  
% 3.21/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.21/1.00  ------ Proving...
% 3.21/1.00  ------ Problem Properties 
% 3.21/1.00  
% 3.21/1.00  
% 3.21/1.00  clauses                                 21
% 3.21/1.00  conjectures                             8
% 3.21/1.00  EPR                                     4
% 3.21/1.00  Horn                                    16
% 3.21/1.00  unary                                   4
% 3.21/1.00  binary                                  10
% 3.21/1.00  lits                                    59
% 3.21/1.00  lits eq                                 15
% 3.21/1.00  fd_pure                                 0
% 3.21/1.00  fd_pseudo                               0
% 3.21/1.00  fd_cond                                 1
% 3.21/1.00  fd_pseudo_cond                          0
% 3.21/1.00  AC symbols                              0
% 3.21/1.00  
% 3.21/1.00  ------ Schedule dynamic 5 is on 
% 3.21/1.00  
% 3.21/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.21/1.00  
% 3.21/1.00  
% 3.21/1.00  ------ 
% 3.21/1.00  Current options:
% 3.21/1.00  ------ 
% 3.21/1.00  
% 3.21/1.00  ------ Input Options
% 3.21/1.00  
% 3.21/1.00  --out_options                           all
% 3.21/1.00  --tptp_safe_out                         true
% 3.21/1.00  --problem_path                          ""
% 3.21/1.00  --include_path                          ""
% 3.21/1.00  --clausifier                            res/vclausify_rel
% 3.21/1.00  --clausifier_options                    --mode clausify
% 3.21/1.00  --stdin                                 false
% 3.21/1.00  --stats_out                             all
% 3.21/1.00  
% 3.21/1.00  ------ General Options
% 3.21/1.00  
% 3.21/1.00  --fof                                   false
% 3.21/1.00  --time_out_real                         305.
% 3.21/1.00  --time_out_virtual                      -1.
% 3.21/1.00  --symbol_type_check                     false
% 3.21/1.00  --clausify_out                          false
% 3.21/1.00  --sig_cnt_out                           false
% 3.21/1.00  --trig_cnt_out                          false
% 3.21/1.00  --trig_cnt_out_tolerance                1.
% 3.21/1.00  --trig_cnt_out_sk_spl                   false
% 3.21/1.00  --abstr_cl_out                          false
% 3.21/1.00  
% 3.21/1.00  ------ Global Options
% 3.21/1.00  
% 3.21/1.00  --schedule                              default
% 3.21/1.00  --add_important_lit                     false
% 3.21/1.00  --prop_solver_per_cl                    1000
% 3.21/1.00  --min_unsat_core                        false
% 3.21/1.00  --soft_assumptions                      false
% 3.21/1.00  --soft_lemma_size                       3
% 3.21/1.00  --prop_impl_unit_size                   0
% 3.21/1.00  --prop_impl_unit                        []
% 3.21/1.00  --share_sel_clauses                     true
% 3.21/1.00  --reset_solvers                         false
% 3.21/1.00  --bc_imp_inh                            [conj_cone]
% 3.21/1.00  --conj_cone_tolerance                   3.
% 3.21/1.00  --extra_neg_conj                        none
% 3.21/1.00  --large_theory_mode                     true
% 3.21/1.00  --prolific_symb_bound                   200
% 3.21/1.00  --lt_threshold                          2000
% 3.21/1.00  --clause_weak_htbl                      true
% 3.21/1.00  --gc_record_bc_elim                     false
% 3.21/1.00  
% 3.21/1.00  ------ Preprocessing Options
% 3.21/1.00  
% 3.21/1.00  --preprocessing_flag                    true
% 3.21/1.00  --time_out_prep_mult                    0.1
% 3.21/1.00  --splitting_mode                        input
% 3.21/1.00  --splitting_grd                         true
% 3.21/1.00  --splitting_cvd                         false
% 3.21/1.00  --splitting_cvd_svl                     false
% 3.21/1.00  --splitting_nvd                         32
% 3.21/1.00  --sub_typing                            true
% 3.21/1.00  --prep_gs_sim                           true
% 3.21/1.00  --prep_unflatten                        true
% 3.21/1.00  --prep_res_sim                          true
% 3.21/1.00  --prep_upred                            true
% 3.21/1.00  --prep_sem_filter                       exhaustive
% 3.21/1.00  --prep_sem_filter_out                   false
% 3.21/1.00  --pred_elim                             true
% 3.21/1.00  --res_sim_input                         true
% 3.21/1.00  --eq_ax_congr_red                       true
% 3.21/1.00  --pure_diseq_elim                       true
% 3.21/1.00  --brand_transform                       false
% 3.21/1.00  --non_eq_to_eq                          false
% 3.21/1.00  --prep_def_merge                        true
% 3.21/1.00  --prep_def_merge_prop_impl              false
% 3.21/1.00  --prep_def_merge_mbd                    true
% 3.21/1.00  --prep_def_merge_tr_red                 false
% 3.21/1.00  --prep_def_merge_tr_cl                  false
% 3.21/1.00  --smt_preprocessing                     true
% 3.21/1.00  --smt_ac_axioms                         fast
% 3.21/1.00  --preprocessed_out                      false
% 3.21/1.00  --preprocessed_stats                    false
% 3.21/1.00  
% 3.21/1.00  ------ Abstraction refinement Options
% 3.21/1.00  
% 3.21/1.00  --abstr_ref                             []
% 3.21/1.00  --abstr_ref_prep                        false
% 3.21/1.00  --abstr_ref_until_sat                   false
% 3.21/1.00  --abstr_ref_sig_restrict                funpre
% 3.21/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.21/1.00  --abstr_ref_under                       []
% 3.21/1.00  
% 3.21/1.00  ------ SAT Options
% 3.21/1.00  
% 3.21/1.00  --sat_mode                              false
% 3.21/1.00  --sat_fm_restart_options                ""
% 3.21/1.00  --sat_gr_def                            false
% 3.21/1.00  --sat_epr_types                         true
% 3.21/1.00  --sat_non_cyclic_types                  false
% 3.21/1.00  --sat_finite_models                     false
% 3.21/1.00  --sat_fm_lemmas                         false
% 3.21/1.00  --sat_fm_prep                           false
% 3.21/1.00  --sat_fm_uc_incr                        true
% 3.21/1.00  --sat_out_model                         small
% 3.21/1.00  --sat_out_clauses                       false
% 3.21/1.00  
% 3.21/1.00  ------ QBF Options
% 3.21/1.00  
% 3.21/1.00  --qbf_mode                              false
% 3.21/1.00  --qbf_elim_univ                         false
% 3.21/1.00  --qbf_dom_inst                          none
% 3.21/1.00  --qbf_dom_pre_inst                      false
% 3.21/1.00  --qbf_sk_in                             false
% 3.21/1.00  --qbf_pred_elim                         true
% 3.21/1.00  --qbf_split                             512
% 3.21/1.00  
% 3.21/1.00  ------ BMC1 Options
% 3.21/1.00  
% 3.21/1.00  --bmc1_incremental                      false
% 3.21/1.00  --bmc1_axioms                           reachable_all
% 3.21/1.00  --bmc1_min_bound                        0
% 3.21/1.00  --bmc1_max_bound                        -1
% 3.21/1.00  --bmc1_max_bound_default                -1
% 3.21/1.00  --bmc1_symbol_reachability              true
% 3.21/1.00  --bmc1_property_lemmas                  false
% 3.21/1.00  --bmc1_k_induction                      false
% 3.21/1.00  --bmc1_non_equiv_states                 false
% 3.21/1.00  --bmc1_deadlock                         false
% 3.21/1.00  --bmc1_ucm                              false
% 3.21/1.00  --bmc1_add_unsat_core                   none
% 3.21/1.00  --bmc1_unsat_core_children              false
% 3.21/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.21/1.00  --bmc1_out_stat                         full
% 3.21/1.00  --bmc1_ground_init                      false
% 3.21/1.00  --bmc1_pre_inst_next_state              false
% 3.21/1.00  --bmc1_pre_inst_state                   false
% 3.21/1.00  --bmc1_pre_inst_reach_state             false
% 3.21/1.00  --bmc1_out_unsat_core                   false
% 3.21/1.00  --bmc1_aig_witness_out                  false
% 3.21/1.00  --bmc1_verbose                          false
% 3.21/1.00  --bmc1_dump_clauses_tptp                false
% 3.21/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.21/1.00  --bmc1_dump_file                        -
% 3.21/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.21/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.21/1.00  --bmc1_ucm_extend_mode                  1
% 3.21/1.00  --bmc1_ucm_init_mode                    2
% 3.21/1.00  --bmc1_ucm_cone_mode                    none
% 3.21/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.21/1.00  --bmc1_ucm_relax_model                  4
% 3.21/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.21/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.21/1.00  --bmc1_ucm_layered_model                none
% 3.21/1.00  --bmc1_ucm_max_lemma_size               10
% 3.21/1.00  
% 3.21/1.00  ------ AIG Options
% 3.21/1.00  
% 3.21/1.00  --aig_mode                              false
% 3.21/1.00  
% 3.21/1.00  ------ Instantiation Options
% 3.21/1.00  
% 3.21/1.00  --instantiation_flag                    true
% 3.21/1.00  --inst_sos_flag                         false
% 3.21/1.00  --inst_sos_phase                        true
% 3.21/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.21/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.21/1.00  --inst_lit_sel_side                     none
% 3.21/1.00  --inst_solver_per_active                1400
% 3.21/1.00  --inst_solver_calls_frac                1.
% 3.21/1.00  --inst_passive_queue_type               priority_queues
% 3.21/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.21/1.00  --inst_passive_queues_freq              [25;2]
% 3.21/1.00  --inst_dismatching                      true
% 3.21/1.00  --inst_eager_unprocessed_to_passive     true
% 3.21/1.00  --inst_prop_sim_given                   true
% 3.21/1.00  --inst_prop_sim_new                     false
% 3.21/1.00  --inst_subs_new                         false
% 3.21/1.00  --inst_eq_res_simp                      false
% 3.21/1.00  --inst_subs_given                       false
% 3.21/1.00  --inst_orphan_elimination               true
% 3.21/1.00  --inst_learning_loop_flag               true
% 3.21/1.00  --inst_learning_start                   3000
% 3.21/1.00  --inst_learning_factor                  2
% 3.21/1.00  --inst_start_prop_sim_after_learn       3
% 3.21/1.00  --inst_sel_renew                        solver
% 3.21/1.00  --inst_lit_activity_flag                true
% 3.21/1.00  --inst_restr_to_given                   false
% 3.21/1.00  --inst_activity_threshold               500
% 3.21/1.00  --inst_out_proof                        true
% 3.21/1.00  
% 3.21/1.00  ------ Resolution Options
% 3.21/1.00  
% 3.21/1.00  --resolution_flag                       false
% 3.21/1.00  --res_lit_sel                           adaptive
% 3.21/1.00  --res_lit_sel_side                      none
% 3.21/1.00  --res_ordering                          kbo
% 3.21/1.00  --res_to_prop_solver                    active
% 3.21/1.00  --res_prop_simpl_new                    false
% 3.21/1.00  --res_prop_simpl_given                  true
% 3.21/1.00  --res_passive_queue_type                priority_queues
% 3.21/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.21/1.00  --res_passive_queues_freq               [15;5]
% 3.21/1.00  --res_forward_subs                      full
% 3.21/1.00  --res_backward_subs                     full
% 3.21/1.00  --res_forward_subs_resolution           true
% 3.21/1.00  --res_backward_subs_resolution          true
% 3.21/1.00  --res_orphan_elimination                true
% 3.21/1.00  --res_time_limit                        2.
% 3.21/1.00  --res_out_proof                         true
% 3.21/1.00  
% 3.21/1.00  ------ Superposition Options
% 3.21/1.00  
% 3.21/1.00  --superposition_flag                    true
% 3.21/1.00  --sup_passive_queue_type                priority_queues
% 3.21/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.21/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.21/1.00  --demod_completeness_check              fast
% 3.21/1.00  --demod_use_ground                      true
% 3.21/1.00  --sup_to_prop_solver                    passive
% 3.21/1.00  --sup_prop_simpl_new                    true
% 3.21/1.00  --sup_prop_simpl_given                  true
% 3.21/1.00  --sup_fun_splitting                     false
% 3.21/1.00  --sup_smt_interval                      50000
% 3.21/1.00  
% 3.21/1.00  ------ Superposition Simplification Setup
% 3.21/1.00  
% 3.21/1.00  --sup_indices_passive                   []
% 3.21/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.21/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.21/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.21/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.21/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.21/1.00  --sup_full_bw                           [BwDemod]
% 3.21/1.00  --sup_immed_triv                        [TrivRules]
% 3.21/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.21/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.21/1.00  --sup_immed_bw_main                     []
% 3.21/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.21/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.21/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.21/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.21/1.00  
% 3.21/1.00  ------ Combination Options
% 3.21/1.00  
% 3.21/1.00  --comb_res_mult                         3
% 3.21/1.00  --comb_sup_mult                         2
% 3.21/1.00  --comb_inst_mult                        10
% 3.21/1.00  
% 3.21/1.00  ------ Debug Options
% 3.21/1.00  
% 3.21/1.00  --dbg_backtrace                         false
% 3.21/1.00  --dbg_dump_prop_clauses                 false
% 3.21/1.00  --dbg_dump_prop_clauses_file            -
% 3.21/1.00  --dbg_out_stat                          false
% 3.21/1.00  
% 3.21/1.00  
% 3.21/1.00  
% 3.21/1.00  
% 3.21/1.00  ------ Proving...
% 3.21/1.00  
% 3.21/1.00  
% 3.21/1.00  % SZS status Theorem for theBenchmark.p
% 3.21/1.00  
% 3.21/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.21/1.00  
% 3.21/1.00  fof(f9,conjecture,(
% 3.21/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (r1_partfun1(X2,X3) <=> ! [X4] : (r2_hidden(X4,k1_relset_1(X0,X1,X2)) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4))))))),
% 3.21/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.21/1.00  
% 3.21/1.00  fof(f10,negated_conjecture,(
% 3.21/1.00    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (r1_partfun1(X2,X3) <=> ! [X4] : (r2_hidden(X4,k1_relset_1(X0,X1,X2)) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4))))))),
% 3.21/1.00    inference(negated_conjecture,[],[f9])).
% 3.21/1.00  
% 3.21/1.00  fof(f22,plain,(
% 3.21/1.00    ? [X0,X1,X2] : (? [X3] : (((r1_partfun1(X2,X3) <~> ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,k1_relset_1(X0,X1,X2)))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 3.21/1.00    inference(ennf_transformation,[],[f10])).
% 3.21/1.00  
% 3.21/1.00  fof(f23,plain,(
% 3.21/1.00    ? [X0,X1,X2] : (? [X3] : ((r1_partfun1(X2,X3) <~> ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,k1_relset_1(X0,X1,X2)))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 3.21/1.00    inference(flattening,[],[f22])).
% 3.21/1.00  
% 3.21/1.00  fof(f31,plain,(
% 3.21/1.00    ? [X0,X1,X2] : (? [X3] : (((? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & r2_hidden(X4,k1_relset_1(X0,X1,X2))) | ~r1_partfun1(X2,X3)) & (! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,k1_relset_1(X0,X1,X2))) | r1_partfun1(X2,X3))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 3.21/1.00    inference(nnf_transformation,[],[f23])).
% 3.21/1.00  
% 3.21/1.00  fof(f32,plain,(
% 3.21/1.00    ? [X0,X1,X2] : (? [X3] : ((? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & r2_hidden(X4,k1_relset_1(X0,X1,X2))) | ~r1_partfun1(X2,X3)) & (! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,k1_relset_1(X0,X1,X2))) | r1_partfun1(X2,X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 3.21/1.00    inference(flattening,[],[f31])).
% 3.21/1.00  
% 3.21/1.00  fof(f33,plain,(
% 3.21/1.00    ? [X0,X1,X2] : (? [X3] : ((? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & r2_hidden(X4,k1_relset_1(X0,X1,X2))) | ~r1_partfun1(X2,X3)) & (! [X5] : (k1_funct_1(X2,X5) = k1_funct_1(X3,X5) | ~r2_hidden(X5,k1_relset_1(X0,X1,X2))) | r1_partfun1(X2,X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 3.21/1.00    inference(rectify,[],[f32])).
% 3.21/1.00  
% 3.21/1.00  fof(f36,plain,(
% 3.21/1.00    ( ! [X2,X0,X3,X1] : (? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & r2_hidden(X4,k1_relset_1(X0,X1,X2))) => (k1_funct_1(X2,sK6) != k1_funct_1(X3,sK6) & r2_hidden(sK6,k1_relset_1(X0,X1,X2)))) )),
% 3.21/1.00    introduced(choice_axiom,[])).
% 3.21/1.00  
% 3.21/1.00  fof(f35,plain,(
% 3.21/1.00    ( ! [X2,X0,X1] : (? [X3] : ((? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & r2_hidden(X4,k1_relset_1(X0,X1,X2))) | ~r1_partfun1(X2,X3)) & (! [X5] : (k1_funct_1(X2,X5) = k1_funct_1(X3,X5) | ~r2_hidden(X5,k1_relset_1(X0,X1,X2))) | r1_partfun1(X2,X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((? [X4] : (k1_funct_1(sK5,X4) != k1_funct_1(X2,X4) & r2_hidden(X4,k1_relset_1(X0,X1,X2))) | ~r1_partfun1(X2,sK5)) & (! [X5] : (k1_funct_1(sK5,X5) = k1_funct_1(X2,X5) | ~r2_hidden(X5,k1_relset_1(X0,X1,X2))) | r1_partfun1(X2,sK5)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(sK5,X0,X1) & v1_funct_1(sK5))) )),
% 3.21/1.00    introduced(choice_axiom,[])).
% 3.21/1.00  
% 3.21/1.00  fof(f34,plain,(
% 3.21/1.00    ? [X0,X1,X2] : (? [X3] : ((? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & r2_hidden(X4,k1_relset_1(X0,X1,X2))) | ~r1_partfun1(X2,X3)) & (! [X5] : (k1_funct_1(X2,X5) = k1_funct_1(X3,X5) | ~r2_hidden(X5,k1_relset_1(X0,X1,X2))) | r1_partfun1(X2,X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (? [X3] : ((? [X4] : (k1_funct_1(sK4,X4) != k1_funct_1(X3,X4) & r2_hidden(X4,k1_relset_1(sK2,sK3,sK4))) | ~r1_partfun1(sK4,X3)) & (! [X5] : (k1_funct_1(sK4,X5) = k1_funct_1(X3,X5) | ~r2_hidden(X5,k1_relset_1(sK2,sK3,sK4))) | r1_partfun1(sK4,X3)) & (k1_xboole_0 = sK2 | k1_xboole_0 != sK3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(X3,sK2,sK3) & v1_funct_1(X3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_1(sK4))),
% 3.21/1.00    introduced(choice_axiom,[])).
% 3.21/1.00  
% 3.21/1.00  fof(f37,plain,(
% 3.21/1.00    (((k1_funct_1(sK4,sK6) != k1_funct_1(sK5,sK6) & r2_hidden(sK6,k1_relset_1(sK2,sK3,sK4))) | ~r1_partfun1(sK4,sK5)) & (! [X5] : (k1_funct_1(sK4,X5) = k1_funct_1(sK5,X5) | ~r2_hidden(X5,k1_relset_1(sK2,sK3,sK4))) | r1_partfun1(sK4,sK5)) & (k1_xboole_0 = sK2 | k1_xboole_0 != sK3) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK5,sK2,sK3) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_1(sK4)),
% 3.21/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f33,f36,f35,f34])).
% 3.21/1.00  
% 3.21/1.00  fof(f58,plain,(
% 3.21/1.00    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 3.21/1.00    inference(cnf_transformation,[],[f37])).
% 3.21/1.00  
% 3.21/1.00  fof(f6,axiom,(
% 3.21/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 3.21/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.21/1.00  
% 3.21/1.00  fof(f17,plain,(
% 3.21/1.00    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.21/1.00    inference(ennf_transformation,[],[f6])).
% 3.21/1.00  
% 3.21/1.00  fof(f44,plain,(
% 3.21/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.21/1.00    inference(cnf_transformation,[],[f17])).
% 3.21/1.00  
% 3.21/1.00  fof(f7,axiom,(
% 3.21/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.21/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.21/1.00  
% 3.21/1.00  fof(f18,plain,(
% 3.21/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.21/1.00    inference(ennf_transformation,[],[f7])).
% 3.21/1.00  
% 3.21/1.00  fof(f19,plain,(
% 3.21/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.21/1.00    inference(flattening,[],[f18])).
% 3.21/1.00  
% 3.21/1.00  fof(f26,plain,(
% 3.21/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.21/1.00    inference(nnf_transformation,[],[f19])).
% 3.21/1.00  
% 3.21/1.00  fof(f45,plain,(
% 3.21/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.21/1.00    inference(cnf_transformation,[],[f26])).
% 3.21/1.00  
% 3.21/1.00  fof(f57,plain,(
% 3.21/1.00    v1_funct_2(sK5,sK2,sK3)),
% 3.21/1.00    inference(cnf_transformation,[],[f37])).
% 3.21/1.00  
% 3.21/1.00  fof(f1,axiom,(
% 3.21/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.21/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.21/1.00  
% 3.21/1.00  fof(f11,plain,(
% 3.21/1.00    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 3.21/1.00    inference(unused_predicate_definition_removal,[],[f1])).
% 3.21/1.00  
% 3.21/1.00  fof(f12,plain,(
% 3.21/1.00    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 3.21/1.00    inference(ennf_transformation,[],[f11])).
% 3.21/1.00  
% 3.21/1.00  fof(f24,plain,(
% 3.21/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.21/1.00    introduced(choice_axiom,[])).
% 3.21/1.00  
% 3.21/1.00  fof(f25,plain,(
% 3.21/1.00    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.21/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f24])).
% 3.21/1.00  
% 3.21/1.00  fof(f38,plain,(
% 3.21/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.21/1.00    inference(cnf_transformation,[],[f25])).
% 3.21/1.00  
% 3.21/1.00  fof(f55,plain,(
% 3.21/1.00    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 3.21/1.00    inference(cnf_transformation,[],[f37])).
% 3.21/1.00  
% 3.21/1.00  fof(f5,axiom,(
% 3.21/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 3.21/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.21/1.00  
% 3.21/1.00  fof(f16,plain,(
% 3.21/1.00    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.21/1.00    inference(ennf_transformation,[],[f5])).
% 3.21/1.00  
% 3.21/1.00  fof(f43,plain,(
% 3.21/1.00    ( ! [X2,X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.21/1.00    inference(cnf_transformation,[],[f16])).
% 3.21/1.00  
% 3.21/1.00  fof(f3,axiom,(
% 3.21/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 3.21/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.21/1.00  
% 3.21/1.00  fof(f14,plain,(
% 3.21/1.00    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.21/1.00    inference(ennf_transformation,[],[f3])).
% 3.21/1.00  
% 3.21/1.00  fof(f41,plain,(
% 3.21/1.00    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.21/1.00    inference(cnf_transformation,[],[f14])).
% 3.21/1.00  
% 3.21/1.00  fof(f39,plain,(
% 3.21/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 3.21/1.00    inference(cnf_transformation,[],[f25])).
% 3.21/1.00  
% 3.21/1.00  fof(f8,axiom,(
% 3.21/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) => (r1_partfun1(X0,X1) <=> ! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2))))))),
% 3.21/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.21/1.00  
% 3.21/1.00  fof(f20,plain,(
% 3.21/1.00    ! [X0] : (! [X1] : (((r1_partfun1(X0,X1) <=> ! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0)))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.21/1.00    inference(ennf_transformation,[],[f8])).
% 3.21/1.00  
% 3.21/1.00  fof(f21,plain,(
% 3.21/1.00    ! [X0] : (! [X1] : ((r1_partfun1(X0,X1) <=> ! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0)))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.21/1.00    inference(flattening,[],[f20])).
% 3.21/1.00  
% 3.21/1.00  fof(f27,plain,(
% 3.21/1.00    ! [X0] : (! [X1] : (((r1_partfun1(X0,X1) | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0)))) & (! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0))) | ~r1_partfun1(X0,X1))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.21/1.00    inference(nnf_transformation,[],[f21])).
% 3.21/1.00  
% 3.21/1.00  fof(f28,plain,(
% 3.21/1.00    ! [X0] : (! [X1] : (((r1_partfun1(X0,X1) | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0)))) & (! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r1_partfun1(X0,X1))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.21/1.00    inference(rectify,[],[f27])).
% 3.21/1.00  
% 3.21/1.00  fof(f29,plain,(
% 3.21/1.00    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1)) & r2_hidden(sK1(X0,X1),k1_relat_1(X0))))),
% 3.21/1.00    introduced(choice_axiom,[])).
% 3.21/1.00  
% 3.21/1.00  fof(f30,plain,(
% 3.21/1.00    ! [X0] : (! [X1] : (((r1_partfun1(X0,X1) | (k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1)) & r2_hidden(sK1(X0,X1),k1_relat_1(X0)))) & (! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r1_partfun1(X0,X1))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.21/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f28,f29])).
% 3.21/1.00  
% 3.21/1.00  fof(f52,plain,(
% 3.21/1.00    ( ! [X0,X1] : (r1_partfun1(X0,X1) | r2_hidden(sK1(X0,X1),k1_relat_1(X0)) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.21/1.00    inference(cnf_transformation,[],[f30])).
% 3.21/1.00  
% 3.21/1.00  fof(f60,plain,(
% 3.21/1.00    ( ! [X5] : (k1_funct_1(sK4,X5) = k1_funct_1(sK5,X5) | ~r2_hidden(X5,k1_relset_1(sK2,sK3,sK4)) | r1_partfun1(sK4,sK5)) )),
% 3.21/1.00    inference(cnf_transformation,[],[f37])).
% 3.21/1.00  
% 3.21/1.00  fof(f54,plain,(
% 3.21/1.00    v1_funct_1(sK4)),
% 3.21/1.00    inference(cnf_transformation,[],[f37])).
% 3.21/1.00  
% 3.21/1.00  fof(f4,axiom,(
% 3.21/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.21/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.21/1.00  
% 3.21/1.00  fof(f15,plain,(
% 3.21/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.21/1.00    inference(ennf_transformation,[],[f4])).
% 3.21/1.00  
% 3.21/1.00  fof(f42,plain,(
% 3.21/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.21/1.00    inference(cnf_transformation,[],[f15])).
% 3.21/1.00  
% 3.21/1.00  fof(f56,plain,(
% 3.21/1.00    v1_funct_1(sK5)),
% 3.21/1.00    inference(cnf_transformation,[],[f37])).
% 3.21/1.00  
% 3.21/1.00  fof(f61,plain,(
% 3.21/1.00    r2_hidden(sK6,k1_relset_1(sK2,sK3,sK4)) | ~r1_partfun1(sK4,sK5)),
% 3.21/1.00    inference(cnf_transformation,[],[f37])).
% 3.21/1.00  
% 3.21/1.00  fof(f51,plain,(
% 3.21/1.00    ( ! [X0,X3,X1] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r1_partfun1(X0,X1) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.21/1.00    inference(cnf_transformation,[],[f30])).
% 3.21/1.00  
% 3.21/1.00  fof(f62,plain,(
% 3.21/1.00    k1_funct_1(sK4,sK6) != k1_funct_1(sK5,sK6) | ~r1_partfun1(sK4,sK5)),
% 3.21/1.00    inference(cnf_transformation,[],[f37])).
% 3.21/1.00  
% 3.21/1.00  fof(f53,plain,(
% 3.21/1.00    ( ! [X0,X1] : (r1_partfun1(X0,X1) | k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1)) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.21/1.00    inference(cnf_transformation,[],[f30])).
% 3.21/1.00  
% 3.21/1.00  fof(f59,plain,(
% 3.21/1.00    k1_xboole_0 = sK2 | k1_xboole_0 != sK3),
% 3.21/1.00    inference(cnf_transformation,[],[f37])).
% 3.21/1.00  
% 3.21/1.00  fof(f46,plain,(
% 3.21/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.21/1.00    inference(cnf_transformation,[],[f26])).
% 3.21/1.00  
% 3.21/1.00  fof(f67,plain,(
% 3.21/1.00    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.21/1.00    inference(equality_resolution,[],[f46])).
% 3.21/1.00  
% 3.21/1.00  fof(f2,axiom,(
% 3.21/1.00    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 3.21/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.21/1.00  
% 3.21/1.00  fof(f13,plain,(
% 3.21/1.00    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 3.21/1.00    inference(ennf_transformation,[],[f2])).
% 3.21/1.00  
% 3.21/1.00  fof(f40,plain,(
% 3.21/1.00    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 3.21/1.00    inference(cnf_transformation,[],[f13])).
% 3.21/1.00  
% 3.21/1.00  cnf(c_20,negated_conjecture,
% 3.21/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 3.21/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_1818,plain,
% 3.21/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_6,plain,
% 3.21/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.21/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.21/1.00      inference(cnf_transformation,[],[f44]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_1825,plain,
% 3.21/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.21/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2469,plain,
% 3.21/1.00      ( k1_relset_1(sK2,sK3,sK5) = k1_relat_1(sK5) ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_1818,c_1825]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_12,plain,
% 3.21/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.21/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.21/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.21/1.00      | k1_xboole_0 = X2 ),
% 3.21/1.00      inference(cnf_transformation,[],[f45]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_21,negated_conjecture,
% 3.21/1.00      ( v1_funct_2(sK5,sK2,sK3) ),
% 3.21/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_555,plain,
% 3.21/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.21/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.21/1.00      | sK3 != X2
% 3.21/1.00      | sK2 != X1
% 3.21/1.00      | sK5 != X0
% 3.21/1.00      | k1_xboole_0 = X2 ),
% 3.21/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_21]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_556,plain,
% 3.21/1.00      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 3.21/1.00      | k1_relset_1(sK2,sK3,sK5) = sK2
% 3.21/1.00      | k1_xboole_0 = sK3 ),
% 3.21/1.00      inference(unflattening,[status(thm)],[c_555]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_558,plain,
% 3.21/1.00      ( k1_relset_1(sK2,sK3,sK5) = sK2 | k1_xboole_0 = sK3 ),
% 3.21/1.00      inference(global_propositional_subsumption,
% 3.21/1.00                [status(thm)],
% 3.21/1.00                [c_556,c_20]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2652,plain,
% 3.21/1.00      ( k1_relat_1(sK5) = sK2 | sK3 = k1_xboole_0 ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_2469,c_558]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_1,plain,
% 3.21/1.00      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.21/1.00      inference(cnf_transformation,[],[f38]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_1830,plain,
% 3.21/1.00      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 3.21/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_23,negated_conjecture,
% 3.21/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 3.21/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_1816,plain,
% 3.21/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2470,plain,
% 3.21/1.00      ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_1816,c_1825]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_5,plain,
% 3.21/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.21/1.00      | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 3.21/1.00      inference(cnf_transformation,[],[f43]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_1826,plain,
% 3.21/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.21/1.00      | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2762,plain,
% 3.21/1.00      ( m1_subset_1(k1_relat_1(sK4),k1_zfmisc_1(sK2)) = iProver_top
% 3.21/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_2470,c_1826]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_26,plain,
% 3.21/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_3181,plain,
% 3.21/1.00      ( m1_subset_1(k1_relat_1(sK4),k1_zfmisc_1(sK2)) = iProver_top ),
% 3.21/1.00      inference(global_propositional_subsumption,
% 3.21/1.00                [status(thm)],
% 3.21/1.00                [c_2762,c_26]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_3,plain,
% 3.21/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.21/1.00      | ~ r2_hidden(X2,X0)
% 3.21/1.00      | r2_hidden(X2,X1) ),
% 3.21/1.00      inference(cnf_transformation,[],[f41]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_1828,plain,
% 3.21/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.21/1.00      | r2_hidden(X2,X0) != iProver_top
% 3.21/1.00      | r2_hidden(X2,X1) = iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_3186,plain,
% 3.21/1.00      ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 3.21/1.00      | r2_hidden(X0,sK2) = iProver_top ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_3181,c_1828]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_3839,plain,
% 3.21/1.00      ( r2_hidden(sK0(k1_relat_1(sK4),X0),sK2) = iProver_top
% 3.21/1.00      | r1_tarski(k1_relat_1(sK4),X0) = iProver_top ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_1830,c_3186]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_0,plain,
% 3.21/1.00      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 3.21/1.00      inference(cnf_transformation,[],[f39]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_1831,plain,
% 3.21/1.00      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 3.21/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_4302,plain,
% 3.21/1.00      ( r1_tarski(k1_relat_1(sK4),sK2) = iProver_top ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_3839,c_1831]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_14,plain,
% 3.21/1.00      ( r1_partfun1(X0,X1)
% 3.21/1.00      | r2_hidden(sK1(X0,X1),k1_relat_1(X0))
% 3.21/1.00      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 3.21/1.00      | ~ v1_funct_1(X1)
% 3.21/1.00      | ~ v1_funct_1(X0)
% 3.21/1.00      | ~ v1_relat_1(X1)
% 3.21/1.00      | ~ v1_relat_1(X0) ),
% 3.21/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_1823,plain,
% 3.21/1.00      ( r1_partfun1(X0,X1) = iProver_top
% 3.21/1.00      | r2_hidden(sK1(X0,X1),k1_relat_1(X0)) = iProver_top
% 3.21/1.00      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) != iProver_top
% 3.21/1.00      | v1_funct_1(X1) != iProver_top
% 3.21/1.00      | v1_funct_1(X0) != iProver_top
% 3.21/1.00      | v1_relat_1(X1) != iProver_top
% 3.21/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_18,negated_conjecture,
% 3.21/1.00      ( r1_partfun1(sK4,sK5)
% 3.21/1.00      | ~ r2_hidden(X0,k1_relset_1(sK2,sK3,sK4))
% 3.21/1.00      | k1_funct_1(sK4,X0) = k1_funct_1(sK5,X0) ),
% 3.21/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_1819,plain,
% 3.21/1.00      ( k1_funct_1(sK4,X0) = k1_funct_1(sK5,X0)
% 3.21/1.00      | r1_partfun1(sK4,sK5) = iProver_top
% 3.21/1.00      | r2_hidden(X0,k1_relset_1(sK2,sK3,sK4)) != iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2730,plain,
% 3.21/1.00      ( k1_funct_1(sK5,X0) = k1_funct_1(sK4,X0)
% 3.21/1.00      | r1_partfun1(sK4,sK5) = iProver_top
% 3.21/1.00      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
% 3.21/1.00      inference(demodulation,[status(thm)],[c_2470,c_1819]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_3002,plain,
% 3.21/1.00      ( k1_funct_1(sK4,sK1(sK4,X0)) = k1_funct_1(sK5,sK1(sK4,X0))
% 3.21/1.00      | r1_partfun1(sK4,X0) = iProver_top
% 3.21/1.00      | r1_partfun1(sK4,sK5) = iProver_top
% 3.21/1.00      | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
% 3.21/1.00      | v1_funct_1(X0) != iProver_top
% 3.21/1.00      | v1_funct_1(sK4) != iProver_top
% 3.21/1.00      | v1_relat_1(X0) != iProver_top
% 3.21/1.00      | v1_relat_1(sK4) != iProver_top ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_1823,c_2730]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_24,negated_conjecture,
% 3.21/1.00      ( v1_funct_1(sK4) ),
% 3.21/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_25,plain,
% 3.21/1.00      ( v1_funct_1(sK4) = iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_4,plain,
% 3.21/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.21/1.00      | v1_relat_1(X0) ),
% 3.21/1.00      inference(cnf_transformation,[],[f42]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2000,plain,
% 3.21/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 3.21/1.00      | v1_relat_1(sK4) ),
% 3.21/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2001,plain,
% 3.21/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 3.21/1.00      | v1_relat_1(sK4) = iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_2000]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_3933,plain,
% 3.21/1.00      ( v1_relat_1(X0) != iProver_top
% 3.21/1.00      | k1_funct_1(sK4,sK1(sK4,X0)) = k1_funct_1(sK5,sK1(sK4,X0))
% 3.21/1.00      | r1_partfun1(sK4,X0) = iProver_top
% 3.21/1.00      | r1_partfun1(sK4,sK5) = iProver_top
% 3.21/1.00      | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
% 3.21/1.00      | v1_funct_1(X0) != iProver_top ),
% 3.21/1.00      inference(global_propositional_subsumption,
% 3.21/1.00                [status(thm)],
% 3.21/1.00                [c_3002,c_25,c_26,c_2001]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_3934,plain,
% 3.21/1.00      ( k1_funct_1(sK4,sK1(sK4,X0)) = k1_funct_1(sK5,sK1(sK4,X0))
% 3.21/1.00      | r1_partfun1(sK4,X0) = iProver_top
% 3.21/1.00      | r1_partfun1(sK4,sK5) = iProver_top
% 3.21/1.00      | r1_tarski(k1_relat_1(sK4),k1_relat_1(X0)) != iProver_top
% 3.21/1.00      | v1_funct_1(X0) != iProver_top
% 3.21/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.21/1.00      inference(renaming,[status(thm)],[c_3933]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_3947,plain,
% 3.21/1.00      ( k1_funct_1(sK4,sK1(sK4,sK5)) = k1_funct_1(sK5,sK1(sK4,sK5))
% 3.21/1.00      | sK3 = k1_xboole_0
% 3.21/1.00      | r1_partfun1(sK4,sK5) = iProver_top
% 3.21/1.00      | r1_tarski(k1_relat_1(sK4),sK2) != iProver_top
% 3.21/1.00      | v1_funct_1(sK5) != iProver_top
% 3.21/1.00      | v1_relat_1(sK5) != iProver_top ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_2652,c_3934]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_22,negated_conjecture,
% 3.21/1.00      ( v1_funct_1(sK5) ),
% 3.21/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_27,plain,
% 3.21/1.00      ( v1_funct_1(sK5) = iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_29,plain,
% 3.21/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_1997,plain,
% 3.21/1.00      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 3.21/1.00      | v1_relat_1(sK5) ),
% 3.21/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_1998,plain,
% 3.21/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 3.21/1.00      | v1_relat_1(sK5) = iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_1997]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_3988,plain,
% 3.21/1.00      ( k1_funct_1(sK4,sK1(sK4,sK5)) = k1_funct_1(sK5,sK1(sK4,sK5))
% 3.21/1.00      | sK3 = k1_xboole_0
% 3.21/1.00      | r1_partfun1(sK4,sK5) = iProver_top
% 3.21/1.00      | r1_tarski(k1_relat_1(sK4),sK2) != iProver_top ),
% 3.21/1.00      inference(global_propositional_subsumption,
% 3.21/1.00                [status(thm)],
% 3.21/1.00                [c_3947,c_27,c_29,c_1998]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_4376,plain,
% 3.21/1.00      ( k1_funct_1(sK4,sK1(sK4,sK5)) = k1_funct_1(sK5,sK1(sK4,sK5))
% 3.21/1.00      | sK3 = k1_xboole_0
% 3.21/1.00      | r1_partfun1(sK4,sK5) = iProver_top ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_4302,c_3988]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_17,negated_conjecture,
% 3.21/1.00      ( ~ r1_partfun1(sK4,sK5)
% 3.21/1.00      | r2_hidden(sK6,k1_relset_1(sK2,sK3,sK4)) ),
% 3.21/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_1820,plain,
% 3.21/1.00      ( r1_partfun1(sK4,sK5) != iProver_top
% 3.21/1.00      | r2_hidden(sK6,k1_relset_1(sK2,sK3,sK4)) = iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2731,plain,
% 3.21/1.00      ( r1_partfun1(sK4,sK5) != iProver_top
% 3.21/1.00      | r2_hidden(sK6,k1_relat_1(sK4)) = iProver_top ),
% 3.21/1.00      inference(demodulation,[status(thm)],[c_2470,c_1820]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_15,plain,
% 3.21/1.00      ( ~ r1_partfun1(X0,X1)
% 3.21/1.00      | ~ r2_hidden(X2,k1_relat_1(X0))
% 3.21/1.00      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 3.21/1.00      | ~ v1_funct_1(X1)
% 3.21/1.00      | ~ v1_funct_1(X0)
% 3.21/1.00      | ~ v1_relat_1(X1)
% 3.21/1.00      | ~ v1_relat_1(X0)
% 3.21/1.00      | k1_funct_1(X1,X2) = k1_funct_1(X0,X2) ),
% 3.21/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_1822,plain,
% 3.21/1.00      ( k1_funct_1(X0,X1) = k1_funct_1(X2,X1)
% 3.21/1.00      | r1_partfun1(X2,X0) != iProver_top
% 3.21/1.00      | r2_hidden(X1,k1_relat_1(X2)) != iProver_top
% 3.21/1.00      | r1_tarski(k1_relat_1(X2),k1_relat_1(X0)) != iProver_top
% 3.21/1.00      | v1_funct_1(X0) != iProver_top
% 3.21/1.00      | v1_funct_1(X2) != iProver_top
% 3.21/1.00      | v1_relat_1(X0) != iProver_top
% 3.21/1.00      | v1_relat_1(X2) != iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2880,plain,
% 3.21/1.00      ( k1_funct_1(X0,X1) = k1_funct_1(sK5,X1)
% 3.21/1.00      | sK3 = k1_xboole_0
% 3.21/1.00      | r1_partfun1(X0,sK5) != iProver_top
% 3.21/1.00      | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
% 3.21/1.00      | r1_tarski(k1_relat_1(X0),sK2) != iProver_top
% 3.21/1.00      | v1_funct_1(X0) != iProver_top
% 3.21/1.00      | v1_funct_1(sK5) != iProver_top
% 3.21/1.00      | v1_relat_1(X0) != iProver_top
% 3.21/1.00      | v1_relat_1(sK5) != iProver_top ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_2652,c_1822]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_4042,plain,
% 3.21/1.00      ( v1_relat_1(X0) != iProver_top
% 3.21/1.00      | k1_funct_1(X0,X1) = k1_funct_1(sK5,X1)
% 3.21/1.00      | sK3 = k1_xboole_0
% 3.21/1.00      | r1_partfun1(X0,sK5) != iProver_top
% 3.21/1.00      | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
% 3.21/1.00      | r1_tarski(k1_relat_1(X0),sK2) != iProver_top
% 3.21/1.00      | v1_funct_1(X0) != iProver_top ),
% 3.21/1.00      inference(global_propositional_subsumption,
% 3.21/1.00                [status(thm)],
% 3.21/1.00                [c_2880,c_27,c_29,c_1998]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_4043,plain,
% 3.21/1.00      ( k1_funct_1(X0,X1) = k1_funct_1(sK5,X1)
% 3.21/1.00      | sK3 = k1_xboole_0
% 3.21/1.00      | r1_partfun1(X0,sK5) != iProver_top
% 3.21/1.00      | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
% 3.21/1.00      | r1_tarski(k1_relat_1(X0),sK2) != iProver_top
% 3.21/1.00      | v1_funct_1(X0) != iProver_top
% 3.21/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.21/1.00      inference(renaming,[status(thm)],[c_4042]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_4057,plain,
% 3.21/1.00      ( k1_funct_1(sK5,sK6) = k1_funct_1(sK4,sK6)
% 3.21/1.00      | sK3 = k1_xboole_0
% 3.21/1.00      | r1_partfun1(sK4,sK5) != iProver_top
% 3.21/1.00      | r1_tarski(k1_relat_1(sK4),sK2) != iProver_top
% 3.21/1.00      | v1_funct_1(sK4) != iProver_top
% 3.21/1.00      | v1_relat_1(sK4) != iProver_top ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_2731,c_4043]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_4207,plain,
% 3.21/1.00      ( k1_funct_1(sK5,sK6) = k1_funct_1(sK4,sK6)
% 3.21/1.00      | sK3 = k1_xboole_0
% 3.21/1.00      | r1_partfun1(sK4,sK5) != iProver_top
% 3.21/1.00      | r1_tarski(k1_relat_1(sK4),sK2) != iProver_top ),
% 3.21/1.00      inference(global_propositional_subsumption,
% 3.21/1.00                [status(thm)],
% 3.21/1.00                [c_4057,c_25,c_26,c_2001]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_4375,plain,
% 3.21/1.00      ( k1_funct_1(sK5,sK6) = k1_funct_1(sK4,sK6)
% 3.21/1.00      | sK3 = k1_xboole_0
% 3.21/1.00      | r1_partfun1(sK4,sK5) != iProver_top ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_4302,c_4207]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_4709,plain,
% 3.21/1.00      ( k1_funct_1(sK5,sK6) = k1_funct_1(sK4,sK6)
% 3.21/1.00      | k1_funct_1(sK4,sK1(sK4,sK5)) = k1_funct_1(sK5,sK1(sK4,sK5))
% 3.21/1.00      | sK3 = k1_xboole_0 ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_4376,c_4375]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_16,negated_conjecture,
% 3.21/1.00      ( ~ r1_partfun1(sK4,sK5)
% 3.21/1.00      | k1_funct_1(sK4,sK6) != k1_funct_1(sK5,sK6) ),
% 3.21/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_34,plain,
% 3.21/1.00      ( k1_funct_1(sK4,sK6) != k1_funct_1(sK5,sK6)
% 3.21/1.00      | r1_partfun1(sK4,sK5) != iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_1445,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2368,plain,
% 3.21/1.00      ( k1_funct_1(sK5,sK6) != X0
% 3.21/1.00      | k1_funct_1(sK4,sK6) != X0
% 3.21/1.00      | k1_funct_1(sK4,sK6) = k1_funct_1(sK5,sK6) ),
% 3.21/1.00      inference(instantiation,[status(thm)],[c_1445]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2625,plain,
% 3.21/1.00      ( k1_funct_1(sK5,sK6) != k1_funct_1(X0,sK6)
% 3.21/1.00      | k1_funct_1(sK4,sK6) != k1_funct_1(X0,sK6)
% 3.21/1.00      | k1_funct_1(sK4,sK6) = k1_funct_1(sK5,sK6) ),
% 3.21/1.00      inference(instantiation,[status(thm)],[c_2368]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_6166,plain,
% 3.21/1.00      ( k1_funct_1(sK5,sK6) != k1_funct_1(sK4,sK6)
% 3.21/1.00      | k1_funct_1(sK4,sK6) = k1_funct_1(sK5,sK6)
% 3.21/1.00      | k1_funct_1(sK4,sK6) != k1_funct_1(sK4,sK6) ),
% 3.21/1.00      inference(instantiation,[status(thm)],[c_2625]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_1444,plain,( X0 = X0 ),theory(equality) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_6167,plain,
% 3.21/1.00      ( k1_funct_1(sK4,sK6) = k1_funct_1(sK4,sK6) ),
% 3.21/1.00      inference(instantiation,[status(thm)],[c_1444]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_6287,plain,
% 3.21/1.00      ( k1_funct_1(sK4,sK1(sK4,sK5)) = k1_funct_1(sK5,sK1(sK4,sK5))
% 3.21/1.00      | sK3 = k1_xboole_0 ),
% 3.21/1.00      inference(global_propositional_subsumption,
% 3.21/1.00                [status(thm)],
% 3.21/1.00                [c_4709,c_34,c_3988,c_4302,c_6166,c_6167]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_13,plain,
% 3.21/1.00      ( r1_partfun1(X0,X1)
% 3.21/1.00      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 3.21/1.00      | ~ v1_funct_1(X1)
% 3.21/1.00      | ~ v1_funct_1(X0)
% 3.21/1.00      | ~ v1_relat_1(X1)
% 3.21/1.00      | ~ v1_relat_1(X0)
% 3.21/1.00      | k1_funct_1(X1,sK1(X0,X1)) != k1_funct_1(X0,sK1(X0,X1)) ),
% 3.21/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_1824,plain,
% 3.21/1.00      ( k1_funct_1(X0,sK1(X1,X0)) != k1_funct_1(X1,sK1(X1,X0))
% 3.21/1.00      | r1_partfun1(X1,X0) = iProver_top
% 3.21/1.00      | r1_tarski(k1_relat_1(X1),k1_relat_1(X0)) != iProver_top
% 3.21/1.00      | v1_funct_1(X0) != iProver_top
% 3.21/1.00      | v1_funct_1(X1) != iProver_top
% 3.21/1.00      | v1_relat_1(X0) != iProver_top
% 3.21/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_6291,plain,
% 3.21/1.00      ( sK3 = k1_xboole_0
% 3.21/1.00      | r1_partfun1(sK4,sK5) = iProver_top
% 3.21/1.00      | r1_tarski(k1_relat_1(sK4),k1_relat_1(sK5)) != iProver_top
% 3.21/1.00      | v1_funct_1(sK5) != iProver_top
% 3.21/1.00      | v1_funct_1(sK4) != iProver_top
% 3.21/1.00      | v1_relat_1(sK5) != iProver_top
% 3.21/1.00      | v1_relat_1(sK4) != iProver_top ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_6287,c_1824]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_4055,plain,
% 3.21/1.00      ( k1_funct_1(X0,sK0(k1_relat_1(X0),X1)) = k1_funct_1(sK5,sK0(k1_relat_1(X0),X1))
% 3.21/1.00      | sK3 = k1_xboole_0
% 3.21/1.00      | r1_partfun1(X0,sK5) != iProver_top
% 3.21/1.00      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 3.21/1.00      | r1_tarski(k1_relat_1(X0),sK2) != iProver_top
% 3.21/1.00      | v1_funct_1(X0) != iProver_top
% 3.21/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_1830,c_4043]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_5781,plain,
% 3.21/1.00      ( k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0)) = k1_funct_1(sK5,sK0(k1_relat_1(sK4),X0))
% 3.21/1.00      | sK3 = k1_xboole_0
% 3.21/1.00      | r1_partfun1(sK4,sK5) != iProver_top
% 3.21/1.00      | r1_tarski(k1_relat_1(sK4),X0) = iProver_top
% 3.21/1.00      | v1_funct_1(sK4) != iProver_top
% 3.21/1.00      | v1_relat_1(sK4) != iProver_top ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_4302,c_4055]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_6324,plain,
% 3.21/1.00      ( r1_partfun1(sK4,sK5) != iProver_top | sK3 = k1_xboole_0 ),
% 3.21/1.00      inference(global_propositional_subsumption,
% 3.21/1.00                [status(thm)],
% 3.21/1.00                [c_5781,c_34,c_4207,c_4302,c_6166,c_6167]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_6325,plain,
% 3.21/1.00      ( sK3 = k1_xboole_0 | r1_partfun1(sK4,sK5) != iProver_top ),
% 3.21/1.00      inference(renaming,[status(thm)],[c_6324]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_6446,plain,
% 3.21/1.00      ( sK3 = k1_xboole_0
% 3.21/1.00      | r1_tarski(k1_relat_1(sK4),k1_relat_1(sK5)) != iProver_top ),
% 3.21/1.00      inference(global_propositional_subsumption,
% 3.21/1.00                [status(thm)],
% 3.21/1.00                [c_6291,c_25,c_26,c_27,c_29,c_1998,c_2001,c_6325]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_6453,plain,
% 3.21/1.00      ( sK3 = k1_xboole_0
% 3.21/1.00      | r1_tarski(k1_relat_1(sK4),sK2) != iProver_top ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_2652,c_6446]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_6581,plain,
% 3.21/1.00      ( sK3 = k1_xboole_0 ),
% 3.21/1.00      inference(global_propositional_subsumption,
% 3.21/1.00                [status(thm)],
% 3.21/1.00                [c_6453,c_4302]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_19,negated_conjecture,
% 3.21/1.00      ( k1_xboole_0 != sK3 | k1_xboole_0 = sK2 ),
% 3.21/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_6606,plain,
% 3.21/1.00      ( sK2 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 3.21/1.00      inference(demodulation,[status(thm)],[c_6581,c_19]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_6607,plain,
% 3.21/1.00      ( sK2 = k1_xboole_0 ),
% 3.21/1.00      inference(equality_resolution_simp,[status(thm)],[c_6606]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_3841,plain,
% 3.21/1.00      ( r1_partfun1(sK4,sK5) != iProver_top
% 3.21/1.00      | r2_hidden(sK6,sK2) = iProver_top ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_2731,c_3186]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_6715,plain,
% 3.21/1.00      ( r1_partfun1(sK4,sK5) != iProver_top
% 3.21/1.00      | r2_hidden(sK6,k1_xboole_0) = iProver_top ),
% 3.21/1.00      inference(demodulation,[status(thm)],[c_6607,c_3841]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2055,plain,
% 3.21/1.00      ( r1_partfun1(X0,sK5)
% 3.21/1.00      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(sK5))
% 3.21/1.00      | ~ v1_funct_1(X0)
% 3.21/1.00      | ~ v1_funct_1(sK5)
% 3.21/1.00      | ~ v1_relat_1(X0)
% 3.21/1.00      | ~ v1_relat_1(sK5)
% 3.21/1.00      | k1_funct_1(sK5,sK1(X0,sK5)) != k1_funct_1(X0,sK1(X0,sK5)) ),
% 3.21/1.00      inference(instantiation,[status(thm)],[c_13]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2131,plain,
% 3.21/1.00      ( r1_partfun1(sK4,sK5)
% 3.21/1.00      | ~ r1_tarski(k1_relat_1(sK4),k1_relat_1(sK5))
% 3.21/1.00      | ~ v1_funct_1(sK5)
% 3.21/1.00      | ~ v1_funct_1(sK4)
% 3.21/1.00      | ~ v1_relat_1(sK5)
% 3.21/1.00      | ~ v1_relat_1(sK4)
% 3.21/1.00      | k1_funct_1(sK5,sK1(sK4,sK5)) != k1_funct_1(sK4,sK1(sK4,sK5)) ),
% 3.21/1.00      inference(instantiation,[status(thm)],[c_2055]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2132,plain,
% 3.21/1.00      ( k1_funct_1(sK5,sK1(sK4,sK5)) != k1_funct_1(sK4,sK1(sK4,sK5))
% 3.21/1.00      | r1_partfun1(sK4,sK5) = iProver_top
% 3.21/1.00      | r1_tarski(k1_relat_1(sK4),k1_relat_1(sK5)) != iProver_top
% 3.21/1.00      | v1_funct_1(sK5) != iProver_top
% 3.21/1.00      | v1_funct_1(sK4) != iProver_top
% 3.21/1.00      | v1_relat_1(sK5) != iProver_top
% 3.21/1.00      | v1_relat_1(sK4) != iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_2131]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_1446,plain,
% 3.21/1.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.21/1.00      theory(equality) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2173,plain,
% 3.21/1.00      ( ~ r1_tarski(X0,X1)
% 3.21/1.00      | r1_tarski(k1_relat_1(sK4),k1_relat_1(sK5))
% 3.21/1.00      | k1_relat_1(sK5) != X1
% 3.21/1.00      | k1_relat_1(sK4) != X0 ),
% 3.21/1.00      inference(instantiation,[status(thm)],[c_1446]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2174,plain,
% 3.21/1.00      ( k1_relat_1(sK5) != X0
% 3.21/1.00      | k1_relat_1(sK4) != X1
% 3.21/1.00      | r1_tarski(X1,X0) != iProver_top
% 3.21/1.00      | r1_tarski(k1_relat_1(sK4),k1_relat_1(sK5)) = iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_2173]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2176,plain,
% 3.21/1.00      ( k1_relat_1(sK5) != k1_xboole_0
% 3.21/1.00      | k1_relat_1(sK4) != k1_xboole_0
% 3.21/1.00      | r1_tarski(k1_relat_1(sK4),k1_relat_1(sK5)) = iProver_top
% 3.21/1.00      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.21/1.00      inference(instantiation,[status(thm)],[c_2174]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2335,plain,
% 3.21/1.00      ( r1_tarski(X0,X0) = iProver_top ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_1830,c_1831]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2337,plain,
% 3.21/1.00      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 3.21/1.00      inference(instantiation,[status(thm)],[c_2335]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_6600,plain,
% 3.21/1.00      ( k1_relset_1(sK2,k1_xboole_0,sK5) = k1_relat_1(sK5) ),
% 3.21/1.00      inference(demodulation,[status(thm)],[c_6581,c_2469]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_11,plain,
% 3.21/1.00      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 3.21/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.21/1.00      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 3.21/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_542,plain,
% 3.21/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.21/1.00      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 3.21/1.00      | sK3 != X1
% 3.21/1.00      | sK2 != k1_xboole_0
% 3.21/1.00      | sK5 != X0 ),
% 3.21/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_21]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_543,plain,
% 3.21/1.00      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)))
% 3.21/1.00      | k1_relset_1(k1_xboole_0,sK3,sK5) = k1_xboole_0
% 3.21/1.00      | sK2 != k1_xboole_0 ),
% 3.21/1.00      inference(unflattening,[status(thm)],[c_542]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_1813,plain,
% 3.21/1.00      ( k1_relset_1(k1_xboole_0,sK3,sK5) = k1_xboole_0
% 3.21/1.00      | sK2 != k1_xboole_0
% 3.21/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_543]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_6602,plain,
% 3.21/1.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK5) = k1_xboole_0
% 3.21/1.00      | sK2 != k1_xboole_0
% 3.21/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 3.21/1.00      inference(demodulation,[status(thm)],[c_6581,c_1813]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_6616,plain,
% 3.21/1.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK5) = k1_xboole_0
% 3.21/1.00      | k1_xboole_0 != k1_xboole_0
% 3.21/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 3.21/1.00      inference(light_normalisation,[status(thm)],[c_6602,c_6607]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_6617,plain,
% 3.21/1.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK5) = k1_xboole_0
% 3.21/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 3.21/1.00      inference(equality_resolution_simp,[status(thm)],[c_6616]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_6604,plain,
% 3.21/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) = iProver_top ),
% 3.21/1.00      inference(demodulation,[status(thm)],[c_6581,c_1818]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_6613,plain,
% 3.21/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 3.21/1.00      inference(light_normalisation,[status(thm)],[c_6604,c_6607]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_6620,plain,
% 3.21/1.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK5) = k1_xboole_0 ),
% 3.21/1.00      inference(forward_subsumption_resolution,
% 3.21/1.00                [status(thm)],
% 3.21/1.00                [c_6617,c_6613]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_6623,plain,
% 3.21/1.00      ( k1_relat_1(sK5) = k1_xboole_0 ),
% 3.21/1.00      inference(light_normalisation,[status(thm)],[c_6600,c_6607,c_6620]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_6712,plain,
% 3.21/1.00      ( r1_tarski(k1_relat_1(sK4),k1_xboole_0) = iProver_top ),
% 3.21/1.00      inference(demodulation,[status(thm)],[c_6607,c_4302]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_6834,plain,
% 3.21/1.00      ( k1_funct_1(sK4,sK1(sK4,sK5)) = k1_funct_1(sK5,sK1(sK4,sK5))
% 3.21/1.00      | r1_partfun1(sK4,sK5) = iProver_top
% 3.21/1.00      | r1_tarski(k1_relat_1(sK4),k1_xboole_0) != iProver_top
% 3.21/1.00      | v1_funct_1(sK5) != iProver_top
% 3.21/1.00      | v1_relat_1(sK5) != iProver_top ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_6623,c_3934]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_3236,plain,
% 3.21/1.00      ( k1_funct_1(sK5,sK1(sK4,sK5)) != X0
% 3.21/1.00      | k1_funct_1(sK5,sK1(sK4,sK5)) = k1_funct_1(sK4,sK1(sK4,sK5))
% 3.21/1.00      | k1_funct_1(sK4,sK1(sK4,sK5)) != X0 ),
% 3.21/1.00      inference(instantiation,[status(thm)],[c_1445]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_3611,plain,
% 3.21/1.00      ( k1_funct_1(sK5,sK1(sK4,sK5)) != k1_funct_1(X0,sK1(sK4,sK5))
% 3.21/1.00      | k1_funct_1(sK5,sK1(sK4,sK5)) = k1_funct_1(sK4,sK1(sK4,sK5))
% 3.21/1.00      | k1_funct_1(sK4,sK1(sK4,sK5)) != k1_funct_1(X0,sK1(sK4,sK5)) ),
% 3.21/1.00      inference(instantiation,[status(thm)],[c_3236]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_6921,plain,
% 3.21/1.00      ( k1_funct_1(sK5,sK1(sK4,sK5)) != k1_funct_1(sK5,sK1(sK4,sK5))
% 3.21/1.00      | k1_funct_1(sK5,sK1(sK4,sK5)) = k1_funct_1(sK4,sK1(sK4,sK5))
% 3.21/1.00      | k1_funct_1(sK4,sK1(sK4,sK5)) != k1_funct_1(sK5,sK1(sK4,sK5)) ),
% 3.21/1.00      inference(instantiation,[status(thm)],[c_3611]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_6922,plain,
% 3.21/1.00      ( k1_funct_1(sK5,sK1(sK4,sK5)) = k1_funct_1(sK5,sK1(sK4,sK5)) ),
% 3.21/1.00      inference(instantiation,[status(thm)],[c_1444]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2,plain,
% 3.21/1.00      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 3.21/1.00      inference(cnf_transformation,[],[f40]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_1829,plain,
% 3.21/1.00      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_6927,plain,
% 3.21/1.00      ( k1_relat_1(sK4) = k1_xboole_0 ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_6712,c_1829]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_7536,plain,
% 3.21/1.00      ( r2_hidden(sK6,k1_xboole_0) = iProver_top ),
% 3.21/1.00      inference(global_propositional_subsumption,
% 3.21/1.00                [status(thm)],
% 3.21/1.00                [c_6715,c_25,c_26,c_27,c_29,c_1998,c_2001,c_2132,c_2176,
% 3.21/1.00                 c_2337,c_6623,c_6712,c_6834,c_6921,c_6922,c_6927]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_7164,plain,
% 3.21/1.00      ( k1_funct_1(X0,X1) = k1_funct_1(sK4,X1)
% 3.21/1.00      | r1_partfun1(X0,sK4) != iProver_top
% 3.21/1.00      | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
% 3.21/1.00      | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
% 3.21/1.00      | v1_funct_1(X0) != iProver_top
% 3.21/1.00      | v1_funct_1(sK4) != iProver_top
% 3.21/1.00      | v1_relat_1(X0) != iProver_top
% 3.21/1.00      | v1_relat_1(sK4) != iProver_top ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_6927,c_1822]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_7740,plain,
% 3.21/1.00      ( v1_relat_1(X0) != iProver_top
% 3.21/1.00      | k1_funct_1(X0,X1) = k1_funct_1(sK4,X1)
% 3.21/1.00      | r1_partfun1(X0,sK4) != iProver_top
% 3.21/1.00      | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
% 3.21/1.00      | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
% 3.21/1.00      | v1_funct_1(X0) != iProver_top ),
% 3.21/1.00      inference(global_propositional_subsumption,
% 3.21/1.00                [status(thm)],
% 3.21/1.00                [c_7164,c_25,c_26,c_2001]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_7741,plain,
% 3.21/1.00      ( k1_funct_1(X0,X1) = k1_funct_1(sK4,X1)
% 3.21/1.00      | r1_partfun1(X0,sK4) != iProver_top
% 3.21/1.00      | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
% 3.21/1.00      | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
% 3.21/1.00      | v1_funct_1(X0) != iProver_top
% 3.21/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.21/1.00      inference(renaming,[status(thm)],[c_7740]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_7755,plain,
% 3.21/1.00      ( k1_funct_1(sK5,X0) = k1_funct_1(sK4,X0)
% 3.21/1.00      | r1_partfun1(sK5,sK4) != iProver_top
% 3.21/1.00      | r2_hidden(X0,k1_xboole_0) != iProver_top
% 3.21/1.00      | r1_tarski(k1_relat_1(sK5),k1_xboole_0) != iProver_top
% 3.21/1.00      | v1_funct_1(sK5) != iProver_top
% 3.21/1.00      | v1_relat_1(sK5) != iProver_top ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_6623,c_7741]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_7763,plain,
% 3.21/1.00      ( k1_funct_1(sK5,X0) = k1_funct_1(sK4,X0)
% 3.21/1.00      | r1_partfun1(sK5,sK4) != iProver_top
% 3.21/1.00      | r2_hidden(X0,k1_xboole_0) != iProver_top
% 3.21/1.00      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 3.21/1.00      | v1_funct_1(sK5) != iProver_top
% 3.21/1.00      | v1_relat_1(sK5) != iProver_top ),
% 3.21/1.00      inference(light_normalisation,[status(thm)],[c_7755,c_6623]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_6836,plain,
% 3.21/1.00      ( k1_funct_1(X0,X1) = k1_funct_1(sK5,X1)
% 3.21/1.00      | r1_partfun1(X0,sK5) != iProver_top
% 3.21/1.00      | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
% 3.21/1.00      | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
% 3.21/1.00      | v1_funct_1(X0) != iProver_top
% 3.21/1.00      | v1_funct_1(sK5) != iProver_top
% 3.21/1.00      | v1_relat_1(X0) != iProver_top
% 3.21/1.00      | v1_relat_1(sK5) != iProver_top ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_6623,c_1822]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_7281,plain,
% 3.21/1.00      ( v1_relat_1(X0) != iProver_top
% 3.21/1.00      | k1_funct_1(X0,X1) = k1_funct_1(sK5,X1)
% 3.21/1.00      | r1_partfun1(X0,sK5) != iProver_top
% 3.21/1.00      | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
% 3.21/1.00      | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
% 3.21/1.00      | v1_funct_1(X0) != iProver_top ),
% 3.21/1.00      inference(global_propositional_subsumption,
% 3.21/1.00                [status(thm)],
% 3.21/1.00                [c_6836,c_27,c_29,c_1998]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_7282,plain,
% 3.21/1.00      ( k1_funct_1(X0,X1) = k1_funct_1(sK5,X1)
% 3.21/1.00      | r1_partfun1(X0,sK5) != iProver_top
% 3.21/1.00      | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
% 3.21/1.00      | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
% 3.21/1.00      | v1_funct_1(X0) != iProver_top
% 3.21/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.21/1.00      inference(renaming,[status(thm)],[c_7281]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_7297,plain,
% 3.21/1.00      ( k1_funct_1(sK5,X0) = k1_funct_1(sK4,X0)
% 3.21/1.00      | r1_partfun1(sK4,sK5) != iProver_top
% 3.21/1.00      | r2_hidden(X0,k1_xboole_0) != iProver_top
% 3.21/1.00      | r1_tarski(k1_relat_1(sK4),k1_xboole_0) != iProver_top
% 3.21/1.00      | v1_funct_1(sK4) != iProver_top
% 3.21/1.00      | v1_relat_1(sK4) != iProver_top ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_6927,c_7282]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_7304,plain,
% 3.21/1.00      ( k1_funct_1(sK5,X0) = k1_funct_1(sK4,X0)
% 3.21/1.00      | r1_partfun1(sK4,sK5) != iProver_top
% 3.21/1.00      | r2_hidden(X0,k1_xboole_0) != iProver_top
% 3.21/1.00      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 3.21/1.00      | v1_funct_1(sK4) != iProver_top
% 3.21/1.00      | v1_relat_1(sK4) != iProver_top ),
% 3.21/1.00      inference(light_normalisation,[status(thm)],[c_7297,c_6927]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_8891,plain,
% 3.21/1.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 3.21/1.00      | k1_funct_1(sK5,X0) = k1_funct_1(sK4,X0) ),
% 3.21/1.00      inference(global_propositional_subsumption,
% 3.21/1.00                [status(thm)],
% 3.21/1.00                [c_7763,c_25,c_26,c_27,c_29,c_1998,c_2001,c_2132,c_2176,
% 3.21/1.00                 c_2337,c_6623,c_6712,c_6834,c_6921,c_6922,c_6927,c_7304]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_8892,plain,
% 3.21/1.00      ( k1_funct_1(sK5,X0) = k1_funct_1(sK4,X0)
% 3.21/1.00      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.21/1.00      inference(renaming,[status(thm)],[c_8891]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_8900,plain,
% 3.21/1.00      ( k1_funct_1(sK5,sK6) = k1_funct_1(sK4,sK6) ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_7536,c_8892]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_7063,plain,
% 3.21/1.00      ( k1_funct_1(sK5,X0) = k1_funct_1(sK4,X0)
% 3.21/1.00      | r1_partfun1(sK4,sK5) = iProver_top
% 3.21/1.00      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.21/1.00      inference(demodulation,[status(thm)],[c_6927,c_2730]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_8467,plain,
% 3.21/1.00      ( r1_partfun1(sK4,sK5) = iProver_top ),
% 3.21/1.00      inference(global_propositional_subsumption,
% 3.21/1.00                [status(thm)],
% 3.21/1.00                [c_7063,c_25,c_26,c_27,c_29,c_1998,c_2001,c_2132,c_2176,
% 3.21/1.00                 c_2337,c_6623,c_6712,c_6834,c_6921,c_6922,c_6927]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(contradiction,plain,
% 3.21/1.00      ( $false ),
% 3.21/1.00      inference(minisat,[status(thm)],[c_8900,c_8467,c_6167,c_6166,c_34]) ).
% 3.21/1.00  
% 3.21/1.00  
% 3.21/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.21/1.00  
% 3.21/1.00  ------                               Statistics
% 3.21/1.00  
% 3.21/1.00  ------ General
% 3.21/1.00  
% 3.21/1.00  abstr_ref_over_cycles:                  0
% 3.21/1.00  abstr_ref_under_cycles:                 0
% 3.21/1.00  gc_basic_clause_elim:                   0
% 3.21/1.00  forced_gc_time:                         0
% 3.21/1.00  parsing_time:                           0.01
% 3.21/1.00  unif_index_cands_time:                  0.
% 3.21/1.00  unif_index_add_time:                    0.
% 3.21/1.00  orderings_time:                         0.
% 3.21/1.00  out_proof_time:                         0.01
% 3.21/1.00  total_time:                             0.263
% 3.21/1.00  num_of_symbols:                         51
% 3.21/1.00  num_of_terms:                           5354
% 3.21/1.00  
% 3.21/1.00  ------ Preprocessing
% 3.21/1.00  
% 3.21/1.00  num_of_splits:                          0
% 3.21/1.00  num_of_split_atoms:                     0
% 3.21/1.00  num_of_reused_defs:                     0
% 3.21/1.00  num_eq_ax_congr_red:                    18
% 3.21/1.00  num_of_sem_filtered_clauses:            1
% 3.21/1.00  num_of_subtypes:                        0
% 3.21/1.00  monotx_restored_types:                  0
% 3.21/1.00  sat_num_of_epr_types:                   0
% 3.21/1.00  sat_num_of_non_cyclic_types:            0
% 3.21/1.00  sat_guarded_non_collapsed_types:        0
% 3.21/1.00  num_pure_diseq_elim:                    0
% 3.21/1.00  simp_replaced_by:                       0
% 3.21/1.00  res_preprocessed:                       111
% 3.21/1.00  prep_upred:                             0
% 3.21/1.00  prep_unflattend:                        79
% 3.21/1.00  smt_new_axioms:                         0
% 3.21/1.00  pred_elim_cands:                        6
% 3.21/1.00  pred_elim:                              1
% 3.21/1.00  pred_elim_cl:                           4
% 3.21/1.00  pred_elim_cycles:                       5
% 3.21/1.00  merged_defs:                            0
% 3.21/1.00  merged_defs_ncl:                        0
% 3.21/1.00  bin_hyper_res:                          0
% 3.21/1.00  prep_cycles:                            4
% 3.21/1.00  pred_elim_time:                         0.021
% 3.21/1.00  splitting_time:                         0.
% 3.21/1.00  sem_filter_time:                        0.
% 3.21/1.00  monotx_time:                            0.001
% 3.21/1.00  subtype_inf_time:                       0.
% 3.21/1.00  
% 3.21/1.00  ------ Problem properties
% 3.21/1.00  
% 3.21/1.00  clauses:                                21
% 3.21/1.00  conjectures:                            8
% 3.21/1.00  epr:                                    4
% 3.21/1.00  horn:                                   16
% 3.21/1.00  ground:                                 10
% 3.21/1.00  unary:                                  4
% 3.21/1.00  binary:                                 10
% 3.21/1.00  lits:                                   59
% 3.21/1.00  lits_eq:                                15
% 3.21/1.00  fd_pure:                                0
% 3.21/1.00  fd_pseudo:                              0
% 3.21/1.00  fd_cond:                                1
% 3.21/1.00  fd_pseudo_cond:                         0
% 3.21/1.00  ac_symbols:                             0
% 3.21/1.00  
% 3.21/1.00  ------ Propositional Solver
% 3.21/1.00  
% 3.21/1.00  prop_solver_calls:                      29
% 3.21/1.00  prop_fast_solver_calls:                 1539
% 3.21/1.00  smt_solver_calls:                       0
% 3.21/1.00  smt_fast_solver_calls:                  0
% 3.21/1.00  prop_num_of_clauses:                    2524
% 3.21/1.00  prop_preprocess_simplified:             6210
% 3.21/1.00  prop_fo_subsumed:                       97
% 3.21/1.00  prop_solver_time:                       0.
% 3.21/1.00  smt_solver_time:                        0.
% 3.21/1.00  smt_fast_solver_time:                   0.
% 3.21/1.00  prop_fast_solver_time:                  0.
% 3.21/1.00  prop_unsat_core_time:                   0.
% 3.21/1.00  
% 3.21/1.00  ------ QBF
% 3.21/1.00  
% 3.21/1.00  qbf_q_res:                              0
% 3.21/1.00  qbf_num_tautologies:                    0
% 3.21/1.00  qbf_prep_cycles:                        0
% 3.21/1.00  
% 3.21/1.00  ------ BMC1
% 3.21/1.00  
% 3.21/1.00  bmc1_current_bound:                     -1
% 3.21/1.00  bmc1_last_solved_bound:                 -1
% 3.21/1.00  bmc1_unsat_core_size:                   -1
% 3.21/1.00  bmc1_unsat_core_parents_size:           -1
% 3.21/1.00  bmc1_merge_next_fun:                    0
% 3.21/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.21/1.00  
% 3.21/1.00  ------ Instantiation
% 3.21/1.00  
% 3.21/1.00  inst_num_of_clauses:                    845
% 3.21/1.00  inst_num_in_passive:                    44
% 3.21/1.00  inst_num_in_active:                     537
% 3.21/1.00  inst_num_in_unprocessed:                264
% 3.21/1.00  inst_num_of_loops:                      680
% 3.21/1.00  inst_num_of_learning_restarts:          0
% 3.21/1.00  inst_num_moves_active_passive:          140
% 3.21/1.00  inst_lit_activity:                      0
% 3.21/1.00  inst_lit_activity_moves:                0
% 3.21/1.00  inst_num_tautologies:                   0
% 3.21/1.00  inst_num_prop_implied:                  0
% 3.21/1.00  inst_num_existing_simplified:           0
% 3.21/1.00  inst_num_eq_res_simplified:             0
% 3.21/1.00  inst_num_child_elim:                    0
% 3.21/1.00  inst_num_of_dismatching_blockings:      206
% 3.21/1.00  inst_num_of_non_proper_insts:           874
% 3.21/1.00  inst_num_of_duplicates:                 0
% 3.21/1.00  inst_inst_num_from_inst_to_res:         0
% 3.21/1.00  inst_dismatching_checking_time:         0.
% 3.21/1.00  
% 3.21/1.00  ------ Resolution
% 3.21/1.00  
% 3.21/1.00  res_num_of_clauses:                     0
% 3.21/1.00  res_num_in_passive:                     0
% 3.21/1.00  res_num_in_active:                      0
% 3.21/1.00  res_num_of_loops:                       115
% 3.21/1.00  res_forward_subset_subsumed:            72
% 3.21/1.00  res_backward_subset_subsumed:           0
% 3.21/1.00  res_forward_subsumed:                   0
% 3.21/1.00  res_backward_subsumed:                  0
% 3.21/1.00  res_forward_subsumption_resolution:     0
% 3.21/1.00  res_backward_subsumption_resolution:    0
% 3.21/1.00  res_clause_to_clause_subsumption:       768
% 3.21/1.00  res_orphan_elimination:                 0
% 3.21/1.00  res_tautology_del:                      161
% 3.21/1.00  res_num_eq_res_simplified:              0
% 3.21/1.00  res_num_sel_changes:                    0
% 3.21/1.00  res_moves_from_active_to_pass:          0
% 3.21/1.00  
% 3.21/1.00  ------ Superposition
% 3.21/1.00  
% 3.21/1.00  sup_time_total:                         0.
% 3.21/1.00  sup_time_generating:                    0.
% 3.21/1.00  sup_time_sim_full:                      0.
% 3.21/1.00  sup_time_sim_immed:                     0.
% 3.21/1.00  
% 3.21/1.00  sup_num_of_clauses:                     121
% 3.21/1.00  sup_num_in_active:                      68
% 3.21/1.00  sup_num_in_passive:                     53
% 3.21/1.00  sup_num_of_loops:                       135
% 3.21/1.00  sup_fw_superposition:                   127
% 3.21/1.00  sup_bw_superposition:                   74
% 3.21/1.00  sup_immediate_simplified:               51
% 3.21/1.00  sup_given_eliminated:                   0
% 3.21/1.00  comparisons_done:                       0
% 3.21/1.00  comparisons_avoided:                    76
% 3.21/1.00  
% 3.21/1.00  ------ Simplifications
% 3.21/1.00  
% 3.21/1.00  
% 3.21/1.00  sim_fw_subset_subsumed:                 6
% 3.21/1.00  sim_bw_subset_subsumed:                 11
% 3.21/1.00  sim_fw_subsumed:                        21
% 3.21/1.00  sim_bw_subsumed:                        1
% 3.21/1.00  sim_fw_subsumption_res:                 3
% 3.21/1.00  sim_bw_subsumption_res:                 0
% 3.21/1.00  sim_tautology_del:                      15
% 3.21/1.00  sim_eq_tautology_del:                   28
% 3.21/1.00  sim_eq_res_simp:                        4
% 3.21/1.00  sim_fw_demodulated:                     0
% 3.21/1.00  sim_bw_demodulated:                     59
% 3.21/1.00  sim_light_normalised:                   40
% 3.21/1.00  sim_joinable_taut:                      0
% 3.21/1.00  sim_joinable_simp:                      0
% 3.21/1.00  sim_ac_normalised:                      0
% 3.21/1.00  sim_smt_subsumption:                    0
% 3.21/1.00  
%------------------------------------------------------------------------------
