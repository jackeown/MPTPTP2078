%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:08:39 EST 2020

% Result     : Theorem 2.66s
% Output     : CNFRefutation 2.66s
% Verified   : 
% Statistics : Number of formulae       :  174 (41639 expanded)
%              Number of clauses        :  121 (11737 expanded)
%              Number of leaves         :   14 (9897 expanded)
%              Depth                    :   43
%              Number of atoms          :  742 (339814 expanded)
%              Number of equality atoms :  417 (116758 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f13])).

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
    inference(nnf_transformation,[],[f19])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
          & r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
     => ( k1_funct_1(X2,sK5) != k1_funct_1(X3,sK5)
        & r2_hidden(sK5,k1_relset_1(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
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

fof(f29,plain,
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

fof(f32,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f28,f31,f30,f29])).

fof(f48,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f32])).

fof(f54,plain,
    ( r2_hidden(sK5,k1_relset_1(sK1,sK2,sK3))
    | ~ r1_partfun1(sK3,sK4) ),
    inference(cnf_transformation,[],[f32])).

fof(f50,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
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
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
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

fof(f53,plain,(
    ! [X5] :
      ( k1_funct_1(sK3,X5) = k1_funct_1(sK4,X5)
      | ~ r2_hidden(X5,k1_relset_1(sK1,sK2,sK3))
      | r1_partfun1(sK3,sK4) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f47,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f32])).

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

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f49,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f32])).

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

fof(f55,plain,
    ( k1_funct_1(sK3,sK5) != k1_funct_1(sK4,sK5)
    | ~ r1_partfun1(sK3,sK4) ),
    inference(cnf_transformation,[],[f32])).

fof(f52,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f32])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f60,plain,(
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

fof(f58,plain,(
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

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_635,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_21])).

cnf(c_636,plain,
    ( k1_relset_1(X0,X1,sK3) = k1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(unflattening,[status(thm)],[c_635])).

cnf(c_2183,plain,
    ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
    inference(equality_resolution,[status(thm)],[c_636])).

cnf(c_15,negated_conjecture,
    ( r2_hidden(sK5,k1_relset_1(sK1,sK2,sK3))
    | ~ r1_partfun1(sK3,sK4) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1883,plain,
    ( r2_hidden(sK5,k1_relset_1(sK1,sK2,sK3)) = iProver_top
    | r1_partfun1(sK3,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2367,plain,
    ( r2_hidden(sK5,k1_relat_1(sK3)) = iProver_top
    | r1_partfun1(sK3,sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2183,c_1883])).

cnf(c_19,negated_conjecture,
    ( v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_10,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_530,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_18])).

cnf(c_531,plain,
    ( ~ v1_funct_2(sK4,X0,X1)
    | k1_relset_1(X0,X1,sK4) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_530])).

cnf(c_1384,plain,
    ( k1_relset_1(X0,X1,sK4) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sK2 != X1
    | sK1 != X0
    | sK4 != sK4
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_531])).

cnf(c_1385,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_1384])).

cnf(c_1928,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(equality_resolution_simp,[status(thm)],[c_1385])).

cnf(c_566,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_18])).

cnf(c_567,plain,
    ( k1_relset_1(X0,X1,sK4) = k1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(unflattening,[status(thm)],[c_566])).

cnf(c_2140,plain,
    ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
    inference(equality_resolution,[status(thm)],[c_567])).

cnf(c_2701,plain,
    ( k1_relat_1(sK4) = sK1
    | sK2 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1928,c_2140])).

cnf(c_12,plain,
    ( r2_hidden(sK0(X0,X1),k1_relat_1(X0))
    | r1_partfun1(X0,X1)
    | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1886,plain,
    ( r2_hidden(sK0(X0,X1),k1_relat_1(X0)) = iProver_top
    | r1_partfun1(X0,X1) = iProver_top
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_16,negated_conjecture,
    ( ~ r2_hidden(X0,k1_relset_1(sK1,sK2,sK3))
    | r1_partfun1(sK3,sK4)
    | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1882,plain,
    ( k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0)
    | r2_hidden(X0,k1_relset_1(sK1,sK2,sK3)) != iProver_top
    | r1_partfun1(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2366,plain,
    ( k1_funct_1(sK4,X0) = k1_funct_1(sK3,X0)
    | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | r1_partfun1(sK3,sK4) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2183,c_1882])).

cnf(c_2604,plain,
    ( k1_funct_1(sK3,sK0(sK3,X0)) = k1_funct_1(sK4,sK0(sK3,X0))
    | r1_partfun1(sK3,X0) = iProver_top
    | r1_partfun1(sK3,sK4) = iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1886,c_2366])).

cnf(c_22,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_23,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1605,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2100,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_1605])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_644,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_21])).

cnf(c_645,plain,
    ( v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(unflattening,[status(thm)],[c_644])).

cnf(c_2105,plain,
    ( v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_645])).

cnf(c_2109,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2105])).

cnf(c_2638,plain,
    ( v1_relat_1(X0) != iProver_top
    | k1_funct_1(sK3,sK0(sK3,X0)) = k1_funct_1(sK4,sK0(sK3,X0))
    | r1_partfun1(sK3,X0) = iProver_top
    | r1_partfun1(sK3,sK4) = iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2604,c_23,c_2100,c_2109])).

cnf(c_2639,plain,
    ( k1_funct_1(sK3,sK0(sK3,X0)) = k1_funct_1(sK4,sK0(sK3,X0))
    | r1_partfun1(sK3,X0) = iProver_top
    | r1_partfun1(sK3,sK4) = iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2638])).

cnf(c_2704,plain,
    ( k1_funct_1(sK4,sK0(sK3,sK4)) = k1_funct_1(sK3,sK0(sK3,sK4))
    | sK2 = k1_xboole_0
    | r1_partfun1(sK3,sK4) = iProver_top
    | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2701,c_2639])).

cnf(c_20,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_25,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_575,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_18])).

cnf(c_576,plain,
    ( v1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(unflattening,[status(thm)],[c_575])).

cnf(c_2106,plain,
    ( v1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_576])).

cnf(c_2107,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2106])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v4_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_247,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_3,c_1])).

cnf(c_251,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_247,c_2])).

cnf(c_252,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_251])).

cnf(c_587,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_252,c_21])).

cnf(c_588,plain,
    ( r1_tarski(k1_relat_1(sK3),X0)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(unflattening,[status(thm)],[c_587])).

cnf(c_2103,plain,
    ( r1_tarski(k1_relat_1(sK3),sK1)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_588])).

cnf(c_2113,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | r1_tarski(k1_relat_1(sK3),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2103])).

cnf(c_3503,plain,
    ( r1_partfun1(sK3,sK4) = iProver_top
    | sK2 = k1_xboole_0
    | k1_funct_1(sK4,sK0(sK3,sK4)) = k1_funct_1(sK3,sK0(sK3,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2704,c_25,c_2100,c_2107,c_2113])).

cnf(c_3504,plain,
    ( k1_funct_1(sK4,sK0(sK3,sK4)) = k1_funct_1(sK3,sK0(sK3,sK4))
    | sK2 = k1_xboole_0
    | r1_partfun1(sK3,sK4) = iProver_top ),
    inference(renaming,[status(thm)],[c_3503])).

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

cnf(c_1885,plain,
    ( k1_funct_1(X0,X1) = k1_funct_1(X2,X1)
    | r2_hidden(X1,k1_relat_1(X2)) != iProver_top
    | r1_partfun1(X2,X0) != iProver_top
    | r1_tarski(k1_relat_1(X2),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2707,plain,
    ( k1_funct_1(X0,X1) = k1_funct_1(sK4,X1)
    | sK2 = k1_xboole_0
    | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
    | r1_partfun1(X0,sK4) != iProver_top
    | r1_tarski(k1_relat_1(X0),sK1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2701,c_1885])).

cnf(c_3051,plain,
    ( v1_relat_1(X0) != iProver_top
    | k1_funct_1(X0,X1) = k1_funct_1(sK4,X1)
    | sK2 = k1_xboole_0
    | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
    | r1_partfun1(X0,sK4) != iProver_top
    | r1_tarski(k1_relat_1(X0),sK1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2707,c_25,c_2100,c_2107])).

cnf(c_3052,plain,
    ( k1_funct_1(X0,X1) = k1_funct_1(sK4,X1)
    | sK2 = k1_xboole_0
    | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
    | r1_partfun1(X0,sK4) != iProver_top
    | r1_tarski(k1_relat_1(X0),sK1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3051])).

cnf(c_3065,plain,
    ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
    | sK2 = k1_xboole_0
    | r1_partfun1(sK3,sK4) != iProver_top
    | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2367,c_3052])).

cnf(c_3289,plain,
    ( r1_partfun1(sK3,sK4) != iProver_top
    | sK2 = k1_xboole_0
    | k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3065,c_23,c_2100,c_2109,c_2113])).

cnf(c_3290,plain,
    ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
    | sK2 = k1_xboole_0
    | r1_partfun1(sK3,sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_3289])).

cnf(c_3510,plain,
    ( k1_funct_1(sK4,sK0(sK3,sK4)) = k1_funct_1(sK3,sK0(sK3,sK4))
    | k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3504,c_3290])).

cnf(c_11,plain,
    ( r1_partfun1(X0,X1)
    | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k1_funct_1(X1,sK0(X0,X1)) != k1_funct_1(X0,sK0(X0,X1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1887,plain,
    ( k1_funct_1(X0,sK0(X1,X0)) != k1_funct_1(X1,sK0(X1,X0))
    | r1_partfun1(X1,X0) = iProver_top
    | r1_tarski(k1_relat_1(X1),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3514,plain,
    ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
    | sK2 = k1_xboole_0
    | r1_partfun1(sK3,sK4) = iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3510,c_1887])).

cnf(c_2151,plain,
    ( r1_partfun1(X0,sK4)
    | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(sK4))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK4)
    | k1_funct_1(sK4,sK0(X0,sK4)) != k1_funct_1(X0,sK0(X0,sK4)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2204,plain,
    ( r1_partfun1(sK3,sK4)
    | ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK4)
    | ~ v1_relat_1(sK3)
    | k1_funct_1(sK4,sK0(sK3,sK4)) != k1_funct_1(sK3,sK0(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_2151])).

cnf(c_2205,plain,
    ( k1_funct_1(sK4,sK0(sK3,sK4)) != k1_funct_1(sK3,sK0(sK3,sK4))
    | r1_partfun1(sK3,sK4) = iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2204])).

cnf(c_3553,plain,
    ( sK2 = k1_xboole_0
    | r1_partfun1(sK3,sK4) = iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3514,c_23,c_25,c_2100,c_2107,c_2109,c_2113,c_2205,c_2704])).

cnf(c_3560,plain,
    ( sK2 = k1_xboole_0
    | r1_partfun1(sK3,sK4) = iProver_top
    | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2701,c_3553])).

cnf(c_3563,plain,
    ( r1_partfun1(sK3,sK4) = iProver_top
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3560,c_2100,c_2113])).

cnf(c_3564,plain,
    ( sK2 = k1_xboole_0
    | r1_partfun1(sK3,sK4) = iProver_top ),
    inference(renaming,[status(thm)],[c_3563])).

cnf(c_3569,plain,
    ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3564,c_3290])).

cnf(c_14,negated_conjecture,
    ( ~ r1_partfun1(sK3,sK4)
    | k1_funct_1(sK3,sK5) != k1_funct_1(sK4,sK5) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1884,plain,
    ( k1_funct_1(sK3,sK5) != k1_funct_1(sK4,sK5)
    | r1_partfun1(sK3,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3643,plain,
    ( sK2 = k1_xboole_0
    | r1_partfun1(sK3,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3569,c_1884])).

cnf(c_3646,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3643,c_2100,c_2113,c_3560])).

cnf(c_3661,plain,
    ( k1_relset_1(sK1,k1_xboole_0,sK4) = k1_relat_1(sK4) ),
    inference(demodulation,[status(thm)],[c_3646,c_2140])).

cnf(c_17,negated_conjecture,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_3667,plain,
    ( sK1 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3646,c_17])).

cnf(c_3668,plain,
    ( sK1 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_3667])).

cnf(c_9,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_726,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_18])).

cnf(c_727,plain,
    ( ~ v1_funct_2(sK4,k1_xboole_0,X0)
    | k1_relset_1(k1_xboole_0,X0,sK4) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(unflattening,[status(thm)],[c_726])).

cnf(c_1440,plain,
    ( k1_relset_1(k1_xboole_0,X0,sK4) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sK2 != X0
    | sK1 != k1_xboole_0
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_727])).

cnf(c_1441,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sK1 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_1440])).

cnf(c_3664,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | sK1 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3646,c_1441])).

cnf(c_3681,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3664,c_3668])).

cnf(c_3682,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_3681])).

cnf(c_3692,plain,
    ( k1_relat_1(sK4) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3661,c_3668,c_3682])).

cnf(c_3811,plain,
    ( k1_funct_1(X0,X1) = k1_funct_1(sK4,X1)
    | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
    | r1_partfun1(X0,sK4) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3692,c_1885])).

cnf(c_4113,plain,
    ( v1_relat_1(X0) != iProver_top
    | k1_funct_1(X0,X1) = k1_funct_1(sK4,X1)
    | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
    | r1_partfun1(X0,sK4) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3811,c_25,c_2100,c_2107])).

cnf(c_4114,plain,
    ( k1_funct_1(X0,X1) = k1_funct_1(sK4,X1)
    | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
    | r1_partfun1(X0,sK4) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4113])).

cnf(c_4126,plain,
    ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
    | r1_partfun1(sK3,sK4) != iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2367,c_4114])).

cnf(c_6,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_690,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sK4 != X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_18])).

cnf(c_691,plain,
    ( ~ v1_funct_2(sK4,X0,k1_xboole_0)
    | k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | k1_xboole_0 = X0
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_690])).

cnf(c_1409,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sK2 != k1_xboole_0
    | sK1 != X0
    | sK4 != sK4
    | sK4 = k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_691])).

cnf(c_1410,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sK2 != k1_xboole_0
    | sK4 = k1_xboole_0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_1409])).

cnf(c_1628,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1605])).

cnf(c_1606,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2127,plain,
    ( sK2 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_1606])).

cnf(c_2128,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2127])).

cnf(c_2215,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1410,c_17,c_1628,c_2128])).

cnf(c_1608,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2225,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k1_relat_1(sK3),sK1)
    | X0 != k1_relat_1(sK3)
    | X1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1608])).

cnf(c_2382,plain,
    ( r1_tarski(X0,k1_xboole_0)
    | ~ r1_tarski(k1_relat_1(sK3),sK1)
    | X0 != k1_relat_1(sK3)
    | k1_xboole_0 != sK1 ),
    inference(instantiation,[status(thm)],[c_2225])).

cnf(c_2897,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),sK1)
    | r1_tarski(k1_relat_1(sK3),k1_xboole_0)
    | k1_relat_1(sK3) != k1_relat_1(sK3)
    | k1_xboole_0 != sK1 ),
    inference(instantiation,[status(thm)],[c_2382])).

cnf(c_2899,plain,
    ( k1_relat_1(sK3) != k1_relat_1(sK3)
    | k1_xboole_0 != sK1
    | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2897])).

cnf(c_2898,plain,
    ( k1_relat_1(sK3) = k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1605])).

cnf(c_2990,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k1_relat_1(sK3),X2)
    | X1 != X2
    | X0 != k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1608])).

cnf(c_3758,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),X0)
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4))
    | k1_relat_1(sK4) != X0
    | k1_relat_1(sK3) != k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2990])).

cnf(c_3759,plain,
    ( k1_relat_1(sK4) != X0
    | k1_relat_1(sK3) != k1_relat_1(sK3)
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3758])).

cnf(c_3761,plain,
    ( k1_relat_1(sK4) != k1_xboole_0
    | k1_relat_1(sK3) != k1_relat_1(sK3)
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4)) = iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3759])).

cnf(c_3808,plain,
    ( k1_funct_1(sK4,sK0(sK3,sK4)) = k1_funct_1(sK3,sK0(sK3,sK4))
    | r1_partfun1(sK3,sK4) = iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3692,c_2639])).

cnf(c_4264,plain,
    ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4126,c_23,c_25,c_2100,c_2107,c_2109,c_2113,c_2205,c_2215,c_2899,c_2898,c_3560,c_3643,c_3692,c_3761,c_3808])).

cnf(c_4267,plain,
    ( k1_funct_1(sK3,sK5) != k1_funct_1(sK3,sK5)
    | r1_partfun1(sK3,sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4264,c_1884])).

cnf(c_4269,plain,
    ( r1_partfun1(sK3,sK4) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4267])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4269,c_3808,c_3761,c_3692,c_3646,c_2898,c_2899,c_2215,c_2205,c_2113,c_2109,c_2107,c_2100,c_25,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:52:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.66/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.66/0.99  
% 2.66/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.66/0.99  
% 2.66/0.99  ------  iProver source info
% 2.66/0.99  
% 2.66/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.66/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.66/0.99  git: non_committed_changes: false
% 2.66/0.99  git: last_make_outside_of_git: false
% 2.66/0.99  
% 2.66/0.99  ------ 
% 2.66/0.99  
% 2.66/0.99  ------ Input Options
% 2.66/0.99  
% 2.66/0.99  --out_options                           all
% 2.66/0.99  --tptp_safe_out                         true
% 2.66/0.99  --problem_path                          ""
% 2.66/0.99  --include_path                          ""
% 2.66/0.99  --clausifier                            res/vclausify_rel
% 2.66/0.99  --clausifier_options                    --mode clausify
% 2.66/0.99  --stdin                                 false
% 2.66/0.99  --stats_out                             all
% 2.66/0.99  
% 2.66/0.99  ------ General Options
% 2.66/0.99  
% 2.66/0.99  --fof                                   false
% 2.66/0.99  --time_out_real                         305.
% 2.66/0.99  --time_out_virtual                      -1.
% 2.66/0.99  --symbol_type_check                     false
% 2.66/0.99  --clausify_out                          false
% 2.66/0.99  --sig_cnt_out                           false
% 2.66/1.00  --trig_cnt_out                          false
% 2.66/1.00  --trig_cnt_out_tolerance                1.
% 2.66/1.00  --trig_cnt_out_sk_spl                   false
% 2.66/1.00  --abstr_cl_out                          false
% 2.66/1.00  
% 2.66/1.00  ------ Global Options
% 2.66/1.00  
% 2.66/1.00  --schedule                              default
% 2.66/1.00  --add_important_lit                     false
% 2.66/1.00  --prop_solver_per_cl                    1000
% 2.66/1.00  --min_unsat_core                        false
% 2.66/1.00  --soft_assumptions                      false
% 2.66/1.00  --soft_lemma_size                       3
% 2.66/1.00  --prop_impl_unit_size                   0
% 2.66/1.00  --prop_impl_unit                        []
% 2.66/1.00  --share_sel_clauses                     true
% 2.66/1.00  --reset_solvers                         false
% 2.66/1.00  --bc_imp_inh                            [conj_cone]
% 2.66/1.00  --conj_cone_tolerance                   3.
% 2.66/1.00  --extra_neg_conj                        none
% 2.66/1.00  --large_theory_mode                     true
% 2.66/1.00  --prolific_symb_bound                   200
% 2.66/1.00  --lt_threshold                          2000
% 2.66/1.00  --clause_weak_htbl                      true
% 2.66/1.00  --gc_record_bc_elim                     false
% 2.66/1.00  
% 2.66/1.00  ------ Preprocessing Options
% 2.66/1.00  
% 2.66/1.00  --preprocessing_flag                    true
% 2.66/1.00  --time_out_prep_mult                    0.1
% 2.66/1.00  --splitting_mode                        input
% 2.66/1.00  --splitting_grd                         true
% 2.66/1.00  --splitting_cvd                         false
% 2.66/1.00  --splitting_cvd_svl                     false
% 2.66/1.00  --splitting_nvd                         32
% 2.66/1.00  --sub_typing                            true
% 2.66/1.00  --prep_gs_sim                           true
% 2.66/1.00  --prep_unflatten                        true
% 2.66/1.00  --prep_res_sim                          true
% 2.66/1.00  --prep_upred                            true
% 2.66/1.00  --prep_sem_filter                       exhaustive
% 2.66/1.00  --prep_sem_filter_out                   false
% 2.66/1.00  --pred_elim                             true
% 2.66/1.00  --res_sim_input                         true
% 2.66/1.00  --eq_ax_congr_red                       true
% 2.66/1.00  --pure_diseq_elim                       true
% 2.66/1.00  --brand_transform                       false
% 2.66/1.00  --non_eq_to_eq                          false
% 2.66/1.00  --prep_def_merge                        true
% 2.66/1.00  --prep_def_merge_prop_impl              false
% 2.66/1.00  --prep_def_merge_mbd                    true
% 2.66/1.00  --prep_def_merge_tr_red                 false
% 2.66/1.00  --prep_def_merge_tr_cl                  false
% 2.66/1.00  --smt_preprocessing                     true
% 2.66/1.00  --smt_ac_axioms                         fast
% 2.66/1.00  --preprocessed_out                      false
% 2.66/1.00  --preprocessed_stats                    false
% 2.66/1.00  
% 2.66/1.00  ------ Abstraction refinement Options
% 2.66/1.00  
% 2.66/1.00  --abstr_ref                             []
% 2.66/1.00  --abstr_ref_prep                        false
% 2.66/1.00  --abstr_ref_until_sat                   false
% 2.66/1.00  --abstr_ref_sig_restrict                funpre
% 2.66/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.66/1.00  --abstr_ref_under                       []
% 2.66/1.00  
% 2.66/1.00  ------ SAT Options
% 2.66/1.00  
% 2.66/1.00  --sat_mode                              false
% 2.66/1.00  --sat_fm_restart_options                ""
% 2.66/1.00  --sat_gr_def                            false
% 2.66/1.00  --sat_epr_types                         true
% 2.66/1.00  --sat_non_cyclic_types                  false
% 2.66/1.00  --sat_finite_models                     false
% 2.66/1.00  --sat_fm_lemmas                         false
% 2.66/1.00  --sat_fm_prep                           false
% 2.66/1.00  --sat_fm_uc_incr                        true
% 2.66/1.00  --sat_out_model                         small
% 2.66/1.00  --sat_out_clauses                       false
% 2.66/1.00  
% 2.66/1.00  ------ QBF Options
% 2.66/1.00  
% 2.66/1.00  --qbf_mode                              false
% 2.66/1.00  --qbf_elim_univ                         false
% 2.66/1.00  --qbf_dom_inst                          none
% 2.66/1.00  --qbf_dom_pre_inst                      false
% 2.66/1.00  --qbf_sk_in                             false
% 2.66/1.00  --qbf_pred_elim                         true
% 2.66/1.00  --qbf_split                             512
% 2.66/1.00  
% 2.66/1.00  ------ BMC1 Options
% 2.66/1.00  
% 2.66/1.00  --bmc1_incremental                      false
% 2.66/1.00  --bmc1_axioms                           reachable_all
% 2.66/1.00  --bmc1_min_bound                        0
% 2.66/1.00  --bmc1_max_bound                        -1
% 2.66/1.00  --bmc1_max_bound_default                -1
% 2.66/1.00  --bmc1_symbol_reachability              true
% 2.66/1.00  --bmc1_property_lemmas                  false
% 2.66/1.00  --bmc1_k_induction                      false
% 2.66/1.00  --bmc1_non_equiv_states                 false
% 2.66/1.00  --bmc1_deadlock                         false
% 2.66/1.00  --bmc1_ucm                              false
% 2.66/1.00  --bmc1_add_unsat_core                   none
% 2.66/1.00  --bmc1_unsat_core_children              false
% 2.66/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.66/1.00  --bmc1_out_stat                         full
% 2.66/1.00  --bmc1_ground_init                      false
% 2.66/1.00  --bmc1_pre_inst_next_state              false
% 2.66/1.00  --bmc1_pre_inst_state                   false
% 2.66/1.00  --bmc1_pre_inst_reach_state             false
% 2.66/1.00  --bmc1_out_unsat_core                   false
% 2.66/1.00  --bmc1_aig_witness_out                  false
% 2.66/1.00  --bmc1_verbose                          false
% 2.66/1.00  --bmc1_dump_clauses_tptp                false
% 2.66/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.66/1.00  --bmc1_dump_file                        -
% 2.66/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.66/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.66/1.00  --bmc1_ucm_extend_mode                  1
% 2.66/1.00  --bmc1_ucm_init_mode                    2
% 2.66/1.00  --bmc1_ucm_cone_mode                    none
% 2.66/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.66/1.00  --bmc1_ucm_relax_model                  4
% 2.66/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.66/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.66/1.00  --bmc1_ucm_layered_model                none
% 2.66/1.00  --bmc1_ucm_max_lemma_size               10
% 2.66/1.00  
% 2.66/1.00  ------ AIG Options
% 2.66/1.00  
% 2.66/1.00  --aig_mode                              false
% 2.66/1.00  
% 2.66/1.00  ------ Instantiation Options
% 2.66/1.00  
% 2.66/1.00  --instantiation_flag                    true
% 2.66/1.00  --inst_sos_flag                         false
% 2.66/1.00  --inst_sos_phase                        true
% 2.66/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.66/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.66/1.00  --inst_lit_sel_side                     num_symb
% 2.66/1.00  --inst_solver_per_active                1400
% 2.66/1.00  --inst_solver_calls_frac                1.
% 2.66/1.00  --inst_passive_queue_type               priority_queues
% 2.66/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.66/1.00  --inst_passive_queues_freq              [25;2]
% 2.66/1.00  --inst_dismatching                      true
% 2.66/1.00  --inst_eager_unprocessed_to_passive     true
% 2.66/1.00  --inst_prop_sim_given                   true
% 2.66/1.00  --inst_prop_sim_new                     false
% 2.66/1.00  --inst_subs_new                         false
% 2.66/1.00  --inst_eq_res_simp                      false
% 2.66/1.00  --inst_subs_given                       false
% 2.66/1.00  --inst_orphan_elimination               true
% 2.66/1.00  --inst_learning_loop_flag               true
% 2.66/1.00  --inst_learning_start                   3000
% 2.66/1.00  --inst_learning_factor                  2
% 2.66/1.00  --inst_start_prop_sim_after_learn       3
% 2.66/1.00  --inst_sel_renew                        solver
% 2.66/1.00  --inst_lit_activity_flag                true
% 2.66/1.00  --inst_restr_to_given                   false
% 2.66/1.00  --inst_activity_threshold               500
% 2.66/1.00  --inst_out_proof                        true
% 2.66/1.00  
% 2.66/1.00  ------ Resolution Options
% 2.66/1.00  
% 2.66/1.00  --resolution_flag                       true
% 2.66/1.00  --res_lit_sel                           adaptive
% 2.66/1.00  --res_lit_sel_side                      none
% 2.66/1.00  --res_ordering                          kbo
% 2.66/1.00  --res_to_prop_solver                    active
% 2.66/1.00  --res_prop_simpl_new                    false
% 2.66/1.00  --res_prop_simpl_given                  true
% 2.66/1.00  --res_passive_queue_type                priority_queues
% 2.66/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.66/1.00  --res_passive_queues_freq               [15;5]
% 2.66/1.00  --res_forward_subs                      full
% 2.66/1.00  --res_backward_subs                     full
% 2.66/1.00  --res_forward_subs_resolution           true
% 2.66/1.00  --res_backward_subs_resolution          true
% 2.66/1.00  --res_orphan_elimination                true
% 2.66/1.00  --res_time_limit                        2.
% 2.66/1.00  --res_out_proof                         true
% 2.66/1.00  
% 2.66/1.00  ------ Superposition Options
% 2.66/1.00  
% 2.66/1.00  --superposition_flag                    true
% 2.66/1.00  --sup_passive_queue_type                priority_queues
% 2.66/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.66/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.66/1.00  --demod_completeness_check              fast
% 2.66/1.00  --demod_use_ground                      true
% 2.66/1.00  --sup_to_prop_solver                    passive
% 2.66/1.00  --sup_prop_simpl_new                    true
% 2.66/1.00  --sup_prop_simpl_given                  true
% 2.66/1.00  --sup_fun_splitting                     false
% 2.66/1.00  --sup_smt_interval                      50000
% 2.66/1.00  
% 2.66/1.00  ------ Superposition Simplification Setup
% 2.66/1.00  
% 2.66/1.00  --sup_indices_passive                   []
% 2.66/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.66/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.66/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.66/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.66/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.66/1.00  --sup_full_bw                           [BwDemod]
% 2.66/1.00  --sup_immed_triv                        [TrivRules]
% 2.66/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.66/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.66/1.00  --sup_immed_bw_main                     []
% 2.66/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.66/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.66/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.66/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.66/1.00  
% 2.66/1.00  ------ Combination Options
% 2.66/1.00  
% 2.66/1.00  --comb_res_mult                         3
% 2.66/1.00  --comb_sup_mult                         2
% 2.66/1.00  --comb_inst_mult                        10
% 2.66/1.00  
% 2.66/1.00  ------ Debug Options
% 2.66/1.00  
% 2.66/1.00  --dbg_backtrace                         false
% 2.66/1.00  --dbg_dump_prop_clauses                 false
% 2.66/1.00  --dbg_dump_prop_clauses_file            -
% 2.66/1.00  --dbg_out_stat                          false
% 2.66/1.00  ------ Parsing...
% 2.66/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.66/1.00  
% 2.66/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 2.66/1.00  
% 2.66/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.66/1.00  
% 2.66/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.66/1.00  ------ Proving...
% 2.66/1.00  ------ Problem Properties 
% 2.66/1.00  
% 2.66/1.00  
% 2.66/1.00  clauses                                 25
% 2.66/1.00  conjectures                             6
% 2.66/1.00  EPR                                     3
% 2.66/1.00  Horn                                    17
% 2.66/1.00  unary                                   2
% 2.66/1.00  binary                                  9
% 2.66/1.00  lits                                    86
% 2.66/1.00  lits eq                                 55
% 2.66/1.00  fd_pure                                 0
% 2.66/1.00  fd_pseudo                               0
% 2.66/1.00  fd_cond                                 0
% 2.66/1.00  fd_pseudo_cond                          0
% 2.66/1.00  AC symbols                              0
% 2.66/1.00  
% 2.66/1.00  ------ Schedule dynamic 5 is on 
% 2.66/1.00  
% 2.66/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.66/1.00  
% 2.66/1.00  
% 2.66/1.00  ------ 
% 2.66/1.00  Current options:
% 2.66/1.00  ------ 
% 2.66/1.00  
% 2.66/1.00  ------ Input Options
% 2.66/1.00  
% 2.66/1.00  --out_options                           all
% 2.66/1.00  --tptp_safe_out                         true
% 2.66/1.00  --problem_path                          ""
% 2.66/1.00  --include_path                          ""
% 2.66/1.00  --clausifier                            res/vclausify_rel
% 2.66/1.00  --clausifier_options                    --mode clausify
% 2.66/1.00  --stdin                                 false
% 2.66/1.00  --stats_out                             all
% 2.66/1.00  
% 2.66/1.00  ------ General Options
% 2.66/1.00  
% 2.66/1.00  --fof                                   false
% 2.66/1.00  --time_out_real                         305.
% 2.66/1.00  --time_out_virtual                      -1.
% 2.66/1.00  --symbol_type_check                     false
% 2.66/1.00  --clausify_out                          false
% 2.66/1.00  --sig_cnt_out                           false
% 2.66/1.00  --trig_cnt_out                          false
% 2.66/1.00  --trig_cnt_out_tolerance                1.
% 2.66/1.00  --trig_cnt_out_sk_spl                   false
% 2.66/1.00  --abstr_cl_out                          false
% 2.66/1.00  
% 2.66/1.00  ------ Global Options
% 2.66/1.00  
% 2.66/1.00  --schedule                              default
% 2.66/1.00  --add_important_lit                     false
% 2.66/1.00  --prop_solver_per_cl                    1000
% 2.66/1.00  --min_unsat_core                        false
% 2.66/1.00  --soft_assumptions                      false
% 2.66/1.00  --soft_lemma_size                       3
% 2.66/1.00  --prop_impl_unit_size                   0
% 2.66/1.00  --prop_impl_unit                        []
% 2.66/1.00  --share_sel_clauses                     true
% 2.66/1.00  --reset_solvers                         false
% 2.66/1.00  --bc_imp_inh                            [conj_cone]
% 2.66/1.00  --conj_cone_tolerance                   3.
% 2.66/1.00  --extra_neg_conj                        none
% 2.66/1.00  --large_theory_mode                     true
% 2.66/1.00  --prolific_symb_bound                   200
% 2.66/1.00  --lt_threshold                          2000
% 2.66/1.00  --clause_weak_htbl                      true
% 2.66/1.00  --gc_record_bc_elim                     false
% 2.66/1.00  
% 2.66/1.00  ------ Preprocessing Options
% 2.66/1.00  
% 2.66/1.00  --preprocessing_flag                    true
% 2.66/1.00  --time_out_prep_mult                    0.1
% 2.66/1.00  --splitting_mode                        input
% 2.66/1.00  --splitting_grd                         true
% 2.66/1.00  --splitting_cvd                         false
% 2.66/1.00  --splitting_cvd_svl                     false
% 2.66/1.00  --splitting_nvd                         32
% 2.66/1.00  --sub_typing                            true
% 2.66/1.00  --prep_gs_sim                           true
% 2.66/1.00  --prep_unflatten                        true
% 2.66/1.00  --prep_res_sim                          true
% 2.66/1.00  --prep_upred                            true
% 2.66/1.00  --prep_sem_filter                       exhaustive
% 2.66/1.00  --prep_sem_filter_out                   false
% 2.66/1.00  --pred_elim                             true
% 2.66/1.00  --res_sim_input                         true
% 2.66/1.00  --eq_ax_congr_red                       true
% 2.66/1.00  --pure_diseq_elim                       true
% 2.66/1.00  --brand_transform                       false
% 2.66/1.00  --non_eq_to_eq                          false
% 2.66/1.00  --prep_def_merge                        true
% 2.66/1.00  --prep_def_merge_prop_impl              false
% 2.66/1.00  --prep_def_merge_mbd                    true
% 2.66/1.00  --prep_def_merge_tr_red                 false
% 2.66/1.00  --prep_def_merge_tr_cl                  false
% 2.66/1.00  --smt_preprocessing                     true
% 2.66/1.00  --smt_ac_axioms                         fast
% 2.66/1.00  --preprocessed_out                      false
% 2.66/1.00  --preprocessed_stats                    false
% 2.66/1.00  
% 2.66/1.00  ------ Abstraction refinement Options
% 2.66/1.00  
% 2.66/1.00  --abstr_ref                             []
% 2.66/1.00  --abstr_ref_prep                        false
% 2.66/1.00  --abstr_ref_until_sat                   false
% 2.66/1.00  --abstr_ref_sig_restrict                funpre
% 2.66/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.66/1.00  --abstr_ref_under                       []
% 2.66/1.00  
% 2.66/1.00  ------ SAT Options
% 2.66/1.00  
% 2.66/1.00  --sat_mode                              false
% 2.66/1.00  --sat_fm_restart_options                ""
% 2.66/1.00  --sat_gr_def                            false
% 2.66/1.00  --sat_epr_types                         true
% 2.66/1.00  --sat_non_cyclic_types                  false
% 2.66/1.00  --sat_finite_models                     false
% 2.66/1.00  --sat_fm_lemmas                         false
% 2.66/1.00  --sat_fm_prep                           false
% 2.66/1.00  --sat_fm_uc_incr                        true
% 2.66/1.00  --sat_out_model                         small
% 2.66/1.00  --sat_out_clauses                       false
% 2.66/1.00  
% 2.66/1.00  ------ QBF Options
% 2.66/1.00  
% 2.66/1.00  --qbf_mode                              false
% 2.66/1.00  --qbf_elim_univ                         false
% 2.66/1.00  --qbf_dom_inst                          none
% 2.66/1.00  --qbf_dom_pre_inst                      false
% 2.66/1.00  --qbf_sk_in                             false
% 2.66/1.00  --qbf_pred_elim                         true
% 2.66/1.00  --qbf_split                             512
% 2.66/1.00  
% 2.66/1.00  ------ BMC1 Options
% 2.66/1.00  
% 2.66/1.00  --bmc1_incremental                      false
% 2.66/1.00  --bmc1_axioms                           reachable_all
% 2.66/1.00  --bmc1_min_bound                        0
% 2.66/1.00  --bmc1_max_bound                        -1
% 2.66/1.00  --bmc1_max_bound_default                -1
% 2.66/1.00  --bmc1_symbol_reachability              true
% 2.66/1.00  --bmc1_property_lemmas                  false
% 2.66/1.00  --bmc1_k_induction                      false
% 2.66/1.00  --bmc1_non_equiv_states                 false
% 2.66/1.00  --bmc1_deadlock                         false
% 2.66/1.00  --bmc1_ucm                              false
% 2.66/1.00  --bmc1_add_unsat_core                   none
% 2.66/1.00  --bmc1_unsat_core_children              false
% 2.66/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.66/1.00  --bmc1_out_stat                         full
% 2.66/1.00  --bmc1_ground_init                      false
% 2.66/1.00  --bmc1_pre_inst_next_state              false
% 2.66/1.00  --bmc1_pre_inst_state                   false
% 2.66/1.00  --bmc1_pre_inst_reach_state             false
% 2.66/1.00  --bmc1_out_unsat_core                   false
% 2.66/1.00  --bmc1_aig_witness_out                  false
% 2.66/1.00  --bmc1_verbose                          false
% 2.66/1.00  --bmc1_dump_clauses_tptp                false
% 2.66/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.66/1.00  --bmc1_dump_file                        -
% 2.66/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.66/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.66/1.00  --bmc1_ucm_extend_mode                  1
% 2.66/1.00  --bmc1_ucm_init_mode                    2
% 2.66/1.00  --bmc1_ucm_cone_mode                    none
% 2.66/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.66/1.00  --bmc1_ucm_relax_model                  4
% 2.66/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.66/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.66/1.00  --bmc1_ucm_layered_model                none
% 2.66/1.00  --bmc1_ucm_max_lemma_size               10
% 2.66/1.00  
% 2.66/1.00  ------ AIG Options
% 2.66/1.00  
% 2.66/1.00  --aig_mode                              false
% 2.66/1.00  
% 2.66/1.00  ------ Instantiation Options
% 2.66/1.00  
% 2.66/1.00  --instantiation_flag                    true
% 2.66/1.00  --inst_sos_flag                         false
% 2.66/1.00  --inst_sos_phase                        true
% 2.66/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.66/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.66/1.00  --inst_lit_sel_side                     none
% 2.66/1.00  --inst_solver_per_active                1400
% 2.66/1.00  --inst_solver_calls_frac                1.
% 2.66/1.00  --inst_passive_queue_type               priority_queues
% 2.66/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.66/1.00  --inst_passive_queues_freq              [25;2]
% 2.66/1.00  --inst_dismatching                      true
% 2.66/1.00  --inst_eager_unprocessed_to_passive     true
% 2.66/1.00  --inst_prop_sim_given                   true
% 2.66/1.00  --inst_prop_sim_new                     false
% 2.66/1.00  --inst_subs_new                         false
% 2.66/1.00  --inst_eq_res_simp                      false
% 2.66/1.00  --inst_subs_given                       false
% 2.66/1.00  --inst_orphan_elimination               true
% 2.66/1.00  --inst_learning_loop_flag               true
% 2.66/1.00  --inst_learning_start                   3000
% 2.66/1.00  --inst_learning_factor                  2
% 2.66/1.00  --inst_start_prop_sim_after_learn       3
% 2.66/1.00  --inst_sel_renew                        solver
% 2.66/1.00  --inst_lit_activity_flag                true
% 2.66/1.00  --inst_restr_to_given                   false
% 2.66/1.00  --inst_activity_threshold               500
% 2.66/1.00  --inst_out_proof                        true
% 2.66/1.00  
% 2.66/1.00  ------ Resolution Options
% 2.66/1.00  
% 2.66/1.00  --resolution_flag                       false
% 2.66/1.00  --res_lit_sel                           adaptive
% 2.66/1.00  --res_lit_sel_side                      none
% 2.66/1.00  --res_ordering                          kbo
% 2.66/1.00  --res_to_prop_solver                    active
% 2.66/1.00  --res_prop_simpl_new                    false
% 2.66/1.00  --res_prop_simpl_given                  true
% 2.66/1.00  --res_passive_queue_type                priority_queues
% 2.66/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.66/1.00  --res_passive_queues_freq               [15;5]
% 2.66/1.00  --res_forward_subs                      full
% 2.66/1.00  --res_backward_subs                     full
% 2.66/1.00  --res_forward_subs_resolution           true
% 2.66/1.00  --res_backward_subs_resolution          true
% 2.66/1.00  --res_orphan_elimination                true
% 2.66/1.00  --res_time_limit                        2.
% 2.66/1.00  --res_out_proof                         true
% 2.66/1.00  
% 2.66/1.00  ------ Superposition Options
% 2.66/1.00  
% 2.66/1.00  --superposition_flag                    true
% 2.66/1.00  --sup_passive_queue_type                priority_queues
% 2.66/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.66/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.66/1.00  --demod_completeness_check              fast
% 2.66/1.00  --demod_use_ground                      true
% 2.66/1.00  --sup_to_prop_solver                    passive
% 2.66/1.00  --sup_prop_simpl_new                    true
% 2.66/1.00  --sup_prop_simpl_given                  true
% 2.66/1.00  --sup_fun_splitting                     false
% 2.66/1.00  --sup_smt_interval                      50000
% 2.66/1.00  
% 2.66/1.00  ------ Superposition Simplification Setup
% 2.66/1.00  
% 2.66/1.00  --sup_indices_passive                   []
% 2.66/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.66/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.66/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.66/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.66/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.66/1.00  --sup_full_bw                           [BwDemod]
% 2.66/1.00  --sup_immed_triv                        [TrivRules]
% 2.66/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.66/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.66/1.00  --sup_immed_bw_main                     []
% 2.66/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.66/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.66/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.66/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.66/1.00  
% 2.66/1.00  ------ Combination Options
% 2.66/1.00  
% 2.66/1.00  --comb_res_mult                         3
% 2.66/1.00  --comb_sup_mult                         2
% 2.66/1.00  --comb_inst_mult                        10
% 2.66/1.00  
% 2.66/1.00  ------ Debug Options
% 2.66/1.00  
% 2.66/1.00  --dbg_backtrace                         false
% 2.66/1.00  --dbg_dump_prop_clauses                 false
% 2.66/1.00  --dbg_dump_prop_clauses_file            -
% 2.66/1.00  --dbg_out_stat                          false
% 2.66/1.00  
% 2.66/1.00  
% 2.66/1.00  
% 2.66/1.00  
% 2.66/1.00  ------ Proving...
% 2.66/1.00  
% 2.66/1.00  
% 2.66/1.00  % SZS status Theorem for theBenchmark.p
% 2.66/1.00  
% 2.66/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.66/1.00  
% 2.66/1.00  fof(f4,axiom,(
% 2.66/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.66/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.66/1.00  
% 2.66/1.00  fof(f13,plain,(
% 2.66/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.66/1.00    inference(ennf_transformation,[],[f4])).
% 2.66/1.00  
% 2.66/1.00  fof(f37,plain,(
% 2.66/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.66/1.00    inference(cnf_transformation,[],[f13])).
% 2.66/1.00  
% 2.66/1.00  fof(f7,conjecture,(
% 2.66/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (r1_partfun1(X2,X3) <=> ! [X4] : (r2_hidden(X4,k1_relset_1(X0,X1,X2)) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4))))))),
% 2.66/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.66/1.00  
% 2.66/1.00  fof(f8,negated_conjecture,(
% 2.66/1.00    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (r1_partfun1(X2,X3) <=> ! [X4] : (r2_hidden(X4,k1_relset_1(X0,X1,X2)) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4))))))),
% 2.66/1.00    inference(negated_conjecture,[],[f7])).
% 2.66/1.00  
% 2.66/1.00  fof(f18,plain,(
% 2.66/1.00    ? [X0,X1,X2] : (? [X3] : (((r1_partfun1(X2,X3) <~> ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,k1_relset_1(X0,X1,X2)))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 2.66/1.00    inference(ennf_transformation,[],[f8])).
% 2.66/1.00  
% 2.66/1.00  fof(f19,plain,(
% 2.66/1.00    ? [X0,X1,X2] : (? [X3] : ((r1_partfun1(X2,X3) <~> ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,k1_relset_1(X0,X1,X2)))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 2.66/1.00    inference(flattening,[],[f18])).
% 2.66/1.00  
% 2.66/1.00  fof(f26,plain,(
% 2.66/1.00    ? [X0,X1,X2] : (? [X3] : (((? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & r2_hidden(X4,k1_relset_1(X0,X1,X2))) | ~r1_partfun1(X2,X3)) & (! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,k1_relset_1(X0,X1,X2))) | r1_partfun1(X2,X3))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 2.66/1.00    inference(nnf_transformation,[],[f19])).
% 2.66/1.00  
% 2.66/1.00  fof(f27,plain,(
% 2.66/1.00    ? [X0,X1,X2] : (? [X3] : ((? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & r2_hidden(X4,k1_relset_1(X0,X1,X2))) | ~r1_partfun1(X2,X3)) & (! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,k1_relset_1(X0,X1,X2))) | r1_partfun1(X2,X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 2.66/1.00    inference(flattening,[],[f26])).
% 2.66/1.00  
% 2.66/1.00  fof(f28,plain,(
% 2.66/1.00    ? [X0,X1,X2] : (? [X3] : ((? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & r2_hidden(X4,k1_relset_1(X0,X1,X2))) | ~r1_partfun1(X2,X3)) & (! [X5] : (k1_funct_1(X2,X5) = k1_funct_1(X3,X5) | ~r2_hidden(X5,k1_relset_1(X0,X1,X2))) | r1_partfun1(X2,X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 2.66/1.00    inference(rectify,[],[f27])).
% 2.66/1.00  
% 2.66/1.00  fof(f31,plain,(
% 2.66/1.00    ( ! [X2,X0,X3,X1] : (? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & r2_hidden(X4,k1_relset_1(X0,X1,X2))) => (k1_funct_1(X2,sK5) != k1_funct_1(X3,sK5) & r2_hidden(sK5,k1_relset_1(X0,X1,X2)))) )),
% 2.66/1.00    introduced(choice_axiom,[])).
% 2.66/1.00  
% 2.66/1.00  fof(f30,plain,(
% 2.66/1.00    ( ! [X2,X0,X1] : (? [X3] : ((? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & r2_hidden(X4,k1_relset_1(X0,X1,X2))) | ~r1_partfun1(X2,X3)) & (! [X5] : (k1_funct_1(X2,X5) = k1_funct_1(X3,X5) | ~r2_hidden(X5,k1_relset_1(X0,X1,X2))) | r1_partfun1(X2,X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((? [X4] : (k1_funct_1(sK4,X4) != k1_funct_1(X2,X4) & r2_hidden(X4,k1_relset_1(X0,X1,X2))) | ~r1_partfun1(X2,sK4)) & (! [X5] : (k1_funct_1(sK4,X5) = k1_funct_1(X2,X5) | ~r2_hidden(X5,k1_relset_1(X0,X1,X2))) | r1_partfun1(X2,sK4)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(sK4,X0,X1) & v1_funct_1(sK4))) )),
% 2.66/1.00    introduced(choice_axiom,[])).
% 2.66/1.00  
% 2.66/1.00  fof(f29,plain,(
% 2.66/1.00    ? [X0,X1,X2] : (? [X3] : ((? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & r2_hidden(X4,k1_relset_1(X0,X1,X2))) | ~r1_partfun1(X2,X3)) & (! [X5] : (k1_funct_1(X2,X5) = k1_funct_1(X3,X5) | ~r2_hidden(X5,k1_relset_1(X0,X1,X2))) | r1_partfun1(X2,X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (? [X3] : ((? [X4] : (k1_funct_1(sK3,X4) != k1_funct_1(X3,X4) & r2_hidden(X4,k1_relset_1(sK1,sK2,sK3))) | ~r1_partfun1(sK3,X3)) & (! [X5] : (k1_funct_1(sK3,X5) = k1_funct_1(X3,X5) | ~r2_hidden(X5,k1_relset_1(sK1,sK2,sK3))) | r1_partfun1(sK3,X3)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X3,sK1,sK2) & v1_funct_1(X3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_1(sK3))),
% 2.66/1.00    introduced(choice_axiom,[])).
% 2.66/1.00  
% 2.66/1.00  fof(f32,plain,(
% 2.66/1.00    (((k1_funct_1(sK3,sK5) != k1_funct_1(sK4,sK5) & r2_hidden(sK5,k1_relset_1(sK1,sK2,sK3))) | ~r1_partfun1(sK3,sK4)) & (! [X5] : (k1_funct_1(sK3,X5) = k1_funct_1(sK4,X5) | ~r2_hidden(X5,k1_relset_1(sK1,sK2,sK3))) | r1_partfun1(sK3,sK4)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK2) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_1(sK3)),
% 2.66/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f28,f31,f30,f29])).
% 2.66/1.00  
% 2.66/1.00  fof(f48,plain,(
% 2.66/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 2.66/1.00    inference(cnf_transformation,[],[f32])).
% 2.66/1.00  
% 2.66/1.00  fof(f54,plain,(
% 2.66/1.00    r2_hidden(sK5,k1_relset_1(sK1,sK2,sK3)) | ~r1_partfun1(sK3,sK4)),
% 2.66/1.00    inference(cnf_transformation,[],[f32])).
% 2.66/1.00  
% 2.66/1.00  fof(f50,plain,(
% 2.66/1.00    v1_funct_2(sK4,sK1,sK2)),
% 2.66/1.00    inference(cnf_transformation,[],[f32])).
% 2.66/1.00  
% 2.66/1.00  fof(f5,axiom,(
% 2.66/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.66/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.66/1.00  
% 2.66/1.00  fof(f14,plain,(
% 2.66/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.66/1.00    inference(ennf_transformation,[],[f5])).
% 2.66/1.00  
% 2.66/1.00  fof(f15,plain,(
% 2.66/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.66/1.00    inference(flattening,[],[f14])).
% 2.66/1.00  
% 2.66/1.00  fof(f21,plain,(
% 2.66/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.66/1.00    inference(nnf_transformation,[],[f15])).
% 2.66/1.00  
% 2.66/1.00  fof(f38,plain,(
% 2.66/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.66/1.00    inference(cnf_transformation,[],[f21])).
% 2.66/1.00  
% 2.66/1.00  fof(f51,plain,(
% 2.66/1.00    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 2.66/1.00    inference(cnf_transformation,[],[f32])).
% 2.66/1.00  
% 2.66/1.00  fof(f6,axiom,(
% 2.66/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) => (r1_partfun1(X0,X1) <=> ! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2))))))),
% 2.66/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.66/1.00  
% 2.66/1.00  fof(f16,plain,(
% 2.66/1.00    ! [X0] : (! [X1] : (((r1_partfun1(X0,X1) <=> ! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0)))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.66/1.00    inference(ennf_transformation,[],[f6])).
% 2.66/1.00  
% 2.66/1.00  fof(f17,plain,(
% 2.66/1.00    ! [X0] : (! [X1] : ((r1_partfun1(X0,X1) <=> ! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0)))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.66/1.00    inference(flattening,[],[f16])).
% 2.66/1.00  
% 2.66/1.00  fof(f22,plain,(
% 2.66/1.00    ! [X0] : (! [X1] : (((r1_partfun1(X0,X1) | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0)))) & (! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0))) | ~r1_partfun1(X0,X1))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.66/1.00    inference(nnf_transformation,[],[f17])).
% 2.66/1.00  
% 2.66/1.00  fof(f23,plain,(
% 2.66/1.00    ! [X0] : (! [X1] : (((r1_partfun1(X0,X1) | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0)))) & (! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r1_partfun1(X0,X1))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.66/1.00    inference(rectify,[],[f22])).
% 2.66/1.00  
% 2.66/1.00  fof(f24,plain,(
% 2.66/1.00    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1)) & r2_hidden(sK0(X0,X1),k1_relat_1(X0))))),
% 2.66/1.00    introduced(choice_axiom,[])).
% 2.66/1.00  
% 2.66/1.00  fof(f25,plain,(
% 2.66/1.00    ! [X0] : (! [X1] : (((r1_partfun1(X0,X1) | (k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1)) & r2_hidden(sK0(X0,X1),k1_relat_1(X0)))) & (! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r1_partfun1(X0,X1))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.66/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).
% 2.66/1.00  
% 2.66/1.00  fof(f45,plain,(
% 2.66/1.00    ( ! [X0,X1] : (r1_partfun1(X0,X1) | r2_hidden(sK0(X0,X1),k1_relat_1(X0)) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.66/1.00    inference(cnf_transformation,[],[f25])).
% 2.66/1.00  
% 2.66/1.00  fof(f53,plain,(
% 2.66/1.00    ( ! [X5] : (k1_funct_1(sK3,X5) = k1_funct_1(sK4,X5) | ~r2_hidden(X5,k1_relset_1(sK1,sK2,sK3)) | r1_partfun1(sK3,sK4)) )),
% 2.66/1.00    inference(cnf_transformation,[],[f32])).
% 2.66/1.00  
% 2.66/1.00  fof(f47,plain,(
% 2.66/1.00    v1_funct_1(sK3)),
% 2.66/1.00    inference(cnf_transformation,[],[f32])).
% 2.66/1.00  
% 2.66/1.00  fof(f2,axiom,(
% 2.66/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.66/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.66/1.00  
% 2.66/1.00  fof(f11,plain,(
% 2.66/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.66/1.00    inference(ennf_transformation,[],[f2])).
% 2.66/1.00  
% 2.66/1.00  fof(f35,plain,(
% 2.66/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.66/1.00    inference(cnf_transformation,[],[f11])).
% 2.66/1.00  
% 2.66/1.00  fof(f49,plain,(
% 2.66/1.00    v1_funct_1(sK4)),
% 2.66/1.00    inference(cnf_transformation,[],[f32])).
% 2.66/1.00  
% 2.66/1.00  fof(f3,axiom,(
% 2.66/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.66/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.66/1.00  
% 2.66/1.00  fof(f9,plain,(
% 2.66/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.66/1.00    inference(pure_predicate_removal,[],[f3])).
% 2.66/1.00  
% 2.66/1.00  fof(f12,plain,(
% 2.66/1.00    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.66/1.00    inference(ennf_transformation,[],[f9])).
% 2.66/1.00  
% 2.66/1.00  fof(f36,plain,(
% 2.66/1.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.66/1.00    inference(cnf_transformation,[],[f12])).
% 2.66/1.00  
% 2.66/1.00  fof(f1,axiom,(
% 2.66/1.00    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 2.66/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.66/1.00  
% 2.66/1.00  fof(f10,plain,(
% 2.66/1.00    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.66/1.00    inference(ennf_transformation,[],[f1])).
% 2.66/1.00  
% 2.66/1.00  fof(f20,plain,(
% 2.66/1.00    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.66/1.00    inference(nnf_transformation,[],[f10])).
% 2.66/1.00  
% 2.66/1.00  fof(f33,plain,(
% 2.66/1.00    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.66/1.00    inference(cnf_transformation,[],[f20])).
% 2.66/1.00  
% 2.66/1.00  fof(f44,plain,(
% 2.66/1.00    ( ! [X0,X3,X1] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r1_partfun1(X0,X1) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.66/1.00    inference(cnf_transformation,[],[f25])).
% 2.66/1.00  
% 2.66/1.00  fof(f46,plain,(
% 2.66/1.00    ( ! [X0,X1] : (r1_partfun1(X0,X1) | k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1)) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.66/1.00    inference(cnf_transformation,[],[f25])).
% 2.66/1.00  
% 2.66/1.00  fof(f55,plain,(
% 2.66/1.00    k1_funct_1(sK3,sK5) != k1_funct_1(sK4,sK5) | ~r1_partfun1(sK3,sK4)),
% 2.66/1.00    inference(cnf_transformation,[],[f32])).
% 2.66/1.00  
% 2.66/1.00  fof(f52,plain,(
% 2.66/1.00    k1_xboole_0 = sK1 | k1_xboole_0 != sK2),
% 2.66/1.00    inference(cnf_transformation,[],[f32])).
% 2.66/1.00  
% 2.66/1.00  fof(f39,plain,(
% 2.66/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.66/1.00    inference(cnf_transformation,[],[f21])).
% 2.66/1.00  
% 2.66/1.00  fof(f60,plain,(
% 2.66/1.00    ( ! [X2,X1] : (k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0 | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 2.66/1.00    inference(equality_resolution,[],[f39])).
% 2.66/1.00  
% 2.66/1.00  fof(f42,plain,(
% 2.66/1.00    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.66/1.00    inference(cnf_transformation,[],[f21])).
% 2.66/1.00  
% 2.66/1.00  fof(f58,plain,(
% 2.66/1.00    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 2.66/1.00    inference(equality_resolution,[],[f42])).
% 2.66/1.00  
% 2.66/1.00  cnf(c_4,plain,
% 2.66/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.66/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.66/1.00      inference(cnf_transformation,[],[f37]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_21,negated_conjecture,
% 2.66/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 2.66/1.00      inference(cnf_transformation,[],[f48]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_635,plain,
% 2.66/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.66/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.66/1.00      | sK3 != X2 ),
% 2.66/1.00      inference(resolution_lifted,[status(thm)],[c_4,c_21]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_636,plain,
% 2.66/1.00      ( k1_relset_1(X0,X1,sK3) = k1_relat_1(sK3)
% 2.66/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 2.66/1.00      inference(unflattening,[status(thm)],[c_635]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_2183,plain,
% 2.66/1.00      ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
% 2.66/1.00      inference(equality_resolution,[status(thm)],[c_636]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_15,negated_conjecture,
% 2.66/1.00      ( r2_hidden(sK5,k1_relset_1(sK1,sK2,sK3))
% 2.66/1.00      | ~ r1_partfun1(sK3,sK4) ),
% 2.66/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_1883,plain,
% 2.66/1.00      ( r2_hidden(sK5,k1_relset_1(sK1,sK2,sK3)) = iProver_top
% 2.66/1.00      | r1_partfun1(sK3,sK4) != iProver_top ),
% 2.66/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_2367,plain,
% 2.66/1.00      ( r2_hidden(sK5,k1_relat_1(sK3)) = iProver_top
% 2.66/1.00      | r1_partfun1(sK3,sK4) != iProver_top ),
% 2.66/1.00      inference(demodulation,[status(thm)],[c_2183,c_1883]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_19,negated_conjecture,
% 2.66/1.00      ( v1_funct_2(sK4,sK1,sK2) ),
% 2.66/1.00      inference(cnf_transformation,[],[f50]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_10,plain,
% 2.66/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.66/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.66/1.00      | k1_relset_1(X1,X2,X0) = X1
% 2.66/1.00      | k1_xboole_0 = X2 ),
% 2.66/1.00      inference(cnf_transformation,[],[f38]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_18,negated_conjecture,
% 2.66/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 2.66/1.00      inference(cnf_transformation,[],[f51]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_530,plain,
% 2.66/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.66/1.00      | k1_relset_1(X1,X2,X0) = X1
% 2.66/1.00      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.66/1.00      | sK4 != X0
% 2.66/1.00      | k1_xboole_0 = X2 ),
% 2.66/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_18]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_531,plain,
% 2.66/1.00      ( ~ v1_funct_2(sK4,X0,X1)
% 2.66/1.00      | k1_relset_1(X0,X1,sK4) = X0
% 2.66/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.66/1.00      | k1_xboole_0 = X1 ),
% 2.66/1.00      inference(unflattening,[status(thm)],[c_530]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_1384,plain,
% 2.66/1.00      ( k1_relset_1(X0,X1,sK4) = X0
% 2.66/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.66/1.00      | sK2 != X1
% 2.66/1.00      | sK1 != X0
% 2.66/1.00      | sK4 != sK4
% 2.66/1.00      | k1_xboole_0 = X1 ),
% 2.66/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_531]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_1385,plain,
% 2.66/1.00      ( k1_relset_1(sK1,sK2,sK4) = sK1
% 2.66/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.66/1.00      | k1_xboole_0 = sK2 ),
% 2.66/1.00      inference(unflattening,[status(thm)],[c_1384]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_1928,plain,
% 2.66/1.00      ( k1_relset_1(sK1,sK2,sK4) = sK1 | k1_xboole_0 = sK2 ),
% 2.66/1.00      inference(equality_resolution_simp,[status(thm)],[c_1385]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_566,plain,
% 2.66/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.66/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.66/1.00      | sK4 != X2 ),
% 2.66/1.00      inference(resolution_lifted,[status(thm)],[c_4,c_18]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_567,plain,
% 2.66/1.00      ( k1_relset_1(X0,X1,sK4) = k1_relat_1(sK4)
% 2.66/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 2.66/1.00      inference(unflattening,[status(thm)],[c_566]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_2140,plain,
% 2.66/1.00      ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
% 2.66/1.00      inference(equality_resolution,[status(thm)],[c_567]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_2701,plain,
% 2.66/1.00      ( k1_relat_1(sK4) = sK1 | sK2 = k1_xboole_0 ),
% 2.66/1.00      inference(demodulation,[status(thm)],[c_1928,c_2140]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_12,plain,
% 2.66/1.00      ( r2_hidden(sK0(X0,X1),k1_relat_1(X0))
% 2.66/1.00      | r1_partfun1(X0,X1)
% 2.66/1.00      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 2.66/1.00      | ~ v1_funct_1(X1)
% 2.66/1.00      | ~ v1_funct_1(X0)
% 2.66/1.00      | ~ v1_relat_1(X1)
% 2.66/1.00      | ~ v1_relat_1(X0) ),
% 2.66/1.00      inference(cnf_transformation,[],[f45]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_1886,plain,
% 2.66/1.00      ( r2_hidden(sK0(X0,X1),k1_relat_1(X0)) = iProver_top
% 2.66/1.00      | r1_partfun1(X0,X1) = iProver_top
% 2.66/1.00      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) != iProver_top
% 2.66/1.00      | v1_funct_1(X1) != iProver_top
% 2.66/1.00      | v1_funct_1(X0) != iProver_top
% 2.66/1.00      | v1_relat_1(X1) != iProver_top
% 2.66/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.66/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_16,negated_conjecture,
% 2.66/1.00      ( ~ r2_hidden(X0,k1_relset_1(sK1,sK2,sK3))
% 2.66/1.00      | r1_partfun1(sK3,sK4)
% 2.66/1.00      | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0) ),
% 2.66/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_1882,plain,
% 2.66/1.00      ( k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0)
% 2.66/1.00      | r2_hidden(X0,k1_relset_1(sK1,sK2,sK3)) != iProver_top
% 2.66/1.00      | r1_partfun1(sK3,sK4) = iProver_top ),
% 2.66/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_2366,plain,
% 2.66/1.00      ( k1_funct_1(sK4,X0) = k1_funct_1(sK3,X0)
% 2.66/1.00      | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 2.66/1.00      | r1_partfun1(sK3,sK4) = iProver_top ),
% 2.66/1.00      inference(demodulation,[status(thm)],[c_2183,c_1882]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_2604,plain,
% 2.66/1.00      ( k1_funct_1(sK3,sK0(sK3,X0)) = k1_funct_1(sK4,sK0(sK3,X0))
% 2.66/1.00      | r1_partfun1(sK3,X0) = iProver_top
% 2.66/1.00      | r1_partfun1(sK3,sK4) = iProver_top
% 2.66/1.00      | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) != iProver_top
% 2.66/1.00      | v1_funct_1(X0) != iProver_top
% 2.66/1.00      | v1_funct_1(sK3) != iProver_top
% 2.66/1.00      | v1_relat_1(X0) != iProver_top
% 2.66/1.00      | v1_relat_1(sK3) != iProver_top ),
% 2.66/1.00      inference(superposition,[status(thm)],[c_1886,c_2366]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_22,negated_conjecture,
% 2.66/1.00      ( v1_funct_1(sK3) ),
% 2.66/1.00      inference(cnf_transformation,[],[f47]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_23,plain,
% 2.66/1.00      ( v1_funct_1(sK3) = iProver_top ),
% 2.66/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_1605,plain,( X0 = X0 ),theory(equality) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_2100,plain,
% 2.66/1.00      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 2.66/1.00      inference(instantiation,[status(thm)],[c_1605]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_2,plain,
% 2.66/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.66/1.00      | v1_relat_1(X0) ),
% 2.66/1.00      inference(cnf_transformation,[],[f35]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_644,plain,
% 2.66/1.00      ( v1_relat_1(X0)
% 2.66/1.00      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.66/1.00      | sK3 != X0 ),
% 2.66/1.00      inference(resolution_lifted,[status(thm)],[c_2,c_21]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_645,plain,
% 2.66/1.00      ( v1_relat_1(sK3)
% 2.66/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 2.66/1.00      inference(unflattening,[status(thm)],[c_644]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_2105,plain,
% 2.66/1.00      ( v1_relat_1(sK3)
% 2.66/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 2.66/1.00      inference(instantiation,[status(thm)],[c_645]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_2109,plain,
% 2.66/1.00      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.66/1.00      | v1_relat_1(sK3) = iProver_top ),
% 2.66/1.00      inference(predicate_to_equality,[status(thm)],[c_2105]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_2638,plain,
% 2.66/1.00      ( v1_relat_1(X0) != iProver_top
% 2.66/1.00      | k1_funct_1(sK3,sK0(sK3,X0)) = k1_funct_1(sK4,sK0(sK3,X0))
% 2.66/1.00      | r1_partfun1(sK3,X0) = iProver_top
% 2.66/1.00      | r1_partfun1(sK3,sK4) = iProver_top
% 2.66/1.00      | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) != iProver_top
% 2.66/1.00      | v1_funct_1(X0) != iProver_top ),
% 2.66/1.00      inference(global_propositional_subsumption,
% 2.66/1.00                [status(thm)],
% 2.66/1.00                [c_2604,c_23,c_2100,c_2109]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_2639,plain,
% 2.66/1.00      ( k1_funct_1(sK3,sK0(sK3,X0)) = k1_funct_1(sK4,sK0(sK3,X0))
% 2.66/1.00      | r1_partfun1(sK3,X0) = iProver_top
% 2.66/1.00      | r1_partfun1(sK3,sK4) = iProver_top
% 2.66/1.00      | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) != iProver_top
% 2.66/1.00      | v1_funct_1(X0) != iProver_top
% 2.66/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.66/1.00      inference(renaming,[status(thm)],[c_2638]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_2704,plain,
% 2.66/1.00      ( k1_funct_1(sK4,sK0(sK3,sK4)) = k1_funct_1(sK3,sK0(sK3,sK4))
% 2.66/1.00      | sK2 = k1_xboole_0
% 2.66/1.00      | r1_partfun1(sK3,sK4) = iProver_top
% 2.66/1.00      | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top
% 2.66/1.00      | v1_funct_1(sK4) != iProver_top
% 2.66/1.00      | v1_relat_1(sK4) != iProver_top ),
% 2.66/1.00      inference(superposition,[status(thm)],[c_2701,c_2639]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_20,negated_conjecture,
% 2.66/1.00      ( v1_funct_1(sK4) ),
% 2.66/1.00      inference(cnf_transformation,[],[f49]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_25,plain,
% 2.66/1.00      ( v1_funct_1(sK4) = iProver_top ),
% 2.66/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_575,plain,
% 2.66/1.00      ( v1_relat_1(X0)
% 2.66/1.00      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.66/1.00      | sK4 != X0 ),
% 2.66/1.00      inference(resolution_lifted,[status(thm)],[c_2,c_18]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_576,plain,
% 2.66/1.00      ( v1_relat_1(sK4)
% 2.66/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 2.66/1.00      inference(unflattening,[status(thm)],[c_575]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_2106,plain,
% 2.66/1.00      ( v1_relat_1(sK4)
% 2.66/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 2.66/1.00      inference(instantiation,[status(thm)],[c_576]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_2107,plain,
% 2.66/1.00      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.66/1.00      | v1_relat_1(sK4) = iProver_top ),
% 2.66/1.00      inference(predicate_to_equality,[status(thm)],[c_2106]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_3,plain,
% 2.66/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.66/1.00      | v4_relat_1(X0,X1) ),
% 2.66/1.00      inference(cnf_transformation,[],[f36]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_1,plain,
% 2.66/1.00      ( r1_tarski(k1_relat_1(X0),X1)
% 2.66/1.00      | ~ v4_relat_1(X0,X1)
% 2.66/1.00      | ~ v1_relat_1(X0) ),
% 2.66/1.00      inference(cnf_transformation,[],[f33]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_247,plain,
% 2.66/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.66/1.00      | r1_tarski(k1_relat_1(X0),X1)
% 2.66/1.00      | ~ v1_relat_1(X0) ),
% 2.66/1.00      inference(resolution,[status(thm)],[c_3,c_1]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_251,plain,
% 2.66/1.00      ( r1_tarski(k1_relat_1(X0),X1)
% 2.66/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.66/1.00      inference(global_propositional_subsumption,
% 2.66/1.00                [status(thm)],
% 2.66/1.00                [c_247,c_2]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_252,plain,
% 2.66/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.66/1.00      | r1_tarski(k1_relat_1(X0),X1) ),
% 2.66/1.00      inference(renaming,[status(thm)],[c_251]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_587,plain,
% 2.66/1.00      ( r1_tarski(k1_relat_1(X0),X1)
% 2.66/1.00      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.66/1.00      | sK3 != X0 ),
% 2.66/1.00      inference(resolution_lifted,[status(thm)],[c_252,c_21]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_588,plain,
% 2.66/1.00      ( r1_tarski(k1_relat_1(sK3),X0)
% 2.66/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 2.66/1.00      inference(unflattening,[status(thm)],[c_587]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_2103,plain,
% 2.66/1.00      ( r1_tarski(k1_relat_1(sK3),sK1)
% 2.66/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 2.66/1.00      inference(instantiation,[status(thm)],[c_588]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_2113,plain,
% 2.66/1.00      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.66/1.00      | r1_tarski(k1_relat_1(sK3),sK1) = iProver_top ),
% 2.66/1.00      inference(predicate_to_equality,[status(thm)],[c_2103]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_3503,plain,
% 2.66/1.00      ( r1_partfun1(sK3,sK4) = iProver_top
% 2.66/1.00      | sK2 = k1_xboole_0
% 2.66/1.00      | k1_funct_1(sK4,sK0(sK3,sK4)) = k1_funct_1(sK3,sK0(sK3,sK4)) ),
% 2.66/1.00      inference(global_propositional_subsumption,
% 2.66/1.00                [status(thm)],
% 2.66/1.00                [c_2704,c_25,c_2100,c_2107,c_2113]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_3504,plain,
% 2.66/1.00      ( k1_funct_1(sK4,sK0(sK3,sK4)) = k1_funct_1(sK3,sK0(sK3,sK4))
% 2.66/1.00      | sK2 = k1_xboole_0
% 2.66/1.00      | r1_partfun1(sK3,sK4) = iProver_top ),
% 2.66/1.00      inference(renaming,[status(thm)],[c_3503]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_13,plain,
% 2.66/1.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.66/1.00      | ~ r1_partfun1(X1,X2)
% 2.66/1.00      | ~ r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
% 2.66/1.00      | ~ v1_funct_1(X2)
% 2.66/1.00      | ~ v1_funct_1(X1)
% 2.66/1.00      | ~ v1_relat_1(X2)
% 2.66/1.00      | ~ v1_relat_1(X1)
% 2.66/1.00      | k1_funct_1(X2,X0) = k1_funct_1(X1,X0) ),
% 2.66/1.00      inference(cnf_transformation,[],[f44]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_1885,plain,
% 2.66/1.00      ( k1_funct_1(X0,X1) = k1_funct_1(X2,X1)
% 2.66/1.00      | r2_hidden(X1,k1_relat_1(X2)) != iProver_top
% 2.66/1.00      | r1_partfun1(X2,X0) != iProver_top
% 2.66/1.00      | r1_tarski(k1_relat_1(X2),k1_relat_1(X0)) != iProver_top
% 2.66/1.00      | v1_funct_1(X0) != iProver_top
% 2.66/1.00      | v1_funct_1(X2) != iProver_top
% 2.66/1.00      | v1_relat_1(X0) != iProver_top
% 2.66/1.00      | v1_relat_1(X2) != iProver_top ),
% 2.66/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_2707,plain,
% 2.66/1.00      ( k1_funct_1(X0,X1) = k1_funct_1(sK4,X1)
% 2.66/1.00      | sK2 = k1_xboole_0
% 2.66/1.00      | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
% 2.66/1.00      | r1_partfun1(X0,sK4) != iProver_top
% 2.66/1.00      | r1_tarski(k1_relat_1(X0),sK1) != iProver_top
% 2.66/1.00      | v1_funct_1(X0) != iProver_top
% 2.66/1.00      | v1_funct_1(sK4) != iProver_top
% 2.66/1.00      | v1_relat_1(X0) != iProver_top
% 2.66/1.00      | v1_relat_1(sK4) != iProver_top ),
% 2.66/1.00      inference(superposition,[status(thm)],[c_2701,c_1885]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_3051,plain,
% 2.66/1.00      ( v1_relat_1(X0) != iProver_top
% 2.66/1.00      | k1_funct_1(X0,X1) = k1_funct_1(sK4,X1)
% 2.66/1.00      | sK2 = k1_xboole_0
% 2.66/1.00      | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
% 2.66/1.00      | r1_partfun1(X0,sK4) != iProver_top
% 2.66/1.00      | r1_tarski(k1_relat_1(X0),sK1) != iProver_top
% 2.66/1.00      | v1_funct_1(X0) != iProver_top ),
% 2.66/1.00      inference(global_propositional_subsumption,
% 2.66/1.00                [status(thm)],
% 2.66/1.00                [c_2707,c_25,c_2100,c_2107]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_3052,plain,
% 2.66/1.00      ( k1_funct_1(X0,X1) = k1_funct_1(sK4,X1)
% 2.66/1.00      | sK2 = k1_xboole_0
% 2.66/1.00      | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
% 2.66/1.00      | r1_partfun1(X0,sK4) != iProver_top
% 2.66/1.00      | r1_tarski(k1_relat_1(X0),sK1) != iProver_top
% 2.66/1.00      | v1_funct_1(X0) != iProver_top
% 2.66/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.66/1.00      inference(renaming,[status(thm)],[c_3051]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_3065,plain,
% 2.66/1.00      ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
% 2.66/1.00      | sK2 = k1_xboole_0
% 2.66/1.00      | r1_partfun1(sK3,sK4) != iProver_top
% 2.66/1.00      | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top
% 2.66/1.00      | v1_funct_1(sK3) != iProver_top
% 2.66/1.00      | v1_relat_1(sK3) != iProver_top ),
% 2.66/1.00      inference(superposition,[status(thm)],[c_2367,c_3052]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_3289,plain,
% 2.66/1.00      ( r1_partfun1(sK3,sK4) != iProver_top
% 2.66/1.00      | sK2 = k1_xboole_0
% 2.66/1.00      | k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5) ),
% 2.66/1.00      inference(global_propositional_subsumption,
% 2.66/1.00                [status(thm)],
% 2.66/1.00                [c_3065,c_23,c_2100,c_2109,c_2113]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_3290,plain,
% 2.66/1.00      ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
% 2.66/1.00      | sK2 = k1_xboole_0
% 2.66/1.00      | r1_partfun1(sK3,sK4) != iProver_top ),
% 2.66/1.00      inference(renaming,[status(thm)],[c_3289]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_3510,plain,
% 2.66/1.00      ( k1_funct_1(sK4,sK0(sK3,sK4)) = k1_funct_1(sK3,sK0(sK3,sK4))
% 2.66/1.00      | k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
% 2.66/1.00      | sK2 = k1_xboole_0 ),
% 2.66/1.00      inference(superposition,[status(thm)],[c_3504,c_3290]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_11,plain,
% 2.66/1.00      ( r1_partfun1(X0,X1)
% 2.66/1.00      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 2.66/1.00      | ~ v1_funct_1(X1)
% 2.66/1.00      | ~ v1_funct_1(X0)
% 2.66/1.00      | ~ v1_relat_1(X1)
% 2.66/1.00      | ~ v1_relat_1(X0)
% 2.66/1.00      | k1_funct_1(X1,sK0(X0,X1)) != k1_funct_1(X0,sK0(X0,X1)) ),
% 2.66/1.00      inference(cnf_transformation,[],[f46]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_1887,plain,
% 2.66/1.00      ( k1_funct_1(X0,sK0(X1,X0)) != k1_funct_1(X1,sK0(X1,X0))
% 2.66/1.00      | r1_partfun1(X1,X0) = iProver_top
% 2.66/1.00      | r1_tarski(k1_relat_1(X1),k1_relat_1(X0)) != iProver_top
% 2.66/1.00      | v1_funct_1(X0) != iProver_top
% 2.66/1.00      | v1_funct_1(X1) != iProver_top
% 2.66/1.00      | v1_relat_1(X0) != iProver_top
% 2.66/1.00      | v1_relat_1(X1) != iProver_top ),
% 2.66/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_3514,plain,
% 2.66/1.00      ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
% 2.66/1.00      | sK2 = k1_xboole_0
% 2.66/1.00      | r1_partfun1(sK3,sK4) = iProver_top
% 2.66/1.00      | r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4)) != iProver_top
% 2.66/1.00      | v1_funct_1(sK4) != iProver_top
% 2.66/1.00      | v1_funct_1(sK3) != iProver_top
% 2.66/1.00      | v1_relat_1(sK4) != iProver_top
% 2.66/1.00      | v1_relat_1(sK3) != iProver_top ),
% 2.66/1.00      inference(superposition,[status(thm)],[c_3510,c_1887]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_2151,plain,
% 2.66/1.00      ( r1_partfun1(X0,sK4)
% 2.66/1.00      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(sK4))
% 2.66/1.00      | ~ v1_funct_1(X0)
% 2.66/1.00      | ~ v1_funct_1(sK4)
% 2.66/1.00      | ~ v1_relat_1(X0)
% 2.66/1.00      | ~ v1_relat_1(sK4)
% 2.66/1.00      | k1_funct_1(sK4,sK0(X0,sK4)) != k1_funct_1(X0,sK0(X0,sK4)) ),
% 2.66/1.00      inference(instantiation,[status(thm)],[c_11]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_2204,plain,
% 2.66/1.00      ( r1_partfun1(sK3,sK4)
% 2.66/1.00      | ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4))
% 2.66/1.00      | ~ v1_funct_1(sK4)
% 2.66/1.00      | ~ v1_funct_1(sK3)
% 2.66/1.00      | ~ v1_relat_1(sK4)
% 2.66/1.00      | ~ v1_relat_1(sK3)
% 2.66/1.00      | k1_funct_1(sK4,sK0(sK3,sK4)) != k1_funct_1(sK3,sK0(sK3,sK4)) ),
% 2.66/1.00      inference(instantiation,[status(thm)],[c_2151]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_2205,plain,
% 2.66/1.00      ( k1_funct_1(sK4,sK0(sK3,sK4)) != k1_funct_1(sK3,sK0(sK3,sK4))
% 2.66/1.00      | r1_partfun1(sK3,sK4) = iProver_top
% 2.66/1.00      | r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4)) != iProver_top
% 2.66/1.00      | v1_funct_1(sK4) != iProver_top
% 2.66/1.00      | v1_funct_1(sK3) != iProver_top
% 2.66/1.00      | v1_relat_1(sK4) != iProver_top
% 2.66/1.00      | v1_relat_1(sK3) != iProver_top ),
% 2.66/1.00      inference(predicate_to_equality,[status(thm)],[c_2204]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_3553,plain,
% 2.66/1.00      ( sK2 = k1_xboole_0
% 2.66/1.00      | r1_partfun1(sK3,sK4) = iProver_top
% 2.66/1.00      | r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4)) != iProver_top ),
% 2.66/1.00      inference(global_propositional_subsumption,
% 2.66/1.00                [status(thm)],
% 2.66/1.00                [c_3514,c_23,c_25,c_2100,c_2107,c_2109,c_2113,c_2205,
% 2.66/1.00                 c_2704]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_3560,plain,
% 2.66/1.00      ( sK2 = k1_xboole_0
% 2.66/1.00      | r1_partfun1(sK3,sK4) = iProver_top
% 2.66/1.00      | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top ),
% 2.66/1.00      inference(superposition,[status(thm)],[c_2701,c_3553]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_3563,plain,
% 2.66/1.00      ( r1_partfun1(sK3,sK4) = iProver_top | sK2 = k1_xboole_0 ),
% 2.66/1.00      inference(global_propositional_subsumption,
% 2.66/1.00                [status(thm)],
% 2.66/1.00                [c_3560,c_2100,c_2113]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_3564,plain,
% 2.66/1.00      ( sK2 = k1_xboole_0 | r1_partfun1(sK3,sK4) = iProver_top ),
% 2.66/1.00      inference(renaming,[status(thm)],[c_3563]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_3569,plain,
% 2.66/1.00      ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5) | sK2 = k1_xboole_0 ),
% 2.66/1.00      inference(superposition,[status(thm)],[c_3564,c_3290]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_14,negated_conjecture,
% 2.66/1.00      ( ~ r1_partfun1(sK3,sK4)
% 2.66/1.00      | k1_funct_1(sK3,sK5) != k1_funct_1(sK4,sK5) ),
% 2.66/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_1884,plain,
% 2.66/1.00      ( k1_funct_1(sK3,sK5) != k1_funct_1(sK4,sK5)
% 2.66/1.00      | r1_partfun1(sK3,sK4) != iProver_top ),
% 2.66/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_3643,plain,
% 2.66/1.00      ( sK2 = k1_xboole_0 | r1_partfun1(sK3,sK4) != iProver_top ),
% 2.66/1.00      inference(superposition,[status(thm)],[c_3569,c_1884]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_3646,plain,
% 2.66/1.00      ( sK2 = k1_xboole_0 ),
% 2.66/1.00      inference(global_propositional_subsumption,
% 2.66/1.00                [status(thm)],
% 2.66/1.00                [c_3643,c_2100,c_2113,c_3560]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_3661,plain,
% 2.66/1.00      ( k1_relset_1(sK1,k1_xboole_0,sK4) = k1_relat_1(sK4) ),
% 2.66/1.00      inference(demodulation,[status(thm)],[c_3646,c_2140]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_17,negated_conjecture,
% 2.66/1.00      ( k1_xboole_0 != sK2 | k1_xboole_0 = sK1 ),
% 2.66/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_3667,plain,
% 2.66/1.00      ( sK1 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 2.66/1.00      inference(demodulation,[status(thm)],[c_3646,c_17]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_3668,plain,
% 2.66/1.00      ( sK1 = k1_xboole_0 ),
% 2.66/1.00      inference(equality_resolution_simp,[status(thm)],[c_3667]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_9,plain,
% 2.66/1.00      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 2.66/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.66/1.00      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 2.66/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_726,plain,
% 2.66/1.00      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 2.66/1.00      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 2.66/1.00      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.66/1.00      | sK4 != X0 ),
% 2.66/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_18]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_727,plain,
% 2.66/1.00      ( ~ v1_funct_2(sK4,k1_xboole_0,X0)
% 2.66/1.00      | k1_relset_1(k1_xboole_0,X0,sK4) = k1_xboole_0
% 2.66/1.00      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 2.66/1.00      inference(unflattening,[status(thm)],[c_726]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_1440,plain,
% 2.66/1.00      ( k1_relset_1(k1_xboole_0,X0,sK4) = k1_xboole_0
% 2.66/1.00      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.66/1.00      | sK2 != X0
% 2.66/1.00      | sK1 != k1_xboole_0
% 2.66/1.00      | sK4 != sK4 ),
% 2.66/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_727]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_1441,plain,
% 2.66/1.00      ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
% 2.66/1.00      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.66/1.00      | sK1 != k1_xboole_0 ),
% 2.66/1.00      inference(unflattening,[status(thm)],[c_1440]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_3664,plain,
% 2.66/1.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
% 2.66/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
% 2.66/1.00      | sK1 != k1_xboole_0 ),
% 2.66/1.00      inference(demodulation,[status(thm)],[c_3646,c_1441]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_3681,plain,
% 2.66/1.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
% 2.66/1.00      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
% 2.66/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 2.66/1.00      inference(light_normalisation,[status(thm)],[c_3664,c_3668]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_3682,plain,
% 2.66/1.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0 ),
% 2.66/1.00      inference(equality_resolution_simp,[status(thm)],[c_3681]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_3692,plain,
% 2.66/1.00      ( k1_relat_1(sK4) = k1_xboole_0 ),
% 2.66/1.00      inference(light_normalisation,[status(thm)],[c_3661,c_3668,c_3682]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_3811,plain,
% 2.66/1.00      ( k1_funct_1(X0,X1) = k1_funct_1(sK4,X1)
% 2.66/1.00      | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
% 2.66/1.00      | r1_partfun1(X0,sK4) != iProver_top
% 2.66/1.00      | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
% 2.66/1.00      | v1_funct_1(X0) != iProver_top
% 2.66/1.00      | v1_funct_1(sK4) != iProver_top
% 2.66/1.00      | v1_relat_1(X0) != iProver_top
% 2.66/1.00      | v1_relat_1(sK4) != iProver_top ),
% 2.66/1.00      inference(superposition,[status(thm)],[c_3692,c_1885]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_4113,plain,
% 2.66/1.00      ( v1_relat_1(X0) != iProver_top
% 2.66/1.00      | k1_funct_1(X0,X1) = k1_funct_1(sK4,X1)
% 2.66/1.00      | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
% 2.66/1.00      | r1_partfun1(X0,sK4) != iProver_top
% 2.66/1.00      | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
% 2.66/1.00      | v1_funct_1(X0) != iProver_top ),
% 2.66/1.00      inference(global_propositional_subsumption,
% 2.66/1.00                [status(thm)],
% 2.66/1.00                [c_3811,c_25,c_2100,c_2107]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_4114,plain,
% 2.66/1.00      ( k1_funct_1(X0,X1) = k1_funct_1(sK4,X1)
% 2.66/1.00      | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
% 2.66/1.00      | r1_partfun1(X0,sK4) != iProver_top
% 2.66/1.00      | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
% 2.66/1.00      | v1_funct_1(X0) != iProver_top
% 2.66/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.66/1.00      inference(renaming,[status(thm)],[c_4113]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_4126,plain,
% 2.66/1.00      ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
% 2.66/1.00      | r1_partfun1(sK3,sK4) != iProver_top
% 2.66/1.00      | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top
% 2.66/1.00      | v1_funct_1(sK3) != iProver_top
% 2.66/1.00      | v1_relat_1(sK3) != iProver_top ),
% 2.66/1.00      inference(superposition,[status(thm)],[c_2367,c_4114]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_6,plain,
% 2.66/1.00      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 2.66/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 2.66/1.00      | k1_xboole_0 = X1
% 2.66/1.00      | k1_xboole_0 = X0 ),
% 2.66/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_690,plain,
% 2.66/1.00      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 2.66/1.00      | k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.66/1.00      | sK4 != X0
% 2.66/1.00      | k1_xboole_0 = X1
% 2.66/1.00      | k1_xboole_0 = X0 ),
% 2.66/1.00      inference(resolution_lifted,[status(thm)],[c_6,c_18]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_691,plain,
% 2.66/1.00      ( ~ v1_funct_2(sK4,X0,k1_xboole_0)
% 2.66/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.66/1.00      | k1_xboole_0 = X0
% 2.66/1.00      | k1_xboole_0 = sK4 ),
% 2.66/1.00      inference(unflattening,[status(thm)],[c_690]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_1409,plain,
% 2.66/1.00      ( k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.66/1.00      | sK2 != k1_xboole_0
% 2.66/1.00      | sK1 != X0
% 2.66/1.00      | sK4 != sK4
% 2.66/1.00      | sK4 = k1_xboole_0
% 2.66/1.00      | k1_xboole_0 = X0 ),
% 2.66/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_691]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_1410,plain,
% 2.66/1.00      ( k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.66/1.00      | sK2 != k1_xboole_0
% 2.66/1.00      | sK4 = k1_xboole_0
% 2.66/1.00      | k1_xboole_0 = sK1 ),
% 2.66/1.00      inference(unflattening,[status(thm)],[c_1409]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_1628,plain,
% 2.66/1.00      ( k1_xboole_0 = k1_xboole_0 ),
% 2.66/1.00      inference(instantiation,[status(thm)],[c_1605]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_1606,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_2127,plain,
% 2.66/1.00      ( sK2 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK2 ),
% 2.66/1.00      inference(instantiation,[status(thm)],[c_1606]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_2128,plain,
% 2.66/1.00      ( sK2 != k1_xboole_0
% 2.66/1.00      | k1_xboole_0 = sK2
% 2.66/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 2.66/1.00      inference(instantiation,[status(thm)],[c_2127]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_2215,plain,
% 2.66/1.00      ( sK2 != k1_xboole_0 | k1_xboole_0 = sK1 ),
% 2.66/1.00      inference(global_propositional_subsumption,
% 2.66/1.00                [status(thm)],
% 2.66/1.00                [c_1410,c_17,c_1628,c_2128]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_1608,plain,
% 2.66/1.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.66/1.00      theory(equality) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_2225,plain,
% 2.66/1.00      ( r1_tarski(X0,X1)
% 2.66/1.00      | ~ r1_tarski(k1_relat_1(sK3),sK1)
% 2.66/1.00      | X0 != k1_relat_1(sK3)
% 2.66/1.00      | X1 != sK1 ),
% 2.66/1.00      inference(instantiation,[status(thm)],[c_1608]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_2382,plain,
% 2.66/1.00      ( r1_tarski(X0,k1_xboole_0)
% 2.66/1.00      | ~ r1_tarski(k1_relat_1(sK3),sK1)
% 2.66/1.00      | X0 != k1_relat_1(sK3)
% 2.66/1.00      | k1_xboole_0 != sK1 ),
% 2.66/1.00      inference(instantiation,[status(thm)],[c_2225]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_2897,plain,
% 2.66/1.00      ( ~ r1_tarski(k1_relat_1(sK3),sK1)
% 2.66/1.00      | r1_tarski(k1_relat_1(sK3),k1_xboole_0)
% 2.66/1.00      | k1_relat_1(sK3) != k1_relat_1(sK3)
% 2.66/1.00      | k1_xboole_0 != sK1 ),
% 2.66/1.00      inference(instantiation,[status(thm)],[c_2382]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_2899,plain,
% 2.66/1.00      ( k1_relat_1(sK3) != k1_relat_1(sK3)
% 2.66/1.00      | k1_xboole_0 != sK1
% 2.66/1.00      | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top
% 2.66/1.00      | r1_tarski(k1_relat_1(sK3),k1_xboole_0) = iProver_top ),
% 2.66/1.00      inference(predicate_to_equality,[status(thm)],[c_2897]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_2898,plain,
% 2.66/1.00      ( k1_relat_1(sK3) = k1_relat_1(sK3) ),
% 2.66/1.00      inference(instantiation,[status(thm)],[c_1605]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_2990,plain,
% 2.66/1.00      ( r1_tarski(X0,X1)
% 2.66/1.00      | ~ r1_tarski(k1_relat_1(sK3),X2)
% 2.66/1.00      | X1 != X2
% 2.66/1.00      | X0 != k1_relat_1(sK3) ),
% 2.66/1.00      inference(instantiation,[status(thm)],[c_1608]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_3758,plain,
% 2.66/1.00      ( ~ r1_tarski(k1_relat_1(sK3),X0)
% 2.66/1.00      | r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4))
% 2.66/1.00      | k1_relat_1(sK4) != X0
% 2.66/1.00      | k1_relat_1(sK3) != k1_relat_1(sK3) ),
% 2.66/1.00      inference(instantiation,[status(thm)],[c_2990]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_3759,plain,
% 2.66/1.00      ( k1_relat_1(sK4) != X0
% 2.66/1.00      | k1_relat_1(sK3) != k1_relat_1(sK3)
% 2.66/1.00      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top
% 2.66/1.00      | r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4)) = iProver_top ),
% 2.66/1.00      inference(predicate_to_equality,[status(thm)],[c_3758]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_3761,plain,
% 2.66/1.00      ( k1_relat_1(sK4) != k1_xboole_0
% 2.66/1.00      | k1_relat_1(sK3) != k1_relat_1(sK3)
% 2.66/1.00      | r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4)) = iProver_top
% 2.66/1.00      | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top ),
% 2.66/1.00      inference(instantiation,[status(thm)],[c_3759]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_3808,plain,
% 2.66/1.00      ( k1_funct_1(sK4,sK0(sK3,sK4)) = k1_funct_1(sK3,sK0(sK3,sK4))
% 2.66/1.00      | r1_partfun1(sK3,sK4) = iProver_top
% 2.66/1.00      | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top
% 2.66/1.00      | v1_funct_1(sK4) != iProver_top
% 2.66/1.00      | v1_relat_1(sK4) != iProver_top ),
% 2.66/1.00      inference(superposition,[status(thm)],[c_3692,c_2639]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_4264,plain,
% 2.66/1.00      ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5) ),
% 2.66/1.00      inference(global_propositional_subsumption,
% 2.66/1.00                [status(thm)],
% 2.66/1.00                [c_4126,c_23,c_25,c_2100,c_2107,c_2109,c_2113,c_2205,
% 2.66/1.00                 c_2215,c_2899,c_2898,c_3560,c_3643,c_3692,c_3761,c_3808]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_4267,plain,
% 2.66/1.00      ( k1_funct_1(sK3,sK5) != k1_funct_1(sK3,sK5)
% 2.66/1.00      | r1_partfun1(sK3,sK4) != iProver_top ),
% 2.66/1.00      inference(demodulation,[status(thm)],[c_4264,c_1884]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_4269,plain,
% 2.66/1.00      ( r1_partfun1(sK3,sK4) != iProver_top ),
% 2.66/1.00      inference(equality_resolution_simp,[status(thm)],[c_4267]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(contradiction,plain,
% 2.66/1.00      ( $false ),
% 2.66/1.00      inference(minisat,
% 2.66/1.00                [status(thm)],
% 2.66/1.00                [c_4269,c_3808,c_3761,c_3692,c_3646,c_2898,c_2899,c_2215,
% 2.66/1.00                 c_2205,c_2113,c_2109,c_2107,c_2100,c_25,c_23]) ).
% 2.66/1.00  
% 2.66/1.00  
% 2.66/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.66/1.00  
% 2.66/1.00  ------                               Statistics
% 2.66/1.00  
% 2.66/1.00  ------ General
% 2.66/1.00  
% 2.66/1.00  abstr_ref_over_cycles:                  0
% 2.66/1.00  abstr_ref_under_cycles:                 0
% 2.66/1.00  gc_basic_clause_elim:                   0
% 2.66/1.00  forced_gc_time:                         0
% 2.66/1.00  parsing_time:                           0.012
% 2.66/1.00  unif_index_cands_time:                  0.
% 2.66/1.00  unif_index_add_time:                    0.
% 2.66/1.00  orderings_time:                         0.
% 2.66/1.00  out_proof_time:                         0.031
% 2.66/1.00  total_time:                             0.184
% 2.66/1.00  num_of_symbols:                         51
% 2.66/1.00  num_of_terms:                           2360
% 2.66/1.00  
% 2.66/1.00  ------ Preprocessing
% 2.66/1.00  
% 2.66/1.00  num_of_splits:                          0
% 2.66/1.00  num_of_split_atoms:                     0
% 2.66/1.00  num_of_reused_defs:                     0
% 2.66/1.00  num_eq_ax_congr_red:                    8
% 2.66/1.00  num_of_sem_filtered_clauses:            1
% 2.66/1.00  num_of_subtypes:                        0
% 2.66/1.00  monotx_restored_types:                  0
% 2.66/1.00  sat_num_of_epr_types:                   0
% 2.66/1.00  sat_num_of_non_cyclic_types:            0
% 2.66/1.00  sat_guarded_non_collapsed_types:        0
% 2.66/1.00  num_pure_diseq_elim:                    0
% 2.66/1.00  simp_replaced_by:                       0
% 2.66/1.00  res_preprocessed:                       98
% 2.66/1.00  prep_upred:                             0
% 2.66/1.00  prep_unflattend:                        109
% 2.66/1.00  smt_new_axioms:                         0
% 2.66/1.00  pred_elim_cands:                        8
% 2.66/1.00  pred_elim:                              3
% 2.66/1.00  pred_elim_cl:                           -2
% 2.66/1.00  pred_elim_cycles:                       8
% 2.66/1.00  merged_defs:                            0
% 2.66/1.00  merged_defs_ncl:                        0
% 2.66/1.00  bin_hyper_res:                          0
% 2.66/1.00  prep_cycles:                            3
% 2.66/1.00  pred_elim_time:                         0.03
% 2.66/1.00  splitting_time:                         0.
% 2.66/1.00  sem_filter_time:                        0.
% 2.66/1.00  monotx_time:                            0.
% 2.66/1.00  subtype_inf_time:                       0.
% 2.66/1.00  
% 2.66/1.00  ------ Problem properties
% 2.66/1.00  
% 2.66/1.00  clauses:                                25
% 2.66/1.00  conjectures:                            6
% 2.66/1.00  epr:                                    3
% 2.66/1.00  horn:                                   17
% 2.66/1.00  ground:                                 11
% 2.66/1.00  unary:                                  2
% 2.66/1.00  binary:                                 9
% 2.66/1.00  lits:                                   86
% 2.66/1.00  lits_eq:                                55
% 2.66/1.00  fd_pure:                                0
% 2.66/1.00  fd_pseudo:                              0
% 2.66/1.00  fd_cond:                                0
% 2.66/1.00  fd_pseudo_cond:                         0
% 2.66/1.00  ac_symbols:                             0
% 2.66/1.00  
% 2.66/1.00  ------ Propositional Solver
% 2.66/1.00  
% 2.66/1.00  prop_solver_calls:                      24
% 2.66/1.00  prop_fast_solver_calls:                 1242
% 2.66/1.00  smt_solver_calls:                       0
% 2.66/1.00  smt_fast_solver_calls:                  0
% 2.66/1.00  prop_num_of_clauses:                    1104
% 2.66/1.00  prop_preprocess_simplified:             3460
% 2.66/1.00  prop_fo_subsumed:                       56
% 2.66/1.00  prop_solver_time:                       0.
% 2.66/1.00  smt_solver_time:                        0.
% 2.66/1.00  smt_fast_solver_time:                   0.
% 2.66/1.00  prop_fast_solver_time:                  0.
% 2.66/1.00  prop_unsat_core_time:                   0.
% 2.66/1.00  
% 2.66/1.00  ------ QBF
% 2.66/1.00  
% 2.66/1.00  qbf_q_res:                              0
% 2.66/1.00  qbf_num_tautologies:                    0
% 2.66/1.00  qbf_prep_cycles:                        0
% 2.66/1.00  
% 2.66/1.00  ------ BMC1
% 2.66/1.00  
% 2.66/1.00  bmc1_current_bound:                     -1
% 2.66/1.00  bmc1_last_solved_bound:                 -1
% 2.66/1.00  bmc1_unsat_core_size:                   -1
% 2.66/1.00  bmc1_unsat_core_parents_size:           -1
% 2.66/1.00  bmc1_merge_next_fun:                    0
% 2.66/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.66/1.00  
% 2.66/1.00  ------ Instantiation
% 2.66/1.00  
% 2.66/1.00  inst_num_of_clauses:                    341
% 2.66/1.00  inst_num_in_passive:                    89
% 2.66/1.00  inst_num_in_active:                     227
% 2.66/1.00  inst_num_in_unprocessed:                25
% 2.66/1.00  inst_num_of_loops:                      310
% 2.66/1.00  inst_num_of_learning_restarts:          0
% 2.66/1.00  inst_num_moves_active_passive:          79
% 2.66/1.00  inst_lit_activity:                      0
% 2.66/1.00  inst_lit_activity_moves:                0
% 2.66/1.00  inst_num_tautologies:                   0
% 2.66/1.00  inst_num_prop_implied:                  0
% 2.66/1.00  inst_num_existing_simplified:           0
% 2.66/1.00  inst_num_eq_res_simplified:             0
% 2.66/1.00  inst_num_child_elim:                    0
% 2.66/1.00  inst_num_of_dismatching_blockings:      71
% 2.66/1.00  inst_num_of_non_proper_insts:           334
% 2.66/1.00  inst_num_of_duplicates:                 0
% 2.66/1.00  inst_inst_num_from_inst_to_res:         0
% 2.66/1.00  inst_dismatching_checking_time:         0.
% 2.66/1.00  
% 2.66/1.00  ------ Resolution
% 2.66/1.00  
% 2.66/1.00  res_num_of_clauses:                     0
% 2.66/1.00  res_num_in_passive:                     0
% 2.66/1.00  res_num_in_active:                      0
% 2.66/1.00  res_num_of_loops:                       101
% 2.66/1.00  res_forward_subset_subsumed:            35
% 2.66/1.00  res_backward_subset_subsumed:           0
% 2.66/1.00  res_forward_subsumed:                   4
% 2.66/1.00  res_backward_subsumed:                  0
% 2.66/1.00  res_forward_subsumption_resolution:     0
% 2.66/1.00  res_backward_subsumption_resolution:    0
% 2.66/1.00  res_clause_to_clause_subsumption:       165
% 2.66/1.00  res_orphan_elimination:                 0
% 2.66/1.00  res_tautology_del:                      71
% 2.66/1.00  res_num_eq_res_simplified:              2
% 2.66/1.00  res_num_sel_changes:                    0
% 2.66/1.00  res_moves_from_active_to_pass:          0
% 2.66/1.00  
% 2.66/1.00  ------ Superposition
% 2.66/1.00  
% 2.66/1.00  sup_time_total:                         0.
% 2.66/1.00  sup_time_generating:                    0.
% 2.66/1.00  sup_time_sim_full:                      0.
% 2.66/1.00  sup_time_sim_immed:                     0.
% 2.66/1.00  
% 2.66/1.00  sup_num_of_clauses:                     36
% 2.66/1.00  sup_num_in_active:                      28
% 2.66/1.00  sup_num_in_passive:                     8
% 2.66/1.00  sup_num_of_loops:                       61
% 2.66/1.00  sup_fw_superposition:                   18
% 2.66/1.00  sup_bw_superposition:                   16
% 2.66/1.00  sup_immediate_simplified:               21
% 2.66/1.00  sup_given_eliminated:                   0
% 2.66/1.00  comparisons_done:                       0
% 2.66/1.00  comparisons_avoided:                    27
% 2.66/1.00  
% 2.66/1.00  ------ Simplifications
% 2.66/1.00  
% 2.66/1.00  
% 2.66/1.00  sim_fw_subset_subsumed:                 3
% 2.66/1.00  sim_bw_subset_subsumed:                 9
% 2.66/1.00  sim_fw_subsumed:                        2
% 2.66/1.00  sim_bw_subsumed:                        0
% 2.66/1.00  sim_fw_subsumption_res:                 1
% 2.66/1.00  sim_bw_subsumption_res:                 0
% 2.66/1.00  sim_tautology_del:                      3
% 2.66/1.00  sim_eq_tautology_del:                   11
% 2.66/1.00  sim_eq_res_simp:                        7
% 2.66/1.00  sim_fw_demodulated:                     5
% 2.66/1.00  sim_bw_demodulated:                     27
% 2.66/1.00  sim_light_normalised:                   17
% 2.66/1.00  sim_joinable_taut:                      0
% 2.66/1.00  sim_joinable_simp:                      0
% 2.66/1.00  sim_ac_normalised:                      0
% 2.66/1.00  sim_smt_subsumption:                    0
% 2.66/1.00  
%------------------------------------------------------------------------------
