%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:08:40 EST 2020

% Result     : Theorem 2.80s
% Output     : CNFRefutation 2.80s
% Verified   : 
% Statistics : Number of formulae       :  202 (130667 expanded)
%              Number of clauses        :  141 (37366 expanded)
%              Number of leaves         :   17 (30187 expanded)
%              Depth                    :   55
%              Number of atoms          :  807 (1034506 expanded)
%              Number of equality atoms :  480 (349098 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
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

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f11])).

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
    inference(flattening,[],[f21])).

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
    inference(nnf_transformation,[],[f22])).

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
     => ( k1_funct_1(X2,sK5) != k1_funct_1(X3,sK5)
        & r2_hidden(sK5,k1_relset_1(X0,X1,X2)) ) ) ),
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

fof(f37,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f33,f36,f35,f34])).

fof(f60,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f8,axiom,(
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

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f8])).

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
    inference(flattening,[],[f17])).

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
    inference(nnf_transformation,[],[f18])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f61,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f37])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f9,axiom,(
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

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f9])).

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
    inference(flattening,[],[f19])).

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
    inference(nnf_transformation,[],[f20])).

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
     => ( k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1))
        & r2_hidden(sK0(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_partfun1(X0,X1)
      | r2_hidden(sK0(X0,X1),k1_relat_1(X0))
      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f58,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f37])).

fof(f63,plain,(
    ! [X5] :
      ( k1_funct_1(sK3,X5) = k1_funct_1(sK4,X5)
      | ~ r2_hidden(X5,k1_relset_1(sK1,sK2,sK3))
      | r1_partfun1(sK3,sK4) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f57,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f59,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f37])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f64,plain,
    ( r2_hidden(sK5,k1_relset_1(sK1,sK2,sK3))
    | ~ r1_partfun1(sK3,sK4) ),
    inference(cnf_transformation,[],[f37])).

fof(f54,plain,(
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

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_partfun1(X0,X1)
      | k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1))
      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f65,plain,
    ( k1_funct_1(sK3,sK5) != k1_funct_1(sK4,sK5)
    | ~ r1_partfun1(sK3,sK4) ),
    inference(cnf_transformation,[],[f37])).

fof(f62,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f37])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f72,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f49])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f23])).

fof(f40,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f70,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f52])).

cnf(c_24,negated_conjecture,
    ( v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_488,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_23])).

cnf(c_489,plain,
    ( ~ v1_funct_2(sK4,X0,X1)
    | k1_relset_1(X0,X1,sK4) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_488])).

cnf(c_1089,plain,
    ( k1_relset_1(X0,X1,sK4) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sK2 != X1
    | sK1 != X0
    | sK4 != sK4
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_489])).

cnf(c_1090,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_1089])).

cnf(c_1693,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(equality_resolution_simp,[status(thm)],[c_1090])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_524,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_23])).

cnf(c_525,plain,
    ( k1_relset_1(X0,X1,sK4) = k1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(unflattening,[status(thm)],[c_524])).

cnf(c_1920,plain,
    ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
    inference(equality_resolution,[status(thm)],[c_525])).

cnf(c_2808,plain,
    ( k1_relat_1(sK4) = sK1
    | sK2 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1693,c_1920])).

cnf(c_17,plain,
    ( r2_hidden(sK0(X0,X1),k1_relat_1(X0))
    | r1_partfun1(X0,X1)
    | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1639,plain,
    ( r2_hidden(sK0(X0,X1),k1_relat_1(X0)) = iProver_top
    | r1_partfun1(X0,X1) = iProver_top
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_584,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_26])).

cnf(c_585,plain,
    ( k1_relset_1(X0,X1,sK3) = k1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(unflattening,[status(thm)],[c_584])).

cnf(c_1968,plain,
    ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
    inference(equality_resolution,[status(thm)],[c_585])).

cnf(c_21,negated_conjecture,
    ( ~ r2_hidden(X0,k1_relset_1(sK1,sK2,sK3))
    | r1_partfun1(sK3,sK4)
    | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1635,plain,
    ( k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0)
    | r2_hidden(X0,k1_relset_1(sK1,sK2,sK3)) != iProver_top
    | r1_partfun1(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2270,plain,
    ( k1_funct_1(sK4,X0) = k1_funct_1(sK3,X0)
    | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | r1_partfun1(sK3,sK4) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1968,c_1635])).

cnf(c_2964,plain,
    ( k1_funct_1(sK3,sK0(sK3,X0)) = k1_funct_1(sK4,sK0(sK3,X0))
    | r1_partfun1(sK3,X0) = iProver_top
    | r1_partfun1(sK3,sK4) = iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1639,c_2270])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_28,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_458,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_26])).

cnf(c_459,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_458])).

cnf(c_1631,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(X0)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_459])).

cnf(c_2328,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1631])).

cnf(c_7,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_2336,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2337,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2336])).

cnf(c_3370,plain,
    ( v1_relat_1(X0) != iProver_top
    | k1_funct_1(sK3,sK0(sK3,X0)) = k1_funct_1(sK4,sK0(sK3,X0))
    | r1_partfun1(sK3,X0) = iProver_top
    | r1_partfun1(sK3,sK4) = iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2964,c_28,c_2328,c_2337])).

cnf(c_3371,plain,
    ( k1_funct_1(sK3,sK0(sK3,X0)) = k1_funct_1(sK4,sK0(sK3,X0))
    | r1_partfun1(sK3,X0) = iProver_top
    | r1_partfun1(sK3,sK4) = iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3370])).

cnf(c_3383,plain,
    ( k1_funct_1(sK3,sK0(sK3,sK4)) = k1_funct_1(sK4,sK0(sK3,sK4))
    | sK2 = k1_xboole_0
    | r1_partfun1(sK3,sK4) = iProver_top
    | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2808,c_3371])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_30,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_443,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_23])).

cnf(c_444,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_443])).

cnf(c_1632,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(X0)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_444])).

cnf(c_2334,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1632])).

cnf(c_8,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_6,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_292,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_8,c_6])).

cnf(c_533,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_292,c_26])).

cnf(c_534,plain,
    ( r1_tarski(k1_relat_1(sK3),X0)
    | ~ v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(unflattening,[status(thm)],[c_533])).

cnf(c_1629,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | r1_tarski(k1_relat_1(sK3),X0) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_534])).

cnf(c_535,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | r1_tarski(k1_relat_1(sK3),X0) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_534])).

cnf(c_2564,plain,
    ( r1_tarski(k1_relat_1(sK3),X0) = iProver_top
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1629,c_535,c_2328,c_2337])).

cnf(c_2565,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | r1_tarski(k1_relat_1(sK3),X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_2564])).

cnf(c_2572,plain,
    ( r1_tarski(k1_relat_1(sK3),sK1) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2565])).

cnf(c_3803,plain,
    ( r1_partfun1(sK3,sK4) = iProver_top
    | sK2 = k1_xboole_0
    | k1_funct_1(sK3,sK0(sK3,sK4)) = k1_funct_1(sK4,sK0(sK3,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3383,c_30,c_2334,c_2337,c_2572])).

cnf(c_3804,plain,
    ( k1_funct_1(sK3,sK0(sK3,sK4)) = k1_funct_1(sK4,sK0(sK3,sK4))
    | sK2 = k1_xboole_0
    | r1_partfun1(sK3,sK4) = iProver_top ),
    inference(renaming,[status(thm)],[c_3803])).

cnf(c_20,negated_conjecture,
    ( r2_hidden(sK5,k1_relset_1(sK1,sK2,sK3))
    | ~ r1_partfun1(sK3,sK4) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1636,plain,
    ( r2_hidden(sK5,k1_relset_1(sK1,sK2,sK3)) = iProver_top
    | r1_partfun1(sK3,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2271,plain,
    ( r2_hidden(sK5,k1_relat_1(sK3)) = iProver_top
    | r1_partfun1(sK3,sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1968,c_1636])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r1_partfun1(X1,X2)
    | ~ r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = k1_funct_1(X1,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1638,plain,
    ( k1_funct_1(X0,X1) = k1_funct_1(X2,X1)
    | r2_hidden(X1,k1_relat_1(X2)) != iProver_top
    | r1_partfun1(X2,X0) != iProver_top
    | r1_tarski(k1_relat_1(X2),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2811,plain,
    ( k1_funct_1(X0,X1) = k1_funct_1(sK4,X1)
    | sK2 = k1_xboole_0
    | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
    | r1_partfun1(X0,sK4) != iProver_top
    | r1_tarski(k1_relat_1(X0),sK1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2808,c_1638])).

cnf(c_3563,plain,
    ( v1_relat_1(X0) != iProver_top
    | k1_funct_1(X0,X1) = k1_funct_1(sK4,X1)
    | sK2 = k1_xboole_0
    | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
    | r1_partfun1(X0,sK4) != iProver_top
    | r1_tarski(k1_relat_1(X0),sK1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2811,c_30,c_2334,c_2337])).

cnf(c_3564,plain,
    ( k1_funct_1(X0,X1) = k1_funct_1(sK4,X1)
    | sK2 = k1_xboole_0
    | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
    | r1_partfun1(X0,sK4) != iProver_top
    | r1_tarski(k1_relat_1(X0),sK1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3563])).

cnf(c_3577,plain,
    ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
    | sK2 = k1_xboole_0
    | r1_partfun1(sK3,sK4) != iProver_top
    | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2271,c_3564])).

cnf(c_3665,plain,
    ( r1_partfun1(sK3,sK4) != iProver_top
    | sK2 = k1_xboole_0
    | k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3577,c_28,c_2328,c_2337,c_2572])).

cnf(c_3666,plain,
    ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
    | sK2 = k1_xboole_0
    | r1_partfun1(sK3,sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_3665])).

cnf(c_3810,plain,
    ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
    | k1_funct_1(sK3,sK0(sK3,sK4)) = k1_funct_1(sK4,sK0(sK3,sK4))
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3804,c_3666])).

cnf(c_16,plain,
    ( r1_partfun1(X0,X1)
    | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK0(X0,X1)) != k1_funct_1(X0,sK0(X0,X1)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1640,plain,
    ( k1_funct_1(X0,sK0(X1,X0)) != k1_funct_1(X1,sK0(X1,X0))
    | r1_partfun1(X1,X0) = iProver_top
    | r1_tarski(k1_relat_1(X1),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3880,plain,
    ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
    | sK2 = k1_xboole_0
    | r1_partfun1(sK3,sK4) = iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3810,c_1640])).

cnf(c_3883,plain,
    ( sK2 = k1_xboole_0
    | k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3880,c_28,c_30,c_2328,c_2334,c_2337,c_2572,c_3577])).

cnf(c_3884,plain,
    ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
    | sK2 = k1_xboole_0
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3883])).

cnf(c_3890,plain,
    ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
    | sK2 = k1_xboole_0
    | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2808,c_3884])).

cnf(c_3918,plain,
    ( sK2 = k1_xboole_0
    | k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3890,c_2572])).

cnf(c_3919,plain,
    ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
    | sK2 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_3918])).

cnf(c_19,negated_conjecture,
    ( ~ r1_partfun1(sK3,sK4)
    | k1_funct_1(sK3,sK5) != k1_funct_1(sK4,sK5) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1637,plain,
    ( k1_funct_1(sK3,sK5) != k1_funct_1(sK4,sK5)
    | r1_partfun1(sK3,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3922,plain,
    ( sK2 = k1_xboole_0
    | r1_partfun1(sK3,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3919,c_1637])).

cnf(c_3927,plain,
    ( k1_funct_1(sK3,sK0(sK3,sK4)) = k1_funct_1(sK4,sK0(sK3,sK4))
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3804,c_3922])).

cnf(c_3978,plain,
    ( sK2 = k1_xboole_0
    | r1_partfun1(sK3,sK4) = iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3927,c_1640])).

cnf(c_3981,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3978,c_28,c_30,c_2328,c_2334,c_2337,c_3922])).

cnf(c_3987,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2808,c_3981])).

cnf(c_4023,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3987,c_2572])).

cnf(c_4039,plain,
    ( k1_relset_1(sK1,k1_xboole_0,sK4) = k1_relat_1(sK4) ),
    inference(demodulation,[status(thm)],[c_4023,c_1920])).

cnf(c_22,negated_conjecture,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_4045,plain,
    ( sK1 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4023,c_22])).

cnf(c_4046,plain,
    ( sK1 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_4045])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_663,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_23])).

cnf(c_664,plain,
    ( ~ v1_funct_2(sK4,k1_xboole_0,X0)
    | k1_relset_1(k1_xboole_0,X0,sK4) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(unflattening,[status(thm)],[c_663])).

cnf(c_1145,plain,
    ( k1_relset_1(k1_xboole_0,X0,sK4) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sK2 != X0
    | sK1 != k1_xboole_0
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_664])).

cnf(c_1146,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sK1 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_1145])).

cnf(c_4042,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | sK1 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4023,c_1146])).

cnf(c_4059,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4042,c_4046])).

cnf(c_4060,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_4059])).

cnf(c_4070,plain,
    ( k1_relat_1(sK4) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4039,c_4046,c_4060])).

cnf(c_4192,plain,
    ( k1_funct_1(sK3,sK0(sK3,sK4)) = k1_funct_1(sK4,sK0(sK3,sK4))
    | r1_partfun1(sK3,sK4) = iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4070,c_3371])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_82,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_87,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_537,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | r1_tarski(k1_relat_1(sK3),k1_xboole_0) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_535])).

cnf(c_1314,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_1903,plain,
    ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK1,sK2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_1314])).

cnf(c_1904,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k2_zfmisc_1(sK1,sK2)
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_1903])).

cnf(c_1311,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1938,plain,
    ( sK2 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_1311])).

cnf(c_1939,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1938])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_627,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sK4 != X0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_23])).

cnf(c_628,plain,
    ( ~ v1_funct_2(sK4,X0,k1_xboole_0)
    | k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | k1_xboole_0 = X0
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_627])).

cnf(c_1114,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sK2 != k1_xboole_0
    | sK1 != X0
    | sK4 != sK4
    | sK4 = k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_628])).

cnf(c_1115,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sK2 != k1_xboole_0
    | sK4 = k1_xboole_0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_1114])).

cnf(c_2016,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1115,c_22,c_82,c_87,c_1939])).

cnf(c_1316,plain,
    ( X0 != X1
    | X2 != X3
    | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
    theory(equality)).

cnf(c_2141,plain,
    ( X0 != sK2
    | X1 != sK1
    | k2_zfmisc_1(X1,X0) = k2_zfmisc_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1316])).

cnf(c_2142,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k2_zfmisc_1(sK1,sK2)
    | k1_xboole_0 != sK2
    | k1_xboole_0 != sK1 ),
    inference(instantiation,[status(thm)],[c_2141])).

cnf(c_5582,plain,
    ( r1_partfun1(sK3,sK4) = iProver_top
    | k1_funct_1(sK3,sK0(sK3,sK4)) = k1_funct_1(sK4,sK0(sK3,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4192,c_30,c_82,c_87,c_537,c_1904,c_1939,c_2016,c_2142,c_2328,c_2334,c_2337,c_2572,c_3987])).

cnf(c_5583,plain,
    ( k1_funct_1(sK3,sK0(sK3,sK4)) = k1_funct_1(sK4,sK0(sK3,sK4))
    | r1_partfun1(sK3,sK4) = iProver_top ),
    inference(renaming,[status(thm)],[c_5582])).

cnf(c_4193,plain,
    ( k1_funct_1(X0,X1) = k1_funct_1(sK4,X1)
    | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
    | r1_partfun1(X0,sK4) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4070,c_1638])).

cnf(c_4265,plain,
    ( v1_relat_1(X0) != iProver_top
    | k1_funct_1(X0,X1) = k1_funct_1(sK4,X1)
    | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
    | r1_partfun1(X0,sK4) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4193,c_30,c_2334,c_2337])).

cnf(c_4266,plain,
    ( k1_funct_1(X0,X1) = k1_funct_1(sK4,X1)
    | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
    | r1_partfun1(X0,sK4) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4265])).

cnf(c_4278,plain,
    ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
    | r1_partfun1(sK3,sK4) != iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2271,c_4266])).

cnf(c_4402,plain,
    ( r1_partfun1(sK3,sK4) != iProver_top
    | k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4278,c_28,c_82,c_87,c_537,c_1904,c_1939,c_2016,c_2142,c_2328,c_2337,c_2572,c_3987])).

cnf(c_4403,plain,
    ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
    | r1_partfun1(sK3,sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_4402])).

cnf(c_5589,plain,
    ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
    | k1_funct_1(sK3,sK0(sK3,sK4)) = k1_funct_1(sK4,sK0(sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_5583,c_4403])).

cnf(c_6281,plain,
    ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
    | r1_partfun1(sK3,sK4) = iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5589,c_1640])).

cnf(c_4135,plain,
    ( r1_tarski(k1_relat_1(sK3),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4046,c_2572])).

cnf(c_1642,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1644,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2159,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1642,c_1644])).

cnf(c_4350,plain,
    ( k1_relat_1(sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4135,c_2159])).

cnf(c_6282,plain,
    ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
    | r1_partfun1(sK3,sK4) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6281,c_4070,c_4350])).

cnf(c_81,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_83,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_81])).

cnf(c_6290,plain,
    ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6282,c_28,c_30,c_83,c_2328,c_2334,c_2337,c_4403])).

cnf(c_6293,plain,
    ( k1_funct_1(sK3,sK5) != k1_funct_1(sK3,sK5)
    | r1_partfun1(sK3,sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6290,c_1637])).

cnf(c_6352,plain,
    ( r1_partfun1(sK3,sK4) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_6293])).

cnf(c_6355,plain,
    ( k1_funct_1(sK3,sK0(sK3,sK4)) = k1_funct_1(sK4,sK0(sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_5583,c_6352])).

cnf(c_6366,plain,
    ( r1_partfun1(sK3,sK4) = iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_6355,c_1640])).

cnf(c_6367,plain,
    ( r1_partfun1(sK3,sK4) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6366,c_4070,c_4350])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6367,c_6352,c_2337,c_2334,c_2328,c_83,c_30,c_28])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:28:39 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.80/0.94  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.80/0.94  
% 2.80/0.94  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.80/0.94  
% 2.80/0.94  ------  iProver source info
% 2.80/0.94  
% 2.80/0.94  git: date: 2020-06-30 10:37:57 +0100
% 2.80/0.94  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.80/0.94  git: non_committed_changes: false
% 2.80/0.94  git: last_make_outside_of_git: false
% 2.80/0.94  
% 2.80/0.94  ------ 
% 2.80/0.94  
% 2.80/0.94  ------ Input Options
% 2.80/0.94  
% 2.80/0.94  --out_options                           all
% 2.80/0.94  --tptp_safe_out                         true
% 2.80/0.94  --problem_path                          ""
% 2.80/0.94  --include_path                          ""
% 2.80/0.94  --clausifier                            res/vclausify_rel
% 2.80/0.94  --clausifier_options                    --mode clausify
% 2.80/0.94  --stdin                                 false
% 2.80/0.94  --stats_out                             all
% 2.80/0.94  
% 2.80/0.94  ------ General Options
% 2.80/0.94  
% 2.80/0.94  --fof                                   false
% 2.80/0.94  --time_out_real                         305.
% 2.80/0.94  --time_out_virtual                      -1.
% 2.80/0.94  --symbol_type_check                     false
% 2.80/0.94  --clausify_out                          false
% 2.80/0.94  --sig_cnt_out                           false
% 2.80/0.94  --trig_cnt_out                          false
% 2.80/0.94  --trig_cnt_out_tolerance                1.
% 2.80/0.94  --trig_cnt_out_sk_spl                   false
% 2.80/0.94  --abstr_cl_out                          false
% 2.80/0.94  
% 2.80/0.94  ------ Global Options
% 2.80/0.94  
% 2.80/0.94  --schedule                              default
% 2.80/0.94  --add_important_lit                     false
% 2.80/0.94  --prop_solver_per_cl                    1000
% 2.80/0.94  --min_unsat_core                        false
% 2.80/0.94  --soft_assumptions                      false
% 2.80/0.94  --soft_lemma_size                       3
% 2.80/0.94  --prop_impl_unit_size                   0
% 2.80/0.94  --prop_impl_unit                        []
% 2.80/0.94  --share_sel_clauses                     true
% 2.80/0.94  --reset_solvers                         false
% 2.80/0.94  --bc_imp_inh                            [conj_cone]
% 2.80/0.94  --conj_cone_tolerance                   3.
% 2.80/0.94  --extra_neg_conj                        none
% 2.80/0.94  --large_theory_mode                     true
% 2.80/0.94  --prolific_symb_bound                   200
% 2.80/0.94  --lt_threshold                          2000
% 2.80/0.94  --clause_weak_htbl                      true
% 2.80/0.94  --gc_record_bc_elim                     false
% 2.80/0.94  
% 2.80/0.94  ------ Preprocessing Options
% 2.80/0.94  
% 2.80/0.94  --preprocessing_flag                    true
% 2.80/0.94  --time_out_prep_mult                    0.1
% 2.80/0.94  --splitting_mode                        input
% 2.80/0.94  --splitting_grd                         true
% 2.80/0.94  --splitting_cvd                         false
% 2.80/0.94  --splitting_cvd_svl                     false
% 2.80/0.94  --splitting_nvd                         32
% 2.80/0.94  --sub_typing                            true
% 2.80/0.94  --prep_gs_sim                           true
% 2.80/0.94  --prep_unflatten                        true
% 2.80/0.94  --prep_res_sim                          true
% 2.80/0.94  --prep_upred                            true
% 2.80/0.94  --prep_sem_filter                       exhaustive
% 2.80/0.94  --prep_sem_filter_out                   false
% 2.80/0.94  --pred_elim                             true
% 2.80/0.94  --res_sim_input                         true
% 2.80/0.94  --eq_ax_congr_red                       true
% 2.80/0.94  --pure_diseq_elim                       true
% 2.80/0.94  --brand_transform                       false
% 2.80/0.94  --non_eq_to_eq                          false
% 2.80/0.94  --prep_def_merge                        true
% 2.80/0.94  --prep_def_merge_prop_impl              false
% 2.80/0.94  --prep_def_merge_mbd                    true
% 2.80/0.94  --prep_def_merge_tr_red                 false
% 2.80/0.94  --prep_def_merge_tr_cl                  false
% 2.80/0.94  --smt_preprocessing                     true
% 2.80/0.94  --smt_ac_axioms                         fast
% 2.80/0.94  --preprocessed_out                      false
% 2.80/0.94  --preprocessed_stats                    false
% 2.80/0.94  
% 2.80/0.94  ------ Abstraction refinement Options
% 2.80/0.94  
% 2.80/0.94  --abstr_ref                             []
% 2.80/0.94  --abstr_ref_prep                        false
% 2.80/0.94  --abstr_ref_until_sat                   false
% 2.80/0.94  --abstr_ref_sig_restrict                funpre
% 2.80/0.94  --abstr_ref_af_restrict_to_split_sk     false
% 2.80/0.94  --abstr_ref_under                       []
% 2.80/0.94  
% 2.80/0.94  ------ SAT Options
% 2.80/0.94  
% 2.80/0.94  --sat_mode                              false
% 2.80/0.94  --sat_fm_restart_options                ""
% 2.80/0.94  --sat_gr_def                            false
% 2.80/0.94  --sat_epr_types                         true
% 2.80/0.94  --sat_non_cyclic_types                  false
% 2.80/0.94  --sat_finite_models                     false
% 2.80/0.94  --sat_fm_lemmas                         false
% 2.80/0.94  --sat_fm_prep                           false
% 2.80/0.94  --sat_fm_uc_incr                        true
% 2.80/0.94  --sat_out_model                         small
% 2.80/0.94  --sat_out_clauses                       false
% 2.80/0.94  
% 2.80/0.94  ------ QBF Options
% 2.80/0.94  
% 2.80/0.94  --qbf_mode                              false
% 2.80/0.94  --qbf_elim_univ                         false
% 2.80/0.94  --qbf_dom_inst                          none
% 2.80/0.94  --qbf_dom_pre_inst                      false
% 2.80/0.94  --qbf_sk_in                             false
% 2.80/0.94  --qbf_pred_elim                         true
% 2.80/0.94  --qbf_split                             512
% 2.80/0.94  
% 2.80/0.94  ------ BMC1 Options
% 2.80/0.94  
% 2.80/0.94  --bmc1_incremental                      false
% 2.80/0.94  --bmc1_axioms                           reachable_all
% 2.80/0.94  --bmc1_min_bound                        0
% 2.80/0.94  --bmc1_max_bound                        -1
% 2.80/0.94  --bmc1_max_bound_default                -1
% 2.80/0.94  --bmc1_symbol_reachability              true
% 2.80/0.94  --bmc1_property_lemmas                  false
% 2.80/0.94  --bmc1_k_induction                      false
% 2.80/0.94  --bmc1_non_equiv_states                 false
% 2.80/0.94  --bmc1_deadlock                         false
% 2.80/0.94  --bmc1_ucm                              false
% 2.80/0.94  --bmc1_add_unsat_core                   none
% 2.80/0.94  --bmc1_unsat_core_children              false
% 2.80/0.94  --bmc1_unsat_core_extrapolate_axioms    false
% 2.80/0.94  --bmc1_out_stat                         full
% 2.80/0.94  --bmc1_ground_init                      false
% 2.80/0.94  --bmc1_pre_inst_next_state              false
% 2.80/0.94  --bmc1_pre_inst_state                   false
% 2.80/0.94  --bmc1_pre_inst_reach_state             false
% 2.80/0.94  --bmc1_out_unsat_core                   false
% 2.80/0.94  --bmc1_aig_witness_out                  false
% 2.80/0.94  --bmc1_verbose                          false
% 2.80/0.94  --bmc1_dump_clauses_tptp                false
% 2.80/0.94  --bmc1_dump_unsat_core_tptp             false
% 2.80/0.94  --bmc1_dump_file                        -
% 2.80/0.94  --bmc1_ucm_expand_uc_limit              128
% 2.80/0.94  --bmc1_ucm_n_expand_iterations          6
% 2.80/0.94  --bmc1_ucm_extend_mode                  1
% 2.80/0.94  --bmc1_ucm_init_mode                    2
% 2.80/0.94  --bmc1_ucm_cone_mode                    none
% 2.80/0.94  --bmc1_ucm_reduced_relation_type        0
% 2.80/0.94  --bmc1_ucm_relax_model                  4
% 2.80/0.94  --bmc1_ucm_full_tr_after_sat            true
% 2.80/0.94  --bmc1_ucm_expand_neg_assumptions       false
% 2.80/0.94  --bmc1_ucm_layered_model                none
% 2.80/0.94  --bmc1_ucm_max_lemma_size               10
% 2.80/0.94  
% 2.80/0.94  ------ AIG Options
% 2.80/0.94  
% 2.80/0.94  --aig_mode                              false
% 2.80/0.94  
% 2.80/0.94  ------ Instantiation Options
% 2.80/0.94  
% 2.80/0.94  --instantiation_flag                    true
% 2.80/0.94  --inst_sos_flag                         false
% 2.80/0.94  --inst_sos_phase                        true
% 2.80/0.94  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.80/0.94  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.80/0.94  --inst_lit_sel_side                     num_symb
% 2.80/0.94  --inst_solver_per_active                1400
% 2.80/0.94  --inst_solver_calls_frac                1.
% 2.80/0.94  --inst_passive_queue_type               priority_queues
% 2.80/0.94  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.80/0.94  --inst_passive_queues_freq              [25;2]
% 2.80/0.94  --inst_dismatching                      true
% 2.80/0.94  --inst_eager_unprocessed_to_passive     true
% 2.80/0.94  --inst_prop_sim_given                   true
% 2.80/0.94  --inst_prop_sim_new                     false
% 2.80/0.94  --inst_subs_new                         false
% 2.80/0.94  --inst_eq_res_simp                      false
% 2.80/0.94  --inst_subs_given                       false
% 2.80/0.94  --inst_orphan_elimination               true
% 2.80/0.94  --inst_learning_loop_flag               true
% 2.80/0.94  --inst_learning_start                   3000
% 2.80/0.94  --inst_learning_factor                  2
% 2.80/0.94  --inst_start_prop_sim_after_learn       3
% 2.80/0.94  --inst_sel_renew                        solver
% 2.80/0.94  --inst_lit_activity_flag                true
% 2.80/0.94  --inst_restr_to_given                   false
% 2.80/0.94  --inst_activity_threshold               500
% 2.80/0.94  --inst_out_proof                        true
% 2.80/0.94  
% 2.80/0.94  ------ Resolution Options
% 2.80/0.94  
% 2.80/0.94  --resolution_flag                       true
% 2.80/0.94  --res_lit_sel                           adaptive
% 2.80/0.94  --res_lit_sel_side                      none
% 2.80/0.94  --res_ordering                          kbo
% 2.80/0.94  --res_to_prop_solver                    active
% 2.80/0.94  --res_prop_simpl_new                    false
% 2.80/0.94  --res_prop_simpl_given                  true
% 2.80/0.94  --res_passive_queue_type                priority_queues
% 2.80/0.94  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.80/0.94  --res_passive_queues_freq               [15;5]
% 2.80/0.94  --res_forward_subs                      full
% 2.80/0.94  --res_backward_subs                     full
% 2.80/0.94  --res_forward_subs_resolution           true
% 2.80/0.94  --res_backward_subs_resolution          true
% 2.80/0.94  --res_orphan_elimination                true
% 2.80/0.94  --res_time_limit                        2.
% 2.80/0.94  --res_out_proof                         true
% 2.80/0.94  
% 2.80/0.94  ------ Superposition Options
% 2.80/0.94  
% 2.80/0.94  --superposition_flag                    true
% 2.80/0.94  --sup_passive_queue_type                priority_queues
% 2.80/0.94  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.80/0.94  --sup_passive_queues_freq               [8;1;4]
% 2.80/0.94  --demod_completeness_check              fast
% 2.80/0.94  --demod_use_ground                      true
% 2.80/0.94  --sup_to_prop_solver                    passive
% 2.80/0.94  --sup_prop_simpl_new                    true
% 2.80/0.94  --sup_prop_simpl_given                  true
% 2.80/0.94  --sup_fun_splitting                     false
% 2.80/0.94  --sup_smt_interval                      50000
% 2.80/0.94  
% 2.80/0.94  ------ Superposition Simplification Setup
% 2.80/0.94  
% 2.80/0.94  --sup_indices_passive                   []
% 2.80/0.94  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.80/0.94  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.80/0.94  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.80/0.94  --sup_full_triv                         [TrivRules;PropSubs]
% 2.80/0.94  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.80/0.94  --sup_full_bw                           [BwDemod]
% 2.80/0.94  --sup_immed_triv                        [TrivRules]
% 2.80/0.94  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.80/0.94  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.80/0.94  --sup_immed_bw_main                     []
% 2.80/0.94  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.80/0.94  --sup_input_triv                        [Unflattening;TrivRules]
% 2.80/0.94  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.80/0.94  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.80/0.94  
% 2.80/0.94  ------ Combination Options
% 2.80/0.94  
% 2.80/0.94  --comb_res_mult                         3
% 2.80/0.94  --comb_sup_mult                         2
% 2.80/0.94  --comb_inst_mult                        10
% 2.80/0.94  
% 2.80/0.94  ------ Debug Options
% 2.80/0.94  
% 2.80/0.94  --dbg_backtrace                         false
% 2.80/0.94  --dbg_dump_prop_clauses                 false
% 2.80/0.94  --dbg_dump_prop_clauses_file            -
% 2.80/0.94  --dbg_out_stat                          false
% 2.80/0.94  ------ Parsing...
% 2.80/0.94  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.80/0.94  
% 2.80/0.94  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 2.80/0.94  
% 2.80/0.94  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.80/0.94  
% 2.80/0.94  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.80/0.94  ------ Proving...
% 2.80/0.94  ------ Problem Properties 
% 2.80/0.94  
% 2.80/0.94  
% 2.80/0.94  clauses                                 29
% 2.80/0.94  conjectures                             6
% 2.80/0.94  EPR                                     6
% 2.80/0.94  Horn                                    21
% 2.80/0.94  unary                                   5
% 2.80/0.94  binary                                  5
% 2.80/0.94  lits                                    96
% 2.80/0.94  lits eq                                 56
% 2.80/0.94  fd_pure                                 0
% 2.80/0.94  fd_pseudo                               0
% 2.80/0.94  fd_cond                                 0
% 2.80/0.94  fd_pseudo_cond                          1
% 2.80/0.94  AC symbols                              0
% 2.80/0.94  
% 2.80/0.94  ------ Schedule dynamic 5 is on 
% 2.80/0.94  
% 2.80/0.94  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.80/0.94  
% 2.80/0.94  
% 2.80/0.94  ------ 
% 2.80/0.94  Current options:
% 2.80/0.94  ------ 
% 2.80/0.94  
% 2.80/0.94  ------ Input Options
% 2.80/0.94  
% 2.80/0.94  --out_options                           all
% 2.80/0.94  --tptp_safe_out                         true
% 2.80/0.94  --problem_path                          ""
% 2.80/0.94  --include_path                          ""
% 2.80/0.94  --clausifier                            res/vclausify_rel
% 2.80/0.94  --clausifier_options                    --mode clausify
% 2.80/0.94  --stdin                                 false
% 2.80/0.94  --stats_out                             all
% 2.80/0.94  
% 2.80/0.94  ------ General Options
% 2.80/0.94  
% 2.80/0.94  --fof                                   false
% 2.80/0.94  --time_out_real                         305.
% 2.80/0.94  --time_out_virtual                      -1.
% 2.80/0.94  --symbol_type_check                     false
% 2.80/0.94  --clausify_out                          false
% 2.80/0.94  --sig_cnt_out                           false
% 2.80/0.94  --trig_cnt_out                          false
% 2.80/0.94  --trig_cnt_out_tolerance                1.
% 2.80/0.94  --trig_cnt_out_sk_spl                   false
% 2.80/0.94  --abstr_cl_out                          false
% 2.80/0.94  
% 2.80/0.94  ------ Global Options
% 2.80/0.94  
% 2.80/0.94  --schedule                              default
% 2.80/0.94  --add_important_lit                     false
% 2.80/0.94  --prop_solver_per_cl                    1000
% 2.80/0.94  --min_unsat_core                        false
% 2.80/0.94  --soft_assumptions                      false
% 2.80/0.94  --soft_lemma_size                       3
% 2.80/0.94  --prop_impl_unit_size                   0
% 2.80/0.94  --prop_impl_unit                        []
% 2.80/0.94  --share_sel_clauses                     true
% 2.80/0.94  --reset_solvers                         false
% 2.80/0.94  --bc_imp_inh                            [conj_cone]
% 2.80/0.94  --conj_cone_tolerance                   3.
% 2.80/0.94  --extra_neg_conj                        none
% 2.80/0.94  --large_theory_mode                     true
% 2.80/0.94  --prolific_symb_bound                   200
% 2.80/0.94  --lt_threshold                          2000
% 2.80/0.94  --clause_weak_htbl                      true
% 2.80/0.94  --gc_record_bc_elim                     false
% 2.80/0.94  
% 2.80/0.94  ------ Preprocessing Options
% 2.80/0.94  
% 2.80/0.94  --preprocessing_flag                    true
% 2.80/0.94  --time_out_prep_mult                    0.1
% 2.80/0.94  --splitting_mode                        input
% 2.80/0.94  --splitting_grd                         true
% 2.80/0.94  --splitting_cvd                         false
% 2.80/0.94  --splitting_cvd_svl                     false
% 2.80/0.94  --splitting_nvd                         32
% 2.80/0.94  --sub_typing                            true
% 2.80/0.94  --prep_gs_sim                           true
% 2.80/0.94  --prep_unflatten                        true
% 2.80/0.94  --prep_res_sim                          true
% 2.80/0.94  --prep_upred                            true
% 2.80/0.94  --prep_sem_filter                       exhaustive
% 2.80/0.94  --prep_sem_filter_out                   false
% 2.80/0.94  --pred_elim                             true
% 2.80/0.94  --res_sim_input                         true
% 2.80/0.94  --eq_ax_congr_red                       true
% 2.80/0.94  --pure_diseq_elim                       true
% 2.80/0.94  --brand_transform                       false
% 2.80/0.94  --non_eq_to_eq                          false
% 2.80/0.94  --prep_def_merge                        true
% 2.80/0.94  --prep_def_merge_prop_impl              false
% 2.80/0.94  --prep_def_merge_mbd                    true
% 2.80/0.94  --prep_def_merge_tr_red                 false
% 2.80/0.94  --prep_def_merge_tr_cl                  false
% 2.80/0.94  --smt_preprocessing                     true
% 2.80/0.94  --smt_ac_axioms                         fast
% 2.80/0.94  --preprocessed_out                      false
% 2.80/0.94  --preprocessed_stats                    false
% 2.80/0.94  
% 2.80/0.94  ------ Abstraction refinement Options
% 2.80/0.94  
% 2.80/0.94  --abstr_ref                             []
% 2.80/0.94  --abstr_ref_prep                        false
% 2.80/0.94  --abstr_ref_until_sat                   false
% 2.80/0.94  --abstr_ref_sig_restrict                funpre
% 2.80/0.94  --abstr_ref_af_restrict_to_split_sk     false
% 2.80/0.94  --abstr_ref_under                       []
% 2.80/0.94  
% 2.80/0.94  ------ SAT Options
% 2.80/0.94  
% 2.80/0.94  --sat_mode                              false
% 2.80/0.94  --sat_fm_restart_options                ""
% 2.80/0.94  --sat_gr_def                            false
% 2.80/0.94  --sat_epr_types                         true
% 2.80/0.94  --sat_non_cyclic_types                  false
% 2.80/0.94  --sat_finite_models                     false
% 2.80/0.94  --sat_fm_lemmas                         false
% 2.80/0.94  --sat_fm_prep                           false
% 2.80/0.94  --sat_fm_uc_incr                        true
% 2.80/0.94  --sat_out_model                         small
% 2.80/0.94  --sat_out_clauses                       false
% 2.80/0.94  
% 2.80/0.94  ------ QBF Options
% 2.80/0.94  
% 2.80/0.94  --qbf_mode                              false
% 2.80/0.94  --qbf_elim_univ                         false
% 2.80/0.94  --qbf_dom_inst                          none
% 2.80/0.94  --qbf_dom_pre_inst                      false
% 2.80/0.94  --qbf_sk_in                             false
% 2.80/0.94  --qbf_pred_elim                         true
% 2.80/0.94  --qbf_split                             512
% 2.80/0.94  
% 2.80/0.94  ------ BMC1 Options
% 2.80/0.94  
% 2.80/0.94  --bmc1_incremental                      false
% 2.80/0.94  --bmc1_axioms                           reachable_all
% 2.80/0.94  --bmc1_min_bound                        0
% 2.80/0.94  --bmc1_max_bound                        -1
% 2.80/0.94  --bmc1_max_bound_default                -1
% 2.80/0.94  --bmc1_symbol_reachability              true
% 2.80/0.94  --bmc1_property_lemmas                  false
% 2.80/0.94  --bmc1_k_induction                      false
% 2.80/0.94  --bmc1_non_equiv_states                 false
% 2.80/0.94  --bmc1_deadlock                         false
% 2.80/0.94  --bmc1_ucm                              false
% 2.80/0.94  --bmc1_add_unsat_core                   none
% 2.80/0.94  --bmc1_unsat_core_children              false
% 2.80/0.94  --bmc1_unsat_core_extrapolate_axioms    false
% 2.80/0.94  --bmc1_out_stat                         full
% 2.80/0.94  --bmc1_ground_init                      false
% 2.80/0.94  --bmc1_pre_inst_next_state              false
% 2.80/0.94  --bmc1_pre_inst_state                   false
% 2.80/0.94  --bmc1_pre_inst_reach_state             false
% 2.80/0.94  --bmc1_out_unsat_core                   false
% 2.80/0.94  --bmc1_aig_witness_out                  false
% 2.80/0.94  --bmc1_verbose                          false
% 2.80/0.94  --bmc1_dump_clauses_tptp                false
% 2.80/0.94  --bmc1_dump_unsat_core_tptp             false
% 2.80/0.94  --bmc1_dump_file                        -
% 2.80/0.94  --bmc1_ucm_expand_uc_limit              128
% 2.80/0.94  --bmc1_ucm_n_expand_iterations          6
% 2.80/0.94  --bmc1_ucm_extend_mode                  1
% 2.80/0.94  --bmc1_ucm_init_mode                    2
% 2.80/0.95  --bmc1_ucm_cone_mode                    none
% 2.80/0.95  --bmc1_ucm_reduced_relation_type        0
% 2.80/0.95  --bmc1_ucm_relax_model                  4
% 2.80/0.95  --bmc1_ucm_full_tr_after_sat            true
% 2.80/0.95  --bmc1_ucm_expand_neg_assumptions       false
% 2.80/0.95  --bmc1_ucm_layered_model                none
% 2.80/0.95  --bmc1_ucm_max_lemma_size               10
% 2.80/0.95  
% 2.80/0.95  ------ AIG Options
% 2.80/0.95  
% 2.80/0.95  --aig_mode                              false
% 2.80/0.95  
% 2.80/0.95  ------ Instantiation Options
% 2.80/0.95  
% 2.80/0.95  --instantiation_flag                    true
% 2.80/0.95  --inst_sos_flag                         false
% 2.80/0.95  --inst_sos_phase                        true
% 2.80/0.95  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.80/0.95  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.80/0.95  --inst_lit_sel_side                     none
% 2.80/0.95  --inst_solver_per_active                1400
% 2.80/0.95  --inst_solver_calls_frac                1.
% 2.80/0.95  --inst_passive_queue_type               priority_queues
% 2.80/0.95  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.80/0.95  --inst_passive_queues_freq              [25;2]
% 2.80/0.95  --inst_dismatching                      true
% 2.80/0.95  --inst_eager_unprocessed_to_passive     true
% 2.80/0.95  --inst_prop_sim_given                   true
% 2.80/0.95  --inst_prop_sim_new                     false
% 2.80/0.95  --inst_subs_new                         false
% 2.80/0.95  --inst_eq_res_simp                      false
% 2.80/0.95  --inst_subs_given                       false
% 2.80/0.95  --inst_orphan_elimination               true
% 2.80/0.95  --inst_learning_loop_flag               true
% 2.80/0.95  --inst_learning_start                   3000
% 2.80/0.95  --inst_learning_factor                  2
% 2.80/0.95  --inst_start_prop_sim_after_learn       3
% 2.80/0.95  --inst_sel_renew                        solver
% 2.80/0.95  --inst_lit_activity_flag                true
% 2.80/0.95  --inst_restr_to_given                   false
% 2.80/0.95  --inst_activity_threshold               500
% 2.80/0.95  --inst_out_proof                        true
% 2.80/0.95  
% 2.80/0.95  ------ Resolution Options
% 2.80/0.95  
% 2.80/0.95  --resolution_flag                       false
% 2.80/0.95  --res_lit_sel                           adaptive
% 2.80/0.95  --res_lit_sel_side                      none
% 2.80/0.95  --res_ordering                          kbo
% 2.80/0.95  --res_to_prop_solver                    active
% 2.80/0.95  --res_prop_simpl_new                    false
% 2.80/0.95  --res_prop_simpl_given                  true
% 2.80/0.95  --res_passive_queue_type                priority_queues
% 2.80/0.95  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.80/0.95  --res_passive_queues_freq               [15;5]
% 2.80/0.95  --res_forward_subs                      full
% 2.80/0.95  --res_backward_subs                     full
% 2.80/0.95  --res_forward_subs_resolution           true
% 2.80/0.95  --res_backward_subs_resolution          true
% 2.80/0.95  --res_orphan_elimination                true
% 2.80/0.95  --res_time_limit                        2.
% 2.80/0.95  --res_out_proof                         true
% 2.80/0.95  
% 2.80/0.95  ------ Superposition Options
% 2.80/0.95  
% 2.80/0.95  --superposition_flag                    true
% 2.80/0.95  --sup_passive_queue_type                priority_queues
% 2.80/0.95  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.80/0.95  --sup_passive_queues_freq               [8;1;4]
% 2.80/0.95  --demod_completeness_check              fast
% 2.80/0.95  --demod_use_ground                      true
% 2.80/0.95  --sup_to_prop_solver                    passive
% 2.80/0.95  --sup_prop_simpl_new                    true
% 2.80/0.95  --sup_prop_simpl_given                  true
% 2.80/0.95  --sup_fun_splitting                     false
% 2.80/0.95  --sup_smt_interval                      50000
% 2.80/0.95  
% 2.80/0.95  ------ Superposition Simplification Setup
% 2.80/0.95  
% 2.80/0.95  --sup_indices_passive                   []
% 2.80/0.95  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.80/0.95  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.80/0.95  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.80/0.95  --sup_full_triv                         [TrivRules;PropSubs]
% 2.80/0.95  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.80/0.95  --sup_full_bw                           [BwDemod]
% 2.80/0.95  --sup_immed_triv                        [TrivRules]
% 2.80/0.95  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.80/0.95  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.80/0.95  --sup_immed_bw_main                     []
% 2.80/0.95  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.80/0.95  --sup_input_triv                        [Unflattening;TrivRules]
% 2.80/0.95  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.80/0.95  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.80/0.95  
% 2.80/0.95  ------ Combination Options
% 2.80/0.95  
% 2.80/0.95  --comb_res_mult                         3
% 2.80/0.95  --comb_sup_mult                         2
% 2.80/0.95  --comb_inst_mult                        10
% 2.80/0.95  
% 2.80/0.95  ------ Debug Options
% 2.80/0.95  
% 2.80/0.95  --dbg_backtrace                         false
% 2.80/0.95  --dbg_dump_prop_clauses                 false
% 2.80/0.95  --dbg_dump_prop_clauses_file            -
% 2.80/0.95  --dbg_out_stat                          false
% 2.80/0.95  
% 2.80/0.95  
% 2.80/0.95  
% 2.80/0.95  
% 2.80/0.95  ------ Proving...
% 2.80/0.95  
% 2.80/0.95  
% 2.80/0.95  % SZS status Theorem for theBenchmark.p
% 2.80/0.95  
% 2.80/0.95  % SZS output start CNFRefutation for theBenchmark.p
% 2.80/0.95  
% 2.80/0.95  fof(f10,conjecture,(
% 2.80/0.95    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (r1_partfun1(X2,X3) <=> ! [X4] : (r2_hidden(X4,k1_relset_1(X0,X1,X2)) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4))))))),
% 2.80/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/0.95  
% 2.80/0.95  fof(f11,negated_conjecture,(
% 2.80/0.95    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (r1_partfun1(X2,X3) <=> ! [X4] : (r2_hidden(X4,k1_relset_1(X0,X1,X2)) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4))))))),
% 2.80/0.95    inference(negated_conjecture,[],[f10])).
% 2.80/0.95  
% 2.80/0.95  fof(f21,plain,(
% 2.80/0.95    ? [X0,X1,X2] : (? [X3] : (((r1_partfun1(X2,X3) <~> ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,k1_relset_1(X0,X1,X2)))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 2.80/0.95    inference(ennf_transformation,[],[f11])).
% 2.80/0.95  
% 2.80/0.95  fof(f22,plain,(
% 2.80/0.95    ? [X0,X1,X2] : (? [X3] : ((r1_partfun1(X2,X3) <~> ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,k1_relset_1(X0,X1,X2)))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 2.80/0.95    inference(flattening,[],[f21])).
% 2.80/0.95  
% 2.80/0.95  fof(f31,plain,(
% 2.80/0.95    ? [X0,X1,X2] : (? [X3] : (((? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & r2_hidden(X4,k1_relset_1(X0,X1,X2))) | ~r1_partfun1(X2,X3)) & (! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,k1_relset_1(X0,X1,X2))) | r1_partfun1(X2,X3))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 2.80/0.95    inference(nnf_transformation,[],[f22])).
% 2.80/0.95  
% 2.80/0.95  fof(f32,plain,(
% 2.80/0.95    ? [X0,X1,X2] : (? [X3] : ((? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & r2_hidden(X4,k1_relset_1(X0,X1,X2))) | ~r1_partfun1(X2,X3)) & (! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,k1_relset_1(X0,X1,X2))) | r1_partfun1(X2,X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 2.80/0.95    inference(flattening,[],[f31])).
% 2.80/0.95  
% 2.80/0.95  fof(f33,plain,(
% 2.80/0.95    ? [X0,X1,X2] : (? [X3] : ((? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & r2_hidden(X4,k1_relset_1(X0,X1,X2))) | ~r1_partfun1(X2,X3)) & (! [X5] : (k1_funct_1(X2,X5) = k1_funct_1(X3,X5) | ~r2_hidden(X5,k1_relset_1(X0,X1,X2))) | r1_partfun1(X2,X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 2.80/0.95    inference(rectify,[],[f32])).
% 2.80/0.95  
% 2.80/0.95  fof(f36,plain,(
% 2.80/0.95    ( ! [X2,X0,X3,X1] : (? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & r2_hidden(X4,k1_relset_1(X0,X1,X2))) => (k1_funct_1(X2,sK5) != k1_funct_1(X3,sK5) & r2_hidden(sK5,k1_relset_1(X0,X1,X2)))) )),
% 2.80/0.95    introduced(choice_axiom,[])).
% 2.80/0.95  
% 2.80/0.95  fof(f35,plain,(
% 2.80/0.95    ( ! [X2,X0,X1] : (? [X3] : ((? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & r2_hidden(X4,k1_relset_1(X0,X1,X2))) | ~r1_partfun1(X2,X3)) & (! [X5] : (k1_funct_1(X2,X5) = k1_funct_1(X3,X5) | ~r2_hidden(X5,k1_relset_1(X0,X1,X2))) | r1_partfun1(X2,X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((? [X4] : (k1_funct_1(sK4,X4) != k1_funct_1(X2,X4) & r2_hidden(X4,k1_relset_1(X0,X1,X2))) | ~r1_partfun1(X2,sK4)) & (! [X5] : (k1_funct_1(sK4,X5) = k1_funct_1(X2,X5) | ~r2_hidden(X5,k1_relset_1(X0,X1,X2))) | r1_partfun1(X2,sK4)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(sK4,X0,X1) & v1_funct_1(sK4))) )),
% 2.80/0.95    introduced(choice_axiom,[])).
% 2.80/0.95  
% 2.80/0.95  fof(f34,plain,(
% 2.80/0.95    ? [X0,X1,X2] : (? [X3] : ((? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & r2_hidden(X4,k1_relset_1(X0,X1,X2))) | ~r1_partfun1(X2,X3)) & (! [X5] : (k1_funct_1(X2,X5) = k1_funct_1(X3,X5) | ~r2_hidden(X5,k1_relset_1(X0,X1,X2))) | r1_partfun1(X2,X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (? [X3] : ((? [X4] : (k1_funct_1(sK3,X4) != k1_funct_1(X3,X4) & r2_hidden(X4,k1_relset_1(sK1,sK2,sK3))) | ~r1_partfun1(sK3,X3)) & (! [X5] : (k1_funct_1(sK3,X5) = k1_funct_1(X3,X5) | ~r2_hidden(X5,k1_relset_1(sK1,sK2,sK3))) | r1_partfun1(sK3,X3)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X3,sK1,sK2) & v1_funct_1(X3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_1(sK3))),
% 2.80/0.95    introduced(choice_axiom,[])).
% 2.80/0.95  
% 2.80/0.95  fof(f37,plain,(
% 2.80/0.95    (((k1_funct_1(sK3,sK5) != k1_funct_1(sK4,sK5) & r2_hidden(sK5,k1_relset_1(sK1,sK2,sK3))) | ~r1_partfun1(sK3,sK4)) & (! [X5] : (k1_funct_1(sK3,X5) = k1_funct_1(sK4,X5) | ~r2_hidden(X5,k1_relset_1(sK1,sK2,sK3))) | r1_partfun1(sK3,sK4)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK2) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_1(sK3)),
% 2.80/0.95    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f33,f36,f35,f34])).
% 2.80/0.95  
% 2.80/0.95  fof(f60,plain,(
% 2.80/0.95    v1_funct_2(sK4,sK1,sK2)),
% 2.80/0.95    inference(cnf_transformation,[],[f37])).
% 2.80/0.95  
% 2.80/0.95  fof(f8,axiom,(
% 2.80/0.95    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.80/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/0.95  
% 2.80/0.95  fof(f17,plain,(
% 2.80/0.95    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.80/0.95    inference(ennf_transformation,[],[f8])).
% 2.80/0.95  
% 2.80/0.95  fof(f18,plain,(
% 2.80/0.95    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.80/0.95    inference(flattening,[],[f17])).
% 2.80/0.95  
% 2.80/0.95  fof(f26,plain,(
% 2.80/0.95    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.80/0.95    inference(nnf_transformation,[],[f18])).
% 2.80/0.95  
% 2.80/0.95  fof(f48,plain,(
% 2.80/0.95    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.80/0.95    inference(cnf_transformation,[],[f26])).
% 2.80/0.95  
% 2.80/0.95  fof(f61,plain,(
% 2.80/0.95    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 2.80/0.95    inference(cnf_transformation,[],[f37])).
% 2.80/0.95  
% 2.80/0.95  fof(f7,axiom,(
% 2.80/0.95    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.80/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/0.95  
% 2.80/0.95  fof(f16,plain,(
% 2.80/0.95    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.80/0.95    inference(ennf_transformation,[],[f7])).
% 2.80/0.95  
% 2.80/0.95  fof(f47,plain,(
% 2.80/0.95    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.80/0.95    inference(cnf_transformation,[],[f16])).
% 2.80/0.95  
% 2.80/0.95  fof(f9,axiom,(
% 2.80/0.95    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) => (r1_partfun1(X0,X1) <=> ! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2))))))),
% 2.80/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/0.95  
% 2.80/0.95  fof(f19,plain,(
% 2.80/0.95    ! [X0] : (! [X1] : (((r1_partfun1(X0,X1) <=> ! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0)))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.80/0.95    inference(ennf_transformation,[],[f9])).
% 2.80/0.95  
% 2.80/0.95  fof(f20,plain,(
% 2.80/0.95    ! [X0] : (! [X1] : ((r1_partfun1(X0,X1) <=> ! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0)))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.80/0.95    inference(flattening,[],[f19])).
% 2.80/0.95  
% 2.80/0.95  fof(f27,plain,(
% 2.80/0.95    ! [X0] : (! [X1] : (((r1_partfun1(X0,X1) | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0)))) & (! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0))) | ~r1_partfun1(X0,X1))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.80/0.95    inference(nnf_transformation,[],[f20])).
% 2.80/0.95  
% 2.80/0.95  fof(f28,plain,(
% 2.80/0.95    ! [X0] : (! [X1] : (((r1_partfun1(X0,X1) | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0)))) & (! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r1_partfun1(X0,X1))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.80/0.95    inference(rectify,[],[f27])).
% 2.80/0.95  
% 2.80/0.95  fof(f29,plain,(
% 2.80/0.95    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1)) & r2_hidden(sK0(X0,X1),k1_relat_1(X0))))),
% 2.80/0.95    introduced(choice_axiom,[])).
% 2.80/0.95  
% 2.80/0.95  fof(f30,plain,(
% 2.80/0.95    ! [X0] : (! [X1] : (((r1_partfun1(X0,X1) | (k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1)) & r2_hidden(sK0(X0,X1),k1_relat_1(X0)))) & (! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r1_partfun1(X0,X1))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.80/0.95    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).
% 2.80/0.95  
% 2.80/0.95  fof(f55,plain,(
% 2.80/0.95    ( ! [X0,X1] : (r1_partfun1(X0,X1) | r2_hidden(sK0(X0,X1),k1_relat_1(X0)) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.80/0.95    inference(cnf_transformation,[],[f30])).
% 2.80/0.95  
% 2.80/0.95  fof(f58,plain,(
% 2.80/0.95    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 2.80/0.95    inference(cnf_transformation,[],[f37])).
% 2.80/0.95  
% 2.80/0.95  fof(f63,plain,(
% 2.80/0.95    ( ! [X5] : (k1_funct_1(sK3,X5) = k1_funct_1(sK4,X5) | ~r2_hidden(X5,k1_relset_1(sK1,sK2,sK3)) | r1_partfun1(sK3,sK4)) )),
% 2.80/0.95    inference(cnf_transformation,[],[f37])).
% 2.80/0.95  
% 2.80/0.95  fof(f57,plain,(
% 2.80/0.95    v1_funct_1(sK3)),
% 2.80/0.95    inference(cnf_transformation,[],[f37])).
% 2.80/0.95  
% 2.80/0.95  fof(f3,axiom,(
% 2.80/0.95    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.80/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/0.95  
% 2.80/0.95  fof(f13,plain,(
% 2.80/0.95    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.80/0.95    inference(ennf_transformation,[],[f3])).
% 2.80/0.95  
% 2.80/0.95  fof(f42,plain,(
% 2.80/0.95    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.80/0.95    inference(cnf_transformation,[],[f13])).
% 2.80/0.95  
% 2.80/0.95  fof(f5,axiom,(
% 2.80/0.95    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.80/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/0.95  
% 2.80/0.95  fof(f45,plain,(
% 2.80/0.95    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.80/0.95    inference(cnf_transformation,[],[f5])).
% 2.80/0.95  
% 2.80/0.95  fof(f59,plain,(
% 2.80/0.95    v1_funct_1(sK4)),
% 2.80/0.95    inference(cnf_transformation,[],[f37])).
% 2.80/0.95  
% 2.80/0.95  fof(f6,axiom,(
% 2.80/0.95    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.80/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/0.95  
% 2.80/0.95  fof(f12,plain,(
% 2.80/0.95    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.80/0.95    inference(pure_predicate_removal,[],[f6])).
% 2.80/0.95  
% 2.80/0.95  fof(f15,plain,(
% 2.80/0.95    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.80/0.95    inference(ennf_transformation,[],[f12])).
% 2.80/0.95  
% 2.80/0.95  fof(f46,plain,(
% 2.80/0.95    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.80/0.95    inference(cnf_transformation,[],[f15])).
% 2.80/0.95  
% 2.80/0.95  fof(f4,axiom,(
% 2.80/0.95    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 2.80/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/0.95  
% 2.80/0.95  fof(f14,plain,(
% 2.80/0.95    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.80/0.95    inference(ennf_transformation,[],[f4])).
% 2.80/0.95  
% 2.80/0.95  fof(f25,plain,(
% 2.80/0.95    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.80/0.95    inference(nnf_transformation,[],[f14])).
% 2.80/0.95  
% 2.80/0.95  fof(f43,plain,(
% 2.80/0.95    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.80/0.95    inference(cnf_transformation,[],[f25])).
% 2.80/0.95  
% 2.80/0.95  fof(f64,plain,(
% 2.80/0.95    r2_hidden(sK5,k1_relset_1(sK1,sK2,sK3)) | ~r1_partfun1(sK3,sK4)),
% 2.80/0.95    inference(cnf_transformation,[],[f37])).
% 2.80/0.95  
% 2.80/0.95  fof(f54,plain,(
% 2.80/0.95    ( ! [X0,X3,X1] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r1_partfun1(X0,X1) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.80/0.95    inference(cnf_transformation,[],[f30])).
% 2.80/0.95  
% 2.80/0.95  fof(f56,plain,(
% 2.80/0.95    ( ! [X0,X1] : (r1_partfun1(X0,X1) | k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1)) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.80/0.95    inference(cnf_transformation,[],[f30])).
% 2.80/0.95  
% 2.80/0.95  fof(f65,plain,(
% 2.80/0.95    k1_funct_1(sK3,sK5) != k1_funct_1(sK4,sK5) | ~r1_partfun1(sK3,sK4)),
% 2.80/0.95    inference(cnf_transformation,[],[f37])).
% 2.80/0.95  
% 2.80/0.95  fof(f62,plain,(
% 2.80/0.95    k1_xboole_0 = sK1 | k1_xboole_0 != sK2),
% 2.80/0.95    inference(cnf_transformation,[],[f37])).
% 2.80/0.95  
% 2.80/0.95  fof(f49,plain,(
% 2.80/0.95    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.80/0.95    inference(cnf_transformation,[],[f26])).
% 2.80/0.95  
% 2.80/0.95  fof(f72,plain,(
% 2.80/0.95    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 2.80/0.95    inference(equality_resolution,[],[f49])).
% 2.80/0.95  
% 2.80/0.95  fof(f2,axiom,(
% 2.80/0.95    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.80/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/0.95  
% 2.80/0.95  fof(f41,plain,(
% 2.80/0.95    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.80/0.95    inference(cnf_transformation,[],[f2])).
% 2.80/0.95  
% 2.80/0.95  fof(f1,axiom,(
% 2.80/0.95    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.80/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/0.95  
% 2.80/0.95  fof(f23,plain,(
% 2.80/0.95    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.80/0.95    inference(nnf_transformation,[],[f1])).
% 2.80/0.95  
% 2.80/0.95  fof(f24,plain,(
% 2.80/0.95    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.80/0.95    inference(flattening,[],[f23])).
% 2.80/0.95  
% 2.80/0.95  fof(f40,plain,(
% 2.80/0.95    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.80/0.95    inference(cnf_transformation,[],[f24])).
% 2.80/0.95  
% 2.80/0.95  fof(f52,plain,(
% 2.80/0.95    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.80/0.95    inference(cnf_transformation,[],[f26])).
% 2.80/0.95  
% 2.80/0.95  fof(f70,plain,(
% 2.80/0.95    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 2.80/0.95    inference(equality_resolution,[],[f52])).
% 2.80/0.95  
% 2.80/0.95  cnf(c_24,negated_conjecture,
% 2.80/0.95      ( v1_funct_2(sK4,sK1,sK2) ),
% 2.80/0.95      inference(cnf_transformation,[],[f60]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_15,plain,
% 2.80/0.95      ( ~ v1_funct_2(X0,X1,X2)
% 2.80/0.95      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.80/0.95      | k1_relset_1(X1,X2,X0) = X1
% 2.80/0.95      | k1_xboole_0 = X2 ),
% 2.80/0.95      inference(cnf_transformation,[],[f48]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_23,negated_conjecture,
% 2.80/0.95      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 2.80/0.95      inference(cnf_transformation,[],[f61]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_488,plain,
% 2.80/0.95      ( ~ v1_funct_2(X0,X1,X2)
% 2.80/0.95      | k1_relset_1(X1,X2,X0) = X1
% 2.80/0.95      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.80/0.95      | sK4 != X0
% 2.80/0.95      | k1_xboole_0 = X2 ),
% 2.80/0.95      inference(resolution_lifted,[status(thm)],[c_15,c_23]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_489,plain,
% 2.80/0.95      ( ~ v1_funct_2(sK4,X0,X1)
% 2.80/0.95      | k1_relset_1(X0,X1,sK4) = X0
% 2.80/0.95      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.80/0.95      | k1_xboole_0 = X1 ),
% 2.80/0.95      inference(unflattening,[status(thm)],[c_488]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_1089,plain,
% 2.80/0.95      ( k1_relset_1(X0,X1,sK4) = X0
% 2.80/0.95      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.80/0.95      | sK2 != X1
% 2.80/0.95      | sK1 != X0
% 2.80/0.95      | sK4 != sK4
% 2.80/0.95      | k1_xboole_0 = X1 ),
% 2.80/0.95      inference(resolution_lifted,[status(thm)],[c_24,c_489]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_1090,plain,
% 2.80/0.95      ( k1_relset_1(sK1,sK2,sK4) = sK1
% 2.80/0.95      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.80/0.95      | k1_xboole_0 = sK2 ),
% 2.80/0.95      inference(unflattening,[status(thm)],[c_1089]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_1693,plain,
% 2.80/0.95      ( k1_relset_1(sK1,sK2,sK4) = sK1 | k1_xboole_0 = sK2 ),
% 2.80/0.95      inference(equality_resolution_simp,[status(thm)],[c_1090]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_9,plain,
% 2.80/0.95      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.80/0.95      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.80/0.95      inference(cnf_transformation,[],[f47]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_524,plain,
% 2.80/0.95      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.80/0.95      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.80/0.95      | sK4 != X2 ),
% 2.80/0.95      inference(resolution_lifted,[status(thm)],[c_9,c_23]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_525,plain,
% 2.80/0.95      ( k1_relset_1(X0,X1,sK4) = k1_relat_1(sK4)
% 2.80/0.95      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 2.80/0.95      inference(unflattening,[status(thm)],[c_524]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_1920,plain,
% 2.80/0.95      ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
% 2.80/0.95      inference(equality_resolution,[status(thm)],[c_525]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_2808,plain,
% 2.80/0.95      ( k1_relat_1(sK4) = sK1 | sK2 = k1_xboole_0 ),
% 2.80/0.95      inference(demodulation,[status(thm)],[c_1693,c_1920]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_17,plain,
% 2.80/0.95      ( r2_hidden(sK0(X0,X1),k1_relat_1(X0))
% 2.80/0.95      | r1_partfun1(X0,X1)
% 2.80/0.95      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 2.80/0.95      | ~ v1_funct_1(X1)
% 2.80/0.95      | ~ v1_funct_1(X0)
% 2.80/0.95      | ~ v1_relat_1(X0)
% 2.80/0.95      | ~ v1_relat_1(X1) ),
% 2.80/0.95      inference(cnf_transformation,[],[f55]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_1639,plain,
% 2.80/0.95      ( r2_hidden(sK0(X0,X1),k1_relat_1(X0)) = iProver_top
% 2.80/0.95      | r1_partfun1(X0,X1) = iProver_top
% 2.80/0.95      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) != iProver_top
% 2.80/0.95      | v1_funct_1(X1) != iProver_top
% 2.80/0.95      | v1_funct_1(X0) != iProver_top
% 2.80/0.95      | v1_relat_1(X1) != iProver_top
% 2.80/0.95      | v1_relat_1(X0) != iProver_top ),
% 2.80/0.95      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_26,negated_conjecture,
% 2.80/0.95      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 2.80/0.95      inference(cnf_transformation,[],[f58]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_584,plain,
% 2.80/0.95      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.80/0.95      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.80/0.95      | sK3 != X2 ),
% 2.80/0.95      inference(resolution_lifted,[status(thm)],[c_9,c_26]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_585,plain,
% 2.80/0.95      ( k1_relset_1(X0,X1,sK3) = k1_relat_1(sK3)
% 2.80/0.95      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 2.80/0.95      inference(unflattening,[status(thm)],[c_584]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_1968,plain,
% 2.80/0.95      ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
% 2.80/0.95      inference(equality_resolution,[status(thm)],[c_585]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_21,negated_conjecture,
% 2.80/0.95      ( ~ r2_hidden(X0,k1_relset_1(sK1,sK2,sK3))
% 2.80/0.95      | r1_partfun1(sK3,sK4)
% 2.80/0.95      | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0) ),
% 2.80/0.95      inference(cnf_transformation,[],[f63]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_1635,plain,
% 2.80/0.95      ( k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0)
% 2.80/0.95      | r2_hidden(X0,k1_relset_1(sK1,sK2,sK3)) != iProver_top
% 2.80/0.95      | r1_partfun1(sK3,sK4) = iProver_top ),
% 2.80/0.95      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_2270,plain,
% 2.80/0.95      ( k1_funct_1(sK4,X0) = k1_funct_1(sK3,X0)
% 2.80/0.95      | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 2.80/0.95      | r1_partfun1(sK3,sK4) = iProver_top ),
% 2.80/0.95      inference(demodulation,[status(thm)],[c_1968,c_1635]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_2964,plain,
% 2.80/0.95      ( k1_funct_1(sK3,sK0(sK3,X0)) = k1_funct_1(sK4,sK0(sK3,X0))
% 2.80/0.95      | r1_partfun1(sK3,X0) = iProver_top
% 2.80/0.95      | r1_partfun1(sK3,sK4) = iProver_top
% 2.80/0.95      | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) != iProver_top
% 2.80/0.95      | v1_funct_1(X0) != iProver_top
% 2.80/0.95      | v1_funct_1(sK3) != iProver_top
% 2.80/0.95      | v1_relat_1(X0) != iProver_top
% 2.80/0.95      | v1_relat_1(sK3) != iProver_top ),
% 2.80/0.95      inference(superposition,[status(thm)],[c_1639,c_2270]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_27,negated_conjecture,
% 2.80/0.95      ( v1_funct_1(sK3) ),
% 2.80/0.95      inference(cnf_transformation,[],[f57]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_28,plain,
% 2.80/0.95      ( v1_funct_1(sK3) = iProver_top ),
% 2.80/0.95      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_4,plain,
% 2.80/0.95      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.80/0.95      | ~ v1_relat_1(X1)
% 2.80/0.95      | v1_relat_1(X0) ),
% 2.80/0.95      inference(cnf_transformation,[],[f42]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_458,plain,
% 2.80/0.95      ( ~ v1_relat_1(X0)
% 2.80/0.95      | v1_relat_1(X1)
% 2.80/0.95      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(X0)
% 2.80/0.95      | sK3 != X1 ),
% 2.80/0.95      inference(resolution_lifted,[status(thm)],[c_4,c_26]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_459,plain,
% 2.80/0.95      ( ~ v1_relat_1(X0)
% 2.80/0.95      | v1_relat_1(sK3)
% 2.80/0.95      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(X0) ),
% 2.80/0.95      inference(unflattening,[status(thm)],[c_458]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_1631,plain,
% 2.80/0.95      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(X0)
% 2.80/0.95      | v1_relat_1(X0) != iProver_top
% 2.80/0.95      | v1_relat_1(sK3) = iProver_top ),
% 2.80/0.95      inference(predicate_to_equality,[status(thm)],[c_459]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_2328,plain,
% 2.80/0.95      ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
% 2.80/0.95      | v1_relat_1(sK3) = iProver_top ),
% 2.80/0.95      inference(equality_resolution,[status(thm)],[c_1631]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_7,plain,
% 2.80/0.95      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.80/0.95      inference(cnf_transformation,[],[f45]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_2336,plain,
% 2.80/0.95      ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) ),
% 2.80/0.95      inference(instantiation,[status(thm)],[c_7]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_2337,plain,
% 2.80/0.95      ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) = iProver_top ),
% 2.80/0.95      inference(predicate_to_equality,[status(thm)],[c_2336]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_3370,plain,
% 2.80/0.95      ( v1_relat_1(X0) != iProver_top
% 2.80/0.95      | k1_funct_1(sK3,sK0(sK3,X0)) = k1_funct_1(sK4,sK0(sK3,X0))
% 2.80/0.95      | r1_partfun1(sK3,X0) = iProver_top
% 2.80/0.95      | r1_partfun1(sK3,sK4) = iProver_top
% 2.80/0.95      | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) != iProver_top
% 2.80/0.95      | v1_funct_1(X0) != iProver_top ),
% 2.80/0.95      inference(global_propositional_subsumption,
% 2.80/0.95                [status(thm)],
% 2.80/0.95                [c_2964,c_28,c_2328,c_2337]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_3371,plain,
% 2.80/0.95      ( k1_funct_1(sK3,sK0(sK3,X0)) = k1_funct_1(sK4,sK0(sK3,X0))
% 2.80/0.95      | r1_partfun1(sK3,X0) = iProver_top
% 2.80/0.95      | r1_partfun1(sK3,sK4) = iProver_top
% 2.80/0.95      | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) != iProver_top
% 2.80/0.95      | v1_funct_1(X0) != iProver_top
% 2.80/0.95      | v1_relat_1(X0) != iProver_top ),
% 2.80/0.95      inference(renaming,[status(thm)],[c_3370]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_3383,plain,
% 2.80/0.95      ( k1_funct_1(sK3,sK0(sK3,sK4)) = k1_funct_1(sK4,sK0(sK3,sK4))
% 2.80/0.95      | sK2 = k1_xboole_0
% 2.80/0.95      | r1_partfun1(sK3,sK4) = iProver_top
% 2.80/0.95      | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top
% 2.80/0.95      | v1_funct_1(sK4) != iProver_top
% 2.80/0.95      | v1_relat_1(sK4) != iProver_top ),
% 2.80/0.95      inference(superposition,[status(thm)],[c_2808,c_3371]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_25,negated_conjecture,
% 2.80/0.95      ( v1_funct_1(sK4) ),
% 2.80/0.95      inference(cnf_transformation,[],[f59]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_30,plain,
% 2.80/0.95      ( v1_funct_1(sK4) = iProver_top ),
% 2.80/0.95      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_443,plain,
% 2.80/0.95      ( ~ v1_relat_1(X0)
% 2.80/0.95      | v1_relat_1(X1)
% 2.80/0.95      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(X0)
% 2.80/0.95      | sK4 != X1 ),
% 2.80/0.95      inference(resolution_lifted,[status(thm)],[c_4,c_23]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_444,plain,
% 2.80/0.95      ( ~ v1_relat_1(X0)
% 2.80/0.95      | v1_relat_1(sK4)
% 2.80/0.95      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(X0) ),
% 2.80/0.95      inference(unflattening,[status(thm)],[c_443]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_1632,plain,
% 2.80/0.95      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(X0)
% 2.80/0.95      | v1_relat_1(X0) != iProver_top
% 2.80/0.95      | v1_relat_1(sK4) = iProver_top ),
% 2.80/0.95      inference(predicate_to_equality,[status(thm)],[c_444]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_2334,plain,
% 2.80/0.95      ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
% 2.80/0.95      | v1_relat_1(sK4) = iProver_top ),
% 2.80/0.95      inference(equality_resolution,[status(thm)],[c_1632]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_8,plain,
% 2.80/0.95      ( v4_relat_1(X0,X1)
% 2.80/0.95      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.80/0.95      inference(cnf_transformation,[],[f46]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_6,plain,
% 2.80/0.95      ( ~ v4_relat_1(X0,X1)
% 2.80/0.95      | r1_tarski(k1_relat_1(X0),X1)
% 2.80/0.95      | ~ v1_relat_1(X0) ),
% 2.80/0.95      inference(cnf_transformation,[],[f43]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_292,plain,
% 2.80/0.95      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.80/0.95      | r1_tarski(k1_relat_1(X0),X1)
% 2.80/0.95      | ~ v1_relat_1(X0) ),
% 2.80/0.95      inference(resolution,[status(thm)],[c_8,c_6]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_533,plain,
% 2.80/0.95      ( r1_tarski(k1_relat_1(X0),X1)
% 2.80/0.95      | ~ v1_relat_1(X0)
% 2.80/0.95      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.80/0.95      | sK3 != X0 ),
% 2.80/0.95      inference(resolution_lifted,[status(thm)],[c_292,c_26]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_534,plain,
% 2.80/0.95      ( r1_tarski(k1_relat_1(sK3),X0)
% 2.80/0.95      | ~ v1_relat_1(sK3)
% 2.80/0.95      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 2.80/0.95      inference(unflattening,[status(thm)],[c_533]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_1629,plain,
% 2.80/0.95      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.80/0.95      | r1_tarski(k1_relat_1(sK3),X0) = iProver_top
% 2.80/0.95      | v1_relat_1(sK3) != iProver_top ),
% 2.80/0.95      inference(predicate_to_equality,[status(thm)],[c_534]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_535,plain,
% 2.80/0.95      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.80/0.95      | r1_tarski(k1_relat_1(sK3),X0) = iProver_top
% 2.80/0.95      | v1_relat_1(sK3) != iProver_top ),
% 2.80/0.95      inference(predicate_to_equality,[status(thm)],[c_534]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_2564,plain,
% 2.80/0.95      ( r1_tarski(k1_relat_1(sK3),X0) = iProver_top
% 2.80/0.95      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 2.80/0.95      inference(global_propositional_subsumption,
% 2.80/0.95                [status(thm)],
% 2.80/0.95                [c_1629,c_535,c_2328,c_2337]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_2565,plain,
% 2.80/0.95      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.80/0.95      | r1_tarski(k1_relat_1(sK3),X0) = iProver_top ),
% 2.80/0.95      inference(renaming,[status(thm)],[c_2564]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_2572,plain,
% 2.80/0.95      ( r1_tarski(k1_relat_1(sK3),sK1) = iProver_top ),
% 2.80/0.95      inference(equality_resolution,[status(thm)],[c_2565]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_3803,plain,
% 2.80/0.95      ( r1_partfun1(sK3,sK4) = iProver_top
% 2.80/0.95      | sK2 = k1_xboole_0
% 2.80/0.95      | k1_funct_1(sK3,sK0(sK3,sK4)) = k1_funct_1(sK4,sK0(sK3,sK4)) ),
% 2.80/0.95      inference(global_propositional_subsumption,
% 2.80/0.95                [status(thm)],
% 2.80/0.95                [c_3383,c_30,c_2334,c_2337,c_2572]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_3804,plain,
% 2.80/0.95      ( k1_funct_1(sK3,sK0(sK3,sK4)) = k1_funct_1(sK4,sK0(sK3,sK4))
% 2.80/0.95      | sK2 = k1_xboole_0
% 2.80/0.95      | r1_partfun1(sK3,sK4) = iProver_top ),
% 2.80/0.95      inference(renaming,[status(thm)],[c_3803]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_20,negated_conjecture,
% 2.80/0.95      ( r2_hidden(sK5,k1_relset_1(sK1,sK2,sK3))
% 2.80/0.95      | ~ r1_partfun1(sK3,sK4) ),
% 2.80/0.95      inference(cnf_transformation,[],[f64]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_1636,plain,
% 2.80/0.95      ( r2_hidden(sK5,k1_relset_1(sK1,sK2,sK3)) = iProver_top
% 2.80/0.95      | r1_partfun1(sK3,sK4) != iProver_top ),
% 2.80/0.95      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_2271,plain,
% 2.80/0.95      ( r2_hidden(sK5,k1_relat_1(sK3)) = iProver_top
% 2.80/0.95      | r1_partfun1(sK3,sK4) != iProver_top ),
% 2.80/0.95      inference(demodulation,[status(thm)],[c_1968,c_1636]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_18,plain,
% 2.80/0.95      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.80/0.95      | ~ r1_partfun1(X1,X2)
% 2.80/0.95      | ~ r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
% 2.80/0.95      | ~ v1_funct_1(X2)
% 2.80/0.95      | ~ v1_funct_1(X1)
% 2.80/0.95      | ~ v1_relat_1(X1)
% 2.80/0.95      | ~ v1_relat_1(X2)
% 2.80/0.95      | k1_funct_1(X2,X0) = k1_funct_1(X1,X0) ),
% 2.80/0.95      inference(cnf_transformation,[],[f54]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_1638,plain,
% 2.80/0.95      ( k1_funct_1(X0,X1) = k1_funct_1(X2,X1)
% 2.80/0.95      | r2_hidden(X1,k1_relat_1(X2)) != iProver_top
% 2.80/0.95      | r1_partfun1(X2,X0) != iProver_top
% 2.80/0.95      | r1_tarski(k1_relat_1(X2),k1_relat_1(X0)) != iProver_top
% 2.80/0.95      | v1_funct_1(X0) != iProver_top
% 2.80/0.95      | v1_funct_1(X2) != iProver_top
% 2.80/0.95      | v1_relat_1(X2) != iProver_top
% 2.80/0.95      | v1_relat_1(X0) != iProver_top ),
% 2.80/0.95      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_2811,plain,
% 2.80/0.95      ( k1_funct_1(X0,X1) = k1_funct_1(sK4,X1)
% 2.80/0.95      | sK2 = k1_xboole_0
% 2.80/0.95      | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
% 2.80/0.95      | r1_partfun1(X0,sK4) != iProver_top
% 2.80/0.95      | r1_tarski(k1_relat_1(X0),sK1) != iProver_top
% 2.80/0.95      | v1_funct_1(X0) != iProver_top
% 2.80/0.95      | v1_funct_1(sK4) != iProver_top
% 2.80/0.95      | v1_relat_1(X0) != iProver_top
% 2.80/0.95      | v1_relat_1(sK4) != iProver_top ),
% 2.80/0.95      inference(superposition,[status(thm)],[c_2808,c_1638]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_3563,plain,
% 2.80/0.95      ( v1_relat_1(X0) != iProver_top
% 2.80/0.95      | k1_funct_1(X0,X1) = k1_funct_1(sK4,X1)
% 2.80/0.95      | sK2 = k1_xboole_0
% 2.80/0.95      | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
% 2.80/0.95      | r1_partfun1(X0,sK4) != iProver_top
% 2.80/0.95      | r1_tarski(k1_relat_1(X0),sK1) != iProver_top
% 2.80/0.95      | v1_funct_1(X0) != iProver_top ),
% 2.80/0.95      inference(global_propositional_subsumption,
% 2.80/0.95                [status(thm)],
% 2.80/0.95                [c_2811,c_30,c_2334,c_2337]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_3564,plain,
% 2.80/0.95      ( k1_funct_1(X0,X1) = k1_funct_1(sK4,X1)
% 2.80/0.95      | sK2 = k1_xboole_0
% 2.80/0.95      | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
% 2.80/0.95      | r1_partfun1(X0,sK4) != iProver_top
% 2.80/0.95      | r1_tarski(k1_relat_1(X0),sK1) != iProver_top
% 2.80/0.95      | v1_funct_1(X0) != iProver_top
% 2.80/0.95      | v1_relat_1(X0) != iProver_top ),
% 2.80/0.95      inference(renaming,[status(thm)],[c_3563]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_3577,plain,
% 2.80/0.95      ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
% 2.80/0.95      | sK2 = k1_xboole_0
% 2.80/0.95      | r1_partfun1(sK3,sK4) != iProver_top
% 2.80/0.95      | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top
% 2.80/0.95      | v1_funct_1(sK3) != iProver_top
% 2.80/0.95      | v1_relat_1(sK3) != iProver_top ),
% 2.80/0.95      inference(superposition,[status(thm)],[c_2271,c_3564]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_3665,plain,
% 2.80/0.95      ( r1_partfun1(sK3,sK4) != iProver_top
% 2.80/0.95      | sK2 = k1_xboole_0
% 2.80/0.95      | k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5) ),
% 2.80/0.95      inference(global_propositional_subsumption,
% 2.80/0.95                [status(thm)],
% 2.80/0.95                [c_3577,c_28,c_2328,c_2337,c_2572]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_3666,plain,
% 2.80/0.95      ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
% 2.80/0.95      | sK2 = k1_xboole_0
% 2.80/0.95      | r1_partfun1(sK3,sK4) != iProver_top ),
% 2.80/0.95      inference(renaming,[status(thm)],[c_3665]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_3810,plain,
% 2.80/0.95      ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
% 2.80/0.95      | k1_funct_1(sK3,sK0(sK3,sK4)) = k1_funct_1(sK4,sK0(sK3,sK4))
% 2.80/0.95      | sK2 = k1_xboole_0 ),
% 2.80/0.95      inference(superposition,[status(thm)],[c_3804,c_3666]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_16,plain,
% 2.80/0.95      ( r1_partfun1(X0,X1)
% 2.80/0.95      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 2.80/0.95      | ~ v1_funct_1(X1)
% 2.80/0.95      | ~ v1_funct_1(X0)
% 2.80/0.95      | ~ v1_relat_1(X0)
% 2.80/0.95      | ~ v1_relat_1(X1)
% 2.80/0.95      | k1_funct_1(X1,sK0(X0,X1)) != k1_funct_1(X0,sK0(X0,X1)) ),
% 2.80/0.95      inference(cnf_transformation,[],[f56]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_1640,plain,
% 2.80/0.95      ( k1_funct_1(X0,sK0(X1,X0)) != k1_funct_1(X1,sK0(X1,X0))
% 2.80/0.95      | r1_partfun1(X1,X0) = iProver_top
% 2.80/0.95      | r1_tarski(k1_relat_1(X1),k1_relat_1(X0)) != iProver_top
% 2.80/0.95      | v1_funct_1(X0) != iProver_top
% 2.80/0.95      | v1_funct_1(X1) != iProver_top
% 2.80/0.95      | v1_relat_1(X0) != iProver_top
% 2.80/0.95      | v1_relat_1(X1) != iProver_top ),
% 2.80/0.95      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_3880,plain,
% 2.80/0.95      ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
% 2.80/0.95      | sK2 = k1_xboole_0
% 2.80/0.95      | r1_partfun1(sK3,sK4) = iProver_top
% 2.80/0.95      | r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4)) != iProver_top
% 2.80/0.95      | v1_funct_1(sK4) != iProver_top
% 2.80/0.95      | v1_funct_1(sK3) != iProver_top
% 2.80/0.95      | v1_relat_1(sK4) != iProver_top
% 2.80/0.95      | v1_relat_1(sK3) != iProver_top ),
% 2.80/0.95      inference(superposition,[status(thm)],[c_3810,c_1640]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_3883,plain,
% 2.80/0.95      ( sK2 = k1_xboole_0
% 2.80/0.95      | k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
% 2.80/0.95      | r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4)) != iProver_top ),
% 2.80/0.95      inference(global_propositional_subsumption,
% 2.80/0.95                [status(thm)],
% 2.80/0.95                [c_3880,c_28,c_30,c_2328,c_2334,c_2337,c_2572,c_3577]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_3884,plain,
% 2.80/0.95      ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
% 2.80/0.95      | sK2 = k1_xboole_0
% 2.80/0.95      | r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4)) != iProver_top ),
% 2.80/0.95      inference(renaming,[status(thm)],[c_3883]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_3890,plain,
% 2.80/0.95      ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
% 2.80/0.95      | sK2 = k1_xboole_0
% 2.80/0.95      | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top ),
% 2.80/0.95      inference(superposition,[status(thm)],[c_2808,c_3884]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_3918,plain,
% 2.80/0.95      ( sK2 = k1_xboole_0 | k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5) ),
% 2.80/0.95      inference(global_propositional_subsumption,
% 2.80/0.95                [status(thm)],
% 2.80/0.95                [c_3890,c_2572]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_3919,plain,
% 2.80/0.95      ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5) | sK2 = k1_xboole_0 ),
% 2.80/0.95      inference(renaming,[status(thm)],[c_3918]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_19,negated_conjecture,
% 2.80/0.95      ( ~ r1_partfun1(sK3,sK4)
% 2.80/0.95      | k1_funct_1(sK3,sK5) != k1_funct_1(sK4,sK5) ),
% 2.80/0.95      inference(cnf_transformation,[],[f65]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_1637,plain,
% 2.80/0.95      ( k1_funct_1(sK3,sK5) != k1_funct_1(sK4,sK5)
% 2.80/0.95      | r1_partfun1(sK3,sK4) != iProver_top ),
% 2.80/0.95      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_3922,plain,
% 2.80/0.95      ( sK2 = k1_xboole_0 | r1_partfun1(sK3,sK4) != iProver_top ),
% 2.80/0.95      inference(superposition,[status(thm)],[c_3919,c_1637]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_3927,plain,
% 2.80/0.95      ( k1_funct_1(sK3,sK0(sK3,sK4)) = k1_funct_1(sK4,sK0(sK3,sK4))
% 2.80/0.95      | sK2 = k1_xboole_0 ),
% 2.80/0.95      inference(superposition,[status(thm)],[c_3804,c_3922]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_3978,plain,
% 2.80/0.95      ( sK2 = k1_xboole_0
% 2.80/0.95      | r1_partfun1(sK3,sK4) = iProver_top
% 2.80/0.95      | r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4)) != iProver_top
% 2.80/0.95      | v1_funct_1(sK4) != iProver_top
% 2.80/0.95      | v1_funct_1(sK3) != iProver_top
% 2.80/0.95      | v1_relat_1(sK4) != iProver_top
% 2.80/0.95      | v1_relat_1(sK3) != iProver_top ),
% 2.80/0.95      inference(superposition,[status(thm)],[c_3927,c_1640]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_3981,plain,
% 2.80/0.95      ( sK2 = k1_xboole_0
% 2.80/0.95      | r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4)) != iProver_top ),
% 2.80/0.95      inference(global_propositional_subsumption,
% 2.80/0.95                [status(thm)],
% 2.80/0.95                [c_3978,c_28,c_30,c_2328,c_2334,c_2337,c_3922]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_3987,plain,
% 2.80/0.95      ( sK2 = k1_xboole_0
% 2.80/0.95      | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top ),
% 2.80/0.95      inference(superposition,[status(thm)],[c_2808,c_3981]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_4023,plain,
% 2.80/0.95      ( sK2 = k1_xboole_0 ),
% 2.80/0.95      inference(global_propositional_subsumption,
% 2.80/0.95                [status(thm)],
% 2.80/0.95                [c_3987,c_2572]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_4039,plain,
% 2.80/0.95      ( k1_relset_1(sK1,k1_xboole_0,sK4) = k1_relat_1(sK4) ),
% 2.80/0.95      inference(demodulation,[status(thm)],[c_4023,c_1920]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_22,negated_conjecture,
% 2.80/0.95      ( k1_xboole_0 != sK2 | k1_xboole_0 = sK1 ),
% 2.80/0.95      inference(cnf_transformation,[],[f62]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_4045,plain,
% 2.80/0.95      ( sK1 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 2.80/0.95      inference(demodulation,[status(thm)],[c_4023,c_22]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_4046,plain,
% 2.80/0.95      ( sK1 = k1_xboole_0 ),
% 2.80/0.95      inference(equality_resolution_simp,[status(thm)],[c_4045]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_14,plain,
% 2.80/0.95      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 2.80/0.95      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.80/0.95      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 2.80/0.95      inference(cnf_transformation,[],[f72]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_663,plain,
% 2.80/0.95      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 2.80/0.95      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 2.80/0.95      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.80/0.95      | sK4 != X0 ),
% 2.80/0.95      inference(resolution_lifted,[status(thm)],[c_14,c_23]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_664,plain,
% 2.80/0.95      ( ~ v1_funct_2(sK4,k1_xboole_0,X0)
% 2.80/0.95      | k1_relset_1(k1_xboole_0,X0,sK4) = k1_xboole_0
% 2.80/0.95      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 2.80/0.95      inference(unflattening,[status(thm)],[c_663]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_1145,plain,
% 2.80/0.95      ( k1_relset_1(k1_xboole_0,X0,sK4) = k1_xboole_0
% 2.80/0.95      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.80/0.95      | sK2 != X0
% 2.80/0.95      | sK1 != k1_xboole_0
% 2.80/0.95      | sK4 != sK4 ),
% 2.80/0.95      inference(resolution_lifted,[status(thm)],[c_24,c_664]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_1146,plain,
% 2.80/0.95      ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
% 2.80/0.95      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.80/0.95      | sK1 != k1_xboole_0 ),
% 2.80/0.95      inference(unflattening,[status(thm)],[c_1145]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_4042,plain,
% 2.80/0.95      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
% 2.80/0.95      | k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
% 2.80/0.95      | sK1 != k1_xboole_0 ),
% 2.80/0.95      inference(demodulation,[status(thm)],[c_4023,c_1146]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_4059,plain,
% 2.80/0.95      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
% 2.80/0.95      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
% 2.80/0.95      | k1_xboole_0 != k1_xboole_0 ),
% 2.80/0.95      inference(light_normalisation,[status(thm)],[c_4042,c_4046]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_4060,plain,
% 2.80/0.95      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0 ),
% 2.80/0.95      inference(equality_resolution_simp,[status(thm)],[c_4059]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_4070,plain,
% 2.80/0.95      ( k1_relat_1(sK4) = k1_xboole_0 ),
% 2.80/0.95      inference(light_normalisation,[status(thm)],[c_4039,c_4046,c_4060]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_4192,plain,
% 2.80/0.95      ( k1_funct_1(sK3,sK0(sK3,sK4)) = k1_funct_1(sK4,sK0(sK3,sK4))
% 2.80/0.95      | r1_partfun1(sK3,sK4) = iProver_top
% 2.80/0.95      | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top
% 2.80/0.95      | v1_funct_1(sK4) != iProver_top
% 2.80/0.95      | v1_relat_1(sK4) != iProver_top ),
% 2.80/0.95      inference(superposition,[status(thm)],[c_4070,c_3371]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_3,plain,
% 2.80/0.95      ( r1_tarski(k1_xboole_0,X0) ),
% 2.80/0.95      inference(cnf_transformation,[],[f41]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_82,plain,
% 2.80/0.95      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 2.80/0.95      inference(instantiation,[status(thm)],[c_3]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_0,plain,
% 2.80/0.95      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 2.80/0.95      inference(cnf_transformation,[],[f40]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_87,plain,
% 2.80/0.95      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 2.80/0.95      | k1_xboole_0 = k1_xboole_0 ),
% 2.80/0.95      inference(instantiation,[status(thm)],[c_0]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_537,plain,
% 2.80/0.95      ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.80/0.95      | r1_tarski(k1_relat_1(sK3),k1_xboole_0) = iProver_top
% 2.80/0.95      | v1_relat_1(sK3) != iProver_top ),
% 2.80/0.95      inference(instantiation,[status(thm)],[c_535]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_1314,plain,
% 2.80/0.95      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 2.80/0.95      theory(equality) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_1903,plain,
% 2.80/0.95      ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK1,sK2)
% 2.80/0.95      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 2.80/0.95      inference(instantiation,[status(thm)],[c_1314]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_1904,plain,
% 2.80/0.95      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k2_zfmisc_1(sK1,sK2)
% 2.80/0.95      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 2.80/0.95      inference(instantiation,[status(thm)],[c_1903]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_1311,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_1938,plain,
% 2.80/0.95      ( sK2 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK2 ),
% 2.80/0.95      inference(instantiation,[status(thm)],[c_1311]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_1939,plain,
% 2.80/0.95      ( sK2 != k1_xboole_0
% 2.80/0.95      | k1_xboole_0 = sK2
% 2.80/0.95      | k1_xboole_0 != k1_xboole_0 ),
% 2.80/0.95      inference(instantiation,[status(thm)],[c_1938]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_11,plain,
% 2.80/0.95      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 2.80/0.95      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 2.80/0.95      | k1_xboole_0 = X1
% 2.80/0.95      | k1_xboole_0 = X0 ),
% 2.80/0.95      inference(cnf_transformation,[],[f70]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_627,plain,
% 2.80/0.95      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 2.80/0.95      | k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.80/0.95      | sK4 != X0
% 2.80/0.95      | k1_xboole_0 = X0
% 2.80/0.95      | k1_xboole_0 = X1 ),
% 2.80/0.95      inference(resolution_lifted,[status(thm)],[c_11,c_23]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_628,plain,
% 2.80/0.95      ( ~ v1_funct_2(sK4,X0,k1_xboole_0)
% 2.80/0.95      | k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.80/0.95      | k1_xboole_0 = X0
% 2.80/0.95      | k1_xboole_0 = sK4 ),
% 2.80/0.95      inference(unflattening,[status(thm)],[c_627]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_1114,plain,
% 2.80/0.95      ( k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.80/0.95      | sK2 != k1_xboole_0
% 2.80/0.95      | sK1 != X0
% 2.80/0.95      | sK4 != sK4
% 2.80/0.95      | sK4 = k1_xboole_0
% 2.80/0.95      | k1_xboole_0 = X0 ),
% 2.80/0.95      inference(resolution_lifted,[status(thm)],[c_24,c_628]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_1115,plain,
% 2.80/0.95      ( k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.80/0.95      | sK2 != k1_xboole_0
% 2.80/0.95      | sK4 = k1_xboole_0
% 2.80/0.95      | k1_xboole_0 = sK1 ),
% 2.80/0.95      inference(unflattening,[status(thm)],[c_1114]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_2016,plain,
% 2.80/0.95      ( sK2 != k1_xboole_0 | k1_xboole_0 = sK1 ),
% 2.80/0.95      inference(global_propositional_subsumption,
% 2.80/0.95                [status(thm)],
% 2.80/0.95                [c_1115,c_22,c_82,c_87,c_1939]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_1316,plain,
% 2.80/0.95      ( X0 != X1 | X2 != X3 | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
% 2.80/0.95      theory(equality) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_2141,plain,
% 2.80/0.95      ( X0 != sK2
% 2.80/0.95      | X1 != sK1
% 2.80/0.95      | k2_zfmisc_1(X1,X0) = k2_zfmisc_1(sK1,sK2) ),
% 2.80/0.95      inference(instantiation,[status(thm)],[c_1316]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_2142,plain,
% 2.80/0.95      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k2_zfmisc_1(sK1,sK2)
% 2.80/0.95      | k1_xboole_0 != sK2
% 2.80/0.95      | k1_xboole_0 != sK1 ),
% 2.80/0.95      inference(instantiation,[status(thm)],[c_2141]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_5582,plain,
% 2.80/0.95      ( r1_partfun1(sK3,sK4) = iProver_top
% 2.80/0.95      | k1_funct_1(sK3,sK0(sK3,sK4)) = k1_funct_1(sK4,sK0(sK3,sK4)) ),
% 2.80/0.95      inference(global_propositional_subsumption,
% 2.80/0.95                [status(thm)],
% 2.80/0.95                [c_4192,c_30,c_82,c_87,c_537,c_1904,c_1939,c_2016,c_2142,
% 2.80/0.95                 c_2328,c_2334,c_2337,c_2572,c_3987]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_5583,plain,
% 2.80/0.95      ( k1_funct_1(sK3,sK0(sK3,sK4)) = k1_funct_1(sK4,sK0(sK3,sK4))
% 2.80/0.95      | r1_partfun1(sK3,sK4) = iProver_top ),
% 2.80/0.95      inference(renaming,[status(thm)],[c_5582]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_4193,plain,
% 2.80/0.95      ( k1_funct_1(X0,X1) = k1_funct_1(sK4,X1)
% 2.80/0.95      | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
% 2.80/0.95      | r1_partfun1(X0,sK4) != iProver_top
% 2.80/0.95      | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
% 2.80/0.95      | v1_funct_1(X0) != iProver_top
% 2.80/0.95      | v1_funct_1(sK4) != iProver_top
% 2.80/0.95      | v1_relat_1(X0) != iProver_top
% 2.80/0.95      | v1_relat_1(sK4) != iProver_top ),
% 2.80/0.95      inference(superposition,[status(thm)],[c_4070,c_1638]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_4265,plain,
% 2.80/0.95      ( v1_relat_1(X0) != iProver_top
% 2.80/0.95      | k1_funct_1(X0,X1) = k1_funct_1(sK4,X1)
% 2.80/0.95      | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
% 2.80/0.95      | r1_partfun1(X0,sK4) != iProver_top
% 2.80/0.95      | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
% 2.80/0.95      | v1_funct_1(X0) != iProver_top ),
% 2.80/0.95      inference(global_propositional_subsumption,
% 2.80/0.95                [status(thm)],
% 2.80/0.95                [c_4193,c_30,c_2334,c_2337]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_4266,plain,
% 2.80/0.95      ( k1_funct_1(X0,X1) = k1_funct_1(sK4,X1)
% 2.80/0.95      | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
% 2.80/0.95      | r1_partfun1(X0,sK4) != iProver_top
% 2.80/0.95      | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
% 2.80/0.95      | v1_funct_1(X0) != iProver_top
% 2.80/0.95      | v1_relat_1(X0) != iProver_top ),
% 2.80/0.95      inference(renaming,[status(thm)],[c_4265]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_4278,plain,
% 2.80/0.95      ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
% 2.80/0.95      | r1_partfun1(sK3,sK4) != iProver_top
% 2.80/0.95      | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top
% 2.80/0.95      | v1_funct_1(sK3) != iProver_top
% 2.80/0.95      | v1_relat_1(sK3) != iProver_top ),
% 2.80/0.95      inference(superposition,[status(thm)],[c_2271,c_4266]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_4402,plain,
% 2.80/0.95      ( r1_partfun1(sK3,sK4) != iProver_top
% 2.80/0.95      | k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5) ),
% 2.80/0.95      inference(global_propositional_subsumption,
% 2.80/0.95                [status(thm)],
% 2.80/0.95                [c_4278,c_28,c_82,c_87,c_537,c_1904,c_1939,c_2016,c_2142,
% 2.80/0.95                 c_2328,c_2337,c_2572,c_3987]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_4403,plain,
% 2.80/0.95      ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
% 2.80/0.95      | r1_partfun1(sK3,sK4) != iProver_top ),
% 2.80/0.95      inference(renaming,[status(thm)],[c_4402]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_5589,plain,
% 2.80/0.95      ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
% 2.80/0.95      | k1_funct_1(sK3,sK0(sK3,sK4)) = k1_funct_1(sK4,sK0(sK3,sK4)) ),
% 2.80/0.95      inference(superposition,[status(thm)],[c_5583,c_4403]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_6281,plain,
% 2.80/0.95      ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
% 2.80/0.95      | r1_partfun1(sK3,sK4) = iProver_top
% 2.80/0.95      | r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4)) != iProver_top
% 2.80/0.95      | v1_funct_1(sK4) != iProver_top
% 2.80/0.95      | v1_funct_1(sK3) != iProver_top
% 2.80/0.95      | v1_relat_1(sK4) != iProver_top
% 2.80/0.95      | v1_relat_1(sK3) != iProver_top ),
% 2.80/0.95      inference(superposition,[status(thm)],[c_5589,c_1640]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_4135,plain,
% 2.80/0.95      ( r1_tarski(k1_relat_1(sK3),k1_xboole_0) = iProver_top ),
% 2.80/0.95      inference(demodulation,[status(thm)],[c_4046,c_2572]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_1642,plain,
% 2.80/0.95      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.80/0.95      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_1644,plain,
% 2.80/0.95      ( X0 = X1
% 2.80/0.95      | r1_tarski(X0,X1) != iProver_top
% 2.80/0.95      | r1_tarski(X1,X0) != iProver_top ),
% 2.80/0.95      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_2159,plain,
% 2.80/0.95      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 2.80/0.95      inference(superposition,[status(thm)],[c_1642,c_1644]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_4350,plain,
% 2.80/0.95      ( k1_relat_1(sK3) = k1_xboole_0 ),
% 2.80/0.95      inference(superposition,[status(thm)],[c_4135,c_2159]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_6282,plain,
% 2.80/0.95      ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
% 2.80/0.95      | r1_partfun1(sK3,sK4) = iProver_top
% 2.80/0.95      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 2.80/0.95      | v1_funct_1(sK4) != iProver_top
% 2.80/0.95      | v1_funct_1(sK3) != iProver_top
% 2.80/0.95      | v1_relat_1(sK4) != iProver_top
% 2.80/0.95      | v1_relat_1(sK3) != iProver_top ),
% 2.80/0.95      inference(light_normalisation,[status(thm)],[c_6281,c_4070,c_4350]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_81,plain,
% 2.80/0.95      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.80/0.95      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_83,plain,
% 2.80/0.95      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 2.80/0.95      inference(instantiation,[status(thm)],[c_81]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_6290,plain,
% 2.80/0.95      ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5) ),
% 2.80/0.95      inference(global_propositional_subsumption,
% 2.80/0.95                [status(thm)],
% 2.80/0.95                [c_6282,c_28,c_30,c_83,c_2328,c_2334,c_2337,c_4403]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_6293,plain,
% 2.80/0.95      ( k1_funct_1(sK3,sK5) != k1_funct_1(sK3,sK5)
% 2.80/0.95      | r1_partfun1(sK3,sK4) != iProver_top ),
% 2.80/0.95      inference(demodulation,[status(thm)],[c_6290,c_1637]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_6352,plain,
% 2.80/0.95      ( r1_partfun1(sK3,sK4) != iProver_top ),
% 2.80/0.95      inference(equality_resolution_simp,[status(thm)],[c_6293]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_6355,plain,
% 2.80/0.95      ( k1_funct_1(sK3,sK0(sK3,sK4)) = k1_funct_1(sK4,sK0(sK3,sK4)) ),
% 2.80/0.95      inference(superposition,[status(thm)],[c_5583,c_6352]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_6366,plain,
% 2.80/0.95      ( r1_partfun1(sK3,sK4) = iProver_top
% 2.80/0.95      | r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4)) != iProver_top
% 2.80/0.95      | v1_funct_1(sK4) != iProver_top
% 2.80/0.95      | v1_funct_1(sK3) != iProver_top
% 2.80/0.95      | v1_relat_1(sK4) != iProver_top
% 2.80/0.95      | v1_relat_1(sK3) != iProver_top ),
% 2.80/0.95      inference(superposition,[status(thm)],[c_6355,c_1640]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(c_6367,plain,
% 2.80/0.95      ( r1_partfun1(sK3,sK4) = iProver_top
% 2.80/0.95      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 2.80/0.95      | v1_funct_1(sK4) != iProver_top
% 2.80/0.95      | v1_funct_1(sK3) != iProver_top
% 2.80/0.95      | v1_relat_1(sK4) != iProver_top
% 2.80/0.95      | v1_relat_1(sK3) != iProver_top ),
% 2.80/0.95      inference(light_normalisation,[status(thm)],[c_6366,c_4070,c_4350]) ).
% 2.80/0.95  
% 2.80/0.95  cnf(contradiction,plain,
% 2.80/0.95      ( $false ),
% 2.80/0.95      inference(minisat,
% 2.80/0.95                [status(thm)],
% 2.80/0.95                [c_6367,c_6352,c_2337,c_2334,c_2328,c_83,c_30,c_28]) ).
% 2.80/0.95  
% 2.80/0.95  
% 2.80/0.95  % SZS output end CNFRefutation for theBenchmark.p
% 2.80/0.95  
% 2.80/0.95  ------                               Statistics
% 2.80/0.95  
% 2.80/0.95  ------ General
% 2.80/0.95  
% 2.80/0.95  abstr_ref_over_cycles:                  0
% 2.80/0.95  abstr_ref_under_cycles:                 0
% 2.80/0.95  gc_basic_clause_elim:                   0
% 2.80/0.95  forced_gc_time:                         0
% 2.80/0.95  parsing_time:                           0.009
% 2.80/0.95  unif_index_cands_time:                  0.
% 2.80/0.95  unif_index_add_time:                    0.
% 2.80/0.95  orderings_time:                         0.
% 2.80/0.95  out_proof_time:                         0.02
% 2.80/0.95  total_time:                             0.236
% 2.80/0.95  num_of_symbols:                         51
% 2.80/0.95  num_of_terms:                           3240
% 2.80/0.95  
% 2.80/0.95  ------ Preprocessing
% 2.80/0.95  
% 2.80/0.95  num_of_splits:                          0
% 2.80/0.95  num_of_split_atoms:                     0
% 2.80/0.95  num_of_reused_defs:                     0
% 2.80/0.95  num_eq_ax_congr_red:                    7
% 2.80/0.95  num_of_sem_filtered_clauses:            1
% 2.80/0.95  num_of_subtypes:                        0
% 2.80/0.95  monotx_restored_types:                  0
% 2.80/0.95  sat_num_of_epr_types:                   0
% 2.80/0.95  sat_num_of_non_cyclic_types:            0
% 2.80/0.95  sat_guarded_non_collapsed_types:        0
% 2.80/0.95  num_pure_diseq_elim:                    0
% 2.80/0.95  simp_replaced_by:                       0
% 2.80/0.95  res_preprocessed:                       110
% 2.80/0.95  prep_upred:                             0
% 2.80/0.95  prep_unflattend:                        100
% 2.80/0.95  smt_new_axioms:                         0
% 2.80/0.95  pred_elim_cands:                        8
% 2.80/0.95  pred_elim:                              3
% 2.80/0.95  pred_elim_cl:                           -2
% 2.80/0.95  pred_elim_cycles:                       6
% 2.80/0.95  merged_defs:                            0
% 2.80/0.95  merged_defs_ncl:                        0
% 2.80/0.95  bin_hyper_res:                          0
% 2.80/0.95  prep_cycles:                            3
% 2.80/0.95  pred_elim_time:                         0.026
% 2.80/0.95  splitting_time:                         0.
% 2.80/0.95  sem_filter_time:                        0.
% 2.80/0.95  monotx_time:                            0.001
% 2.80/0.95  subtype_inf_time:                       0.
% 2.80/0.95  
% 2.80/0.95  ------ Problem properties
% 2.80/0.95  
% 2.80/0.95  clauses:                                29
% 2.80/0.95  conjectures:                            6
% 2.80/0.95  epr:                                    6
% 2.80/0.95  horn:                                   21
% 2.80/0.95  ground:                                 11
% 2.80/0.95  unary:                                  5
% 2.80/0.95  binary:                                 5
% 2.80/0.95  lits:                                   96
% 2.80/0.95  lits_eq:                                56
% 2.80/0.95  fd_pure:                                0
% 2.80/0.95  fd_pseudo:                              0
% 2.80/0.95  fd_cond:                                0
% 2.80/0.95  fd_pseudo_cond:                         1
% 2.80/0.95  ac_symbols:                             0
% 2.80/0.95  
% 2.80/0.95  ------ Propositional Solver
% 2.80/0.95  
% 2.80/0.95  prop_solver_calls:                      25
% 2.80/0.95  prop_fast_solver_calls:                 1367
% 2.80/0.95  smt_solver_calls:                       0
% 2.80/0.95  smt_fast_solver_calls:                  0
% 2.80/0.95  prop_num_of_clauses:                    1871
% 2.80/0.95  prop_preprocess_simplified:             4942
% 2.80/0.95  prop_fo_subsumed:                       71
% 2.80/0.95  prop_solver_time:                       0.
% 2.80/0.95  smt_solver_time:                        0.
% 2.80/0.95  smt_fast_solver_time:                   0.
% 2.80/0.95  prop_fast_solver_time:                  0.
% 2.80/0.95  prop_unsat_core_time:                   0.
% 2.80/0.95  
% 2.80/0.95  ------ QBF
% 2.80/0.95  
% 2.80/0.95  qbf_q_res:                              0
% 2.80/0.95  qbf_num_tautologies:                    0
% 2.80/0.95  qbf_prep_cycles:                        0
% 2.80/0.95  
% 2.80/0.95  ------ BMC1
% 2.80/0.95  
% 2.80/0.95  bmc1_current_bound:                     -1
% 2.80/0.95  bmc1_last_solved_bound:                 -1
% 2.80/0.95  bmc1_unsat_core_size:                   -1
% 2.80/0.95  bmc1_unsat_core_parents_size:           -1
% 2.80/0.95  bmc1_merge_next_fun:                    0
% 2.80/0.95  bmc1_unsat_core_clauses_time:           0.
% 2.80/0.95  
% 2.80/0.95  ------ Instantiation
% 2.80/0.95  
% 2.80/0.95  inst_num_of_clauses:                    578
% 2.80/0.95  inst_num_in_passive:                    211
% 2.80/0.95  inst_num_in_active:                     352
% 2.80/0.95  inst_num_in_unprocessed:                15
% 2.80/0.95  inst_num_of_loops:                      430
% 2.80/0.95  inst_num_of_learning_restarts:          0
% 2.80/0.95  inst_num_moves_active_passive:          74
% 2.80/0.95  inst_lit_activity:                      0
% 2.80/0.95  inst_lit_activity_moves:                0
% 2.80/0.95  inst_num_tautologies:                   0
% 2.80/0.95  inst_num_prop_implied:                  0
% 2.80/0.95  inst_num_existing_simplified:           0
% 2.80/0.95  inst_num_eq_res_simplified:             0
% 2.80/0.95  inst_num_child_elim:                    0
% 2.80/0.95  inst_num_of_dismatching_blockings:      210
% 2.80/0.95  inst_num_of_non_proper_insts:           762
% 2.80/0.95  inst_num_of_duplicates:                 0
% 2.80/0.95  inst_inst_num_from_inst_to_res:         0
% 2.80/0.95  inst_dismatching_checking_time:         0.
% 2.80/0.95  
% 2.80/0.95  ------ Resolution
% 2.80/0.95  
% 2.80/0.95  res_num_of_clauses:                     0
% 2.80/0.95  res_num_in_passive:                     0
% 2.80/0.95  res_num_in_active:                      0
% 2.80/0.95  res_num_of_loops:                       113
% 2.80/0.95  res_forward_subset_subsumed:            99
% 2.80/0.95  res_backward_subset_subsumed:           0
% 2.80/0.95  res_forward_subsumed:                   4
% 2.80/0.95  res_backward_subsumed:                  0
% 2.80/0.95  res_forward_subsumption_resolution:     0
% 2.80/0.95  res_backward_subsumption_resolution:    0
% 2.80/0.95  res_clause_to_clause_subsumption:       395
% 2.80/0.95  res_orphan_elimination:                 0
% 2.80/0.95  res_tautology_del:                      81
% 2.80/0.95  res_num_eq_res_simplified:              2
% 2.80/0.95  res_num_sel_changes:                    0
% 2.80/0.95  res_moves_from_active_to_pass:          0
% 2.80/0.95  
% 2.80/0.95  ------ Superposition
% 2.80/0.95  
% 2.80/0.95  sup_time_total:                         0.
% 2.80/0.95  sup_time_generating:                    0.
% 2.80/0.95  sup_time_sim_full:                      0.
% 2.80/0.95  sup_time_sim_immed:                     0.
% 2.80/0.95  
% 2.80/0.95  sup_num_of_clauses:                     49
% 2.80/0.95  sup_num_in_active:                      37
% 2.80/0.95  sup_num_in_passive:                     12
% 2.80/0.95  sup_num_of_loops:                       85
% 2.80/0.95  sup_fw_superposition:                   43
% 2.80/0.95  sup_bw_superposition:                   30
% 2.80/0.95  sup_immediate_simplified:               45
% 2.80/0.95  sup_given_eliminated:                   1
% 2.80/0.95  comparisons_done:                       0
% 2.80/0.95  comparisons_avoided:                    36
% 2.80/0.95  
% 2.80/0.95  ------ Simplifications
% 2.80/0.95  
% 2.80/0.95  
% 2.80/0.95  sim_fw_subset_subsumed:                 10
% 2.80/0.95  sim_bw_subset_subsumed:                 20
% 2.80/0.95  sim_fw_subsumed:                        13
% 2.80/0.95  sim_bw_subsumed:                        0
% 2.80/0.95  sim_fw_subsumption_res:                 5
% 2.80/0.95  sim_bw_subsumption_res:                 0
% 2.80/0.95  sim_tautology_del:                      4
% 2.80/0.95  sim_eq_tautology_del:                   15
% 2.80/0.95  sim_eq_res_simp:                        7
% 2.80/0.95  sim_fw_demodulated:                     4
% 2.80/0.95  sim_bw_demodulated:                     37
% 2.80/0.95  sim_light_normalised:                   25
% 2.80/0.95  sim_joinable_taut:                      0
% 2.80/0.95  sim_joinable_simp:                      0
% 2.80/0.95  sim_ac_normalised:                      0
% 2.80/0.95  sim_smt_subsumption:                    0
% 2.80/0.95  
%------------------------------------------------------------------------------
