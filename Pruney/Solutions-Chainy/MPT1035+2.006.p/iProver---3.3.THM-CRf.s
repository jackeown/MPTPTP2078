%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:08:40 EST 2020

% Result     : Theorem 2.32s
% Output     : CNFRefutation 2.32s
% Verified   : 
% Statistics : Number of formulae       :  219 (206715 expanded)
%              Number of clauses        :  156 (60889 expanded)
%              Number of leaves         :   17 (47949 expanded)
%              Depth                    :   59
%              Number of atoms          :  857 (1619350 expanded)
%              Number of equality atoms :  534 (548829 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    3 (   2 average)

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f20,plain,(
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
    inference(flattening,[],[f20])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f21])).

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
    inference(flattening,[],[f30])).

fof(f32,plain,(
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
    inference(rectify,[],[f31])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
          & r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
     => ( k1_funct_1(X2,sK5) != k1_funct_1(X3,sK5)
        & r2_hidden(sK5,k1_relset_1(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
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

fof(f33,plain,
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

fof(f36,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f32,f35,f34,f33])).

fof(f58,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f36])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
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
    inference(flattening,[],[f16])).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f59,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f36])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
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
    inference(flattening,[],[f18])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f27,plain,(
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
    inference(rectify,[],[f26])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1))
        & r2_hidden(sK0(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_partfun1(X0,X1)
      | r2_hidden(sK0(X0,X1),k1_relat_1(X0))
      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f56,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f36])).

fof(f61,plain,(
    ! [X5] :
      ( k1_funct_1(sK3,X5) = k1_funct_1(sK4,X5)
      | ~ r2_hidden(X5,k1_relset_1(sK1,sK2,sK3))
      | r1_partfun1(sK3,sK4) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f55,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f57,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f36])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f62,plain,
    ( r2_hidden(sK5,k1_relset_1(sK1,sK2,sK3))
    | ~ r1_partfun1(sK3,sK4) ),
    inference(cnf_transformation,[],[f36])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ r1_partfun1(X0,X1)
      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_partfun1(X0,X1)
      | k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1))
      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f63,plain,
    ( k1_funct_1(sK3,sK5) != k1_funct_1(sK4,sK5)
    | ~ r1_partfun1(sK3,sK4) ),
    inference(cnf_transformation,[],[f36])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f70,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f47])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f22])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f65,plain,(
    ! [X1] : k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(equality_resolution,[],[f38])).

fof(f60,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f36])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f68,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f50])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f64,plain,(
    ! [X0] : k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[],[f39])).

cnf(c_23,negated_conjecture,
    ( v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_587,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_22])).

cnf(c_588,plain,
    ( ~ v1_funct_2(sK4,X0,X1)
    | k1_relset_1(X0,X1,sK4) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_587])).

cnf(c_1448,plain,
    ( k1_relset_1(X0,X1,sK4) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sK2 != X1
    | sK1 != X0
    | sK4 != sK4
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_588])).

cnf(c_1449,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_1448])).

cnf(c_2007,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(equality_resolution_simp,[status(thm)],[c_1449])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_623,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_22])).

cnf(c_624,plain,
    ( k1_relset_1(X0,X1,sK4) = k1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(unflattening,[status(thm)],[c_623])).

cnf(c_2227,plain,
    ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
    inference(equality_resolution,[status(thm)],[c_624])).

cnf(c_2909,plain,
    ( k1_relat_1(sK4) = sK1
    | sK2 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2007,c_2227])).

cnf(c_16,plain,
    ( r2_hidden(sK0(X0,X1),k1_relat_1(X0))
    | r1_partfun1(X0,X1)
    | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1956,plain,
    ( r2_hidden(sK0(X0,X1),k1_relat_1(X0)) = iProver_top
    | r1_partfun1(X0,X1) = iProver_top
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_683,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_25])).

cnf(c_684,plain,
    ( k1_relset_1(X0,X1,sK3) = k1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(unflattening,[status(thm)],[c_683])).

cnf(c_2268,plain,
    ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
    inference(equality_resolution,[status(thm)],[c_684])).

cnf(c_20,negated_conjecture,
    ( ~ r2_hidden(X0,k1_relset_1(sK1,sK2,sK3))
    | r1_partfun1(sK3,sK4)
    | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1952,plain,
    ( k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0)
    | r2_hidden(X0,k1_relset_1(sK1,sK2,sK3)) != iProver_top
    | r1_partfun1(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2460,plain,
    ( k1_funct_1(sK4,X0) = k1_funct_1(sK3,X0)
    | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | r1_partfun1(sK3,sK4) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2268,c_1952])).

cnf(c_3327,plain,
    ( k1_funct_1(sK3,sK0(sK3,X0)) = k1_funct_1(sK4,sK0(sK3,X0))
    | r1_partfun1(sK3,X0) = iProver_top
    | r1_partfun1(sK3,sK4) = iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1956,c_2460])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_27,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_557,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_25])).

cnf(c_558,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_557])).

cnf(c_1948,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(X0)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_558])).

cnf(c_2608,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1948])).

cnf(c_6,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_2636,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2637,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2636])).

cnf(c_3530,plain,
    ( v1_relat_1(X0) != iProver_top
    | k1_funct_1(sK3,sK0(sK3,X0)) = k1_funct_1(sK4,sK0(sK3,X0))
    | r1_partfun1(sK3,X0) = iProver_top
    | r1_partfun1(sK3,sK4) = iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3327,c_27,c_2608,c_2637])).

cnf(c_3531,plain,
    ( k1_funct_1(sK3,sK0(sK3,X0)) = k1_funct_1(sK4,sK0(sK3,X0))
    | r1_partfun1(sK3,X0) = iProver_top
    | r1_partfun1(sK3,sK4) = iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3530])).

cnf(c_3542,plain,
    ( k1_funct_1(sK3,sK0(sK3,sK4)) = k1_funct_1(sK4,sK0(sK3,sK4))
    | sK2 = k1_xboole_0
    | r1_partfun1(sK3,sK4) = iProver_top
    | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2909,c_3531])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_29,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_1669,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2211,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_1669])).

cnf(c_542,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_22])).

cnf(c_543,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_542])).

cnf(c_2202,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(X0,X1))
    | v1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_543])).

cnf(c_2428,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK2))
    | v1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_2202])).

cnf(c_2429,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2428])).

cnf(c_7,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_5,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_261,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_7,c_5])).

cnf(c_632,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_261,c_25])).

cnf(c_633,plain,
    ( r1_tarski(k1_relat_1(sK3),X0)
    | ~ v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(unflattening,[status(thm)],[c_632])).

cnf(c_1946,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | r1_tarski(k1_relat_1(sK3),X0) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_633])).

cnf(c_634,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | r1_tarski(k1_relat_1(sK3),X0) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_633])).

cnf(c_2782,plain,
    ( r1_tarski(k1_relat_1(sK3),X0) = iProver_top
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1946,c_634,c_2608,c_2637])).

cnf(c_2783,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | r1_tarski(k1_relat_1(sK3),X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_2782])).

cnf(c_2792,plain,
    ( r1_tarski(k1_relat_1(sK3),sK1) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2783])).

cnf(c_3606,plain,
    ( r1_partfun1(sK3,sK4) = iProver_top
    | sK2 = k1_xboole_0
    | k1_funct_1(sK3,sK0(sK3,sK4)) = k1_funct_1(sK4,sK0(sK3,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3542,c_29,c_2211,c_2429,c_2637,c_2792])).

cnf(c_3607,plain,
    ( k1_funct_1(sK3,sK0(sK3,sK4)) = k1_funct_1(sK4,sK0(sK3,sK4))
    | sK2 = k1_xboole_0
    | r1_partfun1(sK3,sK4) = iProver_top ),
    inference(renaming,[status(thm)],[c_3606])).

cnf(c_19,negated_conjecture,
    ( r2_hidden(sK5,k1_relset_1(sK1,sK2,sK3))
    | ~ r1_partfun1(sK3,sK4) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1953,plain,
    ( r2_hidden(sK5,k1_relset_1(sK1,sK2,sK3)) = iProver_top
    | r1_partfun1(sK3,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2461,plain,
    ( r2_hidden(sK5,k1_relat_1(sK3)) = iProver_top
    | r1_partfun1(sK3,sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2268,c_1953])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r1_partfun1(X1,X2)
    | ~ r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = k1_funct_1(X1,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1955,plain,
    ( k1_funct_1(X0,X1) = k1_funct_1(X2,X1)
    | r2_hidden(X1,k1_relat_1(X2)) != iProver_top
    | r1_partfun1(X2,X0) != iProver_top
    | r1_tarski(k1_relat_1(X2),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3037,plain,
    ( k1_funct_1(X0,X1) = k1_funct_1(sK4,X1)
    | sK2 = k1_xboole_0
    | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
    | r1_partfun1(X0,sK4) != iProver_top
    | r1_tarski(k1_relat_1(X0),sK1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2909,c_1955])).

cnf(c_3655,plain,
    ( v1_relat_1(X0) != iProver_top
    | k1_funct_1(X0,X1) = k1_funct_1(sK4,X1)
    | sK2 = k1_xboole_0
    | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
    | r1_partfun1(X0,sK4) != iProver_top
    | r1_tarski(k1_relat_1(X0),sK1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3037,c_29,c_2211,c_2429,c_2637])).

cnf(c_3656,plain,
    ( k1_funct_1(X0,X1) = k1_funct_1(sK4,X1)
    | sK2 = k1_xboole_0
    | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
    | r1_partfun1(X0,sK4) != iProver_top
    | r1_tarski(k1_relat_1(X0),sK1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3655])).

cnf(c_3669,plain,
    ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
    | sK2 = k1_xboole_0
    | r1_partfun1(sK3,sK4) != iProver_top
    | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2461,c_3656])).

cnf(c_3706,plain,
    ( r1_partfun1(sK3,sK4) != iProver_top
    | sK2 = k1_xboole_0
    | k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3669,c_27,c_2608,c_2637,c_2792])).

cnf(c_3707,plain,
    ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
    | sK2 = k1_xboole_0
    | r1_partfun1(sK3,sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_3706])).

cnf(c_3713,plain,
    ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
    | k1_funct_1(sK3,sK0(sK3,sK4)) = k1_funct_1(sK4,sK0(sK3,sK4))
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3607,c_3707])).

cnf(c_15,plain,
    ( r1_partfun1(X0,X1)
    | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK0(X0,X1)) != k1_funct_1(X0,sK0(X0,X1)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1957,plain,
    ( k1_funct_1(X0,sK0(X1,X0)) != k1_funct_1(X1,sK0(X1,X0))
    | r1_partfun1(X1,X0) = iProver_top
    | r1_tarski(k1_relat_1(X1),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3762,plain,
    ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
    | sK2 = k1_xboole_0
    | r1_partfun1(sK3,sK4) = iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3713,c_1957])).

cnf(c_3802,plain,
    ( sK2 = k1_xboole_0
    | k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3762,c_27,c_29,c_2211,c_2429,c_2608,c_2637,c_2792,c_3669])).

cnf(c_3803,plain,
    ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
    | sK2 = k1_xboole_0
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3802])).

cnf(c_3809,plain,
    ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
    | sK2 = k1_xboole_0
    | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2909,c_3803])).

cnf(c_3812,plain,
    ( sK2 = k1_xboole_0
    | k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3809,c_2792])).

cnf(c_3813,plain,
    ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
    | sK2 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_3812])).

cnf(c_18,negated_conjecture,
    ( ~ r1_partfun1(sK3,sK4)
    | k1_funct_1(sK3,sK5) != k1_funct_1(sK4,sK5) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1954,plain,
    ( k1_funct_1(sK3,sK5) != k1_funct_1(sK4,sK5)
    | r1_partfun1(sK3,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3816,plain,
    ( sK2 = k1_xboole_0
    | r1_partfun1(sK3,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3813,c_1954])).

cnf(c_3858,plain,
    ( k1_funct_1(sK3,sK0(sK3,sK4)) = k1_funct_1(sK4,sK0(sK3,sK4))
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3607,c_3816])).

cnf(c_3861,plain,
    ( sK2 = k1_xboole_0
    | r1_partfun1(sK3,sK4) = iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3858,c_1957])).

cnf(c_3976,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3861,c_27,c_29,c_2211,c_2429,c_2608,c_2637,c_3816])).

cnf(c_3982,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2909,c_3976])).

cnf(c_3985,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3982,c_2792])).

cnf(c_13,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_762,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_22])).

cnf(c_763,plain,
    ( ~ v1_funct_2(sK4,k1_xboole_0,X0)
    | k1_relset_1(k1_xboole_0,X0,sK4) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(unflattening,[status(thm)],[c_762])).

cnf(c_1504,plain,
    ( k1_relset_1(k1_xboole_0,X0,sK4) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sK2 != X0
    | sK1 != k1_xboole_0
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_763])).

cnf(c_1505,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sK1 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_1504])).

cnf(c_1,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2012,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k1_xboole_0)
    | sK1 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1505,c_1])).

cnf(c_4000,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)) != k1_zfmisc_1(k1_xboole_0)
    | sK1 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3985,c_2012])).

cnf(c_21,negated_conjecture,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_4012,plain,
    ( sK1 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3985,c_21])).

cnf(c_4013,plain,
    ( sK1 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_4012])).

cnf(c_4082,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4000,c_4013])).

cnf(c_4083,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k1_xboole_0) ),
    inference(equality_resolution_simp,[status(thm)],[c_4082])).

cnf(c_2376,plain,
    ( k1_relset_1(k1_xboole_0,X0,sK4) = k1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1,c_624])).

cnf(c_4003,plain,
    ( k1_relset_1(k1_xboole_0,X0,sK4) = k1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)) != k1_zfmisc_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_3985,c_2376])).

cnf(c_4064,plain,
    ( k1_relset_1(k1_xboole_0,X0,sK4) = k1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_4003,c_4013])).

cnf(c_4067,plain,
    ( k1_relset_1(k1_xboole_0,X0,sK4) = k1_relat_1(sK4)
    | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_4064,c_1])).

cnf(c_4068,plain,
    ( k1_relset_1(k1_xboole_0,X0,sK4) = k1_relat_1(sK4) ),
    inference(equality_resolution_simp,[status(thm)],[c_4067])).

cnf(c_4084,plain,
    ( k1_relat_1(sK4) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_4083,c_4068])).

cnf(c_4087,plain,
    ( k1_relat_1(sK4) = k1_xboole_0
    | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_4084,c_1])).

cnf(c_4088,plain,
    ( k1_relat_1(sK4) = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_4087])).

cnf(c_4375,plain,
    ( k1_funct_1(sK3,sK0(sK3,sK4)) = k1_funct_1(sK4,sK0(sK3,sK4))
    | r1_partfun1(sK3,sK4) = iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4088,c_3531])).

cnf(c_2,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_80,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_81,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_636,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | r1_tarski(k1_relat_1(sK3),k1_xboole_0) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_634])).

cnf(c_1673,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_2220,plain,
    ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK1,sK2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_1673])).

cnf(c_2221,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k2_zfmisc_1(sK1,sK2)
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_2220])).

cnf(c_1670,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2238,plain,
    ( sK2 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_1670])).

cnf(c_2239,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2238])).

cnf(c_1671,plain,
    ( X0 != X1
    | X2 != X3
    | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
    theory(equality)).

cnf(c_2433,plain,
    ( X0 != sK2
    | X1 != sK1
    | k2_zfmisc_1(X1,X0) = k2_zfmisc_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1671])).

cnf(c_2434,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k2_zfmisc_1(sK1,sK2)
    | k1_xboole_0 != sK2
    | k1_xboole_0 != sK1 ),
    inference(instantiation,[status(thm)],[c_2433])).

cnf(c_2599,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1670])).

cnf(c_2600,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2599])).

cnf(c_10,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_726,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sK4 != X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_22])).

cnf(c_727,plain,
    ( ~ v1_funct_2(sK4,X0,k1_xboole_0)
    | k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | k1_xboole_0 = X0
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_726])).

cnf(c_1473,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sK2 != k1_xboole_0
    | sK1 != X0
    | sK4 != sK4
    | sK4 = k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_727])).

cnf(c_1474,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sK2 != k1_xboole_0
    | sK4 = k1_xboole_0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_1473])).

cnf(c_0,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_2019,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k1_xboole_0)
    | sK2 != k1_xboole_0
    | sK1 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1474,c_0])).

cnf(c_2245,plain,
    ( sK1 != X0
    | sK1 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1670])).

cnf(c_2398,plain,
    ( sK1 != sK1
    | sK1 = k1_xboole_0
    | k1_xboole_0 != sK1 ),
    inference(instantiation,[status(thm)],[c_2245])).

cnf(c_2399,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_1669])).

cnf(c_2735,plain,
    ( sK1 = k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2019,c_21,c_80,c_81,c_2239,c_2398,c_2399])).

cnf(c_2736,plain,
    ( sK2 != k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_2735])).

cnf(c_4697,plain,
    ( r1_partfun1(sK3,sK4) = iProver_top
    | k1_funct_1(sK3,sK0(sK3,sK4)) = k1_funct_1(sK4,sK0(sK3,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4375,c_29,c_80,c_81,c_636,c_2211,c_2221,c_2239,c_2429,c_2434,c_2600,c_2608,c_2637,c_2736,c_2792,c_3982])).

cnf(c_4698,plain,
    ( k1_funct_1(sK3,sK0(sK3,sK4)) = k1_funct_1(sK4,sK0(sK3,sK4))
    | r1_partfun1(sK3,sK4) = iProver_top ),
    inference(renaming,[status(thm)],[c_4697])).

cnf(c_4379,plain,
    ( k1_funct_1(X0,X1) = k1_funct_1(sK4,X1)
    | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
    | r1_partfun1(X0,sK4) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4088,c_1955])).

cnf(c_4965,plain,
    ( v1_relat_1(X0) != iProver_top
    | k1_funct_1(X0,X1) = k1_funct_1(sK4,X1)
    | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
    | r1_partfun1(X0,sK4) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4379,c_29,c_2211,c_2429,c_2637])).

cnf(c_4966,plain,
    ( k1_funct_1(X0,X1) = k1_funct_1(sK4,X1)
    | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
    | r1_partfun1(X0,sK4) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4965])).

cnf(c_4978,plain,
    ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
    | r1_partfun1(sK3,sK4) != iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2461,c_4966])).

cnf(c_5390,plain,
    ( r1_partfun1(sK3,sK4) != iProver_top
    | k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4978,c_27,c_80,c_81,c_636,c_2221,c_2239,c_2434,c_2600,c_2608,c_2637,c_2736,c_2792,c_3982])).

cnf(c_5391,plain,
    ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
    | r1_partfun1(sK3,sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_5390])).

cnf(c_5396,plain,
    ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
    | k1_funct_1(sK3,sK0(sK3,sK4)) = k1_funct_1(sK4,sK0(sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_4698,c_5391])).

cnf(c_5535,plain,
    ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
    | r1_partfun1(sK3,sK4) = iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5396,c_1957])).

cnf(c_5536,plain,
    ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
    | r1_partfun1(sK3,sK4) = iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5535,c_4088])).

cnf(c_635,plain,
    ( r1_tarski(k1_relat_1(sK3),k1_xboole_0)
    | ~ v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_633])).

cnf(c_2609,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK2))
    | v1_relat_1(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2608])).

cnf(c_5392,plain,
    ( ~ r1_partfun1(sK3,sK4)
    | k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5391])).

cnf(c_5537,plain,
    ( r1_partfun1(sK3,sK4)
    | ~ r1_tarski(k1_relat_1(sK3),k1_xboole_0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK4)
    | ~ v1_relat_1(sK3)
    | k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5536])).

cnf(c_5851,plain,
    ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5536,c_26,c_24,c_80,c_81,c_635,c_2211,c_2221,c_2239,c_2428,c_2434,c_2600,c_2609,c_2636,c_2736,c_2792,c_3982,c_5392,c_5537])).

cnf(c_5854,plain,
    ( k1_funct_1(sK3,sK5) != k1_funct_1(sK3,sK5)
    | r1_partfun1(sK3,sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5851,c_1954])).

cnf(c_5874,plain,
    ( r1_partfun1(sK3,sK4) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_5854])).

cnf(c_5877,plain,
    ( k1_funct_1(sK3,sK0(sK3,sK4)) = k1_funct_1(sK4,sK0(sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_4698,c_5874])).

cnf(c_5892,plain,
    ( r1_partfun1(sK3,sK4) = iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5877,c_1957])).

cnf(c_5893,plain,
    ( r1_partfun1(sK3,sK4) = iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5892,c_4088])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5893,c_5874,c_3982,c_2792,c_2736,c_2637,c_2608,c_2600,c_2434,c_2429,c_2239,c_2221,c_2211,c_636,c_81,c_80,c_29,c_27])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.14/0.33  % Computer   : n012.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 13:04:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 2.32/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.32/0.99  
% 2.32/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.32/0.99  
% 2.32/0.99  ------  iProver source info
% 2.32/0.99  
% 2.32/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.32/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.32/0.99  git: non_committed_changes: false
% 2.32/0.99  git: last_make_outside_of_git: false
% 2.32/0.99  
% 2.32/0.99  ------ 
% 2.32/0.99  
% 2.32/0.99  ------ Input Options
% 2.32/0.99  
% 2.32/0.99  --out_options                           all
% 2.32/0.99  --tptp_safe_out                         true
% 2.32/0.99  --problem_path                          ""
% 2.32/0.99  --include_path                          ""
% 2.32/0.99  --clausifier                            res/vclausify_rel
% 2.32/0.99  --clausifier_options                    --mode clausify
% 2.32/0.99  --stdin                                 false
% 2.32/0.99  --stats_out                             all
% 2.32/0.99  
% 2.32/0.99  ------ General Options
% 2.32/0.99  
% 2.32/0.99  --fof                                   false
% 2.32/0.99  --time_out_real                         305.
% 2.32/0.99  --time_out_virtual                      -1.
% 2.32/0.99  --symbol_type_check                     false
% 2.32/0.99  --clausify_out                          false
% 2.32/0.99  --sig_cnt_out                           false
% 2.32/0.99  --trig_cnt_out                          false
% 2.32/0.99  --trig_cnt_out_tolerance                1.
% 2.32/0.99  --trig_cnt_out_sk_spl                   false
% 2.32/0.99  --abstr_cl_out                          false
% 2.32/0.99  
% 2.32/0.99  ------ Global Options
% 2.32/0.99  
% 2.32/0.99  --schedule                              default
% 2.32/0.99  --add_important_lit                     false
% 2.32/0.99  --prop_solver_per_cl                    1000
% 2.32/0.99  --min_unsat_core                        false
% 2.32/0.99  --soft_assumptions                      false
% 2.32/0.99  --soft_lemma_size                       3
% 2.32/0.99  --prop_impl_unit_size                   0
% 2.32/0.99  --prop_impl_unit                        []
% 2.32/0.99  --share_sel_clauses                     true
% 2.32/0.99  --reset_solvers                         false
% 2.32/0.99  --bc_imp_inh                            [conj_cone]
% 2.32/0.99  --conj_cone_tolerance                   3.
% 2.32/0.99  --extra_neg_conj                        none
% 2.32/0.99  --large_theory_mode                     true
% 2.32/0.99  --prolific_symb_bound                   200
% 2.32/0.99  --lt_threshold                          2000
% 2.32/0.99  --clause_weak_htbl                      true
% 2.32/0.99  --gc_record_bc_elim                     false
% 2.32/0.99  
% 2.32/0.99  ------ Preprocessing Options
% 2.32/0.99  
% 2.32/0.99  --preprocessing_flag                    true
% 2.32/0.99  --time_out_prep_mult                    0.1
% 2.32/0.99  --splitting_mode                        input
% 2.32/0.99  --splitting_grd                         true
% 2.32/0.99  --splitting_cvd                         false
% 2.32/0.99  --splitting_cvd_svl                     false
% 2.32/0.99  --splitting_nvd                         32
% 2.32/0.99  --sub_typing                            true
% 2.32/0.99  --prep_gs_sim                           true
% 2.32/0.99  --prep_unflatten                        true
% 2.32/0.99  --prep_res_sim                          true
% 2.32/0.99  --prep_upred                            true
% 2.32/0.99  --prep_sem_filter                       exhaustive
% 2.32/0.99  --prep_sem_filter_out                   false
% 2.32/0.99  --pred_elim                             true
% 2.32/0.99  --res_sim_input                         true
% 2.32/0.99  --eq_ax_congr_red                       true
% 2.32/0.99  --pure_diseq_elim                       true
% 2.32/0.99  --brand_transform                       false
% 2.32/0.99  --non_eq_to_eq                          false
% 2.32/0.99  --prep_def_merge                        true
% 2.32/0.99  --prep_def_merge_prop_impl              false
% 2.32/0.99  --prep_def_merge_mbd                    true
% 2.32/0.99  --prep_def_merge_tr_red                 false
% 2.32/0.99  --prep_def_merge_tr_cl                  false
% 2.32/0.99  --smt_preprocessing                     true
% 2.32/0.99  --smt_ac_axioms                         fast
% 2.32/0.99  --preprocessed_out                      false
% 2.32/0.99  --preprocessed_stats                    false
% 2.32/0.99  
% 2.32/0.99  ------ Abstraction refinement Options
% 2.32/0.99  
% 2.32/0.99  --abstr_ref                             []
% 2.32/0.99  --abstr_ref_prep                        false
% 2.32/0.99  --abstr_ref_until_sat                   false
% 2.32/0.99  --abstr_ref_sig_restrict                funpre
% 2.32/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.32/0.99  --abstr_ref_under                       []
% 2.32/0.99  
% 2.32/0.99  ------ SAT Options
% 2.32/0.99  
% 2.32/0.99  --sat_mode                              false
% 2.32/0.99  --sat_fm_restart_options                ""
% 2.32/0.99  --sat_gr_def                            false
% 2.32/0.99  --sat_epr_types                         true
% 2.32/0.99  --sat_non_cyclic_types                  false
% 2.32/0.99  --sat_finite_models                     false
% 2.32/0.99  --sat_fm_lemmas                         false
% 2.32/0.99  --sat_fm_prep                           false
% 2.32/0.99  --sat_fm_uc_incr                        true
% 2.32/0.99  --sat_out_model                         small
% 2.32/0.99  --sat_out_clauses                       false
% 2.32/0.99  
% 2.32/0.99  ------ QBF Options
% 2.32/0.99  
% 2.32/0.99  --qbf_mode                              false
% 2.32/0.99  --qbf_elim_univ                         false
% 2.32/0.99  --qbf_dom_inst                          none
% 2.32/0.99  --qbf_dom_pre_inst                      false
% 2.32/0.99  --qbf_sk_in                             false
% 2.32/0.99  --qbf_pred_elim                         true
% 2.32/0.99  --qbf_split                             512
% 2.32/0.99  
% 2.32/0.99  ------ BMC1 Options
% 2.32/0.99  
% 2.32/0.99  --bmc1_incremental                      false
% 2.32/0.99  --bmc1_axioms                           reachable_all
% 2.32/0.99  --bmc1_min_bound                        0
% 2.32/0.99  --bmc1_max_bound                        -1
% 2.32/0.99  --bmc1_max_bound_default                -1
% 2.32/0.99  --bmc1_symbol_reachability              true
% 2.32/0.99  --bmc1_property_lemmas                  false
% 2.32/0.99  --bmc1_k_induction                      false
% 2.32/0.99  --bmc1_non_equiv_states                 false
% 2.32/0.99  --bmc1_deadlock                         false
% 2.32/0.99  --bmc1_ucm                              false
% 2.32/0.99  --bmc1_add_unsat_core                   none
% 2.32/0.99  --bmc1_unsat_core_children              false
% 2.32/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.32/0.99  --bmc1_out_stat                         full
% 2.32/0.99  --bmc1_ground_init                      false
% 2.32/0.99  --bmc1_pre_inst_next_state              false
% 2.32/0.99  --bmc1_pre_inst_state                   false
% 2.32/0.99  --bmc1_pre_inst_reach_state             false
% 2.32/0.99  --bmc1_out_unsat_core                   false
% 2.32/0.99  --bmc1_aig_witness_out                  false
% 2.32/0.99  --bmc1_verbose                          false
% 2.32/0.99  --bmc1_dump_clauses_tptp                false
% 2.32/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.32/0.99  --bmc1_dump_file                        -
% 2.32/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.32/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.32/0.99  --bmc1_ucm_extend_mode                  1
% 2.32/0.99  --bmc1_ucm_init_mode                    2
% 2.32/0.99  --bmc1_ucm_cone_mode                    none
% 2.32/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.32/0.99  --bmc1_ucm_relax_model                  4
% 2.32/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.32/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.32/0.99  --bmc1_ucm_layered_model                none
% 2.32/0.99  --bmc1_ucm_max_lemma_size               10
% 2.32/0.99  
% 2.32/0.99  ------ AIG Options
% 2.32/0.99  
% 2.32/0.99  --aig_mode                              false
% 2.32/0.99  
% 2.32/0.99  ------ Instantiation Options
% 2.32/0.99  
% 2.32/0.99  --instantiation_flag                    true
% 2.32/0.99  --inst_sos_flag                         false
% 2.32/0.99  --inst_sos_phase                        true
% 2.32/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.32/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.32/0.99  --inst_lit_sel_side                     num_symb
% 2.32/0.99  --inst_solver_per_active                1400
% 2.32/0.99  --inst_solver_calls_frac                1.
% 2.32/0.99  --inst_passive_queue_type               priority_queues
% 2.32/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.32/0.99  --inst_passive_queues_freq              [25;2]
% 2.32/0.99  --inst_dismatching                      true
% 2.32/0.99  --inst_eager_unprocessed_to_passive     true
% 2.32/0.99  --inst_prop_sim_given                   true
% 2.32/0.99  --inst_prop_sim_new                     false
% 2.32/0.99  --inst_subs_new                         false
% 2.32/0.99  --inst_eq_res_simp                      false
% 2.32/0.99  --inst_subs_given                       false
% 2.32/0.99  --inst_orphan_elimination               true
% 2.32/0.99  --inst_learning_loop_flag               true
% 2.32/0.99  --inst_learning_start                   3000
% 2.32/0.99  --inst_learning_factor                  2
% 2.32/0.99  --inst_start_prop_sim_after_learn       3
% 2.32/0.99  --inst_sel_renew                        solver
% 2.32/0.99  --inst_lit_activity_flag                true
% 2.32/0.99  --inst_restr_to_given                   false
% 2.32/0.99  --inst_activity_threshold               500
% 2.32/0.99  --inst_out_proof                        true
% 2.32/0.99  
% 2.32/0.99  ------ Resolution Options
% 2.32/0.99  
% 2.32/0.99  --resolution_flag                       true
% 2.32/0.99  --res_lit_sel                           adaptive
% 2.32/0.99  --res_lit_sel_side                      none
% 2.32/0.99  --res_ordering                          kbo
% 2.32/0.99  --res_to_prop_solver                    active
% 2.32/0.99  --res_prop_simpl_new                    false
% 2.32/0.99  --res_prop_simpl_given                  true
% 2.32/0.99  --res_passive_queue_type                priority_queues
% 2.32/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.32/0.99  --res_passive_queues_freq               [15;5]
% 2.32/0.99  --res_forward_subs                      full
% 2.32/0.99  --res_backward_subs                     full
% 2.32/0.99  --res_forward_subs_resolution           true
% 2.32/0.99  --res_backward_subs_resolution          true
% 2.32/0.99  --res_orphan_elimination                true
% 2.32/0.99  --res_time_limit                        2.
% 2.32/0.99  --res_out_proof                         true
% 2.32/0.99  
% 2.32/0.99  ------ Superposition Options
% 2.32/0.99  
% 2.32/0.99  --superposition_flag                    true
% 2.32/0.99  --sup_passive_queue_type                priority_queues
% 2.32/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.32/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.32/0.99  --demod_completeness_check              fast
% 2.32/0.99  --demod_use_ground                      true
% 2.32/0.99  --sup_to_prop_solver                    passive
% 2.32/0.99  --sup_prop_simpl_new                    true
% 2.32/0.99  --sup_prop_simpl_given                  true
% 2.32/0.99  --sup_fun_splitting                     false
% 2.32/0.99  --sup_smt_interval                      50000
% 2.32/0.99  
% 2.32/0.99  ------ Superposition Simplification Setup
% 2.32/0.99  
% 2.32/0.99  --sup_indices_passive                   []
% 2.32/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.32/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/0.99  --sup_full_bw                           [BwDemod]
% 2.32/0.99  --sup_immed_triv                        [TrivRules]
% 2.32/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.32/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/0.99  --sup_immed_bw_main                     []
% 2.32/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.32/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.32/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.32/0.99  
% 2.32/0.99  ------ Combination Options
% 2.32/0.99  
% 2.32/0.99  --comb_res_mult                         3
% 2.32/0.99  --comb_sup_mult                         2
% 2.32/0.99  --comb_inst_mult                        10
% 2.32/0.99  
% 2.32/0.99  ------ Debug Options
% 2.32/0.99  
% 2.32/0.99  --dbg_backtrace                         false
% 2.32/0.99  --dbg_dump_prop_clauses                 false
% 2.32/0.99  --dbg_dump_prop_clauses_file            -
% 2.32/0.99  --dbg_out_stat                          false
% 2.32/0.99  ------ Parsing...
% 2.32/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.32/0.99  
% 2.32/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 2.32/0.99  
% 2.32/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.32/0.99  
% 2.32/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.32/0.99  ------ Proving...
% 2.32/0.99  ------ Problem Properties 
% 2.32/0.99  
% 2.32/0.99  
% 2.32/0.99  clauses                                 29
% 2.32/0.99  conjectures                             6
% 2.32/0.99  EPR                                     3
% 2.32/0.99  Horn                                    20
% 2.32/0.99  unary                                   5
% 2.32/0.99  binary                                  5
% 2.32/0.99  lits                                    96
% 2.32/0.99  lits eq                                 60
% 2.32/0.99  fd_pure                                 0
% 2.32/0.99  fd_pseudo                               0
% 2.32/0.99  fd_cond                                 1
% 2.32/0.99  fd_pseudo_cond                          0
% 2.32/0.99  AC symbols                              0
% 2.32/0.99  
% 2.32/0.99  ------ Schedule dynamic 5 is on 
% 2.32/0.99  
% 2.32/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.32/0.99  
% 2.32/0.99  
% 2.32/0.99  ------ 
% 2.32/0.99  Current options:
% 2.32/0.99  ------ 
% 2.32/0.99  
% 2.32/0.99  ------ Input Options
% 2.32/0.99  
% 2.32/0.99  --out_options                           all
% 2.32/0.99  --tptp_safe_out                         true
% 2.32/0.99  --problem_path                          ""
% 2.32/0.99  --include_path                          ""
% 2.32/0.99  --clausifier                            res/vclausify_rel
% 2.32/0.99  --clausifier_options                    --mode clausify
% 2.32/0.99  --stdin                                 false
% 2.32/0.99  --stats_out                             all
% 2.32/0.99  
% 2.32/0.99  ------ General Options
% 2.32/0.99  
% 2.32/0.99  --fof                                   false
% 2.32/0.99  --time_out_real                         305.
% 2.32/0.99  --time_out_virtual                      -1.
% 2.32/0.99  --symbol_type_check                     false
% 2.32/0.99  --clausify_out                          false
% 2.32/0.99  --sig_cnt_out                           false
% 2.32/0.99  --trig_cnt_out                          false
% 2.32/0.99  --trig_cnt_out_tolerance                1.
% 2.32/0.99  --trig_cnt_out_sk_spl                   false
% 2.32/0.99  --abstr_cl_out                          false
% 2.32/0.99  
% 2.32/0.99  ------ Global Options
% 2.32/0.99  
% 2.32/0.99  --schedule                              default
% 2.32/0.99  --add_important_lit                     false
% 2.32/0.99  --prop_solver_per_cl                    1000
% 2.32/0.99  --min_unsat_core                        false
% 2.32/0.99  --soft_assumptions                      false
% 2.32/0.99  --soft_lemma_size                       3
% 2.32/0.99  --prop_impl_unit_size                   0
% 2.32/0.99  --prop_impl_unit                        []
% 2.32/0.99  --share_sel_clauses                     true
% 2.32/0.99  --reset_solvers                         false
% 2.32/0.99  --bc_imp_inh                            [conj_cone]
% 2.32/0.99  --conj_cone_tolerance                   3.
% 2.32/0.99  --extra_neg_conj                        none
% 2.32/0.99  --large_theory_mode                     true
% 2.32/0.99  --prolific_symb_bound                   200
% 2.32/0.99  --lt_threshold                          2000
% 2.32/0.99  --clause_weak_htbl                      true
% 2.32/0.99  --gc_record_bc_elim                     false
% 2.32/0.99  
% 2.32/0.99  ------ Preprocessing Options
% 2.32/0.99  
% 2.32/0.99  --preprocessing_flag                    true
% 2.32/0.99  --time_out_prep_mult                    0.1
% 2.32/0.99  --splitting_mode                        input
% 2.32/0.99  --splitting_grd                         true
% 2.32/0.99  --splitting_cvd                         false
% 2.32/0.99  --splitting_cvd_svl                     false
% 2.32/0.99  --splitting_nvd                         32
% 2.32/0.99  --sub_typing                            true
% 2.32/0.99  --prep_gs_sim                           true
% 2.32/0.99  --prep_unflatten                        true
% 2.32/0.99  --prep_res_sim                          true
% 2.32/0.99  --prep_upred                            true
% 2.32/0.99  --prep_sem_filter                       exhaustive
% 2.32/0.99  --prep_sem_filter_out                   false
% 2.32/0.99  --pred_elim                             true
% 2.32/0.99  --res_sim_input                         true
% 2.32/0.99  --eq_ax_congr_red                       true
% 2.32/0.99  --pure_diseq_elim                       true
% 2.32/0.99  --brand_transform                       false
% 2.32/0.99  --non_eq_to_eq                          false
% 2.32/0.99  --prep_def_merge                        true
% 2.32/0.99  --prep_def_merge_prop_impl              false
% 2.32/0.99  --prep_def_merge_mbd                    true
% 2.32/0.99  --prep_def_merge_tr_red                 false
% 2.32/0.99  --prep_def_merge_tr_cl                  false
% 2.32/0.99  --smt_preprocessing                     true
% 2.32/0.99  --smt_ac_axioms                         fast
% 2.32/0.99  --preprocessed_out                      false
% 2.32/0.99  --preprocessed_stats                    false
% 2.32/0.99  
% 2.32/0.99  ------ Abstraction refinement Options
% 2.32/0.99  
% 2.32/0.99  --abstr_ref                             []
% 2.32/0.99  --abstr_ref_prep                        false
% 2.32/0.99  --abstr_ref_until_sat                   false
% 2.32/0.99  --abstr_ref_sig_restrict                funpre
% 2.32/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.32/0.99  --abstr_ref_under                       []
% 2.32/0.99  
% 2.32/0.99  ------ SAT Options
% 2.32/0.99  
% 2.32/0.99  --sat_mode                              false
% 2.32/0.99  --sat_fm_restart_options                ""
% 2.32/0.99  --sat_gr_def                            false
% 2.32/0.99  --sat_epr_types                         true
% 2.32/0.99  --sat_non_cyclic_types                  false
% 2.32/0.99  --sat_finite_models                     false
% 2.32/0.99  --sat_fm_lemmas                         false
% 2.32/0.99  --sat_fm_prep                           false
% 2.32/0.99  --sat_fm_uc_incr                        true
% 2.32/0.99  --sat_out_model                         small
% 2.32/0.99  --sat_out_clauses                       false
% 2.32/0.99  
% 2.32/0.99  ------ QBF Options
% 2.32/0.99  
% 2.32/0.99  --qbf_mode                              false
% 2.32/0.99  --qbf_elim_univ                         false
% 2.32/0.99  --qbf_dom_inst                          none
% 2.32/0.99  --qbf_dom_pre_inst                      false
% 2.32/0.99  --qbf_sk_in                             false
% 2.32/0.99  --qbf_pred_elim                         true
% 2.32/0.99  --qbf_split                             512
% 2.32/0.99  
% 2.32/0.99  ------ BMC1 Options
% 2.32/0.99  
% 2.32/0.99  --bmc1_incremental                      false
% 2.32/0.99  --bmc1_axioms                           reachable_all
% 2.32/0.99  --bmc1_min_bound                        0
% 2.32/0.99  --bmc1_max_bound                        -1
% 2.32/0.99  --bmc1_max_bound_default                -1
% 2.32/0.99  --bmc1_symbol_reachability              true
% 2.32/0.99  --bmc1_property_lemmas                  false
% 2.32/0.99  --bmc1_k_induction                      false
% 2.32/0.99  --bmc1_non_equiv_states                 false
% 2.32/0.99  --bmc1_deadlock                         false
% 2.32/0.99  --bmc1_ucm                              false
% 2.32/0.99  --bmc1_add_unsat_core                   none
% 2.32/0.99  --bmc1_unsat_core_children              false
% 2.32/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.32/0.99  --bmc1_out_stat                         full
% 2.32/0.99  --bmc1_ground_init                      false
% 2.32/0.99  --bmc1_pre_inst_next_state              false
% 2.32/0.99  --bmc1_pre_inst_state                   false
% 2.32/0.99  --bmc1_pre_inst_reach_state             false
% 2.32/0.99  --bmc1_out_unsat_core                   false
% 2.32/0.99  --bmc1_aig_witness_out                  false
% 2.32/0.99  --bmc1_verbose                          false
% 2.32/0.99  --bmc1_dump_clauses_tptp                false
% 2.32/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.32/0.99  --bmc1_dump_file                        -
% 2.32/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.32/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.32/0.99  --bmc1_ucm_extend_mode                  1
% 2.32/0.99  --bmc1_ucm_init_mode                    2
% 2.32/0.99  --bmc1_ucm_cone_mode                    none
% 2.32/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.32/0.99  --bmc1_ucm_relax_model                  4
% 2.32/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.32/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.32/0.99  --bmc1_ucm_layered_model                none
% 2.32/0.99  --bmc1_ucm_max_lemma_size               10
% 2.32/0.99  
% 2.32/0.99  ------ AIG Options
% 2.32/0.99  
% 2.32/0.99  --aig_mode                              false
% 2.32/0.99  
% 2.32/0.99  ------ Instantiation Options
% 2.32/0.99  
% 2.32/0.99  --instantiation_flag                    true
% 2.32/0.99  --inst_sos_flag                         false
% 2.32/0.99  --inst_sos_phase                        true
% 2.32/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.32/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.32/0.99  --inst_lit_sel_side                     none
% 2.32/0.99  --inst_solver_per_active                1400
% 2.32/0.99  --inst_solver_calls_frac                1.
% 2.32/0.99  --inst_passive_queue_type               priority_queues
% 2.32/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.32/0.99  --inst_passive_queues_freq              [25;2]
% 2.32/0.99  --inst_dismatching                      true
% 2.32/0.99  --inst_eager_unprocessed_to_passive     true
% 2.32/0.99  --inst_prop_sim_given                   true
% 2.32/0.99  --inst_prop_sim_new                     false
% 2.32/0.99  --inst_subs_new                         false
% 2.32/0.99  --inst_eq_res_simp                      false
% 2.32/0.99  --inst_subs_given                       false
% 2.32/0.99  --inst_orphan_elimination               true
% 2.32/0.99  --inst_learning_loop_flag               true
% 2.32/0.99  --inst_learning_start                   3000
% 2.32/0.99  --inst_learning_factor                  2
% 2.32/0.99  --inst_start_prop_sim_after_learn       3
% 2.32/0.99  --inst_sel_renew                        solver
% 2.32/0.99  --inst_lit_activity_flag                true
% 2.32/0.99  --inst_restr_to_given                   false
% 2.32/0.99  --inst_activity_threshold               500
% 2.32/0.99  --inst_out_proof                        true
% 2.32/0.99  
% 2.32/0.99  ------ Resolution Options
% 2.32/0.99  
% 2.32/0.99  --resolution_flag                       false
% 2.32/0.99  --res_lit_sel                           adaptive
% 2.32/0.99  --res_lit_sel_side                      none
% 2.32/0.99  --res_ordering                          kbo
% 2.32/0.99  --res_to_prop_solver                    active
% 2.32/0.99  --res_prop_simpl_new                    false
% 2.32/0.99  --res_prop_simpl_given                  true
% 2.32/0.99  --res_passive_queue_type                priority_queues
% 2.32/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.32/0.99  --res_passive_queues_freq               [15;5]
% 2.32/0.99  --res_forward_subs                      full
% 2.32/0.99  --res_backward_subs                     full
% 2.32/0.99  --res_forward_subs_resolution           true
% 2.32/0.99  --res_backward_subs_resolution          true
% 2.32/0.99  --res_orphan_elimination                true
% 2.32/0.99  --res_time_limit                        2.
% 2.32/0.99  --res_out_proof                         true
% 2.32/0.99  
% 2.32/0.99  ------ Superposition Options
% 2.32/0.99  
% 2.32/0.99  --superposition_flag                    true
% 2.32/0.99  --sup_passive_queue_type                priority_queues
% 2.32/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.32/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.32/0.99  --demod_completeness_check              fast
% 2.32/0.99  --demod_use_ground                      true
% 2.32/0.99  --sup_to_prop_solver                    passive
% 2.32/0.99  --sup_prop_simpl_new                    true
% 2.32/0.99  --sup_prop_simpl_given                  true
% 2.32/0.99  --sup_fun_splitting                     false
% 2.32/0.99  --sup_smt_interval                      50000
% 2.32/0.99  
% 2.32/0.99  ------ Superposition Simplification Setup
% 2.32/0.99  
% 2.32/0.99  --sup_indices_passive                   []
% 2.32/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.32/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/0.99  --sup_full_bw                           [BwDemod]
% 2.32/0.99  --sup_immed_triv                        [TrivRules]
% 2.32/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.32/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/0.99  --sup_immed_bw_main                     []
% 2.32/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.32/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.32/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.32/0.99  
% 2.32/0.99  ------ Combination Options
% 2.32/0.99  
% 2.32/0.99  --comb_res_mult                         3
% 2.32/0.99  --comb_sup_mult                         2
% 2.32/0.99  --comb_inst_mult                        10
% 2.32/0.99  
% 2.32/0.99  ------ Debug Options
% 2.32/0.99  
% 2.32/0.99  --dbg_backtrace                         false
% 2.32/0.99  --dbg_dump_prop_clauses                 false
% 2.32/0.99  --dbg_dump_prop_clauses_file            -
% 2.32/0.99  --dbg_out_stat                          false
% 2.32/0.99  
% 2.32/0.99  
% 2.32/0.99  
% 2.32/0.99  
% 2.32/0.99  ------ Proving...
% 2.32/0.99  
% 2.32/0.99  
% 2.32/0.99  % SZS status Theorem for theBenchmark.p
% 2.32/0.99  
% 2.32/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.32/0.99  
% 2.32/0.99  fof(f9,conjecture,(
% 2.32/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (r1_partfun1(X2,X3) <=> ! [X4] : (r2_hidden(X4,k1_relset_1(X0,X1,X2)) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4))))))),
% 2.32/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.32/0.99  
% 2.32/0.99  fof(f10,negated_conjecture,(
% 2.32/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (r1_partfun1(X2,X3) <=> ! [X4] : (r2_hidden(X4,k1_relset_1(X0,X1,X2)) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4))))))),
% 2.32/0.99    inference(negated_conjecture,[],[f9])).
% 2.32/0.99  
% 2.32/0.99  fof(f20,plain,(
% 2.32/0.99    ? [X0,X1,X2] : (? [X3] : (((r1_partfun1(X2,X3) <~> ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,k1_relset_1(X0,X1,X2)))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 2.32/0.99    inference(ennf_transformation,[],[f10])).
% 2.32/0.99  
% 2.32/0.99  fof(f21,plain,(
% 2.32/0.99    ? [X0,X1,X2] : (? [X3] : ((r1_partfun1(X2,X3) <~> ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,k1_relset_1(X0,X1,X2)))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 2.32/0.99    inference(flattening,[],[f20])).
% 2.32/0.99  
% 2.32/0.99  fof(f30,plain,(
% 2.32/0.99    ? [X0,X1,X2] : (? [X3] : (((? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & r2_hidden(X4,k1_relset_1(X0,X1,X2))) | ~r1_partfun1(X2,X3)) & (! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,k1_relset_1(X0,X1,X2))) | r1_partfun1(X2,X3))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 2.32/0.99    inference(nnf_transformation,[],[f21])).
% 2.32/0.99  
% 2.32/0.99  fof(f31,plain,(
% 2.32/0.99    ? [X0,X1,X2] : (? [X3] : ((? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & r2_hidden(X4,k1_relset_1(X0,X1,X2))) | ~r1_partfun1(X2,X3)) & (! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,k1_relset_1(X0,X1,X2))) | r1_partfun1(X2,X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 2.32/0.99    inference(flattening,[],[f30])).
% 2.32/0.99  
% 2.32/0.99  fof(f32,plain,(
% 2.32/0.99    ? [X0,X1,X2] : (? [X3] : ((? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & r2_hidden(X4,k1_relset_1(X0,X1,X2))) | ~r1_partfun1(X2,X3)) & (! [X5] : (k1_funct_1(X2,X5) = k1_funct_1(X3,X5) | ~r2_hidden(X5,k1_relset_1(X0,X1,X2))) | r1_partfun1(X2,X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 2.32/0.99    inference(rectify,[],[f31])).
% 2.32/0.99  
% 2.32/0.99  fof(f35,plain,(
% 2.32/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & r2_hidden(X4,k1_relset_1(X0,X1,X2))) => (k1_funct_1(X2,sK5) != k1_funct_1(X3,sK5) & r2_hidden(sK5,k1_relset_1(X0,X1,X2)))) )),
% 2.32/0.99    introduced(choice_axiom,[])).
% 2.32/0.99  
% 2.32/0.99  fof(f34,plain,(
% 2.32/0.99    ( ! [X2,X0,X1] : (? [X3] : ((? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & r2_hidden(X4,k1_relset_1(X0,X1,X2))) | ~r1_partfun1(X2,X3)) & (! [X5] : (k1_funct_1(X2,X5) = k1_funct_1(X3,X5) | ~r2_hidden(X5,k1_relset_1(X0,X1,X2))) | r1_partfun1(X2,X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((? [X4] : (k1_funct_1(sK4,X4) != k1_funct_1(X2,X4) & r2_hidden(X4,k1_relset_1(X0,X1,X2))) | ~r1_partfun1(X2,sK4)) & (! [X5] : (k1_funct_1(sK4,X5) = k1_funct_1(X2,X5) | ~r2_hidden(X5,k1_relset_1(X0,X1,X2))) | r1_partfun1(X2,sK4)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(sK4,X0,X1) & v1_funct_1(sK4))) )),
% 2.32/0.99    introduced(choice_axiom,[])).
% 2.32/0.99  
% 2.32/0.99  fof(f33,plain,(
% 2.32/0.99    ? [X0,X1,X2] : (? [X3] : ((? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & r2_hidden(X4,k1_relset_1(X0,X1,X2))) | ~r1_partfun1(X2,X3)) & (! [X5] : (k1_funct_1(X2,X5) = k1_funct_1(X3,X5) | ~r2_hidden(X5,k1_relset_1(X0,X1,X2))) | r1_partfun1(X2,X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (? [X3] : ((? [X4] : (k1_funct_1(sK3,X4) != k1_funct_1(X3,X4) & r2_hidden(X4,k1_relset_1(sK1,sK2,sK3))) | ~r1_partfun1(sK3,X3)) & (! [X5] : (k1_funct_1(sK3,X5) = k1_funct_1(X3,X5) | ~r2_hidden(X5,k1_relset_1(sK1,sK2,sK3))) | r1_partfun1(sK3,X3)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X3,sK1,sK2) & v1_funct_1(X3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_1(sK3))),
% 2.32/0.99    introduced(choice_axiom,[])).
% 2.32/0.99  
% 2.32/0.99  fof(f36,plain,(
% 2.32/0.99    (((k1_funct_1(sK3,sK5) != k1_funct_1(sK4,sK5) & r2_hidden(sK5,k1_relset_1(sK1,sK2,sK3))) | ~r1_partfun1(sK3,sK4)) & (! [X5] : (k1_funct_1(sK3,X5) = k1_funct_1(sK4,X5) | ~r2_hidden(X5,k1_relset_1(sK1,sK2,sK3))) | r1_partfun1(sK3,sK4)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK2) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_1(sK3)),
% 2.32/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f32,f35,f34,f33])).
% 2.32/0.99  
% 2.32/0.99  fof(f58,plain,(
% 2.32/0.99    v1_funct_2(sK4,sK1,sK2)),
% 2.32/0.99    inference(cnf_transformation,[],[f36])).
% 2.32/0.99  
% 2.32/0.99  fof(f7,axiom,(
% 2.32/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.32/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.32/0.99  
% 2.32/0.99  fof(f16,plain,(
% 2.32/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.32/0.99    inference(ennf_transformation,[],[f7])).
% 2.32/0.99  
% 2.32/0.99  fof(f17,plain,(
% 2.32/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.32/0.99    inference(flattening,[],[f16])).
% 2.32/0.99  
% 2.32/0.99  fof(f25,plain,(
% 2.32/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.32/0.99    inference(nnf_transformation,[],[f17])).
% 2.32/0.99  
% 2.32/0.99  fof(f46,plain,(
% 2.32/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.32/0.99    inference(cnf_transformation,[],[f25])).
% 2.32/0.99  
% 2.32/0.99  fof(f59,plain,(
% 2.32/0.99    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 2.32/0.99    inference(cnf_transformation,[],[f36])).
% 2.32/0.99  
% 2.32/0.99  fof(f6,axiom,(
% 2.32/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.32/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.32/0.99  
% 2.32/0.99  fof(f15,plain,(
% 2.32/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.32/0.99    inference(ennf_transformation,[],[f6])).
% 2.32/0.99  
% 2.32/0.99  fof(f45,plain,(
% 2.32/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.32/0.99    inference(cnf_transformation,[],[f15])).
% 2.32/0.99  
% 2.32/0.99  fof(f8,axiom,(
% 2.32/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) => (r1_partfun1(X0,X1) <=> ! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2))))))),
% 2.32/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.32/0.99  
% 2.32/0.99  fof(f18,plain,(
% 2.32/0.99    ! [X0] : (! [X1] : (((r1_partfun1(X0,X1) <=> ! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0)))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.32/0.99    inference(ennf_transformation,[],[f8])).
% 2.32/0.99  
% 2.32/0.99  fof(f19,plain,(
% 2.32/0.99    ! [X0] : (! [X1] : ((r1_partfun1(X0,X1) <=> ! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0)))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.32/0.99    inference(flattening,[],[f18])).
% 2.32/0.99  
% 2.32/0.99  fof(f26,plain,(
% 2.32/0.99    ! [X0] : (! [X1] : (((r1_partfun1(X0,X1) | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0)))) & (! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0))) | ~r1_partfun1(X0,X1))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.32/0.99    inference(nnf_transformation,[],[f19])).
% 2.32/0.99  
% 2.32/0.99  fof(f27,plain,(
% 2.32/0.99    ! [X0] : (! [X1] : (((r1_partfun1(X0,X1) | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0)))) & (! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r1_partfun1(X0,X1))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.32/0.99    inference(rectify,[],[f26])).
% 2.32/0.99  
% 2.32/0.99  fof(f28,plain,(
% 2.32/0.99    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1)) & r2_hidden(sK0(X0,X1),k1_relat_1(X0))))),
% 2.32/0.99    introduced(choice_axiom,[])).
% 2.32/0.99  
% 2.32/0.99  fof(f29,plain,(
% 2.32/0.99    ! [X0] : (! [X1] : (((r1_partfun1(X0,X1) | (k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1)) & r2_hidden(sK0(X0,X1),k1_relat_1(X0)))) & (! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r1_partfun1(X0,X1))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.32/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).
% 2.32/0.99  
% 2.32/0.99  fof(f53,plain,(
% 2.32/0.99    ( ! [X0,X1] : (r1_partfun1(X0,X1) | r2_hidden(sK0(X0,X1),k1_relat_1(X0)) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.32/0.99    inference(cnf_transformation,[],[f29])).
% 2.32/0.99  
% 2.32/0.99  fof(f56,plain,(
% 2.32/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 2.32/0.99    inference(cnf_transformation,[],[f36])).
% 2.32/0.99  
% 2.32/0.99  fof(f61,plain,(
% 2.32/0.99    ( ! [X5] : (k1_funct_1(sK3,X5) = k1_funct_1(sK4,X5) | ~r2_hidden(X5,k1_relset_1(sK1,sK2,sK3)) | r1_partfun1(sK3,sK4)) )),
% 2.32/0.99    inference(cnf_transformation,[],[f36])).
% 2.32/0.99  
% 2.32/0.99  fof(f55,plain,(
% 2.32/0.99    v1_funct_1(sK3)),
% 2.32/0.99    inference(cnf_transformation,[],[f36])).
% 2.32/0.99  
% 2.32/0.99  fof(f2,axiom,(
% 2.32/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.32/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.32/0.99  
% 2.32/0.99  fof(f12,plain,(
% 2.32/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.32/0.99    inference(ennf_transformation,[],[f2])).
% 2.32/0.99  
% 2.32/0.99  fof(f40,plain,(
% 2.32/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.32/0.99    inference(cnf_transformation,[],[f12])).
% 2.32/0.99  
% 2.32/0.99  fof(f4,axiom,(
% 2.32/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.32/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.32/0.99  
% 2.32/0.99  fof(f43,plain,(
% 2.32/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.32/0.99    inference(cnf_transformation,[],[f4])).
% 2.32/0.99  
% 2.32/0.99  fof(f57,plain,(
% 2.32/0.99    v1_funct_1(sK4)),
% 2.32/0.99    inference(cnf_transformation,[],[f36])).
% 2.32/0.99  
% 2.32/0.99  fof(f5,axiom,(
% 2.32/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.32/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.32/0.99  
% 2.32/0.99  fof(f11,plain,(
% 2.32/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.32/0.99    inference(pure_predicate_removal,[],[f5])).
% 2.32/0.99  
% 2.32/0.99  fof(f14,plain,(
% 2.32/0.99    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.32/0.99    inference(ennf_transformation,[],[f11])).
% 2.32/0.99  
% 2.32/0.99  fof(f44,plain,(
% 2.32/0.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.32/0.99    inference(cnf_transformation,[],[f14])).
% 2.32/0.99  
% 2.32/0.99  fof(f3,axiom,(
% 2.32/0.99    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 2.32/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.32/0.99  
% 2.32/0.99  fof(f13,plain,(
% 2.32/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.32/0.99    inference(ennf_transformation,[],[f3])).
% 2.32/0.99  
% 2.32/0.99  fof(f24,plain,(
% 2.32/0.99    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.32/0.99    inference(nnf_transformation,[],[f13])).
% 2.32/0.99  
% 2.32/0.99  fof(f41,plain,(
% 2.32/0.99    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.32/0.99    inference(cnf_transformation,[],[f24])).
% 2.32/0.99  
% 2.32/0.99  fof(f62,plain,(
% 2.32/0.99    r2_hidden(sK5,k1_relset_1(sK1,sK2,sK3)) | ~r1_partfun1(sK3,sK4)),
% 2.32/0.99    inference(cnf_transformation,[],[f36])).
% 2.32/0.99  
% 2.32/0.99  fof(f52,plain,(
% 2.32/0.99    ( ! [X0,X3,X1] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r1_partfun1(X0,X1) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.32/0.99    inference(cnf_transformation,[],[f29])).
% 2.32/0.99  
% 2.32/0.99  fof(f54,plain,(
% 2.32/0.99    ( ! [X0,X1] : (r1_partfun1(X0,X1) | k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1)) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.32/0.99    inference(cnf_transformation,[],[f29])).
% 2.32/0.99  
% 2.32/0.99  fof(f63,plain,(
% 2.32/0.99    k1_funct_1(sK3,sK5) != k1_funct_1(sK4,sK5) | ~r1_partfun1(sK3,sK4)),
% 2.32/0.99    inference(cnf_transformation,[],[f36])).
% 2.32/0.99  
% 2.32/0.99  fof(f47,plain,(
% 2.32/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.32/0.99    inference(cnf_transformation,[],[f25])).
% 2.32/0.99  
% 2.32/0.99  fof(f70,plain,(
% 2.32/0.99    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 2.32/0.99    inference(equality_resolution,[],[f47])).
% 2.32/0.99  
% 2.32/0.99  fof(f1,axiom,(
% 2.32/0.99    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.32/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.32/0.99  
% 2.32/0.99  fof(f22,plain,(
% 2.32/0.99    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 2.32/0.99    inference(nnf_transformation,[],[f1])).
% 2.32/0.99  
% 2.32/0.99  fof(f23,plain,(
% 2.32/0.99    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 2.32/0.99    inference(flattening,[],[f22])).
% 2.32/0.99  
% 2.32/0.99  fof(f38,plain,(
% 2.32/0.99    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 2.32/0.99    inference(cnf_transformation,[],[f23])).
% 2.32/0.99  
% 2.32/0.99  fof(f65,plain,(
% 2.32/0.99    ( ! [X1] : (k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0) )),
% 2.32/0.99    inference(equality_resolution,[],[f38])).
% 2.32/0.99  
% 2.32/0.99  fof(f60,plain,(
% 2.32/0.99    k1_xboole_0 = sK1 | k1_xboole_0 != sK2),
% 2.32/0.99    inference(cnf_transformation,[],[f36])).
% 2.32/0.99  
% 2.32/0.99  fof(f37,plain,(
% 2.32/0.99    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0) )),
% 2.32/0.99    inference(cnf_transformation,[],[f23])).
% 2.32/0.99  
% 2.32/0.99  fof(f50,plain,(
% 2.32/0.99    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.32/0.99    inference(cnf_transformation,[],[f25])).
% 2.32/0.99  
% 2.32/0.99  fof(f68,plain,(
% 2.32/0.99    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 2.32/0.99    inference(equality_resolution,[],[f50])).
% 2.32/0.99  
% 2.32/0.99  fof(f39,plain,(
% 2.32/0.99    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 2.32/0.99    inference(cnf_transformation,[],[f23])).
% 2.32/0.99  
% 2.32/0.99  fof(f64,plain,(
% 2.32/0.99    ( ! [X0] : (k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0) )),
% 2.32/0.99    inference(equality_resolution,[],[f39])).
% 2.32/0.99  
% 2.32/0.99  cnf(c_23,negated_conjecture,
% 2.32/0.99      ( v1_funct_2(sK4,sK1,sK2) ),
% 2.32/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_14,plain,
% 2.32/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.32/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.32/0.99      | k1_relset_1(X1,X2,X0) = X1
% 2.32/0.99      | k1_xboole_0 = X2 ),
% 2.32/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_22,negated_conjecture,
% 2.32/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 2.32/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_587,plain,
% 2.32/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.32/0.99      | k1_relset_1(X1,X2,X0) = X1
% 2.32/0.99      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.32/0.99      | sK4 != X0
% 2.32/0.99      | k1_xboole_0 = X2 ),
% 2.32/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_22]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_588,plain,
% 2.32/0.99      ( ~ v1_funct_2(sK4,X0,X1)
% 2.32/0.99      | k1_relset_1(X0,X1,sK4) = X0
% 2.32/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.32/0.99      | k1_xboole_0 = X1 ),
% 2.32/0.99      inference(unflattening,[status(thm)],[c_587]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_1448,plain,
% 2.32/0.99      ( k1_relset_1(X0,X1,sK4) = X0
% 2.32/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.32/0.99      | sK2 != X1
% 2.32/0.99      | sK1 != X0
% 2.32/0.99      | sK4 != sK4
% 2.32/0.99      | k1_xboole_0 = X1 ),
% 2.32/0.99      inference(resolution_lifted,[status(thm)],[c_23,c_588]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_1449,plain,
% 2.32/0.99      ( k1_relset_1(sK1,sK2,sK4) = sK1
% 2.32/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.32/0.99      | k1_xboole_0 = sK2 ),
% 2.32/0.99      inference(unflattening,[status(thm)],[c_1448]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_2007,plain,
% 2.32/0.99      ( k1_relset_1(sK1,sK2,sK4) = sK1 | k1_xboole_0 = sK2 ),
% 2.32/0.99      inference(equality_resolution_simp,[status(thm)],[c_1449]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_8,plain,
% 2.32/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.32/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.32/0.99      inference(cnf_transformation,[],[f45]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_623,plain,
% 2.32/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.32/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.32/0.99      | sK4 != X2 ),
% 2.32/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_22]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_624,plain,
% 2.32/0.99      ( k1_relset_1(X0,X1,sK4) = k1_relat_1(sK4)
% 2.32/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 2.32/0.99      inference(unflattening,[status(thm)],[c_623]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_2227,plain,
% 2.32/0.99      ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
% 2.32/0.99      inference(equality_resolution,[status(thm)],[c_624]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_2909,plain,
% 2.32/0.99      ( k1_relat_1(sK4) = sK1 | sK2 = k1_xboole_0 ),
% 2.32/0.99      inference(demodulation,[status(thm)],[c_2007,c_2227]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_16,plain,
% 2.32/0.99      ( r2_hidden(sK0(X0,X1),k1_relat_1(X0))
% 2.32/0.99      | r1_partfun1(X0,X1)
% 2.32/0.99      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 2.32/0.99      | ~ v1_funct_1(X1)
% 2.32/0.99      | ~ v1_funct_1(X0)
% 2.32/0.99      | ~ v1_relat_1(X0)
% 2.32/0.99      | ~ v1_relat_1(X1) ),
% 2.32/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_1956,plain,
% 2.32/0.99      ( r2_hidden(sK0(X0,X1),k1_relat_1(X0)) = iProver_top
% 2.32/0.99      | r1_partfun1(X0,X1) = iProver_top
% 2.32/0.99      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) != iProver_top
% 2.32/0.99      | v1_funct_1(X1) != iProver_top
% 2.32/0.99      | v1_funct_1(X0) != iProver_top
% 2.32/0.99      | v1_relat_1(X1) != iProver_top
% 2.32/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.32/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_25,negated_conjecture,
% 2.32/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 2.32/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_683,plain,
% 2.32/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.32/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.32/0.99      | sK3 != X2 ),
% 2.32/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_25]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_684,plain,
% 2.32/0.99      ( k1_relset_1(X0,X1,sK3) = k1_relat_1(sK3)
% 2.32/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 2.32/0.99      inference(unflattening,[status(thm)],[c_683]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_2268,plain,
% 2.32/0.99      ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
% 2.32/0.99      inference(equality_resolution,[status(thm)],[c_684]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_20,negated_conjecture,
% 2.32/0.99      ( ~ r2_hidden(X0,k1_relset_1(sK1,sK2,sK3))
% 2.32/0.99      | r1_partfun1(sK3,sK4)
% 2.32/0.99      | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0) ),
% 2.32/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_1952,plain,
% 2.32/0.99      ( k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0)
% 2.32/0.99      | r2_hidden(X0,k1_relset_1(sK1,sK2,sK3)) != iProver_top
% 2.32/0.99      | r1_partfun1(sK3,sK4) = iProver_top ),
% 2.32/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_2460,plain,
% 2.32/0.99      ( k1_funct_1(sK4,X0) = k1_funct_1(sK3,X0)
% 2.32/0.99      | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 2.32/0.99      | r1_partfun1(sK3,sK4) = iProver_top ),
% 2.32/0.99      inference(demodulation,[status(thm)],[c_2268,c_1952]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_3327,plain,
% 2.32/0.99      ( k1_funct_1(sK3,sK0(sK3,X0)) = k1_funct_1(sK4,sK0(sK3,X0))
% 2.32/0.99      | r1_partfun1(sK3,X0) = iProver_top
% 2.32/0.99      | r1_partfun1(sK3,sK4) = iProver_top
% 2.32/0.99      | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) != iProver_top
% 2.32/0.99      | v1_funct_1(X0) != iProver_top
% 2.32/0.99      | v1_funct_1(sK3) != iProver_top
% 2.32/0.99      | v1_relat_1(X0) != iProver_top
% 2.32/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.32/0.99      inference(superposition,[status(thm)],[c_1956,c_2460]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_26,negated_conjecture,
% 2.32/0.99      ( v1_funct_1(sK3) ),
% 2.32/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_27,plain,
% 2.32/0.99      ( v1_funct_1(sK3) = iProver_top ),
% 2.32/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_3,plain,
% 2.32/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.32/0.99      | ~ v1_relat_1(X1)
% 2.32/0.99      | v1_relat_1(X0) ),
% 2.32/0.99      inference(cnf_transformation,[],[f40]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_557,plain,
% 2.32/0.99      ( ~ v1_relat_1(X0)
% 2.32/0.99      | v1_relat_1(X1)
% 2.32/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(X0)
% 2.32/0.99      | sK3 != X1 ),
% 2.32/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_25]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_558,plain,
% 2.32/0.99      ( ~ v1_relat_1(X0)
% 2.32/0.99      | v1_relat_1(sK3)
% 2.32/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(X0) ),
% 2.32/0.99      inference(unflattening,[status(thm)],[c_557]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_1948,plain,
% 2.32/0.99      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(X0)
% 2.32/0.99      | v1_relat_1(X0) != iProver_top
% 2.32/0.99      | v1_relat_1(sK3) = iProver_top ),
% 2.32/0.99      inference(predicate_to_equality,[status(thm)],[c_558]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_2608,plain,
% 2.32/0.99      ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
% 2.32/0.99      | v1_relat_1(sK3) = iProver_top ),
% 2.32/0.99      inference(equality_resolution,[status(thm)],[c_1948]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_6,plain,
% 2.32/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.32/0.99      inference(cnf_transformation,[],[f43]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_2636,plain,
% 2.32/0.99      ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) ),
% 2.32/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_2637,plain,
% 2.32/0.99      ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) = iProver_top ),
% 2.32/0.99      inference(predicate_to_equality,[status(thm)],[c_2636]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_3530,plain,
% 2.32/0.99      ( v1_relat_1(X0) != iProver_top
% 2.32/0.99      | k1_funct_1(sK3,sK0(sK3,X0)) = k1_funct_1(sK4,sK0(sK3,X0))
% 2.32/0.99      | r1_partfun1(sK3,X0) = iProver_top
% 2.32/0.99      | r1_partfun1(sK3,sK4) = iProver_top
% 2.32/0.99      | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) != iProver_top
% 2.32/0.99      | v1_funct_1(X0) != iProver_top ),
% 2.32/0.99      inference(global_propositional_subsumption,
% 2.32/0.99                [status(thm)],
% 2.32/0.99                [c_3327,c_27,c_2608,c_2637]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_3531,plain,
% 2.32/0.99      ( k1_funct_1(sK3,sK0(sK3,X0)) = k1_funct_1(sK4,sK0(sK3,X0))
% 2.32/0.99      | r1_partfun1(sK3,X0) = iProver_top
% 2.32/0.99      | r1_partfun1(sK3,sK4) = iProver_top
% 2.32/0.99      | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) != iProver_top
% 2.32/0.99      | v1_funct_1(X0) != iProver_top
% 2.32/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.32/0.99      inference(renaming,[status(thm)],[c_3530]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_3542,plain,
% 2.32/0.99      ( k1_funct_1(sK3,sK0(sK3,sK4)) = k1_funct_1(sK4,sK0(sK3,sK4))
% 2.32/0.99      | sK2 = k1_xboole_0
% 2.32/0.99      | r1_partfun1(sK3,sK4) = iProver_top
% 2.32/0.99      | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top
% 2.32/0.99      | v1_funct_1(sK4) != iProver_top
% 2.32/0.99      | v1_relat_1(sK4) != iProver_top ),
% 2.32/0.99      inference(superposition,[status(thm)],[c_2909,c_3531]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_24,negated_conjecture,
% 2.32/0.99      ( v1_funct_1(sK4) ),
% 2.32/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_29,plain,
% 2.32/0.99      ( v1_funct_1(sK4) = iProver_top ),
% 2.32/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_1669,plain,( X0 = X0 ),theory(equality) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_2211,plain,
% 2.32/0.99      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 2.32/0.99      inference(instantiation,[status(thm)],[c_1669]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_542,plain,
% 2.32/0.99      ( ~ v1_relat_1(X0)
% 2.32/0.99      | v1_relat_1(X1)
% 2.32/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(X0)
% 2.32/0.99      | sK4 != X1 ),
% 2.32/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_22]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_543,plain,
% 2.32/0.99      ( ~ v1_relat_1(X0)
% 2.32/0.99      | v1_relat_1(sK4)
% 2.32/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(X0) ),
% 2.32/0.99      inference(unflattening,[status(thm)],[c_542]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_2202,plain,
% 2.32/0.99      ( ~ v1_relat_1(k2_zfmisc_1(X0,X1))
% 2.32/0.99      | v1_relat_1(sK4)
% 2.32/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.32/0.99      inference(instantiation,[status(thm)],[c_543]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_2428,plain,
% 2.32/0.99      ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK2))
% 2.32/0.99      | v1_relat_1(sK4)
% 2.32/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 2.32/0.99      inference(instantiation,[status(thm)],[c_2202]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_2429,plain,
% 2.32/0.99      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.32/0.99      | v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
% 2.32/0.99      | v1_relat_1(sK4) = iProver_top ),
% 2.32/0.99      inference(predicate_to_equality,[status(thm)],[c_2428]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_7,plain,
% 2.32/0.99      ( v4_relat_1(X0,X1)
% 2.32/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.32/0.99      inference(cnf_transformation,[],[f44]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_5,plain,
% 2.32/0.99      ( r1_tarski(k1_relat_1(X0),X1)
% 2.32/0.99      | ~ v4_relat_1(X0,X1)
% 2.32/0.99      | ~ v1_relat_1(X0) ),
% 2.32/0.99      inference(cnf_transformation,[],[f41]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_261,plain,
% 2.32/0.99      ( r1_tarski(k1_relat_1(X0),X1)
% 2.32/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.32/0.99      | ~ v1_relat_1(X0) ),
% 2.32/0.99      inference(resolution,[status(thm)],[c_7,c_5]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_632,plain,
% 2.32/0.99      ( r1_tarski(k1_relat_1(X0),X1)
% 2.32/0.99      | ~ v1_relat_1(X0)
% 2.32/0.99      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.32/0.99      | sK3 != X0 ),
% 2.32/0.99      inference(resolution_lifted,[status(thm)],[c_261,c_25]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_633,plain,
% 2.32/0.99      ( r1_tarski(k1_relat_1(sK3),X0)
% 2.32/0.99      | ~ v1_relat_1(sK3)
% 2.32/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 2.32/0.99      inference(unflattening,[status(thm)],[c_632]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_1946,plain,
% 2.32/0.99      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.32/0.99      | r1_tarski(k1_relat_1(sK3),X0) = iProver_top
% 2.32/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.32/0.99      inference(predicate_to_equality,[status(thm)],[c_633]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_634,plain,
% 2.32/0.99      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.32/0.99      | r1_tarski(k1_relat_1(sK3),X0) = iProver_top
% 2.32/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.32/0.99      inference(predicate_to_equality,[status(thm)],[c_633]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_2782,plain,
% 2.32/0.99      ( r1_tarski(k1_relat_1(sK3),X0) = iProver_top
% 2.32/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 2.32/0.99      inference(global_propositional_subsumption,
% 2.32/0.99                [status(thm)],
% 2.32/0.99                [c_1946,c_634,c_2608,c_2637]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_2783,plain,
% 2.32/0.99      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.32/0.99      | r1_tarski(k1_relat_1(sK3),X0) = iProver_top ),
% 2.32/0.99      inference(renaming,[status(thm)],[c_2782]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_2792,plain,
% 2.32/0.99      ( r1_tarski(k1_relat_1(sK3),sK1) = iProver_top ),
% 2.32/0.99      inference(equality_resolution,[status(thm)],[c_2783]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_3606,plain,
% 2.32/0.99      ( r1_partfun1(sK3,sK4) = iProver_top
% 2.32/0.99      | sK2 = k1_xboole_0
% 2.32/0.99      | k1_funct_1(sK3,sK0(sK3,sK4)) = k1_funct_1(sK4,sK0(sK3,sK4)) ),
% 2.32/0.99      inference(global_propositional_subsumption,
% 2.32/0.99                [status(thm)],
% 2.32/0.99                [c_3542,c_29,c_2211,c_2429,c_2637,c_2792]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_3607,plain,
% 2.32/0.99      ( k1_funct_1(sK3,sK0(sK3,sK4)) = k1_funct_1(sK4,sK0(sK3,sK4))
% 2.32/0.99      | sK2 = k1_xboole_0
% 2.32/0.99      | r1_partfun1(sK3,sK4) = iProver_top ),
% 2.32/0.99      inference(renaming,[status(thm)],[c_3606]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_19,negated_conjecture,
% 2.32/0.99      ( r2_hidden(sK5,k1_relset_1(sK1,sK2,sK3))
% 2.32/0.99      | ~ r1_partfun1(sK3,sK4) ),
% 2.32/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_1953,plain,
% 2.32/0.99      ( r2_hidden(sK5,k1_relset_1(sK1,sK2,sK3)) = iProver_top
% 2.32/0.99      | r1_partfun1(sK3,sK4) != iProver_top ),
% 2.32/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_2461,plain,
% 2.32/0.99      ( r2_hidden(sK5,k1_relat_1(sK3)) = iProver_top
% 2.32/0.99      | r1_partfun1(sK3,sK4) != iProver_top ),
% 2.32/0.99      inference(demodulation,[status(thm)],[c_2268,c_1953]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_17,plain,
% 2.32/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.32/0.99      | ~ r1_partfun1(X1,X2)
% 2.32/0.99      | ~ r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
% 2.32/0.99      | ~ v1_funct_1(X2)
% 2.32/0.99      | ~ v1_funct_1(X1)
% 2.32/0.99      | ~ v1_relat_1(X1)
% 2.32/0.99      | ~ v1_relat_1(X2)
% 2.32/0.99      | k1_funct_1(X2,X0) = k1_funct_1(X1,X0) ),
% 2.32/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_1955,plain,
% 2.32/0.99      ( k1_funct_1(X0,X1) = k1_funct_1(X2,X1)
% 2.32/0.99      | r2_hidden(X1,k1_relat_1(X2)) != iProver_top
% 2.32/0.99      | r1_partfun1(X2,X0) != iProver_top
% 2.32/0.99      | r1_tarski(k1_relat_1(X2),k1_relat_1(X0)) != iProver_top
% 2.32/0.99      | v1_funct_1(X0) != iProver_top
% 2.32/0.99      | v1_funct_1(X2) != iProver_top
% 2.32/0.99      | v1_relat_1(X2) != iProver_top
% 2.32/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.32/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_3037,plain,
% 2.32/0.99      ( k1_funct_1(X0,X1) = k1_funct_1(sK4,X1)
% 2.32/0.99      | sK2 = k1_xboole_0
% 2.32/0.99      | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
% 2.32/0.99      | r1_partfun1(X0,sK4) != iProver_top
% 2.32/0.99      | r1_tarski(k1_relat_1(X0),sK1) != iProver_top
% 2.32/0.99      | v1_funct_1(X0) != iProver_top
% 2.32/0.99      | v1_funct_1(sK4) != iProver_top
% 2.32/0.99      | v1_relat_1(X0) != iProver_top
% 2.32/0.99      | v1_relat_1(sK4) != iProver_top ),
% 2.32/0.99      inference(superposition,[status(thm)],[c_2909,c_1955]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_3655,plain,
% 2.32/0.99      ( v1_relat_1(X0) != iProver_top
% 2.32/0.99      | k1_funct_1(X0,X1) = k1_funct_1(sK4,X1)
% 2.32/0.99      | sK2 = k1_xboole_0
% 2.32/0.99      | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
% 2.32/0.99      | r1_partfun1(X0,sK4) != iProver_top
% 2.32/0.99      | r1_tarski(k1_relat_1(X0),sK1) != iProver_top
% 2.32/0.99      | v1_funct_1(X0) != iProver_top ),
% 2.32/0.99      inference(global_propositional_subsumption,
% 2.32/0.99                [status(thm)],
% 2.32/0.99                [c_3037,c_29,c_2211,c_2429,c_2637]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_3656,plain,
% 2.32/0.99      ( k1_funct_1(X0,X1) = k1_funct_1(sK4,X1)
% 2.32/0.99      | sK2 = k1_xboole_0
% 2.32/0.99      | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
% 2.32/0.99      | r1_partfun1(X0,sK4) != iProver_top
% 2.32/0.99      | r1_tarski(k1_relat_1(X0),sK1) != iProver_top
% 2.32/0.99      | v1_funct_1(X0) != iProver_top
% 2.32/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.32/0.99      inference(renaming,[status(thm)],[c_3655]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_3669,plain,
% 2.32/0.99      ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
% 2.32/0.99      | sK2 = k1_xboole_0
% 2.32/0.99      | r1_partfun1(sK3,sK4) != iProver_top
% 2.32/0.99      | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top
% 2.32/0.99      | v1_funct_1(sK3) != iProver_top
% 2.32/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.32/0.99      inference(superposition,[status(thm)],[c_2461,c_3656]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_3706,plain,
% 2.32/0.99      ( r1_partfun1(sK3,sK4) != iProver_top
% 2.32/0.99      | sK2 = k1_xboole_0
% 2.32/0.99      | k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5) ),
% 2.32/0.99      inference(global_propositional_subsumption,
% 2.32/0.99                [status(thm)],
% 2.32/0.99                [c_3669,c_27,c_2608,c_2637,c_2792]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_3707,plain,
% 2.32/0.99      ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
% 2.32/0.99      | sK2 = k1_xboole_0
% 2.32/0.99      | r1_partfun1(sK3,sK4) != iProver_top ),
% 2.32/0.99      inference(renaming,[status(thm)],[c_3706]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_3713,plain,
% 2.32/0.99      ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
% 2.32/0.99      | k1_funct_1(sK3,sK0(sK3,sK4)) = k1_funct_1(sK4,sK0(sK3,sK4))
% 2.32/0.99      | sK2 = k1_xboole_0 ),
% 2.32/0.99      inference(superposition,[status(thm)],[c_3607,c_3707]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_15,plain,
% 2.32/0.99      ( r1_partfun1(X0,X1)
% 2.32/0.99      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 2.32/0.99      | ~ v1_funct_1(X1)
% 2.32/0.99      | ~ v1_funct_1(X0)
% 2.32/0.99      | ~ v1_relat_1(X0)
% 2.32/0.99      | ~ v1_relat_1(X1)
% 2.32/0.99      | k1_funct_1(X1,sK0(X0,X1)) != k1_funct_1(X0,sK0(X0,X1)) ),
% 2.32/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_1957,plain,
% 2.32/0.99      ( k1_funct_1(X0,sK0(X1,X0)) != k1_funct_1(X1,sK0(X1,X0))
% 2.32/0.99      | r1_partfun1(X1,X0) = iProver_top
% 2.32/0.99      | r1_tarski(k1_relat_1(X1),k1_relat_1(X0)) != iProver_top
% 2.32/0.99      | v1_funct_1(X0) != iProver_top
% 2.32/0.99      | v1_funct_1(X1) != iProver_top
% 2.32/0.99      | v1_relat_1(X0) != iProver_top
% 2.32/0.99      | v1_relat_1(X1) != iProver_top ),
% 2.32/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_3762,plain,
% 2.32/0.99      ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
% 2.32/0.99      | sK2 = k1_xboole_0
% 2.32/0.99      | r1_partfun1(sK3,sK4) = iProver_top
% 2.32/0.99      | r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4)) != iProver_top
% 2.32/0.99      | v1_funct_1(sK4) != iProver_top
% 2.32/0.99      | v1_funct_1(sK3) != iProver_top
% 2.32/0.99      | v1_relat_1(sK4) != iProver_top
% 2.32/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.32/0.99      inference(superposition,[status(thm)],[c_3713,c_1957]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_3802,plain,
% 2.32/0.99      ( sK2 = k1_xboole_0
% 2.32/0.99      | k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
% 2.32/0.99      | r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4)) != iProver_top ),
% 2.32/0.99      inference(global_propositional_subsumption,
% 2.32/0.99                [status(thm)],
% 2.32/0.99                [c_3762,c_27,c_29,c_2211,c_2429,c_2608,c_2637,c_2792,
% 2.32/0.99                 c_3669]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_3803,plain,
% 2.32/0.99      ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
% 2.32/0.99      | sK2 = k1_xboole_0
% 2.32/0.99      | r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4)) != iProver_top ),
% 2.32/0.99      inference(renaming,[status(thm)],[c_3802]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_3809,plain,
% 2.32/0.99      ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
% 2.32/0.99      | sK2 = k1_xboole_0
% 2.32/0.99      | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top ),
% 2.32/0.99      inference(superposition,[status(thm)],[c_2909,c_3803]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_3812,plain,
% 2.32/0.99      ( sK2 = k1_xboole_0 | k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5) ),
% 2.32/0.99      inference(global_propositional_subsumption,
% 2.32/0.99                [status(thm)],
% 2.32/0.99                [c_3809,c_2792]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_3813,plain,
% 2.32/0.99      ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5) | sK2 = k1_xboole_0 ),
% 2.32/0.99      inference(renaming,[status(thm)],[c_3812]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_18,negated_conjecture,
% 2.32/0.99      ( ~ r1_partfun1(sK3,sK4)
% 2.32/0.99      | k1_funct_1(sK3,sK5) != k1_funct_1(sK4,sK5) ),
% 2.32/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_1954,plain,
% 2.32/0.99      ( k1_funct_1(sK3,sK5) != k1_funct_1(sK4,sK5)
% 2.32/0.99      | r1_partfun1(sK3,sK4) != iProver_top ),
% 2.32/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_3816,plain,
% 2.32/0.99      ( sK2 = k1_xboole_0 | r1_partfun1(sK3,sK4) != iProver_top ),
% 2.32/0.99      inference(superposition,[status(thm)],[c_3813,c_1954]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_3858,plain,
% 2.32/0.99      ( k1_funct_1(sK3,sK0(sK3,sK4)) = k1_funct_1(sK4,sK0(sK3,sK4))
% 2.32/0.99      | sK2 = k1_xboole_0 ),
% 2.32/0.99      inference(superposition,[status(thm)],[c_3607,c_3816]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_3861,plain,
% 2.32/0.99      ( sK2 = k1_xboole_0
% 2.32/0.99      | r1_partfun1(sK3,sK4) = iProver_top
% 2.32/0.99      | r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4)) != iProver_top
% 2.32/0.99      | v1_funct_1(sK4) != iProver_top
% 2.32/0.99      | v1_funct_1(sK3) != iProver_top
% 2.32/0.99      | v1_relat_1(sK4) != iProver_top
% 2.32/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.32/0.99      inference(superposition,[status(thm)],[c_3858,c_1957]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_3976,plain,
% 2.32/0.99      ( sK2 = k1_xboole_0
% 2.32/0.99      | r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4)) != iProver_top ),
% 2.32/0.99      inference(global_propositional_subsumption,
% 2.32/0.99                [status(thm)],
% 2.32/0.99                [c_3861,c_27,c_29,c_2211,c_2429,c_2608,c_2637,c_3816]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_3982,plain,
% 2.32/0.99      ( sK2 = k1_xboole_0
% 2.32/0.99      | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top ),
% 2.32/0.99      inference(superposition,[status(thm)],[c_2909,c_3976]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_3985,plain,
% 2.32/0.99      ( sK2 = k1_xboole_0 ),
% 2.32/0.99      inference(global_propositional_subsumption,
% 2.32/0.99                [status(thm)],
% 2.32/0.99                [c_3982,c_2792]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_13,plain,
% 2.32/0.99      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 2.32/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.32/0.99      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 2.32/0.99      inference(cnf_transformation,[],[f70]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_762,plain,
% 2.32/0.99      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 2.32/0.99      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 2.32/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.32/0.99      | sK4 != X0 ),
% 2.32/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_22]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_763,plain,
% 2.32/0.99      ( ~ v1_funct_2(sK4,k1_xboole_0,X0)
% 2.32/0.99      | k1_relset_1(k1_xboole_0,X0,sK4) = k1_xboole_0
% 2.32/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 2.32/0.99      inference(unflattening,[status(thm)],[c_762]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_1504,plain,
% 2.32/0.99      ( k1_relset_1(k1_xboole_0,X0,sK4) = k1_xboole_0
% 2.32/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.32/0.99      | sK2 != X0
% 2.32/0.99      | sK1 != k1_xboole_0
% 2.32/0.99      | sK4 != sK4 ),
% 2.32/0.99      inference(resolution_lifted,[status(thm)],[c_23,c_763]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_1505,plain,
% 2.32/0.99      ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
% 2.32/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.32/0.99      | sK1 != k1_xboole_0 ),
% 2.32/0.99      inference(unflattening,[status(thm)],[c_1504]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_1,plain,
% 2.32/0.99      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.32/0.99      inference(cnf_transformation,[],[f65]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_2012,plain,
% 2.32/0.99      ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
% 2.32/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k1_xboole_0)
% 2.32/0.99      | sK1 != k1_xboole_0 ),
% 2.32/0.99      inference(demodulation,[status(thm)],[c_1505,c_1]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_4000,plain,
% 2.32/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
% 2.32/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)) != k1_zfmisc_1(k1_xboole_0)
% 2.32/0.99      | sK1 != k1_xboole_0 ),
% 2.32/0.99      inference(demodulation,[status(thm)],[c_3985,c_2012]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_21,negated_conjecture,
% 2.32/0.99      ( k1_xboole_0 != sK2 | k1_xboole_0 = sK1 ),
% 2.32/0.99      inference(cnf_transformation,[],[f60]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_4012,plain,
% 2.32/0.99      ( sK1 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 2.32/0.99      inference(demodulation,[status(thm)],[c_3985,c_21]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_4013,plain,
% 2.32/0.99      ( sK1 = k1_xboole_0 ),
% 2.32/0.99      inference(equality_resolution_simp,[status(thm)],[c_4012]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_4082,plain,
% 2.32/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
% 2.32/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k1_xboole_0)
% 2.32/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 2.32/0.99      inference(light_normalisation,[status(thm)],[c_4000,c_4013]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_4083,plain,
% 2.32/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
% 2.32/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k1_xboole_0) ),
% 2.32/0.99      inference(equality_resolution_simp,[status(thm)],[c_4082]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_2376,plain,
% 2.32/0.99      ( k1_relset_1(k1_xboole_0,X0,sK4) = k1_relat_1(sK4)
% 2.32/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k1_xboole_0) ),
% 2.32/0.99      inference(superposition,[status(thm)],[c_1,c_624]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_4003,plain,
% 2.32/0.99      ( k1_relset_1(k1_xboole_0,X0,sK4) = k1_relat_1(sK4)
% 2.32/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)) != k1_zfmisc_1(k1_xboole_0) ),
% 2.32/0.99      inference(demodulation,[status(thm)],[c_3985,c_2376]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_4064,plain,
% 2.32/0.99      ( k1_relset_1(k1_xboole_0,X0,sK4) = k1_relat_1(sK4)
% 2.32/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k1_xboole_0) ),
% 2.32/0.99      inference(light_normalisation,[status(thm)],[c_4003,c_4013]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_4067,plain,
% 2.32/0.99      ( k1_relset_1(k1_xboole_0,X0,sK4) = k1_relat_1(sK4)
% 2.32/0.99      | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0) ),
% 2.32/0.99      inference(demodulation,[status(thm)],[c_4064,c_1]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_4068,plain,
% 2.32/0.99      ( k1_relset_1(k1_xboole_0,X0,sK4) = k1_relat_1(sK4) ),
% 2.32/0.99      inference(equality_resolution_simp,[status(thm)],[c_4067]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_4084,plain,
% 2.32/0.99      ( k1_relat_1(sK4) = k1_xboole_0
% 2.32/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k1_xboole_0) ),
% 2.32/0.99      inference(demodulation,[status(thm)],[c_4083,c_4068]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_4087,plain,
% 2.32/0.99      ( k1_relat_1(sK4) = k1_xboole_0
% 2.32/0.99      | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0) ),
% 2.32/0.99      inference(demodulation,[status(thm)],[c_4084,c_1]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_4088,plain,
% 2.32/0.99      ( k1_relat_1(sK4) = k1_xboole_0 ),
% 2.32/0.99      inference(equality_resolution_simp,[status(thm)],[c_4087]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_4375,plain,
% 2.32/0.99      ( k1_funct_1(sK3,sK0(sK3,sK4)) = k1_funct_1(sK4,sK0(sK3,sK4))
% 2.32/0.99      | r1_partfun1(sK3,sK4) = iProver_top
% 2.32/0.99      | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top
% 2.32/0.99      | v1_funct_1(sK4) != iProver_top
% 2.32/0.99      | v1_relat_1(sK4) != iProver_top ),
% 2.32/0.99      inference(superposition,[status(thm)],[c_4088,c_3531]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_2,plain,
% 2.32/0.99      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 2.32/0.99      | k1_xboole_0 = X1
% 2.32/0.99      | k1_xboole_0 = X0 ),
% 2.32/0.99      inference(cnf_transformation,[],[f37]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_80,plain,
% 2.32/0.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 2.32/0.99      | k1_xboole_0 = k1_xboole_0 ),
% 2.32/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_81,plain,
% 2.32/0.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 2.32/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_636,plain,
% 2.32/0.99      ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.32/0.99      | r1_tarski(k1_relat_1(sK3),k1_xboole_0) = iProver_top
% 2.32/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.32/0.99      inference(instantiation,[status(thm)],[c_634]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_1673,plain,
% 2.32/0.99      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 2.32/0.99      theory(equality) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_2220,plain,
% 2.32/0.99      ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK1,sK2)
% 2.32/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 2.32/0.99      inference(instantiation,[status(thm)],[c_1673]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_2221,plain,
% 2.32/0.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k2_zfmisc_1(sK1,sK2)
% 2.32/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 2.32/0.99      inference(instantiation,[status(thm)],[c_2220]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_1670,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_2238,plain,
% 2.32/0.99      ( sK2 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK2 ),
% 2.32/0.99      inference(instantiation,[status(thm)],[c_1670]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_2239,plain,
% 2.32/0.99      ( sK2 != k1_xboole_0
% 2.32/0.99      | k1_xboole_0 = sK2
% 2.32/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 2.32/0.99      inference(instantiation,[status(thm)],[c_2238]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_1671,plain,
% 2.32/0.99      ( X0 != X1 | X2 != X3 | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
% 2.32/0.99      theory(equality) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_2433,plain,
% 2.32/0.99      ( X0 != sK2
% 2.32/0.99      | X1 != sK1
% 2.32/0.99      | k2_zfmisc_1(X1,X0) = k2_zfmisc_1(sK1,sK2) ),
% 2.32/0.99      inference(instantiation,[status(thm)],[c_1671]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_2434,plain,
% 2.32/0.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k2_zfmisc_1(sK1,sK2)
% 2.32/0.99      | k1_xboole_0 != sK2
% 2.32/0.99      | k1_xboole_0 != sK1 ),
% 2.32/0.99      inference(instantiation,[status(thm)],[c_2433]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_2599,plain,
% 2.32/0.99      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 2.32/0.99      inference(instantiation,[status(thm)],[c_1670]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_2600,plain,
% 2.32/0.99      ( sK1 != k1_xboole_0
% 2.32/0.99      | k1_xboole_0 = sK1
% 2.32/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 2.32/0.99      inference(instantiation,[status(thm)],[c_2599]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_10,plain,
% 2.32/0.99      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 2.32/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 2.32/0.99      | k1_xboole_0 = X1
% 2.32/0.99      | k1_xboole_0 = X0 ),
% 2.32/0.99      inference(cnf_transformation,[],[f68]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_726,plain,
% 2.32/0.99      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 2.32/0.99      | k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.32/0.99      | sK4 != X0
% 2.32/0.99      | k1_xboole_0 = X1
% 2.32/0.99      | k1_xboole_0 = X0 ),
% 2.32/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_22]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_727,plain,
% 2.32/0.99      ( ~ v1_funct_2(sK4,X0,k1_xboole_0)
% 2.32/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.32/0.99      | k1_xboole_0 = X0
% 2.32/0.99      | k1_xboole_0 = sK4 ),
% 2.32/0.99      inference(unflattening,[status(thm)],[c_726]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_1473,plain,
% 2.32/0.99      ( k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.32/0.99      | sK2 != k1_xboole_0
% 2.32/0.99      | sK1 != X0
% 2.32/0.99      | sK4 != sK4
% 2.32/0.99      | sK4 = k1_xboole_0
% 2.32/0.99      | k1_xboole_0 = X0 ),
% 2.32/0.99      inference(resolution_lifted,[status(thm)],[c_23,c_727]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_1474,plain,
% 2.32/0.99      ( k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.32/0.99      | sK2 != k1_xboole_0
% 2.32/0.99      | sK4 = k1_xboole_0
% 2.32/0.99      | k1_xboole_0 = sK1 ),
% 2.32/0.99      inference(unflattening,[status(thm)],[c_1473]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_0,plain,
% 2.32/0.99      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 2.32/0.99      inference(cnf_transformation,[],[f64]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_2019,plain,
% 2.32/0.99      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k1_xboole_0)
% 2.32/0.99      | sK2 != k1_xboole_0
% 2.32/0.99      | sK1 = k1_xboole_0
% 2.32/0.99      | sK4 = k1_xboole_0 ),
% 2.32/0.99      inference(demodulation,[status(thm)],[c_1474,c_0]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_2245,plain,
% 2.32/0.99      ( sK1 != X0 | sK1 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 2.32/0.99      inference(instantiation,[status(thm)],[c_1670]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_2398,plain,
% 2.32/0.99      ( sK1 != sK1 | sK1 = k1_xboole_0 | k1_xboole_0 != sK1 ),
% 2.32/0.99      inference(instantiation,[status(thm)],[c_2245]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_2399,plain,
% 2.32/0.99      ( sK1 = sK1 ),
% 2.32/0.99      inference(instantiation,[status(thm)],[c_1669]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_2735,plain,
% 2.32/0.99      ( sK1 = k1_xboole_0 | sK2 != k1_xboole_0 ),
% 2.32/0.99      inference(global_propositional_subsumption,
% 2.32/0.99                [status(thm)],
% 2.32/0.99                [c_2019,c_21,c_80,c_81,c_2239,c_2398,c_2399]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_2736,plain,
% 2.32/0.99      ( sK2 != k1_xboole_0 | sK1 = k1_xboole_0 ),
% 2.32/0.99      inference(renaming,[status(thm)],[c_2735]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_4697,plain,
% 2.32/0.99      ( r1_partfun1(sK3,sK4) = iProver_top
% 2.32/0.99      | k1_funct_1(sK3,sK0(sK3,sK4)) = k1_funct_1(sK4,sK0(sK3,sK4)) ),
% 2.32/0.99      inference(global_propositional_subsumption,
% 2.32/0.99                [status(thm)],
% 2.32/0.99                [c_4375,c_29,c_80,c_81,c_636,c_2211,c_2221,c_2239,c_2429,
% 2.32/0.99                 c_2434,c_2600,c_2608,c_2637,c_2736,c_2792,c_3982]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_4698,plain,
% 2.32/0.99      ( k1_funct_1(sK3,sK0(sK3,sK4)) = k1_funct_1(sK4,sK0(sK3,sK4))
% 2.32/0.99      | r1_partfun1(sK3,sK4) = iProver_top ),
% 2.32/0.99      inference(renaming,[status(thm)],[c_4697]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_4379,plain,
% 2.32/0.99      ( k1_funct_1(X0,X1) = k1_funct_1(sK4,X1)
% 2.32/0.99      | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
% 2.32/0.99      | r1_partfun1(X0,sK4) != iProver_top
% 2.32/0.99      | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
% 2.32/0.99      | v1_funct_1(X0) != iProver_top
% 2.32/0.99      | v1_funct_1(sK4) != iProver_top
% 2.32/0.99      | v1_relat_1(X0) != iProver_top
% 2.32/0.99      | v1_relat_1(sK4) != iProver_top ),
% 2.32/0.99      inference(superposition,[status(thm)],[c_4088,c_1955]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_4965,plain,
% 2.32/0.99      ( v1_relat_1(X0) != iProver_top
% 2.32/0.99      | k1_funct_1(X0,X1) = k1_funct_1(sK4,X1)
% 2.32/0.99      | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
% 2.32/0.99      | r1_partfun1(X0,sK4) != iProver_top
% 2.32/0.99      | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
% 2.32/0.99      | v1_funct_1(X0) != iProver_top ),
% 2.32/0.99      inference(global_propositional_subsumption,
% 2.32/0.99                [status(thm)],
% 2.32/0.99                [c_4379,c_29,c_2211,c_2429,c_2637]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_4966,plain,
% 2.32/0.99      ( k1_funct_1(X0,X1) = k1_funct_1(sK4,X1)
% 2.32/0.99      | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
% 2.32/0.99      | r1_partfun1(X0,sK4) != iProver_top
% 2.32/0.99      | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
% 2.32/0.99      | v1_funct_1(X0) != iProver_top
% 2.32/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.32/0.99      inference(renaming,[status(thm)],[c_4965]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_4978,plain,
% 2.32/0.99      ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
% 2.32/0.99      | r1_partfun1(sK3,sK4) != iProver_top
% 2.32/0.99      | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top
% 2.32/0.99      | v1_funct_1(sK3) != iProver_top
% 2.32/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.32/0.99      inference(superposition,[status(thm)],[c_2461,c_4966]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_5390,plain,
% 2.32/0.99      ( r1_partfun1(sK3,sK4) != iProver_top
% 2.32/0.99      | k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5) ),
% 2.32/0.99      inference(global_propositional_subsumption,
% 2.32/0.99                [status(thm)],
% 2.32/0.99                [c_4978,c_27,c_80,c_81,c_636,c_2221,c_2239,c_2434,c_2600,
% 2.32/0.99                 c_2608,c_2637,c_2736,c_2792,c_3982]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_5391,plain,
% 2.32/0.99      ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
% 2.32/0.99      | r1_partfun1(sK3,sK4) != iProver_top ),
% 2.32/0.99      inference(renaming,[status(thm)],[c_5390]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_5396,plain,
% 2.32/0.99      ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
% 2.32/0.99      | k1_funct_1(sK3,sK0(sK3,sK4)) = k1_funct_1(sK4,sK0(sK3,sK4)) ),
% 2.32/0.99      inference(superposition,[status(thm)],[c_4698,c_5391]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_5535,plain,
% 2.32/0.99      ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
% 2.32/0.99      | r1_partfun1(sK3,sK4) = iProver_top
% 2.32/0.99      | r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4)) != iProver_top
% 2.32/0.99      | v1_funct_1(sK4) != iProver_top
% 2.32/0.99      | v1_funct_1(sK3) != iProver_top
% 2.32/0.99      | v1_relat_1(sK4) != iProver_top
% 2.32/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.32/0.99      inference(superposition,[status(thm)],[c_5396,c_1957]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_5536,plain,
% 2.32/0.99      ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
% 2.32/0.99      | r1_partfun1(sK3,sK4) = iProver_top
% 2.32/0.99      | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top
% 2.32/0.99      | v1_funct_1(sK4) != iProver_top
% 2.32/0.99      | v1_funct_1(sK3) != iProver_top
% 2.32/0.99      | v1_relat_1(sK4) != iProver_top
% 2.32/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.32/0.99      inference(light_normalisation,[status(thm)],[c_5535,c_4088]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_635,plain,
% 2.32/0.99      ( r1_tarski(k1_relat_1(sK3),k1_xboole_0)
% 2.32/0.99      | ~ v1_relat_1(sK3)
% 2.32/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 2.32/0.99      inference(instantiation,[status(thm)],[c_633]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_2609,plain,
% 2.32/0.99      ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK2)) | v1_relat_1(sK3) ),
% 2.32/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_2608]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_5392,plain,
% 2.32/0.99      ( ~ r1_partfun1(sK3,sK4)
% 2.32/0.99      | k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5) ),
% 2.32/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_5391]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_5537,plain,
% 2.32/0.99      ( r1_partfun1(sK3,sK4)
% 2.32/0.99      | ~ r1_tarski(k1_relat_1(sK3),k1_xboole_0)
% 2.32/0.99      | ~ v1_funct_1(sK4)
% 2.32/0.99      | ~ v1_funct_1(sK3)
% 2.32/0.99      | ~ v1_relat_1(sK4)
% 2.32/0.99      | ~ v1_relat_1(sK3)
% 2.32/0.99      | k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5) ),
% 2.32/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_5536]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_5851,plain,
% 2.32/0.99      ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5) ),
% 2.32/0.99      inference(global_propositional_subsumption,
% 2.32/0.99                [status(thm)],
% 2.32/0.99                [c_5536,c_26,c_24,c_80,c_81,c_635,c_2211,c_2221,c_2239,
% 2.32/0.99                 c_2428,c_2434,c_2600,c_2609,c_2636,c_2736,c_2792,c_3982,
% 2.32/0.99                 c_5392,c_5537]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_5854,plain,
% 2.32/0.99      ( k1_funct_1(sK3,sK5) != k1_funct_1(sK3,sK5)
% 2.32/0.99      | r1_partfun1(sK3,sK4) != iProver_top ),
% 2.32/0.99      inference(demodulation,[status(thm)],[c_5851,c_1954]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_5874,plain,
% 2.32/0.99      ( r1_partfun1(sK3,sK4) != iProver_top ),
% 2.32/0.99      inference(equality_resolution_simp,[status(thm)],[c_5854]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_5877,plain,
% 2.32/0.99      ( k1_funct_1(sK3,sK0(sK3,sK4)) = k1_funct_1(sK4,sK0(sK3,sK4)) ),
% 2.32/0.99      inference(superposition,[status(thm)],[c_4698,c_5874]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_5892,plain,
% 2.32/0.99      ( r1_partfun1(sK3,sK4) = iProver_top
% 2.32/0.99      | r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4)) != iProver_top
% 2.32/0.99      | v1_funct_1(sK4) != iProver_top
% 2.32/0.99      | v1_funct_1(sK3) != iProver_top
% 2.32/0.99      | v1_relat_1(sK4) != iProver_top
% 2.32/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.32/0.99      inference(superposition,[status(thm)],[c_5877,c_1957]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_5893,plain,
% 2.32/0.99      ( r1_partfun1(sK3,sK4) = iProver_top
% 2.32/0.99      | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top
% 2.32/0.99      | v1_funct_1(sK4) != iProver_top
% 2.32/0.99      | v1_funct_1(sK3) != iProver_top
% 2.32/0.99      | v1_relat_1(sK4) != iProver_top
% 2.32/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.32/0.99      inference(light_normalisation,[status(thm)],[c_5892,c_4088]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(contradiction,plain,
% 2.32/0.99      ( $false ),
% 2.32/0.99      inference(minisat,
% 2.32/0.99                [status(thm)],
% 2.32/0.99                [c_5893,c_5874,c_3982,c_2792,c_2736,c_2637,c_2608,c_2600,
% 2.32/0.99                 c_2434,c_2429,c_2239,c_2221,c_2211,c_636,c_81,c_80,c_29,
% 2.32/0.99                 c_27]) ).
% 2.32/0.99  
% 2.32/0.99  
% 2.32/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.32/0.99  
% 2.32/0.99  ------                               Statistics
% 2.32/0.99  
% 2.32/0.99  ------ General
% 2.32/0.99  
% 2.32/0.99  abstr_ref_over_cycles:                  0
% 2.32/0.99  abstr_ref_under_cycles:                 0
% 2.32/0.99  gc_basic_clause_elim:                   0
% 2.32/0.99  forced_gc_time:                         0
% 2.32/0.99  parsing_time:                           0.01
% 2.32/0.99  unif_index_cands_time:                  0.
% 2.32/0.99  unif_index_add_time:                    0.
% 2.32/0.99  orderings_time:                         0.
% 2.32/0.99  out_proof_time:                         0.012
% 2.32/0.99  total_time:                             0.192
% 2.32/0.99  num_of_symbols:                         51
% 2.32/0.99  num_of_terms:                           3536
% 2.32/0.99  
% 2.32/0.99  ------ Preprocessing
% 2.32/0.99  
% 2.32/0.99  num_of_splits:                          0
% 2.32/0.99  num_of_split_atoms:                     0
% 2.32/0.99  num_of_reused_defs:                     0
% 2.32/0.99  num_eq_ax_congr_red:                    7
% 2.32/0.99  num_of_sem_filtered_clauses:            1
% 2.32/0.99  num_of_subtypes:                        0
% 2.32/0.99  monotx_restored_types:                  0
% 2.32/0.99  sat_num_of_epr_types:                   0
% 2.32/0.99  sat_num_of_non_cyclic_types:            0
% 2.32/0.99  sat_guarded_non_collapsed_types:        0
% 2.32/0.99  num_pure_diseq_elim:                    0
% 2.32/0.99  simp_replaced_by:                       0
% 2.32/0.99  res_preprocessed:                       110
% 2.32/0.99  prep_upred:                             0
% 2.32/0.99  prep_unflattend:                        109
% 2.32/0.99  smt_new_axioms:                         0
% 2.32/0.99  pred_elim_cands:                        8
% 2.32/0.99  pred_elim:                              3
% 2.32/0.99  pred_elim_cl:                           -2
% 2.32/0.99  pred_elim_cycles:                       8
% 2.32/0.99  merged_defs:                            0
% 2.32/0.99  merged_defs_ncl:                        0
% 2.32/0.99  bin_hyper_res:                          0
% 2.32/0.99  prep_cycles:                            3
% 2.32/0.99  pred_elim_time:                         0.029
% 2.32/0.99  splitting_time:                         0.
% 2.32/0.99  sem_filter_time:                        0.
% 2.32/0.99  monotx_time:                            0.001
% 2.32/0.99  subtype_inf_time:                       0.
% 2.32/0.99  
% 2.32/0.99  ------ Problem properties
% 2.32/0.99  
% 2.32/0.99  clauses:                                29
% 2.32/0.99  conjectures:                            6
% 2.32/0.99  epr:                                    3
% 2.32/0.99  horn:                                   20
% 2.32/0.99  ground:                                 11
% 2.32/0.99  unary:                                  5
% 2.32/0.99  binary:                                 5
% 2.32/0.99  lits:                                   96
% 2.32/0.99  lits_eq:                                60
% 2.32/0.99  fd_pure:                                0
% 2.32/0.99  fd_pseudo:                              0
% 2.32/0.99  fd_cond:                                1
% 2.32/0.99  fd_pseudo_cond:                         0
% 2.32/0.99  ac_symbols:                             0
% 2.32/0.99  
% 2.32/0.99  ------ Propositional Solver
% 2.32/0.99  
% 2.32/0.99  prop_solver_calls:                      25
% 2.32/0.99  prop_fast_solver_calls:                 1489
% 2.32/0.99  smt_solver_calls:                       0
% 2.32/0.99  smt_fast_solver_calls:                  0
% 2.32/0.99  prop_num_of_clauses:                    1589
% 2.32/0.99  prop_preprocess_simplified:             4956
% 2.32/0.99  prop_fo_subsumed:                       86
% 2.32/0.99  prop_solver_time:                       0.
% 2.32/0.99  smt_solver_time:                        0.
% 2.32/0.99  smt_fast_solver_time:                   0.
% 2.32/0.99  prop_fast_solver_time:                  0.
% 2.32/0.99  prop_unsat_core_time:                   0.
% 2.32/0.99  
% 2.32/0.99  ------ QBF
% 2.32/0.99  
% 2.32/0.99  qbf_q_res:                              0
% 2.32/0.99  qbf_num_tautologies:                    0
% 2.32/0.99  qbf_prep_cycles:                        0
% 2.32/0.99  
% 2.32/0.99  ------ BMC1
% 2.32/0.99  
% 2.32/0.99  bmc1_current_bound:                     -1
% 2.32/0.99  bmc1_last_solved_bound:                 -1
% 2.32/0.99  bmc1_unsat_core_size:                   -1
% 2.32/0.99  bmc1_unsat_core_parents_size:           -1
% 2.32/0.99  bmc1_merge_next_fun:                    0
% 2.32/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.32/0.99  
% 2.32/0.99  ------ Instantiation
% 2.32/0.99  
% 2.32/0.99  inst_num_of_clauses:                    715
% 2.32/0.99  inst_num_in_passive:                    350
% 2.32/0.99  inst_num_in_active:                     359
% 2.32/0.99  inst_num_in_unprocessed:                6
% 2.32/0.99  inst_num_of_loops:                      470
% 2.32/0.99  inst_num_of_learning_restarts:          0
% 2.32/0.99  inst_num_moves_active_passive:          107
% 2.32/0.99  inst_lit_activity:                      0
% 2.32/0.99  inst_lit_activity_moves:                0
% 2.32/0.99  inst_num_tautologies:                   0
% 2.32/0.99  inst_num_prop_implied:                  0
% 2.32/0.99  inst_num_existing_simplified:           0
% 2.32/0.99  inst_num_eq_res_simplified:             0
% 2.32/0.99  inst_num_child_elim:                    0
% 2.32/0.99  inst_num_of_dismatching_blockings:      148
% 2.32/0.99  inst_num_of_non_proper_insts:           624
% 2.32/0.99  inst_num_of_duplicates:                 0
% 2.32/0.99  inst_inst_num_from_inst_to_res:         0
% 2.32/0.99  inst_dismatching_checking_time:         0.
% 2.32/0.99  
% 2.32/0.99  ------ Resolution
% 2.32/0.99  
% 2.32/0.99  res_num_of_clauses:                     0
% 2.32/0.99  res_num_in_passive:                     0
% 2.32/0.99  res_num_in_active:                      0
% 2.32/0.99  res_num_of_loops:                       113
% 2.32/0.99  res_forward_subset_subsumed:            57
% 2.32/0.99  res_backward_subset_subsumed:           2
% 2.32/0.99  res_forward_subsumed:                   4
% 2.32/0.99  res_backward_subsumed:                  0
% 2.32/0.99  res_forward_subsumption_resolution:     0
% 2.32/0.99  res_backward_subsumption_resolution:    0
% 2.32/0.99  res_clause_to_clause_subsumption:       308
% 2.32/0.99  res_orphan_elimination:                 0
% 2.32/0.99  res_tautology_del:                      79
% 2.32/0.99  res_num_eq_res_simplified:              2
% 2.32/0.99  res_num_sel_changes:                    0
% 2.32/0.99  res_moves_from_active_to_pass:          0
% 2.32/0.99  
% 2.32/0.99  ------ Superposition
% 2.32/0.99  
% 2.32/0.99  sup_time_total:                         0.
% 2.32/0.99  sup_time_generating:                    0.
% 2.32/0.99  sup_time_sim_full:                      0.
% 2.32/0.99  sup_time_sim_immed:                     0.
% 2.32/0.99  
% 2.32/0.99  sup_num_of_clauses:                     54
% 2.32/0.99  sup_num_in_active:                      44
% 2.32/0.99  sup_num_in_passive:                     10
% 2.32/0.99  sup_num_of_loops:                       93
% 2.32/0.99  sup_fw_superposition:                   66
% 2.32/0.99  sup_bw_superposition:                   26
% 2.32/0.99  sup_immediate_simplified:               61
% 2.32/0.99  sup_given_eliminated:                   0
% 2.32/0.99  comparisons_done:                       0
% 2.32/0.99  comparisons_avoided:                    41
% 2.32/0.99  
% 2.32/0.99  ------ Simplifications
% 2.32/0.99  
% 2.32/0.99  
% 2.32/0.99  sim_fw_subset_subsumed:                 14
% 2.32/0.99  sim_bw_subset_subsumed:                 18
% 2.32/0.99  sim_fw_subsumed:                        2
% 2.32/0.99  sim_bw_subsumed:                        7
% 2.32/0.99  sim_fw_subsumption_res:                 3
% 2.32/0.99  sim_bw_subsumption_res:                 0
% 2.32/0.99  sim_tautology_del:                      3
% 2.32/0.99  sim_eq_tautology_del:                   19
% 2.32/0.99  sim_eq_res_simp:                        16
% 2.32/0.99  sim_fw_demodulated:                     25
% 2.32/0.99  sim_bw_demodulated:                     38
% 2.32/0.99  sim_light_normalised:                   24
% 2.32/0.99  sim_joinable_taut:                      0
% 2.32/0.99  sim_joinable_simp:                      0
% 2.32/0.99  sim_ac_normalised:                      0
% 2.32/0.99  sim_smt_subsumption:                    0
% 2.32/0.99  
%------------------------------------------------------------------------------
