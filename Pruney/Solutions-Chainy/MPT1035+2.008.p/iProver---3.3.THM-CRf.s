%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:08:40 EST 2020

% Result     : Theorem 2.07s
% Output     : CNFRefutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :  198 (56423 expanded)
%              Number of clauses        :  143 (17357 expanded)
%              Number of leaves         :   16 (13167 expanded)
%              Depth                    :   45
%              Number of atoms          :  798 (437142 expanded)
%              Number of equality atoms :  466 (147144 expanded)
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
    inference(nnf_transformation,[],[f23])).

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

fof(f56,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f6,axiom,(
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
    inference(ennf_transformation,[],[f6])).

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

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f57,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f36])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f7,axiom,(
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
    inference(ennf_transformation,[],[f7])).

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

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_partfun1(X0,X1)
      | r2_hidden(sK0(X0,X1),k1_relat_1(X0))
      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f54,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f36])).

fof(f59,plain,(
    ! [X5] :
      ( k1_funct_1(sK3,X5) = k1_funct_1(sK4,X5)
      | ~ r2_hidden(X5,k1_relset_1(sK1,sK2,sK3))
      | r1_partfun1(sK3,sK4) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f53,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f55,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f36])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f60,plain,
    ( r2_hidden(sK5,k1_relset_1(sK1,sK2,sK3))
    | ~ r1_partfun1(sK3,sK4) ),
    inference(cnf_transformation,[],[f36])).

fof(f49,plain,(
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

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_partfun1(X0,X1)
      | k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1))
      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f61,plain,
    ( k1_funct_1(sK3,sK5) != k1_funct_1(sK4,sK5)
    | ~ r1_partfun1(sK3,sK4) ),
    inference(cnf_transformation,[],[f36])).

fof(f58,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f36])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f66,plain,(
    ! [X2,X1] :
      ( k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f44])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f64,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f47])).

cnf(c_21,negated_conjecture,
    ( v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_593,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_20])).

cnf(c_594,plain,
    ( ~ v1_funct_2(sK4,X0,X1)
    | k1_relset_1(X0,X1,sK4) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_593])).

cnf(c_1504,plain,
    ( k1_relset_1(X0,X1,sK4) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sK2 != X1
    | sK1 != X0
    | sK4 != sK4
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_594])).

cnf(c_1505,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_1504])).

cnf(c_2101,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(equality_resolution_simp,[status(thm)],[c_1505])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_629,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_20])).

cnf(c_630,plain,
    ( k1_relset_1(X0,X1,sK4) = k1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(unflattening,[status(thm)],[c_629])).

cnf(c_2336,plain,
    ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
    inference(equality_resolution,[status(thm)],[c_630])).

cnf(c_2938,plain,
    ( k1_relat_1(sK4) = sK1
    | sK2 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2101,c_2336])).

cnf(c_13,plain,
    ( r2_hidden(sK0(X0,X1),k1_relat_1(X0))
    | r1_partfun1(X0,X1)
    | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2060,plain,
    ( r2_hidden(sK0(X0,X1),k1_relat_1(X0)) = iProver_top
    | r1_partfun1(X0,X1) = iProver_top
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_689,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_23])).

cnf(c_690,plain,
    ( k1_relset_1(X0,X1,sK3) = k1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(unflattening,[status(thm)],[c_689])).

cnf(c_2369,plain,
    ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
    inference(equality_resolution,[status(thm)],[c_690])).

cnf(c_18,negated_conjecture,
    ( ~ r2_hidden(X0,k1_relset_1(sK1,sK2,sK3))
    | r1_partfun1(sK3,sK4)
    | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2056,plain,
    ( k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0)
    | r2_hidden(X0,k1_relset_1(sK1,sK2,sK3)) != iProver_top
    | r1_partfun1(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2569,plain,
    ( k1_funct_1(sK4,X0) = k1_funct_1(sK3,X0)
    | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | r1_partfun1(sK3,sK4) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2369,c_2056])).

cnf(c_2746,plain,
    ( k1_funct_1(sK3,sK0(sK3,X0)) = k1_funct_1(sK4,sK0(sK3,X0))
    | r1_partfun1(sK3,X0) = iProver_top
    | r1_partfun1(sK3,sK4) = iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2060,c_2569])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_25,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_1773,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2311,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_1773])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_563,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_23])).

cnf(c_564,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_563])).

cnf(c_2301,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(X0,X1))
    | v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_564])).

cnf(c_2478,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK2))
    | v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_2301])).

cnf(c_2479,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2478])).

cnf(c_3,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_2585,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2586,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2585])).

cnf(c_3173,plain,
    ( v1_relat_1(X0) != iProver_top
    | k1_funct_1(sK3,sK0(sK3,X0)) = k1_funct_1(sK4,sK0(sK3,X0))
    | r1_partfun1(sK3,X0) = iProver_top
    | r1_partfun1(sK3,sK4) = iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2746,c_25,c_2311,c_2479,c_2586])).

cnf(c_3174,plain,
    ( k1_funct_1(sK3,sK0(sK3,X0)) = k1_funct_1(sK4,sK0(sK3,X0))
    | r1_partfun1(sK3,X0) = iProver_top
    | r1_partfun1(sK3,sK4) = iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3173])).

cnf(c_3185,plain,
    ( k1_funct_1(sK4,sK0(sK3,sK4)) = k1_funct_1(sK3,sK0(sK3,sK4))
    | sK2 = k1_xboole_0
    | r1_partfun1(sK3,sK4) = iProver_top
    | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2938,c_3174])).

cnf(c_22,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_27,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_548,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_20])).

cnf(c_549,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_548])).

cnf(c_2302,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(X0,X1))
    | v1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_549])).

cnf(c_2485,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK2))
    | v1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_2302])).

cnf(c_2486,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2485])).

cnf(c_4,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_2,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_267,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_4,c_2])).

cnf(c_638,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_267,c_23])).

cnf(c_639,plain,
    ( r1_tarski(k1_relat_1(sK3),X0)
    | ~ v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(unflattening,[status(thm)],[c_638])).

cnf(c_2050,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | r1_tarski(k1_relat_1(sK3),X0) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_639])).

cnf(c_640,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | r1_tarski(k1_relat_1(sK3),X0) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_639])).

cnf(c_2822,plain,
    ( r1_tarski(k1_relat_1(sK3),X0) = iProver_top
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2050,c_640,c_2311,c_2479,c_2586])).

cnf(c_2823,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | r1_tarski(k1_relat_1(sK3),X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_2822])).

cnf(c_2830,plain,
    ( r1_tarski(k1_relat_1(sK3),sK1) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2823])).

cnf(c_3748,plain,
    ( r1_partfun1(sK3,sK4) = iProver_top
    | sK2 = k1_xboole_0
    | k1_funct_1(sK4,sK0(sK3,sK4)) = k1_funct_1(sK3,sK0(sK3,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3185,c_27,c_2311,c_2486,c_2586,c_2830])).

cnf(c_3749,plain,
    ( k1_funct_1(sK4,sK0(sK3,sK4)) = k1_funct_1(sK3,sK0(sK3,sK4))
    | sK2 = k1_xboole_0
    | r1_partfun1(sK3,sK4) = iProver_top ),
    inference(renaming,[status(thm)],[c_3748])).

cnf(c_17,negated_conjecture,
    ( r2_hidden(sK5,k1_relset_1(sK1,sK2,sK3))
    | ~ r1_partfun1(sK3,sK4) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2057,plain,
    ( r2_hidden(sK5,k1_relset_1(sK1,sK2,sK3)) = iProver_top
    | r1_partfun1(sK3,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2570,plain,
    ( r2_hidden(sK5,k1_relat_1(sK3)) = iProver_top
    | r1_partfun1(sK3,sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2369,c_2057])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r1_partfun1(X1,X2)
    | ~ r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = k1_funct_1(X1,X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2059,plain,
    ( k1_funct_1(X0,X1) = k1_funct_1(X2,X1)
    | r2_hidden(X1,k1_relat_1(X2)) != iProver_top
    | r1_partfun1(X2,X0) != iProver_top
    | r1_tarski(k1_relat_1(X2),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2943,plain,
    ( k1_funct_1(X0,X1) = k1_funct_1(sK4,X1)
    | sK2 = k1_xboole_0
    | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
    | r1_partfun1(X0,sK4) != iProver_top
    | r1_tarski(k1_relat_1(X0),sK1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2938,c_2059])).

cnf(c_3309,plain,
    ( v1_relat_1(X0) != iProver_top
    | k1_funct_1(X0,X1) = k1_funct_1(sK4,X1)
    | sK2 = k1_xboole_0
    | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
    | r1_partfun1(X0,sK4) != iProver_top
    | r1_tarski(k1_relat_1(X0),sK1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2943,c_27,c_2311,c_2486,c_2586])).

cnf(c_3310,plain,
    ( k1_funct_1(X0,X1) = k1_funct_1(sK4,X1)
    | sK2 = k1_xboole_0
    | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
    | r1_partfun1(X0,sK4) != iProver_top
    | r1_tarski(k1_relat_1(X0),sK1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3309])).

cnf(c_3323,plain,
    ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
    | sK2 = k1_xboole_0
    | r1_partfun1(sK3,sK4) != iProver_top
    | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2570,c_3310])).

cnf(c_3493,plain,
    ( r1_partfun1(sK3,sK4) != iProver_top
    | sK2 = k1_xboole_0
    | k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3323,c_25,c_2311,c_2479,c_2586,c_2830])).

cnf(c_3494,plain,
    ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
    | sK2 = k1_xboole_0
    | r1_partfun1(sK3,sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_3493])).

cnf(c_3755,plain,
    ( k1_funct_1(sK4,sK0(sK3,sK4)) = k1_funct_1(sK3,sK0(sK3,sK4))
    | k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3749,c_3494])).

cnf(c_12,plain,
    ( r1_partfun1(X0,X1)
    | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK0(X0,X1)) != k1_funct_1(X0,sK0(X0,X1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2061,plain,
    ( k1_funct_1(X0,sK0(X1,X0)) != k1_funct_1(X1,sK0(X1,X0))
    | r1_partfun1(X1,X0) = iProver_top
    | r1_tarski(k1_relat_1(X1),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3798,plain,
    ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
    | sK2 = k1_xboole_0
    | r1_partfun1(sK3,sK4) = iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3755,c_2061])).

cnf(c_2357,plain,
    ( r1_partfun1(X0,sK4)
    | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(sK4))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK4)
    | k1_funct_1(sK4,sK0(X0,sK4)) != k1_funct_1(X0,sK0(X0,sK4)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2410,plain,
    ( r1_partfun1(sK3,sK4)
    | ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK4)
    | ~ v1_relat_1(sK3)
    | k1_funct_1(sK4,sK0(sK3,sK4)) != k1_funct_1(sK3,sK0(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_2357])).

cnf(c_2411,plain,
    ( k1_funct_1(sK4,sK0(sK3,sK4)) != k1_funct_1(sK3,sK0(sK3,sK4))
    | r1_partfun1(sK3,sK4) = iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2410])).

cnf(c_3801,plain,
    ( sK2 = k1_xboole_0
    | r1_partfun1(sK3,sK4) = iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3798,c_25,c_27,c_2311,c_2411,c_2479,c_2486,c_2586,c_2830,c_3185])).

cnf(c_3808,plain,
    ( sK2 = k1_xboole_0
    | r1_partfun1(sK3,sK4) = iProver_top
    | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2938,c_3801])).

cnf(c_3851,plain,
    ( r1_partfun1(sK3,sK4) = iProver_top
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3808,c_2830])).

cnf(c_3852,plain,
    ( sK2 = k1_xboole_0
    | r1_partfun1(sK3,sK4) = iProver_top ),
    inference(renaming,[status(thm)],[c_3851])).

cnf(c_3857,plain,
    ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3852,c_3494])).

cnf(c_16,negated_conjecture,
    ( ~ r1_partfun1(sK3,sK4)
    | k1_funct_1(sK3,sK5) != k1_funct_1(sK4,sK5) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2058,plain,
    ( k1_funct_1(sK3,sK5) != k1_funct_1(sK4,sK5)
    | r1_partfun1(sK3,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3860,plain,
    ( sK2 = k1_xboole_0
    | r1_partfun1(sK3,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3857,c_2058])).

cnf(c_3896,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3860,c_2830,c_3808])).

cnf(c_3911,plain,
    ( k1_relset_1(sK1,k1_xboole_0,sK4) = k1_relat_1(sK4) ),
    inference(demodulation,[status(thm)],[c_3896,c_2336])).

cnf(c_19,negated_conjecture,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_3919,plain,
    ( sK1 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3896,c_19])).

cnf(c_3920,plain,
    ( sK1 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_3919])).

cnf(c_10,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_768,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_20])).

cnf(c_769,plain,
    ( ~ v1_funct_2(sK4,k1_xboole_0,X0)
    | k1_relset_1(k1_xboole_0,X0,sK4) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(unflattening,[status(thm)],[c_768])).

cnf(c_1560,plain,
    ( k1_relset_1(k1_xboole_0,X0,sK4) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sK2 != X0
    | sK1 != k1_xboole_0
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_769])).

cnf(c_1561,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sK1 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_1560])).

cnf(c_3916,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | sK1 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3896,c_1561])).

cnf(c_3933,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3916,c_3920])).

cnf(c_3934,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_3933])).

cnf(c_3944,plain,
    ( k1_relat_1(sK4) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3911,c_3920,c_3934])).

cnf(c_4076,plain,
    ( k1_funct_1(sK4,sK0(sK3,sK4)) = k1_funct_1(sK3,sK0(sK3,sK4))
    | r1_partfun1(sK3,sK4) = iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3944,c_3174])).

cnf(c_1796,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1773])).

cnf(c_1774,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2337,plain,
    ( sK2 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_1774])).

cnf(c_2338,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2337])).

cnf(c_7,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_732,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sK4 != X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_20])).

cnf(c_733,plain,
    ( ~ v1_funct_2(sK4,X0,k1_xboole_0)
    | k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | k1_xboole_0 = X0
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_732])).

cnf(c_1529,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sK2 != k1_xboole_0
    | sK1 != X0
    | sK4 != sK4
    | sK4 = k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_733])).

cnf(c_1530,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sK2 != k1_xboole_0
    | sK4 = k1_xboole_0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_1529])).

cnf(c_2415,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1530,c_19,c_1796,c_2338])).

cnf(c_2437,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_1773])).

cnf(c_2344,plain,
    ( sK1 != X0
    | sK1 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1774])).

cnf(c_2439,plain,
    ( sK1 != sK1
    | sK1 = k1_xboole_0
    | k1_xboole_0 != sK1 ),
    inference(instantiation,[status(thm)],[c_2344])).

cnf(c_2440,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_1773])).

cnf(c_1779,plain,
    ( X0 != X1
    | X2 != X3
    | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
    theory(equality)).

cnf(c_2490,plain,
    ( X0 != sK2
    | X1 != sK1
    | k2_zfmisc_1(X1,X0) = k2_zfmisc_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1779])).

cnf(c_2608,plain,
    ( X0 != sK1
    | k2_zfmisc_1(X0,sK2) = k2_zfmisc_1(sK1,sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_2490])).

cnf(c_2609,plain,
    ( k2_zfmisc_1(k1_xboole_0,sK2) = k2_zfmisc_1(sK1,sK2)
    | sK2 != sK2
    | k1_xboole_0 != sK1 ),
    inference(instantiation,[status(thm)],[c_2608])).

cnf(c_2781,plain,
    ( r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4))
    | ~ v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_639])).

cnf(c_2782,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2781])).

cnf(c_2784,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2782])).

cnf(c_1776,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_2319,plain,
    ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK1,sK2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_1776])).

cnf(c_2921,plain,
    ( k2_zfmisc_1(k1_xboole_0,sK2) != k2_zfmisc_1(sK1,sK2)
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_2319])).

cnf(c_3116,plain,
    ( k2_zfmisc_1(k1_relat_1(sK4),X0) != k2_zfmisc_1(sK1,sK2)
    | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_2319])).

cnf(c_3117,plain,
    ( k2_zfmisc_1(k1_relat_1(sK4),k1_xboole_0) != k2_zfmisc_1(sK1,sK2)
    | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k1_xboole_0)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_3116])).

cnf(c_3817,plain,
    ( r1_tarski(k1_relat_1(sK3),k1_xboole_0)
    | ~ v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_639])).

cnf(c_3818,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | r1_tarski(k1_relat_1(sK3),k1_xboole_0) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3817])).

cnf(c_2657,plain,
    ( X0 != X1
    | X0 = sK1
    | sK1 != X1 ),
    inference(instantiation,[status(thm)],[c_1774])).

cnf(c_4058,plain,
    ( k1_relat_1(sK4) != X0
    | k1_relat_1(sK4) = sK1
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_2657])).

cnf(c_4059,plain,
    ( k1_relat_1(sK4) = sK1
    | k1_relat_1(sK4) != k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4058])).

cnf(c_4745,plain,
    ( X0 != sK2
    | k2_zfmisc_1(k1_relat_1(sK4),X0) = k2_zfmisc_1(sK1,sK2)
    | k1_relat_1(sK4) != sK1 ),
    inference(instantiation,[status(thm)],[c_2490])).

cnf(c_4746,plain,
    ( k2_zfmisc_1(k1_relat_1(sK4),k1_xboole_0) = k2_zfmisc_1(sK1,sK2)
    | k1_relat_1(sK4) != sK1
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_4745])).

cnf(c_4758,plain,
    ( r1_partfun1(sK3,sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4076,c_25,c_27,c_1796,c_2311,c_2338,c_2411,c_2415,c_2437,c_2439,c_2440,c_2479,c_2486,c_2586,c_2609,c_2784,c_2830,c_2921,c_3117,c_3808,c_3818,c_3860,c_3944,c_4059,c_4746])).

cnf(c_4079,plain,
    ( k1_funct_1(X0,X1) = k1_funct_1(sK4,X1)
    | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
    | r1_partfun1(X0,sK4) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3944,c_2059])).

cnf(c_4260,plain,
    ( v1_relat_1(X0) != iProver_top
    | k1_funct_1(X0,X1) = k1_funct_1(sK4,X1)
    | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
    | r1_partfun1(X0,sK4) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4079,c_27,c_2311,c_2486,c_2586])).

cnf(c_4261,plain,
    ( k1_funct_1(X0,X1) = k1_funct_1(sK4,X1)
    | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
    | r1_partfun1(X0,sK4) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4260])).

cnf(c_4273,plain,
    ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
    | r1_partfun1(sK3,sK4) != iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2570,c_4261])).

cnf(c_4435,plain,
    ( r1_partfun1(sK3,sK4) != iProver_top
    | k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4273,c_25,c_2311,c_2415,c_2437,c_2479,c_2586,c_2609,c_2830,c_2921,c_3808,c_3818,c_3860])).

cnf(c_4436,plain,
    ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
    | r1_partfun1(sK3,sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_4435])).

cnf(c_4763,plain,
    ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5) ),
    inference(superposition,[status(thm)],[c_4758,c_4436])).

cnf(c_4844,plain,
    ( k1_funct_1(sK3,sK5) != k1_funct_1(sK3,sK5)
    | r1_partfun1(sK3,sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4763,c_2058])).

cnf(c_4846,plain,
    ( r1_partfun1(sK3,sK4) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4844])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4846,c_4758])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:48:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.07/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/0.99  
% 2.07/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.07/0.99  
% 2.07/0.99  ------  iProver source info
% 2.07/0.99  
% 2.07/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.07/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.07/0.99  git: non_committed_changes: false
% 2.07/0.99  git: last_make_outside_of_git: false
% 2.07/0.99  
% 2.07/0.99  ------ 
% 2.07/0.99  
% 2.07/0.99  ------ Input Options
% 2.07/0.99  
% 2.07/0.99  --out_options                           all
% 2.07/0.99  --tptp_safe_out                         true
% 2.07/0.99  --problem_path                          ""
% 2.07/0.99  --include_path                          ""
% 2.07/0.99  --clausifier                            res/vclausify_rel
% 2.07/0.99  --clausifier_options                    --mode clausify
% 2.07/0.99  --stdin                                 false
% 2.07/0.99  --stats_out                             all
% 2.07/0.99  
% 2.07/0.99  ------ General Options
% 2.07/0.99  
% 2.07/0.99  --fof                                   false
% 2.07/0.99  --time_out_real                         305.
% 2.07/0.99  --time_out_virtual                      -1.
% 2.07/0.99  --symbol_type_check                     false
% 2.07/0.99  --clausify_out                          false
% 2.07/0.99  --sig_cnt_out                           false
% 2.07/0.99  --trig_cnt_out                          false
% 2.07/0.99  --trig_cnt_out_tolerance                1.
% 2.07/0.99  --trig_cnt_out_sk_spl                   false
% 2.07/0.99  --abstr_cl_out                          false
% 2.07/0.99  
% 2.07/0.99  ------ Global Options
% 2.07/0.99  
% 2.07/0.99  --schedule                              default
% 2.07/0.99  --add_important_lit                     false
% 2.07/0.99  --prop_solver_per_cl                    1000
% 2.07/0.99  --min_unsat_core                        false
% 2.07/0.99  --soft_assumptions                      false
% 2.07/0.99  --soft_lemma_size                       3
% 2.07/0.99  --prop_impl_unit_size                   0
% 2.07/0.99  --prop_impl_unit                        []
% 2.07/0.99  --share_sel_clauses                     true
% 2.07/0.99  --reset_solvers                         false
% 2.07/0.99  --bc_imp_inh                            [conj_cone]
% 2.07/0.99  --conj_cone_tolerance                   3.
% 2.07/0.99  --extra_neg_conj                        none
% 2.07/0.99  --large_theory_mode                     true
% 2.07/0.99  --prolific_symb_bound                   200
% 2.07/0.99  --lt_threshold                          2000
% 2.07/0.99  --clause_weak_htbl                      true
% 2.07/0.99  --gc_record_bc_elim                     false
% 2.07/0.99  
% 2.07/0.99  ------ Preprocessing Options
% 2.07/0.99  
% 2.07/0.99  --preprocessing_flag                    true
% 2.07/0.99  --time_out_prep_mult                    0.1
% 2.07/0.99  --splitting_mode                        input
% 2.07/0.99  --splitting_grd                         true
% 2.07/0.99  --splitting_cvd                         false
% 2.07/0.99  --splitting_cvd_svl                     false
% 2.07/0.99  --splitting_nvd                         32
% 2.07/0.99  --sub_typing                            true
% 2.07/0.99  --prep_gs_sim                           true
% 2.07/0.99  --prep_unflatten                        true
% 2.07/0.99  --prep_res_sim                          true
% 2.07/0.99  --prep_upred                            true
% 2.07/0.99  --prep_sem_filter                       exhaustive
% 2.07/0.99  --prep_sem_filter_out                   false
% 2.07/0.99  --pred_elim                             true
% 2.07/0.99  --res_sim_input                         true
% 2.07/0.99  --eq_ax_congr_red                       true
% 2.07/0.99  --pure_diseq_elim                       true
% 2.07/0.99  --brand_transform                       false
% 2.07/0.99  --non_eq_to_eq                          false
% 2.07/0.99  --prep_def_merge                        true
% 2.07/0.99  --prep_def_merge_prop_impl              false
% 2.07/0.99  --prep_def_merge_mbd                    true
% 2.07/0.99  --prep_def_merge_tr_red                 false
% 2.07/0.99  --prep_def_merge_tr_cl                  false
% 2.07/0.99  --smt_preprocessing                     true
% 2.07/0.99  --smt_ac_axioms                         fast
% 2.07/0.99  --preprocessed_out                      false
% 2.07/0.99  --preprocessed_stats                    false
% 2.07/0.99  
% 2.07/0.99  ------ Abstraction refinement Options
% 2.07/0.99  
% 2.07/0.99  --abstr_ref                             []
% 2.07/0.99  --abstr_ref_prep                        false
% 2.07/0.99  --abstr_ref_until_sat                   false
% 2.07/0.99  --abstr_ref_sig_restrict                funpre
% 2.07/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.07/0.99  --abstr_ref_under                       []
% 2.07/0.99  
% 2.07/0.99  ------ SAT Options
% 2.07/0.99  
% 2.07/0.99  --sat_mode                              false
% 2.07/0.99  --sat_fm_restart_options                ""
% 2.07/0.99  --sat_gr_def                            false
% 2.07/0.99  --sat_epr_types                         true
% 2.07/0.99  --sat_non_cyclic_types                  false
% 2.07/0.99  --sat_finite_models                     false
% 2.07/0.99  --sat_fm_lemmas                         false
% 2.07/0.99  --sat_fm_prep                           false
% 2.07/0.99  --sat_fm_uc_incr                        true
% 2.07/0.99  --sat_out_model                         small
% 2.07/0.99  --sat_out_clauses                       false
% 2.07/0.99  
% 2.07/0.99  ------ QBF Options
% 2.07/0.99  
% 2.07/0.99  --qbf_mode                              false
% 2.07/0.99  --qbf_elim_univ                         false
% 2.07/0.99  --qbf_dom_inst                          none
% 2.07/0.99  --qbf_dom_pre_inst                      false
% 2.07/0.99  --qbf_sk_in                             false
% 2.07/0.99  --qbf_pred_elim                         true
% 2.07/0.99  --qbf_split                             512
% 2.07/0.99  
% 2.07/0.99  ------ BMC1 Options
% 2.07/0.99  
% 2.07/0.99  --bmc1_incremental                      false
% 2.07/0.99  --bmc1_axioms                           reachable_all
% 2.07/0.99  --bmc1_min_bound                        0
% 2.07/0.99  --bmc1_max_bound                        -1
% 2.07/0.99  --bmc1_max_bound_default                -1
% 2.07/0.99  --bmc1_symbol_reachability              true
% 2.07/0.99  --bmc1_property_lemmas                  false
% 2.07/0.99  --bmc1_k_induction                      false
% 2.07/0.99  --bmc1_non_equiv_states                 false
% 2.07/0.99  --bmc1_deadlock                         false
% 2.07/0.99  --bmc1_ucm                              false
% 2.07/0.99  --bmc1_add_unsat_core                   none
% 2.07/0.99  --bmc1_unsat_core_children              false
% 2.07/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.07/0.99  --bmc1_out_stat                         full
% 2.07/0.99  --bmc1_ground_init                      false
% 2.07/0.99  --bmc1_pre_inst_next_state              false
% 2.07/0.99  --bmc1_pre_inst_state                   false
% 2.07/0.99  --bmc1_pre_inst_reach_state             false
% 2.07/0.99  --bmc1_out_unsat_core                   false
% 2.07/0.99  --bmc1_aig_witness_out                  false
% 2.07/0.99  --bmc1_verbose                          false
% 2.07/0.99  --bmc1_dump_clauses_tptp                false
% 2.07/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.07/0.99  --bmc1_dump_file                        -
% 2.07/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.07/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.07/0.99  --bmc1_ucm_extend_mode                  1
% 2.07/0.99  --bmc1_ucm_init_mode                    2
% 2.07/0.99  --bmc1_ucm_cone_mode                    none
% 2.07/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.07/0.99  --bmc1_ucm_relax_model                  4
% 2.07/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.07/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.07/0.99  --bmc1_ucm_layered_model                none
% 2.07/0.99  --bmc1_ucm_max_lemma_size               10
% 2.07/0.99  
% 2.07/0.99  ------ AIG Options
% 2.07/0.99  
% 2.07/0.99  --aig_mode                              false
% 2.07/0.99  
% 2.07/0.99  ------ Instantiation Options
% 2.07/0.99  
% 2.07/0.99  --instantiation_flag                    true
% 2.07/0.99  --inst_sos_flag                         false
% 2.07/0.99  --inst_sos_phase                        true
% 2.07/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.07/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.07/0.99  --inst_lit_sel_side                     num_symb
% 2.07/0.99  --inst_solver_per_active                1400
% 2.07/0.99  --inst_solver_calls_frac                1.
% 2.07/0.99  --inst_passive_queue_type               priority_queues
% 2.07/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.07/0.99  --inst_passive_queues_freq              [25;2]
% 2.07/0.99  --inst_dismatching                      true
% 2.07/0.99  --inst_eager_unprocessed_to_passive     true
% 2.07/0.99  --inst_prop_sim_given                   true
% 2.07/0.99  --inst_prop_sim_new                     false
% 2.07/0.99  --inst_subs_new                         false
% 2.07/0.99  --inst_eq_res_simp                      false
% 2.07/0.99  --inst_subs_given                       false
% 2.07/0.99  --inst_orphan_elimination               true
% 2.07/0.99  --inst_learning_loop_flag               true
% 2.07/0.99  --inst_learning_start                   3000
% 2.07/0.99  --inst_learning_factor                  2
% 2.07/0.99  --inst_start_prop_sim_after_learn       3
% 2.07/0.99  --inst_sel_renew                        solver
% 2.07/0.99  --inst_lit_activity_flag                true
% 2.07/0.99  --inst_restr_to_given                   false
% 2.07/0.99  --inst_activity_threshold               500
% 2.07/0.99  --inst_out_proof                        true
% 2.07/0.99  
% 2.07/0.99  ------ Resolution Options
% 2.07/0.99  
% 2.07/0.99  --resolution_flag                       true
% 2.07/0.99  --res_lit_sel                           adaptive
% 2.07/0.99  --res_lit_sel_side                      none
% 2.07/0.99  --res_ordering                          kbo
% 2.07/0.99  --res_to_prop_solver                    active
% 2.07/0.99  --res_prop_simpl_new                    false
% 2.07/0.99  --res_prop_simpl_given                  true
% 2.07/0.99  --res_passive_queue_type                priority_queues
% 2.07/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.07/0.99  --res_passive_queues_freq               [15;5]
% 2.07/0.99  --res_forward_subs                      full
% 2.07/0.99  --res_backward_subs                     full
% 2.07/0.99  --res_forward_subs_resolution           true
% 2.07/0.99  --res_backward_subs_resolution          true
% 2.07/0.99  --res_orphan_elimination                true
% 2.07/0.99  --res_time_limit                        2.
% 2.07/0.99  --res_out_proof                         true
% 2.07/0.99  
% 2.07/0.99  ------ Superposition Options
% 2.07/0.99  
% 2.07/0.99  --superposition_flag                    true
% 2.07/0.99  --sup_passive_queue_type                priority_queues
% 2.07/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.07/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.07/0.99  --demod_completeness_check              fast
% 2.07/0.99  --demod_use_ground                      true
% 2.07/0.99  --sup_to_prop_solver                    passive
% 2.07/0.99  --sup_prop_simpl_new                    true
% 2.07/0.99  --sup_prop_simpl_given                  true
% 2.07/0.99  --sup_fun_splitting                     false
% 2.07/0.99  --sup_smt_interval                      50000
% 2.07/0.99  
% 2.07/0.99  ------ Superposition Simplification Setup
% 2.07/0.99  
% 2.07/0.99  --sup_indices_passive                   []
% 2.07/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.07/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.07/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.07/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.07/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.07/0.99  --sup_full_bw                           [BwDemod]
% 2.07/0.99  --sup_immed_triv                        [TrivRules]
% 2.07/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.07/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.07/0.99  --sup_immed_bw_main                     []
% 2.07/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.07/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.07/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.07/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.07/0.99  
% 2.07/0.99  ------ Combination Options
% 2.07/0.99  
% 2.07/0.99  --comb_res_mult                         3
% 2.07/0.99  --comb_sup_mult                         2
% 2.07/0.99  --comb_inst_mult                        10
% 2.07/0.99  
% 2.07/0.99  ------ Debug Options
% 2.07/0.99  
% 2.07/0.99  --dbg_backtrace                         false
% 2.07/0.99  --dbg_dump_prop_clauses                 false
% 2.07/0.99  --dbg_dump_prop_clauses_file            -
% 2.07/0.99  --dbg_out_stat                          false
% 2.07/0.99  ------ Parsing...
% 2.07/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.07/0.99  
% 2.07/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 2.07/0.99  
% 2.07/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.07/0.99  
% 2.07/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.07/0.99  ------ Proving...
% 2.07/0.99  ------ Problem Properties 
% 2.07/0.99  
% 2.07/0.99  
% 2.07/0.99  clauses                                 28
% 2.07/0.99  conjectures                             6
% 2.07/0.99  EPR                                     3
% 2.07/0.99  Horn                                    20
% 2.07/0.99  unary                                   3
% 2.07/0.99  binary                                  5
% 2.07/0.99  lits                                    98
% 2.07/0.99  lits eq                                 62
% 2.07/0.99  fd_pure                                 0
% 2.07/0.99  fd_pseudo                               0
% 2.07/0.99  fd_cond                                 0
% 2.07/0.99  fd_pseudo_cond                          0
% 2.07/0.99  AC symbols                              0
% 2.07/0.99  
% 2.07/0.99  ------ Schedule dynamic 5 is on 
% 2.07/0.99  
% 2.07/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.07/0.99  
% 2.07/0.99  
% 2.07/0.99  ------ 
% 2.07/0.99  Current options:
% 2.07/0.99  ------ 
% 2.07/0.99  
% 2.07/0.99  ------ Input Options
% 2.07/0.99  
% 2.07/0.99  --out_options                           all
% 2.07/0.99  --tptp_safe_out                         true
% 2.07/0.99  --problem_path                          ""
% 2.07/0.99  --include_path                          ""
% 2.07/0.99  --clausifier                            res/vclausify_rel
% 2.07/0.99  --clausifier_options                    --mode clausify
% 2.07/0.99  --stdin                                 false
% 2.07/0.99  --stats_out                             all
% 2.07/0.99  
% 2.07/0.99  ------ General Options
% 2.07/0.99  
% 2.07/0.99  --fof                                   false
% 2.07/0.99  --time_out_real                         305.
% 2.07/0.99  --time_out_virtual                      -1.
% 2.07/0.99  --symbol_type_check                     false
% 2.07/0.99  --clausify_out                          false
% 2.07/0.99  --sig_cnt_out                           false
% 2.07/0.99  --trig_cnt_out                          false
% 2.07/0.99  --trig_cnt_out_tolerance                1.
% 2.07/0.99  --trig_cnt_out_sk_spl                   false
% 2.07/0.99  --abstr_cl_out                          false
% 2.07/0.99  
% 2.07/0.99  ------ Global Options
% 2.07/0.99  
% 2.07/0.99  --schedule                              default
% 2.07/0.99  --add_important_lit                     false
% 2.07/0.99  --prop_solver_per_cl                    1000
% 2.07/0.99  --min_unsat_core                        false
% 2.07/0.99  --soft_assumptions                      false
% 2.07/0.99  --soft_lemma_size                       3
% 2.07/0.99  --prop_impl_unit_size                   0
% 2.07/0.99  --prop_impl_unit                        []
% 2.07/0.99  --share_sel_clauses                     true
% 2.07/0.99  --reset_solvers                         false
% 2.07/0.99  --bc_imp_inh                            [conj_cone]
% 2.07/0.99  --conj_cone_tolerance                   3.
% 2.07/0.99  --extra_neg_conj                        none
% 2.07/0.99  --large_theory_mode                     true
% 2.07/0.99  --prolific_symb_bound                   200
% 2.07/0.99  --lt_threshold                          2000
% 2.07/0.99  --clause_weak_htbl                      true
% 2.07/0.99  --gc_record_bc_elim                     false
% 2.07/0.99  
% 2.07/0.99  ------ Preprocessing Options
% 2.07/0.99  
% 2.07/0.99  --preprocessing_flag                    true
% 2.07/0.99  --time_out_prep_mult                    0.1
% 2.07/0.99  --splitting_mode                        input
% 2.07/0.99  --splitting_grd                         true
% 2.07/0.99  --splitting_cvd                         false
% 2.07/0.99  --splitting_cvd_svl                     false
% 2.07/0.99  --splitting_nvd                         32
% 2.07/0.99  --sub_typing                            true
% 2.07/0.99  --prep_gs_sim                           true
% 2.07/0.99  --prep_unflatten                        true
% 2.07/0.99  --prep_res_sim                          true
% 2.07/0.99  --prep_upred                            true
% 2.07/0.99  --prep_sem_filter                       exhaustive
% 2.07/0.99  --prep_sem_filter_out                   false
% 2.07/0.99  --pred_elim                             true
% 2.07/0.99  --res_sim_input                         true
% 2.07/0.99  --eq_ax_congr_red                       true
% 2.07/0.99  --pure_diseq_elim                       true
% 2.07/0.99  --brand_transform                       false
% 2.07/0.99  --non_eq_to_eq                          false
% 2.07/0.99  --prep_def_merge                        true
% 2.07/0.99  --prep_def_merge_prop_impl              false
% 2.07/0.99  --prep_def_merge_mbd                    true
% 2.07/0.99  --prep_def_merge_tr_red                 false
% 2.07/0.99  --prep_def_merge_tr_cl                  false
% 2.07/0.99  --smt_preprocessing                     true
% 2.07/0.99  --smt_ac_axioms                         fast
% 2.07/0.99  --preprocessed_out                      false
% 2.07/0.99  --preprocessed_stats                    false
% 2.07/0.99  
% 2.07/0.99  ------ Abstraction refinement Options
% 2.07/0.99  
% 2.07/0.99  --abstr_ref                             []
% 2.07/0.99  --abstr_ref_prep                        false
% 2.07/0.99  --abstr_ref_until_sat                   false
% 2.07/0.99  --abstr_ref_sig_restrict                funpre
% 2.07/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.07/0.99  --abstr_ref_under                       []
% 2.07/0.99  
% 2.07/0.99  ------ SAT Options
% 2.07/0.99  
% 2.07/0.99  --sat_mode                              false
% 2.07/0.99  --sat_fm_restart_options                ""
% 2.07/0.99  --sat_gr_def                            false
% 2.07/0.99  --sat_epr_types                         true
% 2.07/0.99  --sat_non_cyclic_types                  false
% 2.07/0.99  --sat_finite_models                     false
% 2.07/0.99  --sat_fm_lemmas                         false
% 2.07/0.99  --sat_fm_prep                           false
% 2.07/0.99  --sat_fm_uc_incr                        true
% 2.07/0.99  --sat_out_model                         small
% 2.07/0.99  --sat_out_clauses                       false
% 2.07/0.99  
% 2.07/0.99  ------ QBF Options
% 2.07/0.99  
% 2.07/0.99  --qbf_mode                              false
% 2.07/0.99  --qbf_elim_univ                         false
% 2.07/0.99  --qbf_dom_inst                          none
% 2.07/0.99  --qbf_dom_pre_inst                      false
% 2.07/0.99  --qbf_sk_in                             false
% 2.07/0.99  --qbf_pred_elim                         true
% 2.07/0.99  --qbf_split                             512
% 2.07/0.99  
% 2.07/0.99  ------ BMC1 Options
% 2.07/0.99  
% 2.07/0.99  --bmc1_incremental                      false
% 2.07/0.99  --bmc1_axioms                           reachable_all
% 2.07/0.99  --bmc1_min_bound                        0
% 2.07/0.99  --bmc1_max_bound                        -1
% 2.07/0.99  --bmc1_max_bound_default                -1
% 2.07/0.99  --bmc1_symbol_reachability              true
% 2.07/0.99  --bmc1_property_lemmas                  false
% 2.07/0.99  --bmc1_k_induction                      false
% 2.07/0.99  --bmc1_non_equiv_states                 false
% 2.07/0.99  --bmc1_deadlock                         false
% 2.07/0.99  --bmc1_ucm                              false
% 2.07/0.99  --bmc1_add_unsat_core                   none
% 2.07/0.99  --bmc1_unsat_core_children              false
% 2.07/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.07/0.99  --bmc1_out_stat                         full
% 2.07/0.99  --bmc1_ground_init                      false
% 2.07/0.99  --bmc1_pre_inst_next_state              false
% 2.07/0.99  --bmc1_pre_inst_state                   false
% 2.07/0.99  --bmc1_pre_inst_reach_state             false
% 2.07/0.99  --bmc1_out_unsat_core                   false
% 2.07/0.99  --bmc1_aig_witness_out                  false
% 2.07/0.99  --bmc1_verbose                          false
% 2.07/0.99  --bmc1_dump_clauses_tptp                false
% 2.07/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.07/0.99  --bmc1_dump_file                        -
% 2.07/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.07/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.07/0.99  --bmc1_ucm_extend_mode                  1
% 2.07/0.99  --bmc1_ucm_init_mode                    2
% 2.07/0.99  --bmc1_ucm_cone_mode                    none
% 2.07/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.07/0.99  --bmc1_ucm_relax_model                  4
% 2.07/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.07/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.07/0.99  --bmc1_ucm_layered_model                none
% 2.07/0.99  --bmc1_ucm_max_lemma_size               10
% 2.07/0.99  
% 2.07/0.99  ------ AIG Options
% 2.07/0.99  
% 2.07/0.99  --aig_mode                              false
% 2.07/0.99  
% 2.07/0.99  ------ Instantiation Options
% 2.07/0.99  
% 2.07/0.99  --instantiation_flag                    true
% 2.07/0.99  --inst_sos_flag                         false
% 2.07/0.99  --inst_sos_phase                        true
% 2.07/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.07/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.07/0.99  --inst_lit_sel_side                     none
% 2.07/0.99  --inst_solver_per_active                1400
% 2.07/0.99  --inst_solver_calls_frac                1.
% 2.07/0.99  --inst_passive_queue_type               priority_queues
% 2.07/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.07/0.99  --inst_passive_queues_freq              [25;2]
% 2.07/0.99  --inst_dismatching                      true
% 2.07/0.99  --inst_eager_unprocessed_to_passive     true
% 2.07/0.99  --inst_prop_sim_given                   true
% 2.07/0.99  --inst_prop_sim_new                     false
% 2.07/0.99  --inst_subs_new                         false
% 2.07/0.99  --inst_eq_res_simp                      false
% 2.07/0.99  --inst_subs_given                       false
% 2.07/0.99  --inst_orphan_elimination               true
% 2.07/0.99  --inst_learning_loop_flag               true
% 2.07/0.99  --inst_learning_start                   3000
% 2.07/0.99  --inst_learning_factor                  2
% 2.07/0.99  --inst_start_prop_sim_after_learn       3
% 2.07/0.99  --inst_sel_renew                        solver
% 2.07/0.99  --inst_lit_activity_flag                true
% 2.07/0.99  --inst_restr_to_given                   false
% 2.07/0.99  --inst_activity_threshold               500
% 2.07/0.99  --inst_out_proof                        true
% 2.07/0.99  
% 2.07/0.99  ------ Resolution Options
% 2.07/0.99  
% 2.07/0.99  --resolution_flag                       false
% 2.07/0.99  --res_lit_sel                           adaptive
% 2.07/0.99  --res_lit_sel_side                      none
% 2.07/0.99  --res_ordering                          kbo
% 2.07/0.99  --res_to_prop_solver                    active
% 2.07/0.99  --res_prop_simpl_new                    false
% 2.07/0.99  --res_prop_simpl_given                  true
% 2.07/0.99  --res_passive_queue_type                priority_queues
% 2.07/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.07/0.99  --res_passive_queues_freq               [15;5]
% 2.07/0.99  --res_forward_subs                      full
% 2.07/0.99  --res_backward_subs                     full
% 2.07/0.99  --res_forward_subs_resolution           true
% 2.07/0.99  --res_backward_subs_resolution          true
% 2.07/0.99  --res_orphan_elimination                true
% 2.07/0.99  --res_time_limit                        2.
% 2.07/0.99  --res_out_proof                         true
% 2.07/0.99  
% 2.07/0.99  ------ Superposition Options
% 2.07/0.99  
% 2.07/0.99  --superposition_flag                    true
% 2.07/0.99  --sup_passive_queue_type                priority_queues
% 2.07/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.07/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.07/0.99  --demod_completeness_check              fast
% 2.07/0.99  --demod_use_ground                      true
% 2.07/0.99  --sup_to_prop_solver                    passive
% 2.07/0.99  --sup_prop_simpl_new                    true
% 2.07/0.99  --sup_prop_simpl_given                  true
% 2.07/0.99  --sup_fun_splitting                     false
% 2.07/0.99  --sup_smt_interval                      50000
% 2.07/0.99  
% 2.07/0.99  ------ Superposition Simplification Setup
% 2.07/0.99  
% 2.07/0.99  --sup_indices_passive                   []
% 2.07/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.07/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.07/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.07/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.07/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.07/0.99  --sup_full_bw                           [BwDemod]
% 2.07/0.99  --sup_immed_triv                        [TrivRules]
% 2.07/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.07/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.07/0.99  --sup_immed_bw_main                     []
% 2.07/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.07/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.07/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.07/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.07/0.99  
% 2.07/0.99  ------ Combination Options
% 2.07/0.99  
% 2.07/0.99  --comb_res_mult                         3
% 2.07/0.99  --comb_sup_mult                         2
% 2.07/0.99  --comb_inst_mult                        10
% 2.07/0.99  
% 2.07/0.99  ------ Debug Options
% 2.07/0.99  
% 2.07/0.99  --dbg_backtrace                         false
% 2.07/0.99  --dbg_dump_prop_clauses                 false
% 2.07/0.99  --dbg_dump_prop_clauses_file            -
% 2.07/0.99  --dbg_out_stat                          false
% 2.07/0.99  
% 2.07/0.99  
% 2.07/0.99  
% 2.07/0.99  
% 2.07/0.99  ------ Proving...
% 2.07/0.99  
% 2.07/0.99  
% 2.07/0.99  % SZS status Theorem for theBenchmark.p
% 2.07/0.99  
% 2.07/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.07/0.99  
% 2.07/0.99  fof(f9,conjecture,(
% 2.07/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (r1_partfun1(X2,X3) <=> ! [X4] : (r2_hidden(X4,k1_relset_1(X0,X1,X2)) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4))))))),
% 2.07/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.07/1.00  
% 2.07/1.00  fof(f10,negated_conjecture,(
% 2.07/1.00    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (r1_partfun1(X2,X3) <=> ! [X4] : (r2_hidden(X4,k1_relset_1(X0,X1,X2)) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4))))))),
% 2.07/1.00    inference(negated_conjecture,[],[f9])).
% 2.07/1.00  
% 2.07/1.00  fof(f22,plain,(
% 2.07/1.00    ? [X0,X1,X2] : (? [X3] : (((r1_partfun1(X2,X3) <~> ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,k1_relset_1(X0,X1,X2)))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 2.07/1.00    inference(ennf_transformation,[],[f10])).
% 2.07/1.00  
% 2.07/1.00  fof(f23,plain,(
% 2.07/1.00    ? [X0,X1,X2] : (? [X3] : ((r1_partfun1(X2,X3) <~> ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,k1_relset_1(X0,X1,X2)))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 2.07/1.00    inference(flattening,[],[f22])).
% 2.07/1.00  
% 2.07/1.00  fof(f30,plain,(
% 2.07/1.00    ? [X0,X1,X2] : (? [X3] : (((? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & r2_hidden(X4,k1_relset_1(X0,X1,X2))) | ~r1_partfun1(X2,X3)) & (! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,k1_relset_1(X0,X1,X2))) | r1_partfun1(X2,X3))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 2.07/1.00    inference(nnf_transformation,[],[f23])).
% 2.07/1.00  
% 2.07/1.00  fof(f31,plain,(
% 2.07/1.00    ? [X0,X1,X2] : (? [X3] : ((? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & r2_hidden(X4,k1_relset_1(X0,X1,X2))) | ~r1_partfun1(X2,X3)) & (! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,k1_relset_1(X0,X1,X2))) | r1_partfun1(X2,X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 2.07/1.00    inference(flattening,[],[f30])).
% 2.07/1.00  
% 2.07/1.00  fof(f32,plain,(
% 2.07/1.00    ? [X0,X1,X2] : (? [X3] : ((? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & r2_hidden(X4,k1_relset_1(X0,X1,X2))) | ~r1_partfun1(X2,X3)) & (! [X5] : (k1_funct_1(X2,X5) = k1_funct_1(X3,X5) | ~r2_hidden(X5,k1_relset_1(X0,X1,X2))) | r1_partfun1(X2,X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 2.07/1.00    inference(rectify,[],[f31])).
% 2.07/1.00  
% 2.07/1.00  fof(f35,plain,(
% 2.07/1.00    ( ! [X2,X0,X3,X1] : (? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & r2_hidden(X4,k1_relset_1(X0,X1,X2))) => (k1_funct_1(X2,sK5) != k1_funct_1(X3,sK5) & r2_hidden(sK5,k1_relset_1(X0,X1,X2)))) )),
% 2.07/1.00    introduced(choice_axiom,[])).
% 2.07/1.00  
% 2.07/1.00  fof(f34,plain,(
% 2.07/1.00    ( ! [X2,X0,X1] : (? [X3] : ((? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & r2_hidden(X4,k1_relset_1(X0,X1,X2))) | ~r1_partfun1(X2,X3)) & (! [X5] : (k1_funct_1(X2,X5) = k1_funct_1(X3,X5) | ~r2_hidden(X5,k1_relset_1(X0,X1,X2))) | r1_partfun1(X2,X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((? [X4] : (k1_funct_1(sK4,X4) != k1_funct_1(X2,X4) & r2_hidden(X4,k1_relset_1(X0,X1,X2))) | ~r1_partfun1(X2,sK4)) & (! [X5] : (k1_funct_1(sK4,X5) = k1_funct_1(X2,X5) | ~r2_hidden(X5,k1_relset_1(X0,X1,X2))) | r1_partfun1(X2,sK4)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(sK4,X0,X1) & v1_funct_1(sK4))) )),
% 2.07/1.00    introduced(choice_axiom,[])).
% 2.07/1.00  
% 2.07/1.00  fof(f33,plain,(
% 2.07/1.00    ? [X0,X1,X2] : (? [X3] : ((? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & r2_hidden(X4,k1_relset_1(X0,X1,X2))) | ~r1_partfun1(X2,X3)) & (! [X5] : (k1_funct_1(X2,X5) = k1_funct_1(X3,X5) | ~r2_hidden(X5,k1_relset_1(X0,X1,X2))) | r1_partfun1(X2,X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (? [X3] : ((? [X4] : (k1_funct_1(sK3,X4) != k1_funct_1(X3,X4) & r2_hidden(X4,k1_relset_1(sK1,sK2,sK3))) | ~r1_partfun1(sK3,X3)) & (! [X5] : (k1_funct_1(sK3,X5) = k1_funct_1(X3,X5) | ~r2_hidden(X5,k1_relset_1(sK1,sK2,sK3))) | r1_partfun1(sK3,X3)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X3,sK1,sK2) & v1_funct_1(X3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_1(sK3))),
% 2.07/1.00    introduced(choice_axiom,[])).
% 2.07/1.00  
% 2.07/1.00  fof(f36,plain,(
% 2.07/1.00    (((k1_funct_1(sK3,sK5) != k1_funct_1(sK4,sK5) & r2_hidden(sK5,k1_relset_1(sK1,sK2,sK3))) | ~r1_partfun1(sK3,sK4)) & (! [X5] : (k1_funct_1(sK3,X5) = k1_funct_1(sK4,X5) | ~r2_hidden(X5,k1_relset_1(sK1,sK2,sK3))) | r1_partfun1(sK3,sK4)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK2) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_1(sK3)),
% 2.07/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f32,f35,f34,f33])).
% 2.07/1.00  
% 2.07/1.00  fof(f56,plain,(
% 2.07/1.00    v1_funct_2(sK4,sK1,sK2)),
% 2.07/1.00    inference(cnf_transformation,[],[f36])).
% 2.07/1.00  
% 2.07/1.00  fof(f6,axiom,(
% 2.07/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.07/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.07/1.00  
% 2.07/1.00  fof(f16,plain,(
% 2.07/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.07/1.00    inference(ennf_transformation,[],[f6])).
% 2.07/1.00  
% 2.07/1.00  fof(f17,plain,(
% 2.07/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.07/1.00    inference(flattening,[],[f16])).
% 2.07/1.00  
% 2.07/1.00  fof(f25,plain,(
% 2.07/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.07/1.00    inference(nnf_transformation,[],[f17])).
% 2.07/1.00  
% 2.07/1.00  fof(f43,plain,(
% 2.07/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.07/1.00    inference(cnf_transformation,[],[f25])).
% 2.07/1.00  
% 2.07/1.00  fof(f57,plain,(
% 2.07/1.00    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 2.07/1.00    inference(cnf_transformation,[],[f36])).
% 2.07/1.00  
% 2.07/1.00  fof(f5,axiom,(
% 2.07/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.07/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.07/1.00  
% 2.07/1.00  fof(f15,plain,(
% 2.07/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.07/1.00    inference(ennf_transformation,[],[f5])).
% 2.07/1.00  
% 2.07/1.00  fof(f42,plain,(
% 2.07/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.07/1.00    inference(cnf_transformation,[],[f15])).
% 2.07/1.00  
% 2.07/1.00  fof(f7,axiom,(
% 2.07/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) => (r1_partfun1(X0,X1) <=> ! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2))))))),
% 2.07/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.07/1.00  
% 2.07/1.00  fof(f18,plain,(
% 2.07/1.00    ! [X0] : (! [X1] : (((r1_partfun1(X0,X1) <=> ! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0)))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.07/1.00    inference(ennf_transformation,[],[f7])).
% 2.07/1.00  
% 2.07/1.00  fof(f19,plain,(
% 2.07/1.00    ! [X0] : (! [X1] : ((r1_partfun1(X0,X1) <=> ! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0)))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.07/1.00    inference(flattening,[],[f18])).
% 2.07/1.00  
% 2.07/1.00  fof(f26,plain,(
% 2.07/1.00    ! [X0] : (! [X1] : (((r1_partfun1(X0,X1) | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0)))) & (! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0))) | ~r1_partfun1(X0,X1))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.07/1.00    inference(nnf_transformation,[],[f19])).
% 2.07/1.00  
% 2.07/1.00  fof(f27,plain,(
% 2.07/1.00    ! [X0] : (! [X1] : (((r1_partfun1(X0,X1) | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0)))) & (! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r1_partfun1(X0,X1))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.07/1.00    inference(rectify,[],[f26])).
% 2.07/1.00  
% 2.07/1.00  fof(f28,plain,(
% 2.07/1.00    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1)) & r2_hidden(sK0(X0,X1),k1_relat_1(X0))))),
% 2.07/1.00    introduced(choice_axiom,[])).
% 2.07/1.00  
% 2.07/1.00  fof(f29,plain,(
% 2.07/1.00    ! [X0] : (! [X1] : (((r1_partfun1(X0,X1) | (k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1)) & r2_hidden(sK0(X0,X1),k1_relat_1(X0)))) & (! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r1_partfun1(X0,X1))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.07/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).
% 2.07/1.00  
% 2.07/1.00  fof(f50,plain,(
% 2.07/1.00    ( ! [X0,X1] : (r1_partfun1(X0,X1) | r2_hidden(sK0(X0,X1),k1_relat_1(X0)) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.07/1.00    inference(cnf_transformation,[],[f29])).
% 2.07/1.00  
% 2.07/1.00  fof(f54,plain,(
% 2.07/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 2.07/1.00    inference(cnf_transformation,[],[f36])).
% 2.07/1.00  
% 2.07/1.00  fof(f59,plain,(
% 2.07/1.00    ( ! [X5] : (k1_funct_1(sK3,X5) = k1_funct_1(sK4,X5) | ~r2_hidden(X5,k1_relset_1(sK1,sK2,sK3)) | r1_partfun1(sK3,sK4)) )),
% 2.07/1.00    inference(cnf_transformation,[],[f36])).
% 2.07/1.00  
% 2.07/1.00  fof(f53,plain,(
% 2.07/1.00    v1_funct_1(sK3)),
% 2.07/1.00    inference(cnf_transformation,[],[f36])).
% 2.07/1.00  
% 2.07/1.00  fof(f1,axiom,(
% 2.07/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.07/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.07/1.00  
% 2.07/1.00  fof(f12,plain,(
% 2.07/1.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.07/1.00    inference(ennf_transformation,[],[f1])).
% 2.07/1.00  
% 2.07/1.00  fof(f37,plain,(
% 2.07/1.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.07/1.00    inference(cnf_transformation,[],[f12])).
% 2.07/1.00  
% 2.07/1.00  fof(f3,axiom,(
% 2.07/1.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.07/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.07/1.00  
% 2.07/1.00  fof(f40,plain,(
% 2.07/1.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.07/1.00    inference(cnf_transformation,[],[f3])).
% 2.07/1.00  
% 2.07/1.00  fof(f55,plain,(
% 2.07/1.00    v1_funct_1(sK4)),
% 2.07/1.00    inference(cnf_transformation,[],[f36])).
% 2.07/1.00  
% 2.07/1.00  fof(f4,axiom,(
% 2.07/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.07/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.07/1.00  
% 2.07/1.00  fof(f11,plain,(
% 2.07/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.07/1.00    inference(pure_predicate_removal,[],[f4])).
% 2.07/1.00  
% 2.07/1.00  fof(f14,plain,(
% 2.07/1.00    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.07/1.00    inference(ennf_transformation,[],[f11])).
% 2.07/1.00  
% 2.07/1.00  fof(f41,plain,(
% 2.07/1.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.07/1.00    inference(cnf_transformation,[],[f14])).
% 2.07/1.00  
% 2.07/1.00  fof(f2,axiom,(
% 2.07/1.00    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 2.07/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.07/1.00  
% 2.07/1.00  fof(f13,plain,(
% 2.07/1.00    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.07/1.00    inference(ennf_transformation,[],[f2])).
% 2.07/1.00  
% 2.07/1.00  fof(f24,plain,(
% 2.07/1.00    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.07/1.00    inference(nnf_transformation,[],[f13])).
% 2.07/1.00  
% 2.07/1.00  fof(f38,plain,(
% 2.07/1.00    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.07/1.00    inference(cnf_transformation,[],[f24])).
% 2.07/1.00  
% 2.07/1.00  fof(f60,plain,(
% 2.07/1.00    r2_hidden(sK5,k1_relset_1(sK1,sK2,sK3)) | ~r1_partfun1(sK3,sK4)),
% 2.07/1.00    inference(cnf_transformation,[],[f36])).
% 2.07/1.00  
% 2.07/1.00  fof(f49,plain,(
% 2.07/1.00    ( ! [X0,X3,X1] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r1_partfun1(X0,X1) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.07/1.00    inference(cnf_transformation,[],[f29])).
% 2.07/1.00  
% 2.07/1.00  fof(f51,plain,(
% 2.07/1.00    ( ! [X0,X1] : (r1_partfun1(X0,X1) | k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1)) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.07/1.00    inference(cnf_transformation,[],[f29])).
% 2.07/1.00  
% 2.07/1.00  fof(f61,plain,(
% 2.07/1.00    k1_funct_1(sK3,sK5) != k1_funct_1(sK4,sK5) | ~r1_partfun1(sK3,sK4)),
% 2.07/1.00    inference(cnf_transformation,[],[f36])).
% 2.07/1.00  
% 2.07/1.00  fof(f58,plain,(
% 2.07/1.00    k1_xboole_0 = sK1 | k1_xboole_0 != sK2),
% 2.07/1.00    inference(cnf_transformation,[],[f36])).
% 2.07/1.00  
% 2.07/1.00  fof(f44,plain,(
% 2.07/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.07/1.00    inference(cnf_transformation,[],[f25])).
% 2.07/1.00  
% 2.07/1.00  fof(f66,plain,(
% 2.07/1.00    ( ! [X2,X1] : (k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0 | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 2.07/1.00    inference(equality_resolution,[],[f44])).
% 2.07/1.00  
% 2.07/1.00  fof(f47,plain,(
% 2.07/1.00    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.07/1.00    inference(cnf_transformation,[],[f25])).
% 2.07/1.00  
% 2.07/1.00  fof(f64,plain,(
% 2.07/1.00    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 2.07/1.00    inference(equality_resolution,[],[f47])).
% 2.07/1.00  
% 2.07/1.00  cnf(c_21,negated_conjecture,
% 2.07/1.00      ( v1_funct_2(sK4,sK1,sK2) ),
% 2.07/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_11,plain,
% 2.07/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.07/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.07/1.00      | k1_relset_1(X1,X2,X0) = X1
% 2.07/1.00      | k1_xboole_0 = X2 ),
% 2.07/1.00      inference(cnf_transformation,[],[f43]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_20,negated_conjecture,
% 2.07/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 2.07/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_593,plain,
% 2.07/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.07/1.00      | k1_relset_1(X1,X2,X0) = X1
% 2.07/1.00      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.07/1.00      | sK4 != X0
% 2.07/1.00      | k1_xboole_0 = X2 ),
% 2.07/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_20]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_594,plain,
% 2.07/1.00      ( ~ v1_funct_2(sK4,X0,X1)
% 2.07/1.00      | k1_relset_1(X0,X1,sK4) = X0
% 2.07/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.07/1.00      | k1_xboole_0 = X1 ),
% 2.07/1.00      inference(unflattening,[status(thm)],[c_593]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_1504,plain,
% 2.07/1.00      ( k1_relset_1(X0,X1,sK4) = X0
% 2.07/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.07/1.00      | sK2 != X1
% 2.07/1.00      | sK1 != X0
% 2.07/1.00      | sK4 != sK4
% 2.07/1.00      | k1_xboole_0 = X1 ),
% 2.07/1.00      inference(resolution_lifted,[status(thm)],[c_21,c_594]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_1505,plain,
% 2.07/1.00      ( k1_relset_1(sK1,sK2,sK4) = sK1
% 2.07/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.07/1.00      | k1_xboole_0 = sK2 ),
% 2.07/1.00      inference(unflattening,[status(thm)],[c_1504]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_2101,plain,
% 2.07/1.00      ( k1_relset_1(sK1,sK2,sK4) = sK1 | k1_xboole_0 = sK2 ),
% 2.07/1.00      inference(equality_resolution_simp,[status(thm)],[c_1505]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_5,plain,
% 2.07/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.07/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.07/1.00      inference(cnf_transformation,[],[f42]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_629,plain,
% 2.07/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.07/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.07/1.00      | sK4 != X2 ),
% 2.07/1.00      inference(resolution_lifted,[status(thm)],[c_5,c_20]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_630,plain,
% 2.07/1.00      ( k1_relset_1(X0,X1,sK4) = k1_relat_1(sK4)
% 2.07/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 2.07/1.00      inference(unflattening,[status(thm)],[c_629]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_2336,plain,
% 2.07/1.00      ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
% 2.07/1.00      inference(equality_resolution,[status(thm)],[c_630]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_2938,plain,
% 2.07/1.00      ( k1_relat_1(sK4) = sK1 | sK2 = k1_xboole_0 ),
% 2.07/1.00      inference(demodulation,[status(thm)],[c_2101,c_2336]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_13,plain,
% 2.07/1.00      ( r2_hidden(sK0(X0,X1),k1_relat_1(X0))
% 2.07/1.00      | r1_partfun1(X0,X1)
% 2.07/1.00      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 2.07/1.00      | ~ v1_funct_1(X1)
% 2.07/1.00      | ~ v1_funct_1(X0)
% 2.07/1.00      | ~ v1_relat_1(X0)
% 2.07/1.00      | ~ v1_relat_1(X1) ),
% 2.07/1.00      inference(cnf_transformation,[],[f50]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_2060,plain,
% 2.07/1.00      ( r2_hidden(sK0(X0,X1),k1_relat_1(X0)) = iProver_top
% 2.07/1.00      | r1_partfun1(X0,X1) = iProver_top
% 2.07/1.00      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) != iProver_top
% 2.07/1.00      | v1_funct_1(X0) != iProver_top
% 2.07/1.00      | v1_funct_1(X1) != iProver_top
% 2.07/1.00      | v1_relat_1(X1) != iProver_top
% 2.07/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.07/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_23,negated_conjecture,
% 2.07/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 2.07/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_689,plain,
% 2.07/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.07/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.07/1.00      | sK3 != X2 ),
% 2.07/1.00      inference(resolution_lifted,[status(thm)],[c_5,c_23]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_690,plain,
% 2.07/1.00      ( k1_relset_1(X0,X1,sK3) = k1_relat_1(sK3)
% 2.07/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 2.07/1.00      inference(unflattening,[status(thm)],[c_689]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_2369,plain,
% 2.07/1.00      ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
% 2.07/1.00      inference(equality_resolution,[status(thm)],[c_690]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_18,negated_conjecture,
% 2.07/1.00      ( ~ r2_hidden(X0,k1_relset_1(sK1,sK2,sK3))
% 2.07/1.00      | r1_partfun1(sK3,sK4)
% 2.07/1.00      | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0) ),
% 2.07/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_2056,plain,
% 2.07/1.00      ( k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0)
% 2.07/1.00      | r2_hidden(X0,k1_relset_1(sK1,sK2,sK3)) != iProver_top
% 2.07/1.00      | r1_partfun1(sK3,sK4) = iProver_top ),
% 2.07/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_2569,plain,
% 2.07/1.00      ( k1_funct_1(sK4,X0) = k1_funct_1(sK3,X0)
% 2.07/1.00      | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 2.07/1.00      | r1_partfun1(sK3,sK4) = iProver_top ),
% 2.07/1.00      inference(demodulation,[status(thm)],[c_2369,c_2056]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_2746,plain,
% 2.07/1.00      ( k1_funct_1(sK3,sK0(sK3,X0)) = k1_funct_1(sK4,sK0(sK3,X0))
% 2.07/1.00      | r1_partfun1(sK3,X0) = iProver_top
% 2.07/1.00      | r1_partfun1(sK3,sK4) = iProver_top
% 2.07/1.00      | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) != iProver_top
% 2.07/1.00      | v1_funct_1(X0) != iProver_top
% 2.07/1.00      | v1_funct_1(sK3) != iProver_top
% 2.07/1.00      | v1_relat_1(X0) != iProver_top
% 2.07/1.00      | v1_relat_1(sK3) != iProver_top ),
% 2.07/1.00      inference(superposition,[status(thm)],[c_2060,c_2569]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_24,negated_conjecture,
% 2.07/1.00      ( v1_funct_1(sK3) ),
% 2.07/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_25,plain,
% 2.07/1.00      ( v1_funct_1(sK3) = iProver_top ),
% 2.07/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_1773,plain,( X0 = X0 ),theory(equality) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_2311,plain,
% 2.07/1.00      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 2.07/1.00      inference(instantiation,[status(thm)],[c_1773]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_0,plain,
% 2.07/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.07/1.00      | ~ v1_relat_1(X1)
% 2.07/1.00      | v1_relat_1(X0) ),
% 2.07/1.00      inference(cnf_transformation,[],[f37]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_563,plain,
% 2.07/1.00      ( ~ v1_relat_1(X0)
% 2.07/1.00      | v1_relat_1(X1)
% 2.07/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(X0)
% 2.07/1.00      | sK3 != X1 ),
% 2.07/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_23]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_564,plain,
% 2.07/1.00      ( ~ v1_relat_1(X0)
% 2.07/1.00      | v1_relat_1(sK3)
% 2.07/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(X0) ),
% 2.07/1.00      inference(unflattening,[status(thm)],[c_563]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_2301,plain,
% 2.07/1.00      ( ~ v1_relat_1(k2_zfmisc_1(X0,X1))
% 2.07/1.00      | v1_relat_1(sK3)
% 2.07/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.07/1.00      inference(instantiation,[status(thm)],[c_564]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_2478,plain,
% 2.07/1.00      ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK2))
% 2.07/1.00      | v1_relat_1(sK3)
% 2.07/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 2.07/1.00      inference(instantiation,[status(thm)],[c_2301]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_2479,plain,
% 2.07/1.00      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.07/1.00      | v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
% 2.07/1.00      | v1_relat_1(sK3) = iProver_top ),
% 2.07/1.00      inference(predicate_to_equality,[status(thm)],[c_2478]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_3,plain,
% 2.07/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.07/1.00      inference(cnf_transformation,[],[f40]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_2585,plain,
% 2.07/1.00      ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) ),
% 2.07/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_2586,plain,
% 2.07/1.00      ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) = iProver_top ),
% 2.07/1.00      inference(predicate_to_equality,[status(thm)],[c_2585]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_3173,plain,
% 2.07/1.00      ( v1_relat_1(X0) != iProver_top
% 2.07/1.00      | k1_funct_1(sK3,sK0(sK3,X0)) = k1_funct_1(sK4,sK0(sK3,X0))
% 2.07/1.00      | r1_partfun1(sK3,X0) = iProver_top
% 2.07/1.00      | r1_partfun1(sK3,sK4) = iProver_top
% 2.07/1.00      | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) != iProver_top
% 2.07/1.00      | v1_funct_1(X0) != iProver_top ),
% 2.07/1.00      inference(global_propositional_subsumption,
% 2.07/1.00                [status(thm)],
% 2.07/1.00                [c_2746,c_25,c_2311,c_2479,c_2586]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_3174,plain,
% 2.07/1.00      ( k1_funct_1(sK3,sK0(sK3,X0)) = k1_funct_1(sK4,sK0(sK3,X0))
% 2.07/1.00      | r1_partfun1(sK3,X0) = iProver_top
% 2.07/1.00      | r1_partfun1(sK3,sK4) = iProver_top
% 2.07/1.00      | r1_tarski(k1_relat_1(sK3),k1_relat_1(X0)) != iProver_top
% 2.07/1.00      | v1_funct_1(X0) != iProver_top
% 2.07/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.07/1.00      inference(renaming,[status(thm)],[c_3173]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_3185,plain,
% 2.07/1.00      ( k1_funct_1(sK4,sK0(sK3,sK4)) = k1_funct_1(sK3,sK0(sK3,sK4))
% 2.07/1.00      | sK2 = k1_xboole_0
% 2.07/1.00      | r1_partfun1(sK3,sK4) = iProver_top
% 2.07/1.00      | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top
% 2.07/1.00      | v1_funct_1(sK4) != iProver_top
% 2.07/1.00      | v1_relat_1(sK4) != iProver_top ),
% 2.07/1.00      inference(superposition,[status(thm)],[c_2938,c_3174]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_22,negated_conjecture,
% 2.07/1.00      ( v1_funct_1(sK4) ),
% 2.07/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_27,plain,
% 2.07/1.00      ( v1_funct_1(sK4) = iProver_top ),
% 2.07/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_548,plain,
% 2.07/1.00      ( ~ v1_relat_1(X0)
% 2.07/1.00      | v1_relat_1(X1)
% 2.07/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(X0)
% 2.07/1.00      | sK4 != X1 ),
% 2.07/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_20]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_549,plain,
% 2.07/1.00      ( ~ v1_relat_1(X0)
% 2.07/1.00      | v1_relat_1(sK4)
% 2.07/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(X0) ),
% 2.07/1.00      inference(unflattening,[status(thm)],[c_548]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_2302,plain,
% 2.07/1.00      ( ~ v1_relat_1(k2_zfmisc_1(X0,X1))
% 2.07/1.00      | v1_relat_1(sK4)
% 2.07/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.07/1.00      inference(instantiation,[status(thm)],[c_549]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_2485,plain,
% 2.07/1.00      ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK2))
% 2.07/1.00      | v1_relat_1(sK4)
% 2.07/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 2.07/1.00      inference(instantiation,[status(thm)],[c_2302]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_2486,plain,
% 2.07/1.00      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.07/1.00      | v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
% 2.07/1.00      | v1_relat_1(sK4) = iProver_top ),
% 2.07/1.00      inference(predicate_to_equality,[status(thm)],[c_2485]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_4,plain,
% 2.07/1.00      ( v4_relat_1(X0,X1)
% 2.07/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.07/1.00      inference(cnf_transformation,[],[f41]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_2,plain,
% 2.07/1.00      ( r1_tarski(k1_relat_1(X0),X1)
% 2.07/1.00      | ~ v4_relat_1(X0,X1)
% 2.07/1.00      | ~ v1_relat_1(X0) ),
% 2.07/1.00      inference(cnf_transformation,[],[f38]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_267,plain,
% 2.07/1.00      ( r1_tarski(k1_relat_1(X0),X1)
% 2.07/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.07/1.00      | ~ v1_relat_1(X0) ),
% 2.07/1.00      inference(resolution,[status(thm)],[c_4,c_2]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_638,plain,
% 2.07/1.00      ( r1_tarski(k1_relat_1(X0),X1)
% 2.07/1.00      | ~ v1_relat_1(X0)
% 2.07/1.00      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.07/1.00      | sK3 != X0 ),
% 2.07/1.00      inference(resolution_lifted,[status(thm)],[c_267,c_23]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_639,plain,
% 2.07/1.00      ( r1_tarski(k1_relat_1(sK3),X0)
% 2.07/1.00      | ~ v1_relat_1(sK3)
% 2.07/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 2.07/1.00      inference(unflattening,[status(thm)],[c_638]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_2050,plain,
% 2.07/1.00      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.07/1.00      | r1_tarski(k1_relat_1(sK3),X0) = iProver_top
% 2.07/1.00      | v1_relat_1(sK3) != iProver_top ),
% 2.07/1.00      inference(predicate_to_equality,[status(thm)],[c_639]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_640,plain,
% 2.07/1.00      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.07/1.00      | r1_tarski(k1_relat_1(sK3),X0) = iProver_top
% 2.07/1.00      | v1_relat_1(sK3) != iProver_top ),
% 2.07/1.00      inference(predicate_to_equality,[status(thm)],[c_639]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_2822,plain,
% 2.07/1.00      ( r1_tarski(k1_relat_1(sK3),X0) = iProver_top
% 2.07/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 2.07/1.00      inference(global_propositional_subsumption,
% 2.07/1.00                [status(thm)],
% 2.07/1.00                [c_2050,c_640,c_2311,c_2479,c_2586]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_2823,plain,
% 2.07/1.00      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.07/1.00      | r1_tarski(k1_relat_1(sK3),X0) = iProver_top ),
% 2.07/1.00      inference(renaming,[status(thm)],[c_2822]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_2830,plain,
% 2.07/1.00      ( r1_tarski(k1_relat_1(sK3),sK1) = iProver_top ),
% 2.07/1.00      inference(equality_resolution,[status(thm)],[c_2823]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_3748,plain,
% 2.07/1.00      ( r1_partfun1(sK3,sK4) = iProver_top
% 2.07/1.00      | sK2 = k1_xboole_0
% 2.07/1.00      | k1_funct_1(sK4,sK0(sK3,sK4)) = k1_funct_1(sK3,sK0(sK3,sK4)) ),
% 2.07/1.00      inference(global_propositional_subsumption,
% 2.07/1.00                [status(thm)],
% 2.07/1.00                [c_3185,c_27,c_2311,c_2486,c_2586,c_2830]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_3749,plain,
% 2.07/1.00      ( k1_funct_1(sK4,sK0(sK3,sK4)) = k1_funct_1(sK3,sK0(sK3,sK4))
% 2.07/1.00      | sK2 = k1_xboole_0
% 2.07/1.00      | r1_partfun1(sK3,sK4) = iProver_top ),
% 2.07/1.00      inference(renaming,[status(thm)],[c_3748]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_17,negated_conjecture,
% 2.07/1.00      ( r2_hidden(sK5,k1_relset_1(sK1,sK2,sK3))
% 2.07/1.00      | ~ r1_partfun1(sK3,sK4) ),
% 2.07/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_2057,plain,
% 2.07/1.00      ( r2_hidden(sK5,k1_relset_1(sK1,sK2,sK3)) = iProver_top
% 2.07/1.00      | r1_partfun1(sK3,sK4) != iProver_top ),
% 2.07/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_2570,plain,
% 2.07/1.00      ( r2_hidden(sK5,k1_relat_1(sK3)) = iProver_top
% 2.07/1.00      | r1_partfun1(sK3,sK4) != iProver_top ),
% 2.07/1.00      inference(demodulation,[status(thm)],[c_2369,c_2057]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_14,plain,
% 2.07/1.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.07/1.00      | ~ r1_partfun1(X1,X2)
% 2.07/1.00      | ~ r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
% 2.07/1.00      | ~ v1_funct_1(X2)
% 2.07/1.00      | ~ v1_funct_1(X1)
% 2.07/1.00      | ~ v1_relat_1(X1)
% 2.07/1.00      | ~ v1_relat_1(X2)
% 2.07/1.00      | k1_funct_1(X2,X0) = k1_funct_1(X1,X0) ),
% 2.07/1.00      inference(cnf_transformation,[],[f49]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_2059,plain,
% 2.07/1.00      ( k1_funct_1(X0,X1) = k1_funct_1(X2,X1)
% 2.07/1.00      | r2_hidden(X1,k1_relat_1(X2)) != iProver_top
% 2.07/1.00      | r1_partfun1(X2,X0) != iProver_top
% 2.07/1.00      | r1_tarski(k1_relat_1(X2),k1_relat_1(X0)) != iProver_top
% 2.07/1.00      | v1_funct_1(X2) != iProver_top
% 2.07/1.00      | v1_funct_1(X0) != iProver_top
% 2.07/1.00      | v1_relat_1(X2) != iProver_top
% 2.07/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.07/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_2943,plain,
% 2.07/1.00      ( k1_funct_1(X0,X1) = k1_funct_1(sK4,X1)
% 2.07/1.00      | sK2 = k1_xboole_0
% 2.07/1.00      | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
% 2.07/1.00      | r1_partfun1(X0,sK4) != iProver_top
% 2.07/1.00      | r1_tarski(k1_relat_1(X0),sK1) != iProver_top
% 2.07/1.00      | v1_funct_1(X0) != iProver_top
% 2.07/1.00      | v1_funct_1(sK4) != iProver_top
% 2.07/1.00      | v1_relat_1(X0) != iProver_top
% 2.07/1.00      | v1_relat_1(sK4) != iProver_top ),
% 2.07/1.00      inference(superposition,[status(thm)],[c_2938,c_2059]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_3309,plain,
% 2.07/1.00      ( v1_relat_1(X0) != iProver_top
% 2.07/1.00      | k1_funct_1(X0,X1) = k1_funct_1(sK4,X1)
% 2.07/1.00      | sK2 = k1_xboole_0
% 2.07/1.00      | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
% 2.07/1.00      | r1_partfun1(X0,sK4) != iProver_top
% 2.07/1.00      | r1_tarski(k1_relat_1(X0),sK1) != iProver_top
% 2.07/1.00      | v1_funct_1(X0) != iProver_top ),
% 2.07/1.00      inference(global_propositional_subsumption,
% 2.07/1.00                [status(thm)],
% 2.07/1.00                [c_2943,c_27,c_2311,c_2486,c_2586]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_3310,plain,
% 2.07/1.00      ( k1_funct_1(X0,X1) = k1_funct_1(sK4,X1)
% 2.07/1.00      | sK2 = k1_xboole_0
% 2.07/1.00      | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
% 2.07/1.00      | r1_partfun1(X0,sK4) != iProver_top
% 2.07/1.00      | r1_tarski(k1_relat_1(X0),sK1) != iProver_top
% 2.07/1.00      | v1_funct_1(X0) != iProver_top
% 2.07/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.07/1.00      inference(renaming,[status(thm)],[c_3309]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_3323,plain,
% 2.07/1.00      ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
% 2.07/1.00      | sK2 = k1_xboole_0
% 2.07/1.00      | r1_partfun1(sK3,sK4) != iProver_top
% 2.07/1.00      | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top
% 2.07/1.00      | v1_funct_1(sK3) != iProver_top
% 2.07/1.00      | v1_relat_1(sK3) != iProver_top ),
% 2.07/1.00      inference(superposition,[status(thm)],[c_2570,c_3310]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_3493,plain,
% 2.07/1.00      ( r1_partfun1(sK3,sK4) != iProver_top
% 2.07/1.00      | sK2 = k1_xboole_0
% 2.07/1.00      | k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5) ),
% 2.07/1.00      inference(global_propositional_subsumption,
% 2.07/1.00                [status(thm)],
% 2.07/1.00                [c_3323,c_25,c_2311,c_2479,c_2586,c_2830]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_3494,plain,
% 2.07/1.00      ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
% 2.07/1.00      | sK2 = k1_xboole_0
% 2.07/1.00      | r1_partfun1(sK3,sK4) != iProver_top ),
% 2.07/1.00      inference(renaming,[status(thm)],[c_3493]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_3755,plain,
% 2.07/1.00      ( k1_funct_1(sK4,sK0(sK3,sK4)) = k1_funct_1(sK3,sK0(sK3,sK4))
% 2.07/1.00      | k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
% 2.07/1.00      | sK2 = k1_xboole_0 ),
% 2.07/1.00      inference(superposition,[status(thm)],[c_3749,c_3494]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_12,plain,
% 2.07/1.00      ( r1_partfun1(X0,X1)
% 2.07/1.00      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 2.07/1.00      | ~ v1_funct_1(X1)
% 2.07/1.00      | ~ v1_funct_1(X0)
% 2.07/1.00      | ~ v1_relat_1(X0)
% 2.07/1.00      | ~ v1_relat_1(X1)
% 2.07/1.00      | k1_funct_1(X1,sK0(X0,X1)) != k1_funct_1(X0,sK0(X0,X1)) ),
% 2.07/1.00      inference(cnf_transformation,[],[f51]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_2061,plain,
% 2.07/1.00      ( k1_funct_1(X0,sK0(X1,X0)) != k1_funct_1(X1,sK0(X1,X0))
% 2.07/1.00      | r1_partfun1(X1,X0) = iProver_top
% 2.07/1.00      | r1_tarski(k1_relat_1(X1),k1_relat_1(X0)) != iProver_top
% 2.07/1.00      | v1_funct_1(X1) != iProver_top
% 2.07/1.00      | v1_funct_1(X0) != iProver_top
% 2.07/1.00      | v1_relat_1(X0) != iProver_top
% 2.07/1.00      | v1_relat_1(X1) != iProver_top ),
% 2.07/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_3798,plain,
% 2.07/1.00      ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
% 2.07/1.00      | sK2 = k1_xboole_0
% 2.07/1.00      | r1_partfun1(sK3,sK4) = iProver_top
% 2.07/1.00      | r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4)) != iProver_top
% 2.07/1.00      | v1_funct_1(sK4) != iProver_top
% 2.07/1.00      | v1_funct_1(sK3) != iProver_top
% 2.07/1.00      | v1_relat_1(sK4) != iProver_top
% 2.07/1.00      | v1_relat_1(sK3) != iProver_top ),
% 2.07/1.00      inference(superposition,[status(thm)],[c_3755,c_2061]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_2357,plain,
% 2.07/1.00      ( r1_partfun1(X0,sK4)
% 2.07/1.00      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(sK4))
% 2.07/1.00      | ~ v1_funct_1(X0)
% 2.07/1.00      | ~ v1_funct_1(sK4)
% 2.07/1.00      | ~ v1_relat_1(X0)
% 2.07/1.00      | ~ v1_relat_1(sK4)
% 2.07/1.00      | k1_funct_1(sK4,sK0(X0,sK4)) != k1_funct_1(X0,sK0(X0,sK4)) ),
% 2.07/1.00      inference(instantiation,[status(thm)],[c_12]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_2410,plain,
% 2.07/1.00      ( r1_partfun1(sK3,sK4)
% 2.07/1.00      | ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4))
% 2.07/1.00      | ~ v1_funct_1(sK4)
% 2.07/1.00      | ~ v1_funct_1(sK3)
% 2.07/1.00      | ~ v1_relat_1(sK4)
% 2.07/1.00      | ~ v1_relat_1(sK3)
% 2.07/1.00      | k1_funct_1(sK4,sK0(sK3,sK4)) != k1_funct_1(sK3,sK0(sK3,sK4)) ),
% 2.07/1.00      inference(instantiation,[status(thm)],[c_2357]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_2411,plain,
% 2.07/1.00      ( k1_funct_1(sK4,sK0(sK3,sK4)) != k1_funct_1(sK3,sK0(sK3,sK4))
% 2.07/1.00      | r1_partfun1(sK3,sK4) = iProver_top
% 2.07/1.00      | r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4)) != iProver_top
% 2.07/1.00      | v1_funct_1(sK4) != iProver_top
% 2.07/1.00      | v1_funct_1(sK3) != iProver_top
% 2.07/1.00      | v1_relat_1(sK4) != iProver_top
% 2.07/1.00      | v1_relat_1(sK3) != iProver_top ),
% 2.07/1.00      inference(predicate_to_equality,[status(thm)],[c_2410]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_3801,plain,
% 2.07/1.00      ( sK2 = k1_xboole_0
% 2.07/1.00      | r1_partfun1(sK3,sK4) = iProver_top
% 2.07/1.00      | r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4)) != iProver_top ),
% 2.07/1.00      inference(global_propositional_subsumption,
% 2.07/1.00                [status(thm)],
% 2.07/1.00                [c_3798,c_25,c_27,c_2311,c_2411,c_2479,c_2486,c_2586,
% 2.07/1.00                 c_2830,c_3185]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_3808,plain,
% 2.07/1.00      ( sK2 = k1_xboole_0
% 2.07/1.00      | r1_partfun1(sK3,sK4) = iProver_top
% 2.07/1.00      | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top ),
% 2.07/1.00      inference(superposition,[status(thm)],[c_2938,c_3801]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_3851,plain,
% 2.07/1.00      ( r1_partfun1(sK3,sK4) = iProver_top | sK2 = k1_xboole_0 ),
% 2.07/1.00      inference(global_propositional_subsumption,
% 2.07/1.00                [status(thm)],
% 2.07/1.00                [c_3808,c_2830]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_3852,plain,
% 2.07/1.00      ( sK2 = k1_xboole_0 | r1_partfun1(sK3,sK4) = iProver_top ),
% 2.07/1.00      inference(renaming,[status(thm)],[c_3851]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_3857,plain,
% 2.07/1.00      ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5) | sK2 = k1_xboole_0 ),
% 2.07/1.00      inference(superposition,[status(thm)],[c_3852,c_3494]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_16,negated_conjecture,
% 2.07/1.00      ( ~ r1_partfun1(sK3,sK4)
% 2.07/1.00      | k1_funct_1(sK3,sK5) != k1_funct_1(sK4,sK5) ),
% 2.07/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_2058,plain,
% 2.07/1.00      ( k1_funct_1(sK3,sK5) != k1_funct_1(sK4,sK5)
% 2.07/1.00      | r1_partfun1(sK3,sK4) != iProver_top ),
% 2.07/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_3860,plain,
% 2.07/1.00      ( sK2 = k1_xboole_0 | r1_partfun1(sK3,sK4) != iProver_top ),
% 2.07/1.00      inference(superposition,[status(thm)],[c_3857,c_2058]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_3896,plain,
% 2.07/1.00      ( sK2 = k1_xboole_0 ),
% 2.07/1.00      inference(global_propositional_subsumption,
% 2.07/1.00                [status(thm)],
% 2.07/1.00                [c_3860,c_2830,c_3808]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_3911,plain,
% 2.07/1.00      ( k1_relset_1(sK1,k1_xboole_0,sK4) = k1_relat_1(sK4) ),
% 2.07/1.00      inference(demodulation,[status(thm)],[c_3896,c_2336]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_19,negated_conjecture,
% 2.07/1.00      ( k1_xboole_0 != sK2 | k1_xboole_0 = sK1 ),
% 2.07/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_3919,plain,
% 2.07/1.00      ( sK1 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 2.07/1.00      inference(demodulation,[status(thm)],[c_3896,c_19]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_3920,plain,
% 2.07/1.00      ( sK1 = k1_xboole_0 ),
% 2.07/1.00      inference(equality_resolution_simp,[status(thm)],[c_3919]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_10,plain,
% 2.07/1.00      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 2.07/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.07/1.00      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 2.07/1.00      inference(cnf_transformation,[],[f66]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_768,plain,
% 2.07/1.00      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 2.07/1.00      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 2.07/1.00      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.07/1.00      | sK4 != X0 ),
% 2.07/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_20]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_769,plain,
% 2.07/1.00      ( ~ v1_funct_2(sK4,k1_xboole_0,X0)
% 2.07/1.00      | k1_relset_1(k1_xboole_0,X0,sK4) = k1_xboole_0
% 2.07/1.00      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 2.07/1.00      inference(unflattening,[status(thm)],[c_768]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_1560,plain,
% 2.07/1.00      ( k1_relset_1(k1_xboole_0,X0,sK4) = k1_xboole_0
% 2.07/1.00      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.07/1.00      | sK2 != X0
% 2.07/1.00      | sK1 != k1_xboole_0
% 2.07/1.00      | sK4 != sK4 ),
% 2.07/1.00      inference(resolution_lifted,[status(thm)],[c_21,c_769]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_1561,plain,
% 2.07/1.00      ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
% 2.07/1.00      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.07/1.00      | sK1 != k1_xboole_0 ),
% 2.07/1.00      inference(unflattening,[status(thm)],[c_1560]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_3916,plain,
% 2.07/1.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
% 2.07/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
% 2.07/1.00      | sK1 != k1_xboole_0 ),
% 2.07/1.00      inference(demodulation,[status(thm)],[c_3896,c_1561]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_3933,plain,
% 2.07/1.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
% 2.07/1.00      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
% 2.07/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 2.07/1.00      inference(light_normalisation,[status(thm)],[c_3916,c_3920]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_3934,plain,
% 2.07/1.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0 ),
% 2.07/1.00      inference(equality_resolution_simp,[status(thm)],[c_3933]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_3944,plain,
% 2.07/1.00      ( k1_relat_1(sK4) = k1_xboole_0 ),
% 2.07/1.00      inference(light_normalisation,[status(thm)],[c_3911,c_3920,c_3934]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_4076,plain,
% 2.07/1.00      ( k1_funct_1(sK4,sK0(sK3,sK4)) = k1_funct_1(sK3,sK0(sK3,sK4))
% 2.07/1.00      | r1_partfun1(sK3,sK4) = iProver_top
% 2.07/1.00      | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top
% 2.07/1.00      | v1_funct_1(sK4) != iProver_top
% 2.07/1.00      | v1_relat_1(sK4) != iProver_top ),
% 2.07/1.00      inference(superposition,[status(thm)],[c_3944,c_3174]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_1796,plain,
% 2.07/1.00      ( k1_xboole_0 = k1_xboole_0 ),
% 2.07/1.00      inference(instantiation,[status(thm)],[c_1773]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_1774,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_2337,plain,
% 2.07/1.00      ( sK2 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK2 ),
% 2.07/1.00      inference(instantiation,[status(thm)],[c_1774]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_2338,plain,
% 2.07/1.00      ( sK2 != k1_xboole_0
% 2.07/1.00      | k1_xboole_0 = sK2
% 2.07/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 2.07/1.00      inference(instantiation,[status(thm)],[c_2337]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_7,plain,
% 2.07/1.00      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 2.07/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 2.07/1.00      | k1_xboole_0 = X1
% 2.07/1.00      | k1_xboole_0 = X0 ),
% 2.07/1.00      inference(cnf_transformation,[],[f64]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_732,plain,
% 2.07/1.00      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 2.07/1.00      | k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.07/1.00      | sK4 != X0
% 2.07/1.00      | k1_xboole_0 = X1
% 2.07/1.00      | k1_xboole_0 = X0 ),
% 2.07/1.00      inference(resolution_lifted,[status(thm)],[c_7,c_20]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_733,plain,
% 2.07/1.00      ( ~ v1_funct_2(sK4,X0,k1_xboole_0)
% 2.07/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.07/1.00      | k1_xboole_0 = X0
% 2.07/1.00      | k1_xboole_0 = sK4 ),
% 2.07/1.00      inference(unflattening,[status(thm)],[c_732]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_1529,plain,
% 2.07/1.00      ( k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.07/1.00      | sK2 != k1_xboole_0
% 2.07/1.00      | sK1 != X0
% 2.07/1.00      | sK4 != sK4
% 2.07/1.00      | sK4 = k1_xboole_0
% 2.07/1.00      | k1_xboole_0 = X0 ),
% 2.07/1.00      inference(resolution_lifted,[status(thm)],[c_21,c_733]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_1530,plain,
% 2.07/1.00      ( k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.07/1.00      | sK2 != k1_xboole_0
% 2.07/1.00      | sK4 = k1_xboole_0
% 2.07/1.00      | k1_xboole_0 = sK1 ),
% 2.07/1.00      inference(unflattening,[status(thm)],[c_1529]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_2415,plain,
% 2.07/1.00      ( sK2 != k1_xboole_0 | k1_xboole_0 = sK1 ),
% 2.07/1.00      inference(global_propositional_subsumption,
% 2.07/1.00                [status(thm)],
% 2.07/1.00                [c_1530,c_19,c_1796,c_2338]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_2437,plain,
% 2.07/1.00      ( sK2 = sK2 ),
% 2.07/1.00      inference(instantiation,[status(thm)],[c_1773]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_2344,plain,
% 2.07/1.00      ( sK1 != X0 | sK1 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 2.07/1.00      inference(instantiation,[status(thm)],[c_1774]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_2439,plain,
% 2.07/1.00      ( sK1 != sK1 | sK1 = k1_xboole_0 | k1_xboole_0 != sK1 ),
% 2.07/1.00      inference(instantiation,[status(thm)],[c_2344]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_2440,plain,
% 2.07/1.00      ( sK1 = sK1 ),
% 2.07/1.00      inference(instantiation,[status(thm)],[c_1773]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_1779,plain,
% 2.07/1.00      ( X0 != X1 | X2 != X3 | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
% 2.07/1.00      theory(equality) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_2490,plain,
% 2.07/1.00      ( X0 != sK2
% 2.07/1.00      | X1 != sK1
% 2.07/1.00      | k2_zfmisc_1(X1,X0) = k2_zfmisc_1(sK1,sK2) ),
% 2.07/1.00      inference(instantiation,[status(thm)],[c_1779]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_2608,plain,
% 2.07/1.00      ( X0 != sK1
% 2.07/1.00      | k2_zfmisc_1(X0,sK2) = k2_zfmisc_1(sK1,sK2)
% 2.07/1.00      | sK2 != sK2 ),
% 2.07/1.00      inference(instantiation,[status(thm)],[c_2490]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_2609,plain,
% 2.07/1.00      ( k2_zfmisc_1(k1_xboole_0,sK2) = k2_zfmisc_1(sK1,sK2)
% 2.07/1.00      | sK2 != sK2
% 2.07/1.00      | k1_xboole_0 != sK1 ),
% 2.07/1.00      inference(instantiation,[status(thm)],[c_2608]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_2781,plain,
% 2.07/1.00      ( r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4))
% 2.07/1.00      | ~ v1_relat_1(sK3)
% 2.07/1.00      | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 2.07/1.00      inference(instantiation,[status(thm)],[c_639]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_2782,plain,
% 2.07/1.00      ( k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.07/1.00      | r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4)) = iProver_top
% 2.07/1.00      | v1_relat_1(sK3) != iProver_top ),
% 2.07/1.00      inference(predicate_to_equality,[status(thm)],[c_2781]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_2784,plain,
% 2.07/1.00      ( k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.07/1.00      | r1_tarski(k1_relat_1(sK3),k1_relat_1(sK4)) = iProver_top
% 2.07/1.00      | v1_relat_1(sK3) != iProver_top ),
% 2.07/1.00      inference(instantiation,[status(thm)],[c_2782]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_1776,plain,
% 2.07/1.00      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 2.07/1.00      theory(equality) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_2319,plain,
% 2.07/1.00      ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK1,sK2)
% 2.07/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 2.07/1.00      inference(instantiation,[status(thm)],[c_1776]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_2921,plain,
% 2.07/1.00      ( k2_zfmisc_1(k1_xboole_0,sK2) != k2_zfmisc_1(sK1,sK2)
% 2.07/1.00      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 2.07/1.00      inference(instantiation,[status(thm)],[c_2319]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_3116,plain,
% 2.07/1.00      ( k2_zfmisc_1(k1_relat_1(sK4),X0) != k2_zfmisc_1(sK1,sK2)
% 2.07/1.00      | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 2.07/1.00      inference(instantiation,[status(thm)],[c_2319]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_3117,plain,
% 2.07/1.00      ( k2_zfmisc_1(k1_relat_1(sK4),k1_xboole_0) != k2_zfmisc_1(sK1,sK2)
% 2.07/1.00      | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k1_xboole_0)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 2.07/1.00      inference(instantiation,[status(thm)],[c_3116]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_3817,plain,
% 2.07/1.00      ( r1_tarski(k1_relat_1(sK3),k1_xboole_0)
% 2.07/1.00      | ~ v1_relat_1(sK3)
% 2.07/1.00      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 2.07/1.00      inference(instantiation,[status(thm)],[c_639]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_3818,plain,
% 2.07/1.00      ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.07/1.00      | r1_tarski(k1_relat_1(sK3),k1_xboole_0) = iProver_top
% 2.07/1.00      | v1_relat_1(sK3) != iProver_top ),
% 2.07/1.00      inference(predicate_to_equality,[status(thm)],[c_3817]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_2657,plain,
% 2.07/1.00      ( X0 != X1 | X0 = sK1 | sK1 != X1 ),
% 2.07/1.00      inference(instantiation,[status(thm)],[c_1774]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_4058,plain,
% 2.07/1.00      ( k1_relat_1(sK4) != X0 | k1_relat_1(sK4) = sK1 | sK1 != X0 ),
% 2.07/1.00      inference(instantiation,[status(thm)],[c_2657]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_4059,plain,
% 2.07/1.00      ( k1_relat_1(sK4) = sK1
% 2.07/1.00      | k1_relat_1(sK4) != k1_xboole_0
% 2.07/1.00      | sK1 != k1_xboole_0 ),
% 2.07/1.00      inference(instantiation,[status(thm)],[c_4058]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_4745,plain,
% 2.07/1.00      ( X0 != sK2
% 2.07/1.00      | k2_zfmisc_1(k1_relat_1(sK4),X0) = k2_zfmisc_1(sK1,sK2)
% 2.07/1.00      | k1_relat_1(sK4) != sK1 ),
% 2.07/1.00      inference(instantiation,[status(thm)],[c_2490]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_4746,plain,
% 2.07/1.00      ( k2_zfmisc_1(k1_relat_1(sK4),k1_xboole_0) = k2_zfmisc_1(sK1,sK2)
% 2.07/1.00      | k1_relat_1(sK4) != sK1
% 2.07/1.00      | k1_xboole_0 != sK2 ),
% 2.07/1.00      inference(instantiation,[status(thm)],[c_4745]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_4758,plain,
% 2.07/1.00      ( r1_partfun1(sK3,sK4) = iProver_top ),
% 2.07/1.00      inference(global_propositional_subsumption,
% 2.07/1.00                [status(thm)],
% 2.07/1.00                [c_4076,c_25,c_27,c_1796,c_2311,c_2338,c_2411,c_2415,
% 2.07/1.00                 c_2437,c_2439,c_2440,c_2479,c_2486,c_2586,c_2609,c_2784,
% 2.07/1.00                 c_2830,c_2921,c_3117,c_3808,c_3818,c_3860,c_3944,c_4059,
% 2.07/1.00                 c_4746]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_4079,plain,
% 2.07/1.00      ( k1_funct_1(X0,X1) = k1_funct_1(sK4,X1)
% 2.07/1.00      | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
% 2.07/1.00      | r1_partfun1(X0,sK4) != iProver_top
% 2.07/1.00      | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
% 2.07/1.00      | v1_funct_1(X0) != iProver_top
% 2.07/1.00      | v1_funct_1(sK4) != iProver_top
% 2.07/1.00      | v1_relat_1(X0) != iProver_top
% 2.07/1.00      | v1_relat_1(sK4) != iProver_top ),
% 2.07/1.00      inference(superposition,[status(thm)],[c_3944,c_2059]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_4260,plain,
% 2.07/1.00      ( v1_relat_1(X0) != iProver_top
% 2.07/1.00      | k1_funct_1(X0,X1) = k1_funct_1(sK4,X1)
% 2.07/1.00      | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
% 2.07/1.00      | r1_partfun1(X0,sK4) != iProver_top
% 2.07/1.00      | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
% 2.07/1.00      | v1_funct_1(X0) != iProver_top ),
% 2.07/1.00      inference(global_propositional_subsumption,
% 2.07/1.00                [status(thm)],
% 2.07/1.00                [c_4079,c_27,c_2311,c_2486,c_2586]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_4261,plain,
% 2.07/1.00      ( k1_funct_1(X0,X1) = k1_funct_1(sK4,X1)
% 2.07/1.00      | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
% 2.07/1.00      | r1_partfun1(X0,sK4) != iProver_top
% 2.07/1.00      | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
% 2.07/1.00      | v1_funct_1(X0) != iProver_top
% 2.07/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.07/1.00      inference(renaming,[status(thm)],[c_4260]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_4273,plain,
% 2.07/1.00      ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
% 2.07/1.00      | r1_partfun1(sK3,sK4) != iProver_top
% 2.07/1.00      | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top
% 2.07/1.00      | v1_funct_1(sK3) != iProver_top
% 2.07/1.00      | v1_relat_1(sK3) != iProver_top ),
% 2.07/1.00      inference(superposition,[status(thm)],[c_2570,c_4261]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_4435,plain,
% 2.07/1.00      ( r1_partfun1(sK3,sK4) != iProver_top
% 2.07/1.00      | k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5) ),
% 2.07/1.00      inference(global_propositional_subsumption,
% 2.07/1.00                [status(thm)],
% 2.07/1.00                [c_4273,c_25,c_2311,c_2415,c_2437,c_2479,c_2586,c_2609,
% 2.07/1.00                 c_2830,c_2921,c_3808,c_3818,c_3860]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_4436,plain,
% 2.07/1.00      ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
% 2.07/1.00      | r1_partfun1(sK3,sK4) != iProver_top ),
% 2.07/1.00      inference(renaming,[status(thm)],[c_4435]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_4763,plain,
% 2.07/1.00      ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5) ),
% 2.07/1.00      inference(superposition,[status(thm)],[c_4758,c_4436]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_4844,plain,
% 2.07/1.00      ( k1_funct_1(sK3,sK5) != k1_funct_1(sK3,sK5)
% 2.07/1.00      | r1_partfun1(sK3,sK4) != iProver_top ),
% 2.07/1.00      inference(demodulation,[status(thm)],[c_4763,c_2058]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_4846,plain,
% 2.07/1.00      ( r1_partfun1(sK3,sK4) != iProver_top ),
% 2.07/1.00      inference(equality_resolution_simp,[status(thm)],[c_4844]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(contradiction,plain,
% 2.07/1.00      ( $false ),
% 2.07/1.00      inference(minisat,[status(thm)],[c_4846,c_4758]) ).
% 2.07/1.00  
% 2.07/1.00  
% 2.07/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.07/1.00  
% 2.07/1.00  ------                               Statistics
% 2.07/1.00  
% 2.07/1.00  ------ General
% 2.07/1.00  
% 2.07/1.00  abstr_ref_over_cycles:                  0
% 2.07/1.00  abstr_ref_under_cycles:                 0
% 2.07/1.00  gc_basic_clause_elim:                   0
% 2.07/1.00  forced_gc_time:                         0
% 2.07/1.00  parsing_time:                           0.01
% 2.07/1.00  unif_index_cands_time:                  0.
% 2.07/1.00  unif_index_add_time:                    0.
% 2.07/1.00  orderings_time:                         0.
% 2.07/1.00  out_proof_time:                         0.013
% 2.07/1.00  total_time:                             0.165
% 2.07/1.00  num_of_symbols:                         51
% 2.07/1.00  num_of_terms:                           2405
% 2.07/1.00  
% 2.07/1.00  ------ Preprocessing
% 2.07/1.00  
% 2.07/1.00  num_of_splits:                          0
% 2.07/1.00  num_of_split_atoms:                     0
% 2.07/1.00  num_of_reused_defs:                     0
% 2.07/1.00  num_eq_ax_congr_red:                    7
% 2.07/1.00  num_of_sem_filtered_clauses:            1
% 2.07/1.00  num_of_subtypes:                        0
% 2.07/1.00  monotx_restored_types:                  0
% 2.07/1.00  sat_num_of_epr_types:                   0
% 2.07/1.00  sat_num_of_non_cyclic_types:            0
% 2.07/1.00  sat_guarded_non_collapsed_types:        0
% 2.07/1.00  num_pure_diseq_elim:                    0
% 2.07/1.00  simp_replaced_by:                       0
% 2.07/1.00  res_preprocessed:                       106
% 2.07/1.00  prep_upred:                             0
% 2.07/1.00  prep_unflattend:                        137
% 2.07/1.00  smt_new_axioms:                         0
% 2.07/1.00  pred_elim_cands:                        8
% 2.07/1.00  pred_elim:                              3
% 2.07/1.00  pred_elim_cl:                           -3
% 2.07/1.00  pred_elim_cycles:                       8
% 2.07/1.00  merged_defs:                            0
% 2.07/1.00  merged_defs_ncl:                        0
% 2.07/1.00  bin_hyper_res:                          0
% 2.07/1.00  prep_cycles:                            3
% 2.07/1.00  pred_elim_time:                         0.033
% 2.07/1.00  splitting_time:                         0.
% 2.07/1.00  sem_filter_time:                        0.
% 2.07/1.00  monotx_time:                            0.001
% 2.07/1.00  subtype_inf_time:                       0.
% 2.07/1.00  
% 2.07/1.00  ------ Problem properties
% 2.07/1.00  
% 2.07/1.00  clauses:                                28
% 2.07/1.00  conjectures:                            6
% 2.07/1.00  epr:                                    3
% 2.07/1.00  horn:                                   20
% 2.07/1.00  ground:                                 13
% 2.07/1.00  unary:                                  3
% 2.07/1.00  binary:                                 5
% 2.07/1.00  lits:                                   98
% 2.07/1.00  lits_eq:                                62
% 2.07/1.00  fd_pure:                                0
% 2.07/1.00  fd_pseudo:                              0
% 2.07/1.00  fd_cond:                                0
% 2.07/1.00  fd_pseudo_cond:                         0
% 2.07/1.00  ac_symbols:                             0
% 2.07/1.00  
% 2.07/1.00  ------ Propositional Solver
% 2.07/1.00  
% 2.07/1.00  prop_solver_calls:                      25
% 2.07/1.00  prop_fast_solver_calls:                 1409
% 2.07/1.00  smt_solver_calls:                       0
% 2.07/1.00  smt_fast_solver_calls:                  0
% 2.07/1.00  prop_num_of_clauses:                    1024
% 2.07/1.00  prop_preprocess_simplified:             3558
% 2.07/1.00  prop_fo_subsumed:                       68
% 2.07/1.00  prop_solver_time:                       0.
% 2.07/1.00  smt_solver_time:                        0.
% 2.07/1.00  smt_fast_solver_time:                   0.
% 2.07/1.00  prop_fast_solver_time:                  0.
% 2.07/1.00  prop_unsat_core_time:                   0.
% 2.07/1.00  
% 2.07/1.00  ------ QBF
% 2.07/1.00  
% 2.07/1.00  qbf_q_res:                              0
% 2.07/1.00  qbf_num_tautologies:                    0
% 2.07/1.00  qbf_prep_cycles:                        0
% 2.07/1.00  
% 2.07/1.00  ------ BMC1
% 2.07/1.00  
% 2.07/1.00  bmc1_current_bound:                     -1
% 2.07/1.00  bmc1_last_solved_bound:                 -1
% 2.07/1.00  bmc1_unsat_core_size:                   -1
% 2.07/1.00  bmc1_unsat_core_parents_size:           -1
% 2.07/1.00  bmc1_merge_next_fun:                    0
% 2.07/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.07/1.00  
% 2.07/1.00  ------ Instantiation
% 2.07/1.00  
% 2.07/1.00  inst_num_of_clauses:                    333
% 2.07/1.00  inst_num_in_passive:                    37
% 2.07/1.00  inst_num_in_active:                     270
% 2.07/1.00  inst_num_in_unprocessed:                26
% 2.07/1.00  inst_num_of_loops:                      360
% 2.07/1.00  inst_num_of_learning_restarts:          0
% 2.07/1.00  inst_num_moves_active_passive:          85
% 2.07/1.00  inst_lit_activity:                      0
% 2.07/1.00  inst_lit_activity_moves:                0
% 2.07/1.00  inst_num_tautologies:                   0
% 2.07/1.00  inst_num_prop_implied:                  0
% 2.07/1.00  inst_num_existing_simplified:           0
% 2.07/1.00  inst_num_eq_res_simplified:             0
% 2.07/1.00  inst_num_child_elim:                    0
% 2.07/1.00  inst_num_of_dismatching_blockings:      199
% 2.07/1.00  inst_num_of_non_proper_insts:           511
% 2.07/1.00  inst_num_of_duplicates:                 0
% 2.07/1.00  inst_inst_num_from_inst_to_res:         0
% 2.07/1.00  inst_dismatching_checking_time:         0.
% 2.07/1.00  
% 2.07/1.00  ------ Resolution
% 2.07/1.00  
% 2.07/1.00  res_num_of_clauses:                     0
% 2.07/1.00  res_num_in_passive:                     0
% 2.07/1.00  res_num_in_active:                      0
% 2.07/1.00  res_num_of_loops:                       109
% 2.07/1.00  res_forward_subset_subsumed:            85
% 2.07/1.00  res_backward_subset_subsumed:           0
% 2.07/1.00  res_forward_subsumed:                   8
% 2.07/1.00  res_backward_subsumed:                  0
% 2.07/1.00  res_forward_subsumption_resolution:     0
% 2.07/1.00  res_backward_subsumption_resolution:    0
% 2.07/1.00  res_clause_to_clause_subsumption:       198
% 2.07/1.00  res_orphan_elimination:                 0
% 2.07/1.00  res_tautology_del:                      129
% 2.07/1.00  res_num_eq_res_simplified:              2
% 2.07/1.00  res_num_sel_changes:                    0
% 2.07/1.00  res_moves_from_active_to_pass:          0
% 2.07/1.00  
% 2.07/1.00  ------ Superposition
% 2.07/1.00  
% 2.07/1.00  sup_time_total:                         0.
% 2.07/1.00  sup_time_generating:                    0.
% 2.07/1.00  sup_time_sim_full:                      0.
% 2.07/1.00  sup_time_sim_immed:                     0.
% 2.07/1.00  
% 2.07/1.00  sup_num_of_clauses:                     38
% 2.07/1.00  sup_num_in_active:                      35
% 2.07/1.00  sup_num_in_passive:                     3
% 2.07/1.00  sup_num_of_loops:                       71
% 2.07/1.00  sup_fw_superposition:                   20
% 2.07/1.00  sup_bw_superposition:                   16
% 2.07/1.00  sup_immediate_simplified:               21
% 2.07/1.00  sup_given_eliminated:                   0
% 2.07/1.00  comparisons_done:                       0
% 2.07/1.00  comparisons_avoided:                    27
% 2.07/1.00  
% 2.07/1.00  ------ Simplifications
% 2.07/1.00  
% 2.07/1.00  
% 2.07/1.00  sim_fw_subset_subsumed:                 3
% 2.07/1.00  sim_bw_subset_subsumed:                 10
% 2.07/1.00  sim_fw_subsumed:                        2
% 2.07/1.00  sim_bw_subsumed:                        0
% 2.07/1.00  sim_fw_subsumption_res:                 1
% 2.07/1.00  sim_bw_subsumption_res:                 0
% 2.07/1.00  sim_tautology_del:                      3
% 2.07/1.00  sim_eq_tautology_del:                   12
% 2.07/1.00  sim_eq_res_simp:                        7
% 2.07/1.00  sim_fw_demodulated:                     5
% 2.07/1.00  sim_bw_demodulated:                     29
% 2.07/1.00  sim_light_normalised:                   17
% 2.07/1.00  sim_joinable_taut:                      0
% 2.07/1.00  sim_joinable_simp:                      0
% 2.07/1.00  sim_ac_normalised:                      0
% 2.07/1.00  sim_smt_subsumption:                    0
% 2.07/1.00  
%------------------------------------------------------------------------------
