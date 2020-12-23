%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:09:48 EST 2020

% Result     : Theorem 3.66s
% Output     : CNFRefutation 3.66s
% Verified   : 
% Statistics : Number of formulae       :  201 (1036 expanded)
%              Number of clauses        :  118 ( 288 expanded)
%              Number of leaves         :   26 ( 346 expanded)
%              Depth                    :   20
%              Number of atoms          :  774 (7648 expanded)
%              Number of equality atoms :  338 (2141 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
         => ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                   => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                      | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ~ v1_xboole_0(X2)
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X3,X1,X2)
              & v1_funct_1(X3) )
           => ! [X4] :
                ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                  & v1_funct_1(X4) )
               => ! [X5] :
                    ( m1_subset_1(X5,X1)
                   => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                     => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                        | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f38,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f39,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(flattening,[],[f38])).

fof(f54,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
          & k1_xboole_0 != X1
          & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
          & m1_subset_1(X5,X1) )
     => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),sK9) != k7_partfun1(X0,X4,k1_funct_1(X3,sK9))
        & k1_xboole_0 != X1
        & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
        & m1_subset_1(sK9,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
              & k1_xboole_0 != X1
              & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
              & m1_subset_1(X5,X1) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
          & v1_funct_1(X4) )
     => ( ? [X5] :
            ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,sK8),X5) != k7_partfun1(X0,sK8,k1_funct_1(X3,X5))
            & k1_xboole_0 != X1
            & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,sK8))
            & m1_subset_1(X5,X1) )
        & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
        & v1_funct_1(sK8) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( k1_funct_1(k8_funct_2(X1,X2,X0,sK7,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(sK7,X5))
                & k1_xboole_0 != X1
                & r1_tarski(k2_relset_1(X1,X2,sK7),k1_relset_1(X2,X0,X4))
                & m1_subset_1(X5,X1) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
            & v1_funct_1(X4) )
        & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(sK7,X1,X2)
        & v1_funct_1(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                    & k1_xboole_0 != X1
                    & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                    & m1_subset_1(X5,X1) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
        & ~ v1_xboole_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(sK5,sK6,sK4,X3,X4),X5) != k7_partfun1(sK4,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != sK5
                  & r1_tarski(k2_relset_1(sK5,sK6,X3),k1_relset_1(sK6,sK4,X4))
                  & m1_subset_1(X5,sK5) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
          & v1_funct_2(X3,sK5,sK6)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,
    ( k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),sK9) != k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9))
    & k1_xboole_0 != sK5
    & r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8))
    & m1_subset_1(sK9,sK5)
    & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4)))
    & v1_funct_1(sK8)
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    & v1_funct_2(sK7,sK5,sK6)
    & v1_funct_1(sK7)
    & ~ v1_xboole_0(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8,sK9])],[f39,f54,f53,f52,f51])).

fof(f88,plain,(
    m1_subset_1(sK9,sK5) ),
    inference(cnf_transformation,[],[f55])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f90,plain,(
    k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f55])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f85,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f55])).

fof(f12,axiom,(
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

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f50,plain,(
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
    inference(nnf_transformation,[],[f33])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f82,plain,(
    ~ v1_xboole_0(sK6) ),
    inference(cnf_transformation,[],[f55])).

fof(f84,plain,(
    v1_funct_2(sK7,sK5,sK6) ),
    inference(cnf_transformation,[],[f55])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X2
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ? [X7] :
                      ( k1_funct_1(X0,X7) = X5
                      & r2_hidden(X7,k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f44])).

fof(f48,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X5)) = X5
        & r2_hidden(sK3(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X1)) = X2
        & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k1_funct_1(X0,X3) != X2
                | ~ r2_hidden(X3,k1_relat_1(X0)) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( k1_funct_1(X0,X4) = X2
                & r2_hidden(X4,k1_relat_1(X0)) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( k1_funct_1(X0,X3) != sK1(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK1(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK1(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK1(X0,X1),X1) )
              & ( ( k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1)
                  & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK1(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK3(X0,X5)) = X5
                    & r2_hidden(sK3(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f45,f48,f47,f46])).

fof(f64,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f92,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f64])).

fof(f93,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f92])).

fof(f63,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK3(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f94,plain,(
    ! [X0,X5] :
      ( k1_funct_1(X0,sK3(X0,X5)) = X5
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f63])).

fof(f83,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f55])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f40])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f41,f42])).

fof(f56,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f87,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) ),
    inference(cnf_transformation,[],[f55])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f86,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f55])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(X1))
           => k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0)
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0)
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_1(X4) )
         => ( r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))
           => ( k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4)
              | k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4)
          | k1_xboole_0 = X1
          | ~ r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4)
          | k1_xboole_0 = X1
          | ~ r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f30])).

fof(f73,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4)
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f36])).

fof(f81,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f89,plain,(
    r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8)) ),
    inference(cnf_transformation,[],[f55])).

fof(f91,plain,(
    k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),sK9) != k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK9,sK5) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1869,plain,
    ( m1_subset_1(sK9,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1889,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3067,plain,
    ( r2_hidden(sK9,sK5) = iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1869,c_1889])).

cnf(c_42,plain,
    ( m1_subset_1(sK9,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_27,negated_conjecture,
    ( k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_3,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_110,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_4,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2179,plain,
    ( ~ v1_xboole_0(sK5)
    | ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2180,plain,
    ( k1_xboole_0 = sK5
    | v1_xboole_0(sK5) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2179])).

cnf(c_2384,plain,
    ( ~ m1_subset_1(X0,sK5)
    | r2_hidden(X0,sK5)
    | v1_xboole_0(sK5) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2665,plain,
    ( ~ m1_subset_1(sK9,sK5)
    | r2_hidden(sK9,sK5)
    | v1_xboole_0(sK5) ),
    inference(instantiation,[status(thm)],[c_2384])).

cnf(c_2666,plain,
    ( m1_subset_1(sK9,sK5) != iProver_top
    | r2_hidden(sK9,sK5) = iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2665])).

cnf(c_4225,plain,
    ( r2_hidden(sK9,sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3067,c_42,c_27,c_110,c_2180,c_2666])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1866,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1872,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3882,plain,
    ( k1_relset_1(sK5,sK6,sK7) = sK5
    | sK6 = k1_xboole_0
    | v1_funct_2(sK7,sK5,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1866,c_1872])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1880,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3058,plain,
    ( k1_relset_1(sK5,sK6,sK7) = k1_relat_1(sK7) ),
    inference(superposition,[status(thm)],[c_1866,c_1880])).

cnf(c_3886,plain,
    ( k1_relat_1(sK7) = sK5
    | sK6 = k1_xboole_0
    | v1_funct_2(sK7,sK5,sK6) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3882,c_3058])).

cnf(c_35,negated_conjecture,
    ( ~ v1_xboole_0(sK6) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_33,negated_conjecture,
    ( v1_funct_2(sK7,sK5,sK6) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_38,plain,
    ( v1_funct_2(sK7,sK5,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_1286,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2188,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK6)
    | sK6 != X0 ),
    inference(instantiation,[status(thm)],[c_1286])).

cnf(c_2190,plain,
    ( v1_xboole_0(sK6)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK6 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2188])).

cnf(c_4282,plain,
    ( k1_relat_1(sK7) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3886,c_35,c_38,c_3,c_2190])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1885,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | k1_funct_1(X1,sK3(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1884,plain,
    ( k1_funct_1(X0,sK3(X0,X1)) = X1
    | r2_hidden(X1,k2_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4655,plain,
    ( k1_funct_1(X0,sK3(X0,k1_funct_1(X0,X1))) = k1_funct_1(X0,X1)
    | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1885,c_1884])).

cnf(c_8100,plain,
    ( k1_funct_1(sK7,sK3(sK7,k1_funct_1(sK7,X0))) = k1_funct_1(sK7,X0)
    | r2_hidden(X0,sK5) != iProver_top
    | v1_relat_1(sK7) != iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_4282,c_4655])).

cnf(c_34,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_37,plain,
    ( v1_funct_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_39,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_2185,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_2186,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
    | v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2185])).

cnf(c_8451,plain,
    ( k1_funct_1(sK7,sK3(sK7,k1_funct_1(sK7,X0))) = k1_funct_1(sK7,X0)
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8100,c_37,c_39,c_2186])).

cnf(c_8463,plain,
    ( k1_funct_1(sK7,sK3(sK7,k1_funct_1(sK7,sK9))) = k1_funct_1(sK7,sK9) ),
    inference(superposition,[status(thm)],[c_4225,c_8451])).

cnf(c_8576,plain,
    ( r2_hidden(sK3(sK7,k1_funct_1(sK7,sK9)),k1_relat_1(sK7)) != iProver_top
    | r2_hidden(k1_funct_1(sK7,sK9),k2_relat_1(sK7)) = iProver_top
    | v1_relat_1(sK7) != iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_8463,c_1885])).

cnf(c_8581,plain,
    ( r2_hidden(sK3(sK7,k1_funct_1(sK7,sK9)),sK5) != iProver_top
    | r2_hidden(k1_funct_1(sK7,sK9),k2_relat_1(sK7)) = iProver_top
    | v1_relat_1(sK7) != iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8576,c_4282])).

cnf(c_1282,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2501,plain,
    ( sK9 = sK9 ),
    inference(instantiation,[status(thm)],[c_1282])).

cnf(c_1285,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2928,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK9,sK5)
    | X0 != sK9
    | X1 != sK5 ),
    inference(instantiation,[status(thm)],[c_1285])).

cnf(c_3813,plain,
    ( r2_hidden(sK9,X0)
    | ~ r2_hidden(sK9,sK5)
    | X0 != sK5
    | sK9 != sK9 ),
    inference(instantiation,[status(thm)],[c_2928])).

cnf(c_6102,plain,
    ( r2_hidden(sK9,k1_relat_1(sK7))
    | ~ r2_hidden(sK9,sK5)
    | k1_relat_1(sK7) != sK5
    | sK9 != sK9 ),
    inference(instantiation,[status(thm)],[c_3813])).

cnf(c_6107,plain,
    ( k1_relat_1(sK7) != sK5
    | sK9 != sK9
    | r2_hidden(sK9,k1_relat_1(sK7)) = iProver_top
    | r2_hidden(sK9,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6102])).

cnf(c_2363,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK7))
    | r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7))
    | ~ v1_relat_1(sK7)
    | ~ v1_funct_1(sK7) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_6106,plain,
    ( r2_hidden(k1_funct_1(sK7,sK9),k2_relat_1(sK7))
    | ~ r2_hidden(sK9,k1_relat_1(sK7))
    | ~ v1_relat_1(sK7)
    | ~ v1_funct_1(sK7) ),
    inference(instantiation,[status(thm)],[c_2363])).

cnf(c_6109,plain,
    ( r2_hidden(k1_funct_1(sK7,sK9),k2_relat_1(sK7)) = iProver_top
    | r2_hidden(sK9,k1_relat_1(sK7)) != iProver_top
    | v1_relat_1(sK7) != iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6106])).

cnf(c_8636,plain,
    ( r2_hidden(k1_funct_1(sK7,sK9),k2_relat_1(sK7)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8581,c_35,c_37,c_38,c_39,c_42,c_27,c_3,c_110,c_2180,c_2186,c_2190,c_2501,c_2666,c_3886,c_6107,c_6109])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1892,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_8641,plain,
    ( r2_hidden(k1_funct_1(sK7,sK9),X0) = iProver_top
    | r1_tarski(k2_relat_1(sK7),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8636,c_1892])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1868,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_14,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_24,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k7_partfun1(X1,X0,X2) = k1_funct_1(X0,X2) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_378,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(resolution,[status(thm)],[c_14,c_24])).

cnf(c_382,plain,
    ( ~ r2_hidden(X3,k1_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_378,c_13])).

cnf(c_383,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(renaming,[status(thm)],[c_382])).

cnf(c_1862,plain,
    ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) != iProver_top
    | r2_hidden(X2,k1_relat_1(X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_383])).

cnf(c_2396,plain,
    ( k7_partfun1(sK4,sK8,X0) = k1_funct_1(sK8,X0)
    | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
    | v1_funct_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_1868,c_1862])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_40,plain,
    ( v1_funct_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_2650,plain,
    ( r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
    | k7_partfun1(sK4,sK8,X0) = k1_funct_1(sK8,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2396,c_40])).

cnf(c_2651,plain,
    ( k7_partfun1(sK4,sK8,X0) = k1_funct_1(sK8,X0)
    | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2650])).

cnf(c_9042,plain,
    ( k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) = k1_funct_1(sK8,k1_funct_1(sK7,sK9))
    | r1_tarski(k2_relat_1(sK7),k1_relat_1(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8641,c_2651])).

cnf(c_1881,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2702,plain,
    ( v1_relat_1(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_1868,c_1881])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1882,plain,
    ( k1_funct_1(k5_relat_1(X0,X1),X2) = k1_funct_1(X1,k1_funct_1(X0,X2))
    | r2_hidden(X2,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_5340,plain,
    ( k1_funct_1(X0,k1_funct_1(sK7,X1)) = k1_funct_1(k5_relat_1(sK7,X0),X1)
    | r2_hidden(X1,sK5) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK7) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_4282,c_1882])).

cnf(c_7389,plain,
    ( v1_funct_1(X0) != iProver_top
    | k1_funct_1(X0,k1_funct_1(sK7,X1)) = k1_funct_1(k5_relat_1(sK7,X0),X1)
    | r2_hidden(X1,sK5) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5340,c_37,c_39,c_2186])).

cnf(c_7390,plain,
    ( k1_funct_1(X0,k1_funct_1(sK7,X1)) = k1_funct_1(k5_relat_1(sK7,X0),X1)
    | r2_hidden(X1,sK5) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_7389])).

cnf(c_7403,plain,
    ( k1_funct_1(k5_relat_1(sK7,X0),sK9) = k1_funct_1(X0,k1_funct_1(sK7,sK9))
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4225,c_7390])).

cnf(c_7585,plain,
    ( k1_funct_1(sK8,k1_funct_1(sK7,sK9)) = k1_funct_1(k5_relat_1(sK7,sK8),sK9)
    | v1_funct_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_2702,c_7403])).

cnf(c_7598,plain,
    ( k1_funct_1(sK8,k1_funct_1(sK7,sK9)) = k1_funct_1(k5_relat_1(sK7,sK8),sK9) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7585,c_40])).

cnf(c_3057,plain,
    ( k1_relset_1(sK6,sK4,sK8) = k1_relat_1(sK8) ),
    inference(superposition,[status(thm)],[c_1868,c_1880])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1879,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2986,plain,
    ( k2_relset_1(sK5,sK6,sK7) = k2_relat_1(sK7) ),
    inference(superposition,[status(thm)],[c_1866,c_1879])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X4,X3))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X1,X2,X2,X4,X0,X3) = k8_funct_2(X1,X2,X4,X0,X3)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1878,plain,
    ( k1_partfun1(X0,X1,X1,X2,X3,X4) = k8_funct_2(X0,X1,X2,X3,X4)
    | k1_xboole_0 = X1
    | v1_funct_2(X3,X0,X1) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4982,plain,
    ( k1_partfun1(sK5,sK6,sK6,X0,sK7,X1) = k8_funct_2(sK5,sK6,X0,sK7,X1)
    | sK6 = k1_xboole_0
    | v1_funct_2(sK7,sK5,sK6) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK6,X0))) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
    | r1_tarski(k2_relat_1(sK7),k1_relset_1(sK6,X0,X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2986,c_1878])).

cnf(c_5681,plain,
    ( v1_funct_1(X1) != iProver_top
    | r1_tarski(k2_relat_1(sK7),k1_relset_1(sK6,X0,X1)) != iProver_top
    | k1_partfun1(sK5,sK6,sK6,X0,sK7,X1) = k8_funct_2(sK5,sK6,X0,sK7,X1)
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK6,X0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4982,c_35,c_37,c_38,c_39,c_3,c_2190])).

cnf(c_5682,plain,
    ( k1_partfun1(sK5,sK6,sK6,X0,sK7,X1) = k8_funct_2(sK5,sK6,X0,sK7,X1)
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK6,X0))) != iProver_top
    | r1_tarski(k2_relat_1(sK7),k1_relset_1(sK6,X0,X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_5681])).

cnf(c_5691,plain,
    ( k1_partfun1(sK5,sK6,sK6,sK4,sK7,sK8) = k8_funct_2(sK5,sK6,sK4,sK7,sK8)
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) != iProver_top
    | r1_tarski(k2_relat_1(sK7),k1_relat_1(sK8)) != iProver_top
    | v1_funct_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_3057,c_5682])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1871,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2904,plain,
    ( k1_partfun1(X0,X1,sK6,sK4,X2,sK8) = k5_relat_1(X2,sK8)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_1868,c_1871])).

cnf(c_3642,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK6,sK4,X2,sK8) = k5_relat_1(X2,sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2904,c_40])).

cnf(c_3643,plain,
    ( k1_partfun1(X0,X1,sK6,sK4,X2,sK8) = k5_relat_1(X2,sK8)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_3642])).

cnf(c_3652,plain,
    ( k1_partfun1(sK5,sK6,sK6,sK4,sK7,sK8) = k5_relat_1(sK7,sK8)
    | v1_funct_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1866,c_3643])).

cnf(c_2280,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK7)
    | k1_partfun1(X3,X4,X1,X2,sK7,X0) = k5_relat_1(sK7,X0) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_2609,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(sK8)
    | ~ v1_funct_1(sK7)
    | k1_partfun1(X2,X3,X0,X1,sK7,sK8) = k5_relat_1(sK7,sK8) ),
    inference(instantiation,[status(thm)],[c_2280])).

cnf(c_2946,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK8)
    | ~ v1_funct_1(sK7)
    | k1_partfun1(X0,X1,sK6,sK4,sK7,sK8) = k5_relat_1(sK7,sK8) ),
    inference(instantiation,[status(thm)],[c_2609])).

cnf(c_3226,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | ~ v1_funct_1(sK8)
    | ~ v1_funct_1(sK7)
    | k1_partfun1(sK5,sK6,sK6,sK4,sK7,sK8) = k5_relat_1(sK7,sK8) ),
    inference(instantiation,[status(thm)],[c_2946])).

cnf(c_3778,plain,
    ( k1_partfun1(sK5,sK6,sK6,sK4,sK7,sK8) = k5_relat_1(sK7,sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3652,c_34,c_32,c_31,c_30,c_3226])).

cnf(c_5692,plain,
    ( k8_funct_2(sK5,sK6,sK4,sK7,sK8) = k5_relat_1(sK7,sK8)
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) != iProver_top
    | r1_tarski(k2_relat_1(sK7),k1_relat_1(sK8)) != iProver_top
    | v1_funct_1(sK8) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5691,c_3778])).

cnf(c_41,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_28,negated_conjecture,
    ( r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1870,plain,
    ( r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_3224,plain,
    ( r1_tarski(k2_relat_1(sK7),k1_relset_1(sK6,sK4,sK8)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2986,c_1870])).

cnf(c_3638,plain,
    ( r1_tarski(k2_relat_1(sK7),k1_relat_1(sK8)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3224,c_3057])).

cnf(c_5707,plain,
    ( k8_funct_2(sK5,sK6,sK4,sK7,sK8) = k5_relat_1(sK7,sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5692,c_40,c_41,c_3638])).

cnf(c_26,negated_conjecture,
    ( k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),sK9) != k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_5710,plain,
    ( k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) != k1_funct_1(k5_relat_1(sK7,sK8),sK9) ),
    inference(demodulation,[status(thm)],[c_5707,c_26])).

cnf(c_7601,plain,
    ( k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) != k1_funct_1(sK8,k1_funct_1(sK7,sK9)) ),
    inference(demodulation,[status(thm)],[c_7598,c_5710])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9042,c_7601,c_3638])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:03:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.66/1.02  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.66/1.02  
% 3.66/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.66/1.02  
% 3.66/1.02  ------  iProver source info
% 3.66/1.02  
% 3.66/1.02  git: date: 2020-06-30 10:37:57 +0100
% 3.66/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.66/1.02  git: non_committed_changes: false
% 3.66/1.02  git: last_make_outside_of_git: false
% 3.66/1.02  
% 3.66/1.02  ------ 
% 3.66/1.02  
% 3.66/1.02  ------ Input Options
% 3.66/1.02  
% 3.66/1.02  --out_options                           all
% 3.66/1.02  --tptp_safe_out                         true
% 3.66/1.02  --problem_path                          ""
% 3.66/1.02  --include_path                          ""
% 3.66/1.02  --clausifier                            res/vclausify_rel
% 3.66/1.02  --clausifier_options                    --mode clausify
% 3.66/1.02  --stdin                                 false
% 3.66/1.02  --stats_out                             all
% 3.66/1.02  
% 3.66/1.02  ------ General Options
% 3.66/1.02  
% 3.66/1.02  --fof                                   false
% 3.66/1.02  --time_out_real                         305.
% 3.66/1.02  --time_out_virtual                      -1.
% 3.66/1.02  --symbol_type_check                     false
% 3.66/1.02  --clausify_out                          false
% 3.66/1.02  --sig_cnt_out                           false
% 3.66/1.02  --trig_cnt_out                          false
% 3.66/1.02  --trig_cnt_out_tolerance                1.
% 3.66/1.02  --trig_cnt_out_sk_spl                   false
% 3.66/1.02  --abstr_cl_out                          false
% 3.66/1.02  
% 3.66/1.02  ------ Global Options
% 3.66/1.02  
% 3.66/1.02  --schedule                              default
% 3.66/1.02  --add_important_lit                     false
% 3.66/1.02  --prop_solver_per_cl                    1000
% 3.66/1.02  --min_unsat_core                        false
% 3.66/1.02  --soft_assumptions                      false
% 3.66/1.02  --soft_lemma_size                       3
% 3.66/1.02  --prop_impl_unit_size                   0
% 3.66/1.02  --prop_impl_unit                        []
% 3.66/1.02  --share_sel_clauses                     true
% 3.66/1.02  --reset_solvers                         false
% 3.66/1.02  --bc_imp_inh                            [conj_cone]
% 3.66/1.02  --conj_cone_tolerance                   3.
% 3.66/1.02  --extra_neg_conj                        none
% 3.66/1.02  --large_theory_mode                     true
% 3.66/1.02  --prolific_symb_bound                   200
% 3.66/1.02  --lt_threshold                          2000
% 3.66/1.02  --clause_weak_htbl                      true
% 3.66/1.02  --gc_record_bc_elim                     false
% 3.66/1.02  
% 3.66/1.02  ------ Preprocessing Options
% 3.66/1.02  
% 3.66/1.02  --preprocessing_flag                    true
% 3.66/1.02  --time_out_prep_mult                    0.1
% 3.66/1.02  --splitting_mode                        input
% 3.66/1.02  --splitting_grd                         true
% 3.66/1.02  --splitting_cvd                         false
% 3.66/1.02  --splitting_cvd_svl                     false
% 3.66/1.02  --splitting_nvd                         32
% 3.66/1.02  --sub_typing                            true
% 3.66/1.02  --prep_gs_sim                           true
% 3.66/1.02  --prep_unflatten                        true
% 3.66/1.02  --prep_res_sim                          true
% 3.66/1.02  --prep_upred                            true
% 3.66/1.02  --prep_sem_filter                       exhaustive
% 3.66/1.02  --prep_sem_filter_out                   false
% 3.66/1.02  --pred_elim                             true
% 3.66/1.02  --res_sim_input                         true
% 3.66/1.02  --eq_ax_congr_red                       true
% 3.66/1.02  --pure_diseq_elim                       true
% 3.66/1.02  --brand_transform                       false
% 3.66/1.02  --non_eq_to_eq                          false
% 3.66/1.02  --prep_def_merge                        true
% 3.66/1.02  --prep_def_merge_prop_impl              false
% 3.66/1.02  --prep_def_merge_mbd                    true
% 3.66/1.02  --prep_def_merge_tr_red                 false
% 3.66/1.02  --prep_def_merge_tr_cl                  false
% 3.66/1.02  --smt_preprocessing                     true
% 3.66/1.02  --smt_ac_axioms                         fast
% 3.66/1.02  --preprocessed_out                      false
% 3.66/1.02  --preprocessed_stats                    false
% 3.66/1.02  
% 3.66/1.02  ------ Abstraction refinement Options
% 3.66/1.02  
% 3.66/1.02  --abstr_ref                             []
% 3.66/1.02  --abstr_ref_prep                        false
% 3.66/1.02  --abstr_ref_until_sat                   false
% 3.66/1.02  --abstr_ref_sig_restrict                funpre
% 3.66/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.66/1.02  --abstr_ref_under                       []
% 3.66/1.02  
% 3.66/1.02  ------ SAT Options
% 3.66/1.02  
% 3.66/1.02  --sat_mode                              false
% 3.66/1.02  --sat_fm_restart_options                ""
% 3.66/1.02  --sat_gr_def                            false
% 3.66/1.02  --sat_epr_types                         true
% 3.66/1.02  --sat_non_cyclic_types                  false
% 3.66/1.02  --sat_finite_models                     false
% 3.66/1.02  --sat_fm_lemmas                         false
% 3.66/1.02  --sat_fm_prep                           false
% 3.66/1.02  --sat_fm_uc_incr                        true
% 3.66/1.02  --sat_out_model                         small
% 3.66/1.02  --sat_out_clauses                       false
% 3.66/1.02  
% 3.66/1.02  ------ QBF Options
% 3.66/1.02  
% 3.66/1.02  --qbf_mode                              false
% 3.66/1.02  --qbf_elim_univ                         false
% 3.66/1.02  --qbf_dom_inst                          none
% 3.66/1.02  --qbf_dom_pre_inst                      false
% 3.66/1.02  --qbf_sk_in                             false
% 3.66/1.02  --qbf_pred_elim                         true
% 3.66/1.02  --qbf_split                             512
% 3.66/1.02  
% 3.66/1.02  ------ BMC1 Options
% 3.66/1.02  
% 3.66/1.02  --bmc1_incremental                      false
% 3.66/1.02  --bmc1_axioms                           reachable_all
% 3.66/1.02  --bmc1_min_bound                        0
% 3.66/1.02  --bmc1_max_bound                        -1
% 3.66/1.02  --bmc1_max_bound_default                -1
% 3.66/1.02  --bmc1_symbol_reachability              true
% 3.66/1.02  --bmc1_property_lemmas                  false
% 3.66/1.02  --bmc1_k_induction                      false
% 3.66/1.02  --bmc1_non_equiv_states                 false
% 3.66/1.02  --bmc1_deadlock                         false
% 3.66/1.02  --bmc1_ucm                              false
% 3.66/1.02  --bmc1_add_unsat_core                   none
% 3.66/1.02  --bmc1_unsat_core_children              false
% 3.66/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.66/1.02  --bmc1_out_stat                         full
% 3.66/1.02  --bmc1_ground_init                      false
% 3.66/1.02  --bmc1_pre_inst_next_state              false
% 3.66/1.02  --bmc1_pre_inst_state                   false
% 3.66/1.02  --bmc1_pre_inst_reach_state             false
% 3.66/1.02  --bmc1_out_unsat_core                   false
% 3.66/1.02  --bmc1_aig_witness_out                  false
% 3.66/1.02  --bmc1_verbose                          false
% 3.66/1.02  --bmc1_dump_clauses_tptp                false
% 3.66/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.66/1.02  --bmc1_dump_file                        -
% 3.66/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.66/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.66/1.02  --bmc1_ucm_extend_mode                  1
% 3.66/1.02  --bmc1_ucm_init_mode                    2
% 3.66/1.02  --bmc1_ucm_cone_mode                    none
% 3.66/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.66/1.02  --bmc1_ucm_relax_model                  4
% 3.66/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.66/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.66/1.02  --bmc1_ucm_layered_model                none
% 3.66/1.02  --bmc1_ucm_max_lemma_size               10
% 3.66/1.02  
% 3.66/1.02  ------ AIG Options
% 3.66/1.02  
% 3.66/1.02  --aig_mode                              false
% 3.66/1.02  
% 3.66/1.02  ------ Instantiation Options
% 3.66/1.02  
% 3.66/1.02  --instantiation_flag                    true
% 3.66/1.02  --inst_sos_flag                         false
% 3.66/1.02  --inst_sos_phase                        true
% 3.66/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.66/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.66/1.02  --inst_lit_sel_side                     num_symb
% 3.66/1.02  --inst_solver_per_active                1400
% 3.66/1.02  --inst_solver_calls_frac                1.
% 3.66/1.02  --inst_passive_queue_type               priority_queues
% 3.66/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.66/1.02  --inst_passive_queues_freq              [25;2]
% 3.66/1.02  --inst_dismatching                      true
% 3.66/1.02  --inst_eager_unprocessed_to_passive     true
% 3.66/1.02  --inst_prop_sim_given                   true
% 3.66/1.02  --inst_prop_sim_new                     false
% 3.66/1.02  --inst_subs_new                         false
% 3.66/1.02  --inst_eq_res_simp                      false
% 3.66/1.02  --inst_subs_given                       false
% 3.66/1.02  --inst_orphan_elimination               true
% 3.66/1.02  --inst_learning_loop_flag               true
% 3.66/1.02  --inst_learning_start                   3000
% 3.66/1.02  --inst_learning_factor                  2
% 3.66/1.02  --inst_start_prop_sim_after_learn       3
% 3.66/1.02  --inst_sel_renew                        solver
% 3.66/1.02  --inst_lit_activity_flag                true
% 3.66/1.02  --inst_restr_to_given                   false
% 3.66/1.02  --inst_activity_threshold               500
% 3.66/1.02  --inst_out_proof                        true
% 3.66/1.02  
% 3.66/1.02  ------ Resolution Options
% 3.66/1.02  
% 3.66/1.02  --resolution_flag                       true
% 3.66/1.02  --res_lit_sel                           adaptive
% 3.66/1.02  --res_lit_sel_side                      none
% 3.66/1.02  --res_ordering                          kbo
% 3.66/1.02  --res_to_prop_solver                    active
% 3.66/1.02  --res_prop_simpl_new                    false
% 3.66/1.02  --res_prop_simpl_given                  true
% 3.66/1.02  --res_passive_queue_type                priority_queues
% 3.66/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.66/1.02  --res_passive_queues_freq               [15;5]
% 3.66/1.02  --res_forward_subs                      full
% 3.66/1.02  --res_backward_subs                     full
% 3.66/1.02  --res_forward_subs_resolution           true
% 3.66/1.02  --res_backward_subs_resolution          true
% 3.66/1.02  --res_orphan_elimination                true
% 3.66/1.02  --res_time_limit                        2.
% 3.66/1.02  --res_out_proof                         true
% 3.66/1.02  
% 3.66/1.02  ------ Superposition Options
% 3.66/1.02  
% 3.66/1.02  --superposition_flag                    true
% 3.66/1.02  --sup_passive_queue_type                priority_queues
% 3.66/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.66/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.66/1.02  --demod_completeness_check              fast
% 3.66/1.02  --demod_use_ground                      true
% 3.66/1.02  --sup_to_prop_solver                    passive
% 3.66/1.02  --sup_prop_simpl_new                    true
% 3.66/1.02  --sup_prop_simpl_given                  true
% 3.66/1.02  --sup_fun_splitting                     false
% 3.66/1.02  --sup_smt_interval                      50000
% 3.66/1.02  
% 3.66/1.02  ------ Superposition Simplification Setup
% 3.66/1.02  
% 3.66/1.02  --sup_indices_passive                   []
% 3.66/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.66/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.66/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.66/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.66/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.66/1.02  --sup_full_bw                           [BwDemod]
% 3.66/1.02  --sup_immed_triv                        [TrivRules]
% 3.66/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.66/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.66/1.02  --sup_immed_bw_main                     []
% 3.66/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.66/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.66/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.66/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.66/1.02  
% 3.66/1.02  ------ Combination Options
% 3.66/1.02  
% 3.66/1.02  --comb_res_mult                         3
% 3.66/1.02  --comb_sup_mult                         2
% 3.66/1.02  --comb_inst_mult                        10
% 3.66/1.02  
% 3.66/1.02  ------ Debug Options
% 3.66/1.02  
% 3.66/1.02  --dbg_backtrace                         false
% 3.66/1.02  --dbg_dump_prop_clauses                 false
% 3.66/1.02  --dbg_dump_prop_clauses_file            -
% 3.66/1.02  --dbg_out_stat                          false
% 3.66/1.02  ------ Parsing...
% 3.66/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.66/1.02  
% 3.66/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.66/1.02  
% 3.66/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.66/1.02  
% 3.66/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.66/1.02  ------ Proving...
% 3.66/1.02  ------ Problem Properties 
% 3.66/1.02  
% 3.66/1.02  
% 3.66/1.02  clauses                                 35
% 3.66/1.02  conjectures                             10
% 3.66/1.02  EPR                                     10
% 3.66/1.02  Horn                                    26
% 3.66/1.02  unary                                   11
% 3.66/1.02  binary                                  5
% 3.66/1.02  lits                                    102
% 3.66/1.02  lits eq                                 25
% 3.66/1.02  fd_pure                                 0
% 3.66/1.02  fd_pseudo                               0
% 3.66/1.02  fd_cond                                 4
% 3.66/1.02  fd_pseudo_cond                          4
% 3.66/1.02  AC symbols                              0
% 3.66/1.02  
% 3.66/1.02  ------ Schedule dynamic 5 is on 
% 3.66/1.02  
% 3.66/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.66/1.02  
% 3.66/1.02  
% 3.66/1.02  ------ 
% 3.66/1.02  Current options:
% 3.66/1.02  ------ 
% 3.66/1.02  
% 3.66/1.02  ------ Input Options
% 3.66/1.02  
% 3.66/1.02  --out_options                           all
% 3.66/1.02  --tptp_safe_out                         true
% 3.66/1.02  --problem_path                          ""
% 3.66/1.02  --include_path                          ""
% 3.66/1.02  --clausifier                            res/vclausify_rel
% 3.66/1.02  --clausifier_options                    --mode clausify
% 3.66/1.02  --stdin                                 false
% 3.66/1.02  --stats_out                             all
% 3.66/1.02  
% 3.66/1.02  ------ General Options
% 3.66/1.02  
% 3.66/1.02  --fof                                   false
% 3.66/1.02  --time_out_real                         305.
% 3.66/1.02  --time_out_virtual                      -1.
% 3.66/1.02  --symbol_type_check                     false
% 3.66/1.02  --clausify_out                          false
% 3.66/1.02  --sig_cnt_out                           false
% 3.66/1.02  --trig_cnt_out                          false
% 3.66/1.02  --trig_cnt_out_tolerance                1.
% 3.66/1.02  --trig_cnt_out_sk_spl                   false
% 3.66/1.02  --abstr_cl_out                          false
% 3.66/1.02  
% 3.66/1.02  ------ Global Options
% 3.66/1.02  
% 3.66/1.02  --schedule                              default
% 3.66/1.02  --add_important_lit                     false
% 3.66/1.02  --prop_solver_per_cl                    1000
% 3.66/1.02  --min_unsat_core                        false
% 3.66/1.02  --soft_assumptions                      false
% 3.66/1.02  --soft_lemma_size                       3
% 3.66/1.02  --prop_impl_unit_size                   0
% 3.66/1.02  --prop_impl_unit                        []
% 3.66/1.02  --share_sel_clauses                     true
% 3.66/1.02  --reset_solvers                         false
% 3.66/1.02  --bc_imp_inh                            [conj_cone]
% 3.66/1.02  --conj_cone_tolerance                   3.
% 3.66/1.02  --extra_neg_conj                        none
% 3.66/1.02  --large_theory_mode                     true
% 3.66/1.02  --prolific_symb_bound                   200
% 3.66/1.02  --lt_threshold                          2000
% 3.66/1.02  --clause_weak_htbl                      true
% 3.66/1.02  --gc_record_bc_elim                     false
% 3.66/1.02  
% 3.66/1.02  ------ Preprocessing Options
% 3.66/1.02  
% 3.66/1.02  --preprocessing_flag                    true
% 3.66/1.02  --time_out_prep_mult                    0.1
% 3.66/1.02  --splitting_mode                        input
% 3.66/1.02  --splitting_grd                         true
% 3.66/1.02  --splitting_cvd                         false
% 3.66/1.02  --splitting_cvd_svl                     false
% 3.66/1.02  --splitting_nvd                         32
% 3.66/1.02  --sub_typing                            true
% 3.66/1.02  --prep_gs_sim                           true
% 3.66/1.02  --prep_unflatten                        true
% 3.66/1.02  --prep_res_sim                          true
% 3.66/1.02  --prep_upred                            true
% 3.66/1.02  --prep_sem_filter                       exhaustive
% 3.66/1.02  --prep_sem_filter_out                   false
% 3.66/1.02  --pred_elim                             true
% 3.66/1.02  --res_sim_input                         true
% 3.66/1.02  --eq_ax_congr_red                       true
% 3.66/1.02  --pure_diseq_elim                       true
% 3.66/1.02  --brand_transform                       false
% 3.66/1.02  --non_eq_to_eq                          false
% 3.66/1.02  --prep_def_merge                        true
% 3.66/1.02  --prep_def_merge_prop_impl              false
% 3.66/1.02  --prep_def_merge_mbd                    true
% 3.66/1.02  --prep_def_merge_tr_red                 false
% 3.66/1.02  --prep_def_merge_tr_cl                  false
% 3.66/1.02  --smt_preprocessing                     true
% 3.66/1.02  --smt_ac_axioms                         fast
% 3.66/1.02  --preprocessed_out                      false
% 3.66/1.02  --preprocessed_stats                    false
% 3.66/1.02  
% 3.66/1.02  ------ Abstraction refinement Options
% 3.66/1.02  
% 3.66/1.02  --abstr_ref                             []
% 3.66/1.02  --abstr_ref_prep                        false
% 3.66/1.02  --abstr_ref_until_sat                   false
% 3.66/1.02  --abstr_ref_sig_restrict                funpre
% 3.66/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.66/1.02  --abstr_ref_under                       []
% 3.66/1.02  
% 3.66/1.02  ------ SAT Options
% 3.66/1.02  
% 3.66/1.02  --sat_mode                              false
% 3.66/1.02  --sat_fm_restart_options                ""
% 3.66/1.02  --sat_gr_def                            false
% 3.66/1.02  --sat_epr_types                         true
% 3.66/1.02  --sat_non_cyclic_types                  false
% 3.66/1.02  --sat_finite_models                     false
% 3.66/1.02  --sat_fm_lemmas                         false
% 3.66/1.02  --sat_fm_prep                           false
% 3.66/1.02  --sat_fm_uc_incr                        true
% 3.66/1.02  --sat_out_model                         small
% 3.66/1.02  --sat_out_clauses                       false
% 3.66/1.02  
% 3.66/1.02  ------ QBF Options
% 3.66/1.02  
% 3.66/1.02  --qbf_mode                              false
% 3.66/1.02  --qbf_elim_univ                         false
% 3.66/1.02  --qbf_dom_inst                          none
% 3.66/1.02  --qbf_dom_pre_inst                      false
% 3.66/1.02  --qbf_sk_in                             false
% 3.66/1.02  --qbf_pred_elim                         true
% 3.66/1.02  --qbf_split                             512
% 3.66/1.02  
% 3.66/1.02  ------ BMC1 Options
% 3.66/1.02  
% 3.66/1.02  --bmc1_incremental                      false
% 3.66/1.02  --bmc1_axioms                           reachable_all
% 3.66/1.02  --bmc1_min_bound                        0
% 3.66/1.02  --bmc1_max_bound                        -1
% 3.66/1.02  --bmc1_max_bound_default                -1
% 3.66/1.02  --bmc1_symbol_reachability              true
% 3.66/1.02  --bmc1_property_lemmas                  false
% 3.66/1.02  --bmc1_k_induction                      false
% 3.66/1.02  --bmc1_non_equiv_states                 false
% 3.66/1.02  --bmc1_deadlock                         false
% 3.66/1.02  --bmc1_ucm                              false
% 3.66/1.02  --bmc1_add_unsat_core                   none
% 3.66/1.02  --bmc1_unsat_core_children              false
% 3.66/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.66/1.02  --bmc1_out_stat                         full
% 3.66/1.02  --bmc1_ground_init                      false
% 3.66/1.02  --bmc1_pre_inst_next_state              false
% 3.66/1.02  --bmc1_pre_inst_state                   false
% 3.66/1.02  --bmc1_pre_inst_reach_state             false
% 3.66/1.02  --bmc1_out_unsat_core                   false
% 3.66/1.02  --bmc1_aig_witness_out                  false
% 3.66/1.02  --bmc1_verbose                          false
% 3.66/1.02  --bmc1_dump_clauses_tptp                false
% 3.66/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.66/1.02  --bmc1_dump_file                        -
% 3.66/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.66/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.66/1.02  --bmc1_ucm_extend_mode                  1
% 3.66/1.02  --bmc1_ucm_init_mode                    2
% 3.66/1.02  --bmc1_ucm_cone_mode                    none
% 3.66/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.66/1.02  --bmc1_ucm_relax_model                  4
% 3.66/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.66/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.66/1.02  --bmc1_ucm_layered_model                none
% 3.66/1.02  --bmc1_ucm_max_lemma_size               10
% 3.66/1.02  
% 3.66/1.02  ------ AIG Options
% 3.66/1.02  
% 3.66/1.02  --aig_mode                              false
% 3.66/1.02  
% 3.66/1.02  ------ Instantiation Options
% 3.66/1.02  
% 3.66/1.02  --instantiation_flag                    true
% 3.66/1.02  --inst_sos_flag                         false
% 3.66/1.02  --inst_sos_phase                        true
% 3.66/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.66/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.66/1.02  --inst_lit_sel_side                     none
% 3.66/1.02  --inst_solver_per_active                1400
% 3.66/1.02  --inst_solver_calls_frac                1.
% 3.66/1.02  --inst_passive_queue_type               priority_queues
% 3.66/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.66/1.02  --inst_passive_queues_freq              [25;2]
% 3.66/1.02  --inst_dismatching                      true
% 3.66/1.02  --inst_eager_unprocessed_to_passive     true
% 3.66/1.02  --inst_prop_sim_given                   true
% 3.66/1.02  --inst_prop_sim_new                     false
% 3.66/1.02  --inst_subs_new                         false
% 3.66/1.02  --inst_eq_res_simp                      false
% 3.66/1.02  --inst_subs_given                       false
% 3.66/1.02  --inst_orphan_elimination               true
% 3.66/1.02  --inst_learning_loop_flag               true
% 3.66/1.02  --inst_learning_start                   3000
% 3.66/1.02  --inst_learning_factor                  2
% 3.66/1.02  --inst_start_prop_sim_after_learn       3
% 3.66/1.02  --inst_sel_renew                        solver
% 3.66/1.02  --inst_lit_activity_flag                true
% 3.66/1.02  --inst_restr_to_given                   false
% 3.66/1.02  --inst_activity_threshold               500
% 3.66/1.02  --inst_out_proof                        true
% 3.66/1.02  
% 3.66/1.02  ------ Resolution Options
% 3.66/1.02  
% 3.66/1.02  --resolution_flag                       false
% 3.66/1.02  --res_lit_sel                           adaptive
% 3.66/1.02  --res_lit_sel_side                      none
% 3.66/1.02  --res_ordering                          kbo
% 3.66/1.02  --res_to_prop_solver                    active
% 3.66/1.02  --res_prop_simpl_new                    false
% 3.66/1.02  --res_prop_simpl_given                  true
% 3.66/1.02  --res_passive_queue_type                priority_queues
% 3.66/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.66/1.02  --res_passive_queues_freq               [15;5]
% 3.66/1.02  --res_forward_subs                      full
% 3.66/1.02  --res_backward_subs                     full
% 3.66/1.02  --res_forward_subs_resolution           true
% 3.66/1.02  --res_backward_subs_resolution          true
% 3.66/1.02  --res_orphan_elimination                true
% 3.66/1.02  --res_time_limit                        2.
% 3.66/1.02  --res_out_proof                         true
% 3.66/1.02  
% 3.66/1.02  ------ Superposition Options
% 3.66/1.02  
% 3.66/1.02  --superposition_flag                    true
% 3.66/1.02  --sup_passive_queue_type                priority_queues
% 3.66/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.66/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.66/1.02  --demod_completeness_check              fast
% 3.66/1.03  --demod_use_ground                      true
% 3.66/1.03  --sup_to_prop_solver                    passive
% 3.66/1.03  --sup_prop_simpl_new                    true
% 3.66/1.03  --sup_prop_simpl_given                  true
% 3.66/1.03  --sup_fun_splitting                     false
% 3.66/1.03  --sup_smt_interval                      50000
% 3.66/1.03  
% 3.66/1.03  ------ Superposition Simplification Setup
% 3.66/1.03  
% 3.66/1.03  --sup_indices_passive                   []
% 3.66/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.66/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.66/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.66/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 3.66/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.66/1.03  --sup_full_bw                           [BwDemod]
% 3.66/1.03  --sup_immed_triv                        [TrivRules]
% 3.66/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.66/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.66/1.03  --sup_immed_bw_main                     []
% 3.66/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.66/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 3.66/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.66/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.66/1.03  
% 3.66/1.03  ------ Combination Options
% 3.66/1.03  
% 3.66/1.03  --comb_res_mult                         3
% 3.66/1.03  --comb_sup_mult                         2
% 3.66/1.03  --comb_inst_mult                        10
% 3.66/1.03  
% 3.66/1.03  ------ Debug Options
% 3.66/1.03  
% 3.66/1.03  --dbg_backtrace                         false
% 3.66/1.03  --dbg_dump_prop_clauses                 false
% 3.66/1.03  --dbg_dump_prop_clauses_file            -
% 3.66/1.03  --dbg_out_stat                          false
% 3.66/1.03  
% 3.66/1.03  
% 3.66/1.03  
% 3.66/1.03  
% 3.66/1.03  ------ Proving...
% 3.66/1.03  
% 3.66/1.03  
% 3.66/1.03  % SZS status Theorem for theBenchmark.p
% 3.66/1.03  
% 3.66/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 3.66/1.03  
% 3.66/1.03  fof(f15,conjecture,(
% 3.66/1.03    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 3.66/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.66/1.03  
% 3.66/1.03  fof(f16,negated_conjecture,(
% 3.66/1.03    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 3.66/1.03    inference(negated_conjecture,[],[f15])).
% 3.66/1.03  
% 3.66/1.03  fof(f38,plain,(
% 3.66/1.03    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 3.66/1.03    inference(ennf_transformation,[],[f16])).
% 3.66/1.03  
% 3.66/1.03  fof(f39,plain,(
% 3.66/1.03    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 3.66/1.03    inference(flattening,[],[f38])).
% 3.66/1.03  
% 3.66/1.03  fof(f54,plain,(
% 3.66/1.03    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),sK9) != k7_partfun1(X0,X4,k1_funct_1(X3,sK9)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(sK9,X1))) )),
% 3.66/1.03    introduced(choice_axiom,[])).
% 3.66/1.03  
% 3.66/1.03  fof(f53,plain,(
% 3.66/1.03    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,sK8),X5) != k7_partfun1(X0,sK8,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,sK8)) & m1_subset_1(X5,X1)) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(sK8))) )),
% 3.66/1.03    introduced(choice_axiom,[])).
% 3.66/1.03  
% 3.66/1.03  fof(f52,plain,(
% 3.66/1.03    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,sK7,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(sK7,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,sK7),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK7,X1,X2) & v1_funct_1(sK7))) )),
% 3.66/1.03    introduced(choice_axiom,[])).
% 3.66/1.03  
% 3.66/1.03  fof(f51,plain,(
% 3.66/1.03    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK5,sK6,sK4,X3,X4),X5) != k7_partfun1(sK4,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != sK5 & r1_tarski(k2_relset_1(sK5,sK6,X3),k1_relset_1(sK6,sK4,X4)) & m1_subset_1(X5,sK5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(X3,sK5,sK6) & v1_funct_1(X3)) & ~v1_xboole_0(sK6))),
% 3.66/1.03    introduced(choice_axiom,[])).
% 3.66/1.03  
% 3.66/1.03  fof(f55,plain,(
% 3.66/1.03    (((k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),sK9) != k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) & k1_xboole_0 != sK5 & r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8)) & m1_subset_1(sK9,sK5)) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) & v1_funct_1(sK8)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(sK7,sK5,sK6) & v1_funct_1(sK7)) & ~v1_xboole_0(sK6)),
% 3.66/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8,sK9])],[f39,f54,f53,f52,f51])).
% 3.66/1.03  
% 3.66/1.03  fof(f88,plain,(
% 3.66/1.03    m1_subset_1(sK9,sK5)),
% 3.66/1.03    inference(cnf_transformation,[],[f55])).
% 3.66/1.03  
% 3.66/1.03  fof(f4,axiom,(
% 3.66/1.03    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.66/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.66/1.03  
% 3.66/1.03  fof(f20,plain,(
% 3.66/1.03    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.66/1.03    inference(ennf_transformation,[],[f4])).
% 3.66/1.03  
% 3.66/1.03  fof(f21,plain,(
% 3.66/1.03    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.66/1.03    inference(flattening,[],[f20])).
% 3.66/1.03  
% 3.66/1.03  fof(f61,plain,(
% 3.66/1.03    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 3.66/1.03    inference(cnf_transformation,[],[f21])).
% 3.66/1.03  
% 3.66/1.03  fof(f90,plain,(
% 3.66/1.03    k1_xboole_0 != sK5),
% 3.66/1.03    inference(cnf_transformation,[],[f55])).
% 3.66/1.03  
% 3.66/1.03  fof(f2,axiom,(
% 3.66/1.03    v1_xboole_0(k1_xboole_0)),
% 3.66/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.66/1.03  
% 3.66/1.03  fof(f59,plain,(
% 3.66/1.03    v1_xboole_0(k1_xboole_0)),
% 3.66/1.03    inference(cnf_transformation,[],[f2])).
% 3.66/1.03  
% 3.66/1.03  fof(f3,axiom,(
% 3.66/1.03    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 3.66/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.66/1.03  
% 3.66/1.03  fof(f19,plain,(
% 3.66/1.03    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 3.66/1.03    inference(ennf_transformation,[],[f3])).
% 3.66/1.03  
% 3.66/1.03  fof(f60,plain,(
% 3.66/1.03    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 3.66/1.03    inference(cnf_transformation,[],[f19])).
% 3.66/1.03  
% 3.66/1.03  fof(f85,plain,(
% 3.66/1.03    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))),
% 3.66/1.03    inference(cnf_transformation,[],[f55])).
% 3.66/1.03  
% 3.66/1.03  fof(f12,axiom,(
% 3.66/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.66/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.66/1.03  
% 3.66/1.03  fof(f32,plain,(
% 3.66/1.03    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.66/1.03    inference(ennf_transformation,[],[f12])).
% 3.66/1.03  
% 3.66/1.03  fof(f33,plain,(
% 3.66/1.03    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.66/1.03    inference(flattening,[],[f32])).
% 3.66/1.03  
% 3.66/1.03  fof(f50,plain,(
% 3.66/1.03    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.66/1.03    inference(nnf_transformation,[],[f33])).
% 3.66/1.03  
% 3.66/1.03  fof(f74,plain,(
% 3.66/1.03    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.66/1.03    inference(cnf_transformation,[],[f50])).
% 3.66/1.03  
% 3.66/1.03  fof(f9,axiom,(
% 3.66/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.66/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.66/1.03  
% 3.66/1.03  fof(f28,plain,(
% 3.66/1.03    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.66/1.03    inference(ennf_transformation,[],[f9])).
% 3.66/1.03  
% 3.66/1.03  fof(f71,plain,(
% 3.66/1.03    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.66/1.03    inference(cnf_transformation,[],[f28])).
% 3.66/1.03  
% 3.66/1.03  fof(f82,plain,(
% 3.66/1.03    ~v1_xboole_0(sK6)),
% 3.66/1.03    inference(cnf_transformation,[],[f55])).
% 3.66/1.03  
% 3.66/1.03  fof(f84,plain,(
% 3.66/1.03    v1_funct_2(sK7,sK5,sK6)),
% 3.66/1.03    inference(cnf_transformation,[],[f55])).
% 3.66/1.03  
% 3.66/1.03  fof(f5,axiom,(
% 3.66/1.03    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 3.66/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.66/1.03  
% 3.66/1.03  fof(f22,plain,(
% 3.66/1.03    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.66/1.03    inference(ennf_transformation,[],[f5])).
% 3.66/1.03  
% 3.66/1.03  fof(f23,plain,(
% 3.66/1.03    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.66/1.03    inference(flattening,[],[f22])).
% 3.66/1.03  
% 3.66/1.03  fof(f44,plain,(
% 3.66/1.03    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.66/1.03    inference(nnf_transformation,[],[f23])).
% 3.66/1.03  
% 3.66/1.03  fof(f45,plain,(
% 3.66/1.03    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.66/1.03    inference(rectify,[],[f44])).
% 3.66/1.03  
% 3.66/1.03  fof(f48,plain,(
% 3.66/1.03    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X5)) = X5 & r2_hidden(sK3(X0,X5),k1_relat_1(X0))))),
% 3.66/1.03    introduced(choice_axiom,[])).
% 3.66/1.03  
% 3.66/1.03  fof(f47,plain,(
% 3.66/1.03    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK2(X0,X1)) = X2 & r2_hidden(sK2(X0,X1),k1_relat_1(X0))))) )),
% 3.66/1.03    introduced(choice_axiom,[])).
% 3.66/1.03  
% 3.66/1.03  fof(f46,plain,(
% 3.66/1.03    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK1(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK1(X0,X1),X1))))),
% 3.66/1.03    introduced(choice_axiom,[])).
% 3.66/1.03  
% 3.66/1.03  fof(f49,plain,(
% 3.66/1.03    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1),X1)) & ((k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK3(X0,X5)) = X5 & r2_hidden(sK3(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.66/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f45,f48,f47,f46])).
% 3.66/1.03  
% 3.66/1.03  fof(f64,plain,(
% 3.66/1.03    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.66/1.03    inference(cnf_transformation,[],[f49])).
% 3.66/1.03  
% 3.66/1.03  fof(f92,plain,(
% 3.66/1.03    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.66/1.03    inference(equality_resolution,[],[f64])).
% 3.66/1.03  
% 3.66/1.03  fof(f93,plain,(
% 3.66/1.03    ( ! [X6,X0] : (r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~r2_hidden(X6,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.66/1.03    inference(equality_resolution,[],[f92])).
% 3.66/1.03  
% 3.66/1.03  fof(f63,plain,(
% 3.66/1.03    ( ! [X0,X5,X1] : (k1_funct_1(X0,sK3(X0,X5)) = X5 | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.66/1.03    inference(cnf_transformation,[],[f49])).
% 3.66/1.03  
% 3.66/1.03  fof(f94,plain,(
% 3.66/1.03    ( ! [X0,X5] : (k1_funct_1(X0,sK3(X0,X5)) = X5 | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.66/1.03    inference(equality_resolution,[],[f63])).
% 3.66/1.03  
% 3.66/1.03  fof(f83,plain,(
% 3.66/1.03    v1_funct_1(sK7)),
% 3.66/1.03    inference(cnf_transformation,[],[f55])).
% 3.66/1.03  
% 3.66/1.03  fof(f7,axiom,(
% 3.66/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.66/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.66/1.03  
% 3.66/1.03  fof(f26,plain,(
% 3.66/1.03    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.66/1.03    inference(ennf_transformation,[],[f7])).
% 3.66/1.03  
% 3.66/1.03  fof(f69,plain,(
% 3.66/1.03    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.66/1.03    inference(cnf_transformation,[],[f26])).
% 3.66/1.03  
% 3.66/1.03  fof(f1,axiom,(
% 3.66/1.03    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.66/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.66/1.03  
% 3.66/1.03  fof(f18,plain,(
% 3.66/1.03    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.66/1.03    inference(ennf_transformation,[],[f1])).
% 3.66/1.03  
% 3.66/1.03  fof(f40,plain,(
% 3.66/1.03    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.66/1.03    inference(nnf_transformation,[],[f18])).
% 3.66/1.03  
% 3.66/1.03  fof(f41,plain,(
% 3.66/1.03    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.66/1.03    inference(rectify,[],[f40])).
% 3.66/1.03  
% 3.66/1.03  fof(f42,plain,(
% 3.66/1.03    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.66/1.03    introduced(choice_axiom,[])).
% 3.66/1.03  
% 3.66/1.03  fof(f43,plain,(
% 3.66/1.03    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.66/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f41,f42])).
% 3.66/1.03  
% 3.66/1.03  fof(f56,plain,(
% 3.66/1.03    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.66/1.03    inference(cnf_transformation,[],[f43])).
% 3.66/1.03  
% 3.66/1.03  fof(f87,plain,(
% 3.66/1.03    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4)))),
% 3.66/1.03    inference(cnf_transformation,[],[f55])).
% 3.66/1.03  
% 3.66/1.03  fof(f8,axiom,(
% 3.66/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.66/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.66/1.03  
% 3.66/1.03  fof(f17,plain,(
% 3.66/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.66/1.03    inference(pure_predicate_removal,[],[f8])).
% 3.66/1.03  
% 3.66/1.03  fof(f27,plain,(
% 3.66/1.03    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.66/1.03    inference(ennf_transformation,[],[f17])).
% 3.66/1.03  
% 3.66/1.03  fof(f70,plain,(
% 3.66/1.03    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.66/1.03    inference(cnf_transformation,[],[f27])).
% 3.66/1.03  
% 3.66/1.03  fof(f13,axiom,(
% 3.66/1.03    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)))),
% 3.66/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.66/1.03  
% 3.66/1.03  fof(f34,plain,(
% 3.66/1.03    ! [X0,X1] : (! [X2] : (k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.66/1.03    inference(ennf_transformation,[],[f13])).
% 3.66/1.03  
% 3.66/1.03  fof(f35,plain,(
% 3.66/1.03    ! [X0,X1] : (! [X2] : (k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.66/1.03    inference(flattening,[],[f34])).
% 3.66/1.03  
% 3.66/1.03  fof(f80,plain,(
% 3.66/1.03    ( ! [X2,X0,X1] : (k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.66/1.03    inference(cnf_transformation,[],[f35])).
% 3.66/1.03  
% 3.66/1.03  fof(f86,plain,(
% 3.66/1.03    v1_funct_1(sK8)),
% 3.66/1.03    inference(cnf_transformation,[],[f55])).
% 3.66/1.03  
% 3.66/1.03  fof(f6,axiom,(
% 3.66/1.03    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0))))),
% 3.66/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.66/1.03  
% 3.66/1.03  fof(f24,plain,(
% 3.66/1.03    ! [X0,X1] : (! [X2] : ((k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.66/1.03    inference(ennf_transformation,[],[f6])).
% 3.66/1.03  
% 3.66/1.03  fof(f25,plain,(
% 3.66/1.03    ! [X0,X1] : (! [X2] : (k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.66/1.03    inference(flattening,[],[f24])).
% 3.66/1.03  
% 3.66/1.03  fof(f68,plain,(
% 3.66/1.03    ( ! [X2,X0,X1] : (k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.66/1.03    inference(cnf_transformation,[],[f25])).
% 3.66/1.03  
% 3.66/1.03  fof(f10,axiom,(
% 3.66/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.66/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.66/1.03  
% 3.66/1.03  fof(f29,plain,(
% 3.66/1.03    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.66/1.03    inference(ennf_transformation,[],[f10])).
% 3.66/1.03  
% 3.66/1.03  fof(f72,plain,(
% 3.66/1.03    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.66/1.03    inference(cnf_transformation,[],[f29])).
% 3.66/1.03  
% 3.66/1.03  fof(f11,axiom,(
% 3.66/1.03    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X4)) => (r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) => (k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1))))),
% 3.66/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.66/1.03  
% 3.66/1.03  fof(f30,plain,(
% 3.66/1.03    ! [X0,X1,X2,X3] : (! [X4] : (((k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 3.66/1.03    inference(ennf_transformation,[],[f11])).
% 3.66/1.03  
% 3.66/1.03  fof(f31,plain,(
% 3.66/1.03    ! [X0,X1,X2,X3] : (! [X4] : (k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.66/1.03    inference(flattening,[],[f30])).
% 3.66/1.03  
% 3.66/1.03  fof(f73,plain,(
% 3.66/1.03    ( ! [X4,X2,X0,X3,X1] : (k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.66/1.03    inference(cnf_transformation,[],[f31])).
% 3.66/1.03  
% 3.66/1.03  fof(f14,axiom,(
% 3.66/1.03    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 3.66/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.66/1.03  
% 3.66/1.03  fof(f36,plain,(
% 3.66/1.03    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.66/1.03    inference(ennf_transformation,[],[f14])).
% 3.66/1.03  
% 3.66/1.03  fof(f37,plain,(
% 3.66/1.03    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.66/1.03    inference(flattening,[],[f36])).
% 3.66/1.03  
% 3.66/1.03  fof(f81,plain,(
% 3.66/1.03    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.66/1.03    inference(cnf_transformation,[],[f37])).
% 3.66/1.03  
% 3.66/1.03  fof(f89,plain,(
% 3.66/1.03    r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8))),
% 3.66/1.03    inference(cnf_transformation,[],[f55])).
% 3.66/1.03  
% 3.66/1.03  fof(f91,plain,(
% 3.66/1.03    k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),sK9) != k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9))),
% 3.66/1.03    inference(cnf_transformation,[],[f55])).
% 3.66/1.03  
% 3.66/1.03  cnf(c_29,negated_conjecture,
% 3.66/1.03      ( m1_subset_1(sK9,sK5) ),
% 3.66/1.03      inference(cnf_transformation,[],[f88]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_1869,plain,
% 3.66/1.03      ( m1_subset_1(sK9,sK5) = iProver_top ),
% 3.66/1.03      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_5,plain,
% 3.66/1.03      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.66/1.03      inference(cnf_transformation,[],[f61]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_1889,plain,
% 3.66/1.03      ( m1_subset_1(X0,X1) != iProver_top
% 3.66/1.03      | r2_hidden(X0,X1) = iProver_top
% 3.66/1.03      | v1_xboole_0(X1) = iProver_top ),
% 3.66/1.03      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_3067,plain,
% 3.66/1.03      ( r2_hidden(sK9,sK5) = iProver_top
% 3.66/1.03      | v1_xboole_0(sK5) = iProver_top ),
% 3.66/1.03      inference(superposition,[status(thm)],[c_1869,c_1889]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_42,plain,
% 3.66/1.03      ( m1_subset_1(sK9,sK5) = iProver_top ),
% 3.66/1.03      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_27,negated_conjecture,
% 3.66/1.03      ( k1_xboole_0 != sK5 ),
% 3.66/1.03      inference(cnf_transformation,[],[f90]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_3,plain,
% 3.66/1.03      ( v1_xboole_0(k1_xboole_0) ),
% 3.66/1.03      inference(cnf_transformation,[],[f59]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_110,plain,
% 3.66/1.03      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.66/1.03      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_4,plain,
% 3.66/1.03      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X0 = X1 ),
% 3.66/1.03      inference(cnf_transformation,[],[f60]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_2179,plain,
% 3.66/1.03      ( ~ v1_xboole_0(sK5)
% 3.66/1.03      | ~ v1_xboole_0(k1_xboole_0)
% 3.66/1.03      | k1_xboole_0 = sK5 ),
% 3.66/1.03      inference(instantiation,[status(thm)],[c_4]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_2180,plain,
% 3.66/1.03      ( k1_xboole_0 = sK5
% 3.66/1.03      | v1_xboole_0(sK5) != iProver_top
% 3.66/1.03      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.66/1.03      inference(predicate_to_equality,[status(thm)],[c_2179]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_2384,plain,
% 3.66/1.03      ( ~ m1_subset_1(X0,sK5) | r2_hidden(X0,sK5) | v1_xboole_0(sK5) ),
% 3.66/1.03      inference(instantiation,[status(thm)],[c_5]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_2665,plain,
% 3.66/1.03      ( ~ m1_subset_1(sK9,sK5) | r2_hidden(sK9,sK5) | v1_xboole_0(sK5) ),
% 3.66/1.03      inference(instantiation,[status(thm)],[c_2384]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_2666,plain,
% 3.66/1.03      ( m1_subset_1(sK9,sK5) != iProver_top
% 3.66/1.03      | r2_hidden(sK9,sK5) = iProver_top
% 3.66/1.03      | v1_xboole_0(sK5) = iProver_top ),
% 3.66/1.03      inference(predicate_to_equality,[status(thm)],[c_2665]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_4225,plain,
% 3.66/1.03      ( r2_hidden(sK9,sK5) = iProver_top ),
% 3.66/1.03      inference(global_propositional_subsumption,
% 3.66/1.03                [status(thm)],
% 3.66/1.03                [c_3067,c_42,c_27,c_110,c_2180,c_2666]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_32,negated_conjecture,
% 3.66/1.03      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
% 3.66/1.03      inference(cnf_transformation,[],[f85]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_1866,plain,
% 3.66/1.03      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
% 3.66/1.03      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_23,plain,
% 3.66/1.03      ( ~ v1_funct_2(X0,X1,X2)
% 3.66/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.66/1.03      | k1_relset_1(X1,X2,X0) = X1
% 3.66/1.03      | k1_xboole_0 = X2 ),
% 3.66/1.03      inference(cnf_transformation,[],[f74]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_1872,plain,
% 3.66/1.03      ( k1_relset_1(X0,X1,X2) = X0
% 3.66/1.03      | k1_xboole_0 = X1
% 3.66/1.03      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.66/1.03      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.66/1.03      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_3882,plain,
% 3.66/1.03      ( k1_relset_1(sK5,sK6,sK7) = sK5
% 3.66/1.03      | sK6 = k1_xboole_0
% 3.66/1.03      | v1_funct_2(sK7,sK5,sK6) != iProver_top ),
% 3.66/1.03      inference(superposition,[status(thm)],[c_1866,c_1872]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_15,plain,
% 3.66/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.66/1.03      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.66/1.03      inference(cnf_transformation,[],[f71]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_1880,plain,
% 3.66/1.03      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.66/1.03      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.66/1.03      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_3058,plain,
% 3.66/1.03      ( k1_relset_1(sK5,sK6,sK7) = k1_relat_1(sK7) ),
% 3.66/1.03      inference(superposition,[status(thm)],[c_1866,c_1880]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_3886,plain,
% 3.66/1.03      ( k1_relat_1(sK7) = sK5
% 3.66/1.03      | sK6 = k1_xboole_0
% 3.66/1.03      | v1_funct_2(sK7,sK5,sK6) != iProver_top ),
% 3.66/1.03      inference(demodulation,[status(thm)],[c_3882,c_3058]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_35,negated_conjecture,
% 3.66/1.03      ( ~ v1_xboole_0(sK6) ),
% 3.66/1.03      inference(cnf_transformation,[],[f82]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_33,negated_conjecture,
% 3.66/1.03      ( v1_funct_2(sK7,sK5,sK6) ),
% 3.66/1.03      inference(cnf_transformation,[],[f84]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_38,plain,
% 3.66/1.03      ( v1_funct_2(sK7,sK5,sK6) = iProver_top ),
% 3.66/1.03      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_1286,plain,
% 3.66/1.03      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 3.66/1.03      theory(equality) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_2188,plain,
% 3.66/1.03      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK6) | sK6 != X0 ),
% 3.66/1.03      inference(instantiation,[status(thm)],[c_1286]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_2190,plain,
% 3.66/1.03      ( v1_xboole_0(sK6)
% 3.66/1.03      | ~ v1_xboole_0(k1_xboole_0)
% 3.66/1.03      | sK6 != k1_xboole_0 ),
% 3.66/1.03      inference(instantiation,[status(thm)],[c_2188]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_4282,plain,
% 3.66/1.03      ( k1_relat_1(sK7) = sK5 ),
% 3.66/1.03      inference(global_propositional_subsumption,
% 3.66/1.03                [status(thm)],
% 3.66/1.03                [c_3886,c_35,c_38,c_3,c_2190]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_9,plain,
% 3.66/1.03      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.66/1.03      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 3.66/1.03      | ~ v1_relat_1(X1)
% 3.66/1.03      | ~ v1_funct_1(X1) ),
% 3.66/1.03      inference(cnf_transformation,[],[f93]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_1885,plain,
% 3.66/1.03      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 3.66/1.03      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
% 3.66/1.03      | v1_relat_1(X1) != iProver_top
% 3.66/1.03      | v1_funct_1(X1) != iProver_top ),
% 3.66/1.03      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_10,plain,
% 3.66/1.03      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 3.66/1.03      | ~ v1_relat_1(X1)
% 3.66/1.03      | ~ v1_funct_1(X1)
% 3.66/1.03      | k1_funct_1(X1,sK3(X1,X0)) = X0 ),
% 3.66/1.03      inference(cnf_transformation,[],[f94]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_1884,plain,
% 3.66/1.03      ( k1_funct_1(X0,sK3(X0,X1)) = X1
% 3.66/1.03      | r2_hidden(X1,k2_relat_1(X0)) != iProver_top
% 3.66/1.03      | v1_relat_1(X0) != iProver_top
% 3.66/1.03      | v1_funct_1(X0) != iProver_top ),
% 3.66/1.03      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_4655,plain,
% 3.66/1.03      ( k1_funct_1(X0,sK3(X0,k1_funct_1(X0,X1))) = k1_funct_1(X0,X1)
% 3.66/1.03      | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
% 3.66/1.03      | v1_relat_1(X0) != iProver_top
% 3.66/1.03      | v1_funct_1(X0) != iProver_top ),
% 3.66/1.03      inference(superposition,[status(thm)],[c_1885,c_1884]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_8100,plain,
% 3.66/1.03      ( k1_funct_1(sK7,sK3(sK7,k1_funct_1(sK7,X0))) = k1_funct_1(sK7,X0)
% 3.66/1.03      | r2_hidden(X0,sK5) != iProver_top
% 3.66/1.03      | v1_relat_1(sK7) != iProver_top
% 3.66/1.03      | v1_funct_1(sK7) != iProver_top ),
% 3.66/1.03      inference(superposition,[status(thm)],[c_4282,c_4655]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_34,negated_conjecture,
% 3.66/1.03      ( v1_funct_1(sK7) ),
% 3.66/1.03      inference(cnf_transformation,[],[f83]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_37,plain,
% 3.66/1.03      ( v1_funct_1(sK7) = iProver_top ),
% 3.66/1.03      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_39,plain,
% 3.66/1.03      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
% 3.66/1.03      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_13,plain,
% 3.66/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.66/1.03      | v1_relat_1(X0) ),
% 3.66/1.03      inference(cnf_transformation,[],[f69]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_2185,plain,
% 3.66/1.03      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 3.66/1.03      | v1_relat_1(sK7) ),
% 3.66/1.03      inference(instantiation,[status(thm)],[c_13]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_2186,plain,
% 3.66/1.03      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
% 3.66/1.03      | v1_relat_1(sK7) = iProver_top ),
% 3.66/1.03      inference(predicate_to_equality,[status(thm)],[c_2185]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_8451,plain,
% 3.66/1.03      ( k1_funct_1(sK7,sK3(sK7,k1_funct_1(sK7,X0))) = k1_funct_1(sK7,X0)
% 3.66/1.03      | r2_hidden(X0,sK5) != iProver_top ),
% 3.66/1.03      inference(global_propositional_subsumption,
% 3.66/1.03                [status(thm)],
% 3.66/1.03                [c_8100,c_37,c_39,c_2186]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_8463,plain,
% 3.66/1.03      ( k1_funct_1(sK7,sK3(sK7,k1_funct_1(sK7,sK9))) = k1_funct_1(sK7,sK9) ),
% 3.66/1.03      inference(superposition,[status(thm)],[c_4225,c_8451]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_8576,plain,
% 3.66/1.03      ( r2_hidden(sK3(sK7,k1_funct_1(sK7,sK9)),k1_relat_1(sK7)) != iProver_top
% 3.66/1.03      | r2_hidden(k1_funct_1(sK7,sK9),k2_relat_1(sK7)) = iProver_top
% 3.66/1.03      | v1_relat_1(sK7) != iProver_top
% 3.66/1.03      | v1_funct_1(sK7) != iProver_top ),
% 3.66/1.03      inference(superposition,[status(thm)],[c_8463,c_1885]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_8581,plain,
% 3.66/1.03      ( r2_hidden(sK3(sK7,k1_funct_1(sK7,sK9)),sK5) != iProver_top
% 3.66/1.03      | r2_hidden(k1_funct_1(sK7,sK9),k2_relat_1(sK7)) = iProver_top
% 3.66/1.03      | v1_relat_1(sK7) != iProver_top
% 3.66/1.03      | v1_funct_1(sK7) != iProver_top ),
% 3.66/1.03      inference(light_normalisation,[status(thm)],[c_8576,c_4282]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_1282,plain,( X0 = X0 ),theory(equality) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_2501,plain,
% 3.66/1.03      ( sK9 = sK9 ),
% 3.66/1.03      inference(instantiation,[status(thm)],[c_1282]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_1285,plain,
% 3.66/1.03      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.66/1.03      theory(equality) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_2928,plain,
% 3.66/1.03      ( r2_hidden(X0,X1) | ~ r2_hidden(sK9,sK5) | X0 != sK9 | X1 != sK5 ),
% 3.66/1.03      inference(instantiation,[status(thm)],[c_1285]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_3813,plain,
% 3.66/1.03      ( r2_hidden(sK9,X0)
% 3.66/1.03      | ~ r2_hidden(sK9,sK5)
% 3.66/1.03      | X0 != sK5
% 3.66/1.03      | sK9 != sK9 ),
% 3.66/1.03      inference(instantiation,[status(thm)],[c_2928]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_6102,plain,
% 3.66/1.03      ( r2_hidden(sK9,k1_relat_1(sK7))
% 3.66/1.03      | ~ r2_hidden(sK9,sK5)
% 3.66/1.03      | k1_relat_1(sK7) != sK5
% 3.66/1.03      | sK9 != sK9 ),
% 3.66/1.03      inference(instantiation,[status(thm)],[c_3813]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_6107,plain,
% 3.66/1.03      ( k1_relat_1(sK7) != sK5
% 3.66/1.03      | sK9 != sK9
% 3.66/1.03      | r2_hidden(sK9,k1_relat_1(sK7)) = iProver_top
% 3.66/1.03      | r2_hidden(sK9,sK5) != iProver_top ),
% 3.66/1.03      inference(predicate_to_equality,[status(thm)],[c_6102]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_2363,plain,
% 3.66/1.03      ( ~ r2_hidden(X0,k1_relat_1(sK7))
% 3.66/1.03      | r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7))
% 3.66/1.03      | ~ v1_relat_1(sK7)
% 3.66/1.03      | ~ v1_funct_1(sK7) ),
% 3.66/1.03      inference(instantiation,[status(thm)],[c_9]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_6106,plain,
% 3.66/1.03      ( r2_hidden(k1_funct_1(sK7,sK9),k2_relat_1(sK7))
% 3.66/1.03      | ~ r2_hidden(sK9,k1_relat_1(sK7))
% 3.66/1.03      | ~ v1_relat_1(sK7)
% 3.66/1.03      | ~ v1_funct_1(sK7) ),
% 3.66/1.03      inference(instantiation,[status(thm)],[c_2363]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_6109,plain,
% 3.66/1.03      ( r2_hidden(k1_funct_1(sK7,sK9),k2_relat_1(sK7)) = iProver_top
% 3.66/1.03      | r2_hidden(sK9,k1_relat_1(sK7)) != iProver_top
% 3.66/1.03      | v1_relat_1(sK7) != iProver_top
% 3.66/1.03      | v1_funct_1(sK7) != iProver_top ),
% 3.66/1.03      inference(predicate_to_equality,[status(thm)],[c_6106]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_8636,plain,
% 3.66/1.03      ( r2_hidden(k1_funct_1(sK7,sK9),k2_relat_1(sK7)) = iProver_top ),
% 3.66/1.03      inference(global_propositional_subsumption,
% 3.66/1.03                [status(thm)],
% 3.66/1.03                [c_8581,c_35,c_37,c_38,c_39,c_42,c_27,c_3,c_110,c_2180,
% 3.66/1.03                 c_2186,c_2190,c_2501,c_2666,c_3886,c_6107,c_6109]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_2,plain,
% 3.66/1.03      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 3.66/1.03      inference(cnf_transformation,[],[f56]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_1892,plain,
% 3.66/1.03      ( r2_hidden(X0,X1) != iProver_top
% 3.66/1.03      | r2_hidden(X0,X2) = iProver_top
% 3.66/1.03      | r1_tarski(X1,X2) != iProver_top ),
% 3.66/1.03      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_8641,plain,
% 3.66/1.03      ( r2_hidden(k1_funct_1(sK7,sK9),X0) = iProver_top
% 3.66/1.03      | r1_tarski(k2_relat_1(sK7),X0) != iProver_top ),
% 3.66/1.03      inference(superposition,[status(thm)],[c_8636,c_1892]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_30,negated_conjecture,
% 3.66/1.03      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) ),
% 3.66/1.03      inference(cnf_transformation,[],[f87]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_1868,plain,
% 3.66/1.03      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) = iProver_top ),
% 3.66/1.03      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_14,plain,
% 3.66/1.03      ( v5_relat_1(X0,X1)
% 3.66/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.66/1.03      inference(cnf_transformation,[],[f70]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_24,plain,
% 3.66/1.03      ( ~ v5_relat_1(X0,X1)
% 3.66/1.03      | ~ r2_hidden(X2,k1_relat_1(X0))
% 3.66/1.03      | ~ v1_relat_1(X0)
% 3.66/1.03      | ~ v1_funct_1(X0)
% 3.66/1.03      | k7_partfun1(X1,X0,X2) = k1_funct_1(X0,X2) ),
% 3.66/1.03      inference(cnf_transformation,[],[f80]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_378,plain,
% 3.66/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.66/1.03      | ~ r2_hidden(X3,k1_relat_1(X0))
% 3.66/1.03      | ~ v1_relat_1(X0)
% 3.66/1.03      | ~ v1_funct_1(X0)
% 3.66/1.03      | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
% 3.66/1.03      inference(resolution,[status(thm)],[c_14,c_24]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_382,plain,
% 3.66/1.03      ( ~ r2_hidden(X3,k1_relat_1(X0))
% 3.66/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.66/1.03      | ~ v1_funct_1(X0)
% 3.66/1.03      | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
% 3.66/1.03      inference(global_propositional_subsumption,
% 3.66/1.03                [status(thm)],
% 3.66/1.03                [c_378,c_13]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_383,plain,
% 3.66/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.66/1.03      | ~ r2_hidden(X3,k1_relat_1(X0))
% 3.66/1.03      | ~ v1_funct_1(X0)
% 3.66/1.03      | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
% 3.66/1.03      inference(renaming,[status(thm)],[c_382]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_1862,plain,
% 3.66/1.03      ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
% 3.66/1.03      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) != iProver_top
% 3.66/1.03      | r2_hidden(X2,k1_relat_1(X1)) != iProver_top
% 3.66/1.03      | v1_funct_1(X1) != iProver_top ),
% 3.66/1.03      inference(predicate_to_equality,[status(thm)],[c_383]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_2396,plain,
% 3.66/1.03      ( k7_partfun1(sK4,sK8,X0) = k1_funct_1(sK8,X0)
% 3.66/1.03      | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
% 3.66/1.03      | v1_funct_1(sK8) != iProver_top ),
% 3.66/1.03      inference(superposition,[status(thm)],[c_1868,c_1862]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_31,negated_conjecture,
% 3.66/1.03      ( v1_funct_1(sK8) ),
% 3.66/1.03      inference(cnf_transformation,[],[f86]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_40,plain,
% 3.66/1.03      ( v1_funct_1(sK8) = iProver_top ),
% 3.66/1.03      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_2650,plain,
% 3.66/1.03      ( r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
% 3.66/1.03      | k7_partfun1(sK4,sK8,X0) = k1_funct_1(sK8,X0) ),
% 3.66/1.03      inference(global_propositional_subsumption,
% 3.66/1.03                [status(thm)],
% 3.66/1.03                [c_2396,c_40]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_2651,plain,
% 3.66/1.03      ( k7_partfun1(sK4,sK8,X0) = k1_funct_1(sK8,X0)
% 3.66/1.03      | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top ),
% 3.66/1.03      inference(renaming,[status(thm)],[c_2650]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_9042,plain,
% 3.66/1.03      ( k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) = k1_funct_1(sK8,k1_funct_1(sK7,sK9))
% 3.66/1.03      | r1_tarski(k2_relat_1(sK7),k1_relat_1(sK8)) != iProver_top ),
% 3.66/1.03      inference(superposition,[status(thm)],[c_8641,c_2651]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_1881,plain,
% 3.66/1.03      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.66/1.03      | v1_relat_1(X0) = iProver_top ),
% 3.66/1.03      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_2702,plain,
% 3.66/1.03      ( v1_relat_1(sK8) = iProver_top ),
% 3.66/1.03      inference(superposition,[status(thm)],[c_1868,c_1881]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_12,plain,
% 3.66/1.03      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.66/1.03      | ~ v1_relat_1(X1)
% 3.66/1.03      | ~ v1_relat_1(X2)
% 3.66/1.03      | ~ v1_funct_1(X1)
% 3.66/1.03      | ~ v1_funct_1(X2)
% 3.66/1.03      | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ),
% 3.66/1.03      inference(cnf_transformation,[],[f68]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_1882,plain,
% 3.66/1.03      ( k1_funct_1(k5_relat_1(X0,X1),X2) = k1_funct_1(X1,k1_funct_1(X0,X2))
% 3.66/1.03      | r2_hidden(X2,k1_relat_1(X0)) != iProver_top
% 3.66/1.03      | v1_relat_1(X0) != iProver_top
% 3.66/1.03      | v1_relat_1(X1) != iProver_top
% 3.66/1.03      | v1_funct_1(X0) != iProver_top
% 3.66/1.03      | v1_funct_1(X1) != iProver_top ),
% 3.66/1.03      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_5340,plain,
% 3.66/1.03      ( k1_funct_1(X0,k1_funct_1(sK7,X1)) = k1_funct_1(k5_relat_1(sK7,X0),X1)
% 3.66/1.03      | r2_hidden(X1,sK5) != iProver_top
% 3.66/1.03      | v1_relat_1(X0) != iProver_top
% 3.66/1.03      | v1_relat_1(sK7) != iProver_top
% 3.66/1.03      | v1_funct_1(X0) != iProver_top
% 3.66/1.03      | v1_funct_1(sK7) != iProver_top ),
% 3.66/1.03      inference(superposition,[status(thm)],[c_4282,c_1882]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_7389,plain,
% 3.66/1.03      ( v1_funct_1(X0) != iProver_top
% 3.66/1.03      | k1_funct_1(X0,k1_funct_1(sK7,X1)) = k1_funct_1(k5_relat_1(sK7,X0),X1)
% 3.66/1.03      | r2_hidden(X1,sK5) != iProver_top
% 3.66/1.03      | v1_relat_1(X0) != iProver_top ),
% 3.66/1.03      inference(global_propositional_subsumption,
% 3.66/1.03                [status(thm)],
% 3.66/1.03                [c_5340,c_37,c_39,c_2186]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_7390,plain,
% 3.66/1.03      ( k1_funct_1(X0,k1_funct_1(sK7,X1)) = k1_funct_1(k5_relat_1(sK7,X0),X1)
% 3.66/1.03      | r2_hidden(X1,sK5) != iProver_top
% 3.66/1.03      | v1_relat_1(X0) != iProver_top
% 3.66/1.03      | v1_funct_1(X0) != iProver_top ),
% 3.66/1.03      inference(renaming,[status(thm)],[c_7389]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_7403,plain,
% 3.66/1.03      ( k1_funct_1(k5_relat_1(sK7,X0),sK9) = k1_funct_1(X0,k1_funct_1(sK7,sK9))
% 3.66/1.03      | v1_relat_1(X0) != iProver_top
% 3.66/1.03      | v1_funct_1(X0) != iProver_top ),
% 3.66/1.03      inference(superposition,[status(thm)],[c_4225,c_7390]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_7585,plain,
% 3.66/1.03      ( k1_funct_1(sK8,k1_funct_1(sK7,sK9)) = k1_funct_1(k5_relat_1(sK7,sK8),sK9)
% 3.66/1.03      | v1_funct_1(sK8) != iProver_top ),
% 3.66/1.03      inference(superposition,[status(thm)],[c_2702,c_7403]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_7598,plain,
% 3.66/1.03      ( k1_funct_1(sK8,k1_funct_1(sK7,sK9)) = k1_funct_1(k5_relat_1(sK7,sK8),sK9) ),
% 3.66/1.03      inference(global_propositional_subsumption,
% 3.66/1.03                [status(thm)],
% 3.66/1.03                [c_7585,c_40]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_3057,plain,
% 3.66/1.03      ( k1_relset_1(sK6,sK4,sK8) = k1_relat_1(sK8) ),
% 3.66/1.03      inference(superposition,[status(thm)],[c_1868,c_1880]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_16,plain,
% 3.66/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.66/1.03      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.66/1.03      inference(cnf_transformation,[],[f72]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_1879,plain,
% 3.66/1.03      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.66/1.03      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.66/1.03      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_2986,plain,
% 3.66/1.03      ( k2_relset_1(sK5,sK6,sK7) = k2_relat_1(sK7) ),
% 3.66/1.03      inference(superposition,[status(thm)],[c_1866,c_1879]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_17,plain,
% 3.66/1.03      ( ~ v1_funct_2(X0,X1,X2)
% 3.66/1.03      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
% 3.66/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.66/1.03      | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X4,X3))
% 3.66/1.03      | ~ v1_funct_1(X0)
% 3.66/1.03      | ~ v1_funct_1(X3)
% 3.66/1.03      | k1_partfun1(X1,X2,X2,X4,X0,X3) = k8_funct_2(X1,X2,X4,X0,X3)
% 3.66/1.03      | k1_xboole_0 = X2 ),
% 3.66/1.03      inference(cnf_transformation,[],[f73]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_1878,plain,
% 3.66/1.03      ( k1_partfun1(X0,X1,X1,X2,X3,X4) = k8_funct_2(X0,X1,X2,X3,X4)
% 3.66/1.03      | k1_xboole_0 = X1
% 3.66/1.03      | v1_funct_2(X3,X0,X1) != iProver_top
% 3.66/1.03      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.66/1.03      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.66/1.03      | r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) != iProver_top
% 3.66/1.03      | v1_funct_1(X4) != iProver_top
% 3.66/1.03      | v1_funct_1(X3) != iProver_top ),
% 3.66/1.03      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_4982,plain,
% 3.66/1.03      ( k1_partfun1(sK5,sK6,sK6,X0,sK7,X1) = k8_funct_2(sK5,sK6,X0,sK7,X1)
% 3.66/1.03      | sK6 = k1_xboole_0
% 3.66/1.03      | v1_funct_2(sK7,sK5,sK6) != iProver_top
% 3.66/1.03      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK6,X0))) != iProver_top
% 3.66/1.03      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
% 3.66/1.03      | r1_tarski(k2_relat_1(sK7),k1_relset_1(sK6,X0,X1)) != iProver_top
% 3.66/1.03      | v1_funct_1(X1) != iProver_top
% 3.66/1.03      | v1_funct_1(sK7) != iProver_top ),
% 3.66/1.03      inference(superposition,[status(thm)],[c_2986,c_1878]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_5681,plain,
% 3.66/1.03      ( v1_funct_1(X1) != iProver_top
% 3.66/1.03      | r1_tarski(k2_relat_1(sK7),k1_relset_1(sK6,X0,X1)) != iProver_top
% 3.66/1.03      | k1_partfun1(sK5,sK6,sK6,X0,sK7,X1) = k8_funct_2(sK5,sK6,X0,sK7,X1)
% 3.66/1.03      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK6,X0))) != iProver_top ),
% 3.66/1.03      inference(global_propositional_subsumption,
% 3.66/1.03                [status(thm)],
% 3.66/1.03                [c_4982,c_35,c_37,c_38,c_39,c_3,c_2190]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_5682,plain,
% 3.66/1.03      ( k1_partfun1(sK5,sK6,sK6,X0,sK7,X1) = k8_funct_2(sK5,sK6,X0,sK7,X1)
% 3.66/1.03      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK6,X0))) != iProver_top
% 3.66/1.03      | r1_tarski(k2_relat_1(sK7),k1_relset_1(sK6,X0,X1)) != iProver_top
% 3.66/1.03      | v1_funct_1(X1) != iProver_top ),
% 3.66/1.03      inference(renaming,[status(thm)],[c_5681]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_5691,plain,
% 3.66/1.03      ( k1_partfun1(sK5,sK6,sK6,sK4,sK7,sK8) = k8_funct_2(sK5,sK6,sK4,sK7,sK8)
% 3.66/1.03      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) != iProver_top
% 3.66/1.03      | r1_tarski(k2_relat_1(sK7),k1_relat_1(sK8)) != iProver_top
% 3.66/1.03      | v1_funct_1(sK8) != iProver_top ),
% 3.66/1.03      inference(superposition,[status(thm)],[c_3057,c_5682]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_25,plain,
% 3.66/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.66/1.03      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.66/1.03      | ~ v1_funct_1(X3)
% 3.66/1.03      | ~ v1_funct_1(X0)
% 3.66/1.03      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.66/1.03      inference(cnf_transformation,[],[f81]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_1871,plain,
% 3.66/1.03      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 3.66/1.03      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 3.66/1.03      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.66/1.03      | v1_funct_1(X4) != iProver_top
% 3.66/1.03      | v1_funct_1(X5) != iProver_top ),
% 3.66/1.03      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_2904,plain,
% 3.66/1.03      ( k1_partfun1(X0,X1,sK6,sK4,X2,sK8) = k5_relat_1(X2,sK8)
% 3.66/1.03      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.66/1.03      | v1_funct_1(X2) != iProver_top
% 3.66/1.03      | v1_funct_1(sK8) != iProver_top ),
% 3.66/1.03      inference(superposition,[status(thm)],[c_1868,c_1871]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_3642,plain,
% 3.66/1.03      ( v1_funct_1(X2) != iProver_top
% 3.66/1.03      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.66/1.03      | k1_partfun1(X0,X1,sK6,sK4,X2,sK8) = k5_relat_1(X2,sK8) ),
% 3.66/1.03      inference(global_propositional_subsumption,
% 3.66/1.03                [status(thm)],
% 3.66/1.03                [c_2904,c_40]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_3643,plain,
% 3.66/1.03      ( k1_partfun1(X0,X1,sK6,sK4,X2,sK8) = k5_relat_1(X2,sK8)
% 3.66/1.03      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.66/1.03      | v1_funct_1(X2) != iProver_top ),
% 3.66/1.03      inference(renaming,[status(thm)],[c_3642]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_3652,plain,
% 3.66/1.03      ( k1_partfun1(sK5,sK6,sK6,sK4,sK7,sK8) = k5_relat_1(sK7,sK8)
% 3.66/1.03      | v1_funct_1(sK7) != iProver_top ),
% 3.66/1.03      inference(superposition,[status(thm)],[c_1866,c_3643]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_2280,plain,
% 3.66/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.66/1.03      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 3.66/1.03      | ~ v1_funct_1(X0)
% 3.66/1.03      | ~ v1_funct_1(sK7)
% 3.66/1.03      | k1_partfun1(X3,X4,X1,X2,sK7,X0) = k5_relat_1(sK7,X0) ),
% 3.66/1.03      inference(instantiation,[status(thm)],[c_25]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_2609,plain,
% 3.66/1.03      ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.66/1.03      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 3.66/1.03      | ~ v1_funct_1(sK8)
% 3.66/1.03      | ~ v1_funct_1(sK7)
% 3.66/1.03      | k1_partfun1(X2,X3,X0,X1,sK7,sK8) = k5_relat_1(sK7,sK8) ),
% 3.66/1.03      inference(instantiation,[status(thm)],[c_2280]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_2946,plain,
% 3.66/1.03      ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4)))
% 3.66/1.03      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.66/1.03      | ~ v1_funct_1(sK8)
% 3.66/1.03      | ~ v1_funct_1(sK7)
% 3.66/1.03      | k1_partfun1(X0,X1,sK6,sK4,sK7,sK8) = k5_relat_1(sK7,sK8) ),
% 3.66/1.03      inference(instantiation,[status(thm)],[c_2609]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_3226,plain,
% 3.66/1.03      ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4)))
% 3.66/1.03      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 3.66/1.03      | ~ v1_funct_1(sK8)
% 3.66/1.03      | ~ v1_funct_1(sK7)
% 3.66/1.03      | k1_partfun1(sK5,sK6,sK6,sK4,sK7,sK8) = k5_relat_1(sK7,sK8) ),
% 3.66/1.03      inference(instantiation,[status(thm)],[c_2946]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_3778,plain,
% 3.66/1.03      ( k1_partfun1(sK5,sK6,sK6,sK4,sK7,sK8) = k5_relat_1(sK7,sK8) ),
% 3.66/1.03      inference(global_propositional_subsumption,
% 3.66/1.03                [status(thm)],
% 3.66/1.03                [c_3652,c_34,c_32,c_31,c_30,c_3226]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_5692,plain,
% 3.66/1.03      ( k8_funct_2(sK5,sK6,sK4,sK7,sK8) = k5_relat_1(sK7,sK8)
% 3.66/1.03      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) != iProver_top
% 3.66/1.03      | r1_tarski(k2_relat_1(sK7),k1_relat_1(sK8)) != iProver_top
% 3.66/1.03      | v1_funct_1(sK8) != iProver_top ),
% 3.66/1.03      inference(light_normalisation,[status(thm)],[c_5691,c_3778]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_41,plain,
% 3.66/1.03      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) = iProver_top ),
% 3.66/1.03      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_28,negated_conjecture,
% 3.66/1.03      ( r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8)) ),
% 3.66/1.03      inference(cnf_transformation,[],[f89]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_1870,plain,
% 3.66/1.03      ( r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8)) = iProver_top ),
% 3.66/1.03      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_3224,plain,
% 3.66/1.03      ( r1_tarski(k2_relat_1(sK7),k1_relset_1(sK6,sK4,sK8)) = iProver_top ),
% 3.66/1.03      inference(demodulation,[status(thm)],[c_2986,c_1870]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_3638,plain,
% 3.66/1.03      ( r1_tarski(k2_relat_1(sK7),k1_relat_1(sK8)) = iProver_top ),
% 3.66/1.03      inference(light_normalisation,[status(thm)],[c_3224,c_3057]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_5707,plain,
% 3.66/1.03      ( k8_funct_2(sK5,sK6,sK4,sK7,sK8) = k5_relat_1(sK7,sK8) ),
% 3.66/1.03      inference(global_propositional_subsumption,
% 3.66/1.03                [status(thm)],
% 3.66/1.03                [c_5692,c_40,c_41,c_3638]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_26,negated_conjecture,
% 3.66/1.03      ( k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),sK9) != k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) ),
% 3.66/1.03      inference(cnf_transformation,[],[f91]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_5710,plain,
% 3.66/1.03      ( k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) != k1_funct_1(k5_relat_1(sK7,sK8),sK9) ),
% 3.66/1.03      inference(demodulation,[status(thm)],[c_5707,c_26]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(c_7601,plain,
% 3.66/1.03      ( k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) != k1_funct_1(sK8,k1_funct_1(sK7,sK9)) ),
% 3.66/1.03      inference(demodulation,[status(thm)],[c_7598,c_5710]) ).
% 3.66/1.03  
% 3.66/1.03  cnf(contradiction,plain,
% 3.66/1.03      ( $false ),
% 3.66/1.03      inference(minisat,[status(thm)],[c_9042,c_7601,c_3638]) ).
% 3.66/1.03  
% 3.66/1.03  
% 3.66/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 3.66/1.03  
% 3.66/1.03  ------                               Statistics
% 3.66/1.03  
% 3.66/1.03  ------ General
% 3.66/1.03  
% 3.66/1.03  abstr_ref_over_cycles:                  0
% 3.66/1.03  abstr_ref_under_cycles:                 0
% 3.66/1.03  gc_basic_clause_elim:                   0
% 3.66/1.03  forced_gc_time:                         0
% 3.66/1.03  parsing_time:                           0.01
% 3.66/1.03  unif_index_cands_time:                  0.
% 3.66/1.03  unif_index_add_time:                    0.
% 3.66/1.03  orderings_time:                         0.
% 3.66/1.03  out_proof_time:                         0.019
% 3.66/1.03  total_time:                             0.422
% 3.66/1.03  num_of_symbols:                         61
% 3.66/1.03  num_of_terms:                           9750
% 3.66/1.03  
% 3.66/1.03  ------ Preprocessing
% 3.66/1.03  
% 3.66/1.03  num_of_splits:                          0
% 3.66/1.03  num_of_split_atoms:                     0
% 3.66/1.03  num_of_reused_defs:                     0
% 3.66/1.03  num_eq_ax_congr_red:                    59
% 3.66/1.03  num_of_sem_filtered_clauses:            1
% 3.66/1.03  num_of_subtypes:                        0
% 3.66/1.03  monotx_restored_types:                  0
% 3.66/1.03  sat_num_of_epr_types:                   0
% 3.66/1.03  sat_num_of_non_cyclic_types:            0
% 3.66/1.03  sat_guarded_non_collapsed_types:        0
% 3.66/1.03  num_pure_diseq_elim:                    0
% 3.66/1.03  simp_replaced_by:                       0
% 3.66/1.03  res_preprocessed:                       172
% 3.66/1.03  prep_upred:                             0
% 3.66/1.03  prep_unflattend:                        92
% 3.66/1.03  smt_new_axioms:                         0
% 3.66/1.03  pred_elim_cands:                        7
% 3.66/1.03  pred_elim:                              1
% 3.66/1.03  pred_elim_cl:                           1
% 3.66/1.03  pred_elim_cycles:                       5
% 3.66/1.03  merged_defs:                            0
% 3.66/1.03  merged_defs_ncl:                        0
% 3.66/1.03  bin_hyper_res:                          0
% 3.66/1.03  prep_cycles:                            4
% 3.66/1.03  pred_elim_time:                         0.03
% 3.66/1.03  splitting_time:                         0.
% 3.66/1.03  sem_filter_time:                        0.
% 3.66/1.03  monotx_time:                            0.001
% 3.66/1.03  subtype_inf_time:                       0.
% 3.66/1.03  
% 3.66/1.03  ------ Problem properties
% 3.66/1.03  
% 3.66/1.03  clauses:                                35
% 3.66/1.03  conjectures:                            10
% 3.66/1.03  epr:                                    10
% 3.66/1.03  horn:                                   26
% 3.66/1.03  ground:                                 11
% 3.66/1.03  unary:                                  11
% 3.66/1.03  binary:                                 5
% 3.66/1.03  lits:                                   102
% 3.66/1.03  lits_eq:                                25
% 3.66/1.03  fd_pure:                                0
% 3.66/1.03  fd_pseudo:                              0
% 3.66/1.03  fd_cond:                                4
% 3.66/1.03  fd_pseudo_cond:                         4
% 3.66/1.03  ac_symbols:                             0
% 3.66/1.03  
% 3.66/1.03  ------ Propositional Solver
% 3.66/1.03  
% 3.66/1.03  prop_solver_calls:                      29
% 3.66/1.03  prop_fast_solver_calls:                 1585
% 3.66/1.03  smt_solver_calls:                       0
% 3.66/1.03  smt_fast_solver_calls:                  0
% 3.66/1.03  prop_num_of_clauses:                    2858
% 3.66/1.03  prop_preprocess_simplified:             7306
% 3.66/1.03  prop_fo_subsumed:                       54
% 3.66/1.03  prop_solver_time:                       0.
% 3.66/1.03  smt_solver_time:                        0.
% 3.66/1.03  smt_fast_solver_time:                   0.
% 3.66/1.03  prop_fast_solver_time:                  0.
% 3.66/1.03  prop_unsat_core_time:                   0.
% 3.66/1.03  
% 3.66/1.03  ------ QBF
% 3.66/1.03  
% 3.66/1.03  qbf_q_res:                              0
% 3.66/1.03  qbf_num_tautologies:                    0
% 3.66/1.03  qbf_prep_cycles:                        0
% 3.66/1.03  
% 3.66/1.03  ------ BMC1
% 3.66/1.03  
% 3.66/1.03  bmc1_current_bound:                     -1
% 3.66/1.03  bmc1_last_solved_bound:                 -1
% 3.66/1.03  bmc1_unsat_core_size:                   -1
% 3.66/1.03  bmc1_unsat_core_parents_size:           -1
% 3.66/1.03  bmc1_merge_next_fun:                    0
% 3.66/1.03  bmc1_unsat_core_clauses_time:           0.
% 3.66/1.03  
% 3.66/1.03  ------ Instantiation
% 3.66/1.03  
% 3.66/1.03  inst_num_of_clauses:                    719
% 3.66/1.03  inst_num_in_passive:                    107
% 3.66/1.03  inst_num_in_active:                     531
% 3.66/1.03  inst_num_in_unprocessed:                81
% 3.66/1.03  inst_num_of_loops:                      570
% 3.66/1.03  inst_num_of_learning_restarts:          0
% 3.66/1.03  inst_num_moves_active_passive:          35
% 3.66/1.03  inst_lit_activity:                      0
% 3.66/1.03  inst_lit_activity_moves:                0
% 3.66/1.03  inst_num_tautologies:                   0
% 3.66/1.03  inst_num_prop_implied:                  0
% 3.66/1.03  inst_num_existing_simplified:           0
% 3.66/1.03  inst_num_eq_res_simplified:             0
% 3.66/1.03  inst_num_child_elim:                    0
% 3.66/1.03  inst_num_of_dismatching_blockings:      144
% 3.66/1.03  inst_num_of_non_proper_insts:           657
% 3.66/1.03  inst_num_of_duplicates:                 0
% 3.66/1.03  inst_inst_num_from_inst_to_res:         0
% 3.66/1.03  inst_dismatching_checking_time:         0.
% 3.66/1.03  
% 3.66/1.03  ------ Resolution
% 3.66/1.03  
% 3.66/1.03  res_num_of_clauses:                     0
% 3.66/1.03  res_num_in_passive:                     0
% 3.66/1.03  res_num_in_active:                      0
% 3.66/1.03  res_num_of_loops:                       176
% 3.66/1.03  res_forward_subset_subsumed:            69
% 3.66/1.03  res_backward_subset_subsumed:           0
% 3.66/1.03  res_forward_subsumed:                   0
% 3.66/1.03  res_backward_subsumed:                  0
% 3.66/1.03  res_forward_subsumption_resolution:     0
% 3.66/1.03  res_backward_subsumption_resolution:    0
% 3.66/1.03  res_clause_to_clause_subsumption:       627
% 3.66/1.03  res_orphan_elimination:                 0
% 3.66/1.03  res_tautology_del:                      71
% 3.66/1.03  res_num_eq_res_simplified:              0
% 3.66/1.03  res_num_sel_changes:                    0
% 3.66/1.03  res_moves_from_active_to_pass:          0
% 3.66/1.03  
% 3.66/1.03  ------ Superposition
% 3.66/1.03  
% 3.66/1.03  sup_time_total:                         0.
% 3.66/1.03  sup_time_generating:                    0.
% 3.66/1.03  sup_time_sim_full:                      0.
% 3.66/1.03  sup_time_sim_immed:                     0.
% 3.66/1.03  
% 3.66/1.03  sup_num_of_clauses:                     264
% 3.66/1.03  sup_num_in_active:                      106
% 3.66/1.03  sup_num_in_passive:                     158
% 3.66/1.03  sup_num_of_loops:                       112
% 3.66/1.03  sup_fw_superposition:                   148
% 3.66/1.03  sup_bw_superposition:                   112
% 3.66/1.03  sup_immediate_simplified:               20
% 3.66/1.03  sup_given_eliminated:                   0
% 3.66/1.03  comparisons_done:                       0
% 3.66/1.03  comparisons_avoided:                    36
% 3.66/1.03  
% 3.66/1.03  ------ Simplifications
% 3.66/1.03  
% 3.66/1.03  
% 3.66/1.03  sim_fw_subset_subsumed:                 6
% 3.66/1.03  sim_bw_subset_subsumed:                 1
% 3.66/1.03  sim_fw_subsumed:                        3
% 3.66/1.03  sim_bw_subsumed:                        1
% 3.66/1.03  sim_fw_subsumption_res:                 0
% 3.66/1.03  sim_bw_subsumption_res:                 0
% 3.66/1.03  sim_tautology_del:                      1
% 3.66/1.03  sim_eq_tautology_del:                   4
% 3.66/1.03  sim_eq_res_simp:                        0
% 3.66/1.03  sim_fw_demodulated:                     2
% 3.66/1.03  sim_bw_demodulated:                     7
% 3.66/1.03  sim_light_normalised:                   11
% 3.66/1.03  sim_joinable_taut:                      0
% 3.66/1.03  sim_joinable_simp:                      0
% 3.66/1.03  sim_ac_normalised:                      0
% 3.66/1.03  sim_smt_subsumption:                    0
% 3.66/1.03  
%------------------------------------------------------------------------------
