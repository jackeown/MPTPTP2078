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
% DateTime   : Thu Dec  3 12:08:29 EST 2020

% Result     : Theorem 8.04s
% Output     : CNFRefutation 8.04s
% Verified   : 
% Statistics : Number of formulae       :  235 (9007 expanded)
%              Number of clauses        :  148 (2578 expanded)
%              Number of leaves         :   30 (2342 expanded)
%              Depth                    :   29
%              Number of atoms          :  770 (66442 expanded)
%              Number of equality atoms :  292 (14955 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f10,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f48,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f49,plain,(
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
    inference(rectify,[],[f48])).

fof(f52,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X5)) = X5
        & r2_hidden(sK3(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X1)) = X2
        & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
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

fof(f53,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f49,f52,f51,f50])).

fof(f73,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f97,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f73])).

fof(f98,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f97])).

fof(f9,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | r2_hidden(sK2(X0,X1),k1_relat_1(X0))
      | r2_hidden(sK1(X0,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f70,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f78,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f2,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] : m1_subset_1(sK0(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f2,f44])).

fof(f60,plain,(
    ! [X0] : m1_subset_1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f45])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f38])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f19,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( r1_partfun1(X2,X3)
           => ( r2_relset_1(X0,X1,X2,X3)
              | ( k1_xboole_0 != X0
                & k1_xboole_0 = X1 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
           => ( r1_partfun1(X2,X3)
             => ( r2_relset_1(X0,X1,X2,X3)
                | ( k1_xboole_0 != X0
                  & k1_xboole_0 = X1 ) ) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f42,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & r1_partfun1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f43,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & r1_partfun1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f42])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & r1_partfun1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
     => ( ~ r2_relset_1(X0,X1,X2,sK8)
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_partfun1(X2,sK8)
        & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(sK8,X0,X1)
        & v1_funct_1(sK8) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r2_relset_1(X0,X1,X2,X3)
            & ( k1_xboole_0 = X0
              | k1_xboole_0 != X1 )
            & r1_partfun1(X2,X3)
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ~ r2_relset_1(sK5,sK6,sK7,X3)
          & ( k1_xboole_0 = sK5
            | k1_xboole_0 != sK6 )
          & r1_partfun1(sK7,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
          & v1_funct_2(X3,sK5,sK6)
          & v1_funct_1(X3) )
      & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
      & v1_funct_2(sK7,sK5,sK6)
      & v1_funct_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,
    ( ~ r2_relset_1(sK5,sK6,sK7,sK8)
    & ( k1_xboole_0 = sK5
      | k1_xboole_0 != sK6 )
    & r1_partfun1(sK7,sK8)
    & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    & v1_funct_2(sK8,sK5,sK6)
    & v1_funct_1(sK8)
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    & v1_funct_2(sK7,sK5,sK6)
    & v1_funct_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f43,f57,f56])).

fof(f92,plain,(
    v1_funct_2(sK8,sK5,sK6) ),
    inference(cnf_transformation,[],[f58])).

fof(f91,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f58])).

fof(f93,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f58])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
         => ( ( r1_partfun1(X2,X3)
              & v1_partfun1(X3,X0)
              & v1_partfun1(X2,X0) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( X2 = X3
          | ~ r1_partfun1(X2,X3)
          | ~ v1_partfun1(X3,X0)
          | ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( X2 = X3
          | ~ r1_partfun1(X2,X3)
          | ~ v1_partfun1(X3,X0)
          | ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f40])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r1_partfun1(X2,X3)
      | ~ v1_partfun1(X3,X0)
      | ~ v1_partfun1(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f94,plain,(
    r1_partfun1(sK7,sK8) ),
    inference(cnf_transformation,[],[f58])).

fof(f88,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f58])).

fof(f90,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f58])).

fof(f89,plain,(
    v1_funct_2(sK7,sK5,sK6) ),
    inference(cnf_transformation,[],[f58])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f59,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f36])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f96,plain,(
    ~ r2_relset_1(sK5,sK6,sK7,sK8) ),
    inference(cnf_transformation,[],[f58])).

fof(f95,plain,
    ( k1_xboole_0 = sK5
    | k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f58])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f13,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( ! [X2] :
                  ( r2_hidden(X2,k1_relat_1(X0))
                 => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) )
              & k1_relat_1(X0) = k1_relat_1(X1) )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f54,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
        & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ( k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
            & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f32,f54])).

fof(f79,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK4(X0,X1),k1_relat_1(X0))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_38539,plain,
    ( ~ r2_hidden(k1_funct_1(sK7,sK4(sK7,sK8)),k2_relat_1(sK7))
    | ~ m1_subset_1(k2_relat_1(sK7),k1_zfmisc_1(X0))
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_38554,plain,
    ( ~ r2_hidden(k1_funct_1(sK7,sK4(sK7,sK8)),k2_relat_1(sK7))
    | ~ m1_subset_1(k2_relat_1(sK7),k1_zfmisc_1(sK5))
    | ~ v1_xboole_0(sK5) ),
    inference(instantiation,[status(thm)],[c_38539])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1869,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK7))
    | r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7))
    | ~ v1_funct_1(sK7)
    | ~ v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_19532,plain,
    ( ~ r2_hidden(sK4(sK7,sK8),k1_relat_1(sK7))
    | r2_hidden(k1_funct_1(sK7,sK4(sK7,sK8)),k2_relat_1(sK7))
    | ~ v1_funct_1(sK7)
    | ~ v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_1869])).

cnf(c_998,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2266,plain,
    ( k1_relat_1(sK8) != X0
    | k1_relat_1(sK7) != X0
    | k1_relat_1(sK7) = k1_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_998])).

cnf(c_11418,plain,
    ( k1_relat_1(sK8) != k1_xboole_0
    | k1_relat_1(sK7) = k1_relat_1(sK8)
    | k1_relat_1(sK7) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2266])).

cnf(c_11,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_14,plain,
    ( r2_hidden(sK2(X0,X1),k1_relat_1(X0))
    | r2_hidden(sK1(X0,X1),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1528,plain,
    ( k2_relat_1(X0) = X1
    | r2_hidden(sK2(X0,X1),k1_relat_1(X0)) = iProver_top
    | r2_hidden(sK1(X0,X1),X1) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_5211,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X1
    | r2_hidden(sK2(k6_relat_1(X0),X1),X0) = iProver_top
    | r2_hidden(sK1(k6_relat_1(X0),X1),X1) = iProver_top
    | v1_funct_1(k6_relat_1(X0)) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_1528])).

cnf(c_10,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_5254,plain,
    ( X0 = X1
    | r2_hidden(sK2(k6_relat_1(X1),X0),X1) = iProver_top
    | r2_hidden(sK1(k6_relat_1(X1),X0),X0) = iProver_top
    | v1_funct_1(k6_relat_1(X1)) != iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5211,c_10])).

cnf(c_19,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1523,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_18,plain,
    ( v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1524,plain,
    ( v1_funct_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_5814,plain,
    ( X0 = X1
    | r2_hidden(sK2(k6_relat_1(X0),X1),X0) = iProver_top
    | r2_hidden(sK1(k6_relat_1(X0),X1),X1) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5254,c_1523,c_1524])).

cnf(c_1,plain,
    ( m1_subset_1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1535,plain,
    ( m1_subset_1(sK0(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_33,negated_conjecture,
    ( v1_funct_2(sK8,sK5,sK6) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_582,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | sK8 != X0
    | sK6 != X2
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_33])).

cnf(c_583,plain,
    ( v1_partfun1(sK8,sK5)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | ~ v1_funct_1(sK8)
    | v1_xboole_0(sK6) ),
    inference(unflattening,[status(thm)],[c_582])).

cnf(c_34,negated_conjecture,
    ( v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_585,plain,
    ( v1_partfun1(sK8,sK5)
    | v1_xboole_0(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_583,c_34,c_32])).

cnf(c_1510,plain,
    ( v1_partfun1(sK8,sK5) = iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_585])).

cnf(c_1519,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_28,plain,
    ( ~ r1_partfun1(X0,X1)
    | ~ v1_partfun1(X1,X2)
    | ~ v1_partfun1(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_31,negated_conjecture,
    ( r1_partfun1(sK7,sK8) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_504,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v1_partfun1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X0)
    | X0 = X2
    | sK8 != X0
    | sK7 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_31])).

cnf(c_505,plain,
    ( ~ v1_partfun1(sK8,X0)
    | ~ v1_partfun1(sK7,X0)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK8)
    | ~ v1_funct_1(sK7)
    | sK8 = sK7 ),
    inference(unflattening,[status(thm)],[c_504])).

cnf(c_37,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_509,plain,
    ( ~ v1_partfun1(sK8,X0)
    | ~ v1_partfun1(sK7,X0)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | sK8 = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_505,c_37,c_34])).

cnf(c_1514,plain,
    ( sK8 = sK7
    | v1_partfun1(sK8,X0) != iProver_top
    | v1_partfun1(sK7,X0) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_509])).

cnf(c_1953,plain,
    ( sK8 = sK7
    | v1_partfun1(sK8,sK5) != iProver_top
    | v1_partfun1(sK7,sK5) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1519,c_1514])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_40,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_1956,plain,
    ( v1_partfun1(sK7,sK5) != iProver_top
    | v1_partfun1(sK8,sK5) != iProver_top
    | sK8 = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1953,c_40])).

cnf(c_1957,plain,
    ( sK8 = sK7
    | v1_partfun1(sK8,sK5) != iProver_top
    | v1_partfun1(sK7,sK5) != iProver_top ),
    inference(renaming,[status(thm)],[c_1956])).

cnf(c_2245,plain,
    ( sK8 = sK7
    | v1_partfun1(sK7,sK5) != iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_1510,c_1957])).

cnf(c_36,negated_conjecture,
    ( v1_funct_2(sK7,sK5,sK6) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_596,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | sK7 != X0
    | sK6 != X2
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_36])).

cnf(c_597,plain,
    ( v1_partfun1(sK7,sK5)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | ~ v1_funct_1(sK7)
    | v1_xboole_0(sK6) ),
    inference(unflattening,[status(thm)],[c_596])).

cnf(c_599,plain,
    ( v1_partfun1(sK7,sK5)
    | v1_xboole_0(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_597,c_37,c_35])).

cnf(c_601,plain,
    ( v1_partfun1(sK7,sK5) = iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_599])).

cnf(c_2366,plain,
    ( sK8 = sK7
    | v1_xboole_0(sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2245,c_601])).

cnf(c_0,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1536,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2659,plain,
    ( sK8 = sK7
    | sK6 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2366,c_1536])).

cnf(c_25,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_29,negated_conjecture,
    ( ~ r2_relset_1(sK5,sK6,sK7,sK8) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_463,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | sK8 != X0
    | sK7 != X0
    | sK6 != X2
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_29])).

cnf(c_464,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | sK7 != sK8 ),
    inference(unflattening,[status(thm)],[c_463])).

cnf(c_468,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | sK7 != sK8 ),
    inference(global_propositional_subsumption,[status(thm)],[c_464,c_32])).

cnf(c_1515,plain,
    ( sK7 != sK8
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_468])).

cnf(c_2809,plain,
    ( sK6 = k1_xboole_0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2659,c_1515])).

cnf(c_2822,plain,
    ( sK6 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1535,c_2809])).

cnf(c_1517,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_2961,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2822,c_1517])).

cnf(c_30,negated_conjecture,
    ( k1_xboole_0 != sK6
    | k1_xboole_0 = sK5 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_2962,plain,
    ( sK5 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2822,c_30])).

cnf(c_2963,plain,
    ( sK5 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_2962])).

cnf(c_2966,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2961,c_2963])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_273,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_4])).

cnf(c_24,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_9,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_484,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_24,c_9])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_494,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_484,c_23])).

cnf(c_561,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | X4 != X1
    | k2_relat_1(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_273,c_494])).

cnf(c_562,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relat_1(X0),k1_zfmisc_1(X2)) ),
    inference(unflattening,[status(thm)],[c_561])).

cnf(c_1511,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_relat_1(X0),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_562])).

cnf(c_3517,plain,
    ( m1_subset_1(k2_relat_1(sK7),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2966,c_1511])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1532,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4564,plain,
    ( r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
    | m1_subset_1(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3517,c_1532])).

cnf(c_997,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2173,plain,
    ( sK7 = sK7 ),
    inference(instantiation,[status(thm)],[c_997])).

cnf(c_1857,plain,
    ( sK8 != X0
    | sK7 != X0
    | sK7 = sK8 ),
    inference(instantiation,[status(thm)],[c_998])).

cnf(c_2284,plain,
    ( sK8 != sK7
    | sK7 = sK8
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_1857])).

cnf(c_2956,plain,
    ( sK8 = sK7
    | v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2822,c_2366])).

cnf(c_3085,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | sK7 != sK8 ),
    inference(instantiation,[status(thm)],[c_468])).

cnf(c_1531,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
    | v1_xboole_0(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4565,plain,
    ( r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3517,c_1531])).

cnf(c_5564,plain,
    ( r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4564,c_32,c_2173,c_2284,c_2956,c_3085,c_4565])).

cnf(c_5821,plain,
    ( k2_relat_1(sK7) = X0
    | r2_hidden(sK1(k6_relat_1(k2_relat_1(sK7)),X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5814,c_5564])).

cnf(c_1527,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_5573,plain,
    ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1527,c_5564])).

cnf(c_38,plain,
    ( v1_funct_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_1797,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_1798,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
    | v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1797])).

cnf(c_7611,plain,
    ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5573,c_38,c_40,c_1798])).

cnf(c_8069,plain,
    ( k1_relat_1(sK7) = k2_relat_1(sK7) ),
    inference(superposition,[status(thm)],[c_5821,c_7611])).

cnf(c_5818,plain,
    ( k2_relat_1(sK7) = X0
    | r2_hidden(sK2(k6_relat_1(X0),k2_relat_1(sK7)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5814,c_5564])).

cnf(c_2,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1534,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_5,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_271,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_5])).

cnf(c_22,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_537,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ),
    inference(resolution,[status(thm)],[c_271,c_22])).

cnf(c_1513,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_537])).

cnf(c_4916,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1534,c_1513])).

cnf(c_8045,plain,
    ( k2_relat_1(sK7) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5818,c_4916])).

cnf(c_10006,plain,
    ( k1_relat_1(sK7) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_8069,c_8045])).

cnf(c_2960,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2822,c_1519])).

cnf(c_2969,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2960,c_2963])).

cnf(c_3704,plain,
    ( m1_subset_1(k2_relat_1(sK8),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2969,c_1511])).

cnf(c_4740,plain,
    ( r2_hidden(X0,k2_relat_1(sK8)) != iProver_top
    | m1_subset_1(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3704,c_1532])).

cnf(c_4741,plain,
    ( r2_hidden(X0,k2_relat_1(sK8)) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3704,c_1531])).

cnf(c_6108,plain,
    ( r2_hidden(X0,k2_relat_1(sK8)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4740,c_32,c_2173,c_2284,c_2956,c_3085,c_4741])).

cnf(c_6117,plain,
    ( r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
    | v1_funct_1(sK8) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_1527,c_6108])).

cnf(c_41,plain,
    ( v1_funct_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_43,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_1794,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | v1_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_1795,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
    | v1_relat_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1794])).

cnf(c_7674,plain,
    ( r2_hidden(X0,k1_relat_1(sK8)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6117,c_41,c_43,c_1795])).

cnf(c_8068,plain,
    ( k1_relat_1(sK8) = k2_relat_1(sK7) ),
    inference(superposition,[status(thm)],[c_5821,c_7674])).

cnf(c_9752,plain,
    ( k1_relat_1(sK8) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_8068,c_8045])).

cnf(c_9226,plain,
    ( k1_relat_1(sK8) = k1_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_997])).

cnf(c_4202,plain,
    ( k1_relat_1(sK8) != X0
    | k1_relat_1(sK8) = k1_relat_1(sK7)
    | k1_relat_1(sK7) != X0 ),
    inference(instantiation,[status(thm)],[c_998])).

cnf(c_9225,plain,
    ( k1_relat_1(sK8) != k1_relat_1(sK8)
    | k1_relat_1(sK8) = k1_relat_1(sK7)
    | k1_relat_1(sK7) != k1_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_4202])).

cnf(c_2145,plain,
    ( X0 != X1
    | sK6 != X1
    | sK6 = X0 ),
    inference(instantiation,[status(thm)],[c_998])).

cnf(c_8722,plain,
    ( X0 != k1_xboole_0
    | sK6 = X0
    | sK6 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2145])).

cnf(c_8723,plain,
    ( sK6 = sK5
    | sK6 != k1_xboole_0
    | sK5 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8722])).

cnf(c_6420,plain,
    ( X0 != X1
    | X0 = sK6
    | sK6 != X1 ),
    inference(instantiation,[status(thm)],[c_998])).

cnf(c_6421,plain,
    ( sK6 != sK5
    | sK5 = sK6
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_6420])).

cnf(c_999,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_4259,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(sK6)
    | X0 != sK6 ),
    inference(instantiation,[status(thm)],[c_999])).

cnf(c_4262,plain,
    ( ~ v1_xboole_0(sK6)
    | v1_xboole_0(sK5)
    | sK5 != sK6 ),
    inference(instantiation,[status(thm)],[c_4259])).

cnf(c_21,plain,
    ( r2_hidden(sK4(X0,X1),k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | X1 = X0
    | k1_relat_1(X1) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2121,plain,
    ( r2_hidden(sK4(sK7,X0),k1_relat_1(sK7))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK7)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK7)
    | X0 = sK7
    | k1_relat_1(X0) != k1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_3884,plain,
    ( r2_hidden(sK4(sK7,sK8),k1_relat_1(sK7))
    | ~ v1_funct_1(sK8)
    | ~ v1_funct_1(sK7)
    | ~ v1_relat_1(sK8)
    | ~ v1_relat_1(sK7)
    | k1_relat_1(sK8) != k1_relat_1(sK7)
    | sK8 = sK7 ),
    inference(instantiation,[status(thm)],[c_2121])).

cnf(c_1000,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1909,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | X1 != k1_zfmisc_1(X2)
    | X0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1000])).

cnf(c_2556,plain,
    ( m1_subset_1(k2_relat_1(sK7),X0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | X0 != k1_zfmisc_1(X1)
    | k2_relat_1(sK7) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1909])).

cnf(c_3833,plain,
    ( m1_subset_1(k2_relat_1(sK7),k1_zfmisc_1(X0))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | k2_relat_1(sK7) != k1_xboole_0
    | k1_zfmisc_1(X0) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_2556])).

cnf(c_3835,plain,
    ( m1_subset_1(k2_relat_1(sK7),k1_zfmisc_1(sK5))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK5))
    | k2_relat_1(sK7) != k1_xboole_0
    | k1_zfmisc_1(sK5) != k1_zfmisc_1(sK5) ),
    inference(instantiation,[status(thm)],[c_3833])).

cnf(c_2368,plain,
    ( v1_xboole_0(sK6)
    | sK8 = sK7 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2366])).

cnf(c_1022,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_997])).

cnf(c_1001,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_1012,plain,
    ( k1_zfmisc_1(sK5) = k1_zfmisc_1(sK5)
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_1001])).

cnf(c_119,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK5)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_38554,c_19532,c_11418,c_10006,c_9752,c_9226,c_9225,c_8723,c_8045,c_6421,c_4262,c_3884,c_3835,c_3085,c_2963,c_2822,c_2368,c_2284,c_2173,c_1797,c_1794,c_1022,c_1012,c_119,c_32,c_34,c_35,c_37])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:45:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 8.04/1.51  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.04/1.51  
% 8.04/1.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 8.04/1.51  
% 8.04/1.51  ------  iProver source info
% 8.04/1.51  
% 8.04/1.51  git: date: 2020-06-30 10:37:57 +0100
% 8.04/1.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 8.04/1.51  git: non_committed_changes: false
% 8.04/1.51  git: last_make_outside_of_git: false
% 8.04/1.51  
% 8.04/1.51  ------ 
% 8.04/1.51  
% 8.04/1.51  ------ Input Options
% 8.04/1.51  
% 8.04/1.51  --out_options                           all
% 8.04/1.51  --tptp_safe_out                         true
% 8.04/1.51  --problem_path                          ""
% 8.04/1.51  --include_path                          ""
% 8.04/1.51  --clausifier                            res/vclausify_rel
% 8.04/1.51  --clausifier_options                    --mode clausify
% 8.04/1.51  --stdin                                 false
% 8.04/1.51  --stats_out                             all
% 8.04/1.51  
% 8.04/1.51  ------ General Options
% 8.04/1.51  
% 8.04/1.51  --fof                                   false
% 8.04/1.51  --time_out_real                         305.
% 8.04/1.51  --time_out_virtual                      -1.
% 8.04/1.51  --symbol_type_check                     false
% 8.04/1.51  --clausify_out                          false
% 8.04/1.51  --sig_cnt_out                           false
% 8.04/1.51  --trig_cnt_out                          false
% 8.04/1.51  --trig_cnt_out_tolerance                1.
% 8.04/1.51  --trig_cnt_out_sk_spl                   false
% 8.04/1.51  --abstr_cl_out                          false
% 8.04/1.51  
% 8.04/1.51  ------ Global Options
% 8.04/1.51  
% 8.04/1.51  --schedule                              default
% 8.04/1.51  --add_important_lit                     false
% 8.04/1.51  --prop_solver_per_cl                    1000
% 8.04/1.51  --min_unsat_core                        false
% 8.04/1.51  --soft_assumptions                      false
% 8.04/1.51  --soft_lemma_size                       3
% 8.04/1.51  --prop_impl_unit_size                   0
% 8.04/1.51  --prop_impl_unit                        []
% 8.04/1.51  --share_sel_clauses                     true
% 8.04/1.51  --reset_solvers                         false
% 8.04/1.51  --bc_imp_inh                            [conj_cone]
% 8.04/1.51  --conj_cone_tolerance                   3.
% 8.04/1.51  --extra_neg_conj                        none
% 8.04/1.51  --large_theory_mode                     true
% 8.04/1.51  --prolific_symb_bound                   200
% 8.04/1.51  --lt_threshold                          2000
% 8.04/1.51  --clause_weak_htbl                      true
% 8.04/1.51  --gc_record_bc_elim                     false
% 8.04/1.51  
% 8.04/1.51  ------ Preprocessing Options
% 8.04/1.51  
% 8.04/1.51  --preprocessing_flag                    true
% 8.04/1.51  --time_out_prep_mult                    0.1
% 8.04/1.51  --splitting_mode                        input
% 8.04/1.51  --splitting_grd                         true
% 8.04/1.51  --splitting_cvd                         false
% 8.04/1.51  --splitting_cvd_svl                     false
% 8.04/1.51  --splitting_nvd                         32
% 8.04/1.51  --sub_typing                            true
% 8.04/1.51  --prep_gs_sim                           true
% 8.04/1.51  --prep_unflatten                        true
% 8.04/1.51  --prep_res_sim                          true
% 8.04/1.51  --prep_upred                            true
% 8.04/1.51  --prep_sem_filter                       exhaustive
% 8.04/1.51  --prep_sem_filter_out                   false
% 8.04/1.51  --pred_elim                             true
% 8.04/1.51  --res_sim_input                         true
% 8.04/1.51  --eq_ax_congr_red                       true
% 8.04/1.51  --pure_diseq_elim                       true
% 8.04/1.51  --brand_transform                       false
% 8.04/1.51  --non_eq_to_eq                          false
% 8.04/1.51  --prep_def_merge                        true
% 8.04/1.51  --prep_def_merge_prop_impl              false
% 8.04/1.51  --prep_def_merge_mbd                    true
% 8.04/1.51  --prep_def_merge_tr_red                 false
% 8.04/1.51  --prep_def_merge_tr_cl                  false
% 8.04/1.51  --smt_preprocessing                     true
% 8.04/1.51  --smt_ac_axioms                         fast
% 8.04/1.51  --preprocessed_out                      false
% 8.04/1.51  --preprocessed_stats                    false
% 8.04/1.51  
% 8.04/1.51  ------ Abstraction refinement Options
% 8.04/1.51  
% 8.04/1.51  --abstr_ref                             []
% 8.04/1.51  --abstr_ref_prep                        false
% 8.04/1.51  --abstr_ref_until_sat                   false
% 8.04/1.51  --abstr_ref_sig_restrict                funpre
% 8.04/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 8.04/1.51  --abstr_ref_under                       []
% 8.04/1.51  
% 8.04/1.51  ------ SAT Options
% 8.04/1.51  
% 8.04/1.51  --sat_mode                              false
% 8.04/1.51  --sat_fm_restart_options                ""
% 8.04/1.51  --sat_gr_def                            false
% 8.04/1.51  --sat_epr_types                         true
% 8.04/1.51  --sat_non_cyclic_types                  false
% 8.04/1.51  --sat_finite_models                     false
% 8.04/1.51  --sat_fm_lemmas                         false
% 8.04/1.51  --sat_fm_prep                           false
% 8.04/1.51  --sat_fm_uc_incr                        true
% 8.04/1.51  --sat_out_model                         small
% 8.04/1.51  --sat_out_clauses                       false
% 8.04/1.51  
% 8.04/1.51  ------ QBF Options
% 8.04/1.51  
% 8.04/1.51  --qbf_mode                              false
% 8.04/1.51  --qbf_elim_univ                         false
% 8.04/1.51  --qbf_dom_inst                          none
% 8.04/1.51  --qbf_dom_pre_inst                      false
% 8.04/1.51  --qbf_sk_in                             false
% 8.04/1.51  --qbf_pred_elim                         true
% 8.04/1.51  --qbf_split                             512
% 8.04/1.51  
% 8.04/1.51  ------ BMC1 Options
% 8.04/1.51  
% 8.04/1.51  --bmc1_incremental                      false
% 8.04/1.51  --bmc1_axioms                           reachable_all
% 8.04/1.51  --bmc1_min_bound                        0
% 8.04/1.51  --bmc1_max_bound                        -1
% 8.04/1.51  --bmc1_max_bound_default                -1
% 8.04/1.51  --bmc1_symbol_reachability              true
% 8.04/1.51  --bmc1_property_lemmas                  false
% 8.04/1.51  --bmc1_k_induction                      false
% 8.04/1.51  --bmc1_non_equiv_states                 false
% 8.04/1.51  --bmc1_deadlock                         false
% 8.04/1.51  --bmc1_ucm                              false
% 8.04/1.51  --bmc1_add_unsat_core                   none
% 8.04/1.51  --bmc1_unsat_core_children              false
% 8.04/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 8.04/1.51  --bmc1_out_stat                         full
% 8.04/1.51  --bmc1_ground_init                      false
% 8.04/1.51  --bmc1_pre_inst_next_state              false
% 8.04/1.51  --bmc1_pre_inst_state                   false
% 8.04/1.51  --bmc1_pre_inst_reach_state             false
% 8.04/1.51  --bmc1_out_unsat_core                   false
% 8.04/1.51  --bmc1_aig_witness_out                  false
% 8.04/1.51  --bmc1_verbose                          false
% 8.04/1.51  --bmc1_dump_clauses_tptp                false
% 8.04/1.51  --bmc1_dump_unsat_core_tptp             false
% 8.04/1.51  --bmc1_dump_file                        -
% 8.04/1.51  --bmc1_ucm_expand_uc_limit              128
% 8.04/1.51  --bmc1_ucm_n_expand_iterations          6
% 8.04/1.51  --bmc1_ucm_extend_mode                  1
% 8.04/1.51  --bmc1_ucm_init_mode                    2
% 8.04/1.51  --bmc1_ucm_cone_mode                    none
% 8.04/1.51  --bmc1_ucm_reduced_relation_type        0
% 8.04/1.51  --bmc1_ucm_relax_model                  4
% 8.04/1.51  --bmc1_ucm_full_tr_after_sat            true
% 8.04/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 8.04/1.51  --bmc1_ucm_layered_model                none
% 8.04/1.51  --bmc1_ucm_max_lemma_size               10
% 8.04/1.51  
% 8.04/1.51  ------ AIG Options
% 8.04/1.51  
% 8.04/1.51  --aig_mode                              false
% 8.04/1.51  
% 8.04/1.51  ------ Instantiation Options
% 8.04/1.51  
% 8.04/1.51  --instantiation_flag                    true
% 8.04/1.51  --inst_sos_flag                         false
% 8.04/1.51  --inst_sos_phase                        true
% 8.04/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 8.04/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 8.04/1.51  --inst_lit_sel_side                     num_symb
% 8.04/1.51  --inst_solver_per_active                1400
% 8.04/1.51  --inst_solver_calls_frac                1.
% 8.04/1.51  --inst_passive_queue_type               priority_queues
% 8.04/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 8.04/1.51  --inst_passive_queues_freq              [25;2]
% 8.04/1.51  --inst_dismatching                      true
% 8.04/1.51  --inst_eager_unprocessed_to_passive     true
% 8.04/1.51  --inst_prop_sim_given                   true
% 8.04/1.51  --inst_prop_sim_new                     false
% 8.04/1.51  --inst_subs_new                         false
% 8.04/1.51  --inst_eq_res_simp                      false
% 8.04/1.51  --inst_subs_given                       false
% 8.04/1.51  --inst_orphan_elimination               true
% 8.04/1.51  --inst_learning_loop_flag               true
% 8.04/1.51  --inst_learning_start                   3000
% 8.04/1.51  --inst_learning_factor                  2
% 8.04/1.51  --inst_start_prop_sim_after_learn       3
% 8.04/1.51  --inst_sel_renew                        solver
% 8.04/1.51  --inst_lit_activity_flag                true
% 8.04/1.51  --inst_restr_to_given                   false
% 8.04/1.51  --inst_activity_threshold               500
% 8.04/1.51  --inst_out_proof                        true
% 8.04/1.51  
% 8.04/1.51  ------ Resolution Options
% 8.04/1.51  
% 8.04/1.51  --resolution_flag                       true
% 8.04/1.51  --res_lit_sel                           adaptive
% 8.04/1.51  --res_lit_sel_side                      none
% 8.04/1.51  --res_ordering                          kbo
% 8.04/1.51  --res_to_prop_solver                    active
% 8.04/1.51  --res_prop_simpl_new                    false
% 8.04/1.51  --res_prop_simpl_given                  true
% 8.04/1.51  --res_passive_queue_type                priority_queues
% 8.04/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 8.04/1.51  --res_passive_queues_freq               [15;5]
% 8.04/1.51  --res_forward_subs                      full
% 8.04/1.51  --res_backward_subs                     full
% 8.04/1.51  --res_forward_subs_resolution           true
% 8.04/1.51  --res_backward_subs_resolution          true
% 8.04/1.51  --res_orphan_elimination                true
% 8.04/1.51  --res_time_limit                        2.
% 8.04/1.51  --res_out_proof                         true
% 8.04/1.51  
% 8.04/1.51  ------ Superposition Options
% 8.04/1.51  
% 8.04/1.51  --superposition_flag                    true
% 8.04/1.51  --sup_passive_queue_type                priority_queues
% 8.04/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 8.04/1.51  --sup_passive_queues_freq               [8;1;4]
% 8.04/1.51  --demod_completeness_check              fast
% 8.04/1.51  --demod_use_ground                      true
% 8.04/1.51  --sup_to_prop_solver                    passive
% 8.04/1.51  --sup_prop_simpl_new                    true
% 8.04/1.51  --sup_prop_simpl_given                  true
% 8.04/1.51  --sup_fun_splitting                     false
% 8.04/1.51  --sup_smt_interval                      50000
% 8.04/1.51  
% 8.04/1.51  ------ Superposition Simplification Setup
% 8.04/1.51  
% 8.04/1.51  --sup_indices_passive                   []
% 8.04/1.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 8.04/1.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 8.04/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 8.04/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 8.04/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 8.04/1.51  --sup_full_bw                           [BwDemod]
% 8.04/1.51  --sup_immed_triv                        [TrivRules]
% 8.04/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 8.04/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 8.04/1.51  --sup_immed_bw_main                     []
% 8.04/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 8.04/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 8.04/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 8.04/1.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 8.04/1.51  
% 8.04/1.51  ------ Combination Options
% 8.04/1.51  
% 8.04/1.51  --comb_res_mult                         3
% 8.04/1.51  --comb_sup_mult                         2
% 8.04/1.51  --comb_inst_mult                        10
% 8.04/1.51  
% 8.04/1.51  ------ Debug Options
% 8.04/1.51  
% 8.04/1.51  --dbg_backtrace                         false
% 8.04/1.51  --dbg_dump_prop_clauses                 false
% 8.04/1.51  --dbg_dump_prop_clauses_file            -
% 8.04/1.51  --dbg_out_stat                          false
% 8.04/1.51  ------ Parsing...
% 8.04/1.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 8.04/1.51  
% 8.04/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 8.04/1.51  
% 8.04/1.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 8.04/1.51  
% 8.04/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.04/1.51  ------ Proving...
% 8.04/1.51  ------ Problem Properties 
% 8.04/1.51  
% 8.04/1.51  
% 8.04/1.51  clauses                                 31
% 8.04/1.51  conjectures                             5
% 8.04/1.51  EPR                                     7
% 8.04/1.51  Horn                                    25
% 8.04/1.51  unary                                   10
% 8.04/1.51  binary                                  9
% 8.04/1.51  lits                                    84
% 8.04/1.51  lits eq                                 18
% 8.04/1.51  fd_pure                                 0
% 8.04/1.51  fd_pseudo                               0
% 8.04/1.51  fd_cond                                 1
% 8.04/1.51  fd_pseudo_cond                          5
% 8.04/1.51  AC symbols                              0
% 8.04/1.51  
% 8.04/1.51  ------ Schedule dynamic 5 is on 
% 8.04/1.51  
% 8.04/1.51  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 8.04/1.51  
% 8.04/1.51  
% 8.04/1.51  ------ 
% 8.04/1.51  Current options:
% 8.04/1.51  ------ 
% 8.04/1.51  
% 8.04/1.51  ------ Input Options
% 8.04/1.51  
% 8.04/1.51  --out_options                           all
% 8.04/1.51  --tptp_safe_out                         true
% 8.04/1.51  --problem_path                          ""
% 8.04/1.51  --include_path                          ""
% 8.04/1.51  --clausifier                            res/vclausify_rel
% 8.04/1.51  --clausifier_options                    --mode clausify
% 8.04/1.51  --stdin                                 false
% 8.04/1.51  --stats_out                             all
% 8.04/1.51  
% 8.04/1.51  ------ General Options
% 8.04/1.51  
% 8.04/1.51  --fof                                   false
% 8.04/1.51  --time_out_real                         305.
% 8.04/1.51  --time_out_virtual                      -1.
% 8.04/1.51  --symbol_type_check                     false
% 8.04/1.51  --clausify_out                          false
% 8.04/1.51  --sig_cnt_out                           false
% 8.04/1.51  --trig_cnt_out                          false
% 8.04/1.51  --trig_cnt_out_tolerance                1.
% 8.04/1.51  --trig_cnt_out_sk_spl                   false
% 8.04/1.51  --abstr_cl_out                          false
% 8.04/1.51  
% 8.04/1.51  ------ Global Options
% 8.04/1.51  
% 8.04/1.51  --schedule                              default
% 8.04/1.51  --add_important_lit                     false
% 8.04/1.51  --prop_solver_per_cl                    1000
% 8.04/1.51  --min_unsat_core                        false
% 8.04/1.51  --soft_assumptions                      false
% 8.04/1.51  --soft_lemma_size                       3
% 8.04/1.51  --prop_impl_unit_size                   0
% 8.04/1.51  --prop_impl_unit                        []
% 8.04/1.51  --share_sel_clauses                     true
% 8.04/1.51  --reset_solvers                         false
% 8.04/1.51  --bc_imp_inh                            [conj_cone]
% 8.04/1.51  --conj_cone_tolerance                   3.
% 8.04/1.51  --extra_neg_conj                        none
% 8.04/1.51  --large_theory_mode                     true
% 8.04/1.51  --prolific_symb_bound                   200
% 8.04/1.51  --lt_threshold                          2000
% 8.04/1.51  --clause_weak_htbl                      true
% 8.04/1.51  --gc_record_bc_elim                     false
% 8.04/1.51  
% 8.04/1.51  ------ Preprocessing Options
% 8.04/1.51  
% 8.04/1.51  --preprocessing_flag                    true
% 8.04/1.51  --time_out_prep_mult                    0.1
% 8.04/1.51  --splitting_mode                        input
% 8.04/1.51  --splitting_grd                         true
% 8.04/1.51  --splitting_cvd                         false
% 8.04/1.51  --splitting_cvd_svl                     false
% 8.04/1.51  --splitting_nvd                         32
% 8.04/1.51  --sub_typing                            true
% 8.04/1.51  --prep_gs_sim                           true
% 8.04/1.51  --prep_unflatten                        true
% 8.04/1.51  --prep_res_sim                          true
% 8.04/1.51  --prep_upred                            true
% 8.04/1.51  --prep_sem_filter                       exhaustive
% 8.04/1.51  --prep_sem_filter_out                   false
% 8.04/1.51  --pred_elim                             true
% 8.04/1.51  --res_sim_input                         true
% 8.04/1.51  --eq_ax_congr_red                       true
% 8.04/1.51  --pure_diseq_elim                       true
% 8.04/1.51  --brand_transform                       false
% 8.04/1.51  --non_eq_to_eq                          false
% 8.04/1.51  --prep_def_merge                        true
% 8.04/1.51  --prep_def_merge_prop_impl              false
% 8.04/1.51  --prep_def_merge_mbd                    true
% 8.04/1.51  --prep_def_merge_tr_red                 false
% 8.04/1.51  --prep_def_merge_tr_cl                  false
% 8.04/1.51  --smt_preprocessing                     true
% 8.04/1.51  --smt_ac_axioms                         fast
% 8.04/1.51  --preprocessed_out                      false
% 8.04/1.51  --preprocessed_stats                    false
% 8.04/1.51  
% 8.04/1.51  ------ Abstraction refinement Options
% 8.04/1.51  
% 8.04/1.51  --abstr_ref                             []
% 8.04/1.51  --abstr_ref_prep                        false
% 8.04/1.51  --abstr_ref_until_sat                   false
% 8.04/1.51  --abstr_ref_sig_restrict                funpre
% 8.04/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 8.04/1.51  --abstr_ref_under                       []
% 8.04/1.51  
% 8.04/1.51  ------ SAT Options
% 8.04/1.51  
% 8.04/1.51  --sat_mode                              false
% 8.04/1.51  --sat_fm_restart_options                ""
% 8.04/1.51  --sat_gr_def                            false
% 8.04/1.51  --sat_epr_types                         true
% 8.04/1.51  --sat_non_cyclic_types                  false
% 8.04/1.51  --sat_finite_models                     false
% 8.04/1.51  --sat_fm_lemmas                         false
% 8.04/1.51  --sat_fm_prep                           false
% 8.04/1.51  --sat_fm_uc_incr                        true
% 8.04/1.51  --sat_out_model                         small
% 8.04/1.51  --sat_out_clauses                       false
% 8.04/1.51  
% 8.04/1.51  ------ QBF Options
% 8.04/1.51  
% 8.04/1.51  --qbf_mode                              false
% 8.04/1.51  --qbf_elim_univ                         false
% 8.04/1.51  --qbf_dom_inst                          none
% 8.04/1.51  --qbf_dom_pre_inst                      false
% 8.04/1.51  --qbf_sk_in                             false
% 8.04/1.51  --qbf_pred_elim                         true
% 8.04/1.51  --qbf_split                             512
% 8.04/1.51  
% 8.04/1.51  ------ BMC1 Options
% 8.04/1.51  
% 8.04/1.51  --bmc1_incremental                      false
% 8.04/1.51  --bmc1_axioms                           reachable_all
% 8.04/1.51  --bmc1_min_bound                        0
% 8.04/1.51  --bmc1_max_bound                        -1
% 8.04/1.51  --bmc1_max_bound_default                -1
% 8.04/1.51  --bmc1_symbol_reachability              true
% 8.04/1.51  --bmc1_property_lemmas                  false
% 8.04/1.51  --bmc1_k_induction                      false
% 8.04/1.51  --bmc1_non_equiv_states                 false
% 8.04/1.51  --bmc1_deadlock                         false
% 8.04/1.51  --bmc1_ucm                              false
% 8.04/1.51  --bmc1_add_unsat_core                   none
% 8.04/1.51  --bmc1_unsat_core_children              false
% 8.04/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 8.04/1.51  --bmc1_out_stat                         full
% 8.04/1.51  --bmc1_ground_init                      false
% 8.04/1.51  --bmc1_pre_inst_next_state              false
% 8.04/1.51  --bmc1_pre_inst_state                   false
% 8.04/1.51  --bmc1_pre_inst_reach_state             false
% 8.04/1.51  --bmc1_out_unsat_core                   false
% 8.04/1.51  --bmc1_aig_witness_out                  false
% 8.04/1.51  --bmc1_verbose                          false
% 8.04/1.51  --bmc1_dump_clauses_tptp                false
% 8.04/1.51  --bmc1_dump_unsat_core_tptp             false
% 8.04/1.51  --bmc1_dump_file                        -
% 8.04/1.51  --bmc1_ucm_expand_uc_limit              128
% 8.04/1.51  --bmc1_ucm_n_expand_iterations          6
% 8.04/1.51  --bmc1_ucm_extend_mode                  1
% 8.04/1.51  --bmc1_ucm_init_mode                    2
% 8.04/1.51  --bmc1_ucm_cone_mode                    none
% 8.04/1.51  --bmc1_ucm_reduced_relation_type        0
% 8.04/1.51  --bmc1_ucm_relax_model                  4
% 8.04/1.51  --bmc1_ucm_full_tr_after_sat            true
% 8.04/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 8.04/1.51  --bmc1_ucm_layered_model                none
% 8.04/1.51  --bmc1_ucm_max_lemma_size               10
% 8.04/1.51  
% 8.04/1.51  ------ AIG Options
% 8.04/1.51  
% 8.04/1.51  --aig_mode                              false
% 8.04/1.51  
% 8.04/1.51  ------ Instantiation Options
% 8.04/1.51  
% 8.04/1.51  --instantiation_flag                    true
% 8.04/1.51  --inst_sos_flag                         false
% 8.04/1.51  --inst_sos_phase                        true
% 8.04/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 8.04/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 8.04/1.51  --inst_lit_sel_side                     none
% 8.04/1.51  --inst_solver_per_active                1400
% 8.04/1.51  --inst_solver_calls_frac                1.
% 8.04/1.51  --inst_passive_queue_type               priority_queues
% 8.04/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 8.04/1.51  --inst_passive_queues_freq              [25;2]
% 8.04/1.51  --inst_dismatching                      true
% 8.04/1.51  --inst_eager_unprocessed_to_passive     true
% 8.04/1.51  --inst_prop_sim_given                   true
% 8.04/1.51  --inst_prop_sim_new                     false
% 8.04/1.51  --inst_subs_new                         false
% 8.04/1.51  --inst_eq_res_simp                      false
% 8.04/1.51  --inst_subs_given                       false
% 8.04/1.51  --inst_orphan_elimination               true
% 8.04/1.51  --inst_learning_loop_flag               true
% 8.04/1.51  --inst_learning_start                   3000
% 8.04/1.51  --inst_learning_factor                  2
% 8.04/1.51  --inst_start_prop_sim_after_learn       3
% 8.04/1.51  --inst_sel_renew                        solver
% 8.04/1.51  --inst_lit_activity_flag                true
% 8.04/1.51  --inst_restr_to_given                   false
% 8.04/1.51  --inst_activity_threshold               500
% 8.04/1.51  --inst_out_proof                        true
% 8.04/1.51  
% 8.04/1.51  ------ Resolution Options
% 8.04/1.51  
% 8.04/1.51  --resolution_flag                       false
% 8.04/1.51  --res_lit_sel                           adaptive
% 8.04/1.51  --res_lit_sel_side                      none
% 8.04/1.51  --res_ordering                          kbo
% 8.04/1.51  --res_to_prop_solver                    active
% 8.04/1.51  --res_prop_simpl_new                    false
% 8.04/1.51  --res_prop_simpl_given                  true
% 8.04/1.51  --res_passive_queue_type                priority_queues
% 8.04/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 8.04/1.51  --res_passive_queues_freq               [15;5]
% 8.04/1.51  --res_forward_subs                      full
% 8.04/1.51  --res_backward_subs                     full
% 8.04/1.51  --res_forward_subs_resolution           true
% 8.04/1.51  --res_backward_subs_resolution          true
% 8.04/1.51  --res_orphan_elimination                true
% 8.04/1.51  --res_time_limit                        2.
% 8.04/1.51  --res_out_proof                         true
% 8.04/1.51  
% 8.04/1.51  ------ Superposition Options
% 8.04/1.51  
% 8.04/1.51  --superposition_flag                    true
% 8.04/1.51  --sup_passive_queue_type                priority_queues
% 8.04/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 8.04/1.51  --sup_passive_queues_freq               [8;1;4]
% 8.04/1.51  --demod_completeness_check              fast
% 8.04/1.51  --demod_use_ground                      true
% 8.04/1.51  --sup_to_prop_solver                    passive
% 8.04/1.51  --sup_prop_simpl_new                    true
% 8.04/1.51  --sup_prop_simpl_given                  true
% 8.04/1.51  --sup_fun_splitting                     false
% 8.04/1.51  --sup_smt_interval                      50000
% 8.04/1.51  
% 8.04/1.51  ------ Superposition Simplification Setup
% 8.04/1.51  
% 8.04/1.51  --sup_indices_passive                   []
% 8.04/1.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 8.04/1.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 8.04/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 8.04/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 8.04/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 8.04/1.51  --sup_full_bw                           [BwDemod]
% 8.04/1.51  --sup_immed_triv                        [TrivRules]
% 8.04/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 8.04/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 8.04/1.51  --sup_immed_bw_main                     []
% 8.04/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 8.04/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 8.04/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 8.04/1.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 8.04/1.51  
% 8.04/1.51  ------ Combination Options
% 8.04/1.51  
% 8.04/1.51  --comb_res_mult                         3
% 8.04/1.51  --comb_sup_mult                         2
% 8.04/1.51  --comb_inst_mult                        10
% 8.04/1.51  
% 8.04/1.51  ------ Debug Options
% 8.04/1.51  
% 8.04/1.51  --dbg_backtrace                         false
% 8.04/1.51  --dbg_dump_prop_clauses                 false
% 8.04/1.51  --dbg_dump_prop_clauses_file            -
% 8.04/1.51  --dbg_out_stat                          false
% 8.04/1.51  
% 8.04/1.51  
% 8.04/1.51  
% 8.04/1.51  
% 8.04/1.51  ------ Proving...
% 8.04/1.51  
% 8.04/1.51  
% 8.04/1.51  % SZS status Theorem for theBenchmark.p
% 8.04/1.51  
% 8.04/1.51  % SZS output start CNFRefutation for theBenchmark.p
% 8.04/1.51  
% 8.04/1.51  fof(f7,axiom,(
% 8.04/1.51    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 8.04/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.04/1.51  
% 8.04/1.51  fof(f27,plain,(
% 8.04/1.51    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 8.04/1.51    inference(ennf_transformation,[],[f7])).
% 8.04/1.51  
% 8.04/1.51  fof(f66,plain,(
% 8.04/1.51    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 8.04/1.51    inference(cnf_transformation,[],[f27])).
% 8.04/1.51  
% 8.04/1.51  fof(f10,axiom,(
% 8.04/1.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 8.04/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.04/1.51  
% 8.04/1.51  fof(f29,plain,(
% 8.04/1.51    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 8.04/1.51    inference(ennf_transformation,[],[f10])).
% 8.04/1.51  
% 8.04/1.51  fof(f30,plain,(
% 8.04/1.51    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 8.04/1.51    inference(flattening,[],[f29])).
% 8.04/1.51  
% 8.04/1.51  fof(f48,plain,(
% 8.04/1.51    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 8.04/1.51    inference(nnf_transformation,[],[f30])).
% 8.04/1.51  
% 8.04/1.51  fof(f49,plain,(
% 8.04/1.51    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 8.04/1.51    inference(rectify,[],[f48])).
% 8.04/1.51  
% 8.04/1.51  fof(f52,plain,(
% 8.04/1.51    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X5)) = X5 & r2_hidden(sK3(X0,X5),k1_relat_1(X0))))),
% 8.04/1.51    introduced(choice_axiom,[])).
% 8.04/1.51  
% 8.04/1.51  fof(f51,plain,(
% 8.04/1.51    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK2(X0,X1)) = X2 & r2_hidden(sK2(X0,X1),k1_relat_1(X0))))) )),
% 8.04/1.51    introduced(choice_axiom,[])).
% 8.04/1.51  
% 8.04/1.51  fof(f50,plain,(
% 8.04/1.51    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK1(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK1(X0,X1),X1))))),
% 8.04/1.51    introduced(choice_axiom,[])).
% 8.04/1.51  
% 8.04/1.51  fof(f53,plain,(
% 8.04/1.51    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1),X1)) & ((k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK3(X0,X5)) = X5 & r2_hidden(sK3(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 8.04/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f49,f52,f51,f50])).
% 8.04/1.51  
% 8.04/1.51  fof(f73,plain,(
% 8.04/1.51    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 8.04/1.51    inference(cnf_transformation,[],[f53])).
% 8.04/1.51  
% 8.04/1.51  fof(f97,plain,(
% 8.04/1.51    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 8.04/1.51    inference(equality_resolution,[],[f73])).
% 8.04/1.51  
% 8.04/1.51  fof(f98,plain,(
% 8.04/1.51    ( ! [X6,X0] : (r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~r2_hidden(X6,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 8.04/1.51    inference(equality_resolution,[],[f97])).
% 8.04/1.51  
% 8.04/1.51  fof(f9,axiom,(
% 8.04/1.51    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 8.04/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.04/1.51  
% 8.04/1.51  fof(f69,plain,(
% 8.04/1.51    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 8.04/1.51    inference(cnf_transformation,[],[f9])).
% 8.04/1.51  
% 8.04/1.51  fof(f74,plain,(
% 8.04/1.51    ( ! [X0,X1] : (k2_relat_1(X0) = X1 | r2_hidden(sK2(X0,X1),k1_relat_1(X0)) | r2_hidden(sK1(X0,X1),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 8.04/1.51    inference(cnf_transformation,[],[f53])).
% 8.04/1.51  
% 8.04/1.51  fof(f70,plain,(
% 8.04/1.51    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 8.04/1.51    inference(cnf_transformation,[],[f9])).
% 8.04/1.51  
% 8.04/1.51  fof(f11,axiom,(
% 8.04/1.51    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 8.04/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.04/1.51  
% 8.04/1.51  fof(f77,plain,(
% 8.04/1.51    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 8.04/1.51    inference(cnf_transformation,[],[f11])).
% 8.04/1.51  
% 8.04/1.51  fof(f78,plain,(
% 8.04/1.51    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 8.04/1.51    inference(cnf_transformation,[],[f11])).
% 8.04/1.51  
% 8.04/1.51  fof(f2,axiom,(
% 8.04/1.51    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 8.04/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.04/1.51  
% 8.04/1.51  fof(f44,plain,(
% 8.04/1.51    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK0(X0),X0))),
% 8.04/1.51    introduced(choice_axiom,[])).
% 8.04/1.51  
% 8.04/1.51  fof(f45,plain,(
% 8.04/1.51    ! [X0] : m1_subset_1(sK0(X0),X0)),
% 8.04/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f2,f44])).
% 8.04/1.51  
% 8.04/1.51  fof(f60,plain,(
% 8.04/1.51    ( ! [X0] : (m1_subset_1(sK0(X0),X0)) )),
% 8.04/1.51    inference(cnf_transformation,[],[f45])).
% 8.04/1.51  
% 8.04/1.51  fof(f17,axiom,(
% 8.04/1.51    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 8.04/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.04/1.51  
% 8.04/1.51  fof(f38,plain,(
% 8.04/1.51    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 8.04/1.51    inference(ennf_transformation,[],[f17])).
% 8.04/1.51  
% 8.04/1.51  fof(f39,plain,(
% 8.04/1.51    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 8.04/1.51    inference(flattening,[],[f38])).
% 8.04/1.51  
% 8.04/1.51  fof(f86,plain,(
% 8.04/1.51    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 8.04/1.51    inference(cnf_transformation,[],[f39])).
% 8.04/1.51  
% 8.04/1.51  fof(f19,conjecture,(
% 8.04/1.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_relset_1(X0,X1,X2,X3) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 8.04/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.04/1.51  
% 8.04/1.51  fof(f20,negated_conjecture,(
% 8.04/1.51    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_relset_1(X0,X1,X2,X3) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 8.04/1.51    inference(negated_conjecture,[],[f19])).
% 8.04/1.51  
% 8.04/1.51  fof(f42,plain,(
% 8.04/1.51    ? [X0,X1,X2] : (? [X3] : (((~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_partfun1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 8.04/1.51    inference(ennf_transformation,[],[f20])).
% 8.04/1.51  
% 8.04/1.51  fof(f43,plain,(
% 8.04/1.51    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 8.04/1.51    inference(flattening,[],[f42])).
% 8.04/1.51  
% 8.04/1.51  fof(f57,plain,(
% 8.04/1.51    ( ! [X2,X0,X1] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (~r2_relset_1(X0,X1,X2,sK8) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,sK8) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(sK8,X0,X1) & v1_funct_1(sK8))) )),
% 8.04/1.51    introduced(choice_axiom,[])).
% 8.04/1.51  
% 8.04/1.51  fof(f56,plain,(
% 8.04/1.51    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK5,sK6,sK7,X3) & (k1_xboole_0 = sK5 | k1_xboole_0 != sK6) & r1_partfun1(sK7,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(X3,sK5,sK6) & v1_funct_1(X3)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(sK7,sK5,sK6) & v1_funct_1(sK7))),
% 8.04/1.51    introduced(choice_axiom,[])).
% 8.04/1.51  
% 8.04/1.51  fof(f58,plain,(
% 8.04/1.51    (~r2_relset_1(sK5,sK6,sK7,sK8) & (k1_xboole_0 = sK5 | k1_xboole_0 != sK6) & r1_partfun1(sK7,sK8) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(sK8,sK5,sK6) & v1_funct_1(sK8)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(sK7,sK5,sK6) & v1_funct_1(sK7)),
% 8.04/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f43,f57,f56])).
% 8.04/1.51  
% 8.04/1.51  fof(f92,plain,(
% 8.04/1.51    v1_funct_2(sK8,sK5,sK6)),
% 8.04/1.51    inference(cnf_transformation,[],[f58])).
% 8.04/1.51  
% 8.04/1.51  fof(f91,plain,(
% 8.04/1.51    v1_funct_1(sK8)),
% 8.04/1.51    inference(cnf_transformation,[],[f58])).
% 8.04/1.51  
% 8.04/1.51  fof(f93,plain,(
% 8.04/1.51    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))),
% 8.04/1.51    inference(cnf_transformation,[],[f58])).
% 8.04/1.51  
% 8.04/1.51  fof(f18,axiom,(
% 8.04/1.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ((r1_partfun1(X2,X3) & v1_partfun1(X3,X0) & v1_partfun1(X2,X0)) => X2 = X3)))),
% 8.04/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.04/1.51  
% 8.04/1.51  fof(f40,plain,(
% 8.04/1.51    ! [X0,X1,X2] : (! [X3] : ((X2 = X3 | (~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 8.04/1.51    inference(ennf_transformation,[],[f18])).
% 8.04/1.51  
% 8.04/1.51  fof(f41,plain,(
% 8.04/1.51    ! [X0,X1,X2] : (! [X3] : (X2 = X3 | ~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 8.04/1.51    inference(flattening,[],[f40])).
% 8.04/1.51  
% 8.04/1.51  fof(f87,plain,(
% 8.04/1.51    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 8.04/1.51    inference(cnf_transformation,[],[f41])).
% 8.04/1.51  
% 8.04/1.51  fof(f94,plain,(
% 8.04/1.51    r1_partfun1(sK7,sK8)),
% 8.04/1.51    inference(cnf_transformation,[],[f58])).
% 8.04/1.51  
% 8.04/1.51  fof(f88,plain,(
% 8.04/1.51    v1_funct_1(sK7)),
% 8.04/1.51    inference(cnf_transformation,[],[f58])).
% 8.04/1.51  
% 8.04/1.51  fof(f90,plain,(
% 8.04/1.51    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))),
% 8.04/1.51    inference(cnf_transformation,[],[f58])).
% 8.04/1.51  
% 8.04/1.51  fof(f89,plain,(
% 8.04/1.51    v1_funct_2(sK7,sK5,sK6)),
% 8.04/1.51    inference(cnf_transformation,[],[f58])).
% 8.04/1.51  
% 8.04/1.51  fof(f1,axiom,(
% 8.04/1.51    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 8.04/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.04/1.51  
% 8.04/1.51  fof(f22,plain,(
% 8.04/1.51    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 8.04/1.51    inference(ennf_transformation,[],[f1])).
% 8.04/1.51  
% 8.04/1.51  fof(f59,plain,(
% 8.04/1.51    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 8.04/1.51    inference(cnf_transformation,[],[f22])).
% 8.04/1.51  
% 8.04/1.51  fof(f16,axiom,(
% 8.04/1.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 8.04/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.04/1.51  
% 8.04/1.51  fof(f36,plain,(
% 8.04/1.51    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 8.04/1.51    inference(ennf_transformation,[],[f16])).
% 8.04/1.51  
% 8.04/1.51  fof(f37,plain,(
% 8.04/1.51    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 8.04/1.51    inference(flattening,[],[f36])).
% 8.04/1.51  
% 8.04/1.51  fof(f84,plain,(
% 8.04/1.51    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 8.04/1.51    inference(cnf_transformation,[],[f37])).
% 8.04/1.51  
% 8.04/1.51  fof(f96,plain,(
% 8.04/1.51    ~r2_relset_1(sK5,sK6,sK7,sK8)),
% 8.04/1.51    inference(cnf_transformation,[],[f58])).
% 8.04/1.51  
% 8.04/1.51  fof(f95,plain,(
% 8.04/1.51    k1_xboole_0 = sK5 | k1_xboole_0 != sK6),
% 8.04/1.51    inference(cnf_transformation,[],[f58])).
% 8.04/1.51  
% 8.04/1.51  fof(f5,axiom,(
% 8.04/1.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 8.04/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.04/1.51  
% 8.04/1.51  fof(f46,plain,(
% 8.04/1.51    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 8.04/1.51    inference(nnf_transformation,[],[f5])).
% 8.04/1.51  
% 8.04/1.51  fof(f64,plain,(
% 8.04/1.51    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 8.04/1.51    inference(cnf_transformation,[],[f46])).
% 8.04/1.51  
% 8.04/1.51  fof(f15,axiom,(
% 8.04/1.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 8.04/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.04/1.51  
% 8.04/1.51  fof(f21,plain,(
% 8.04/1.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 8.04/1.51    inference(pure_predicate_removal,[],[f15])).
% 8.04/1.51  
% 8.04/1.51  fof(f35,plain,(
% 8.04/1.51    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 8.04/1.51    inference(ennf_transformation,[],[f21])).
% 8.04/1.51  
% 8.04/1.51  fof(f83,plain,(
% 8.04/1.51    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 8.04/1.51    inference(cnf_transformation,[],[f35])).
% 8.04/1.51  
% 8.04/1.51  fof(f8,axiom,(
% 8.04/1.51    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 8.04/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.04/1.51  
% 8.04/1.51  fof(f28,plain,(
% 8.04/1.51    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 8.04/1.51    inference(ennf_transformation,[],[f8])).
% 8.04/1.51  
% 8.04/1.51  fof(f47,plain,(
% 8.04/1.51    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 8.04/1.51    inference(nnf_transformation,[],[f28])).
% 8.04/1.51  
% 8.04/1.51  fof(f67,plain,(
% 8.04/1.51    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 8.04/1.51    inference(cnf_transformation,[],[f47])).
% 8.04/1.51  
% 8.04/1.51  fof(f14,axiom,(
% 8.04/1.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 8.04/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.04/1.51  
% 8.04/1.51  fof(f34,plain,(
% 8.04/1.51    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 8.04/1.51    inference(ennf_transformation,[],[f14])).
% 8.04/1.51  
% 8.04/1.51  fof(f82,plain,(
% 8.04/1.51    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 8.04/1.51    inference(cnf_transformation,[],[f34])).
% 8.04/1.51  
% 8.04/1.51  fof(f6,axiom,(
% 8.04/1.51    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 8.04/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.04/1.51  
% 8.04/1.51  fof(f25,plain,(
% 8.04/1.51    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 8.04/1.51    inference(ennf_transformation,[],[f6])).
% 8.04/1.51  
% 8.04/1.51  fof(f26,plain,(
% 8.04/1.51    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 8.04/1.51    inference(flattening,[],[f25])).
% 8.04/1.51  
% 8.04/1.51  fof(f65,plain,(
% 8.04/1.51    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 8.04/1.51    inference(cnf_transformation,[],[f26])).
% 8.04/1.51  
% 8.04/1.51  fof(f3,axiom,(
% 8.04/1.51    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 8.04/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.04/1.51  
% 8.04/1.51  fof(f61,plain,(
% 8.04/1.51    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 8.04/1.51    inference(cnf_transformation,[],[f3])).
% 8.04/1.51  
% 8.04/1.51  fof(f63,plain,(
% 8.04/1.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 8.04/1.51    inference(cnf_transformation,[],[f46])).
% 8.04/1.51  
% 8.04/1.51  fof(f13,axiom,(
% 8.04/1.51    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 8.04/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.04/1.51  
% 8.04/1.51  fof(f33,plain,(
% 8.04/1.51    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 8.04/1.51    inference(ennf_transformation,[],[f13])).
% 8.04/1.51  
% 8.04/1.51  fof(f81,plain,(
% 8.04/1.51    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 8.04/1.51    inference(cnf_transformation,[],[f33])).
% 8.04/1.51  
% 8.04/1.51  fof(f12,axiom,(
% 8.04/1.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 8.04/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.04/1.51  
% 8.04/1.51  fof(f31,plain,(
% 8.04/1.51    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 8.04/1.51    inference(ennf_transformation,[],[f12])).
% 8.04/1.51  
% 8.04/1.51  fof(f32,plain,(
% 8.04/1.51    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 8.04/1.51    inference(flattening,[],[f31])).
% 8.04/1.51  
% 8.04/1.51  fof(f54,plain,(
% 8.04/1.51    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),k1_relat_1(X0))))),
% 8.04/1.51    introduced(choice_axiom,[])).
% 8.04/1.51  
% 8.04/1.51  fof(f55,plain,(
% 8.04/1.51    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 8.04/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f32,f54])).
% 8.04/1.51  
% 8.04/1.51  fof(f79,plain,(
% 8.04/1.51    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK4(X0,X1),k1_relat_1(X0)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 8.04/1.51    inference(cnf_transformation,[],[f55])).
% 8.04/1.51  
% 8.04/1.51  cnf(c_7,plain,
% 8.04/1.51      ( ~ r2_hidden(X0,X1)
% 8.04/1.51      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 8.04/1.51      | ~ v1_xboole_0(X2) ),
% 8.04/1.51      inference(cnf_transformation,[],[f66]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_38539,plain,
% 8.04/1.51      ( ~ r2_hidden(k1_funct_1(sK7,sK4(sK7,sK8)),k2_relat_1(sK7))
% 8.04/1.51      | ~ m1_subset_1(k2_relat_1(sK7),k1_zfmisc_1(X0))
% 8.04/1.51      | ~ v1_xboole_0(X0) ),
% 8.04/1.51      inference(instantiation,[status(thm)],[c_7]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_38554,plain,
% 8.04/1.51      ( ~ r2_hidden(k1_funct_1(sK7,sK4(sK7,sK8)),k2_relat_1(sK7))
% 8.04/1.51      | ~ m1_subset_1(k2_relat_1(sK7),k1_zfmisc_1(sK5))
% 8.04/1.51      | ~ v1_xboole_0(sK5) ),
% 8.04/1.51      inference(instantiation,[status(thm)],[c_38539]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_15,plain,
% 8.04/1.51      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 8.04/1.51      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 8.04/1.51      | ~ v1_funct_1(X1)
% 8.04/1.51      | ~ v1_relat_1(X1) ),
% 8.04/1.51      inference(cnf_transformation,[],[f98]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_1869,plain,
% 8.04/1.51      ( ~ r2_hidden(X0,k1_relat_1(sK7))
% 8.04/1.51      | r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7))
% 8.04/1.51      | ~ v1_funct_1(sK7)
% 8.04/1.51      | ~ v1_relat_1(sK7) ),
% 8.04/1.51      inference(instantiation,[status(thm)],[c_15]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_19532,plain,
% 8.04/1.51      ( ~ r2_hidden(sK4(sK7,sK8),k1_relat_1(sK7))
% 8.04/1.51      | r2_hidden(k1_funct_1(sK7,sK4(sK7,sK8)),k2_relat_1(sK7))
% 8.04/1.51      | ~ v1_funct_1(sK7)
% 8.04/1.51      | ~ v1_relat_1(sK7) ),
% 8.04/1.51      inference(instantiation,[status(thm)],[c_1869]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_998,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_2266,plain,
% 8.04/1.51      ( k1_relat_1(sK8) != X0
% 8.04/1.51      | k1_relat_1(sK7) != X0
% 8.04/1.51      | k1_relat_1(sK7) = k1_relat_1(sK8) ),
% 8.04/1.51      inference(instantiation,[status(thm)],[c_998]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_11418,plain,
% 8.04/1.51      ( k1_relat_1(sK8) != k1_xboole_0
% 8.04/1.51      | k1_relat_1(sK7) = k1_relat_1(sK8)
% 8.04/1.51      | k1_relat_1(sK7) != k1_xboole_0 ),
% 8.04/1.51      inference(instantiation,[status(thm)],[c_2266]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_11,plain,
% 8.04/1.51      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 8.04/1.51      inference(cnf_transformation,[],[f69]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_14,plain,
% 8.04/1.51      ( r2_hidden(sK2(X0,X1),k1_relat_1(X0))
% 8.04/1.51      | r2_hidden(sK1(X0,X1),X1)
% 8.04/1.51      | ~ v1_funct_1(X0)
% 8.04/1.51      | ~ v1_relat_1(X0)
% 8.04/1.51      | k2_relat_1(X0) = X1 ),
% 8.04/1.51      inference(cnf_transformation,[],[f74]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_1528,plain,
% 8.04/1.51      ( k2_relat_1(X0) = X1
% 8.04/1.51      | r2_hidden(sK2(X0,X1),k1_relat_1(X0)) = iProver_top
% 8.04/1.51      | r2_hidden(sK1(X0,X1),X1) = iProver_top
% 8.04/1.51      | v1_funct_1(X0) != iProver_top
% 8.04/1.51      | v1_relat_1(X0) != iProver_top ),
% 8.04/1.51      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_5211,plain,
% 8.04/1.51      ( k2_relat_1(k6_relat_1(X0)) = X1
% 8.04/1.51      | r2_hidden(sK2(k6_relat_1(X0),X1),X0) = iProver_top
% 8.04/1.51      | r2_hidden(sK1(k6_relat_1(X0),X1),X1) = iProver_top
% 8.04/1.51      | v1_funct_1(k6_relat_1(X0)) != iProver_top
% 8.04/1.51      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 8.04/1.51      inference(superposition,[status(thm)],[c_11,c_1528]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_10,plain,
% 8.04/1.51      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 8.04/1.51      inference(cnf_transformation,[],[f70]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_5254,plain,
% 8.04/1.51      ( X0 = X1
% 8.04/1.51      | r2_hidden(sK2(k6_relat_1(X1),X0),X1) = iProver_top
% 8.04/1.51      | r2_hidden(sK1(k6_relat_1(X1),X0),X0) = iProver_top
% 8.04/1.51      | v1_funct_1(k6_relat_1(X1)) != iProver_top
% 8.04/1.51      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 8.04/1.51      inference(demodulation,[status(thm)],[c_5211,c_10]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_19,plain,
% 8.04/1.51      ( v1_relat_1(k6_relat_1(X0)) ),
% 8.04/1.51      inference(cnf_transformation,[],[f77]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_1523,plain,
% 8.04/1.51      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 8.04/1.51      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_18,plain,
% 8.04/1.51      ( v1_funct_1(k6_relat_1(X0)) ),
% 8.04/1.51      inference(cnf_transformation,[],[f78]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_1524,plain,
% 8.04/1.51      ( v1_funct_1(k6_relat_1(X0)) = iProver_top ),
% 8.04/1.51      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_5814,plain,
% 8.04/1.51      ( X0 = X1
% 8.04/1.51      | r2_hidden(sK2(k6_relat_1(X0),X1),X0) = iProver_top
% 8.04/1.51      | r2_hidden(sK1(k6_relat_1(X0),X1),X1) = iProver_top ),
% 8.04/1.51      inference(forward_subsumption_resolution,
% 8.04/1.51                [status(thm)],
% 8.04/1.51                [c_5254,c_1523,c_1524]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_1,plain,
% 8.04/1.51      ( m1_subset_1(sK0(X0),X0) ),
% 8.04/1.51      inference(cnf_transformation,[],[f60]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_1535,plain,
% 8.04/1.51      ( m1_subset_1(sK0(X0),X0) = iProver_top ),
% 8.04/1.51      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_26,plain,
% 8.04/1.51      ( ~ v1_funct_2(X0,X1,X2)
% 8.04/1.51      | v1_partfun1(X0,X1)
% 8.04/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.04/1.51      | ~ v1_funct_1(X0)
% 8.04/1.51      | v1_xboole_0(X2) ),
% 8.04/1.51      inference(cnf_transformation,[],[f86]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_33,negated_conjecture,
% 8.04/1.51      ( v1_funct_2(sK8,sK5,sK6) ),
% 8.04/1.51      inference(cnf_transformation,[],[f92]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_582,plain,
% 8.04/1.51      ( v1_partfun1(X0,X1)
% 8.04/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.04/1.51      | ~ v1_funct_1(X0)
% 8.04/1.51      | v1_xboole_0(X2)
% 8.04/1.51      | sK8 != X0
% 8.04/1.51      | sK6 != X2
% 8.04/1.51      | sK5 != X1 ),
% 8.04/1.51      inference(resolution_lifted,[status(thm)],[c_26,c_33]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_583,plain,
% 8.04/1.51      ( v1_partfun1(sK8,sK5)
% 8.04/1.51      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 8.04/1.51      | ~ v1_funct_1(sK8)
% 8.04/1.51      | v1_xboole_0(sK6) ),
% 8.04/1.51      inference(unflattening,[status(thm)],[c_582]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_34,negated_conjecture,
% 8.04/1.51      ( v1_funct_1(sK8) ),
% 8.04/1.51      inference(cnf_transformation,[],[f91]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_32,negated_conjecture,
% 8.04/1.51      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
% 8.04/1.51      inference(cnf_transformation,[],[f93]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_585,plain,
% 8.04/1.51      ( v1_partfun1(sK8,sK5) | v1_xboole_0(sK6) ),
% 8.04/1.51      inference(global_propositional_subsumption,
% 8.04/1.51                [status(thm)],
% 8.04/1.51                [c_583,c_34,c_32]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_1510,plain,
% 8.04/1.51      ( v1_partfun1(sK8,sK5) = iProver_top
% 8.04/1.51      | v1_xboole_0(sK6) = iProver_top ),
% 8.04/1.51      inference(predicate_to_equality,[status(thm)],[c_585]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_1519,plain,
% 8.04/1.51      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
% 8.04/1.51      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_28,plain,
% 8.04/1.51      ( ~ r1_partfun1(X0,X1)
% 8.04/1.51      | ~ v1_partfun1(X1,X2)
% 8.04/1.51      | ~ v1_partfun1(X0,X2)
% 8.04/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 8.04/1.51      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 8.04/1.51      | ~ v1_funct_1(X0)
% 8.04/1.51      | ~ v1_funct_1(X1)
% 8.04/1.51      | X1 = X0 ),
% 8.04/1.51      inference(cnf_transformation,[],[f87]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_31,negated_conjecture,
% 8.04/1.51      ( r1_partfun1(sK7,sK8) ),
% 8.04/1.51      inference(cnf_transformation,[],[f94]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_504,plain,
% 8.04/1.51      ( ~ v1_partfun1(X0,X1)
% 8.04/1.51      | ~ v1_partfun1(X2,X1)
% 8.04/1.51      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 8.04/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 8.04/1.51      | ~ v1_funct_1(X2)
% 8.04/1.51      | ~ v1_funct_1(X0)
% 8.04/1.51      | X0 = X2
% 8.04/1.51      | sK8 != X0
% 8.04/1.51      | sK7 != X2 ),
% 8.04/1.51      inference(resolution_lifted,[status(thm)],[c_28,c_31]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_505,plain,
% 8.04/1.51      ( ~ v1_partfun1(sK8,X0)
% 8.04/1.51      | ~ v1_partfun1(sK7,X0)
% 8.04/1.51      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 8.04/1.51      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 8.04/1.51      | ~ v1_funct_1(sK8)
% 8.04/1.51      | ~ v1_funct_1(sK7)
% 8.04/1.51      | sK8 = sK7 ),
% 8.04/1.51      inference(unflattening,[status(thm)],[c_504]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_37,negated_conjecture,
% 8.04/1.51      ( v1_funct_1(sK7) ),
% 8.04/1.51      inference(cnf_transformation,[],[f88]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_509,plain,
% 8.04/1.51      ( ~ v1_partfun1(sK8,X0)
% 8.04/1.51      | ~ v1_partfun1(sK7,X0)
% 8.04/1.51      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 8.04/1.51      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 8.04/1.51      | sK8 = sK7 ),
% 8.04/1.51      inference(global_propositional_subsumption,
% 8.04/1.51                [status(thm)],
% 8.04/1.51                [c_505,c_37,c_34]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_1514,plain,
% 8.04/1.51      ( sK8 = sK7
% 8.04/1.51      | v1_partfun1(sK8,X0) != iProver_top
% 8.04/1.51      | v1_partfun1(sK7,X0) != iProver_top
% 8.04/1.51      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 8.04/1.51      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 8.04/1.51      inference(predicate_to_equality,[status(thm)],[c_509]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_1953,plain,
% 8.04/1.51      ( sK8 = sK7
% 8.04/1.51      | v1_partfun1(sK8,sK5) != iProver_top
% 8.04/1.51      | v1_partfun1(sK7,sK5) != iProver_top
% 8.04/1.51      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top ),
% 8.04/1.51      inference(superposition,[status(thm)],[c_1519,c_1514]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_35,negated_conjecture,
% 8.04/1.51      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
% 8.04/1.51      inference(cnf_transformation,[],[f90]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_40,plain,
% 8.04/1.51      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
% 8.04/1.51      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_1956,plain,
% 8.04/1.51      ( v1_partfun1(sK7,sK5) != iProver_top
% 8.04/1.51      | v1_partfun1(sK8,sK5) != iProver_top
% 8.04/1.51      | sK8 = sK7 ),
% 8.04/1.51      inference(global_propositional_subsumption,
% 8.04/1.51                [status(thm)],
% 8.04/1.51                [c_1953,c_40]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_1957,plain,
% 8.04/1.51      ( sK8 = sK7
% 8.04/1.51      | v1_partfun1(sK8,sK5) != iProver_top
% 8.04/1.51      | v1_partfun1(sK7,sK5) != iProver_top ),
% 8.04/1.51      inference(renaming,[status(thm)],[c_1956]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_2245,plain,
% 8.04/1.51      ( sK8 = sK7
% 8.04/1.51      | v1_partfun1(sK7,sK5) != iProver_top
% 8.04/1.51      | v1_xboole_0(sK6) = iProver_top ),
% 8.04/1.51      inference(superposition,[status(thm)],[c_1510,c_1957]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_36,negated_conjecture,
% 8.04/1.51      ( v1_funct_2(sK7,sK5,sK6) ),
% 8.04/1.51      inference(cnf_transformation,[],[f89]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_596,plain,
% 8.04/1.51      ( v1_partfun1(X0,X1)
% 8.04/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.04/1.51      | ~ v1_funct_1(X0)
% 8.04/1.51      | v1_xboole_0(X2)
% 8.04/1.51      | sK7 != X0
% 8.04/1.51      | sK6 != X2
% 8.04/1.51      | sK5 != X1 ),
% 8.04/1.51      inference(resolution_lifted,[status(thm)],[c_26,c_36]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_597,plain,
% 8.04/1.51      ( v1_partfun1(sK7,sK5)
% 8.04/1.51      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 8.04/1.51      | ~ v1_funct_1(sK7)
% 8.04/1.51      | v1_xboole_0(sK6) ),
% 8.04/1.51      inference(unflattening,[status(thm)],[c_596]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_599,plain,
% 8.04/1.51      ( v1_partfun1(sK7,sK5) | v1_xboole_0(sK6) ),
% 8.04/1.51      inference(global_propositional_subsumption,
% 8.04/1.51                [status(thm)],
% 8.04/1.51                [c_597,c_37,c_35]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_601,plain,
% 8.04/1.51      ( v1_partfun1(sK7,sK5) = iProver_top
% 8.04/1.51      | v1_xboole_0(sK6) = iProver_top ),
% 8.04/1.51      inference(predicate_to_equality,[status(thm)],[c_599]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_2366,plain,
% 8.04/1.51      ( sK8 = sK7 | v1_xboole_0(sK6) = iProver_top ),
% 8.04/1.51      inference(global_propositional_subsumption,
% 8.04/1.51                [status(thm)],
% 8.04/1.51                [c_2245,c_601]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_0,plain,
% 8.04/1.51      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 8.04/1.51      inference(cnf_transformation,[],[f59]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_1536,plain,
% 8.04/1.51      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 8.04/1.51      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_2659,plain,
% 8.04/1.51      ( sK8 = sK7 | sK6 = k1_xboole_0 ),
% 8.04/1.51      inference(superposition,[status(thm)],[c_2366,c_1536]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_25,plain,
% 8.04/1.51      ( r2_relset_1(X0,X1,X2,X2)
% 8.04/1.51      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 8.04/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 8.04/1.51      inference(cnf_transformation,[],[f84]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_29,negated_conjecture,
% 8.04/1.51      ( ~ r2_relset_1(sK5,sK6,sK7,sK8) ),
% 8.04/1.51      inference(cnf_transformation,[],[f96]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_463,plain,
% 8.04/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.04/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.04/1.51      | sK8 != X0
% 8.04/1.51      | sK7 != X0
% 8.04/1.51      | sK6 != X2
% 8.04/1.51      | sK5 != X1 ),
% 8.04/1.51      inference(resolution_lifted,[status(thm)],[c_25,c_29]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_464,plain,
% 8.04/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 8.04/1.51      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 8.04/1.51      | sK7 != sK8 ),
% 8.04/1.51      inference(unflattening,[status(thm)],[c_463]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_468,plain,
% 8.04/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 8.04/1.51      | sK7 != sK8 ),
% 8.04/1.51      inference(global_propositional_subsumption,
% 8.04/1.51                [status(thm)],
% 8.04/1.51                [c_464,c_32]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_1515,plain,
% 8.04/1.51      ( sK7 != sK8
% 8.04/1.51      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top ),
% 8.04/1.51      inference(predicate_to_equality,[status(thm)],[c_468]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_2809,plain,
% 8.04/1.51      ( sK6 = k1_xboole_0
% 8.04/1.51      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top ),
% 8.04/1.51      inference(superposition,[status(thm)],[c_2659,c_1515]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_2822,plain,
% 8.04/1.51      ( sK6 = k1_xboole_0 ),
% 8.04/1.51      inference(superposition,[status(thm)],[c_1535,c_2809]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_1517,plain,
% 8.04/1.51      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
% 8.04/1.51      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_2961,plain,
% 8.04/1.51      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_xboole_0))) = iProver_top ),
% 8.04/1.51      inference(demodulation,[status(thm)],[c_2822,c_1517]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_30,negated_conjecture,
% 8.04/1.51      ( k1_xboole_0 != sK6 | k1_xboole_0 = sK5 ),
% 8.04/1.51      inference(cnf_transformation,[],[f95]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_2962,plain,
% 8.04/1.51      ( sK5 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 8.04/1.51      inference(demodulation,[status(thm)],[c_2822,c_30]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_2963,plain,
% 8.04/1.51      ( sK5 = k1_xboole_0 ),
% 8.04/1.51      inference(equality_resolution_simp,[status(thm)],[c_2962]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_2966,plain,
% 8.04/1.51      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 8.04/1.51      inference(light_normalisation,[status(thm)],[c_2961,c_2963]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_4,plain,
% 8.04/1.51      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 8.04/1.51      inference(cnf_transformation,[],[f64]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_273,plain,
% 8.04/1.51      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 8.04/1.51      inference(prop_impl,[status(thm)],[c_4]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_24,plain,
% 8.04/1.51      ( v5_relat_1(X0,X1)
% 8.04/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 8.04/1.51      inference(cnf_transformation,[],[f83]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_9,plain,
% 8.04/1.51      ( ~ v5_relat_1(X0,X1)
% 8.04/1.51      | r1_tarski(k2_relat_1(X0),X1)
% 8.04/1.51      | ~ v1_relat_1(X0) ),
% 8.04/1.51      inference(cnf_transformation,[],[f67]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_484,plain,
% 8.04/1.51      ( r1_tarski(k2_relat_1(X0),X1)
% 8.04/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 8.04/1.51      | ~ v1_relat_1(X0) ),
% 8.04/1.51      inference(resolution,[status(thm)],[c_24,c_9]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_23,plain,
% 8.04/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.04/1.51      | v1_relat_1(X0) ),
% 8.04/1.51      inference(cnf_transformation,[],[f82]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_494,plain,
% 8.04/1.51      ( r1_tarski(k2_relat_1(X0),X1)
% 8.04/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 8.04/1.51      inference(forward_subsumption_resolution,
% 8.04/1.51                [status(thm)],
% 8.04/1.51                [c_484,c_23]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_561,plain,
% 8.04/1.51      ( m1_subset_1(X0,k1_zfmisc_1(X1))
% 8.04/1.51      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 8.04/1.51      | X4 != X1
% 8.04/1.51      | k2_relat_1(X2) != X0 ),
% 8.04/1.51      inference(resolution_lifted,[status(thm)],[c_273,c_494]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_562,plain,
% 8.04/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.04/1.51      | m1_subset_1(k2_relat_1(X0),k1_zfmisc_1(X2)) ),
% 8.04/1.51      inference(unflattening,[status(thm)],[c_561]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_1511,plain,
% 8.04/1.51      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 8.04/1.51      | m1_subset_1(k2_relat_1(X0),k1_zfmisc_1(X2)) = iProver_top ),
% 8.04/1.51      inference(predicate_to_equality,[status(thm)],[c_562]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_3517,plain,
% 8.04/1.51      ( m1_subset_1(k2_relat_1(sK7),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 8.04/1.51      inference(superposition,[status(thm)],[c_2966,c_1511]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_6,plain,
% 8.04/1.51      ( ~ r2_hidden(X0,X1)
% 8.04/1.51      | m1_subset_1(X0,X2)
% 8.04/1.51      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
% 8.04/1.51      inference(cnf_transformation,[],[f65]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_1532,plain,
% 8.04/1.51      ( r2_hidden(X0,X1) != iProver_top
% 8.04/1.51      | m1_subset_1(X0,X2) = iProver_top
% 8.04/1.51      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 8.04/1.51      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_4564,plain,
% 8.04/1.51      ( r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
% 8.04/1.51      | m1_subset_1(X0,k1_xboole_0) = iProver_top ),
% 8.04/1.51      inference(superposition,[status(thm)],[c_3517,c_1532]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_997,plain,( X0 = X0 ),theory(equality) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_2173,plain,
% 8.04/1.51      ( sK7 = sK7 ),
% 8.04/1.51      inference(instantiation,[status(thm)],[c_997]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_1857,plain,
% 8.04/1.51      ( sK8 != X0 | sK7 != X0 | sK7 = sK8 ),
% 8.04/1.51      inference(instantiation,[status(thm)],[c_998]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_2284,plain,
% 8.04/1.51      ( sK8 != sK7 | sK7 = sK8 | sK7 != sK7 ),
% 8.04/1.51      inference(instantiation,[status(thm)],[c_1857]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_2956,plain,
% 8.04/1.51      ( sK8 = sK7 | v1_xboole_0(k1_xboole_0) = iProver_top ),
% 8.04/1.51      inference(demodulation,[status(thm)],[c_2822,c_2366]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_3085,plain,
% 8.04/1.51      ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 8.04/1.51      | sK7 != sK8 ),
% 8.04/1.51      inference(instantiation,[status(thm)],[c_468]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_1531,plain,
% 8.04/1.51      ( r2_hidden(X0,X1) != iProver_top
% 8.04/1.51      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
% 8.04/1.51      | v1_xboole_0(X2) != iProver_top ),
% 8.04/1.51      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_4565,plain,
% 8.04/1.51      ( r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
% 8.04/1.51      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 8.04/1.51      inference(superposition,[status(thm)],[c_3517,c_1531]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_5564,plain,
% 8.04/1.51      ( r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
% 8.04/1.51      inference(global_propositional_subsumption,
% 8.04/1.51                [status(thm)],
% 8.04/1.51                [c_4564,c_32,c_2173,c_2284,c_2956,c_3085,c_4565]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_5821,plain,
% 8.04/1.51      ( k2_relat_1(sK7) = X0
% 8.04/1.51      | r2_hidden(sK1(k6_relat_1(k2_relat_1(sK7)),X0),X0) = iProver_top ),
% 8.04/1.51      inference(superposition,[status(thm)],[c_5814,c_5564]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_1527,plain,
% 8.04/1.51      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 8.04/1.51      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
% 8.04/1.51      | v1_funct_1(X1) != iProver_top
% 8.04/1.51      | v1_relat_1(X1) != iProver_top ),
% 8.04/1.51      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_5573,plain,
% 8.04/1.51      ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
% 8.04/1.51      | v1_funct_1(sK7) != iProver_top
% 8.04/1.51      | v1_relat_1(sK7) != iProver_top ),
% 8.04/1.51      inference(superposition,[status(thm)],[c_1527,c_5564]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_38,plain,
% 8.04/1.51      ( v1_funct_1(sK7) = iProver_top ),
% 8.04/1.51      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_1797,plain,
% 8.04/1.51      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 8.04/1.51      | v1_relat_1(sK7) ),
% 8.04/1.51      inference(instantiation,[status(thm)],[c_23]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_1798,plain,
% 8.04/1.51      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
% 8.04/1.51      | v1_relat_1(sK7) = iProver_top ),
% 8.04/1.51      inference(predicate_to_equality,[status(thm)],[c_1797]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_7611,plain,
% 8.04/1.51      ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top ),
% 8.04/1.51      inference(global_propositional_subsumption,
% 8.04/1.51                [status(thm)],
% 8.04/1.51                [c_5573,c_38,c_40,c_1798]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_8069,plain,
% 8.04/1.51      ( k1_relat_1(sK7) = k2_relat_1(sK7) ),
% 8.04/1.51      inference(superposition,[status(thm)],[c_5821,c_7611]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_5818,plain,
% 8.04/1.51      ( k2_relat_1(sK7) = X0
% 8.04/1.51      | r2_hidden(sK2(k6_relat_1(X0),k2_relat_1(sK7)),X0) = iProver_top ),
% 8.04/1.51      inference(superposition,[status(thm)],[c_5814,c_5564]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_2,plain,
% 8.04/1.51      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 8.04/1.51      inference(cnf_transformation,[],[f61]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_1534,plain,
% 8.04/1.51      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 8.04/1.51      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_5,plain,
% 8.04/1.51      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 8.04/1.51      inference(cnf_transformation,[],[f63]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_271,plain,
% 8.04/1.51      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 8.04/1.51      inference(prop_impl,[status(thm)],[c_5]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_22,plain,
% 8.04/1.51      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 8.04/1.51      inference(cnf_transformation,[],[f81]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_537,plain,
% 8.04/1.51      ( ~ r2_hidden(X0,X1) | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ),
% 8.04/1.51      inference(resolution,[status(thm)],[c_271,c_22]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_1513,plain,
% 8.04/1.51      ( r2_hidden(X0,X1) != iProver_top
% 8.04/1.51      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 8.04/1.51      inference(predicate_to_equality,[status(thm)],[c_537]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_4916,plain,
% 8.04/1.51      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 8.04/1.51      inference(superposition,[status(thm)],[c_1534,c_1513]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_8045,plain,
% 8.04/1.51      ( k2_relat_1(sK7) = k1_xboole_0 ),
% 8.04/1.51      inference(superposition,[status(thm)],[c_5818,c_4916]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_10006,plain,
% 8.04/1.51      ( k1_relat_1(sK7) = k1_xboole_0 ),
% 8.04/1.51      inference(light_normalisation,[status(thm)],[c_8069,c_8045]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_2960,plain,
% 8.04/1.51      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_xboole_0))) = iProver_top ),
% 8.04/1.51      inference(demodulation,[status(thm)],[c_2822,c_1519]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_2969,plain,
% 8.04/1.51      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 8.04/1.51      inference(light_normalisation,[status(thm)],[c_2960,c_2963]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_3704,plain,
% 8.04/1.51      ( m1_subset_1(k2_relat_1(sK8),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 8.04/1.51      inference(superposition,[status(thm)],[c_2969,c_1511]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_4740,plain,
% 8.04/1.51      ( r2_hidden(X0,k2_relat_1(sK8)) != iProver_top
% 8.04/1.51      | m1_subset_1(X0,k1_xboole_0) = iProver_top ),
% 8.04/1.51      inference(superposition,[status(thm)],[c_3704,c_1532]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_4741,plain,
% 8.04/1.51      ( r2_hidden(X0,k2_relat_1(sK8)) != iProver_top
% 8.04/1.51      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 8.04/1.51      inference(superposition,[status(thm)],[c_3704,c_1531]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_6108,plain,
% 8.04/1.51      ( r2_hidden(X0,k2_relat_1(sK8)) != iProver_top ),
% 8.04/1.51      inference(global_propositional_subsumption,
% 8.04/1.51                [status(thm)],
% 8.04/1.51                [c_4740,c_32,c_2173,c_2284,c_2956,c_3085,c_4741]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_6117,plain,
% 8.04/1.51      ( r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
% 8.04/1.51      | v1_funct_1(sK8) != iProver_top
% 8.04/1.51      | v1_relat_1(sK8) != iProver_top ),
% 8.04/1.51      inference(superposition,[status(thm)],[c_1527,c_6108]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_41,plain,
% 8.04/1.51      ( v1_funct_1(sK8) = iProver_top ),
% 8.04/1.51      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_43,plain,
% 8.04/1.51      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
% 8.04/1.51      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_1794,plain,
% 8.04/1.51      ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 8.04/1.51      | v1_relat_1(sK8) ),
% 8.04/1.51      inference(instantiation,[status(thm)],[c_23]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_1795,plain,
% 8.04/1.51      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
% 8.04/1.51      | v1_relat_1(sK8) = iProver_top ),
% 8.04/1.51      inference(predicate_to_equality,[status(thm)],[c_1794]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_7674,plain,
% 8.04/1.51      ( r2_hidden(X0,k1_relat_1(sK8)) != iProver_top ),
% 8.04/1.51      inference(global_propositional_subsumption,
% 8.04/1.51                [status(thm)],
% 8.04/1.51                [c_6117,c_41,c_43,c_1795]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_8068,plain,
% 8.04/1.51      ( k1_relat_1(sK8) = k2_relat_1(sK7) ),
% 8.04/1.51      inference(superposition,[status(thm)],[c_5821,c_7674]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_9752,plain,
% 8.04/1.51      ( k1_relat_1(sK8) = k1_xboole_0 ),
% 8.04/1.51      inference(light_normalisation,[status(thm)],[c_8068,c_8045]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_9226,plain,
% 8.04/1.51      ( k1_relat_1(sK8) = k1_relat_1(sK8) ),
% 8.04/1.51      inference(instantiation,[status(thm)],[c_997]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_4202,plain,
% 8.04/1.51      ( k1_relat_1(sK8) != X0
% 8.04/1.51      | k1_relat_1(sK8) = k1_relat_1(sK7)
% 8.04/1.51      | k1_relat_1(sK7) != X0 ),
% 8.04/1.51      inference(instantiation,[status(thm)],[c_998]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_9225,plain,
% 8.04/1.51      ( k1_relat_1(sK8) != k1_relat_1(sK8)
% 8.04/1.51      | k1_relat_1(sK8) = k1_relat_1(sK7)
% 8.04/1.51      | k1_relat_1(sK7) != k1_relat_1(sK8) ),
% 8.04/1.51      inference(instantiation,[status(thm)],[c_4202]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_2145,plain,
% 8.04/1.51      ( X0 != X1 | sK6 != X1 | sK6 = X0 ),
% 8.04/1.51      inference(instantiation,[status(thm)],[c_998]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_8722,plain,
% 8.04/1.51      ( X0 != k1_xboole_0 | sK6 = X0 | sK6 != k1_xboole_0 ),
% 8.04/1.51      inference(instantiation,[status(thm)],[c_2145]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_8723,plain,
% 8.04/1.51      ( sK6 = sK5 | sK6 != k1_xboole_0 | sK5 != k1_xboole_0 ),
% 8.04/1.51      inference(instantiation,[status(thm)],[c_8722]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_6420,plain,
% 8.04/1.51      ( X0 != X1 | X0 = sK6 | sK6 != X1 ),
% 8.04/1.51      inference(instantiation,[status(thm)],[c_998]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_6421,plain,
% 8.04/1.51      ( sK6 != sK5 | sK5 = sK6 | sK5 != sK5 ),
% 8.04/1.51      inference(instantiation,[status(thm)],[c_6420]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_999,plain,
% 8.04/1.51      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 8.04/1.51      theory(equality) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_4259,plain,
% 8.04/1.51      ( v1_xboole_0(X0) | ~ v1_xboole_0(sK6) | X0 != sK6 ),
% 8.04/1.51      inference(instantiation,[status(thm)],[c_999]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_4262,plain,
% 8.04/1.51      ( ~ v1_xboole_0(sK6) | v1_xboole_0(sK5) | sK5 != sK6 ),
% 8.04/1.51      inference(instantiation,[status(thm)],[c_4259]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_21,plain,
% 8.04/1.51      ( r2_hidden(sK4(X0,X1),k1_relat_1(X0))
% 8.04/1.51      | ~ v1_funct_1(X0)
% 8.04/1.51      | ~ v1_funct_1(X1)
% 8.04/1.51      | ~ v1_relat_1(X1)
% 8.04/1.51      | ~ v1_relat_1(X0)
% 8.04/1.51      | X1 = X0
% 8.04/1.51      | k1_relat_1(X1) != k1_relat_1(X0) ),
% 8.04/1.51      inference(cnf_transformation,[],[f79]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_2121,plain,
% 8.04/1.51      ( r2_hidden(sK4(sK7,X0),k1_relat_1(sK7))
% 8.04/1.51      | ~ v1_funct_1(X0)
% 8.04/1.51      | ~ v1_funct_1(sK7)
% 8.04/1.51      | ~ v1_relat_1(X0)
% 8.04/1.51      | ~ v1_relat_1(sK7)
% 8.04/1.51      | X0 = sK7
% 8.04/1.51      | k1_relat_1(X0) != k1_relat_1(sK7) ),
% 8.04/1.51      inference(instantiation,[status(thm)],[c_21]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_3884,plain,
% 8.04/1.51      ( r2_hidden(sK4(sK7,sK8),k1_relat_1(sK7))
% 8.04/1.51      | ~ v1_funct_1(sK8)
% 8.04/1.51      | ~ v1_funct_1(sK7)
% 8.04/1.51      | ~ v1_relat_1(sK8)
% 8.04/1.51      | ~ v1_relat_1(sK7)
% 8.04/1.51      | k1_relat_1(sK8) != k1_relat_1(sK7)
% 8.04/1.51      | sK8 = sK7 ),
% 8.04/1.51      inference(instantiation,[status(thm)],[c_2121]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_1000,plain,
% 8.04/1.51      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 8.04/1.51      theory(equality) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_1909,plain,
% 8.04/1.51      ( m1_subset_1(X0,X1)
% 8.04/1.51      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
% 8.04/1.51      | X1 != k1_zfmisc_1(X2)
% 8.04/1.51      | X0 != k1_xboole_0 ),
% 8.04/1.51      inference(instantiation,[status(thm)],[c_1000]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_2556,plain,
% 8.04/1.51      ( m1_subset_1(k2_relat_1(sK7),X0)
% 8.04/1.51      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
% 8.04/1.51      | X0 != k1_zfmisc_1(X1)
% 8.04/1.51      | k2_relat_1(sK7) != k1_xboole_0 ),
% 8.04/1.51      inference(instantiation,[status(thm)],[c_1909]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_3833,plain,
% 8.04/1.51      ( m1_subset_1(k2_relat_1(sK7),k1_zfmisc_1(X0))
% 8.04/1.51      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
% 8.04/1.51      | k2_relat_1(sK7) != k1_xboole_0
% 8.04/1.51      | k1_zfmisc_1(X0) != k1_zfmisc_1(X1) ),
% 8.04/1.51      inference(instantiation,[status(thm)],[c_2556]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_3835,plain,
% 8.04/1.51      ( m1_subset_1(k2_relat_1(sK7),k1_zfmisc_1(sK5))
% 8.04/1.51      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK5))
% 8.04/1.51      | k2_relat_1(sK7) != k1_xboole_0
% 8.04/1.51      | k1_zfmisc_1(sK5) != k1_zfmisc_1(sK5) ),
% 8.04/1.51      inference(instantiation,[status(thm)],[c_3833]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_2368,plain,
% 8.04/1.51      ( v1_xboole_0(sK6) | sK8 = sK7 ),
% 8.04/1.51      inference(predicate_to_equality_rev,[status(thm)],[c_2366]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_1022,plain,
% 8.04/1.51      ( sK5 = sK5 ),
% 8.04/1.51      inference(instantiation,[status(thm)],[c_997]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_1001,plain,
% 8.04/1.51      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 8.04/1.51      theory(equality) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_1012,plain,
% 8.04/1.51      ( k1_zfmisc_1(sK5) = k1_zfmisc_1(sK5) | sK5 != sK5 ),
% 8.04/1.51      inference(instantiation,[status(thm)],[c_1001]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_119,plain,
% 8.04/1.51      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK5)) ),
% 8.04/1.51      inference(instantiation,[status(thm)],[c_2]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(contradiction,plain,
% 8.04/1.51      ( $false ),
% 8.04/1.51      inference(minisat,
% 8.04/1.51                [status(thm)],
% 8.04/1.51                [c_38554,c_19532,c_11418,c_10006,c_9752,c_9226,c_9225,
% 8.04/1.51                 c_8723,c_8045,c_6421,c_4262,c_3884,c_3835,c_3085,c_2963,
% 8.04/1.51                 c_2822,c_2368,c_2284,c_2173,c_1797,c_1794,c_1022,c_1012,
% 8.04/1.51                 c_119,c_32,c_34,c_35,c_37]) ).
% 8.04/1.51  
% 8.04/1.51  
% 8.04/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 8.04/1.51  
% 8.04/1.51  ------                               Statistics
% 8.04/1.51  
% 8.04/1.51  ------ General
% 8.04/1.51  
% 8.04/1.51  abstr_ref_over_cycles:                  0
% 8.04/1.51  abstr_ref_under_cycles:                 0
% 8.04/1.51  gc_basic_clause_elim:                   0
% 8.04/1.51  forced_gc_time:                         0
% 8.04/1.51  parsing_time:                           0.014
% 8.04/1.51  unif_index_cands_time:                  0.
% 8.04/1.51  unif_index_add_time:                    0.
% 8.04/1.51  orderings_time:                         0.
% 8.04/1.51  out_proof_time:                         0.014
% 8.04/1.51  total_time:                             0.971
% 8.04/1.51  num_of_symbols:                         58
% 8.04/1.51  num_of_terms:                           30787
% 8.04/1.51  
% 8.04/1.51  ------ Preprocessing
% 8.04/1.51  
% 8.04/1.51  num_of_splits:                          0
% 8.04/1.51  num_of_split_atoms:                     0
% 8.04/1.51  num_of_reused_defs:                     0
% 8.04/1.51  num_eq_ax_congr_red:                    39
% 8.04/1.51  num_of_sem_filtered_clauses:            1
% 8.04/1.51  num_of_subtypes:                        0
% 8.04/1.51  monotx_restored_types:                  0
% 8.04/1.51  sat_num_of_epr_types:                   0
% 8.04/1.51  sat_num_of_non_cyclic_types:            0
% 8.04/1.51  sat_guarded_non_collapsed_types:        0
% 8.04/1.51  num_pure_diseq_elim:                    0
% 8.04/1.51  simp_replaced_by:                       0
% 8.04/1.51  res_preprocessed:                       157
% 8.04/1.51  prep_upred:                             0
% 8.04/1.51  prep_unflattend:                        27
% 8.04/1.51  smt_new_axioms:                         0
% 8.04/1.51  pred_elim_cands:                        6
% 8.04/1.51  pred_elim:                              5
% 8.04/1.51  pred_elim_cl:                           6
% 8.04/1.51  pred_elim_cycles:                       7
% 8.04/1.51  merged_defs:                            2
% 8.04/1.51  merged_defs_ncl:                        0
% 8.04/1.51  bin_hyper_res:                          2
% 8.04/1.51  prep_cycles:                            4
% 8.04/1.51  pred_elim_time:                         0.005
% 8.04/1.51  splitting_time:                         0.
% 8.04/1.51  sem_filter_time:                        0.
% 8.04/1.51  monotx_time:                            0.
% 8.04/1.51  subtype_inf_time:                       0.
% 8.04/1.51  
% 8.04/1.51  ------ Problem properties
% 8.04/1.51  
% 8.04/1.51  clauses:                                31
% 8.04/1.51  conjectures:                            5
% 8.04/1.51  epr:                                    7
% 8.04/1.51  horn:                                   25
% 8.04/1.51  ground:                                 7
% 8.04/1.51  unary:                                  10
% 8.04/1.51  binary:                                 9
% 8.04/1.51  lits:                                   84
% 8.04/1.51  lits_eq:                                18
% 8.04/1.51  fd_pure:                                0
% 8.04/1.51  fd_pseudo:                              0
% 8.04/1.51  fd_cond:                                1
% 8.04/1.51  fd_pseudo_cond:                         5
% 8.04/1.51  ac_symbols:                             0
% 8.04/1.51  
% 8.04/1.51  ------ Propositional Solver
% 8.04/1.51  
% 8.04/1.51  prop_solver_calls:                      28
% 8.04/1.51  prop_fast_solver_calls:                 2732
% 8.04/1.51  smt_solver_calls:                       0
% 8.04/1.51  smt_fast_solver_calls:                  0
% 8.04/1.51  prop_num_of_clauses:                    12956
% 8.04/1.51  prop_preprocess_simplified:             24314
% 8.04/1.51  prop_fo_subsumed:                       66
% 8.04/1.51  prop_solver_time:                       0.
% 8.04/1.51  smt_solver_time:                        0.
% 8.04/1.51  smt_fast_solver_time:                   0.
% 8.04/1.51  prop_fast_solver_time:                  0.
% 8.04/1.51  prop_unsat_core_time:                   0.001
% 8.04/1.51  
% 8.04/1.51  ------ QBF
% 8.04/1.51  
% 8.04/1.51  qbf_q_res:                              0
% 8.04/1.51  qbf_num_tautologies:                    0
% 8.04/1.51  qbf_prep_cycles:                        0
% 8.04/1.51  
% 8.04/1.51  ------ BMC1
% 8.04/1.51  
% 8.04/1.51  bmc1_current_bound:                     -1
% 8.04/1.51  bmc1_last_solved_bound:                 -1
% 8.04/1.51  bmc1_unsat_core_size:                   -1
% 8.04/1.51  bmc1_unsat_core_parents_size:           -1
% 8.04/1.51  bmc1_merge_next_fun:                    0
% 8.04/1.51  bmc1_unsat_core_clauses_time:           0.
% 8.04/1.51  
% 8.04/1.51  ------ Instantiation
% 8.04/1.51  
% 8.04/1.51  inst_num_of_clauses:                    3257
% 8.04/1.51  inst_num_in_passive:                    1776
% 8.04/1.51  inst_num_in_active:                     1411
% 8.04/1.51  inst_num_in_unprocessed:                69
% 8.04/1.51  inst_num_of_loops:                      1757
% 8.04/1.51  inst_num_of_learning_restarts:          0
% 8.04/1.51  inst_num_moves_active_passive:          345
% 8.04/1.51  inst_lit_activity:                      0
% 8.04/1.51  inst_lit_activity_moves:                0
% 8.04/1.51  inst_num_tautologies:                   0
% 8.04/1.51  inst_num_prop_implied:                  0
% 8.04/1.51  inst_num_existing_simplified:           0
% 8.04/1.51  inst_num_eq_res_simplified:             0
% 8.04/1.51  inst_num_child_elim:                    0
% 8.04/1.51  inst_num_of_dismatching_blockings:      2178
% 8.04/1.51  inst_num_of_non_proper_insts:           3046
% 8.04/1.51  inst_num_of_duplicates:                 0
% 8.04/1.51  inst_inst_num_from_inst_to_res:         0
% 8.04/1.51  inst_dismatching_checking_time:         0.
% 8.04/1.51  
% 8.04/1.51  ------ Resolution
% 8.04/1.51  
% 8.04/1.51  res_num_of_clauses:                     0
% 8.04/1.51  res_num_in_passive:                     0
% 8.04/1.51  res_num_in_active:                      0
% 8.04/1.51  res_num_of_loops:                       161
% 8.04/1.51  res_forward_subset_subsumed:            160
% 8.04/1.51  res_backward_subset_subsumed:           0
% 8.04/1.51  res_forward_subsumed:                   0
% 8.04/1.51  res_backward_subsumed:                  0
% 8.04/1.51  res_forward_subsumption_resolution:     1
% 8.04/1.51  res_backward_subsumption_resolution:    0
% 8.04/1.51  res_clause_to_clause_subsumption:       3215
% 8.04/1.51  res_orphan_elimination:                 0
% 8.04/1.51  res_tautology_del:                      108
% 8.04/1.51  res_num_eq_res_simplified:              0
% 8.04/1.51  res_num_sel_changes:                    0
% 8.04/1.51  res_moves_from_active_to_pass:          0
% 8.04/1.51  
% 8.04/1.51  ------ Superposition
% 8.04/1.51  
% 8.04/1.51  sup_time_total:                         0.
% 8.04/1.51  sup_time_generating:                    0.
% 8.04/1.51  sup_time_sim_full:                      0.
% 8.04/1.51  sup_time_sim_immed:                     0.
% 8.04/1.51  
% 8.04/1.51  sup_num_of_clauses:                     1022
% 8.04/1.51  sup_num_in_active:                      322
% 8.04/1.51  sup_num_in_passive:                     700
% 8.04/1.51  sup_num_of_loops:                       350
% 8.04/1.51  sup_fw_superposition:                   691
% 8.04/1.51  sup_bw_superposition:                   852
% 8.04/1.51  sup_immediate_simplified:               455
% 8.04/1.51  sup_given_eliminated:                   1
% 8.04/1.51  comparisons_done:                       0
% 8.04/1.51  comparisons_avoided:                    333
% 8.04/1.51  
% 8.04/1.51  ------ Simplifications
% 8.04/1.51  
% 8.04/1.51  
% 8.04/1.51  sim_fw_subset_subsumed:                 226
% 8.04/1.51  sim_bw_subset_subsumed:                 6
% 8.04/1.51  sim_fw_subsumed:                        40
% 8.04/1.51  sim_bw_subsumed:                        0
% 8.04/1.51  sim_fw_subsumption_res:                 136
% 8.04/1.51  sim_bw_subsumption_res:                 0
% 8.04/1.51  sim_tautology_del:                      18
% 8.04/1.51  sim_eq_tautology_del:                   93
% 8.04/1.51  sim_eq_res_simp:                        3
% 8.04/1.51  sim_fw_demodulated:                     174
% 8.04/1.51  sim_bw_demodulated:                     29
% 8.04/1.51  sim_light_normalised:                   103
% 8.04/1.51  sim_joinable_taut:                      0
% 8.04/1.51  sim_joinable_simp:                      0
% 8.04/1.51  sim_ac_normalised:                      0
% 8.04/1.51  sim_smt_subsumption:                    0
% 8.04/1.51  
%------------------------------------------------------------------------------
