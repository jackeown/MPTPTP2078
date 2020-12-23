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
% DateTime   : Thu Dec  3 12:08:30 EST 2020

% Result     : Theorem 3.04s
% Output     : CNFRefutation 3.04s
% Verified   : 
% Statistics : Number of formulae       :  152 (1465 expanded)
%              Number of clauses        :   98 ( 460 expanded)
%              Number of leaves         :   17 ( 368 expanded)
%              Depth                    :   22
%              Number of atoms          :  592 (11062 expanded)
%              Number of equality atoms :  246 (2753 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f23,conjecture,(
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

fof(f24,negated_conjecture,(
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
    inference(negated_conjecture,[],[f23])).

fof(f49,plain,(
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
    inference(ennf_transformation,[],[f24])).

fof(f50,plain,(
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
    inference(flattening,[],[f49])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & r1_partfun1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
     => ( ~ r2_relset_1(X0,X1,X2,sK6)
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_partfun1(X2,sK6)
        & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(sK6,X0,X1)
        & v1_funct_1(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,
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
          ( ~ r2_relset_1(sK3,sK4,sK5,X3)
          & ( k1_xboole_0 = sK3
            | k1_xboole_0 != sK4 )
          & r1_partfun1(sK5,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
          & v1_funct_2(X3,sK3,sK4)
          & v1_funct_1(X3) )
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
      & v1_funct_2(sK5,sK3,sK4)
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,
    ( ~ r2_relset_1(sK3,sK4,sK5,sK6)
    & ( k1_xboole_0 = sK3
      | k1_xboole_0 != sK4 )
    & r1_partfun1(sK5,sK6)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_2(sK6,sK3,sK4)
    & v1_funct_1(sK6)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_2(sK5,sK3,sK4)
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f50,f62,f61])).

fof(f99,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f63])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( ! [X4] :
                ( r2_hidden(X4,X0)
               => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
           => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,X1,X2,X3)
          | ? [X4] :
              ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
              & r2_hidden(X4,X0) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,X1,X2,X3)
          | ? [X4] :
              ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
              & r2_hidden(X4,X0) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f47])).

fof(f59,plain,(
    ! [X3,X2,X0] :
      ( ? [X4] :
          ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
          & r2_hidden(X4,X0) )
     => ( k1_funct_1(X2,sK2(X0,X2,X3)) != k1_funct_1(X3,sK2(X0,X2,X3))
        & r2_hidden(sK2(X0,X2,X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,X1,X2,X3)
          | ( k1_funct_1(X2,sK2(X0,X2,X3)) != k1_funct_1(X3,sK2(X0,X2,X3))
            & r2_hidden(sK2(X0,X2,X3),X0) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f48,f59])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | k1_funct_1(X2,sK2(X0,X2,X3)) != k1_funct_1(X3,sK2(X0,X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f97,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f63])).

fof(f98,plain,(
    v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f63])).

fof(f102,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f63])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v1_partfun1(X2,X0)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f43])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f100,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f63])).

fof(f101,plain,(
    v1_funct_2(sK6,sK3,sK4) ),
    inference(cnf_transformation,[],[f63])).

fof(f21,axiom,(
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

fof(f45,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f94,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r1_partfun1(X2,X3)
      | ~ v1_partfun1(X3,X0)
      | ~ v1_partfun1(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f103,plain,(
    r1_partfun1(sK5,sK6) ),
    inference(cnf_transformation,[],[f63])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f76,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f11,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f79,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( r1_partfun1(X0,X1)
       => r1_partfun1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_partfun1(X1,X0)
      | ~ r1_partfun1(X0,X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_partfun1(X1,X0)
      | ~ r1_partfun1(X0,X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f41])).

fof(f91,plain,(
    ! [X0,X1] :
      ( r1_partfun1(X1,X0)
      | ~ r1_partfun1(X0,X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f105,plain,(
    ~ r2_relset_1(sK3,sK4,sK5,sK6) ),
    inference(cnf_transformation,[],[f63])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ~ v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f95,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | r2_hidden(sK2(X0,X2,X3),X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f52,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f51])).

fof(f53,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f52,f53])).

fof(f64,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f104,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f63])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f106,plain,(
    ! [X2,X1] :
      ( v1_partfun1(X2,k1_xboole_0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f93])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

cnf(c_39,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1745,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_31,plain,
    ( r2_relset_1(X0,X1,X2,X3)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k1_funct_1(X3,sK2(X0,X2,X3)) != k1_funct_1(X2,sK2(X0,X2,X3)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1752,plain,
    ( k1_funct_1(X0,sK2(X1,X2,X0)) != k1_funct_1(X2,sK2(X1,X2,X0))
    | r2_relset_1(X1,X3,X2,X0) = iProver_top
    | v1_funct_2(X2,X1,X3) != iProver_top
    | v1_funct_2(X0,X1,X3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_3510,plain,
    ( r2_relset_1(X0,X1,X2,X2) = iProver_top
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1752])).

cnf(c_8091,plain,
    ( r2_relset_1(sK3,sK4,sK5,sK5) = iProver_top
    | v1_funct_2(sK5,sK3,sK4) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1745,c_3510])).

cnf(c_41,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_42,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_40,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_43,plain,
    ( v1_funct_2(sK5,sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_9197,plain,
    ( r2_relset_1(sK3,sK4,sK5,sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8091,c_42,c_43])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1748,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_29,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1754,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | v1_partfun1(X1,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_5377,plain,
    ( sK4 = k1_xboole_0
    | v1_funct_2(sK6,sK3,sK4) != iProver_top
    | v1_partfun1(sK6,sK3) = iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1748,c_1754])).

cnf(c_38,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_45,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_37,negated_conjecture,
    ( v1_funct_2(sK6,sK3,sK4) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_46,plain,
    ( v1_funct_2(sK6,sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_5704,plain,
    ( v1_partfun1(sK6,sK3) = iProver_top
    | sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5377,c_45,c_46])).

cnf(c_5705,plain,
    ( sK4 = k1_xboole_0
    | v1_partfun1(sK6,sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_5704])).

cnf(c_30,plain,
    ( ~ r1_partfun1(X0,X1)
    | ~ v1_partfun1(X0,X2)
    | ~ v1_partfun1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1753,plain,
    ( X0 = X1
    | r1_partfun1(X1,X0) != iProver_top
    | v1_partfun1(X1,X2) != iProver_top
    | v1_partfun1(X0,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_4585,plain,
    ( sK6 = X0
    | r1_partfun1(sK6,X0) != iProver_top
    | v1_partfun1(X0,sK3) != iProver_top
    | v1_partfun1(sK6,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1748,c_1753])).

cnf(c_5135,plain,
    ( v1_funct_1(X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_partfun1(sK6,sK3) != iProver_top
    | v1_partfun1(X0,sK3) != iProver_top
    | r1_partfun1(sK6,X0) != iProver_top
    | sK6 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4585,c_45])).

cnf(c_5136,plain,
    ( sK6 = X0
    | r1_partfun1(sK6,X0) != iProver_top
    | v1_partfun1(X0,sK3) != iProver_top
    | v1_partfun1(sK6,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5135])).

cnf(c_5148,plain,
    ( sK6 = sK5
    | r1_partfun1(sK6,sK5) != iProver_top
    | v1_partfun1(sK6,sK3) != iProver_top
    | v1_partfun1(sK5,sK3) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1745,c_5136])).

cnf(c_44,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_47,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_35,negated_conjecture,
    ( r1_partfun1(sK5,sK6) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_48,plain,
    ( r1_partfun1(sK5,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_2093,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2840,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ v1_relat_1(k2_zfmisc_1(sK3,sK4))
    | v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_2093])).

cnf(c_2841,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK3,sK4)) != iProver_top
    | v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2840])).

cnf(c_2843,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ v1_relat_1(k2_zfmisc_1(sK3,sK4))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_2093])).

cnf(c_2844,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK3,sK4)) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2843])).

cnf(c_15,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_3185,plain,
    ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_3186,plain,
    ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3185])).

cnf(c_27,plain,
    ( ~ r1_partfun1(X0,X1)
    | r1_partfun1(X1,X0)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_2147,plain,
    ( r1_partfun1(X0,sK5)
    | ~ r1_partfun1(sK5,X0)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK5)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_3412,plain,
    ( r1_partfun1(sK6,sK5)
    | ~ r1_partfun1(sK5,sK6)
    | ~ v1_funct_1(sK6)
    | ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK6)
    | ~ v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_2147])).

cnf(c_3413,plain,
    ( r1_partfun1(sK6,sK5) = iProver_top
    | r1_partfun1(sK5,sK6) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_relat_1(sK6) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3412])).

cnf(c_5161,plain,
    ( v1_partfun1(sK5,sK3) != iProver_top
    | v1_partfun1(sK6,sK3) != iProver_top
    | sK6 = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5148,c_42,c_44,c_45,c_47,c_48,c_2841,c_2844,c_3186,c_3413])).

cnf(c_5162,plain,
    ( sK6 = sK5
    | v1_partfun1(sK6,sK3) != iProver_top
    | v1_partfun1(sK5,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_5161])).

cnf(c_5710,plain,
    ( sK6 = sK5
    | sK4 = k1_xboole_0
    | v1_partfun1(sK5,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5705,c_5162])).

cnf(c_5378,plain,
    ( sK4 = k1_xboole_0
    | v1_funct_2(sK5,sK3,sK4) != iProver_top
    | v1_partfun1(sK5,sK3) = iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1745,c_1754])).

cnf(c_5852,plain,
    ( v1_partfun1(sK5,sK3) = iProver_top
    | sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5378,c_42,c_43])).

cnf(c_5853,plain,
    ( sK4 = k1_xboole_0
    | v1_partfun1(sK5,sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_5852])).

cnf(c_6043,plain,
    ( sK4 = k1_xboole_0
    | sK6 = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5710,c_5853])).

cnf(c_6044,plain,
    ( sK6 = sK5
    | sK4 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_6043])).

cnf(c_33,negated_conjecture,
    ( ~ r2_relset_1(sK3,sK4,sK5,sK6) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1750,plain,
    ( r2_relset_1(sK3,sK4,sK5,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_6056,plain,
    ( sK4 = k1_xboole_0
    | r2_relset_1(sK3,sK4,sK5,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_6044,c_1750])).

cnf(c_9202,plain,
    ( sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_9197,c_6056])).

cnf(c_24,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1758,plain,
    ( v1_partfun1(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_6333,plain,
    ( v1_partfun1(sK6,sK3) != iProver_top
    | v1_xboole_0(sK4) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1748,c_1758])).

cnf(c_32,plain,
    ( r2_relset_1(X0,X1,X2,X3)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | r2_hidden(sK2(X0,X2,X3),X0)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1751,plain,
    ( r2_relset_1(X0,X1,X2,X3) = iProver_top
    | v1_funct_2(X2,X0,X1) != iProver_top
    | v1_funct_2(X3,X0,X1) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | r2_hidden(sK2(X0,X2,X3),X0) = iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_2917,plain,
    ( r2_relset_1(sK3,sK4,X0,sK6) = iProver_top
    | v1_funct_2(X0,sK3,sK4) != iProver_top
    | v1_funct_2(sK6,sK3,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | r2_hidden(sK2(sK3,X0,sK6),sK3) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1748,c_1751])).

cnf(c_3192,plain,
    ( v1_funct_1(X0) != iProver_top
    | r2_hidden(sK2(sK3,X0,sK6),sK3) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | r2_relset_1(sK3,sK4,X0,sK6) = iProver_top
    | v1_funct_2(X0,sK3,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2917,c_45,c_46])).

cnf(c_3193,plain,
    ( r2_relset_1(sK3,sK4,X0,sK6) = iProver_top
    | v1_funct_2(X0,sK3,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | r2_hidden(sK2(sK3,X0,sK6),sK3) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3192])).

cnf(c_3204,plain,
    ( r2_relset_1(sK3,sK4,sK5,sK6) = iProver_top
    | v1_funct_2(sK5,sK3,sK4) != iProver_top
    | r2_hidden(sK2(sK3,sK5,sK6),sK3) = iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1745,c_3193])).

cnf(c_49,plain,
    ( r2_relset_1(sK3,sK4,sK5,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_3264,plain,
    ( r2_hidden(sK2(sK3,sK5,sK6),sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3204,c_42,c_43,c_49])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1777,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3269,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3264,c_1777])).

cnf(c_6492,plain,
    ( v1_xboole_0(sK4) != iProver_top
    | v1_partfun1(sK6,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6333,c_3269])).

cnf(c_6493,plain,
    ( v1_partfun1(sK6,sK3) != iProver_top
    | v1_xboole_0(sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_6492])).

cnf(c_9296,plain,
    ( v1_partfun1(sK6,sK3) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9202,c_6493])).

cnf(c_34,negated_conjecture,
    ( k1_xboole_0 != sK4
    | k1_xboole_0 = sK3 ),
    inference(cnf_transformation,[],[f104])).

cnf(c_9307,plain,
    ( sK3 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_9202,c_34])).

cnf(c_9308,plain,
    ( sK3 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_9307])).

cnf(c_9379,plain,
    ( v1_partfun1(sK6,k1_xboole_0) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9296,c_9308])).

cnf(c_9303,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9202,c_1748])).

cnf(c_9320,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9303,c_9308])).

cnf(c_831,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_2180,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(sK6,sK3,sK4)
    | X0 != sK6
    | X2 != sK4
    | X1 != sK3 ),
    inference(instantiation,[status(thm)],[c_831])).

cnf(c_2670,plain,
    ( v1_funct_2(sK6,X0,X1)
    | ~ v1_funct_2(sK6,sK3,sK4)
    | X1 != sK4
    | X0 != sK3
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_2180])).

cnf(c_2673,plain,
    ( X0 != sK4
    | X1 != sK3
    | sK6 != sK6
    | v1_funct_2(sK6,X1,X0) = iProver_top
    | v1_funct_2(sK6,sK3,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2670])).

cnf(c_2675,plain,
    ( sK6 != sK6
    | k1_xboole_0 != sK4
    | k1_xboole_0 != sK3
    | v1_funct_2(sK6,sK3,sK4) != iProver_top
    | v1_funct_2(sK6,k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2673])).

cnf(c_814,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2353,plain,
    ( sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_814])).

cnf(c_815,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2136,plain,
    ( sK4 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_815])).

cnf(c_2137,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2136])).

cnf(c_28,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | v1_partfun1(X0,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_2126,plain,
    ( ~ v1_funct_2(sK6,k1_xboole_0,X0)
    | v1_partfun1(sK6,k1_xboole_0)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
    | ~ v1_funct_1(sK6) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_2127,plain,
    ( v1_funct_2(sK6,k1_xboole_0,X0) != iProver_top
    | v1_partfun1(sK6,k1_xboole_0) = iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2126])).

cnf(c_2129,plain,
    ( v1_funct_2(sK6,k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_partfun1(sK6,k1_xboole_0) = iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2127])).

cnf(c_855,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_814])).

cnf(c_2,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_112,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9379,c_9320,c_8091,c_6056,c_2675,c_2353,c_2137,c_2129,c_855,c_112,c_34,c_46,c_45,c_43,c_42])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:32:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.04/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.04/0.99  
% 3.04/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.04/0.99  
% 3.04/0.99  ------  iProver source info
% 3.04/0.99  
% 3.04/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.04/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.04/0.99  git: non_committed_changes: false
% 3.04/0.99  git: last_make_outside_of_git: false
% 3.04/0.99  
% 3.04/0.99  ------ 
% 3.04/0.99  
% 3.04/0.99  ------ Input Options
% 3.04/0.99  
% 3.04/0.99  --out_options                           all
% 3.04/0.99  --tptp_safe_out                         true
% 3.04/0.99  --problem_path                          ""
% 3.04/0.99  --include_path                          ""
% 3.04/0.99  --clausifier                            res/vclausify_rel
% 3.04/0.99  --clausifier_options                    --mode clausify
% 3.04/0.99  --stdin                                 false
% 3.04/0.99  --stats_out                             all
% 3.04/0.99  
% 3.04/0.99  ------ General Options
% 3.04/0.99  
% 3.04/0.99  --fof                                   false
% 3.04/0.99  --time_out_real                         305.
% 3.04/0.99  --time_out_virtual                      -1.
% 3.04/0.99  --symbol_type_check                     false
% 3.04/0.99  --clausify_out                          false
% 3.04/0.99  --sig_cnt_out                           false
% 3.04/0.99  --trig_cnt_out                          false
% 3.04/0.99  --trig_cnt_out_tolerance                1.
% 3.04/0.99  --trig_cnt_out_sk_spl                   false
% 3.04/0.99  --abstr_cl_out                          false
% 3.04/0.99  
% 3.04/0.99  ------ Global Options
% 3.04/0.99  
% 3.04/0.99  --schedule                              default
% 3.04/0.99  --add_important_lit                     false
% 3.04/0.99  --prop_solver_per_cl                    1000
% 3.04/0.99  --min_unsat_core                        false
% 3.04/0.99  --soft_assumptions                      false
% 3.04/0.99  --soft_lemma_size                       3
% 3.04/0.99  --prop_impl_unit_size                   0
% 3.04/0.99  --prop_impl_unit                        []
% 3.04/0.99  --share_sel_clauses                     true
% 3.04/0.99  --reset_solvers                         false
% 3.04/0.99  --bc_imp_inh                            [conj_cone]
% 3.04/0.99  --conj_cone_tolerance                   3.
% 3.04/0.99  --extra_neg_conj                        none
% 3.04/0.99  --large_theory_mode                     true
% 3.04/0.99  --prolific_symb_bound                   200
% 3.04/0.99  --lt_threshold                          2000
% 3.04/0.99  --clause_weak_htbl                      true
% 3.04/0.99  --gc_record_bc_elim                     false
% 3.04/0.99  
% 3.04/0.99  ------ Preprocessing Options
% 3.04/0.99  
% 3.04/0.99  --preprocessing_flag                    true
% 3.04/0.99  --time_out_prep_mult                    0.1
% 3.04/0.99  --splitting_mode                        input
% 3.04/0.99  --splitting_grd                         true
% 3.04/0.99  --splitting_cvd                         false
% 3.04/0.99  --splitting_cvd_svl                     false
% 3.04/0.99  --splitting_nvd                         32
% 3.04/0.99  --sub_typing                            true
% 3.04/0.99  --prep_gs_sim                           true
% 3.04/0.99  --prep_unflatten                        true
% 3.04/0.99  --prep_res_sim                          true
% 3.04/0.99  --prep_upred                            true
% 3.04/0.99  --prep_sem_filter                       exhaustive
% 3.04/0.99  --prep_sem_filter_out                   false
% 3.04/0.99  --pred_elim                             true
% 3.04/0.99  --res_sim_input                         true
% 3.04/0.99  --eq_ax_congr_red                       true
% 3.04/0.99  --pure_diseq_elim                       true
% 3.04/0.99  --brand_transform                       false
% 3.04/0.99  --non_eq_to_eq                          false
% 3.04/0.99  --prep_def_merge                        true
% 3.04/0.99  --prep_def_merge_prop_impl              false
% 3.04/0.99  --prep_def_merge_mbd                    true
% 3.04/0.99  --prep_def_merge_tr_red                 false
% 3.04/0.99  --prep_def_merge_tr_cl                  false
% 3.04/0.99  --smt_preprocessing                     true
% 3.04/0.99  --smt_ac_axioms                         fast
% 3.04/0.99  --preprocessed_out                      false
% 3.04/0.99  --preprocessed_stats                    false
% 3.04/0.99  
% 3.04/0.99  ------ Abstraction refinement Options
% 3.04/0.99  
% 3.04/0.99  --abstr_ref                             []
% 3.04/0.99  --abstr_ref_prep                        false
% 3.04/0.99  --abstr_ref_until_sat                   false
% 3.04/0.99  --abstr_ref_sig_restrict                funpre
% 3.04/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.04/0.99  --abstr_ref_under                       []
% 3.04/0.99  
% 3.04/0.99  ------ SAT Options
% 3.04/0.99  
% 3.04/0.99  --sat_mode                              false
% 3.04/0.99  --sat_fm_restart_options                ""
% 3.04/0.99  --sat_gr_def                            false
% 3.04/0.99  --sat_epr_types                         true
% 3.04/0.99  --sat_non_cyclic_types                  false
% 3.04/0.99  --sat_finite_models                     false
% 3.04/0.99  --sat_fm_lemmas                         false
% 3.04/0.99  --sat_fm_prep                           false
% 3.04/0.99  --sat_fm_uc_incr                        true
% 3.04/0.99  --sat_out_model                         small
% 3.04/0.99  --sat_out_clauses                       false
% 3.04/0.99  
% 3.04/0.99  ------ QBF Options
% 3.04/0.99  
% 3.04/0.99  --qbf_mode                              false
% 3.04/0.99  --qbf_elim_univ                         false
% 3.04/0.99  --qbf_dom_inst                          none
% 3.04/0.99  --qbf_dom_pre_inst                      false
% 3.04/0.99  --qbf_sk_in                             false
% 3.04/0.99  --qbf_pred_elim                         true
% 3.04/0.99  --qbf_split                             512
% 3.04/0.99  
% 3.04/0.99  ------ BMC1 Options
% 3.04/0.99  
% 3.04/0.99  --bmc1_incremental                      false
% 3.04/0.99  --bmc1_axioms                           reachable_all
% 3.04/0.99  --bmc1_min_bound                        0
% 3.04/0.99  --bmc1_max_bound                        -1
% 3.04/0.99  --bmc1_max_bound_default                -1
% 3.04/0.99  --bmc1_symbol_reachability              true
% 3.04/0.99  --bmc1_property_lemmas                  false
% 3.04/0.99  --bmc1_k_induction                      false
% 3.04/0.99  --bmc1_non_equiv_states                 false
% 3.04/0.99  --bmc1_deadlock                         false
% 3.04/0.99  --bmc1_ucm                              false
% 3.04/0.99  --bmc1_add_unsat_core                   none
% 3.04/0.99  --bmc1_unsat_core_children              false
% 3.04/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.04/0.99  --bmc1_out_stat                         full
% 3.04/0.99  --bmc1_ground_init                      false
% 3.04/0.99  --bmc1_pre_inst_next_state              false
% 3.04/0.99  --bmc1_pre_inst_state                   false
% 3.04/0.99  --bmc1_pre_inst_reach_state             false
% 3.04/0.99  --bmc1_out_unsat_core                   false
% 3.04/0.99  --bmc1_aig_witness_out                  false
% 3.04/0.99  --bmc1_verbose                          false
% 3.04/0.99  --bmc1_dump_clauses_tptp                false
% 3.04/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.04/0.99  --bmc1_dump_file                        -
% 3.04/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.04/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.04/0.99  --bmc1_ucm_extend_mode                  1
% 3.04/0.99  --bmc1_ucm_init_mode                    2
% 3.04/0.99  --bmc1_ucm_cone_mode                    none
% 3.04/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.04/0.99  --bmc1_ucm_relax_model                  4
% 3.04/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.04/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.04/0.99  --bmc1_ucm_layered_model                none
% 3.04/0.99  --bmc1_ucm_max_lemma_size               10
% 3.04/0.99  
% 3.04/0.99  ------ AIG Options
% 3.04/0.99  
% 3.04/0.99  --aig_mode                              false
% 3.04/0.99  
% 3.04/0.99  ------ Instantiation Options
% 3.04/0.99  
% 3.04/0.99  --instantiation_flag                    true
% 3.04/0.99  --inst_sos_flag                         false
% 3.04/0.99  --inst_sos_phase                        true
% 3.04/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.04/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.04/0.99  --inst_lit_sel_side                     num_symb
% 3.04/0.99  --inst_solver_per_active                1400
% 3.04/0.99  --inst_solver_calls_frac                1.
% 3.04/0.99  --inst_passive_queue_type               priority_queues
% 3.04/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.04/0.99  --inst_passive_queues_freq              [25;2]
% 3.04/0.99  --inst_dismatching                      true
% 3.04/0.99  --inst_eager_unprocessed_to_passive     true
% 3.04/0.99  --inst_prop_sim_given                   true
% 3.04/0.99  --inst_prop_sim_new                     false
% 3.04/0.99  --inst_subs_new                         false
% 3.04/0.99  --inst_eq_res_simp                      false
% 3.04/0.99  --inst_subs_given                       false
% 3.04/0.99  --inst_orphan_elimination               true
% 3.04/0.99  --inst_learning_loop_flag               true
% 3.04/0.99  --inst_learning_start                   3000
% 3.04/0.99  --inst_learning_factor                  2
% 3.04/0.99  --inst_start_prop_sim_after_learn       3
% 3.04/0.99  --inst_sel_renew                        solver
% 3.04/0.99  --inst_lit_activity_flag                true
% 3.04/0.99  --inst_restr_to_given                   false
% 3.04/0.99  --inst_activity_threshold               500
% 3.04/0.99  --inst_out_proof                        true
% 3.04/0.99  
% 3.04/0.99  ------ Resolution Options
% 3.04/0.99  
% 3.04/0.99  --resolution_flag                       true
% 3.04/0.99  --res_lit_sel                           adaptive
% 3.04/0.99  --res_lit_sel_side                      none
% 3.04/0.99  --res_ordering                          kbo
% 3.04/0.99  --res_to_prop_solver                    active
% 3.04/0.99  --res_prop_simpl_new                    false
% 3.04/0.99  --res_prop_simpl_given                  true
% 3.04/0.99  --res_passive_queue_type                priority_queues
% 3.04/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.04/0.99  --res_passive_queues_freq               [15;5]
% 3.04/0.99  --res_forward_subs                      full
% 3.04/0.99  --res_backward_subs                     full
% 3.04/0.99  --res_forward_subs_resolution           true
% 3.04/0.99  --res_backward_subs_resolution          true
% 3.04/0.99  --res_orphan_elimination                true
% 3.04/0.99  --res_time_limit                        2.
% 3.04/0.99  --res_out_proof                         true
% 3.04/0.99  
% 3.04/0.99  ------ Superposition Options
% 3.04/0.99  
% 3.04/0.99  --superposition_flag                    true
% 3.04/0.99  --sup_passive_queue_type                priority_queues
% 3.04/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.04/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.04/0.99  --demod_completeness_check              fast
% 3.04/0.99  --demod_use_ground                      true
% 3.04/0.99  --sup_to_prop_solver                    passive
% 3.04/0.99  --sup_prop_simpl_new                    true
% 3.04/0.99  --sup_prop_simpl_given                  true
% 3.04/0.99  --sup_fun_splitting                     false
% 3.04/0.99  --sup_smt_interval                      50000
% 3.04/0.99  
% 3.04/0.99  ------ Superposition Simplification Setup
% 3.04/0.99  
% 3.04/0.99  --sup_indices_passive                   []
% 3.04/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.04/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.04/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.04/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.04/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.04/0.99  --sup_full_bw                           [BwDemod]
% 3.04/0.99  --sup_immed_triv                        [TrivRules]
% 3.04/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.04/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.04/0.99  --sup_immed_bw_main                     []
% 3.04/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.04/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.04/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.04/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.04/0.99  
% 3.04/0.99  ------ Combination Options
% 3.04/0.99  
% 3.04/0.99  --comb_res_mult                         3
% 3.04/0.99  --comb_sup_mult                         2
% 3.04/0.99  --comb_inst_mult                        10
% 3.04/0.99  
% 3.04/0.99  ------ Debug Options
% 3.04/0.99  
% 3.04/0.99  --dbg_backtrace                         false
% 3.04/0.99  --dbg_dump_prop_clauses                 false
% 3.04/0.99  --dbg_dump_prop_clauses_file            -
% 3.04/0.99  --dbg_out_stat                          false
% 3.04/0.99  ------ Parsing...
% 3.04/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.04/0.99  
% 3.04/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.04/0.99  
% 3.04/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.04/0.99  
% 3.04/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.04/0.99  ------ Proving...
% 3.04/0.99  ------ Problem Properties 
% 3.04/0.99  
% 3.04/0.99  
% 3.04/0.99  clauses                                 41
% 3.04/0.99  conjectures                             9
% 3.04/0.99  EPR                                     12
% 3.04/0.99  Horn                                    35
% 3.04/0.99  unary                                   15
% 3.04/0.99  binary                                  10
% 3.04/0.99  lits                                    109
% 3.04/0.99  lits eq                                 18
% 3.04/0.99  fd_pure                                 0
% 3.04/0.99  fd_pseudo                               0
% 3.04/0.99  fd_cond                                 1
% 3.04/0.99  fd_pseudo_cond                          2
% 3.04/0.99  AC symbols                              0
% 3.04/0.99  
% 3.04/0.99  ------ Schedule dynamic 5 is on 
% 3.04/0.99  
% 3.04/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.04/0.99  
% 3.04/0.99  
% 3.04/0.99  ------ 
% 3.04/0.99  Current options:
% 3.04/0.99  ------ 
% 3.04/0.99  
% 3.04/0.99  ------ Input Options
% 3.04/0.99  
% 3.04/0.99  --out_options                           all
% 3.04/0.99  --tptp_safe_out                         true
% 3.04/0.99  --problem_path                          ""
% 3.04/0.99  --include_path                          ""
% 3.04/0.99  --clausifier                            res/vclausify_rel
% 3.04/0.99  --clausifier_options                    --mode clausify
% 3.04/0.99  --stdin                                 false
% 3.04/0.99  --stats_out                             all
% 3.04/0.99  
% 3.04/0.99  ------ General Options
% 3.04/0.99  
% 3.04/0.99  --fof                                   false
% 3.04/0.99  --time_out_real                         305.
% 3.04/0.99  --time_out_virtual                      -1.
% 3.04/0.99  --symbol_type_check                     false
% 3.04/0.99  --clausify_out                          false
% 3.04/0.99  --sig_cnt_out                           false
% 3.04/0.99  --trig_cnt_out                          false
% 3.04/0.99  --trig_cnt_out_tolerance                1.
% 3.04/0.99  --trig_cnt_out_sk_spl                   false
% 3.04/0.99  --abstr_cl_out                          false
% 3.04/0.99  
% 3.04/0.99  ------ Global Options
% 3.04/0.99  
% 3.04/0.99  --schedule                              default
% 3.04/0.99  --add_important_lit                     false
% 3.04/0.99  --prop_solver_per_cl                    1000
% 3.04/0.99  --min_unsat_core                        false
% 3.04/0.99  --soft_assumptions                      false
% 3.04/0.99  --soft_lemma_size                       3
% 3.04/0.99  --prop_impl_unit_size                   0
% 3.04/0.99  --prop_impl_unit                        []
% 3.04/0.99  --share_sel_clauses                     true
% 3.04/0.99  --reset_solvers                         false
% 3.04/0.99  --bc_imp_inh                            [conj_cone]
% 3.04/0.99  --conj_cone_tolerance                   3.
% 3.04/0.99  --extra_neg_conj                        none
% 3.04/0.99  --large_theory_mode                     true
% 3.04/0.99  --prolific_symb_bound                   200
% 3.04/0.99  --lt_threshold                          2000
% 3.04/0.99  --clause_weak_htbl                      true
% 3.04/0.99  --gc_record_bc_elim                     false
% 3.04/0.99  
% 3.04/0.99  ------ Preprocessing Options
% 3.04/0.99  
% 3.04/0.99  --preprocessing_flag                    true
% 3.04/0.99  --time_out_prep_mult                    0.1
% 3.04/0.99  --splitting_mode                        input
% 3.04/0.99  --splitting_grd                         true
% 3.04/0.99  --splitting_cvd                         false
% 3.04/0.99  --splitting_cvd_svl                     false
% 3.04/0.99  --splitting_nvd                         32
% 3.04/0.99  --sub_typing                            true
% 3.04/0.99  --prep_gs_sim                           true
% 3.04/0.99  --prep_unflatten                        true
% 3.04/0.99  --prep_res_sim                          true
% 3.04/0.99  --prep_upred                            true
% 3.04/0.99  --prep_sem_filter                       exhaustive
% 3.04/0.99  --prep_sem_filter_out                   false
% 3.04/0.99  --pred_elim                             true
% 3.04/0.99  --res_sim_input                         true
% 3.04/0.99  --eq_ax_congr_red                       true
% 3.04/0.99  --pure_diseq_elim                       true
% 3.04/0.99  --brand_transform                       false
% 3.04/0.99  --non_eq_to_eq                          false
% 3.04/0.99  --prep_def_merge                        true
% 3.04/0.99  --prep_def_merge_prop_impl              false
% 3.04/0.99  --prep_def_merge_mbd                    true
% 3.04/0.99  --prep_def_merge_tr_red                 false
% 3.04/0.99  --prep_def_merge_tr_cl                  false
% 3.04/0.99  --smt_preprocessing                     true
% 3.04/0.99  --smt_ac_axioms                         fast
% 3.04/0.99  --preprocessed_out                      false
% 3.04/0.99  --preprocessed_stats                    false
% 3.04/0.99  
% 3.04/0.99  ------ Abstraction refinement Options
% 3.04/0.99  
% 3.04/0.99  --abstr_ref                             []
% 3.04/0.99  --abstr_ref_prep                        false
% 3.04/0.99  --abstr_ref_until_sat                   false
% 3.04/0.99  --abstr_ref_sig_restrict                funpre
% 3.04/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.04/0.99  --abstr_ref_under                       []
% 3.04/0.99  
% 3.04/0.99  ------ SAT Options
% 3.04/0.99  
% 3.04/0.99  --sat_mode                              false
% 3.04/0.99  --sat_fm_restart_options                ""
% 3.04/0.99  --sat_gr_def                            false
% 3.04/0.99  --sat_epr_types                         true
% 3.04/0.99  --sat_non_cyclic_types                  false
% 3.04/0.99  --sat_finite_models                     false
% 3.04/0.99  --sat_fm_lemmas                         false
% 3.04/0.99  --sat_fm_prep                           false
% 3.04/0.99  --sat_fm_uc_incr                        true
% 3.04/0.99  --sat_out_model                         small
% 3.04/0.99  --sat_out_clauses                       false
% 3.04/0.99  
% 3.04/0.99  ------ QBF Options
% 3.04/0.99  
% 3.04/0.99  --qbf_mode                              false
% 3.04/0.99  --qbf_elim_univ                         false
% 3.04/0.99  --qbf_dom_inst                          none
% 3.04/0.99  --qbf_dom_pre_inst                      false
% 3.04/0.99  --qbf_sk_in                             false
% 3.04/0.99  --qbf_pred_elim                         true
% 3.04/0.99  --qbf_split                             512
% 3.04/0.99  
% 3.04/0.99  ------ BMC1 Options
% 3.04/0.99  
% 3.04/0.99  --bmc1_incremental                      false
% 3.04/0.99  --bmc1_axioms                           reachable_all
% 3.04/0.99  --bmc1_min_bound                        0
% 3.04/0.99  --bmc1_max_bound                        -1
% 3.04/0.99  --bmc1_max_bound_default                -1
% 3.04/0.99  --bmc1_symbol_reachability              true
% 3.04/0.99  --bmc1_property_lemmas                  false
% 3.04/0.99  --bmc1_k_induction                      false
% 3.04/0.99  --bmc1_non_equiv_states                 false
% 3.04/0.99  --bmc1_deadlock                         false
% 3.04/0.99  --bmc1_ucm                              false
% 3.04/0.99  --bmc1_add_unsat_core                   none
% 3.04/0.99  --bmc1_unsat_core_children              false
% 3.04/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.04/0.99  --bmc1_out_stat                         full
% 3.04/0.99  --bmc1_ground_init                      false
% 3.04/0.99  --bmc1_pre_inst_next_state              false
% 3.04/0.99  --bmc1_pre_inst_state                   false
% 3.04/0.99  --bmc1_pre_inst_reach_state             false
% 3.04/0.99  --bmc1_out_unsat_core                   false
% 3.04/0.99  --bmc1_aig_witness_out                  false
% 3.04/0.99  --bmc1_verbose                          false
% 3.04/0.99  --bmc1_dump_clauses_tptp                false
% 3.04/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.04/0.99  --bmc1_dump_file                        -
% 3.04/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.04/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.04/0.99  --bmc1_ucm_extend_mode                  1
% 3.04/0.99  --bmc1_ucm_init_mode                    2
% 3.04/0.99  --bmc1_ucm_cone_mode                    none
% 3.04/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.04/0.99  --bmc1_ucm_relax_model                  4
% 3.04/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.04/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.04/0.99  --bmc1_ucm_layered_model                none
% 3.04/0.99  --bmc1_ucm_max_lemma_size               10
% 3.04/0.99  
% 3.04/0.99  ------ AIG Options
% 3.04/0.99  
% 3.04/0.99  --aig_mode                              false
% 3.04/0.99  
% 3.04/0.99  ------ Instantiation Options
% 3.04/0.99  
% 3.04/0.99  --instantiation_flag                    true
% 3.04/0.99  --inst_sos_flag                         false
% 3.04/0.99  --inst_sos_phase                        true
% 3.04/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.04/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.04/0.99  --inst_lit_sel_side                     none
% 3.04/0.99  --inst_solver_per_active                1400
% 3.04/0.99  --inst_solver_calls_frac                1.
% 3.04/0.99  --inst_passive_queue_type               priority_queues
% 3.04/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.04/0.99  --inst_passive_queues_freq              [25;2]
% 3.04/0.99  --inst_dismatching                      true
% 3.04/0.99  --inst_eager_unprocessed_to_passive     true
% 3.04/0.99  --inst_prop_sim_given                   true
% 3.04/0.99  --inst_prop_sim_new                     false
% 3.04/0.99  --inst_subs_new                         false
% 3.04/0.99  --inst_eq_res_simp                      false
% 3.04/0.99  --inst_subs_given                       false
% 3.04/0.99  --inst_orphan_elimination               true
% 3.04/0.99  --inst_learning_loop_flag               true
% 3.04/0.99  --inst_learning_start                   3000
% 3.04/0.99  --inst_learning_factor                  2
% 3.04/0.99  --inst_start_prop_sim_after_learn       3
% 3.04/0.99  --inst_sel_renew                        solver
% 3.04/0.99  --inst_lit_activity_flag                true
% 3.04/0.99  --inst_restr_to_given                   false
% 3.04/0.99  --inst_activity_threshold               500
% 3.04/0.99  --inst_out_proof                        true
% 3.04/0.99  
% 3.04/0.99  ------ Resolution Options
% 3.04/0.99  
% 3.04/0.99  --resolution_flag                       false
% 3.04/0.99  --res_lit_sel                           adaptive
% 3.04/0.99  --res_lit_sel_side                      none
% 3.04/0.99  --res_ordering                          kbo
% 3.04/0.99  --res_to_prop_solver                    active
% 3.04/0.99  --res_prop_simpl_new                    false
% 3.04/0.99  --res_prop_simpl_given                  true
% 3.04/0.99  --res_passive_queue_type                priority_queues
% 3.04/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.04/0.99  --res_passive_queues_freq               [15;5]
% 3.04/0.99  --res_forward_subs                      full
% 3.04/0.99  --res_backward_subs                     full
% 3.04/0.99  --res_forward_subs_resolution           true
% 3.04/0.99  --res_backward_subs_resolution          true
% 3.04/0.99  --res_orphan_elimination                true
% 3.04/0.99  --res_time_limit                        2.
% 3.04/0.99  --res_out_proof                         true
% 3.04/0.99  
% 3.04/0.99  ------ Superposition Options
% 3.04/0.99  
% 3.04/0.99  --superposition_flag                    true
% 3.04/0.99  --sup_passive_queue_type                priority_queues
% 3.04/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.04/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.04/0.99  --demod_completeness_check              fast
% 3.04/0.99  --demod_use_ground                      true
% 3.04/0.99  --sup_to_prop_solver                    passive
% 3.04/0.99  --sup_prop_simpl_new                    true
% 3.04/0.99  --sup_prop_simpl_given                  true
% 3.04/0.99  --sup_fun_splitting                     false
% 3.04/0.99  --sup_smt_interval                      50000
% 3.04/0.99  
% 3.04/0.99  ------ Superposition Simplification Setup
% 3.04/0.99  
% 3.04/0.99  --sup_indices_passive                   []
% 3.04/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.04/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.04/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.04/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.04/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.04/0.99  --sup_full_bw                           [BwDemod]
% 3.04/0.99  --sup_immed_triv                        [TrivRules]
% 3.04/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.04/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.04/0.99  --sup_immed_bw_main                     []
% 3.04/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.04/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.04/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.04/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.04/0.99  
% 3.04/0.99  ------ Combination Options
% 3.04/0.99  
% 3.04/0.99  --comb_res_mult                         3
% 3.04/0.99  --comb_sup_mult                         2
% 3.04/0.99  --comb_inst_mult                        10
% 3.04/0.99  
% 3.04/0.99  ------ Debug Options
% 3.04/0.99  
% 3.04/0.99  --dbg_backtrace                         false
% 3.04/0.99  --dbg_dump_prop_clauses                 false
% 3.04/0.99  --dbg_dump_prop_clauses_file            -
% 3.04/0.99  --dbg_out_stat                          false
% 3.04/0.99  
% 3.04/0.99  
% 3.04/0.99  
% 3.04/0.99  
% 3.04/0.99  ------ Proving...
% 3.04/0.99  
% 3.04/0.99  
% 3.04/0.99  % SZS status Theorem for theBenchmark.p
% 3.04/0.99  
% 3.04/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.04/0.99  
% 3.04/0.99  fof(f23,conjecture,(
% 3.04/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_relset_1(X0,X1,X2,X3) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 3.04/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f24,negated_conjecture,(
% 3.04/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_relset_1(X0,X1,X2,X3) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 3.04/0.99    inference(negated_conjecture,[],[f23])).
% 3.04/0.99  
% 3.04/0.99  fof(f49,plain,(
% 3.04/0.99    ? [X0,X1,X2] : (? [X3] : (((~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_partfun1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.04/0.99    inference(ennf_transformation,[],[f24])).
% 3.04/0.99  
% 3.04/0.99  fof(f50,plain,(
% 3.04/0.99    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.04/0.99    inference(flattening,[],[f49])).
% 3.04/0.99  
% 3.04/0.99  fof(f62,plain,(
% 3.04/0.99    ( ! [X2,X0,X1] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (~r2_relset_1(X0,X1,X2,sK6) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,sK6) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(sK6,X0,X1) & v1_funct_1(sK6))) )),
% 3.04/0.99    introduced(choice_axiom,[])).
% 3.04/0.99  
% 3.04/0.99  fof(f61,plain,(
% 3.04/0.99    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK3,sK4,sK5,X3) & (k1_xboole_0 = sK3 | k1_xboole_0 != sK4) & r1_partfun1(sK5,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(X3,sK3,sK4) & v1_funct_1(X3)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5))),
% 3.04/0.99    introduced(choice_axiom,[])).
% 3.04/0.99  
% 3.04/0.99  fof(f63,plain,(
% 3.04/0.99    (~r2_relset_1(sK3,sK4,sK5,sK6) & (k1_xboole_0 = sK3 | k1_xboole_0 != sK4) & r1_partfun1(sK5,sK6) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK6,sK3,sK4) & v1_funct_1(sK6)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5)),
% 3.04/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f50,f62,f61])).
% 3.04/0.99  
% 3.04/0.99  fof(f99,plain,(
% 3.04/0.99    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 3.04/0.99    inference(cnf_transformation,[],[f63])).
% 3.04/0.99  
% 3.04/0.99  fof(f22,axiom,(
% 3.04/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 3.04/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f47,plain,(
% 3.04/0.99    ! [X0,X1,X2] : (! [X3] : ((r2_relset_1(X0,X1,X2,X3) | ? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & r2_hidden(X4,X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.04/0.99    inference(ennf_transformation,[],[f22])).
% 3.04/0.99  
% 3.04/0.99  fof(f48,plain,(
% 3.04/0.99    ! [X0,X1,X2] : (! [X3] : (r2_relset_1(X0,X1,X2,X3) | ? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & r2_hidden(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.04/0.99    inference(flattening,[],[f47])).
% 3.04/0.99  
% 3.04/0.99  fof(f59,plain,(
% 3.04/0.99    ! [X3,X2,X0] : (? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & r2_hidden(X4,X0)) => (k1_funct_1(X2,sK2(X0,X2,X3)) != k1_funct_1(X3,sK2(X0,X2,X3)) & r2_hidden(sK2(X0,X2,X3),X0)))),
% 3.04/0.99    introduced(choice_axiom,[])).
% 3.04/0.99  
% 3.04/0.99  fof(f60,plain,(
% 3.04/0.99    ! [X0,X1,X2] : (! [X3] : (r2_relset_1(X0,X1,X2,X3) | (k1_funct_1(X2,sK2(X0,X2,X3)) != k1_funct_1(X3,sK2(X0,X2,X3)) & r2_hidden(sK2(X0,X2,X3),X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.04/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f48,f59])).
% 3.04/0.99  
% 3.04/0.99  fof(f96,plain,(
% 3.04/0.99    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | k1_funct_1(X2,sK2(X0,X2,X3)) != k1_funct_1(X3,sK2(X0,X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.04/0.99    inference(cnf_transformation,[],[f60])).
% 3.04/0.99  
% 3.04/0.99  fof(f97,plain,(
% 3.04/0.99    v1_funct_1(sK5)),
% 3.04/0.99    inference(cnf_transformation,[],[f63])).
% 3.04/0.99  
% 3.04/0.99  fof(f98,plain,(
% 3.04/0.99    v1_funct_2(sK5,sK3,sK4)),
% 3.04/0.99    inference(cnf_transformation,[],[f63])).
% 3.04/0.99  
% 3.04/0.99  fof(f102,plain,(
% 3.04/0.99    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 3.04/0.99    inference(cnf_transformation,[],[f63])).
% 3.04/0.99  
% 3.04/0.99  fof(f20,axiom,(
% 3.04/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.04/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f43,plain,(
% 3.04/0.99    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.04/0.99    inference(ennf_transformation,[],[f20])).
% 3.04/0.99  
% 3.04/0.99  fof(f44,plain,(
% 3.04/0.99    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.04/0.99    inference(flattening,[],[f43])).
% 3.04/0.99  
% 3.04/0.99  fof(f92,plain,(
% 3.04/0.99    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.04/0.99    inference(cnf_transformation,[],[f44])).
% 3.04/0.99  
% 3.04/0.99  fof(f100,plain,(
% 3.04/0.99    v1_funct_1(sK6)),
% 3.04/0.99    inference(cnf_transformation,[],[f63])).
% 3.04/0.99  
% 3.04/0.99  fof(f101,plain,(
% 3.04/0.99    v1_funct_2(sK6,sK3,sK4)),
% 3.04/0.99    inference(cnf_transformation,[],[f63])).
% 3.04/0.99  
% 3.04/0.99  fof(f21,axiom,(
% 3.04/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ((r1_partfun1(X2,X3) & v1_partfun1(X3,X0) & v1_partfun1(X2,X0)) => X2 = X3)))),
% 3.04/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f45,plain,(
% 3.04/0.99    ! [X0,X1,X2] : (! [X3] : ((X2 = X3 | (~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.04/0.99    inference(ennf_transformation,[],[f21])).
% 3.04/0.99  
% 3.04/0.99  fof(f46,plain,(
% 3.04/0.99    ! [X0,X1,X2] : (! [X3] : (X2 = X3 | ~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.04/0.99    inference(flattening,[],[f45])).
% 3.04/0.99  
% 3.04/0.99  fof(f94,plain,(
% 3.04/0.99    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.04/0.99    inference(cnf_transformation,[],[f46])).
% 3.04/0.99  
% 3.04/0.99  fof(f103,plain,(
% 3.04/0.99    r1_partfun1(sK5,sK6)),
% 3.04/0.99    inference(cnf_transformation,[],[f63])).
% 3.04/0.99  
% 3.04/0.99  fof(f9,axiom,(
% 3.04/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.04/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f30,plain,(
% 3.04/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.04/0.99    inference(ennf_transformation,[],[f9])).
% 3.04/0.99  
% 3.04/0.99  fof(f76,plain,(
% 3.04/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.04/0.99    inference(cnf_transformation,[],[f30])).
% 3.04/0.99  
% 3.04/0.99  fof(f11,axiom,(
% 3.04/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.04/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f79,plain,(
% 3.04/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.04/0.99    inference(cnf_transformation,[],[f11])).
% 3.04/0.99  
% 3.04/0.99  fof(f19,axiom,(
% 3.04/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1) & v1_funct_1(X0) & v1_relat_1(X0)) => (r1_partfun1(X0,X1) => r1_partfun1(X1,X0)))),
% 3.04/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f41,plain,(
% 3.04/0.99    ! [X0,X1] : ((r1_partfun1(X1,X0) | ~r1_partfun1(X0,X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.04/0.99    inference(ennf_transformation,[],[f19])).
% 3.04/0.99  
% 3.04/0.99  fof(f42,plain,(
% 3.04/0.99    ! [X0,X1] : (r1_partfun1(X1,X0) | ~r1_partfun1(X0,X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.04/0.99    inference(flattening,[],[f41])).
% 3.04/0.99  
% 3.04/0.99  fof(f91,plain,(
% 3.04/0.99    ( ! [X0,X1] : (r1_partfun1(X1,X0) | ~r1_partfun1(X0,X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.04/0.99    inference(cnf_transformation,[],[f42])).
% 3.04/0.99  
% 3.04/0.99  fof(f105,plain,(
% 3.04/0.99    ~r2_relset_1(sK3,sK4,sK5,sK6)),
% 3.04/0.99    inference(cnf_transformation,[],[f63])).
% 3.04/0.99  
% 3.04/0.99  fof(f17,axiom,(
% 3.04/0.99    ! [X0,X1] : ((v1_xboole_0(X1) & ~v1_xboole_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~v1_partfun1(X2,X0)))),
% 3.04/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f37,plain,(
% 3.04/0.99    ! [X0,X1] : (! [X2] : (~v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | (~v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 3.04/0.99    inference(ennf_transformation,[],[f17])).
% 3.04/0.99  
% 3.04/0.99  fof(f38,plain,(
% 3.04/0.99    ! [X0,X1] : (! [X2] : (~v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X1) | v1_xboole_0(X0))),
% 3.04/0.99    inference(flattening,[],[f37])).
% 3.04/0.99  
% 3.04/0.99  fof(f88,plain,(
% 3.04/0.99    ( ! [X2,X0,X1] : (~v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.04/0.99    inference(cnf_transformation,[],[f38])).
% 3.04/0.99  
% 3.04/0.99  fof(f95,plain,(
% 3.04/0.99    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | r2_hidden(sK2(X0,X2,X3),X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.04/0.99    inference(cnf_transformation,[],[f60])).
% 3.04/0.99  
% 3.04/0.99  fof(f1,axiom,(
% 3.04/0.99    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.04/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f51,plain,(
% 3.04/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.04/0.99    inference(nnf_transformation,[],[f1])).
% 3.04/0.99  
% 3.04/0.99  fof(f52,plain,(
% 3.04/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.04/0.99    inference(rectify,[],[f51])).
% 3.04/0.99  
% 3.04/0.99  fof(f53,plain,(
% 3.04/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.04/0.99    introduced(choice_axiom,[])).
% 3.04/0.99  
% 3.04/0.99  fof(f54,plain,(
% 3.04/0.99    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.04/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f52,f53])).
% 3.04/0.99  
% 3.04/0.99  fof(f64,plain,(
% 3.04/0.99    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.04/0.99    inference(cnf_transformation,[],[f54])).
% 3.04/0.99  
% 3.04/0.99  fof(f104,plain,(
% 3.04/0.99    k1_xboole_0 = sK3 | k1_xboole_0 != sK4),
% 3.04/0.99    inference(cnf_transformation,[],[f63])).
% 3.04/0.99  
% 3.04/0.99  fof(f93,plain,(
% 3.04/0.99    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.04/0.99    inference(cnf_transformation,[],[f44])).
% 3.04/0.99  
% 3.04/0.99  fof(f106,plain,(
% 3.04/0.99    ( ! [X2,X1] : (v1_partfun1(X2,k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_1(X2)) )),
% 3.04/0.99    inference(equality_resolution,[],[f93])).
% 3.04/0.99  
% 3.04/0.99  fof(f2,axiom,(
% 3.04/0.99    v1_xboole_0(k1_xboole_0)),
% 3.04/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f66,plain,(
% 3.04/0.99    v1_xboole_0(k1_xboole_0)),
% 3.04/0.99    inference(cnf_transformation,[],[f2])).
% 3.04/0.99  
% 3.04/0.99  cnf(c_39,negated_conjecture,
% 3.04/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 3.04/0.99      inference(cnf_transformation,[],[f99]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1745,plain,
% 3.04/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_31,plain,
% 3.04/0.99      ( r2_relset_1(X0,X1,X2,X3)
% 3.04/0.99      | ~ v1_funct_2(X2,X0,X1)
% 3.04/0.99      | ~ v1_funct_2(X3,X0,X1)
% 3.04/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.04/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.04/0.99      | ~ v1_funct_1(X2)
% 3.04/0.99      | ~ v1_funct_1(X3)
% 3.04/0.99      | k1_funct_1(X3,sK2(X0,X2,X3)) != k1_funct_1(X2,sK2(X0,X2,X3)) ),
% 3.04/0.99      inference(cnf_transformation,[],[f96]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1752,plain,
% 3.04/0.99      ( k1_funct_1(X0,sK2(X1,X2,X0)) != k1_funct_1(X2,sK2(X1,X2,X0))
% 3.04/0.99      | r2_relset_1(X1,X3,X2,X0) = iProver_top
% 3.04/0.99      | v1_funct_2(X2,X1,X3) != iProver_top
% 3.04/0.99      | v1_funct_2(X0,X1,X3) != iProver_top
% 3.04/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
% 3.04/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
% 3.04/0.99      | v1_funct_1(X2) != iProver_top
% 3.04/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3510,plain,
% 3.04/0.99      ( r2_relset_1(X0,X1,X2,X2) = iProver_top
% 3.04/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.04/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.04/0.99      | v1_funct_1(X2) != iProver_top ),
% 3.04/0.99      inference(equality_resolution,[status(thm)],[c_1752]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_8091,plain,
% 3.04/0.99      ( r2_relset_1(sK3,sK4,sK5,sK5) = iProver_top
% 3.04/0.99      | v1_funct_2(sK5,sK3,sK4) != iProver_top
% 3.04/0.99      | v1_funct_1(sK5) != iProver_top ),
% 3.04/0.99      inference(superposition,[status(thm)],[c_1745,c_3510]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_41,negated_conjecture,
% 3.04/0.99      ( v1_funct_1(sK5) ),
% 3.04/0.99      inference(cnf_transformation,[],[f97]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_42,plain,
% 3.04/0.99      ( v1_funct_1(sK5) = iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_40,negated_conjecture,
% 3.04/0.99      ( v1_funct_2(sK5,sK3,sK4) ),
% 3.04/0.99      inference(cnf_transformation,[],[f98]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_43,plain,
% 3.04/0.99      ( v1_funct_2(sK5,sK3,sK4) = iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_9197,plain,
% 3.04/0.99      ( r2_relset_1(sK3,sK4,sK5,sK5) = iProver_top ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_8091,c_42,c_43]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_36,negated_conjecture,
% 3.04/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 3.04/0.99      inference(cnf_transformation,[],[f102]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1748,plain,
% 3.04/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_29,plain,
% 3.04/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.04/0.99      | v1_partfun1(X0,X1)
% 3.04/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.04/0.99      | ~ v1_funct_1(X0)
% 3.04/0.99      | k1_xboole_0 = X2 ),
% 3.04/0.99      inference(cnf_transformation,[],[f92]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1754,plain,
% 3.04/0.99      ( k1_xboole_0 = X0
% 3.04/0.99      | v1_funct_2(X1,X2,X0) != iProver_top
% 3.04/0.99      | v1_partfun1(X1,X2) = iProver_top
% 3.04/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 3.04/0.99      | v1_funct_1(X1) != iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_5377,plain,
% 3.04/0.99      ( sK4 = k1_xboole_0
% 3.04/0.99      | v1_funct_2(sK6,sK3,sK4) != iProver_top
% 3.04/0.99      | v1_partfun1(sK6,sK3) = iProver_top
% 3.04/0.99      | v1_funct_1(sK6) != iProver_top ),
% 3.04/0.99      inference(superposition,[status(thm)],[c_1748,c_1754]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_38,negated_conjecture,
% 3.04/0.99      ( v1_funct_1(sK6) ),
% 3.04/0.99      inference(cnf_transformation,[],[f100]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_45,plain,
% 3.04/0.99      ( v1_funct_1(sK6) = iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_37,negated_conjecture,
% 3.04/0.99      ( v1_funct_2(sK6,sK3,sK4) ),
% 3.04/0.99      inference(cnf_transformation,[],[f101]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_46,plain,
% 3.04/0.99      ( v1_funct_2(sK6,sK3,sK4) = iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_5704,plain,
% 3.04/0.99      ( v1_partfun1(sK6,sK3) = iProver_top | sK4 = k1_xboole_0 ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_5377,c_45,c_46]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_5705,plain,
% 3.04/0.99      ( sK4 = k1_xboole_0 | v1_partfun1(sK6,sK3) = iProver_top ),
% 3.04/0.99      inference(renaming,[status(thm)],[c_5704]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_30,plain,
% 3.04/0.99      ( ~ r1_partfun1(X0,X1)
% 3.04/0.99      | ~ v1_partfun1(X0,X2)
% 3.04/0.99      | ~ v1_partfun1(X1,X2)
% 3.04/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 3.04/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 3.04/0.99      | ~ v1_funct_1(X0)
% 3.04/0.99      | ~ v1_funct_1(X1)
% 3.04/0.99      | X1 = X0 ),
% 3.04/0.99      inference(cnf_transformation,[],[f94]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1753,plain,
% 3.04/0.99      ( X0 = X1
% 3.04/0.99      | r1_partfun1(X1,X0) != iProver_top
% 3.04/0.99      | v1_partfun1(X1,X2) != iProver_top
% 3.04/0.99      | v1_partfun1(X0,X2) != iProver_top
% 3.04/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 3.04/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 3.04/0.99      | v1_funct_1(X1) != iProver_top
% 3.04/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_4585,plain,
% 3.04/0.99      ( sK6 = X0
% 3.04/0.99      | r1_partfun1(sK6,X0) != iProver_top
% 3.04/0.99      | v1_partfun1(X0,sK3) != iProver_top
% 3.04/0.99      | v1_partfun1(sK6,sK3) != iProver_top
% 3.04/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 3.04/0.99      | v1_funct_1(X0) != iProver_top
% 3.04/0.99      | v1_funct_1(sK6) != iProver_top ),
% 3.04/0.99      inference(superposition,[status(thm)],[c_1748,c_1753]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_5135,plain,
% 3.04/0.99      ( v1_funct_1(X0) != iProver_top
% 3.04/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 3.04/0.99      | v1_partfun1(sK6,sK3) != iProver_top
% 3.04/0.99      | v1_partfun1(X0,sK3) != iProver_top
% 3.04/0.99      | r1_partfun1(sK6,X0) != iProver_top
% 3.04/0.99      | sK6 = X0 ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_4585,c_45]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_5136,plain,
% 3.04/0.99      ( sK6 = X0
% 3.04/0.99      | r1_partfun1(sK6,X0) != iProver_top
% 3.04/0.99      | v1_partfun1(X0,sK3) != iProver_top
% 3.04/0.99      | v1_partfun1(sK6,sK3) != iProver_top
% 3.04/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 3.04/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.04/0.99      inference(renaming,[status(thm)],[c_5135]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_5148,plain,
% 3.04/0.99      ( sK6 = sK5
% 3.04/0.99      | r1_partfun1(sK6,sK5) != iProver_top
% 3.04/0.99      | v1_partfun1(sK6,sK3) != iProver_top
% 3.04/0.99      | v1_partfun1(sK5,sK3) != iProver_top
% 3.04/0.99      | v1_funct_1(sK5) != iProver_top ),
% 3.04/0.99      inference(superposition,[status(thm)],[c_1745,c_5136]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_44,plain,
% 3.04/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_47,plain,
% 3.04/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_35,negated_conjecture,
% 3.04/0.99      ( r1_partfun1(sK5,sK6) ),
% 3.04/0.99      inference(cnf_transformation,[],[f103]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_48,plain,
% 3.04/0.99      ( r1_partfun1(sK5,sK6) = iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_12,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.04/0.99      | ~ v1_relat_1(X1)
% 3.04/0.99      | v1_relat_1(X0) ),
% 3.04/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2093,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.04/0.99      | v1_relat_1(X0)
% 3.04/0.99      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_12]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2840,plain,
% 3.04/0.99      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 3.04/0.99      | ~ v1_relat_1(k2_zfmisc_1(sK3,sK4))
% 3.04/0.99      | v1_relat_1(sK6) ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_2093]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2841,plain,
% 3.04/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 3.04/0.99      | v1_relat_1(k2_zfmisc_1(sK3,sK4)) != iProver_top
% 3.04/0.99      | v1_relat_1(sK6) = iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_2840]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2843,plain,
% 3.04/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 3.04/0.99      | ~ v1_relat_1(k2_zfmisc_1(sK3,sK4))
% 3.04/0.99      | v1_relat_1(sK5) ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_2093]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2844,plain,
% 3.04/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 3.04/0.99      | v1_relat_1(k2_zfmisc_1(sK3,sK4)) != iProver_top
% 3.04/0.99      | v1_relat_1(sK5) = iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_2843]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_15,plain,
% 3.04/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.04/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3185,plain,
% 3.04/0.99      ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_15]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3186,plain,
% 3.04/0.99      ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) = iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_3185]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_27,plain,
% 3.04/0.99      ( ~ r1_partfun1(X0,X1)
% 3.04/0.99      | r1_partfun1(X1,X0)
% 3.04/0.99      | ~ v1_funct_1(X0)
% 3.04/0.99      | ~ v1_funct_1(X1)
% 3.04/0.99      | ~ v1_relat_1(X0)
% 3.04/0.99      | ~ v1_relat_1(X1) ),
% 3.04/0.99      inference(cnf_transformation,[],[f91]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2147,plain,
% 3.04/0.99      ( r1_partfun1(X0,sK5)
% 3.04/0.99      | ~ r1_partfun1(sK5,X0)
% 3.04/0.99      | ~ v1_funct_1(X0)
% 3.04/0.99      | ~ v1_funct_1(sK5)
% 3.04/0.99      | ~ v1_relat_1(X0)
% 3.04/0.99      | ~ v1_relat_1(sK5) ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_27]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3412,plain,
% 3.04/0.99      ( r1_partfun1(sK6,sK5)
% 3.04/0.99      | ~ r1_partfun1(sK5,sK6)
% 3.04/0.99      | ~ v1_funct_1(sK6)
% 3.04/0.99      | ~ v1_funct_1(sK5)
% 3.04/0.99      | ~ v1_relat_1(sK6)
% 3.04/0.99      | ~ v1_relat_1(sK5) ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_2147]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3413,plain,
% 3.04/0.99      ( r1_partfun1(sK6,sK5) = iProver_top
% 3.04/0.99      | r1_partfun1(sK5,sK6) != iProver_top
% 3.04/0.99      | v1_funct_1(sK6) != iProver_top
% 3.04/0.99      | v1_funct_1(sK5) != iProver_top
% 3.04/0.99      | v1_relat_1(sK6) != iProver_top
% 3.04/0.99      | v1_relat_1(sK5) != iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_3412]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_5161,plain,
% 3.04/0.99      ( v1_partfun1(sK5,sK3) != iProver_top
% 3.04/0.99      | v1_partfun1(sK6,sK3) != iProver_top
% 3.04/0.99      | sK6 = sK5 ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_5148,c_42,c_44,c_45,c_47,c_48,c_2841,c_2844,c_3186,
% 3.04/0.99                 c_3413]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_5162,plain,
% 3.04/0.99      ( sK6 = sK5
% 3.04/0.99      | v1_partfun1(sK6,sK3) != iProver_top
% 3.04/0.99      | v1_partfun1(sK5,sK3) != iProver_top ),
% 3.04/0.99      inference(renaming,[status(thm)],[c_5161]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_5710,plain,
% 3.04/0.99      ( sK6 = sK5
% 3.04/0.99      | sK4 = k1_xboole_0
% 3.04/0.99      | v1_partfun1(sK5,sK3) != iProver_top ),
% 3.04/0.99      inference(superposition,[status(thm)],[c_5705,c_5162]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_5378,plain,
% 3.04/0.99      ( sK4 = k1_xboole_0
% 3.04/0.99      | v1_funct_2(sK5,sK3,sK4) != iProver_top
% 3.04/0.99      | v1_partfun1(sK5,sK3) = iProver_top
% 3.04/0.99      | v1_funct_1(sK5) != iProver_top ),
% 3.04/0.99      inference(superposition,[status(thm)],[c_1745,c_1754]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_5852,plain,
% 3.04/0.99      ( v1_partfun1(sK5,sK3) = iProver_top | sK4 = k1_xboole_0 ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_5378,c_42,c_43]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_5853,plain,
% 3.04/0.99      ( sK4 = k1_xboole_0 | v1_partfun1(sK5,sK3) = iProver_top ),
% 3.04/0.99      inference(renaming,[status(thm)],[c_5852]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_6043,plain,
% 3.04/0.99      ( sK4 = k1_xboole_0 | sK6 = sK5 ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_5710,c_5853]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_6044,plain,
% 3.04/0.99      ( sK6 = sK5 | sK4 = k1_xboole_0 ),
% 3.04/0.99      inference(renaming,[status(thm)],[c_6043]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_33,negated_conjecture,
% 3.04/0.99      ( ~ r2_relset_1(sK3,sK4,sK5,sK6) ),
% 3.04/0.99      inference(cnf_transformation,[],[f105]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1750,plain,
% 3.04/0.99      ( r2_relset_1(sK3,sK4,sK5,sK6) != iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_6056,plain,
% 3.04/0.99      ( sK4 = k1_xboole_0 | r2_relset_1(sK3,sK4,sK5,sK5) != iProver_top ),
% 3.04/0.99      inference(superposition,[status(thm)],[c_6044,c_1750]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_9202,plain,
% 3.04/0.99      ( sK4 = k1_xboole_0 ),
% 3.04/0.99      inference(superposition,[status(thm)],[c_9197,c_6056]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_24,plain,
% 3.04/0.99      ( ~ v1_partfun1(X0,X1)
% 3.04/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.04/0.99      | ~ v1_xboole_0(X2)
% 3.04/0.99      | v1_xboole_0(X1) ),
% 3.04/0.99      inference(cnf_transformation,[],[f88]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1758,plain,
% 3.04/0.99      ( v1_partfun1(X0,X1) != iProver_top
% 3.04/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.04/0.99      | v1_xboole_0(X2) != iProver_top
% 3.04/0.99      | v1_xboole_0(X1) = iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_6333,plain,
% 3.04/0.99      ( v1_partfun1(sK6,sK3) != iProver_top
% 3.04/0.99      | v1_xboole_0(sK4) != iProver_top
% 3.04/0.99      | v1_xboole_0(sK3) = iProver_top ),
% 3.04/0.99      inference(superposition,[status(thm)],[c_1748,c_1758]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_32,plain,
% 3.04/0.99      ( r2_relset_1(X0,X1,X2,X3)
% 3.04/0.99      | ~ v1_funct_2(X2,X0,X1)
% 3.04/0.99      | ~ v1_funct_2(X3,X0,X1)
% 3.04/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.04/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.04/0.99      | r2_hidden(sK2(X0,X2,X3),X0)
% 3.04/0.99      | ~ v1_funct_1(X2)
% 3.04/0.99      | ~ v1_funct_1(X3) ),
% 3.04/0.99      inference(cnf_transformation,[],[f95]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1751,plain,
% 3.04/0.99      ( r2_relset_1(X0,X1,X2,X3) = iProver_top
% 3.04/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.04/0.99      | v1_funct_2(X3,X0,X1) != iProver_top
% 3.04/0.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.04/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.04/0.99      | r2_hidden(sK2(X0,X2,X3),X0) = iProver_top
% 3.04/0.99      | v1_funct_1(X2) != iProver_top
% 3.04/0.99      | v1_funct_1(X3) != iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2917,plain,
% 3.04/0.99      ( r2_relset_1(sK3,sK4,X0,sK6) = iProver_top
% 3.04/0.99      | v1_funct_2(X0,sK3,sK4) != iProver_top
% 3.04/0.99      | v1_funct_2(sK6,sK3,sK4) != iProver_top
% 3.04/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 3.04/0.99      | r2_hidden(sK2(sK3,X0,sK6),sK3) = iProver_top
% 3.04/0.99      | v1_funct_1(X0) != iProver_top
% 3.04/0.99      | v1_funct_1(sK6) != iProver_top ),
% 3.04/0.99      inference(superposition,[status(thm)],[c_1748,c_1751]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3192,plain,
% 3.04/0.99      ( v1_funct_1(X0) != iProver_top
% 3.04/0.99      | r2_hidden(sK2(sK3,X0,sK6),sK3) = iProver_top
% 3.04/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 3.04/0.99      | r2_relset_1(sK3,sK4,X0,sK6) = iProver_top
% 3.04/0.99      | v1_funct_2(X0,sK3,sK4) != iProver_top ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_2917,c_45,c_46]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3193,plain,
% 3.04/0.99      ( r2_relset_1(sK3,sK4,X0,sK6) = iProver_top
% 3.04/0.99      | v1_funct_2(X0,sK3,sK4) != iProver_top
% 3.04/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 3.04/0.99      | r2_hidden(sK2(sK3,X0,sK6),sK3) = iProver_top
% 3.04/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.04/0.99      inference(renaming,[status(thm)],[c_3192]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3204,plain,
% 3.04/0.99      ( r2_relset_1(sK3,sK4,sK5,sK6) = iProver_top
% 3.04/0.99      | v1_funct_2(sK5,sK3,sK4) != iProver_top
% 3.04/0.99      | r2_hidden(sK2(sK3,sK5,sK6),sK3) = iProver_top
% 3.04/0.99      | v1_funct_1(sK5) != iProver_top ),
% 3.04/0.99      inference(superposition,[status(thm)],[c_1745,c_3193]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_49,plain,
% 3.04/0.99      ( r2_relset_1(sK3,sK4,sK5,sK6) != iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3264,plain,
% 3.04/0.99      ( r2_hidden(sK2(sK3,sK5,sK6),sK3) = iProver_top ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_3204,c_42,c_43,c_49]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1,plain,
% 3.04/0.99      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.04/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1777,plain,
% 3.04/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.04/0.99      | v1_xboole_0(X1) != iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3269,plain,
% 3.04/0.99      ( v1_xboole_0(sK3) != iProver_top ),
% 3.04/0.99      inference(superposition,[status(thm)],[c_3264,c_1777]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_6492,plain,
% 3.04/0.99      ( v1_xboole_0(sK4) != iProver_top
% 3.04/0.99      | v1_partfun1(sK6,sK3) != iProver_top ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_6333,c_3269]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_6493,plain,
% 3.04/0.99      ( v1_partfun1(sK6,sK3) != iProver_top
% 3.04/0.99      | v1_xboole_0(sK4) != iProver_top ),
% 3.04/0.99      inference(renaming,[status(thm)],[c_6492]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_9296,plain,
% 3.04/0.99      ( v1_partfun1(sK6,sK3) != iProver_top
% 3.04/0.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.04/0.99      inference(demodulation,[status(thm)],[c_9202,c_6493]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_34,negated_conjecture,
% 3.04/0.99      ( k1_xboole_0 != sK4 | k1_xboole_0 = sK3 ),
% 3.04/0.99      inference(cnf_transformation,[],[f104]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_9307,plain,
% 3.04/0.99      ( sK3 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 3.04/0.99      inference(demodulation,[status(thm)],[c_9202,c_34]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_9308,plain,
% 3.04/0.99      ( sK3 = k1_xboole_0 ),
% 3.04/0.99      inference(equality_resolution_simp,[status(thm)],[c_9307]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_9379,plain,
% 3.04/0.99      ( v1_partfun1(sK6,k1_xboole_0) != iProver_top
% 3.04/0.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.04/0.99      inference(light_normalisation,[status(thm)],[c_9296,c_9308]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_9303,plain,
% 3.04/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) = iProver_top ),
% 3.04/0.99      inference(demodulation,[status(thm)],[c_9202,c_1748]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_9320,plain,
% 3.04/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 3.04/0.99      inference(light_normalisation,[status(thm)],[c_9303,c_9308]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_831,plain,
% 3.04/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.04/0.99      | v1_funct_2(X3,X4,X5)
% 3.04/0.99      | X3 != X0
% 3.04/0.99      | X4 != X1
% 3.04/0.99      | X5 != X2 ),
% 3.04/0.99      theory(equality) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2180,plain,
% 3.04/0.99      ( v1_funct_2(X0,X1,X2)
% 3.04/0.99      | ~ v1_funct_2(sK6,sK3,sK4)
% 3.04/0.99      | X0 != sK6
% 3.04/0.99      | X2 != sK4
% 3.04/0.99      | X1 != sK3 ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_831]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2670,plain,
% 3.04/0.99      ( v1_funct_2(sK6,X0,X1)
% 3.04/0.99      | ~ v1_funct_2(sK6,sK3,sK4)
% 3.04/0.99      | X1 != sK4
% 3.04/0.99      | X0 != sK3
% 3.04/0.99      | sK6 != sK6 ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_2180]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2673,plain,
% 3.04/0.99      ( X0 != sK4
% 3.04/0.99      | X1 != sK3
% 3.04/0.99      | sK6 != sK6
% 3.04/0.99      | v1_funct_2(sK6,X1,X0) = iProver_top
% 3.04/0.99      | v1_funct_2(sK6,sK3,sK4) != iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_2670]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2675,plain,
% 3.04/0.99      ( sK6 != sK6
% 3.04/0.99      | k1_xboole_0 != sK4
% 3.04/0.99      | k1_xboole_0 != sK3
% 3.04/0.99      | v1_funct_2(sK6,sK3,sK4) != iProver_top
% 3.04/0.99      | v1_funct_2(sK6,k1_xboole_0,k1_xboole_0) = iProver_top ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_2673]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_814,plain,( X0 = X0 ),theory(equality) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2353,plain,
% 3.04/0.99      ( sK6 = sK6 ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_814]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_815,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2136,plain,
% 3.04/0.99      ( sK4 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK4 ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_815]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2137,plain,
% 3.04/0.99      ( sK4 != k1_xboole_0
% 3.04/0.99      | k1_xboole_0 = sK4
% 3.04/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_2136]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_28,plain,
% 3.04/0.99      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 3.04/0.99      | v1_partfun1(X0,k1_xboole_0)
% 3.04/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.04/0.99      | ~ v1_funct_1(X0) ),
% 3.04/0.99      inference(cnf_transformation,[],[f106]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2126,plain,
% 3.04/0.99      ( ~ v1_funct_2(sK6,k1_xboole_0,X0)
% 3.04/0.99      | v1_partfun1(sK6,k1_xboole_0)
% 3.04/0.99      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
% 3.04/0.99      | ~ v1_funct_1(sK6) ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_28]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2127,plain,
% 3.04/0.99      ( v1_funct_2(sK6,k1_xboole_0,X0) != iProver_top
% 3.04/0.99      | v1_partfun1(sK6,k1_xboole_0) = iProver_top
% 3.04/0.99      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top
% 3.04/0.99      | v1_funct_1(sK6) != iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_2126]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2129,plain,
% 3.04/0.99      ( v1_funct_2(sK6,k1_xboole_0,k1_xboole_0) != iProver_top
% 3.04/0.99      | v1_partfun1(sK6,k1_xboole_0) = iProver_top
% 3.04/0.99      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 3.04/0.99      | v1_funct_1(sK6) != iProver_top ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_2127]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_855,plain,
% 3.04/0.99      ( k1_xboole_0 = k1_xboole_0 ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_814]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2,plain,
% 3.04/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 3.04/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_112,plain,
% 3.04/0.99      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(contradiction,plain,
% 3.04/0.99      ( $false ),
% 3.04/0.99      inference(minisat,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_9379,c_9320,c_8091,c_6056,c_2675,c_2353,c_2137,c_2129,
% 3.04/0.99                 c_855,c_112,c_34,c_46,c_45,c_43,c_42]) ).
% 3.04/0.99  
% 3.04/0.99  
% 3.04/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.04/0.99  
% 3.04/0.99  ------                               Statistics
% 3.04/0.99  
% 3.04/0.99  ------ General
% 3.04/0.99  
% 3.04/0.99  abstr_ref_over_cycles:                  0
% 3.04/0.99  abstr_ref_under_cycles:                 0
% 3.04/0.99  gc_basic_clause_elim:                   0
% 3.04/0.99  forced_gc_time:                         0
% 3.04/0.99  parsing_time:                           0.018
% 3.04/0.99  unif_index_cands_time:                  0.
% 3.04/0.99  unif_index_add_time:                    0.
% 3.04/0.99  orderings_time:                         0.
% 3.04/0.99  out_proof_time:                         0.011
% 3.04/0.99  total_time:                             0.326
% 3.04/0.99  num_of_symbols:                         58
% 3.04/0.99  num_of_terms:                           10542
% 3.04/0.99  
% 3.04/0.99  ------ Preprocessing
% 3.04/0.99  
% 3.04/0.99  num_of_splits:                          0
% 3.04/0.99  num_of_split_atoms:                     0
% 3.04/0.99  num_of_reused_defs:                     0
% 3.04/0.99  num_eq_ax_congr_red:                    36
% 3.04/0.99  num_of_sem_filtered_clauses:            1
% 3.04/0.99  num_of_subtypes:                        0
% 3.04/0.99  monotx_restored_types:                  0
% 3.04/0.99  sat_num_of_epr_types:                   0
% 3.04/0.99  sat_num_of_non_cyclic_types:            0
% 3.04/0.99  sat_guarded_non_collapsed_types:        0
% 3.04/0.99  num_pure_diseq_elim:                    0
% 3.04/0.99  simp_replaced_by:                       0
% 3.04/0.99  res_preprocessed:                       207
% 3.04/0.99  prep_upred:                             0
% 3.04/0.99  prep_unflattend:                        0
% 3.04/0.99  smt_new_axioms:                         0
% 3.04/0.99  pred_elim_cands:                        10
% 3.04/0.99  pred_elim:                              0
% 3.04/0.99  pred_elim_cl:                           0
% 3.04/0.99  pred_elim_cycles:                       2
% 3.04/0.99  merged_defs:                            8
% 3.04/0.99  merged_defs_ncl:                        0
% 3.04/0.99  bin_hyper_res:                          8
% 3.04/0.99  prep_cycles:                            4
% 3.04/0.99  pred_elim_time:                         0.001
% 3.04/0.99  splitting_time:                         0.
% 3.04/0.99  sem_filter_time:                        0.
% 3.04/0.99  monotx_time:                            0.001
% 3.04/0.99  subtype_inf_time:                       0.
% 3.04/0.99  
% 3.04/0.99  ------ Problem properties
% 3.04/0.99  
% 3.04/0.99  clauses:                                41
% 3.04/0.99  conjectures:                            9
% 3.04/0.99  epr:                                    12
% 3.04/0.99  horn:                                   35
% 3.04/0.99  ground:                                 12
% 3.04/0.99  unary:                                  15
% 3.04/0.99  binary:                                 10
% 3.04/0.99  lits:                                   109
% 3.04/0.99  lits_eq:                                18
% 3.04/0.99  fd_pure:                                0
% 3.04/0.99  fd_pseudo:                              0
% 3.04/0.99  fd_cond:                                1
% 3.04/0.99  fd_pseudo_cond:                         2
% 3.04/0.99  ac_symbols:                             0
% 3.04/0.99  
% 3.04/0.99  ------ Propositional Solver
% 3.04/0.99  
% 3.04/0.99  prop_solver_calls:                      28
% 3.04/0.99  prop_fast_solver_calls:                 1466
% 3.04/0.99  smt_solver_calls:                       0
% 3.04/0.99  smt_fast_solver_calls:                  0
% 3.04/0.99  prop_num_of_clauses:                    3763
% 3.04/0.99  prop_preprocess_simplified:             11917
% 3.04/0.99  prop_fo_subsumed:                       46
% 3.04/0.99  prop_solver_time:                       0.
% 3.04/0.99  smt_solver_time:                        0.
% 3.04/0.99  smt_fast_solver_time:                   0.
% 3.04/0.99  prop_fast_solver_time:                  0.
% 3.04/0.99  prop_unsat_core_time:                   0.
% 3.04/0.99  
% 3.04/0.99  ------ QBF
% 3.04/0.99  
% 3.04/0.99  qbf_q_res:                              0
% 3.04/0.99  qbf_num_tautologies:                    0
% 3.04/0.99  qbf_prep_cycles:                        0
% 3.04/0.99  
% 3.04/0.99  ------ BMC1
% 3.04/0.99  
% 3.04/0.99  bmc1_current_bound:                     -1
% 3.04/0.99  bmc1_last_solved_bound:                 -1
% 3.04/0.99  bmc1_unsat_core_size:                   -1
% 3.04/0.99  bmc1_unsat_core_parents_size:           -1
% 3.04/0.99  bmc1_merge_next_fun:                    0
% 3.04/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.04/0.99  
% 3.04/0.99  ------ Instantiation
% 3.04/0.99  
% 3.04/0.99  inst_num_of_clauses:                    1068
% 3.04/0.99  inst_num_in_passive:                    637
% 3.04/0.99  inst_num_in_active:                     400
% 3.04/0.99  inst_num_in_unprocessed:                31
% 3.04/0.99  inst_num_of_loops:                      520
% 3.04/0.99  inst_num_of_learning_restarts:          0
% 3.04/0.99  inst_num_moves_active_passive:          118
% 3.04/0.99  inst_lit_activity:                      0
% 3.04/0.99  inst_lit_activity_moves:                0
% 3.04/0.99  inst_num_tautologies:                   0
% 3.04/0.99  inst_num_prop_implied:                  0
% 3.04/0.99  inst_num_existing_simplified:           0
% 3.04/0.99  inst_num_eq_res_simplified:             0
% 3.04/0.99  inst_num_child_elim:                    0
% 3.04/0.99  inst_num_of_dismatching_blockings:      175
% 3.04/0.99  inst_num_of_non_proper_insts:           914
% 3.04/0.99  inst_num_of_duplicates:                 0
% 3.04/0.99  inst_inst_num_from_inst_to_res:         0
% 3.04/0.99  inst_dismatching_checking_time:         0.
% 3.04/0.99  
% 3.04/0.99  ------ Resolution
% 3.04/0.99  
% 3.04/0.99  res_num_of_clauses:                     0
% 3.04/0.99  res_num_in_passive:                     0
% 3.04/0.99  res_num_in_active:                      0
% 3.04/0.99  res_num_of_loops:                       211
% 3.04/0.99  res_forward_subset_subsumed:            32
% 3.04/0.99  res_backward_subset_subsumed:           0
% 3.04/0.99  res_forward_subsumed:                   0
% 3.04/0.99  res_backward_subsumed:                  0
% 3.04/0.99  res_forward_subsumption_resolution:     0
% 3.04/0.99  res_backward_subsumption_resolution:    0
% 3.04/0.99  res_clause_to_clause_subsumption:       257
% 3.04/0.99  res_orphan_elimination:                 0
% 3.04/0.99  res_tautology_del:                      50
% 3.04/0.99  res_num_eq_res_simplified:              0
% 3.04/0.99  res_num_sel_changes:                    0
% 3.04/0.99  res_moves_from_active_to_pass:          0
% 3.04/0.99  
% 3.04/0.99  ------ Superposition
% 3.04/0.99  
% 3.04/0.99  sup_time_total:                         0.
% 3.04/0.99  sup_time_generating:                    0.
% 3.04/0.99  sup_time_sim_full:                      0.
% 3.04/0.99  sup_time_sim_immed:                     0.
% 3.04/0.99  
% 3.04/0.99  sup_num_of_clauses:                     104
% 3.04/0.99  sup_num_in_active:                      68
% 3.04/0.99  sup_num_in_passive:                     36
% 3.04/0.99  sup_num_of_loops:                       102
% 3.04/0.99  sup_fw_superposition:                   81
% 3.04/0.99  sup_bw_superposition:                   75
% 3.04/0.99  sup_immediate_simplified:               59
% 3.04/0.99  sup_given_eliminated:                   0
% 3.04/0.99  comparisons_done:                       0
% 3.04/0.99  comparisons_avoided:                    12
% 3.04/0.99  
% 3.04/0.99  ------ Simplifications
% 3.04/0.99  
% 3.04/0.99  
% 3.04/0.99  sim_fw_subset_subsumed:                 26
% 3.04/0.99  sim_bw_subset_subsumed:                 9
% 3.04/0.99  sim_fw_subsumed:                        10
% 3.04/0.99  sim_bw_subsumed:                        2
% 3.04/0.99  sim_fw_subsumption_res:                 1
% 3.04/0.99  sim_bw_subsumption_res:                 1
% 3.04/0.99  sim_tautology_del:                      13
% 3.04/0.99  sim_eq_tautology_del:                   5
% 3.04/0.99  sim_eq_res_simp:                        1
% 3.04/0.99  sim_fw_demodulated:                     2
% 3.04/0.99  sim_bw_demodulated:                     26
% 3.04/0.99  sim_light_normalised:                   19
% 3.04/0.99  sim_joinable_taut:                      0
% 3.04/0.99  sim_joinable_simp:                      0
% 3.04/0.99  sim_ac_normalised:                      0
% 3.04/0.99  sim_smt_subsumption:                    0
% 3.04/0.99  
%------------------------------------------------------------------------------
