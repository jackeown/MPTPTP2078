%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:06:48 EST 2020

% Result     : Theorem 11.60s
% Output     : CNFRefutation 11.60s
% Verified   : 
% Statistics : Number of formulae       :  288 (2667 expanded)
%              Number of clauses        :  182 ( 757 expanded)
%              Number of leaves         :   32 ( 685 expanded)
%              Depth                    :   24
%              Number of atoms          :  975 (17602 expanded)
%              Number of equality atoms :  409 (1378 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f27,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
         => ( ( v2_funct_1(X1)
              & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1) )
           => r2_relset_1(X0,X0,X2,k6_partfun1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_2(X2,X0,X0)
              & v1_funct_1(X2) )
           => ( ( v2_funct_1(X1)
                & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1) )
             => r2_relset_1(X0,X0,X2,k6_partfun1(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f27])).

fof(f68,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k6_partfun1(X0))
          & v2_funct_1(X1)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f69,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k6_partfun1(X0))
          & v2_funct_1(X1)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f68])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k6_partfun1(X0))
          & v2_funct_1(X1)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
     => ( ~ r2_relset_1(X0,X0,sK4,k6_partfun1(X0))
        & v2_funct_1(X1)
        & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,sK4,X1),X1)
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(sK4,X0,X0)
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f75,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r2_relset_1(X0,X0,X2,k6_partfun1(X0))
            & v2_funct_1(X1)
            & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ? [X2] :
          ( ~ r2_relset_1(sK2,sK2,X2,k6_partfun1(sK2))
          & v2_funct_1(sK3)
          & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,X2,sK3),sK3)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
          & v1_funct_2(X2,sK2,sK2)
          & v1_funct_1(X2) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      & v1_funct_2(sK3,sK2,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f77,plain,
    ( ~ r2_relset_1(sK2,sK2,sK4,k6_partfun1(sK2))
    & v2_funct_1(sK3)
    & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3),sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    & v1_funct_2(sK4,sK2,sK2)
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    & v1_funct_2(sK3,sK2,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f69,f76,f75])).

fof(f123,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f77])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f37,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f36])).

fof(f88,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
          & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f43,plain,(
    ! [X0] :
      ( ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f42])).

fof(f94,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f86,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f87,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f47,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f46])).

fof(f97,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f116,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f77])).

fof(f118,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f77])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f41,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f40])).

fof(f92,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f66])).

fof(f115,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f117,plain,(
    v1_funct_2(sK3,sK2,sK2) ),
    inference(cnf_transformation,[],[f77])).

fof(f121,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f77])).

fof(f23,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f61,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f60])).

fof(f111,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f54,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f53])).

fof(f72,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f54])).

fof(f102,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f122,plain,(
    r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3),sK3) ),
    inference(cnf_transformation,[],[f77])).

fof(f119,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f77])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f59,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f58])).

fof(f109,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( ( k5_relat_1(X2,X1) = X1
              & v2_funct_1(X1)
              & r1_tarski(k2_relat_1(X2),X0)
              & k1_relat_1(X2) = X0
              & k1_relat_1(X1) = X0 )
           => k6_relat_1(X0) = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k6_relat_1(X0) = X2
          | k5_relat_1(X2,X1) != X1
          | ~ v2_funct_1(X1)
          | ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X0
          | k1_relat_1(X1) != X0
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k6_relat_1(X0) = X2
          | k5_relat_1(X2,X1) != X1
          | ~ v2_funct_1(X1)
          | ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X0
          | k1_relat_1(X1) != X0
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f38])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( k6_relat_1(X0) = X2
      | k5_relat_1(X2,X1) != X1
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(k2_relat_1(X2),X0)
      | k1_relat_1(X2) != X0
      | k1_relat_1(X1) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f125,plain,(
    ! [X2,X1] :
      ( k6_relat_1(k1_relat_1(X2)) = X2
      | k5_relat_1(X2,X1) != X1
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(k2_relat_1(X2),k1_relat_1(X2))
      | k1_relat_1(X1) != k1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f89])).

fof(f120,plain,(
    v1_funct_2(sK4,sK2,sK2) ),
    inference(cnf_transformation,[],[f77])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f25,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => r1_tarski(k7_relset_1(X0,X1,X3,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k7_relset_1(X0,X1,X3,X2),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f65,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k7_relset_1(X0,X1,X3,X2),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f64])).

fof(f114,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k7_relset_1(X0,X1,X3,X2),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f45,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f44])).

fof(f95,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f80,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f9,axiom,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f90,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
            & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f62])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
         => ( ! [X3] :
                ( r2_hidden(X3,X0)
               => k11_relat_1(X1,X3) = k11_relat_1(X2,X3) )
           => r2_relset_1(X0,X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_relset_1(X0,X0,X1,X2)
          | ? [X3] :
              ( k11_relat_1(X1,X3) != k11_relat_1(X2,X3)
              & r2_hidden(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_relset_1(X0,X0,X1,X2)
          | ? [X3] :
              ( k11_relat_1(X1,X3) != k11_relat_1(X2,X3)
              & r2_hidden(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(flattening,[],[f56])).

fof(f73,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k11_relat_1(X1,X3) != k11_relat_1(X2,X3)
          & r2_hidden(X3,X0) )
     => ( k11_relat_1(X1,sK1(X0,X1,X2)) != k11_relat_1(X2,sK1(X0,X1,X2))
        & r2_hidden(sK1(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_relset_1(X0,X0,X1,X2)
          | ( k11_relat_1(X1,sK1(X0,X1,X2)) != k11_relat_1(X2,sK1(X0,X1,X2))
            & r2_hidden(sK1(X0,X1,X2),X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f57,f73])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( r2_relset_1(X0,X0,X1,X2)
      | r2_hidden(sK1(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f22,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f22])).

fof(f110,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f29])).

fof(f1,axiom,(
    ! [X0] :
    ? [X1] :
      ( v1_xboole_0(X1)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( v1_xboole_0(sK0(X0))
        & m1_subset_1(sK0(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f71,plain,(
    ! [X0] :
      ( v1_xboole_0(sK0(X0))
      & m1_subset_1(sK0(X0),k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f1,f70])).

fof(f78,plain,(
    ! [X0] : m1_subset_1(sK0(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f71])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f81,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f124,plain,(
    ~ r2_relset_1(sK2,sK2,sK4,k6_partfun1(sK2)) ),
    inference(cnf_transformation,[],[f77])).

fof(f103,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f126,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f103])).

fof(f79,plain,(
    ! [X0] : v1_xboole_0(sK0(X0)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_8178,plain,
    ( ~ r2_hidden(X0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0(X1)))
    | ~ v1_xboole_0(sK0(X1)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_30017,plain,
    ( ~ r2_hidden(sK1(sK2,sK3,k6_partfun1(sK2)),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0(X0)))
    | ~ v1_xboole_0(sK0(X0)) ),
    inference(instantiation,[status(thm)],[c_8178])).

cnf(c_39,negated_conjecture,
    ( v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_1730,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_8,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1750,plain,
    ( v2_funct_1(X0) != iProver_top
    | v2_funct_1(k2_funct_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_15,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1745,plain,
    ( k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0)
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_5353,plain,
    ( k2_relat_1(k5_relat_1(k2_funct_1(k2_funct_1(X0)),k2_funct_1(X0))) = k2_relat_1(k2_funct_1(X0))
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1750,c_1745])).

cnf(c_10,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_137,plain,
    ( v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_9,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_140,plain,
    ( v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_26153,plain,
    ( v1_funct_1(X0) != iProver_top
    | k2_relat_1(k5_relat_1(k2_funct_1(k2_funct_1(X0)),k2_funct_1(X0))) = k2_relat_1(k2_funct_1(X0))
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5353,c_137,c_140])).

cnf(c_26154,plain,
    ( k2_relat_1(k5_relat_1(k2_funct_1(k2_funct_1(X0)),k2_funct_1(X0))) = k2_relat_1(k2_funct_1(X0))
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_26153])).

cnf(c_26161,plain,
    ( k2_relat_1(k5_relat_1(k2_funct_1(k2_funct_1(sK3)),k2_funct_1(sK3))) = k2_relat_1(k2_funct_1(sK3))
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1730,c_26154])).

cnf(c_19,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_funct_1(k2_funct_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1741,plain,
    ( k2_funct_1(k2_funct_1(X0)) = X0
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4124,plain,
    ( k2_funct_1(k2_funct_1(sK3)) = sK3
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1730,c_1741])).

cnf(c_46,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_47,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_54,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_2469,plain,
    ( ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | k2_funct_1(k2_funct_1(sK3)) = sK3 ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_2470,plain,
    ( k2_funct_1(k2_funct_1(sK3)) = sK3
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2469])).

cnf(c_44,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_1727,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1739,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2683,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1727,c_1739])).

cnf(c_4424,plain,
    ( k2_funct_1(k2_funct_1(sK3)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4124,c_47,c_54,c_2470,c_2683])).

cnf(c_13,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1747,plain,
    ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_4558,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1730,c_1747])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1738,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2758,plain,
    ( k1_relset_1(sK2,sK2,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1727,c_1738])).

cnf(c_37,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k1_relset_1(X1,X1,X0) = X1 ),
    inference(cnf_transformation,[],[f115])).

cnf(c_45,negated_conjecture,
    ( v1_funct_2(sK3,sK2,sK2) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_910,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k1_relset_1(X1,X1,X0) = X1
    | sK3 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_37,c_45])).

cnf(c_911,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(sK3)
    | k1_relset_1(sK2,sK2,sK3) = sK2 ),
    inference(unflattening,[status(thm)],[c_910])).

cnf(c_913,plain,
    ( k1_relset_1(sK2,sK2,sK3) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_911,c_46,c_44])).

cnf(c_2759,plain,
    ( k1_relat_1(sK3) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_2758,c_913])).

cnf(c_4559,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = sK2
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4558,c_2759])).

cnf(c_5082,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4559,c_47,c_2683])).

cnf(c_41,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_1729,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_33,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_1731,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_5369,plain,
    ( k1_partfun1(X0,X1,sK2,sK2,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1727,c_1731])).

cnf(c_5680,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK2,sK2,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5369,c_47])).

cnf(c_5681,plain,
    ( k1_partfun1(X0,X1,sK2,sK2,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_5680])).

cnf(c_5690,plain,
    ( k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3) = k5_relat_1(sK4,sK3)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1729,c_5681])).

cnf(c_25,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f102])).

cnf(c_40,negated_conjecture,
    ( r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3),sK3) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_661,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3) != X0
    | sK3 != X3
    | sK2 != X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_40])).

cnf(c_662,plain,
    ( ~ m1_subset_1(k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3) ),
    inference(unflattening,[status(thm)],[c_661])).

cnf(c_664,plain,
    ( ~ m1_subset_1(k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_662,c_44])).

cnf(c_1723,plain,
    ( sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3)
    | m1_subset_1(k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_664])).

cnf(c_43,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_30,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_1839,plain,
    ( m1_subset_1(k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_2481,plain,
    ( sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1723,c_46,c_44,c_43,c_41,c_662,c_1839])).

cnf(c_5692,plain,
    ( k5_relat_1(sK4,sK3) = sK3
    | v1_funct_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5690,c_2481])).

cnf(c_50,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_6025,plain,
    ( k5_relat_1(sK4,sK3) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5692,c_50])).

cnf(c_11,plain,
    ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X0))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | k5_relat_1(X0,X1) != X1
    | k6_relat_1(k1_relat_1(X0)) = X0
    | k1_relat_1(X1) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_1749,plain,
    ( k5_relat_1(X0,X1) != X1
    | k6_relat_1(k1_relat_1(X0)) = X0
    | k1_relat_1(X1) != k1_relat_1(X0)
    | r1_tarski(k2_relat_1(X0),k1_relat_1(X0)) != iProver_top
    | v2_funct_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_6027,plain,
    ( k6_relat_1(k1_relat_1(sK4)) = sK4
    | k1_relat_1(sK4) != k1_relat_1(sK3)
    | r1_tarski(k2_relat_1(sK4),k1_relat_1(sK4)) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6025,c_1749])).

cnf(c_2757,plain,
    ( k1_relset_1(sK2,sK2,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1729,c_1738])).

cnf(c_42,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK2) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_902,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k1_relset_1(X1,X1,X0) = X1
    | sK4 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_37,c_42])).

cnf(c_903,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(sK4)
    | k1_relset_1(sK2,sK2,sK4) = sK2 ),
    inference(unflattening,[status(thm)],[c_902])).

cnf(c_905,plain,
    ( k1_relset_1(sK2,sK2,sK4) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_903,c_43,c_41])).

cnf(c_2760,plain,
    ( k1_relat_1(sK4) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_2757,c_905])).

cnf(c_6028,plain,
    ( k6_relat_1(sK2) = sK4
    | sK2 != sK2
    | r1_tarski(k2_relat_1(sK4),sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6027,c_2759,c_2760])).

cnf(c_6029,plain,
    ( k6_relat_1(sK2) = sK4
    | r1_tarski(k2_relat_1(sK4),sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_6028])).

cnf(c_2682,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1729,c_1739])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X1) = k2_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1735,plain,
    ( k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_3542,plain,
    ( k7_relset_1(sK2,sK2,sK4,sK2) = k2_relset_1(sK2,sK2,sK4) ),
    inference(superposition,[status(thm)],[c_1729,c_1735])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1737,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2748,plain,
    ( k2_relset_1(sK2,sK2,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1729,c_1737])).

cnf(c_3545,plain,
    ( k7_relset_1(sK2,sK2,sK4,sK2) = k2_relat_1(sK4) ),
    inference(light_normalisation,[status(thm)],[c_3542,c_2748])).

cnf(c_36,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | r1_tarski(k7_relset_1(X1,X2,X0,X3),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_804,plain,
    ( r1_tarski(k7_relset_1(X0,X1,X2,X3),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | sK4 != X2
    | sK2 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_36,c_42])).

cnf(c_805,plain,
    ( r1_tarski(k7_relset_1(sK2,sK2,sK4,X0),sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(sK4) ),
    inference(unflattening,[status(thm)],[c_804])).

cnf(c_809,plain,
    ( r1_tarski(k7_relset_1(sK2,sK2,sK4,X0),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_805,c_43,c_41])).

cnf(c_1721,plain,
    ( r1_tarski(k7_relset_1(sK2,sK2,sK4,X0),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_809])).

cnf(c_3756,plain,
    ( r1_tarski(k2_relat_1(sK4),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3545,c_1721])).

cnf(c_19383,plain,
    ( k6_relat_1(sK2) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6029,c_47,c_50,c_54,c_2682,c_2683,c_3756])).

cnf(c_18,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1742,plain,
    ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4692,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_relat_1(k1_relat_1(sK3))
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1730,c_1742])).

cnf(c_4693,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_relat_1(sK2)
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4692,c_2759])).

cnf(c_5107,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4693,c_47,c_2683])).

cnf(c_19387,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = sK4 ),
    inference(demodulation,[status(thm)],[c_19383,c_5107])).

cnf(c_26164,plain,
    ( k2_relat_1(sK4) = sK2
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_26161,c_4424,c_5082,c_19387])).

cnf(c_8267,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(sK0(sK0(X2))))
    | ~ v1_xboole_0(sK0(sK0(X2))) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_16234,plain,
    ( ~ r2_hidden(sK1(sK2,sK3,sK4),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(sK0(sK0(X1))))
    | ~ v1_xboole_0(sK0(sK0(X1))) ),
    inference(instantiation,[status(thm)],[c_8267])).

cnf(c_23537,plain,
    ( ~ r2_hidden(sK1(sK2,sK3,sK4),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0(sK0(X0))))
    | ~ v1_xboole_0(sK0(sK0(X0))) ),
    inference(instantiation,[status(thm)],[c_16234])).

cnf(c_1031,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_22641,plain,
    ( sK1(sK2,sK3,sK4) = sK1(sK2,sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1031])).

cnf(c_2,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_3500,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0(X0))) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_20411,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0(sK0(X0)))) ),
    inference(instantiation,[status(thm)],[c_3500])).

cnf(c_12,plain,
    ( v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1748,plain,
    ( v2_funct_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4691,plain,
    ( k5_relat_1(k6_relat_1(X0),k2_funct_1(k6_relat_1(X0))) = k6_relat_1(k1_relat_1(k6_relat_1(X0)))
    | v1_relat_1(k6_relat_1(X0)) != iProver_top
    | v1_funct_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1748,c_1742])).

cnf(c_19393,plain,
    ( k5_relat_1(k6_relat_1(sK2),k2_funct_1(k6_relat_1(sK2))) = k6_relat_1(k1_relat_1(k6_relat_1(sK2)))
    | v1_relat_1(sK4) != iProver_top
    | v1_funct_1(k6_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_19383,c_4691])).

cnf(c_19413,plain,
    ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_relat_1(k1_relat_1(sK4))
    | v1_relat_1(sK4) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_19393,c_19383])).

cnf(c_19414,plain,
    ( k5_relat_1(sK4,k2_funct_1(sK4)) = sK4
    | v1_relat_1(sK4) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_19413,c_2760,c_19383])).

cnf(c_19539,plain,
    ( k5_relat_1(sK4,k2_funct_1(sK4)) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_19414,c_50,c_2682])).

cnf(c_35,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f112])).

cnf(c_819,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | sK4 != X0
    | sK2 != X1
    | sK2 != X2
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_35,c_42])).

cnf(c_820,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v2_funct_1(sK4)
    | ~ v1_funct_1(sK4)
    | k2_relset_1(sK2,sK2,sK4) != sK2
    | k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(sK2)
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_819])).

cnf(c_822,plain,
    ( ~ v2_funct_1(sK4)
    | k2_relset_1(sK2,sK2,sK4) != sK2
    | k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(sK2)
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_820,c_43,c_41])).

cnf(c_1720,plain,
    ( k2_relset_1(sK2,sK2,sK4) != sK2
    | k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(sK2)
    | k1_xboole_0 = sK2
    | v2_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_822])).

cnf(c_3082,plain,
    ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(sK2)
    | k2_relat_1(sK4) != sK2
    | sK2 = k1_xboole_0
    | v2_funct_1(sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2748,c_1720])).

cnf(c_19541,plain,
    ( k6_partfun1(sK2) = sK4
    | k2_relat_1(sK4) != sK2
    | sK2 = k1_xboole_0
    | v2_funct_1(sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_19539,c_3082])).

cnf(c_19542,plain,
    ( ~ v2_funct_1(sK4)
    | k6_partfun1(sK2) = sK4
    | k2_relat_1(sK4) != sK2
    | sK2 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_19541])).

cnf(c_1032,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1947,plain,
    ( X0 != X1
    | sK4 != X1
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_1032])).

cnf(c_2156,plain,
    ( X0 != sK4
    | sK4 = X0
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1947])).

cnf(c_17732,plain,
    ( k6_relat_1(X0) != sK4
    | sK4 = k6_relat_1(X0)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_2156])).

cnf(c_17736,plain,
    ( k6_relat_1(sK2) != sK4
    | sK4 = k6_relat_1(sK2)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_17732])).

cnf(c_1036,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3476,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK1(X2,sK3,k6_partfun1(sK2)),X2)
    | X1 != X2
    | X0 != sK1(X2,sK3,k6_partfun1(sK2)) ),
    inference(instantiation,[status(thm)],[c_1036])).

cnf(c_6297,plain,
    ( ~ r2_hidden(sK1(X0,sK3,k6_partfun1(sK2)),X0)
    | r2_hidden(sK1(X0,sK3,k6_partfun1(sK2)),X1)
    | X1 != X0
    | sK1(X0,sK3,k6_partfun1(sK2)) != sK1(X0,sK3,k6_partfun1(sK2)) ),
    inference(instantiation,[status(thm)],[c_3476])).

cnf(c_12111,plain,
    ( ~ r2_hidden(sK1(X0,sK3,k6_partfun1(sK2)),X0)
    | r2_hidden(sK1(X0,sK3,k6_partfun1(sK2)),k1_xboole_0)
    | sK1(X0,sK3,k6_partfun1(sK2)) != sK1(X0,sK3,k6_partfun1(sK2))
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_6297])).

cnf(c_12114,plain,
    ( ~ r2_hidden(sK1(sK2,sK3,k6_partfun1(sK2)),sK2)
    | r2_hidden(sK1(sK2,sK3,k6_partfun1(sK2)),k1_xboole_0)
    | sK1(sK2,sK3,k6_partfun1(sK2)) != sK1(sK2,sK3,k6_partfun1(sK2))
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_12111])).

cnf(c_3479,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK1(sK2,sK3,sK4),sK2)
    | X0 != sK1(sK2,sK3,sK4)
    | X1 != sK2 ),
    inference(instantiation,[status(thm)],[c_1036])).

cnf(c_5432,plain,
    ( r2_hidden(sK1(sK2,sK3,sK4),X0)
    | ~ r2_hidden(sK1(sK2,sK3,sK4),sK2)
    | X0 != sK2
    | sK1(sK2,sK3,sK4) != sK1(sK2,sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_3479])).

cnf(c_9860,plain,
    ( ~ r2_hidden(sK1(sK2,sK3,sK4),sK2)
    | r2_hidden(sK1(sK2,sK3,sK4),k1_xboole_0)
    | sK1(sK2,sK3,sK4) != sK1(sK2,sK3,sK4)
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_5432])).

cnf(c_4198,plain,
    ( X0 != X1
    | k1_xboole_0 != X1
    | k1_xboole_0 = X0 ),
    inference(instantiation,[status(thm)],[c_1032])).

cnf(c_8135,plain,
    ( X0 != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4198])).

cnf(c_8136,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8135])).

cnf(c_5947,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1031])).

cnf(c_29,plain,
    ( r2_relset_1(X0,X0,X1,X2)
    | r2_hidden(sK1(X0,X1,X2),X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_625,plain,
    ( r2_hidden(sK1(X0,X1,X2),X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | X0 != X4
    | X0 != X5
    | X1 != X3
    | X2 != X6
    | X6 = X3 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_29])).

cnf(c_626,plain,
    ( r2_hidden(sK1(X0,X1,X2),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | X2 = X1 ),
    inference(unflattening,[status(thm)],[c_625])).

cnf(c_1725,plain,
    ( X0 = X1
    | r2_hidden(sK1(X2,X1,X0),X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_626])).

cnf(c_3936,plain,
    ( sK3 = X0
    | r2_hidden(sK1(sK2,sK3,X0),sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1727,c_1725])).

cnf(c_4810,plain,
    ( sK3 = sK4
    | r2_hidden(sK1(sK2,sK3,sK4),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1729,c_3936])).

cnf(c_4815,plain,
    ( r2_hidden(sK1(sK2,sK3,sK4),sK2)
    | sK3 = sK4 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4810])).

cnf(c_32,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_1732,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_4809,plain,
    ( k6_partfun1(sK2) = sK3
    | r2_hidden(sK1(sK2,sK3,k6_partfun1(sK2)),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1732,c_3936])).

cnf(c_4814,plain,
    ( r2_hidden(sK1(sK2,sK3,k6_partfun1(sK2)),sK2)
    | k6_partfun1(sK2) = sK3 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4809])).

cnf(c_4529,plain,
    ( sK1(X0,sK3,k6_partfun1(sK2)) = sK1(X0,sK3,k6_partfun1(sK2)) ),
    inference(instantiation,[status(thm)],[c_1031])).

cnf(c_4530,plain,
    ( sK1(sK2,sK3,k6_partfun1(sK2)) = sK1(sK2,sK3,k6_partfun1(sK2)) ),
    inference(instantiation,[status(thm)],[c_4529])).

cnf(c_1,plain,
    ( m1_subset_1(sK0(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_3974,plain,
    ( m1_subset_1(sK0(sK0(X0)),k1_zfmisc_1(sK0(X0))) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2131,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0(X1)))
    | v1_xboole_0(X0)
    | ~ v1_xboole_0(sK0(X1)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2802,plain,
    ( ~ m1_subset_1(sK0(sK0(X0)),k1_zfmisc_1(sK0(X0)))
    | ~ v1_xboole_0(sK0(X0))
    | v1_xboole_0(sK0(sK0(X0))) ),
    inference(instantiation,[status(thm)],[c_2131])).

cnf(c_38,negated_conjecture,
    ( ~ r2_relset_1(sK2,sK2,sK4,k6_partfun1(sK2)) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_694,plain,
    ( k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3) != sK4
    | k6_partfun1(sK2) != sK3
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_38,c_40])).

cnf(c_1759,plain,
    ( k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3) != sK4
    | k6_partfun1(sK2) != sK3 ),
    inference(equality_resolution_simp,[status(thm)],[c_694])).

cnf(c_2483,plain,
    ( k6_partfun1(sK2) != sK3
    | sK3 != sK4 ),
    inference(demodulation,[status(thm)],[c_2481,c_1759])).

cnf(c_2072,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_1031])).

cnf(c_1040,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1863,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(sK4)
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_1040])).

cnf(c_1998,plain,
    ( ~ v2_funct_1(k6_relat_1(X0))
    | v2_funct_1(sK4)
    | sK4 != k6_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_1863])).

cnf(c_2000,plain,
    ( ~ v2_funct_1(k6_relat_1(sK2))
    | v2_funct_1(sK4)
    | sK4 != k6_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1998])).

cnf(c_1828,plain,
    ( k6_partfun1(sK2) != X0
    | sK4 != X0
    | sK4 = k6_partfun1(sK2) ),
    inference(instantiation,[status(thm)],[c_1032])).

cnf(c_1940,plain,
    ( k6_partfun1(sK2) != sK4
    | sK4 = k6_partfun1(sK2)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1828])).

cnf(c_24,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f126])).

cnf(c_617,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k6_partfun1(sK2) != X0
    | sK4 != X0
    | sK2 != X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_38])).

cnf(c_618,plain,
    ( ~ m1_subset_1(k6_partfun1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | sK4 != k6_partfun1(sK2) ),
    inference(unflattening,[status(thm)],[c_617])).

cnf(c_0,plain,
    ( v1_xboole_0(sK0(X0)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_132,plain,
    ( v2_funct_1(k6_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_72,plain,
    ( m1_subset_1(k6_partfun1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_30022,plain,
    ( ~ r2_hidden(sK1(sK2,sK3,k6_partfun1(sK2)),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0(sK2)))
    | ~ v1_xboole_0(sK0(sK2)) ),
    inference(grounding,[status(thm)],[c_30017:[bind(X0,$fot(sK2))]])).

cnf(c_30023,plain,
    ( ~ r2_hidden(sK1(sK2,sK3,sK4),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0(sK0(sK2))))
    | ~ v1_xboole_0(sK0(sK0(sK2))) ),
    inference(grounding,[status(thm)],[c_23537:[bind(X0,$fot(sK2))]])).

cnf(c_30024,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0(sK0(sK2)))) ),
    inference(grounding,[status(thm)],[c_20411:[bind(X0,$fot(sK2))]])).

cnf(c_30025,plain,
    ( m1_subset_1(sK0(sK0(sK2)),k1_zfmisc_1(sK0(sK2))) ),
    inference(grounding,[status(thm)],[c_3974:[bind(X0,$fot(sK2))]])).

cnf(c_30026,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0(sK2))) ),
    inference(grounding,[status(thm)],[c_3500:[bind(X0,$fot(sK2))]])).

cnf(c_30027,plain,
    ( ~ m1_subset_1(sK0(sK0(sK2)),k1_zfmisc_1(sK0(sK2)))
    | v1_xboole_0(sK0(sK0(sK2)))
    | ~ v1_xboole_0(sK0(sK2)) ),
    inference(grounding,[status(thm)],[c_2802:[bind(X0,$fot(sK2))]])).

cnf(c_30028,plain,
    ( v1_xboole_0(sK0(sK2)) ),
    inference(grounding,[status(thm)],[c_0:[bind(X0,$fot(sK2))]])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_30022,c_26164,c_30023,c_22641,c_30024,c_19542,c_17736,c_12114,c_9860,c_8136,c_6029,c_5947,c_4815,c_4814,c_4530,c_30025,c_3756,c_30026,c_30027,c_2683,c_2682,c_2483,c_2072,c_2000,c_1940,c_618,c_30028,c_132,c_72,c_54,c_50,c_47])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:28:04 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 11.60/1.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.60/1.98  
% 11.60/1.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.60/1.98  
% 11.60/1.98  ------  iProver source info
% 11.60/1.98  
% 11.60/1.98  git: date: 2020-06-30 10:37:57 +0100
% 11.60/1.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.60/1.98  git: non_committed_changes: false
% 11.60/1.98  git: last_make_outside_of_git: false
% 11.60/1.98  
% 11.60/1.98  ------ 
% 11.60/1.98  
% 11.60/1.98  ------ Input Options
% 11.60/1.98  
% 11.60/1.98  --out_options                           all
% 11.60/1.98  --tptp_safe_out                         true
% 11.60/1.98  --problem_path                          ""
% 11.60/1.98  --include_path                          ""
% 11.60/1.98  --clausifier                            res/vclausify_rel
% 11.60/1.98  --clausifier_options                    ""
% 11.60/1.98  --stdin                                 false
% 11.60/1.98  --stats_out                             all
% 11.60/1.98  
% 11.60/1.98  ------ General Options
% 11.60/1.98  
% 11.60/1.98  --fof                                   false
% 11.60/1.98  --time_out_real                         305.
% 11.60/1.98  --time_out_virtual                      -1.
% 11.60/1.98  --symbol_type_check                     false
% 11.60/1.98  --clausify_out                          false
% 11.60/1.98  --sig_cnt_out                           false
% 11.60/1.98  --trig_cnt_out                          false
% 11.60/1.98  --trig_cnt_out_tolerance                1.
% 11.60/1.98  --trig_cnt_out_sk_spl                   false
% 11.60/1.98  --abstr_cl_out                          false
% 11.60/1.98  
% 11.60/1.98  ------ Global Options
% 11.60/1.98  
% 11.60/1.98  --schedule                              default
% 11.60/1.98  --add_important_lit                     false
% 11.60/1.98  --prop_solver_per_cl                    1000
% 11.60/1.98  --min_unsat_core                        false
% 11.60/1.98  --soft_assumptions                      false
% 11.60/1.98  --soft_lemma_size                       3
% 11.60/1.98  --prop_impl_unit_size                   0
% 11.60/1.98  --prop_impl_unit                        []
% 11.60/1.98  --share_sel_clauses                     true
% 11.60/1.98  --reset_solvers                         false
% 11.60/1.98  --bc_imp_inh                            [conj_cone]
% 11.60/1.98  --conj_cone_tolerance                   3.
% 11.60/1.98  --extra_neg_conj                        none
% 11.60/1.98  --large_theory_mode                     true
% 11.60/1.98  --prolific_symb_bound                   200
% 11.60/1.98  --lt_threshold                          2000
% 11.60/1.98  --clause_weak_htbl                      true
% 11.60/1.98  --gc_record_bc_elim                     false
% 11.60/1.98  
% 11.60/1.98  ------ Preprocessing Options
% 11.60/1.98  
% 11.60/1.98  --preprocessing_flag                    true
% 11.60/1.98  --time_out_prep_mult                    0.1
% 11.60/1.98  --splitting_mode                        input
% 11.60/1.98  --splitting_grd                         true
% 11.60/1.98  --splitting_cvd                         false
% 11.60/1.98  --splitting_cvd_svl                     false
% 11.60/1.98  --splitting_nvd                         32
% 11.60/1.98  --sub_typing                            true
% 11.60/1.98  --prep_gs_sim                           true
% 11.60/1.98  --prep_unflatten                        true
% 11.60/1.98  --prep_res_sim                          true
% 11.60/1.98  --prep_upred                            true
% 11.60/1.98  --prep_sem_filter                       exhaustive
% 11.60/1.98  --prep_sem_filter_out                   false
% 11.60/1.98  --pred_elim                             true
% 11.60/1.98  --res_sim_input                         true
% 11.60/1.98  --eq_ax_congr_red                       true
% 11.60/1.98  --pure_diseq_elim                       true
% 11.60/1.98  --brand_transform                       false
% 11.60/1.98  --non_eq_to_eq                          false
% 11.60/1.98  --prep_def_merge                        true
% 11.60/1.98  --prep_def_merge_prop_impl              false
% 11.60/1.98  --prep_def_merge_mbd                    true
% 11.60/1.98  --prep_def_merge_tr_red                 false
% 11.60/1.98  --prep_def_merge_tr_cl                  false
% 11.60/1.98  --smt_preprocessing                     true
% 11.60/1.98  --smt_ac_axioms                         fast
% 11.60/1.98  --preprocessed_out                      false
% 11.60/1.98  --preprocessed_stats                    false
% 11.60/1.98  
% 11.60/1.98  ------ Abstraction refinement Options
% 11.60/1.98  
% 11.60/1.98  --abstr_ref                             []
% 11.60/1.98  --abstr_ref_prep                        false
% 11.60/1.98  --abstr_ref_until_sat                   false
% 11.60/1.98  --abstr_ref_sig_restrict                funpre
% 11.60/1.98  --abstr_ref_af_restrict_to_split_sk     false
% 11.60/1.98  --abstr_ref_under                       []
% 11.60/1.98  
% 11.60/1.98  ------ SAT Options
% 11.60/1.98  
% 11.60/1.98  --sat_mode                              false
% 11.60/1.98  --sat_fm_restart_options                ""
% 11.60/1.98  --sat_gr_def                            false
% 11.60/1.98  --sat_epr_types                         true
% 11.60/1.98  --sat_non_cyclic_types                  false
% 11.60/1.98  --sat_finite_models                     false
% 11.60/1.98  --sat_fm_lemmas                         false
% 11.60/1.98  --sat_fm_prep                           false
% 11.60/1.98  --sat_fm_uc_incr                        true
% 11.60/1.98  --sat_out_model                         small
% 11.60/1.98  --sat_out_clauses                       false
% 11.60/1.98  
% 11.60/1.98  ------ QBF Options
% 11.60/1.98  
% 11.60/1.98  --qbf_mode                              false
% 11.60/1.98  --qbf_elim_univ                         false
% 11.60/1.98  --qbf_dom_inst                          none
% 11.60/1.98  --qbf_dom_pre_inst                      false
% 11.60/1.98  --qbf_sk_in                             false
% 11.60/1.98  --qbf_pred_elim                         true
% 11.60/1.98  --qbf_split                             512
% 11.60/1.98  
% 11.60/1.98  ------ BMC1 Options
% 11.60/1.98  
% 11.60/1.98  --bmc1_incremental                      false
% 11.60/1.98  --bmc1_axioms                           reachable_all
% 11.60/1.98  --bmc1_min_bound                        0
% 11.60/1.98  --bmc1_max_bound                        -1
% 11.60/1.98  --bmc1_max_bound_default                -1
% 11.60/1.98  --bmc1_symbol_reachability              true
% 11.60/1.98  --bmc1_property_lemmas                  false
% 11.60/1.98  --bmc1_k_induction                      false
% 11.60/1.98  --bmc1_non_equiv_states                 false
% 11.60/1.98  --bmc1_deadlock                         false
% 11.60/1.98  --bmc1_ucm                              false
% 11.60/1.98  --bmc1_add_unsat_core                   none
% 11.60/1.98  --bmc1_unsat_core_children              false
% 11.60/1.98  --bmc1_unsat_core_extrapolate_axioms    false
% 11.60/1.98  --bmc1_out_stat                         full
% 11.60/1.98  --bmc1_ground_init                      false
% 11.60/1.98  --bmc1_pre_inst_next_state              false
% 11.60/1.98  --bmc1_pre_inst_state                   false
% 11.60/1.98  --bmc1_pre_inst_reach_state             false
% 11.60/1.98  --bmc1_out_unsat_core                   false
% 11.60/1.98  --bmc1_aig_witness_out                  false
% 11.60/1.98  --bmc1_verbose                          false
% 11.60/1.98  --bmc1_dump_clauses_tptp                false
% 11.60/1.98  --bmc1_dump_unsat_core_tptp             false
% 11.60/1.98  --bmc1_dump_file                        -
% 11.60/1.98  --bmc1_ucm_expand_uc_limit              128
% 11.60/1.98  --bmc1_ucm_n_expand_iterations          6
% 11.60/1.98  --bmc1_ucm_extend_mode                  1
% 11.60/1.98  --bmc1_ucm_init_mode                    2
% 11.60/1.98  --bmc1_ucm_cone_mode                    none
% 11.60/1.98  --bmc1_ucm_reduced_relation_type        0
% 11.60/1.98  --bmc1_ucm_relax_model                  4
% 11.60/1.98  --bmc1_ucm_full_tr_after_sat            true
% 11.60/1.98  --bmc1_ucm_expand_neg_assumptions       false
% 11.60/1.98  --bmc1_ucm_layered_model                none
% 11.60/1.98  --bmc1_ucm_max_lemma_size               10
% 11.60/1.98  
% 11.60/1.98  ------ AIG Options
% 11.60/1.98  
% 11.60/1.98  --aig_mode                              false
% 11.60/1.98  
% 11.60/1.98  ------ Instantiation Options
% 11.60/1.98  
% 11.60/1.98  --instantiation_flag                    true
% 11.60/1.98  --inst_sos_flag                         true
% 11.60/1.98  --inst_sos_phase                        true
% 11.60/1.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.60/1.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.60/1.98  --inst_lit_sel_side                     num_symb
% 11.60/1.98  --inst_solver_per_active                1400
% 11.60/1.98  --inst_solver_calls_frac                1.
% 11.60/1.98  --inst_passive_queue_type               priority_queues
% 11.60/1.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.60/1.98  --inst_passive_queues_freq              [25;2]
% 11.60/1.98  --inst_dismatching                      true
% 11.60/1.98  --inst_eager_unprocessed_to_passive     true
% 11.60/1.98  --inst_prop_sim_given                   true
% 11.60/1.98  --inst_prop_sim_new                     false
% 11.60/1.98  --inst_subs_new                         false
% 11.60/1.98  --inst_eq_res_simp                      false
% 11.60/1.98  --inst_subs_given                       false
% 11.60/1.98  --inst_orphan_elimination               true
% 11.60/1.98  --inst_learning_loop_flag               true
% 11.60/1.98  --inst_learning_start                   3000
% 11.60/1.98  --inst_learning_factor                  2
% 11.60/1.98  --inst_start_prop_sim_after_learn       3
% 11.60/1.98  --inst_sel_renew                        solver
% 11.60/1.98  --inst_lit_activity_flag                true
% 11.60/1.98  --inst_restr_to_given                   false
% 11.60/1.98  --inst_activity_threshold               500
% 11.60/1.98  --inst_out_proof                        true
% 11.60/1.98  
% 11.60/1.98  ------ Resolution Options
% 11.60/1.98  
% 11.60/1.98  --resolution_flag                       true
% 11.60/1.98  --res_lit_sel                           adaptive
% 11.60/1.98  --res_lit_sel_side                      none
% 11.60/1.98  --res_ordering                          kbo
% 11.60/1.98  --res_to_prop_solver                    active
% 11.60/1.98  --res_prop_simpl_new                    false
% 11.60/1.98  --res_prop_simpl_given                  true
% 11.60/1.98  --res_passive_queue_type                priority_queues
% 11.60/1.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.60/1.98  --res_passive_queues_freq               [15;5]
% 11.60/1.98  --res_forward_subs                      full
% 11.60/1.98  --res_backward_subs                     full
% 11.60/1.98  --res_forward_subs_resolution           true
% 11.60/1.98  --res_backward_subs_resolution          true
% 11.60/1.98  --res_orphan_elimination                true
% 11.60/1.98  --res_time_limit                        2.
% 11.60/1.98  --res_out_proof                         true
% 11.60/1.98  
% 11.60/1.98  ------ Superposition Options
% 11.60/1.98  
% 11.60/1.98  --superposition_flag                    true
% 11.60/1.98  --sup_passive_queue_type                priority_queues
% 11.60/1.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.60/1.98  --sup_passive_queues_freq               [8;1;4]
% 11.60/1.98  --demod_completeness_check              fast
% 11.60/1.98  --demod_use_ground                      true
% 11.60/1.98  --sup_to_prop_solver                    passive
% 11.60/1.98  --sup_prop_simpl_new                    true
% 11.60/1.98  --sup_prop_simpl_given                  true
% 11.60/1.98  --sup_fun_splitting                     true
% 11.60/1.98  --sup_smt_interval                      50000
% 11.60/1.98  
% 11.60/1.98  ------ Superposition Simplification Setup
% 11.60/1.98  
% 11.60/1.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.60/1.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.60/1.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.60/1.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.60/1.98  --sup_full_triv                         [TrivRules;PropSubs]
% 11.60/1.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.60/1.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.60/1.98  --sup_immed_triv                        [TrivRules]
% 11.60/1.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.60/1.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.60/1.98  --sup_immed_bw_main                     []
% 11.60/1.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.60/1.98  --sup_input_triv                        [Unflattening;TrivRules]
% 11.60/1.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.60/1.98  --sup_input_bw                          []
% 11.60/1.98  
% 11.60/1.98  ------ Combination Options
% 11.60/1.98  
% 11.60/1.98  --comb_res_mult                         3
% 11.60/1.98  --comb_sup_mult                         2
% 11.60/1.98  --comb_inst_mult                        10
% 11.60/1.98  
% 11.60/1.98  ------ Debug Options
% 11.60/1.98  
% 11.60/1.98  --dbg_backtrace                         false
% 11.60/1.98  --dbg_dump_prop_clauses                 false
% 11.60/1.98  --dbg_dump_prop_clauses_file            -
% 11.60/1.98  --dbg_out_stat                          false
% 11.60/1.98  ------ Parsing...
% 11.60/1.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.60/1.98  
% 11.60/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 11.60/1.98  
% 11.60/1.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.60/1.98  
% 11.60/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.60/1.98  ------ Proving...
% 11.60/1.98  ------ Problem Properties 
% 11.60/1.98  
% 11.60/1.98  
% 11.60/1.98  clauses                                 48
% 11.60/1.98  conjectures                             5
% 11.60/1.98  EPR                                     3
% 11.60/1.98  Horn                                    43
% 11.60/1.98  unary                                   17
% 11.60/1.98  binary                                  6
% 11.60/1.98  lits                                    132
% 11.60/1.98  lits eq                                 39
% 11.60/1.98  fd_pure                                 0
% 11.60/1.98  fd_pseudo                               0
% 11.60/1.98  fd_cond                                 0
% 11.60/1.98  fd_pseudo_cond                          2
% 11.60/1.98  AC symbols                              0
% 11.60/1.98  
% 11.60/1.98  ------ Schedule dynamic 5 is on 
% 11.60/1.98  
% 11.60/1.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.60/1.98  
% 11.60/1.98  
% 11.60/1.98  ------ 
% 11.60/1.98  Current options:
% 11.60/1.98  ------ 
% 11.60/1.98  
% 11.60/1.98  ------ Input Options
% 11.60/1.98  
% 11.60/1.98  --out_options                           all
% 11.60/1.98  --tptp_safe_out                         true
% 11.60/1.98  --problem_path                          ""
% 11.60/1.98  --include_path                          ""
% 11.60/1.98  --clausifier                            res/vclausify_rel
% 11.60/1.98  --clausifier_options                    ""
% 11.60/1.98  --stdin                                 false
% 11.60/1.98  --stats_out                             all
% 11.60/1.98  
% 11.60/1.98  ------ General Options
% 11.60/1.98  
% 11.60/1.98  --fof                                   false
% 11.60/1.98  --time_out_real                         305.
% 11.60/1.98  --time_out_virtual                      -1.
% 11.60/1.98  --symbol_type_check                     false
% 11.60/1.98  --clausify_out                          false
% 11.60/1.98  --sig_cnt_out                           false
% 11.60/1.98  --trig_cnt_out                          false
% 11.60/1.98  --trig_cnt_out_tolerance                1.
% 11.60/1.98  --trig_cnt_out_sk_spl                   false
% 11.60/1.98  --abstr_cl_out                          false
% 11.60/1.98  
% 11.60/1.98  ------ Global Options
% 11.60/1.98  
% 11.60/1.98  --schedule                              default
% 11.60/1.98  --add_important_lit                     false
% 11.60/1.98  --prop_solver_per_cl                    1000
% 11.60/1.98  --min_unsat_core                        false
% 11.60/1.98  --soft_assumptions                      false
% 11.60/1.98  --soft_lemma_size                       3
% 11.60/1.98  --prop_impl_unit_size                   0
% 11.60/1.98  --prop_impl_unit                        []
% 11.60/1.98  --share_sel_clauses                     true
% 11.60/1.98  --reset_solvers                         false
% 11.60/1.98  --bc_imp_inh                            [conj_cone]
% 11.60/1.98  --conj_cone_tolerance                   3.
% 11.60/1.98  --extra_neg_conj                        none
% 11.60/1.98  --large_theory_mode                     true
% 11.60/1.98  --prolific_symb_bound                   200
% 11.60/1.98  --lt_threshold                          2000
% 11.60/1.98  --clause_weak_htbl                      true
% 11.60/1.98  --gc_record_bc_elim                     false
% 11.60/1.98  
% 11.60/1.98  ------ Preprocessing Options
% 11.60/1.98  
% 11.60/1.98  --preprocessing_flag                    true
% 11.60/1.98  --time_out_prep_mult                    0.1
% 11.60/1.98  --splitting_mode                        input
% 11.60/1.98  --splitting_grd                         true
% 11.60/1.98  --splitting_cvd                         false
% 11.60/1.98  --splitting_cvd_svl                     false
% 11.60/1.98  --splitting_nvd                         32
% 11.60/1.98  --sub_typing                            true
% 11.60/1.98  --prep_gs_sim                           true
% 11.60/1.98  --prep_unflatten                        true
% 11.60/1.98  --prep_res_sim                          true
% 11.60/1.98  --prep_upred                            true
% 11.60/1.98  --prep_sem_filter                       exhaustive
% 11.60/1.98  --prep_sem_filter_out                   false
% 11.60/1.98  --pred_elim                             true
% 11.60/1.98  --res_sim_input                         true
% 11.60/1.98  --eq_ax_congr_red                       true
% 11.60/1.98  --pure_diseq_elim                       true
% 11.60/1.98  --brand_transform                       false
% 11.60/1.98  --non_eq_to_eq                          false
% 11.60/1.98  --prep_def_merge                        true
% 11.60/1.98  --prep_def_merge_prop_impl              false
% 11.60/1.98  --prep_def_merge_mbd                    true
% 11.60/1.98  --prep_def_merge_tr_red                 false
% 11.60/1.98  --prep_def_merge_tr_cl                  false
% 11.60/1.98  --smt_preprocessing                     true
% 11.60/1.98  --smt_ac_axioms                         fast
% 11.60/1.98  --preprocessed_out                      false
% 11.60/1.98  --preprocessed_stats                    false
% 11.60/1.98  
% 11.60/1.98  ------ Abstraction refinement Options
% 11.60/1.98  
% 11.60/1.98  --abstr_ref                             []
% 11.60/1.98  --abstr_ref_prep                        false
% 11.60/1.98  --abstr_ref_until_sat                   false
% 11.60/1.98  --abstr_ref_sig_restrict                funpre
% 11.60/1.98  --abstr_ref_af_restrict_to_split_sk     false
% 11.60/1.98  --abstr_ref_under                       []
% 11.60/1.98  
% 11.60/1.98  ------ SAT Options
% 11.60/1.98  
% 11.60/1.98  --sat_mode                              false
% 11.60/1.98  --sat_fm_restart_options                ""
% 11.60/1.98  --sat_gr_def                            false
% 11.60/1.98  --sat_epr_types                         true
% 11.60/1.98  --sat_non_cyclic_types                  false
% 11.60/1.98  --sat_finite_models                     false
% 11.60/1.98  --sat_fm_lemmas                         false
% 11.60/1.98  --sat_fm_prep                           false
% 11.60/1.98  --sat_fm_uc_incr                        true
% 11.60/1.98  --sat_out_model                         small
% 11.60/1.98  --sat_out_clauses                       false
% 11.60/1.98  
% 11.60/1.98  ------ QBF Options
% 11.60/1.98  
% 11.60/1.98  --qbf_mode                              false
% 11.60/1.98  --qbf_elim_univ                         false
% 11.60/1.98  --qbf_dom_inst                          none
% 11.60/1.98  --qbf_dom_pre_inst                      false
% 11.60/1.98  --qbf_sk_in                             false
% 11.60/1.98  --qbf_pred_elim                         true
% 11.60/1.98  --qbf_split                             512
% 11.60/1.98  
% 11.60/1.98  ------ BMC1 Options
% 11.60/1.98  
% 11.60/1.98  --bmc1_incremental                      false
% 11.60/1.98  --bmc1_axioms                           reachable_all
% 11.60/1.98  --bmc1_min_bound                        0
% 11.60/1.98  --bmc1_max_bound                        -1
% 11.60/1.98  --bmc1_max_bound_default                -1
% 11.60/1.98  --bmc1_symbol_reachability              true
% 11.60/1.98  --bmc1_property_lemmas                  false
% 11.60/1.98  --bmc1_k_induction                      false
% 11.60/1.98  --bmc1_non_equiv_states                 false
% 11.60/1.98  --bmc1_deadlock                         false
% 11.60/1.98  --bmc1_ucm                              false
% 11.60/1.98  --bmc1_add_unsat_core                   none
% 11.60/1.98  --bmc1_unsat_core_children              false
% 11.60/1.98  --bmc1_unsat_core_extrapolate_axioms    false
% 11.60/1.98  --bmc1_out_stat                         full
% 11.60/1.98  --bmc1_ground_init                      false
% 11.60/1.98  --bmc1_pre_inst_next_state              false
% 11.60/1.98  --bmc1_pre_inst_state                   false
% 11.60/1.98  --bmc1_pre_inst_reach_state             false
% 11.60/1.98  --bmc1_out_unsat_core                   false
% 11.60/1.98  --bmc1_aig_witness_out                  false
% 11.60/1.98  --bmc1_verbose                          false
% 11.60/1.98  --bmc1_dump_clauses_tptp                false
% 11.60/1.98  --bmc1_dump_unsat_core_tptp             false
% 11.60/1.98  --bmc1_dump_file                        -
% 11.60/1.98  --bmc1_ucm_expand_uc_limit              128
% 11.60/1.98  --bmc1_ucm_n_expand_iterations          6
% 11.60/1.98  --bmc1_ucm_extend_mode                  1
% 11.60/1.98  --bmc1_ucm_init_mode                    2
% 11.60/1.98  --bmc1_ucm_cone_mode                    none
% 11.60/1.98  --bmc1_ucm_reduced_relation_type        0
% 11.60/1.98  --bmc1_ucm_relax_model                  4
% 11.60/1.98  --bmc1_ucm_full_tr_after_sat            true
% 11.60/1.98  --bmc1_ucm_expand_neg_assumptions       false
% 11.60/1.98  --bmc1_ucm_layered_model                none
% 11.60/1.98  --bmc1_ucm_max_lemma_size               10
% 11.60/1.98  
% 11.60/1.98  ------ AIG Options
% 11.60/1.98  
% 11.60/1.98  --aig_mode                              false
% 11.60/1.98  
% 11.60/1.98  ------ Instantiation Options
% 11.60/1.98  
% 11.60/1.98  --instantiation_flag                    true
% 11.60/1.98  --inst_sos_flag                         true
% 11.60/1.98  --inst_sos_phase                        true
% 11.60/1.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.60/1.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.60/1.98  --inst_lit_sel_side                     none
% 11.60/1.98  --inst_solver_per_active                1400
% 11.60/1.98  --inst_solver_calls_frac                1.
% 11.60/1.98  --inst_passive_queue_type               priority_queues
% 11.60/1.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.60/1.98  --inst_passive_queues_freq              [25;2]
% 11.60/1.98  --inst_dismatching                      true
% 11.60/1.98  --inst_eager_unprocessed_to_passive     true
% 11.60/1.98  --inst_prop_sim_given                   true
% 11.60/1.98  --inst_prop_sim_new                     false
% 11.60/1.98  --inst_subs_new                         false
% 11.60/1.98  --inst_eq_res_simp                      false
% 11.60/1.98  --inst_subs_given                       false
% 11.60/1.98  --inst_orphan_elimination               true
% 11.60/1.98  --inst_learning_loop_flag               true
% 11.60/1.98  --inst_learning_start                   3000
% 11.60/1.98  --inst_learning_factor                  2
% 11.60/1.98  --inst_start_prop_sim_after_learn       3
% 11.60/1.98  --inst_sel_renew                        solver
% 11.60/1.98  --inst_lit_activity_flag                true
% 11.60/1.98  --inst_restr_to_given                   false
% 11.60/1.98  --inst_activity_threshold               500
% 11.60/1.98  --inst_out_proof                        true
% 11.60/1.98  
% 11.60/1.98  ------ Resolution Options
% 11.60/1.98  
% 11.60/1.98  --resolution_flag                       false
% 11.60/1.98  --res_lit_sel                           adaptive
% 11.60/1.98  --res_lit_sel_side                      none
% 11.60/1.98  --res_ordering                          kbo
% 11.60/1.98  --res_to_prop_solver                    active
% 11.60/1.98  --res_prop_simpl_new                    false
% 11.60/1.98  --res_prop_simpl_given                  true
% 11.60/1.98  --res_passive_queue_type                priority_queues
% 11.60/1.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.60/1.98  --res_passive_queues_freq               [15;5]
% 11.60/1.98  --res_forward_subs                      full
% 11.60/1.98  --res_backward_subs                     full
% 11.60/1.98  --res_forward_subs_resolution           true
% 11.60/1.98  --res_backward_subs_resolution          true
% 11.60/1.98  --res_orphan_elimination                true
% 11.60/1.98  --res_time_limit                        2.
% 11.60/1.98  --res_out_proof                         true
% 11.60/1.98  
% 11.60/1.98  ------ Superposition Options
% 11.60/1.98  
% 11.60/1.98  --superposition_flag                    true
% 11.60/1.98  --sup_passive_queue_type                priority_queues
% 11.60/1.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.60/1.98  --sup_passive_queues_freq               [8;1;4]
% 11.60/1.98  --demod_completeness_check              fast
% 11.60/1.98  --demod_use_ground                      true
% 11.60/1.98  --sup_to_prop_solver                    passive
% 11.60/1.98  --sup_prop_simpl_new                    true
% 11.60/1.98  --sup_prop_simpl_given                  true
% 11.60/1.98  --sup_fun_splitting                     true
% 11.60/1.98  --sup_smt_interval                      50000
% 11.60/1.98  
% 11.60/1.98  ------ Superposition Simplification Setup
% 11.60/1.98  
% 11.60/1.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.60/1.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.60/1.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.60/1.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.60/1.98  --sup_full_triv                         [TrivRules;PropSubs]
% 11.60/1.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.60/1.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.60/1.98  --sup_immed_triv                        [TrivRules]
% 11.60/1.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.60/1.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.60/1.98  --sup_immed_bw_main                     []
% 11.60/1.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.60/1.98  --sup_input_triv                        [Unflattening;TrivRules]
% 11.60/1.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.60/1.98  --sup_input_bw                          []
% 11.60/1.98  
% 11.60/1.98  ------ Combination Options
% 11.60/1.98  
% 11.60/1.98  --comb_res_mult                         3
% 11.60/1.98  --comb_sup_mult                         2
% 11.60/1.98  --comb_inst_mult                        10
% 11.60/1.98  
% 11.60/1.98  ------ Debug Options
% 11.60/1.98  
% 11.60/1.98  --dbg_backtrace                         false
% 11.60/1.98  --dbg_dump_prop_clauses                 false
% 11.60/1.98  --dbg_dump_prop_clauses_file            -
% 11.60/1.98  --dbg_out_stat                          false
% 11.60/1.98  
% 11.60/1.98  
% 11.60/1.98  
% 11.60/1.98  
% 11.60/1.98  ------ Proving...
% 11.60/1.98  
% 11.60/1.98  
% 11.60/1.98  % SZS status Theorem for theBenchmark.p
% 11.60/1.98  
% 11.60/1.98  % SZS output start CNFRefutation for theBenchmark.p
% 11.60/1.98  
% 11.60/1.98  fof(f5,axiom,(
% 11.60/1.98    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 11.60/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.60/1.98  
% 11.60/1.98  fof(f33,plain,(
% 11.60/1.98    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 11.60/1.98    inference(ennf_transformation,[],[f5])).
% 11.60/1.98  
% 11.60/1.98  fof(f83,plain,(
% 11.60/1.98    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 11.60/1.98    inference(cnf_transformation,[],[f33])).
% 11.60/1.98  
% 11.60/1.98  fof(f27,conjecture,(
% 11.60/1.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)) => r2_relset_1(X0,X0,X2,k6_partfun1(X0)))))),
% 11.60/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.60/1.98  
% 11.60/1.98  fof(f28,negated_conjecture,(
% 11.60/1.98    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)) => r2_relset_1(X0,X0,X2,k6_partfun1(X0)))))),
% 11.60/1.98    inference(negated_conjecture,[],[f27])).
% 11.60/1.98  
% 11.60/1.98  fof(f68,plain,(
% 11.60/1.98    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & (v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 11.60/1.98    inference(ennf_transformation,[],[f28])).
% 11.60/1.98  
% 11.60/1.98  fof(f69,plain,(
% 11.60/1.98    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 11.60/1.98    inference(flattening,[],[f68])).
% 11.60/1.98  
% 11.60/1.98  fof(f76,plain,(
% 11.60/1.98    ( ! [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (~r2_relset_1(X0,X0,sK4,k6_partfun1(X0)) & v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,sK4,X1),X1) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(sK4,X0,X0) & v1_funct_1(sK4))) )),
% 11.60/1.98    introduced(choice_axiom,[])).
% 11.60/1.98  
% 11.60/1.98  fof(f75,plain,(
% 11.60/1.98    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK2,sK2,X2,k6_partfun1(sK2)) & v2_funct_1(sK3) & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,X2,sK3),sK3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(X2,sK2,sK2) & v1_funct_1(X2)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(sK3,sK2,sK2) & v1_funct_1(sK3))),
% 11.60/1.98    introduced(choice_axiom,[])).
% 11.60/1.98  
% 11.60/1.98  fof(f77,plain,(
% 11.60/1.98    (~r2_relset_1(sK2,sK2,sK4,k6_partfun1(sK2)) & v2_funct_1(sK3) & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3),sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(sK4,sK2,sK2) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(sK3,sK2,sK2) & v1_funct_1(sK3)),
% 11.60/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f69,f76,f75])).
% 11.60/1.98  
% 11.60/1.98  fof(f123,plain,(
% 11.60/1.98    v2_funct_1(sK3)),
% 11.60/1.98    inference(cnf_transformation,[],[f77])).
% 11.60/1.98  
% 11.60/1.98  fof(f7,axiom,(
% 11.60/1.98    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 11.60/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.60/1.98  
% 11.60/1.98  fof(f36,plain,(
% 11.60/1.98    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.60/1.98    inference(ennf_transformation,[],[f7])).
% 11.60/1.98  
% 11.60/1.98  fof(f37,plain,(
% 11.60/1.98    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.60/1.98    inference(flattening,[],[f36])).
% 11.60/1.98  
% 11.60/1.98  fof(f88,plain,(
% 11.60/1.98    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.60/1.98    inference(cnf_transformation,[],[f37])).
% 11.60/1.98  
% 11.60/1.98  fof(f11,axiom,(
% 11.60/1.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0))))),
% 11.60/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.60/1.98  
% 11.60/1.98  fof(f42,plain,(
% 11.60/1.98    ! [X0] : (((k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.60/1.98    inference(ennf_transformation,[],[f11])).
% 11.60/1.98  
% 11.60/1.98  fof(f43,plain,(
% 11.60/1.98    ! [X0] : ((k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.60/1.98    inference(flattening,[],[f42])).
% 11.60/1.98  
% 11.60/1.98  fof(f94,plain,(
% 11.60/1.98    ( ! [X0] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.60/1.98    inference(cnf_transformation,[],[f43])).
% 11.60/1.98  
% 11.60/1.98  fof(f86,plain,(
% 11.60/1.98    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.60/1.98    inference(cnf_transformation,[],[f37])).
% 11.60/1.98  
% 11.60/1.98  fof(f87,plain,(
% 11.60/1.98    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.60/1.98    inference(cnf_transformation,[],[f37])).
% 11.60/1.98  
% 11.60/1.98  fof(f13,axiom,(
% 11.60/1.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 11.60/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.60/1.98  
% 11.60/1.98  fof(f46,plain,(
% 11.60/1.98    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.60/1.98    inference(ennf_transformation,[],[f13])).
% 11.60/1.98  
% 11.60/1.98  fof(f47,plain,(
% 11.60/1.98    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.60/1.98    inference(flattening,[],[f46])).
% 11.60/1.98  
% 11.60/1.98  fof(f97,plain,(
% 11.60/1.98    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.60/1.98    inference(cnf_transformation,[],[f47])).
% 11.60/1.98  
% 11.60/1.98  fof(f116,plain,(
% 11.60/1.98    v1_funct_1(sK3)),
% 11.60/1.98    inference(cnf_transformation,[],[f77])).
% 11.60/1.98  
% 11.60/1.98  fof(f118,plain,(
% 11.60/1.98    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 11.60/1.98    inference(cnf_transformation,[],[f77])).
% 11.60/1.98  
% 11.60/1.98  fof(f15,axiom,(
% 11.60/1.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 11.60/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.60/1.98  
% 11.60/1.98  fof(f50,plain,(
% 11.60/1.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.60/1.98    inference(ennf_transformation,[],[f15])).
% 11.60/1.98  
% 11.60/1.98  fof(f99,plain,(
% 11.60/1.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.60/1.98    inference(cnf_transformation,[],[f50])).
% 11.60/1.98  
% 11.60/1.98  fof(f10,axiom,(
% 11.60/1.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 11.60/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.60/1.98  
% 11.60/1.98  fof(f40,plain,(
% 11.60/1.98    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.60/1.98    inference(ennf_transformation,[],[f10])).
% 11.60/1.98  
% 11.60/1.98  fof(f41,plain,(
% 11.60/1.98    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.60/1.98    inference(flattening,[],[f40])).
% 11.60/1.98  
% 11.60/1.98  fof(f92,plain,(
% 11.60/1.98    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.60/1.98    inference(cnf_transformation,[],[f41])).
% 11.60/1.98  
% 11.60/1.98  fof(f16,axiom,(
% 11.60/1.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 11.60/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.60/1.98  
% 11.60/1.98  fof(f51,plain,(
% 11.60/1.98    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.60/1.98    inference(ennf_transformation,[],[f16])).
% 11.60/1.98  
% 11.60/1.98  fof(f100,plain,(
% 11.60/1.98    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.60/1.98    inference(cnf_transformation,[],[f51])).
% 11.60/1.98  
% 11.60/1.98  fof(f26,axiom,(
% 11.60/1.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 11.60/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.60/1.98  
% 11.60/1.98  fof(f66,plain,(
% 11.60/1.98    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 11.60/1.98    inference(ennf_transformation,[],[f26])).
% 11.60/1.98  
% 11.60/1.98  fof(f67,plain,(
% 11.60/1.98    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 11.60/1.98    inference(flattening,[],[f66])).
% 11.60/1.98  
% 11.60/1.98  fof(f115,plain,(
% 11.60/1.98    ( ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 11.60/1.98    inference(cnf_transformation,[],[f67])).
% 11.60/1.98  
% 11.60/1.98  fof(f117,plain,(
% 11.60/1.98    v1_funct_2(sK3,sK2,sK2)),
% 11.60/1.98    inference(cnf_transformation,[],[f77])).
% 11.60/1.98  
% 11.60/1.98  fof(f121,plain,(
% 11.60/1.98    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 11.60/1.98    inference(cnf_transformation,[],[f77])).
% 11.60/1.98  
% 11.60/1.98  fof(f23,axiom,(
% 11.60/1.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 11.60/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.60/1.98  
% 11.60/1.98  fof(f60,plain,(
% 11.60/1.98    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 11.60/1.98    inference(ennf_transformation,[],[f23])).
% 11.60/1.98  
% 11.60/1.98  fof(f61,plain,(
% 11.60/1.98    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 11.60/1.98    inference(flattening,[],[f60])).
% 11.60/1.98  
% 11.60/1.98  fof(f111,plain,(
% 11.60/1.98    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 11.60/1.98    inference(cnf_transformation,[],[f61])).
% 11.60/1.98  
% 11.60/1.98  fof(f18,axiom,(
% 11.60/1.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 11.60/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.60/1.98  
% 11.60/1.98  fof(f53,plain,(
% 11.60/1.98    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 11.60/1.98    inference(ennf_transformation,[],[f18])).
% 11.60/1.98  
% 11.60/1.98  fof(f54,plain,(
% 11.60/1.98    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.60/1.98    inference(flattening,[],[f53])).
% 11.60/1.98  
% 11.60/1.98  fof(f72,plain,(
% 11.60/1.98    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.60/1.98    inference(nnf_transformation,[],[f54])).
% 11.60/1.98  
% 11.60/1.98  fof(f102,plain,(
% 11.60/1.98    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.60/1.98    inference(cnf_transformation,[],[f72])).
% 11.60/1.98  
% 11.60/1.98  fof(f122,plain,(
% 11.60/1.98    r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3),sK3)),
% 11.60/1.98    inference(cnf_transformation,[],[f77])).
% 11.60/1.98  
% 11.60/1.98  fof(f119,plain,(
% 11.60/1.98    v1_funct_1(sK4)),
% 11.60/1.98    inference(cnf_transformation,[],[f77])).
% 11.60/1.98  
% 11.60/1.98  fof(f21,axiom,(
% 11.60/1.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 11.60/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.60/1.98  
% 11.60/1.98  fof(f58,plain,(
% 11.60/1.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 11.60/1.98    inference(ennf_transformation,[],[f21])).
% 11.60/1.98  
% 11.60/1.98  fof(f59,plain,(
% 11.60/1.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 11.60/1.98    inference(flattening,[],[f58])).
% 11.60/1.98  
% 11.60/1.98  fof(f109,plain,(
% 11.60/1.98    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 11.60/1.98    inference(cnf_transformation,[],[f59])).
% 11.60/1.98  
% 11.60/1.98  fof(f8,axiom,(
% 11.60/1.98    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k5_relat_1(X2,X1) = X1 & v2_funct_1(X1) & r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => k6_relat_1(X0) = X2)))),
% 11.60/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.60/1.98  
% 11.60/1.98  fof(f38,plain,(
% 11.60/1.98    ! [X0,X1] : (! [X2] : ((k6_relat_1(X0) = X2 | (k5_relat_1(X2,X1) != X1 | ~v2_funct_1(X1) | ~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 11.60/1.98    inference(ennf_transformation,[],[f8])).
% 11.60/1.98  
% 11.60/1.98  fof(f39,plain,(
% 11.60/1.98    ! [X0,X1] : (! [X2] : (k6_relat_1(X0) = X2 | k5_relat_1(X2,X1) != X1 | ~v2_funct_1(X1) | ~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 11.60/1.98    inference(flattening,[],[f38])).
% 11.60/1.98  
% 11.60/1.98  fof(f89,plain,(
% 11.60/1.98    ( ! [X2,X0,X1] : (k6_relat_1(X0) = X2 | k5_relat_1(X2,X1) != X1 | ~v2_funct_1(X1) | ~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 11.60/1.98    inference(cnf_transformation,[],[f39])).
% 11.60/1.98  
% 11.60/1.98  fof(f125,plain,(
% 11.60/1.98    ( ! [X2,X1] : (k6_relat_1(k1_relat_1(X2)) = X2 | k5_relat_1(X2,X1) != X1 | ~v2_funct_1(X1) | ~r1_tarski(k2_relat_1(X2),k1_relat_1(X2)) | k1_relat_1(X1) != k1_relat_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 11.60/1.98    inference(equality_resolution,[],[f89])).
% 11.60/1.98  
% 11.60/1.98  fof(f120,plain,(
% 11.60/1.98    v1_funct_2(sK4,sK2,sK2)),
% 11.60/1.98    inference(cnf_transformation,[],[f77])).
% 11.60/1.98  
% 11.60/1.98  fof(f19,axiom,(
% 11.60/1.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 11.60/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.60/1.98  
% 11.60/1.98  fof(f55,plain,(
% 11.60/1.98    ! [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.60/1.98    inference(ennf_transformation,[],[f19])).
% 11.60/1.98  
% 11.60/1.98  fof(f104,plain,(
% 11.60/1.98    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.60/1.98    inference(cnf_transformation,[],[f55])).
% 11.60/1.98  
% 11.60/1.98  fof(f17,axiom,(
% 11.60/1.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 11.60/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.60/1.98  
% 11.60/1.98  fof(f52,plain,(
% 11.60/1.98    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.60/1.98    inference(ennf_transformation,[],[f17])).
% 11.60/1.98  
% 11.60/1.98  fof(f101,plain,(
% 11.60/1.98    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.60/1.98    inference(cnf_transformation,[],[f52])).
% 11.60/1.98  
% 11.60/1.98  fof(f25,axiom,(
% 11.60/1.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => r1_tarski(k7_relset_1(X0,X1,X3,X2),X1))),
% 11.60/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.60/1.98  
% 11.60/1.98  fof(f64,plain,(
% 11.60/1.98    ! [X0,X1,X2,X3] : (r1_tarski(k7_relset_1(X0,X1,X3,X2),X1) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 11.60/1.98    inference(ennf_transformation,[],[f25])).
% 11.60/1.98  
% 11.60/1.98  fof(f65,plain,(
% 11.60/1.98    ! [X0,X1,X2,X3] : (r1_tarski(k7_relset_1(X0,X1,X3,X2),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 11.60/1.98    inference(flattening,[],[f64])).
% 11.60/1.98  
% 11.60/1.98  fof(f114,plain,(
% 11.60/1.98    ( ! [X2,X0,X3,X1] : (r1_tarski(k7_relset_1(X0,X1,X3,X2),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 11.60/1.98    inference(cnf_transformation,[],[f65])).
% 11.60/1.98  
% 11.60/1.98  fof(f12,axiom,(
% 11.60/1.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 11.60/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.60/1.98  
% 11.60/1.98  fof(f44,plain,(
% 11.60/1.98    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.60/1.98    inference(ennf_transformation,[],[f12])).
% 11.60/1.98  
% 11.60/1.98  fof(f45,plain,(
% 11.60/1.98    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.60/1.98    inference(flattening,[],[f44])).
% 11.60/1.98  
% 11.60/1.98  fof(f95,plain,(
% 11.60/1.98    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.60/1.98    inference(cnf_transformation,[],[f45])).
% 11.60/1.98  
% 11.60/1.98  fof(f2,axiom,(
% 11.60/1.98    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 11.60/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.60/1.98  
% 11.60/1.98  fof(f80,plain,(
% 11.60/1.98    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 11.60/1.98    inference(cnf_transformation,[],[f2])).
% 11.60/1.98  
% 11.60/1.98  fof(f9,axiom,(
% 11.60/1.98    ! [X0] : v2_funct_1(k6_relat_1(X0))),
% 11.60/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.60/1.98  
% 11.60/1.98  fof(f90,plain,(
% 11.60/1.98    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 11.60/1.98    inference(cnf_transformation,[],[f9])).
% 11.60/1.98  
% 11.60/1.98  fof(f24,axiom,(
% 11.60/1.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1)))),
% 11.60/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.60/1.98  
% 11.60/1.98  fof(f62,plain,(
% 11.60/1.98    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 11.60/1.98    inference(ennf_transformation,[],[f24])).
% 11.60/1.98  
% 11.60/1.98  fof(f63,plain,(
% 11.60/1.98    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 11.60/1.98    inference(flattening,[],[f62])).
% 11.60/1.98  
% 11.60/1.98  fof(f112,plain,(
% 11.60/1.98    ( ! [X2,X0,X1] : (k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 11.60/1.98    inference(cnf_transformation,[],[f63])).
% 11.60/1.98  
% 11.60/1.98  fof(f20,axiom,(
% 11.60/1.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => (! [X3] : (r2_hidden(X3,X0) => k11_relat_1(X1,X3) = k11_relat_1(X2,X3)) => r2_relset_1(X0,X0,X1,X2))))),
% 11.60/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.60/1.98  
% 11.60/1.98  fof(f56,plain,(
% 11.60/1.98    ! [X0,X1] : (! [X2] : ((r2_relset_1(X0,X0,X1,X2) | ? [X3] : (k11_relat_1(X1,X3) != k11_relat_1(X2,X3) & r2_hidden(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 11.60/1.98    inference(ennf_transformation,[],[f20])).
% 11.60/1.98  
% 11.60/1.98  fof(f57,plain,(
% 11.60/1.98    ! [X0,X1] : (! [X2] : (r2_relset_1(X0,X0,X1,X2) | ? [X3] : (k11_relat_1(X1,X3) != k11_relat_1(X2,X3) & r2_hidden(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 11.60/1.98    inference(flattening,[],[f56])).
% 11.60/1.98  
% 11.60/1.98  fof(f73,plain,(
% 11.60/1.98    ! [X2,X1,X0] : (? [X3] : (k11_relat_1(X1,X3) != k11_relat_1(X2,X3) & r2_hidden(X3,X0)) => (k11_relat_1(X1,sK1(X0,X1,X2)) != k11_relat_1(X2,sK1(X0,X1,X2)) & r2_hidden(sK1(X0,X1,X2),X0)))),
% 11.60/1.98    introduced(choice_axiom,[])).
% 11.60/1.98  
% 11.60/1.98  fof(f74,plain,(
% 11.60/1.98    ! [X0,X1] : (! [X2] : (r2_relset_1(X0,X0,X1,X2) | (k11_relat_1(X1,sK1(X0,X1,X2)) != k11_relat_1(X2,sK1(X0,X1,X2)) & r2_hidden(sK1(X0,X1,X2),X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 11.60/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f57,f73])).
% 11.60/1.98  
% 11.60/1.98  fof(f106,plain,(
% 11.60/1.98    ( ! [X2,X0,X1] : (r2_relset_1(X0,X0,X1,X2) | r2_hidden(sK1(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 11.60/1.98    inference(cnf_transformation,[],[f74])).
% 11.60/1.98  
% 11.60/1.98  fof(f22,axiom,(
% 11.60/1.98    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 11.60/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.60/1.98  
% 11.60/1.98  fof(f29,plain,(
% 11.60/1.98    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 11.60/1.98    inference(pure_predicate_removal,[],[f22])).
% 11.60/1.98  
% 11.60/1.98  fof(f110,plain,(
% 11.60/1.98    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 11.60/1.98    inference(cnf_transformation,[],[f29])).
% 11.60/1.98  
% 11.60/1.98  fof(f1,axiom,(
% 11.60/1.98    ! [X0] : ? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.60/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.60/1.98  
% 11.60/1.98  fof(f70,plain,(
% 11.60/1.98    ! [X0] : (? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (v1_xboole_0(sK0(X0)) & m1_subset_1(sK0(X0),k1_zfmisc_1(X0))))),
% 11.60/1.98    introduced(choice_axiom,[])).
% 11.60/1.98  
% 11.60/1.98  fof(f71,plain,(
% 11.60/1.98    ! [X0] : (v1_xboole_0(sK0(X0)) & m1_subset_1(sK0(X0),k1_zfmisc_1(X0)))),
% 11.60/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f1,f70])).
% 11.60/1.98  
% 11.60/1.98  fof(f78,plain,(
% 11.60/1.98    ( ! [X0] : (m1_subset_1(sK0(X0),k1_zfmisc_1(X0))) )),
% 11.60/1.98    inference(cnf_transformation,[],[f71])).
% 11.60/1.98  
% 11.60/1.98  fof(f3,axiom,(
% 11.60/1.98    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 11.60/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.60/1.98  
% 11.60/1.98  fof(f30,plain,(
% 11.60/1.98    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 11.60/1.98    inference(ennf_transformation,[],[f3])).
% 11.60/1.98  
% 11.60/1.98  fof(f81,plain,(
% 11.60/1.98    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 11.60/1.98    inference(cnf_transformation,[],[f30])).
% 11.60/1.98  
% 11.60/1.98  fof(f124,plain,(
% 11.60/1.98    ~r2_relset_1(sK2,sK2,sK4,k6_partfun1(sK2))),
% 11.60/1.98    inference(cnf_transformation,[],[f77])).
% 11.60/1.98  
% 11.60/1.98  fof(f103,plain,(
% 11.60/1.98    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.60/1.98    inference(cnf_transformation,[],[f72])).
% 11.60/1.98  
% 11.60/1.98  fof(f126,plain,(
% 11.60/1.98    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.60/1.98    inference(equality_resolution,[],[f103])).
% 11.60/1.98  
% 11.60/1.98  fof(f79,plain,(
% 11.60/1.98    ( ! [X0] : (v1_xboole_0(sK0(X0))) )),
% 11.60/1.98    inference(cnf_transformation,[],[f71])).
% 11.60/1.98  
% 11.60/1.98  cnf(c_5,plain,
% 11.60/1.98      ( ~ r2_hidden(X0,X1)
% 11.60/1.98      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 11.60/1.98      | ~ v1_xboole_0(X2) ),
% 11.60/1.98      inference(cnf_transformation,[],[f83]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_8178,plain,
% 11.60/1.98      ( ~ r2_hidden(X0,k1_xboole_0)
% 11.60/1.98      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0(X1)))
% 11.60/1.98      | ~ v1_xboole_0(sK0(X1)) ),
% 11.60/1.98      inference(instantiation,[status(thm)],[c_5]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_30017,plain,
% 11.60/1.98      ( ~ r2_hidden(sK1(sK2,sK3,k6_partfun1(sK2)),k1_xboole_0)
% 11.60/1.98      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0(X0)))
% 11.60/1.98      | ~ v1_xboole_0(sK0(X0)) ),
% 11.60/1.98      inference(instantiation,[status(thm)],[c_8178]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_39,negated_conjecture,
% 11.60/1.98      ( v2_funct_1(sK3) ),
% 11.60/1.98      inference(cnf_transformation,[],[f123]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1730,plain,
% 11.60/1.98      ( v2_funct_1(sK3) = iProver_top ),
% 11.60/1.98      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_8,plain,
% 11.60/1.98      ( ~ v2_funct_1(X0)
% 11.60/1.98      | v2_funct_1(k2_funct_1(X0))
% 11.60/1.98      | ~ v1_relat_1(X0)
% 11.60/1.98      | ~ v1_funct_1(X0) ),
% 11.60/1.98      inference(cnf_transformation,[],[f88]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1750,plain,
% 11.60/1.98      ( v2_funct_1(X0) != iProver_top
% 11.60/1.98      | v2_funct_1(k2_funct_1(X0)) = iProver_top
% 11.60/1.98      | v1_relat_1(X0) != iProver_top
% 11.60/1.98      | v1_funct_1(X0) != iProver_top ),
% 11.60/1.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_15,plain,
% 11.60/1.98      ( ~ v2_funct_1(X0)
% 11.60/1.98      | ~ v1_relat_1(X0)
% 11.60/1.98      | ~ v1_funct_1(X0)
% 11.60/1.98      | k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) ),
% 11.60/1.98      inference(cnf_transformation,[],[f94]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1745,plain,
% 11.60/1.98      ( k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0)
% 11.60/1.98      | v2_funct_1(X0) != iProver_top
% 11.60/1.98      | v1_relat_1(X0) != iProver_top
% 11.60/1.98      | v1_funct_1(X0) != iProver_top ),
% 11.60/1.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_5353,plain,
% 11.60/1.98      ( k2_relat_1(k5_relat_1(k2_funct_1(k2_funct_1(X0)),k2_funct_1(X0))) = k2_relat_1(k2_funct_1(X0))
% 11.60/1.98      | v2_funct_1(X0) != iProver_top
% 11.60/1.98      | v1_relat_1(X0) != iProver_top
% 11.60/1.98      | v1_relat_1(k2_funct_1(X0)) != iProver_top
% 11.60/1.98      | v1_funct_1(X0) != iProver_top
% 11.60/1.98      | v1_funct_1(k2_funct_1(X0)) != iProver_top ),
% 11.60/1.98      inference(superposition,[status(thm)],[c_1750,c_1745]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_10,plain,
% 11.60/1.98      ( ~ v2_funct_1(X0)
% 11.60/1.98      | ~ v1_relat_1(X0)
% 11.60/1.98      | v1_relat_1(k2_funct_1(X0))
% 11.60/1.98      | ~ v1_funct_1(X0) ),
% 11.60/1.98      inference(cnf_transformation,[],[f86]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_137,plain,
% 11.60/1.98      ( v2_funct_1(X0) != iProver_top
% 11.60/1.98      | v1_relat_1(X0) != iProver_top
% 11.60/1.98      | v1_relat_1(k2_funct_1(X0)) = iProver_top
% 11.60/1.98      | v1_funct_1(X0) != iProver_top ),
% 11.60/1.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_9,plain,
% 11.60/1.98      ( ~ v2_funct_1(X0)
% 11.60/1.98      | ~ v1_relat_1(X0)
% 11.60/1.98      | ~ v1_funct_1(X0)
% 11.60/1.98      | v1_funct_1(k2_funct_1(X0)) ),
% 11.60/1.98      inference(cnf_transformation,[],[f87]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_140,plain,
% 11.60/1.98      ( v2_funct_1(X0) != iProver_top
% 11.60/1.98      | v1_relat_1(X0) != iProver_top
% 11.60/1.98      | v1_funct_1(X0) != iProver_top
% 11.60/1.98      | v1_funct_1(k2_funct_1(X0)) = iProver_top ),
% 11.60/1.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_26153,plain,
% 11.60/1.98      ( v1_funct_1(X0) != iProver_top
% 11.60/1.98      | k2_relat_1(k5_relat_1(k2_funct_1(k2_funct_1(X0)),k2_funct_1(X0))) = k2_relat_1(k2_funct_1(X0))
% 11.60/1.98      | v2_funct_1(X0) != iProver_top
% 11.60/1.98      | v1_relat_1(X0) != iProver_top ),
% 11.60/1.98      inference(global_propositional_subsumption,
% 11.60/1.98                [status(thm)],
% 11.60/1.98                [c_5353,c_137,c_140]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_26154,plain,
% 11.60/1.98      ( k2_relat_1(k5_relat_1(k2_funct_1(k2_funct_1(X0)),k2_funct_1(X0))) = k2_relat_1(k2_funct_1(X0))
% 11.60/1.98      | v2_funct_1(X0) != iProver_top
% 11.60/1.98      | v1_relat_1(X0) != iProver_top
% 11.60/1.98      | v1_funct_1(X0) != iProver_top ),
% 11.60/1.98      inference(renaming,[status(thm)],[c_26153]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_26161,plain,
% 11.60/1.98      ( k2_relat_1(k5_relat_1(k2_funct_1(k2_funct_1(sK3)),k2_funct_1(sK3))) = k2_relat_1(k2_funct_1(sK3))
% 11.60/1.98      | v1_relat_1(sK3) != iProver_top
% 11.60/1.98      | v1_funct_1(sK3) != iProver_top ),
% 11.60/1.98      inference(superposition,[status(thm)],[c_1730,c_26154]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_19,plain,
% 11.60/1.98      ( ~ v2_funct_1(X0)
% 11.60/1.98      | ~ v1_relat_1(X0)
% 11.60/1.98      | ~ v1_funct_1(X0)
% 11.60/1.98      | k2_funct_1(k2_funct_1(X0)) = X0 ),
% 11.60/1.98      inference(cnf_transformation,[],[f97]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1741,plain,
% 11.60/1.98      ( k2_funct_1(k2_funct_1(X0)) = X0
% 11.60/1.98      | v2_funct_1(X0) != iProver_top
% 11.60/1.98      | v1_relat_1(X0) != iProver_top
% 11.60/1.98      | v1_funct_1(X0) != iProver_top ),
% 11.60/1.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_4124,plain,
% 11.60/1.98      ( k2_funct_1(k2_funct_1(sK3)) = sK3
% 11.60/1.98      | v1_relat_1(sK3) != iProver_top
% 11.60/1.98      | v1_funct_1(sK3) != iProver_top ),
% 11.60/1.98      inference(superposition,[status(thm)],[c_1730,c_1741]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_46,negated_conjecture,
% 11.60/1.98      ( v1_funct_1(sK3) ),
% 11.60/1.98      inference(cnf_transformation,[],[f116]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_47,plain,
% 11.60/1.98      ( v1_funct_1(sK3) = iProver_top ),
% 11.60/1.98      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_54,plain,
% 11.60/1.98      ( v2_funct_1(sK3) = iProver_top ),
% 11.60/1.98      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_2469,plain,
% 11.60/1.98      ( ~ v2_funct_1(sK3)
% 11.60/1.98      | ~ v1_relat_1(sK3)
% 11.60/1.98      | ~ v1_funct_1(sK3)
% 11.60/1.98      | k2_funct_1(k2_funct_1(sK3)) = sK3 ),
% 11.60/1.98      inference(instantiation,[status(thm)],[c_19]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_2470,plain,
% 11.60/1.98      ( k2_funct_1(k2_funct_1(sK3)) = sK3
% 11.60/1.98      | v2_funct_1(sK3) != iProver_top
% 11.60/1.98      | v1_relat_1(sK3) != iProver_top
% 11.60/1.98      | v1_funct_1(sK3) != iProver_top ),
% 11.60/1.98      inference(predicate_to_equality,[status(thm)],[c_2469]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_44,negated_conjecture,
% 11.60/1.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
% 11.60/1.98      inference(cnf_transformation,[],[f118]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1727,plain,
% 11.60/1.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
% 11.60/1.98      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_21,plain,
% 11.60/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.60/1.98      | v1_relat_1(X0) ),
% 11.60/1.98      inference(cnf_transformation,[],[f99]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1739,plain,
% 11.60/1.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 11.60/1.98      | v1_relat_1(X0) = iProver_top ),
% 11.60/1.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_2683,plain,
% 11.60/1.98      ( v1_relat_1(sK3) = iProver_top ),
% 11.60/1.98      inference(superposition,[status(thm)],[c_1727,c_1739]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_4424,plain,
% 11.60/1.98      ( k2_funct_1(k2_funct_1(sK3)) = sK3 ),
% 11.60/1.98      inference(global_propositional_subsumption,
% 11.60/1.98                [status(thm)],
% 11.60/1.98                [c_4124,c_47,c_54,c_2470,c_2683]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_13,plain,
% 11.60/1.98      ( ~ v2_funct_1(X0)
% 11.60/1.98      | ~ v1_relat_1(X0)
% 11.60/1.98      | ~ v1_funct_1(X0)
% 11.60/1.98      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 11.60/1.98      inference(cnf_transformation,[],[f92]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1747,plain,
% 11.60/1.98      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 11.60/1.98      | v2_funct_1(X0) != iProver_top
% 11.60/1.98      | v1_relat_1(X0) != iProver_top
% 11.60/1.98      | v1_funct_1(X0) != iProver_top ),
% 11.60/1.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_4558,plain,
% 11.60/1.98      ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
% 11.60/1.98      | v1_relat_1(sK3) != iProver_top
% 11.60/1.98      | v1_funct_1(sK3) != iProver_top ),
% 11.60/1.98      inference(superposition,[status(thm)],[c_1730,c_1747]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_22,plain,
% 11.60/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.60/1.98      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 11.60/1.98      inference(cnf_transformation,[],[f100]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1738,plain,
% 11.60/1.98      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 11.60/1.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 11.60/1.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_2758,plain,
% 11.60/1.98      ( k1_relset_1(sK2,sK2,sK3) = k1_relat_1(sK3) ),
% 11.60/1.98      inference(superposition,[status(thm)],[c_1727,c_1738]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_37,plain,
% 11.60/1.98      ( ~ v1_funct_2(X0,X1,X1)
% 11.60/1.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 11.60/1.98      | ~ v1_funct_1(X0)
% 11.60/1.98      | k1_relset_1(X1,X1,X0) = X1 ),
% 11.60/1.98      inference(cnf_transformation,[],[f115]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_45,negated_conjecture,
% 11.60/1.98      ( v1_funct_2(sK3,sK2,sK2) ),
% 11.60/1.98      inference(cnf_transformation,[],[f117]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_910,plain,
% 11.60/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 11.60/1.98      | ~ v1_funct_1(X0)
% 11.60/1.98      | k1_relset_1(X1,X1,X0) = X1
% 11.60/1.98      | sK3 != X0
% 11.60/1.98      | sK2 != X1 ),
% 11.60/1.98      inference(resolution_lifted,[status(thm)],[c_37,c_45]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_911,plain,
% 11.60/1.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
% 11.60/1.98      | ~ v1_funct_1(sK3)
% 11.60/1.98      | k1_relset_1(sK2,sK2,sK3) = sK2 ),
% 11.60/1.98      inference(unflattening,[status(thm)],[c_910]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_913,plain,
% 11.60/1.98      ( k1_relset_1(sK2,sK2,sK3) = sK2 ),
% 11.60/1.98      inference(global_propositional_subsumption,
% 11.60/1.98                [status(thm)],
% 11.60/1.98                [c_911,c_46,c_44]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_2759,plain,
% 11.60/1.98      ( k1_relat_1(sK3) = sK2 ),
% 11.60/1.98      inference(light_normalisation,[status(thm)],[c_2758,c_913]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_4559,plain,
% 11.60/1.98      ( k2_relat_1(k2_funct_1(sK3)) = sK2
% 11.60/1.98      | v1_relat_1(sK3) != iProver_top
% 11.60/1.98      | v1_funct_1(sK3) != iProver_top ),
% 11.60/1.98      inference(light_normalisation,[status(thm)],[c_4558,c_2759]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_5082,plain,
% 11.60/1.98      ( k2_relat_1(k2_funct_1(sK3)) = sK2 ),
% 11.60/1.98      inference(global_propositional_subsumption,
% 11.60/1.98                [status(thm)],
% 11.60/1.98                [c_4559,c_47,c_2683]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_41,negated_conjecture,
% 11.60/1.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
% 11.60/1.98      inference(cnf_transformation,[],[f121]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1729,plain,
% 11.60/1.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
% 11.60/1.98      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_33,plain,
% 11.60/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.60/1.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 11.60/1.98      | ~ v1_funct_1(X0)
% 11.60/1.98      | ~ v1_funct_1(X3)
% 11.60/1.98      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 11.60/1.98      inference(cnf_transformation,[],[f111]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1731,plain,
% 11.60/1.98      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 11.60/1.98      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 11.60/1.98      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.60/1.98      | v1_funct_1(X5) != iProver_top
% 11.60/1.98      | v1_funct_1(X4) != iProver_top ),
% 11.60/1.98      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_5369,plain,
% 11.60/1.98      ( k1_partfun1(X0,X1,sK2,sK2,X2,sK3) = k5_relat_1(X2,sK3)
% 11.60/1.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.60/1.98      | v1_funct_1(X2) != iProver_top
% 11.60/1.98      | v1_funct_1(sK3) != iProver_top ),
% 11.60/1.98      inference(superposition,[status(thm)],[c_1727,c_1731]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_5680,plain,
% 11.60/1.98      ( v1_funct_1(X2) != iProver_top
% 11.60/1.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.60/1.98      | k1_partfun1(X0,X1,sK2,sK2,X2,sK3) = k5_relat_1(X2,sK3) ),
% 11.60/1.98      inference(global_propositional_subsumption,
% 11.60/1.98                [status(thm)],
% 11.60/1.98                [c_5369,c_47]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_5681,plain,
% 11.60/1.98      ( k1_partfun1(X0,X1,sK2,sK2,X2,sK3) = k5_relat_1(X2,sK3)
% 11.60/1.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.60/1.98      | v1_funct_1(X2) != iProver_top ),
% 11.60/1.98      inference(renaming,[status(thm)],[c_5680]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_5690,plain,
% 11.60/1.98      ( k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3) = k5_relat_1(sK4,sK3)
% 11.60/1.98      | v1_funct_1(sK4) != iProver_top ),
% 11.60/1.98      inference(superposition,[status(thm)],[c_1729,c_5681]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_25,plain,
% 11.60/1.98      ( ~ r2_relset_1(X0,X1,X2,X3)
% 11.60/1.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.60/1.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.60/1.98      | X3 = X2 ),
% 11.60/1.98      inference(cnf_transformation,[],[f102]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_40,negated_conjecture,
% 11.60/1.98      ( r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3),sK3) ),
% 11.60/1.98      inference(cnf_transformation,[],[f122]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_661,plain,
% 11.60/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.60/1.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.60/1.98      | X3 = X0
% 11.60/1.98      | k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3) != X0
% 11.60/1.98      | sK3 != X3
% 11.60/1.98      | sK2 != X2
% 11.60/1.98      | sK2 != X1 ),
% 11.60/1.98      inference(resolution_lifted,[status(thm)],[c_25,c_40]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_662,plain,
% 11.60/1.98      ( ~ m1_subset_1(k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
% 11.60/1.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
% 11.60/1.98      | sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3) ),
% 11.60/1.98      inference(unflattening,[status(thm)],[c_661]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_664,plain,
% 11.60/1.98      ( ~ m1_subset_1(k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
% 11.60/1.98      | sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3) ),
% 11.60/1.98      inference(global_propositional_subsumption,
% 11.60/1.98                [status(thm)],
% 11.60/1.98                [c_662,c_44]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1723,plain,
% 11.60/1.98      ( sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3)
% 11.60/1.98      | m1_subset_1(k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top ),
% 11.60/1.98      inference(predicate_to_equality,[status(thm)],[c_664]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_43,negated_conjecture,
% 11.60/1.98      ( v1_funct_1(sK4) ),
% 11.60/1.98      inference(cnf_transformation,[],[f119]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_30,plain,
% 11.60/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.60/1.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 11.60/1.98      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 11.60/1.98      | ~ v1_funct_1(X0)
% 11.60/1.98      | ~ v1_funct_1(X3) ),
% 11.60/1.98      inference(cnf_transformation,[],[f109]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1839,plain,
% 11.60/1.98      ( m1_subset_1(k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
% 11.60/1.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
% 11.60/1.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
% 11.60/1.98      | ~ v1_funct_1(sK3)
% 11.60/1.98      | ~ v1_funct_1(sK4) ),
% 11.60/1.98      inference(instantiation,[status(thm)],[c_30]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_2481,plain,
% 11.60/1.98      ( sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3) ),
% 11.60/1.98      inference(global_propositional_subsumption,
% 11.60/1.98                [status(thm)],
% 11.60/1.98                [c_1723,c_46,c_44,c_43,c_41,c_662,c_1839]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_5692,plain,
% 11.60/1.98      ( k5_relat_1(sK4,sK3) = sK3 | v1_funct_1(sK4) != iProver_top ),
% 11.60/1.98      inference(light_normalisation,[status(thm)],[c_5690,c_2481]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_50,plain,
% 11.60/1.98      ( v1_funct_1(sK4) = iProver_top ),
% 11.60/1.98      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_6025,plain,
% 11.60/1.98      ( k5_relat_1(sK4,sK3) = sK3 ),
% 11.60/1.98      inference(global_propositional_subsumption,
% 11.60/1.98                [status(thm)],
% 11.60/1.98                [c_5692,c_50]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_11,plain,
% 11.60/1.98      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X0))
% 11.60/1.98      | ~ v2_funct_1(X1)
% 11.60/1.98      | ~ v1_relat_1(X0)
% 11.60/1.98      | ~ v1_relat_1(X1)
% 11.60/1.98      | ~ v1_funct_1(X0)
% 11.60/1.98      | ~ v1_funct_1(X1)
% 11.60/1.98      | k5_relat_1(X0,X1) != X1
% 11.60/1.98      | k6_relat_1(k1_relat_1(X0)) = X0
% 11.60/1.98      | k1_relat_1(X1) != k1_relat_1(X0) ),
% 11.60/1.98      inference(cnf_transformation,[],[f125]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1749,plain,
% 11.60/1.98      ( k5_relat_1(X0,X1) != X1
% 11.60/1.98      | k6_relat_1(k1_relat_1(X0)) = X0
% 11.60/1.98      | k1_relat_1(X1) != k1_relat_1(X0)
% 11.60/1.98      | r1_tarski(k2_relat_1(X0),k1_relat_1(X0)) != iProver_top
% 11.60/1.98      | v2_funct_1(X1) != iProver_top
% 11.60/1.98      | v1_relat_1(X0) != iProver_top
% 11.60/1.98      | v1_relat_1(X1) != iProver_top
% 11.60/1.98      | v1_funct_1(X0) != iProver_top
% 11.60/1.98      | v1_funct_1(X1) != iProver_top ),
% 11.60/1.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_6027,plain,
% 11.60/1.98      ( k6_relat_1(k1_relat_1(sK4)) = sK4
% 11.60/1.98      | k1_relat_1(sK4) != k1_relat_1(sK3)
% 11.60/1.98      | r1_tarski(k2_relat_1(sK4),k1_relat_1(sK4)) != iProver_top
% 11.60/1.98      | v2_funct_1(sK3) != iProver_top
% 11.60/1.98      | v1_relat_1(sK3) != iProver_top
% 11.60/1.98      | v1_relat_1(sK4) != iProver_top
% 11.60/1.98      | v1_funct_1(sK3) != iProver_top
% 11.60/1.98      | v1_funct_1(sK4) != iProver_top ),
% 11.60/1.98      inference(superposition,[status(thm)],[c_6025,c_1749]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_2757,plain,
% 11.60/1.98      ( k1_relset_1(sK2,sK2,sK4) = k1_relat_1(sK4) ),
% 11.60/1.98      inference(superposition,[status(thm)],[c_1729,c_1738]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_42,negated_conjecture,
% 11.60/1.98      ( v1_funct_2(sK4,sK2,sK2) ),
% 11.60/1.98      inference(cnf_transformation,[],[f120]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_902,plain,
% 11.60/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 11.60/1.98      | ~ v1_funct_1(X0)
% 11.60/1.98      | k1_relset_1(X1,X1,X0) = X1
% 11.60/1.98      | sK4 != X0
% 11.60/1.98      | sK2 != X1 ),
% 11.60/1.98      inference(resolution_lifted,[status(thm)],[c_37,c_42]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_903,plain,
% 11.60/1.98      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
% 11.60/1.98      | ~ v1_funct_1(sK4)
% 11.60/1.98      | k1_relset_1(sK2,sK2,sK4) = sK2 ),
% 11.60/1.98      inference(unflattening,[status(thm)],[c_902]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_905,plain,
% 11.60/1.98      ( k1_relset_1(sK2,sK2,sK4) = sK2 ),
% 11.60/1.98      inference(global_propositional_subsumption,
% 11.60/1.98                [status(thm)],
% 11.60/1.98                [c_903,c_43,c_41]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_2760,plain,
% 11.60/1.98      ( k1_relat_1(sK4) = sK2 ),
% 11.60/1.98      inference(light_normalisation,[status(thm)],[c_2757,c_905]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_6028,plain,
% 11.60/1.98      ( k6_relat_1(sK2) = sK4
% 11.60/1.98      | sK2 != sK2
% 11.60/1.98      | r1_tarski(k2_relat_1(sK4),sK2) != iProver_top
% 11.60/1.98      | v2_funct_1(sK3) != iProver_top
% 11.60/1.98      | v1_relat_1(sK3) != iProver_top
% 11.60/1.98      | v1_relat_1(sK4) != iProver_top
% 11.60/1.98      | v1_funct_1(sK3) != iProver_top
% 11.60/1.98      | v1_funct_1(sK4) != iProver_top ),
% 11.60/1.98      inference(light_normalisation,[status(thm)],[c_6027,c_2759,c_2760]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_6029,plain,
% 11.60/1.98      ( k6_relat_1(sK2) = sK4
% 11.60/1.98      | r1_tarski(k2_relat_1(sK4),sK2) != iProver_top
% 11.60/1.98      | v2_funct_1(sK3) != iProver_top
% 11.60/1.98      | v1_relat_1(sK3) != iProver_top
% 11.60/1.98      | v1_relat_1(sK4) != iProver_top
% 11.60/1.98      | v1_funct_1(sK3) != iProver_top
% 11.60/1.98      | v1_funct_1(sK4) != iProver_top ),
% 11.60/1.98      inference(equality_resolution_simp,[status(thm)],[c_6028]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_2682,plain,
% 11.60/1.98      ( v1_relat_1(sK4) = iProver_top ),
% 11.60/1.98      inference(superposition,[status(thm)],[c_1729,c_1739]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_27,plain,
% 11.60/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.60/1.98      | k7_relset_1(X1,X2,X0,X1) = k2_relset_1(X1,X2,X0) ),
% 11.60/1.98      inference(cnf_transformation,[],[f104]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1735,plain,
% 11.60/1.98      ( k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)
% 11.60/1.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 11.60/1.98      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_3542,plain,
% 11.60/1.98      ( k7_relset_1(sK2,sK2,sK4,sK2) = k2_relset_1(sK2,sK2,sK4) ),
% 11.60/1.98      inference(superposition,[status(thm)],[c_1729,c_1735]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_23,plain,
% 11.60/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.60/1.98      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 11.60/1.98      inference(cnf_transformation,[],[f101]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1737,plain,
% 11.60/1.98      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 11.60/1.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 11.60/1.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_2748,plain,
% 11.60/1.98      ( k2_relset_1(sK2,sK2,sK4) = k2_relat_1(sK4) ),
% 11.60/1.98      inference(superposition,[status(thm)],[c_1729,c_1737]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_3545,plain,
% 11.60/1.98      ( k7_relset_1(sK2,sK2,sK4,sK2) = k2_relat_1(sK4) ),
% 11.60/1.98      inference(light_normalisation,[status(thm)],[c_3542,c_2748]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_36,plain,
% 11.60/1.98      ( ~ v1_funct_2(X0,X1,X2)
% 11.60/1.98      | r1_tarski(k7_relset_1(X1,X2,X0,X3),X2)
% 11.60/1.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.60/1.98      | ~ v1_funct_1(X0) ),
% 11.60/1.98      inference(cnf_transformation,[],[f114]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_804,plain,
% 11.60/1.98      ( r1_tarski(k7_relset_1(X0,X1,X2,X3),X1)
% 11.60/1.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.60/1.98      | ~ v1_funct_1(X2)
% 11.60/1.98      | sK4 != X2
% 11.60/1.98      | sK2 != X0
% 11.60/1.98      | sK2 != X1 ),
% 11.60/1.98      inference(resolution_lifted,[status(thm)],[c_36,c_42]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_805,plain,
% 11.60/1.98      ( r1_tarski(k7_relset_1(sK2,sK2,sK4,X0),sK2)
% 11.60/1.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
% 11.60/1.98      | ~ v1_funct_1(sK4) ),
% 11.60/1.98      inference(unflattening,[status(thm)],[c_804]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_809,plain,
% 11.60/1.98      ( r1_tarski(k7_relset_1(sK2,sK2,sK4,X0),sK2) ),
% 11.60/1.98      inference(global_propositional_subsumption,
% 11.60/1.98                [status(thm)],
% 11.60/1.98                [c_805,c_43,c_41]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1721,plain,
% 11.60/1.98      ( r1_tarski(k7_relset_1(sK2,sK2,sK4,X0),sK2) = iProver_top ),
% 11.60/1.98      inference(predicate_to_equality,[status(thm)],[c_809]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_3756,plain,
% 11.60/1.98      ( r1_tarski(k2_relat_1(sK4),sK2) = iProver_top ),
% 11.60/1.98      inference(superposition,[status(thm)],[c_3545,c_1721]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_19383,plain,
% 11.60/1.98      ( k6_relat_1(sK2) = sK4 ),
% 11.60/1.98      inference(global_propositional_subsumption,
% 11.60/1.98                [status(thm)],
% 11.60/1.98                [c_6029,c_47,c_50,c_54,c_2682,c_2683,c_3756]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_18,plain,
% 11.60/1.98      ( ~ v2_funct_1(X0)
% 11.60/1.98      | ~ v1_relat_1(X0)
% 11.60/1.98      | ~ v1_funct_1(X0)
% 11.60/1.98      | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ),
% 11.60/1.98      inference(cnf_transformation,[],[f95]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1742,plain,
% 11.60/1.98      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
% 11.60/1.98      | v2_funct_1(X0) != iProver_top
% 11.60/1.98      | v1_relat_1(X0) != iProver_top
% 11.60/1.98      | v1_funct_1(X0) != iProver_top ),
% 11.60/1.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_4692,plain,
% 11.60/1.98      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_relat_1(k1_relat_1(sK3))
% 11.60/1.98      | v1_relat_1(sK3) != iProver_top
% 11.60/1.98      | v1_funct_1(sK3) != iProver_top ),
% 11.60/1.98      inference(superposition,[status(thm)],[c_1730,c_1742]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_4693,plain,
% 11.60/1.98      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_relat_1(sK2)
% 11.60/1.98      | v1_relat_1(sK3) != iProver_top
% 11.60/1.98      | v1_funct_1(sK3) != iProver_top ),
% 11.60/1.98      inference(light_normalisation,[status(thm)],[c_4692,c_2759]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_5107,plain,
% 11.60/1.98      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_relat_1(sK2) ),
% 11.60/1.98      inference(global_propositional_subsumption,
% 11.60/1.98                [status(thm)],
% 11.60/1.98                [c_4693,c_47,c_2683]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_19387,plain,
% 11.60/1.98      ( k5_relat_1(sK3,k2_funct_1(sK3)) = sK4 ),
% 11.60/1.98      inference(demodulation,[status(thm)],[c_19383,c_5107]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_26164,plain,
% 11.60/1.98      ( k2_relat_1(sK4) = sK2
% 11.60/1.98      | v1_relat_1(sK3) != iProver_top
% 11.60/1.98      | v1_funct_1(sK3) != iProver_top ),
% 11.60/1.98      inference(light_normalisation,
% 11.60/1.98                [status(thm)],
% 11.60/1.98                [c_26161,c_4424,c_5082,c_19387]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_8267,plain,
% 11.60/1.98      ( ~ r2_hidden(X0,X1)
% 11.60/1.98      | ~ m1_subset_1(X1,k1_zfmisc_1(sK0(sK0(X2))))
% 11.60/1.98      | ~ v1_xboole_0(sK0(sK0(X2))) ),
% 11.60/1.98      inference(instantiation,[status(thm)],[c_5]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_16234,plain,
% 11.60/1.98      ( ~ r2_hidden(sK1(sK2,sK3,sK4),X0)
% 11.60/1.98      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0(sK0(X1))))
% 11.60/1.98      | ~ v1_xboole_0(sK0(sK0(X1))) ),
% 11.60/1.98      inference(instantiation,[status(thm)],[c_8267]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_23537,plain,
% 11.60/1.98      ( ~ r2_hidden(sK1(sK2,sK3,sK4),k1_xboole_0)
% 11.60/1.98      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0(sK0(X0))))
% 11.60/1.98      | ~ v1_xboole_0(sK0(sK0(X0))) ),
% 11.60/1.98      inference(instantiation,[status(thm)],[c_16234]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1031,plain,( X0 = X0 ),theory(equality) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_22641,plain,
% 11.60/1.98      ( sK1(sK2,sK3,sK4) = sK1(sK2,sK3,sK4) ),
% 11.60/1.98      inference(instantiation,[status(thm)],[c_1031]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_2,plain,
% 11.60/1.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 11.60/1.98      inference(cnf_transformation,[],[f80]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_3500,plain,
% 11.60/1.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0(X0))) ),
% 11.60/1.98      inference(instantiation,[status(thm)],[c_2]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_20411,plain,
% 11.60/1.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0(sK0(X0)))) ),
% 11.60/1.98      inference(instantiation,[status(thm)],[c_3500]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_12,plain,
% 11.60/1.98      ( v2_funct_1(k6_relat_1(X0)) ),
% 11.60/1.98      inference(cnf_transformation,[],[f90]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1748,plain,
% 11.60/1.98      ( v2_funct_1(k6_relat_1(X0)) = iProver_top ),
% 11.60/1.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_4691,plain,
% 11.60/1.98      ( k5_relat_1(k6_relat_1(X0),k2_funct_1(k6_relat_1(X0))) = k6_relat_1(k1_relat_1(k6_relat_1(X0)))
% 11.60/1.98      | v1_relat_1(k6_relat_1(X0)) != iProver_top
% 11.60/1.98      | v1_funct_1(k6_relat_1(X0)) != iProver_top ),
% 11.60/1.98      inference(superposition,[status(thm)],[c_1748,c_1742]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_19393,plain,
% 11.60/1.98      ( k5_relat_1(k6_relat_1(sK2),k2_funct_1(k6_relat_1(sK2))) = k6_relat_1(k1_relat_1(k6_relat_1(sK2)))
% 11.60/1.98      | v1_relat_1(sK4) != iProver_top
% 11.60/1.98      | v1_funct_1(k6_relat_1(sK2)) != iProver_top ),
% 11.60/1.98      inference(superposition,[status(thm)],[c_19383,c_4691]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_19413,plain,
% 11.60/1.98      ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_relat_1(k1_relat_1(sK4))
% 11.60/1.98      | v1_relat_1(sK4) != iProver_top
% 11.60/1.98      | v1_funct_1(sK4) != iProver_top ),
% 11.60/1.98      inference(demodulation,[status(thm)],[c_19393,c_19383]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_19414,plain,
% 11.60/1.98      ( k5_relat_1(sK4,k2_funct_1(sK4)) = sK4
% 11.60/1.98      | v1_relat_1(sK4) != iProver_top
% 11.60/1.98      | v1_funct_1(sK4) != iProver_top ),
% 11.60/1.98      inference(light_normalisation,
% 11.60/1.98                [status(thm)],
% 11.60/1.98                [c_19413,c_2760,c_19383]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_19539,plain,
% 11.60/1.98      ( k5_relat_1(sK4,k2_funct_1(sK4)) = sK4 ),
% 11.60/1.98      inference(global_propositional_subsumption,
% 11.60/1.98                [status(thm)],
% 11.60/1.98                [c_19414,c_50,c_2682]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_35,plain,
% 11.60/1.98      ( ~ v1_funct_2(X0,X1,X2)
% 11.60/1.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.60/1.98      | ~ v2_funct_1(X0)
% 11.60/1.98      | ~ v1_funct_1(X0)
% 11.60/1.98      | k2_relset_1(X1,X2,X0) != X2
% 11.60/1.98      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 11.60/1.98      | k1_xboole_0 = X2 ),
% 11.60/1.98      inference(cnf_transformation,[],[f112]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_819,plain,
% 11.60/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.60/1.98      | ~ v2_funct_1(X0)
% 11.60/1.98      | ~ v1_funct_1(X0)
% 11.60/1.98      | k2_relset_1(X1,X2,X0) != X2
% 11.60/1.98      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 11.60/1.98      | sK4 != X0
% 11.60/1.98      | sK2 != X1
% 11.60/1.98      | sK2 != X2
% 11.60/1.98      | k1_xboole_0 = X2 ),
% 11.60/1.98      inference(resolution_lifted,[status(thm)],[c_35,c_42]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_820,plain,
% 11.60/1.98      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
% 11.60/1.98      | ~ v2_funct_1(sK4)
% 11.60/1.98      | ~ v1_funct_1(sK4)
% 11.60/1.98      | k2_relset_1(sK2,sK2,sK4) != sK2
% 11.60/1.98      | k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(sK2)
% 11.60/1.98      | k1_xboole_0 = sK2 ),
% 11.60/1.98      inference(unflattening,[status(thm)],[c_819]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_822,plain,
% 11.60/1.98      ( ~ v2_funct_1(sK4)
% 11.60/1.98      | k2_relset_1(sK2,sK2,sK4) != sK2
% 11.60/1.98      | k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(sK2)
% 11.60/1.98      | k1_xboole_0 = sK2 ),
% 11.60/1.98      inference(global_propositional_subsumption,
% 11.60/1.98                [status(thm)],
% 11.60/1.98                [c_820,c_43,c_41]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1720,plain,
% 11.60/1.98      ( k2_relset_1(sK2,sK2,sK4) != sK2
% 11.60/1.98      | k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(sK2)
% 11.60/1.98      | k1_xboole_0 = sK2
% 11.60/1.98      | v2_funct_1(sK4) != iProver_top ),
% 11.60/1.98      inference(predicate_to_equality,[status(thm)],[c_822]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_3082,plain,
% 11.60/1.98      ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(sK2)
% 11.60/1.98      | k2_relat_1(sK4) != sK2
% 11.60/1.98      | sK2 = k1_xboole_0
% 11.60/1.98      | v2_funct_1(sK4) != iProver_top ),
% 11.60/1.98      inference(demodulation,[status(thm)],[c_2748,c_1720]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_19541,plain,
% 11.60/1.98      ( k6_partfun1(sK2) = sK4
% 11.60/1.98      | k2_relat_1(sK4) != sK2
% 11.60/1.98      | sK2 = k1_xboole_0
% 11.60/1.98      | v2_funct_1(sK4) != iProver_top ),
% 11.60/1.98      inference(demodulation,[status(thm)],[c_19539,c_3082]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_19542,plain,
% 11.60/1.98      ( ~ v2_funct_1(sK4)
% 11.60/1.98      | k6_partfun1(sK2) = sK4
% 11.60/1.98      | k2_relat_1(sK4) != sK2
% 11.60/1.98      | sK2 = k1_xboole_0 ),
% 11.60/1.98      inference(predicate_to_equality_rev,[status(thm)],[c_19541]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1032,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1947,plain,
% 11.60/1.98      ( X0 != X1 | sK4 != X1 | sK4 = X0 ),
% 11.60/1.98      inference(instantiation,[status(thm)],[c_1032]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_2156,plain,
% 11.60/1.98      ( X0 != sK4 | sK4 = X0 | sK4 != sK4 ),
% 11.60/1.98      inference(instantiation,[status(thm)],[c_1947]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_17732,plain,
% 11.60/1.98      ( k6_relat_1(X0) != sK4 | sK4 = k6_relat_1(X0) | sK4 != sK4 ),
% 11.60/1.98      inference(instantiation,[status(thm)],[c_2156]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_17736,plain,
% 11.60/1.98      ( k6_relat_1(sK2) != sK4 | sK4 = k6_relat_1(sK2) | sK4 != sK4 ),
% 11.60/1.98      inference(instantiation,[status(thm)],[c_17732]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1036,plain,
% 11.60/1.98      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 11.60/1.98      theory(equality) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_3476,plain,
% 11.60/1.98      ( r2_hidden(X0,X1)
% 11.60/1.98      | ~ r2_hidden(sK1(X2,sK3,k6_partfun1(sK2)),X2)
% 11.60/1.98      | X1 != X2
% 11.60/1.98      | X0 != sK1(X2,sK3,k6_partfun1(sK2)) ),
% 11.60/1.98      inference(instantiation,[status(thm)],[c_1036]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_6297,plain,
% 11.60/1.98      ( ~ r2_hidden(sK1(X0,sK3,k6_partfun1(sK2)),X0)
% 11.60/1.98      | r2_hidden(sK1(X0,sK3,k6_partfun1(sK2)),X1)
% 11.60/1.98      | X1 != X0
% 11.60/1.98      | sK1(X0,sK3,k6_partfun1(sK2)) != sK1(X0,sK3,k6_partfun1(sK2)) ),
% 11.60/1.98      inference(instantiation,[status(thm)],[c_3476]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_12111,plain,
% 11.60/1.98      ( ~ r2_hidden(sK1(X0,sK3,k6_partfun1(sK2)),X0)
% 11.60/1.98      | r2_hidden(sK1(X0,sK3,k6_partfun1(sK2)),k1_xboole_0)
% 11.60/1.98      | sK1(X0,sK3,k6_partfun1(sK2)) != sK1(X0,sK3,k6_partfun1(sK2))
% 11.60/1.98      | k1_xboole_0 != X0 ),
% 11.60/1.98      inference(instantiation,[status(thm)],[c_6297]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_12114,plain,
% 11.60/1.98      ( ~ r2_hidden(sK1(sK2,sK3,k6_partfun1(sK2)),sK2)
% 11.60/1.98      | r2_hidden(sK1(sK2,sK3,k6_partfun1(sK2)),k1_xboole_0)
% 11.60/1.98      | sK1(sK2,sK3,k6_partfun1(sK2)) != sK1(sK2,sK3,k6_partfun1(sK2))
% 11.60/1.98      | k1_xboole_0 != sK2 ),
% 11.60/1.98      inference(instantiation,[status(thm)],[c_12111]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_3479,plain,
% 11.60/1.98      ( r2_hidden(X0,X1)
% 11.60/1.98      | ~ r2_hidden(sK1(sK2,sK3,sK4),sK2)
% 11.60/1.98      | X0 != sK1(sK2,sK3,sK4)
% 11.60/1.98      | X1 != sK2 ),
% 11.60/1.98      inference(instantiation,[status(thm)],[c_1036]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_5432,plain,
% 11.60/1.98      ( r2_hidden(sK1(sK2,sK3,sK4),X0)
% 11.60/1.98      | ~ r2_hidden(sK1(sK2,sK3,sK4),sK2)
% 11.60/1.98      | X0 != sK2
% 11.60/1.98      | sK1(sK2,sK3,sK4) != sK1(sK2,sK3,sK4) ),
% 11.60/1.98      inference(instantiation,[status(thm)],[c_3479]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_9860,plain,
% 11.60/1.98      ( ~ r2_hidden(sK1(sK2,sK3,sK4),sK2)
% 11.60/1.98      | r2_hidden(sK1(sK2,sK3,sK4),k1_xboole_0)
% 11.60/1.98      | sK1(sK2,sK3,sK4) != sK1(sK2,sK3,sK4)
% 11.60/1.98      | k1_xboole_0 != sK2 ),
% 11.60/1.98      inference(instantiation,[status(thm)],[c_5432]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_4198,plain,
% 11.60/1.98      ( X0 != X1 | k1_xboole_0 != X1 | k1_xboole_0 = X0 ),
% 11.60/1.98      inference(instantiation,[status(thm)],[c_1032]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_8135,plain,
% 11.60/1.98      ( X0 != k1_xboole_0
% 11.60/1.98      | k1_xboole_0 = X0
% 11.60/1.98      | k1_xboole_0 != k1_xboole_0 ),
% 11.60/1.98      inference(instantiation,[status(thm)],[c_4198]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_8136,plain,
% 11.60/1.98      ( sK2 != k1_xboole_0
% 11.60/1.98      | k1_xboole_0 = sK2
% 11.60/1.98      | k1_xboole_0 != k1_xboole_0 ),
% 11.60/1.98      inference(instantiation,[status(thm)],[c_8135]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_5947,plain,
% 11.60/1.98      ( k1_xboole_0 = k1_xboole_0 ),
% 11.60/1.98      inference(instantiation,[status(thm)],[c_1031]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_29,plain,
% 11.60/1.98      ( r2_relset_1(X0,X0,X1,X2)
% 11.60/1.98      | r2_hidden(sK1(X0,X1,X2),X0)
% 11.60/1.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 11.60/1.98      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 11.60/1.98      inference(cnf_transformation,[],[f106]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_625,plain,
% 11.60/1.98      ( r2_hidden(sK1(X0,X1,X2),X0)
% 11.60/1.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 11.60/1.98      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 11.60/1.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 11.60/1.98      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 11.60/1.98      | X0 != X4
% 11.60/1.98      | X0 != X5
% 11.60/1.98      | X1 != X3
% 11.60/1.98      | X2 != X6
% 11.60/1.98      | X6 = X3 ),
% 11.60/1.98      inference(resolution_lifted,[status(thm)],[c_25,c_29]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_626,plain,
% 11.60/1.98      ( r2_hidden(sK1(X0,X1,X2),X0)
% 11.60/1.98      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 11.60/1.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 11.60/1.98      | X2 = X1 ),
% 11.60/1.98      inference(unflattening,[status(thm)],[c_625]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1725,plain,
% 11.60/1.98      ( X0 = X1
% 11.60/1.98      | r2_hidden(sK1(X2,X1,X0),X2) = iProver_top
% 11.60/1.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) != iProver_top
% 11.60/1.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) != iProver_top ),
% 11.60/1.98      inference(predicate_to_equality,[status(thm)],[c_626]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_3936,plain,
% 11.60/1.98      ( sK3 = X0
% 11.60/1.98      | r2_hidden(sK1(sK2,sK3,X0),sK2) = iProver_top
% 11.60/1.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top ),
% 11.60/1.98      inference(superposition,[status(thm)],[c_1727,c_1725]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_4810,plain,
% 11.60/1.98      ( sK3 = sK4 | r2_hidden(sK1(sK2,sK3,sK4),sK2) = iProver_top ),
% 11.60/1.98      inference(superposition,[status(thm)],[c_1729,c_3936]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_4815,plain,
% 11.60/1.98      ( r2_hidden(sK1(sK2,sK3,sK4),sK2) | sK3 = sK4 ),
% 11.60/1.98      inference(predicate_to_equality_rev,[status(thm)],[c_4810]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_32,plain,
% 11.60/1.98      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 11.60/1.98      inference(cnf_transformation,[],[f110]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1732,plain,
% 11.60/1.98      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 11.60/1.98      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_4809,plain,
% 11.60/1.98      ( k6_partfun1(sK2) = sK3
% 11.60/1.98      | r2_hidden(sK1(sK2,sK3,k6_partfun1(sK2)),sK2) = iProver_top ),
% 11.60/1.98      inference(superposition,[status(thm)],[c_1732,c_3936]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_4814,plain,
% 11.60/1.98      ( r2_hidden(sK1(sK2,sK3,k6_partfun1(sK2)),sK2)
% 11.60/1.98      | k6_partfun1(sK2) = sK3 ),
% 11.60/1.98      inference(predicate_to_equality_rev,[status(thm)],[c_4809]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_4529,plain,
% 11.60/1.98      ( sK1(X0,sK3,k6_partfun1(sK2)) = sK1(X0,sK3,k6_partfun1(sK2)) ),
% 11.60/1.98      inference(instantiation,[status(thm)],[c_1031]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_4530,plain,
% 11.60/1.98      ( sK1(sK2,sK3,k6_partfun1(sK2)) = sK1(sK2,sK3,k6_partfun1(sK2)) ),
% 11.60/1.98      inference(instantiation,[status(thm)],[c_4529]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1,plain,
% 11.60/1.98      ( m1_subset_1(sK0(X0),k1_zfmisc_1(X0)) ),
% 11.60/1.98      inference(cnf_transformation,[],[f78]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_3974,plain,
% 11.60/1.98      ( m1_subset_1(sK0(sK0(X0)),k1_zfmisc_1(sK0(X0))) ),
% 11.60/1.98      inference(instantiation,[status(thm)],[c_1]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_3,plain,
% 11.60/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.60/1.98      | ~ v1_xboole_0(X1)
% 11.60/1.98      | v1_xboole_0(X0) ),
% 11.60/1.98      inference(cnf_transformation,[],[f81]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_2131,plain,
% 11.60/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0(X1)))
% 11.60/1.98      | v1_xboole_0(X0)
% 11.60/1.98      | ~ v1_xboole_0(sK0(X1)) ),
% 11.60/1.98      inference(instantiation,[status(thm)],[c_3]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_2802,plain,
% 11.60/1.98      ( ~ m1_subset_1(sK0(sK0(X0)),k1_zfmisc_1(sK0(X0)))
% 11.60/1.98      | ~ v1_xboole_0(sK0(X0))
% 11.60/1.98      | v1_xboole_0(sK0(sK0(X0))) ),
% 11.60/1.98      inference(instantiation,[status(thm)],[c_2131]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_38,negated_conjecture,
% 11.60/1.98      ( ~ r2_relset_1(sK2,sK2,sK4,k6_partfun1(sK2)) ),
% 11.60/1.98      inference(cnf_transformation,[],[f124]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_694,plain,
% 11.60/1.98      ( k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3) != sK4
% 11.60/1.98      | k6_partfun1(sK2) != sK3
% 11.60/1.98      | sK2 != sK2 ),
% 11.60/1.98      inference(resolution_lifted,[status(thm)],[c_38,c_40]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1759,plain,
% 11.60/1.98      ( k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3) != sK4
% 11.60/1.98      | k6_partfun1(sK2) != sK3 ),
% 11.60/1.98      inference(equality_resolution_simp,[status(thm)],[c_694]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_2483,plain,
% 11.60/1.98      ( k6_partfun1(sK2) != sK3 | sK3 != sK4 ),
% 11.60/1.98      inference(demodulation,[status(thm)],[c_2481,c_1759]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_2072,plain,
% 11.60/1.98      ( sK4 = sK4 ),
% 11.60/1.98      inference(instantiation,[status(thm)],[c_1031]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1040,plain,
% 11.60/1.98      ( ~ v2_funct_1(X0) | v2_funct_1(X1) | X1 != X0 ),
% 11.60/1.98      theory(equality) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1863,plain,
% 11.60/1.98      ( ~ v2_funct_1(X0) | v2_funct_1(sK4) | sK4 != X0 ),
% 11.60/1.98      inference(instantiation,[status(thm)],[c_1040]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1998,plain,
% 11.60/1.98      ( ~ v2_funct_1(k6_relat_1(X0))
% 11.60/1.98      | v2_funct_1(sK4)
% 11.60/1.98      | sK4 != k6_relat_1(X0) ),
% 11.60/1.98      inference(instantiation,[status(thm)],[c_1863]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_2000,plain,
% 11.60/1.98      ( ~ v2_funct_1(k6_relat_1(sK2))
% 11.60/1.98      | v2_funct_1(sK4)
% 11.60/1.98      | sK4 != k6_relat_1(sK2) ),
% 11.60/1.98      inference(instantiation,[status(thm)],[c_1998]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1828,plain,
% 11.60/1.98      ( k6_partfun1(sK2) != X0 | sK4 != X0 | sK4 = k6_partfun1(sK2) ),
% 11.60/1.98      inference(instantiation,[status(thm)],[c_1032]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1940,plain,
% 11.60/1.98      ( k6_partfun1(sK2) != sK4 | sK4 = k6_partfun1(sK2) | sK4 != sK4 ),
% 11.60/1.98      inference(instantiation,[status(thm)],[c_1828]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_24,plain,
% 11.60/1.98      ( r2_relset_1(X0,X1,X2,X2)
% 11.60/1.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 11.60/1.98      inference(cnf_transformation,[],[f126]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_617,plain,
% 11.60/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.60/1.98      | k6_partfun1(sK2) != X0
% 11.60/1.98      | sK4 != X0
% 11.60/1.98      | sK2 != X2
% 11.60/1.98      | sK2 != X1 ),
% 11.60/1.98      inference(resolution_lifted,[status(thm)],[c_24,c_38]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_618,plain,
% 11.60/1.98      ( ~ m1_subset_1(k6_partfun1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
% 11.60/1.98      | sK4 != k6_partfun1(sK2) ),
% 11.60/1.98      inference(unflattening,[status(thm)],[c_617]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_0,plain,
% 11.60/1.98      ( v1_xboole_0(sK0(X0)) ),
% 11.60/1.98      inference(cnf_transformation,[],[f79]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_132,plain,
% 11.60/1.98      ( v2_funct_1(k6_relat_1(sK2)) ),
% 11.60/1.98      inference(instantiation,[status(thm)],[c_12]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_72,plain,
% 11.60/1.98      ( m1_subset_1(k6_partfun1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
% 11.60/1.98      inference(instantiation,[status(thm)],[c_32]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_30022,plain,
% 11.60/1.98      ( ~ r2_hidden(sK1(sK2,sK3,k6_partfun1(sK2)),k1_xboole_0)
% 11.60/1.98      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0(sK2)))
% 11.60/1.98      | ~ v1_xboole_0(sK0(sK2)) ),
% 11.60/1.98      inference(grounding,[status(thm)],[c_30017:[bind(X0,$fot(sK2))]]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_30023,plain,
% 11.60/1.98      ( ~ r2_hidden(sK1(sK2,sK3,sK4),k1_xboole_0)
% 11.60/1.98      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0(sK0(sK2))))
% 11.60/1.98      | ~ v1_xboole_0(sK0(sK0(sK2))) ),
% 11.60/1.98      inference(grounding,[status(thm)],[c_23537:[bind(X0,$fot(sK2))]]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_30024,plain,
% 11.60/1.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0(sK0(sK2)))) ),
% 11.60/1.98      inference(grounding,[status(thm)],[c_20411:[bind(X0,$fot(sK2))]]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_30025,plain,
% 11.60/1.98      ( m1_subset_1(sK0(sK0(sK2)),k1_zfmisc_1(sK0(sK2))) ),
% 11.60/1.98      inference(grounding,[status(thm)],[c_3974:[bind(X0,$fot(sK2))]]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_30026,plain,
% 11.60/1.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0(sK2))) ),
% 11.60/1.98      inference(grounding,[status(thm)],[c_3500:[bind(X0,$fot(sK2))]]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_30027,plain,
% 11.60/1.98      ( ~ m1_subset_1(sK0(sK0(sK2)),k1_zfmisc_1(sK0(sK2)))
% 11.60/1.98      | v1_xboole_0(sK0(sK0(sK2)))
% 11.60/1.98      | ~ v1_xboole_0(sK0(sK2)) ),
% 11.60/1.98      inference(grounding,[status(thm)],[c_2802:[bind(X0,$fot(sK2))]]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_30028,plain,
% 11.60/1.98      ( v1_xboole_0(sK0(sK2)) ),
% 11.60/1.98      inference(grounding,[status(thm)],[c_0:[bind(X0,$fot(sK2))]]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(contradiction,plain,
% 11.60/1.98      ( $false ),
% 11.60/1.98      inference(minisat,
% 11.60/1.98                [status(thm)],
% 11.60/1.98                [c_30022,c_26164,c_30023,c_22641,c_30024,c_19542,c_17736,
% 11.60/1.98                 c_12114,c_9860,c_8136,c_6029,c_5947,c_4815,c_4814,
% 11.60/1.98                 c_4530,c_30025,c_3756,c_30026,c_30027,c_2683,c_2682,
% 11.60/1.98                 c_2483,c_2072,c_2000,c_1940,c_618,c_30028,c_132,c_72,
% 11.60/1.98                 c_54,c_50,c_47]) ).
% 11.60/1.98  
% 11.60/1.98  
% 11.60/1.98  % SZS output end CNFRefutation for theBenchmark.p
% 11.60/1.98  
% 11.60/1.98  ------                               Statistics
% 11.60/1.98  
% 11.60/1.98  ------ General
% 11.60/1.98  
% 11.60/1.98  abstr_ref_over_cycles:                  0
% 11.60/1.98  abstr_ref_under_cycles:                 0
% 11.60/1.98  gc_basic_clause_elim:                   0
% 11.60/1.98  forced_gc_time:                         0
% 11.60/1.98  parsing_time:                           0.011
% 11.60/1.98  unif_index_cands_time:                  0.
% 11.60/1.98  unif_index_add_time:                    0.
% 11.60/1.98  orderings_time:                         0.
% 11.60/1.98  out_proof_time:                         0.02
% 11.60/1.98  total_time:                             1.099
% 11.60/1.98  num_of_symbols:                         60
% 11.60/1.98  num_of_terms:                           45300
% 11.60/1.98  
% 11.60/1.98  ------ Preprocessing
% 11.60/1.98  
% 11.60/1.98  num_of_splits:                          0
% 11.60/1.98  num_of_split_atoms:                     0
% 11.60/1.98  num_of_reused_defs:                     0
% 11.60/1.98  num_eq_ax_congr_red:                    26
% 11.60/1.98  num_of_sem_filtered_clauses:            1
% 11.60/1.98  num_of_subtypes:                        0
% 11.60/1.98  monotx_restored_types:                  0
% 11.60/1.98  sat_num_of_epr_types:                   0
% 11.60/1.98  sat_num_of_non_cyclic_types:            0
% 11.60/1.98  sat_guarded_non_collapsed_types:        0
% 11.60/1.98  num_pure_diseq_elim:                    0
% 11.60/1.98  simp_replaced_by:                       0
% 11.60/1.98  res_preprocessed:                       188
% 11.60/1.98  prep_upred:                             0
% 11.60/1.98  prep_unflattend:                        60
% 11.60/1.98  smt_new_axioms:                         0
% 11.60/1.98  pred_elim_cands:                        9
% 11.60/1.98  pred_elim:                              2
% 11.60/1.98  pred_elim_cl:                           -3
% 11.60/1.98  pred_elim_cycles:                       6
% 11.60/1.98  merged_defs:                            0
% 11.60/1.98  merged_defs_ncl:                        0
% 11.60/1.98  bin_hyper_res:                          0
% 11.60/1.98  prep_cycles:                            3
% 11.60/1.98  pred_elim_time:                         0.011
% 11.60/1.98  splitting_time:                         0.
% 11.60/1.98  sem_filter_time:                        0.
% 11.60/1.98  monotx_time:                            0.
% 11.60/1.98  subtype_inf_time:                       0.
% 11.60/1.98  
% 11.60/1.98  ------ Problem properties
% 11.60/1.98  
% 11.60/1.98  clauses:                                48
% 11.60/1.98  conjectures:                            5
% 11.60/1.98  epr:                                    3
% 11.60/1.98  horn:                                   43
% 11.60/1.98  ground:                                 16
% 11.60/1.98  unary:                                  17
% 11.60/1.98  binary:                                 6
% 11.60/1.98  lits:                                   132
% 11.60/1.98  lits_eq:                                39
% 11.60/1.98  fd_pure:                                0
% 11.60/1.98  fd_pseudo:                              0
% 11.60/1.98  fd_cond:                                0
% 11.60/1.98  fd_pseudo_cond:                         2
% 11.60/1.98  ac_symbols:                             0
% 11.60/1.98  
% 11.60/1.98  ------ Propositional Solver
% 11.60/1.98  
% 11.60/1.98  prop_solver_calls:                      28
% 11.60/1.98  prop_fast_solver_calls:                 2876
% 11.60/1.98  smt_solver_calls:                       0
% 11.60/1.98  smt_fast_solver_calls:                  0
% 11.60/1.98  prop_num_of_clauses:                    15804
% 11.60/1.98  prop_preprocess_simplified:             27760
% 11.60/1.98  prop_fo_subsumed:                       382
% 11.60/1.98  prop_solver_time:                       0.
% 11.60/1.98  smt_solver_time:                        0.
% 11.60/1.98  smt_fast_solver_time:                   0.
% 11.60/1.98  prop_fast_solver_time:                  0.
% 11.60/1.98  prop_unsat_core_time:                   0.002
% 11.60/1.98  
% 11.60/1.98  ------ QBF
% 11.60/1.98  
% 11.60/1.98  qbf_q_res:                              0
% 11.60/1.98  qbf_num_tautologies:                    0
% 11.60/1.98  qbf_prep_cycles:                        0
% 11.60/1.98  
% 11.60/1.98  ------ BMC1
% 11.60/1.98  
% 11.60/1.98  bmc1_current_bound:                     -1
% 11.60/1.98  bmc1_last_solved_bound:                 -1
% 11.60/1.98  bmc1_unsat_core_size:                   -1
% 11.60/1.98  bmc1_unsat_core_parents_size:           -1
% 11.60/1.98  bmc1_merge_next_fun:                    0
% 11.60/1.98  bmc1_unsat_core_clauses_time:           0.
% 11.60/1.98  
% 11.60/1.98  ------ Instantiation
% 11.60/1.98  
% 11.60/1.98  inst_num_of_clauses:                    4295
% 11.60/1.98  inst_num_in_passive:                    551
% 11.60/1.98  inst_num_in_active:                     2094
% 11.60/1.98  inst_num_in_unprocessed:                1649
% 11.60/1.98  inst_num_of_loops:                      2418
% 11.60/1.98  inst_num_of_learning_restarts:          0
% 11.60/1.98  inst_num_moves_active_passive:          320
% 11.60/1.98  inst_lit_activity:                      0
% 11.60/1.98  inst_lit_activity_moves:                1
% 11.60/1.98  inst_num_tautologies:                   0
% 11.60/1.98  inst_num_prop_implied:                  0
% 11.60/1.98  inst_num_existing_simplified:           0
% 11.60/1.98  inst_num_eq_res_simplified:             0
% 11.60/1.98  inst_num_child_elim:                    0
% 11.60/1.98  inst_num_of_dismatching_blockings:      2341
% 11.60/1.98  inst_num_of_non_proper_insts:           5013
% 11.60/1.98  inst_num_of_duplicates:                 0
% 11.60/1.98  inst_inst_num_from_inst_to_res:         0
% 11.60/1.98  inst_dismatching_checking_time:         0.
% 11.60/1.98  
% 11.60/1.98  ------ Resolution
% 11.60/1.98  
% 11.60/1.98  res_num_of_clauses:                     0
% 11.60/1.98  res_num_in_passive:                     0
% 11.60/1.98  res_num_in_active:                      0
% 11.60/1.98  res_num_of_loops:                       191
% 11.60/1.98  res_forward_subset_subsumed:            305
% 11.60/1.98  res_backward_subset_subsumed:           2
% 11.60/1.98  res_forward_subsumed:                   0
% 11.60/1.98  res_backward_subsumed:                  0
% 11.60/1.98  res_forward_subsumption_resolution:     0
% 11.60/1.98  res_backward_subsumption_resolution:    0
% 11.60/1.98  res_clause_to_clause_subsumption:       4334
% 11.60/1.98  res_orphan_elimination:                 0
% 11.60/1.98  res_tautology_del:                      437
% 11.60/1.98  res_num_eq_res_simplified:              1
% 11.60/1.98  res_num_sel_changes:                    0
% 11.60/1.98  res_moves_from_active_to_pass:          0
% 11.60/1.98  
% 11.60/1.98  ------ Superposition
% 11.60/1.98  
% 11.60/1.98  sup_time_total:                         0.
% 11.60/1.98  sup_time_generating:                    0.
% 11.60/1.98  sup_time_sim_full:                      0.
% 11.60/1.98  sup_time_sim_immed:                     0.
% 11.60/1.98  
% 11.60/1.98  sup_num_of_clauses:                     1558
% 11.60/1.98  sup_num_in_active:                      452
% 11.60/1.98  sup_num_in_passive:                     1106
% 11.60/1.98  sup_num_of_loops:                       482
% 11.60/1.98  sup_fw_superposition:                   1104
% 11.60/1.98  sup_bw_superposition:                   625
% 11.60/1.98  sup_immediate_simplified:               691
% 11.60/1.98  sup_given_eliminated:                   0
% 11.60/1.98  comparisons_done:                       0
% 11.60/1.98  comparisons_avoided:                    0
% 11.60/1.98  
% 11.60/1.98  ------ Simplifications
% 11.60/1.98  
% 11.60/1.98  
% 11.60/1.98  sim_fw_subset_subsumed:                 49
% 11.60/1.98  sim_bw_subset_subsumed:                 56
% 11.60/1.98  sim_fw_subsumed:                        22
% 11.60/1.98  sim_bw_subsumed:                        0
% 11.60/1.98  sim_fw_subsumption_res:                 0
% 11.60/1.98  sim_bw_subsumption_res:                 0
% 11.60/1.98  sim_tautology_del:                      7
% 11.60/1.98  sim_eq_tautology_del:                   59
% 11.60/1.98  sim_eq_res_simp:                        4
% 11.60/1.98  sim_fw_demodulated:                     246
% 11.60/1.98  sim_bw_demodulated:                     23
% 11.60/1.98  sim_light_normalised:                   428
% 11.60/1.98  sim_joinable_taut:                      0
% 11.60/1.98  sim_joinable_simp:                      0
% 11.60/1.98  sim_ac_normalised:                      0
% 11.60/1.98  sim_smt_subsumption:                    0
% 11.60/1.98  
%------------------------------------------------------------------------------
