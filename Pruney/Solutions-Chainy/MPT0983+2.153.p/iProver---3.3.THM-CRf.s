%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:17 EST 2020

% Result     : Theorem 31.48s
% Output     : CNFRefutation 31.48s
% Verified   : 
% Statistics : Number of formulae       :  220 (1073 expanded)
%              Number of clauses        :  128 ( 335 expanded)
%              Number of leaves         :   24 ( 256 expanded)
%              Depth                    :   22
%              Number of atoms          :  656 (5927 expanded)
%              Number of equality atoms :  278 ( 686 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f22,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
           => ( v2_funct_2(X3,X0)
              & v2_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
           => ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
             => ( v2_funct_2(X3,X0)
                & v2_funct_1(X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f40,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f41,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f40])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
     => ( ( ~ v2_funct_2(sK3,X0)
          | ~ v2_funct_1(X2) )
        & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0))
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(sK3,X1,X0)
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ( ~ v2_funct_2(X3,X0)
              | ~ v2_funct_1(X2) )
            & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ( ~ v2_funct_2(X3,sK0)
            | ~ v2_funct_1(sK2) )
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_2(X3,sK1,sK0)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ( ~ v2_funct_2(sK3,sK0)
      | ~ v2_funct_1(sK2) )
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f41,f51,f50])).

fof(f89,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f52])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f36])).

fof(f83,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f87,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f34])).

fof(f82,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f92,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f52])).

fof(f90,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f81,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
           => ( v2_funct_1(X3)
              | ( k1_xboole_0 != X1
                & k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( v2_funct_1(X3)
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( v2_funct_1(X3)
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f38])).

fof(f85,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v2_funct_1(X3)
      | k1_xboole_0 = X2
      | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v5_relat_1(X1,X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f106,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f80])).

fof(f94,plain,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f42])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f102,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f54])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f30])).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f93,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f52])).

fof(f16,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f20,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f84,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f20])).

fof(f100,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f78,f84])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f11,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f95,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f71,f84])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f56,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f13,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f98,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f74,f84])).

fof(f88,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f91,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f8,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

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

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f44])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f104,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f59])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f103,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f60])).

fof(f12,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f97,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f72,f84])).

fof(f10,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f73,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f99,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f73,f84])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_38,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1456,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_30,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1462,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_3932,plain,
    ( k1_partfun1(X0,X1,sK0,sK1,X2,sK2) = k5_relat_1(X2,sK2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1456,c_1462])).

cnf(c_40,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_41,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_4020,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK0,sK1,X2,sK2) = k5_relat_1(X2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3932,c_41])).

cnf(c_4021,plain,
    ( k1_partfun1(X0,X1,sK0,sK1,X2,sK2) = k5_relat_1(X2,sK2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_4020])).

cnf(c_4029,plain,
    ( k1_partfun1(sK0,sK1,sK0,sK1,sK2,sK2) = k5_relat_1(sK2,sK2)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1456,c_4021])).

cnf(c_4094,plain,
    ( k1_partfun1(sK0,sK1,sK0,sK1,sK2,sK2) = k5_relat_1(sK2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4029,c_41])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1464,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_4323,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4094,c_1464])).

cnf(c_43,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_6888,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4323,c_41,c_43])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1459,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_3931,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1459,c_1462])).

cnf(c_37,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_44,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_3948,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3931,c_44])).

cnf(c_3949,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_3948])).

cnf(c_6894,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,k5_relat_1(sK2,sK2),sK3) = k5_relat_1(k5_relat_1(sK2,sK2),sK3)
    | v1_funct_1(k5_relat_1(sK2,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6888,c_3949])).

cnf(c_29,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v1_funct_1(k1_partfun1(X4,X5,X1,X2,X3,X0)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1463,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(k1_partfun1(X4,X5,X1,X2,X3,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_4096,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(k5_relat_1(sK2,sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4094,c_1463])).

cnf(c_7350,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,k5_relat_1(sK2,sK2),sK3) = k5_relat_1(k5_relat_1(sK2,sK2),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6894,c_41,c_43,c_4096])).

cnf(c_32,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v2_funct_1(X3)
    | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1460,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | v1_funct_2(X3,X4,X2) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v2_funct_1(X3) = iProver_top
    | v2_funct_1(k1_partfun1(X4,X2,X2,X0,X3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_7354,plain,
    ( sK0 = k1_xboole_0
    | v1_funct_2(k5_relat_1(sK2,sK2),sK0,sK1) != iProver_top
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(k5_relat_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k5_relat_1(sK2,sK2)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k5_relat_1(k5_relat_1(sK2,sK2),sK3)) != iProver_top
    | v2_funct_1(k5_relat_1(sK2,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7350,c_1460])).

cnf(c_11,plain,
    ( v5_relat_1(X0,X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_26,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_33,negated_conjecture,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_471,plain,
    ( ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) != sK0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_33])).

cnf(c_472,plain,
    ( ~ v5_relat_1(sK3,k2_relat_1(sK3))
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(sK3) != sK0 ),
    inference(unflattening,[status(thm)],[c_471])).

cnf(c_525,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(sK3) != X1
    | k2_relat_1(sK3) != sK0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_472])).

cnf(c_526,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k2_relat_1(sK3))
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(sK3) != sK0 ),
    inference(unflattening,[status(thm)],[c_525])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_536,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(sK3) != sK0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_526,c_3])).

cnf(c_537,plain,
    ( k2_relat_1(sK3) != sK0
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_536])).

cnf(c_3957,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1456,c_3949])).

cnf(c_24,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_34,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_453,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_34])).

cnf(c_454,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_453])).

cnf(c_25,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_462,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_454,c_25])).

cnf(c_1452,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_462])).

cnf(c_1516,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_1816,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1452,c_40,c_38,c_37,c_35,c_462,c_1516])).

cnf(c_3960,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3957,c_1816])).

cnf(c_4164,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3960,c_41])).

cnf(c_14,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1468,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_4166,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1(sK0)),k2_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4164,c_1468])).

cnf(c_17,plain,
    ( k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_4167,plain,
    ( r1_tarski(sK0,k2_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4166,c_17])).

cnf(c_22,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_12,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_492,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_22,c_12])).

cnf(c_1451,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_492])).

cnf(c_3078,plain,
    ( r1_tarski(k2_relat_1(sK3),sK0) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1459,c_1451])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1474,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3343,plain,
    ( k2_relat_1(sK3) = sK0
    | r1_tarski(sK0,k2_relat_1(sK3)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3078,c_1474])).

cnf(c_4756,plain,
    ( k2_relat_1(sK3) = sK0
    | v1_relat_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4167,c_3343])).

cnf(c_20,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1467,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3821,plain,
    ( sK0 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1816,c_1460])).

cnf(c_39,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_42,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_36,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_45,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_46,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_7922,plain,
    ( sK0 = k1_xboole_0
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3821,c_41,c_42,c_43,c_44,c_45,c_46])).

cnf(c_7926,plain,
    ( sK0 = k1_xboole_0
    | v2_funct_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1467,c_7922])).

cnf(c_13,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1469,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1470,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2587,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK1,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1459,c_1470])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_8,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_260,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_8])).

cnf(c_261,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_260])).

cnf(c_335,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_10,c_261])).

cnf(c_1453,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_335])).

cnf(c_15721,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2587,c_1453])).

cnf(c_15808,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1469,c_15721])).

cnf(c_2588,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1456,c_1470])).

cnf(c_15722,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2588,c_1453])).

cnf(c_15811,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1469,c_15722])).

cnf(c_96033,plain,
    ( sK0 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7354,c_537,c_4756,c_7926,c_15808,c_15811])).

cnf(c_96826,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(k1_xboole_0,sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_96033,c_2588])).

cnf(c_6,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f104])).

cnf(c_96838,plain,
    ( r1_tarski(sK2,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_96826,c_6])).

cnf(c_5,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1465,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2429,plain,
    ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_1465])).

cnf(c_19,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_2431,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2429,c_19])).

cnf(c_3081,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k2_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_1451])).

cnf(c_3176,plain,
    ( r1_tarski(k2_relat_1(k1_xboole_0),X0) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2431,c_3081])).

cnf(c_15,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_3177,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3176,c_15])).

cnf(c_21,plain,
    ( v1_relat_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1466,plain,
    ( v1_relat_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2213,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_19,c_1466])).

cnf(c_3183,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3177,c_2213])).

cnf(c_3187,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3183,c_1474])).

cnf(c_98513,plain,
    ( sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_96838,c_3187])).

cnf(c_792,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1852,plain,
    ( X0 != X1
    | X0 = k6_partfun1(X2)
    | k6_partfun1(X2) != X1 ),
    inference(instantiation,[status(thm)],[c_792])).

cnf(c_1853,plain,
    ( k6_partfun1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k6_partfun1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1852])).

cnf(c_802,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1588,plain,
    ( v2_funct_1(X0)
    | ~ v2_funct_1(k6_partfun1(X1))
    | X0 != k6_partfun1(X1) ),
    inference(instantiation,[status(thm)],[c_802])).

cnf(c_1589,plain,
    ( X0 != k6_partfun1(X1)
    | v2_funct_1(X0) = iProver_top
    | v2_funct_1(k6_partfun1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1588])).

cnf(c_1591,plain,
    ( k1_xboole_0 != k6_partfun1(k1_xboole_0)
    | v2_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top
    | v2_funct_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1589])).

cnf(c_1529,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(sK2)
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_802])).

cnf(c_1530,plain,
    ( sK2 != X0
    | v2_funct_1(X0) != iProver_top
    | v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1529])).

cnf(c_1532,plain,
    ( sK2 != k1_xboole_0
    | v2_funct_1(sK2) = iProver_top
    | v2_funct_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1530])).

cnf(c_110,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_7,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_109,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_85,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_87,plain,
    ( v2_funct_1(k6_partfun1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_85])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_98513,c_15811,c_15808,c_4756,c_1853,c_1591,c_1532,c_537,c_110,c_109,c_19,c_87])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.11  % Command    : iproveropt_run.sh %d %s
% 0.11/0.31  % Computer   : n001.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % WCLimit    : 600
% 0.11/0.31  % DateTime   : Tue Dec  1 18:24:30 EST 2020
% 0.11/0.31  % CPUTime    : 
% 0.11/0.31  % Running in FOF mode
% 31.48/4.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 31.48/4.49  
% 31.48/4.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 31.48/4.49  
% 31.48/4.49  ------  iProver source info
% 31.48/4.49  
% 31.48/4.49  git: date: 2020-06-30 10:37:57 +0100
% 31.48/4.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 31.48/4.49  git: non_committed_changes: false
% 31.48/4.49  git: last_make_outside_of_git: false
% 31.48/4.49  
% 31.48/4.49  ------ 
% 31.48/4.49  
% 31.48/4.49  ------ Input Options
% 31.48/4.49  
% 31.48/4.49  --out_options                           all
% 31.48/4.49  --tptp_safe_out                         true
% 31.48/4.49  --problem_path                          ""
% 31.48/4.49  --include_path                          ""
% 31.48/4.49  --clausifier                            res/vclausify_rel
% 31.48/4.49  --clausifier_options                    ""
% 31.48/4.49  --stdin                                 false
% 31.48/4.49  --stats_out                             all
% 31.48/4.49  
% 31.48/4.49  ------ General Options
% 31.48/4.49  
% 31.48/4.49  --fof                                   false
% 31.48/4.49  --time_out_real                         305.
% 31.48/4.49  --time_out_virtual                      -1.
% 31.48/4.49  --symbol_type_check                     false
% 31.48/4.49  --clausify_out                          false
% 31.48/4.49  --sig_cnt_out                           false
% 31.48/4.49  --trig_cnt_out                          false
% 31.48/4.49  --trig_cnt_out_tolerance                1.
% 31.48/4.49  --trig_cnt_out_sk_spl                   false
% 31.48/4.49  --abstr_cl_out                          false
% 31.48/4.49  
% 31.48/4.49  ------ Global Options
% 31.48/4.49  
% 31.48/4.49  --schedule                              default
% 31.48/4.49  --add_important_lit                     false
% 31.48/4.49  --prop_solver_per_cl                    1000
% 31.48/4.49  --min_unsat_core                        false
% 31.48/4.49  --soft_assumptions                      false
% 31.48/4.49  --soft_lemma_size                       3
% 31.48/4.49  --prop_impl_unit_size                   0
% 31.48/4.49  --prop_impl_unit                        []
% 31.48/4.49  --share_sel_clauses                     true
% 31.48/4.49  --reset_solvers                         false
% 31.48/4.49  --bc_imp_inh                            [conj_cone]
% 31.48/4.49  --conj_cone_tolerance                   3.
% 31.48/4.49  --extra_neg_conj                        none
% 31.48/4.49  --large_theory_mode                     true
% 31.48/4.49  --prolific_symb_bound                   200
% 31.48/4.49  --lt_threshold                          2000
% 31.48/4.49  --clause_weak_htbl                      true
% 31.48/4.49  --gc_record_bc_elim                     false
% 31.48/4.49  
% 31.48/4.49  ------ Preprocessing Options
% 31.48/4.49  
% 31.48/4.49  --preprocessing_flag                    true
% 31.48/4.49  --time_out_prep_mult                    0.1
% 31.48/4.49  --splitting_mode                        input
% 31.48/4.49  --splitting_grd                         true
% 31.48/4.49  --splitting_cvd                         false
% 31.48/4.49  --splitting_cvd_svl                     false
% 31.48/4.49  --splitting_nvd                         32
% 31.48/4.49  --sub_typing                            true
% 31.48/4.49  --prep_gs_sim                           true
% 31.48/4.49  --prep_unflatten                        true
% 31.48/4.49  --prep_res_sim                          true
% 31.48/4.49  --prep_upred                            true
% 31.48/4.49  --prep_sem_filter                       exhaustive
% 31.48/4.49  --prep_sem_filter_out                   false
% 31.48/4.49  --pred_elim                             true
% 31.48/4.49  --res_sim_input                         true
% 31.48/4.49  --eq_ax_congr_red                       true
% 31.48/4.49  --pure_diseq_elim                       true
% 31.48/4.49  --brand_transform                       false
% 31.48/4.49  --non_eq_to_eq                          false
% 31.48/4.49  --prep_def_merge                        true
% 31.48/4.49  --prep_def_merge_prop_impl              false
% 31.48/4.49  --prep_def_merge_mbd                    true
% 31.48/4.49  --prep_def_merge_tr_red                 false
% 31.48/4.49  --prep_def_merge_tr_cl                  false
% 31.48/4.49  --smt_preprocessing                     true
% 31.48/4.49  --smt_ac_axioms                         fast
% 31.48/4.49  --preprocessed_out                      false
% 31.48/4.49  --preprocessed_stats                    false
% 31.48/4.49  
% 31.48/4.49  ------ Abstraction refinement Options
% 31.48/4.49  
% 31.48/4.49  --abstr_ref                             []
% 31.48/4.49  --abstr_ref_prep                        false
% 31.48/4.49  --abstr_ref_until_sat                   false
% 31.48/4.49  --abstr_ref_sig_restrict                funpre
% 31.48/4.49  --abstr_ref_af_restrict_to_split_sk     false
% 31.48/4.49  --abstr_ref_under                       []
% 31.48/4.49  
% 31.48/4.49  ------ SAT Options
% 31.48/4.49  
% 31.48/4.49  --sat_mode                              false
% 31.48/4.49  --sat_fm_restart_options                ""
% 31.48/4.49  --sat_gr_def                            false
% 31.48/4.49  --sat_epr_types                         true
% 31.48/4.49  --sat_non_cyclic_types                  false
% 31.48/4.49  --sat_finite_models                     false
% 31.48/4.49  --sat_fm_lemmas                         false
% 31.48/4.49  --sat_fm_prep                           false
% 31.48/4.49  --sat_fm_uc_incr                        true
% 31.48/4.49  --sat_out_model                         small
% 31.48/4.49  --sat_out_clauses                       false
% 31.48/4.49  
% 31.48/4.49  ------ QBF Options
% 31.48/4.49  
% 31.48/4.49  --qbf_mode                              false
% 31.48/4.49  --qbf_elim_univ                         false
% 31.48/4.49  --qbf_dom_inst                          none
% 31.48/4.49  --qbf_dom_pre_inst                      false
% 31.48/4.49  --qbf_sk_in                             false
% 31.48/4.49  --qbf_pred_elim                         true
% 31.48/4.49  --qbf_split                             512
% 31.48/4.49  
% 31.48/4.49  ------ BMC1 Options
% 31.48/4.49  
% 31.48/4.49  --bmc1_incremental                      false
% 31.48/4.49  --bmc1_axioms                           reachable_all
% 31.48/4.49  --bmc1_min_bound                        0
% 31.48/4.49  --bmc1_max_bound                        -1
% 31.48/4.49  --bmc1_max_bound_default                -1
% 31.48/4.49  --bmc1_symbol_reachability              true
% 31.48/4.49  --bmc1_property_lemmas                  false
% 31.48/4.49  --bmc1_k_induction                      false
% 31.48/4.49  --bmc1_non_equiv_states                 false
% 31.48/4.49  --bmc1_deadlock                         false
% 31.48/4.49  --bmc1_ucm                              false
% 31.48/4.49  --bmc1_add_unsat_core                   none
% 31.48/4.49  --bmc1_unsat_core_children              false
% 31.48/4.49  --bmc1_unsat_core_extrapolate_axioms    false
% 31.48/4.49  --bmc1_out_stat                         full
% 31.48/4.49  --bmc1_ground_init                      false
% 31.48/4.49  --bmc1_pre_inst_next_state              false
% 31.48/4.49  --bmc1_pre_inst_state                   false
% 31.48/4.49  --bmc1_pre_inst_reach_state             false
% 31.48/4.49  --bmc1_out_unsat_core                   false
% 31.48/4.49  --bmc1_aig_witness_out                  false
% 31.48/4.49  --bmc1_verbose                          false
% 31.48/4.49  --bmc1_dump_clauses_tptp                false
% 31.48/4.49  --bmc1_dump_unsat_core_tptp             false
% 31.48/4.49  --bmc1_dump_file                        -
% 31.48/4.49  --bmc1_ucm_expand_uc_limit              128
% 31.48/4.49  --bmc1_ucm_n_expand_iterations          6
% 31.48/4.49  --bmc1_ucm_extend_mode                  1
% 31.48/4.49  --bmc1_ucm_init_mode                    2
% 31.48/4.49  --bmc1_ucm_cone_mode                    none
% 31.48/4.49  --bmc1_ucm_reduced_relation_type        0
% 31.48/4.49  --bmc1_ucm_relax_model                  4
% 31.48/4.49  --bmc1_ucm_full_tr_after_sat            true
% 31.48/4.49  --bmc1_ucm_expand_neg_assumptions       false
% 31.48/4.49  --bmc1_ucm_layered_model                none
% 31.48/4.49  --bmc1_ucm_max_lemma_size               10
% 31.48/4.49  
% 31.48/4.49  ------ AIG Options
% 31.48/4.49  
% 31.48/4.49  --aig_mode                              false
% 31.48/4.49  
% 31.48/4.49  ------ Instantiation Options
% 31.48/4.49  
% 31.48/4.49  --instantiation_flag                    true
% 31.48/4.49  --inst_sos_flag                         true
% 31.48/4.49  --inst_sos_phase                        true
% 31.48/4.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 31.48/4.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 31.48/4.49  --inst_lit_sel_side                     num_symb
% 31.48/4.49  --inst_solver_per_active                1400
% 31.48/4.49  --inst_solver_calls_frac                1.
% 31.48/4.49  --inst_passive_queue_type               priority_queues
% 31.48/4.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 31.48/4.49  --inst_passive_queues_freq              [25;2]
% 31.48/4.49  --inst_dismatching                      true
% 31.48/4.49  --inst_eager_unprocessed_to_passive     true
% 31.48/4.49  --inst_prop_sim_given                   true
% 31.48/4.49  --inst_prop_sim_new                     false
% 31.48/4.49  --inst_subs_new                         false
% 31.48/4.49  --inst_eq_res_simp                      false
% 31.48/4.49  --inst_subs_given                       false
% 31.48/4.49  --inst_orphan_elimination               true
% 31.48/4.49  --inst_learning_loop_flag               true
% 31.48/4.49  --inst_learning_start                   3000
% 31.48/4.49  --inst_learning_factor                  2
% 31.48/4.49  --inst_start_prop_sim_after_learn       3
% 31.48/4.49  --inst_sel_renew                        solver
% 31.48/4.49  --inst_lit_activity_flag                true
% 31.48/4.49  --inst_restr_to_given                   false
% 31.48/4.49  --inst_activity_threshold               500
% 31.48/4.49  --inst_out_proof                        true
% 31.48/4.49  
% 31.48/4.49  ------ Resolution Options
% 31.48/4.49  
% 31.48/4.49  --resolution_flag                       true
% 31.48/4.49  --res_lit_sel                           adaptive
% 31.48/4.49  --res_lit_sel_side                      none
% 31.48/4.49  --res_ordering                          kbo
% 31.48/4.49  --res_to_prop_solver                    active
% 31.48/4.49  --res_prop_simpl_new                    false
% 31.48/4.49  --res_prop_simpl_given                  true
% 31.48/4.49  --res_passive_queue_type                priority_queues
% 31.48/4.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 31.48/4.49  --res_passive_queues_freq               [15;5]
% 31.48/4.49  --res_forward_subs                      full
% 31.48/4.49  --res_backward_subs                     full
% 31.48/4.49  --res_forward_subs_resolution           true
% 31.48/4.49  --res_backward_subs_resolution          true
% 31.48/4.49  --res_orphan_elimination                true
% 31.48/4.49  --res_time_limit                        2.
% 31.48/4.49  --res_out_proof                         true
% 31.48/4.49  
% 31.48/4.49  ------ Superposition Options
% 31.48/4.49  
% 31.48/4.49  --superposition_flag                    true
% 31.48/4.49  --sup_passive_queue_type                priority_queues
% 31.48/4.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 31.48/4.49  --sup_passive_queues_freq               [8;1;4]
% 31.48/4.49  --demod_completeness_check              fast
% 31.48/4.49  --demod_use_ground                      true
% 31.48/4.49  --sup_to_prop_solver                    passive
% 31.48/4.49  --sup_prop_simpl_new                    true
% 31.48/4.49  --sup_prop_simpl_given                  true
% 31.48/4.49  --sup_fun_splitting                     true
% 31.48/4.49  --sup_smt_interval                      50000
% 31.48/4.49  
% 31.48/4.49  ------ Superposition Simplification Setup
% 31.48/4.49  
% 31.48/4.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 31.48/4.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 31.48/4.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 31.48/4.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 31.48/4.49  --sup_full_triv                         [TrivRules;PropSubs]
% 31.48/4.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 31.48/4.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 31.48/4.49  --sup_immed_triv                        [TrivRules]
% 31.48/4.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 31.48/4.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.48/4.49  --sup_immed_bw_main                     []
% 31.48/4.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 31.48/4.49  --sup_input_triv                        [Unflattening;TrivRules]
% 31.48/4.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.48/4.49  --sup_input_bw                          []
% 31.48/4.49  
% 31.48/4.49  ------ Combination Options
% 31.48/4.49  
% 31.48/4.49  --comb_res_mult                         3
% 31.48/4.49  --comb_sup_mult                         2
% 31.48/4.49  --comb_inst_mult                        10
% 31.48/4.49  
% 31.48/4.49  ------ Debug Options
% 31.48/4.49  
% 31.48/4.49  --dbg_backtrace                         false
% 31.48/4.49  --dbg_dump_prop_clauses                 false
% 31.48/4.49  --dbg_dump_prop_clauses_file            -
% 31.48/4.49  --dbg_out_stat                          false
% 31.48/4.49  ------ Parsing...
% 31.48/4.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 31.48/4.49  
% 31.48/4.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 31.48/4.49  
% 31.48/4.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 31.48/4.49  
% 31.48/4.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.48/4.49  ------ Proving...
% 31.48/4.49  ------ Problem Properties 
% 31.48/4.49  
% 31.48/4.49  
% 31.48/4.49  clauses                                 34
% 31.48/4.49  conjectures                             6
% 31.48/4.49  EPR                                     9
% 31.48/4.49  Horn                                    32
% 31.48/4.49  unary                                   19
% 31.48/4.49  binary                                  3
% 31.48/4.49  lits                                    78
% 31.48/4.49  lits eq                                 16
% 31.48/4.49  fd_pure                                 0
% 31.48/4.49  fd_pseudo                               0
% 31.48/4.49  fd_cond                                 2
% 31.48/4.49  fd_pseudo_cond                          2
% 31.48/4.49  AC symbols                              0
% 31.48/4.49  
% 31.48/4.49  ------ Schedule dynamic 5 is on 
% 31.48/4.49  
% 31.48/4.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 31.48/4.49  
% 31.48/4.49  
% 31.48/4.49  ------ 
% 31.48/4.49  Current options:
% 31.48/4.49  ------ 
% 31.48/4.49  
% 31.48/4.49  ------ Input Options
% 31.48/4.49  
% 31.48/4.49  --out_options                           all
% 31.48/4.49  --tptp_safe_out                         true
% 31.48/4.49  --problem_path                          ""
% 31.48/4.49  --include_path                          ""
% 31.48/4.49  --clausifier                            res/vclausify_rel
% 31.48/4.49  --clausifier_options                    ""
% 31.48/4.49  --stdin                                 false
% 31.48/4.49  --stats_out                             all
% 31.48/4.49  
% 31.48/4.49  ------ General Options
% 31.48/4.49  
% 31.48/4.49  --fof                                   false
% 31.48/4.49  --time_out_real                         305.
% 31.48/4.49  --time_out_virtual                      -1.
% 31.48/4.49  --symbol_type_check                     false
% 31.48/4.49  --clausify_out                          false
% 31.48/4.49  --sig_cnt_out                           false
% 31.48/4.49  --trig_cnt_out                          false
% 31.48/4.49  --trig_cnt_out_tolerance                1.
% 31.48/4.49  --trig_cnt_out_sk_spl                   false
% 31.48/4.49  --abstr_cl_out                          false
% 31.48/4.49  
% 31.48/4.49  ------ Global Options
% 31.48/4.49  
% 31.48/4.49  --schedule                              default
% 31.48/4.49  --add_important_lit                     false
% 31.48/4.49  --prop_solver_per_cl                    1000
% 31.48/4.49  --min_unsat_core                        false
% 31.48/4.49  --soft_assumptions                      false
% 31.48/4.49  --soft_lemma_size                       3
% 31.48/4.49  --prop_impl_unit_size                   0
% 31.48/4.49  --prop_impl_unit                        []
% 31.48/4.49  --share_sel_clauses                     true
% 31.48/4.49  --reset_solvers                         false
% 31.48/4.49  --bc_imp_inh                            [conj_cone]
% 31.48/4.49  --conj_cone_tolerance                   3.
% 31.48/4.49  --extra_neg_conj                        none
% 31.48/4.49  --large_theory_mode                     true
% 31.48/4.49  --prolific_symb_bound                   200
% 31.48/4.49  --lt_threshold                          2000
% 31.48/4.49  --clause_weak_htbl                      true
% 31.48/4.49  --gc_record_bc_elim                     false
% 31.48/4.49  
% 31.48/4.49  ------ Preprocessing Options
% 31.48/4.49  
% 31.48/4.49  --preprocessing_flag                    true
% 31.48/4.49  --time_out_prep_mult                    0.1
% 31.48/4.49  --splitting_mode                        input
% 31.48/4.49  --splitting_grd                         true
% 31.48/4.49  --splitting_cvd                         false
% 31.48/4.49  --splitting_cvd_svl                     false
% 31.48/4.49  --splitting_nvd                         32
% 31.48/4.49  --sub_typing                            true
% 31.48/4.49  --prep_gs_sim                           true
% 31.48/4.49  --prep_unflatten                        true
% 31.48/4.49  --prep_res_sim                          true
% 31.48/4.49  --prep_upred                            true
% 31.48/4.49  --prep_sem_filter                       exhaustive
% 31.48/4.49  --prep_sem_filter_out                   false
% 31.48/4.49  --pred_elim                             true
% 31.48/4.49  --res_sim_input                         true
% 31.48/4.49  --eq_ax_congr_red                       true
% 31.48/4.49  --pure_diseq_elim                       true
% 31.48/4.49  --brand_transform                       false
% 31.48/4.49  --non_eq_to_eq                          false
% 31.48/4.49  --prep_def_merge                        true
% 31.48/4.49  --prep_def_merge_prop_impl              false
% 31.48/4.49  --prep_def_merge_mbd                    true
% 31.48/4.49  --prep_def_merge_tr_red                 false
% 31.48/4.49  --prep_def_merge_tr_cl                  false
% 31.48/4.49  --smt_preprocessing                     true
% 31.48/4.49  --smt_ac_axioms                         fast
% 31.48/4.49  --preprocessed_out                      false
% 31.48/4.49  --preprocessed_stats                    false
% 31.48/4.49  
% 31.48/4.49  ------ Abstraction refinement Options
% 31.48/4.49  
% 31.48/4.49  --abstr_ref                             []
% 31.48/4.49  --abstr_ref_prep                        false
% 31.48/4.49  --abstr_ref_until_sat                   false
% 31.48/4.49  --abstr_ref_sig_restrict                funpre
% 31.48/4.49  --abstr_ref_af_restrict_to_split_sk     false
% 31.48/4.49  --abstr_ref_under                       []
% 31.48/4.49  
% 31.48/4.49  ------ SAT Options
% 31.48/4.49  
% 31.48/4.49  --sat_mode                              false
% 31.48/4.49  --sat_fm_restart_options                ""
% 31.48/4.49  --sat_gr_def                            false
% 31.48/4.49  --sat_epr_types                         true
% 31.48/4.49  --sat_non_cyclic_types                  false
% 31.48/4.49  --sat_finite_models                     false
% 31.48/4.49  --sat_fm_lemmas                         false
% 31.48/4.49  --sat_fm_prep                           false
% 31.48/4.49  --sat_fm_uc_incr                        true
% 31.48/4.49  --sat_out_model                         small
% 31.48/4.49  --sat_out_clauses                       false
% 31.48/4.49  
% 31.48/4.49  ------ QBF Options
% 31.48/4.49  
% 31.48/4.49  --qbf_mode                              false
% 31.48/4.49  --qbf_elim_univ                         false
% 31.48/4.49  --qbf_dom_inst                          none
% 31.48/4.49  --qbf_dom_pre_inst                      false
% 31.48/4.49  --qbf_sk_in                             false
% 31.48/4.49  --qbf_pred_elim                         true
% 31.48/4.49  --qbf_split                             512
% 31.48/4.49  
% 31.48/4.49  ------ BMC1 Options
% 31.48/4.49  
% 31.48/4.49  --bmc1_incremental                      false
% 31.48/4.49  --bmc1_axioms                           reachable_all
% 31.48/4.49  --bmc1_min_bound                        0
% 31.48/4.49  --bmc1_max_bound                        -1
% 31.48/4.49  --bmc1_max_bound_default                -1
% 31.48/4.49  --bmc1_symbol_reachability              true
% 31.48/4.49  --bmc1_property_lemmas                  false
% 31.48/4.49  --bmc1_k_induction                      false
% 31.48/4.49  --bmc1_non_equiv_states                 false
% 31.48/4.49  --bmc1_deadlock                         false
% 31.48/4.49  --bmc1_ucm                              false
% 31.48/4.49  --bmc1_add_unsat_core                   none
% 31.48/4.49  --bmc1_unsat_core_children              false
% 31.48/4.49  --bmc1_unsat_core_extrapolate_axioms    false
% 31.48/4.49  --bmc1_out_stat                         full
% 31.48/4.49  --bmc1_ground_init                      false
% 31.48/4.49  --bmc1_pre_inst_next_state              false
% 31.48/4.49  --bmc1_pre_inst_state                   false
% 31.48/4.49  --bmc1_pre_inst_reach_state             false
% 31.48/4.49  --bmc1_out_unsat_core                   false
% 31.48/4.49  --bmc1_aig_witness_out                  false
% 31.48/4.49  --bmc1_verbose                          false
% 31.48/4.49  --bmc1_dump_clauses_tptp                false
% 31.48/4.49  --bmc1_dump_unsat_core_tptp             false
% 31.48/4.49  --bmc1_dump_file                        -
% 31.48/4.49  --bmc1_ucm_expand_uc_limit              128
% 31.48/4.49  --bmc1_ucm_n_expand_iterations          6
% 31.48/4.49  --bmc1_ucm_extend_mode                  1
% 31.48/4.49  --bmc1_ucm_init_mode                    2
% 31.48/4.49  --bmc1_ucm_cone_mode                    none
% 31.48/4.49  --bmc1_ucm_reduced_relation_type        0
% 31.48/4.49  --bmc1_ucm_relax_model                  4
% 31.48/4.49  --bmc1_ucm_full_tr_after_sat            true
% 31.48/4.49  --bmc1_ucm_expand_neg_assumptions       false
% 31.48/4.49  --bmc1_ucm_layered_model                none
% 31.48/4.49  --bmc1_ucm_max_lemma_size               10
% 31.48/4.49  
% 31.48/4.49  ------ AIG Options
% 31.48/4.49  
% 31.48/4.49  --aig_mode                              false
% 31.48/4.49  
% 31.48/4.49  ------ Instantiation Options
% 31.48/4.49  
% 31.48/4.49  --instantiation_flag                    true
% 31.48/4.49  --inst_sos_flag                         true
% 31.48/4.49  --inst_sos_phase                        true
% 31.48/4.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 31.48/4.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 31.48/4.49  --inst_lit_sel_side                     none
% 31.48/4.49  --inst_solver_per_active                1400
% 31.48/4.49  --inst_solver_calls_frac                1.
% 31.48/4.49  --inst_passive_queue_type               priority_queues
% 31.48/4.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 31.48/4.49  --inst_passive_queues_freq              [25;2]
% 31.48/4.49  --inst_dismatching                      true
% 31.48/4.49  --inst_eager_unprocessed_to_passive     true
% 31.48/4.49  --inst_prop_sim_given                   true
% 31.48/4.49  --inst_prop_sim_new                     false
% 31.48/4.49  --inst_subs_new                         false
% 31.48/4.49  --inst_eq_res_simp                      false
% 31.48/4.49  --inst_subs_given                       false
% 31.48/4.49  --inst_orphan_elimination               true
% 31.48/4.49  --inst_learning_loop_flag               true
% 31.48/4.49  --inst_learning_start                   3000
% 31.48/4.49  --inst_learning_factor                  2
% 31.48/4.49  --inst_start_prop_sim_after_learn       3
% 31.48/4.49  --inst_sel_renew                        solver
% 31.48/4.49  --inst_lit_activity_flag                true
% 31.48/4.49  --inst_restr_to_given                   false
% 31.48/4.49  --inst_activity_threshold               500
% 31.48/4.49  --inst_out_proof                        true
% 31.48/4.49  
% 31.48/4.49  ------ Resolution Options
% 31.48/4.49  
% 31.48/4.49  --resolution_flag                       false
% 31.48/4.49  --res_lit_sel                           adaptive
% 31.48/4.49  --res_lit_sel_side                      none
% 31.48/4.49  --res_ordering                          kbo
% 31.48/4.49  --res_to_prop_solver                    active
% 31.48/4.49  --res_prop_simpl_new                    false
% 31.48/4.49  --res_prop_simpl_given                  true
% 31.48/4.49  --res_passive_queue_type                priority_queues
% 31.48/4.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 31.48/4.49  --res_passive_queues_freq               [15;5]
% 31.48/4.49  --res_forward_subs                      full
% 31.48/4.49  --res_backward_subs                     full
% 31.48/4.49  --res_forward_subs_resolution           true
% 31.48/4.49  --res_backward_subs_resolution          true
% 31.48/4.49  --res_orphan_elimination                true
% 31.48/4.49  --res_time_limit                        2.
% 31.48/4.49  --res_out_proof                         true
% 31.48/4.49  
% 31.48/4.49  ------ Superposition Options
% 31.48/4.49  
% 31.48/4.49  --superposition_flag                    true
% 31.48/4.49  --sup_passive_queue_type                priority_queues
% 31.48/4.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 31.48/4.49  --sup_passive_queues_freq               [8;1;4]
% 31.48/4.49  --demod_completeness_check              fast
% 31.48/4.49  --demod_use_ground                      true
% 31.48/4.49  --sup_to_prop_solver                    passive
% 31.48/4.49  --sup_prop_simpl_new                    true
% 31.48/4.49  --sup_prop_simpl_given                  true
% 31.48/4.49  --sup_fun_splitting                     true
% 31.48/4.49  --sup_smt_interval                      50000
% 31.48/4.49  
% 31.48/4.49  ------ Superposition Simplification Setup
% 31.48/4.49  
% 31.48/4.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 31.48/4.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 31.48/4.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 31.48/4.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 31.48/4.49  --sup_full_triv                         [TrivRules;PropSubs]
% 31.48/4.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 31.48/4.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 31.48/4.49  --sup_immed_triv                        [TrivRules]
% 31.48/4.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 31.48/4.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.48/4.49  --sup_immed_bw_main                     []
% 31.48/4.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 31.48/4.49  --sup_input_triv                        [Unflattening;TrivRules]
% 31.48/4.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.48/4.49  --sup_input_bw                          []
% 31.48/4.49  
% 31.48/4.49  ------ Combination Options
% 31.48/4.49  
% 31.48/4.49  --comb_res_mult                         3
% 31.48/4.49  --comb_sup_mult                         2
% 31.48/4.49  --comb_inst_mult                        10
% 31.48/4.49  
% 31.48/4.49  ------ Debug Options
% 31.48/4.49  
% 31.48/4.49  --dbg_backtrace                         false
% 31.48/4.49  --dbg_dump_prop_clauses                 false
% 31.48/4.49  --dbg_dump_prop_clauses_file            -
% 31.48/4.49  --dbg_out_stat                          false
% 31.48/4.49  
% 31.48/4.49  
% 31.48/4.49  
% 31.48/4.49  
% 31.48/4.49  ------ Proving...
% 31.48/4.49  
% 31.48/4.49  
% 31.48/4.49  % SZS status Theorem for theBenchmark.p
% 31.48/4.49  
% 31.48/4.49  % SZS output start CNFRefutation for theBenchmark.p
% 31.48/4.49  
% 31.48/4.49  fof(f22,conjecture,(
% 31.48/4.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 31.48/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.48/4.49  
% 31.48/4.49  fof(f23,negated_conjecture,(
% 31.48/4.49    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 31.48/4.49    inference(negated_conjecture,[],[f22])).
% 31.48/4.49  
% 31.48/4.49  fof(f40,plain,(
% 31.48/4.49    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 31.48/4.49    inference(ennf_transformation,[],[f23])).
% 31.48/4.49  
% 31.48/4.49  fof(f41,plain,(
% 31.48/4.49    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 31.48/4.49    inference(flattening,[],[f40])).
% 31.48/4.49  
% 31.48/4.49  fof(f51,plain,(
% 31.48/4.49    ( ! [X2,X0,X1] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((~v2_funct_2(sK3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 31.48/4.49    introduced(choice_axiom,[])).
% 31.48/4.49  
% 31.48/4.49  fof(f50,plain,(
% 31.48/4.49    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 31.48/4.49    introduced(choice_axiom,[])).
% 31.48/4.49  
% 31.48/4.49  fof(f52,plain,(
% 31.48/4.49    ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 31.48/4.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f41,f51,f50])).
% 31.48/4.49  
% 31.48/4.49  fof(f89,plain,(
% 31.48/4.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 31.48/4.49    inference(cnf_transformation,[],[f52])).
% 31.48/4.49  
% 31.48/4.49  fof(f19,axiom,(
% 31.48/4.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 31.48/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.48/4.49  
% 31.48/4.49  fof(f36,plain,(
% 31.48/4.49    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 31.48/4.49    inference(ennf_transformation,[],[f19])).
% 31.48/4.49  
% 31.48/4.49  fof(f37,plain,(
% 31.48/4.49    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 31.48/4.49    inference(flattening,[],[f36])).
% 31.48/4.49  
% 31.48/4.49  fof(f83,plain,(
% 31.48/4.49    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 31.48/4.49    inference(cnf_transformation,[],[f37])).
% 31.48/4.49  
% 31.48/4.49  fof(f87,plain,(
% 31.48/4.49    v1_funct_1(sK2)),
% 31.48/4.49    inference(cnf_transformation,[],[f52])).
% 31.48/4.49  
% 31.48/4.49  fof(f18,axiom,(
% 31.48/4.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 31.48/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.48/4.49  
% 31.48/4.49  fof(f34,plain,(
% 31.48/4.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 31.48/4.49    inference(ennf_transformation,[],[f18])).
% 31.48/4.49  
% 31.48/4.49  fof(f35,plain,(
% 31.48/4.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 31.48/4.49    inference(flattening,[],[f34])).
% 31.48/4.49  
% 31.48/4.49  fof(f82,plain,(
% 31.48/4.49    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 31.48/4.49    inference(cnf_transformation,[],[f35])).
% 31.48/4.49  
% 31.48/4.49  fof(f92,plain,(
% 31.48/4.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 31.48/4.49    inference(cnf_transformation,[],[f52])).
% 31.48/4.49  
% 31.48/4.49  fof(f90,plain,(
% 31.48/4.49    v1_funct_1(sK3)),
% 31.48/4.49    inference(cnf_transformation,[],[f52])).
% 31.48/4.49  
% 31.48/4.49  fof(f81,plain,(
% 31.48/4.49    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 31.48/4.49    inference(cnf_transformation,[],[f35])).
% 31.48/4.49  
% 31.48/4.49  fof(f21,axiom,(
% 31.48/4.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 31.48/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.48/4.49  
% 31.48/4.49  fof(f38,plain,(
% 31.48/4.49    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 31.48/4.49    inference(ennf_transformation,[],[f21])).
% 31.48/4.49  
% 31.48/4.49  fof(f39,plain,(
% 31.48/4.49    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 31.48/4.49    inference(flattening,[],[f38])).
% 31.48/4.49  
% 31.48/4.49  fof(f85,plain,(
% 31.48/4.49    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X3) | k1_xboole_0 = X2 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 31.48/4.49    inference(cnf_transformation,[],[f39])).
% 31.48/4.49  
% 31.48/4.49  fof(f7,axiom,(
% 31.48/4.49    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 31.48/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.48/4.49  
% 31.48/4.49  fof(f27,plain,(
% 31.48/4.49    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 31.48/4.49    inference(ennf_transformation,[],[f7])).
% 31.48/4.49  
% 31.48/4.49  fof(f47,plain,(
% 31.48/4.49    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 31.48/4.49    inference(nnf_transformation,[],[f27])).
% 31.48/4.49  
% 31.48/4.49  fof(f65,plain,(
% 31.48/4.49    ( ! [X0,X1] : (v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 31.48/4.49    inference(cnf_transformation,[],[f47])).
% 31.48/4.49  
% 31.48/4.49  fof(f17,axiom,(
% 31.48/4.49    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 31.48/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.48/4.49  
% 31.48/4.49  fof(f32,plain,(
% 31.48/4.49    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 31.48/4.49    inference(ennf_transformation,[],[f17])).
% 31.48/4.49  
% 31.48/4.49  fof(f33,plain,(
% 31.48/4.49    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 31.48/4.49    inference(flattening,[],[f32])).
% 31.48/4.49  
% 31.48/4.49  fof(f49,plain,(
% 31.48/4.49    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 31.48/4.49    inference(nnf_transformation,[],[f33])).
% 31.48/4.49  
% 31.48/4.49  fof(f80,plain,(
% 31.48/4.49    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 31.48/4.49    inference(cnf_transformation,[],[f49])).
% 31.48/4.49  
% 31.48/4.49  fof(f106,plain,(
% 31.48/4.49    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 31.48/4.49    inference(equality_resolution,[],[f80])).
% 31.48/4.49  
% 31.48/4.49  fof(f94,plain,(
% 31.48/4.49    ~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)),
% 31.48/4.49    inference(cnf_transformation,[],[f52])).
% 31.48/4.49  
% 31.48/4.49  fof(f2,axiom,(
% 31.48/4.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 31.48/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.48/4.49  
% 31.48/4.49  fof(f42,plain,(
% 31.48/4.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 31.48/4.49    inference(nnf_transformation,[],[f2])).
% 31.48/4.49  
% 31.48/4.49  fof(f43,plain,(
% 31.48/4.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 31.48/4.49    inference(flattening,[],[f42])).
% 31.48/4.49  
% 31.48/4.49  fof(f54,plain,(
% 31.48/4.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 31.48/4.49    inference(cnf_transformation,[],[f43])).
% 31.48/4.49  
% 31.48/4.49  fof(f102,plain,(
% 31.48/4.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 31.48/4.49    inference(equality_resolution,[],[f54])).
% 31.48/4.49  
% 31.48/4.49  fof(f15,axiom,(
% 31.48/4.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 31.48/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.48/4.49  
% 31.48/4.49  fof(f30,plain,(
% 31.48/4.49    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 31.48/4.49    inference(ennf_transformation,[],[f15])).
% 31.48/4.49  
% 31.48/4.49  fof(f31,plain,(
% 31.48/4.49    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 31.48/4.49    inference(flattening,[],[f30])).
% 31.48/4.49  
% 31.48/4.49  fof(f48,plain,(
% 31.48/4.49    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 31.48/4.49    inference(nnf_transformation,[],[f31])).
% 31.48/4.49  
% 31.48/4.49  fof(f76,plain,(
% 31.48/4.49    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 31.48/4.49    inference(cnf_transformation,[],[f48])).
% 31.48/4.49  
% 31.48/4.49  fof(f93,plain,(
% 31.48/4.49    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 31.48/4.49    inference(cnf_transformation,[],[f52])).
% 31.48/4.49  
% 31.48/4.49  fof(f16,axiom,(
% 31.48/4.49    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 31.48/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.48/4.49  
% 31.48/4.49  fof(f78,plain,(
% 31.48/4.49    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 31.48/4.49    inference(cnf_transformation,[],[f16])).
% 31.48/4.49  
% 31.48/4.49  fof(f20,axiom,(
% 31.48/4.49    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 31.48/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.48/4.49  
% 31.48/4.49  fof(f84,plain,(
% 31.48/4.49    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 31.48/4.49    inference(cnf_transformation,[],[f20])).
% 31.48/4.49  
% 31.48/4.49  fof(f100,plain,(
% 31.48/4.49    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 31.48/4.49    inference(definition_unfolding,[],[f78,f84])).
% 31.48/4.49  
% 31.48/4.49  fof(f9,axiom,(
% 31.48/4.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 31.48/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.48/4.49  
% 31.48/4.49  fof(f28,plain,(
% 31.48/4.49    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 31.48/4.49    inference(ennf_transformation,[],[f9])).
% 31.48/4.49  
% 31.48/4.49  fof(f67,plain,(
% 31.48/4.49    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 31.48/4.49    inference(cnf_transformation,[],[f28])).
% 31.48/4.49  
% 31.48/4.49  fof(f11,axiom,(
% 31.48/4.49    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 31.48/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.48/4.49  
% 31.48/4.49  fof(f71,plain,(
% 31.48/4.49    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 31.48/4.49    inference(cnf_transformation,[],[f11])).
% 31.48/4.49  
% 31.48/4.49  fof(f95,plain,(
% 31.48/4.49    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 31.48/4.49    inference(definition_unfolding,[],[f71,f84])).
% 31.48/4.49  
% 31.48/4.49  fof(f14,axiom,(
% 31.48/4.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 31.48/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.48/4.49  
% 31.48/4.49  fof(f24,plain,(
% 31.48/4.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 31.48/4.49    inference(pure_predicate_removal,[],[f14])).
% 31.48/4.49  
% 31.48/4.49  fof(f29,plain,(
% 31.48/4.49    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 31.48/4.49    inference(ennf_transformation,[],[f24])).
% 31.48/4.49  
% 31.48/4.49  fof(f75,plain,(
% 31.48/4.49    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 31.48/4.49    inference(cnf_transformation,[],[f29])).
% 31.48/4.49  
% 31.48/4.49  fof(f64,plain,(
% 31.48/4.49    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 31.48/4.49    inference(cnf_transformation,[],[f47])).
% 31.48/4.49  
% 31.48/4.49  fof(f56,plain,(
% 31.48/4.49    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 31.48/4.49    inference(cnf_transformation,[],[f43])).
% 31.48/4.49  
% 31.48/4.49  fof(f13,axiom,(
% 31.48/4.49    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 31.48/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.48/4.49  
% 31.48/4.49  fof(f74,plain,(
% 31.48/4.49    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 31.48/4.49    inference(cnf_transformation,[],[f13])).
% 31.48/4.49  
% 31.48/4.49  fof(f98,plain,(
% 31.48/4.49    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 31.48/4.49    inference(definition_unfolding,[],[f74,f84])).
% 31.48/4.49  
% 31.48/4.49  fof(f88,plain,(
% 31.48/4.49    v1_funct_2(sK2,sK0,sK1)),
% 31.48/4.49    inference(cnf_transformation,[],[f52])).
% 31.48/4.49  
% 31.48/4.49  fof(f91,plain,(
% 31.48/4.49    v1_funct_2(sK3,sK1,sK0)),
% 31.48/4.49    inference(cnf_transformation,[],[f52])).
% 31.48/4.49  
% 31.48/4.49  fof(f8,axiom,(
% 31.48/4.49    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 31.48/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.48/4.49  
% 31.48/4.49  fof(f66,plain,(
% 31.48/4.49    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 31.48/4.49    inference(cnf_transformation,[],[f8])).
% 31.48/4.49  
% 31.48/4.49  fof(f5,axiom,(
% 31.48/4.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 31.48/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.48/4.49  
% 31.48/4.49  fof(f46,plain,(
% 31.48/4.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 31.48/4.49    inference(nnf_transformation,[],[f5])).
% 31.48/4.49  
% 31.48/4.49  fof(f61,plain,(
% 31.48/4.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 31.48/4.49    inference(cnf_transformation,[],[f46])).
% 31.48/4.49  
% 31.48/4.49  fof(f6,axiom,(
% 31.48/4.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 31.48/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.48/4.49  
% 31.48/4.49  fof(f26,plain,(
% 31.48/4.49    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 31.48/4.49    inference(ennf_transformation,[],[f6])).
% 31.48/4.49  
% 31.48/4.49  fof(f63,plain,(
% 31.48/4.49    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 31.48/4.49    inference(cnf_transformation,[],[f26])).
% 31.48/4.49  
% 31.48/4.49  fof(f62,plain,(
% 31.48/4.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 31.48/4.49    inference(cnf_transformation,[],[f46])).
% 31.48/4.49  
% 31.48/4.49  fof(f4,axiom,(
% 31.48/4.49    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 31.48/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.48/4.49  
% 31.48/4.49  fof(f44,plain,(
% 31.48/4.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 31.48/4.49    inference(nnf_transformation,[],[f4])).
% 31.48/4.49  
% 31.48/4.49  fof(f45,plain,(
% 31.48/4.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 31.48/4.49    inference(flattening,[],[f44])).
% 31.48/4.49  
% 31.48/4.49  fof(f59,plain,(
% 31.48/4.49    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 31.48/4.49    inference(cnf_transformation,[],[f45])).
% 31.48/4.49  
% 31.48/4.49  fof(f104,plain,(
% 31.48/4.49    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 31.48/4.49    inference(equality_resolution,[],[f59])).
% 31.48/4.49  
% 31.48/4.49  fof(f60,plain,(
% 31.48/4.49    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 31.48/4.49    inference(cnf_transformation,[],[f45])).
% 31.48/4.49  
% 31.48/4.49  fof(f103,plain,(
% 31.48/4.49    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 31.48/4.49    inference(equality_resolution,[],[f60])).
% 31.48/4.49  
% 31.48/4.49  fof(f12,axiom,(
% 31.48/4.49    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 31.48/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.48/4.49  
% 31.48/4.49  fof(f72,plain,(
% 31.48/4.49    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 31.48/4.49    inference(cnf_transformation,[],[f12])).
% 31.48/4.49  
% 31.48/4.49  fof(f97,plain,(
% 31.48/4.49    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 31.48/4.49    inference(definition_unfolding,[],[f72,f84])).
% 31.48/4.49  
% 31.48/4.49  fof(f10,axiom,(
% 31.48/4.49    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 31.48/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.48/4.49  
% 31.48/4.49  fof(f69,plain,(
% 31.48/4.49    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 31.48/4.49    inference(cnf_transformation,[],[f10])).
% 31.48/4.49  
% 31.48/4.49  fof(f73,plain,(
% 31.48/4.49    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 31.48/4.49    inference(cnf_transformation,[],[f13])).
% 31.48/4.49  
% 31.48/4.49  fof(f99,plain,(
% 31.48/4.49    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 31.48/4.49    inference(definition_unfolding,[],[f73,f84])).
% 31.48/4.49  
% 31.48/4.49  fof(f58,plain,(
% 31.48/4.49    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 31.48/4.49    inference(cnf_transformation,[],[f45])).
% 31.48/4.49  
% 31.48/4.49  cnf(c_38,negated_conjecture,
% 31.48/4.49      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 31.48/4.49      inference(cnf_transformation,[],[f89]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_1456,plain,
% 31.48/4.49      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 31.48/4.49      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_30,plain,
% 31.48/4.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.48/4.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 31.48/4.49      | ~ v1_funct_1(X0)
% 31.48/4.49      | ~ v1_funct_1(X3)
% 31.48/4.49      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 31.48/4.49      inference(cnf_transformation,[],[f83]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_1462,plain,
% 31.48/4.49      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 31.48/4.49      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 31.48/4.49      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 31.48/4.49      | v1_funct_1(X5) != iProver_top
% 31.48/4.49      | v1_funct_1(X4) != iProver_top ),
% 31.48/4.49      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_3932,plain,
% 31.48/4.49      ( k1_partfun1(X0,X1,sK0,sK1,X2,sK2) = k5_relat_1(X2,sK2)
% 31.48/4.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 31.48/4.49      | v1_funct_1(X2) != iProver_top
% 31.48/4.49      | v1_funct_1(sK2) != iProver_top ),
% 31.48/4.49      inference(superposition,[status(thm)],[c_1456,c_1462]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_40,negated_conjecture,
% 31.48/4.49      ( v1_funct_1(sK2) ),
% 31.48/4.49      inference(cnf_transformation,[],[f87]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_41,plain,
% 31.48/4.49      ( v1_funct_1(sK2) = iProver_top ),
% 31.48/4.49      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_4020,plain,
% 31.48/4.49      ( v1_funct_1(X2) != iProver_top
% 31.48/4.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 31.48/4.49      | k1_partfun1(X0,X1,sK0,sK1,X2,sK2) = k5_relat_1(X2,sK2) ),
% 31.48/4.49      inference(global_propositional_subsumption,
% 31.48/4.49                [status(thm)],
% 31.48/4.49                [c_3932,c_41]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_4021,plain,
% 31.48/4.49      ( k1_partfun1(X0,X1,sK0,sK1,X2,sK2) = k5_relat_1(X2,sK2)
% 31.48/4.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 31.48/4.49      | v1_funct_1(X2) != iProver_top ),
% 31.48/4.49      inference(renaming,[status(thm)],[c_4020]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_4029,plain,
% 31.48/4.49      ( k1_partfun1(sK0,sK1,sK0,sK1,sK2,sK2) = k5_relat_1(sK2,sK2)
% 31.48/4.49      | v1_funct_1(sK2) != iProver_top ),
% 31.48/4.49      inference(superposition,[status(thm)],[c_1456,c_4021]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_4094,plain,
% 31.48/4.49      ( k1_partfun1(sK0,sK1,sK0,sK1,sK2,sK2) = k5_relat_1(sK2,sK2) ),
% 31.48/4.49      inference(global_propositional_subsumption,
% 31.48/4.49                [status(thm)],
% 31.48/4.49                [c_4029,c_41]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_28,plain,
% 31.48/4.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.48/4.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 31.48/4.49      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 31.48/4.49      | ~ v1_funct_1(X0)
% 31.48/4.49      | ~ v1_funct_1(X3) ),
% 31.48/4.49      inference(cnf_transformation,[],[f82]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_1464,plain,
% 31.48/4.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 31.48/4.49      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 31.48/4.49      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
% 31.48/4.49      | v1_funct_1(X0) != iProver_top
% 31.48/4.49      | v1_funct_1(X3) != iProver_top ),
% 31.48/4.49      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_4323,plain,
% 31.48/4.49      ( m1_subset_1(k5_relat_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
% 31.48/4.49      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 31.48/4.49      | v1_funct_1(sK2) != iProver_top ),
% 31.48/4.49      inference(superposition,[status(thm)],[c_4094,c_1464]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_43,plain,
% 31.48/4.49      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 31.48/4.49      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_6888,plain,
% 31.48/4.49      ( m1_subset_1(k5_relat_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 31.48/4.49      inference(global_propositional_subsumption,
% 31.48/4.49                [status(thm)],
% 31.48/4.49                [c_4323,c_41,c_43]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_35,negated_conjecture,
% 31.48/4.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 31.48/4.49      inference(cnf_transformation,[],[f92]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_1459,plain,
% 31.48/4.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 31.48/4.49      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_3931,plain,
% 31.48/4.49      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 31.48/4.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 31.48/4.49      | v1_funct_1(X2) != iProver_top
% 31.48/4.49      | v1_funct_1(sK3) != iProver_top ),
% 31.48/4.49      inference(superposition,[status(thm)],[c_1459,c_1462]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_37,negated_conjecture,
% 31.48/4.49      ( v1_funct_1(sK3) ),
% 31.48/4.49      inference(cnf_transformation,[],[f90]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_44,plain,
% 31.48/4.49      ( v1_funct_1(sK3) = iProver_top ),
% 31.48/4.49      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_3948,plain,
% 31.48/4.49      ( v1_funct_1(X2) != iProver_top
% 31.48/4.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 31.48/4.49      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 31.48/4.49      inference(global_propositional_subsumption,
% 31.48/4.49                [status(thm)],
% 31.48/4.49                [c_3931,c_44]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_3949,plain,
% 31.48/4.49      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 31.48/4.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 31.48/4.49      | v1_funct_1(X2) != iProver_top ),
% 31.48/4.49      inference(renaming,[status(thm)],[c_3948]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_6894,plain,
% 31.48/4.49      ( k1_partfun1(sK0,sK1,sK1,sK0,k5_relat_1(sK2,sK2),sK3) = k5_relat_1(k5_relat_1(sK2,sK2),sK3)
% 31.48/4.49      | v1_funct_1(k5_relat_1(sK2,sK2)) != iProver_top ),
% 31.48/4.49      inference(superposition,[status(thm)],[c_6888,c_3949]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_29,plain,
% 31.48/4.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.48/4.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 31.48/4.49      | ~ v1_funct_1(X0)
% 31.48/4.49      | ~ v1_funct_1(X3)
% 31.48/4.49      | v1_funct_1(k1_partfun1(X4,X5,X1,X2,X3,X0)) ),
% 31.48/4.49      inference(cnf_transformation,[],[f81]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_1463,plain,
% 31.48/4.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 31.48/4.49      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 31.48/4.49      | v1_funct_1(X0) != iProver_top
% 31.48/4.49      | v1_funct_1(X3) != iProver_top
% 31.48/4.49      | v1_funct_1(k1_partfun1(X4,X5,X1,X2,X3,X0)) = iProver_top ),
% 31.48/4.49      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_4096,plain,
% 31.48/4.49      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 31.48/4.49      | v1_funct_1(k5_relat_1(sK2,sK2)) = iProver_top
% 31.48/4.49      | v1_funct_1(sK2) != iProver_top ),
% 31.48/4.49      inference(superposition,[status(thm)],[c_4094,c_1463]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_7350,plain,
% 31.48/4.49      ( k1_partfun1(sK0,sK1,sK1,sK0,k5_relat_1(sK2,sK2),sK3) = k5_relat_1(k5_relat_1(sK2,sK2),sK3) ),
% 31.48/4.49      inference(global_propositional_subsumption,
% 31.48/4.49                [status(thm)],
% 31.48/4.49                [c_6894,c_41,c_43,c_4096]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_32,plain,
% 31.48/4.49      ( ~ v1_funct_2(X0,X1,X2)
% 31.48/4.49      | ~ v1_funct_2(X3,X4,X1)
% 31.48/4.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
% 31.48/4.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.48/4.49      | ~ v1_funct_1(X0)
% 31.48/4.49      | ~ v1_funct_1(X3)
% 31.48/4.49      | v2_funct_1(X3)
% 31.48/4.49      | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
% 31.48/4.49      | k1_xboole_0 = X2 ),
% 31.48/4.49      inference(cnf_transformation,[],[f85]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_1460,plain,
% 31.48/4.49      ( k1_xboole_0 = X0
% 31.48/4.49      | v1_funct_2(X1,X2,X0) != iProver_top
% 31.48/4.49      | v1_funct_2(X3,X4,X2) != iProver_top
% 31.48/4.49      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
% 31.48/4.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 31.48/4.49      | v1_funct_1(X1) != iProver_top
% 31.48/4.49      | v1_funct_1(X3) != iProver_top
% 31.48/4.49      | v2_funct_1(X3) = iProver_top
% 31.48/4.49      | v2_funct_1(k1_partfun1(X4,X2,X2,X0,X3,X1)) != iProver_top ),
% 31.48/4.49      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_7354,plain,
% 31.48/4.49      ( sK0 = k1_xboole_0
% 31.48/4.49      | v1_funct_2(k5_relat_1(sK2,sK2),sK0,sK1) != iProver_top
% 31.48/4.49      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 31.48/4.49      | m1_subset_1(k5_relat_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 31.48/4.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 31.48/4.49      | v1_funct_1(k5_relat_1(sK2,sK2)) != iProver_top
% 31.48/4.49      | v1_funct_1(sK3) != iProver_top
% 31.48/4.49      | v2_funct_1(k5_relat_1(k5_relat_1(sK2,sK2),sK3)) != iProver_top
% 31.48/4.49      | v2_funct_1(k5_relat_1(sK2,sK2)) = iProver_top ),
% 31.48/4.49      inference(superposition,[status(thm)],[c_7350,c_1460]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_11,plain,
% 31.48/4.49      ( v5_relat_1(X0,X1)
% 31.48/4.49      | ~ r1_tarski(k2_relat_1(X0),X1)
% 31.48/4.49      | ~ v1_relat_1(X0) ),
% 31.48/4.49      inference(cnf_transformation,[],[f65]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_26,plain,
% 31.48/4.49      ( v2_funct_2(X0,k2_relat_1(X0))
% 31.48/4.49      | ~ v5_relat_1(X0,k2_relat_1(X0))
% 31.48/4.49      | ~ v1_relat_1(X0) ),
% 31.48/4.49      inference(cnf_transformation,[],[f106]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_33,negated_conjecture,
% 31.48/4.49      ( ~ v2_funct_2(sK3,sK0) | ~ v2_funct_1(sK2) ),
% 31.48/4.49      inference(cnf_transformation,[],[f94]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_471,plain,
% 31.48/4.49      ( ~ v5_relat_1(X0,k2_relat_1(X0))
% 31.48/4.49      | ~ v2_funct_1(sK2)
% 31.48/4.49      | ~ v1_relat_1(X0)
% 31.48/4.49      | k2_relat_1(X0) != sK0
% 31.48/4.49      | sK3 != X0 ),
% 31.48/4.49      inference(resolution_lifted,[status(thm)],[c_26,c_33]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_472,plain,
% 31.48/4.49      ( ~ v5_relat_1(sK3,k2_relat_1(sK3))
% 31.48/4.49      | ~ v2_funct_1(sK2)
% 31.48/4.49      | ~ v1_relat_1(sK3)
% 31.48/4.49      | k2_relat_1(sK3) != sK0 ),
% 31.48/4.49      inference(unflattening,[status(thm)],[c_471]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_525,plain,
% 31.48/4.49      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 31.48/4.49      | ~ v2_funct_1(sK2)
% 31.48/4.49      | ~ v1_relat_1(X0)
% 31.48/4.49      | ~ v1_relat_1(sK3)
% 31.48/4.49      | k2_relat_1(sK3) != X1
% 31.48/4.49      | k2_relat_1(sK3) != sK0
% 31.48/4.49      | sK3 != X0 ),
% 31.48/4.49      inference(resolution_lifted,[status(thm)],[c_11,c_472]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_526,plain,
% 31.48/4.49      ( ~ r1_tarski(k2_relat_1(sK3),k2_relat_1(sK3))
% 31.48/4.49      | ~ v2_funct_1(sK2)
% 31.48/4.49      | ~ v1_relat_1(sK3)
% 31.48/4.49      | k2_relat_1(sK3) != sK0 ),
% 31.48/4.49      inference(unflattening,[status(thm)],[c_525]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_3,plain,
% 31.48/4.49      ( r1_tarski(X0,X0) ),
% 31.48/4.49      inference(cnf_transformation,[],[f102]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_536,plain,
% 31.48/4.49      ( ~ v2_funct_1(sK2) | ~ v1_relat_1(sK3) | k2_relat_1(sK3) != sK0 ),
% 31.48/4.49      inference(forward_subsumption_resolution,[status(thm)],[c_526,c_3]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_537,plain,
% 31.48/4.49      ( k2_relat_1(sK3) != sK0
% 31.48/4.49      | v2_funct_1(sK2) != iProver_top
% 31.48/4.49      | v1_relat_1(sK3) != iProver_top ),
% 31.48/4.49      inference(predicate_to_equality,[status(thm)],[c_536]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_3957,plain,
% 31.48/4.49      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 31.48/4.49      | v1_funct_1(sK2) != iProver_top ),
% 31.48/4.49      inference(superposition,[status(thm)],[c_1456,c_3949]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_24,plain,
% 31.48/4.49      ( ~ r2_relset_1(X0,X1,X2,X3)
% 31.48/4.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 31.48/4.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 31.48/4.49      | X3 = X2 ),
% 31.48/4.49      inference(cnf_transformation,[],[f76]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_34,negated_conjecture,
% 31.48/4.49      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 31.48/4.49      inference(cnf_transformation,[],[f93]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_453,plain,
% 31.48/4.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.48/4.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.48/4.49      | X3 = X0
% 31.48/4.49      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 31.48/4.49      | k6_partfun1(sK0) != X3
% 31.48/4.49      | sK0 != X2
% 31.48/4.49      | sK0 != X1 ),
% 31.48/4.49      inference(resolution_lifted,[status(thm)],[c_24,c_34]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_454,plain,
% 31.48/4.49      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 31.48/4.49      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 31.48/4.49      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 31.48/4.49      inference(unflattening,[status(thm)],[c_453]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_25,plain,
% 31.48/4.49      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 31.48/4.49      inference(cnf_transformation,[],[f100]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_462,plain,
% 31.48/4.49      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 31.48/4.49      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 31.48/4.49      inference(forward_subsumption_resolution,
% 31.48/4.49                [status(thm)],
% 31.48/4.49                [c_454,c_25]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_1452,plain,
% 31.48/4.49      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 31.48/4.49      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 31.48/4.49      inference(predicate_to_equality,[status(thm)],[c_462]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_1516,plain,
% 31.48/4.49      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 31.48/4.49      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 31.48/4.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 31.48/4.49      | ~ v1_funct_1(sK2)
% 31.48/4.49      | ~ v1_funct_1(sK3) ),
% 31.48/4.49      inference(instantiation,[status(thm)],[c_28]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_1816,plain,
% 31.48/4.49      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 31.48/4.49      inference(global_propositional_subsumption,
% 31.48/4.49                [status(thm)],
% 31.48/4.49                [c_1452,c_40,c_38,c_37,c_35,c_462,c_1516]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_3960,plain,
% 31.48/4.49      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 31.48/4.49      | v1_funct_1(sK2) != iProver_top ),
% 31.48/4.49      inference(light_normalisation,[status(thm)],[c_3957,c_1816]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_4164,plain,
% 31.48/4.49      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 31.48/4.49      inference(global_propositional_subsumption,
% 31.48/4.49                [status(thm)],
% 31.48/4.49                [c_3960,c_41]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_14,plain,
% 31.48/4.49      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
% 31.48/4.49      | ~ v1_relat_1(X0)
% 31.48/4.49      | ~ v1_relat_1(X1) ),
% 31.48/4.49      inference(cnf_transformation,[],[f67]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_1468,plain,
% 31.48/4.49      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
% 31.48/4.49      | v1_relat_1(X0) != iProver_top
% 31.48/4.49      | v1_relat_1(X1) != iProver_top ),
% 31.48/4.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_4166,plain,
% 31.48/4.49      ( r1_tarski(k2_relat_1(k6_partfun1(sK0)),k2_relat_1(sK3)) = iProver_top
% 31.48/4.49      | v1_relat_1(sK2) != iProver_top
% 31.48/4.49      | v1_relat_1(sK3) != iProver_top ),
% 31.48/4.49      inference(superposition,[status(thm)],[c_4164,c_1468]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_17,plain,
% 31.48/4.49      ( k2_relat_1(k6_partfun1(X0)) = X0 ),
% 31.48/4.49      inference(cnf_transformation,[],[f95]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_4167,plain,
% 31.48/4.49      ( r1_tarski(sK0,k2_relat_1(sK3)) = iProver_top
% 31.48/4.49      | v1_relat_1(sK2) != iProver_top
% 31.48/4.49      | v1_relat_1(sK3) != iProver_top ),
% 31.48/4.49      inference(demodulation,[status(thm)],[c_4166,c_17]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_22,plain,
% 31.48/4.49      ( v5_relat_1(X0,X1)
% 31.48/4.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 31.48/4.49      inference(cnf_transformation,[],[f75]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_12,plain,
% 31.48/4.49      ( ~ v5_relat_1(X0,X1)
% 31.48/4.49      | r1_tarski(k2_relat_1(X0),X1)
% 31.48/4.49      | ~ v1_relat_1(X0) ),
% 31.48/4.49      inference(cnf_transformation,[],[f64]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_492,plain,
% 31.48/4.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.48/4.49      | r1_tarski(k2_relat_1(X0),X2)
% 31.48/4.49      | ~ v1_relat_1(X0) ),
% 31.48/4.49      inference(resolution,[status(thm)],[c_22,c_12]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_1451,plain,
% 31.48/4.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 31.48/4.49      | r1_tarski(k2_relat_1(X0),X2) = iProver_top
% 31.48/4.49      | v1_relat_1(X0) != iProver_top ),
% 31.48/4.49      inference(predicate_to_equality,[status(thm)],[c_492]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_3078,plain,
% 31.48/4.49      ( r1_tarski(k2_relat_1(sK3),sK0) = iProver_top
% 31.48/4.49      | v1_relat_1(sK3) != iProver_top ),
% 31.48/4.49      inference(superposition,[status(thm)],[c_1459,c_1451]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_1,plain,
% 31.48/4.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 31.48/4.49      inference(cnf_transformation,[],[f56]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_1474,plain,
% 31.48/4.49      ( X0 = X1
% 31.48/4.49      | r1_tarski(X0,X1) != iProver_top
% 31.48/4.49      | r1_tarski(X1,X0) != iProver_top ),
% 31.48/4.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_3343,plain,
% 31.48/4.49      ( k2_relat_1(sK3) = sK0
% 31.48/4.49      | r1_tarski(sK0,k2_relat_1(sK3)) != iProver_top
% 31.48/4.49      | v1_relat_1(sK3) != iProver_top ),
% 31.48/4.49      inference(superposition,[status(thm)],[c_3078,c_1474]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_4756,plain,
% 31.48/4.49      ( k2_relat_1(sK3) = sK0
% 31.48/4.49      | v1_relat_1(sK2) != iProver_top
% 31.48/4.49      | v1_relat_1(sK3) != iProver_top ),
% 31.48/4.49      inference(superposition,[status(thm)],[c_4167,c_3343]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_20,plain,
% 31.48/4.49      ( v2_funct_1(k6_partfun1(X0)) ),
% 31.48/4.49      inference(cnf_transformation,[],[f98]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_1467,plain,
% 31.48/4.49      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 31.48/4.49      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_3821,plain,
% 31.48/4.49      ( sK0 = k1_xboole_0
% 31.48/4.49      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 31.48/4.49      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 31.48/4.49      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 31.48/4.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 31.48/4.49      | v1_funct_1(sK2) != iProver_top
% 31.48/4.49      | v1_funct_1(sK3) != iProver_top
% 31.48/4.49      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 31.48/4.49      | v2_funct_1(sK2) = iProver_top ),
% 31.48/4.49      inference(superposition,[status(thm)],[c_1816,c_1460]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_39,negated_conjecture,
% 31.48/4.49      ( v1_funct_2(sK2,sK0,sK1) ),
% 31.48/4.49      inference(cnf_transformation,[],[f88]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_42,plain,
% 31.48/4.49      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 31.48/4.49      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_36,negated_conjecture,
% 31.48/4.49      ( v1_funct_2(sK3,sK1,sK0) ),
% 31.48/4.49      inference(cnf_transformation,[],[f91]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_45,plain,
% 31.48/4.49      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 31.48/4.49      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_46,plain,
% 31.48/4.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 31.48/4.49      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_7922,plain,
% 31.48/4.49      ( sK0 = k1_xboole_0
% 31.48/4.49      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 31.48/4.49      | v2_funct_1(sK2) = iProver_top ),
% 31.48/4.49      inference(global_propositional_subsumption,
% 31.48/4.49                [status(thm)],
% 31.48/4.49                [c_3821,c_41,c_42,c_43,c_44,c_45,c_46]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_7926,plain,
% 31.48/4.49      ( sK0 = k1_xboole_0 | v2_funct_1(sK2) = iProver_top ),
% 31.48/4.49      inference(superposition,[status(thm)],[c_1467,c_7922]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_13,plain,
% 31.48/4.49      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 31.48/4.49      inference(cnf_transformation,[],[f66]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_1469,plain,
% 31.48/4.49      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 31.48/4.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_9,plain,
% 31.48/4.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 31.48/4.49      inference(cnf_transformation,[],[f61]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_1470,plain,
% 31.48/4.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 31.48/4.49      | r1_tarski(X0,X1) = iProver_top ),
% 31.48/4.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_2587,plain,
% 31.48/4.49      ( r1_tarski(sK3,k2_zfmisc_1(sK1,sK0)) = iProver_top ),
% 31.48/4.49      inference(superposition,[status(thm)],[c_1459,c_1470]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_10,plain,
% 31.48/4.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 31.48/4.49      | ~ v1_relat_1(X1)
% 31.48/4.49      | v1_relat_1(X0) ),
% 31.48/4.49      inference(cnf_transformation,[],[f63]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_8,plain,
% 31.48/4.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 31.48/4.49      inference(cnf_transformation,[],[f62]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_260,plain,
% 31.48/4.49      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 31.48/4.49      inference(prop_impl,[status(thm)],[c_8]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_261,plain,
% 31.48/4.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 31.48/4.49      inference(renaming,[status(thm)],[c_260]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_335,plain,
% 31.48/4.49      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 31.48/4.49      inference(bin_hyper_res,[status(thm)],[c_10,c_261]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_1453,plain,
% 31.48/4.49      ( r1_tarski(X0,X1) != iProver_top
% 31.48/4.49      | v1_relat_1(X1) != iProver_top
% 31.48/4.49      | v1_relat_1(X0) = iProver_top ),
% 31.48/4.49      inference(predicate_to_equality,[status(thm)],[c_335]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_15721,plain,
% 31.48/4.49      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 31.48/4.49      | v1_relat_1(sK3) = iProver_top ),
% 31.48/4.49      inference(superposition,[status(thm)],[c_2587,c_1453]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_15808,plain,
% 31.48/4.49      ( v1_relat_1(sK3) = iProver_top ),
% 31.48/4.49      inference(superposition,[status(thm)],[c_1469,c_15721]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_2588,plain,
% 31.48/4.49      ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 31.48/4.49      inference(superposition,[status(thm)],[c_1456,c_1470]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_15722,plain,
% 31.48/4.49      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 31.48/4.49      | v1_relat_1(sK2) = iProver_top ),
% 31.48/4.49      inference(superposition,[status(thm)],[c_2588,c_1453]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_15811,plain,
% 31.48/4.49      ( v1_relat_1(sK2) = iProver_top ),
% 31.48/4.49      inference(superposition,[status(thm)],[c_1469,c_15722]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_96033,plain,
% 31.48/4.49      ( sK0 = k1_xboole_0 ),
% 31.48/4.49      inference(global_propositional_subsumption,
% 31.48/4.49                [status(thm)],
% 31.48/4.49                [c_7354,c_537,c_4756,c_7926,c_15808,c_15811]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_96826,plain,
% 31.48/4.49      ( r1_tarski(sK2,k2_zfmisc_1(k1_xboole_0,sK1)) = iProver_top ),
% 31.48/4.49      inference(demodulation,[status(thm)],[c_96033,c_2588]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_6,plain,
% 31.48/4.49      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 31.48/4.49      inference(cnf_transformation,[],[f104]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_96838,plain,
% 31.48/4.49      ( r1_tarski(sK2,k1_xboole_0) = iProver_top ),
% 31.48/4.49      inference(demodulation,[status(thm)],[c_96826,c_6]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_5,plain,
% 31.48/4.49      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 31.48/4.49      inference(cnf_transformation,[],[f103]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_1465,plain,
% 31.48/4.49      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 31.48/4.49      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_2429,plain,
% 31.48/4.49      ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 31.48/4.49      inference(superposition,[status(thm)],[c_5,c_1465]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_19,plain,
% 31.48/4.49      ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 31.48/4.49      inference(cnf_transformation,[],[f97]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_2431,plain,
% 31.48/4.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 31.48/4.49      inference(light_normalisation,[status(thm)],[c_2429,c_19]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_3081,plain,
% 31.48/4.49      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 31.48/4.49      | r1_tarski(k2_relat_1(X0),X1) = iProver_top
% 31.48/4.49      | v1_relat_1(X0) != iProver_top ),
% 31.48/4.49      inference(superposition,[status(thm)],[c_6,c_1451]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_3176,plain,
% 31.48/4.49      ( r1_tarski(k2_relat_1(k1_xboole_0),X0) = iProver_top
% 31.48/4.49      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 31.48/4.49      inference(superposition,[status(thm)],[c_2431,c_3081]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_15,plain,
% 31.48/4.49      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 31.48/4.49      inference(cnf_transformation,[],[f69]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_3177,plain,
% 31.48/4.49      ( r1_tarski(k1_xboole_0,X0) = iProver_top
% 31.48/4.49      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 31.48/4.49      inference(light_normalisation,[status(thm)],[c_3176,c_15]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_21,plain,
% 31.48/4.49      ( v1_relat_1(k6_partfun1(X0)) ),
% 31.48/4.49      inference(cnf_transformation,[],[f99]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_1466,plain,
% 31.48/4.49      ( v1_relat_1(k6_partfun1(X0)) = iProver_top ),
% 31.48/4.49      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_2213,plain,
% 31.48/4.49      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 31.48/4.49      inference(superposition,[status(thm)],[c_19,c_1466]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_3183,plain,
% 31.48/4.49      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 31.48/4.49      inference(global_propositional_subsumption,
% 31.48/4.49                [status(thm)],
% 31.48/4.49                [c_3177,c_2213]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_3187,plain,
% 31.48/4.49      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 31.48/4.49      inference(superposition,[status(thm)],[c_3183,c_1474]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_98513,plain,
% 31.48/4.49      ( sK2 = k1_xboole_0 ),
% 31.48/4.49      inference(superposition,[status(thm)],[c_96838,c_3187]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_792,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_1852,plain,
% 31.48/4.49      ( X0 != X1 | X0 = k6_partfun1(X2) | k6_partfun1(X2) != X1 ),
% 31.48/4.49      inference(instantiation,[status(thm)],[c_792]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_1853,plain,
% 31.48/4.49      ( k6_partfun1(k1_xboole_0) != k1_xboole_0
% 31.48/4.49      | k1_xboole_0 = k6_partfun1(k1_xboole_0)
% 31.48/4.49      | k1_xboole_0 != k1_xboole_0 ),
% 31.48/4.49      inference(instantiation,[status(thm)],[c_1852]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_802,plain,
% 31.48/4.49      ( ~ v2_funct_1(X0) | v2_funct_1(X1) | X1 != X0 ),
% 31.48/4.49      theory(equality) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_1588,plain,
% 31.48/4.49      ( v2_funct_1(X0)
% 31.48/4.49      | ~ v2_funct_1(k6_partfun1(X1))
% 31.48/4.49      | X0 != k6_partfun1(X1) ),
% 31.48/4.49      inference(instantiation,[status(thm)],[c_802]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_1589,plain,
% 31.48/4.49      ( X0 != k6_partfun1(X1)
% 31.48/4.49      | v2_funct_1(X0) = iProver_top
% 31.48/4.49      | v2_funct_1(k6_partfun1(X1)) != iProver_top ),
% 31.48/4.49      inference(predicate_to_equality,[status(thm)],[c_1588]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_1591,plain,
% 31.48/4.49      ( k1_xboole_0 != k6_partfun1(k1_xboole_0)
% 31.48/4.49      | v2_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top
% 31.48/4.49      | v2_funct_1(k1_xboole_0) = iProver_top ),
% 31.48/4.49      inference(instantiation,[status(thm)],[c_1589]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_1529,plain,
% 31.48/4.49      ( ~ v2_funct_1(X0) | v2_funct_1(sK2) | sK2 != X0 ),
% 31.48/4.49      inference(instantiation,[status(thm)],[c_802]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_1530,plain,
% 31.48/4.49      ( sK2 != X0
% 31.48/4.49      | v2_funct_1(X0) != iProver_top
% 31.48/4.49      | v2_funct_1(sK2) = iProver_top ),
% 31.48/4.49      inference(predicate_to_equality,[status(thm)],[c_1529]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_1532,plain,
% 31.48/4.49      ( sK2 != k1_xboole_0
% 31.48/4.49      | v2_funct_1(sK2) = iProver_top
% 31.48/4.49      | v2_funct_1(k1_xboole_0) != iProver_top ),
% 31.48/4.49      inference(instantiation,[status(thm)],[c_1530]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_110,plain,
% 31.48/4.49      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 31.48/4.49      inference(instantiation,[status(thm)],[c_6]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_7,plain,
% 31.48/4.49      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 31.48/4.49      | k1_xboole_0 = X1
% 31.48/4.49      | k1_xboole_0 = X0 ),
% 31.48/4.49      inference(cnf_transformation,[],[f58]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_109,plain,
% 31.48/4.49      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 31.48/4.49      | k1_xboole_0 = k1_xboole_0 ),
% 31.48/4.49      inference(instantiation,[status(thm)],[c_7]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_85,plain,
% 31.48/4.49      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 31.48/4.49      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(c_87,plain,
% 31.48/4.49      ( v2_funct_1(k6_partfun1(k1_xboole_0)) = iProver_top ),
% 31.48/4.49      inference(instantiation,[status(thm)],[c_85]) ).
% 31.48/4.49  
% 31.48/4.49  cnf(contradiction,plain,
% 31.48/4.49      ( $false ),
% 31.48/4.49      inference(minisat,
% 31.48/4.49                [status(thm)],
% 31.48/4.49                [c_98513,c_15811,c_15808,c_4756,c_1853,c_1591,c_1532,
% 31.48/4.49                 c_537,c_110,c_109,c_19,c_87]) ).
% 31.48/4.49  
% 31.48/4.49  
% 31.48/4.49  % SZS output end CNFRefutation for theBenchmark.p
% 31.48/4.49  
% 31.48/4.49  ------                               Statistics
% 31.48/4.49  
% 31.48/4.49  ------ General
% 31.48/4.49  
% 31.48/4.49  abstr_ref_over_cycles:                  0
% 31.48/4.49  abstr_ref_under_cycles:                 0
% 31.48/4.49  gc_basic_clause_elim:                   0
% 31.48/4.49  forced_gc_time:                         0
% 31.48/4.49  parsing_time:                           0.008
% 31.48/4.49  unif_index_cands_time:                  0.
% 31.48/4.49  unif_index_add_time:                    0.
% 31.48/4.49  orderings_time:                         0.
% 31.48/4.49  out_proof_time:                         0.023
% 31.48/4.49  total_time:                             3.897
% 31.48/4.49  num_of_symbols:                         53
% 31.48/4.49  num_of_terms:                           111743
% 31.48/4.49  
% 31.48/4.49  ------ Preprocessing
% 31.48/4.49  
% 31.48/4.49  num_of_splits:                          0
% 31.48/4.49  num_of_split_atoms:                     0
% 31.48/4.49  num_of_reused_defs:                     0
% 31.48/4.49  num_eq_ax_congr_red:                    7
% 31.48/4.49  num_of_sem_filtered_clauses:            1
% 31.48/4.49  num_of_subtypes:                        0
% 31.48/4.49  monotx_restored_types:                  0
% 31.48/4.49  sat_num_of_epr_types:                   0
% 31.48/4.49  sat_num_of_non_cyclic_types:            0
% 31.48/4.49  sat_guarded_non_collapsed_types:        0
% 31.48/4.49  num_pure_diseq_elim:                    0
% 31.48/4.49  simp_replaced_by:                       0
% 31.48/4.49  res_preprocessed:                       173
% 31.48/4.49  prep_upred:                             0
% 31.48/4.49  prep_unflattend:                        15
% 31.48/4.49  smt_new_axioms:                         0
% 31.48/4.49  pred_elim_cands:                        7
% 31.48/4.49  pred_elim:                              3
% 31.48/4.49  pred_elim_cl:                           6
% 31.48/4.49  pred_elim_cycles:                       5
% 31.48/4.49  merged_defs:                            8
% 31.48/4.49  merged_defs_ncl:                        0
% 31.48/4.49  bin_hyper_res:                          9
% 31.48/4.49  prep_cycles:                            4
% 31.48/4.49  pred_elim_time:                         0.003
% 31.48/4.49  splitting_time:                         0.
% 31.48/4.49  sem_filter_time:                        0.
% 31.48/4.49  monotx_time:                            0.
% 31.48/4.49  subtype_inf_time:                       0.
% 31.48/4.49  
% 31.48/4.49  ------ Problem properties
% 31.48/4.49  
% 31.48/4.49  clauses:                                34
% 31.48/4.49  conjectures:                            6
% 31.48/4.49  epr:                                    9
% 31.48/4.49  horn:                                   32
% 31.48/4.49  ground:                                 12
% 31.48/4.49  unary:                                  19
% 31.48/4.49  binary:                                 3
% 31.48/4.49  lits:                                   78
% 31.48/4.49  lits_eq:                                16
% 31.48/4.49  fd_pure:                                0
% 31.48/4.49  fd_pseudo:                              0
% 31.48/4.49  fd_cond:                                2
% 31.48/4.49  fd_pseudo_cond:                         2
% 31.48/4.49  ac_symbols:                             0
% 31.48/4.49  
% 31.48/4.49  ------ Propositional Solver
% 31.48/4.49  
% 31.48/4.49  prop_solver_calls:                      50
% 31.48/4.49  prop_fast_solver_calls:                 6354
% 31.48/4.49  smt_solver_calls:                       0
% 31.48/4.49  smt_fast_solver_calls:                  0
% 31.48/4.49  prop_num_of_clauses:                    46547
% 31.48/4.49  prop_preprocess_simplified:             102491
% 31.48/4.49  prop_fo_subsumed:                       490
% 31.48/4.49  prop_solver_time:                       0.
% 31.48/4.49  smt_solver_time:                        0.
% 31.48/4.49  smt_fast_solver_time:                   0.
% 31.48/4.49  prop_fast_solver_time:                  0.
% 31.48/4.49  prop_unsat_core_time:                   0.006
% 31.48/4.49  
% 31.48/4.49  ------ QBF
% 31.48/4.49  
% 31.48/4.49  qbf_q_res:                              0
% 31.48/4.49  qbf_num_tautologies:                    0
% 31.48/4.49  qbf_prep_cycles:                        0
% 31.48/4.49  
% 31.48/4.49  ------ BMC1
% 31.48/4.49  
% 31.48/4.49  bmc1_current_bound:                     -1
% 31.48/4.49  bmc1_last_solved_bound:                 -1
% 31.48/4.49  bmc1_unsat_core_size:                   -1
% 31.48/4.49  bmc1_unsat_core_parents_size:           -1
% 31.48/4.49  bmc1_merge_next_fun:                    0
% 31.48/4.49  bmc1_unsat_core_clauses_time:           0.
% 31.48/4.49  
% 31.48/4.49  ------ Instantiation
% 31.48/4.49  
% 31.48/4.49  inst_num_of_clauses:                    7016
% 31.48/4.49  inst_num_in_passive:                    3426
% 31.48/4.49  inst_num_in_active:                     5277
% 31.48/4.49  inst_num_in_unprocessed:                1167
% 31.48/4.49  inst_num_of_loops:                      5459
% 31.48/4.49  inst_num_of_learning_restarts:          1
% 31.48/4.49  inst_num_moves_active_passive:          175
% 31.48/4.49  inst_lit_activity:                      0
% 31.48/4.49  inst_lit_activity_moves:                2
% 31.48/4.49  inst_num_tautologies:                   0
% 31.48/4.49  inst_num_prop_implied:                  0
% 31.48/4.49  inst_num_existing_simplified:           0
% 31.48/4.49  inst_num_eq_res_simplified:             0
% 31.48/4.49  inst_num_child_elim:                    0
% 31.48/4.49  inst_num_of_dismatching_blockings:      6390
% 31.48/4.49  inst_num_of_non_proper_insts:           13590
% 31.48/4.49  inst_num_of_duplicates:                 0
% 31.48/4.49  inst_inst_num_from_inst_to_res:         0
% 31.48/4.49  inst_dismatching_checking_time:         0.
% 31.48/4.49  
% 31.48/4.49  ------ Resolution
% 31.48/4.49  
% 31.48/4.49  res_num_of_clauses:                     49
% 31.48/4.49  res_num_in_passive:                     49
% 31.48/4.49  res_num_in_active:                      0
% 31.48/4.49  res_num_of_loops:                       177
% 31.48/4.49  res_forward_subset_subsumed:            543
% 31.48/4.49  res_backward_subset_subsumed:           6
% 31.48/4.49  res_forward_subsumed:                   0
% 31.48/4.49  res_backward_subsumed:                  1
% 31.48/4.49  res_forward_subsumption_resolution:     2
% 31.48/4.49  res_backward_subsumption_resolution:    0
% 31.48/4.49  res_clause_to_clause_subsumption:       103067
% 31.48/4.49  res_orphan_elimination:                 0
% 31.48/4.49  res_tautology_del:                      519
% 31.48/4.49  res_num_eq_res_simplified:              0
% 31.48/4.49  res_num_sel_changes:                    0
% 31.48/4.49  res_moves_from_active_to_pass:          0
% 31.48/4.49  
% 31.48/4.49  ------ Superposition
% 31.48/4.49  
% 31.48/4.49  sup_time_total:                         0.
% 31.48/4.49  sup_time_generating:                    0.
% 31.48/4.49  sup_time_sim_full:                      0.
% 31.48/4.49  sup_time_sim_immed:                     0.
% 31.48/4.49  
% 31.48/4.49  sup_num_of_clauses:                     4122
% 31.48/4.49  sup_num_in_active:                      134
% 31.48/4.49  sup_num_in_passive:                     3988
% 31.48/4.49  sup_num_of_loops:                       1091
% 31.48/4.49  sup_fw_superposition:                   4175
% 31.48/4.49  sup_bw_superposition:                   1167
% 31.48/4.49  sup_immediate_simplified:               1150
% 31.48/4.49  sup_given_eliminated:                   2
% 31.48/4.49  comparisons_done:                       0
% 31.48/4.49  comparisons_avoided:                    0
% 31.48/4.49  
% 31.48/4.49  ------ Simplifications
% 31.48/4.49  
% 31.48/4.49  
% 31.48/4.49  sim_fw_subset_subsumed:                 65
% 31.48/4.49  sim_bw_subset_subsumed:                 424
% 31.48/4.49  sim_fw_subsumed:                        70
% 31.48/4.49  sim_bw_subsumed:                        62
% 31.48/4.49  sim_fw_subsumption_res:                 0
% 31.48/4.49  sim_bw_subsumption_res:                 0
% 31.48/4.49  sim_tautology_del:                      3
% 31.48/4.49  sim_eq_tautology_del:                   15
% 31.48/4.49  sim_eq_res_simp:                        0
% 31.48/4.49  sim_fw_demodulated:                     570
% 31.48/4.49  sim_bw_demodulated:                     801
% 31.48/4.49  sim_light_normalised:                   251
% 31.48/4.49  sim_joinable_taut:                      0
% 31.48/4.49  sim_joinable_simp:                      0
% 31.48/4.49  sim_ac_normalised:                      0
% 31.48/4.49  sim_smt_subsumption:                    0
% 31.48/4.49  
%------------------------------------------------------------------------------
