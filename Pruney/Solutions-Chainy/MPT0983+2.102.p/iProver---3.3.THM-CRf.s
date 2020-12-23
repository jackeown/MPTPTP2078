%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:06 EST 2020

% Result     : Theorem 2.88s
% Output     : CNFRefutation 2.88s
% Verified   : 
% Statistics : Number of formulae       :  190 (1121 expanded)
%              Number of clauses        :  113 ( 355 expanded)
%              Number of leaves         :   21 ( 261 expanded)
%              Depth                    :   22
%              Number of atoms          :  622 (6501 expanded)
%              Number of equality atoms :  200 ( 592 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,axiom,(
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
    inference(ennf_transformation,[],[f16])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f34])).

fof(f79,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f13,axiom,(
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
    inference(ennf_transformation,[],[f13])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f30])).

fof(f50,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f20,conjecture,(
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

fof(f21,negated_conjecture,(
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
    inference(negated_conjecture,[],[f20])).

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
    inference(ennf_transformation,[],[f21])).

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

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
     => ( ( ~ v2_funct_2(sK4,X0)
          | ~ v2_funct_1(X2) )
        & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK4),k6_partfun1(X0))
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(sK4,X1,X0)
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
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
          ( ( ~ v2_funct_2(X3,sK1)
            | ~ v2_funct_1(sK3) )
          & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,X3),k6_partfun1(sK1))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
          & v1_funct_2(X3,sK2,sK1)
          & v1_funct_1(X3) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK3,sK1,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
    ( ( ~ v2_funct_2(sK4,sK1)
      | ~ v2_funct_1(sK3) )
    & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1))
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    & v1_funct_2(sK4,sK2,sK1)
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f41,f53,f52])).

fof(f90,plain,(
    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f54])).

fof(f14,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f17,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f80,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f17])).

fof(f93,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f75,f80])).

fof(f84,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f54])).

fof(f86,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f54])).

fof(f87,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f54])).

fof(f89,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f54])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f19,axiom,(
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
    inference(ennf_transformation,[],[f19])).

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

fof(f82,plain,(
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

fof(f85,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f88,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f9,axiom,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f92,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f69,f80])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v5_relat_1(X1,X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f15,axiom,(
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
    inference(ennf_transformation,[],[f15])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f77,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f97,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f77])).

fof(f91,plain,
    ( ~ v2_funct_2(sK4,sK1)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f54])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f46])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f94,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f60])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
           => k2_relset_1(X0,X1,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f61,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1662,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_19,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X2 = X3 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_29,negated_conjecture,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_568,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X0 = X3
    | k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) != X3
    | k6_partfun1(sK1) != X0
    | sK1 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_29])).

cnf(c_569,plain,
    ( ~ m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
    inference(unflattening,[status(thm)],[c_568])).

cnf(c_20,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_66,plain,
    ( m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_571,plain,
    ( ~ m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_569,c_66])).

cnf(c_1648,plain,
    ( k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_571])).

cnf(c_4380,plain,
    ( k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k6_partfun1(sK1)
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1662,c_1648])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_32,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_2315,plain,
    ( ~ m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | r1_tarski(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k2_zfmisc_1(sK1,sK1)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_9,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1668,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2834,plain,
    ( k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k6_partfun1(sK1)
    | r1_tarski(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k2_zfmisc_1(sK1,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1668,c_1648])).

cnf(c_2839,plain,
    ( ~ r1_tarski(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k2_zfmisc_1(sK1,sK1))
    | k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k6_partfun1(sK1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2834])).

cnf(c_2017,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_partfun1(X1,X2,X3,X4,X0,sK4),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_2258,plain,
    ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2017])).

cnf(c_2760,plain,
    ( m1_subset_1(k1_partfun1(sK1,sK2,X0,X1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2258])).

cnf(c_4184,plain,
    ( m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2760])).

cnf(c_4618,plain,
    ( k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4380,c_35,c_33,c_32,c_30,c_2315,c_2839,c_4184])).

cnf(c_27,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | ~ v2_funct_1(k1_partfun1(X1,X2,X2,X4,X0,X3))
    | k1_xboole_0 = X4 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1659,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X3) != iProver_top
    | v1_funct_2(X4,X3,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(X2,X3,X3,X0,X1,X4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_4644,plain,
    ( sK1 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK2) != iProver_top
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v2_funct_1(k6_partfun1(sK1)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4618,c_1659])).

cnf(c_36,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_34,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_37,plain,
    ( v1_funct_2(sK3,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_38,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_39,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_31,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_40,plain,
    ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_41,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_14,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_81,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_83,plain,
    ( v2_funct_1(k6_partfun1(sK1)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_81])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_12,plain,
    ( v5_relat_1(X0,X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_21,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_28,negated_conjecture,
    ( ~ v2_funct_2(sK4,sK1)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_470,plain,
    ( ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) != sK1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_28])).

cnf(c_471,plain,
    ( ~ v5_relat_1(sK4,k2_relat_1(sK4))
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK4)
    | k2_relat_1(sK4) != sK1 ),
    inference(unflattening,[status(thm)],[c_470])).

cnf(c_492,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK4)
    | k2_relat_1(sK4) != X1
    | k2_relat_1(sK4) != sK1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_471])).

cnf(c_493,plain,
    ( ~ r1_tarski(k2_relat_1(sK4),k2_relat_1(sK4))
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK4)
    | k2_relat_1(sK4) != sK1 ),
    inference(unflattening,[status(thm)],[c_492])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_503,plain,
    ( ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK4)
    | k2_relat_1(sK4) != sK1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_493,c_5])).

cnf(c_512,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(sK3)
    | k2_relat_1(sK4) != sK1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_503])).

cnf(c_513,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v2_funct_1(sK3)
    | k2_relat_1(sK4) != sK1 ),
    inference(unflattening,[status(thm)],[c_512])).

cnf(c_904,plain,
    ( ~ v2_funct_1(sK3)
    | sP0_iProver_split
    | k2_relat_1(sK4) != sK1 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_513])).

cnf(c_937,plain,
    ( k2_relat_1(sK4) != sK1
    | v2_funct_1(sK3) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_904])).

cnf(c_1658,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_903,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_513])).

cnf(c_1651,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_903])).

cnf(c_2426,plain,
    ( sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_1658,c_1651])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1664,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3355,plain,
    ( k2_relset_1(sK2,sK1,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1658,c_1664])).

cnf(c_25,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_582,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k1_partfun1(X1,X2,X2,X1,X0,X3) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | k2_relset_1(X2,X1,X3) = X1
    | k6_partfun1(X1) != k6_partfun1(sK1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_29])).

cnf(c_583,plain,
    ( ~ v1_funct_2(X0,X1,sK1)
    | ~ v1_funct_2(X2,sK1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X0)
    | k1_partfun1(sK1,X1,X1,sK1,X2,X0) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | k2_relset_1(X1,sK1,X0) = sK1
    | k6_partfun1(sK1) != k6_partfun1(sK1) ),
    inference(unflattening,[status(thm)],[c_582])).

cnf(c_666,plain,
    ( ~ v1_funct_2(X0,X1,sK1)
    | ~ v1_funct_2(X2,sK1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK1,X1,X1,sK1,X2,X0) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | k2_relset_1(X1,sK1,X0) = sK1 ),
    inference(equality_resolution_simp,[status(thm)],[c_583])).

cnf(c_1647,plain,
    ( k1_partfun1(sK1,X0,X0,sK1,X1,X2) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | k2_relset_1(X0,sK1,X2) = sK1
    | v1_funct_2(X2,X0,sK1) != iProver_top
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_666])).

cnf(c_2073,plain,
    ( k2_relset_1(sK2,sK1,sK4) = sK1
    | v1_funct_2(sK3,sK1,sK2) != iProver_top
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1647])).

cnf(c_2325,plain,
    ( k2_relset_1(sK2,sK1,sK4) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2073,c_36,c_37,c_38,c_39,c_40,c_41])).

cnf(c_3365,plain,
    ( k2_relat_1(sK4) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_3355,c_2325])).

cnf(c_4757,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4644,c_36,c_37,c_38,c_39,c_40,c_41,c_83,c_937,c_2426,c_3365])).

cnf(c_1655,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1665,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3778,plain,
    ( v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1655,c_1665])).

cnf(c_4766,plain,
    ( v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4757,c_3778])).

cnf(c_3,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_112,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_909,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2051,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(k1_xboole_0)
    | X0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_909])).

cnf(c_2052,plain,
    ( X0 != k1_xboole_0
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2051])).

cnf(c_2054,plain,
    ( sK1 != k1_xboole_0
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2052])).

cnf(c_5636,plain,
    ( v1_xboole_0(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4766,c_36,c_37,c_38,c_39,c_40,c_41,c_83,c_112,c_937,c_2054,c_2426,c_3365,c_3778,c_4644])).

cnf(c_1673,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_7,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1670,plain,
    ( X0 = X1
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2904,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1673,c_1670])).

cnf(c_5646,plain,
    ( sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5636,c_2904])).

cnf(c_1650,plain,
    ( k2_relat_1(sK4) != sK1
    | v2_funct_1(sK3) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_904])).

cnf(c_2563,plain,
    ( v2_funct_1(sK3) != iProver_top
    | k2_relat_1(sK4) != sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1650,c_937,c_2426])).

cnf(c_2564,plain,
    ( k2_relat_1(sK4) != sK1
    | v2_funct_1(sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_2563])).

cnf(c_4163,plain,
    ( sK1 != sK1
    | v2_funct_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3365,c_2564])).

cnf(c_4206,plain,
    ( v2_funct_1(sK3) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4163])).

cnf(c_5729,plain,
    ( v2_funct_1(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5646,c_4206])).

cnf(c_8,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1669,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3037,plain,
    ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1669,c_2904])).

cnf(c_3048,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1673,c_3037])).

cnf(c_1663,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1667,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2725,plain,
    ( r1_tarski(k6_partfun1(X0),k2_zfmisc_1(X0,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1663,c_1667])).

cnf(c_3153,plain,
    ( r1_tarski(k6_partfun1(k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3048,c_2725])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1672,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3614,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k6_partfun1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3153,c_1672])).

cnf(c_1997,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | v1_xboole_0(X0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_2485,plain,
    ( ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | v1_xboole_0(k6_partfun1(k1_xboole_0))
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1997])).

cnf(c_2486,plain,
    ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_2190,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(k1_xboole_0)
    | X0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_3289,plain,
    ( ~ v1_xboole_0(k6_partfun1(k1_xboole_0))
    | ~ v1_xboole_0(k1_xboole_0)
    | k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2190])).

cnf(c_4554,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3614,c_3,c_2485,c_2486,c_3289])).

cnf(c_1666,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_4567,plain,
    ( v2_funct_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4554,c_1666])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5729,c_4567])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.33  % Computer   : n018.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 14:26:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 2.88/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.88/1.00  
% 2.88/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.88/1.00  
% 2.88/1.00  ------  iProver source info
% 2.88/1.00  
% 2.88/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.88/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.88/1.00  git: non_committed_changes: false
% 2.88/1.00  git: last_make_outside_of_git: false
% 2.88/1.00  
% 2.88/1.00  ------ 
% 2.88/1.00  
% 2.88/1.00  ------ Input Options
% 2.88/1.00  
% 2.88/1.00  --out_options                           all
% 2.88/1.00  --tptp_safe_out                         true
% 2.88/1.00  --problem_path                          ""
% 2.88/1.00  --include_path                          ""
% 2.88/1.00  --clausifier                            res/vclausify_rel
% 2.88/1.00  --clausifier_options                    --mode clausify
% 2.88/1.00  --stdin                                 false
% 2.88/1.00  --stats_out                             all
% 2.88/1.00  
% 2.88/1.00  ------ General Options
% 2.88/1.00  
% 2.88/1.00  --fof                                   false
% 2.88/1.00  --time_out_real                         305.
% 2.88/1.00  --time_out_virtual                      -1.
% 2.88/1.00  --symbol_type_check                     false
% 2.88/1.00  --clausify_out                          false
% 2.88/1.00  --sig_cnt_out                           false
% 2.88/1.00  --trig_cnt_out                          false
% 2.88/1.00  --trig_cnt_out_tolerance                1.
% 2.88/1.00  --trig_cnt_out_sk_spl                   false
% 2.88/1.00  --abstr_cl_out                          false
% 2.88/1.00  
% 2.88/1.00  ------ Global Options
% 2.88/1.00  
% 2.88/1.00  --schedule                              default
% 2.88/1.00  --add_important_lit                     false
% 2.88/1.00  --prop_solver_per_cl                    1000
% 2.88/1.00  --min_unsat_core                        false
% 2.88/1.00  --soft_assumptions                      false
% 2.88/1.00  --soft_lemma_size                       3
% 2.88/1.00  --prop_impl_unit_size                   0
% 2.88/1.00  --prop_impl_unit                        []
% 2.88/1.00  --share_sel_clauses                     true
% 2.88/1.00  --reset_solvers                         false
% 2.88/1.00  --bc_imp_inh                            [conj_cone]
% 2.88/1.00  --conj_cone_tolerance                   3.
% 2.88/1.00  --extra_neg_conj                        none
% 2.88/1.00  --large_theory_mode                     true
% 2.88/1.00  --prolific_symb_bound                   200
% 2.88/1.00  --lt_threshold                          2000
% 2.88/1.00  --clause_weak_htbl                      true
% 2.88/1.00  --gc_record_bc_elim                     false
% 2.88/1.00  
% 2.88/1.00  ------ Preprocessing Options
% 2.88/1.00  
% 2.88/1.00  --preprocessing_flag                    true
% 2.88/1.00  --time_out_prep_mult                    0.1
% 2.88/1.00  --splitting_mode                        input
% 2.88/1.00  --splitting_grd                         true
% 2.88/1.00  --splitting_cvd                         false
% 2.88/1.00  --splitting_cvd_svl                     false
% 2.88/1.00  --splitting_nvd                         32
% 2.88/1.00  --sub_typing                            true
% 2.88/1.00  --prep_gs_sim                           true
% 2.88/1.00  --prep_unflatten                        true
% 2.88/1.00  --prep_res_sim                          true
% 2.88/1.00  --prep_upred                            true
% 2.88/1.00  --prep_sem_filter                       exhaustive
% 2.88/1.00  --prep_sem_filter_out                   false
% 2.88/1.00  --pred_elim                             true
% 2.88/1.00  --res_sim_input                         true
% 2.88/1.00  --eq_ax_congr_red                       true
% 2.88/1.00  --pure_diseq_elim                       true
% 2.88/1.00  --brand_transform                       false
% 2.88/1.00  --non_eq_to_eq                          false
% 2.88/1.00  --prep_def_merge                        true
% 2.88/1.00  --prep_def_merge_prop_impl              false
% 2.88/1.00  --prep_def_merge_mbd                    true
% 2.88/1.00  --prep_def_merge_tr_red                 false
% 2.88/1.00  --prep_def_merge_tr_cl                  false
% 2.88/1.00  --smt_preprocessing                     true
% 2.88/1.00  --smt_ac_axioms                         fast
% 2.88/1.00  --preprocessed_out                      false
% 2.88/1.00  --preprocessed_stats                    false
% 2.88/1.00  
% 2.88/1.00  ------ Abstraction refinement Options
% 2.88/1.00  
% 2.88/1.00  --abstr_ref                             []
% 2.88/1.00  --abstr_ref_prep                        false
% 2.88/1.00  --abstr_ref_until_sat                   false
% 2.88/1.00  --abstr_ref_sig_restrict                funpre
% 2.88/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.88/1.00  --abstr_ref_under                       []
% 2.88/1.00  
% 2.88/1.00  ------ SAT Options
% 2.88/1.00  
% 2.88/1.00  --sat_mode                              false
% 2.88/1.00  --sat_fm_restart_options                ""
% 2.88/1.00  --sat_gr_def                            false
% 2.88/1.00  --sat_epr_types                         true
% 2.88/1.00  --sat_non_cyclic_types                  false
% 2.88/1.00  --sat_finite_models                     false
% 2.88/1.00  --sat_fm_lemmas                         false
% 2.88/1.00  --sat_fm_prep                           false
% 2.88/1.00  --sat_fm_uc_incr                        true
% 2.88/1.00  --sat_out_model                         small
% 2.88/1.00  --sat_out_clauses                       false
% 2.88/1.00  
% 2.88/1.00  ------ QBF Options
% 2.88/1.00  
% 2.88/1.00  --qbf_mode                              false
% 2.88/1.00  --qbf_elim_univ                         false
% 2.88/1.00  --qbf_dom_inst                          none
% 2.88/1.00  --qbf_dom_pre_inst                      false
% 2.88/1.00  --qbf_sk_in                             false
% 2.88/1.00  --qbf_pred_elim                         true
% 2.88/1.00  --qbf_split                             512
% 2.88/1.00  
% 2.88/1.00  ------ BMC1 Options
% 2.88/1.00  
% 2.88/1.00  --bmc1_incremental                      false
% 2.88/1.00  --bmc1_axioms                           reachable_all
% 2.88/1.00  --bmc1_min_bound                        0
% 2.88/1.00  --bmc1_max_bound                        -1
% 2.88/1.00  --bmc1_max_bound_default                -1
% 2.88/1.00  --bmc1_symbol_reachability              true
% 2.88/1.00  --bmc1_property_lemmas                  false
% 2.88/1.00  --bmc1_k_induction                      false
% 2.88/1.00  --bmc1_non_equiv_states                 false
% 2.88/1.00  --bmc1_deadlock                         false
% 2.88/1.00  --bmc1_ucm                              false
% 2.88/1.00  --bmc1_add_unsat_core                   none
% 2.88/1.00  --bmc1_unsat_core_children              false
% 2.88/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.88/1.00  --bmc1_out_stat                         full
% 2.88/1.00  --bmc1_ground_init                      false
% 2.88/1.00  --bmc1_pre_inst_next_state              false
% 2.88/1.00  --bmc1_pre_inst_state                   false
% 2.88/1.00  --bmc1_pre_inst_reach_state             false
% 2.88/1.00  --bmc1_out_unsat_core                   false
% 2.88/1.00  --bmc1_aig_witness_out                  false
% 2.88/1.00  --bmc1_verbose                          false
% 2.88/1.00  --bmc1_dump_clauses_tptp                false
% 2.88/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.88/1.00  --bmc1_dump_file                        -
% 2.88/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.88/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.88/1.00  --bmc1_ucm_extend_mode                  1
% 2.88/1.00  --bmc1_ucm_init_mode                    2
% 2.88/1.00  --bmc1_ucm_cone_mode                    none
% 2.88/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.88/1.00  --bmc1_ucm_relax_model                  4
% 2.88/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.88/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.88/1.00  --bmc1_ucm_layered_model                none
% 2.88/1.00  --bmc1_ucm_max_lemma_size               10
% 2.88/1.00  
% 2.88/1.00  ------ AIG Options
% 2.88/1.00  
% 2.88/1.00  --aig_mode                              false
% 2.88/1.00  
% 2.88/1.00  ------ Instantiation Options
% 2.88/1.00  
% 2.88/1.00  --instantiation_flag                    true
% 2.88/1.00  --inst_sos_flag                         false
% 2.88/1.00  --inst_sos_phase                        true
% 2.88/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.88/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.88/1.00  --inst_lit_sel_side                     num_symb
% 2.88/1.00  --inst_solver_per_active                1400
% 2.88/1.00  --inst_solver_calls_frac                1.
% 2.88/1.00  --inst_passive_queue_type               priority_queues
% 2.88/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.88/1.00  --inst_passive_queues_freq              [25;2]
% 2.88/1.00  --inst_dismatching                      true
% 2.88/1.00  --inst_eager_unprocessed_to_passive     true
% 2.88/1.00  --inst_prop_sim_given                   true
% 2.88/1.00  --inst_prop_sim_new                     false
% 2.88/1.00  --inst_subs_new                         false
% 2.88/1.00  --inst_eq_res_simp                      false
% 2.88/1.00  --inst_subs_given                       false
% 2.88/1.00  --inst_orphan_elimination               true
% 2.88/1.00  --inst_learning_loop_flag               true
% 2.88/1.00  --inst_learning_start                   3000
% 2.88/1.00  --inst_learning_factor                  2
% 2.88/1.00  --inst_start_prop_sim_after_learn       3
% 2.88/1.00  --inst_sel_renew                        solver
% 2.88/1.00  --inst_lit_activity_flag                true
% 2.88/1.00  --inst_restr_to_given                   false
% 2.88/1.00  --inst_activity_threshold               500
% 2.88/1.00  --inst_out_proof                        true
% 2.88/1.00  
% 2.88/1.00  ------ Resolution Options
% 2.88/1.00  
% 2.88/1.00  --resolution_flag                       true
% 2.88/1.00  --res_lit_sel                           adaptive
% 2.88/1.00  --res_lit_sel_side                      none
% 2.88/1.00  --res_ordering                          kbo
% 2.88/1.00  --res_to_prop_solver                    active
% 2.88/1.00  --res_prop_simpl_new                    false
% 2.88/1.00  --res_prop_simpl_given                  true
% 2.88/1.00  --res_passive_queue_type                priority_queues
% 2.88/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.88/1.00  --res_passive_queues_freq               [15;5]
% 2.88/1.00  --res_forward_subs                      full
% 2.88/1.00  --res_backward_subs                     full
% 2.88/1.00  --res_forward_subs_resolution           true
% 2.88/1.00  --res_backward_subs_resolution          true
% 2.88/1.00  --res_orphan_elimination                true
% 2.88/1.00  --res_time_limit                        2.
% 2.88/1.00  --res_out_proof                         true
% 2.88/1.00  
% 2.88/1.00  ------ Superposition Options
% 2.88/1.00  
% 2.88/1.00  --superposition_flag                    true
% 2.88/1.00  --sup_passive_queue_type                priority_queues
% 2.88/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.88/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.88/1.00  --demod_completeness_check              fast
% 2.88/1.00  --demod_use_ground                      true
% 2.88/1.00  --sup_to_prop_solver                    passive
% 2.88/1.00  --sup_prop_simpl_new                    true
% 2.88/1.00  --sup_prop_simpl_given                  true
% 2.88/1.00  --sup_fun_splitting                     false
% 2.88/1.00  --sup_smt_interval                      50000
% 2.88/1.00  
% 2.88/1.00  ------ Superposition Simplification Setup
% 2.88/1.00  
% 2.88/1.00  --sup_indices_passive                   []
% 2.88/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.88/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.88/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.88/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.88/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.88/1.00  --sup_full_bw                           [BwDemod]
% 2.88/1.00  --sup_immed_triv                        [TrivRules]
% 2.88/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.88/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.88/1.00  --sup_immed_bw_main                     []
% 2.88/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.88/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.88/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.88/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.88/1.00  
% 2.88/1.00  ------ Combination Options
% 2.88/1.00  
% 2.88/1.00  --comb_res_mult                         3
% 2.88/1.00  --comb_sup_mult                         2
% 2.88/1.00  --comb_inst_mult                        10
% 2.88/1.00  
% 2.88/1.00  ------ Debug Options
% 2.88/1.00  
% 2.88/1.00  --dbg_backtrace                         false
% 2.88/1.00  --dbg_dump_prop_clauses                 false
% 2.88/1.00  --dbg_dump_prop_clauses_file            -
% 2.88/1.00  --dbg_out_stat                          false
% 2.88/1.00  ------ Parsing...
% 2.88/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.88/1.00  
% 2.88/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.88/1.00  
% 2.88/1.00  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.88/1.00  
% 2.88/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.88/1.00  ------ Proving...
% 2.88/1.00  ------ Problem Properties 
% 2.88/1.00  
% 2.88/1.00  
% 2.88/1.00  clauses                                 30
% 2.88/1.00  conjectures                             6
% 2.88/1.00  EPR                                     10
% 2.88/1.00  Horn                                    28
% 2.88/1.00  unary                                   10
% 2.88/1.00  binary                                  8
% 2.88/1.00  lits                                    87
% 2.88/1.00  lits eq                                 10
% 2.88/1.00  fd_pure                                 0
% 2.88/1.00  fd_pseudo                               0
% 2.88/1.00  fd_cond                                 1
% 2.88/1.00  fd_pseudo_cond                          2
% 2.88/1.00  AC symbols                              0
% 2.88/1.00  
% 2.88/1.00  ------ Schedule dynamic 5 is on 
% 2.88/1.00  
% 2.88/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.88/1.00  
% 2.88/1.00  
% 2.88/1.00  ------ 
% 2.88/1.00  Current options:
% 2.88/1.00  ------ 
% 2.88/1.00  
% 2.88/1.00  ------ Input Options
% 2.88/1.00  
% 2.88/1.00  --out_options                           all
% 2.88/1.00  --tptp_safe_out                         true
% 2.88/1.00  --problem_path                          ""
% 2.88/1.00  --include_path                          ""
% 2.88/1.00  --clausifier                            res/vclausify_rel
% 2.88/1.00  --clausifier_options                    --mode clausify
% 2.88/1.00  --stdin                                 false
% 2.88/1.00  --stats_out                             all
% 2.88/1.00  
% 2.88/1.00  ------ General Options
% 2.88/1.00  
% 2.88/1.00  --fof                                   false
% 2.88/1.00  --time_out_real                         305.
% 2.88/1.00  --time_out_virtual                      -1.
% 2.88/1.00  --symbol_type_check                     false
% 2.88/1.00  --clausify_out                          false
% 2.88/1.00  --sig_cnt_out                           false
% 2.88/1.00  --trig_cnt_out                          false
% 2.88/1.00  --trig_cnt_out_tolerance                1.
% 2.88/1.00  --trig_cnt_out_sk_spl                   false
% 2.88/1.00  --abstr_cl_out                          false
% 2.88/1.00  
% 2.88/1.00  ------ Global Options
% 2.88/1.00  
% 2.88/1.00  --schedule                              default
% 2.88/1.00  --add_important_lit                     false
% 2.88/1.00  --prop_solver_per_cl                    1000
% 2.88/1.00  --min_unsat_core                        false
% 2.88/1.00  --soft_assumptions                      false
% 2.88/1.00  --soft_lemma_size                       3
% 2.88/1.00  --prop_impl_unit_size                   0
% 2.88/1.00  --prop_impl_unit                        []
% 2.88/1.00  --share_sel_clauses                     true
% 2.88/1.00  --reset_solvers                         false
% 2.88/1.00  --bc_imp_inh                            [conj_cone]
% 2.88/1.00  --conj_cone_tolerance                   3.
% 2.88/1.00  --extra_neg_conj                        none
% 2.88/1.00  --large_theory_mode                     true
% 2.88/1.00  --prolific_symb_bound                   200
% 2.88/1.00  --lt_threshold                          2000
% 2.88/1.00  --clause_weak_htbl                      true
% 2.88/1.00  --gc_record_bc_elim                     false
% 2.88/1.00  
% 2.88/1.00  ------ Preprocessing Options
% 2.88/1.00  
% 2.88/1.00  --preprocessing_flag                    true
% 2.88/1.00  --time_out_prep_mult                    0.1
% 2.88/1.00  --splitting_mode                        input
% 2.88/1.00  --splitting_grd                         true
% 2.88/1.00  --splitting_cvd                         false
% 2.88/1.00  --splitting_cvd_svl                     false
% 2.88/1.00  --splitting_nvd                         32
% 2.88/1.00  --sub_typing                            true
% 2.88/1.00  --prep_gs_sim                           true
% 2.88/1.00  --prep_unflatten                        true
% 2.88/1.00  --prep_res_sim                          true
% 2.88/1.00  --prep_upred                            true
% 2.88/1.00  --prep_sem_filter                       exhaustive
% 2.88/1.00  --prep_sem_filter_out                   false
% 2.88/1.00  --pred_elim                             true
% 2.88/1.00  --res_sim_input                         true
% 2.88/1.00  --eq_ax_congr_red                       true
% 2.88/1.00  --pure_diseq_elim                       true
% 2.88/1.00  --brand_transform                       false
% 2.88/1.00  --non_eq_to_eq                          false
% 2.88/1.00  --prep_def_merge                        true
% 2.88/1.00  --prep_def_merge_prop_impl              false
% 2.88/1.00  --prep_def_merge_mbd                    true
% 2.88/1.00  --prep_def_merge_tr_red                 false
% 2.88/1.00  --prep_def_merge_tr_cl                  false
% 2.88/1.00  --smt_preprocessing                     true
% 2.88/1.00  --smt_ac_axioms                         fast
% 2.88/1.00  --preprocessed_out                      false
% 2.88/1.00  --preprocessed_stats                    false
% 2.88/1.00  
% 2.88/1.00  ------ Abstraction refinement Options
% 2.88/1.00  
% 2.88/1.00  --abstr_ref                             []
% 2.88/1.00  --abstr_ref_prep                        false
% 2.88/1.00  --abstr_ref_until_sat                   false
% 2.88/1.00  --abstr_ref_sig_restrict                funpre
% 2.88/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.88/1.00  --abstr_ref_under                       []
% 2.88/1.00  
% 2.88/1.00  ------ SAT Options
% 2.88/1.00  
% 2.88/1.00  --sat_mode                              false
% 2.88/1.00  --sat_fm_restart_options                ""
% 2.88/1.00  --sat_gr_def                            false
% 2.88/1.00  --sat_epr_types                         true
% 2.88/1.00  --sat_non_cyclic_types                  false
% 2.88/1.00  --sat_finite_models                     false
% 2.88/1.00  --sat_fm_lemmas                         false
% 2.88/1.00  --sat_fm_prep                           false
% 2.88/1.00  --sat_fm_uc_incr                        true
% 2.88/1.00  --sat_out_model                         small
% 2.88/1.00  --sat_out_clauses                       false
% 2.88/1.00  
% 2.88/1.00  ------ QBF Options
% 2.88/1.00  
% 2.88/1.00  --qbf_mode                              false
% 2.88/1.00  --qbf_elim_univ                         false
% 2.88/1.00  --qbf_dom_inst                          none
% 2.88/1.00  --qbf_dom_pre_inst                      false
% 2.88/1.00  --qbf_sk_in                             false
% 2.88/1.00  --qbf_pred_elim                         true
% 2.88/1.00  --qbf_split                             512
% 2.88/1.00  
% 2.88/1.00  ------ BMC1 Options
% 2.88/1.00  
% 2.88/1.00  --bmc1_incremental                      false
% 2.88/1.00  --bmc1_axioms                           reachable_all
% 2.88/1.00  --bmc1_min_bound                        0
% 2.88/1.00  --bmc1_max_bound                        -1
% 2.88/1.00  --bmc1_max_bound_default                -1
% 2.88/1.00  --bmc1_symbol_reachability              true
% 2.88/1.00  --bmc1_property_lemmas                  false
% 2.88/1.00  --bmc1_k_induction                      false
% 2.88/1.00  --bmc1_non_equiv_states                 false
% 2.88/1.00  --bmc1_deadlock                         false
% 2.88/1.00  --bmc1_ucm                              false
% 2.88/1.00  --bmc1_add_unsat_core                   none
% 2.88/1.00  --bmc1_unsat_core_children              false
% 2.88/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.88/1.00  --bmc1_out_stat                         full
% 2.88/1.00  --bmc1_ground_init                      false
% 2.88/1.00  --bmc1_pre_inst_next_state              false
% 2.88/1.00  --bmc1_pre_inst_state                   false
% 2.88/1.00  --bmc1_pre_inst_reach_state             false
% 2.88/1.00  --bmc1_out_unsat_core                   false
% 2.88/1.00  --bmc1_aig_witness_out                  false
% 2.88/1.00  --bmc1_verbose                          false
% 2.88/1.00  --bmc1_dump_clauses_tptp                false
% 2.88/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.88/1.00  --bmc1_dump_file                        -
% 2.88/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.88/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.88/1.00  --bmc1_ucm_extend_mode                  1
% 2.88/1.00  --bmc1_ucm_init_mode                    2
% 2.88/1.00  --bmc1_ucm_cone_mode                    none
% 2.88/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.88/1.00  --bmc1_ucm_relax_model                  4
% 2.88/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.88/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.88/1.00  --bmc1_ucm_layered_model                none
% 2.88/1.00  --bmc1_ucm_max_lemma_size               10
% 2.88/1.00  
% 2.88/1.00  ------ AIG Options
% 2.88/1.00  
% 2.88/1.00  --aig_mode                              false
% 2.88/1.00  
% 2.88/1.00  ------ Instantiation Options
% 2.88/1.00  
% 2.88/1.00  --instantiation_flag                    true
% 2.88/1.00  --inst_sos_flag                         false
% 2.88/1.00  --inst_sos_phase                        true
% 2.88/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.88/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.88/1.00  --inst_lit_sel_side                     none
% 2.88/1.00  --inst_solver_per_active                1400
% 2.88/1.00  --inst_solver_calls_frac                1.
% 2.88/1.00  --inst_passive_queue_type               priority_queues
% 2.88/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.88/1.00  --inst_passive_queues_freq              [25;2]
% 2.88/1.00  --inst_dismatching                      true
% 2.88/1.00  --inst_eager_unprocessed_to_passive     true
% 2.88/1.00  --inst_prop_sim_given                   true
% 2.88/1.00  --inst_prop_sim_new                     false
% 2.88/1.00  --inst_subs_new                         false
% 2.88/1.00  --inst_eq_res_simp                      false
% 2.88/1.00  --inst_subs_given                       false
% 2.88/1.00  --inst_orphan_elimination               true
% 2.88/1.00  --inst_learning_loop_flag               true
% 2.88/1.00  --inst_learning_start                   3000
% 2.88/1.00  --inst_learning_factor                  2
% 2.88/1.00  --inst_start_prop_sim_after_learn       3
% 2.88/1.00  --inst_sel_renew                        solver
% 2.88/1.00  --inst_lit_activity_flag                true
% 2.88/1.00  --inst_restr_to_given                   false
% 2.88/1.00  --inst_activity_threshold               500
% 2.88/1.00  --inst_out_proof                        true
% 2.88/1.00  
% 2.88/1.00  ------ Resolution Options
% 2.88/1.00  
% 2.88/1.00  --resolution_flag                       false
% 2.88/1.00  --res_lit_sel                           adaptive
% 2.88/1.00  --res_lit_sel_side                      none
% 2.88/1.00  --res_ordering                          kbo
% 2.88/1.00  --res_to_prop_solver                    active
% 2.88/1.00  --res_prop_simpl_new                    false
% 2.88/1.00  --res_prop_simpl_given                  true
% 2.88/1.00  --res_passive_queue_type                priority_queues
% 2.88/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.88/1.00  --res_passive_queues_freq               [15;5]
% 2.88/1.00  --res_forward_subs                      full
% 2.88/1.00  --res_backward_subs                     full
% 2.88/1.00  --res_forward_subs_resolution           true
% 2.88/1.00  --res_backward_subs_resolution          true
% 2.88/1.00  --res_orphan_elimination                true
% 2.88/1.00  --res_time_limit                        2.
% 2.88/1.00  --res_out_proof                         true
% 2.88/1.00  
% 2.88/1.00  ------ Superposition Options
% 2.88/1.00  
% 2.88/1.00  --superposition_flag                    true
% 2.88/1.00  --sup_passive_queue_type                priority_queues
% 2.88/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.88/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.88/1.00  --demod_completeness_check              fast
% 2.88/1.00  --demod_use_ground                      true
% 2.88/1.00  --sup_to_prop_solver                    passive
% 2.88/1.00  --sup_prop_simpl_new                    true
% 2.88/1.00  --sup_prop_simpl_given                  true
% 2.88/1.00  --sup_fun_splitting                     false
% 2.88/1.00  --sup_smt_interval                      50000
% 2.88/1.00  
% 2.88/1.00  ------ Superposition Simplification Setup
% 2.88/1.00  
% 2.88/1.00  --sup_indices_passive                   []
% 2.88/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.88/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.88/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.88/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.88/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.88/1.00  --sup_full_bw                           [BwDemod]
% 2.88/1.00  --sup_immed_triv                        [TrivRules]
% 2.88/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.88/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.88/1.00  --sup_immed_bw_main                     []
% 2.88/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.88/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.88/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.88/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.88/1.00  
% 2.88/1.00  ------ Combination Options
% 2.88/1.00  
% 2.88/1.00  --comb_res_mult                         3
% 2.88/1.00  --comb_sup_mult                         2
% 2.88/1.00  --comb_inst_mult                        10
% 2.88/1.00  
% 2.88/1.00  ------ Debug Options
% 2.88/1.00  
% 2.88/1.00  --dbg_backtrace                         false
% 2.88/1.00  --dbg_dump_prop_clauses                 false
% 2.88/1.00  --dbg_dump_prop_clauses_file            -
% 2.88/1.00  --dbg_out_stat                          false
% 2.88/1.00  
% 2.88/1.00  
% 2.88/1.00  
% 2.88/1.00  
% 2.88/1.00  ------ Proving...
% 2.88/1.00  
% 2.88/1.00  
% 2.88/1.00  % SZS status Theorem for theBenchmark.p
% 2.88/1.00  
% 2.88/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.88/1.00  
% 2.88/1.00  fof(f16,axiom,(
% 2.88/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 2.88/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.88/1.00  
% 2.88/1.00  fof(f34,plain,(
% 2.88/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.88/1.00    inference(ennf_transformation,[],[f16])).
% 2.88/1.00  
% 2.88/1.00  fof(f35,plain,(
% 2.88/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.88/1.00    inference(flattening,[],[f34])).
% 2.88/1.00  
% 2.88/1.00  fof(f79,plain,(
% 2.88/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.88/1.00    inference(cnf_transformation,[],[f35])).
% 2.88/1.00  
% 2.88/1.00  fof(f13,axiom,(
% 2.88/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.88/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.88/1.00  
% 2.88/1.00  fof(f30,plain,(
% 2.88/1.00    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.88/1.00    inference(ennf_transformation,[],[f13])).
% 2.88/1.00  
% 2.88/1.00  fof(f31,plain,(
% 2.88/1.00    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.88/1.00    inference(flattening,[],[f30])).
% 2.88/1.00  
% 2.88/1.00  fof(f50,plain,(
% 2.88/1.00    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.88/1.00    inference(nnf_transformation,[],[f31])).
% 2.88/1.00  
% 2.88/1.00  fof(f73,plain,(
% 2.88/1.00    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.88/1.00    inference(cnf_transformation,[],[f50])).
% 2.88/1.00  
% 2.88/1.00  fof(f20,conjecture,(
% 2.88/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 2.88/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.88/1.00  
% 2.88/1.00  fof(f21,negated_conjecture,(
% 2.88/1.00    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 2.88/1.00    inference(negated_conjecture,[],[f20])).
% 2.88/1.00  
% 2.88/1.00  fof(f40,plain,(
% 2.88/1.00    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.88/1.00    inference(ennf_transformation,[],[f21])).
% 2.88/1.00  
% 2.88/1.00  fof(f41,plain,(
% 2.88/1.00    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.88/1.00    inference(flattening,[],[f40])).
% 2.88/1.00  
% 2.88/1.00  fof(f53,plain,(
% 2.88/1.00    ( ! [X2,X0,X1] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((~v2_funct_2(sK4,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK4),k6_partfun1(X0)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK4,X1,X0) & v1_funct_1(sK4))) )),
% 2.88/1.00    introduced(choice_axiom,[])).
% 2.88/1.00  
% 2.88/1.00  fof(f52,plain,(
% 2.88/1.00    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK1) | ~v2_funct_1(sK3)) & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,X3),k6_partfun1(sK1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(X3,sK2,sK1) & v1_funct_1(X3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 2.88/1.00    introduced(choice_axiom,[])).
% 2.88/1.00  
% 2.88/1.00  fof(f54,plain,(
% 2.88/1.00    ((~v2_funct_2(sK4,sK1) | ~v2_funct_1(sK3)) & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 2.88/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f41,f53,f52])).
% 2.88/1.00  
% 2.88/1.00  fof(f90,plain,(
% 2.88/1.00    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1))),
% 2.88/1.00    inference(cnf_transformation,[],[f54])).
% 2.88/1.00  
% 2.88/1.00  fof(f14,axiom,(
% 2.88/1.00    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 2.88/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.88/1.00  
% 2.88/1.00  fof(f75,plain,(
% 2.88/1.00    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.88/1.00    inference(cnf_transformation,[],[f14])).
% 2.88/1.00  
% 2.88/1.00  fof(f17,axiom,(
% 2.88/1.00    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.88/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.88/1.00  
% 2.88/1.00  fof(f80,plain,(
% 2.88/1.00    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.88/1.00    inference(cnf_transformation,[],[f17])).
% 2.88/1.00  
% 2.88/1.00  fof(f93,plain,(
% 2.88/1.00    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.88/1.00    inference(definition_unfolding,[],[f75,f80])).
% 2.88/1.00  
% 2.88/1.00  fof(f84,plain,(
% 2.88/1.00    v1_funct_1(sK3)),
% 2.88/1.00    inference(cnf_transformation,[],[f54])).
% 2.88/1.00  
% 2.88/1.00  fof(f86,plain,(
% 2.88/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 2.88/1.00    inference(cnf_transformation,[],[f54])).
% 2.88/1.00  
% 2.88/1.00  fof(f87,plain,(
% 2.88/1.00    v1_funct_1(sK4)),
% 2.88/1.00    inference(cnf_transformation,[],[f54])).
% 2.88/1.00  
% 2.88/1.00  fof(f89,plain,(
% 2.88/1.00    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 2.88/1.00    inference(cnf_transformation,[],[f54])).
% 2.88/1.00  
% 2.88/1.00  fof(f6,axiom,(
% 2.88/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.88/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.88/1.00  
% 2.88/1.00  fof(f48,plain,(
% 2.88/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.88/1.00    inference(nnf_transformation,[],[f6])).
% 2.88/1.00  
% 2.88/1.00  fof(f64,plain,(
% 2.88/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.88/1.00    inference(cnf_transformation,[],[f48])).
% 2.88/1.00  
% 2.88/1.00  fof(f65,plain,(
% 2.88/1.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.88/1.00    inference(cnf_transformation,[],[f48])).
% 2.88/1.00  
% 2.88/1.00  fof(f19,axiom,(
% 2.88/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 2.88/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.88/1.00  
% 2.88/1.00  fof(f38,plain,(
% 2.88/1.00    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.88/1.00    inference(ennf_transformation,[],[f19])).
% 2.88/1.00  
% 2.88/1.00  fof(f39,plain,(
% 2.88/1.00    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.88/1.00    inference(flattening,[],[f38])).
% 2.88/1.00  
% 2.88/1.00  fof(f82,plain,(
% 2.88/1.00    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X3) | k1_xboole_0 = X2 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.88/1.00    inference(cnf_transformation,[],[f39])).
% 2.88/1.00  
% 2.88/1.00  fof(f85,plain,(
% 2.88/1.00    v1_funct_2(sK3,sK1,sK2)),
% 2.88/1.00    inference(cnf_transformation,[],[f54])).
% 2.88/1.00  
% 2.88/1.00  fof(f88,plain,(
% 2.88/1.00    v1_funct_2(sK4,sK2,sK1)),
% 2.88/1.00    inference(cnf_transformation,[],[f54])).
% 2.88/1.00  
% 2.88/1.00  fof(f9,axiom,(
% 2.88/1.00    ! [X0] : v2_funct_1(k6_relat_1(X0))),
% 2.88/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.88/1.00  
% 2.88/1.00  fof(f69,plain,(
% 2.88/1.00    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 2.88/1.00    inference(cnf_transformation,[],[f9])).
% 2.88/1.00  
% 2.88/1.00  fof(f92,plain,(
% 2.88/1.00    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 2.88/1.00    inference(definition_unfolding,[],[f69,f80])).
% 2.88/1.00  
% 2.88/1.00  fof(f10,axiom,(
% 2.88/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.88/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.88/1.00  
% 2.88/1.00  fof(f27,plain,(
% 2.88/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.88/1.00    inference(ennf_transformation,[],[f10])).
% 2.88/1.00  
% 2.88/1.00  fof(f70,plain,(
% 2.88/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.88/1.00    inference(cnf_transformation,[],[f27])).
% 2.88/1.00  
% 2.88/1.00  fof(f8,axiom,(
% 2.88/1.00    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 2.88/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.88/1.00  
% 2.88/1.00  fof(f26,plain,(
% 2.88/1.00    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.88/1.00    inference(ennf_transformation,[],[f8])).
% 2.88/1.00  
% 2.88/1.00  fof(f49,plain,(
% 2.88/1.00    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.88/1.00    inference(nnf_transformation,[],[f26])).
% 2.88/1.00  
% 2.88/1.00  fof(f68,plain,(
% 2.88/1.00    ( ! [X0,X1] : (v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.88/1.00    inference(cnf_transformation,[],[f49])).
% 2.88/1.00  
% 2.88/1.00  fof(f15,axiom,(
% 2.88/1.00    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 2.88/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.88/1.00  
% 2.88/1.00  fof(f32,plain,(
% 2.88/1.00    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.88/1.00    inference(ennf_transformation,[],[f15])).
% 2.88/1.00  
% 2.88/1.00  fof(f33,plain,(
% 2.88/1.00    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.88/1.00    inference(flattening,[],[f32])).
% 2.88/1.00  
% 2.88/1.00  fof(f51,plain,(
% 2.88/1.00    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.88/1.00    inference(nnf_transformation,[],[f33])).
% 2.88/1.00  
% 2.88/1.00  fof(f77,plain,(
% 2.88/1.00    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.88/1.00    inference(cnf_transformation,[],[f51])).
% 2.88/1.00  
% 2.88/1.00  fof(f97,plain,(
% 2.88/1.00    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.88/1.00    inference(equality_resolution,[],[f77])).
% 2.88/1.00  
% 2.88/1.00  fof(f91,plain,(
% 2.88/1.00    ~v2_funct_2(sK4,sK1) | ~v2_funct_1(sK3)),
% 2.88/1.00    inference(cnf_transformation,[],[f54])).
% 2.88/1.00  
% 2.88/1.00  fof(f3,axiom,(
% 2.88/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.88/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.88/1.00  
% 2.88/1.00  fof(f46,plain,(
% 2.88/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.88/1.00    inference(nnf_transformation,[],[f3])).
% 2.88/1.00  
% 2.88/1.00  fof(f47,plain,(
% 2.88/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.88/1.00    inference(flattening,[],[f46])).
% 2.88/1.00  
% 2.88/1.00  fof(f60,plain,(
% 2.88/1.00    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.88/1.00    inference(cnf_transformation,[],[f47])).
% 2.88/1.00  
% 2.88/1.00  fof(f94,plain,(
% 2.88/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.88/1.00    inference(equality_resolution,[],[f60])).
% 2.88/1.00  
% 2.88/1.00  fof(f12,axiom,(
% 2.88/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.88/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.88/1.00  
% 2.88/1.00  fof(f29,plain,(
% 2.88/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.88/1.00    inference(ennf_transformation,[],[f12])).
% 2.88/1.00  
% 2.88/1.00  fof(f72,plain,(
% 2.88/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.88/1.00    inference(cnf_transformation,[],[f29])).
% 2.88/1.00  
% 2.88/1.00  fof(f18,axiom,(
% 2.88/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 2.88/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.88/1.00  
% 2.88/1.00  fof(f36,plain,(
% 2.88/1.00    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.88/1.00    inference(ennf_transformation,[],[f18])).
% 2.88/1.00  
% 2.88/1.00  fof(f37,plain,(
% 2.88/1.00    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.88/1.00    inference(flattening,[],[f36])).
% 2.88/1.00  
% 2.88/1.00  fof(f81,plain,(
% 2.88/1.00    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.88/1.00    inference(cnf_transformation,[],[f37])).
% 2.88/1.00  
% 2.88/1.00  fof(f11,axiom,(
% 2.88/1.00    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 2.88/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.88/1.00  
% 2.88/1.00  fof(f28,plain,(
% 2.88/1.00    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 2.88/1.00    inference(ennf_transformation,[],[f11])).
% 2.88/1.00  
% 2.88/1.00  fof(f71,plain,(
% 2.88/1.00    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 2.88/1.00    inference(cnf_transformation,[],[f28])).
% 2.88/1.00  
% 2.88/1.00  fof(f2,axiom,(
% 2.88/1.00    v1_xboole_0(k1_xboole_0)),
% 2.88/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.88/1.00  
% 2.88/1.00  fof(f58,plain,(
% 2.88/1.00    v1_xboole_0(k1_xboole_0)),
% 2.88/1.00    inference(cnf_transformation,[],[f2])).
% 2.88/1.00  
% 2.88/1.00  fof(f4,axiom,(
% 2.88/1.00    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 2.88/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.88/1.00  
% 2.88/1.00  fof(f23,plain,(
% 2.88/1.00    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 2.88/1.00    inference(ennf_transformation,[],[f4])).
% 2.88/1.00  
% 2.88/1.00  fof(f62,plain,(
% 2.88/1.00    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 2.88/1.00    inference(cnf_transformation,[],[f23])).
% 2.88/1.00  
% 2.88/1.00  fof(f5,axiom,(
% 2.88/1.00    ! [X0,X1] : (v1_xboole_0(X0) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 2.88/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.88/1.00  
% 2.88/1.00  fof(f24,plain,(
% 2.88/1.00    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0))),
% 2.88/1.00    inference(ennf_transformation,[],[f5])).
% 2.88/1.00  
% 2.88/1.00  fof(f63,plain,(
% 2.88/1.00    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0)) )),
% 2.88/1.00    inference(cnf_transformation,[],[f24])).
% 2.88/1.00  
% 2.88/1.00  fof(f61,plain,(
% 2.88/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.88/1.00    inference(cnf_transformation,[],[f47])).
% 2.88/1.00  
% 2.88/1.00  cnf(c_23,plain,
% 2.88/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.88/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 2.88/1.00      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 2.88/1.00      | ~ v1_funct_1(X0)
% 2.88/1.00      | ~ v1_funct_1(X3) ),
% 2.88/1.00      inference(cnf_transformation,[],[f79]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_1662,plain,
% 2.88/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.88/1.00      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 2.88/1.00      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
% 2.88/1.00      | v1_funct_1(X3) != iProver_top
% 2.88/1.00      | v1_funct_1(X0) != iProver_top ),
% 2.88/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_19,plain,
% 2.88/1.00      ( ~ r2_relset_1(X0,X1,X2,X3)
% 2.88/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.88/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.88/1.00      | X2 = X3 ),
% 2.88/1.00      inference(cnf_transformation,[],[f73]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_29,negated_conjecture,
% 2.88/1.00      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) ),
% 2.88/1.00      inference(cnf_transformation,[],[f90]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_568,plain,
% 2.88/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.88/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.88/1.00      | X0 = X3
% 2.88/1.00      | k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) != X3
% 2.88/1.00      | k6_partfun1(sK1) != X0
% 2.88/1.00      | sK1 != X2
% 2.88/1.00      | sK1 != X1 ),
% 2.88/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_29]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_569,plain,
% 2.88/1.00      ( ~ m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 2.88/1.00      | ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 2.88/1.00      | k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
% 2.88/1.00      inference(unflattening,[status(thm)],[c_568]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_20,plain,
% 2.88/1.00      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 2.88/1.00      inference(cnf_transformation,[],[f93]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_66,plain,
% 2.88/1.00      ( m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 2.88/1.00      inference(instantiation,[status(thm)],[c_20]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_571,plain,
% 2.88/1.00      ( ~ m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 2.88/1.00      | k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
% 2.88/1.00      inference(global_propositional_subsumption,
% 2.88/1.00                [status(thm)],
% 2.88/1.00                [c_569,c_66]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_1648,plain,
% 2.88/1.00      ( k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 2.88/1.00      | m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
% 2.88/1.00      inference(predicate_to_equality,[status(thm)],[c_571]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_4380,plain,
% 2.88/1.00      ( k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k6_partfun1(sK1)
% 2.88/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 2.88/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 2.88/1.00      | v1_funct_1(sK3) != iProver_top
% 2.88/1.00      | v1_funct_1(sK4) != iProver_top ),
% 2.88/1.00      inference(superposition,[status(thm)],[c_1662,c_1648]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_35,negated_conjecture,
% 2.88/1.00      ( v1_funct_1(sK3) ),
% 2.88/1.00      inference(cnf_transformation,[],[f84]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_33,negated_conjecture,
% 2.88/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 2.88/1.00      inference(cnf_transformation,[],[f86]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_32,negated_conjecture,
% 2.88/1.00      ( v1_funct_1(sK4) ),
% 2.88/1.00      inference(cnf_transformation,[],[f87]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_30,negated_conjecture,
% 2.88/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 2.88/1.00      inference(cnf_transformation,[],[f89]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_10,plain,
% 2.88/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.88/1.00      inference(cnf_transformation,[],[f64]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_2315,plain,
% 2.88/1.00      ( ~ m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 2.88/1.00      | r1_tarski(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k2_zfmisc_1(sK1,sK1)) ),
% 2.88/1.00      inference(instantiation,[status(thm)],[c_10]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_9,plain,
% 2.88/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.88/1.00      inference(cnf_transformation,[],[f65]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_1668,plain,
% 2.88/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 2.88/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 2.88/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_2834,plain,
% 2.88/1.00      ( k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k6_partfun1(sK1)
% 2.88/1.00      | r1_tarski(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k2_zfmisc_1(sK1,sK1)) != iProver_top ),
% 2.88/1.00      inference(superposition,[status(thm)],[c_1668,c_1648]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_2839,plain,
% 2.88/1.00      ( ~ r1_tarski(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k2_zfmisc_1(sK1,sK1))
% 2.88/1.00      | k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k6_partfun1(sK1) ),
% 2.88/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_2834]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_2017,plain,
% 2.88/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.88/1.00      | m1_subset_1(k1_partfun1(X1,X2,X3,X4,X0,sK4),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
% 2.88/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 2.88/1.00      | ~ v1_funct_1(X0)
% 2.88/1.00      | ~ v1_funct_1(sK4) ),
% 2.88/1.00      inference(instantiation,[status(thm)],[c_23]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_2258,plain,
% 2.88/1.00      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
% 2.88/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.88/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 2.88/1.00      | ~ v1_funct_1(sK3)
% 2.88/1.00      | ~ v1_funct_1(sK4) ),
% 2.88/1.00      inference(instantiation,[status(thm)],[c_2017]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_2760,plain,
% 2.88/1.00      ( m1_subset_1(k1_partfun1(sK1,sK2,X0,X1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
% 2.88/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.88/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.88/1.00      | ~ v1_funct_1(sK3)
% 2.88/1.00      | ~ v1_funct_1(sK4) ),
% 2.88/1.00      inference(instantiation,[status(thm)],[c_2258]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_4184,plain,
% 2.88/1.00      ( m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 2.88/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.88/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 2.88/1.00      | ~ v1_funct_1(sK3)
% 2.88/1.00      | ~ v1_funct_1(sK4) ),
% 2.88/1.00      inference(instantiation,[status(thm)],[c_2760]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_4618,plain,
% 2.88/1.00      ( k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k6_partfun1(sK1) ),
% 2.88/1.00      inference(global_propositional_subsumption,
% 2.88/1.00                [status(thm)],
% 2.88/1.00                [c_4380,c_35,c_33,c_32,c_30,c_2315,c_2839,c_4184]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_27,plain,
% 2.88/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.88/1.00      | ~ v1_funct_2(X3,X2,X4)
% 2.88/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.88/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
% 2.88/1.00      | ~ v1_funct_1(X3)
% 2.88/1.00      | ~ v1_funct_1(X0)
% 2.88/1.00      | v2_funct_1(X0)
% 2.88/1.00      | ~ v2_funct_1(k1_partfun1(X1,X2,X2,X4,X0,X3))
% 2.88/1.00      | k1_xboole_0 = X4 ),
% 2.88/1.00      inference(cnf_transformation,[],[f82]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_1659,plain,
% 2.88/1.00      ( k1_xboole_0 = X0
% 2.88/1.00      | v1_funct_2(X1,X2,X3) != iProver_top
% 2.88/1.00      | v1_funct_2(X4,X3,X0) != iProver_top
% 2.88/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 2.88/1.00      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) != iProver_top
% 2.88/1.00      | v1_funct_1(X4) != iProver_top
% 2.88/1.00      | v1_funct_1(X1) != iProver_top
% 2.88/1.00      | v2_funct_1(X1) = iProver_top
% 2.88/1.00      | v2_funct_1(k1_partfun1(X2,X3,X3,X0,X1,X4)) != iProver_top ),
% 2.88/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_4644,plain,
% 2.88/1.00      ( sK1 = k1_xboole_0
% 2.88/1.00      | v1_funct_2(sK3,sK1,sK2) != iProver_top
% 2.88/1.00      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 2.88/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 2.88/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 2.88/1.00      | v1_funct_1(sK3) != iProver_top
% 2.88/1.00      | v1_funct_1(sK4) != iProver_top
% 2.88/1.00      | v2_funct_1(k6_partfun1(sK1)) != iProver_top
% 2.88/1.00      | v2_funct_1(sK3) = iProver_top ),
% 2.88/1.00      inference(superposition,[status(thm)],[c_4618,c_1659]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_36,plain,
% 2.88/1.00      ( v1_funct_1(sK3) = iProver_top ),
% 2.88/1.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_34,negated_conjecture,
% 2.88/1.00      ( v1_funct_2(sK3,sK1,sK2) ),
% 2.88/1.00      inference(cnf_transformation,[],[f85]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_37,plain,
% 2.88/1.00      ( v1_funct_2(sK3,sK1,sK2) = iProver_top ),
% 2.88/1.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_38,plain,
% 2.88/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 2.88/1.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_39,plain,
% 2.88/1.00      ( v1_funct_1(sK4) = iProver_top ),
% 2.88/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_31,negated_conjecture,
% 2.88/1.00      ( v1_funct_2(sK4,sK2,sK1) ),
% 2.88/1.00      inference(cnf_transformation,[],[f88]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_40,plain,
% 2.88/1.00      ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
% 2.88/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_41,plain,
% 2.88/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 2.88/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_14,plain,
% 2.88/1.00      ( v2_funct_1(k6_partfun1(X0)) ),
% 2.88/1.00      inference(cnf_transformation,[],[f92]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_81,plain,
% 2.88/1.00      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 2.88/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_83,plain,
% 2.88/1.00      ( v2_funct_1(k6_partfun1(sK1)) = iProver_top ),
% 2.88/1.00      inference(instantiation,[status(thm)],[c_81]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_15,plain,
% 2.88/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.88/1.00      | v1_relat_1(X0) ),
% 2.88/1.00      inference(cnf_transformation,[],[f70]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_12,plain,
% 2.88/1.00      ( v5_relat_1(X0,X1)
% 2.88/1.00      | ~ r1_tarski(k2_relat_1(X0),X1)
% 2.88/1.00      | ~ v1_relat_1(X0) ),
% 2.88/1.00      inference(cnf_transformation,[],[f68]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_21,plain,
% 2.88/1.00      ( v2_funct_2(X0,k2_relat_1(X0))
% 2.88/1.00      | ~ v5_relat_1(X0,k2_relat_1(X0))
% 2.88/1.00      | ~ v1_relat_1(X0) ),
% 2.88/1.00      inference(cnf_transformation,[],[f97]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_28,negated_conjecture,
% 2.88/1.00      ( ~ v2_funct_2(sK4,sK1) | ~ v2_funct_1(sK3) ),
% 2.88/1.00      inference(cnf_transformation,[],[f91]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_470,plain,
% 2.88/1.00      ( ~ v5_relat_1(X0,k2_relat_1(X0))
% 2.88/1.00      | ~ v2_funct_1(sK3)
% 2.88/1.00      | ~ v1_relat_1(X0)
% 2.88/1.00      | k2_relat_1(X0) != sK1
% 2.88/1.00      | sK4 != X0 ),
% 2.88/1.00      inference(resolution_lifted,[status(thm)],[c_21,c_28]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_471,plain,
% 2.88/1.00      ( ~ v5_relat_1(sK4,k2_relat_1(sK4))
% 2.88/1.00      | ~ v2_funct_1(sK3)
% 2.88/1.00      | ~ v1_relat_1(sK4)
% 2.88/1.00      | k2_relat_1(sK4) != sK1 ),
% 2.88/1.00      inference(unflattening,[status(thm)],[c_470]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_492,plain,
% 2.88/1.00      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 2.88/1.00      | ~ v2_funct_1(sK3)
% 2.88/1.00      | ~ v1_relat_1(X0)
% 2.88/1.00      | ~ v1_relat_1(sK4)
% 2.88/1.00      | k2_relat_1(sK4) != X1
% 2.88/1.00      | k2_relat_1(sK4) != sK1
% 2.88/1.00      | sK4 != X0 ),
% 2.88/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_471]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_493,plain,
% 2.88/1.00      ( ~ r1_tarski(k2_relat_1(sK4),k2_relat_1(sK4))
% 2.88/1.00      | ~ v2_funct_1(sK3)
% 2.88/1.00      | ~ v1_relat_1(sK4)
% 2.88/1.00      | k2_relat_1(sK4) != sK1 ),
% 2.88/1.00      inference(unflattening,[status(thm)],[c_492]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_5,plain,
% 2.88/1.00      ( r1_tarski(X0,X0) ),
% 2.88/1.00      inference(cnf_transformation,[],[f94]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_503,plain,
% 2.88/1.00      ( ~ v2_funct_1(sK3) | ~ v1_relat_1(sK4) | k2_relat_1(sK4) != sK1 ),
% 2.88/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_493,c_5]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_512,plain,
% 2.88/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.88/1.00      | ~ v2_funct_1(sK3)
% 2.88/1.00      | k2_relat_1(sK4) != sK1
% 2.88/1.00      | sK4 != X0 ),
% 2.88/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_503]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_513,plain,
% 2.88/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.88/1.00      | ~ v2_funct_1(sK3)
% 2.88/1.00      | k2_relat_1(sK4) != sK1 ),
% 2.88/1.00      inference(unflattening,[status(thm)],[c_512]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_904,plain,
% 2.88/1.00      ( ~ v2_funct_1(sK3) | sP0_iProver_split | k2_relat_1(sK4) != sK1 ),
% 2.88/1.00      inference(splitting,
% 2.88/1.00                [splitting(split),new_symbols(definition,[])],
% 2.88/1.00                [c_513]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_937,plain,
% 2.88/1.00      ( k2_relat_1(sK4) != sK1
% 2.88/1.00      | v2_funct_1(sK3) != iProver_top
% 2.88/1.00      | sP0_iProver_split = iProver_top ),
% 2.88/1.00      inference(predicate_to_equality,[status(thm)],[c_904]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_1658,plain,
% 2.88/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 2.88/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_903,plain,
% 2.88/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.88/1.00      | ~ sP0_iProver_split ),
% 2.88/1.00      inference(splitting,
% 2.88/1.00                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.88/1.00                [c_513]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_1651,plain,
% 2.88/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.88/1.00      | sP0_iProver_split != iProver_top ),
% 2.88/1.00      inference(predicate_to_equality,[status(thm)],[c_903]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_2426,plain,
% 2.88/1.00      ( sP0_iProver_split != iProver_top ),
% 2.88/1.00      inference(superposition,[status(thm)],[c_1658,c_1651]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_17,plain,
% 2.88/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.88/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.88/1.00      inference(cnf_transformation,[],[f72]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_1664,plain,
% 2.88/1.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.88/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.88/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_3355,plain,
% 2.88/1.00      ( k2_relset_1(sK2,sK1,sK4) = k2_relat_1(sK4) ),
% 2.88/1.00      inference(superposition,[status(thm)],[c_1658,c_1664]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_25,plain,
% 2.88/1.00      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 2.88/1.00      | ~ v1_funct_2(X2,X0,X1)
% 2.88/1.00      | ~ v1_funct_2(X3,X1,X0)
% 2.88/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.88/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.88/1.00      | ~ v1_funct_1(X3)
% 2.88/1.00      | ~ v1_funct_1(X2)
% 2.88/1.00      | k2_relset_1(X1,X0,X3) = X0 ),
% 2.88/1.00      inference(cnf_transformation,[],[f81]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_582,plain,
% 2.88/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.88/1.00      | ~ v1_funct_2(X3,X2,X1)
% 2.88/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.88/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.88/1.00      | ~ v1_funct_1(X3)
% 2.88/1.00      | ~ v1_funct_1(X0)
% 2.88/1.00      | k1_partfun1(X1,X2,X2,X1,X0,X3) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 2.88/1.00      | k2_relset_1(X2,X1,X3) = X1
% 2.88/1.00      | k6_partfun1(X1) != k6_partfun1(sK1)
% 2.88/1.00      | sK1 != X1 ),
% 2.88/1.00      inference(resolution_lifted,[status(thm)],[c_25,c_29]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_583,plain,
% 2.88/1.00      ( ~ v1_funct_2(X0,X1,sK1)
% 2.88/1.00      | ~ v1_funct_2(X2,sK1,X1)
% 2.88/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
% 2.88/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
% 2.88/1.00      | ~ v1_funct_1(X2)
% 2.88/1.00      | ~ v1_funct_1(X0)
% 2.88/1.00      | k1_partfun1(sK1,X1,X1,sK1,X2,X0) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 2.88/1.00      | k2_relset_1(X1,sK1,X0) = sK1
% 2.88/1.00      | k6_partfun1(sK1) != k6_partfun1(sK1) ),
% 2.88/1.00      inference(unflattening,[status(thm)],[c_582]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_666,plain,
% 2.88/1.00      ( ~ v1_funct_2(X0,X1,sK1)
% 2.88/1.00      | ~ v1_funct_2(X2,sK1,X1)
% 2.88/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
% 2.88/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
% 2.88/1.00      | ~ v1_funct_1(X0)
% 2.88/1.00      | ~ v1_funct_1(X2)
% 2.88/1.00      | k1_partfun1(sK1,X1,X1,sK1,X2,X0) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 2.88/1.00      | k2_relset_1(X1,sK1,X0) = sK1 ),
% 2.88/1.00      inference(equality_resolution_simp,[status(thm)],[c_583]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_1647,plain,
% 2.88/1.00      ( k1_partfun1(sK1,X0,X0,sK1,X1,X2) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 2.88/1.00      | k2_relset_1(X0,sK1,X2) = sK1
% 2.88/1.00      | v1_funct_2(X2,X0,sK1) != iProver_top
% 2.88/1.00      | v1_funct_2(X1,sK1,X0) != iProver_top
% 2.88/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
% 2.88/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 2.88/1.00      | v1_funct_1(X2) != iProver_top
% 2.88/1.00      | v1_funct_1(X1) != iProver_top ),
% 2.88/1.00      inference(predicate_to_equality,[status(thm)],[c_666]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_2073,plain,
% 2.88/1.00      ( k2_relset_1(sK2,sK1,sK4) = sK1
% 2.88/1.00      | v1_funct_2(sK3,sK1,sK2) != iProver_top
% 2.88/1.00      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 2.88/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 2.88/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 2.88/1.00      | v1_funct_1(sK3) != iProver_top
% 2.88/1.00      | v1_funct_1(sK4) != iProver_top ),
% 2.88/1.00      inference(equality_resolution,[status(thm)],[c_1647]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_2325,plain,
% 2.88/1.00      ( k2_relset_1(sK2,sK1,sK4) = sK1 ),
% 2.88/1.00      inference(global_propositional_subsumption,
% 2.88/1.00                [status(thm)],
% 2.88/1.00                [c_2073,c_36,c_37,c_38,c_39,c_40,c_41]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_3365,plain,
% 2.88/1.00      ( k2_relat_1(sK4) = sK1 ),
% 2.88/1.00      inference(light_normalisation,[status(thm)],[c_3355,c_2325]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_4757,plain,
% 2.88/1.00      ( sK1 = k1_xboole_0 ),
% 2.88/1.00      inference(global_propositional_subsumption,
% 2.88/1.00                [status(thm)],
% 2.88/1.00                [c_4644,c_36,c_37,c_38,c_39,c_40,c_41,c_83,c_937,c_2426,
% 2.88/1.00                 c_3365]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_1655,plain,
% 2.88/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 2.88/1.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_16,plain,
% 2.88/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.88/1.00      | ~ v1_xboole_0(X1)
% 2.88/1.00      | v1_xboole_0(X0) ),
% 2.88/1.00      inference(cnf_transformation,[],[f71]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_1665,plain,
% 2.88/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.88/1.00      | v1_xboole_0(X1) != iProver_top
% 2.88/1.00      | v1_xboole_0(X0) = iProver_top ),
% 2.88/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_3778,plain,
% 2.88/1.00      ( v1_xboole_0(sK3) = iProver_top
% 2.88/1.00      | v1_xboole_0(sK1) != iProver_top ),
% 2.88/1.00      inference(superposition,[status(thm)],[c_1655,c_1665]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_4766,plain,
% 2.88/1.00      ( v1_xboole_0(sK3) = iProver_top
% 2.88/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.88/1.00      inference(demodulation,[status(thm)],[c_4757,c_3778]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_3,plain,
% 2.88/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 2.88/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_112,plain,
% 2.88/1.00      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.88/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_909,plain,
% 2.88/1.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 2.88/1.00      theory(equality) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_2051,plain,
% 2.88/1.00      ( v1_xboole_0(X0)
% 2.88/1.00      | ~ v1_xboole_0(k1_xboole_0)
% 2.88/1.00      | X0 != k1_xboole_0 ),
% 2.88/1.00      inference(instantiation,[status(thm)],[c_909]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_2052,plain,
% 2.88/1.00      ( X0 != k1_xboole_0
% 2.88/1.00      | v1_xboole_0(X0) = iProver_top
% 2.88/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.88/1.00      inference(predicate_to_equality,[status(thm)],[c_2051]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_2054,plain,
% 2.88/1.00      ( sK1 != k1_xboole_0
% 2.88/1.00      | v1_xboole_0(sK1) = iProver_top
% 2.88/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.88/1.00      inference(instantiation,[status(thm)],[c_2052]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_5636,plain,
% 2.88/1.00      ( v1_xboole_0(sK3) = iProver_top ),
% 2.88/1.00      inference(global_propositional_subsumption,
% 2.88/1.00                [status(thm)],
% 2.88/1.00                [c_4766,c_36,c_37,c_38,c_39,c_40,c_41,c_83,c_112,c_937,
% 2.88/1.00                 c_2054,c_2426,c_3365,c_3778,c_4644]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_1673,plain,
% 2.88/1.00      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.88/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_7,plain,
% 2.88/1.00      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X0 = X1 ),
% 2.88/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_1670,plain,
% 2.88/1.00      ( X0 = X1
% 2.88/1.00      | v1_xboole_0(X1) != iProver_top
% 2.88/1.00      | v1_xboole_0(X0) != iProver_top ),
% 2.88/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_2904,plain,
% 2.88/1.00      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 2.88/1.00      inference(superposition,[status(thm)],[c_1673,c_1670]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_5646,plain,
% 2.88/1.00      ( sK3 = k1_xboole_0 ),
% 2.88/1.00      inference(superposition,[status(thm)],[c_5636,c_2904]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_1650,plain,
% 2.88/1.00      ( k2_relat_1(sK4) != sK1
% 2.88/1.00      | v2_funct_1(sK3) != iProver_top
% 2.88/1.00      | sP0_iProver_split = iProver_top ),
% 2.88/1.00      inference(predicate_to_equality,[status(thm)],[c_904]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_2563,plain,
% 2.88/1.00      ( v2_funct_1(sK3) != iProver_top | k2_relat_1(sK4) != sK1 ),
% 2.88/1.00      inference(global_propositional_subsumption,
% 2.88/1.00                [status(thm)],
% 2.88/1.00                [c_1650,c_937,c_2426]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_2564,plain,
% 2.88/1.00      ( k2_relat_1(sK4) != sK1 | v2_funct_1(sK3) != iProver_top ),
% 2.88/1.00      inference(renaming,[status(thm)],[c_2563]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_4163,plain,
% 2.88/1.00      ( sK1 != sK1 | v2_funct_1(sK3) != iProver_top ),
% 2.88/1.00      inference(demodulation,[status(thm)],[c_3365,c_2564]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_4206,plain,
% 2.88/1.00      ( v2_funct_1(sK3) != iProver_top ),
% 2.88/1.00      inference(equality_resolution_simp,[status(thm)],[c_4163]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_5729,plain,
% 2.88/1.00      ( v2_funct_1(k1_xboole_0) != iProver_top ),
% 2.88/1.00      inference(demodulation,[status(thm)],[c_5646,c_4206]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_8,plain,
% 2.88/1.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(k2_zfmisc_1(X0,X1)) ),
% 2.88/1.00      inference(cnf_transformation,[],[f63]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_1669,plain,
% 2.88/1.00      ( v1_xboole_0(X0) != iProver_top
% 2.88/1.00      | v1_xboole_0(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 2.88/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_3037,plain,
% 2.88/1.00      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
% 2.88/1.00      | v1_xboole_0(X0) != iProver_top ),
% 2.88/1.00      inference(superposition,[status(thm)],[c_1669,c_2904]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_3048,plain,
% 2.88/1.00      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.88/1.00      inference(superposition,[status(thm)],[c_1673,c_3037]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_1663,plain,
% 2.88/1.00      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 2.88/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_1667,plain,
% 2.88/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.88/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 2.88/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_2725,plain,
% 2.88/1.00      ( r1_tarski(k6_partfun1(X0),k2_zfmisc_1(X0,X0)) = iProver_top ),
% 2.88/1.00      inference(superposition,[status(thm)],[c_1663,c_1667]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_3153,plain,
% 2.88/1.00      ( r1_tarski(k6_partfun1(k1_xboole_0),k1_xboole_0) = iProver_top ),
% 2.88/1.00      inference(superposition,[status(thm)],[c_3048,c_2725]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_4,plain,
% 2.88/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 2.88/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_1672,plain,
% 2.88/1.00      ( X0 = X1
% 2.88/1.00      | r1_tarski(X1,X0) != iProver_top
% 2.88/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 2.88/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_3614,plain,
% 2.88/1.00      ( k6_partfun1(k1_xboole_0) = k1_xboole_0
% 2.88/1.00      | r1_tarski(k1_xboole_0,k6_partfun1(k1_xboole_0)) != iProver_top ),
% 2.88/1.00      inference(superposition,[status(thm)],[c_3153,c_1672]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_1997,plain,
% 2.88/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.88/1.00      | v1_xboole_0(X0)
% 2.88/1.00      | ~ v1_xboole_0(k1_xboole_0) ),
% 2.88/1.00      inference(instantiation,[status(thm)],[c_16]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_2485,plain,
% 2.88/1.00      ( ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
% 2.88/1.00      | v1_xboole_0(k6_partfun1(k1_xboole_0))
% 2.88/1.00      | ~ v1_xboole_0(k1_xboole_0) ),
% 2.88/1.00      inference(instantiation,[status(thm)],[c_1997]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_2486,plain,
% 2.88/1.00      ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
% 2.88/1.00      inference(instantiation,[status(thm)],[c_20]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_2190,plain,
% 2.88/1.00      ( ~ v1_xboole_0(X0)
% 2.88/1.00      | ~ v1_xboole_0(k1_xboole_0)
% 2.88/1.00      | X0 = k1_xboole_0 ),
% 2.88/1.00      inference(instantiation,[status(thm)],[c_7]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_3289,plain,
% 2.88/1.00      ( ~ v1_xboole_0(k6_partfun1(k1_xboole_0))
% 2.88/1.00      | ~ v1_xboole_0(k1_xboole_0)
% 2.88/1.00      | k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 2.88/1.00      inference(instantiation,[status(thm)],[c_2190]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_4554,plain,
% 2.88/1.00      ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 2.88/1.00      inference(global_propositional_subsumption,
% 2.88/1.00                [status(thm)],
% 2.88/1.00                [c_3614,c_3,c_2485,c_2486,c_3289]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_1666,plain,
% 2.88/1.00      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 2.88/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_4567,plain,
% 2.88/1.00      ( v2_funct_1(k1_xboole_0) = iProver_top ),
% 2.88/1.00      inference(superposition,[status(thm)],[c_4554,c_1666]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(contradiction,plain,
% 2.88/1.00      ( $false ),
% 2.88/1.00      inference(minisat,[status(thm)],[c_5729,c_4567]) ).
% 2.88/1.00  
% 2.88/1.00  
% 2.88/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.88/1.00  
% 2.88/1.00  ------                               Statistics
% 2.88/1.00  
% 2.88/1.00  ------ General
% 2.88/1.00  
% 2.88/1.00  abstr_ref_over_cycles:                  0
% 2.88/1.00  abstr_ref_under_cycles:                 0
% 2.88/1.00  gc_basic_clause_elim:                   0
% 2.88/1.00  forced_gc_time:                         0
% 2.88/1.00  parsing_time:                           0.013
% 2.88/1.00  unif_index_cands_time:                  0.
% 2.88/1.00  unif_index_add_time:                    0.
% 2.88/1.00  orderings_time:                         0.
% 2.88/1.00  out_proof_time:                         0.013
% 2.88/1.00  total_time:                             0.221
% 2.88/1.00  num_of_symbols:                         55
% 2.88/1.00  num_of_terms:                           7204
% 2.88/1.00  
% 2.88/1.00  ------ Preprocessing
% 2.88/1.00  
% 2.88/1.00  num_of_splits:                          1
% 2.88/1.00  num_of_split_atoms:                     1
% 2.88/1.00  num_of_reused_defs:                     0
% 2.88/1.00  num_eq_ax_congr_red:                    24
% 2.88/1.00  num_of_sem_filtered_clauses:            1
% 2.88/1.00  num_of_subtypes:                        0
% 2.88/1.00  monotx_restored_types:                  0
% 2.88/1.00  sat_num_of_epr_types:                   0
% 2.88/1.00  sat_num_of_non_cyclic_types:            0
% 2.88/1.00  sat_guarded_non_collapsed_types:        0
% 2.88/1.00  num_pure_diseq_elim:                    0
% 2.88/1.00  simp_replaced_by:                       0
% 2.88/1.00  res_preprocessed:                       153
% 2.88/1.00  prep_upred:                             0
% 2.88/1.00  prep_unflattend:                        18
% 2.88/1.00  smt_new_axioms:                         0
% 2.88/1.00  pred_elim_cands:                        7
% 2.88/1.00  pred_elim:                              4
% 2.88/1.00  pred_elim_cl:                           6
% 2.88/1.00  pred_elim_cycles:                       6
% 2.88/1.00  merged_defs:                            8
% 2.88/1.00  merged_defs_ncl:                        0
% 2.88/1.00  bin_hyper_res:                          9
% 2.88/1.00  prep_cycles:                            4
% 2.88/1.00  pred_elim_time:                         0.008
% 2.88/1.00  splitting_time:                         0.
% 2.88/1.00  sem_filter_time:                        0.
% 2.88/1.00  monotx_time:                            0.001
% 2.88/1.00  subtype_inf_time:                       0.
% 2.88/1.00  
% 2.88/1.00  ------ Problem properties
% 2.88/1.00  
% 2.88/1.00  clauses:                                30
% 2.88/1.00  conjectures:                            6
% 2.88/1.00  epr:                                    10
% 2.88/1.00  horn:                                   28
% 2.88/1.00  ground:                                 9
% 2.88/1.00  unary:                                  10
% 2.88/1.00  binary:                                 8
% 2.88/1.00  lits:                                   87
% 2.88/1.00  lits_eq:                                10
% 2.88/1.00  fd_pure:                                0
% 2.88/1.00  fd_pseudo:                              0
% 2.88/1.00  fd_cond:                                1
% 2.88/1.00  fd_pseudo_cond:                         2
% 2.88/1.00  ac_symbols:                             0
% 2.88/1.00  
% 2.88/1.00  ------ Propositional Solver
% 2.88/1.00  
% 2.88/1.00  prop_solver_calls:                      26
% 2.88/1.00  prop_fast_solver_calls:                 1104
% 2.88/1.00  smt_solver_calls:                       0
% 2.88/1.00  smt_fast_solver_calls:                  0
% 2.88/1.00  prop_num_of_clauses:                    2156
% 2.88/1.00  prop_preprocess_simplified:             6320
% 2.88/1.00  prop_fo_subsumed:                       26
% 2.88/1.00  prop_solver_time:                       0.
% 2.88/1.00  smt_solver_time:                        0.
% 2.88/1.00  smt_fast_solver_time:                   0.
% 2.88/1.00  prop_fast_solver_time:                  0.
% 2.88/1.00  prop_unsat_core_time:                   0.
% 2.88/1.00  
% 2.88/1.00  ------ QBF
% 2.88/1.00  
% 2.88/1.00  qbf_q_res:                              0
% 2.88/1.00  qbf_num_tautologies:                    0
% 2.88/1.00  qbf_prep_cycles:                        0
% 2.88/1.00  
% 2.88/1.00  ------ BMC1
% 2.88/1.00  
% 2.88/1.00  bmc1_current_bound:                     -1
% 2.88/1.00  bmc1_last_solved_bound:                 -1
% 2.88/1.00  bmc1_unsat_core_size:                   -1
% 2.88/1.00  bmc1_unsat_core_parents_size:           -1
% 2.88/1.00  bmc1_merge_next_fun:                    0
% 2.88/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.88/1.00  
% 2.88/1.00  ------ Instantiation
% 2.88/1.00  
% 2.88/1.00  inst_num_of_clauses:                    586
% 2.88/1.00  inst_num_in_passive:                    121
% 2.88/1.00  inst_num_in_active:                     290
% 2.88/1.00  inst_num_in_unprocessed:                175
% 2.88/1.00  inst_num_of_loops:                      350
% 2.88/1.00  inst_num_of_learning_restarts:          0
% 2.88/1.00  inst_num_moves_active_passive:          57
% 2.88/1.00  inst_lit_activity:                      0
% 2.88/1.00  inst_lit_activity_moves:                0
% 2.88/1.00  inst_num_tautologies:                   0
% 2.88/1.00  inst_num_prop_implied:                  0
% 2.88/1.00  inst_num_existing_simplified:           0
% 2.88/1.00  inst_num_eq_res_simplified:             0
% 2.88/1.00  inst_num_child_elim:                    0
% 2.88/1.00  inst_num_of_dismatching_blockings:      132
% 2.88/1.00  inst_num_of_non_proper_insts:           593
% 2.88/1.00  inst_num_of_duplicates:                 0
% 2.88/1.00  inst_inst_num_from_inst_to_res:         0
% 2.88/1.00  inst_dismatching_checking_time:         0.
% 2.88/1.00  
% 2.88/1.00  ------ Resolution
% 2.88/1.00  
% 2.88/1.00  res_num_of_clauses:                     0
% 2.88/1.00  res_num_in_passive:                     0
% 2.88/1.00  res_num_in_active:                      0
% 2.88/1.00  res_num_of_loops:                       157
% 2.88/1.00  res_forward_subset_subsumed:            40
% 2.88/1.00  res_backward_subset_subsumed:           0
% 2.88/1.00  res_forward_subsumed:                   0
% 2.88/1.00  res_backward_subsumed:                  0
% 2.88/1.00  res_forward_subsumption_resolution:     2
% 2.88/1.00  res_backward_subsumption_resolution:    0
% 2.88/1.00  res_clause_to_clause_subsumption:       254
% 2.88/1.00  res_orphan_elimination:                 0
% 2.88/1.00  res_tautology_del:                      35
% 2.88/1.00  res_num_eq_res_simplified:              1
% 2.88/1.00  res_num_sel_changes:                    0
% 2.88/1.00  res_moves_from_active_to_pass:          0
% 2.88/1.00  
% 2.88/1.00  ------ Superposition
% 2.88/1.00  
% 2.88/1.00  sup_time_total:                         0.
% 2.88/1.00  sup_time_generating:                    0.
% 2.88/1.00  sup_time_sim_full:                      0.
% 2.88/1.00  sup_time_sim_immed:                     0.
% 2.88/1.00  
% 2.88/1.00  sup_num_of_clauses:                     74
% 2.88/1.00  sup_num_in_active:                      41
% 2.88/1.00  sup_num_in_passive:                     33
% 2.88/1.00  sup_num_of_loops:                       68
% 2.88/1.00  sup_fw_superposition:                   40
% 2.88/1.00  sup_bw_superposition:                   37
% 2.88/1.00  sup_immediate_simplified:               23
% 2.88/1.00  sup_given_eliminated:                   1
% 2.88/1.00  comparisons_done:                       0
% 2.88/1.00  comparisons_avoided:                    0
% 2.88/1.00  
% 2.88/1.00  ------ Simplifications
% 2.88/1.00  
% 2.88/1.00  
% 2.88/1.00  sim_fw_subset_subsumed:                 2
% 2.88/1.00  sim_bw_subset_subsumed:                 2
% 2.88/1.00  sim_fw_subsumed:                        2
% 2.88/1.00  sim_bw_subsumed:                        0
% 2.88/1.00  sim_fw_subsumption_res:                 0
% 2.88/1.00  sim_bw_subsumption_res:                 0
% 2.88/1.00  sim_tautology_del:                      3
% 2.88/1.00  sim_eq_tautology_del:                   4
% 2.88/1.00  sim_eq_res_simp:                        1
% 2.88/1.00  sim_fw_demodulated:                     9
% 2.88/1.00  sim_bw_demodulated:                     26
% 2.88/1.00  sim_light_normalised:                   11
% 2.88/1.00  sim_joinable_taut:                      0
% 2.88/1.00  sim_joinable_simp:                      0
% 2.88/1.00  sim_ac_normalised:                      0
% 2.88/1.00  sim_smt_subsumption:                    0
% 2.88/1.00  
%------------------------------------------------------------------------------
