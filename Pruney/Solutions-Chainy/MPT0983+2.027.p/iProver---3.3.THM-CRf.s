%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:01:50 EST 2020

% Result     : Theorem 2.89s
% Output     : CNFRefutation 2.89s
% Verified   : 
% Statistics : Number of formulae       :  168 ( 774 expanded)
%              Number of clauses        :   95 ( 239 expanded)
%              Number of leaves         :   22 ( 192 expanded)
%              Depth                    :   21
%              Number of atoms          :  555 (4899 expanded)
%              Number of equality atoms :  217 ( 455 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f29])).

fof(f62,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f25])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f17,conjecture,(
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

fof(f18,negated_conjecture,(
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
    inference(negated_conjecture,[],[f17])).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f42,plain,(
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

fof(f41,plain,
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

fof(f43,plain,
    ( ( ~ v2_funct_2(sK3,sK0)
      | ~ v2_funct_1(sK2) )
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f36,f42,f41])).

fof(f73,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f43])).

fof(f11,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f11])).

fof(f14,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f78,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f58,f63])).

fof(f67,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f69,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f43])).

fof(f70,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f72,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f43])).

fof(f16,axiom,(
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

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f65,plain,(
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
    inference(cnf_transformation,[],[f34])).

fof(f68,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f71,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f15,axiom,(
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

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f82,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f60])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f74,plain,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f6,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f76,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f52,f63])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f37])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f80,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f47])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f45,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f5,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f75,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f50,f63])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1015,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_13,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_23,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_395,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_23])).

cnf(c_396,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_395])).

cnf(c_14,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_404,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_396,c_14])).

cnf(c_1002,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_404])).

cnf(c_2890,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1015,c_1002])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_30,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_32,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_33,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_35,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3089,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2890,c_30,c_32,c_33,c_35])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v2_funct_1(X3)
    | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1012,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | v1_funct_2(X3,X4,X2) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v2_funct_1(X3) = iProver_top
    | v2_funct_1(k1_partfun1(X4,X2,X2,X0,X3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3116,plain,
    ( sK0 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3089,c_1012])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_31,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_25,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_34,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_1011,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1017,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1981,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1011,c_1017])).

cnf(c_19,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_408,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X2,X1,X1,X2,X3,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,X2,X0) = X2
    | k6_partfun1(X2) != k6_partfun1(sK0)
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_23])).

cnf(c_409,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0
    | k6_partfun1(sK0) != k6_partfun1(sK0) ),
    inference(unflattening,[status(thm)],[c_408])).

cnf(c_483,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_409])).

cnf(c_1001,plain,
    ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X0,sK0,X2) = sK0
    | v1_funct_2(X2,X0,sK0) != iProver_top
    | v1_funct_2(X1,sK0,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_483])).

cnf(c_1771,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1001])).

cnf(c_1819,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1771,c_30,c_31,c_32,c_33,c_34,c_35])).

cnf(c_1996,plain,
    ( k2_relat_1(sK3) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_1981,c_1819])).

cnf(c_10,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_15,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_313,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X0)
    | X0 != X1
    | k2_relat_1(X0) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_15])).

cnf(c_314,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_313])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_324,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0)))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_314,c_9])).

cnf(c_22,negated_conjecture,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_339,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
    | ~ v2_funct_1(sK2)
    | k2_relat_1(X0) != sK0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_324,c_22])).

cnf(c_340,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3))))
    | ~ v2_funct_1(sK2)
    | k2_relat_1(sK3) != sK0 ),
    inference(unflattening,[status(thm)],[c_339])).

cnf(c_604,plain,
    ( ~ v2_funct_1(sK2)
    | sP0_iProver_split
    | k2_relat_1(sK3) != sK0 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_340])).

cnf(c_1004,plain,
    ( k2_relat_1(sK3) != sK0
    | v2_funct_1(sK2) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_604])).

cnf(c_2107,plain,
    ( sK0 != sK0
    | v2_funct_1(sK2) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(demodulation,[status(thm)],[c_1996,c_1004])).

cnf(c_2108,plain,
    ( v2_funct_1(sK2) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2107])).

cnf(c_603,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3))))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_340])).

cnf(c_1005,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3)))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_603])).

cnf(c_2106,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(demodulation,[status(thm)],[c_1996,c_1005])).

cnf(c_2124,plain,
    ( sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_1011,c_2106])).

cnf(c_3255,plain,
    ( v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | sK0 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3116,c_30,c_31,c_32,c_33,c_34,c_35,c_2108,c_2124])).

cnf(c_3256,plain,
    ( sK0 = k1_xboole_0
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3255])).

cnf(c_7,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1018,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3261,plain,
    ( sK0 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3256,c_1018])).

cnf(c_1008,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_3271,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3261,c_1008])).

cnf(c_3,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_3279,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3271,c_3])).

cnf(c_607,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1718,plain,
    ( X0 != X1
    | sK2 != X1
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_607])).

cnf(c_2311,plain,
    ( X0 != sK2
    | sK2 = X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1718])).

cnf(c_2312,plain,
    ( sK2 != sK2
    | sK2 = k1_xboole_0
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_2311])).

cnf(c_613,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1914,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(sK2)
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_613])).

cnf(c_1915,plain,
    ( sK2 != X0
    | v2_funct_1(X0) != iProver_top
    | v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1914])).

cnf(c_1917,plain,
    ( sK2 != k1_xboole_0
    | v2_funct_1(sK2) = iProver_top
    | v2_funct_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1915])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1581,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1582,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1581])).

cnf(c_1584,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1582])).

cnf(c_1510,plain,
    ( X0 != X1
    | X0 = k6_partfun1(X2)
    | k6_partfun1(X2) != X1 ),
    inference(instantiation,[status(thm)],[c_607])).

cnf(c_1511,plain,
    ( k6_partfun1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k6_partfun1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1510])).

cnf(c_606,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1388,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_606])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1348,plain,
    ( ~ v1_xboole_0(sK2)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1352,plain,
    ( k1_xboole_0 = sK2
    | v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1348])).

cnf(c_1230,plain,
    ( v2_funct_1(X0)
    | ~ v2_funct_1(k6_partfun1(X1))
    | X0 != k6_partfun1(X1) ),
    inference(instantiation,[status(thm)],[c_613])).

cnf(c_1231,plain,
    ( X0 != k6_partfun1(X1)
    | v2_funct_1(X0) = iProver_top
    | v2_funct_1(k6_partfun1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1230])).

cnf(c_1233,plain,
    ( k1_xboole_0 != k6_partfun1(k1_xboole_0)
    | v2_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top
    | v2_funct_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1231])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_89,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_85,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_4,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_84,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_6,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_80,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_82,plain,
    ( v2_funct_1(k6_partfun1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_80])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3279,c_2312,c_2124,c_2108,c_1917,c_1584,c_1511,c_1388,c_1352,c_1233,c_89,c_85,c_84,c_6,c_82])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:05:32 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 2.89/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.89/0.98  
% 2.89/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.89/0.98  
% 2.89/0.98  ------  iProver source info
% 2.89/0.98  
% 2.89/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.89/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.89/0.98  git: non_committed_changes: false
% 2.89/0.98  git: last_make_outside_of_git: false
% 2.89/0.98  
% 2.89/0.98  ------ 
% 2.89/0.98  
% 2.89/0.98  ------ Input Options
% 2.89/0.98  
% 2.89/0.98  --out_options                           all
% 2.89/0.98  --tptp_safe_out                         true
% 2.89/0.98  --problem_path                          ""
% 2.89/0.98  --include_path                          ""
% 2.89/0.98  --clausifier                            res/vclausify_rel
% 2.89/0.98  --clausifier_options                    --mode clausify
% 2.89/0.98  --stdin                                 false
% 2.89/0.98  --stats_out                             all
% 2.89/0.98  
% 2.89/0.98  ------ General Options
% 2.89/0.98  
% 2.89/0.98  --fof                                   false
% 2.89/0.98  --time_out_real                         305.
% 2.89/0.98  --time_out_virtual                      -1.
% 2.89/0.98  --symbol_type_check                     false
% 2.89/0.98  --clausify_out                          false
% 2.89/0.98  --sig_cnt_out                           false
% 2.89/0.98  --trig_cnt_out                          false
% 2.89/0.98  --trig_cnt_out_tolerance                1.
% 2.89/0.98  --trig_cnt_out_sk_spl                   false
% 2.89/0.98  --abstr_cl_out                          false
% 2.89/0.98  
% 2.89/0.98  ------ Global Options
% 2.89/0.98  
% 2.89/0.98  --schedule                              default
% 2.89/0.98  --add_important_lit                     false
% 2.89/0.98  --prop_solver_per_cl                    1000
% 2.89/0.98  --min_unsat_core                        false
% 2.89/0.98  --soft_assumptions                      false
% 2.89/0.98  --soft_lemma_size                       3
% 2.89/0.98  --prop_impl_unit_size                   0
% 2.89/0.98  --prop_impl_unit                        []
% 2.89/0.98  --share_sel_clauses                     true
% 2.89/0.98  --reset_solvers                         false
% 2.89/0.98  --bc_imp_inh                            [conj_cone]
% 2.89/0.98  --conj_cone_tolerance                   3.
% 2.89/0.98  --extra_neg_conj                        none
% 2.89/0.98  --large_theory_mode                     true
% 2.89/0.98  --prolific_symb_bound                   200
% 2.89/0.98  --lt_threshold                          2000
% 2.89/0.98  --clause_weak_htbl                      true
% 2.89/0.98  --gc_record_bc_elim                     false
% 2.89/0.98  
% 2.89/0.98  ------ Preprocessing Options
% 2.89/0.98  
% 2.89/0.98  --preprocessing_flag                    true
% 2.89/0.98  --time_out_prep_mult                    0.1
% 2.89/0.98  --splitting_mode                        input
% 2.89/0.98  --splitting_grd                         true
% 2.89/0.98  --splitting_cvd                         false
% 2.89/0.98  --splitting_cvd_svl                     false
% 2.89/0.98  --splitting_nvd                         32
% 2.89/0.98  --sub_typing                            true
% 2.89/0.98  --prep_gs_sim                           true
% 2.89/0.98  --prep_unflatten                        true
% 2.89/0.98  --prep_res_sim                          true
% 2.89/0.98  --prep_upred                            true
% 2.89/0.98  --prep_sem_filter                       exhaustive
% 2.89/0.98  --prep_sem_filter_out                   false
% 2.89/0.98  --pred_elim                             true
% 2.89/0.98  --res_sim_input                         true
% 2.89/0.98  --eq_ax_congr_red                       true
% 2.89/0.98  --pure_diseq_elim                       true
% 2.89/0.98  --brand_transform                       false
% 2.89/0.98  --non_eq_to_eq                          false
% 2.89/0.98  --prep_def_merge                        true
% 2.89/0.98  --prep_def_merge_prop_impl              false
% 2.89/0.98  --prep_def_merge_mbd                    true
% 2.89/0.98  --prep_def_merge_tr_red                 false
% 2.89/0.98  --prep_def_merge_tr_cl                  false
% 2.89/0.98  --smt_preprocessing                     true
% 2.89/0.98  --smt_ac_axioms                         fast
% 2.89/0.98  --preprocessed_out                      false
% 2.89/0.98  --preprocessed_stats                    false
% 2.89/0.98  
% 2.89/0.98  ------ Abstraction refinement Options
% 2.89/0.98  
% 2.89/0.98  --abstr_ref                             []
% 2.89/0.98  --abstr_ref_prep                        false
% 2.89/0.98  --abstr_ref_until_sat                   false
% 2.89/0.98  --abstr_ref_sig_restrict                funpre
% 2.89/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.89/0.98  --abstr_ref_under                       []
% 2.89/0.98  
% 2.89/0.98  ------ SAT Options
% 2.89/0.98  
% 2.89/0.98  --sat_mode                              false
% 2.89/0.98  --sat_fm_restart_options                ""
% 2.89/0.98  --sat_gr_def                            false
% 2.89/0.98  --sat_epr_types                         true
% 2.89/0.98  --sat_non_cyclic_types                  false
% 2.89/0.98  --sat_finite_models                     false
% 2.89/0.98  --sat_fm_lemmas                         false
% 2.89/0.98  --sat_fm_prep                           false
% 2.89/0.98  --sat_fm_uc_incr                        true
% 2.89/0.98  --sat_out_model                         small
% 2.89/0.98  --sat_out_clauses                       false
% 2.89/0.98  
% 2.89/0.98  ------ QBF Options
% 2.89/0.98  
% 2.89/0.98  --qbf_mode                              false
% 2.89/0.98  --qbf_elim_univ                         false
% 2.89/0.98  --qbf_dom_inst                          none
% 2.89/0.98  --qbf_dom_pre_inst                      false
% 2.89/0.98  --qbf_sk_in                             false
% 2.89/0.98  --qbf_pred_elim                         true
% 2.89/0.98  --qbf_split                             512
% 2.89/0.98  
% 2.89/0.98  ------ BMC1 Options
% 2.89/0.98  
% 2.89/0.98  --bmc1_incremental                      false
% 2.89/0.98  --bmc1_axioms                           reachable_all
% 2.89/0.98  --bmc1_min_bound                        0
% 2.89/0.98  --bmc1_max_bound                        -1
% 2.89/0.98  --bmc1_max_bound_default                -1
% 2.89/0.98  --bmc1_symbol_reachability              true
% 2.89/0.98  --bmc1_property_lemmas                  false
% 2.89/0.98  --bmc1_k_induction                      false
% 2.89/0.98  --bmc1_non_equiv_states                 false
% 2.89/0.98  --bmc1_deadlock                         false
% 2.89/0.98  --bmc1_ucm                              false
% 2.89/0.98  --bmc1_add_unsat_core                   none
% 2.89/0.98  --bmc1_unsat_core_children              false
% 2.89/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.89/0.98  --bmc1_out_stat                         full
% 2.89/0.98  --bmc1_ground_init                      false
% 2.89/0.98  --bmc1_pre_inst_next_state              false
% 2.89/0.98  --bmc1_pre_inst_state                   false
% 2.89/0.98  --bmc1_pre_inst_reach_state             false
% 2.89/0.98  --bmc1_out_unsat_core                   false
% 2.89/0.98  --bmc1_aig_witness_out                  false
% 2.89/0.98  --bmc1_verbose                          false
% 2.89/0.98  --bmc1_dump_clauses_tptp                false
% 2.89/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.89/0.98  --bmc1_dump_file                        -
% 2.89/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.89/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.89/0.98  --bmc1_ucm_extend_mode                  1
% 2.89/0.98  --bmc1_ucm_init_mode                    2
% 2.89/0.98  --bmc1_ucm_cone_mode                    none
% 2.89/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.89/0.98  --bmc1_ucm_relax_model                  4
% 2.89/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.89/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.89/0.98  --bmc1_ucm_layered_model                none
% 2.89/0.98  --bmc1_ucm_max_lemma_size               10
% 2.89/0.98  
% 2.89/0.98  ------ AIG Options
% 2.89/0.98  
% 2.89/0.98  --aig_mode                              false
% 2.89/0.98  
% 2.89/0.98  ------ Instantiation Options
% 2.89/0.98  
% 2.89/0.98  --instantiation_flag                    true
% 2.89/0.98  --inst_sos_flag                         false
% 2.89/0.98  --inst_sos_phase                        true
% 2.89/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.89/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.89/0.98  --inst_lit_sel_side                     num_symb
% 2.89/0.98  --inst_solver_per_active                1400
% 2.89/0.98  --inst_solver_calls_frac                1.
% 2.89/0.98  --inst_passive_queue_type               priority_queues
% 2.89/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.89/0.98  --inst_passive_queues_freq              [25;2]
% 2.89/0.98  --inst_dismatching                      true
% 2.89/0.98  --inst_eager_unprocessed_to_passive     true
% 2.89/0.98  --inst_prop_sim_given                   true
% 2.89/0.98  --inst_prop_sim_new                     false
% 2.89/0.98  --inst_subs_new                         false
% 2.89/0.98  --inst_eq_res_simp                      false
% 2.89/0.98  --inst_subs_given                       false
% 2.89/0.98  --inst_orphan_elimination               true
% 2.89/0.98  --inst_learning_loop_flag               true
% 2.89/0.98  --inst_learning_start                   3000
% 2.89/0.98  --inst_learning_factor                  2
% 2.89/0.98  --inst_start_prop_sim_after_learn       3
% 2.89/0.98  --inst_sel_renew                        solver
% 2.89/0.98  --inst_lit_activity_flag                true
% 2.89/0.98  --inst_restr_to_given                   false
% 2.89/0.98  --inst_activity_threshold               500
% 2.89/0.98  --inst_out_proof                        true
% 2.89/0.98  
% 2.89/0.98  ------ Resolution Options
% 2.89/0.98  
% 2.89/0.98  --resolution_flag                       true
% 2.89/0.98  --res_lit_sel                           adaptive
% 2.89/0.98  --res_lit_sel_side                      none
% 2.89/0.98  --res_ordering                          kbo
% 2.89/0.98  --res_to_prop_solver                    active
% 2.89/0.98  --res_prop_simpl_new                    false
% 2.89/0.98  --res_prop_simpl_given                  true
% 2.89/0.98  --res_passive_queue_type                priority_queues
% 2.89/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.89/0.98  --res_passive_queues_freq               [15;5]
% 2.89/0.98  --res_forward_subs                      full
% 2.89/0.98  --res_backward_subs                     full
% 2.89/0.98  --res_forward_subs_resolution           true
% 2.89/0.98  --res_backward_subs_resolution          true
% 2.89/0.98  --res_orphan_elimination                true
% 2.89/0.98  --res_time_limit                        2.
% 2.89/0.98  --res_out_proof                         true
% 2.89/0.98  
% 2.89/0.98  ------ Superposition Options
% 2.89/0.98  
% 2.89/0.98  --superposition_flag                    true
% 2.89/0.98  --sup_passive_queue_type                priority_queues
% 2.89/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.89/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.89/0.98  --demod_completeness_check              fast
% 2.89/0.98  --demod_use_ground                      true
% 2.89/0.98  --sup_to_prop_solver                    passive
% 2.89/0.98  --sup_prop_simpl_new                    true
% 2.89/0.98  --sup_prop_simpl_given                  true
% 2.89/0.98  --sup_fun_splitting                     false
% 2.89/0.98  --sup_smt_interval                      50000
% 2.89/0.98  
% 2.89/0.98  ------ Superposition Simplification Setup
% 2.89/0.98  
% 2.89/0.98  --sup_indices_passive                   []
% 2.89/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.89/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.89/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.89/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.89/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.89/0.98  --sup_full_bw                           [BwDemod]
% 2.89/0.98  --sup_immed_triv                        [TrivRules]
% 2.89/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.89/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.89/0.98  --sup_immed_bw_main                     []
% 2.89/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.89/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.89/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.89/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.89/0.98  
% 2.89/0.98  ------ Combination Options
% 2.89/0.98  
% 2.89/0.98  --comb_res_mult                         3
% 2.89/0.98  --comb_sup_mult                         2
% 2.89/0.98  --comb_inst_mult                        10
% 2.89/0.98  
% 2.89/0.98  ------ Debug Options
% 2.89/0.98  
% 2.89/0.98  --dbg_backtrace                         false
% 2.89/0.98  --dbg_dump_prop_clauses                 false
% 2.89/0.98  --dbg_dump_prop_clauses_file            -
% 2.89/0.98  --dbg_out_stat                          false
% 2.89/0.98  ------ Parsing...
% 2.89/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.89/0.98  
% 2.89/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 2.89/0.98  
% 2.89/0.98  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.89/0.98  
% 2.89/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.89/0.98  ------ Proving...
% 2.89/0.98  ------ Problem Properties 
% 2.89/0.98  
% 2.89/0.98  
% 2.89/0.98  clauses                                 25
% 2.89/0.98  conjectures                             6
% 2.89/0.98  EPR                                     6
% 2.89/0.98  Horn                                    23
% 2.89/0.98  unary                                   12
% 2.89/0.98  binary                                  4
% 2.89/0.98  lits                                    72
% 2.89/0.98  lits eq                                 15
% 2.89/0.98  fd_pure                                 0
% 2.89/0.98  fd_pseudo                               0
% 2.89/0.98  fd_cond                                 3
% 2.89/0.98  fd_pseudo_cond                          0
% 2.89/0.98  AC symbols                              0
% 2.89/0.98  
% 2.89/0.98  ------ Schedule dynamic 5 is on 
% 2.89/0.98  
% 2.89/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.89/0.98  
% 2.89/0.98  
% 2.89/0.98  ------ 
% 2.89/0.98  Current options:
% 2.89/0.98  ------ 
% 2.89/0.98  
% 2.89/0.98  ------ Input Options
% 2.89/0.98  
% 2.89/0.98  --out_options                           all
% 2.89/0.98  --tptp_safe_out                         true
% 2.89/0.98  --problem_path                          ""
% 2.89/0.98  --include_path                          ""
% 2.89/0.98  --clausifier                            res/vclausify_rel
% 2.89/0.98  --clausifier_options                    --mode clausify
% 2.89/0.98  --stdin                                 false
% 2.89/0.98  --stats_out                             all
% 2.89/0.98  
% 2.89/0.98  ------ General Options
% 2.89/0.98  
% 2.89/0.98  --fof                                   false
% 2.89/0.98  --time_out_real                         305.
% 2.89/0.98  --time_out_virtual                      -1.
% 2.89/0.98  --symbol_type_check                     false
% 2.89/0.98  --clausify_out                          false
% 2.89/0.98  --sig_cnt_out                           false
% 2.89/0.98  --trig_cnt_out                          false
% 2.89/0.98  --trig_cnt_out_tolerance                1.
% 2.89/0.98  --trig_cnt_out_sk_spl                   false
% 2.89/0.98  --abstr_cl_out                          false
% 2.89/0.98  
% 2.89/0.98  ------ Global Options
% 2.89/0.98  
% 2.89/0.98  --schedule                              default
% 2.89/0.98  --add_important_lit                     false
% 2.89/0.98  --prop_solver_per_cl                    1000
% 2.89/0.98  --min_unsat_core                        false
% 2.89/0.98  --soft_assumptions                      false
% 2.89/0.98  --soft_lemma_size                       3
% 2.89/0.98  --prop_impl_unit_size                   0
% 2.89/0.98  --prop_impl_unit                        []
% 2.89/0.98  --share_sel_clauses                     true
% 2.89/0.98  --reset_solvers                         false
% 2.89/0.98  --bc_imp_inh                            [conj_cone]
% 2.89/0.98  --conj_cone_tolerance                   3.
% 2.89/0.98  --extra_neg_conj                        none
% 2.89/0.98  --large_theory_mode                     true
% 2.89/0.98  --prolific_symb_bound                   200
% 2.89/0.98  --lt_threshold                          2000
% 2.89/0.98  --clause_weak_htbl                      true
% 2.89/0.98  --gc_record_bc_elim                     false
% 2.89/0.98  
% 2.89/0.98  ------ Preprocessing Options
% 2.89/0.98  
% 2.89/0.98  --preprocessing_flag                    true
% 2.89/0.98  --time_out_prep_mult                    0.1
% 2.89/0.98  --splitting_mode                        input
% 2.89/0.98  --splitting_grd                         true
% 2.89/0.98  --splitting_cvd                         false
% 2.89/0.98  --splitting_cvd_svl                     false
% 2.89/0.98  --splitting_nvd                         32
% 2.89/0.98  --sub_typing                            true
% 2.89/0.98  --prep_gs_sim                           true
% 2.89/0.98  --prep_unflatten                        true
% 2.89/0.98  --prep_res_sim                          true
% 2.89/0.98  --prep_upred                            true
% 2.89/0.98  --prep_sem_filter                       exhaustive
% 2.89/0.98  --prep_sem_filter_out                   false
% 2.89/0.98  --pred_elim                             true
% 2.89/0.98  --res_sim_input                         true
% 2.89/0.98  --eq_ax_congr_red                       true
% 2.89/0.98  --pure_diseq_elim                       true
% 2.89/0.98  --brand_transform                       false
% 2.89/0.98  --non_eq_to_eq                          false
% 2.89/0.98  --prep_def_merge                        true
% 2.89/0.98  --prep_def_merge_prop_impl              false
% 2.89/0.98  --prep_def_merge_mbd                    true
% 2.89/0.98  --prep_def_merge_tr_red                 false
% 2.89/0.98  --prep_def_merge_tr_cl                  false
% 2.89/0.98  --smt_preprocessing                     true
% 2.89/0.98  --smt_ac_axioms                         fast
% 2.89/0.98  --preprocessed_out                      false
% 2.89/0.98  --preprocessed_stats                    false
% 2.89/0.98  
% 2.89/0.98  ------ Abstraction refinement Options
% 2.89/0.98  
% 2.89/0.98  --abstr_ref                             []
% 2.89/0.98  --abstr_ref_prep                        false
% 2.89/0.98  --abstr_ref_until_sat                   false
% 2.89/0.98  --abstr_ref_sig_restrict                funpre
% 2.89/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.89/0.98  --abstr_ref_under                       []
% 2.89/0.98  
% 2.89/0.98  ------ SAT Options
% 2.89/0.98  
% 2.89/0.98  --sat_mode                              false
% 2.89/0.98  --sat_fm_restart_options                ""
% 2.89/0.98  --sat_gr_def                            false
% 2.89/0.98  --sat_epr_types                         true
% 2.89/0.98  --sat_non_cyclic_types                  false
% 2.89/0.98  --sat_finite_models                     false
% 2.89/0.98  --sat_fm_lemmas                         false
% 2.89/0.98  --sat_fm_prep                           false
% 2.89/0.98  --sat_fm_uc_incr                        true
% 2.89/0.98  --sat_out_model                         small
% 2.89/0.98  --sat_out_clauses                       false
% 2.89/0.98  
% 2.89/0.98  ------ QBF Options
% 2.89/0.98  
% 2.89/0.98  --qbf_mode                              false
% 2.89/0.98  --qbf_elim_univ                         false
% 2.89/0.98  --qbf_dom_inst                          none
% 2.89/0.98  --qbf_dom_pre_inst                      false
% 2.89/0.98  --qbf_sk_in                             false
% 2.89/0.98  --qbf_pred_elim                         true
% 2.89/0.98  --qbf_split                             512
% 2.89/0.98  
% 2.89/0.98  ------ BMC1 Options
% 2.89/0.98  
% 2.89/0.98  --bmc1_incremental                      false
% 2.89/0.98  --bmc1_axioms                           reachable_all
% 2.89/0.98  --bmc1_min_bound                        0
% 2.89/0.98  --bmc1_max_bound                        -1
% 2.89/0.98  --bmc1_max_bound_default                -1
% 2.89/0.99  --bmc1_symbol_reachability              true
% 2.89/0.99  --bmc1_property_lemmas                  false
% 2.89/0.99  --bmc1_k_induction                      false
% 2.89/0.99  --bmc1_non_equiv_states                 false
% 2.89/0.99  --bmc1_deadlock                         false
% 2.89/0.99  --bmc1_ucm                              false
% 2.89/0.99  --bmc1_add_unsat_core                   none
% 2.89/0.99  --bmc1_unsat_core_children              false
% 2.89/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.89/0.99  --bmc1_out_stat                         full
% 2.89/0.99  --bmc1_ground_init                      false
% 2.89/0.99  --bmc1_pre_inst_next_state              false
% 2.89/0.99  --bmc1_pre_inst_state                   false
% 2.89/0.99  --bmc1_pre_inst_reach_state             false
% 2.89/0.99  --bmc1_out_unsat_core                   false
% 2.89/0.99  --bmc1_aig_witness_out                  false
% 2.89/0.99  --bmc1_verbose                          false
% 2.89/0.99  --bmc1_dump_clauses_tptp                false
% 2.89/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.89/0.99  --bmc1_dump_file                        -
% 2.89/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.89/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.89/0.99  --bmc1_ucm_extend_mode                  1
% 2.89/0.99  --bmc1_ucm_init_mode                    2
% 2.89/0.99  --bmc1_ucm_cone_mode                    none
% 2.89/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.89/0.99  --bmc1_ucm_relax_model                  4
% 2.89/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.89/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.89/0.99  --bmc1_ucm_layered_model                none
% 2.89/0.99  --bmc1_ucm_max_lemma_size               10
% 2.89/0.99  
% 2.89/0.99  ------ AIG Options
% 2.89/0.99  
% 2.89/0.99  --aig_mode                              false
% 2.89/0.99  
% 2.89/0.99  ------ Instantiation Options
% 2.89/0.99  
% 2.89/0.99  --instantiation_flag                    true
% 2.89/0.99  --inst_sos_flag                         false
% 2.89/0.99  --inst_sos_phase                        true
% 2.89/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.89/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.89/0.99  --inst_lit_sel_side                     none
% 2.89/0.99  --inst_solver_per_active                1400
% 2.89/0.99  --inst_solver_calls_frac                1.
% 2.89/0.99  --inst_passive_queue_type               priority_queues
% 2.89/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.89/0.99  --inst_passive_queues_freq              [25;2]
% 2.89/0.99  --inst_dismatching                      true
% 2.89/0.99  --inst_eager_unprocessed_to_passive     true
% 2.89/0.99  --inst_prop_sim_given                   true
% 2.89/0.99  --inst_prop_sim_new                     false
% 2.89/0.99  --inst_subs_new                         false
% 2.89/0.99  --inst_eq_res_simp                      false
% 2.89/0.99  --inst_subs_given                       false
% 2.89/0.99  --inst_orphan_elimination               true
% 2.89/0.99  --inst_learning_loop_flag               true
% 2.89/0.99  --inst_learning_start                   3000
% 2.89/0.99  --inst_learning_factor                  2
% 2.89/0.99  --inst_start_prop_sim_after_learn       3
% 2.89/0.99  --inst_sel_renew                        solver
% 2.89/0.99  --inst_lit_activity_flag                true
% 2.89/0.99  --inst_restr_to_given                   false
% 2.89/0.99  --inst_activity_threshold               500
% 2.89/0.99  --inst_out_proof                        true
% 2.89/0.99  
% 2.89/0.99  ------ Resolution Options
% 2.89/0.99  
% 2.89/0.99  --resolution_flag                       false
% 2.89/0.99  --res_lit_sel                           adaptive
% 2.89/0.99  --res_lit_sel_side                      none
% 2.89/0.99  --res_ordering                          kbo
% 2.89/0.99  --res_to_prop_solver                    active
% 2.89/0.99  --res_prop_simpl_new                    false
% 2.89/0.99  --res_prop_simpl_given                  true
% 2.89/0.99  --res_passive_queue_type                priority_queues
% 2.89/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.89/0.99  --res_passive_queues_freq               [15;5]
% 2.89/0.99  --res_forward_subs                      full
% 2.89/0.99  --res_backward_subs                     full
% 2.89/0.99  --res_forward_subs_resolution           true
% 2.89/0.99  --res_backward_subs_resolution          true
% 2.89/0.99  --res_orphan_elimination                true
% 2.89/0.99  --res_time_limit                        2.
% 2.89/0.99  --res_out_proof                         true
% 2.89/0.99  
% 2.89/0.99  ------ Superposition Options
% 2.89/0.99  
% 2.89/0.99  --superposition_flag                    true
% 2.89/0.99  --sup_passive_queue_type                priority_queues
% 2.89/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.89/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.89/0.99  --demod_completeness_check              fast
% 2.89/0.99  --demod_use_ground                      true
% 2.89/0.99  --sup_to_prop_solver                    passive
% 2.89/0.99  --sup_prop_simpl_new                    true
% 2.89/0.99  --sup_prop_simpl_given                  true
% 2.89/0.99  --sup_fun_splitting                     false
% 2.89/0.99  --sup_smt_interval                      50000
% 2.89/0.99  
% 2.89/0.99  ------ Superposition Simplification Setup
% 2.89/0.99  
% 2.89/0.99  --sup_indices_passive                   []
% 2.89/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.89/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.89/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.89/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.89/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.89/0.99  --sup_full_bw                           [BwDemod]
% 2.89/0.99  --sup_immed_triv                        [TrivRules]
% 2.89/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.89/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.89/0.99  --sup_immed_bw_main                     []
% 2.89/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.89/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.89/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.89/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.89/0.99  
% 2.89/0.99  ------ Combination Options
% 2.89/0.99  
% 2.89/0.99  --comb_res_mult                         3
% 2.89/0.99  --comb_sup_mult                         2
% 2.89/0.99  --comb_inst_mult                        10
% 2.89/0.99  
% 2.89/0.99  ------ Debug Options
% 2.89/0.99  
% 2.89/0.99  --dbg_backtrace                         false
% 2.89/0.99  --dbg_dump_prop_clauses                 false
% 2.89/0.99  --dbg_dump_prop_clauses_file            -
% 2.89/0.99  --dbg_out_stat                          false
% 2.89/0.99  
% 2.89/0.99  
% 2.89/0.99  
% 2.89/0.99  
% 2.89/0.99  ------ Proving...
% 2.89/0.99  
% 2.89/0.99  
% 2.89/0.99  % SZS status Theorem for theBenchmark.p
% 2.89/0.99  
% 2.89/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.89/0.99  
% 2.89/0.99  fof(f13,axiom,(
% 2.89/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 2.89/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/0.99  
% 2.89/0.99  fof(f29,plain,(
% 2.89/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.89/0.99    inference(ennf_transformation,[],[f13])).
% 2.89/0.99  
% 2.89/0.99  fof(f30,plain,(
% 2.89/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.89/0.99    inference(flattening,[],[f29])).
% 2.89/0.99  
% 2.89/0.99  fof(f62,plain,(
% 2.89/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.89/0.99    inference(cnf_transformation,[],[f30])).
% 2.89/0.99  
% 2.89/0.99  fof(f10,axiom,(
% 2.89/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.89/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/0.99  
% 2.89/0.99  fof(f25,plain,(
% 2.89/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.89/0.99    inference(ennf_transformation,[],[f10])).
% 2.89/0.99  
% 2.89/0.99  fof(f26,plain,(
% 2.89/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.89/0.99    inference(flattening,[],[f25])).
% 2.89/0.99  
% 2.89/0.99  fof(f39,plain,(
% 2.89/0.99    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.89/0.99    inference(nnf_transformation,[],[f26])).
% 2.89/0.99  
% 2.89/0.99  fof(f56,plain,(
% 2.89/0.99    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.89/0.99    inference(cnf_transformation,[],[f39])).
% 2.89/0.99  
% 2.89/0.99  fof(f17,conjecture,(
% 2.89/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 2.89/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/0.99  
% 2.89/0.99  fof(f18,negated_conjecture,(
% 2.89/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 2.89/0.99    inference(negated_conjecture,[],[f17])).
% 2.89/0.99  
% 2.89/0.99  fof(f35,plain,(
% 2.89/0.99    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.89/0.99    inference(ennf_transformation,[],[f18])).
% 2.89/0.99  
% 2.89/0.99  fof(f36,plain,(
% 2.89/0.99    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.89/0.99    inference(flattening,[],[f35])).
% 2.89/0.99  
% 2.89/0.99  fof(f42,plain,(
% 2.89/0.99    ( ! [X2,X0,X1] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((~v2_funct_2(sK3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 2.89/0.99    introduced(choice_axiom,[])).
% 2.89/0.99  
% 2.89/0.99  fof(f41,plain,(
% 2.89/0.99    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 2.89/0.99    introduced(choice_axiom,[])).
% 2.89/0.99  
% 2.89/0.99  fof(f43,plain,(
% 2.89/0.99    ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 2.89/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f36,f42,f41])).
% 2.89/0.99  
% 2.89/0.99  fof(f73,plain,(
% 2.89/0.99    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.89/0.99    inference(cnf_transformation,[],[f43])).
% 2.89/0.99  
% 2.89/0.99  fof(f11,axiom,(
% 2.89/0.99    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 2.89/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/0.99  
% 2.89/0.99  fof(f58,plain,(
% 2.89/0.99    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.89/0.99    inference(cnf_transformation,[],[f11])).
% 2.89/0.99  
% 2.89/0.99  fof(f14,axiom,(
% 2.89/0.99    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.89/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/0.99  
% 2.89/0.99  fof(f63,plain,(
% 2.89/0.99    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.89/0.99    inference(cnf_transformation,[],[f14])).
% 2.89/0.99  
% 2.89/0.99  fof(f78,plain,(
% 2.89/0.99    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.89/0.99    inference(definition_unfolding,[],[f58,f63])).
% 2.89/0.99  
% 2.89/0.99  fof(f67,plain,(
% 2.89/0.99    v1_funct_1(sK2)),
% 2.89/0.99    inference(cnf_transformation,[],[f43])).
% 2.89/0.99  
% 2.89/0.99  fof(f69,plain,(
% 2.89/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.89/0.99    inference(cnf_transformation,[],[f43])).
% 2.89/0.99  
% 2.89/0.99  fof(f70,plain,(
% 2.89/0.99    v1_funct_1(sK3)),
% 2.89/0.99    inference(cnf_transformation,[],[f43])).
% 2.89/0.99  
% 2.89/0.99  fof(f72,plain,(
% 2.89/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.89/0.99    inference(cnf_transformation,[],[f43])).
% 2.89/0.99  
% 2.89/0.99  fof(f16,axiom,(
% 2.89/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 2.89/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/0.99  
% 2.89/0.99  fof(f33,plain,(
% 2.89/0.99    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.89/0.99    inference(ennf_transformation,[],[f16])).
% 2.89/0.99  
% 2.89/0.99  fof(f34,plain,(
% 2.89/0.99    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.89/0.99    inference(flattening,[],[f33])).
% 2.89/0.99  
% 2.89/0.99  fof(f65,plain,(
% 2.89/0.99    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X3) | k1_xboole_0 = X2 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.89/0.99    inference(cnf_transformation,[],[f34])).
% 2.89/0.99  
% 2.89/0.99  fof(f68,plain,(
% 2.89/0.99    v1_funct_2(sK2,sK0,sK1)),
% 2.89/0.99    inference(cnf_transformation,[],[f43])).
% 2.89/0.99  
% 2.89/0.99  fof(f71,plain,(
% 2.89/0.99    v1_funct_2(sK3,sK1,sK0)),
% 2.89/0.99    inference(cnf_transformation,[],[f43])).
% 2.89/0.99  
% 2.89/0.99  fof(f9,axiom,(
% 2.89/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 2.89/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/0.99  
% 2.89/0.99  fof(f24,plain,(
% 2.89/0.99    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.89/0.99    inference(ennf_transformation,[],[f9])).
% 2.89/0.99  
% 2.89/0.99  fof(f55,plain,(
% 2.89/0.99    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.89/0.99    inference(cnf_transformation,[],[f24])).
% 2.89/0.99  
% 2.89/0.99  fof(f15,axiom,(
% 2.89/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 2.89/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/0.99  
% 2.89/0.99  fof(f31,plain,(
% 2.89/0.99    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.89/0.99    inference(ennf_transformation,[],[f15])).
% 2.89/0.99  
% 2.89/0.99  fof(f32,plain,(
% 2.89/0.99    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.89/0.99    inference(flattening,[],[f31])).
% 2.89/0.99  
% 2.89/0.99  fof(f64,plain,(
% 2.89/0.99    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.89/0.99    inference(cnf_transformation,[],[f32])).
% 2.89/0.99  
% 2.89/0.99  fof(f8,axiom,(
% 2.89/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.89/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/0.99  
% 2.89/0.99  fof(f19,plain,(
% 2.89/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 2.89/0.99    inference(pure_predicate_removal,[],[f8])).
% 2.89/0.99  
% 2.89/0.99  fof(f23,plain,(
% 2.89/0.99    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.89/0.99    inference(ennf_transformation,[],[f19])).
% 2.89/0.99  
% 2.89/0.99  fof(f54,plain,(
% 2.89/0.99    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.89/0.99    inference(cnf_transformation,[],[f23])).
% 2.89/0.99  
% 2.89/0.99  fof(f12,axiom,(
% 2.89/0.99    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 2.89/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/0.99  
% 2.89/0.99  fof(f27,plain,(
% 2.89/0.99    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.89/0.99    inference(ennf_transformation,[],[f12])).
% 2.89/0.99  
% 2.89/0.99  fof(f28,plain,(
% 2.89/0.99    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.89/0.99    inference(flattening,[],[f27])).
% 2.89/0.99  
% 2.89/0.99  fof(f40,plain,(
% 2.89/0.99    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.89/0.99    inference(nnf_transformation,[],[f28])).
% 2.89/0.99  
% 2.89/0.99  fof(f60,plain,(
% 2.89/0.99    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.89/0.99    inference(cnf_transformation,[],[f40])).
% 2.89/0.99  
% 2.89/0.99  fof(f82,plain,(
% 2.89/0.99    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.89/0.99    inference(equality_resolution,[],[f60])).
% 2.89/0.99  
% 2.89/0.99  fof(f7,axiom,(
% 2.89/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.89/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/0.99  
% 2.89/0.99  fof(f22,plain,(
% 2.89/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.89/0.99    inference(ennf_transformation,[],[f7])).
% 2.89/0.99  
% 2.89/0.99  fof(f53,plain,(
% 2.89/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.89/0.99    inference(cnf_transformation,[],[f22])).
% 2.89/0.99  
% 2.89/0.99  fof(f74,plain,(
% 2.89/0.99    ~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)),
% 2.89/0.99    inference(cnf_transformation,[],[f43])).
% 2.89/0.99  
% 2.89/0.99  fof(f6,axiom,(
% 2.89/0.99    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.89/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/0.99  
% 2.89/0.99  fof(f52,plain,(
% 2.89/0.99    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 2.89/0.99    inference(cnf_transformation,[],[f6])).
% 2.89/0.99  
% 2.89/0.99  fof(f76,plain,(
% 2.89/0.99    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 2.89/0.99    inference(definition_unfolding,[],[f52,f63])).
% 2.89/0.99  
% 2.89/0.99  fof(f3,axiom,(
% 2.89/0.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.89/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/0.99  
% 2.89/0.99  fof(f37,plain,(
% 2.89/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.89/0.99    inference(nnf_transformation,[],[f3])).
% 2.89/0.99  
% 2.89/0.99  fof(f38,plain,(
% 2.89/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.89/0.99    inference(flattening,[],[f37])).
% 2.89/0.99  
% 2.89/0.99  fof(f47,plain,(
% 2.89/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 2.89/0.99    inference(cnf_transformation,[],[f38])).
% 2.89/0.99  
% 2.89/0.99  fof(f80,plain,(
% 2.89/0.99    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.89/0.99    inference(equality_resolution,[],[f47])).
% 2.89/0.99  
% 2.89/0.99  fof(f4,axiom,(
% 2.89/0.99    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 2.89/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/0.99  
% 2.89/0.99  fof(f21,plain,(
% 2.89/0.99    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 2.89/0.99    inference(ennf_transformation,[],[f4])).
% 2.89/0.99  
% 2.89/0.99  fof(f49,plain,(
% 2.89/0.99    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 2.89/0.99    inference(cnf_transformation,[],[f21])).
% 2.89/0.99  
% 2.89/0.99  fof(f2,axiom,(
% 2.89/0.99    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.89/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/0.99  
% 2.89/0.99  fof(f20,plain,(
% 2.89/0.99    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.89/0.99    inference(ennf_transformation,[],[f2])).
% 2.89/0.99  
% 2.89/0.99  fof(f45,plain,(
% 2.89/0.99    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 2.89/0.99    inference(cnf_transformation,[],[f20])).
% 2.89/0.99  
% 2.89/0.99  fof(f1,axiom,(
% 2.89/0.99    v1_xboole_0(k1_xboole_0)),
% 2.89/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/0.99  
% 2.89/0.99  fof(f44,plain,(
% 2.89/0.99    v1_xboole_0(k1_xboole_0)),
% 2.89/0.99    inference(cnf_transformation,[],[f1])).
% 2.89/0.99  
% 2.89/0.99  fof(f46,plain,(
% 2.89/0.99    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 2.89/0.99    inference(cnf_transformation,[],[f38])).
% 2.89/0.99  
% 2.89/0.99  fof(f5,axiom,(
% 2.89/0.99    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 2.89/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/0.99  
% 2.89/0.99  fof(f50,plain,(
% 2.89/0.99    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 2.89/0.99    inference(cnf_transformation,[],[f5])).
% 2.89/0.99  
% 2.89/0.99  fof(f75,plain,(
% 2.89/0.99    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 2.89/0.99    inference(definition_unfolding,[],[f50,f63])).
% 2.89/0.99  
% 2.89/0.99  cnf(c_17,plain,
% 2.89/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.89/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 2.89/0.99      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 2.89/0.99      | ~ v1_funct_1(X0)
% 2.89/0.99      | ~ v1_funct_1(X3) ),
% 2.89/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1015,plain,
% 2.89/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.89/0.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 2.89/0.99      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
% 2.89/0.99      | v1_funct_1(X0) != iProver_top
% 2.89/0.99      | v1_funct_1(X3) != iProver_top ),
% 2.89/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_13,plain,
% 2.89/0.99      ( ~ r2_relset_1(X0,X1,X2,X3)
% 2.89/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.89/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.89/0.99      | X3 = X2 ),
% 2.89/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_23,negated_conjecture,
% 2.89/0.99      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 2.89/0.99      inference(cnf_transformation,[],[f73]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_395,plain,
% 2.89/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.89/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.89/0.99      | X3 = X0
% 2.89/0.99      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 2.89/0.99      | k6_partfun1(sK0) != X3
% 2.89/0.99      | sK0 != X2
% 2.89/0.99      | sK0 != X1 ),
% 2.89/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_23]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_396,plain,
% 2.89/0.99      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.89/0.99      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.89/0.99      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 2.89/0.99      inference(unflattening,[status(thm)],[c_395]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_14,plain,
% 2.89/0.99      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 2.89/0.99      inference(cnf_transformation,[],[f78]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_404,plain,
% 2.89/0.99      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.89/0.99      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 2.89/0.99      inference(forward_subsumption_resolution,
% 2.89/0.99                [status(thm)],
% 2.89/0.99                [c_396,c_14]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1002,plain,
% 2.89/0.99      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 2.89/0.99      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 2.89/0.99      inference(predicate_to_equality,[status(thm)],[c_404]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_2890,plain,
% 2.89/0.99      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
% 2.89/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 2.89/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.89/0.99      | v1_funct_1(sK2) != iProver_top
% 2.89/0.99      | v1_funct_1(sK3) != iProver_top ),
% 2.89/0.99      inference(superposition,[status(thm)],[c_1015,c_1002]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_29,negated_conjecture,
% 2.89/0.99      ( v1_funct_1(sK2) ),
% 2.89/0.99      inference(cnf_transformation,[],[f67]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_30,plain,
% 2.89/0.99      ( v1_funct_1(sK2) = iProver_top ),
% 2.89/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_27,negated_conjecture,
% 2.89/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.89/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_32,plain,
% 2.89/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.89/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_26,negated_conjecture,
% 2.89/0.99      ( v1_funct_1(sK3) ),
% 2.89/0.99      inference(cnf_transformation,[],[f70]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_33,plain,
% 2.89/0.99      ( v1_funct_1(sK3) = iProver_top ),
% 2.89/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_24,negated_conjecture,
% 2.89/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 2.89/0.99      inference(cnf_transformation,[],[f72]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_35,plain,
% 2.89/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 2.89/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_3089,plain,
% 2.89/0.99      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
% 2.89/0.99      inference(global_propositional_subsumption,
% 2.89/0.99                [status(thm)],
% 2.89/0.99                [c_2890,c_30,c_32,c_33,c_35]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_21,plain,
% 2.89/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.89/0.99      | ~ v1_funct_2(X3,X4,X1)
% 2.89/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
% 2.89/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.89/0.99      | ~ v1_funct_1(X0)
% 2.89/0.99      | ~ v1_funct_1(X3)
% 2.89/0.99      | v2_funct_1(X3)
% 2.89/0.99      | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
% 2.89/0.99      | k1_xboole_0 = X2 ),
% 2.89/0.99      inference(cnf_transformation,[],[f65]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1012,plain,
% 2.89/0.99      ( k1_xboole_0 = X0
% 2.89/0.99      | v1_funct_2(X1,X2,X0) != iProver_top
% 2.89/0.99      | v1_funct_2(X3,X4,X2) != iProver_top
% 2.89/0.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
% 2.89/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 2.89/0.99      | v1_funct_1(X1) != iProver_top
% 2.89/0.99      | v1_funct_1(X3) != iProver_top
% 2.89/0.99      | v2_funct_1(X3) = iProver_top
% 2.89/0.99      | v2_funct_1(k1_partfun1(X4,X2,X2,X0,X3,X1)) != iProver_top ),
% 2.89/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_3116,plain,
% 2.89/0.99      ( sK0 = k1_xboole_0
% 2.89/0.99      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 2.89/0.99      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 2.89/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 2.89/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.89/0.99      | v1_funct_1(sK2) != iProver_top
% 2.89/0.99      | v1_funct_1(sK3) != iProver_top
% 2.89/0.99      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 2.89/0.99      | v2_funct_1(sK2) = iProver_top ),
% 2.89/0.99      inference(superposition,[status(thm)],[c_3089,c_1012]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_28,negated_conjecture,
% 2.89/0.99      ( v1_funct_2(sK2,sK0,sK1) ),
% 2.89/0.99      inference(cnf_transformation,[],[f68]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_31,plain,
% 2.89/0.99      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 2.89/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_25,negated_conjecture,
% 2.89/0.99      ( v1_funct_2(sK3,sK1,sK0) ),
% 2.89/0.99      inference(cnf_transformation,[],[f71]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_34,plain,
% 2.89/0.99      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 2.89/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1011,plain,
% 2.89/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 2.89/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_11,plain,
% 2.89/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.89/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.89/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1017,plain,
% 2.89/0.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.89/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.89/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1981,plain,
% 2.89/0.99      ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
% 2.89/0.99      inference(superposition,[status(thm)],[c_1011,c_1017]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_19,plain,
% 2.89/0.99      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 2.89/0.99      | ~ v1_funct_2(X2,X0,X1)
% 2.89/0.99      | ~ v1_funct_2(X3,X1,X0)
% 2.89/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.89/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.89/0.99      | ~ v1_funct_1(X2)
% 2.89/0.99      | ~ v1_funct_1(X3)
% 2.89/0.99      | k2_relset_1(X1,X0,X3) = X0 ),
% 2.89/0.99      inference(cnf_transformation,[],[f64]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_408,plain,
% 2.89/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.89/0.99      | ~ v1_funct_2(X3,X2,X1)
% 2.89/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.89/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.89/0.99      | ~ v1_funct_1(X0)
% 2.89/0.99      | ~ v1_funct_1(X3)
% 2.89/0.99      | k1_partfun1(X2,X1,X1,X2,X3,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 2.89/0.99      | k2_relset_1(X1,X2,X0) = X2
% 2.89/0.99      | k6_partfun1(X2) != k6_partfun1(sK0)
% 2.89/0.99      | sK0 != X2 ),
% 2.89/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_23]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_409,plain,
% 2.89/0.99      ( ~ v1_funct_2(X0,X1,sK0)
% 2.89/0.99      | ~ v1_funct_2(X2,sK0,X1)
% 2.89/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 2.89/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 2.89/0.99      | ~ v1_funct_1(X0)
% 2.89/0.99      | ~ v1_funct_1(X2)
% 2.89/0.99      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 2.89/0.99      | k2_relset_1(X1,sK0,X0) = sK0
% 2.89/0.99      | k6_partfun1(sK0) != k6_partfun1(sK0) ),
% 2.89/0.99      inference(unflattening,[status(thm)],[c_408]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_483,plain,
% 2.89/0.99      ( ~ v1_funct_2(X0,X1,sK0)
% 2.89/0.99      | ~ v1_funct_2(X2,sK0,X1)
% 2.89/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 2.89/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 2.89/0.99      | ~ v1_funct_1(X0)
% 2.89/0.99      | ~ v1_funct_1(X2)
% 2.89/0.99      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 2.89/0.99      | k2_relset_1(X1,sK0,X0) = sK0 ),
% 2.89/0.99      inference(equality_resolution_simp,[status(thm)],[c_409]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1001,plain,
% 2.89/0.99      ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 2.89/0.99      | k2_relset_1(X0,sK0,X2) = sK0
% 2.89/0.99      | v1_funct_2(X2,X0,sK0) != iProver_top
% 2.89/0.99      | v1_funct_2(X1,sK0,X0) != iProver_top
% 2.89/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 2.89/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 2.89/0.99      | v1_funct_1(X2) != iProver_top
% 2.89/0.99      | v1_funct_1(X1) != iProver_top ),
% 2.89/0.99      inference(predicate_to_equality,[status(thm)],[c_483]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1771,plain,
% 2.89/0.99      ( k2_relset_1(sK1,sK0,sK3) = sK0
% 2.89/0.99      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 2.89/0.99      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 2.89/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 2.89/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.89/0.99      | v1_funct_1(sK2) != iProver_top
% 2.89/0.99      | v1_funct_1(sK3) != iProver_top ),
% 2.89/0.99      inference(equality_resolution,[status(thm)],[c_1001]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1819,plain,
% 2.89/0.99      ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
% 2.89/0.99      inference(global_propositional_subsumption,
% 2.89/0.99                [status(thm)],
% 2.89/0.99                [c_1771,c_30,c_31,c_32,c_33,c_34,c_35]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1996,plain,
% 2.89/0.99      ( k2_relat_1(sK3) = sK0 ),
% 2.89/0.99      inference(light_normalisation,[status(thm)],[c_1981,c_1819]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_10,plain,
% 2.89/0.99      ( v5_relat_1(X0,X1)
% 2.89/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.89/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_15,plain,
% 2.89/0.99      ( v2_funct_2(X0,k2_relat_1(X0))
% 2.89/0.99      | ~ v5_relat_1(X0,k2_relat_1(X0))
% 2.89/0.99      | ~ v1_relat_1(X0) ),
% 2.89/0.99      inference(cnf_transformation,[],[f82]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_313,plain,
% 2.89/0.99      ( v2_funct_2(X0,k2_relat_1(X0))
% 2.89/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 2.89/0.99      | ~ v1_relat_1(X0)
% 2.89/0.99      | X0 != X1
% 2.89/0.99      | k2_relat_1(X0) != X3 ),
% 2.89/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_15]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_314,plain,
% 2.89/0.99      ( v2_funct_2(X0,k2_relat_1(X0))
% 2.89/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
% 2.89/0.99      | ~ v1_relat_1(X0) ),
% 2.89/0.99      inference(unflattening,[status(thm)],[c_313]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_9,plain,
% 2.89/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.89/0.99      | v1_relat_1(X0) ),
% 2.89/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_324,plain,
% 2.89/0.99      ( v2_funct_2(X0,k2_relat_1(X0))
% 2.89/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0)))) ),
% 2.89/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_314,c_9]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_22,negated_conjecture,
% 2.89/0.99      ( ~ v2_funct_2(sK3,sK0) | ~ v2_funct_1(sK2) ),
% 2.89/0.99      inference(cnf_transformation,[],[f74]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_339,plain,
% 2.89/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
% 2.89/0.99      | ~ v2_funct_1(sK2)
% 2.89/0.99      | k2_relat_1(X0) != sK0
% 2.89/0.99      | sK3 != X0 ),
% 2.89/0.99      inference(resolution_lifted,[status(thm)],[c_324,c_22]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_340,plain,
% 2.89/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3))))
% 2.89/0.99      | ~ v2_funct_1(sK2)
% 2.89/0.99      | k2_relat_1(sK3) != sK0 ),
% 2.89/0.99      inference(unflattening,[status(thm)],[c_339]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_604,plain,
% 2.89/0.99      ( ~ v2_funct_1(sK2) | sP0_iProver_split | k2_relat_1(sK3) != sK0 ),
% 2.89/0.99      inference(splitting,
% 2.89/0.99                [splitting(split),new_symbols(definition,[])],
% 2.89/0.99                [c_340]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1004,plain,
% 2.89/0.99      ( k2_relat_1(sK3) != sK0
% 2.89/0.99      | v2_funct_1(sK2) != iProver_top
% 2.89/0.99      | sP0_iProver_split = iProver_top ),
% 2.89/0.99      inference(predicate_to_equality,[status(thm)],[c_604]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_2107,plain,
% 2.89/0.99      ( sK0 != sK0
% 2.89/0.99      | v2_funct_1(sK2) != iProver_top
% 2.89/0.99      | sP0_iProver_split = iProver_top ),
% 2.89/0.99      inference(demodulation,[status(thm)],[c_1996,c_1004]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_2108,plain,
% 2.89/0.99      ( v2_funct_1(sK2) != iProver_top
% 2.89/0.99      | sP0_iProver_split = iProver_top ),
% 2.89/0.99      inference(equality_resolution_simp,[status(thm)],[c_2107]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_603,plain,
% 2.89/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3))))
% 2.89/0.99      | ~ sP0_iProver_split ),
% 2.89/0.99      inference(splitting,
% 2.89/0.99                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.89/0.99                [c_340]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1005,plain,
% 2.89/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3)))) != iProver_top
% 2.89/0.99      | sP0_iProver_split != iProver_top ),
% 2.89/0.99      inference(predicate_to_equality,[status(thm)],[c_603]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_2106,plain,
% 2.89/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 2.89/0.99      | sP0_iProver_split != iProver_top ),
% 2.89/0.99      inference(demodulation,[status(thm)],[c_1996,c_1005]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_2124,plain,
% 2.89/0.99      ( sP0_iProver_split != iProver_top ),
% 2.89/0.99      inference(superposition,[status(thm)],[c_1011,c_2106]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_3255,plain,
% 2.89/0.99      ( v2_funct_1(k6_partfun1(sK0)) != iProver_top | sK0 = k1_xboole_0 ),
% 2.89/0.99      inference(global_propositional_subsumption,
% 2.89/0.99                [status(thm)],
% 2.89/0.99                [c_3116,c_30,c_31,c_32,c_33,c_34,c_35,c_2108,c_2124]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_3256,plain,
% 2.89/0.99      ( sK0 = k1_xboole_0 | v2_funct_1(k6_partfun1(sK0)) != iProver_top ),
% 2.89/0.99      inference(renaming,[status(thm)],[c_3255]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_7,plain,
% 2.89/0.99      ( v2_funct_1(k6_partfun1(X0)) ),
% 2.89/0.99      inference(cnf_transformation,[],[f76]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1018,plain,
% 2.89/0.99      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 2.89/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_3261,plain,
% 2.89/0.99      ( sK0 = k1_xboole_0 ),
% 2.89/0.99      inference(forward_subsumption_resolution,
% 2.89/0.99                [status(thm)],
% 2.89/0.99                [c_3256,c_1018]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1008,plain,
% 2.89/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.89/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_3271,plain,
% 2.89/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) = iProver_top ),
% 2.89/0.99      inference(demodulation,[status(thm)],[c_3261,c_1008]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_3,plain,
% 2.89/0.99      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.89/0.99      inference(cnf_transformation,[],[f80]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_3279,plain,
% 2.89/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.89/0.99      inference(demodulation,[status(thm)],[c_3271,c_3]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_607,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1718,plain,
% 2.89/0.99      ( X0 != X1 | sK2 != X1 | sK2 = X0 ),
% 2.89/0.99      inference(instantiation,[status(thm)],[c_607]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_2311,plain,
% 2.89/0.99      ( X0 != sK2 | sK2 = X0 | sK2 != sK2 ),
% 2.89/0.99      inference(instantiation,[status(thm)],[c_1718]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_2312,plain,
% 2.89/0.99      ( sK2 != sK2 | sK2 = k1_xboole_0 | k1_xboole_0 != sK2 ),
% 2.89/0.99      inference(instantiation,[status(thm)],[c_2311]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_613,plain,
% 2.89/0.99      ( ~ v2_funct_1(X0) | v2_funct_1(X1) | X1 != X0 ),
% 2.89/0.99      theory(equality) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1914,plain,
% 2.89/0.99      ( ~ v2_funct_1(X0) | v2_funct_1(sK2) | sK2 != X0 ),
% 2.89/0.99      inference(instantiation,[status(thm)],[c_613]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1915,plain,
% 2.89/0.99      ( sK2 != X0
% 2.89/0.99      | v2_funct_1(X0) != iProver_top
% 2.89/0.99      | v2_funct_1(sK2) = iProver_top ),
% 2.89/0.99      inference(predicate_to_equality,[status(thm)],[c_1914]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1917,plain,
% 2.89/0.99      ( sK2 != k1_xboole_0
% 2.89/0.99      | v2_funct_1(sK2) = iProver_top
% 2.89/0.99      | v2_funct_1(k1_xboole_0) != iProver_top ),
% 2.89/0.99      inference(instantiation,[status(thm)],[c_1915]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_5,plain,
% 2.89/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.89/0.99      | ~ v1_xboole_0(X1)
% 2.89/0.99      | v1_xboole_0(X0) ),
% 2.89/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1581,plain,
% 2.89/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
% 2.89/0.99      | ~ v1_xboole_0(X0)
% 2.89/0.99      | v1_xboole_0(sK2) ),
% 2.89/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1582,plain,
% 2.89/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top
% 2.89/0.99      | v1_xboole_0(X0) != iProver_top
% 2.89/0.99      | v1_xboole_0(sK2) = iProver_top ),
% 2.89/0.99      inference(predicate_to_equality,[status(thm)],[c_1581]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1584,plain,
% 2.89/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.89/0.99      | v1_xboole_0(sK2) = iProver_top
% 2.89/0.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.89/0.99      inference(instantiation,[status(thm)],[c_1582]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1510,plain,
% 2.89/0.99      ( X0 != X1 | X0 = k6_partfun1(X2) | k6_partfun1(X2) != X1 ),
% 2.89/0.99      inference(instantiation,[status(thm)],[c_607]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1511,plain,
% 2.89/0.99      ( k6_partfun1(k1_xboole_0) != k1_xboole_0
% 2.89/0.99      | k1_xboole_0 = k6_partfun1(k1_xboole_0)
% 2.89/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 2.89/0.99      inference(instantiation,[status(thm)],[c_1510]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_606,plain,( X0 = X0 ),theory(equality) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1388,plain,
% 2.89/0.99      ( sK2 = sK2 ),
% 2.89/0.99      inference(instantiation,[status(thm)],[c_606]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1,plain,
% 2.89/0.99      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 2.89/0.99      inference(cnf_transformation,[],[f45]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1348,plain,
% 2.89/0.99      ( ~ v1_xboole_0(sK2) | k1_xboole_0 = sK2 ),
% 2.89/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1352,plain,
% 2.89/0.99      ( k1_xboole_0 = sK2 | v1_xboole_0(sK2) != iProver_top ),
% 2.89/0.99      inference(predicate_to_equality,[status(thm)],[c_1348]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1230,plain,
% 2.89/0.99      ( v2_funct_1(X0)
% 2.89/0.99      | ~ v2_funct_1(k6_partfun1(X1))
% 2.89/0.99      | X0 != k6_partfun1(X1) ),
% 2.89/0.99      inference(instantiation,[status(thm)],[c_613]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1231,plain,
% 2.89/0.99      ( X0 != k6_partfun1(X1)
% 2.89/0.99      | v2_funct_1(X0) = iProver_top
% 2.89/0.99      | v2_funct_1(k6_partfun1(X1)) != iProver_top ),
% 2.89/0.99      inference(predicate_to_equality,[status(thm)],[c_1230]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1233,plain,
% 2.89/0.99      ( k1_xboole_0 != k6_partfun1(k1_xboole_0)
% 2.89/0.99      | v2_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top
% 2.89/0.99      | v2_funct_1(k1_xboole_0) = iProver_top ),
% 2.89/0.99      inference(instantiation,[status(thm)],[c_1231]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_0,plain,
% 2.89/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 2.89/0.99      inference(cnf_transformation,[],[f44]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_89,plain,
% 2.89/0.99      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.89/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_85,plain,
% 2.89/0.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 2.89/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_4,plain,
% 2.89/0.99      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 2.89/0.99      | k1_xboole_0 = X0
% 2.89/0.99      | k1_xboole_0 = X1 ),
% 2.89/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_84,plain,
% 2.89/0.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 2.89/0.99      | k1_xboole_0 = k1_xboole_0 ),
% 2.89/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_6,plain,
% 2.89/0.99      ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 2.89/0.99      inference(cnf_transformation,[],[f75]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_80,plain,
% 2.89/0.99      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 2.89/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_82,plain,
% 2.89/0.99      ( v2_funct_1(k6_partfun1(k1_xboole_0)) = iProver_top ),
% 2.89/0.99      inference(instantiation,[status(thm)],[c_80]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(contradiction,plain,
% 2.89/0.99      ( $false ),
% 2.89/0.99      inference(minisat,
% 2.89/0.99                [status(thm)],
% 2.89/0.99                [c_3279,c_2312,c_2124,c_2108,c_1917,c_1584,c_1511,c_1388,
% 2.89/0.99                 c_1352,c_1233,c_89,c_85,c_84,c_6,c_82]) ).
% 2.89/0.99  
% 2.89/0.99  
% 2.89/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.89/0.99  
% 2.89/0.99  ------                               Statistics
% 2.89/0.99  
% 2.89/0.99  ------ General
% 2.89/0.99  
% 2.89/0.99  abstr_ref_over_cycles:                  0
% 2.89/0.99  abstr_ref_under_cycles:                 0
% 2.89/0.99  gc_basic_clause_elim:                   0
% 2.89/0.99  forced_gc_time:                         0
% 2.89/0.99  parsing_time:                           0.008
% 2.89/0.99  unif_index_cands_time:                  0.
% 2.89/0.99  unif_index_add_time:                    0.
% 2.89/0.99  orderings_time:                         0.
% 2.89/0.99  out_proof_time:                         0.011
% 2.89/0.99  total_time:                             0.153
% 2.89/0.99  num_of_symbols:                         52
% 2.89/0.99  num_of_terms:                           4575
% 2.89/0.99  
% 2.89/0.99  ------ Preprocessing
% 2.89/0.99  
% 2.89/0.99  num_of_splits:                          1
% 2.89/0.99  num_of_split_atoms:                     1
% 2.89/0.99  num_of_reused_defs:                     0
% 2.89/0.99  num_eq_ax_congr_red:                    9
% 2.89/0.99  num_of_sem_filtered_clauses:            1
% 2.89/0.99  num_of_subtypes:                        0
% 2.89/0.99  monotx_restored_types:                  0
% 2.89/0.99  sat_num_of_epr_types:                   0
% 2.89/0.99  sat_num_of_non_cyclic_types:            0
% 2.89/0.99  sat_guarded_non_collapsed_types:        0
% 2.89/0.99  num_pure_diseq_elim:                    0
% 2.89/0.99  simp_replaced_by:                       0
% 2.89/0.99  res_preprocessed:                       131
% 2.89/0.99  prep_upred:                             0
% 2.89/0.99  prep_unflattend:                        17
% 2.89/0.99  smt_new_axioms:                         0
% 2.89/0.99  pred_elim_cands:                        5
% 2.89/0.99  pred_elim:                              4
% 2.89/0.99  pred_elim_cl:                           6
% 2.89/0.99  pred_elim_cycles:                       6
% 2.89/0.99  merged_defs:                            0
% 2.89/0.99  merged_defs_ncl:                        0
% 2.89/0.99  bin_hyper_res:                          0
% 2.89/0.99  prep_cycles:                            4
% 2.89/0.99  pred_elim_time:                         0.005
% 2.89/0.99  splitting_time:                         0.
% 2.89/0.99  sem_filter_time:                        0.
% 2.89/0.99  monotx_time:                            0.
% 2.89/0.99  subtype_inf_time:                       0.
% 2.89/0.99  
% 2.89/0.99  ------ Problem properties
% 2.89/0.99  
% 2.89/0.99  clauses:                                25
% 2.89/0.99  conjectures:                            6
% 2.89/0.99  epr:                                    6
% 2.89/0.99  horn:                                   23
% 2.89/0.99  ground:                                 10
% 2.89/0.99  unary:                                  12
% 2.89/0.99  binary:                                 4
% 2.89/0.99  lits:                                   72
% 2.89/0.99  lits_eq:                                15
% 2.89/0.99  fd_pure:                                0
% 2.89/0.99  fd_pseudo:                              0
% 2.89/0.99  fd_cond:                                3
% 2.89/0.99  fd_pseudo_cond:                         0
% 2.89/0.99  ac_symbols:                             0
% 2.89/0.99  
% 2.89/0.99  ------ Propositional Solver
% 2.89/0.99  
% 2.89/0.99  prop_solver_calls:                      27
% 2.89/0.99  prop_fast_solver_calls:                 904
% 2.89/0.99  smt_solver_calls:                       0
% 2.89/0.99  smt_fast_solver_calls:                  0
% 2.89/0.99  prop_num_of_clauses:                    1274
% 2.89/0.99  prop_preprocess_simplified:             4403
% 2.89/0.99  prop_fo_subsumed:                       23
% 2.89/0.99  prop_solver_time:                       0.
% 2.89/0.99  smt_solver_time:                        0.
% 2.89/0.99  smt_fast_solver_time:                   0.
% 2.89/0.99  prop_fast_solver_time:                  0.
% 2.89/0.99  prop_unsat_core_time:                   0.
% 2.89/0.99  
% 2.89/0.99  ------ QBF
% 2.89/0.99  
% 2.89/0.99  qbf_q_res:                              0
% 2.89/0.99  qbf_num_tautologies:                    0
% 2.89/0.99  qbf_prep_cycles:                        0
% 2.89/0.99  
% 2.89/0.99  ------ BMC1
% 2.89/0.99  
% 2.89/0.99  bmc1_current_bound:                     -1
% 2.89/0.99  bmc1_last_solved_bound:                 -1
% 2.89/0.99  bmc1_unsat_core_size:                   -1
% 2.89/0.99  bmc1_unsat_core_parents_size:           -1
% 2.89/0.99  bmc1_merge_next_fun:                    0
% 2.89/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.89/0.99  
% 2.89/0.99  ------ Instantiation
% 2.89/0.99  
% 2.89/0.99  inst_num_of_clauses:                    434
% 2.89/0.99  inst_num_in_passive:                    121
% 2.89/0.99  inst_num_in_active:                     209
% 2.89/0.99  inst_num_in_unprocessed:                104
% 2.89/0.99  inst_num_of_loops:                      220
% 2.89/0.99  inst_num_of_learning_restarts:          0
% 2.89/0.99  inst_num_moves_active_passive:          8
% 2.89/0.99  inst_lit_activity:                      0
% 2.89/0.99  inst_lit_activity_moves:                0
% 2.89/0.99  inst_num_tautologies:                   0
% 2.89/0.99  inst_num_prop_implied:                  0
% 2.89/0.99  inst_num_existing_simplified:           0
% 2.89/0.99  inst_num_eq_res_simplified:             0
% 2.89/0.99  inst_num_child_elim:                    0
% 2.89/0.99  inst_num_of_dismatching_blockings:      13
% 2.89/0.99  inst_num_of_non_proper_insts:           252
% 2.89/0.99  inst_num_of_duplicates:                 0
% 2.89/0.99  inst_inst_num_from_inst_to_res:         0
% 2.89/0.99  inst_dismatching_checking_time:         0.
% 2.89/0.99  
% 2.89/0.99  ------ Resolution
% 2.89/0.99  
% 2.89/0.99  res_num_of_clauses:                     0
% 2.89/0.99  res_num_in_passive:                     0
% 2.89/0.99  res_num_in_active:                      0
% 2.89/0.99  res_num_of_loops:                       135
% 2.89/0.99  res_forward_subset_subsumed:            14
% 2.89/0.99  res_backward_subset_subsumed:           0
% 2.89/0.99  res_forward_subsumed:                   0
% 2.89/0.99  res_backward_subsumed:                  0
% 2.89/0.99  res_forward_subsumption_resolution:     4
% 2.89/0.99  res_backward_subsumption_resolution:    0
% 2.89/0.99  res_clause_to_clause_subsumption:       84
% 2.89/0.99  res_orphan_elimination:                 0
% 2.89/0.99  res_tautology_del:                      23
% 2.89/0.99  res_num_eq_res_simplified:              1
% 2.89/0.99  res_num_sel_changes:                    0
% 2.89/0.99  res_moves_from_active_to_pass:          0
% 2.89/0.99  
% 2.89/0.99  ------ Superposition
% 2.89/0.99  
% 2.89/0.99  sup_time_total:                         0.
% 2.89/0.99  sup_time_generating:                    0.
% 2.89/0.99  sup_time_sim_full:                      0.
% 2.89/0.99  sup_time_sim_immed:                     0.
% 2.89/0.99  
% 2.89/0.99  sup_num_of_clauses:                     41
% 2.89/0.99  sup_num_in_active:                      25
% 2.89/0.99  sup_num_in_passive:                     16
% 2.89/0.99  sup_num_of_loops:                       42
% 2.89/0.99  sup_fw_superposition:                   24
% 2.89/0.99  sup_bw_superposition:                   8
% 2.89/0.99  sup_immediate_simplified:               14
% 2.89/0.99  sup_given_eliminated:                   1
% 2.89/0.99  comparisons_done:                       0
% 2.89/0.99  comparisons_avoided:                    0
% 2.89/0.99  
% 2.89/0.99  ------ Simplifications
% 2.89/0.99  
% 2.89/0.99  
% 2.89/0.99  sim_fw_subset_subsumed:                 0
% 2.89/0.99  sim_bw_subset_subsumed:                 0
% 2.89/0.99  sim_fw_subsumed:                        2
% 2.89/0.99  sim_bw_subsumed:                        2
% 2.89/0.99  sim_fw_subsumption_res:                 1
% 2.89/0.99  sim_bw_subsumption_res:                 0
% 2.89/0.99  sim_tautology_del:                      1
% 2.89/0.99  sim_eq_tautology_del:                   3
% 2.89/0.99  sim_eq_res_simp:                        1
% 2.89/0.99  sim_fw_demodulated:                     8
% 2.89/0.99  sim_bw_demodulated:                     16
% 2.89/0.99  sim_light_normalised:                   6
% 2.89/0.99  sim_joinable_taut:                      0
% 2.89/0.99  sim_joinable_simp:                      0
% 2.89/0.99  sim_ac_normalised:                      0
% 2.89/0.99  sim_smt_subsumption:                    0
% 2.89/0.99  
%------------------------------------------------------------------------------
