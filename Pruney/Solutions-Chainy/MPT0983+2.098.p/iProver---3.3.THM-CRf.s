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
% DateTime   : Thu Dec  3 12:02:05 EST 2020

% Result     : Theorem 3.08s
% Output     : CNFRefutation 3.08s
% Verified   : 
% Statistics : Number of formulae       :  170 ( 776 expanded)
%              Number of clauses        :   95 ( 239 expanded)
%              Number of leaves         :   23 ( 193 expanded)
%              Depth                    :   21
%              Number of atoms          :  574 (4917 expanded)
%              Number of equality atoms :  221 ( 459 expanded)
%              Maximal formula depth    :   15 (   5 average)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f65,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f24])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f25])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f44,plain,(
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

fof(f43,plain,
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

fof(f45,plain,
    ( ( ~ v2_funct_2(sK4,sK1)
      | ~ v2_funct_1(sK3) )
    & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1))
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    & v1_funct_2(sK4,sK2,sK1)
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f36,f44,f43])).

fof(f76,plain,(
    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f45])).

fof(f10,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f10])).

fof(f14,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f80,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f58,f66])).

fof(f70,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f72,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f45])).

fof(f73,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f45])).

fof(f75,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f45])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f68,plain,(
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

fof(f71,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f74,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f67,plain,(
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

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f42,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f84,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f63])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f77,plain,
    ( ~ v2_funct_2(sK4,sK1)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f5,axiom,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f79,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f52,f66])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f37])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f82,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f48])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f11,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5] :
                  ~ ( k4_mcart_1(X2,X3,X4,X5) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X5,X4,X3,X2] :
            ( k4_mcart_1(X2,X3,X4,X5) != sK0(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK0(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4,X5] :
            ( k4_mcart_1(X2,X3,X4,X5) != sK0(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK0(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f40])).

fof(f59,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f4,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f78,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f51,f66])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1064,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_11,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_24,negated_conjecture,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_496,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) != X0
    | k6_partfun1(sK1) != X3
    | sK1 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_24])).

cnf(c_497,plain,
    ( ~ m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
    inference(unflattening,[status(thm)],[c_496])).

cnf(c_12,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_505,plain,
    ( ~ m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_497,c_12])).

cnf(c_1050,plain,
    ( k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_505])).

cnf(c_2627,plain,
    ( k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k6_partfun1(sK1)
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1064,c_1050])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_31,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_33,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_34,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_36,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2924,plain,
    ( k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2627,c_31,c_33,c_34,c_36])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v2_funct_1(X3)
    | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1061,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | v1_funct_2(X3,X4,X2) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v2_funct_1(X3) = iProver_top
    | v2_funct_1(k1_partfun1(X4,X2,X2,X0,X3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2951,plain,
    ( sK1 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK2) != iProver_top
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v2_funct_1(k6_partfun1(sK1)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2924,c_1061])).

cnf(c_29,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_32,plain,
    ( v1_funct_2(sK3,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_35,plain,
    ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_1060,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1066,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2087,plain,
    ( k2_relset_1(sK2,sK1,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1060,c_1066])).

cnf(c_20,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_509,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X2,X1,X1,X2,X3,X0) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | k2_relset_1(X1,X2,X0) = X2
    | k6_partfun1(X2) != k6_partfun1(sK1)
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_24])).

cnf(c_510,plain,
    ( ~ v1_funct_2(X0,X1,sK1)
    | ~ v1_funct_2(X2,sK1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK1,X1,X1,sK1,X2,X0) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | k2_relset_1(X1,sK1,X0) = sK1
    | k6_partfun1(sK1) != k6_partfun1(sK1) ),
    inference(unflattening,[status(thm)],[c_509])).

cnf(c_582,plain,
    ( ~ v1_funct_2(X0,X1,sK1)
    | ~ v1_funct_2(X2,sK1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK1,X1,X1,sK1,X2,X0) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | k2_relset_1(X1,sK1,X0) = sK1 ),
    inference(equality_resolution_simp,[status(thm)],[c_510])).

cnf(c_1049,plain,
    ( k1_partfun1(sK1,X0,X0,sK1,X1,X2) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | k2_relset_1(X0,sK1,X2) = sK1
    | v1_funct_2(X2,X0,sK1) != iProver_top
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_582])).

cnf(c_1765,plain,
    ( k2_relset_1(sK2,sK1,sK4) = sK1
    | v1_funct_2(sK3,sK1,sK2) != iProver_top
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1049])).

cnf(c_1836,plain,
    ( k2_relset_1(sK2,sK1,sK4) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1765,c_31,c_32,c_33,c_34,c_35,c_36])).

cnf(c_2102,plain,
    ( k2_relat_1(sK4) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2087,c_1836])).

cnf(c_8,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_16,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_377,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X0)
    | X0 != X1
    | k2_relat_1(X0) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_16])).

cnf(c_378,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_377])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_388,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0)))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_378,c_7])).

cnf(c_23,negated_conjecture,
    ( ~ v2_funct_2(sK4,sK1)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_403,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
    | ~ v2_funct_1(sK3)
    | k2_relat_1(X0) != sK1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_388,c_23])).

cnf(c_404,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK4))))
    | ~ v2_funct_1(sK3)
    | k2_relat_1(sK4) != sK1 ),
    inference(unflattening,[status(thm)],[c_403])).

cnf(c_693,plain,
    ( ~ v2_funct_1(sK3)
    | sP0_iProver_split
    | k2_relat_1(sK4) != sK1 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_404])).

cnf(c_1053,plain,
    ( k2_relat_1(sK4) != sK1
    | v2_funct_1(sK3) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_693])).

cnf(c_2241,plain,
    ( sK1 != sK1
    | v2_funct_1(sK3) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(demodulation,[status(thm)],[c_2102,c_1053])).

cnf(c_2242,plain,
    ( v2_funct_1(sK3) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2241])).

cnf(c_692,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK4))))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_404])).

cnf(c_1054,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK4)))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_692])).

cnf(c_2240,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(demodulation,[status(thm)],[c_2102,c_1054])).

cnf(c_2258,plain,
    ( sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_1060,c_2240])).

cnf(c_3086,plain,
    ( v2_funct_1(k6_partfun1(sK1)) != iProver_top
    | sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2951,c_31,c_32,c_33,c_34,c_35,c_36,c_2242,c_2258])).

cnf(c_3087,plain,
    ( sK1 = k1_xboole_0
    | v2_funct_1(k6_partfun1(sK1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3086])).

cnf(c_6,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1067,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3092,plain,
    ( sK1 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3087,c_1067])).

cnf(c_1057,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_3100,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3092,c_1057])).

cnf(c_2,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_3108,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3100,c_2])).

cnf(c_696,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1751,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_696])).

cnf(c_2451,plain,
    ( X0 != sK3
    | sK3 = X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1751])).

cnf(c_2452,plain,
    ( sK3 != sK3
    | sK3 = k1_xboole_0
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_2451])).

cnf(c_701,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2183,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(sK3)
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_701])).

cnf(c_2184,plain,
    ( sK3 != X0
    | v2_funct_1(X0) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2183])).

cnf(c_2186,plain,
    ( sK3 != k1_xboole_0
    | v2_funct_1(sK3) = iProver_top
    | v2_funct_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2184])).

cnf(c_1549,plain,
    ( X0 != X1
    | X0 = k6_partfun1(X2)
    | k6_partfun1(X2) != X1 ),
    inference(instantiation,[status(thm)],[c_696])).

cnf(c_1550,plain,
    ( k6_partfun1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k6_partfun1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1549])).

cnf(c_695,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1431,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_695])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_305,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | k1_xboole_0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_4])).

cnf(c_306,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(unflattening,[status(thm)],[c_305])).

cnf(c_15,plain,
    ( r2_hidden(sK0(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_422,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
    | X1 != X0
    | sK0(X1) != X2
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_306,c_15])).

cnf(c_423,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_422])).

cnf(c_1423,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_423])).

cnf(c_1426,plain,
    ( k1_xboole_0 = sK3
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1423])).

cnf(c_1271,plain,
    ( v2_funct_1(X0)
    | ~ v2_funct_1(k6_partfun1(X1))
    | X0 != k6_partfun1(X1) ),
    inference(instantiation,[status(thm)],[c_701])).

cnf(c_1272,plain,
    ( X0 != k6_partfun1(X1)
    | v2_funct_1(X0) = iProver_top
    | v2_funct_1(k6_partfun1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1271])).

cnf(c_1274,plain,
    ( k1_xboole_0 != k6_partfun1(k1_xboole_0)
    | v2_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top
    | v2_funct_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1272])).

cnf(c_92,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_3,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_91,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_5,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_85,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_87,plain,
    ( v2_funct_1(k6_partfun1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_85])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3108,c_2452,c_2258,c_2242,c_2186,c_1550,c_1431,c_1426,c_1274,c_92,c_91,c_5,c_87])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 11:31:32 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 3.08/0.97  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.08/0.97  
% 3.08/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.08/0.97  
% 3.08/0.97  ------  iProver source info
% 3.08/0.97  
% 3.08/0.97  git: date: 2020-06-30 10:37:57 +0100
% 3.08/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.08/0.97  git: non_committed_changes: false
% 3.08/0.97  git: last_make_outside_of_git: false
% 3.08/0.97  
% 3.08/0.97  ------ 
% 3.08/0.97  
% 3.08/0.97  ------ Input Options
% 3.08/0.97  
% 3.08/0.97  --out_options                           all
% 3.08/0.97  --tptp_safe_out                         true
% 3.08/0.97  --problem_path                          ""
% 3.08/0.97  --include_path                          ""
% 3.08/0.97  --clausifier                            res/vclausify_rel
% 3.08/0.97  --clausifier_options                    --mode clausify
% 3.08/0.97  --stdin                                 false
% 3.08/0.97  --stats_out                             all
% 3.08/0.97  
% 3.08/0.97  ------ General Options
% 3.08/0.97  
% 3.08/0.97  --fof                                   false
% 3.08/0.97  --time_out_real                         305.
% 3.08/0.97  --time_out_virtual                      -1.
% 3.08/0.97  --symbol_type_check                     false
% 3.08/0.97  --clausify_out                          false
% 3.08/0.97  --sig_cnt_out                           false
% 3.08/0.97  --trig_cnt_out                          false
% 3.08/0.97  --trig_cnt_out_tolerance                1.
% 3.08/0.97  --trig_cnt_out_sk_spl                   false
% 3.08/0.97  --abstr_cl_out                          false
% 3.08/0.97  
% 3.08/0.97  ------ Global Options
% 3.08/0.97  
% 3.08/0.97  --schedule                              default
% 3.08/0.97  --add_important_lit                     false
% 3.08/0.97  --prop_solver_per_cl                    1000
% 3.08/0.97  --min_unsat_core                        false
% 3.08/0.97  --soft_assumptions                      false
% 3.08/0.97  --soft_lemma_size                       3
% 3.08/0.97  --prop_impl_unit_size                   0
% 3.08/0.97  --prop_impl_unit                        []
% 3.08/0.97  --share_sel_clauses                     true
% 3.08/0.97  --reset_solvers                         false
% 3.08/0.97  --bc_imp_inh                            [conj_cone]
% 3.08/0.97  --conj_cone_tolerance                   3.
% 3.08/0.97  --extra_neg_conj                        none
% 3.08/0.97  --large_theory_mode                     true
% 3.08/0.97  --prolific_symb_bound                   200
% 3.08/0.97  --lt_threshold                          2000
% 3.08/0.97  --clause_weak_htbl                      true
% 3.08/0.97  --gc_record_bc_elim                     false
% 3.08/0.97  
% 3.08/0.97  ------ Preprocessing Options
% 3.08/0.97  
% 3.08/0.97  --preprocessing_flag                    true
% 3.08/0.97  --time_out_prep_mult                    0.1
% 3.08/0.97  --splitting_mode                        input
% 3.08/0.97  --splitting_grd                         true
% 3.08/0.97  --splitting_cvd                         false
% 3.08/0.97  --splitting_cvd_svl                     false
% 3.08/0.97  --splitting_nvd                         32
% 3.08/0.97  --sub_typing                            true
% 3.08/0.97  --prep_gs_sim                           true
% 3.08/0.97  --prep_unflatten                        true
% 3.08/0.97  --prep_res_sim                          true
% 3.08/0.97  --prep_upred                            true
% 3.08/0.97  --prep_sem_filter                       exhaustive
% 3.08/0.97  --prep_sem_filter_out                   false
% 3.08/0.97  --pred_elim                             true
% 3.08/0.97  --res_sim_input                         true
% 3.08/0.97  --eq_ax_congr_red                       true
% 3.08/0.97  --pure_diseq_elim                       true
% 3.08/0.97  --brand_transform                       false
% 3.08/0.97  --non_eq_to_eq                          false
% 3.08/0.97  --prep_def_merge                        true
% 3.08/0.97  --prep_def_merge_prop_impl              false
% 3.08/0.97  --prep_def_merge_mbd                    true
% 3.08/0.97  --prep_def_merge_tr_red                 false
% 3.08/0.97  --prep_def_merge_tr_cl                  false
% 3.08/0.97  --smt_preprocessing                     true
% 3.08/0.97  --smt_ac_axioms                         fast
% 3.08/0.97  --preprocessed_out                      false
% 3.08/0.97  --preprocessed_stats                    false
% 3.08/0.97  
% 3.08/0.97  ------ Abstraction refinement Options
% 3.08/0.97  
% 3.08/0.97  --abstr_ref                             []
% 3.08/0.97  --abstr_ref_prep                        false
% 3.08/0.97  --abstr_ref_until_sat                   false
% 3.08/0.97  --abstr_ref_sig_restrict                funpre
% 3.08/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 3.08/0.97  --abstr_ref_under                       []
% 3.08/0.97  
% 3.08/0.97  ------ SAT Options
% 3.08/0.97  
% 3.08/0.97  --sat_mode                              false
% 3.08/0.97  --sat_fm_restart_options                ""
% 3.08/0.97  --sat_gr_def                            false
% 3.08/0.97  --sat_epr_types                         true
% 3.08/0.97  --sat_non_cyclic_types                  false
% 3.08/0.97  --sat_finite_models                     false
% 3.08/0.97  --sat_fm_lemmas                         false
% 3.08/0.97  --sat_fm_prep                           false
% 3.08/0.97  --sat_fm_uc_incr                        true
% 3.08/0.97  --sat_out_model                         small
% 3.08/0.97  --sat_out_clauses                       false
% 3.08/0.97  
% 3.08/0.97  ------ QBF Options
% 3.08/0.97  
% 3.08/0.97  --qbf_mode                              false
% 3.08/0.97  --qbf_elim_univ                         false
% 3.08/0.97  --qbf_dom_inst                          none
% 3.08/0.97  --qbf_dom_pre_inst                      false
% 3.08/0.97  --qbf_sk_in                             false
% 3.08/0.97  --qbf_pred_elim                         true
% 3.08/0.97  --qbf_split                             512
% 3.08/0.97  
% 3.08/0.97  ------ BMC1 Options
% 3.08/0.97  
% 3.08/0.97  --bmc1_incremental                      false
% 3.08/0.97  --bmc1_axioms                           reachable_all
% 3.08/0.97  --bmc1_min_bound                        0
% 3.08/0.97  --bmc1_max_bound                        -1
% 3.08/0.97  --bmc1_max_bound_default                -1
% 3.08/0.97  --bmc1_symbol_reachability              true
% 3.08/0.97  --bmc1_property_lemmas                  false
% 3.08/0.97  --bmc1_k_induction                      false
% 3.08/0.97  --bmc1_non_equiv_states                 false
% 3.08/0.97  --bmc1_deadlock                         false
% 3.08/0.97  --bmc1_ucm                              false
% 3.08/0.97  --bmc1_add_unsat_core                   none
% 3.08/0.97  --bmc1_unsat_core_children              false
% 3.08/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 3.08/0.97  --bmc1_out_stat                         full
% 3.08/0.97  --bmc1_ground_init                      false
% 3.08/0.97  --bmc1_pre_inst_next_state              false
% 3.08/0.97  --bmc1_pre_inst_state                   false
% 3.08/0.97  --bmc1_pre_inst_reach_state             false
% 3.08/0.97  --bmc1_out_unsat_core                   false
% 3.08/0.97  --bmc1_aig_witness_out                  false
% 3.08/0.97  --bmc1_verbose                          false
% 3.08/0.97  --bmc1_dump_clauses_tptp                false
% 3.08/0.97  --bmc1_dump_unsat_core_tptp             false
% 3.08/0.97  --bmc1_dump_file                        -
% 3.08/0.97  --bmc1_ucm_expand_uc_limit              128
% 3.08/0.97  --bmc1_ucm_n_expand_iterations          6
% 3.08/0.97  --bmc1_ucm_extend_mode                  1
% 3.08/0.97  --bmc1_ucm_init_mode                    2
% 3.08/0.97  --bmc1_ucm_cone_mode                    none
% 3.08/0.97  --bmc1_ucm_reduced_relation_type        0
% 3.08/0.97  --bmc1_ucm_relax_model                  4
% 3.08/0.97  --bmc1_ucm_full_tr_after_sat            true
% 3.08/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 3.08/0.97  --bmc1_ucm_layered_model                none
% 3.08/0.97  --bmc1_ucm_max_lemma_size               10
% 3.08/0.97  
% 3.08/0.97  ------ AIG Options
% 3.08/0.97  
% 3.08/0.97  --aig_mode                              false
% 3.08/0.97  
% 3.08/0.97  ------ Instantiation Options
% 3.08/0.97  
% 3.08/0.97  --instantiation_flag                    true
% 3.08/0.97  --inst_sos_flag                         false
% 3.08/0.97  --inst_sos_phase                        true
% 3.08/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.08/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.08/0.97  --inst_lit_sel_side                     num_symb
% 3.08/0.97  --inst_solver_per_active                1400
% 3.08/0.97  --inst_solver_calls_frac                1.
% 3.08/0.97  --inst_passive_queue_type               priority_queues
% 3.08/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.08/0.97  --inst_passive_queues_freq              [25;2]
% 3.08/0.97  --inst_dismatching                      true
% 3.08/0.97  --inst_eager_unprocessed_to_passive     true
% 3.08/0.97  --inst_prop_sim_given                   true
% 3.08/0.97  --inst_prop_sim_new                     false
% 3.08/0.97  --inst_subs_new                         false
% 3.08/0.97  --inst_eq_res_simp                      false
% 3.08/0.97  --inst_subs_given                       false
% 3.08/0.97  --inst_orphan_elimination               true
% 3.08/0.97  --inst_learning_loop_flag               true
% 3.08/0.97  --inst_learning_start                   3000
% 3.08/0.97  --inst_learning_factor                  2
% 3.08/0.97  --inst_start_prop_sim_after_learn       3
% 3.08/0.97  --inst_sel_renew                        solver
% 3.08/0.97  --inst_lit_activity_flag                true
% 3.08/0.97  --inst_restr_to_given                   false
% 3.08/0.97  --inst_activity_threshold               500
% 3.08/0.97  --inst_out_proof                        true
% 3.08/0.97  
% 3.08/0.97  ------ Resolution Options
% 3.08/0.97  
% 3.08/0.97  --resolution_flag                       true
% 3.08/0.97  --res_lit_sel                           adaptive
% 3.08/0.97  --res_lit_sel_side                      none
% 3.08/0.97  --res_ordering                          kbo
% 3.08/0.97  --res_to_prop_solver                    active
% 3.08/0.97  --res_prop_simpl_new                    false
% 3.08/0.97  --res_prop_simpl_given                  true
% 3.08/0.97  --res_passive_queue_type                priority_queues
% 3.08/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.08/0.97  --res_passive_queues_freq               [15;5]
% 3.08/0.97  --res_forward_subs                      full
% 3.08/0.97  --res_backward_subs                     full
% 3.08/0.97  --res_forward_subs_resolution           true
% 3.08/0.97  --res_backward_subs_resolution          true
% 3.08/0.97  --res_orphan_elimination                true
% 3.08/0.97  --res_time_limit                        2.
% 3.08/0.97  --res_out_proof                         true
% 3.08/0.97  
% 3.08/0.97  ------ Superposition Options
% 3.08/0.97  
% 3.08/0.97  --superposition_flag                    true
% 3.08/0.97  --sup_passive_queue_type                priority_queues
% 3.08/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.08/0.97  --sup_passive_queues_freq               [8;1;4]
% 3.08/0.97  --demod_completeness_check              fast
% 3.08/0.97  --demod_use_ground                      true
% 3.08/0.97  --sup_to_prop_solver                    passive
% 3.08/0.97  --sup_prop_simpl_new                    true
% 3.08/0.97  --sup_prop_simpl_given                  true
% 3.08/0.97  --sup_fun_splitting                     false
% 3.08/0.97  --sup_smt_interval                      50000
% 3.08/0.97  
% 3.08/0.97  ------ Superposition Simplification Setup
% 3.08/0.97  
% 3.08/0.97  --sup_indices_passive                   []
% 3.08/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.08/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.08/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.08/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 3.08/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.08/0.97  --sup_full_bw                           [BwDemod]
% 3.08/0.97  --sup_immed_triv                        [TrivRules]
% 3.08/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.08/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.08/0.97  --sup_immed_bw_main                     []
% 3.08/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.08/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 3.08/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.08/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.08/0.97  
% 3.08/0.97  ------ Combination Options
% 3.08/0.97  
% 3.08/0.97  --comb_res_mult                         3
% 3.08/0.97  --comb_sup_mult                         2
% 3.08/0.97  --comb_inst_mult                        10
% 3.08/0.97  
% 3.08/0.97  ------ Debug Options
% 3.08/0.97  
% 3.08/0.97  --dbg_backtrace                         false
% 3.08/0.97  --dbg_dump_prop_clauses                 false
% 3.08/0.97  --dbg_dump_prop_clauses_file            -
% 3.08/0.97  --dbg_out_stat                          false
% 3.08/0.97  ------ Parsing...
% 3.08/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.08/0.97  
% 3.08/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 3.08/0.97  
% 3.08/0.97  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.08/0.97  
% 3.08/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.08/0.97  ------ Proving...
% 3.08/0.97  ------ Problem Properties 
% 3.08/0.97  
% 3.08/0.97  
% 3.08/0.97  clauses                                 25
% 3.08/0.97  conjectures                             6
% 3.08/0.97  EPR                                     4
% 3.08/0.97  Horn                                    23
% 3.08/0.97  unary                                   11
% 3.08/0.97  binary                                  6
% 3.08/0.97  lits                                    72
% 3.08/0.97  lits eq                                 19
% 3.08/0.97  fd_pure                                 0
% 3.08/0.97  fd_pseudo                               0
% 3.08/0.97  fd_cond                                 5
% 3.08/0.97  fd_pseudo_cond                          0
% 3.08/0.97  AC symbols                              0
% 3.08/0.97  
% 3.08/0.97  ------ Schedule dynamic 5 is on 
% 3.08/0.97  
% 3.08/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.08/0.97  
% 3.08/0.97  
% 3.08/0.97  ------ 
% 3.08/0.97  Current options:
% 3.08/0.97  ------ 
% 3.08/0.97  
% 3.08/0.97  ------ Input Options
% 3.08/0.97  
% 3.08/0.97  --out_options                           all
% 3.08/0.97  --tptp_safe_out                         true
% 3.08/0.97  --problem_path                          ""
% 3.08/0.97  --include_path                          ""
% 3.08/0.97  --clausifier                            res/vclausify_rel
% 3.08/0.97  --clausifier_options                    --mode clausify
% 3.08/0.97  --stdin                                 false
% 3.08/0.97  --stats_out                             all
% 3.08/0.97  
% 3.08/0.97  ------ General Options
% 3.08/0.97  
% 3.08/0.97  --fof                                   false
% 3.08/0.97  --time_out_real                         305.
% 3.08/0.97  --time_out_virtual                      -1.
% 3.08/0.97  --symbol_type_check                     false
% 3.08/0.97  --clausify_out                          false
% 3.08/0.97  --sig_cnt_out                           false
% 3.08/0.97  --trig_cnt_out                          false
% 3.08/0.97  --trig_cnt_out_tolerance                1.
% 3.08/0.97  --trig_cnt_out_sk_spl                   false
% 3.08/0.97  --abstr_cl_out                          false
% 3.08/0.97  
% 3.08/0.97  ------ Global Options
% 3.08/0.97  
% 3.08/0.97  --schedule                              default
% 3.08/0.97  --add_important_lit                     false
% 3.08/0.97  --prop_solver_per_cl                    1000
% 3.08/0.97  --min_unsat_core                        false
% 3.08/0.97  --soft_assumptions                      false
% 3.08/0.97  --soft_lemma_size                       3
% 3.08/0.97  --prop_impl_unit_size                   0
% 3.08/0.97  --prop_impl_unit                        []
% 3.08/0.97  --share_sel_clauses                     true
% 3.08/0.97  --reset_solvers                         false
% 3.08/0.97  --bc_imp_inh                            [conj_cone]
% 3.08/0.97  --conj_cone_tolerance                   3.
% 3.08/0.97  --extra_neg_conj                        none
% 3.08/0.97  --large_theory_mode                     true
% 3.08/0.97  --prolific_symb_bound                   200
% 3.08/0.97  --lt_threshold                          2000
% 3.08/0.97  --clause_weak_htbl                      true
% 3.08/0.97  --gc_record_bc_elim                     false
% 3.08/0.97  
% 3.08/0.97  ------ Preprocessing Options
% 3.08/0.97  
% 3.08/0.97  --preprocessing_flag                    true
% 3.08/0.97  --time_out_prep_mult                    0.1
% 3.08/0.97  --splitting_mode                        input
% 3.08/0.97  --splitting_grd                         true
% 3.08/0.97  --splitting_cvd                         false
% 3.08/0.97  --splitting_cvd_svl                     false
% 3.08/0.97  --splitting_nvd                         32
% 3.08/0.97  --sub_typing                            true
% 3.08/0.97  --prep_gs_sim                           true
% 3.08/0.97  --prep_unflatten                        true
% 3.08/0.97  --prep_res_sim                          true
% 3.08/0.97  --prep_upred                            true
% 3.08/0.97  --prep_sem_filter                       exhaustive
% 3.08/0.97  --prep_sem_filter_out                   false
% 3.08/0.97  --pred_elim                             true
% 3.08/0.97  --res_sim_input                         true
% 3.08/0.97  --eq_ax_congr_red                       true
% 3.08/0.97  --pure_diseq_elim                       true
% 3.08/0.97  --brand_transform                       false
% 3.08/0.97  --non_eq_to_eq                          false
% 3.08/0.97  --prep_def_merge                        true
% 3.08/0.97  --prep_def_merge_prop_impl              false
% 3.08/0.97  --prep_def_merge_mbd                    true
% 3.08/0.97  --prep_def_merge_tr_red                 false
% 3.08/0.97  --prep_def_merge_tr_cl                  false
% 3.08/0.97  --smt_preprocessing                     true
% 3.08/0.97  --smt_ac_axioms                         fast
% 3.08/0.97  --preprocessed_out                      false
% 3.08/0.97  --preprocessed_stats                    false
% 3.08/0.97  
% 3.08/0.97  ------ Abstraction refinement Options
% 3.08/0.97  
% 3.08/0.97  --abstr_ref                             []
% 3.08/0.97  --abstr_ref_prep                        false
% 3.08/0.97  --abstr_ref_until_sat                   false
% 3.08/0.97  --abstr_ref_sig_restrict                funpre
% 3.08/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 3.08/0.97  --abstr_ref_under                       []
% 3.08/0.97  
% 3.08/0.97  ------ SAT Options
% 3.08/0.97  
% 3.08/0.97  --sat_mode                              false
% 3.08/0.97  --sat_fm_restart_options                ""
% 3.08/0.97  --sat_gr_def                            false
% 3.08/0.97  --sat_epr_types                         true
% 3.08/0.97  --sat_non_cyclic_types                  false
% 3.08/0.97  --sat_finite_models                     false
% 3.08/0.97  --sat_fm_lemmas                         false
% 3.08/0.97  --sat_fm_prep                           false
% 3.08/0.97  --sat_fm_uc_incr                        true
% 3.08/0.97  --sat_out_model                         small
% 3.08/0.97  --sat_out_clauses                       false
% 3.08/0.97  
% 3.08/0.97  ------ QBF Options
% 3.08/0.97  
% 3.08/0.97  --qbf_mode                              false
% 3.08/0.97  --qbf_elim_univ                         false
% 3.08/0.97  --qbf_dom_inst                          none
% 3.08/0.97  --qbf_dom_pre_inst                      false
% 3.08/0.97  --qbf_sk_in                             false
% 3.08/0.97  --qbf_pred_elim                         true
% 3.08/0.97  --qbf_split                             512
% 3.08/0.97  
% 3.08/0.97  ------ BMC1 Options
% 3.08/0.97  
% 3.08/0.97  --bmc1_incremental                      false
% 3.08/0.97  --bmc1_axioms                           reachable_all
% 3.08/0.97  --bmc1_min_bound                        0
% 3.08/0.97  --bmc1_max_bound                        -1
% 3.08/0.97  --bmc1_max_bound_default                -1
% 3.08/0.97  --bmc1_symbol_reachability              true
% 3.08/0.97  --bmc1_property_lemmas                  false
% 3.08/0.97  --bmc1_k_induction                      false
% 3.08/0.97  --bmc1_non_equiv_states                 false
% 3.08/0.97  --bmc1_deadlock                         false
% 3.08/0.97  --bmc1_ucm                              false
% 3.08/0.97  --bmc1_add_unsat_core                   none
% 3.08/0.97  --bmc1_unsat_core_children              false
% 3.08/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 3.08/0.97  --bmc1_out_stat                         full
% 3.08/0.97  --bmc1_ground_init                      false
% 3.08/0.97  --bmc1_pre_inst_next_state              false
% 3.08/0.97  --bmc1_pre_inst_state                   false
% 3.08/0.97  --bmc1_pre_inst_reach_state             false
% 3.08/0.97  --bmc1_out_unsat_core                   false
% 3.08/0.97  --bmc1_aig_witness_out                  false
% 3.08/0.97  --bmc1_verbose                          false
% 3.08/0.97  --bmc1_dump_clauses_tptp                false
% 3.08/0.97  --bmc1_dump_unsat_core_tptp             false
% 3.08/0.97  --bmc1_dump_file                        -
% 3.08/0.97  --bmc1_ucm_expand_uc_limit              128
% 3.08/0.97  --bmc1_ucm_n_expand_iterations          6
% 3.08/0.97  --bmc1_ucm_extend_mode                  1
% 3.08/0.97  --bmc1_ucm_init_mode                    2
% 3.08/0.97  --bmc1_ucm_cone_mode                    none
% 3.08/0.97  --bmc1_ucm_reduced_relation_type        0
% 3.08/0.97  --bmc1_ucm_relax_model                  4
% 3.08/0.97  --bmc1_ucm_full_tr_after_sat            true
% 3.08/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 3.08/0.97  --bmc1_ucm_layered_model                none
% 3.08/0.97  --bmc1_ucm_max_lemma_size               10
% 3.08/0.97  
% 3.08/0.97  ------ AIG Options
% 3.08/0.97  
% 3.08/0.97  --aig_mode                              false
% 3.08/0.97  
% 3.08/0.97  ------ Instantiation Options
% 3.08/0.97  
% 3.08/0.97  --instantiation_flag                    true
% 3.08/0.97  --inst_sos_flag                         false
% 3.08/0.97  --inst_sos_phase                        true
% 3.08/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.08/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.08/0.97  --inst_lit_sel_side                     none
% 3.08/0.97  --inst_solver_per_active                1400
% 3.08/0.97  --inst_solver_calls_frac                1.
% 3.08/0.97  --inst_passive_queue_type               priority_queues
% 3.08/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.08/0.97  --inst_passive_queues_freq              [25;2]
% 3.08/0.97  --inst_dismatching                      true
% 3.08/0.97  --inst_eager_unprocessed_to_passive     true
% 3.08/0.97  --inst_prop_sim_given                   true
% 3.08/0.97  --inst_prop_sim_new                     false
% 3.08/0.97  --inst_subs_new                         false
% 3.08/0.97  --inst_eq_res_simp                      false
% 3.08/0.97  --inst_subs_given                       false
% 3.08/0.97  --inst_orphan_elimination               true
% 3.08/0.97  --inst_learning_loop_flag               true
% 3.08/0.97  --inst_learning_start                   3000
% 3.08/0.97  --inst_learning_factor                  2
% 3.08/0.97  --inst_start_prop_sim_after_learn       3
% 3.08/0.97  --inst_sel_renew                        solver
% 3.08/0.97  --inst_lit_activity_flag                true
% 3.08/0.97  --inst_restr_to_given                   false
% 3.08/0.97  --inst_activity_threshold               500
% 3.08/0.97  --inst_out_proof                        true
% 3.08/0.97  
% 3.08/0.97  ------ Resolution Options
% 3.08/0.97  
% 3.08/0.97  --resolution_flag                       false
% 3.08/0.97  --res_lit_sel                           adaptive
% 3.08/0.97  --res_lit_sel_side                      none
% 3.08/0.97  --res_ordering                          kbo
% 3.08/0.97  --res_to_prop_solver                    active
% 3.08/0.97  --res_prop_simpl_new                    false
% 3.08/0.97  --res_prop_simpl_given                  true
% 3.08/0.97  --res_passive_queue_type                priority_queues
% 3.08/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.08/0.97  --res_passive_queues_freq               [15;5]
% 3.08/0.97  --res_forward_subs                      full
% 3.08/0.97  --res_backward_subs                     full
% 3.08/0.97  --res_forward_subs_resolution           true
% 3.08/0.97  --res_backward_subs_resolution          true
% 3.08/0.97  --res_orphan_elimination                true
% 3.08/0.97  --res_time_limit                        2.
% 3.08/0.97  --res_out_proof                         true
% 3.08/0.97  
% 3.08/0.97  ------ Superposition Options
% 3.08/0.97  
% 3.08/0.97  --superposition_flag                    true
% 3.08/0.97  --sup_passive_queue_type                priority_queues
% 3.08/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.08/0.97  --sup_passive_queues_freq               [8;1;4]
% 3.08/0.97  --demod_completeness_check              fast
% 3.08/0.97  --demod_use_ground                      true
% 3.08/0.97  --sup_to_prop_solver                    passive
% 3.08/0.97  --sup_prop_simpl_new                    true
% 3.08/0.97  --sup_prop_simpl_given                  true
% 3.08/0.97  --sup_fun_splitting                     false
% 3.08/0.97  --sup_smt_interval                      50000
% 3.08/0.97  
% 3.08/0.97  ------ Superposition Simplification Setup
% 3.08/0.97  
% 3.08/0.97  --sup_indices_passive                   []
% 3.08/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.08/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.08/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.08/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 3.08/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.08/0.97  --sup_full_bw                           [BwDemod]
% 3.08/0.97  --sup_immed_triv                        [TrivRules]
% 3.08/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.08/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.08/0.97  --sup_immed_bw_main                     []
% 3.08/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.08/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 3.08/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.08/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.08/0.97  
% 3.08/0.97  ------ Combination Options
% 3.08/0.97  
% 3.08/0.97  --comb_res_mult                         3
% 3.08/0.97  --comb_sup_mult                         2
% 3.08/0.97  --comb_inst_mult                        10
% 3.08/0.97  
% 3.08/0.97  ------ Debug Options
% 3.08/0.97  
% 3.08/0.97  --dbg_backtrace                         false
% 3.08/0.97  --dbg_dump_prop_clauses                 false
% 3.08/0.97  --dbg_dump_prop_clauses_file            -
% 3.08/0.97  --dbg_out_stat                          false
% 3.08/0.97  
% 3.08/0.97  
% 3.08/0.97  
% 3.08/0.97  
% 3.08/0.97  ------ Proving...
% 3.08/0.97  
% 3.08/0.97  
% 3.08/0.97  % SZS status Theorem for theBenchmark.p
% 3.08/0.97  
% 3.08/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 3.08/0.97  
% 3.08/0.97  fof(f13,axiom,(
% 3.08/0.97    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 3.08/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.08/0.98  
% 3.08/0.98  fof(f29,plain,(
% 3.08/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.08/0.98    inference(ennf_transformation,[],[f13])).
% 3.08/0.98  
% 3.08/0.98  fof(f30,plain,(
% 3.08/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.08/0.98    inference(flattening,[],[f29])).
% 3.08/0.98  
% 3.08/0.98  fof(f65,plain,(
% 3.08/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.08/0.98    inference(cnf_transformation,[],[f30])).
% 3.08/0.98  
% 3.08/0.98  fof(f9,axiom,(
% 3.08/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.08/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.08/0.98  
% 3.08/0.98  fof(f24,plain,(
% 3.08/0.98    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.08/0.98    inference(ennf_transformation,[],[f9])).
% 3.08/0.98  
% 3.08/0.98  fof(f25,plain,(
% 3.08/0.98    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.08/0.98    inference(flattening,[],[f24])).
% 3.08/0.98  
% 3.08/0.98  fof(f39,plain,(
% 3.08/0.98    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.08/0.98    inference(nnf_transformation,[],[f25])).
% 3.08/0.98  
% 3.08/0.98  fof(f56,plain,(
% 3.08/0.98    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.08/0.98    inference(cnf_transformation,[],[f39])).
% 3.08/0.98  
% 3.08/0.98  fof(f17,conjecture,(
% 3.08/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 3.08/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.08/0.98  
% 3.08/0.98  fof(f18,negated_conjecture,(
% 3.08/0.98    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 3.08/0.98    inference(negated_conjecture,[],[f17])).
% 3.08/0.98  
% 3.08/0.98  fof(f35,plain,(
% 3.08/0.98    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.08/0.98    inference(ennf_transformation,[],[f18])).
% 3.08/0.98  
% 3.08/0.98  fof(f36,plain,(
% 3.08/0.98    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.08/0.98    inference(flattening,[],[f35])).
% 3.08/0.98  
% 3.08/0.98  fof(f44,plain,(
% 3.08/0.98    ( ! [X2,X0,X1] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((~v2_funct_2(sK4,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK4),k6_partfun1(X0)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK4,X1,X0) & v1_funct_1(sK4))) )),
% 3.08/0.98    introduced(choice_axiom,[])).
% 3.08/0.98  
% 3.08/0.98  fof(f43,plain,(
% 3.08/0.98    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK1) | ~v2_funct_1(sK3)) & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,X3),k6_partfun1(sK1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(X3,sK2,sK1) & v1_funct_1(X3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 3.08/0.98    introduced(choice_axiom,[])).
% 3.08/0.98  
% 3.08/0.98  fof(f45,plain,(
% 3.08/0.98    ((~v2_funct_2(sK4,sK1) | ~v2_funct_1(sK3)) & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 3.08/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f36,f44,f43])).
% 3.08/0.98  
% 3.08/0.98  fof(f76,plain,(
% 3.08/0.98    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1))),
% 3.08/0.98    inference(cnf_transformation,[],[f45])).
% 3.08/0.98  
% 3.08/0.98  fof(f10,axiom,(
% 3.08/0.98    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.08/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.08/0.98  
% 3.08/0.98  fof(f58,plain,(
% 3.08/0.98    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.08/0.98    inference(cnf_transformation,[],[f10])).
% 3.08/0.98  
% 3.08/0.98  fof(f14,axiom,(
% 3.08/0.98    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.08/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.08/0.98  
% 3.08/0.98  fof(f66,plain,(
% 3.08/0.98    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.08/0.98    inference(cnf_transformation,[],[f14])).
% 3.08/0.98  
% 3.08/0.98  fof(f80,plain,(
% 3.08/0.98    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.08/0.98    inference(definition_unfolding,[],[f58,f66])).
% 3.08/0.98  
% 3.08/0.98  fof(f70,plain,(
% 3.08/0.98    v1_funct_1(sK3)),
% 3.08/0.98    inference(cnf_transformation,[],[f45])).
% 3.08/0.98  
% 3.08/0.98  fof(f72,plain,(
% 3.08/0.98    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 3.08/0.98    inference(cnf_transformation,[],[f45])).
% 3.08/0.98  
% 3.08/0.98  fof(f73,plain,(
% 3.08/0.98    v1_funct_1(sK4)),
% 3.08/0.98    inference(cnf_transformation,[],[f45])).
% 3.08/0.98  
% 3.08/0.98  fof(f75,plain,(
% 3.08/0.98    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 3.08/0.98    inference(cnf_transformation,[],[f45])).
% 3.08/0.98  
% 3.08/0.98  fof(f16,axiom,(
% 3.08/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 3.08/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.08/0.98  
% 3.08/0.98  fof(f33,plain,(
% 3.08/0.98    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 3.08/0.98    inference(ennf_transformation,[],[f16])).
% 3.08/0.98  
% 3.08/0.98  fof(f34,plain,(
% 3.08/0.98    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.08/0.98    inference(flattening,[],[f33])).
% 3.08/0.98  
% 3.08/0.98  fof(f68,plain,(
% 3.08/0.98    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X3) | k1_xboole_0 = X2 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.08/0.98    inference(cnf_transformation,[],[f34])).
% 3.08/0.98  
% 3.08/0.98  fof(f71,plain,(
% 3.08/0.98    v1_funct_2(sK3,sK1,sK2)),
% 3.08/0.98    inference(cnf_transformation,[],[f45])).
% 3.08/0.98  
% 3.08/0.98  fof(f74,plain,(
% 3.08/0.98    v1_funct_2(sK4,sK2,sK1)),
% 3.08/0.98    inference(cnf_transformation,[],[f45])).
% 3.08/0.98  
% 3.08/0.98  fof(f8,axiom,(
% 3.08/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 3.08/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.08/0.98  
% 3.08/0.98  fof(f23,plain,(
% 3.08/0.98    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.08/0.98    inference(ennf_transformation,[],[f8])).
% 3.08/0.98  
% 3.08/0.98  fof(f55,plain,(
% 3.08/0.98    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.08/0.98    inference(cnf_transformation,[],[f23])).
% 3.08/0.98  
% 3.08/0.98  fof(f15,axiom,(
% 3.08/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 3.08/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.08/0.98  
% 3.08/0.98  fof(f31,plain,(
% 3.08/0.98    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.08/0.98    inference(ennf_transformation,[],[f15])).
% 3.08/0.98  
% 3.08/0.98  fof(f32,plain,(
% 3.08/0.98    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.08/0.98    inference(flattening,[],[f31])).
% 3.08/0.98  
% 3.08/0.98  fof(f67,plain,(
% 3.08/0.98    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.08/0.98    inference(cnf_transformation,[],[f32])).
% 3.08/0.98  
% 3.08/0.98  fof(f7,axiom,(
% 3.08/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.08/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.08/0.98  
% 3.08/0.98  fof(f19,plain,(
% 3.08/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.08/0.98    inference(pure_predicate_removal,[],[f7])).
% 3.08/0.98  
% 3.08/0.98  fof(f22,plain,(
% 3.08/0.98    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.08/0.98    inference(ennf_transformation,[],[f19])).
% 3.08/0.98  
% 3.08/0.98  fof(f54,plain,(
% 3.08/0.98    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.08/0.98    inference(cnf_transformation,[],[f22])).
% 3.08/0.98  
% 3.08/0.98  fof(f12,axiom,(
% 3.08/0.98    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 3.08/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.08/0.98  
% 3.08/0.98  fof(f27,plain,(
% 3.08/0.98    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.08/0.98    inference(ennf_transformation,[],[f12])).
% 3.08/0.98  
% 3.08/0.98  fof(f28,plain,(
% 3.08/0.98    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.08/0.98    inference(flattening,[],[f27])).
% 3.08/0.98  
% 3.08/0.98  fof(f42,plain,(
% 3.08/0.98    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.08/0.98    inference(nnf_transformation,[],[f28])).
% 3.08/0.98  
% 3.08/0.98  fof(f63,plain,(
% 3.08/0.98    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.08/0.98    inference(cnf_transformation,[],[f42])).
% 3.08/0.98  
% 3.08/0.98  fof(f84,plain,(
% 3.08/0.98    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.08/0.98    inference(equality_resolution,[],[f63])).
% 3.08/0.98  
% 3.08/0.98  fof(f6,axiom,(
% 3.08/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.08/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.08/0.98  
% 3.08/0.98  fof(f21,plain,(
% 3.08/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.08/0.98    inference(ennf_transformation,[],[f6])).
% 3.08/0.98  
% 3.08/0.98  fof(f53,plain,(
% 3.08/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.08/0.98    inference(cnf_transformation,[],[f21])).
% 3.08/0.98  
% 3.08/0.98  fof(f77,plain,(
% 3.08/0.98    ~v2_funct_2(sK4,sK1) | ~v2_funct_1(sK3)),
% 3.08/0.98    inference(cnf_transformation,[],[f45])).
% 3.08/0.98  
% 3.08/0.98  fof(f5,axiom,(
% 3.08/0.98    ! [X0] : v2_funct_1(k6_relat_1(X0))),
% 3.08/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.08/0.98  
% 3.08/0.98  fof(f52,plain,(
% 3.08/0.98    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 3.08/0.98    inference(cnf_transformation,[],[f5])).
% 3.08/0.98  
% 3.08/0.98  fof(f79,plain,(
% 3.08/0.98    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 3.08/0.98    inference(definition_unfolding,[],[f52,f66])).
% 3.08/0.98  
% 3.08/0.98  fof(f2,axiom,(
% 3.08/0.98    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.08/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.08/0.98  
% 3.08/0.98  fof(f37,plain,(
% 3.08/0.98    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.08/0.98    inference(nnf_transformation,[],[f2])).
% 3.08/0.98  
% 3.08/0.98  fof(f38,plain,(
% 3.08/0.98    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.08/0.98    inference(flattening,[],[f37])).
% 3.08/0.98  
% 3.08/0.98  fof(f48,plain,(
% 3.08/0.98    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.08/0.98    inference(cnf_transformation,[],[f38])).
% 3.08/0.98  
% 3.08/0.98  fof(f82,plain,(
% 3.08/0.98    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.08/0.98    inference(equality_resolution,[],[f48])).
% 3.08/0.98  
% 3.08/0.98  fof(f1,axiom,(
% 3.08/0.98    v1_xboole_0(k1_xboole_0)),
% 3.08/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.08/0.98  
% 3.08/0.98  fof(f46,plain,(
% 3.08/0.98    v1_xboole_0(k1_xboole_0)),
% 3.08/0.98    inference(cnf_transformation,[],[f1])).
% 3.08/0.98  
% 3.08/0.98  fof(f3,axiom,(
% 3.08/0.98    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 3.08/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.08/0.98  
% 3.08/0.98  fof(f20,plain,(
% 3.08/0.98    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.08/0.98    inference(ennf_transformation,[],[f3])).
% 3.08/0.98  
% 3.08/0.98  fof(f50,plain,(
% 3.08/0.98    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.08/0.98    inference(cnf_transformation,[],[f20])).
% 3.08/0.98  
% 3.08/0.98  fof(f11,axiom,(
% 3.08/0.98    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5] : ~(k4_mcart_1(X2,X3,X4,X5) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 3.08/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.08/0.98  
% 3.08/0.98  fof(f26,plain,(
% 3.08/0.98    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 3.08/0.98    inference(ennf_transformation,[],[f11])).
% 3.08/0.98  
% 3.08/0.98  fof(f40,plain,(
% 3.08/0.98    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X5,X4,X3,X2] : (k4_mcart_1(X2,X3,X4,X5) != sK0(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK0(X0),X0)))),
% 3.08/0.98    introduced(choice_axiom,[])).
% 3.08/0.98  
% 3.08/0.98  fof(f41,plain,(
% 3.08/0.98    ! [X0] : ((! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != sK0(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK0(X0),X0)) | k1_xboole_0 = X0)),
% 3.08/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f40])).
% 3.08/0.98  
% 3.08/0.98  fof(f59,plain,(
% 3.08/0.98    ( ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0) )),
% 3.08/0.98    inference(cnf_transformation,[],[f41])).
% 3.08/0.98  
% 3.08/0.98  fof(f47,plain,(
% 3.08/0.98    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 3.08/0.98    inference(cnf_transformation,[],[f38])).
% 3.08/0.98  
% 3.08/0.98  fof(f4,axiom,(
% 3.08/0.98    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 3.08/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.08/0.98  
% 3.08/0.98  fof(f51,plain,(
% 3.08/0.98    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 3.08/0.98    inference(cnf_transformation,[],[f4])).
% 3.08/0.98  
% 3.08/0.98  fof(f78,plain,(
% 3.08/0.98    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 3.08/0.98    inference(definition_unfolding,[],[f51,f66])).
% 3.08/0.98  
% 3.08/0.98  cnf(c_18,plain,
% 3.08/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.08/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.08/0.98      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.08/0.98      | ~ v1_funct_1(X0)
% 3.08/0.98      | ~ v1_funct_1(X3) ),
% 3.08/0.98      inference(cnf_transformation,[],[f65]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_1064,plain,
% 3.08/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.08/0.98      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 3.08/0.98      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
% 3.08/0.98      | v1_funct_1(X0) != iProver_top
% 3.08/0.98      | v1_funct_1(X3) != iProver_top ),
% 3.08/0.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_11,plain,
% 3.08/0.98      ( ~ r2_relset_1(X0,X1,X2,X3)
% 3.08/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.08/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.08/0.98      | X3 = X2 ),
% 3.08/0.98      inference(cnf_transformation,[],[f56]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_24,negated_conjecture,
% 3.08/0.98      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) ),
% 3.08/0.98      inference(cnf_transformation,[],[f76]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_496,plain,
% 3.08/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.08/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.08/0.98      | X3 = X0
% 3.08/0.98      | k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) != X0
% 3.08/0.98      | k6_partfun1(sK1) != X3
% 3.08/0.98      | sK1 != X2
% 3.08/0.98      | sK1 != X1 ),
% 3.08/0.98      inference(resolution_lifted,[status(thm)],[c_11,c_24]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_497,plain,
% 3.08/0.98      ( ~ m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.08/0.98      | ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.08/0.98      | k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
% 3.08/0.98      inference(unflattening,[status(thm)],[c_496]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_12,plain,
% 3.08/0.98      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.08/0.98      inference(cnf_transformation,[],[f80]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_505,plain,
% 3.08/0.98      ( ~ m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.08/0.98      | k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
% 3.08/0.98      inference(forward_subsumption_resolution,
% 3.08/0.98                [status(thm)],
% 3.08/0.98                [c_497,c_12]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_1050,plain,
% 3.08/0.98      ( k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 3.08/0.98      | m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
% 3.08/0.98      inference(predicate_to_equality,[status(thm)],[c_505]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_2627,plain,
% 3.08/0.98      ( k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k6_partfun1(sK1)
% 3.08/0.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 3.08/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.08/0.98      | v1_funct_1(sK3) != iProver_top
% 3.08/0.98      | v1_funct_1(sK4) != iProver_top ),
% 3.08/0.98      inference(superposition,[status(thm)],[c_1064,c_1050]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_30,negated_conjecture,
% 3.08/0.98      ( v1_funct_1(sK3) ),
% 3.08/0.98      inference(cnf_transformation,[],[f70]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_31,plain,
% 3.08/0.98      ( v1_funct_1(sK3) = iProver_top ),
% 3.08/0.98      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_28,negated_conjecture,
% 3.08/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 3.08/0.98      inference(cnf_transformation,[],[f72]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_33,plain,
% 3.08/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.08/0.98      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_27,negated_conjecture,
% 3.08/0.98      ( v1_funct_1(sK4) ),
% 3.08/0.98      inference(cnf_transformation,[],[f73]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_34,plain,
% 3.08/0.98      ( v1_funct_1(sK4) = iProver_top ),
% 3.08/0.98      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_25,negated_conjecture,
% 3.08/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 3.08/0.98      inference(cnf_transformation,[],[f75]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_36,plain,
% 3.08/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 3.08/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_2924,plain,
% 3.08/0.98      ( k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k6_partfun1(sK1) ),
% 3.08/0.98      inference(global_propositional_subsumption,
% 3.08/0.98                [status(thm)],
% 3.08/0.98                [c_2627,c_31,c_33,c_34,c_36]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_22,plain,
% 3.08/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.08/0.98      | ~ v1_funct_2(X3,X4,X1)
% 3.08/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
% 3.08/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.08/0.98      | ~ v1_funct_1(X0)
% 3.08/0.98      | ~ v1_funct_1(X3)
% 3.08/0.98      | v2_funct_1(X3)
% 3.08/0.98      | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
% 3.08/0.98      | k1_xboole_0 = X2 ),
% 3.08/0.98      inference(cnf_transformation,[],[f68]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_1061,plain,
% 3.08/0.98      ( k1_xboole_0 = X0
% 3.08/0.98      | v1_funct_2(X1,X2,X0) != iProver_top
% 3.08/0.98      | v1_funct_2(X3,X4,X2) != iProver_top
% 3.08/0.98      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
% 3.08/0.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 3.08/0.98      | v1_funct_1(X1) != iProver_top
% 3.08/0.98      | v1_funct_1(X3) != iProver_top
% 3.08/0.98      | v2_funct_1(X3) = iProver_top
% 3.08/0.98      | v2_funct_1(k1_partfun1(X4,X2,X2,X0,X3,X1)) != iProver_top ),
% 3.08/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_2951,plain,
% 3.08/0.98      ( sK1 = k1_xboole_0
% 3.08/0.98      | v1_funct_2(sK3,sK1,sK2) != iProver_top
% 3.08/0.98      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 3.08/0.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 3.08/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.08/0.98      | v1_funct_1(sK3) != iProver_top
% 3.08/0.98      | v1_funct_1(sK4) != iProver_top
% 3.08/0.98      | v2_funct_1(k6_partfun1(sK1)) != iProver_top
% 3.08/0.98      | v2_funct_1(sK3) = iProver_top ),
% 3.08/0.98      inference(superposition,[status(thm)],[c_2924,c_1061]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_29,negated_conjecture,
% 3.08/0.98      ( v1_funct_2(sK3,sK1,sK2) ),
% 3.08/0.98      inference(cnf_transformation,[],[f71]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_32,plain,
% 3.08/0.98      ( v1_funct_2(sK3,sK1,sK2) = iProver_top ),
% 3.08/0.98      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_26,negated_conjecture,
% 3.08/0.98      ( v1_funct_2(sK4,sK2,sK1) ),
% 3.08/0.98      inference(cnf_transformation,[],[f74]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_35,plain,
% 3.08/0.98      ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
% 3.08/0.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_1060,plain,
% 3.08/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 3.08/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_9,plain,
% 3.08/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.08/0.98      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.08/0.98      inference(cnf_transformation,[],[f55]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_1066,plain,
% 3.08/0.98      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.08/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.08/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_2087,plain,
% 3.08/0.98      ( k2_relset_1(sK2,sK1,sK4) = k2_relat_1(sK4) ),
% 3.08/0.98      inference(superposition,[status(thm)],[c_1060,c_1066]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_20,plain,
% 3.08/0.98      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.08/0.98      | ~ v1_funct_2(X2,X0,X1)
% 3.08/0.98      | ~ v1_funct_2(X3,X1,X0)
% 3.08/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.08/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.08/0.98      | ~ v1_funct_1(X2)
% 3.08/0.98      | ~ v1_funct_1(X3)
% 3.08/0.98      | k2_relset_1(X1,X0,X3) = X0 ),
% 3.08/0.98      inference(cnf_transformation,[],[f67]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_509,plain,
% 3.08/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.08/0.98      | ~ v1_funct_2(X3,X2,X1)
% 3.08/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.08/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.08/0.98      | ~ v1_funct_1(X0)
% 3.08/0.98      | ~ v1_funct_1(X3)
% 3.08/0.98      | k1_partfun1(X2,X1,X1,X2,X3,X0) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 3.08/0.98      | k2_relset_1(X1,X2,X0) = X2
% 3.08/0.98      | k6_partfun1(X2) != k6_partfun1(sK1)
% 3.08/0.98      | sK1 != X2 ),
% 3.08/0.98      inference(resolution_lifted,[status(thm)],[c_20,c_24]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_510,plain,
% 3.08/0.98      ( ~ v1_funct_2(X0,X1,sK1)
% 3.08/0.98      | ~ v1_funct_2(X2,sK1,X1)
% 3.08/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
% 3.08/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
% 3.08/0.98      | ~ v1_funct_1(X0)
% 3.08/0.98      | ~ v1_funct_1(X2)
% 3.08/0.98      | k1_partfun1(sK1,X1,X1,sK1,X2,X0) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 3.08/0.98      | k2_relset_1(X1,sK1,X0) = sK1
% 3.08/0.98      | k6_partfun1(sK1) != k6_partfun1(sK1) ),
% 3.08/0.98      inference(unflattening,[status(thm)],[c_509]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_582,plain,
% 3.08/0.98      ( ~ v1_funct_2(X0,X1,sK1)
% 3.08/0.98      | ~ v1_funct_2(X2,sK1,X1)
% 3.08/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
% 3.08/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
% 3.08/0.98      | ~ v1_funct_1(X0)
% 3.08/0.98      | ~ v1_funct_1(X2)
% 3.08/0.98      | k1_partfun1(sK1,X1,X1,sK1,X2,X0) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 3.08/0.98      | k2_relset_1(X1,sK1,X0) = sK1 ),
% 3.08/0.98      inference(equality_resolution_simp,[status(thm)],[c_510]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_1049,plain,
% 3.08/0.98      ( k1_partfun1(sK1,X0,X0,sK1,X1,X2) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 3.08/0.98      | k2_relset_1(X0,sK1,X2) = sK1
% 3.08/0.98      | v1_funct_2(X2,X0,sK1) != iProver_top
% 3.08/0.98      | v1_funct_2(X1,sK1,X0) != iProver_top
% 3.08/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
% 3.08/0.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 3.08/0.98      | v1_funct_1(X2) != iProver_top
% 3.08/0.98      | v1_funct_1(X1) != iProver_top ),
% 3.08/0.98      inference(predicate_to_equality,[status(thm)],[c_582]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_1765,plain,
% 3.08/0.98      ( k2_relset_1(sK2,sK1,sK4) = sK1
% 3.08/0.98      | v1_funct_2(sK3,sK1,sK2) != iProver_top
% 3.08/0.98      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 3.08/0.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 3.08/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.08/0.98      | v1_funct_1(sK3) != iProver_top
% 3.08/0.98      | v1_funct_1(sK4) != iProver_top ),
% 3.08/0.98      inference(equality_resolution,[status(thm)],[c_1049]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_1836,plain,
% 3.08/0.98      ( k2_relset_1(sK2,sK1,sK4) = sK1 ),
% 3.08/0.98      inference(global_propositional_subsumption,
% 3.08/0.98                [status(thm)],
% 3.08/0.98                [c_1765,c_31,c_32,c_33,c_34,c_35,c_36]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_2102,plain,
% 3.08/0.98      ( k2_relat_1(sK4) = sK1 ),
% 3.08/0.98      inference(light_normalisation,[status(thm)],[c_2087,c_1836]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_8,plain,
% 3.08/0.98      ( v5_relat_1(X0,X1)
% 3.08/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.08/0.98      inference(cnf_transformation,[],[f54]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_16,plain,
% 3.08/0.98      ( v2_funct_2(X0,k2_relat_1(X0))
% 3.08/0.98      | ~ v5_relat_1(X0,k2_relat_1(X0))
% 3.08/0.98      | ~ v1_relat_1(X0) ),
% 3.08/0.98      inference(cnf_transformation,[],[f84]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_377,plain,
% 3.08/0.98      ( v2_funct_2(X0,k2_relat_1(X0))
% 3.08/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 3.08/0.98      | ~ v1_relat_1(X0)
% 3.08/0.98      | X0 != X1
% 3.08/0.98      | k2_relat_1(X0) != X3 ),
% 3.08/0.98      inference(resolution_lifted,[status(thm)],[c_8,c_16]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_378,plain,
% 3.08/0.98      ( v2_funct_2(X0,k2_relat_1(X0))
% 3.08/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
% 3.08/0.98      | ~ v1_relat_1(X0) ),
% 3.08/0.98      inference(unflattening,[status(thm)],[c_377]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_7,plain,
% 3.08/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.08/0.98      | v1_relat_1(X0) ),
% 3.08/0.98      inference(cnf_transformation,[],[f53]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_388,plain,
% 3.08/0.98      ( v2_funct_2(X0,k2_relat_1(X0))
% 3.08/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0)))) ),
% 3.08/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_378,c_7]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_23,negated_conjecture,
% 3.08/0.98      ( ~ v2_funct_2(sK4,sK1) | ~ v2_funct_1(sK3) ),
% 3.08/0.98      inference(cnf_transformation,[],[f77]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_403,plain,
% 3.08/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
% 3.08/0.98      | ~ v2_funct_1(sK3)
% 3.08/0.98      | k2_relat_1(X0) != sK1
% 3.08/0.98      | sK4 != X0 ),
% 3.08/0.98      inference(resolution_lifted,[status(thm)],[c_388,c_23]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_404,plain,
% 3.08/0.98      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK4))))
% 3.08/0.98      | ~ v2_funct_1(sK3)
% 3.08/0.98      | k2_relat_1(sK4) != sK1 ),
% 3.08/0.98      inference(unflattening,[status(thm)],[c_403]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_693,plain,
% 3.08/0.98      ( ~ v2_funct_1(sK3) | sP0_iProver_split | k2_relat_1(sK4) != sK1 ),
% 3.08/0.98      inference(splitting,
% 3.08/0.98                [splitting(split),new_symbols(definition,[])],
% 3.08/0.98                [c_404]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_1053,plain,
% 3.08/0.98      ( k2_relat_1(sK4) != sK1
% 3.08/0.98      | v2_funct_1(sK3) != iProver_top
% 3.08/0.98      | sP0_iProver_split = iProver_top ),
% 3.08/0.98      inference(predicate_to_equality,[status(thm)],[c_693]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_2241,plain,
% 3.08/0.98      ( sK1 != sK1
% 3.08/0.98      | v2_funct_1(sK3) != iProver_top
% 3.08/0.98      | sP0_iProver_split = iProver_top ),
% 3.08/0.98      inference(demodulation,[status(thm)],[c_2102,c_1053]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_2242,plain,
% 3.08/0.98      ( v2_funct_1(sK3) != iProver_top
% 3.08/0.98      | sP0_iProver_split = iProver_top ),
% 3.08/0.98      inference(equality_resolution_simp,[status(thm)],[c_2241]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_692,plain,
% 3.08/0.98      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK4))))
% 3.08/0.98      | ~ sP0_iProver_split ),
% 3.08/0.98      inference(splitting,
% 3.08/0.98                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 3.08/0.98                [c_404]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_1054,plain,
% 3.08/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK4)))) != iProver_top
% 3.08/0.98      | sP0_iProver_split != iProver_top ),
% 3.08/0.98      inference(predicate_to_equality,[status(thm)],[c_692]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_2240,plain,
% 3.08/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
% 3.08/0.98      | sP0_iProver_split != iProver_top ),
% 3.08/0.98      inference(demodulation,[status(thm)],[c_2102,c_1054]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_2258,plain,
% 3.08/0.98      ( sP0_iProver_split != iProver_top ),
% 3.08/0.98      inference(superposition,[status(thm)],[c_1060,c_2240]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_3086,plain,
% 3.08/0.98      ( v2_funct_1(k6_partfun1(sK1)) != iProver_top | sK1 = k1_xboole_0 ),
% 3.08/0.98      inference(global_propositional_subsumption,
% 3.08/0.98                [status(thm)],
% 3.08/0.98                [c_2951,c_31,c_32,c_33,c_34,c_35,c_36,c_2242,c_2258]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_3087,plain,
% 3.08/0.98      ( sK1 = k1_xboole_0 | v2_funct_1(k6_partfun1(sK1)) != iProver_top ),
% 3.08/0.98      inference(renaming,[status(thm)],[c_3086]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_6,plain,
% 3.08/0.98      ( v2_funct_1(k6_partfun1(X0)) ),
% 3.08/0.98      inference(cnf_transformation,[],[f79]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_1067,plain,
% 3.08/0.98      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 3.08/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_3092,plain,
% 3.08/0.98      ( sK1 = k1_xboole_0 ),
% 3.08/0.98      inference(forward_subsumption_resolution,
% 3.08/0.98                [status(thm)],
% 3.08/0.98                [c_3087,c_1067]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_1057,plain,
% 3.08/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.08/0.98      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_3100,plain,
% 3.08/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) = iProver_top ),
% 3.08/0.98      inference(demodulation,[status(thm)],[c_3092,c_1057]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_2,plain,
% 3.08/0.98      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.08/0.98      inference(cnf_transformation,[],[f82]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_3108,plain,
% 3.08/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.08/0.98      inference(demodulation,[status(thm)],[c_3100,c_2]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_696,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_1751,plain,
% 3.08/0.98      ( X0 != X1 | sK3 != X1 | sK3 = X0 ),
% 3.08/0.98      inference(instantiation,[status(thm)],[c_696]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_2451,plain,
% 3.08/0.98      ( X0 != sK3 | sK3 = X0 | sK3 != sK3 ),
% 3.08/0.98      inference(instantiation,[status(thm)],[c_1751]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_2452,plain,
% 3.08/0.98      ( sK3 != sK3 | sK3 = k1_xboole_0 | k1_xboole_0 != sK3 ),
% 3.08/0.98      inference(instantiation,[status(thm)],[c_2451]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_701,plain,
% 3.08/0.98      ( ~ v2_funct_1(X0) | v2_funct_1(X1) | X1 != X0 ),
% 3.08/0.98      theory(equality) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_2183,plain,
% 3.08/0.98      ( ~ v2_funct_1(X0) | v2_funct_1(sK3) | sK3 != X0 ),
% 3.08/0.98      inference(instantiation,[status(thm)],[c_701]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_2184,plain,
% 3.08/0.98      ( sK3 != X0
% 3.08/0.98      | v2_funct_1(X0) != iProver_top
% 3.08/0.98      | v2_funct_1(sK3) = iProver_top ),
% 3.08/0.98      inference(predicate_to_equality,[status(thm)],[c_2183]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_2186,plain,
% 3.08/0.98      ( sK3 != k1_xboole_0
% 3.08/0.98      | v2_funct_1(sK3) = iProver_top
% 3.08/0.98      | v2_funct_1(k1_xboole_0) != iProver_top ),
% 3.08/0.98      inference(instantiation,[status(thm)],[c_2184]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_1549,plain,
% 3.08/0.98      ( X0 != X1 | X0 = k6_partfun1(X2) | k6_partfun1(X2) != X1 ),
% 3.08/0.98      inference(instantiation,[status(thm)],[c_696]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_1550,plain,
% 3.08/0.98      ( k6_partfun1(k1_xboole_0) != k1_xboole_0
% 3.08/0.98      | k1_xboole_0 = k6_partfun1(k1_xboole_0)
% 3.08/0.98      | k1_xboole_0 != k1_xboole_0 ),
% 3.08/0.98      inference(instantiation,[status(thm)],[c_1549]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_695,plain,( X0 = X0 ),theory(equality) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_1431,plain,
% 3.08/0.98      ( sK3 = sK3 ),
% 3.08/0.98      inference(instantiation,[status(thm)],[c_695]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_0,plain,
% 3.08/0.98      ( v1_xboole_0(k1_xboole_0) ),
% 3.08/0.98      inference(cnf_transformation,[],[f46]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_4,plain,
% 3.08/0.98      ( ~ r2_hidden(X0,X1)
% 3.08/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 3.08/0.98      | ~ v1_xboole_0(X2) ),
% 3.08/0.98      inference(cnf_transformation,[],[f50]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_305,plain,
% 3.08/0.98      ( ~ r2_hidden(X0,X1)
% 3.08/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 3.08/0.98      | k1_xboole_0 != X2 ),
% 3.08/0.98      inference(resolution_lifted,[status(thm)],[c_0,c_4]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_306,plain,
% 3.08/0.98      ( ~ r2_hidden(X0,X1) | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
% 3.08/0.98      inference(unflattening,[status(thm)],[c_305]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_15,plain,
% 3.08/0.98      ( r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0 ),
% 3.08/0.98      inference(cnf_transformation,[],[f59]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_422,plain,
% 3.08/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
% 3.08/0.98      | X1 != X0
% 3.08/0.98      | sK0(X1) != X2
% 3.08/0.98      | k1_xboole_0 = X1 ),
% 3.08/0.98      inference(resolution_lifted,[status(thm)],[c_306,c_15]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_423,plain,
% 3.08/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0 ),
% 3.08/0.98      inference(unflattening,[status(thm)],[c_422]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_1423,plain,
% 3.08/0.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = sK3 ),
% 3.08/0.98      inference(instantiation,[status(thm)],[c_423]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_1426,plain,
% 3.08/0.98      ( k1_xboole_0 = sK3
% 3.08/0.98      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.08/0.98      inference(predicate_to_equality,[status(thm)],[c_1423]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_1271,plain,
% 3.08/0.98      ( v2_funct_1(X0)
% 3.08/0.98      | ~ v2_funct_1(k6_partfun1(X1))
% 3.08/0.98      | X0 != k6_partfun1(X1) ),
% 3.08/0.98      inference(instantiation,[status(thm)],[c_701]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_1272,plain,
% 3.08/0.98      ( X0 != k6_partfun1(X1)
% 3.08/0.98      | v2_funct_1(X0) = iProver_top
% 3.08/0.98      | v2_funct_1(k6_partfun1(X1)) != iProver_top ),
% 3.08/0.98      inference(predicate_to_equality,[status(thm)],[c_1271]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_1274,plain,
% 3.08/0.98      ( k1_xboole_0 != k6_partfun1(k1_xboole_0)
% 3.08/0.98      | v2_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top
% 3.08/0.98      | v2_funct_1(k1_xboole_0) = iProver_top ),
% 3.08/0.98      inference(instantiation,[status(thm)],[c_1272]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_92,plain,
% 3.08/0.98      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.08/0.98      inference(instantiation,[status(thm)],[c_2]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_3,plain,
% 3.08/0.98      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 3.08/0.98      | k1_xboole_0 = X1
% 3.08/0.98      | k1_xboole_0 = X0 ),
% 3.08/0.98      inference(cnf_transformation,[],[f47]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_91,plain,
% 3.08/0.98      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.08/0.98      | k1_xboole_0 = k1_xboole_0 ),
% 3.08/0.98      inference(instantiation,[status(thm)],[c_3]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_5,plain,
% 3.08/0.98      ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 3.08/0.98      inference(cnf_transformation,[],[f78]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_85,plain,
% 3.08/0.98      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 3.08/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(c_87,plain,
% 3.08/0.98      ( v2_funct_1(k6_partfun1(k1_xboole_0)) = iProver_top ),
% 3.08/0.98      inference(instantiation,[status(thm)],[c_85]) ).
% 3.08/0.98  
% 3.08/0.98  cnf(contradiction,plain,
% 3.08/0.98      ( $false ),
% 3.08/0.98      inference(minisat,
% 3.08/0.98                [status(thm)],
% 3.08/0.98                [c_3108,c_2452,c_2258,c_2242,c_2186,c_1550,c_1431,c_1426,
% 3.08/0.98                 c_1274,c_92,c_91,c_5,c_87]) ).
% 3.08/0.98  
% 3.08/0.98  
% 3.08/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.08/0.98  
% 3.08/0.98  ------                               Statistics
% 3.08/0.98  
% 3.08/0.98  ------ General
% 3.08/0.98  
% 3.08/0.98  abstr_ref_over_cycles:                  0
% 3.08/0.98  abstr_ref_under_cycles:                 0
% 3.08/0.98  gc_basic_clause_elim:                   0
% 3.08/0.98  forced_gc_time:                         0
% 3.08/0.98  parsing_time:                           0.01
% 3.08/0.98  unif_index_cands_time:                  0.
% 3.08/0.98  unif_index_add_time:                    0.
% 3.08/0.98  orderings_time:                         0.
% 3.08/0.98  out_proof_time:                         0.009
% 3.08/0.98  total_time:                             0.152
% 3.08/0.98  num_of_symbols:                         55
% 3.08/0.98  num_of_terms:                           4613
% 3.08/0.98  
% 3.08/0.98  ------ Preprocessing
% 3.08/0.98  
% 3.08/0.98  num_of_splits:                          1
% 3.08/0.98  num_of_split_atoms:                     1
% 3.08/0.98  num_of_reused_defs:                     0
% 3.08/0.98  num_eq_ax_congr_red:                    22
% 3.08/0.98  num_of_sem_filtered_clauses:            1
% 3.08/0.98  num_of_subtypes:                        0
% 3.08/0.98  monotx_restored_types:                  0
% 3.08/0.98  sat_num_of_epr_types:                   0
% 3.08/0.98  sat_num_of_non_cyclic_types:            0
% 3.08/0.98  sat_guarded_non_collapsed_types:        0
% 3.08/0.98  num_pure_diseq_elim:                    0
% 3.08/0.98  simp_replaced_by:                       0
% 3.08/0.98  res_preprocessed:                       132
% 3.08/0.98  prep_upred:                             0
% 3.08/0.98  prep_unflattend:                        24
% 3.08/0.98  smt_new_axioms:                         0
% 3.08/0.98  pred_elim_cands:                        4
% 3.08/0.98  pred_elim:                              6
% 3.08/0.98  pred_elim_cl:                           7
% 3.08/0.98  pred_elim_cycles:                       9
% 3.08/0.98  merged_defs:                            0
% 3.08/0.98  merged_defs_ncl:                        0
% 3.08/0.98  bin_hyper_res:                          0
% 3.08/0.98  prep_cycles:                            4
% 3.08/0.98  pred_elim_time:                         0.006
% 3.08/0.98  splitting_time:                         0.
% 3.08/0.98  sem_filter_time:                        0.
% 3.08/0.98  monotx_time:                            0.
% 3.08/0.98  subtype_inf_time:                       0.
% 3.08/0.98  
% 3.08/0.98  ------ Problem properties
% 3.08/0.98  
% 3.08/0.98  clauses:                                25
% 3.08/0.98  conjectures:                            6
% 3.08/0.98  epr:                                    4
% 3.08/0.98  horn:                                   23
% 3.08/0.98  ground:                                 9
% 3.08/0.98  unary:                                  11
% 3.08/0.98  binary:                                 6
% 3.08/0.98  lits:                                   72
% 3.08/0.98  lits_eq:                                19
% 3.08/0.98  fd_pure:                                0
% 3.08/0.98  fd_pseudo:                              0
% 3.08/0.98  fd_cond:                                5
% 3.08/0.98  fd_pseudo_cond:                         0
% 3.08/0.98  ac_symbols:                             0
% 3.08/0.98  
% 3.08/0.98  ------ Propositional Solver
% 3.08/0.98  
% 3.08/0.98  prop_solver_calls:                      26
% 3.08/0.98  prop_fast_solver_calls:                 930
% 3.08/0.98  smt_solver_calls:                       0
% 3.08/0.98  smt_fast_solver_calls:                  0
% 3.08/0.98  prop_num_of_clauses:                    1110
% 3.08/0.98  prop_preprocess_simplified:             4261
% 3.08/0.98  prop_fo_subsumed:                       22
% 3.08/0.98  prop_solver_time:                       0.
% 3.08/0.98  smt_solver_time:                        0.
% 3.08/0.98  smt_fast_solver_time:                   0.
% 3.08/0.98  prop_fast_solver_time:                  0.
% 3.08/0.98  prop_unsat_core_time:                   0.
% 3.08/0.98  
% 3.08/0.98  ------ QBF
% 3.08/0.98  
% 3.08/0.98  qbf_q_res:                              0
% 3.08/0.98  qbf_num_tautologies:                    0
% 3.08/0.98  qbf_prep_cycles:                        0
% 3.08/0.98  
% 3.08/0.98  ------ BMC1
% 3.08/0.98  
% 3.08/0.98  bmc1_current_bound:                     -1
% 3.08/0.98  bmc1_last_solved_bound:                 -1
% 3.08/0.98  bmc1_unsat_core_size:                   -1
% 3.08/0.98  bmc1_unsat_core_parents_size:           -1
% 3.08/0.98  bmc1_merge_next_fun:                    0
% 3.08/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.08/0.98  
% 3.08/0.98  ------ Instantiation
% 3.08/0.98  
% 3.08/0.98  inst_num_of_clauses:                    384
% 3.08/0.98  inst_num_in_passive:                    163
% 3.08/0.98  inst_num_in_active:                     203
% 3.08/0.98  inst_num_in_unprocessed:                18
% 3.08/0.98  inst_num_of_loops:                      210
% 3.08/0.98  inst_num_of_learning_restarts:          0
% 3.08/0.98  inst_num_moves_active_passive:          4
% 3.08/0.98  inst_lit_activity:                      0
% 3.08/0.98  inst_lit_activity_moves:                0
% 3.08/0.98  inst_num_tautologies:                   0
% 3.08/0.98  inst_num_prop_implied:                  0
% 3.08/0.98  inst_num_existing_simplified:           0
% 3.08/0.98  inst_num_eq_res_simplified:             0
% 3.08/0.98  inst_num_child_elim:                    0
% 3.08/0.98  inst_num_of_dismatching_blockings:      11
% 3.08/0.98  inst_num_of_non_proper_insts:           235
% 3.08/0.98  inst_num_of_duplicates:                 0
% 3.08/0.98  inst_inst_num_from_inst_to_res:         0
% 3.08/0.98  inst_dismatching_checking_time:         0.
% 3.08/0.98  
% 3.08/0.98  ------ Resolution
% 3.08/0.98  
% 3.08/0.98  res_num_of_clauses:                     0
% 3.08/0.98  res_num_in_passive:                     0
% 3.08/0.98  res_num_in_active:                      0
% 3.08/0.98  res_num_of_loops:                       136
% 3.08/0.98  res_forward_subset_subsumed:            14
% 3.08/0.98  res_backward_subset_subsumed:           0
% 3.08/0.98  res_forward_subsumed:                   0
% 3.08/0.98  res_backward_subsumed:                  0
% 3.08/0.98  res_forward_subsumption_resolution:     4
% 3.08/0.98  res_backward_subsumption_resolution:    0
% 3.08/0.98  res_clause_to_clause_subsumption:       108
% 3.08/0.98  res_orphan_elimination:                 0
% 3.08/0.98  res_tautology_del:                      17
% 3.08/0.98  res_num_eq_res_simplified:              1
% 3.08/0.98  res_num_sel_changes:                    0
% 3.08/0.98  res_moves_from_active_to_pass:          0
% 3.08/0.98  
% 3.08/0.98  ------ Superposition
% 3.08/0.98  
% 3.08/0.98  sup_time_total:                         0.
% 3.08/0.98  sup_time_generating:                    0.
% 3.08/0.98  sup_time_sim_full:                      0.
% 3.08/0.98  sup_time_sim_immed:                     0.
% 3.08/0.98  
% 3.08/0.98  sup_num_of_clauses:                     45
% 3.08/0.98  sup_num_in_active:                      25
% 3.08/0.98  sup_num_in_passive:                     20
% 3.08/0.98  sup_num_of_loops:                       40
% 3.08/0.98  sup_fw_superposition:                   19
% 3.08/0.98  sup_bw_superposition:                   13
% 3.08/0.98  sup_immediate_simplified:               11
% 3.08/0.98  sup_given_eliminated:                   1
% 3.08/0.98  comparisons_done:                       0
% 3.08/0.98  comparisons_avoided:                    0
% 3.08/0.98  
% 3.08/0.98  ------ Simplifications
% 3.08/0.98  
% 3.08/0.98  
% 3.08/0.98  sim_fw_subset_subsumed:                 0
% 3.08/0.98  sim_bw_subset_subsumed:                 0
% 3.08/0.98  sim_fw_subsumed:                        1
% 3.08/0.98  sim_bw_subsumed:                        1
% 3.08/0.98  sim_fw_subsumption_res:                 1
% 3.08/0.98  sim_bw_subsumption_res:                 0
% 3.08/0.98  sim_tautology_del:                      0
% 3.08/0.98  sim_eq_tautology_del:                   3
% 3.08/0.98  sim_eq_res_simp:                        1
% 3.08/0.98  sim_fw_demodulated:                     6
% 3.08/0.98  sim_bw_demodulated:                     14
% 3.08/0.98  sim_light_normalised:                   5
% 3.08/0.98  sim_joinable_taut:                      0
% 3.08/0.98  sim_joinable_simp:                      0
% 3.08/0.98  sim_ac_normalised:                      0
% 3.08/0.98  sim_smt_subsumption:                    0
% 3.08/0.98  
%------------------------------------------------------------------------------
