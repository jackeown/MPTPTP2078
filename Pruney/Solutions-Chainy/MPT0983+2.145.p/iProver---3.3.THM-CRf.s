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
% DateTime   : Thu Dec  3 12:02:16 EST 2020

% Result     : Theorem 3.05s
% Output     : CNFRefutation 3.05s
% Verified   : 
% Statistics : Number of formulae       :  174 ( 498 expanded)
%              Number of clauses        :  105 ( 170 expanded)
%              Number of leaves         :   23 ( 122 expanded)
%              Depth                    :   18
%              Number of atoms          :  591 (3089 expanded)
%              Number of equality atoms :  191 ( 271 expanded)
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

fof(f57,plain,(
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

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

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

fof(f40,plain,(
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

fof(f39,plain,
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

fof(f41,plain,
    ( ( ~ v2_funct_2(sK3,sK0)
      | ~ v2_funct_1(sK2) )
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f36,f40,f39])).

fof(f68,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f41])).

fof(f11,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f11])).

fof(f14,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f72,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f53,f58])).

fof(f62,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f64,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f41])).

fof(f65,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f67,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f41])).

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

fof(f60,plain,(
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

fof(f63,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f66,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f6,axiom,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f71,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f47,f58])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f5,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f70,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f46,f58])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

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

fof(f50,plain,(
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

fof(f59,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f48,plain,(
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

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f74,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f55])).

fof(f69,plain,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_640,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
    | ~ m1_subset_1(X3_48,k1_zfmisc_1(k2_zfmisc_1(X4_48,X5_48)))
    | m1_subset_1(k1_partfun1(X4_48,X5_48,X1_48,X2_48,X3_48,X0_48),k1_zfmisc_1(k2_zfmisc_1(X4_48,X2_48)))
    | ~ v1_funct_1(X0_48)
    | ~ v1_funct_1(X3_48) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1105,plain,
    ( m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48))) != iProver_top
    | m1_subset_1(X3_48,k1_zfmisc_1(k2_zfmisc_1(X4_48,X5_48))) != iProver_top
    | m1_subset_1(k1_partfun1(X4_48,X5_48,X1_48,X2_48,X3_48,X0_48),k1_zfmisc_1(k2_zfmisc_1(X4_48,X2_48))) = iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(X3_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_640])).

cnf(c_10,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_20,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_407,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_20])).

cnf(c_408,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_407])).

cnf(c_11,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_416,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_408,c_11])).

cnf(c_628,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_416])).

cnf(c_1118,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_628])).

cnf(c_2147,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1105,c_1118])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_27,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_29,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_23,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_30,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_32,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3243,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2147,c_27,c_29,c_30,c_32])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | ~ v2_funct_1(k1_partfun1(X1,X2,X2,X4,X0,X3))
    | k1_xboole_0 = X4 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_637,plain,
    ( ~ v1_funct_2(X0_48,X1_48,X2_48)
    | ~ v1_funct_2(X3_48,X2_48,X4_48)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
    | ~ m1_subset_1(X3_48,k1_zfmisc_1(k2_zfmisc_1(X2_48,X4_48)))
    | ~ v1_funct_1(X0_48)
    | ~ v1_funct_1(X3_48)
    | v2_funct_1(X0_48)
    | ~ v2_funct_1(k1_partfun1(X1_48,X2_48,X2_48,X4_48,X0_48,X3_48))
    | k1_xboole_0 = X4_48 ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1108,plain,
    ( k1_xboole_0 = X0_48
    | v1_funct_2(X1_48,X2_48,X3_48) != iProver_top
    | v1_funct_2(X4_48,X3_48,X0_48) != iProver_top
    | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_48,X3_48))) != iProver_top
    | m1_subset_1(X4_48,k1_zfmisc_1(k2_zfmisc_1(X3_48,X0_48))) != iProver_top
    | v1_funct_1(X1_48) != iProver_top
    | v1_funct_1(X4_48) != iProver_top
    | v2_funct_1(X1_48) = iProver_top
    | v2_funct_1(k1_partfun1(X2_48,X3_48,X3_48,X0_48,X1_48,X4_48)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_637])).

cnf(c_3269,plain,
    ( sK0 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3243,c_1108])).

cnf(c_25,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_28,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_22,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_31,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_5,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_72,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_74,plain,
    ( v2_funct_1(k6_partfun1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_72])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_653,plain,
    ( X0_48 = X0_48 ),
    theory(equality)).

cnf(c_681,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_653])).

cnf(c_4,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_645,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_662,plain,
    ( ~ v2_funct_1(X0_48)
    | v2_funct_1(X1_48)
    | X1_48 != X0_48 ),
    theory(equality)).

cnf(c_1337,plain,
    ( v2_funct_1(X0_48)
    | ~ v2_funct_1(k6_partfun1(X1_48))
    | X0_48 != k6_partfun1(X1_48) ),
    inference(instantiation,[status(thm)],[c_662])).

cnf(c_1338,plain,
    ( X0_48 != k6_partfun1(X1_48)
    | v2_funct_1(X0_48) = iProver_top
    | v2_funct_1(k6_partfun1(X1_48)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1337])).

cnf(c_1340,plain,
    ( k1_xboole_0 != k6_partfun1(k1_xboole_0)
    | v2_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top
    | v2_funct_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1338])).

cnf(c_655,plain,
    ( X0_48 != X1_48
    | X2_48 != X1_48
    | X2_48 = X0_48 ),
    theory(equality)).

cnf(c_1607,plain,
    ( X0_48 != X1_48
    | X0_48 = k6_partfun1(X2_48)
    | k6_partfun1(X2_48) != X1_48 ),
    inference(instantiation,[status(thm)],[c_655])).

cnf(c_1608,plain,
    ( k6_partfun1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k6_partfun1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1607])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_647,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(X1_48))
    | ~ v1_relat_1(X1_48)
    | v1_relat_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1332,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
    | v1_relat_1(X0_48)
    | ~ v1_relat_1(k2_zfmisc_1(X1_48,X2_48)) ),
    inference(instantiation,[status(thm)],[c_647])).

cnf(c_1612,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1332])).

cnf(c_1613,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1612])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_648,plain,
    ( ~ v1_xboole_0(X0_48)
    | ~ v1_xboole_0(X1_48)
    | X1_48 = X0_48 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1754,plain,
    ( ~ v1_xboole_0(X0_48)
    | ~ v1_xboole_0(sK2)
    | sK2 = X0_48 ),
    inference(instantiation,[status(thm)],[c_648])).

cnf(c_1756,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK2 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1754])).

cnf(c_3,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_646,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_48,X1_48)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1870,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_646])).

cnf(c_1871,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1870])).

cnf(c_1998,plain,
    ( ~ v2_funct_1(X0_48)
    | v2_funct_1(sK2)
    | sK2 != X0_48 ),
    inference(instantiation,[status(thm)],[c_662])).

cnf(c_1999,plain,
    ( sK2 != X0_48
    | v2_funct_1(X0_48) != iProver_top
    | v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1998])).

cnf(c_2001,plain,
    ( sK2 != k1_xboole_0
    | v2_funct_1(sK2) = iProver_top
    | v2_funct_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1999])).

cnf(c_633,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_1112,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_633])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_643,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
    | ~ v1_xboole_0(X1_48)
    | v1_xboole_0(X0_48) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1102,plain,
    ( m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48))) != iProver_top
    | v1_xboole_0(X1_48) != iProver_top
    | v1_xboole_0(X0_48) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_643])).

cnf(c_2073,plain,
    ( v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1112,c_1102])).

cnf(c_2089,plain,
    ( v1_xboole_0(sK2)
    | ~ v1_xboole_0(sK0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2073])).

cnf(c_656,plain,
    ( ~ v1_xboole_0(X0_48)
    | v1_xboole_0(X1_48)
    | X1_48 != X0_48 ),
    theory(equality)).

cnf(c_2267,plain,
    ( ~ v1_xboole_0(X0_48)
    | v1_xboole_0(sK0)
    | sK0 != X0_48 ),
    inference(instantiation,[status(thm)],[c_656])).

cnf(c_2269,plain,
    ( v1_xboole_0(sK0)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2267])).

cnf(c_636,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1109,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_636])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_642,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
    | k2_relset_1(X1_48,X2_48,X0_48) = k2_relat_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1103,plain,
    ( k2_relset_1(X0_48,X1_48,X2_48) = k2_relat_1(X2_48)
    | m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_642])).

cnf(c_2036,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1109,c_1103])).

cnf(c_16,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_420,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k1_partfun1(X1,X2,X2,X1,X0,X3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X2,X1,X3) = X1
    | k6_partfun1(X1) != k6_partfun1(sK0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_20])).

cnf(c_421,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X0)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0
    | k6_partfun1(sK0) != k6_partfun1(sK0) ),
    inference(unflattening,[status(thm)],[c_420])).

cnf(c_497,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_421])).

cnf(c_627,plain,
    ( ~ v1_funct_2(X0_48,X1_48,sK0)
    | ~ v1_funct_2(X2_48,sK0,X1_48)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,sK0)))
    | ~ m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(sK0,X1_48)))
    | ~ v1_funct_1(X0_48)
    | ~ v1_funct_1(X2_48)
    | k1_partfun1(sK0,X1_48,X1_48,sK0,X2_48,X0_48) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1_48,sK0,X0_48) = sK0 ),
    inference(subtyping,[status(esa)],[c_497])).

cnf(c_1119,plain,
    ( k1_partfun1(sK0,X0_48,X0_48,sK0,X1_48,X2_48) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X0_48,sK0,X2_48) = sK0
    | v1_funct_2(X2_48,X0_48,sK0) != iProver_top
    | v1_funct_2(X1_48,sK0,X0_48) != iProver_top
    | m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(X0_48,sK0))) != iProver_top
    | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_48))) != iProver_top
    | v1_funct_1(X2_48) != iProver_top
    | v1_funct_1(X1_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_627])).

cnf(c_1848,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1119])).

cnf(c_1851,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1848,c_27,c_28,c_29,c_30,c_31,c_32])).

cnf(c_2047,plain,
    ( k2_relat_1(sK3) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_2036,c_1851])).

cnf(c_6,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_12,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_19,negated_conjecture,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_326,plain,
    ( ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) != sK0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_19])).

cnf(c_327,plain,
    ( ~ v5_relat_1(sK3,k2_relat_1(sK3))
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(sK3) != sK0 ),
    inference(unflattening,[status(thm)],[c_326])).

cnf(c_347,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(sK3) != X2
    | k2_relat_1(sK3) != sK0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_327])).

cnf(c_348,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3))))
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(sK3) != sK0 ),
    inference(unflattening,[status(thm)],[c_347])).

cnf(c_630,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_48,k2_relat_1(sK3))))
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(sK3) != sK0 ),
    inference(subtyping,[status(esa)],[c_348])).

cnf(c_651,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | sP0_iProver_split
    | k2_relat_1(sK3) != sK0 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_630])).

cnf(c_1115,plain,
    ( k2_relat_1(sK3) != sK0
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_651])).

cnf(c_2380,plain,
    ( sK0 != sK0
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(demodulation,[status(thm)],[c_2047,c_1115])).

cnf(c_2386,plain,
    ( v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2380])).

cnf(c_650,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_48,k2_relat_1(sK3))))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_630])).

cnf(c_1116,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_48,k2_relat_1(sK3)))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_650])).

cnf(c_2381,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_48,sK0))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(demodulation,[status(thm)],[c_2047,c_1116])).

cnf(c_2400,plain,
    ( sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_1109,c_2381])).

cnf(c_3377,plain,
    ( v2_funct_1(k6_partfun1(sK0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3269,c_27,c_28,c_29,c_30,c_31,c_32,c_74,c_0,c_681,c_645,c_1340,c_1608,c_1613,c_1756,c_1871,c_2001,c_2089,c_2269,c_2386,c_2400])).

cnf(c_644,plain,
    ( v2_funct_1(k6_partfun1(X0_48)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1101,plain,
    ( v2_funct_1(k6_partfun1(X0_48)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_644])).

cnf(c_3382,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3377,c_1101])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:56:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 3.05/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.05/1.00  
% 3.05/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.05/1.00  
% 3.05/1.00  ------  iProver source info
% 3.05/1.00  
% 3.05/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.05/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.05/1.00  git: non_committed_changes: false
% 3.05/1.00  git: last_make_outside_of_git: false
% 3.05/1.00  
% 3.05/1.00  ------ 
% 3.05/1.00  
% 3.05/1.00  ------ Input Options
% 3.05/1.00  
% 3.05/1.00  --out_options                           all
% 3.05/1.00  --tptp_safe_out                         true
% 3.05/1.00  --problem_path                          ""
% 3.05/1.00  --include_path                          ""
% 3.05/1.00  --clausifier                            res/vclausify_rel
% 3.05/1.00  --clausifier_options                    --mode clausify
% 3.05/1.00  --stdin                                 false
% 3.05/1.00  --stats_out                             all
% 3.05/1.00  
% 3.05/1.00  ------ General Options
% 3.05/1.00  
% 3.05/1.00  --fof                                   false
% 3.05/1.00  --time_out_real                         305.
% 3.05/1.00  --time_out_virtual                      -1.
% 3.05/1.00  --symbol_type_check                     false
% 3.05/1.00  --clausify_out                          false
% 3.05/1.00  --sig_cnt_out                           false
% 3.05/1.00  --trig_cnt_out                          false
% 3.05/1.00  --trig_cnt_out_tolerance                1.
% 3.05/1.00  --trig_cnt_out_sk_spl                   false
% 3.05/1.00  --abstr_cl_out                          false
% 3.05/1.00  
% 3.05/1.00  ------ Global Options
% 3.05/1.00  
% 3.05/1.00  --schedule                              default
% 3.05/1.00  --add_important_lit                     false
% 3.05/1.00  --prop_solver_per_cl                    1000
% 3.05/1.00  --min_unsat_core                        false
% 3.05/1.00  --soft_assumptions                      false
% 3.05/1.00  --soft_lemma_size                       3
% 3.05/1.00  --prop_impl_unit_size                   0
% 3.05/1.00  --prop_impl_unit                        []
% 3.05/1.00  --share_sel_clauses                     true
% 3.05/1.00  --reset_solvers                         false
% 3.05/1.00  --bc_imp_inh                            [conj_cone]
% 3.05/1.00  --conj_cone_tolerance                   3.
% 3.05/1.00  --extra_neg_conj                        none
% 3.05/1.00  --large_theory_mode                     true
% 3.05/1.00  --prolific_symb_bound                   200
% 3.05/1.00  --lt_threshold                          2000
% 3.05/1.00  --clause_weak_htbl                      true
% 3.05/1.00  --gc_record_bc_elim                     false
% 3.05/1.00  
% 3.05/1.00  ------ Preprocessing Options
% 3.05/1.00  
% 3.05/1.00  --preprocessing_flag                    true
% 3.05/1.00  --time_out_prep_mult                    0.1
% 3.05/1.00  --splitting_mode                        input
% 3.05/1.00  --splitting_grd                         true
% 3.05/1.00  --splitting_cvd                         false
% 3.05/1.00  --splitting_cvd_svl                     false
% 3.05/1.00  --splitting_nvd                         32
% 3.05/1.00  --sub_typing                            true
% 3.05/1.00  --prep_gs_sim                           true
% 3.05/1.00  --prep_unflatten                        true
% 3.05/1.00  --prep_res_sim                          true
% 3.05/1.00  --prep_upred                            true
% 3.05/1.00  --prep_sem_filter                       exhaustive
% 3.05/1.00  --prep_sem_filter_out                   false
% 3.05/1.00  --pred_elim                             true
% 3.05/1.00  --res_sim_input                         true
% 3.05/1.00  --eq_ax_congr_red                       true
% 3.05/1.00  --pure_diseq_elim                       true
% 3.05/1.00  --brand_transform                       false
% 3.05/1.00  --non_eq_to_eq                          false
% 3.05/1.00  --prep_def_merge                        true
% 3.05/1.00  --prep_def_merge_prop_impl              false
% 3.05/1.00  --prep_def_merge_mbd                    true
% 3.05/1.00  --prep_def_merge_tr_red                 false
% 3.05/1.00  --prep_def_merge_tr_cl                  false
% 3.05/1.00  --smt_preprocessing                     true
% 3.05/1.00  --smt_ac_axioms                         fast
% 3.05/1.00  --preprocessed_out                      false
% 3.05/1.00  --preprocessed_stats                    false
% 3.05/1.00  
% 3.05/1.00  ------ Abstraction refinement Options
% 3.05/1.00  
% 3.05/1.00  --abstr_ref                             []
% 3.05/1.00  --abstr_ref_prep                        false
% 3.05/1.00  --abstr_ref_until_sat                   false
% 3.05/1.00  --abstr_ref_sig_restrict                funpre
% 3.05/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.05/1.00  --abstr_ref_under                       []
% 3.05/1.00  
% 3.05/1.00  ------ SAT Options
% 3.05/1.00  
% 3.05/1.00  --sat_mode                              false
% 3.05/1.00  --sat_fm_restart_options                ""
% 3.05/1.00  --sat_gr_def                            false
% 3.05/1.00  --sat_epr_types                         true
% 3.05/1.00  --sat_non_cyclic_types                  false
% 3.05/1.00  --sat_finite_models                     false
% 3.05/1.00  --sat_fm_lemmas                         false
% 3.05/1.00  --sat_fm_prep                           false
% 3.05/1.00  --sat_fm_uc_incr                        true
% 3.05/1.00  --sat_out_model                         small
% 3.05/1.00  --sat_out_clauses                       false
% 3.05/1.00  
% 3.05/1.00  ------ QBF Options
% 3.05/1.00  
% 3.05/1.00  --qbf_mode                              false
% 3.05/1.00  --qbf_elim_univ                         false
% 3.05/1.00  --qbf_dom_inst                          none
% 3.05/1.00  --qbf_dom_pre_inst                      false
% 3.05/1.00  --qbf_sk_in                             false
% 3.05/1.00  --qbf_pred_elim                         true
% 3.05/1.00  --qbf_split                             512
% 3.05/1.00  
% 3.05/1.00  ------ BMC1 Options
% 3.05/1.00  
% 3.05/1.00  --bmc1_incremental                      false
% 3.05/1.00  --bmc1_axioms                           reachable_all
% 3.05/1.00  --bmc1_min_bound                        0
% 3.05/1.00  --bmc1_max_bound                        -1
% 3.05/1.00  --bmc1_max_bound_default                -1
% 3.05/1.00  --bmc1_symbol_reachability              true
% 3.05/1.00  --bmc1_property_lemmas                  false
% 3.05/1.00  --bmc1_k_induction                      false
% 3.05/1.00  --bmc1_non_equiv_states                 false
% 3.05/1.00  --bmc1_deadlock                         false
% 3.05/1.00  --bmc1_ucm                              false
% 3.05/1.00  --bmc1_add_unsat_core                   none
% 3.05/1.00  --bmc1_unsat_core_children              false
% 3.05/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.05/1.00  --bmc1_out_stat                         full
% 3.05/1.00  --bmc1_ground_init                      false
% 3.05/1.00  --bmc1_pre_inst_next_state              false
% 3.05/1.00  --bmc1_pre_inst_state                   false
% 3.05/1.00  --bmc1_pre_inst_reach_state             false
% 3.05/1.00  --bmc1_out_unsat_core                   false
% 3.05/1.00  --bmc1_aig_witness_out                  false
% 3.05/1.00  --bmc1_verbose                          false
% 3.05/1.00  --bmc1_dump_clauses_tptp                false
% 3.05/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.05/1.00  --bmc1_dump_file                        -
% 3.05/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.05/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.05/1.00  --bmc1_ucm_extend_mode                  1
% 3.05/1.00  --bmc1_ucm_init_mode                    2
% 3.05/1.00  --bmc1_ucm_cone_mode                    none
% 3.05/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.05/1.00  --bmc1_ucm_relax_model                  4
% 3.05/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.05/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.05/1.00  --bmc1_ucm_layered_model                none
% 3.05/1.00  --bmc1_ucm_max_lemma_size               10
% 3.05/1.00  
% 3.05/1.00  ------ AIG Options
% 3.05/1.00  
% 3.05/1.00  --aig_mode                              false
% 3.05/1.00  
% 3.05/1.00  ------ Instantiation Options
% 3.05/1.00  
% 3.05/1.00  --instantiation_flag                    true
% 3.05/1.00  --inst_sos_flag                         false
% 3.05/1.00  --inst_sos_phase                        true
% 3.05/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.05/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.05/1.00  --inst_lit_sel_side                     num_symb
% 3.05/1.00  --inst_solver_per_active                1400
% 3.05/1.00  --inst_solver_calls_frac                1.
% 3.05/1.00  --inst_passive_queue_type               priority_queues
% 3.05/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.05/1.00  --inst_passive_queues_freq              [25;2]
% 3.05/1.00  --inst_dismatching                      true
% 3.05/1.00  --inst_eager_unprocessed_to_passive     true
% 3.05/1.00  --inst_prop_sim_given                   true
% 3.05/1.00  --inst_prop_sim_new                     false
% 3.05/1.00  --inst_subs_new                         false
% 3.05/1.00  --inst_eq_res_simp                      false
% 3.05/1.00  --inst_subs_given                       false
% 3.05/1.00  --inst_orphan_elimination               true
% 3.05/1.00  --inst_learning_loop_flag               true
% 3.05/1.00  --inst_learning_start                   3000
% 3.05/1.00  --inst_learning_factor                  2
% 3.05/1.00  --inst_start_prop_sim_after_learn       3
% 3.05/1.00  --inst_sel_renew                        solver
% 3.05/1.00  --inst_lit_activity_flag                true
% 3.05/1.00  --inst_restr_to_given                   false
% 3.05/1.00  --inst_activity_threshold               500
% 3.05/1.00  --inst_out_proof                        true
% 3.05/1.00  
% 3.05/1.00  ------ Resolution Options
% 3.05/1.00  
% 3.05/1.00  --resolution_flag                       true
% 3.05/1.00  --res_lit_sel                           adaptive
% 3.05/1.00  --res_lit_sel_side                      none
% 3.05/1.00  --res_ordering                          kbo
% 3.05/1.00  --res_to_prop_solver                    active
% 3.05/1.00  --res_prop_simpl_new                    false
% 3.05/1.00  --res_prop_simpl_given                  true
% 3.05/1.00  --res_passive_queue_type                priority_queues
% 3.05/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.05/1.00  --res_passive_queues_freq               [15;5]
% 3.05/1.00  --res_forward_subs                      full
% 3.05/1.00  --res_backward_subs                     full
% 3.05/1.00  --res_forward_subs_resolution           true
% 3.05/1.00  --res_backward_subs_resolution          true
% 3.05/1.00  --res_orphan_elimination                true
% 3.05/1.00  --res_time_limit                        2.
% 3.05/1.00  --res_out_proof                         true
% 3.05/1.00  
% 3.05/1.00  ------ Superposition Options
% 3.05/1.00  
% 3.05/1.00  --superposition_flag                    true
% 3.05/1.00  --sup_passive_queue_type                priority_queues
% 3.05/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.05/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.05/1.00  --demod_completeness_check              fast
% 3.05/1.00  --demod_use_ground                      true
% 3.05/1.00  --sup_to_prop_solver                    passive
% 3.05/1.00  --sup_prop_simpl_new                    true
% 3.05/1.00  --sup_prop_simpl_given                  true
% 3.05/1.00  --sup_fun_splitting                     false
% 3.05/1.00  --sup_smt_interval                      50000
% 3.05/1.00  
% 3.05/1.00  ------ Superposition Simplification Setup
% 3.05/1.00  
% 3.05/1.00  --sup_indices_passive                   []
% 3.05/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.05/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.05/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.05/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.05/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.05/1.00  --sup_full_bw                           [BwDemod]
% 3.05/1.00  --sup_immed_triv                        [TrivRules]
% 3.05/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.05/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.05/1.00  --sup_immed_bw_main                     []
% 3.05/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.05/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.05/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.05/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.05/1.00  
% 3.05/1.00  ------ Combination Options
% 3.05/1.00  
% 3.05/1.00  --comb_res_mult                         3
% 3.05/1.00  --comb_sup_mult                         2
% 3.05/1.00  --comb_inst_mult                        10
% 3.05/1.00  
% 3.05/1.00  ------ Debug Options
% 3.05/1.00  
% 3.05/1.00  --dbg_backtrace                         false
% 3.05/1.00  --dbg_dump_prop_clauses                 false
% 3.05/1.00  --dbg_dump_prop_clauses_file            -
% 3.05/1.00  --dbg_out_stat                          false
% 3.05/1.00  ------ Parsing...
% 3.05/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.05/1.00  
% 3.05/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.05/1.00  
% 3.05/1.00  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.05/1.00  
% 3.05/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.05/1.00  ------ Proving...
% 3.05/1.00  ------ Problem Properties 
% 3.05/1.00  
% 3.05/1.00  
% 3.05/1.00  clauses                                 24
% 3.05/1.00  conjectures                             6
% 3.05/1.00  EPR                                     6
% 3.05/1.00  Horn                                    23
% 3.05/1.00  unary                                   11
% 3.05/1.00  binary                                  3
% 3.05/1.00  lits                                    73
% 3.05/1.00  lits eq                                 10
% 3.05/1.00  fd_pure                                 0
% 3.05/1.00  fd_pseudo                               0
% 3.05/1.00  fd_cond                                 1
% 3.05/1.00  fd_pseudo_cond                          1
% 3.05/1.00  AC symbols                              0
% 3.05/1.00  
% 3.05/1.00  ------ Schedule dynamic 5 is on 
% 3.05/1.00  
% 3.05/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.05/1.00  
% 3.05/1.00  
% 3.05/1.00  ------ 
% 3.05/1.00  Current options:
% 3.05/1.00  ------ 
% 3.05/1.00  
% 3.05/1.00  ------ Input Options
% 3.05/1.00  
% 3.05/1.00  --out_options                           all
% 3.05/1.00  --tptp_safe_out                         true
% 3.05/1.00  --problem_path                          ""
% 3.05/1.00  --include_path                          ""
% 3.05/1.00  --clausifier                            res/vclausify_rel
% 3.05/1.00  --clausifier_options                    --mode clausify
% 3.05/1.00  --stdin                                 false
% 3.05/1.00  --stats_out                             all
% 3.05/1.00  
% 3.05/1.00  ------ General Options
% 3.05/1.00  
% 3.05/1.00  --fof                                   false
% 3.05/1.00  --time_out_real                         305.
% 3.05/1.00  --time_out_virtual                      -1.
% 3.05/1.00  --symbol_type_check                     false
% 3.05/1.00  --clausify_out                          false
% 3.05/1.00  --sig_cnt_out                           false
% 3.05/1.00  --trig_cnt_out                          false
% 3.05/1.00  --trig_cnt_out_tolerance                1.
% 3.05/1.00  --trig_cnt_out_sk_spl                   false
% 3.05/1.00  --abstr_cl_out                          false
% 3.05/1.00  
% 3.05/1.00  ------ Global Options
% 3.05/1.00  
% 3.05/1.00  --schedule                              default
% 3.05/1.00  --add_important_lit                     false
% 3.05/1.00  --prop_solver_per_cl                    1000
% 3.05/1.00  --min_unsat_core                        false
% 3.05/1.00  --soft_assumptions                      false
% 3.05/1.00  --soft_lemma_size                       3
% 3.05/1.00  --prop_impl_unit_size                   0
% 3.05/1.00  --prop_impl_unit                        []
% 3.05/1.00  --share_sel_clauses                     true
% 3.05/1.00  --reset_solvers                         false
% 3.05/1.00  --bc_imp_inh                            [conj_cone]
% 3.05/1.00  --conj_cone_tolerance                   3.
% 3.05/1.00  --extra_neg_conj                        none
% 3.05/1.00  --large_theory_mode                     true
% 3.05/1.00  --prolific_symb_bound                   200
% 3.05/1.00  --lt_threshold                          2000
% 3.05/1.00  --clause_weak_htbl                      true
% 3.05/1.00  --gc_record_bc_elim                     false
% 3.05/1.00  
% 3.05/1.00  ------ Preprocessing Options
% 3.05/1.00  
% 3.05/1.00  --preprocessing_flag                    true
% 3.05/1.00  --time_out_prep_mult                    0.1
% 3.05/1.00  --splitting_mode                        input
% 3.05/1.00  --splitting_grd                         true
% 3.05/1.00  --splitting_cvd                         false
% 3.05/1.00  --splitting_cvd_svl                     false
% 3.05/1.00  --splitting_nvd                         32
% 3.05/1.00  --sub_typing                            true
% 3.05/1.00  --prep_gs_sim                           true
% 3.05/1.00  --prep_unflatten                        true
% 3.05/1.00  --prep_res_sim                          true
% 3.05/1.00  --prep_upred                            true
% 3.05/1.00  --prep_sem_filter                       exhaustive
% 3.05/1.00  --prep_sem_filter_out                   false
% 3.05/1.00  --pred_elim                             true
% 3.05/1.00  --res_sim_input                         true
% 3.05/1.00  --eq_ax_congr_red                       true
% 3.05/1.00  --pure_diseq_elim                       true
% 3.05/1.00  --brand_transform                       false
% 3.05/1.00  --non_eq_to_eq                          false
% 3.05/1.00  --prep_def_merge                        true
% 3.05/1.00  --prep_def_merge_prop_impl              false
% 3.05/1.00  --prep_def_merge_mbd                    true
% 3.05/1.00  --prep_def_merge_tr_red                 false
% 3.05/1.00  --prep_def_merge_tr_cl                  false
% 3.05/1.00  --smt_preprocessing                     true
% 3.05/1.00  --smt_ac_axioms                         fast
% 3.05/1.00  --preprocessed_out                      false
% 3.05/1.00  --preprocessed_stats                    false
% 3.05/1.00  
% 3.05/1.00  ------ Abstraction refinement Options
% 3.05/1.00  
% 3.05/1.00  --abstr_ref                             []
% 3.05/1.00  --abstr_ref_prep                        false
% 3.05/1.00  --abstr_ref_until_sat                   false
% 3.05/1.00  --abstr_ref_sig_restrict                funpre
% 3.05/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.05/1.00  --abstr_ref_under                       []
% 3.05/1.00  
% 3.05/1.00  ------ SAT Options
% 3.05/1.00  
% 3.05/1.00  --sat_mode                              false
% 3.05/1.00  --sat_fm_restart_options                ""
% 3.05/1.00  --sat_gr_def                            false
% 3.05/1.00  --sat_epr_types                         true
% 3.05/1.00  --sat_non_cyclic_types                  false
% 3.05/1.00  --sat_finite_models                     false
% 3.05/1.00  --sat_fm_lemmas                         false
% 3.05/1.00  --sat_fm_prep                           false
% 3.05/1.00  --sat_fm_uc_incr                        true
% 3.05/1.00  --sat_out_model                         small
% 3.05/1.00  --sat_out_clauses                       false
% 3.05/1.00  
% 3.05/1.00  ------ QBF Options
% 3.05/1.00  
% 3.05/1.00  --qbf_mode                              false
% 3.05/1.00  --qbf_elim_univ                         false
% 3.05/1.00  --qbf_dom_inst                          none
% 3.05/1.00  --qbf_dom_pre_inst                      false
% 3.05/1.00  --qbf_sk_in                             false
% 3.05/1.00  --qbf_pred_elim                         true
% 3.05/1.00  --qbf_split                             512
% 3.05/1.00  
% 3.05/1.00  ------ BMC1 Options
% 3.05/1.00  
% 3.05/1.00  --bmc1_incremental                      false
% 3.05/1.00  --bmc1_axioms                           reachable_all
% 3.05/1.00  --bmc1_min_bound                        0
% 3.05/1.00  --bmc1_max_bound                        -1
% 3.05/1.00  --bmc1_max_bound_default                -1
% 3.05/1.00  --bmc1_symbol_reachability              true
% 3.05/1.00  --bmc1_property_lemmas                  false
% 3.05/1.00  --bmc1_k_induction                      false
% 3.05/1.00  --bmc1_non_equiv_states                 false
% 3.05/1.00  --bmc1_deadlock                         false
% 3.05/1.00  --bmc1_ucm                              false
% 3.05/1.00  --bmc1_add_unsat_core                   none
% 3.05/1.00  --bmc1_unsat_core_children              false
% 3.05/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.05/1.00  --bmc1_out_stat                         full
% 3.05/1.00  --bmc1_ground_init                      false
% 3.05/1.00  --bmc1_pre_inst_next_state              false
% 3.05/1.00  --bmc1_pre_inst_state                   false
% 3.05/1.00  --bmc1_pre_inst_reach_state             false
% 3.05/1.00  --bmc1_out_unsat_core                   false
% 3.05/1.00  --bmc1_aig_witness_out                  false
% 3.05/1.00  --bmc1_verbose                          false
% 3.05/1.00  --bmc1_dump_clauses_tptp                false
% 3.05/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.05/1.00  --bmc1_dump_file                        -
% 3.05/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.05/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.05/1.00  --bmc1_ucm_extend_mode                  1
% 3.05/1.00  --bmc1_ucm_init_mode                    2
% 3.05/1.00  --bmc1_ucm_cone_mode                    none
% 3.05/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.05/1.00  --bmc1_ucm_relax_model                  4
% 3.05/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.05/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.05/1.00  --bmc1_ucm_layered_model                none
% 3.05/1.00  --bmc1_ucm_max_lemma_size               10
% 3.05/1.00  
% 3.05/1.00  ------ AIG Options
% 3.05/1.00  
% 3.05/1.00  --aig_mode                              false
% 3.05/1.00  
% 3.05/1.00  ------ Instantiation Options
% 3.05/1.00  
% 3.05/1.00  --instantiation_flag                    true
% 3.05/1.00  --inst_sos_flag                         false
% 3.05/1.00  --inst_sos_phase                        true
% 3.05/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.05/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.05/1.00  --inst_lit_sel_side                     none
% 3.05/1.00  --inst_solver_per_active                1400
% 3.05/1.00  --inst_solver_calls_frac                1.
% 3.05/1.00  --inst_passive_queue_type               priority_queues
% 3.05/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.05/1.00  --inst_passive_queues_freq              [25;2]
% 3.05/1.00  --inst_dismatching                      true
% 3.05/1.00  --inst_eager_unprocessed_to_passive     true
% 3.05/1.00  --inst_prop_sim_given                   true
% 3.05/1.00  --inst_prop_sim_new                     false
% 3.05/1.00  --inst_subs_new                         false
% 3.05/1.00  --inst_eq_res_simp                      false
% 3.05/1.00  --inst_subs_given                       false
% 3.05/1.00  --inst_orphan_elimination               true
% 3.05/1.00  --inst_learning_loop_flag               true
% 3.05/1.00  --inst_learning_start                   3000
% 3.05/1.00  --inst_learning_factor                  2
% 3.05/1.00  --inst_start_prop_sim_after_learn       3
% 3.05/1.00  --inst_sel_renew                        solver
% 3.05/1.00  --inst_lit_activity_flag                true
% 3.05/1.00  --inst_restr_to_given                   false
% 3.05/1.00  --inst_activity_threshold               500
% 3.05/1.00  --inst_out_proof                        true
% 3.05/1.00  
% 3.05/1.00  ------ Resolution Options
% 3.05/1.00  
% 3.05/1.00  --resolution_flag                       false
% 3.05/1.00  --res_lit_sel                           adaptive
% 3.05/1.00  --res_lit_sel_side                      none
% 3.05/1.00  --res_ordering                          kbo
% 3.05/1.00  --res_to_prop_solver                    active
% 3.05/1.00  --res_prop_simpl_new                    false
% 3.05/1.00  --res_prop_simpl_given                  true
% 3.05/1.00  --res_passive_queue_type                priority_queues
% 3.05/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.05/1.00  --res_passive_queues_freq               [15;5]
% 3.05/1.00  --res_forward_subs                      full
% 3.05/1.00  --res_backward_subs                     full
% 3.05/1.00  --res_forward_subs_resolution           true
% 3.05/1.00  --res_backward_subs_resolution          true
% 3.05/1.00  --res_orphan_elimination                true
% 3.05/1.00  --res_time_limit                        2.
% 3.05/1.00  --res_out_proof                         true
% 3.05/1.00  
% 3.05/1.00  ------ Superposition Options
% 3.05/1.00  
% 3.05/1.00  --superposition_flag                    true
% 3.05/1.00  --sup_passive_queue_type                priority_queues
% 3.05/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.05/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.05/1.00  --demod_completeness_check              fast
% 3.05/1.00  --demod_use_ground                      true
% 3.05/1.00  --sup_to_prop_solver                    passive
% 3.05/1.00  --sup_prop_simpl_new                    true
% 3.05/1.00  --sup_prop_simpl_given                  true
% 3.05/1.00  --sup_fun_splitting                     false
% 3.05/1.00  --sup_smt_interval                      50000
% 3.05/1.00  
% 3.05/1.00  ------ Superposition Simplification Setup
% 3.05/1.00  
% 3.05/1.00  --sup_indices_passive                   []
% 3.05/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.05/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.05/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.05/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.05/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.05/1.00  --sup_full_bw                           [BwDemod]
% 3.05/1.00  --sup_immed_triv                        [TrivRules]
% 3.05/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.05/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.05/1.00  --sup_immed_bw_main                     []
% 3.05/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.05/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.05/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.05/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.05/1.00  
% 3.05/1.00  ------ Combination Options
% 3.05/1.00  
% 3.05/1.00  --comb_res_mult                         3
% 3.05/1.00  --comb_sup_mult                         2
% 3.05/1.00  --comb_inst_mult                        10
% 3.05/1.00  
% 3.05/1.00  ------ Debug Options
% 3.05/1.00  
% 3.05/1.00  --dbg_backtrace                         false
% 3.05/1.00  --dbg_dump_prop_clauses                 false
% 3.05/1.00  --dbg_dump_prop_clauses_file            -
% 3.05/1.00  --dbg_out_stat                          false
% 3.05/1.00  
% 3.05/1.00  
% 3.05/1.00  
% 3.05/1.00  
% 3.05/1.00  ------ Proving...
% 3.05/1.00  
% 3.05/1.00  
% 3.05/1.00  % SZS status Theorem for theBenchmark.p
% 3.05/1.00  
% 3.05/1.00   Resolution empty clause
% 3.05/1.00  
% 3.05/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.05/1.00  
% 3.05/1.00  fof(f13,axiom,(
% 3.05/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 3.05/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.05/1.00  
% 3.05/1.00  fof(f29,plain,(
% 3.05/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.05/1.00    inference(ennf_transformation,[],[f13])).
% 3.05/1.00  
% 3.05/1.00  fof(f30,plain,(
% 3.05/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.05/1.00    inference(flattening,[],[f29])).
% 3.05/1.00  
% 3.05/1.00  fof(f57,plain,(
% 3.05/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.05/1.00    inference(cnf_transformation,[],[f30])).
% 3.05/1.00  
% 3.05/1.00  fof(f10,axiom,(
% 3.05/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.05/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.05/1.00  
% 3.05/1.00  fof(f25,plain,(
% 3.05/1.00    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.05/1.00    inference(ennf_transformation,[],[f10])).
% 3.05/1.00  
% 3.05/1.00  fof(f26,plain,(
% 3.05/1.00    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.05/1.00    inference(flattening,[],[f25])).
% 3.05/1.00  
% 3.05/1.00  fof(f37,plain,(
% 3.05/1.00    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.05/1.00    inference(nnf_transformation,[],[f26])).
% 3.05/1.00  
% 3.05/1.00  fof(f51,plain,(
% 3.05/1.00    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.05/1.00    inference(cnf_transformation,[],[f37])).
% 3.05/1.00  
% 3.05/1.00  fof(f17,conjecture,(
% 3.05/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 3.05/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.05/1.00  
% 3.05/1.00  fof(f18,negated_conjecture,(
% 3.05/1.00    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 3.05/1.00    inference(negated_conjecture,[],[f17])).
% 3.05/1.00  
% 3.05/1.00  fof(f35,plain,(
% 3.05/1.00    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.05/1.00    inference(ennf_transformation,[],[f18])).
% 3.05/1.00  
% 3.05/1.00  fof(f36,plain,(
% 3.05/1.00    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.05/1.00    inference(flattening,[],[f35])).
% 3.05/1.00  
% 3.05/1.00  fof(f40,plain,(
% 3.05/1.00    ( ! [X2,X0,X1] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((~v2_funct_2(sK3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 3.05/1.00    introduced(choice_axiom,[])).
% 3.05/1.00  
% 3.05/1.00  fof(f39,plain,(
% 3.05/1.00    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 3.05/1.00    introduced(choice_axiom,[])).
% 3.05/1.00  
% 3.05/1.00  fof(f41,plain,(
% 3.05/1.00    ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 3.05/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f36,f40,f39])).
% 3.05/1.00  
% 3.05/1.00  fof(f68,plain,(
% 3.05/1.00    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 3.05/1.00    inference(cnf_transformation,[],[f41])).
% 3.05/1.00  
% 3.05/1.00  fof(f11,axiom,(
% 3.05/1.00    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.05/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.05/1.00  
% 3.05/1.00  fof(f53,plain,(
% 3.05/1.00    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.05/1.00    inference(cnf_transformation,[],[f11])).
% 3.05/1.00  
% 3.05/1.00  fof(f14,axiom,(
% 3.05/1.00    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.05/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.05/1.00  
% 3.05/1.00  fof(f58,plain,(
% 3.05/1.00    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.05/1.00    inference(cnf_transformation,[],[f14])).
% 3.05/1.00  
% 3.05/1.00  fof(f72,plain,(
% 3.05/1.00    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.05/1.00    inference(definition_unfolding,[],[f53,f58])).
% 3.05/1.00  
% 3.05/1.00  fof(f62,plain,(
% 3.05/1.00    v1_funct_1(sK2)),
% 3.05/1.00    inference(cnf_transformation,[],[f41])).
% 3.05/1.00  
% 3.05/1.00  fof(f64,plain,(
% 3.05/1.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.05/1.00    inference(cnf_transformation,[],[f41])).
% 3.05/1.00  
% 3.05/1.00  fof(f65,plain,(
% 3.05/1.00    v1_funct_1(sK3)),
% 3.05/1.00    inference(cnf_transformation,[],[f41])).
% 3.05/1.00  
% 3.05/1.00  fof(f67,plain,(
% 3.05/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 3.05/1.00    inference(cnf_transformation,[],[f41])).
% 3.05/1.00  
% 3.05/1.00  fof(f16,axiom,(
% 3.05/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 3.05/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.05/1.00  
% 3.05/1.00  fof(f33,plain,(
% 3.05/1.00    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 3.05/1.00    inference(ennf_transformation,[],[f16])).
% 3.05/1.00  
% 3.05/1.00  fof(f34,plain,(
% 3.05/1.00    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.05/1.00    inference(flattening,[],[f33])).
% 3.05/1.00  
% 3.05/1.00  fof(f60,plain,(
% 3.05/1.00    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X3) | k1_xboole_0 = X2 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.05/1.00    inference(cnf_transformation,[],[f34])).
% 3.05/1.00  
% 3.05/1.00  fof(f63,plain,(
% 3.05/1.00    v1_funct_2(sK2,sK0,sK1)),
% 3.05/1.00    inference(cnf_transformation,[],[f41])).
% 3.05/1.00  
% 3.05/1.00  fof(f66,plain,(
% 3.05/1.00    v1_funct_2(sK3,sK1,sK0)),
% 3.05/1.00    inference(cnf_transformation,[],[f41])).
% 3.05/1.00  
% 3.05/1.00  fof(f6,axiom,(
% 3.05/1.00    ! [X0] : v2_funct_1(k6_relat_1(X0))),
% 3.05/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.05/1.00  
% 3.05/1.00  fof(f47,plain,(
% 3.05/1.00    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 3.05/1.00    inference(cnf_transformation,[],[f6])).
% 3.05/1.00  
% 3.05/1.00  fof(f71,plain,(
% 3.05/1.00    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 3.05/1.00    inference(definition_unfolding,[],[f47,f58])).
% 3.05/1.00  
% 3.05/1.00  fof(f1,axiom,(
% 3.05/1.00    v1_xboole_0(k1_xboole_0)),
% 3.05/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.05/1.00  
% 3.05/1.00  fof(f42,plain,(
% 3.05/1.00    v1_xboole_0(k1_xboole_0)),
% 3.05/1.00    inference(cnf_transformation,[],[f1])).
% 3.05/1.00  
% 3.05/1.00  fof(f5,axiom,(
% 3.05/1.00    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 3.05/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.05/1.00  
% 3.05/1.00  fof(f46,plain,(
% 3.05/1.00    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 3.05/1.00    inference(cnf_transformation,[],[f5])).
% 3.05/1.00  
% 3.05/1.00  fof(f70,plain,(
% 3.05/1.00    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 3.05/1.00    inference(definition_unfolding,[],[f46,f58])).
% 3.05/1.00  
% 3.05/1.00  fof(f3,axiom,(
% 3.05/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.05/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.05/1.00  
% 3.05/1.00  fof(f21,plain,(
% 3.05/1.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.05/1.00    inference(ennf_transformation,[],[f3])).
% 3.05/1.00  
% 3.05/1.00  fof(f44,plain,(
% 3.05/1.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.05/1.00    inference(cnf_transformation,[],[f21])).
% 3.05/1.00  
% 3.05/1.00  fof(f2,axiom,(
% 3.05/1.00    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 3.05/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.05/1.00  
% 3.05/1.00  fof(f20,plain,(
% 3.05/1.00    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 3.05/1.00    inference(ennf_transformation,[],[f2])).
% 3.05/1.00  
% 3.05/1.00  fof(f43,plain,(
% 3.05/1.00    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 3.05/1.00    inference(cnf_transformation,[],[f20])).
% 3.05/1.00  
% 3.05/1.00  fof(f4,axiom,(
% 3.05/1.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.05/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.05/1.00  
% 3.05/1.00  fof(f45,plain,(
% 3.05/1.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.05/1.00    inference(cnf_transformation,[],[f4])).
% 3.05/1.00  
% 3.05/1.00  fof(f8,axiom,(
% 3.05/1.00    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 3.05/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.05/1.00  
% 3.05/1.00  fof(f23,plain,(
% 3.05/1.00    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 3.05/1.00    inference(ennf_transformation,[],[f8])).
% 3.05/1.00  
% 3.05/1.00  fof(f49,plain,(
% 3.05/1.00    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 3.05/1.00    inference(cnf_transformation,[],[f23])).
% 3.05/1.00  
% 3.05/1.00  fof(f9,axiom,(
% 3.05/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 3.05/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.05/1.00  
% 3.05/1.00  fof(f24,plain,(
% 3.05/1.00    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.05/1.00    inference(ennf_transformation,[],[f9])).
% 3.05/1.00  
% 3.05/1.00  fof(f50,plain,(
% 3.05/1.00    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.05/1.00    inference(cnf_transformation,[],[f24])).
% 3.05/1.00  
% 3.05/1.00  fof(f15,axiom,(
% 3.05/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 3.05/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.05/1.00  
% 3.05/1.00  fof(f31,plain,(
% 3.05/1.00    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.05/1.00    inference(ennf_transformation,[],[f15])).
% 3.05/1.00  
% 3.05/1.00  fof(f32,plain,(
% 3.05/1.00    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.05/1.00    inference(flattening,[],[f31])).
% 3.05/1.00  
% 3.05/1.00  fof(f59,plain,(
% 3.05/1.00    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.05/1.00    inference(cnf_transformation,[],[f32])).
% 3.05/1.00  
% 3.05/1.00  fof(f7,axiom,(
% 3.05/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.05/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.05/1.00  
% 3.05/1.00  fof(f19,plain,(
% 3.05/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.05/1.00    inference(pure_predicate_removal,[],[f7])).
% 3.05/1.00  
% 3.05/1.00  fof(f22,plain,(
% 3.05/1.00    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.05/1.00    inference(ennf_transformation,[],[f19])).
% 3.05/1.00  
% 3.05/1.00  fof(f48,plain,(
% 3.05/1.00    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.05/1.00    inference(cnf_transformation,[],[f22])).
% 3.05/1.00  
% 3.05/1.00  fof(f12,axiom,(
% 3.05/1.00    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 3.05/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.05/1.00  
% 3.05/1.00  fof(f27,plain,(
% 3.05/1.00    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.05/1.00    inference(ennf_transformation,[],[f12])).
% 3.05/1.00  
% 3.05/1.00  fof(f28,plain,(
% 3.05/1.00    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.05/1.00    inference(flattening,[],[f27])).
% 3.05/1.00  
% 3.05/1.00  fof(f38,plain,(
% 3.05/1.00    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.05/1.00    inference(nnf_transformation,[],[f28])).
% 3.05/1.00  
% 3.05/1.00  fof(f55,plain,(
% 3.05/1.00    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.05/1.00    inference(cnf_transformation,[],[f38])).
% 3.05/1.00  
% 3.05/1.00  fof(f74,plain,(
% 3.05/1.00    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.05/1.00    inference(equality_resolution,[],[f55])).
% 3.05/1.00  
% 3.05/1.00  fof(f69,plain,(
% 3.05/1.00    ~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)),
% 3.05/1.00    inference(cnf_transformation,[],[f41])).
% 3.05/1.00  
% 3.05/1.00  cnf(c_14,plain,
% 3.05/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.05/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.05/1.00      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.05/1.00      | ~ v1_funct_1(X0)
% 3.05/1.00      | ~ v1_funct_1(X3) ),
% 3.05/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_640,plain,
% 3.05/1.00      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
% 3.05/1.00      | ~ m1_subset_1(X3_48,k1_zfmisc_1(k2_zfmisc_1(X4_48,X5_48)))
% 3.05/1.00      | m1_subset_1(k1_partfun1(X4_48,X5_48,X1_48,X2_48,X3_48,X0_48),k1_zfmisc_1(k2_zfmisc_1(X4_48,X2_48)))
% 3.05/1.00      | ~ v1_funct_1(X0_48)
% 3.05/1.00      | ~ v1_funct_1(X3_48) ),
% 3.05/1.00      inference(subtyping,[status(esa)],[c_14]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_1105,plain,
% 3.05/1.00      ( m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48))) != iProver_top
% 3.05/1.00      | m1_subset_1(X3_48,k1_zfmisc_1(k2_zfmisc_1(X4_48,X5_48))) != iProver_top
% 3.05/1.00      | m1_subset_1(k1_partfun1(X4_48,X5_48,X1_48,X2_48,X3_48,X0_48),k1_zfmisc_1(k2_zfmisc_1(X4_48,X2_48))) = iProver_top
% 3.05/1.00      | v1_funct_1(X0_48) != iProver_top
% 3.05/1.00      | v1_funct_1(X3_48) != iProver_top ),
% 3.05/1.00      inference(predicate_to_equality,[status(thm)],[c_640]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_10,plain,
% 3.05/1.00      ( ~ r2_relset_1(X0,X1,X2,X3)
% 3.05/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.05/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.05/1.00      | X3 = X2 ),
% 3.05/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_20,negated_conjecture,
% 3.05/1.00      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 3.05/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_407,plain,
% 3.05/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.05/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.05/1.00      | X3 = X0
% 3.05/1.00      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 3.05/1.00      | k6_partfun1(sK0) != X3
% 3.05/1.00      | sK0 != X2
% 3.05/1.00      | sK0 != X1 ),
% 3.05/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_20]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_408,plain,
% 3.05/1.00      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.05/1.00      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.05/1.00      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.05/1.00      inference(unflattening,[status(thm)],[c_407]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_11,plain,
% 3.05/1.00      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.05/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_416,plain,
% 3.05/1.00      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.05/1.00      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.05/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_408,c_11]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_628,plain,
% 3.05/1.00      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.05/1.00      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.05/1.00      inference(subtyping,[status(esa)],[c_416]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_1118,plain,
% 3.05/1.00      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.05/1.00      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.05/1.00      inference(predicate_to_equality,[status(thm)],[c_628]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_2147,plain,
% 3.05/1.00      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
% 3.05/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.05/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.05/1.00      | v1_funct_1(sK2) != iProver_top
% 3.05/1.00      | v1_funct_1(sK3) != iProver_top ),
% 3.05/1.00      inference(superposition,[status(thm)],[c_1105,c_1118]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_26,negated_conjecture,
% 3.05/1.00      ( v1_funct_1(sK2) ),
% 3.05/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_27,plain,
% 3.05/1.00      ( v1_funct_1(sK2) = iProver_top ),
% 3.05/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_24,negated_conjecture,
% 3.05/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.05/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_29,plain,
% 3.05/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.05/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_23,negated_conjecture,
% 3.05/1.00      ( v1_funct_1(sK3) ),
% 3.05/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_30,plain,
% 3.05/1.00      ( v1_funct_1(sK3) = iProver_top ),
% 3.05/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_21,negated_conjecture,
% 3.05/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 3.05/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_32,plain,
% 3.05/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.05/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_3243,plain,
% 3.05/1.00      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
% 3.05/1.00      inference(global_propositional_subsumption,
% 3.05/1.00                [status(thm)],
% 3.05/1.00                [c_2147,c_27,c_29,c_30,c_32]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_18,plain,
% 3.05/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.05/1.00      | ~ v1_funct_2(X3,X2,X4)
% 3.05/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.05/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
% 3.05/1.00      | ~ v1_funct_1(X3)
% 3.05/1.00      | ~ v1_funct_1(X0)
% 3.05/1.00      | v2_funct_1(X0)
% 3.05/1.00      | ~ v2_funct_1(k1_partfun1(X1,X2,X2,X4,X0,X3))
% 3.05/1.00      | k1_xboole_0 = X4 ),
% 3.05/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_637,plain,
% 3.05/1.00      ( ~ v1_funct_2(X0_48,X1_48,X2_48)
% 3.05/1.00      | ~ v1_funct_2(X3_48,X2_48,X4_48)
% 3.05/1.00      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
% 3.05/1.00      | ~ m1_subset_1(X3_48,k1_zfmisc_1(k2_zfmisc_1(X2_48,X4_48)))
% 3.05/1.00      | ~ v1_funct_1(X0_48)
% 3.05/1.00      | ~ v1_funct_1(X3_48)
% 3.05/1.00      | v2_funct_1(X0_48)
% 3.05/1.00      | ~ v2_funct_1(k1_partfun1(X1_48,X2_48,X2_48,X4_48,X0_48,X3_48))
% 3.05/1.00      | k1_xboole_0 = X4_48 ),
% 3.05/1.00      inference(subtyping,[status(esa)],[c_18]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_1108,plain,
% 3.05/1.00      ( k1_xboole_0 = X0_48
% 3.05/1.00      | v1_funct_2(X1_48,X2_48,X3_48) != iProver_top
% 3.05/1.00      | v1_funct_2(X4_48,X3_48,X0_48) != iProver_top
% 3.05/1.00      | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_48,X3_48))) != iProver_top
% 3.05/1.00      | m1_subset_1(X4_48,k1_zfmisc_1(k2_zfmisc_1(X3_48,X0_48))) != iProver_top
% 3.05/1.00      | v1_funct_1(X1_48) != iProver_top
% 3.05/1.00      | v1_funct_1(X4_48) != iProver_top
% 3.05/1.00      | v2_funct_1(X1_48) = iProver_top
% 3.05/1.00      | v2_funct_1(k1_partfun1(X2_48,X3_48,X3_48,X0_48,X1_48,X4_48)) != iProver_top ),
% 3.05/1.00      inference(predicate_to_equality,[status(thm)],[c_637]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_3269,plain,
% 3.05/1.00      ( sK0 = k1_xboole_0
% 3.05/1.00      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 3.05/1.00      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 3.05/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.05/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.05/1.00      | v1_funct_1(sK2) != iProver_top
% 3.05/1.00      | v1_funct_1(sK3) != iProver_top
% 3.05/1.00      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 3.05/1.00      | v2_funct_1(sK2) = iProver_top ),
% 3.05/1.00      inference(superposition,[status(thm)],[c_3243,c_1108]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_25,negated_conjecture,
% 3.05/1.00      ( v1_funct_2(sK2,sK0,sK1) ),
% 3.05/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_28,plain,
% 3.05/1.00      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 3.05/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_22,negated_conjecture,
% 3.05/1.00      ( v1_funct_2(sK3,sK1,sK0) ),
% 3.05/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_31,plain,
% 3.05/1.00      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 3.05/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_5,plain,
% 3.05/1.00      ( v2_funct_1(k6_partfun1(X0)) ),
% 3.05/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_72,plain,
% 3.05/1.00      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 3.05/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_74,plain,
% 3.05/1.00      ( v2_funct_1(k6_partfun1(k1_xboole_0)) = iProver_top ),
% 3.05/1.00      inference(instantiation,[status(thm)],[c_72]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_0,plain,
% 3.05/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 3.05/1.00      inference(cnf_transformation,[],[f42]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_653,plain,( X0_48 = X0_48 ),theory(equality) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_681,plain,
% 3.05/1.00      ( k1_xboole_0 = k1_xboole_0 ),
% 3.05/1.00      inference(instantiation,[status(thm)],[c_653]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_4,plain,
% 3.05/1.00      ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 3.05/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_645,plain,
% 3.05/1.00      ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 3.05/1.00      inference(subtyping,[status(esa)],[c_4]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_662,plain,
% 3.05/1.00      ( ~ v2_funct_1(X0_48) | v2_funct_1(X1_48) | X1_48 != X0_48 ),
% 3.05/1.00      theory(equality) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_1337,plain,
% 3.05/1.00      ( v2_funct_1(X0_48)
% 3.05/1.00      | ~ v2_funct_1(k6_partfun1(X1_48))
% 3.05/1.00      | X0_48 != k6_partfun1(X1_48) ),
% 3.05/1.00      inference(instantiation,[status(thm)],[c_662]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_1338,plain,
% 3.05/1.00      ( X0_48 != k6_partfun1(X1_48)
% 3.05/1.00      | v2_funct_1(X0_48) = iProver_top
% 3.05/1.00      | v2_funct_1(k6_partfun1(X1_48)) != iProver_top ),
% 3.05/1.00      inference(predicate_to_equality,[status(thm)],[c_1337]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_1340,plain,
% 3.05/1.00      ( k1_xboole_0 != k6_partfun1(k1_xboole_0)
% 3.05/1.00      | v2_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top
% 3.05/1.00      | v2_funct_1(k1_xboole_0) = iProver_top ),
% 3.05/1.00      inference(instantiation,[status(thm)],[c_1338]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_655,plain,
% 3.05/1.00      ( X0_48 != X1_48 | X2_48 != X1_48 | X2_48 = X0_48 ),
% 3.05/1.00      theory(equality) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_1607,plain,
% 3.05/1.00      ( X0_48 != X1_48
% 3.05/1.00      | X0_48 = k6_partfun1(X2_48)
% 3.05/1.00      | k6_partfun1(X2_48) != X1_48 ),
% 3.05/1.00      inference(instantiation,[status(thm)],[c_655]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_1608,plain,
% 3.05/1.00      ( k6_partfun1(k1_xboole_0) != k1_xboole_0
% 3.05/1.00      | k1_xboole_0 = k6_partfun1(k1_xboole_0)
% 3.05/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 3.05/1.00      inference(instantiation,[status(thm)],[c_1607]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_2,plain,
% 3.05/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.05/1.00      inference(cnf_transformation,[],[f44]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_647,plain,
% 3.05/1.00      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(X1_48))
% 3.05/1.00      | ~ v1_relat_1(X1_48)
% 3.05/1.00      | v1_relat_1(X0_48) ),
% 3.05/1.00      inference(subtyping,[status(esa)],[c_2]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_1332,plain,
% 3.05/1.00      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
% 3.05/1.00      | v1_relat_1(X0_48)
% 3.05/1.00      | ~ v1_relat_1(k2_zfmisc_1(X1_48,X2_48)) ),
% 3.05/1.00      inference(instantiation,[status(thm)],[c_647]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_1612,plain,
% 3.05/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.05/1.00      | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
% 3.05/1.00      | v1_relat_1(sK3) ),
% 3.05/1.00      inference(instantiation,[status(thm)],[c_1332]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_1613,plain,
% 3.05/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.05/1.00      | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 3.05/1.00      | v1_relat_1(sK3) = iProver_top ),
% 3.05/1.00      inference(predicate_to_equality,[status(thm)],[c_1612]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_1,plain,
% 3.05/1.00      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X1 = X0 ),
% 3.05/1.00      inference(cnf_transformation,[],[f43]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_648,plain,
% 3.05/1.00      ( ~ v1_xboole_0(X0_48) | ~ v1_xboole_0(X1_48) | X1_48 = X0_48 ),
% 3.05/1.00      inference(subtyping,[status(esa)],[c_1]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_1754,plain,
% 3.05/1.00      ( ~ v1_xboole_0(X0_48) | ~ v1_xboole_0(sK2) | sK2 = X0_48 ),
% 3.05/1.00      inference(instantiation,[status(thm)],[c_648]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_1756,plain,
% 3.05/1.00      ( ~ v1_xboole_0(sK2) | ~ v1_xboole_0(k1_xboole_0) | sK2 = k1_xboole_0 ),
% 3.05/1.00      inference(instantiation,[status(thm)],[c_1754]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_3,plain,
% 3.05/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.05/1.00      inference(cnf_transformation,[],[f45]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_646,plain,
% 3.05/1.00      ( v1_relat_1(k2_zfmisc_1(X0_48,X1_48)) ),
% 3.05/1.00      inference(subtyping,[status(esa)],[c_3]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_1870,plain,
% 3.05/1.00      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
% 3.05/1.00      inference(instantiation,[status(thm)],[c_646]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_1871,plain,
% 3.05/1.00      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
% 3.05/1.00      inference(predicate_to_equality,[status(thm)],[c_1870]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_1998,plain,
% 3.05/1.00      ( ~ v2_funct_1(X0_48) | v2_funct_1(sK2) | sK2 != X0_48 ),
% 3.05/1.00      inference(instantiation,[status(thm)],[c_662]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_1999,plain,
% 3.05/1.00      ( sK2 != X0_48
% 3.05/1.00      | v2_funct_1(X0_48) != iProver_top
% 3.05/1.00      | v2_funct_1(sK2) = iProver_top ),
% 3.05/1.00      inference(predicate_to_equality,[status(thm)],[c_1998]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_2001,plain,
% 3.05/1.00      ( sK2 != k1_xboole_0
% 3.05/1.00      | v2_funct_1(sK2) = iProver_top
% 3.05/1.00      | v2_funct_1(k1_xboole_0) != iProver_top ),
% 3.05/1.00      inference(instantiation,[status(thm)],[c_1999]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_633,negated_conjecture,
% 3.05/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.05/1.00      inference(subtyping,[status(esa)],[c_24]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_1112,plain,
% 3.05/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.05/1.00      inference(predicate_to_equality,[status(thm)],[c_633]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_7,plain,
% 3.05/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.05/1.00      | ~ v1_xboole_0(X1)
% 3.05/1.00      | v1_xboole_0(X0) ),
% 3.05/1.00      inference(cnf_transformation,[],[f49]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_643,plain,
% 3.05/1.00      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
% 3.05/1.00      | ~ v1_xboole_0(X1_48)
% 3.05/1.00      | v1_xboole_0(X0_48) ),
% 3.05/1.00      inference(subtyping,[status(esa)],[c_7]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_1102,plain,
% 3.05/1.00      ( m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48))) != iProver_top
% 3.05/1.00      | v1_xboole_0(X1_48) != iProver_top
% 3.05/1.00      | v1_xboole_0(X0_48) = iProver_top ),
% 3.05/1.00      inference(predicate_to_equality,[status(thm)],[c_643]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_2073,plain,
% 3.05/1.00      ( v1_xboole_0(sK2) = iProver_top | v1_xboole_0(sK0) != iProver_top ),
% 3.05/1.00      inference(superposition,[status(thm)],[c_1112,c_1102]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_2089,plain,
% 3.05/1.00      ( v1_xboole_0(sK2) | ~ v1_xboole_0(sK0) ),
% 3.05/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_2073]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_656,plain,
% 3.05/1.00      ( ~ v1_xboole_0(X0_48) | v1_xboole_0(X1_48) | X1_48 != X0_48 ),
% 3.05/1.00      theory(equality) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_2267,plain,
% 3.05/1.00      ( ~ v1_xboole_0(X0_48) | v1_xboole_0(sK0) | sK0 != X0_48 ),
% 3.05/1.00      inference(instantiation,[status(thm)],[c_656]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_2269,plain,
% 3.05/1.00      ( v1_xboole_0(sK0) | ~ v1_xboole_0(k1_xboole_0) | sK0 != k1_xboole_0 ),
% 3.05/1.00      inference(instantiation,[status(thm)],[c_2267]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_636,negated_conjecture,
% 3.05/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 3.05/1.00      inference(subtyping,[status(esa)],[c_21]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_1109,plain,
% 3.05/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.05/1.00      inference(predicate_to_equality,[status(thm)],[c_636]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_8,plain,
% 3.05/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.05/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.05/1.00      inference(cnf_transformation,[],[f50]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_642,plain,
% 3.05/1.00      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
% 3.05/1.00      | k2_relset_1(X1_48,X2_48,X0_48) = k2_relat_1(X0_48) ),
% 3.05/1.00      inference(subtyping,[status(esa)],[c_8]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_1103,plain,
% 3.05/1.00      ( k2_relset_1(X0_48,X1_48,X2_48) = k2_relat_1(X2_48)
% 3.05/1.00      | m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top ),
% 3.05/1.00      inference(predicate_to_equality,[status(thm)],[c_642]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_2036,plain,
% 3.05/1.00      ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
% 3.05/1.00      inference(superposition,[status(thm)],[c_1109,c_1103]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_16,plain,
% 3.05/1.00      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.05/1.00      | ~ v1_funct_2(X2,X0,X1)
% 3.05/1.00      | ~ v1_funct_2(X3,X1,X0)
% 3.05/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.05/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.05/1.00      | ~ v1_funct_1(X2)
% 3.05/1.00      | ~ v1_funct_1(X3)
% 3.05/1.00      | k2_relset_1(X1,X0,X3) = X0 ),
% 3.05/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_420,plain,
% 3.05/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.05/1.00      | ~ v1_funct_2(X3,X2,X1)
% 3.05/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.05/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.05/1.00      | ~ v1_funct_1(X3)
% 3.05/1.00      | ~ v1_funct_1(X0)
% 3.05/1.00      | k1_partfun1(X1,X2,X2,X1,X0,X3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.05/1.00      | k2_relset_1(X2,X1,X3) = X1
% 3.05/1.00      | k6_partfun1(X1) != k6_partfun1(sK0)
% 3.05/1.00      | sK0 != X1 ),
% 3.05/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_20]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_421,plain,
% 3.05/1.00      ( ~ v1_funct_2(X0,X1,sK0)
% 3.05/1.00      | ~ v1_funct_2(X2,sK0,X1)
% 3.05/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 3.05/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 3.05/1.00      | ~ v1_funct_1(X2)
% 3.05/1.00      | ~ v1_funct_1(X0)
% 3.05/1.00      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.05/1.00      | k2_relset_1(X1,sK0,X0) = sK0
% 3.05/1.00      | k6_partfun1(sK0) != k6_partfun1(sK0) ),
% 3.05/1.00      inference(unflattening,[status(thm)],[c_420]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_497,plain,
% 3.05/1.00      ( ~ v1_funct_2(X0,X1,sK0)
% 3.05/1.00      | ~ v1_funct_2(X2,sK0,X1)
% 3.05/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 3.05/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 3.05/1.00      | ~ v1_funct_1(X0)
% 3.05/1.00      | ~ v1_funct_1(X2)
% 3.05/1.00      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.05/1.00      | k2_relset_1(X1,sK0,X0) = sK0 ),
% 3.05/1.00      inference(equality_resolution_simp,[status(thm)],[c_421]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_627,plain,
% 3.05/1.00      ( ~ v1_funct_2(X0_48,X1_48,sK0)
% 3.05/1.00      | ~ v1_funct_2(X2_48,sK0,X1_48)
% 3.05/1.00      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,sK0)))
% 3.05/1.00      | ~ m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(sK0,X1_48)))
% 3.05/1.00      | ~ v1_funct_1(X0_48)
% 3.05/1.00      | ~ v1_funct_1(X2_48)
% 3.05/1.00      | k1_partfun1(sK0,X1_48,X1_48,sK0,X2_48,X0_48) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.05/1.00      | k2_relset_1(X1_48,sK0,X0_48) = sK0 ),
% 3.05/1.00      inference(subtyping,[status(esa)],[c_497]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_1119,plain,
% 3.05/1.00      ( k1_partfun1(sK0,X0_48,X0_48,sK0,X1_48,X2_48) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.05/1.00      | k2_relset_1(X0_48,sK0,X2_48) = sK0
% 3.05/1.00      | v1_funct_2(X2_48,X0_48,sK0) != iProver_top
% 3.05/1.00      | v1_funct_2(X1_48,sK0,X0_48) != iProver_top
% 3.05/1.00      | m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(X0_48,sK0))) != iProver_top
% 3.05/1.00      | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_48))) != iProver_top
% 3.05/1.00      | v1_funct_1(X2_48) != iProver_top
% 3.05/1.00      | v1_funct_1(X1_48) != iProver_top ),
% 3.05/1.00      inference(predicate_to_equality,[status(thm)],[c_627]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_1848,plain,
% 3.05/1.00      ( k2_relset_1(sK1,sK0,sK3) = sK0
% 3.05/1.00      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 3.05/1.00      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 3.05/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.05/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.05/1.00      | v1_funct_1(sK2) != iProver_top
% 3.05/1.00      | v1_funct_1(sK3) != iProver_top ),
% 3.05/1.00      inference(equality_resolution,[status(thm)],[c_1119]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_1851,plain,
% 3.05/1.00      ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
% 3.05/1.00      inference(global_propositional_subsumption,
% 3.05/1.00                [status(thm)],
% 3.05/1.00                [c_1848,c_27,c_28,c_29,c_30,c_31,c_32]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_2047,plain,
% 3.05/1.00      ( k2_relat_1(sK3) = sK0 ),
% 3.05/1.00      inference(light_normalisation,[status(thm)],[c_2036,c_1851]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_6,plain,
% 3.05/1.00      ( v5_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.05/1.00      inference(cnf_transformation,[],[f48]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_12,plain,
% 3.05/1.00      ( v2_funct_2(X0,k2_relat_1(X0))
% 3.05/1.00      | ~ v5_relat_1(X0,k2_relat_1(X0))
% 3.05/1.00      | ~ v1_relat_1(X0) ),
% 3.05/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_19,negated_conjecture,
% 3.05/1.00      ( ~ v2_funct_2(sK3,sK0) | ~ v2_funct_1(sK2) ),
% 3.05/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_326,plain,
% 3.05/1.00      ( ~ v5_relat_1(X0,k2_relat_1(X0))
% 3.05/1.00      | ~ v2_funct_1(sK2)
% 3.05/1.00      | ~ v1_relat_1(X0)
% 3.05/1.00      | k2_relat_1(X0) != sK0
% 3.05/1.00      | sK3 != X0 ),
% 3.05/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_19]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_327,plain,
% 3.05/1.00      ( ~ v5_relat_1(sK3,k2_relat_1(sK3))
% 3.05/1.00      | ~ v2_funct_1(sK2)
% 3.05/1.00      | ~ v1_relat_1(sK3)
% 3.05/1.00      | k2_relat_1(sK3) != sK0 ),
% 3.05/1.00      inference(unflattening,[status(thm)],[c_326]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_347,plain,
% 3.05/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.05/1.00      | ~ v2_funct_1(sK2)
% 3.05/1.00      | ~ v1_relat_1(sK3)
% 3.05/1.00      | k2_relat_1(sK3) != X2
% 3.05/1.00      | k2_relat_1(sK3) != sK0
% 3.05/1.00      | sK3 != X0 ),
% 3.05/1.00      inference(resolution_lifted,[status(thm)],[c_6,c_327]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_348,plain,
% 3.05/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3))))
% 3.05/1.00      | ~ v2_funct_1(sK2)
% 3.05/1.00      | ~ v1_relat_1(sK3)
% 3.05/1.00      | k2_relat_1(sK3) != sK0 ),
% 3.05/1.00      inference(unflattening,[status(thm)],[c_347]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_630,plain,
% 3.05/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_48,k2_relat_1(sK3))))
% 3.05/1.00      | ~ v2_funct_1(sK2)
% 3.05/1.00      | ~ v1_relat_1(sK3)
% 3.05/1.00      | k2_relat_1(sK3) != sK0 ),
% 3.05/1.00      inference(subtyping,[status(esa)],[c_348]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_651,plain,
% 3.05/1.00      ( ~ v2_funct_1(sK2)
% 3.05/1.00      | ~ v1_relat_1(sK3)
% 3.05/1.00      | sP0_iProver_split
% 3.05/1.00      | k2_relat_1(sK3) != sK0 ),
% 3.05/1.00      inference(splitting,
% 3.05/1.00                [splitting(split),new_symbols(definition,[])],
% 3.05/1.00                [c_630]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_1115,plain,
% 3.05/1.00      ( k2_relat_1(sK3) != sK0
% 3.05/1.00      | v2_funct_1(sK2) != iProver_top
% 3.05/1.00      | v1_relat_1(sK3) != iProver_top
% 3.05/1.00      | sP0_iProver_split = iProver_top ),
% 3.05/1.00      inference(predicate_to_equality,[status(thm)],[c_651]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_2380,plain,
% 3.05/1.00      ( sK0 != sK0
% 3.05/1.00      | v2_funct_1(sK2) != iProver_top
% 3.05/1.00      | v1_relat_1(sK3) != iProver_top
% 3.05/1.00      | sP0_iProver_split = iProver_top ),
% 3.05/1.00      inference(demodulation,[status(thm)],[c_2047,c_1115]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_2386,plain,
% 3.05/1.00      ( v2_funct_1(sK2) != iProver_top
% 3.05/1.00      | v1_relat_1(sK3) != iProver_top
% 3.05/1.00      | sP0_iProver_split = iProver_top ),
% 3.05/1.00      inference(equality_resolution_simp,[status(thm)],[c_2380]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_650,plain,
% 3.05/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_48,k2_relat_1(sK3))))
% 3.05/1.00      | ~ sP0_iProver_split ),
% 3.05/1.00      inference(splitting,
% 3.05/1.00                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 3.05/1.00                [c_630]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_1116,plain,
% 3.05/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_48,k2_relat_1(sK3)))) != iProver_top
% 3.05/1.00      | sP0_iProver_split != iProver_top ),
% 3.05/1.00      inference(predicate_to_equality,[status(thm)],[c_650]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_2381,plain,
% 3.05/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_48,sK0))) != iProver_top
% 3.05/1.00      | sP0_iProver_split != iProver_top ),
% 3.05/1.00      inference(demodulation,[status(thm)],[c_2047,c_1116]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_2400,plain,
% 3.05/1.00      ( sP0_iProver_split != iProver_top ),
% 3.05/1.00      inference(superposition,[status(thm)],[c_1109,c_2381]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_3377,plain,
% 3.05/1.00      ( v2_funct_1(k6_partfun1(sK0)) != iProver_top ),
% 3.05/1.00      inference(global_propositional_subsumption,
% 3.05/1.00                [status(thm)],
% 3.05/1.00                [c_3269,c_27,c_28,c_29,c_30,c_31,c_32,c_74,c_0,c_681,c_645,
% 3.05/1.00                 c_1340,c_1608,c_1613,c_1756,c_1871,c_2001,c_2089,c_2269,
% 3.05/1.00                 c_2386,c_2400]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_644,plain,
% 3.05/1.00      ( v2_funct_1(k6_partfun1(X0_48)) ),
% 3.05/1.00      inference(subtyping,[status(esa)],[c_5]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_1101,plain,
% 3.05/1.00      ( v2_funct_1(k6_partfun1(X0_48)) = iProver_top ),
% 3.05/1.00      inference(predicate_to_equality,[status(thm)],[c_644]) ).
% 3.05/1.00  
% 3.05/1.00  cnf(c_3382,plain,
% 3.05/1.00      ( $false ),
% 3.05/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_3377,c_1101]) ).
% 3.05/1.00  
% 3.05/1.00  
% 3.05/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.05/1.00  
% 3.05/1.00  ------                               Statistics
% 3.05/1.00  
% 3.05/1.00  ------ General
% 3.05/1.00  
% 3.05/1.00  abstr_ref_over_cycles:                  0
% 3.05/1.00  abstr_ref_under_cycles:                 0
% 3.05/1.00  gc_basic_clause_elim:                   0
% 3.05/1.00  forced_gc_time:                         0
% 3.05/1.00  parsing_time:                           0.011
% 3.05/1.00  unif_index_cands_time:                  0.
% 3.05/1.00  unif_index_add_time:                    0.
% 3.05/1.00  orderings_time:                         0.
% 3.05/1.00  out_proof_time:                         0.01
% 3.05/1.00  total_time:                             0.163
% 3.05/1.00  num_of_symbols:                         54
% 3.05/1.00  num_of_terms:                           5399
% 3.05/1.00  
% 3.05/1.00  ------ Preprocessing
% 3.05/1.00  
% 3.05/1.00  num_of_splits:                          1
% 3.05/1.00  num_of_split_atoms:                     1
% 3.05/1.00  num_of_reused_defs:                     0
% 3.05/1.00  num_eq_ax_congr_red:                    9
% 3.05/1.00  num_of_sem_filtered_clauses:            1
% 3.05/1.00  num_of_subtypes:                        2
% 3.05/1.00  monotx_restored_types:                  1
% 3.05/1.00  sat_num_of_epr_types:                   0
% 3.05/1.00  sat_num_of_non_cyclic_types:            0
% 3.05/1.00  sat_guarded_non_collapsed_types:        1
% 3.05/1.00  num_pure_diseq_elim:                    0
% 3.05/1.00  simp_replaced_by:                       0
% 3.05/1.00  res_preprocessed:                       129
% 3.05/1.00  prep_upred:                             0
% 3.05/1.00  prep_unflattend:                        19
% 3.05/1.00  smt_new_axioms:                         0
% 3.05/1.00  pred_elim_cands:                        6
% 3.05/1.00  pred_elim:                              3
% 3.05/1.00  pred_elim_cl:                           4
% 3.05/1.00  pred_elim_cycles:                       6
% 3.05/1.00  merged_defs:                            0
% 3.05/1.00  merged_defs_ncl:                        0
% 3.05/1.00  bin_hyper_res:                          0
% 3.05/1.00  prep_cycles:                            4
% 3.05/1.00  pred_elim_time:                         0.005
% 3.05/1.00  splitting_time:                         0.
% 3.05/1.00  sem_filter_time:                        0.
% 3.05/1.00  monotx_time:                            0.
% 3.05/1.00  subtype_inf_time:                       0.002
% 3.05/1.00  
% 3.05/1.00  ------ Problem properties
% 3.05/1.00  
% 3.05/1.00  clauses:                                24
% 3.05/1.00  conjectures:                            6
% 3.05/1.00  epr:                                    6
% 3.05/1.00  horn:                                   23
% 3.05/1.00  ground:                                 10
% 3.05/1.00  unary:                                  11
% 3.05/1.00  binary:                                 3
% 3.05/1.00  lits:                                   73
% 3.05/1.00  lits_eq:                                10
% 3.05/1.00  fd_pure:                                0
% 3.05/1.00  fd_pseudo:                              0
% 3.05/1.00  fd_cond:                                1
% 3.05/1.00  fd_pseudo_cond:                         1
% 3.05/1.00  ac_symbols:                             0
% 3.05/1.00  
% 3.05/1.00  ------ Propositional Solver
% 3.05/1.00  
% 3.05/1.00  prop_solver_calls:                      27
% 3.05/1.00  prop_fast_solver_calls:                 928
% 3.05/1.00  smt_solver_calls:                       0
% 3.05/1.00  smt_fast_solver_calls:                  0
% 3.05/1.00  prop_num_of_clauses:                    1352
% 3.05/1.00  prop_preprocess_simplified:             4785
% 3.05/1.00  prop_fo_subsumed:                       26
% 3.05/1.00  prop_solver_time:                       0.
% 3.05/1.00  smt_solver_time:                        0.
% 3.05/1.00  smt_fast_solver_time:                   0.
% 3.05/1.00  prop_fast_solver_time:                  0.
% 3.05/1.00  prop_unsat_core_time:                   0.
% 3.05/1.00  
% 3.05/1.00  ------ QBF
% 3.05/1.00  
% 3.05/1.00  qbf_q_res:                              0
% 3.05/1.00  qbf_num_tautologies:                    0
% 3.05/1.00  qbf_prep_cycles:                        0
% 3.05/1.00  
% 3.05/1.00  ------ BMC1
% 3.05/1.00  
% 3.05/1.00  bmc1_current_bound:                     -1
% 3.05/1.00  bmc1_last_solved_bound:                 -1
% 3.05/1.00  bmc1_unsat_core_size:                   -1
% 3.05/1.00  bmc1_unsat_core_parents_size:           -1
% 3.05/1.00  bmc1_merge_next_fun:                    0
% 3.05/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.05/1.00  
% 3.05/1.00  ------ Instantiation
% 3.05/1.00  
% 3.05/1.00  inst_num_of_clauses:                    374
% 3.05/1.00  inst_num_in_passive:                    126
% 3.05/1.00  inst_num_in_active:                     207
% 3.05/1.00  inst_num_in_unprocessed:                41
% 3.05/1.00  inst_num_of_loops:                      220
% 3.05/1.00  inst_num_of_learning_restarts:          0
% 3.05/1.00  inst_num_moves_active_passive:          10
% 3.05/1.00  inst_lit_activity:                      0
% 3.05/1.00  inst_lit_activity_moves:                0
% 3.05/1.00  inst_num_tautologies:                   0
% 3.05/1.00  inst_num_prop_implied:                  0
% 3.05/1.00  inst_num_existing_simplified:           0
% 3.05/1.00  inst_num_eq_res_simplified:             0
% 3.05/1.00  inst_num_child_elim:                    0
% 3.05/1.00  inst_num_of_dismatching_blockings:      17
% 3.05/1.00  inst_num_of_non_proper_insts:           231
% 3.05/1.00  inst_num_of_duplicates:                 0
% 3.05/1.00  inst_inst_num_from_inst_to_res:         0
% 3.05/1.00  inst_dismatching_checking_time:         0.
% 3.05/1.00  
% 3.05/1.00  ------ Resolution
% 3.05/1.00  
% 3.05/1.00  res_num_of_clauses:                     0
% 3.05/1.00  res_num_in_passive:                     0
% 3.05/1.00  res_num_in_active:                      0
% 3.05/1.00  res_num_of_loops:                       133
% 3.05/1.00  res_forward_subset_subsumed:            16
% 3.05/1.00  res_backward_subset_subsumed:           0
% 3.05/1.00  res_forward_subsumed:                   0
% 3.05/1.00  res_backward_subsumed:                  0
% 3.05/1.00  res_forward_subsumption_resolution:     2
% 3.05/1.00  res_backward_subsumption_resolution:    0
% 3.05/1.00  res_clause_to_clause_subsumption:       58
% 3.05/1.00  res_orphan_elimination:                 0
% 3.05/1.00  res_tautology_del:                      21
% 3.05/1.00  res_num_eq_res_simplified:              1
% 3.05/1.00  res_num_sel_changes:                    0
% 3.05/1.00  res_moves_from_active_to_pass:          0
% 3.05/1.00  
% 3.05/1.00  ------ Superposition
% 3.05/1.00  
% 3.05/1.00  sup_time_total:                         0.
% 3.05/1.00  sup_time_generating:                    0.
% 3.05/1.00  sup_time_sim_full:                      0.
% 3.05/1.00  sup_time_sim_immed:                     0.
% 3.05/1.00  
% 3.05/1.00  sup_num_of_clauses:                     47
% 3.05/1.00  sup_num_in_active:                      38
% 3.05/1.00  sup_num_in_passive:                     9
% 3.05/1.00  sup_num_of_loops:                       42
% 3.05/1.00  sup_fw_superposition:                   20
% 3.05/1.00  sup_bw_superposition:                   9
% 3.05/1.00  sup_immediate_simplified:               3
% 3.05/1.00  sup_given_eliminated:                   0
% 3.05/1.00  comparisons_done:                       0
% 3.05/1.00  comparisons_avoided:                    0
% 3.05/1.00  
% 3.05/1.00  ------ Simplifications
% 3.05/1.00  
% 3.05/1.00  
% 3.05/1.00  sim_fw_subset_subsumed:                 0
% 3.05/1.00  sim_bw_subset_subsumed:                 0
% 3.05/1.00  sim_fw_subsumed:                        1
% 3.05/1.00  sim_bw_subsumed:                        0
% 3.05/1.00  sim_fw_subsumption_res:                 1
% 3.05/1.00  sim_bw_subsumption_res:                 0
% 3.05/1.00  sim_tautology_del:                      2
% 3.05/1.00  sim_eq_tautology_del:                   3
% 3.05/1.00  sim_eq_res_simp:                        1
% 3.05/1.00  sim_fw_demodulated:                     0
% 3.05/1.00  sim_bw_demodulated:                     4
% 3.05/1.00  sim_light_normalised:                   2
% 3.05/1.00  sim_joinable_taut:                      0
% 3.05/1.00  sim_joinable_simp:                      0
% 3.05/1.00  sim_ac_normalised:                      0
% 3.05/1.00  sim_smt_subsumption:                    0
% 3.05/1.00  
%------------------------------------------------------------------------------
