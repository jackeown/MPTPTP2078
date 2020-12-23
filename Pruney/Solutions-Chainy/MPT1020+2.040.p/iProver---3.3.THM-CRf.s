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
% DateTime   : Thu Dec  3 12:07:12 EST 2020

% Result     : Theorem 2.43s
% Output     : CNFRefutation 2.43s
% Verified   : 
% Statistics : Number of formulae       :  188 (3983 expanded)
%              Number of clauses        :  117 (1264 expanded)
%              Number of leaves         :   21 ( 947 expanded)
%              Depth                    :   21
%              Number of atoms          :  653 (25371 expanded)
%              Number of equality atoms :  238 (2263 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f2])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v3_funct_2(X2,X0,X0)
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
         => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
           => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v3_funct_2(X2,X0,X0)
              & v1_funct_2(X2,X0,X0)
              & v1_funct_1(X2) )
           => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
             => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f39,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f40,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f39])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
     => ( ~ r2_relset_1(X0,X0,sK2,k2_funct_2(X0,X1))
        & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,sK2),k6_partfun1(X0))
        & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(sK2,X0,X0)
        & v1_funct_2(sK2,X0,X0)
        & v1_funct_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
            & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v3_funct_2(X2,X0,X0)
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ? [X2] :
          ( ~ r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1))
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
          & v3_funct_2(X2,sK0,sK0)
          & v1_funct_2(X2,sK0,sK0)
          & v1_funct_1(X2) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v3_funct_2(sK1,sK0,sK0)
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK2,sK0,sK0)
    & v1_funct_2(sK2,sK0,sK0)
    & v1_funct_1(sK2)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK1,sK0,sK0)
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f40,f44,f43])).

fof(f76,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f45])).

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

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f73,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f27])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_2(X2,X1)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f75,plain,(
    v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( ( k2_relat_1(X1) = k1_xboole_0
              & k2_relat_1(X0) = k1_xboole_0 )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | k2_relat_1(X1) != k1_xboole_0
          | k2_relat_1(X0) != k1_xboole_0
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | k2_relat_1(X1) != k1_xboole_0
          | k2_relat_1(X0) != k1_xboole_0
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f46,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k2_relat_1(X1) != k1_xboole_0
      | k2_relat_1(X0) != k1_xboole_0
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f69,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f70,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f72,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f45])).

fof(f74,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f77,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f45])).

fof(f78,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f45])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_1(X1) = k2_funct_2(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f71,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f9,axiom,(
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
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f25])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f83,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f57])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( ( v2_funct_1(X2)
              & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
              & k2_relset_1(X0,X1,X2) = X1 )
           => ( k2_funct_1(X2) = X3
              | k1_xboole_0 = X1
              | k1_xboole_0 = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_funct_1(X2) = X3
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0
          | ~ v2_funct_1(X2)
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          | k2_relset_1(X0,X1,X2) != X1
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_funct_1(X2) = X3
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0
          | ~ v2_funct_1(X2)
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          | k2_relset_1(X0,X1,X2) != X1
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_funct_1(X2) = X3
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ v2_funct_1(X2)
      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f15,axiom,(
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

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( v2_funct_2(X3,X0)
            & v2_funct_1(X2) )
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( v2_funct_2(X3,X0)
            & v2_funct_1(X2) )
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_funct_1(X2)
      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f13,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f79,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f49,f64])).

fof(f4,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f81,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f50,f64])).

fof(f5,axiom,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f82,plain,(
    ! [X0] : k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0) ),
    inference(definition_unfolding,[],[f52,f64,f64])).

cnf(c_1,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1276,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1263,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_1714,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1263])).

cnf(c_8,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_16,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_313,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_8,c_16])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_325,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | k2_relat_1(X0) = X1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_313,c_7])).

cnf(c_1256,plain,
    ( ~ v2_funct_2(X0_50,X1_50)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X2_50,X1_50)))
    | k2_relat_1(X0_50) = X1_50 ),
    inference(subtyping,[status(esa)],[c_325])).

cnf(c_1721,plain,
    ( k2_relat_1(X0_50) = X1_50
    | v2_funct_2(X0_50,X1_50) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X2_50,X1_50))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1256])).

cnf(c_3326,plain,
    ( k2_relat_1(sK2) = sK0
    | v2_funct_2(sK2,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1714,c_1721])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_12,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | v2_funct_2(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_25,negated_conjecture,
    ( v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_356,plain,
    ( v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | sK2 != X0
    | sK0 != X1
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_25])).

cnf(c_357,plain,
    ( v2_funct_2(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2) ),
    inference(unflattening,[status(thm)],[c_356])).

cnf(c_1924,plain,
    ( ~ v2_funct_2(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_50,sK0)))
    | k2_relat_1(sK2) = sK0 ),
    inference(instantiation,[status(thm)],[c_1256])).

cnf(c_1926,plain,
    ( ~ v2_funct_2(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k2_relat_1(sK2) = sK0 ),
    inference(instantiation,[status(thm)],[c_1924])).

cnf(c_3944,plain,
    ( k2_relat_1(sK2) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3326,c_27,c_24,c_357,c_1926])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | X0 = X1
    | k2_relat_1(X0) != k1_xboole_0
    | k2_relat_1(X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1277,plain,
    ( ~ v1_relat_1(X0_50)
    | ~ v1_relat_1(X1_50)
    | X0_50 = X1_50
    | k2_relat_1(X0_50) != k1_xboole_0
    | k2_relat_1(X1_50) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1704,plain,
    ( X0_50 = X1_50
    | k2_relat_1(X0_50) != k1_xboole_0
    | k2_relat_1(X1_50) != k1_xboole_0
    | v1_relat_1(X0_50) != iProver_top
    | v1_relat_1(X1_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1277])).

cnf(c_3950,plain,
    ( k2_relat_1(X0_50) != k1_xboole_0
    | sK2 = X0_50
    | sK0 != k1_xboole_0
    | v1_relat_1(X0_50) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3944,c_1704])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_39,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_23,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1279,plain,
    ( X0_50 = X0_50 ),
    theory(equality)).

cnf(c_1312,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_1279])).

cnf(c_22,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1265,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1712,plain,
    ( r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1265])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_29,negated_conjecture,
    ( v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_386,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0)
    | sK1 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_29])).

cnf(c_387,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(unflattening,[status(thm)],[c_386])).

cnf(c_389,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_387,c_31,c_30,c_28])).

cnf(c_1251,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(subtyping,[status(esa)],[c_389])).

cnf(c_1755,plain,
    ( r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1712,c_1251])).

cnf(c_1870,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1755])).

cnf(c_1271,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
    | v1_relat_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1906,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1271])).

cnf(c_1907,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1906])).

cnf(c_10,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1269,plain,
    ( r2_relset_1(X0_50,X1_50,X2_50,X2_50)
    | ~ m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1934,plain,
    ( r2_relset_1(sK0,sK0,sK2,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_1269])).

cnf(c_2098,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_1279])).

cnf(c_21,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X3,X1,X0)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | ~ v2_funct_1(X2)
    | k2_relset_1(X0,X1,X2) != X1
    | k2_funct_1(X2) = X3
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_20,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X3,X1,X0)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | v2_funct_1(X2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_162,plain,
    ( ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | k2_relset_1(X0,X1,X2) != X1
    | k2_funct_1(X2) = X3
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_21,c_20])).

cnf(c_163,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X3,X1,X0)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X0,X1,X2) != X1
    | k2_funct_1(X2) = X3
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(renaming,[status(thm)],[c_162])).

cnf(c_1257,plain,
    ( ~ r2_relset_1(X0_50,X0_50,k1_partfun1(X0_50,X1_50,X1_50,X0_50,X2_50,X3_50),k6_partfun1(X0_50))
    | ~ v1_funct_2(X3_50,X1_50,X0_50)
    | ~ v1_funct_2(X2_50,X0_50,X1_50)
    | ~ m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
    | ~ m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X0_50)))
    | ~ v1_funct_1(X2_50)
    | ~ v1_funct_1(X3_50)
    | k2_relset_1(X0_50,X1_50,X2_50) != X1_50
    | k2_funct_1(X2_50) = X3_50
    | k1_xboole_0 = X1_50
    | k1_xboole_0 = X0_50 ),
    inference(subtyping,[status(esa)],[c_163])).

cnf(c_2000,plain,
    ( ~ r2_relset_1(X0_50,X0_50,k1_partfun1(X0_50,X1_50,X1_50,X0_50,sK1,X2_50),k6_partfun1(X0_50))
    | ~ v1_funct_2(X2_50,X1_50,X0_50)
    | ~ v1_funct_2(sK1,X0_50,X1_50)
    | ~ m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X0_50)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
    | ~ v1_funct_1(X2_50)
    | ~ v1_funct_1(sK1)
    | k2_relset_1(X0_50,X1_50,sK1) != X1_50
    | k2_funct_1(sK1) = X2_50
    | k1_xboole_0 = X1_50
    | k1_xboole_0 = X0_50 ),
    inference(instantiation,[status(thm)],[c_1257])).

cnf(c_2203,plain,
    ( ~ r2_relset_1(X0_50,X0_50,k1_partfun1(X0_50,X1_50,X1_50,X0_50,sK1,sK2),k6_partfun1(X0_50))
    | ~ v1_funct_2(sK1,X0_50,X1_50)
    | ~ v1_funct_2(sK2,X1_50,X0_50)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1_50,X0_50)))
    | ~ v1_funct_1(sK1)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X0_50,X1_50,sK1) != X1_50
    | k2_funct_1(sK1) = sK2
    | k1_xboole_0 = X1_50
    | k1_xboole_0 = X0_50 ),
    inference(instantiation,[status(thm)],[c_2000])).

cnf(c_2205,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(sK0,sK0,sK1) != sK0
    | k2_funct_1(sK1) = sK2
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_2203])).

cnf(c_1282,plain,
    ( X0_50 != X1_50
    | X2_50 != X1_50
    | X2_50 = X0_50 ),
    theory(equality)).

cnf(c_2261,plain,
    ( k2_relat_1(sK2) != X0_50
    | k2_relat_1(sK2) = k1_xboole_0
    | k1_xboole_0 != X0_50 ),
    inference(instantiation,[status(thm)],[c_1282])).

cnf(c_2262,plain,
    ( k2_relat_1(sK2) != sK0
    | k2_relat_1(sK2) = k1_xboole_0
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_2261])).

cnf(c_2290,plain,
    ( ~ v1_relat_1(X0_50)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(X0_50) != k1_xboole_0
    | k2_relat_1(sK2) != k1_xboole_0
    | sK2 = X0_50 ),
    inference(instantiation,[status(thm)],[c_1277])).

cnf(c_2291,plain,
    ( k2_relat_1(X0_50) != k1_xboole_0
    | k2_relat_1(sK2) != k1_xboole_0
    | sK2 = X0_50
    | v1_relat_1(X0_50) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2290])).

cnf(c_1260,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_1717,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1260])).

cnf(c_3327,plain,
    ( k2_relat_1(sK1) = sK0
    | v2_funct_2(sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1717,c_1721])).

cnf(c_367,plain,
    ( v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | sK1 != X0
    | sK0 != X1
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_29])).

cnf(c_368,plain,
    ( v2_funct_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1) ),
    inference(unflattening,[status(thm)],[c_367])).

cnf(c_1929,plain,
    ( ~ v2_funct_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0_50,sK0)))
    | k2_relat_1(sK1) = sK0 ),
    inference(instantiation,[status(thm)],[c_1256])).

cnf(c_1931,plain,
    ( ~ v2_funct_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k2_relat_1(sK1) = sK0 ),
    inference(instantiation,[status(thm)],[c_1929])).

cnf(c_3975,plain,
    ( k2_relat_1(sK1) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3327,c_31,c_28,c_368,c_1931])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1270,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
    | k2_relset_1(X1_50,X2_50,X0_50) = k2_relat_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1707,plain,
    ( k2_relset_1(X0_50,X1_50,X2_50) = k2_relat_1(X2_50)
    | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1270])).

cnf(c_2653,plain,
    ( k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_1717,c_1707])).

cnf(c_3978,plain,
    ( k2_relset_1(sK0,sK0,sK1) = sK0 ),
    inference(demodulation,[status(thm)],[c_3975,c_2653])).

cnf(c_1291,plain,
    ( ~ r2_relset_1(X0_50,X1_50,X2_50,X3_50)
    | r2_relset_1(X4_50,X5_50,X6_50,X7_50)
    | X4_50 != X0_50
    | X5_50 != X1_50
    | X6_50 != X2_50
    | X7_50 != X3_50 ),
    theory(equality)).

cnf(c_2034,plain,
    ( r2_relset_1(X0_50,X1_50,X2_50,X3_50)
    | ~ r2_relset_1(sK0,sK0,sK2,sK2)
    | X2_50 != sK2
    | X3_50 != sK2
    | X1_50 != sK0
    | X0_50 != sK0 ),
    inference(instantiation,[status(thm)],[c_1291])).

cnf(c_2356,plain,
    ( r2_relset_1(X0_50,X1_50,sK2,X2_50)
    | ~ r2_relset_1(sK0,sK0,sK2,sK2)
    | X2_50 != sK2
    | X1_50 != sK0
    | X0_50 != sK0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_2034])).

cnf(c_4159,plain,
    ( r2_relset_1(X0_50,X1_50,sK2,k2_funct_1(sK1))
    | ~ r2_relset_1(sK0,sK0,sK2,sK2)
    | X1_50 != sK0
    | X0_50 != sK0
    | k2_funct_1(sK1) != sK2
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_2356])).

cnf(c_4166,plain,
    ( r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1))
    | ~ r2_relset_1(sK0,sK0,sK2,sK2)
    | k2_funct_1(sK1) != sK2
    | sK2 != sK2
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_4159])).

cnf(c_4425,plain,
    ( v1_relat_1(X0_50) != iProver_top
    | k2_relat_1(X0_50) != k1_xboole_0
    | sK2 = X0_50 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3950,c_31,c_30,c_28,c_27,c_26,c_24,c_39,c_23,c_357,c_1312,c_1870,c_1907,c_1926,c_1934,c_2098,c_2205,c_2262,c_2291,c_3978,c_4166])).

cnf(c_4426,plain,
    ( k2_relat_1(X0_50) != k1_xboole_0
    | sK2 = X0_50
    | v1_relat_1(X0_50) != iProver_top ),
    inference(renaming,[status(thm)],[c_4425])).

cnf(c_4434,plain,
    ( sK2 = k1_xboole_0
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1276,c_4426])).

cnf(c_3531,plain,
    ( X0_50 != X1_50
    | X0_50 = k1_xboole_0
    | k1_xboole_0 != X1_50 ),
    inference(instantiation,[status(thm)],[c_1282])).

cnf(c_3532,plain,
    ( sK0 != sK0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_3531])).

cnf(c_2701,plain,
    ( k2_relat_1(X0_50) != k1_xboole_0
    | k1_xboole_0 = X0_50
    | v1_relat_1(X0_50) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1276,c_1704])).

cnf(c_3,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1274,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_5,plain,
    ( v1_relat_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1273,plain,
    ( v1_relat_1(k6_partfun1(X0_50)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1705,plain,
    ( v1_relat_1(k6_partfun1(X0_50)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1273])).

cnf(c_2384,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1274,c_1705])).

cnf(c_2780,plain,
    ( v1_relat_1(X0_50) != iProver_top
    | k1_xboole_0 = X0_50
    | k2_relat_1(X0_50) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2701,c_2384])).

cnf(c_2781,plain,
    ( k2_relat_1(X0_50) != k1_xboole_0
    | k1_xboole_0 = X0_50
    | v1_relat_1(X0_50) != iProver_top ),
    inference(renaming,[status(thm)],[c_2780])).

cnf(c_3949,plain,
    ( sK2 = k1_xboole_0
    | sK0 != k1_xboole_0
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3944,c_2781])).

cnf(c_4501,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4434,c_31,c_30,c_28,c_27,c_26,c_24,c_39,c_23,c_1312,c_1870,c_1907,c_1934,c_2098,c_2205,c_3532,c_3949,c_3978,c_4166])).

cnf(c_4509,plain,
    ( k2_relat_1(k1_xboole_0) = sK0 ),
    inference(demodulation,[status(thm)],[c_4501,c_3944])).

cnf(c_4537,plain,
    ( sK0 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4509,c_1276])).

cnf(c_4512,plain,
    ( r2_relset_1(sK0,sK0,k1_xboole_0,k2_funct_1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4501,c_1755])).

cnf(c_4539,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4537,c_4512])).

cnf(c_6,plain,
    ( k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1272,plain,
    ( k2_funct_1(k6_partfun1(X0_50)) = k6_partfun1(X0_50) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_2046,plain,
    ( k2_funct_1(k1_xboole_0) = k6_partfun1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1274,c_1272])).

cnf(c_2047,plain,
    ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2046,c_1274])).

cnf(c_3980,plain,
    ( sK1 = k1_xboole_0
    | sK0 != k1_xboole_0
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3975,c_2781])).

cnf(c_35,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_1909,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_1271])).

cnf(c_1910,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1909])).

cnf(c_5257,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3980,c_31,c_30,c_28,c_35,c_27,c_26,c_24,c_23,c_1312,c_1870,c_1910,c_1934,c_2098,c_2205,c_3532,c_3978,c_4166])).

cnf(c_5322,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4539,c_2047,c_5257])).

cnf(c_1708,plain,
    ( r2_relset_1(X0_50,X1_50,X2_50,X2_50) = iProver_top
    | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1269])).

cnf(c_2687,plain,
    ( r2_relset_1(sK0,sK0,sK2,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1714,c_1708])).

cnf(c_4510,plain,
    ( r2_relset_1(sK0,sK0,k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4501,c_2687])).

cnf(c_4538,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4537,c_4510])).

cnf(c_5324,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5322,c_4538])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.11  % Command    : iproveropt_run.sh %d %s
% 0.10/0.32  % Computer   : n021.cluster.edu
% 0.10/0.32  % Model      : x86_64 x86_64
% 0.10/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.32  % Memory     : 8042.1875MB
% 0.10/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.32  % CPULimit   : 60
% 0.10/0.32  % WCLimit    : 600
% 0.10/0.32  % DateTime   : Tue Dec  1 13:59:19 EST 2020
% 0.10/0.32  % CPUTime    : 
% 0.10/0.32  % Running in FOF mode
% 2.43/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.43/0.98  
% 2.43/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.43/0.98  
% 2.43/0.98  ------  iProver source info
% 2.43/0.98  
% 2.43/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.43/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.43/0.98  git: non_committed_changes: false
% 2.43/0.98  git: last_make_outside_of_git: false
% 2.43/0.98  
% 2.43/0.98  ------ 
% 2.43/0.98  
% 2.43/0.98  ------ Input Options
% 2.43/0.98  
% 2.43/0.98  --out_options                           all
% 2.43/0.98  --tptp_safe_out                         true
% 2.43/0.98  --problem_path                          ""
% 2.43/0.98  --include_path                          ""
% 2.43/0.98  --clausifier                            res/vclausify_rel
% 2.43/0.98  --clausifier_options                    --mode clausify
% 2.43/0.98  --stdin                                 false
% 2.43/0.98  --stats_out                             all
% 2.43/0.98  
% 2.43/0.98  ------ General Options
% 2.43/0.98  
% 2.43/0.98  --fof                                   false
% 2.43/0.98  --time_out_real                         305.
% 2.43/0.98  --time_out_virtual                      -1.
% 2.43/0.98  --symbol_type_check                     false
% 2.43/0.98  --clausify_out                          false
% 2.43/0.98  --sig_cnt_out                           false
% 2.43/0.98  --trig_cnt_out                          false
% 2.43/0.98  --trig_cnt_out_tolerance                1.
% 2.43/0.98  --trig_cnt_out_sk_spl                   false
% 2.43/0.98  --abstr_cl_out                          false
% 2.43/0.98  
% 2.43/0.98  ------ Global Options
% 2.43/0.98  
% 2.43/0.98  --schedule                              default
% 2.43/0.98  --add_important_lit                     false
% 2.43/0.98  --prop_solver_per_cl                    1000
% 2.43/0.98  --min_unsat_core                        false
% 2.43/0.98  --soft_assumptions                      false
% 2.43/0.98  --soft_lemma_size                       3
% 2.43/0.98  --prop_impl_unit_size                   0
% 2.43/0.98  --prop_impl_unit                        []
% 2.43/0.98  --share_sel_clauses                     true
% 2.43/0.98  --reset_solvers                         false
% 2.43/0.98  --bc_imp_inh                            [conj_cone]
% 2.43/0.98  --conj_cone_tolerance                   3.
% 2.43/0.98  --extra_neg_conj                        none
% 2.43/0.98  --large_theory_mode                     true
% 2.43/0.98  --prolific_symb_bound                   200
% 2.43/0.98  --lt_threshold                          2000
% 2.43/0.98  --clause_weak_htbl                      true
% 2.43/0.98  --gc_record_bc_elim                     false
% 2.43/0.98  
% 2.43/0.98  ------ Preprocessing Options
% 2.43/0.98  
% 2.43/0.98  --preprocessing_flag                    true
% 2.43/0.98  --time_out_prep_mult                    0.1
% 2.43/0.98  --splitting_mode                        input
% 2.43/0.98  --splitting_grd                         true
% 2.43/0.98  --splitting_cvd                         false
% 2.43/0.98  --splitting_cvd_svl                     false
% 2.43/0.98  --splitting_nvd                         32
% 2.43/0.98  --sub_typing                            true
% 2.43/0.98  --prep_gs_sim                           true
% 2.43/0.98  --prep_unflatten                        true
% 2.43/0.98  --prep_res_sim                          true
% 2.43/0.98  --prep_upred                            true
% 2.43/0.98  --prep_sem_filter                       exhaustive
% 2.43/0.98  --prep_sem_filter_out                   false
% 2.43/0.98  --pred_elim                             true
% 2.43/0.98  --res_sim_input                         true
% 2.43/0.98  --eq_ax_congr_red                       true
% 2.43/0.98  --pure_diseq_elim                       true
% 2.43/0.98  --brand_transform                       false
% 2.43/0.98  --non_eq_to_eq                          false
% 2.43/0.98  --prep_def_merge                        true
% 2.43/0.98  --prep_def_merge_prop_impl              false
% 2.43/0.98  --prep_def_merge_mbd                    true
% 2.43/0.98  --prep_def_merge_tr_red                 false
% 2.43/0.98  --prep_def_merge_tr_cl                  false
% 2.43/0.98  --smt_preprocessing                     true
% 2.43/0.98  --smt_ac_axioms                         fast
% 2.43/0.98  --preprocessed_out                      false
% 2.43/0.98  --preprocessed_stats                    false
% 2.43/0.98  
% 2.43/0.98  ------ Abstraction refinement Options
% 2.43/0.98  
% 2.43/0.98  --abstr_ref                             []
% 2.43/0.98  --abstr_ref_prep                        false
% 2.43/0.98  --abstr_ref_until_sat                   false
% 2.43/0.98  --abstr_ref_sig_restrict                funpre
% 2.43/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.43/0.98  --abstr_ref_under                       []
% 2.43/0.98  
% 2.43/0.98  ------ SAT Options
% 2.43/0.98  
% 2.43/0.98  --sat_mode                              false
% 2.43/0.98  --sat_fm_restart_options                ""
% 2.43/0.98  --sat_gr_def                            false
% 2.43/0.98  --sat_epr_types                         true
% 2.43/0.98  --sat_non_cyclic_types                  false
% 2.43/0.98  --sat_finite_models                     false
% 2.43/0.98  --sat_fm_lemmas                         false
% 2.43/0.98  --sat_fm_prep                           false
% 2.43/0.98  --sat_fm_uc_incr                        true
% 2.43/0.98  --sat_out_model                         small
% 2.43/0.98  --sat_out_clauses                       false
% 2.43/0.98  
% 2.43/0.98  ------ QBF Options
% 2.43/0.98  
% 2.43/0.98  --qbf_mode                              false
% 2.43/0.98  --qbf_elim_univ                         false
% 2.43/0.98  --qbf_dom_inst                          none
% 2.43/0.98  --qbf_dom_pre_inst                      false
% 2.43/0.98  --qbf_sk_in                             false
% 2.43/0.98  --qbf_pred_elim                         true
% 2.43/0.98  --qbf_split                             512
% 2.43/0.98  
% 2.43/0.98  ------ BMC1 Options
% 2.43/0.98  
% 2.43/0.98  --bmc1_incremental                      false
% 2.43/0.98  --bmc1_axioms                           reachable_all
% 2.43/0.98  --bmc1_min_bound                        0
% 2.43/0.98  --bmc1_max_bound                        -1
% 2.43/0.98  --bmc1_max_bound_default                -1
% 2.43/0.98  --bmc1_symbol_reachability              true
% 2.43/0.98  --bmc1_property_lemmas                  false
% 2.43/0.98  --bmc1_k_induction                      false
% 2.43/0.98  --bmc1_non_equiv_states                 false
% 2.43/0.98  --bmc1_deadlock                         false
% 2.43/0.98  --bmc1_ucm                              false
% 2.43/0.98  --bmc1_add_unsat_core                   none
% 2.43/0.98  --bmc1_unsat_core_children              false
% 2.43/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.43/0.98  --bmc1_out_stat                         full
% 2.43/0.98  --bmc1_ground_init                      false
% 2.43/0.98  --bmc1_pre_inst_next_state              false
% 2.43/0.98  --bmc1_pre_inst_state                   false
% 2.43/0.98  --bmc1_pre_inst_reach_state             false
% 2.43/0.98  --bmc1_out_unsat_core                   false
% 2.43/0.98  --bmc1_aig_witness_out                  false
% 2.43/0.98  --bmc1_verbose                          false
% 2.43/0.98  --bmc1_dump_clauses_tptp                false
% 2.43/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.43/0.98  --bmc1_dump_file                        -
% 2.43/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.43/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.43/0.98  --bmc1_ucm_extend_mode                  1
% 2.43/0.98  --bmc1_ucm_init_mode                    2
% 2.43/0.98  --bmc1_ucm_cone_mode                    none
% 2.43/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.43/0.98  --bmc1_ucm_relax_model                  4
% 2.43/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.43/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.43/0.98  --bmc1_ucm_layered_model                none
% 2.43/0.98  --bmc1_ucm_max_lemma_size               10
% 2.43/0.98  
% 2.43/0.98  ------ AIG Options
% 2.43/0.98  
% 2.43/0.98  --aig_mode                              false
% 2.43/0.98  
% 2.43/0.98  ------ Instantiation Options
% 2.43/0.98  
% 2.43/0.98  --instantiation_flag                    true
% 2.43/0.98  --inst_sos_flag                         false
% 2.43/0.98  --inst_sos_phase                        true
% 2.43/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.43/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.43/0.98  --inst_lit_sel_side                     num_symb
% 2.43/0.98  --inst_solver_per_active                1400
% 2.43/0.98  --inst_solver_calls_frac                1.
% 2.43/0.98  --inst_passive_queue_type               priority_queues
% 2.43/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.43/0.98  --inst_passive_queues_freq              [25;2]
% 2.43/0.98  --inst_dismatching                      true
% 2.43/0.98  --inst_eager_unprocessed_to_passive     true
% 2.43/0.98  --inst_prop_sim_given                   true
% 2.43/0.98  --inst_prop_sim_new                     false
% 2.43/0.98  --inst_subs_new                         false
% 2.43/0.98  --inst_eq_res_simp                      false
% 2.43/0.98  --inst_subs_given                       false
% 2.43/0.98  --inst_orphan_elimination               true
% 2.43/0.98  --inst_learning_loop_flag               true
% 2.43/0.98  --inst_learning_start                   3000
% 2.43/0.98  --inst_learning_factor                  2
% 2.43/0.98  --inst_start_prop_sim_after_learn       3
% 2.43/0.98  --inst_sel_renew                        solver
% 2.43/0.98  --inst_lit_activity_flag                true
% 2.43/0.98  --inst_restr_to_given                   false
% 2.43/0.98  --inst_activity_threshold               500
% 2.43/0.98  --inst_out_proof                        true
% 2.43/0.98  
% 2.43/0.98  ------ Resolution Options
% 2.43/0.98  
% 2.43/0.98  --resolution_flag                       true
% 2.43/0.98  --res_lit_sel                           adaptive
% 2.43/0.98  --res_lit_sel_side                      none
% 2.43/0.98  --res_ordering                          kbo
% 2.43/0.98  --res_to_prop_solver                    active
% 2.43/0.98  --res_prop_simpl_new                    false
% 2.43/0.98  --res_prop_simpl_given                  true
% 2.43/0.98  --res_passive_queue_type                priority_queues
% 2.43/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.43/0.98  --res_passive_queues_freq               [15;5]
% 2.43/0.98  --res_forward_subs                      full
% 2.43/0.98  --res_backward_subs                     full
% 2.43/0.98  --res_forward_subs_resolution           true
% 2.43/0.98  --res_backward_subs_resolution          true
% 2.43/0.98  --res_orphan_elimination                true
% 2.43/0.98  --res_time_limit                        2.
% 2.43/0.98  --res_out_proof                         true
% 2.43/0.98  
% 2.43/0.98  ------ Superposition Options
% 2.43/0.98  
% 2.43/0.98  --superposition_flag                    true
% 2.43/0.98  --sup_passive_queue_type                priority_queues
% 2.43/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.43/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.43/0.98  --demod_completeness_check              fast
% 2.43/0.98  --demod_use_ground                      true
% 2.43/0.98  --sup_to_prop_solver                    passive
% 2.43/0.98  --sup_prop_simpl_new                    true
% 2.43/0.98  --sup_prop_simpl_given                  true
% 2.43/0.98  --sup_fun_splitting                     false
% 2.43/0.98  --sup_smt_interval                      50000
% 2.43/0.98  
% 2.43/0.98  ------ Superposition Simplification Setup
% 2.43/0.98  
% 2.43/0.98  --sup_indices_passive                   []
% 2.43/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.43/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.43/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.43/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.43/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.43/0.98  --sup_full_bw                           [BwDemod]
% 2.43/0.98  --sup_immed_triv                        [TrivRules]
% 2.43/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.43/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.43/0.98  --sup_immed_bw_main                     []
% 2.43/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.43/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.43/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.43/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.43/0.98  
% 2.43/0.98  ------ Combination Options
% 2.43/0.98  
% 2.43/0.98  --comb_res_mult                         3
% 2.43/0.98  --comb_sup_mult                         2
% 2.43/0.98  --comb_inst_mult                        10
% 2.43/0.98  
% 2.43/0.98  ------ Debug Options
% 2.43/0.98  
% 2.43/0.98  --dbg_backtrace                         false
% 2.43/0.98  --dbg_dump_prop_clauses                 false
% 2.43/0.98  --dbg_dump_prop_clauses_file            -
% 2.43/0.98  --dbg_out_stat                          false
% 2.43/0.98  ------ Parsing...
% 2.43/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.43/0.98  
% 2.43/0.98  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.43/0.98  
% 2.43/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.43/0.98  
% 2.43/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.43/0.98  ------ Proving...
% 2.43/0.98  ------ Problem Properties 
% 2.43/0.98  
% 2.43/0.98  
% 2.43/0.98  clauses                                 27
% 2.43/0.98  conjectures                             8
% 2.43/0.98  EPR                                     6
% 2.43/0.98  Horn                                    26
% 2.43/0.98  unary                                   17
% 2.43/0.98  binary                                  4
% 2.43/0.98  lits                                    64
% 2.43/0.98  lits eq                                 17
% 2.43/0.98  fd_pure                                 0
% 2.43/0.98  fd_pseudo                               0
% 2.43/0.98  fd_cond                                 0
% 2.43/0.98  fd_pseudo_cond                          4
% 2.43/0.98  AC symbols                              0
% 2.43/0.98  
% 2.43/0.98  ------ Schedule dynamic 5 is on 
% 2.43/0.98  
% 2.43/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.43/0.98  
% 2.43/0.98  
% 2.43/0.98  ------ 
% 2.43/0.98  Current options:
% 2.43/0.98  ------ 
% 2.43/0.98  
% 2.43/0.98  ------ Input Options
% 2.43/0.98  
% 2.43/0.98  --out_options                           all
% 2.43/0.98  --tptp_safe_out                         true
% 2.43/0.98  --problem_path                          ""
% 2.43/0.98  --include_path                          ""
% 2.43/0.98  --clausifier                            res/vclausify_rel
% 2.43/0.98  --clausifier_options                    --mode clausify
% 2.43/0.98  --stdin                                 false
% 2.43/0.98  --stats_out                             all
% 2.43/0.98  
% 2.43/0.98  ------ General Options
% 2.43/0.98  
% 2.43/0.98  --fof                                   false
% 2.43/0.98  --time_out_real                         305.
% 2.43/0.98  --time_out_virtual                      -1.
% 2.43/0.98  --symbol_type_check                     false
% 2.43/0.98  --clausify_out                          false
% 2.43/0.98  --sig_cnt_out                           false
% 2.43/0.98  --trig_cnt_out                          false
% 2.43/0.98  --trig_cnt_out_tolerance                1.
% 2.43/0.98  --trig_cnt_out_sk_spl                   false
% 2.43/0.98  --abstr_cl_out                          false
% 2.43/0.98  
% 2.43/0.98  ------ Global Options
% 2.43/0.98  
% 2.43/0.98  --schedule                              default
% 2.43/0.98  --add_important_lit                     false
% 2.43/0.98  --prop_solver_per_cl                    1000
% 2.43/0.98  --min_unsat_core                        false
% 2.43/0.98  --soft_assumptions                      false
% 2.43/0.98  --soft_lemma_size                       3
% 2.43/0.98  --prop_impl_unit_size                   0
% 2.43/0.98  --prop_impl_unit                        []
% 2.43/0.98  --share_sel_clauses                     true
% 2.43/0.98  --reset_solvers                         false
% 2.43/0.98  --bc_imp_inh                            [conj_cone]
% 2.43/0.98  --conj_cone_tolerance                   3.
% 2.43/0.98  --extra_neg_conj                        none
% 2.43/0.98  --large_theory_mode                     true
% 2.43/0.98  --prolific_symb_bound                   200
% 2.43/0.98  --lt_threshold                          2000
% 2.43/0.98  --clause_weak_htbl                      true
% 2.43/0.98  --gc_record_bc_elim                     false
% 2.43/0.98  
% 2.43/0.98  ------ Preprocessing Options
% 2.43/0.98  
% 2.43/0.98  --preprocessing_flag                    true
% 2.43/0.98  --time_out_prep_mult                    0.1
% 2.43/0.98  --splitting_mode                        input
% 2.43/0.98  --splitting_grd                         true
% 2.43/0.98  --splitting_cvd                         false
% 2.43/0.98  --splitting_cvd_svl                     false
% 2.43/0.98  --splitting_nvd                         32
% 2.43/0.98  --sub_typing                            true
% 2.43/0.98  --prep_gs_sim                           true
% 2.43/0.98  --prep_unflatten                        true
% 2.43/0.98  --prep_res_sim                          true
% 2.43/0.98  --prep_upred                            true
% 2.43/0.98  --prep_sem_filter                       exhaustive
% 2.43/0.98  --prep_sem_filter_out                   false
% 2.43/0.98  --pred_elim                             true
% 2.43/0.98  --res_sim_input                         true
% 2.43/0.98  --eq_ax_congr_red                       true
% 2.43/0.98  --pure_diseq_elim                       true
% 2.43/0.98  --brand_transform                       false
% 2.43/0.98  --non_eq_to_eq                          false
% 2.43/0.98  --prep_def_merge                        true
% 2.43/0.98  --prep_def_merge_prop_impl              false
% 2.43/0.98  --prep_def_merge_mbd                    true
% 2.43/0.98  --prep_def_merge_tr_red                 false
% 2.43/0.98  --prep_def_merge_tr_cl                  false
% 2.43/0.98  --smt_preprocessing                     true
% 2.43/0.98  --smt_ac_axioms                         fast
% 2.43/0.98  --preprocessed_out                      false
% 2.43/0.98  --preprocessed_stats                    false
% 2.43/0.98  
% 2.43/0.98  ------ Abstraction refinement Options
% 2.43/0.98  
% 2.43/0.98  --abstr_ref                             []
% 2.43/0.98  --abstr_ref_prep                        false
% 2.43/0.98  --abstr_ref_until_sat                   false
% 2.43/0.98  --abstr_ref_sig_restrict                funpre
% 2.43/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.43/0.98  --abstr_ref_under                       []
% 2.43/0.98  
% 2.43/0.98  ------ SAT Options
% 2.43/0.98  
% 2.43/0.98  --sat_mode                              false
% 2.43/0.98  --sat_fm_restart_options                ""
% 2.43/0.98  --sat_gr_def                            false
% 2.43/0.98  --sat_epr_types                         true
% 2.43/0.98  --sat_non_cyclic_types                  false
% 2.43/0.98  --sat_finite_models                     false
% 2.43/0.98  --sat_fm_lemmas                         false
% 2.43/0.98  --sat_fm_prep                           false
% 2.43/0.98  --sat_fm_uc_incr                        true
% 2.43/0.98  --sat_out_model                         small
% 2.43/0.98  --sat_out_clauses                       false
% 2.43/0.98  
% 2.43/0.98  ------ QBF Options
% 2.43/0.98  
% 2.43/0.98  --qbf_mode                              false
% 2.43/0.98  --qbf_elim_univ                         false
% 2.43/0.98  --qbf_dom_inst                          none
% 2.43/0.98  --qbf_dom_pre_inst                      false
% 2.43/0.98  --qbf_sk_in                             false
% 2.43/0.98  --qbf_pred_elim                         true
% 2.43/0.98  --qbf_split                             512
% 2.43/0.98  
% 2.43/0.98  ------ BMC1 Options
% 2.43/0.98  
% 2.43/0.98  --bmc1_incremental                      false
% 2.43/0.98  --bmc1_axioms                           reachable_all
% 2.43/0.98  --bmc1_min_bound                        0
% 2.43/0.98  --bmc1_max_bound                        -1
% 2.43/0.98  --bmc1_max_bound_default                -1
% 2.43/0.98  --bmc1_symbol_reachability              true
% 2.43/0.98  --bmc1_property_lemmas                  false
% 2.43/0.98  --bmc1_k_induction                      false
% 2.43/0.98  --bmc1_non_equiv_states                 false
% 2.43/0.98  --bmc1_deadlock                         false
% 2.43/0.98  --bmc1_ucm                              false
% 2.43/0.98  --bmc1_add_unsat_core                   none
% 2.43/0.98  --bmc1_unsat_core_children              false
% 2.43/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.43/0.98  --bmc1_out_stat                         full
% 2.43/0.98  --bmc1_ground_init                      false
% 2.43/0.98  --bmc1_pre_inst_next_state              false
% 2.43/0.98  --bmc1_pre_inst_state                   false
% 2.43/0.98  --bmc1_pre_inst_reach_state             false
% 2.43/0.98  --bmc1_out_unsat_core                   false
% 2.43/0.98  --bmc1_aig_witness_out                  false
% 2.43/0.98  --bmc1_verbose                          false
% 2.43/0.98  --bmc1_dump_clauses_tptp                false
% 2.43/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.43/0.98  --bmc1_dump_file                        -
% 2.43/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.43/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.43/0.98  --bmc1_ucm_extend_mode                  1
% 2.43/0.98  --bmc1_ucm_init_mode                    2
% 2.43/0.98  --bmc1_ucm_cone_mode                    none
% 2.43/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.43/0.98  --bmc1_ucm_relax_model                  4
% 2.43/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.43/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.43/0.98  --bmc1_ucm_layered_model                none
% 2.43/0.98  --bmc1_ucm_max_lemma_size               10
% 2.43/0.98  
% 2.43/0.98  ------ AIG Options
% 2.43/0.98  
% 2.43/0.98  --aig_mode                              false
% 2.43/0.98  
% 2.43/0.98  ------ Instantiation Options
% 2.43/0.98  
% 2.43/0.98  --instantiation_flag                    true
% 2.43/0.98  --inst_sos_flag                         false
% 2.43/0.98  --inst_sos_phase                        true
% 2.43/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.43/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.43/0.98  --inst_lit_sel_side                     none
% 2.43/0.98  --inst_solver_per_active                1400
% 2.43/0.98  --inst_solver_calls_frac                1.
% 2.43/0.98  --inst_passive_queue_type               priority_queues
% 2.43/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.43/0.98  --inst_passive_queues_freq              [25;2]
% 2.43/0.98  --inst_dismatching                      true
% 2.43/0.98  --inst_eager_unprocessed_to_passive     true
% 2.43/0.98  --inst_prop_sim_given                   true
% 2.43/0.98  --inst_prop_sim_new                     false
% 2.43/0.98  --inst_subs_new                         false
% 2.43/0.98  --inst_eq_res_simp                      false
% 2.43/0.98  --inst_subs_given                       false
% 2.43/0.98  --inst_orphan_elimination               true
% 2.43/0.98  --inst_learning_loop_flag               true
% 2.43/0.98  --inst_learning_start                   3000
% 2.43/0.98  --inst_learning_factor                  2
% 2.43/0.98  --inst_start_prop_sim_after_learn       3
% 2.43/0.98  --inst_sel_renew                        solver
% 2.43/0.98  --inst_lit_activity_flag                true
% 2.43/0.98  --inst_restr_to_given                   false
% 2.43/0.98  --inst_activity_threshold               500
% 2.43/0.98  --inst_out_proof                        true
% 2.43/0.98  
% 2.43/0.98  ------ Resolution Options
% 2.43/0.98  
% 2.43/0.98  --resolution_flag                       false
% 2.43/0.98  --res_lit_sel                           adaptive
% 2.43/0.98  --res_lit_sel_side                      none
% 2.43/0.98  --res_ordering                          kbo
% 2.43/0.98  --res_to_prop_solver                    active
% 2.43/0.98  --res_prop_simpl_new                    false
% 2.43/0.98  --res_prop_simpl_given                  true
% 2.43/0.98  --res_passive_queue_type                priority_queues
% 2.43/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.43/0.98  --res_passive_queues_freq               [15;5]
% 2.43/0.98  --res_forward_subs                      full
% 2.43/0.98  --res_backward_subs                     full
% 2.43/0.98  --res_forward_subs_resolution           true
% 2.43/0.98  --res_backward_subs_resolution          true
% 2.43/0.98  --res_orphan_elimination                true
% 2.43/0.98  --res_time_limit                        2.
% 2.43/0.98  --res_out_proof                         true
% 2.43/0.98  
% 2.43/0.98  ------ Superposition Options
% 2.43/0.98  
% 2.43/0.98  --superposition_flag                    true
% 2.43/0.98  --sup_passive_queue_type                priority_queues
% 2.43/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.43/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.43/0.98  --demod_completeness_check              fast
% 2.43/0.98  --demod_use_ground                      true
% 2.43/0.98  --sup_to_prop_solver                    passive
% 2.43/0.98  --sup_prop_simpl_new                    true
% 2.43/0.98  --sup_prop_simpl_given                  true
% 2.43/0.98  --sup_fun_splitting                     false
% 2.43/0.98  --sup_smt_interval                      50000
% 2.43/0.98  
% 2.43/0.98  ------ Superposition Simplification Setup
% 2.43/0.98  
% 2.43/0.98  --sup_indices_passive                   []
% 2.43/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.43/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.43/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.43/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.43/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.43/0.98  --sup_full_bw                           [BwDemod]
% 2.43/0.98  --sup_immed_triv                        [TrivRules]
% 2.43/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.43/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.43/0.98  --sup_immed_bw_main                     []
% 2.43/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.43/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.43/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.43/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.43/0.98  
% 2.43/0.98  ------ Combination Options
% 2.43/0.98  
% 2.43/0.98  --comb_res_mult                         3
% 2.43/0.98  --comb_sup_mult                         2
% 2.43/0.98  --comb_inst_mult                        10
% 2.43/0.98  
% 2.43/0.98  ------ Debug Options
% 2.43/0.98  
% 2.43/0.98  --dbg_backtrace                         false
% 2.43/0.98  --dbg_dump_prop_clauses                 false
% 2.43/0.98  --dbg_dump_prop_clauses_file            -
% 2.43/0.98  --dbg_out_stat                          false
% 2.43/0.98  
% 2.43/0.98  
% 2.43/0.98  
% 2.43/0.98  
% 2.43/0.98  ------ Proving...
% 2.43/0.98  
% 2.43/0.98  
% 2.43/0.98  % SZS status Theorem for theBenchmark.p
% 2.43/0.98  
% 2.43/0.98   Resolution empty clause
% 2.43/0.98  
% 2.43/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.43/0.98  
% 2.43/0.98  fof(f2,axiom,(
% 2.43/0.98    k2_relat_1(k1_xboole_0) = k1_xboole_0 & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.43/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/0.98  
% 2.43/0.98  fof(f48,plain,(
% 2.43/0.98    k2_relat_1(k1_xboole_0) = k1_xboole_0),
% 2.43/0.98    inference(cnf_transformation,[],[f2])).
% 2.43/0.98  
% 2.43/0.98  fof(f17,conjecture,(
% 2.43/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 2.43/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/0.98  
% 2.43/0.98  fof(f18,negated_conjecture,(
% 2.43/0.98    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 2.43/0.98    inference(negated_conjecture,[],[f17])).
% 2.43/0.98  
% 2.43/0.98  fof(f39,plain,(
% 2.43/0.98    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 2.43/0.98    inference(ennf_transformation,[],[f18])).
% 2.43/0.98  
% 2.43/0.98  fof(f40,plain,(
% 2.43/0.98    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 2.43/0.98    inference(flattening,[],[f39])).
% 2.43/0.98  
% 2.43/0.98  fof(f44,plain,(
% 2.43/0.98    ( ! [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (~r2_relset_1(X0,X0,sK2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,sK2),k6_partfun1(X0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(sK2,X0,X0) & v1_funct_2(sK2,X0,X0) & v1_funct_1(sK2))) )),
% 2.43/0.98    introduced(choice_axiom,[])).
% 2.43/0.98  
% 2.43/0.98  fof(f43,plain,(
% 2.43/0.98    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(X2,sK0,sK0) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 2.43/0.98    introduced(choice_axiom,[])).
% 2.43/0.98  
% 2.43/0.98  fof(f45,plain,(
% 2.43/0.98    (~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 2.43/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f40,f44,f43])).
% 2.43/0.98  
% 2.43/0.98  fof(f76,plain,(
% 2.43/0.98    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.43/0.98    inference(cnf_transformation,[],[f45])).
% 2.43/0.98  
% 2.43/0.98  fof(f7,axiom,(
% 2.43/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.43/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/0.98  
% 2.43/0.98  fof(f19,plain,(
% 2.43/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 2.43/0.98    inference(pure_predicate_removal,[],[f7])).
% 2.43/0.98  
% 2.43/0.98  fof(f23,plain,(
% 2.43/0.98    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.43/0.98    inference(ennf_transformation,[],[f19])).
% 2.43/0.98  
% 2.43/0.98  fof(f54,plain,(
% 2.43/0.98    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.43/0.98    inference(cnf_transformation,[],[f23])).
% 2.43/0.98  
% 2.43/0.98  fof(f11,axiom,(
% 2.43/0.98    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 2.43/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/0.98  
% 2.43/0.98  fof(f29,plain,(
% 2.43/0.98    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.43/0.98    inference(ennf_transformation,[],[f11])).
% 2.43/0.98  
% 2.43/0.98  fof(f30,plain,(
% 2.43/0.98    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.43/0.98    inference(flattening,[],[f29])).
% 2.43/0.98  
% 2.43/0.98  fof(f42,plain,(
% 2.43/0.98    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.43/0.98    inference(nnf_transformation,[],[f30])).
% 2.43/0.98  
% 2.43/0.98  fof(f61,plain,(
% 2.43/0.98    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.43/0.98    inference(cnf_transformation,[],[f42])).
% 2.43/0.98  
% 2.43/0.98  fof(f6,axiom,(
% 2.43/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.43/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/0.98  
% 2.43/0.98  fof(f22,plain,(
% 2.43/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.43/0.98    inference(ennf_transformation,[],[f6])).
% 2.43/0.98  
% 2.43/0.98  fof(f53,plain,(
% 2.43/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.43/0.98    inference(cnf_transformation,[],[f22])).
% 2.43/0.98  
% 2.43/0.98  fof(f73,plain,(
% 2.43/0.98    v1_funct_1(sK2)),
% 2.43/0.98    inference(cnf_transformation,[],[f45])).
% 2.43/0.98  
% 2.43/0.98  fof(f10,axiom,(
% 2.43/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 2.43/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/0.98  
% 2.43/0.98  fof(f27,plain,(
% 2.43/0.98    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.43/0.98    inference(ennf_transformation,[],[f10])).
% 2.43/0.98  
% 2.43/0.98  fof(f28,plain,(
% 2.43/0.98    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.43/0.98    inference(flattening,[],[f27])).
% 2.43/0.98  
% 2.43/0.98  fof(f60,plain,(
% 2.43/0.98    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.43/0.98    inference(cnf_transformation,[],[f28])).
% 2.43/0.98  
% 2.43/0.98  fof(f75,plain,(
% 2.43/0.98    v3_funct_2(sK2,sK0,sK0)),
% 2.43/0.98    inference(cnf_transformation,[],[f45])).
% 2.43/0.98  
% 2.43/0.98  fof(f1,axiom,(
% 2.43/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ((k2_relat_1(X1) = k1_xboole_0 & k2_relat_1(X0) = k1_xboole_0) => X0 = X1)))),
% 2.43/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/0.98  
% 2.43/0.98  fof(f20,plain,(
% 2.43/0.98    ! [X0] : (! [X1] : ((X0 = X1 | (k2_relat_1(X1) != k1_xboole_0 | k2_relat_1(X0) != k1_xboole_0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.43/0.98    inference(ennf_transformation,[],[f1])).
% 2.43/0.98  
% 2.43/0.98  fof(f21,plain,(
% 2.43/0.98    ! [X0] : (! [X1] : (X0 = X1 | k2_relat_1(X1) != k1_xboole_0 | k2_relat_1(X0) != k1_xboole_0 | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.43/0.98    inference(flattening,[],[f20])).
% 2.43/0.98  
% 2.43/0.98  fof(f46,plain,(
% 2.43/0.98    ( ! [X0,X1] : (X0 = X1 | k2_relat_1(X1) != k1_xboole_0 | k2_relat_1(X0) != k1_xboole_0 | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.43/0.98    inference(cnf_transformation,[],[f21])).
% 2.43/0.98  
% 2.43/0.98  fof(f69,plain,(
% 2.43/0.98    v1_funct_1(sK1)),
% 2.43/0.98    inference(cnf_transformation,[],[f45])).
% 2.43/0.98  
% 2.43/0.98  fof(f70,plain,(
% 2.43/0.98    v1_funct_2(sK1,sK0,sK0)),
% 2.43/0.98    inference(cnf_transformation,[],[f45])).
% 2.43/0.98  
% 2.43/0.98  fof(f72,plain,(
% 2.43/0.98    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.43/0.98    inference(cnf_transformation,[],[f45])).
% 2.43/0.98  
% 2.43/0.98  fof(f74,plain,(
% 2.43/0.98    v1_funct_2(sK2,sK0,sK0)),
% 2.43/0.98    inference(cnf_transformation,[],[f45])).
% 2.43/0.98  
% 2.43/0.98  fof(f77,plain,(
% 2.43/0.98    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))),
% 2.43/0.98    inference(cnf_transformation,[],[f45])).
% 2.43/0.98  
% 2.43/0.98  fof(f78,plain,(
% 2.43/0.98    ~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))),
% 2.43/0.98    inference(cnf_transformation,[],[f45])).
% 2.43/0.98  
% 2.43/0.98  fof(f12,axiom,(
% 2.43/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_1(X1) = k2_funct_2(X0,X1))),
% 2.43/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/0.98  
% 2.43/0.98  fof(f31,plain,(
% 2.43/0.98    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 2.43/0.98    inference(ennf_transformation,[],[f12])).
% 2.43/0.98  
% 2.43/0.98  fof(f32,plain,(
% 2.43/0.98    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 2.43/0.98    inference(flattening,[],[f31])).
% 2.43/0.98  
% 2.43/0.98  fof(f63,plain,(
% 2.43/0.98    ( ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 2.43/0.98    inference(cnf_transformation,[],[f32])).
% 2.43/0.98  
% 2.43/0.98  fof(f71,plain,(
% 2.43/0.98    v3_funct_2(sK1,sK0,sK0)),
% 2.43/0.98    inference(cnf_transformation,[],[f45])).
% 2.43/0.98  
% 2.43/0.98  fof(f9,axiom,(
% 2.43/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.43/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/0.98  
% 2.43/0.98  fof(f25,plain,(
% 2.43/0.98    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.43/0.98    inference(ennf_transformation,[],[f9])).
% 2.43/0.98  
% 2.43/0.98  fof(f26,plain,(
% 2.43/0.98    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.43/0.98    inference(flattening,[],[f25])).
% 2.43/0.98  
% 2.43/0.98  fof(f41,plain,(
% 2.43/0.98    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.43/0.98    inference(nnf_transformation,[],[f26])).
% 2.43/0.98  
% 2.43/0.98  fof(f57,plain,(
% 2.43/0.98    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.43/0.98    inference(cnf_transformation,[],[f41])).
% 2.43/0.98  
% 2.43/0.98  fof(f83,plain,(
% 2.43/0.98    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.43/0.98    inference(equality_resolution,[],[f57])).
% 2.43/0.98  
% 2.43/0.98  fof(f16,axiom,(
% 2.43/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.43/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/0.98  
% 2.43/0.98  fof(f37,plain,(
% 2.43/0.98    ! [X0,X1,X2] : (! [X3] : (((k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | (~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.43/0.98    inference(ennf_transformation,[],[f16])).
% 2.43/0.98  
% 2.43/0.98  fof(f38,plain,(
% 2.43/0.98    ! [X0,X1,X2] : (! [X3] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.43/0.98    inference(flattening,[],[f37])).
% 2.43/0.98  
% 2.43/0.98  fof(f68,plain,(
% 2.43/0.98    ( ! [X2,X0,X3,X1] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.43/0.98    inference(cnf_transformation,[],[f38])).
% 2.43/0.98  
% 2.43/0.98  fof(f15,axiom,(
% 2.43/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 2.43/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/0.98  
% 2.43/0.98  fof(f35,plain,(
% 2.43/0.98    ! [X0,X1,X2] : (! [X3] : (((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.43/0.98    inference(ennf_transformation,[],[f15])).
% 2.43/0.98  
% 2.43/0.98  fof(f36,plain,(
% 2.43/0.98    ! [X0,X1,X2] : (! [X3] : ((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.43/0.98    inference(flattening,[],[f35])).
% 2.43/0.98  
% 2.43/0.98  fof(f66,plain,(
% 2.43/0.98    ( ! [X2,X0,X3,X1] : (v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.43/0.98    inference(cnf_transformation,[],[f36])).
% 2.43/0.98  
% 2.43/0.98  fof(f8,axiom,(
% 2.43/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.43/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/0.98  
% 2.43/0.98  fof(f24,plain,(
% 2.43/0.98    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.43/0.98    inference(ennf_transformation,[],[f8])).
% 2.43/0.98  
% 2.43/0.98  fof(f55,plain,(
% 2.43/0.98    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.43/0.98    inference(cnf_transformation,[],[f24])).
% 2.43/0.98  
% 2.43/0.98  fof(f3,axiom,(
% 2.43/0.98    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 2.43/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/0.98  
% 2.43/0.98  fof(f49,plain,(
% 2.43/0.98    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 2.43/0.98    inference(cnf_transformation,[],[f3])).
% 2.43/0.98  
% 2.43/0.98  fof(f13,axiom,(
% 2.43/0.98    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.43/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/0.98  
% 2.43/0.98  fof(f64,plain,(
% 2.43/0.98    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.43/0.98    inference(cnf_transformation,[],[f13])).
% 2.43/0.98  
% 2.43/0.98  fof(f79,plain,(
% 2.43/0.98    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 2.43/0.98    inference(definition_unfolding,[],[f49,f64])).
% 2.43/0.99  
% 2.43/0.99  fof(f4,axiom,(
% 2.43/0.99    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.43/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/0.99  
% 2.43/0.99  fof(f50,plain,(
% 2.43/0.99    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 2.43/0.99    inference(cnf_transformation,[],[f4])).
% 2.43/0.99  
% 2.43/0.99  fof(f81,plain,(
% 2.43/0.99    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 2.43/0.99    inference(definition_unfolding,[],[f50,f64])).
% 2.43/0.99  
% 2.43/0.99  fof(f5,axiom,(
% 2.43/0.99    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))),
% 2.43/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/0.99  
% 2.43/0.99  fof(f52,plain,(
% 2.43/0.99    ( ! [X0] : (k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))) )),
% 2.43/0.99    inference(cnf_transformation,[],[f5])).
% 2.43/0.99  
% 2.43/0.99  fof(f82,plain,(
% 2.43/0.99    ( ! [X0] : (k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0)) )),
% 2.43/0.99    inference(definition_unfolding,[],[f52,f64,f64])).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1,plain,
% 2.43/0.99      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.43/0.99      inference(cnf_transformation,[],[f48]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1276,plain,
% 2.43/0.99      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.43/0.99      inference(subtyping,[status(esa)],[c_1]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_24,negated_conjecture,
% 2.43/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 2.43/0.99      inference(cnf_transformation,[],[f76]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1263,negated_conjecture,
% 2.43/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 2.43/0.99      inference(subtyping,[status(esa)],[c_24]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1714,plain,
% 2.43/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 2.43/0.99      inference(predicate_to_equality,[status(thm)],[c_1263]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_8,plain,
% 2.43/0.99      ( v5_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.43/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_16,plain,
% 2.43/0.99      ( ~ v2_funct_2(X0,X1)
% 2.43/0.99      | ~ v5_relat_1(X0,X1)
% 2.43/0.99      | ~ v1_relat_1(X0)
% 2.43/0.99      | k2_relat_1(X0) = X1 ),
% 2.43/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_313,plain,
% 2.43/0.99      ( ~ v2_funct_2(X0,X1)
% 2.43/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.43/0.99      | ~ v1_relat_1(X0)
% 2.43/0.99      | k2_relat_1(X0) = X1 ),
% 2.43/0.99      inference(resolution,[status(thm)],[c_8,c_16]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_7,plain,
% 2.43/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 2.43/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_325,plain,
% 2.43/0.99      ( ~ v2_funct_2(X0,X1)
% 2.43/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.43/0.99      | k2_relat_1(X0) = X1 ),
% 2.43/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_313,c_7]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1256,plain,
% 2.43/0.99      ( ~ v2_funct_2(X0_50,X1_50)
% 2.43/0.99      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X2_50,X1_50)))
% 2.43/0.99      | k2_relat_1(X0_50) = X1_50 ),
% 2.43/0.99      inference(subtyping,[status(esa)],[c_325]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1721,plain,
% 2.43/0.99      ( k2_relat_1(X0_50) = X1_50
% 2.43/0.99      | v2_funct_2(X0_50,X1_50) != iProver_top
% 2.43/0.99      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X2_50,X1_50))) != iProver_top ),
% 2.43/0.99      inference(predicate_to_equality,[status(thm)],[c_1256]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_3326,plain,
% 2.43/0.99      ( k2_relat_1(sK2) = sK0 | v2_funct_2(sK2,sK0) != iProver_top ),
% 2.43/0.99      inference(superposition,[status(thm)],[c_1714,c_1721]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_27,negated_conjecture,
% 2.43/0.99      ( v1_funct_1(sK2) ),
% 2.43/0.99      inference(cnf_transformation,[],[f73]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_12,plain,
% 2.43/0.99      ( ~ v3_funct_2(X0,X1,X2)
% 2.43/0.99      | v2_funct_2(X0,X2)
% 2.43/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.43/0.99      | ~ v1_funct_1(X0) ),
% 2.43/0.99      inference(cnf_transformation,[],[f60]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_25,negated_conjecture,
% 2.43/0.99      ( v3_funct_2(sK2,sK0,sK0) ),
% 2.43/0.99      inference(cnf_transformation,[],[f75]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_356,plain,
% 2.43/0.99      ( v2_funct_2(X0,X1)
% 2.43/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.43/0.99      | ~ v1_funct_1(X0)
% 2.43/0.99      | sK2 != X0
% 2.43/0.99      | sK0 != X1
% 2.43/0.99      | sK0 != X2 ),
% 2.43/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_25]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_357,plain,
% 2.43/0.99      ( v2_funct_2(sK2,sK0)
% 2.43/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.43/0.99      | ~ v1_funct_1(sK2) ),
% 2.43/0.99      inference(unflattening,[status(thm)],[c_356]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1924,plain,
% 2.43/0.99      ( ~ v2_funct_2(sK2,sK0)
% 2.43/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_50,sK0)))
% 2.43/0.99      | k2_relat_1(sK2) = sK0 ),
% 2.43/0.99      inference(instantiation,[status(thm)],[c_1256]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1926,plain,
% 2.43/0.99      ( ~ v2_funct_2(sK2,sK0)
% 2.43/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.43/0.99      | k2_relat_1(sK2) = sK0 ),
% 2.43/0.99      inference(instantiation,[status(thm)],[c_1924]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_3944,plain,
% 2.43/0.99      ( k2_relat_1(sK2) = sK0 ),
% 2.43/0.99      inference(global_propositional_subsumption,
% 2.43/0.99                [status(thm)],
% 2.43/0.99                [c_3326,c_27,c_24,c_357,c_1926]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_0,plain,
% 2.43/0.99      ( ~ v1_relat_1(X0)
% 2.43/0.99      | ~ v1_relat_1(X1)
% 2.43/0.99      | X0 = X1
% 2.43/0.99      | k2_relat_1(X0) != k1_xboole_0
% 2.43/0.99      | k2_relat_1(X1) != k1_xboole_0 ),
% 2.43/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1277,plain,
% 2.43/0.99      ( ~ v1_relat_1(X0_50)
% 2.43/0.99      | ~ v1_relat_1(X1_50)
% 2.43/0.99      | X0_50 = X1_50
% 2.43/0.99      | k2_relat_1(X0_50) != k1_xboole_0
% 2.43/0.99      | k2_relat_1(X1_50) != k1_xboole_0 ),
% 2.43/0.99      inference(subtyping,[status(esa)],[c_0]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1704,plain,
% 2.43/0.99      ( X0_50 = X1_50
% 2.43/0.99      | k2_relat_1(X0_50) != k1_xboole_0
% 2.43/0.99      | k2_relat_1(X1_50) != k1_xboole_0
% 2.43/0.99      | v1_relat_1(X0_50) != iProver_top
% 2.43/0.99      | v1_relat_1(X1_50) != iProver_top ),
% 2.43/0.99      inference(predicate_to_equality,[status(thm)],[c_1277]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_3950,plain,
% 2.43/0.99      ( k2_relat_1(X0_50) != k1_xboole_0
% 2.43/0.99      | sK2 = X0_50
% 2.43/0.99      | sK0 != k1_xboole_0
% 2.43/0.99      | v1_relat_1(X0_50) != iProver_top
% 2.43/0.99      | v1_relat_1(sK2) != iProver_top ),
% 2.43/0.99      inference(superposition,[status(thm)],[c_3944,c_1704]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_31,negated_conjecture,
% 2.43/0.99      ( v1_funct_1(sK1) ),
% 2.43/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_30,negated_conjecture,
% 2.43/0.99      ( v1_funct_2(sK1,sK0,sK0) ),
% 2.43/0.99      inference(cnf_transformation,[],[f70]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_28,negated_conjecture,
% 2.43/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 2.43/0.99      inference(cnf_transformation,[],[f72]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_26,negated_conjecture,
% 2.43/0.99      ( v1_funct_2(sK2,sK0,sK0) ),
% 2.43/0.99      inference(cnf_transformation,[],[f74]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_39,plain,
% 2.43/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 2.43/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_23,negated_conjecture,
% 2.43/0.99      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
% 2.43/0.99      inference(cnf_transformation,[],[f77]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1279,plain,( X0_50 = X0_50 ),theory(equality) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1312,plain,
% 2.43/0.99      ( sK0 = sK0 ),
% 2.43/0.99      inference(instantiation,[status(thm)],[c_1279]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_22,negated_conjecture,
% 2.43/0.99      ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
% 2.43/0.99      inference(cnf_transformation,[],[f78]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1265,negated_conjecture,
% 2.43/0.99      ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
% 2.43/0.99      inference(subtyping,[status(esa)],[c_22]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1712,plain,
% 2.43/0.99      ( r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) != iProver_top ),
% 2.43/0.99      inference(predicate_to_equality,[status(thm)],[c_1265]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_17,plain,
% 2.43/0.99      ( ~ v1_funct_2(X0,X1,X1)
% 2.43/0.99      | ~ v3_funct_2(X0,X1,X1)
% 2.43/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 2.43/0.99      | ~ v1_funct_1(X0)
% 2.43/0.99      | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
% 2.43/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_29,negated_conjecture,
% 2.43/0.99      ( v3_funct_2(sK1,sK0,sK0) ),
% 2.43/0.99      inference(cnf_transformation,[],[f71]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_386,plain,
% 2.43/0.99      ( ~ v1_funct_2(X0,X1,X1)
% 2.43/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 2.43/0.99      | ~ v1_funct_1(X0)
% 2.43/0.99      | k2_funct_2(X1,X0) = k2_funct_1(X0)
% 2.43/0.99      | sK1 != X0
% 2.43/0.99      | sK0 != X1 ),
% 2.43/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_29]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_387,plain,
% 2.43/0.99      ( ~ v1_funct_2(sK1,sK0,sK0)
% 2.43/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.43/0.99      | ~ v1_funct_1(sK1)
% 2.43/0.99      | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 2.43/0.99      inference(unflattening,[status(thm)],[c_386]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_389,plain,
% 2.43/0.99      ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 2.43/0.99      inference(global_propositional_subsumption,
% 2.43/0.99                [status(thm)],
% 2.43/0.99                [c_387,c_31,c_30,c_28]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1251,plain,
% 2.43/0.99      ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 2.43/0.99      inference(subtyping,[status(esa)],[c_389]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1755,plain,
% 2.43/0.99      ( r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1)) != iProver_top ),
% 2.43/0.99      inference(light_normalisation,[status(thm)],[c_1712,c_1251]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1870,plain,
% 2.43/0.99      ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1)) ),
% 2.43/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_1755]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1271,plain,
% 2.43/0.99      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
% 2.43/0.99      | v1_relat_1(X0_50) ),
% 2.43/0.99      inference(subtyping,[status(esa)],[c_7]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1906,plain,
% 2.43/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.43/0.99      | v1_relat_1(sK2) ),
% 2.43/0.99      inference(instantiation,[status(thm)],[c_1271]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1907,plain,
% 2.43/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 2.43/0.99      | v1_relat_1(sK2) = iProver_top ),
% 2.43/0.99      inference(predicate_to_equality,[status(thm)],[c_1906]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_10,plain,
% 2.43/0.99      ( r2_relset_1(X0,X1,X2,X2)
% 2.43/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 2.43/0.99      inference(cnf_transformation,[],[f83]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1269,plain,
% 2.43/0.99      ( r2_relset_1(X0_50,X1_50,X2_50,X2_50)
% 2.43/0.99      | ~ m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) ),
% 2.43/0.99      inference(subtyping,[status(esa)],[c_10]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1934,plain,
% 2.43/0.99      ( r2_relset_1(sK0,sK0,sK2,sK2)
% 2.43/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 2.43/0.99      inference(instantiation,[status(thm)],[c_1269]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_2098,plain,
% 2.43/0.99      ( sK2 = sK2 ),
% 2.43/0.99      inference(instantiation,[status(thm)],[c_1279]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_21,plain,
% 2.43/0.99      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 2.43/0.99      | ~ v1_funct_2(X3,X1,X0)
% 2.43/0.99      | ~ v1_funct_2(X2,X0,X1)
% 2.43/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.43/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.43/0.99      | ~ v1_funct_1(X2)
% 2.43/0.99      | ~ v1_funct_1(X3)
% 2.43/0.99      | ~ v2_funct_1(X2)
% 2.43/0.99      | k2_relset_1(X0,X1,X2) != X1
% 2.43/0.99      | k2_funct_1(X2) = X3
% 2.43/0.99      | k1_xboole_0 = X1
% 2.43/0.99      | k1_xboole_0 = X0 ),
% 2.43/0.99      inference(cnf_transformation,[],[f68]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_20,plain,
% 2.43/0.99      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 2.43/0.99      | ~ v1_funct_2(X3,X1,X0)
% 2.43/0.99      | ~ v1_funct_2(X2,X0,X1)
% 2.43/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.43/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.43/0.99      | ~ v1_funct_1(X2)
% 2.43/0.99      | ~ v1_funct_1(X3)
% 2.43/0.99      | v2_funct_1(X2) ),
% 2.43/0.99      inference(cnf_transformation,[],[f66]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_162,plain,
% 2.43/0.99      ( ~ v1_funct_1(X3)
% 2.43/0.99      | ~ v1_funct_1(X2)
% 2.43/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.43/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.43/0.99      | ~ v1_funct_2(X2,X0,X1)
% 2.43/0.99      | ~ v1_funct_2(X3,X1,X0)
% 2.43/0.99      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 2.43/0.99      | k2_relset_1(X0,X1,X2) != X1
% 2.43/0.99      | k2_funct_1(X2) = X3
% 2.43/0.99      | k1_xboole_0 = X1
% 2.43/0.99      | k1_xboole_0 = X0 ),
% 2.43/0.99      inference(global_propositional_subsumption,[status(thm)],[c_21,c_20]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_163,plain,
% 2.43/0.99      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 2.43/0.99      | ~ v1_funct_2(X3,X1,X0)
% 2.43/0.99      | ~ v1_funct_2(X2,X0,X1)
% 2.43/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.43/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.43/0.99      | ~ v1_funct_1(X2)
% 2.43/0.99      | ~ v1_funct_1(X3)
% 2.43/0.99      | k2_relset_1(X0,X1,X2) != X1
% 2.43/0.99      | k2_funct_1(X2) = X3
% 2.43/0.99      | k1_xboole_0 = X1
% 2.43/0.99      | k1_xboole_0 = X0 ),
% 2.43/0.99      inference(renaming,[status(thm)],[c_162]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1257,plain,
% 2.43/0.99      ( ~ r2_relset_1(X0_50,X0_50,k1_partfun1(X0_50,X1_50,X1_50,X0_50,X2_50,X3_50),k6_partfun1(X0_50))
% 2.43/0.99      | ~ v1_funct_2(X3_50,X1_50,X0_50)
% 2.43/0.99      | ~ v1_funct_2(X2_50,X0_50,X1_50)
% 2.43/0.99      | ~ m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
% 2.43/0.99      | ~ m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X0_50)))
% 2.43/0.99      | ~ v1_funct_1(X2_50)
% 2.43/0.99      | ~ v1_funct_1(X3_50)
% 2.43/0.99      | k2_relset_1(X0_50,X1_50,X2_50) != X1_50
% 2.43/0.99      | k2_funct_1(X2_50) = X3_50
% 2.43/0.99      | k1_xboole_0 = X1_50
% 2.43/0.99      | k1_xboole_0 = X0_50 ),
% 2.43/0.99      inference(subtyping,[status(esa)],[c_163]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_2000,plain,
% 2.43/0.99      ( ~ r2_relset_1(X0_50,X0_50,k1_partfun1(X0_50,X1_50,X1_50,X0_50,sK1,X2_50),k6_partfun1(X0_50))
% 2.43/0.99      | ~ v1_funct_2(X2_50,X1_50,X0_50)
% 2.43/0.99      | ~ v1_funct_2(sK1,X0_50,X1_50)
% 2.43/0.99      | ~ m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X0_50)))
% 2.43/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
% 2.43/0.99      | ~ v1_funct_1(X2_50)
% 2.43/0.99      | ~ v1_funct_1(sK1)
% 2.43/0.99      | k2_relset_1(X0_50,X1_50,sK1) != X1_50
% 2.43/0.99      | k2_funct_1(sK1) = X2_50
% 2.43/0.99      | k1_xboole_0 = X1_50
% 2.43/0.99      | k1_xboole_0 = X0_50 ),
% 2.43/0.99      inference(instantiation,[status(thm)],[c_1257]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_2203,plain,
% 2.43/0.99      ( ~ r2_relset_1(X0_50,X0_50,k1_partfun1(X0_50,X1_50,X1_50,X0_50,sK1,sK2),k6_partfun1(X0_50))
% 2.43/0.99      | ~ v1_funct_2(sK1,X0_50,X1_50)
% 2.43/0.99      | ~ v1_funct_2(sK2,X1_50,X0_50)
% 2.43/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
% 2.43/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1_50,X0_50)))
% 2.43/0.99      | ~ v1_funct_1(sK1)
% 2.43/0.99      | ~ v1_funct_1(sK2)
% 2.43/0.99      | k2_relset_1(X0_50,X1_50,sK1) != X1_50
% 2.43/0.99      | k2_funct_1(sK1) = sK2
% 2.43/0.99      | k1_xboole_0 = X1_50
% 2.43/0.99      | k1_xboole_0 = X0_50 ),
% 2.43/0.99      inference(instantiation,[status(thm)],[c_2000]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_2205,plain,
% 2.43/0.99      ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))
% 2.43/0.99      | ~ v1_funct_2(sK1,sK0,sK0)
% 2.43/0.99      | ~ v1_funct_2(sK2,sK0,sK0)
% 2.43/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.43/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.43/0.99      | ~ v1_funct_1(sK1)
% 2.43/0.99      | ~ v1_funct_1(sK2)
% 2.43/0.99      | k2_relset_1(sK0,sK0,sK1) != sK0
% 2.43/0.99      | k2_funct_1(sK1) = sK2
% 2.43/0.99      | k1_xboole_0 = sK0 ),
% 2.43/0.99      inference(instantiation,[status(thm)],[c_2203]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1282,plain,
% 2.43/0.99      ( X0_50 != X1_50 | X2_50 != X1_50 | X2_50 = X0_50 ),
% 2.43/0.99      theory(equality) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_2261,plain,
% 2.43/0.99      ( k2_relat_1(sK2) != X0_50
% 2.43/0.99      | k2_relat_1(sK2) = k1_xboole_0
% 2.43/0.99      | k1_xboole_0 != X0_50 ),
% 2.43/0.99      inference(instantiation,[status(thm)],[c_1282]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_2262,plain,
% 2.43/0.99      ( k2_relat_1(sK2) != sK0
% 2.43/0.99      | k2_relat_1(sK2) = k1_xboole_0
% 2.43/0.99      | k1_xboole_0 != sK0 ),
% 2.43/0.99      inference(instantiation,[status(thm)],[c_2261]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_2290,plain,
% 2.43/0.99      ( ~ v1_relat_1(X0_50)
% 2.43/0.99      | ~ v1_relat_1(sK2)
% 2.43/0.99      | k2_relat_1(X0_50) != k1_xboole_0
% 2.43/0.99      | k2_relat_1(sK2) != k1_xboole_0
% 2.43/0.99      | sK2 = X0_50 ),
% 2.43/0.99      inference(instantiation,[status(thm)],[c_1277]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_2291,plain,
% 2.43/0.99      ( k2_relat_1(X0_50) != k1_xboole_0
% 2.43/0.99      | k2_relat_1(sK2) != k1_xboole_0
% 2.43/0.99      | sK2 = X0_50
% 2.43/0.99      | v1_relat_1(X0_50) != iProver_top
% 2.43/0.99      | v1_relat_1(sK2) != iProver_top ),
% 2.43/0.99      inference(predicate_to_equality,[status(thm)],[c_2290]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1260,negated_conjecture,
% 2.43/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 2.43/0.99      inference(subtyping,[status(esa)],[c_28]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1717,plain,
% 2.43/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 2.43/0.99      inference(predicate_to_equality,[status(thm)],[c_1260]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_3327,plain,
% 2.43/0.99      ( k2_relat_1(sK1) = sK0 | v2_funct_2(sK1,sK0) != iProver_top ),
% 2.43/0.99      inference(superposition,[status(thm)],[c_1717,c_1721]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_367,plain,
% 2.43/0.99      ( v2_funct_2(X0,X1)
% 2.43/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.43/0.99      | ~ v1_funct_1(X0)
% 2.43/0.99      | sK1 != X0
% 2.43/0.99      | sK0 != X1
% 2.43/0.99      | sK0 != X2 ),
% 2.43/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_29]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_368,plain,
% 2.43/0.99      ( v2_funct_2(sK1,sK0)
% 2.43/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.43/0.99      | ~ v1_funct_1(sK1) ),
% 2.43/0.99      inference(unflattening,[status(thm)],[c_367]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1929,plain,
% 2.43/0.99      ( ~ v2_funct_2(sK1,sK0)
% 2.43/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0_50,sK0)))
% 2.43/0.99      | k2_relat_1(sK1) = sK0 ),
% 2.43/0.99      inference(instantiation,[status(thm)],[c_1256]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1931,plain,
% 2.43/0.99      ( ~ v2_funct_2(sK1,sK0)
% 2.43/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.43/0.99      | k2_relat_1(sK1) = sK0 ),
% 2.43/0.99      inference(instantiation,[status(thm)],[c_1929]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_3975,plain,
% 2.43/0.99      ( k2_relat_1(sK1) = sK0 ),
% 2.43/0.99      inference(global_propositional_subsumption,
% 2.43/0.99                [status(thm)],
% 2.43/0.99                [c_3327,c_31,c_28,c_368,c_1931]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_9,plain,
% 2.43/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.43/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.43/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1270,plain,
% 2.43/0.99      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
% 2.43/0.99      | k2_relset_1(X1_50,X2_50,X0_50) = k2_relat_1(X0_50) ),
% 2.43/0.99      inference(subtyping,[status(esa)],[c_9]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1707,plain,
% 2.43/0.99      ( k2_relset_1(X0_50,X1_50,X2_50) = k2_relat_1(X2_50)
% 2.43/0.99      | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top ),
% 2.43/0.99      inference(predicate_to_equality,[status(thm)],[c_1270]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_2653,plain,
% 2.43/0.99      ( k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1) ),
% 2.43/0.99      inference(superposition,[status(thm)],[c_1717,c_1707]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_3978,plain,
% 2.43/0.99      ( k2_relset_1(sK0,sK0,sK1) = sK0 ),
% 2.43/0.99      inference(demodulation,[status(thm)],[c_3975,c_2653]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1291,plain,
% 2.43/0.99      ( ~ r2_relset_1(X0_50,X1_50,X2_50,X3_50)
% 2.43/0.99      | r2_relset_1(X4_50,X5_50,X6_50,X7_50)
% 2.43/0.99      | X4_50 != X0_50
% 2.43/0.99      | X5_50 != X1_50
% 2.43/0.99      | X6_50 != X2_50
% 2.43/0.99      | X7_50 != X3_50 ),
% 2.43/0.99      theory(equality) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_2034,plain,
% 2.43/0.99      ( r2_relset_1(X0_50,X1_50,X2_50,X3_50)
% 2.43/0.99      | ~ r2_relset_1(sK0,sK0,sK2,sK2)
% 2.43/0.99      | X2_50 != sK2
% 2.43/0.99      | X3_50 != sK2
% 2.43/0.99      | X1_50 != sK0
% 2.43/0.99      | X0_50 != sK0 ),
% 2.43/0.99      inference(instantiation,[status(thm)],[c_1291]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_2356,plain,
% 2.43/0.99      ( r2_relset_1(X0_50,X1_50,sK2,X2_50)
% 2.43/0.99      | ~ r2_relset_1(sK0,sK0,sK2,sK2)
% 2.43/0.99      | X2_50 != sK2
% 2.43/0.99      | X1_50 != sK0
% 2.43/0.99      | X0_50 != sK0
% 2.43/0.99      | sK2 != sK2 ),
% 2.43/0.99      inference(instantiation,[status(thm)],[c_2034]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_4159,plain,
% 2.43/0.99      ( r2_relset_1(X0_50,X1_50,sK2,k2_funct_1(sK1))
% 2.43/0.99      | ~ r2_relset_1(sK0,sK0,sK2,sK2)
% 2.43/0.99      | X1_50 != sK0
% 2.43/0.99      | X0_50 != sK0
% 2.43/0.99      | k2_funct_1(sK1) != sK2
% 2.43/0.99      | sK2 != sK2 ),
% 2.43/0.99      inference(instantiation,[status(thm)],[c_2356]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_4166,plain,
% 2.43/0.99      ( r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1))
% 2.43/0.99      | ~ r2_relset_1(sK0,sK0,sK2,sK2)
% 2.43/0.99      | k2_funct_1(sK1) != sK2
% 2.43/0.99      | sK2 != sK2
% 2.43/0.99      | sK0 != sK0 ),
% 2.43/0.99      inference(instantiation,[status(thm)],[c_4159]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_4425,plain,
% 2.43/0.99      ( v1_relat_1(X0_50) != iProver_top
% 2.43/0.99      | k2_relat_1(X0_50) != k1_xboole_0
% 2.43/0.99      | sK2 = X0_50 ),
% 2.43/0.99      inference(global_propositional_subsumption,
% 2.43/0.99                [status(thm)],
% 2.43/0.99                [c_3950,c_31,c_30,c_28,c_27,c_26,c_24,c_39,c_23,c_357,c_1312,
% 2.43/0.99                 c_1870,c_1907,c_1926,c_1934,c_2098,c_2205,c_2262,c_2291,
% 2.43/0.99                 c_3978,c_4166]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_4426,plain,
% 2.43/0.99      ( k2_relat_1(X0_50) != k1_xboole_0
% 2.43/0.99      | sK2 = X0_50
% 2.43/0.99      | v1_relat_1(X0_50) != iProver_top ),
% 2.43/0.99      inference(renaming,[status(thm)],[c_4425]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_4434,plain,
% 2.43/0.99      ( sK2 = k1_xboole_0 | v1_relat_1(k1_xboole_0) != iProver_top ),
% 2.43/0.99      inference(superposition,[status(thm)],[c_1276,c_4426]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_3531,plain,
% 2.43/0.99      ( X0_50 != X1_50 | X0_50 = k1_xboole_0 | k1_xboole_0 != X1_50 ),
% 2.43/0.99      inference(instantiation,[status(thm)],[c_1282]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_3532,plain,
% 2.43/0.99      ( sK0 != sK0 | sK0 = k1_xboole_0 | k1_xboole_0 != sK0 ),
% 2.43/0.99      inference(instantiation,[status(thm)],[c_3531]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_2701,plain,
% 2.43/0.99      ( k2_relat_1(X0_50) != k1_xboole_0
% 2.43/0.99      | k1_xboole_0 = X0_50
% 2.43/0.99      | v1_relat_1(X0_50) != iProver_top
% 2.43/0.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 2.43/0.99      inference(superposition,[status(thm)],[c_1276,c_1704]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_3,plain,
% 2.43/0.99      ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 2.43/0.99      inference(cnf_transformation,[],[f79]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1274,plain,
% 2.43/0.99      ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 2.43/0.99      inference(subtyping,[status(esa)],[c_3]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_5,plain,
% 2.43/0.99      ( v1_relat_1(k6_partfun1(X0)) ),
% 2.43/0.99      inference(cnf_transformation,[],[f81]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1273,plain,
% 2.43/0.99      ( v1_relat_1(k6_partfun1(X0_50)) ),
% 2.43/0.99      inference(subtyping,[status(esa)],[c_5]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1705,plain,
% 2.43/0.99      ( v1_relat_1(k6_partfun1(X0_50)) = iProver_top ),
% 2.43/0.99      inference(predicate_to_equality,[status(thm)],[c_1273]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_2384,plain,
% 2.43/0.99      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 2.43/0.99      inference(superposition,[status(thm)],[c_1274,c_1705]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_2780,plain,
% 2.43/0.99      ( v1_relat_1(X0_50) != iProver_top
% 2.43/0.99      | k1_xboole_0 = X0_50
% 2.43/0.99      | k2_relat_1(X0_50) != k1_xboole_0 ),
% 2.43/0.99      inference(global_propositional_subsumption,[status(thm)],[c_2701,c_2384]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_2781,plain,
% 2.43/0.99      ( k2_relat_1(X0_50) != k1_xboole_0
% 2.43/0.99      | k1_xboole_0 = X0_50
% 2.43/0.99      | v1_relat_1(X0_50) != iProver_top ),
% 2.43/0.99      inference(renaming,[status(thm)],[c_2780]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_3949,plain,
% 2.43/0.99      ( sK2 = k1_xboole_0
% 2.43/0.99      | sK0 != k1_xboole_0
% 2.43/0.99      | v1_relat_1(sK2) != iProver_top ),
% 2.43/0.99      inference(superposition,[status(thm)],[c_3944,c_2781]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_4501,plain,
% 2.43/0.99      ( sK2 = k1_xboole_0 ),
% 2.43/0.99      inference(global_propositional_subsumption,
% 2.43/0.99                [status(thm)],
% 2.43/0.99                [c_4434,c_31,c_30,c_28,c_27,c_26,c_24,c_39,c_23,c_1312,
% 2.43/0.99                 c_1870,c_1907,c_1934,c_2098,c_2205,c_3532,c_3949,c_3978,
% 2.43/0.99                 c_4166]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_4509,plain,
% 2.43/0.99      ( k2_relat_1(k1_xboole_0) = sK0 ),
% 2.43/0.99      inference(demodulation,[status(thm)],[c_4501,c_3944]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_4537,plain,
% 2.43/0.99      ( sK0 = k1_xboole_0 ),
% 2.43/0.99      inference(light_normalisation,[status(thm)],[c_4509,c_1276]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_4512,plain,
% 2.43/0.99      ( r2_relset_1(sK0,sK0,k1_xboole_0,k2_funct_1(sK1)) != iProver_top ),
% 2.43/0.99      inference(demodulation,[status(thm)],[c_4501,c_1755]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_4539,plain,
% 2.43/0.99      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK1)) != iProver_top ),
% 2.43/0.99      inference(demodulation,[status(thm)],[c_4537,c_4512]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_6,plain,
% 2.43/0.99      ( k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0) ),
% 2.43/0.99      inference(cnf_transformation,[],[f82]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1272,plain,
% 2.43/0.99      ( k2_funct_1(k6_partfun1(X0_50)) = k6_partfun1(X0_50) ),
% 2.43/0.99      inference(subtyping,[status(esa)],[c_6]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_2046,plain,
% 2.43/0.99      ( k2_funct_1(k1_xboole_0) = k6_partfun1(k1_xboole_0) ),
% 2.43/0.99      inference(superposition,[status(thm)],[c_1274,c_1272]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_2047,plain,
% 2.43/0.99      ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
% 2.43/0.99      inference(light_normalisation,[status(thm)],[c_2046,c_1274]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_3980,plain,
% 2.43/0.99      ( sK1 = k1_xboole_0
% 2.43/0.99      | sK0 != k1_xboole_0
% 2.43/0.99      | v1_relat_1(sK1) != iProver_top ),
% 2.43/0.99      inference(superposition,[status(thm)],[c_3975,c_2781]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_35,plain,
% 2.43/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 2.43/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1909,plain,
% 2.43/0.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.43/0.99      | v1_relat_1(sK1) ),
% 2.43/0.99      inference(instantiation,[status(thm)],[c_1271]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1910,plain,
% 2.43/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 2.43/0.99      | v1_relat_1(sK1) = iProver_top ),
% 2.43/0.99      inference(predicate_to_equality,[status(thm)],[c_1909]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_5257,plain,
% 2.43/0.99      ( sK1 = k1_xboole_0 ),
% 2.43/0.99      inference(global_propositional_subsumption,
% 2.43/0.99                [status(thm)],
% 2.43/0.99                [c_3980,c_31,c_30,c_28,c_35,c_27,c_26,c_24,c_23,c_1312,
% 2.43/0.99                 c_1870,c_1910,c_1934,c_2098,c_2205,c_3532,c_3978,c_4166]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_5322,plain,
% 2.43/0.99      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 2.43/0.99      inference(light_normalisation,[status(thm)],[c_4539,c_2047,c_5257]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1708,plain,
% 2.43/0.99      ( r2_relset_1(X0_50,X1_50,X2_50,X2_50) = iProver_top
% 2.43/0.99      | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top ),
% 2.43/0.99      inference(predicate_to_equality,[status(thm)],[c_1269]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_2687,plain,
% 2.43/0.99      ( r2_relset_1(sK0,sK0,sK2,sK2) = iProver_top ),
% 2.43/0.99      inference(superposition,[status(thm)],[c_1714,c_1708]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_4510,plain,
% 2.43/0.99      ( r2_relset_1(sK0,sK0,k1_xboole_0,k1_xboole_0) = iProver_top ),
% 2.43/0.99      inference(demodulation,[status(thm)],[c_4501,c_2687]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_4538,plain,
% 2.43/0.99      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top ),
% 2.43/0.99      inference(demodulation,[status(thm)],[c_4537,c_4510]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_5324,plain,
% 2.43/0.99      ( $false ),
% 2.43/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_5322,c_4538]) ).
% 2.43/0.99  
% 2.43/0.99  
% 2.43/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.43/0.99  
% 2.43/0.99  ------                               Statistics
% 2.43/0.99  
% 2.43/0.99  ------ General
% 2.43/0.99  
% 2.43/0.99  abstr_ref_over_cycles:                  0
% 2.43/0.99  abstr_ref_under_cycles:                 0
% 2.43/0.99  gc_basic_clause_elim:                   0
% 2.43/0.99  forced_gc_time:                         0
% 2.43/0.99  parsing_time:                           0.007
% 2.43/0.99  unif_index_cands_time:                  0.
% 2.43/0.99  unif_index_add_time:                    0.
% 2.43/0.99  orderings_time:                         0.
% 2.43/0.99  out_proof_time:                         0.011
% 2.43/0.99  total_time:                             0.165
% 2.43/0.99  num_of_symbols:                         56
% 2.43/0.99  num_of_terms:                           5379
% 2.43/0.99  
% 2.43/0.99  ------ Preprocessing
% 2.43/0.99  
% 2.43/0.99  num_of_splits:                          0
% 2.43/0.99  num_of_split_atoms:                     0
% 2.43/0.99  num_of_reused_defs:                     0
% 2.43/0.99  num_eq_ax_congr_red:                    11
% 2.43/0.99  num_of_sem_filtered_clauses:            4
% 2.43/0.99  num_of_subtypes:                        3
% 2.43/0.99  monotx_restored_types:                  1
% 2.43/0.99  sat_num_of_epr_types:                   0
% 2.43/0.99  sat_num_of_non_cyclic_types:            0
% 2.43/0.99  sat_guarded_non_collapsed_types:        1
% 2.43/0.99  num_pure_diseq_elim:                    0
% 2.43/0.99  simp_replaced_by:                       0
% 2.43/0.99  res_preprocessed:                       149
% 2.43/0.99  prep_upred:                             0
% 2.43/0.99  prep_unflattend:                        74
% 2.43/0.99  smt_new_axioms:                         0
% 2.43/0.99  pred_elim_cands:                        6
% 2.43/0.99  pred_elim:                              2
% 2.43/0.99  pred_elim_cl:                           1
% 2.43/0.99  pred_elim_cycles:                       6
% 2.43/0.99  merged_defs:                            0
% 2.43/0.99  merged_defs_ncl:                        0
% 2.43/0.99  bin_hyper_res:                          0
% 2.43/0.99  prep_cycles:                            4
% 2.43/0.99  pred_elim_time:                         0.014
% 2.43/0.99  splitting_time:                         0.
% 2.43/0.99  sem_filter_time:                        0.
% 2.43/0.99  monotx_time:                            0.
% 2.43/0.99  subtype_inf_time:                       0.001
% 2.43/0.99  
% 2.43/0.99  ------ Problem properties
% 2.43/0.99  
% 2.43/0.99  clauses:                                27
% 2.43/0.99  conjectures:                            8
% 2.43/0.99  epr:                                    6
% 2.43/0.99  horn:                                   26
% 2.43/0.99  ground:                                 15
% 2.43/0.99  unary:                                  17
% 2.43/0.99  binary:                                 4
% 2.43/0.99  lits:                                   64
% 2.43/0.99  lits_eq:                                17
% 2.43/0.99  fd_pure:                                0
% 2.43/0.99  fd_pseudo:                              0
% 2.43/0.99  fd_cond:                                0
% 2.43/0.99  fd_pseudo_cond:                         4
% 2.43/0.99  ac_symbols:                             0
% 2.43/0.99  
% 2.43/0.99  ------ Propositional Solver
% 2.43/0.99  
% 2.43/0.99  prop_solver_calls:                      27
% 2.43/0.99  prop_fast_solver_calls:                 1154
% 2.43/0.99  smt_solver_calls:                       0
% 2.43/0.99  smt_fast_solver_calls:                  0
% 2.43/0.99  prop_num_of_clauses:                    1722
% 2.43/0.99  prop_preprocess_simplified:             5421
% 2.43/0.99  prop_fo_subsumed:                       35
% 2.43/0.99  prop_solver_time:                       0.
% 2.43/0.99  smt_solver_time:                        0.
% 2.43/0.99  smt_fast_solver_time:                   0.
% 2.43/0.99  prop_fast_solver_time:                  0.
% 2.43/0.99  prop_unsat_core_time:                   0.
% 2.43/0.99  
% 2.43/0.99  ------ QBF
% 2.43/0.99  
% 2.43/0.99  qbf_q_res:                              0
% 2.43/0.99  qbf_num_tautologies:                    0
% 2.43/0.99  qbf_prep_cycles:                        0
% 2.43/0.99  
% 2.43/0.99  ------ BMC1
% 2.43/0.99  
% 2.43/0.99  bmc1_current_bound:                     -1
% 2.43/0.99  bmc1_last_solved_bound:                 -1
% 2.43/0.99  bmc1_unsat_core_size:                   -1
% 2.43/0.99  bmc1_unsat_core_parents_size:           -1
% 2.43/0.99  bmc1_merge_next_fun:                    0
% 2.43/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.43/0.99  
% 2.43/0.99  ------ Instantiation
% 2.43/0.99  
% 2.43/0.99  inst_num_of_clauses:                    475
% 2.43/0.99  inst_num_in_passive:                    63
% 2.43/0.99  inst_num_in_active:                     325
% 2.43/0.99  inst_num_in_unprocessed:                87
% 2.43/0.99  inst_num_of_loops:                      340
% 2.43/0.99  inst_num_of_learning_restarts:          0
% 2.43/0.99  inst_num_moves_active_passive:          12
% 2.43/0.99  inst_lit_activity:                      0
% 2.43/0.99  inst_lit_activity_moves:                0
% 2.43/0.99  inst_num_tautologies:                   0
% 2.43/0.99  inst_num_prop_implied:                  0
% 2.43/0.99  inst_num_existing_simplified:           0
% 2.43/0.99  inst_num_eq_res_simplified:             0
% 2.43/0.99  inst_num_child_elim:                    0
% 2.43/0.99  inst_num_of_dismatching_blockings:      253
% 2.43/0.99  inst_num_of_non_proper_insts:           727
% 2.43/0.99  inst_num_of_duplicates:                 0
% 2.43/0.99  inst_inst_num_from_inst_to_res:         0
% 2.43/0.99  inst_dismatching_checking_time:         0.
% 2.43/0.99  
% 2.43/0.99  ------ Resolution
% 2.43/0.99  
% 2.43/0.99  res_num_of_clauses:                     0
% 2.43/0.99  res_num_in_passive:                     0
% 2.43/0.99  res_num_in_active:                      0
% 2.43/0.99  res_num_of_loops:                       153
% 2.43/0.99  res_forward_subset_subsumed:            24
% 2.43/0.99  res_backward_subset_subsumed:           0
% 2.43/0.99  res_forward_subsumed:                   0
% 2.43/0.99  res_backward_subsumed:                  0
% 2.43/0.99  res_forward_subsumption_resolution:     2
% 2.43/0.99  res_backward_subsumption_resolution:    0
% 2.43/0.99  res_clause_to_clause_subsumption:       162
% 2.43/0.99  res_orphan_elimination:                 0
% 2.43/0.99  res_tautology_del:                      32
% 2.43/0.99  res_num_eq_res_simplified:              0
% 2.43/0.99  res_num_sel_changes:                    0
% 2.43/0.99  res_moves_from_active_to_pass:          0
% 2.43/0.99  
% 2.43/0.99  ------ Superposition
% 2.43/0.99  
% 2.43/0.99  sup_time_total:                         0.
% 2.43/0.99  sup_time_generating:                    0.
% 2.43/0.99  sup_time_sim_full:                      0.
% 2.43/0.99  sup_time_sim_immed:                     0.
% 2.43/0.99  
% 2.43/0.99  sup_num_of_clauses:                     38
% 2.43/0.99  sup_num_in_active:                      30
% 2.43/0.99  sup_num_in_passive:                     8
% 2.43/0.99  sup_num_of_loops:                       66
% 2.43/0.99  sup_fw_superposition:                   27
% 2.43/0.99  sup_bw_superposition:                   24
% 2.43/0.99  sup_immediate_simplified:               30
% 2.43/0.99  sup_given_eliminated:                   0
% 2.43/0.99  comparisons_done:                       0
% 2.43/0.99  comparisons_avoided:                    0
% 2.43/0.99  
% 2.43/0.99  ------ Simplifications
% 2.43/0.99  
% 2.43/0.99  
% 2.43/0.99  sim_fw_subset_subsumed:                 6
% 2.43/0.99  sim_bw_subset_subsumed:                 6
% 2.43/0.99  sim_fw_subsumed:                        2
% 2.43/0.99  sim_bw_subsumed:                        0
% 2.43/0.99  sim_fw_subsumption_res:                 1
% 2.43/0.99  sim_bw_subsumption_res:                 0
% 2.43/0.99  sim_tautology_del:                      0
% 2.43/0.99  sim_eq_tautology_del:                   10
% 2.43/0.99  sim_eq_res_simp:                        0
% 2.43/0.99  sim_fw_demodulated:                     3
% 2.43/0.99  sim_bw_demodulated:                     42
% 2.43/0.99  sim_light_normalised:                   21
% 2.43/0.99  sim_joinable_taut:                      0
% 2.43/0.99  sim_joinable_simp:                      0
% 2.43/0.99  sim_ac_normalised:                      0
% 2.43/0.99  sim_smt_subsumption:                    0
% 2.43/0.99  
%------------------------------------------------------------------------------
