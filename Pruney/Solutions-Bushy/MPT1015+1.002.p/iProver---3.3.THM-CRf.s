%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1015+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:40 EST 2020

% Result     : Theorem 19.47s
% Output     : CNFRefutation 19.47s
% Verified   : 
% Statistics : Number of formulae       :  156 ( 489 expanded)
%              Number of clauses        :   97 ( 163 expanded)
%              Number of leaves         :   14 ( 114 expanded)
%              Depth                    :   24
%              Number of atoms          :  531 (3152 expanded)
%              Number of equality atoms :  210 ( 311 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k6_partfun1(X0))
          & v2_funct_1(X1)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
     => ( ~ r2_relset_1(X0,X0,sK3,k6_partfun1(X0))
        & v2_funct_1(X1)
        & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,sK3,X1),X1)
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(sK3,X0,X0)
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
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
          ( ~ r2_relset_1(sK1,sK1,X2,k6_partfun1(sK1))
          & v2_funct_1(sK2)
          & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,X2,sK2),sK2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
          & v1_funct_2(X2,sK1,sK1)
          & v1_funct_1(X2) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
      & v1_funct_2(sK2,sK1,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ~ r2_relset_1(sK1,sK1,sK3,k6_partfun1(sK1))
    & v2_funct_1(sK2)
    & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK3,sK2),sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    & v1_funct_2(sK3,sK1,sK1)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    & v1_funct_2(sK2,sK1,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f40,f45,f44])).

fof(f69,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f46])).

fof(f66,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f46])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f24])).

fof(f53,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f64,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f67,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f70,plain,(
    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK3,sK2),sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f21,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f20])).

fof(f49,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f28])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f13])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f14,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f62,plain,(
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
    inference(cnf_transformation,[],[f36])).

fof(f75,plain,(
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
    inference(equality_resolution,[],[f62])).

fof(f71,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f65,plain,(
    v1_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f68,plain,(
    v1_funct_2(sK3,sK1,sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f72,plain,(
    ~ r2_relset_1(sK1,sK1,sK3,k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f46])).

fof(f9,axiom,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f73,plain,(
    ~ r2_relset_1(sK1,sK1,sK3,k6_relat_1(sK1)) ),
    inference(definition_unfolding,[],[f72,f56])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f74,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f58])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_507,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_889,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_507])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_505,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_891,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_505])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_515,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
    | ~ m1_subset_1(X3_48,k1_zfmisc_1(k2_zfmisc_1(X4_48,X5_48)))
    | ~ v1_funct_1(X0_48)
    | ~ v1_funct_1(X3_48)
    | k1_partfun1(X4_48,X5_48,X1_48,X2_48,X3_48,X0_48) = k5_relat_1(X3_48,X0_48) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_881,plain,
    ( k1_partfun1(X0_48,X1_48,X2_48,X3_48,X4_48,X5_48) = k5_relat_1(X4_48,X5_48)
    | m1_subset_1(X5_48,k1_zfmisc_1(k2_zfmisc_1(X2_48,X3_48))) != iProver_top
    | m1_subset_1(X4_48,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top
    | v1_funct_1(X5_48) != iProver_top
    | v1_funct_1(X4_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_515])).

cnf(c_4803,plain,
    ( k1_partfun1(X0_48,X1_48,sK1,sK1,X2_48,sK2) = k5_relat_1(X2_48,sK2)
    | m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top
    | v1_funct_1(X2_48) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_891,c_881])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_25,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_5027,plain,
    ( v1_funct_1(X2_48) != iProver_top
    | m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top
    | k1_partfun1(X0_48,X1_48,sK1,sK1,X2_48,sK2) = k5_relat_1(X2_48,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4803,c_25])).

cnf(c_5028,plain,
    ( k1_partfun1(X0_48,X1_48,sK1,sK1,X2_48,sK2) = k5_relat_1(X2_48,sK2)
    | m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top
    | v1_funct_1(X2_48) != iProver_top ),
    inference(renaming,[status(thm)],[c_5027])).

cnf(c_5033,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,sK3,sK2) = k5_relat_1(sK3,sK2)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_889,c_5028])).

cnf(c_21,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_28,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_5114,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,sK3,sK2) = k5_relat_1(sK3,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5033,c_28])).

cnf(c_18,negated_conjecture,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK3,sK2),sK2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_508,negated_conjecture,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK3,sK2),sK2) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_888,plain,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK3,sK2),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_508])).

cnf(c_5116,plain,
    ( r2_relset_1(sK1,sK1,k5_relat_1(sK3,sK2),sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5114,c_888])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_520,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
    | ~ m1_subset_1(X3_48,k1_zfmisc_1(k2_zfmisc_1(X4_48,X5_48)))
    | m1_subset_1(k1_partfun1(X4_48,X5_48,X1_48,X2_48,X3_48,X0_48),k1_zfmisc_1(k2_zfmisc_1(X4_48,X2_48)))
    | ~ v1_funct_1(X0_48)
    | ~ v1_funct_1(X3_48) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_876,plain,
    ( m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48))) != iProver_top
    | m1_subset_1(X3_48,k1_zfmisc_1(k2_zfmisc_1(X4_48,X5_48))) != iProver_top
    | m1_subset_1(k1_partfun1(X4_48,X5_48,X1_48,X2_48,X3_48,X0_48),k1_zfmisc_1(k2_zfmisc_1(X4_48,X2_48))) = iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(X3_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_520])).

cnf(c_5119,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5114,c_876])).

cnf(c_27,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_30,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_17331,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5119,c_25,c_27,c_28,c_30])).

cnf(c_10,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_511,plain,
    ( ~ r2_relset_1(X0_48,X1_48,X2_48,X3_48)
    | ~ m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48)))
    | ~ m1_subset_1(X3_48,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48)))
    | X3_48 = X2_48 ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_885,plain,
    ( X0_48 = X1_48
    | r2_relset_1(X2_48,X3_48,X1_48,X0_48) != iProver_top
    | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_48,X3_48))) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X2_48,X3_48))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_511])).

cnf(c_17346,plain,
    ( k5_relat_1(sK3,sK2) = X0_48
    | r2_relset_1(sK1,sK1,k5_relat_1(sK3,sK2),X0_48) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_17331,c_885])).

cnf(c_23149,plain,
    ( k5_relat_1(sK3,sK2) = sK2
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5116,c_17346])).

cnf(c_23153,plain,
    ( k5_relat_1(sK3,sK2) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_23149,c_27])).

cnf(c_13,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_14,plain,
    ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X0))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(X0,X1) != X1
    | k6_relat_1(k1_relat_1(X0)) = X0
    | k1_relat_1(X1) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_17,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_291,plain,
    ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(X0,X1) != X1
    | k6_relat_1(k1_relat_1(X0)) = X0
    | k1_relat_1(X1) != k1_relat_1(X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_17])).

cnf(c_292,plain,
    ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK2)
    | k5_relat_1(X0,sK2) != sK2
    | k6_relat_1(k1_relat_1(X0)) = X0
    | k1_relat_1(sK2) != k1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_291])).

cnf(c_296,plain,
    ( ~ v1_funct_1(X0)
    | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK2)
    | k5_relat_1(X0,sK2) != sK2
    | k6_relat_1(k1_relat_1(X0)) = X0
    | k1_relat_1(sK2) != k1_relat_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_292,c_24])).

cnf(c_297,plain,
    ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK2)
    | k5_relat_1(X0,sK2) != sK2
    | k6_relat_1(k1_relat_1(X0)) = X0
    | k1_relat_1(sK2) != k1_relat_1(X0) ),
    inference(renaming,[status(thm)],[c_296])).

cnf(c_332,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(sK2)
    | k5_relat_1(X2,sK2) != sK2
    | k6_relat_1(k1_relat_1(X2)) = X2
    | k2_relat_1(X2) != X0
    | k1_relat_1(X2) != X1
    | k1_relat_1(X2) != k1_relat_1(sK2) ),
    inference(resolution_lifted,[status(thm)],[c_13,c_297])).

cnf(c_333,plain,
    ( ~ m1_subset_1(k2_relat_1(X0),k1_zfmisc_1(k1_relat_1(X0)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK2)
    | k5_relat_1(X0,sK2) != sK2
    | k6_relat_1(k1_relat_1(X0)) = X0
    | k1_relat_1(X0) != k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_332])).

cnf(c_501,plain,
    ( ~ m1_subset_1(k2_relat_1(X0_48),k1_zfmisc_1(k1_relat_1(X0_48)))
    | ~ v1_funct_1(X0_48)
    | ~ v1_relat_1(X0_48)
    | ~ v1_relat_1(sK2)
    | k5_relat_1(X0_48,sK2) != sK2
    | k6_relat_1(k1_relat_1(X0_48)) = X0_48
    | k1_relat_1(X0_48) != k1_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_333])).

cnf(c_893,plain,
    ( k5_relat_1(X0_48,sK2) != sK2
    | k6_relat_1(k1_relat_1(X0_48)) = X0_48
    | k1_relat_1(X0_48) != k1_relat_1(sK2)
    | m1_subset_1(k2_relat_1(X0_48),k1_zfmisc_1(k1_relat_1(X0_48))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_relat_1(X0_48) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_501])).

cnf(c_577,plain,
    ( k5_relat_1(X0_48,sK2) != sK2
    | k6_relat_1(k1_relat_1(X0_48)) = X0_48
    | k1_relat_1(X0_48) != k1_relat_1(sK2)
    | m1_subset_1(k2_relat_1(X0_48),k1_zfmisc_1(k1_relat_1(X0_48))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_relat_1(X0_48) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_501])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_521,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
    | v1_relat_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_928,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_521])).

cnf(c_929,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_928])).

cnf(c_931,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_929])).

cnf(c_5192,plain,
    ( v1_relat_1(X0_48) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | m1_subset_1(k2_relat_1(X0_48),k1_zfmisc_1(k1_relat_1(X0_48))) != iProver_top
    | k1_relat_1(X0_48) != k1_relat_1(sK2)
    | k6_relat_1(k1_relat_1(X0_48)) = X0_48
    | k5_relat_1(X0_48,sK2) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_893,c_27,c_577,c_931])).

cnf(c_5193,plain,
    ( k5_relat_1(X0_48,sK2) != sK2
    | k6_relat_1(k1_relat_1(X0_48)) = X0_48
    | k1_relat_1(X0_48) != k1_relat_1(sK2)
    | m1_subset_1(k2_relat_1(X0_48),k1_zfmisc_1(k1_relat_1(X0_48))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_relat_1(X0_48) != iProver_top ),
    inference(renaming,[status(thm)],[c_5192])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_514,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
    | k1_relset_1(X1_48,X2_48,X0_48) = k1_relat_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_882,plain,
    ( k1_relset_1(X0_48,X1_48,X2_48) = k1_relat_1(X2_48)
    | m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_514])).

cnf(c_1351,plain,
    ( k1_relset_1(sK1,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_891,c_882])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k1_relset_1(X1,X1,X0) = X1 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_23,negated_conjecture,
    ( v1_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_281,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k1_relset_1(X1,X1,X0) = X1
    | sK2 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_23])).

cnf(c_282,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK2)
    | k1_relset_1(sK1,sK1,sK2) = sK1 ),
    inference(unflattening,[status(thm)],[c_281])).

cnf(c_284,plain,
    ( k1_relset_1(sK1,sK1,sK2) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_282,c_24,c_22])).

cnf(c_502,plain,
    ( k1_relset_1(sK1,sK1,sK2) = sK1 ),
    inference(subtyping,[status(esa)],[c_284])).

cnf(c_1353,plain,
    ( k1_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_1351,c_502])).

cnf(c_5198,plain,
    ( k5_relat_1(X0_48,sK2) != sK2
    | k6_relat_1(k1_relat_1(X0_48)) = X0_48
    | k1_relat_1(X0_48) != sK1
    | m1_subset_1(k2_relat_1(X0_48),k1_zfmisc_1(k1_relat_1(X0_48))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_relat_1(X0_48) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5193,c_1353])).

cnf(c_23179,plain,
    ( k6_relat_1(k1_relat_1(sK3)) = sK3
    | k1_relat_1(sK3) != sK1
    | m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(k1_relat_1(sK3))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_23153,c_5198])).

cnf(c_1350,plain,
    ( k1_relset_1(sK1,sK1,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_889,c_882])).

cnf(c_20,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_273,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k1_relset_1(X1,X1,X0) = X1
    | sK3 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_20])).

cnf(c_274,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK3)
    | k1_relset_1(sK1,sK1,sK3) = sK1 ),
    inference(unflattening,[status(thm)],[c_273])).

cnf(c_276,plain,
    ( k1_relset_1(sK1,sK1,sK3) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_274,c_21,c_19])).

cnf(c_503,plain,
    ( k1_relset_1(sK1,sK1,sK3) = sK1 ),
    inference(subtyping,[status(esa)],[c_276])).

cnf(c_1354,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_1350,c_503])).

cnf(c_23180,plain,
    ( k6_relat_1(sK1) = sK3
    | sK1 != sK1
    | m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_23179,c_1354])).

cnf(c_23181,plain,
    ( k6_relat_1(sK1) = sK3
    | m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_23180])).

cnf(c_977,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_521])).

cnf(c_978,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_977])).

cnf(c_980,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_978])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_513,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
    | k2_relset_1(X1_48,X2_48,X0_48) = k2_relat_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_883,plain,
    ( k2_relset_1(X0_48,X1_48,X2_48) = k2_relat_1(X2_48)
    | m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_513])).

cnf(c_1357,plain,
    ( k2_relset_1(sK1,sK1,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_889,c_883])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_517,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
    | m1_subset_1(k2_relset_1(X1_48,X2_48,X0_48),k1_zfmisc_1(X2_48)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_879,plain,
    ( m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48))) != iProver_top
    | m1_subset_1(k2_relset_1(X1_48,X2_48,X0_48),k1_zfmisc_1(X2_48)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_517])).

cnf(c_2272,plain,
    ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1)) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1357,c_879])).

cnf(c_41963,plain,
    ( k6_relat_1(sK1) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_23181,c_28,c_30,c_980,c_2272])).

cnf(c_16,negated_conjecture,
    ( ~ r2_relset_1(sK1,sK1,sK3,k6_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_509,negated_conjecture,
    ( ~ r2_relset_1(sK1,sK1,sK3,k6_relat_1(sK1)) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_887,plain,
    ( r2_relset_1(sK1,sK1,sK3,k6_relat_1(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_509])).

cnf(c_41965,plain,
    ( r2_relset_1(sK1,sK1,sK3,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_41963,c_887])).

cnf(c_9,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_512,plain,
    ( r2_relset_1(X0_48,X1_48,X2_48,X2_48)
    | ~ m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_884,plain,
    ( r2_relset_1(X0_48,X1_48,X2_48,X2_48) = iProver_top
    | m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_512])).

cnf(c_1471,plain,
    ( r2_relset_1(sK1,sK1,sK3,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_889,c_884])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_41965,c_1471])).


%------------------------------------------------------------------------------
