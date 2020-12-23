%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1015+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:39 EST 2020

% Result     : Theorem 11.31s
% Output     : CNFRefutation 11.31s
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f41,plain,(
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

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k6_partfun1(X0))
          & v2_funct_1(X1)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
     => ( ~ r2_relset_1(X0,X0,sK2,k6_partfun1(X0))
        & v2_funct_1(X1)
        & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,sK2,X1),X1)
        & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(sK2,X0,X0)
        & v1_funct_1(sK2) ) ) ),
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
          ( ~ r2_relset_1(sK0,sK0,X2,k6_partfun1(sK0))
          & v2_funct_1(sK1)
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,X2,sK1),sK1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
          & v1_funct_2(X2,sK0,sK0)
          & v1_funct_1(X2) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0))
    & v2_funct_1(sK1)
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK2,sK0,sK0)
    & v1_funct_1(sK2)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f42,f45,f44])).

fof(f69,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f46])).

fof(f66,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f46])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f27,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f26])).

fof(f53,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f64,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f67,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f70,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f30])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f31])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f13])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f36])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
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
    inference(flattening,[],[f37])).

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
    inference(cnf_transformation,[],[f38])).

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
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f39])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f65,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f68,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    ~ r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f46])).

fof(f9,axiom,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f73,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k6_relat_1(sK0)) ),
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
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_508,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_888,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_508])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_506,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_890,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_506])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_516,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
    | ~ m1_subset_1(X3_47,k1_zfmisc_1(k2_zfmisc_1(X4_47,X5_47)))
    | ~ v1_funct_1(X0_47)
    | ~ v1_funct_1(X3_47)
    | k1_partfun1(X4_47,X5_47,X1_47,X2_47,X3_47,X0_47) = k5_relat_1(X3_47,X0_47) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_880,plain,
    ( k1_partfun1(X0_47,X1_47,X2_47,X3_47,X4_47,X5_47) = k5_relat_1(X4_47,X5_47)
    | m1_subset_1(X5_47,k1_zfmisc_1(k2_zfmisc_1(X2_47,X3_47))) != iProver_top
    | m1_subset_1(X4_47,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top
    | v1_funct_1(X5_47) != iProver_top
    | v1_funct_1(X4_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_516])).

cnf(c_4788,plain,
    ( k1_partfun1(X0_47,X1_47,sK0,sK0,X2_47,sK1) = k5_relat_1(X2_47,sK1)
    | m1_subset_1(X2_47,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top
    | v1_funct_1(X2_47) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_890,c_880])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_25,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_5014,plain,
    ( v1_funct_1(X2_47) != iProver_top
    | m1_subset_1(X2_47,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top
    | k1_partfun1(X0_47,X1_47,sK0,sK0,X2_47,sK1) = k5_relat_1(X2_47,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4788,c_25])).

cnf(c_5015,plain,
    ( k1_partfun1(X0_47,X1_47,sK0,sK0,X2_47,sK1) = k5_relat_1(X2_47,sK1)
    | m1_subset_1(X2_47,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top
    | v1_funct_1(X2_47) != iProver_top ),
    inference(renaming,[status(thm)],[c_5014])).

cnf(c_5020,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) = k5_relat_1(sK2,sK1)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_888,c_5015])).

cnf(c_21,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_28,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_5097,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) = k5_relat_1(sK2,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5020,c_28])).

cnf(c_18,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),sK1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_509,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),sK1) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_887,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_509])).

cnf(c_5099,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK1),sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5097,c_887])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_521,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
    | ~ m1_subset_1(X3_47,k1_zfmisc_1(k2_zfmisc_1(X4_47,X5_47)))
    | m1_subset_1(k1_partfun1(X4_47,X5_47,X1_47,X2_47,X3_47,X0_47),k1_zfmisc_1(k2_zfmisc_1(X4_47,X2_47)))
    | ~ v1_funct_1(X0_47)
    | ~ v1_funct_1(X3_47) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_875,plain,
    ( m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47))) != iProver_top
    | m1_subset_1(X3_47,k1_zfmisc_1(k2_zfmisc_1(X4_47,X5_47))) != iProver_top
    | m1_subset_1(k1_partfun1(X4_47,X5_47,X1_47,X2_47,X3_47,X0_47),k1_zfmisc_1(k2_zfmisc_1(X4_47,X2_47))) = iProver_top
    | v1_funct_1(X0_47) != iProver_top
    | v1_funct_1(X3_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_521])).

cnf(c_5102,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5097,c_875])).

cnf(c_27,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_30,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_11951,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5102,c_25,c_27,c_28,c_30])).

cnf(c_10,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_512,plain,
    ( ~ r2_relset_1(X0_47,X1_47,X2_47,X3_47)
    | ~ m1_subset_1(X2_47,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
    | ~ m1_subset_1(X3_47,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
    | X3_47 = X2_47 ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_884,plain,
    ( X0_47 = X1_47
    | r2_relset_1(X2_47,X3_47,X1_47,X0_47) != iProver_top
    | m1_subset_1(X1_47,k1_zfmisc_1(k2_zfmisc_1(X2_47,X3_47))) != iProver_top
    | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X2_47,X3_47))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_512])).

cnf(c_11966,plain,
    ( k5_relat_1(sK2,sK1) = X0_47
    | r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK1),X0_47) != iProver_top
    | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_11951,c_884])).

cnf(c_13589,plain,
    ( k5_relat_1(sK2,sK1) = sK1
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5099,c_11966])).

cnf(c_13733,plain,
    ( k5_relat_1(sK2,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_13589,c_27])).

cnf(c_13,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_14,plain,
    ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X0))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,X1) != X1
    | k6_relat_1(k1_relat_1(X0)) = X0
    | k1_relat_1(X1) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_17,negated_conjecture,
    ( v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_292,plain,
    ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,X1) != X1
    | k6_relat_1(k1_relat_1(X0)) = X0
    | k1_relat_1(X1) != k1_relat_1(X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_17])).

cnf(c_293,plain,
    ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK1)
    | k5_relat_1(X0,sK1) != sK1
    | k6_relat_1(k1_relat_1(X0)) = X0
    | k1_relat_1(sK1) != k1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_292])).

cnf(c_297,plain,
    ( ~ v1_funct_1(X0)
    | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK1)
    | k5_relat_1(X0,sK1) != sK1
    | k6_relat_1(k1_relat_1(X0)) = X0
    | k1_relat_1(sK1) != k1_relat_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_293,c_24])).

cnf(c_298,plain,
    ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK1)
    | k5_relat_1(X0,sK1) != sK1
    | k6_relat_1(k1_relat_1(X0)) = X0
    | k1_relat_1(sK1) != k1_relat_1(X0) ),
    inference(renaming,[status(thm)],[c_297])).

cnf(c_333,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(sK1)
    | k5_relat_1(X2,sK1) != sK1
    | k6_relat_1(k1_relat_1(X2)) = X2
    | k2_relat_1(X2) != X0
    | k1_relat_1(X2) != X1
    | k1_relat_1(X2) != k1_relat_1(sK1) ),
    inference(resolution_lifted,[status(thm)],[c_13,c_298])).

cnf(c_334,plain,
    ( ~ m1_subset_1(k2_relat_1(X0),k1_zfmisc_1(k1_relat_1(X0)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK1)
    | k5_relat_1(X0,sK1) != sK1
    | k6_relat_1(k1_relat_1(X0)) = X0
    | k1_relat_1(X0) != k1_relat_1(sK1) ),
    inference(unflattening,[status(thm)],[c_333])).

cnf(c_502,plain,
    ( ~ m1_subset_1(k2_relat_1(X0_47),k1_zfmisc_1(k1_relat_1(X0_47)))
    | ~ v1_funct_1(X0_47)
    | ~ v1_relat_1(X0_47)
    | ~ v1_relat_1(sK1)
    | k5_relat_1(X0_47,sK1) != sK1
    | k6_relat_1(k1_relat_1(X0_47)) = X0_47
    | k1_relat_1(X0_47) != k1_relat_1(sK1) ),
    inference(subtyping,[status(esa)],[c_334])).

cnf(c_892,plain,
    ( k5_relat_1(X0_47,sK1) != sK1
    | k6_relat_1(k1_relat_1(X0_47)) = X0_47
    | k1_relat_1(X0_47) != k1_relat_1(sK1)
    | m1_subset_1(k2_relat_1(X0_47),k1_zfmisc_1(k1_relat_1(X0_47))) != iProver_top
    | v1_funct_1(X0_47) != iProver_top
    | v1_relat_1(X0_47) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_502])).

cnf(c_576,plain,
    ( k5_relat_1(X0_47,sK1) != sK1
    | k6_relat_1(k1_relat_1(X0_47)) = X0_47
    | k1_relat_1(X0_47) != k1_relat_1(sK1)
    | m1_subset_1(k2_relat_1(X0_47),k1_zfmisc_1(k1_relat_1(X0_47))) != iProver_top
    | v1_funct_1(X0_47) != iProver_top
    | v1_relat_1(X0_47) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_502])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_522,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
    | v1_relat_1(X0_47) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_927,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
    | v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_522])).

cnf(c_928,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top
    | v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_927])).

cnf(c_930,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_relat_1(sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_928])).

cnf(c_5167,plain,
    ( v1_relat_1(X0_47) != iProver_top
    | v1_funct_1(X0_47) != iProver_top
    | m1_subset_1(k2_relat_1(X0_47),k1_zfmisc_1(k1_relat_1(X0_47))) != iProver_top
    | k1_relat_1(X0_47) != k1_relat_1(sK1)
    | k6_relat_1(k1_relat_1(X0_47)) = X0_47
    | k5_relat_1(X0_47,sK1) != sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_892,c_27,c_576,c_930])).

cnf(c_5168,plain,
    ( k5_relat_1(X0_47,sK1) != sK1
    | k6_relat_1(k1_relat_1(X0_47)) = X0_47
    | k1_relat_1(X0_47) != k1_relat_1(sK1)
    | m1_subset_1(k2_relat_1(X0_47),k1_zfmisc_1(k1_relat_1(X0_47))) != iProver_top
    | v1_funct_1(X0_47) != iProver_top
    | v1_relat_1(X0_47) != iProver_top ),
    inference(renaming,[status(thm)],[c_5167])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_515,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
    | k1_relset_1(X1_47,X2_47,X0_47) = k1_relat_1(X0_47) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_881,plain,
    ( k1_relset_1(X0_47,X1_47,X2_47) = k1_relat_1(X2_47)
    | m1_subset_1(X2_47,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_515])).

cnf(c_1216,plain,
    ( k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_890,c_881])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k1_relset_1(X1,X1,X0) = X1 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_23,negated_conjecture,
    ( v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_282,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k1_relset_1(X1,X1,X0) = X1
    | sK1 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_23])).

cnf(c_283,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | k1_relset_1(sK0,sK0,sK1) = sK0 ),
    inference(unflattening,[status(thm)],[c_282])).

cnf(c_285,plain,
    ( k1_relset_1(sK0,sK0,sK1) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_283,c_24,c_22])).

cnf(c_503,plain,
    ( k1_relset_1(sK0,sK0,sK1) = sK0 ),
    inference(subtyping,[status(esa)],[c_285])).

cnf(c_1217,plain,
    ( k1_relat_1(sK1) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_1216,c_503])).

cnf(c_5173,plain,
    ( k5_relat_1(X0_47,sK1) != sK1
    | k6_relat_1(k1_relat_1(X0_47)) = X0_47
    | k1_relat_1(X0_47) != sK0
    | m1_subset_1(k2_relat_1(X0_47),k1_zfmisc_1(k1_relat_1(X0_47))) != iProver_top
    | v1_funct_1(X0_47) != iProver_top
    | v1_relat_1(X0_47) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5168,c_1217])).

cnf(c_13759,plain,
    ( k6_relat_1(k1_relat_1(sK2)) = sK2
    | k1_relat_1(sK2) != sK0
    | m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(k1_relat_1(sK2))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_13733,c_5173])).

cnf(c_1215,plain,
    ( k1_relset_1(sK0,sK0,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_888,c_881])).

cnf(c_20,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_274,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k1_relset_1(X1,X1,X0) = X1
    | sK2 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_20])).

cnf(c_275,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | k1_relset_1(sK0,sK0,sK2) = sK0 ),
    inference(unflattening,[status(thm)],[c_274])).

cnf(c_277,plain,
    ( k1_relset_1(sK0,sK0,sK2) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_275,c_21,c_19])).

cnf(c_504,plain,
    ( k1_relset_1(sK0,sK0,sK2) = sK0 ),
    inference(subtyping,[status(esa)],[c_277])).

cnf(c_1218,plain,
    ( k1_relat_1(sK2) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_1215,c_504])).

cnf(c_13761,plain,
    ( k6_relat_1(sK0) = sK2
    | sK0 != sK0
    | m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13759,c_1218])).

cnf(c_13762,plain,
    ( k6_relat_1(sK0) = sK2
    | m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_13761])).

cnf(c_976,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_522])).

cnf(c_977,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_976])).

cnf(c_979,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_977])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_514,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
    | k2_relset_1(X1_47,X2_47,X0_47) = k2_relat_1(X0_47) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_882,plain,
    ( k2_relset_1(X0_47,X1_47,X2_47) = k2_relat_1(X2_47)
    | m1_subset_1(X2_47,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_514])).

cnf(c_1349,plain,
    ( k2_relset_1(sK0,sK0,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_888,c_882])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_518,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
    | m1_subset_1(k2_relset_1(X1_47,X2_47,X0_47),k1_zfmisc_1(X2_47)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_878,plain,
    ( m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47))) != iProver_top
    | m1_subset_1(k2_relset_1(X1_47,X2_47,X0_47),k1_zfmisc_1(X2_47)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_518])).

cnf(c_2269,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK0)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1349,c_878])).

cnf(c_23741,plain,
    ( k6_relat_1(sK0) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_13762,c_28,c_30,c_979,c_2269])).

cnf(c_16,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK0,sK2,k6_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_510,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK0,sK2,k6_relat_1(sK0)) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_886,plain,
    ( r2_relset_1(sK0,sK0,sK2,k6_relat_1(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_510])).

cnf(c_23743,plain,
    ( r2_relset_1(sK0,sK0,sK2,sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_23741,c_886])).

cnf(c_9,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_513,plain,
    ( r2_relset_1(X0_47,X1_47,X2_47,X2_47)
    | ~ m1_subset_1(X2_47,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_883,plain,
    ( r2_relset_1(X0_47,X1_47,X2_47,X2_47) = iProver_top
    | m1_subset_1(X2_47,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_513])).

cnf(c_1352,plain,
    ( r2_relset_1(sK0,sK0,sK2,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_888,c_883])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_23743,c_1352])).


%------------------------------------------------------------------------------
