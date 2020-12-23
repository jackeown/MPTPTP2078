%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:07:20 EST 2020

% Result     : Theorem 7.74s
% Output     : CNFRefutation 7.74s
% Verified   : 
% Statistics : Number of formulae       :  230 (1680 expanded)
%              Number of clauses        :  144 ( 547 expanded)
%              Number of leaves         :   25 ( 327 expanded)
%              Depth                    :   23
%              Number of atoms          :  811 (7773 expanded)
%              Number of equality atoms :  332 ( 913 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   12 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f44,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f45,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f44])).

fof(f53,plain,
    ( ? [X0,X1] :
        ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
        | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
      & v3_funct_2(sK2,sK1,sK1)
      & v1_funct_2(sK2,sK1,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
    ( ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
      | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    & v3_funct_2(sK2,sK1,sK1)
    & v1_funct_2(sK2,sK1,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f45,f53])).

fof(f89,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f54])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_2(X0,X1) = k2_funct_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f40])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f86,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f87,plain,(
    v1_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f88,plain,(
    v3_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f36])).

fof(f80,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f38])).

fof(f81,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f77,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k2_funct_2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f13,axiom,(
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
    inference(ennf_transformation,[],[f13])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f34])).

fof(f76,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f9,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f9])).

fof(f17,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f83,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f17])).

fof(f91,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f67,f83])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f26])).

fof(f49,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f3,axiom,(
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
    inference(nnf_transformation,[],[f3])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f2,axiom,(
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
    inference(nnf_transformation,[],[f2])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f46])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f93,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f56])).

fof(f58,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f30])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_2(X2,X1)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f12,axiom,(
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
    inference(ennf_transformation,[],[f12])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f18,axiom,(
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

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f42])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
         => ( ! [X3] :
                ( r2_hidden(X3,X0)
               => k11_relat_1(X1,X3) = k11_relat_1(X2,X3) )
           => r2_relset_1(X0,X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_relset_1(X0,X0,X1,X2)
          | ? [X3] :
              ( k11_relat_1(X1,X3) != k11_relat_1(X2,X3)
              & r2_hidden(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_relset_1(X0,X0,X1,X2)
          | ? [X3] :
              ( k11_relat_1(X1,X3) != k11_relat_1(X2,X3)
              & r2_hidden(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(flattening,[],[f28])).

fof(f50,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k11_relat_1(X1,X3) != k11_relat_1(X2,X3)
          & r2_hidden(X3,X0) )
     => ( k11_relat_1(X1,sK0(X0,X1,X2)) != k11_relat_1(X2,sK0(X0,X1,X2))
        & r2_hidden(sK0(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_relset_1(X0,X0,X1,X2)
          | ( k11_relat_1(X1,sK0(X0,X1,X2)) != k11_relat_1(X2,sK0(X0,X1,X2))
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f50])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r2_relset_1(X0,X0,X1,X2)
      | r2_hidden(sK0(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f90,plain,
    ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
    | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f54])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f94,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f66])).

cnf(c_988,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | r2_relset_1(X4,X5,X6,X7)
    | X4 != X0
    | X5 != X1
    | X6 != X2
    | X7 != X3 ),
    theory(equality)).

cnf(c_1864,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | r2_relset_1(X4,X5,X6,k6_partfun1(sK1))
    | X4 != X0
    | X5 != X1
    | X6 != X2
    | k6_partfun1(sK1) != X3 ),
    inference(instantiation,[status(thm)],[c_988])).

cnf(c_2182,plain,
    ( ~ r2_relset_1(X0,X1,X2,k6_partfun1(sK1))
    | r2_relset_1(X3,X4,X5,k6_partfun1(sK1))
    | X3 != X0
    | X4 != X1
    | X5 != X2
    | k6_partfun1(sK1) != k6_partfun1(sK1) ),
    inference(instantiation,[status(thm)],[c_1864])).

cnf(c_2798,plain,
    ( r2_relset_1(X0,X1,X2,k6_partfun1(sK1))
    | ~ r2_relset_1(X3,X4,k6_partfun1(sK1),k6_partfun1(sK1))
    | X0 != X3
    | X1 != X4
    | X2 != k6_partfun1(sK1)
    | k6_partfun1(sK1) != k6_partfun1(sK1) ),
    inference(instantiation,[status(thm)],[c_2182])).

cnf(c_17993,plain,
    ( r2_relset_1(X0,X1,k5_relat_1(k2_funct_1(sK2),sK2),k6_partfun1(sK1))
    | ~ r2_relset_1(X2,X3,k6_partfun1(sK1),k6_partfun1(sK1))
    | X0 != X2
    | X1 != X3
    | k5_relat_1(k2_funct_1(sK2),sK2) != k6_partfun1(sK1)
    | k6_partfun1(sK1) != k6_partfun1(sK1) ),
    inference(instantiation,[status(thm)],[c_2798])).

cnf(c_17995,plain,
    ( r2_relset_1(sK1,sK1,k5_relat_1(k2_funct_1(sK2),sK2),k6_partfun1(sK1))
    | ~ r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1))
    | k5_relat_1(k2_funct_1(sK2),sK2) != k6_partfun1(sK1)
    | k6_partfun1(sK1) != k6_partfun1(sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_17993])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1619,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_27,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1623,plain,
    ( k2_funct_2(X0,X1) = k2_funct_1(X1)
    | v1_funct_2(X1,X0,X0) != iProver_top
    | v3_funct_2(X1,X0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_2912,plain,
    ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1619,c_1623])).

cnf(c_34,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_35,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( v1_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_36,plain,
    ( v1_funct_2(sK2,sK1,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_32,negated_conjecture,
    ( v3_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_37,plain,
    ( v3_funct_2(sK2,sK1,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_3080,plain,
    ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2912,c_35,c_36,c_37])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1628,plain,
    ( v1_funct_2(X0,X1,X1) != iProver_top
    | v3_funct_2(X0,X1,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3459,plain,
    ( v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3080,c_1628])).

cnf(c_38,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_3707,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3459,c_35,c_36,c_37,c_38])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1624,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_4025,plain,
    ( k1_partfun1(X0,X1,sK1,sK1,X2,k2_funct_1(sK2)) = k5_relat_1(X2,k2_funct_1(sK2))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3707,c_1624])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_2(X1,X0)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1625,plain,
    ( v1_funct_2(X0,X1,X1) != iProver_top
    | v3_funct_2(X0,X1,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_2(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2923,plain,
    ( v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(k2_funct_2(sK1,sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1619,c_1625])).

cnf(c_1737,plain,
    ( ~ v1_funct_2(sK2,sK1,sK1)
    | ~ v3_funct_2(sK2,sK1,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | v1_funct_1(k2_funct_2(sK1,sK2))
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_1738,plain,
    ( v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(k2_funct_2(sK1,sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1737])).

cnf(c_3157,plain,
    ( v1_funct_1(k2_funct_2(sK1,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2923,c_35,c_36,c_37,c_38,c_1738])).

cnf(c_3161,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3157,c_3080])).

cnf(c_7565,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK1,X2,k2_funct_1(sK2)) = k5_relat_1(X2,k2_funct_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4025,c_3161])).

cnf(c_7566,plain,
    ( k1_partfun1(X0,X1,sK1,sK1,X2,k2_funct_1(sK2)) = k5_relat_1(X2,k2_funct_1(sK2))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_7565])).

cnf(c_7575,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2))
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1619,c_7566])).

cnf(c_8349,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7575,c_35])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1630,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_8353,plain,
    ( m1_subset_1(k5_relat_1(sK2,k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_8349,c_1630])).

cnf(c_8687,plain,
    ( m1_subset_1(k5_relat_1(sK2,k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8353,c_35,c_36,c_37,c_38,c_3161,c_3459])).

cnf(c_12,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1633,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_11,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1634,plain,
    ( X0 = X1
    | r2_relset_1(X2,X3,X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2846,plain,
    ( k6_partfun1(X0) = X1
    | r2_relset_1(X0,X0,k6_partfun1(X0),X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1633,c_1634])).

cnf(c_9611,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK1)
    | r2_relset_1(sK1,sK1,k6_partfun1(sK1),k5_relat_1(sK2,k2_funct_1(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8687,c_2846])).

cnf(c_4,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_113,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_115,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK1)) = iProver_top
    | r1_tarski(sK1,sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_113])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_117,plain,
    ( r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_116,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_118,plain,
    ( r1_tarski(sK1,sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_116])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_121,plain,
    ( ~ r1_tarski(sK1,sK1)
    | sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_986,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1698,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0))
    | k1_zfmisc_1(k1_xboole_0) != X1
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_986])).

cnf(c_1778,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0))
    | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(X1)
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_1698])).

cnf(c_1779,plain,
    ( k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(X0)
    | sK1 != X1
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1778])).

cnf(c_1781,plain,
    ( k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(sK1)
    | sK1 != sK1
    | m1_subset_1(sK1,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1779])).

cnf(c_985,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_1901,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(X0)
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_985])).

cnf(c_1902,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(sK1)
    | k1_xboole_0 != sK1 ),
    inference(instantiation,[status(thm)],[c_1901])).

cnf(c_15,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | v2_funct_2(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_8,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_19,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_528,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_8,c_19])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_540,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | k2_relat_1(X0) = X1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_528,c_7])).

cnf(c_571,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | X3 != X0
    | X5 != X2
    | k2_relat_1(X3) = X5 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_540])).

cnf(c_572,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ v1_funct_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(unflattening,[status(thm)],[c_571])).

cnf(c_1614,plain,
    ( k2_relat_1(X0) = X1
    | v3_funct_2(X0,X2,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_572])).

cnf(c_2078,plain,
    ( k2_relat_1(sK2) = sK1
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1619,c_1614])).

cnf(c_2083,plain,
    ( k2_relat_1(sK2) = sK1
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2078])).

cnf(c_2499,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2078,c_35,c_37,c_38,c_2083])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1636,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2217,plain,
    ( k2_relset_1(sK1,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1619,c_1636])).

cnf(c_2501,plain,
    ( k2_relset_1(sK1,sK1,sK2) = sK1 ),
    inference(demodulation,[status(thm)],[c_2499,c_2217])).

cnf(c_16,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v2_funct_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1631,plain,
    ( v3_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v2_funct_1(X0) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2836,plain,
    ( v3_funct_2(sK2,sK1,sK1) != iProver_top
    | v2_funct_1(sK2) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1619,c_1631])).

cnf(c_2843,plain,
    ( ~ v3_funct_2(sK2,sK1,sK1)
    | v2_funct_1(sK2)
    | ~ v1_funct_1(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2836])).

cnf(c_29,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_8426,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
    | k1_xboole_0 = X1 ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_8433,plain,
    ( ~ v1_funct_2(sK2,sK1,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(sK1,sK1,sK2) != sK1
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_8426])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1637,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1994,plain,
    ( r1_tarski(k6_partfun1(X0),k2_zfmisc_1(X0,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1633,c_1637])).

cnf(c_1638,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_454,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | k1_xboole_0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_6])).

cnf(c_455,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(unflattening,[status(thm)],[c_454])).

cnf(c_14,plain,
    ( r2_relset_1(X0,X0,X1,X2)
    | r2_hidden(sK0(X0,X1,X2),X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_469,plain,
    ( r2_relset_1(X0,X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
    | X0 != X3
    | sK0(X0,X1,X2) != X4 ),
    inference(resolution_lifted,[status(thm)],[c_455,c_14])).

cnf(c_470,plain,
    ( r2_relset_1(X0,X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(unflattening,[status(thm)],[c_469])).

cnf(c_1615,plain,
    ( r2_relset_1(X0,X0,X1,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_470])).

cnf(c_2687,plain,
    ( r2_relset_1(X0,X0,X1,X2) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(X1,k2_zfmisc_1(X0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1638,c_1615])).

cnf(c_7693,plain,
    ( r2_relset_1(sK1,sK1,X0,sK2) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(X0,k2_zfmisc_1(sK1,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1619,c_2687])).

cnf(c_8412,plain,
    ( r2_relset_1(sK1,sK1,k6_partfun1(sK1),sK2) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1994,c_7693])).

cnf(c_30,negated_conjecture,
    ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
    | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_39,plain,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) != iProver_top
    | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_89,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_91,plain,
    ( m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_89])).

cnf(c_1674,plain,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
    | ~ m1_subset_1(k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_470])).

cnf(c_1675,plain,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) = iProver_top
    | m1_subset_1(k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1674])).

cnf(c_1687,plain,
    ( m1_subset_1(k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ m1_subset_1(k2_funct_2(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(k2_funct_2(sK1,sK2))
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_1688,plain,
    ( m1_subset_1(k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top
    | m1_subset_1(k2_funct_2(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(k2_funct_2(sK1,sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1687])).

cnf(c_1877,plain,
    ( ~ v1_funct_2(sK2,sK1,sK1)
    | ~ v3_funct_2(sK2,sK1,sK1)
    | m1_subset_1(k2_funct_2(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_1878,plain,
    ( v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | m1_subset_1(k2_funct_2(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1877])).

cnf(c_3431,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_partfun1(X1,X2,X3,X4,X0,k2_funct_2(sK1,sK2)),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
    | ~ m1_subset_1(k2_funct_2(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_2(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_6079,plain,
    ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,sK2,k2_funct_2(sK1,sK2)),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
    | ~ m1_subset_1(k2_funct_2(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(k2_funct_2(sK1,sK2))
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_3431])).

cnf(c_6080,plain,
    ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,sK2,k2_funct_2(sK1,sK2)),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) = iProver_top
    | m1_subset_1(k2_funct_2(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(k2_funct_2(sK1,sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6079])).

cnf(c_6082,plain,
    ( m1_subset_1(k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top
    | m1_subset_1(k2_funct_2(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(k2_funct_2(sK1,sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6080])).

cnf(c_1855,plain,
    ( r2_relset_1(X0,X0,X1,k6_partfun1(sK1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
    | ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(instantiation,[status(thm)],[c_470])).

cnf(c_8492,plain,
    ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X2,X0,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
    | ~ m1_subset_1(k1_partfun1(X0,X1,X2,X0,sK2,k2_funct_2(sK1,sK2)),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(instantiation,[status(thm)],[c_1855])).

cnf(c_8524,plain,
    ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X2,X0,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | m1_subset_1(k1_partfun1(X0,X1,X2,X0,sK2,k2_funct_2(sK1,sK2)),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8492])).

cnf(c_8526,plain,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) = iProver_top
    | m1_subset_1(k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_8524])).

cnf(c_8581,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8412,c_35,c_36,c_37,c_38,c_39,c_91,c_1675,c_1688,c_1738,c_1878,c_6082,c_8526])).

cnf(c_9773,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9611,c_34,c_35,c_33,c_36,c_32,c_37,c_31,c_38,c_39,c_91,c_115,c_117,c_118,c_121,c_1675,c_1688,c_1738,c_1781,c_1878,c_1902,c_2501,c_2843,c_6082,c_8433,c_8526])).

cnf(c_4024,plain,
    ( k1_partfun1(X0,X1,sK1,sK1,X2,sK2) = k5_relat_1(X2,sK2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1619,c_1624])).

cnf(c_4316,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK1,X2,sK2) = k5_relat_1(X2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4024,c_35])).

cnf(c_4317,plain,
    ( k1_partfun1(X0,X1,sK1,sK1,X2,sK2) = k5_relat_1(X2,sK2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_4316])).

cnf(c_4327,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k5_relat_1(k2_funct_1(sK2),sK2)
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3707,c_4317])).

cnf(c_4431,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k5_relat_1(k2_funct_1(sK2),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4327,c_3161])).

cnf(c_1620,plain,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) != iProver_top
    | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_3082,plain,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1)) != iProver_top
    | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)),k6_partfun1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3080,c_1620])).

cnf(c_4433,plain,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)),k6_partfun1(sK1)) != iProver_top
    | r2_relset_1(sK1,sK1,k5_relat_1(k2_funct_1(sK2),sK2),k6_partfun1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4431,c_3082])).

cnf(c_8351,plain,
    ( r2_relset_1(sK1,sK1,k5_relat_1(k2_funct_1(sK2),sK2),k6_partfun1(sK1)) != iProver_top
    | r2_relset_1(sK1,sK1,k5_relat_1(sK2,k2_funct_1(sK2)),k6_partfun1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8349,c_4433])).

cnf(c_9784,plain,
    ( r2_relset_1(sK1,sK1,k5_relat_1(k2_funct_1(sK2),sK2),k6_partfun1(sK1)) != iProver_top
    | r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9773,c_8351])).

cnf(c_9787,plain,
    ( ~ r2_relset_1(sK1,sK1,k5_relat_1(k2_funct_1(sK2),sK2),k6_partfun1(sK1))
    | ~ r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_9784])).

cnf(c_28,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_8427,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(X1)
    | k1_xboole_0 = X1 ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_8429,plain,
    ( ~ v1_funct_2(sK2,sK1,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(sK1,sK1,sK2) != sK1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_8427])).

cnf(c_10,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1635,plain,
    ( r2_relset_1(X0,X1,X2,X2) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2205,plain,
    ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1633,c_1635])).

cnf(c_2210,plain,
    ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2205])).

cnf(c_2212,plain,
    ( r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) ),
    inference(instantiation,[status(thm)],[c_2210])).

cnf(c_989,plain,
    ( X0 != X1
    | k6_partfun1(X0) = k6_partfun1(X1) ),
    theory(equality)).

cnf(c_1001,plain,
    ( k6_partfun1(sK1) = k6_partfun1(sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_989])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_17995,c_9787,c_8581,c_8429,c_2843,c_2501,c_2212,c_1902,c_1781,c_1001,c_121,c_118,c_117,c_115,c_31,c_32,c_33,c_34])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:22:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.37/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.37/1.49  
% 7.37/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.37/1.49  
% 7.37/1.49  ------  iProver source info
% 7.37/1.49  
% 7.37/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.37/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.37/1.49  git: non_committed_changes: false
% 7.37/1.49  git: last_make_outside_of_git: false
% 7.37/1.49  
% 7.37/1.49  ------ 
% 7.37/1.49  
% 7.37/1.49  ------ Input Options
% 7.37/1.49  
% 7.37/1.49  --out_options                           all
% 7.37/1.49  --tptp_safe_out                         true
% 7.37/1.49  --problem_path                          ""
% 7.37/1.49  --include_path                          ""
% 7.37/1.49  --clausifier                            res/vclausify_rel
% 7.37/1.49  --clausifier_options                    ""
% 7.37/1.49  --stdin                                 false
% 7.37/1.49  --stats_out                             all
% 7.37/1.49  
% 7.37/1.49  ------ General Options
% 7.37/1.49  
% 7.37/1.49  --fof                                   false
% 7.37/1.49  --time_out_real                         305.
% 7.37/1.49  --time_out_virtual                      -1.
% 7.37/1.49  --symbol_type_check                     false
% 7.37/1.49  --clausify_out                          false
% 7.37/1.49  --sig_cnt_out                           false
% 7.37/1.49  --trig_cnt_out                          false
% 7.37/1.49  --trig_cnt_out_tolerance                1.
% 7.37/1.49  --trig_cnt_out_sk_spl                   false
% 7.37/1.49  --abstr_cl_out                          false
% 7.37/1.49  
% 7.37/1.49  ------ Global Options
% 7.37/1.49  
% 7.37/1.49  --schedule                              default
% 7.37/1.49  --add_important_lit                     false
% 7.37/1.49  --prop_solver_per_cl                    1000
% 7.37/1.49  --min_unsat_core                        false
% 7.37/1.49  --soft_assumptions                      false
% 7.37/1.49  --soft_lemma_size                       3
% 7.37/1.49  --prop_impl_unit_size                   0
% 7.37/1.49  --prop_impl_unit                        []
% 7.37/1.49  --share_sel_clauses                     true
% 7.37/1.49  --reset_solvers                         false
% 7.37/1.49  --bc_imp_inh                            [conj_cone]
% 7.37/1.49  --conj_cone_tolerance                   3.
% 7.37/1.49  --extra_neg_conj                        none
% 7.37/1.49  --large_theory_mode                     true
% 7.37/1.49  --prolific_symb_bound                   200
% 7.37/1.49  --lt_threshold                          2000
% 7.37/1.49  --clause_weak_htbl                      true
% 7.37/1.49  --gc_record_bc_elim                     false
% 7.37/1.49  
% 7.37/1.49  ------ Preprocessing Options
% 7.37/1.49  
% 7.37/1.49  --preprocessing_flag                    true
% 7.37/1.49  --time_out_prep_mult                    0.1
% 7.37/1.49  --splitting_mode                        input
% 7.37/1.49  --splitting_grd                         true
% 7.37/1.49  --splitting_cvd                         false
% 7.37/1.49  --splitting_cvd_svl                     false
% 7.37/1.49  --splitting_nvd                         32
% 7.37/1.49  --sub_typing                            true
% 7.37/1.49  --prep_gs_sim                           true
% 7.37/1.49  --prep_unflatten                        true
% 7.37/1.49  --prep_res_sim                          true
% 7.37/1.49  --prep_upred                            true
% 7.37/1.49  --prep_sem_filter                       exhaustive
% 7.37/1.49  --prep_sem_filter_out                   false
% 7.37/1.49  --pred_elim                             true
% 7.37/1.49  --res_sim_input                         true
% 7.37/1.49  --eq_ax_congr_red                       true
% 7.37/1.49  --pure_diseq_elim                       true
% 7.37/1.49  --brand_transform                       false
% 7.37/1.49  --non_eq_to_eq                          false
% 7.37/1.49  --prep_def_merge                        true
% 7.37/1.49  --prep_def_merge_prop_impl              false
% 7.37/1.49  --prep_def_merge_mbd                    true
% 7.37/1.49  --prep_def_merge_tr_red                 false
% 7.37/1.49  --prep_def_merge_tr_cl                  false
% 7.37/1.49  --smt_preprocessing                     true
% 7.37/1.49  --smt_ac_axioms                         fast
% 7.37/1.49  --preprocessed_out                      false
% 7.37/1.49  --preprocessed_stats                    false
% 7.37/1.49  
% 7.37/1.49  ------ Abstraction refinement Options
% 7.37/1.49  
% 7.37/1.49  --abstr_ref                             []
% 7.37/1.49  --abstr_ref_prep                        false
% 7.37/1.49  --abstr_ref_until_sat                   false
% 7.37/1.49  --abstr_ref_sig_restrict                funpre
% 7.37/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.37/1.49  --abstr_ref_under                       []
% 7.37/1.49  
% 7.37/1.49  ------ SAT Options
% 7.37/1.49  
% 7.37/1.49  --sat_mode                              false
% 7.37/1.49  --sat_fm_restart_options                ""
% 7.37/1.49  --sat_gr_def                            false
% 7.37/1.49  --sat_epr_types                         true
% 7.37/1.49  --sat_non_cyclic_types                  false
% 7.37/1.49  --sat_finite_models                     false
% 7.37/1.49  --sat_fm_lemmas                         false
% 7.37/1.49  --sat_fm_prep                           false
% 7.37/1.49  --sat_fm_uc_incr                        true
% 7.37/1.49  --sat_out_model                         small
% 7.37/1.49  --sat_out_clauses                       false
% 7.37/1.49  
% 7.37/1.49  ------ QBF Options
% 7.37/1.49  
% 7.37/1.49  --qbf_mode                              false
% 7.37/1.49  --qbf_elim_univ                         false
% 7.37/1.49  --qbf_dom_inst                          none
% 7.37/1.49  --qbf_dom_pre_inst                      false
% 7.37/1.49  --qbf_sk_in                             false
% 7.37/1.49  --qbf_pred_elim                         true
% 7.37/1.49  --qbf_split                             512
% 7.37/1.49  
% 7.37/1.49  ------ BMC1 Options
% 7.37/1.49  
% 7.37/1.49  --bmc1_incremental                      false
% 7.37/1.49  --bmc1_axioms                           reachable_all
% 7.37/1.49  --bmc1_min_bound                        0
% 7.37/1.49  --bmc1_max_bound                        -1
% 7.37/1.49  --bmc1_max_bound_default                -1
% 7.37/1.49  --bmc1_symbol_reachability              true
% 7.37/1.49  --bmc1_property_lemmas                  false
% 7.37/1.49  --bmc1_k_induction                      false
% 7.37/1.49  --bmc1_non_equiv_states                 false
% 7.37/1.49  --bmc1_deadlock                         false
% 7.37/1.49  --bmc1_ucm                              false
% 7.37/1.49  --bmc1_add_unsat_core                   none
% 7.37/1.49  --bmc1_unsat_core_children              false
% 7.37/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.37/1.49  --bmc1_out_stat                         full
% 7.37/1.49  --bmc1_ground_init                      false
% 7.37/1.49  --bmc1_pre_inst_next_state              false
% 7.37/1.49  --bmc1_pre_inst_state                   false
% 7.37/1.49  --bmc1_pre_inst_reach_state             false
% 7.37/1.49  --bmc1_out_unsat_core                   false
% 7.37/1.49  --bmc1_aig_witness_out                  false
% 7.37/1.49  --bmc1_verbose                          false
% 7.37/1.49  --bmc1_dump_clauses_tptp                false
% 7.37/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.37/1.49  --bmc1_dump_file                        -
% 7.37/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.37/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.37/1.49  --bmc1_ucm_extend_mode                  1
% 7.37/1.49  --bmc1_ucm_init_mode                    2
% 7.37/1.49  --bmc1_ucm_cone_mode                    none
% 7.37/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.37/1.49  --bmc1_ucm_relax_model                  4
% 7.37/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.37/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.37/1.49  --bmc1_ucm_layered_model                none
% 7.37/1.49  --bmc1_ucm_max_lemma_size               10
% 7.37/1.49  
% 7.37/1.49  ------ AIG Options
% 7.37/1.49  
% 7.37/1.49  --aig_mode                              false
% 7.37/1.49  
% 7.37/1.49  ------ Instantiation Options
% 7.37/1.49  
% 7.37/1.49  --instantiation_flag                    true
% 7.37/1.49  --inst_sos_flag                         true
% 7.37/1.49  --inst_sos_phase                        true
% 7.37/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.37/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.37/1.49  --inst_lit_sel_side                     num_symb
% 7.37/1.49  --inst_solver_per_active                1400
% 7.37/1.49  --inst_solver_calls_frac                1.
% 7.37/1.49  --inst_passive_queue_type               priority_queues
% 7.37/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.37/1.49  --inst_passive_queues_freq              [25;2]
% 7.37/1.49  --inst_dismatching                      true
% 7.37/1.49  --inst_eager_unprocessed_to_passive     true
% 7.37/1.49  --inst_prop_sim_given                   true
% 7.37/1.49  --inst_prop_sim_new                     false
% 7.37/1.49  --inst_subs_new                         false
% 7.37/1.49  --inst_eq_res_simp                      false
% 7.37/1.49  --inst_subs_given                       false
% 7.37/1.49  --inst_orphan_elimination               true
% 7.37/1.49  --inst_learning_loop_flag               true
% 7.37/1.49  --inst_learning_start                   3000
% 7.37/1.49  --inst_learning_factor                  2
% 7.37/1.49  --inst_start_prop_sim_after_learn       3
% 7.37/1.49  --inst_sel_renew                        solver
% 7.37/1.49  --inst_lit_activity_flag                true
% 7.37/1.49  --inst_restr_to_given                   false
% 7.37/1.49  --inst_activity_threshold               500
% 7.37/1.49  --inst_out_proof                        true
% 7.37/1.49  
% 7.37/1.49  ------ Resolution Options
% 7.37/1.49  
% 7.37/1.49  --resolution_flag                       true
% 7.37/1.49  --res_lit_sel                           adaptive
% 7.37/1.49  --res_lit_sel_side                      none
% 7.37/1.49  --res_ordering                          kbo
% 7.37/1.49  --res_to_prop_solver                    active
% 7.37/1.49  --res_prop_simpl_new                    false
% 7.37/1.49  --res_prop_simpl_given                  true
% 7.37/1.49  --res_passive_queue_type                priority_queues
% 7.37/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.37/1.49  --res_passive_queues_freq               [15;5]
% 7.37/1.49  --res_forward_subs                      full
% 7.37/1.49  --res_backward_subs                     full
% 7.37/1.49  --res_forward_subs_resolution           true
% 7.37/1.49  --res_backward_subs_resolution          true
% 7.37/1.49  --res_orphan_elimination                true
% 7.37/1.49  --res_time_limit                        2.
% 7.37/1.49  --res_out_proof                         true
% 7.37/1.49  
% 7.37/1.49  ------ Superposition Options
% 7.37/1.49  
% 7.37/1.49  --superposition_flag                    true
% 7.37/1.49  --sup_passive_queue_type                priority_queues
% 7.37/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.37/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.37/1.49  --demod_completeness_check              fast
% 7.37/1.49  --demod_use_ground                      true
% 7.37/1.49  --sup_to_prop_solver                    passive
% 7.37/1.49  --sup_prop_simpl_new                    true
% 7.37/1.49  --sup_prop_simpl_given                  true
% 7.37/1.49  --sup_fun_splitting                     true
% 7.37/1.49  --sup_smt_interval                      50000
% 7.74/1.49  
% 7.74/1.49  ------ Superposition Simplification Setup
% 7.74/1.49  
% 7.74/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.74/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.74/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.74/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.74/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.74/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.74/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.74/1.49  --sup_immed_triv                        [TrivRules]
% 7.74/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.74/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.74/1.49  --sup_immed_bw_main                     []
% 7.74/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.74/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.74/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.74/1.49  --sup_input_bw                          []
% 7.74/1.49  
% 7.74/1.49  ------ Combination Options
% 7.74/1.49  
% 7.74/1.49  --comb_res_mult                         3
% 7.74/1.49  --comb_sup_mult                         2
% 7.74/1.49  --comb_inst_mult                        10
% 7.74/1.49  
% 7.74/1.49  ------ Debug Options
% 7.74/1.49  
% 7.74/1.49  --dbg_backtrace                         false
% 7.74/1.49  --dbg_dump_prop_clauses                 false
% 7.74/1.49  --dbg_dump_prop_clauses_file            -
% 7.74/1.49  --dbg_out_stat                          false
% 7.74/1.49  ------ Parsing...
% 7.74/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.74/1.49  
% 7.74/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 7.74/1.49  
% 7.74/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.74/1.49  
% 7.74/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.74/1.49  ------ Proving...
% 7.74/1.49  ------ Problem Properties 
% 7.74/1.49  
% 7.74/1.49  
% 7.74/1.49  clauses                                 27
% 7.74/1.49  conjectures                             5
% 7.74/1.49  EPR                                     5
% 7.74/1.49  Horn                                    25
% 7.74/1.49  unary                                   6
% 7.74/1.49  binary                                  5
% 7.74/1.49  lits                                    94
% 7.74/1.49  lits eq                                 13
% 7.74/1.49  fd_pure                                 0
% 7.74/1.49  fd_pseudo                               0
% 7.74/1.49  fd_cond                                 2
% 7.74/1.49  fd_pseudo_cond                          3
% 7.74/1.49  AC symbols                              0
% 7.74/1.49  
% 7.74/1.49  ------ Schedule dynamic 5 is on 
% 7.74/1.49  
% 7.74/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.74/1.49  
% 7.74/1.49  
% 7.74/1.49  ------ 
% 7.74/1.49  Current options:
% 7.74/1.49  ------ 
% 7.74/1.49  
% 7.74/1.49  ------ Input Options
% 7.74/1.49  
% 7.74/1.49  --out_options                           all
% 7.74/1.49  --tptp_safe_out                         true
% 7.74/1.49  --problem_path                          ""
% 7.74/1.49  --include_path                          ""
% 7.74/1.49  --clausifier                            res/vclausify_rel
% 7.74/1.49  --clausifier_options                    ""
% 7.74/1.49  --stdin                                 false
% 7.74/1.49  --stats_out                             all
% 7.74/1.49  
% 7.74/1.49  ------ General Options
% 7.74/1.49  
% 7.74/1.49  --fof                                   false
% 7.74/1.49  --time_out_real                         305.
% 7.74/1.49  --time_out_virtual                      -1.
% 7.74/1.49  --symbol_type_check                     false
% 7.74/1.49  --clausify_out                          false
% 7.74/1.49  --sig_cnt_out                           false
% 7.74/1.49  --trig_cnt_out                          false
% 7.74/1.49  --trig_cnt_out_tolerance                1.
% 7.74/1.49  --trig_cnt_out_sk_spl                   false
% 7.74/1.49  --abstr_cl_out                          false
% 7.74/1.49  
% 7.74/1.49  ------ Global Options
% 7.74/1.49  
% 7.74/1.49  --schedule                              default
% 7.74/1.49  --add_important_lit                     false
% 7.74/1.49  --prop_solver_per_cl                    1000
% 7.74/1.49  --min_unsat_core                        false
% 7.74/1.49  --soft_assumptions                      false
% 7.74/1.49  --soft_lemma_size                       3
% 7.74/1.49  --prop_impl_unit_size                   0
% 7.74/1.49  --prop_impl_unit                        []
% 7.74/1.49  --share_sel_clauses                     true
% 7.74/1.49  --reset_solvers                         false
% 7.74/1.49  --bc_imp_inh                            [conj_cone]
% 7.74/1.49  --conj_cone_tolerance                   3.
% 7.74/1.49  --extra_neg_conj                        none
% 7.74/1.49  --large_theory_mode                     true
% 7.74/1.49  --prolific_symb_bound                   200
% 7.74/1.49  --lt_threshold                          2000
% 7.74/1.49  --clause_weak_htbl                      true
% 7.74/1.49  --gc_record_bc_elim                     false
% 7.74/1.49  
% 7.74/1.49  ------ Preprocessing Options
% 7.74/1.49  
% 7.74/1.49  --preprocessing_flag                    true
% 7.74/1.49  --time_out_prep_mult                    0.1
% 7.74/1.49  --splitting_mode                        input
% 7.74/1.49  --splitting_grd                         true
% 7.74/1.49  --splitting_cvd                         false
% 7.74/1.49  --splitting_cvd_svl                     false
% 7.74/1.49  --splitting_nvd                         32
% 7.74/1.49  --sub_typing                            true
% 7.74/1.49  --prep_gs_sim                           true
% 7.74/1.49  --prep_unflatten                        true
% 7.74/1.49  --prep_res_sim                          true
% 7.74/1.49  --prep_upred                            true
% 7.74/1.49  --prep_sem_filter                       exhaustive
% 7.74/1.49  --prep_sem_filter_out                   false
% 7.74/1.49  --pred_elim                             true
% 7.74/1.49  --res_sim_input                         true
% 7.74/1.49  --eq_ax_congr_red                       true
% 7.74/1.49  --pure_diseq_elim                       true
% 7.74/1.49  --brand_transform                       false
% 7.74/1.49  --non_eq_to_eq                          false
% 7.74/1.49  --prep_def_merge                        true
% 7.74/1.49  --prep_def_merge_prop_impl              false
% 7.74/1.49  --prep_def_merge_mbd                    true
% 7.74/1.49  --prep_def_merge_tr_red                 false
% 7.74/1.49  --prep_def_merge_tr_cl                  false
% 7.74/1.49  --smt_preprocessing                     true
% 7.74/1.49  --smt_ac_axioms                         fast
% 7.74/1.49  --preprocessed_out                      false
% 7.74/1.49  --preprocessed_stats                    false
% 7.74/1.49  
% 7.74/1.49  ------ Abstraction refinement Options
% 7.74/1.49  
% 7.74/1.49  --abstr_ref                             []
% 7.74/1.49  --abstr_ref_prep                        false
% 7.74/1.49  --abstr_ref_until_sat                   false
% 7.74/1.49  --abstr_ref_sig_restrict                funpre
% 7.74/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.74/1.49  --abstr_ref_under                       []
% 7.74/1.49  
% 7.74/1.49  ------ SAT Options
% 7.74/1.49  
% 7.74/1.49  --sat_mode                              false
% 7.74/1.49  --sat_fm_restart_options                ""
% 7.74/1.49  --sat_gr_def                            false
% 7.74/1.49  --sat_epr_types                         true
% 7.74/1.49  --sat_non_cyclic_types                  false
% 7.74/1.49  --sat_finite_models                     false
% 7.74/1.49  --sat_fm_lemmas                         false
% 7.74/1.49  --sat_fm_prep                           false
% 7.74/1.49  --sat_fm_uc_incr                        true
% 7.74/1.49  --sat_out_model                         small
% 7.74/1.49  --sat_out_clauses                       false
% 7.74/1.49  
% 7.74/1.49  ------ QBF Options
% 7.74/1.49  
% 7.74/1.49  --qbf_mode                              false
% 7.74/1.49  --qbf_elim_univ                         false
% 7.74/1.49  --qbf_dom_inst                          none
% 7.74/1.49  --qbf_dom_pre_inst                      false
% 7.74/1.49  --qbf_sk_in                             false
% 7.74/1.49  --qbf_pred_elim                         true
% 7.74/1.49  --qbf_split                             512
% 7.74/1.49  
% 7.74/1.49  ------ BMC1 Options
% 7.74/1.49  
% 7.74/1.49  --bmc1_incremental                      false
% 7.74/1.49  --bmc1_axioms                           reachable_all
% 7.74/1.49  --bmc1_min_bound                        0
% 7.74/1.49  --bmc1_max_bound                        -1
% 7.74/1.49  --bmc1_max_bound_default                -1
% 7.74/1.49  --bmc1_symbol_reachability              true
% 7.74/1.49  --bmc1_property_lemmas                  false
% 7.74/1.49  --bmc1_k_induction                      false
% 7.74/1.49  --bmc1_non_equiv_states                 false
% 7.74/1.49  --bmc1_deadlock                         false
% 7.74/1.49  --bmc1_ucm                              false
% 7.74/1.49  --bmc1_add_unsat_core                   none
% 7.74/1.49  --bmc1_unsat_core_children              false
% 7.74/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.74/1.49  --bmc1_out_stat                         full
% 7.74/1.49  --bmc1_ground_init                      false
% 7.74/1.49  --bmc1_pre_inst_next_state              false
% 7.74/1.49  --bmc1_pre_inst_state                   false
% 7.74/1.49  --bmc1_pre_inst_reach_state             false
% 7.74/1.49  --bmc1_out_unsat_core                   false
% 7.74/1.49  --bmc1_aig_witness_out                  false
% 7.74/1.49  --bmc1_verbose                          false
% 7.74/1.49  --bmc1_dump_clauses_tptp                false
% 7.74/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.74/1.49  --bmc1_dump_file                        -
% 7.74/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.74/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.74/1.49  --bmc1_ucm_extend_mode                  1
% 7.74/1.49  --bmc1_ucm_init_mode                    2
% 7.74/1.49  --bmc1_ucm_cone_mode                    none
% 7.74/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.74/1.49  --bmc1_ucm_relax_model                  4
% 7.74/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.74/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.74/1.49  --bmc1_ucm_layered_model                none
% 7.74/1.49  --bmc1_ucm_max_lemma_size               10
% 7.74/1.49  
% 7.74/1.49  ------ AIG Options
% 7.74/1.49  
% 7.74/1.49  --aig_mode                              false
% 7.74/1.49  
% 7.74/1.49  ------ Instantiation Options
% 7.74/1.49  
% 7.74/1.49  --instantiation_flag                    true
% 7.74/1.49  --inst_sos_flag                         true
% 7.74/1.49  --inst_sos_phase                        true
% 7.74/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.74/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.74/1.49  --inst_lit_sel_side                     none
% 7.74/1.49  --inst_solver_per_active                1400
% 7.74/1.49  --inst_solver_calls_frac                1.
% 7.74/1.49  --inst_passive_queue_type               priority_queues
% 7.74/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.74/1.49  --inst_passive_queues_freq              [25;2]
% 7.74/1.49  --inst_dismatching                      true
% 7.74/1.49  --inst_eager_unprocessed_to_passive     true
% 7.74/1.49  --inst_prop_sim_given                   true
% 7.74/1.49  --inst_prop_sim_new                     false
% 7.74/1.49  --inst_subs_new                         false
% 7.74/1.49  --inst_eq_res_simp                      false
% 7.74/1.49  --inst_subs_given                       false
% 7.74/1.49  --inst_orphan_elimination               true
% 7.74/1.49  --inst_learning_loop_flag               true
% 7.74/1.49  --inst_learning_start                   3000
% 7.74/1.49  --inst_learning_factor                  2
% 7.74/1.49  --inst_start_prop_sim_after_learn       3
% 7.74/1.49  --inst_sel_renew                        solver
% 7.74/1.49  --inst_lit_activity_flag                true
% 7.74/1.49  --inst_restr_to_given                   false
% 7.74/1.49  --inst_activity_threshold               500
% 7.74/1.49  --inst_out_proof                        true
% 7.74/1.49  
% 7.74/1.49  ------ Resolution Options
% 7.74/1.49  
% 7.74/1.49  --resolution_flag                       false
% 7.74/1.49  --res_lit_sel                           adaptive
% 7.74/1.49  --res_lit_sel_side                      none
% 7.74/1.49  --res_ordering                          kbo
% 7.74/1.49  --res_to_prop_solver                    active
% 7.74/1.49  --res_prop_simpl_new                    false
% 7.74/1.49  --res_prop_simpl_given                  true
% 7.74/1.49  --res_passive_queue_type                priority_queues
% 7.74/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.74/1.49  --res_passive_queues_freq               [15;5]
% 7.74/1.49  --res_forward_subs                      full
% 7.74/1.49  --res_backward_subs                     full
% 7.74/1.49  --res_forward_subs_resolution           true
% 7.74/1.49  --res_backward_subs_resolution          true
% 7.74/1.49  --res_orphan_elimination                true
% 7.74/1.49  --res_time_limit                        2.
% 7.74/1.49  --res_out_proof                         true
% 7.74/1.49  
% 7.74/1.49  ------ Superposition Options
% 7.74/1.49  
% 7.74/1.49  --superposition_flag                    true
% 7.74/1.49  --sup_passive_queue_type                priority_queues
% 7.74/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.74/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.74/1.49  --demod_completeness_check              fast
% 7.74/1.49  --demod_use_ground                      true
% 7.74/1.49  --sup_to_prop_solver                    passive
% 7.74/1.49  --sup_prop_simpl_new                    true
% 7.74/1.49  --sup_prop_simpl_given                  true
% 7.74/1.49  --sup_fun_splitting                     true
% 7.74/1.49  --sup_smt_interval                      50000
% 7.74/1.49  
% 7.74/1.49  ------ Superposition Simplification Setup
% 7.74/1.49  
% 7.74/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.74/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.74/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.74/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.74/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.74/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.74/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.74/1.49  --sup_immed_triv                        [TrivRules]
% 7.74/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.74/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.74/1.49  --sup_immed_bw_main                     []
% 7.74/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.74/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.74/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.74/1.49  --sup_input_bw                          []
% 7.74/1.49  
% 7.74/1.49  ------ Combination Options
% 7.74/1.49  
% 7.74/1.49  --comb_res_mult                         3
% 7.74/1.49  --comb_sup_mult                         2
% 7.74/1.49  --comb_inst_mult                        10
% 7.74/1.49  
% 7.74/1.49  ------ Debug Options
% 7.74/1.49  
% 7.74/1.49  --dbg_backtrace                         false
% 7.74/1.49  --dbg_dump_prop_clauses                 false
% 7.74/1.49  --dbg_dump_prop_clauses_file            -
% 7.74/1.49  --dbg_out_stat                          false
% 7.74/1.49  
% 7.74/1.49  
% 7.74/1.49  
% 7.74/1.49  
% 7.74/1.49  ------ Proving...
% 7.74/1.49  
% 7.74/1.49  
% 7.74/1.49  % SZS status Theorem for theBenchmark.p
% 7.74/1.49  
% 7.74/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.74/1.49  
% 7.74/1.49  fof(f19,conjecture,(
% 7.74/1.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 7.74/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.49  
% 7.74/1.49  fof(f20,negated_conjecture,(
% 7.74/1.49    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 7.74/1.49    inference(negated_conjecture,[],[f19])).
% 7.74/1.49  
% 7.74/1.49  fof(f44,plain,(
% 7.74/1.49    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 7.74/1.49    inference(ennf_transformation,[],[f20])).
% 7.74/1.49  
% 7.74/1.49  fof(f45,plain,(
% 7.74/1.49    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 7.74/1.49    inference(flattening,[],[f44])).
% 7.74/1.49  
% 7.74/1.49  fof(f53,plain,(
% 7.74/1.49    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) | ~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v3_funct_2(sK2,sK1,sK1) & v1_funct_2(sK2,sK1,sK1) & v1_funct_1(sK2))),
% 7.74/1.49    introduced(choice_axiom,[])).
% 7.74/1.49  
% 7.74/1.49  fof(f54,plain,(
% 7.74/1.49    (~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) | ~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v3_funct_2(sK2,sK1,sK1) & v1_funct_2(sK2,sK1,sK1) & v1_funct_1(sK2)),
% 7.74/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f45,f53])).
% 7.74/1.49  
% 7.74/1.49  fof(f89,plain,(
% 7.74/1.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))),
% 7.74/1.49    inference(cnf_transformation,[],[f54])).
% 7.74/1.49  
% 7.74/1.49  fof(f16,axiom,(
% 7.74/1.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_2(X0,X1) = k2_funct_1(X1))),
% 7.74/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.49  
% 7.74/1.49  fof(f40,plain,(
% 7.74/1.49    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 7.74/1.49    inference(ennf_transformation,[],[f16])).
% 7.74/1.49  
% 7.74/1.49  fof(f41,plain,(
% 7.74/1.49    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 7.74/1.49    inference(flattening,[],[f40])).
% 7.74/1.49  
% 7.74/1.49  fof(f82,plain,(
% 7.74/1.49    ( ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 7.74/1.49    inference(cnf_transformation,[],[f41])).
% 7.74/1.49  
% 7.74/1.49  fof(f86,plain,(
% 7.74/1.49    v1_funct_1(sK2)),
% 7.74/1.49    inference(cnf_transformation,[],[f54])).
% 7.74/1.49  
% 7.74/1.49  fof(f87,plain,(
% 7.74/1.49    v1_funct_2(sK2,sK1,sK1)),
% 7.74/1.49    inference(cnf_transformation,[],[f54])).
% 7.74/1.49  
% 7.74/1.49  fof(f88,plain,(
% 7.74/1.49    v3_funct_2(sK2,sK1,sK1)),
% 7.74/1.49    inference(cnf_transformation,[],[f54])).
% 7.74/1.49  
% 7.74/1.49  fof(f14,axiom,(
% 7.74/1.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 7.74/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.49  
% 7.74/1.49  fof(f36,plain,(
% 7.74/1.49    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 7.74/1.49    inference(ennf_transformation,[],[f14])).
% 7.74/1.49  
% 7.74/1.49  fof(f37,plain,(
% 7.74/1.49    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 7.74/1.49    inference(flattening,[],[f36])).
% 7.74/1.49  
% 7.74/1.49  fof(f80,plain,(
% 7.74/1.49    ( ! [X0,X1] : (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 7.74/1.49    inference(cnf_transformation,[],[f37])).
% 7.74/1.49  
% 7.74/1.49  fof(f15,axiom,(
% 7.74/1.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 7.74/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.49  
% 7.74/1.49  fof(f38,plain,(
% 7.74/1.49    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 7.74/1.49    inference(ennf_transformation,[],[f15])).
% 7.74/1.49  
% 7.74/1.49  fof(f39,plain,(
% 7.74/1.49    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 7.74/1.49    inference(flattening,[],[f38])).
% 7.74/1.49  
% 7.74/1.49  fof(f81,plain,(
% 7.74/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 7.74/1.49    inference(cnf_transformation,[],[f39])).
% 7.74/1.49  
% 7.74/1.49  fof(f77,plain,(
% 7.74/1.49    ( ! [X0,X1] : (v1_funct_1(k2_funct_2(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 7.74/1.49    inference(cnf_transformation,[],[f37])).
% 7.74/1.49  
% 7.74/1.49  fof(f13,axiom,(
% 7.74/1.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 7.74/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.49  
% 7.74/1.49  fof(f34,plain,(
% 7.74/1.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 7.74/1.49    inference(ennf_transformation,[],[f13])).
% 7.74/1.49  
% 7.74/1.49  fof(f35,plain,(
% 7.74/1.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 7.74/1.49    inference(flattening,[],[f34])).
% 7.74/1.49  
% 7.74/1.49  fof(f76,plain,(
% 7.74/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 7.74/1.49    inference(cnf_transformation,[],[f35])).
% 7.74/1.49  
% 7.74/1.49  fof(f9,axiom,(
% 7.74/1.49    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 7.74/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.49  
% 7.74/1.49  fof(f67,plain,(
% 7.74/1.49    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 7.74/1.49    inference(cnf_transformation,[],[f9])).
% 7.74/1.49  
% 7.74/1.49  fof(f17,axiom,(
% 7.74/1.49    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 7.74/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.49  
% 7.74/1.49  fof(f83,plain,(
% 7.74/1.49    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 7.74/1.49    inference(cnf_transformation,[],[f17])).
% 7.74/1.49  
% 7.74/1.49  fof(f91,plain,(
% 7.74/1.49    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 7.74/1.49    inference(definition_unfolding,[],[f67,f83])).
% 7.74/1.49  
% 7.74/1.49  fof(f8,axiom,(
% 7.74/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 7.74/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.49  
% 7.74/1.49  fof(f26,plain,(
% 7.74/1.49    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 7.74/1.49    inference(ennf_transformation,[],[f8])).
% 7.74/1.49  
% 7.74/1.49  fof(f27,plain,(
% 7.74/1.49    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.74/1.49    inference(flattening,[],[f26])).
% 7.74/1.49  
% 7.74/1.49  fof(f49,plain,(
% 7.74/1.49    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.74/1.49    inference(nnf_transformation,[],[f27])).
% 7.74/1.49  
% 7.74/1.49  fof(f65,plain,(
% 7.74/1.49    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.74/1.49    inference(cnf_transformation,[],[f49])).
% 7.74/1.49  
% 7.74/1.49  fof(f3,axiom,(
% 7.74/1.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.74/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.49  
% 7.74/1.49  fof(f48,plain,(
% 7.74/1.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.74/1.49    inference(nnf_transformation,[],[f3])).
% 7.74/1.49  
% 7.74/1.49  fof(f60,plain,(
% 7.74/1.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.74/1.49    inference(cnf_transformation,[],[f48])).
% 7.74/1.49  
% 7.74/1.49  fof(f2,axiom,(
% 7.74/1.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.74/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.49  
% 7.74/1.49  fof(f46,plain,(
% 7.74/1.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.74/1.49    inference(nnf_transformation,[],[f2])).
% 7.74/1.49  
% 7.74/1.49  fof(f47,plain,(
% 7.74/1.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.74/1.49    inference(flattening,[],[f46])).
% 7.74/1.49  
% 7.74/1.49  fof(f56,plain,(
% 7.74/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.74/1.49    inference(cnf_transformation,[],[f47])).
% 7.74/1.49  
% 7.74/1.49  fof(f93,plain,(
% 7.74/1.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.74/1.49    inference(equality_resolution,[],[f56])).
% 7.74/1.49  
% 7.74/1.49  fof(f58,plain,(
% 7.74/1.49    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.74/1.49    inference(cnf_transformation,[],[f47])).
% 7.74/1.49  
% 7.74/1.49  fof(f11,axiom,(
% 7.74/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 7.74/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.49  
% 7.74/1.49  fof(f30,plain,(
% 7.74/1.49    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.74/1.49    inference(ennf_transformation,[],[f11])).
% 7.74/1.49  
% 7.74/1.49  fof(f31,plain,(
% 7.74/1.49    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.74/1.49    inference(flattening,[],[f30])).
% 7.74/1.49  
% 7.74/1.49  fof(f72,plain,(
% 7.74/1.49    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.74/1.49    inference(cnf_transformation,[],[f31])).
% 7.74/1.49  
% 7.74/1.49  fof(f6,axiom,(
% 7.74/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.74/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.49  
% 7.74/1.49  fof(f21,plain,(
% 7.74/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 7.74/1.49    inference(pure_predicate_removal,[],[f6])).
% 7.74/1.49  
% 7.74/1.49  fof(f24,plain,(
% 7.74/1.49    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.74/1.49    inference(ennf_transformation,[],[f21])).
% 7.74/1.49  
% 7.74/1.49  fof(f63,plain,(
% 7.74/1.49    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.74/1.49    inference(cnf_transformation,[],[f24])).
% 7.74/1.49  
% 7.74/1.49  fof(f12,axiom,(
% 7.74/1.49    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 7.74/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.49  
% 7.74/1.49  fof(f32,plain,(
% 7.74/1.49    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 7.74/1.49    inference(ennf_transformation,[],[f12])).
% 7.74/1.49  
% 7.74/1.49  fof(f33,plain,(
% 7.74/1.49    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.74/1.49    inference(flattening,[],[f32])).
% 7.74/1.49  
% 7.74/1.49  fof(f52,plain,(
% 7.74/1.49    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.74/1.49    inference(nnf_transformation,[],[f33])).
% 7.74/1.49  
% 7.74/1.49  fof(f73,plain,(
% 7.74/1.49    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.74/1.49    inference(cnf_transformation,[],[f52])).
% 7.74/1.49  
% 7.74/1.49  fof(f5,axiom,(
% 7.74/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.74/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.49  
% 7.74/1.49  fof(f23,plain,(
% 7.74/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.74/1.49    inference(ennf_transformation,[],[f5])).
% 7.74/1.49  
% 7.74/1.49  fof(f62,plain,(
% 7.74/1.49    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.74/1.49    inference(cnf_transformation,[],[f23])).
% 7.74/1.49  
% 7.74/1.49  fof(f7,axiom,(
% 7.74/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 7.74/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.49  
% 7.74/1.49  fof(f25,plain,(
% 7.74/1.49    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.74/1.49    inference(ennf_transformation,[],[f7])).
% 7.74/1.49  
% 7.74/1.49  fof(f64,plain,(
% 7.74/1.49    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.74/1.49    inference(cnf_transformation,[],[f25])).
% 7.74/1.49  
% 7.74/1.49  fof(f71,plain,(
% 7.74/1.49    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.74/1.49    inference(cnf_transformation,[],[f31])).
% 7.74/1.49  
% 7.74/1.49  fof(f18,axiom,(
% 7.74/1.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1)))),
% 7.74/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.49  
% 7.74/1.49  fof(f42,plain,(
% 7.74/1.49    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 7.74/1.49    inference(ennf_transformation,[],[f18])).
% 7.74/1.49  
% 7.74/1.49  fof(f43,plain,(
% 7.74/1.49    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.74/1.49    inference(flattening,[],[f42])).
% 7.74/1.49  
% 7.74/1.49  fof(f84,plain,(
% 7.74/1.49    ( ! [X2,X0,X1] : (k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.74/1.49    inference(cnf_transformation,[],[f43])).
% 7.74/1.49  
% 7.74/1.49  fof(f59,plain,(
% 7.74/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.74/1.49    inference(cnf_transformation,[],[f48])).
% 7.74/1.49  
% 7.74/1.49  fof(f1,axiom,(
% 7.74/1.49    v1_xboole_0(k1_xboole_0)),
% 7.74/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.49  
% 7.74/1.49  fof(f55,plain,(
% 7.74/1.49    v1_xboole_0(k1_xboole_0)),
% 7.74/1.49    inference(cnf_transformation,[],[f1])).
% 7.74/1.49  
% 7.74/1.49  fof(f4,axiom,(
% 7.74/1.49    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 7.74/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.49  
% 7.74/1.49  fof(f22,plain,(
% 7.74/1.49    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 7.74/1.49    inference(ennf_transformation,[],[f4])).
% 7.74/1.49  
% 7.74/1.49  fof(f61,plain,(
% 7.74/1.49    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 7.74/1.49    inference(cnf_transformation,[],[f22])).
% 7.74/1.49  
% 7.74/1.49  fof(f10,axiom,(
% 7.74/1.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => (! [X3] : (r2_hidden(X3,X0) => k11_relat_1(X1,X3) = k11_relat_1(X2,X3)) => r2_relset_1(X0,X0,X1,X2))))),
% 7.74/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.49  
% 7.74/1.49  fof(f28,plain,(
% 7.74/1.49    ! [X0,X1] : (! [X2] : ((r2_relset_1(X0,X0,X1,X2) | ? [X3] : (k11_relat_1(X1,X3) != k11_relat_1(X2,X3) & r2_hidden(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 7.74/1.49    inference(ennf_transformation,[],[f10])).
% 7.74/1.49  
% 7.74/1.49  fof(f29,plain,(
% 7.74/1.49    ! [X0,X1] : (! [X2] : (r2_relset_1(X0,X0,X1,X2) | ? [X3] : (k11_relat_1(X1,X3) != k11_relat_1(X2,X3) & r2_hidden(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 7.74/1.49    inference(flattening,[],[f28])).
% 7.74/1.49  
% 7.74/1.49  fof(f50,plain,(
% 7.74/1.49    ! [X2,X1,X0] : (? [X3] : (k11_relat_1(X1,X3) != k11_relat_1(X2,X3) & r2_hidden(X3,X0)) => (k11_relat_1(X1,sK0(X0,X1,X2)) != k11_relat_1(X2,sK0(X0,X1,X2)) & r2_hidden(sK0(X0,X1,X2),X0)))),
% 7.74/1.49    introduced(choice_axiom,[])).
% 7.74/1.49  
% 7.74/1.49  fof(f51,plain,(
% 7.74/1.49    ! [X0,X1] : (! [X2] : (r2_relset_1(X0,X0,X1,X2) | (k11_relat_1(X1,sK0(X0,X1,X2)) != k11_relat_1(X2,sK0(X0,X1,X2)) & r2_hidden(sK0(X0,X1,X2),X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 7.74/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f50])).
% 7.74/1.49  
% 7.74/1.49  fof(f68,plain,(
% 7.74/1.49    ( ! [X2,X0,X1] : (r2_relset_1(X0,X0,X1,X2) | r2_hidden(sK0(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 7.74/1.49    inference(cnf_transformation,[],[f51])).
% 7.74/1.49  
% 7.74/1.49  fof(f90,plain,(
% 7.74/1.49    ~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) | ~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1))),
% 7.74/1.49    inference(cnf_transformation,[],[f54])).
% 7.74/1.49  
% 7.74/1.49  fof(f85,plain,(
% 7.74/1.49    ( ! [X2,X0,X1] : (k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.74/1.49    inference(cnf_transformation,[],[f43])).
% 7.74/1.49  
% 7.74/1.49  fof(f66,plain,(
% 7.74/1.49    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.74/1.49    inference(cnf_transformation,[],[f49])).
% 7.74/1.49  
% 7.74/1.49  fof(f94,plain,(
% 7.74/1.49    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.74/1.49    inference(equality_resolution,[],[f66])).
% 7.74/1.49  
% 7.74/1.49  cnf(c_988,plain,
% 7.74/1.49      ( ~ r2_relset_1(X0,X1,X2,X3)
% 7.74/1.49      | r2_relset_1(X4,X5,X6,X7)
% 7.74/1.49      | X4 != X0
% 7.74/1.49      | X5 != X1
% 7.74/1.49      | X6 != X2
% 7.74/1.49      | X7 != X3 ),
% 7.74/1.49      theory(equality) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_1864,plain,
% 7.74/1.49      ( ~ r2_relset_1(X0,X1,X2,X3)
% 7.74/1.49      | r2_relset_1(X4,X5,X6,k6_partfun1(sK1))
% 7.74/1.49      | X4 != X0
% 7.74/1.49      | X5 != X1
% 7.74/1.49      | X6 != X2
% 7.74/1.49      | k6_partfun1(sK1) != X3 ),
% 7.74/1.49      inference(instantiation,[status(thm)],[c_988]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_2182,plain,
% 7.74/1.49      ( ~ r2_relset_1(X0,X1,X2,k6_partfun1(sK1))
% 7.74/1.49      | r2_relset_1(X3,X4,X5,k6_partfun1(sK1))
% 7.74/1.49      | X3 != X0
% 7.74/1.49      | X4 != X1
% 7.74/1.49      | X5 != X2
% 7.74/1.49      | k6_partfun1(sK1) != k6_partfun1(sK1) ),
% 7.74/1.49      inference(instantiation,[status(thm)],[c_1864]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_2798,plain,
% 7.74/1.49      ( r2_relset_1(X0,X1,X2,k6_partfun1(sK1))
% 7.74/1.49      | ~ r2_relset_1(X3,X4,k6_partfun1(sK1),k6_partfun1(sK1))
% 7.74/1.49      | X0 != X3
% 7.74/1.49      | X1 != X4
% 7.74/1.49      | X2 != k6_partfun1(sK1)
% 7.74/1.49      | k6_partfun1(sK1) != k6_partfun1(sK1) ),
% 7.74/1.49      inference(instantiation,[status(thm)],[c_2182]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_17993,plain,
% 7.74/1.49      ( r2_relset_1(X0,X1,k5_relat_1(k2_funct_1(sK2),sK2),k6_partfun1(sK1))
% 7.74/1.49      | ~ r2_relset_1(X2,X3,k6_partfun1(sK1),k6_partfun1(sK1))
% 7.74/1.49      | X0 != X2
% 7.74/1.49      | X1 != X3
% 7.74/1.49      | k5_relat_1(k2_funct_1(sK2),sK2) != k6_partfun1(sK1)
% 7.74/1.49      | k6_partfun1(sK1) != k6_partfun1(sK1) ),
% 7.74/1.49      inference(instantiation,[status(thm)],[c_2798]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_17995,plain,
% 7.74/1.49      ( r2_relset_1(sK1,sK1,k5_relat_1(k2_funct_1(sK2),sK2),k6_partfun1(sK1))
% 7.74/1.49      | ~ r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1))
% 7.74/1.49      | k5_relat_1(k2_funct_1(sK2),sK2) != k6_partfun1(sK1)
% 7.74/1.49      | k6_partfun1(sK1) != k6_partfun1(sK1)
% 7.74/1.49      | sK1 != sK1 ),
% 7.74/1.49      inference(instantiation,[status(thm)],[c_17993]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_31,negated_conjecture,
% 7.74/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 7.74/1.49      inference(cnf_transformation,[],[f89]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_1619,plain,
% 7.74/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 7.74/1.49      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_27,plain,
% 7.74/1.49      ( ~ v1_funct_2(X0,X1,X1)
% 7.74/1.49      | ~ v3_funct_2(X0,X1,X1)
% 7.74/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 7.74/1.49      | ~ v1_funct_1(X0)
% 7.74/1.49      | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
% 7.74/1.49      inference(cnf_transformation,[],[f82]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_1623,plain,
% 7.74/1.49      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
% 7.74/1.49      | v1_funct_2(X1,X0,X0) != iProver_top
% 7.74/1.49      | v3_funct_2(X1,X0,X0) != iProver_top
% 7.74/1.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 7.74/1.49      | v1_funct_1(X1) != iProver_top ),
% 7.74/1.49      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_2912,plain,
% 7.74/1.49      ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2)
% 7.74/1.49      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 7.74/1.49      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 7.74/1.49      | v1_funct_1(sK2) != iProver_top ),
% 7.74/1.49      inference(superposition,[status(thm)],[c_1619,c_1623]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_34,negated_conjecture,
% 7.74/1.49      ( v1_funct_1(sK2) ),
% 7.74/1.49      inference(cnf_transformation,[],[f86]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_35,plain,
% 7.74/1.49      ( v1_funct_1(sK2) = iProver_top ),
% 7.74/1.49      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_33,negated_conjecture,
% 7.74/1.49      ( v1_funct_2(sK2,sK1,sK1) ),
% 7.74/1.49      inference(cnf_transformation,[],[f87]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_36,plain,
% 7.74/1.49      ( v1_funct_2(sK2,sK1,sK1) = iProver_top ),
% 7.74/1.49      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_32,negated_conjecture,
% 7.74/1.49      ( v3_funct_2(sK2,sK1,sK1) ),
% 7.74/1.49      inference(cnf_transformation,[],[f88]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_37,plain,
% 7.74/1.49      ( v3_funct_2(sK2,sK1,sK1) = iProver_top ),
% 7.74/1.49      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_3080,plain,
% 7.74/1.49      ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
% 7.74/1.49      inference(global_propositional_subsumption,
% 7.74/1.49                [status(thm)],
% 7.74/1.49                [c_2912,c_35,c_36,c_37]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_22,plain,
% 7.74/1.49      ( ~ v1_funct_2(X0,X1,X1)
% 7.74/1.49      | ~ v3_funct_2(X0,X1,X1)
% 7.74/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 7.74/1.49      | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 7.74/1.49      | ~ v1_funct_1(X0) ),
% 7.74/1.49      inference(cnf_transformation,[],[f80]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_1628,plain,
% 7.74/1.49      ( v1_funct_2(X0,X1,X1) != iProver_top
% 7.74/1.49      | v3_funct_2(X0,X1,X1) != iProver_top
% 7.74/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
% 7.74/1.49      | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) = iProver_top
% 7.74/1.49      | v1_funct_1(X0) != iProver_top ),
% 7.74/1.49      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_3459,plain,
% 7.74/1.49      ( v1_funct_2(sK2,sK1,sK1) != iProver_top
% 7.74/1.49      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 7.74/1.49      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top
% 7.74/1.49      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 7.74/1.49      | v1_funct_1(sK2) != iProver_top ),
% 7.74/1.49      inference(superposition,[status(thm)],[c_3080,c_1628]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_38,plain,
% 7.74/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 7.74/1.49      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_3707,plain,
% 7.74/1.49      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 7.74/1.49      inference(global_propositional_subsumption,
% 7.74/1.49                [status(thm)],
% 7.74/1.49                [c_3459,c_35,c_36,c_37,c_38]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_26,plain,
% 7.74/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.74/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 7.74/1.49      | ~ v1_funct_1(X0)
% 7.74/1.49      | ~ v1_funct_1(X3)
% 7.74/1.49      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 7.74/1.49      inference(cnf_transformation,[],[f81]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_1624,plain,
% 7.74/1.49      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 7.74/1.49      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 7.74/1.49      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.74/1.49      | v1_funct_1(X5) != iProver_top
% 7.74/1.49      | v1_funct_1(X4) != iProver_top ),
% 7.74/1.49      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_4025,plain,
% 7.74/1.49      ( k1_partfun1(X0,X1,sK1,sK1,X2,k2_funct_1(sK2)) = k5_relat_1(X2,k2_funct_1(sK2))
% 7.74/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.74/1.49      | v1_funct_1(X2) != iProver_top
% 7.74/1.49      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 7.74/1.49      inference(superposition,[status(thm)],[c_3707,c_1624]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_25,plain,
% 7.74/1.49      ( ~ v1_funct_2(X0,X1,X1)
% 7.74/1.49      | ~ v3_funct_2(X0,X1,X1)
% 7.74/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 7.74/1.49      | ~ v1_funct_1(X0)
% 7.74/1.49      | v1_funct_1(k2_funct_2(X1,X0)) ),
% 7.74/1.49      inference(cnf_transformation,[],[f77]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_1625,plain,
% 7.74/1.49      ( v1_funct_2(X0,X1,X1) != iProver_top
% 7.74/1.49      | v3_funct_2(X0,X1,X1) != iProver_top
% 7.74/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
% 7.74/1.49      | v1_funct_1(X0) != iProver_top
% 7.74/1.49      | v1_funct_1(k2_funct_2(X1,X0)) = iProver_top ),
% 7.74/1.49      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_2923,plain,
% 7.74/1.49      ( v1_funct_2(sK2,sK1,sK1) != iProver_top
% 7.74/1.49      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 7.74/1.49      | v1_funct_1(k2_funct_2(sK1,sK2)) = iProver_top
% 7.74/1.49      | v1_funct_1(sK2) != iProver_top ),
% 7.74/1.49      inference(superposition,[status(thm)],[c_1619,c_1625]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_1737,plain,
% 7.74/1.49      ( ~ v1_funct_2(sK2,sK1,sK1)
% 7.74/1.49      | ~ v3_funct_2(sK2,sK1,sK1)
% 7.74/1.49      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 7.74/1.49      | v1_funct_1(k2_funct_2(sK1,sK2))
% 7.74/1.49      | ~ v1_funct_1(sK2) ),
% 7.74/1.49      inference(instantiation,[status(thm)],[c_25]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_1738,plain,
% 7.74/1.49      ( v1_funct_2(sK2,sK1,sK1) != iProver_top
% 7.74/1.49      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 7.74/1.49      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 7.74/1.49      | v1_funct_1(k2_funct_2(sK1,sK2)) = iProver_top
% 7.74/1.49      | v1_funct_1(sK2) != iProver_top ),
% 7.74/1.49      inference(predicate_to_equality,[status(thm)],[c_1737]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_3157,plain,
% 7.74/1.49      ( v1_funct_1(k2_funct_2(sK1,sK2)) = iProver_top ),
% 7.74/1.49      inference(global_propositional_subsumption,
% 7.74/1.49                [status(thm)],
% 7.74/1.49                [c_2923,c_35,c_36,c_37,c_38,c_1738]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_3161,plain,
% 7.74/1.49      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top ),
% 7.74/1.49      inference(light_normalisation,[status(thm)],[c_3157,c_3080]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_7565,plain,
% 7.74/1.49      ( v1_funct_1(X2) != iProver_top
% 7.74/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.74/1.49      | k1_partfun1(X0,X1,sK1,sK1,X2,k2_funct_1(sK2)) = k5_relat_1(X2,k2_funct_1(sK2)) ),
% 7.74/1.49      inference(global_propositional_subsumption,
% 7.74/1.49                [status(thm)],
% 7.74/1.49                [c_4025,c_3161]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_7566,plain,
% 7.74/1.49      ( k1_partfun1(X0,X1,sK1,sK1,X2,k2_funct_1(sK2)) = k5_relat_1(X2,k2_funct_1(sK2))
% 7.74/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.74/1.49      | v1_funct_1(X2) != iProver_top ),
% 7.74/1.49      inference(renaming,[status(thm)],[c_7565]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_7575,plain,
% 7.74/1.49      ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2))
% 7.74/1.49      | v1_funct_1(sK2) != iProver_top ),
% 7.74/1.49      inference(superposition,[status(thm)],[c_1619,c_7566]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_8349,plain,
% 7.74/1.49      ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
% 7.74/1.49      inference(global_propositional_subsumption,
% 7.74/1.49                [status(thm)],
% 7.74/1.49                [c_7575,c_35]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_20,plain,
% 7.74/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.74/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 7.74/1.49      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.74/1.49      | ~ v1_funct_1(X0)
% 7.74/1.49      | ~ v1_funct_1(X3) ),
% 7.74/1.49      inference(cnf_transformation,[],[f76]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_1630,plain,
% 7.74/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.74/1.49      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 7.74/1.49      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
% 7.74/1.49      | v1_funct_1(X0) != iProver_top
% 7.74/1.49      | v1_funct_1(X3) != iProver_top ),
% 7.74/1.49      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_8353,plain,
% 7.74/1.49      ( m1_subset_1(k5_relat_1(sK2,k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top
% 7.74/1.49      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 7.74/1.49      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 7.74/1.49      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 7.74/1.49      | v1_funct_1(sK2) != iProver_top ),
% 7.74/1.49      inference(superposition,[status(thm)],[c_8349,c_1630]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_8687,plain,
% 7.74/1.49      ( m1_subset_1(k5_relat_1(sK2,k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 7.74/1.49      inference(global_propositional_subsumption,
% 7.74/1.49                [status(thm)],
% 7.74/1.49                [c_8353,c_35,c_36,c_37,c_38,c_3161,c_3459]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_12,plain,
% 7.74/1.49      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 7.74/1.49      inference(cnf_transformation,[],[f91]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_1633,plain,
% 7.74/1.49      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 7.74/1.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_11,plain,
% 7.74/1.49      ( ~ r2_relset_1(X0,X1,X2,X3)
% 7.74/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.74/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.74/1.49      | X3 = X2 ),
% 7.74/1.49      inference(cnf_transformation,[],[f65]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_1634,plain,
% 7.74/1.49      ( X0 = X1
% 7.74/1.49      | r2_relset_1(X2,X3,X1,X0) != iProver_top
% 7.74/1.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 7.74/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top ),
% 7.74/1.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_2846,plain,
% 7.74/1.49      ( k6_partfun1(X0) = X1
% 7.74/1.49      | r2_relset_1(X0,X0,k6_partfun1(X0),X1) != iProver_top
% 7.74/1.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
% 7.74/1.49      inference(superposition,[status(thm)],[c_1633,c_1634]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_9611,plain,
% 7.74/1.49      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK1)
% 7.74/1.49      | r2_relset_1(sK1,sK1,k6_partfun1(sK1),k5_relat_1(sK2,k2_funct_1(sK2))) != iProver_top ),
% 7.74/1.49      inference(superposition,[status(thm)],[c_8687,c_2846]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_4,plain,
% 7.74/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.74/1.49      inference(cnf_transformation,[],[f60]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_113,plain,
% 7.74/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 7.74/1.49      | r1_tarski(X0,X1) != iProver_top ),
% 7.74/1.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_115,plain,
% 7.74/1.49      ( m1_subset_1(sK1,k1_zfmisc_1(sK1)) = iProver_top
% 7.74/1.49      | r1_tarski(sK1,sK1) != iProver_top ),
% 7.74/1.49      inference(instantiation,[status(thm)],[c_113]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_3,plain,
% 7.74/1.49      ( r1_tarski(X0,X0) ),
% 7.74/1.49      inference(cnf_transformation,[],[f93]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_117,plain,
% 7.74/1.49      ( r1_tarski(sK1,sK1) ),
% 7.74/1.49      inference(instantiation,[status(thm)],[c_3]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_116,plain,
% 7.74/1.49      ( r1_tarski(X0,X0) = iProver_top ),
% 7.74/1.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_118,plain,
% 7.74/1.49      ( r1_tarski(sK1,sK1) = iProver_top ),
% 7.74/1.49      inference(instantiation,[status(thm)],[c_116]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_1,plain,
% 7.74/1.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.74/1.49      inference(cnf_transformation,[],[f58]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_121,plain,
% 7.74/1.49      ( ~ r1_tarski(sK1,sK1) | sK1 = sK1 ),
% 7.74/1.49      inference(instantiation,[status(thm)],[c_1]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_986,plain,
% 7.74/1.49      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.74/1.49      theory(equality) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_1698,plain,
% 7.74/1.49      ( ~ m1_subset_1(X0,X1)
% 7.74/1.49      | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0))
% 7.74/1.49      | k1_zfmisc_1(k1_xboole_0) != X1
% 7.74/1.49      | sK1 != X0 ),
% 7.74/1.49      inference(instantiation,[status(thm)],[c_986]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_1778,plain,
% 7.74/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.74/1.49      | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0))
% 7.74/1.49      | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(X1)
% 7.74/1.49      | sK1 != X0 ),
% 7.74/1.49      inference(instantiation,[status(thm)],[c_1698]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_1779,plain,
% 7.74/1.49      ( k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(X0)
% 7.74/1.49      | sK1 != X1
% 7.74/1.49      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 7.74/1.49      | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 7.74/1.49      inference(predicate_to_equality,[status(thm)],[c_1778]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_1781,plain,
% 7.74/1.49      ( k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(sK1)
% 7.74/1.49      | sK1 != sK1
% 7.74/1.49      | m1_subset_1(sK1,k1_zfmisc_1(sK1)) != iProver_top
% 7.74/1.49      | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 7.74/1.49      inference(instantiation,[status(thm)],[c_1779]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_985,plain,
% 7.74/1.49      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 7.74/1.49      theory(equality) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_1901,plain,
% 7.74/1.49      ( k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(X0) | k1_xboole_0 != X0 ),
% 7.74/1.49      inference(instantiation,[status(thm)],[c_985]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_1902,plain,
% 7.74/1.49      ( k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(sK1)
% 7.74/1.49      | k1_xboole_0 != sK1 ),
% 7.74/1.49      inference(instantiation,[status(thm)],[c_1901]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_15,plain,
% 7.74/1.49      ( ~ v3_funct_2(X0,X1,X2)
% 7.74/1.49      | v2_funct_2(X0,X2)
% 7.74/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.74/1.49      | ~ v1_funct_1(X0) ),
% 7.74/1.49      inference(cnf_transformation,[],[f72]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_8,plain,
% 7.74/1.49      ( v5_relat_1(X0,X1)
% 7.74/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 7.74/1.49      inference(cnf_transformation,[],[f63]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_19,plain,
% 7.74/1.49      ( ~ v2_funct_2(X0,X1)
% 7.74/1.49      | ~ v5_relat_1(X0,X1)
% 7.74/1.49      | ~ v1_relat_1(X0)
% 7.74/1.49      | k2_relat_1(X0) = X1 ),
% 7.74/1.49      inference(cnf_transformation,[],[f73]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_528,plain,
% 7.74/1.49      ( ~ v2_funct_2(X0,X1)
% 7.74/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 7.74/1.49      | ~ v1_relat_1(X0)
% 7.74/1.49      | k2_relat_1(X0) = X1 ),
% 7.74/1.49      inference(resolution,[status(thm)],[c_8,c_19]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_7,plain,
% 7.74/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.74/1.49      | v1_relat_1(X0) ),
% 7.74/1.49      inference(cnf_transformation,[],[f62]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_540,plain,
% 7.74/1.49      ( ~ v2_funct_2(X0,X1)
% 7.74/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 7.74/1.49      | k2_relat_1(X0) = X1 ),
% 7.74/1.49      inference(forward_subsumption_resolution,[status(thm)],[c_528,c_7]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_571,plain,
% 7.74/1.49      ( ~ v3_funct_2(X0,X1,X2)
% 7.74/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.74/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 7.74/1.49      | ~ v1_funct_1(X0)
% 7.74/1.49      | X3 != X0
% 7.74/1.49      | X5 != X2
% 7.74/1.49      | k2_relat_1(X3) = X5 ),
% 7.74/1.49      inference(resolution_lifted,[status(thm)],[c_15,c_540]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_572,plain,
% 7.74/1.49      ( ~ v3_funct_2(X0,X1,X2)
% 7.74/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.74/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
% 7.74/1.49      | ~ v1_funct_1(X0)
% 7.74/1.49      | k2_relat_1(X0) = X2 ),
% 7.74/1.49      inference(unflattening,[status(thm)],[c_571]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_1614,plain,
% 7.74/1.49      ( k2_relat_1(X0) = X1
% 7.74/1.49      | v3_funct_2(X0,X2,X1) != iProver_top
% 7.74/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
% 7.74/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
% 7.74/1.49      | v1_funct_1(X0) != iProver_top ),
% 7.74/1.49      inference(predicate_to_equality,[status(thm)],[c_572]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_2078,plain,
% 7.74/1.49      ( k2_relat_1(sK2) = sK1
% 7.74/1.49      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 7.74/1.49      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
% 7.74/1.49      | v1_funct_1(sK2) != iProver_top ),
% 7.74/1.49      inference(superposition,[status(thm)],[c_1619,c_1614]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_2083,plain,
% 7.74/1.49      ( k2_relat_1(sK2) = sK1
% 7.74/1.49      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 7.74/1.49      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 7.74/1.49      | v1_funct_1(sK2) != iProver_top ),
% 7.74/1.49      inference(instantiation,[status(thm)],[c_2078]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_2499,plain,
% 7.74/1.49      ( k2_relat_1(sK2) = sK1 ),
% 7.74/1.49      inference(global_propositional_subsumption,
% 7.74/1.49                [status(thm)],
% 7.74/1.49                [c_2078,c_35,c_37,c_38,c_2083]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_9,plain,
% 7.74/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.74/1.49      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 7.74/1.49      inference(cnf_transformation,[],[f64]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_1636,plain,
% 7.74/1.49      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 7.74/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.74/1.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_2217,plain,
% 7.74/1.49      ( k2_relset_1(sK1,sK1,sK2) = k2_relat_1(sK2) ),
% 7.74/1.49      inference(superposition,[status(thm)],[c_1619,c_1636]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_2501,plain,
% 7.74/1.49      ( k2_relset_1(sK1,sK1,sK2) = sK1 ),
% 7.74/1.49      inference(demodulation,[status(thm)],[c_2499,c_2217]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_16,plain,
% 7.74/1.49      ( ~ v3_funct_2(X0,X1,X2)
% 7.74/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.74/1.49      | v2_funct_1(X0)
% 7.74/1.49      | ~ v1_funct_1(X0) ),
% 7.74/1.49      inference(cnf_transformation,[],[f71]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_1631,plain,
% 7.74/1.49      ( v3_funct_2(X0,X1,X2) != iProver_top
% 7.74/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.74/1.49      | v2_funct_1(X0) = iProver_top
% 7.74/1.49      | v1_funct_1(X0) != iProver_top ),
% 7.74/1.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_2836,plain,
% 7.74/1.49      ( v3_funct_2(sK2,sK1,sK1) != iProver_top
% 7.74/1.49      | v2_funct_1(sK2) = iProver_top
% 7.74/1.49      | v1_funct_1(sK2) != iProver_top ),
% 7.74/1.49      inference(superposition,[status(thm)],[c_1619,c_1631]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_2843,plain,
% 7.74/1.49      ( ~ v3_funct_2(sK2,sK1,sK1) | v2_funct_1(sK2) | ~ v1_funct_1(sK2) ),
% 7.74/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_2836]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_29,plain,
% 7.74/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.74/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.74/1.49      | ~ v2_funct_1(X0)
% 7.74/1.49      | ~ v1_funct_1(X0)
% 7.74/1.49      | k2_relset_1(X1,X2,X0) != X2
% 7.74/1.49      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 7.74/1.49      | k1_xboole_0 = X2 ),
% 7.74/1.49      inference(cnf_transformation,[],[f84]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_8426,plain,
% 7.74/1.49      ( ~ v1_funct_2(sK2,X0,X1)
% 7.74/1.49      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.74/1.49      | ~ v2_funct_1(sK2)
% 7.74/1.49      | ~ v1_funct_1(sK2)
% 7.74/1.49      | k2_relset_1(X0,X1,sK2) != X1
% 7.74/1.49      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
% 7.74/1.49      | k1_xboole_0 = X1 ),
% 7.74/1.49      inference(instantiation,[status(thm)],[c_29]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_8433,plain,
% 7.74/1.49      ( ~ v1_funct_2(sK2,sK1,sK1)
% 7.74/1.49      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 7.74/1.49      | ~ v2_funct_1(sK2)
% 7.74/1.49      | ~ v1_funct_1(sK2)
% 7.74/1.49      | k2_relset_1(sK1,sK1,sK2) != sK1
% 7.74/1.49      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK1)
% 7.74/1.49      | k1_xboole_0 = sK1 ),
% 7.74/1.49      inference(instantiation,[status(thm)],[c_8426]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_5,plain,
% 7.74/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.74/1.49      inference(cnf_transformation,[],[f59]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_1637,plain,
% 7.74/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.74/1.49      | r1_tarski(X0,X1) = iProver_top ),
% 7.74/1.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_1994,plain,
% 7.74/1.49      ( r1_tarski(k6_partfun1(X0),k2_zfmisc_1(X0,X0)) = iProver_top ),
% 7.74/1.49      inference(superposition,[status(thm)],[c_1633,c_1637]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_1638,plain,
% 7.74/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 7.74/1.49      | r1_tarski(X0,X1) != iProver_top ),
% 7.74/1.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_0,plain,
% 7.74/1.49      ( v1_xboole_0(k1_xboole_0) ),
% 7.74/1.49      inference(cnf_transformation,[],[f55]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_6,plain,
% 7.74/1.49      ( ~ r2_hidden(X0,X1)
% 7.74/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 7.74/1.49      | ~ v1_xboole_0(X2) ),
% 7.74/1.49      inference(cnf_transformation,[],[f61]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_454,plain,
% 7.74/1.49      ( ~ r2_hidden(X0,X1)
% 7.74/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 7.74/1.49      | k1_xboole_0 != X2 ),
% 7.74/1.49      inference(resolution_lifted,[status(thm)],[c_0,c_6]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_455,plain,
% 7.74/1.49      ( ~ r2_hidden(X0,X1) | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
% 7.74/1.49      inference(unflattening,[status(thm)],[c_454]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_14,plain,
% 7.74/1.49      ( r2_relset_1(X0,X0,X1,X2)
% 7.74/1.49      | r2_hidden(sK0(X0,X1,X2),X0)
% 7.74/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 7.74/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 7.74/1.49      inference(cnf_transformation,[],[f68]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_469,plain,
% 7.74/1.49      ( r2_relset_1(X0,X0,X1,X2)
% 7.74/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 7.74/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 7.74/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
% 7.74/1.49      | X0 != X3
% 7.74/1.49      | sK0(X0,X1,X2) != X4 ),
% 7.74/1.49      inference(resolution_lifted,[status(thm)],[c_455,c_14]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_470,plain,
% 7.74/1.49      ( r2_relset_1(X0,X0,X1,X2)
% 7.74/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 7.74/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 7.74/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) ),
% 7.74/1.49      inference(unflattening,[status(thm)],[c_469]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_1615,plain,
% 7.74/1.49      ( r2_relset_1(X0,X0,X1,X2) = iProver_top
% 7.74/1.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 7.74/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 7.74/1.49      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.74/1.49      inference(predicate_to_equality,[status(thm)],[c_470]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_2687,plain,
% 7.74/1.49      ( r2_relset_1(X0,X0,X1,X2) = iProver_top
% 7.74/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 7.74/1.49      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 7.74/1.49      | r1_tarski(X1,k2_zfmisc_1(X0,X0)) != iProver_top ),
% 7.74/1.49      inference(superposition,[status(thm)],[c_1638,c_1615]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_7693,plain,
% 7.74/1.49      ( r2_relset_1(sK1,sK1,X0,sK2) = iProver_top
% 7.74/1.49      | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 7.74/1.49      | r1_tarski(X0,k2_zfmisc_1(sK1,sK1)) != iProver_top ),
% 7.74/1.49      inference(superposition,[status(thm)],[c_1619,c_2687]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_8412,plain,
% 7.74/1.49      ( r2_relset_1(sK1,sK1,k6_partfun1(sK1),sK2) = iProver_top
% 7.74/1.49      | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.74/1.49      inference(superposition,[status(thm)],[c_1994,c_7693]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_30,negated_conjecture,
% 7.74/1.49      ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
% 7.74/1.49      | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) ),
% 7.74/1.49      inference(cnf_transformation,[],[f90]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_39,plain,
% 7.74/1.49      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) != iProver_top
% 7.74/1.49      | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) != iProver_top ),
% 7.74/1.49      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_89,plain,
% 7.74/1.49      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 7.74/1.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_91,plain,
% 7.74/1.49      ( m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 7.74/1.49      inference(instantiation,[status(thm)],[c_89]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_1674,plain,
% 7.74/1.49      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
% 7.74/1.49      | ~ m1_subset_1(k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 7.74/1.49      | ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 7.74/1.49      | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) ),
% 7.74/1.49      inference(instantiation,[status(thm)],[c_470]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_1675,plain,
% 7.74/1.49      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) = iProver_top
% 7.74/1.49      | m1_subset_1(k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 7.74/1.49      | m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 7.74/1.49      | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.74/1.49      inference(predicate_to_equality,[status(thm)],[c_1674]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_1687,plain,
% 7.74/1.49      ( m1_subset_1(k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 7.74/1.49      | ~ m1_subset_1(k2_funct_2(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 7.74/1.49      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 7.74/1.49      | ~ v1_funct_1(k2_funct_2(sK1,sK2))
% 7.74/1.49      | ~ v1_funct_1(sK2) ),
% 7.74/1.49      inference(instantiation,[status(thm)],[c_20]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_1688,plain,
% 7.74/1.49      ( m1_subset_1(k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top
% 7.74/1.49      | m1_subset_1(k2_funct_2(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 7.74/1.49      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 7.74/1.49      | v1_funct_1(k2_funct_2(sK1,sK2)) != iProver_top
% 7.74/1.49      | v1_funct_1(sK2) != iProver_top ),
% 7.74/1.49      inference(predicate_to_equality,[status(thm)],[c_1687]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_1877,plain,
% 7.74/1.49      ( ~ v1_funct_2(sK2,sK1,sK1)
% 7.74/1.49      | ~ v3_funct_2(sK2,sK1,sK1)
% 7.74/1.49      | m1_subset_1(k2_funct_2(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 7.74/1.49      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 7.74/1.49      | ~ v1_funct_1(sK2) ),
% 7.74/1.49      inference(instantiation,[status(thm)],[c_22]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_1878,plain,
% 7.74/1.49      ( v1_funct_2(sK2,sK1,sK1) != iProver_top
% 7.74/1.49      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 7.74/1.49      | m1_subset_1(k2_funct_2(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top
% 7.74/1.49      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 7.74/1.49      | v1_funct_1(sK2) != iProver_top ),
% 7.74/1.49      inference(predicate_to_equality,[status(thm)],[c_1877]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_3431,plain,
% 7.74/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.74/1.49      | m1_subset_1(k1_partfun1(X1,X2,X3,X4,X0,k2_funct_2(sK1,sK2)),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
% 7.74/1.49      | ~ m1_subset_1(k2_funct_2(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 7.74/1.49      | ~ v1_funct_1(X0)
% 7.74/1.49      | ~ v1_funct_1(k2_funct_2(sK1,sK2)) ),
% 7.74/1.49      inference(instantiation,[status(thm)],[c_20]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_6079,plain,
% 7.74/1.49      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,sK2,k2_funct_2(sK1,sK2)),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
% 7.74/1.49      | ~ m1_subset_1(k2_funct_2(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 7.74/1.49      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.74/1.49      | ~ v1_funct_1(k2_funct_2(sK1,sK2))
% 7.74/1.49      | ~ v1_funct_1(sK2) ),
% 7.74/1.49      inference(instantiation,[status(thm)],[c_3431]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_6080,plain,
% 7.74/1.49      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,sK2,k2_funct_2(sK1,sK2)),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) = iProver_top
% 7.74/1.49      | m1_subset_1(k2_funct_2(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 7.74/1.49      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.74/1.49      | v1_funct_1(k2_funct_2(sK1,sK2)) != iProver_top
% 7.74/1.49      | v1_funct_1(sK2) != iProver_top ),
% 7.74/1.49      inference(predicate_to_equality,[status(thm)],[c_6079]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_6082,plain,
% 7.74/1.49      ( m1_subset_1(k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top
% 7.74/1.49      | m1_subset_1(k2_funct_2(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 7.74/1.49      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 7.74/1.49      | v1_funct_1(k2_funct_2(sK1,sK2)) != iProver_top
% 7.74/1.49      | v1_funct_1(sK2) != iProver_top ),
% 7.74/1.49      inference(instantiation,[status(thm)],[c_6080]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_1855,plain,
% 7.74/1.49      ( r2_relset_1(X0,X0,X1,k6_partfun1(sK1))
% 7.74/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 7.74/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
% 7.74/1.49      | ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 7.74/1.49      inference(instantiation,[status(thm)],[c_470]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_8492,plain,
% 7.74/1.49      ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X2,X0,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1))
% 7.74/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
% 7.74/1.49      | ~ m1_subset_1(k1_partfun1(X0,X1,X2,X0,sK2,k2_funct_2(sK1,sK2)),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 7.74/1.49      | ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 7.74/1.49      inference(instantiation,[status(thm)],[c_1855]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_8524,plain,
% 7.74/1.49      ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X2,X0,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) = iProver_top
% 7.74/1.49      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 7.74/1.49      | m1_subset_1(k1_partfun1(X0,X1,X2,X0,sK2,k2_funct_2(sK1,sK2)),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 7.74/1.49      | m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
% 7.74/1.49      inference(predicate_to_equality,[status(thm)],[c_8492]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_8526,plain,
% 7.74/1.49      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) = iProver_top
% 7.74/1.49      | m1_subset_1(k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 7.74/1.49      | m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 7.74/1.49      | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.74/1.49      inference(instantiation,[status(thm)],[c_8524]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_8581,plain,
% 7.74/1.49      ( m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.74/1.49      inference(global_propositional_subsumption,
% 7.74/1.49                [status(thm)],
% 7.74/1.49                [c_8412,c_35,c_36,c_37,c_38,c_39,c_91,c_1675,c_1688,
% 7.74/1.49                 c_1738,c_1878,c_6082,c_8526]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_9773,plain,
% 7.74/1.49      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK1) ),
% 7.74/1.49      inference(global_propositional_subsumption,
% 7.74/1.49                [status(thm)],
% 7.74/1.49                [c_9611,c_34,c_35,c_33,c_36,c_32,c_37,c_31,c_38,c_39,
% 7.74/1.49                 c_91,c_115,c_117,c_118,c_121,c_1675,c_1688,c_1738,
% 7.74/1.49                 c_1781,c_1878,c_1902,c_2501,c_2843,c_6082,c_8433,c_8526]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_4024,plain,
% 7.74/1.49      ( k1_partfun1(X0,X1,sK1,sK1,X2,sK2) = k5_relat_1(X2,sK2)
% 7.74/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.74/1.49      | v1_funct_1(X2) != iProver_top
% 7.74/1.49      | v1_funct_1(sK2) != iProver_top ),
% 7.74/1.49      inference(superposition,[status(thm)],[c_1619,c_1624]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_4316,plain,
% 7.74/1.49      ( v1_funct_1(X2) != iProver_top
% 7.74/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.74/1.49      | k1_partfun1(X0,X1,sK1,sK1,X2,sK2) = k5_relat_1(X2,sK2) ),
% 7.74/1.49      inference(global_propositional_subsumption,
% 7.74/1.49                [status(thm)],
% 7.74/1.49                [c_4024,c_35]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_4317,plain,
% 7.74/1.49      ( k1_partfun1(X0,X1,sK1,sK1,X2,sK2) = k5_relat_1(X2,sK2)
% 7.74/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.74/1.49      | v1_funct_1(X2) != iProver_top ),
% 7.74/1.49      inference(renaming,[status(thm)],[c_4316]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_4327,plain,
% 7.74/1.49      ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k5_relat_1(k2_funct_1(sK2),sK2)
% 7.74/1.49      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 7.74/1.49      inference(superposition,[status(thm)],[c_3707,c_4317]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_4431,plain,
% 7.74/1.49      ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k5_relat_1(k2_funct_1(sK2),sK2) ),
% 7.74/1.49      inference(global_propositional_subsumption,
% 7.74/1.49                [status(thm)],
% 7.74/1.49                [c_4327,c_3161]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_1620,plain,
% 7.74/1.49      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) != iProver_top
% 7.74/1.49      | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) != iProver_top ),
% 7.74/1.49      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_3082,plain,
% 7.74/1.49      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1)) != iProver_top
% 7.74/1.49      | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)),k6_partfun1(sK1)) != iProver_top ),
% 7.74/1.49      inference(demodulation,[status(thm)],[c_3080,c_1620]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_4433,plain,
% 7.74/1.49      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)),k6_partfun1(sK1)) != iProver_top
% 7.74/1.49      | r2_relset_1(sK1,sK1,k5_relat_1(k2_funct_1(sK2),sK2),k6_partfun1(sK1)) != iProver_top ),
% 7.74/1.49      inference(demodulation,[status(thm)],[c_4431,c_3082]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_8351,plain,
% 7.74/1.49      ( r2_relset_1(sK1,sK1,k5_relat_1(k2_funct_1(sK2),sK2),k6_partfun1(sK1)) != iProver_top
% 7.74/1.49      | r2_relset_1(sK1,sK1,k5_relat_1(sK2,k2_funct_1(sK2)),k6_partfun1(sK1)) != iProver_top ),
% 7.74/1.49      inference(demodulation,[status(thm)],[c_8349,c_4433]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_9784,plain,
% 7.74/1.49      ( r2_relset_1(sK1,sK1,k5_relat_1(k2_funct_1(sK2),sK2),k6_partfun1(sK1)) != iProver_top
% 7.74/1.49      | r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) != iProver_top ),
% 7.74/1.49      inference(demodulation,[status(thm)],[c_9773,c_8351]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_9787,plain,
% 7.74/1.49      ( ~ r2_relset_1(sK1,sK1,k5_relat_1(k2_funct_1(sK2),sK2),k6_partfun1(sK1))
% 7.74/1.49      | ~ r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) ),
% 7.74/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_9784]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_28,plain,
% 7.74/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.74/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.74/1.49      | ~ v2_funct_1(X0)
% 7.74/1.49      | ~ v1_funct_1(X0)
% 7.74/1.49      | k2_relset_1(X1,X2,X0) != X2
% 7.74/1.49      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
% 7.74/1.49      | k1_xboole_0 = X2 ),
% 7.74/1.49      inference(cnf_transformation,[],[f85]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_8427,plain,
% 7.74/1.49      ( ~ v1_funct_2(sK2,X0,X1)
% 7.74/1.49      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.74/1.49      | ~ v2_funct_1(sK2)
% 7.74/1.49      | ~ v1_funct_1(sK2)
% 7.74/1.49      | k2_relset_1(X0,X1,sK2) != X1
% 7.74/1.49      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(X1)
% 7.74/1.49      | k1_xboole_0 = X1 ),
% 7.74/1.49      inference(instantiation,[status(thm)],[c_28]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_8429,plain,
% 7.74/1.49      ( ~ v1_funct_2(sK2,sK1,sK1)
% 7.74/1.49      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 7.74/1.49      | ~ v2_funct_1(sK2)
% 7.74/1.49      | ~ v1_funct_1(sK2)
% 7.74/1.49      | k2_relset_1(sK1,sK1,sK2) != sK1
% 7.74/1.49      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 7.74/1.49      | k1_xboole_0 = sK1 ),
% 7.74/1.49      inference(instantiation,[status(thm)],[c_8427]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_10,plain,
% 7.74/1.49      ( r2_relset_1(X0,X1,X2,X2)
% 7.74/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 7.74/1.49      inference(cnf_transformation,[],[f94]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_1635,plain,
% 7.74/1.49      ( r2_relset_1(X0,X1,X2,X2) = iProver_top
% 7.74/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.74/1.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_2205,plain,
% 7.74/1.49      ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0)) = iProver_top ),
% 7.74/1.49      inference(superposition,[status(thm)],[c_1633,c_1635]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_2210,plain,
% 7.74/1.49      ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0)) ),
% 7.74/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_2205]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_2212,plain,
% 7.74/1.49      ( r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) ),
% 7.74/1.49      inference(instantiation,[status(thm)],[c_2210]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_989,plain,
% 7.74/1.49      ( X0 != X1 | k6_partfun1(X0) = k6_partfun1(X1) ),
% 7.74/1.49      theory(equality) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_1001,plain,
% 7.74/1.49      ( k6_partfun1(sK1) = k6_partfun1(sK1) | sK1 != sK1 ),
% 7.74/1.49      inference(instantiation,[status(thm)],[c_989]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(contradiction,plain,
% 7.74/1.49      ( $false ),
% 7.74/1.49      inference(minisat,
% 7.74/1.49                [status(thm)],
% 7.74/1.49                [c_17995,c_9787,c_8581,c_8429,c_2843,c_2501,c_2212,
% 7.74/1.49                 c_1902,c_1781,c_1001,c_121,c_118,c_117,c_115,c_31,c_32,
% 7.74/1.49                 c_33,c_34]) ).
% 7.74/1.49  
% 7.74/1.49  
% 7.74/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.74/1.49  
% 7.74/1.49  ------                               Statistics
% 7.74/1.49  
% 7.74/1.49  ------ General
% 7.74/1.49  
% 7.74/1.49  abstr_ref_over_cycles:                  0
% 7.74/1.49  abstr_ref_under_cycles:                 0
% 7.74/1.49  gc_basic_clause_elim:                   0
% 7.74/1.49  forced_gc_time:                         0
% 7.74/1.49  parsing_time:                           0.019
% 7.74/1.49  unif_index_cands_time:                  0.
% 7.74/1.49  unif_index_add_time:                    0.
% 7.74/1.49  orderings_time:                         0.
% 7.74/1.49  out_proof_time:                         0.013
% 7.74/1.49  total_time:                             0.622
% 7.74/1.49  num_of_symbols:                         57
% 7.74/1.49  num_of_terms:                           20175
% 7.74/1.49  
% 7.74/1.49  ------ Preprocessing
% 7.74/1.49  
% 7.74/1.49  num_of_splits:                          0
% 7.74/1.49  num_of_split_atoms:                     0
% 7.74/1.49  num_of_reused_defs:                     0
% 7.74/1.49  num_eq_ax_congr_red:                    40
% 7.74/1.49  num_of_sem_filtered_clauses:            1
% 7.74/1.49  num_of_subtypes:                        0
% 7.74/1.49  monotx_restored_types:                  0
% 7.74/1.49  sat_num_of_epr_types:                   0
% 7.74/1.49  sat_num_of_non_cyclic_types:            0
% 7.74/1.49  sat_guarded_non_collapsed_types:        0
% 7.74/1.49  num_pure_diseq_elim:                    0
% 7.74/1.49  simp_replaced_by:                       0
% 7.74/1.49  res_preprocessed:                       143
% 7.74/1.49  prep_upred:                             0
% 7.74/1.49  prep_unflattend:                        9
% 7.74/1.49  smt_new_axioms:                         0
% 7.74/1.49  pred_elim_cands:                        7
% 7.74/1.49  pred_elim:                              5
% 7.74/1.49  pred_elim_cl:                           6
% 7.74/1.49  pred_elim_cycles:                       8
% 7.74/1.49  merged_defs:                            8
% 7.74/1.49  merged_defs_ncl:                        0
% 7.74/1.49  bin_hyper_res:                          8
% 7.74/1.49  prep_cycles:                            4
% 7.74/1.49  pred_elim_time:                         0.007
% 7.74/1.49  splitting_time:                         0.
% 7.74/1.49  sem_filter_time:                        0.
% 7.74/1.49  monotx_time:                            0.001
% 7.74/1.49  subtype_inf_time:                       0.
% 7.74/1.49  
% 7.74/1.49  ------ Problem properties
% 7.74/1.49  
% 7.74/1.49  clauses:                                27
% 7.74/1.49  conjectures:                            5
% 7.74/1.49  epr:                                    5
% 7.74/1.49  horn:                                   25
% 7.74/1.49  ground:                                 5
% 7.74/1.49  unary:                                  6
% 7.74/1.49  binary:                                 5
% 7.74/1.49  lits:                                   94
% 7.74/1.49  lits_eq:                                13
% 7.74/1.49  fd_pure:                                0
% 7.74/1.49  fd_pseudo:                              0
% 7.74/1.49  fd_cond:                                2
% 7.74/1.49  fd_pseudo_cond:                         3
% 7.74/1.49  ac_symbols:                             0
% 7.74/1.49  
% 7.74/1.49  ------ Propositional Solver
% 7.74/1.49  
% 7.74/1.49  prop_solver_calls:                      33
% 7.74/1.49  prop_fast_solver_calls:                 1884
% 7.74/1.49  smt_solver_calls:                       0
% 7.74/1.49  smt_fast_solver_calls:                  0
% 7.74/1.49  prop_num_of_clauses:                    7104
% 7.74/1.49  prop_preprocess_simplified:             20533
% 7.74/1.49  prop_fo_subsumed:                       148
% 7.74/1.49  prop_solver_time:                       0.
% 7.74/1.49  smt_solver_time:                        0.
% 7.74/1.49  smt_fast_solver_time:                   0.
% 7.74/1.49  prop_fast_solver_time:                  0.
% 7.74/1.49  prop_unsat_core_time:                   0.
% 7.74/1.49  
% 7.74/1.49  ------ QBF
% 7.74/1.49  
% 7.74/1.49  qbf_q_res:                              0
% 7.74/1.49  qbf_num_tautologies:                    0
% 7.74/1.49  qbf_prep_cycles:                        0
% 7.74/1.49  
% 7.74/1.49  ------ BMC1
% 7.74/1.49  
% 7.74/1.49  bmc1_current_bound:                     -1
% 7.74/1.49  bmc1_last_solved_bound:                 -1
% 7.74/1.49  bmc1_unsat_core_size:                   -1
% 7.74/1.49  bmc1_unsat_core_parents_size:           -1
% 7.74/1.49  bmc1_merge_next_fun:                    0
% 7.74/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.74/1.49  
% 7.74/1.49  ------ Instantiation
% 7.74/1.49  
% 7.74/1.49  inst_num_of_clauses:                    2284
% 7.74/1.49  inst_num_in_passive:                    1122
% 7.74/1.49  inst_num_in_active:                     1119
% 7.74/1.49  inst_num_in_unprocessed:                42
% 7.74/1.49  inst_num_of_loops:                      1248
% 7.74/1.49  inst_num_of_learning_restarts:          0
% 7.74/1.49  inst_num_moves_active_passive:          125
% 7.74/1.49  inst_lit_activity:                      0
% 7.74/1.49  inst_lit_activity_moves:                0
% 7.74/1.49  inst_num_tautologies:                   0
% 7.74/1.49  inst_num_prop_implied:                  0
% 7.74/1.49  inst_num_existing_simplified:           0
% 7.74/1.49  inst_num_eq_res_simplified:             0
% 7.74/1.49  inst_num_child_elim:                    0
% 7.74/1.49  inst_num_of_dismatching_blockings:      1520
% 7.74/1.49  inst_num_of_non_proper_insts:           4182
% 7.74/1.49  inst_num_of_duplicates:                 0
% 7.74/1.49  inst_inst_num_from_inst_to_res:         0
% 7.74/1.49  inst_dismatching_checking_time:         0.
% 7.74/1.49  
% 7.74/1.49  ------ Resolution
% 7.74/1.49  
% 7.74/1.49  res_num_of_clauses:                     0
% 7.74/1.49  res_num_in_passive:                     0
% 7.74/1.49  res_num_in_active:                      0
% 7.74/1.49  res_num_of_loops:                       147
% 7.74/1.49  res_forward_subset_subsumed:            312
% 7.74/1.49  res_backward_subset_subsumed:           0
% 7.74/1.49  res_forward_subsumed:                   0
% 7.74/1.49  res_backward_subsumed:                  0
% 7.74/1.49  res_forward_subsumption_resolution:     2
% 7.74/1.49  res_backward_subsumption_resolution:    0
% 7.74/1.49  res_clause_to_clause_subsumption:       1107
% 7.74/1.49  res_orphan_elimination:                 0
% 7.74/1.49  res_tautology_del:                      242
% 7.74/1.49  res_num_eq_res_simplified:              0
% 7.74/1.49  res_num_sel_changes:                    0
% 7.74/1.49  res_moves_from_active_to_pass:          0
% 7.74/1.49  
% 7.74/1.49  ------ Superposition
% 7.74/1.49  
% 7.74/1.49  sup_time_total:                         0.
% 7.74/1.49  sup_time_generating:                    0.
% 7.74/1.49  sup_time_sim_full:                      0.
% 7.74/1.49  sup_time_sim_immed:                     0.
% 7.74/1.49  
% 7.74/1.49  sup_num_of_clauses:                     428
% 7.74/1.49  sup_num_in_active:                      209
% 7.74/1.49  sup_num_in_passive:                     219
% 7.74/1.49  sup_num_of_loops:                       248
% 7.74/1.49  sup_fw_superposition:                   267
% 7.74/1.49  sup_bw_superposition:                   351
% 7.74/1.49  sup_immediate_simplified:               86
% 7.74/1.49  sup_given_eliminated:                   1
% 7.74/1.49  comparisons_done:                       0
% 7.74/1.49  comparisons_avoided:                    0
% 7.74/1.49  
% 7.74/1.49  ------ Simplifications
% 7.74/1.49  
% 7.74/1.49  
% 7.74/1.49  sim_fw_subset_subsumed:                 41
% 7.74/1.49  sim_bw_subset_subsumed:                 11
% 7.74/1.49  sim_fw_subsumed:                        13
% 7.74/1.49  sim_bw_subsumed:                        21
% 7.74/1.49  sim_fw_subsumption_res:                 0
% 7.74/1.49  sim_bw_subsumption_res:                 0
% 7.74/1.49  sim_tautology_del:                      1
% 7.74/1.49  sim_eq_tautology_del:                   20
% 7.74/1.49  sim_eq_res_simp:                        0
% 7.74/1.49  sim_fw_demodulated:                     30
% 7.74/1.49  sim_bw_demodulated:                     17
% 7.74/1.49  sim_light_normalised:                   18
% 7.74/1.49  sim_joinable_taut:                      0
% 7.74/1.49  sim_joinable_simp:                      0
% 7.74/1.49  sim_ac_normalised:                      0
% 7.74/1.49  sim_smt_subsumption:                    0
% 7.74/1.49  
%------------------------------------------------------------------------------
