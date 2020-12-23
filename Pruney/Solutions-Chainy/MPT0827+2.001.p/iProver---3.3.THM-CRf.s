%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:55:10 EST 2020

% Result     : Theorem 11.21s
% Output     : CNFRefutation 11.21s
% Verified   : 
% Statistics : Number of formulae       :  158 ( 693 expanded)
%              Number of clauses        :   95 ( 316 expanded)
%              Number of leaves         :   17 ( 118 expanded)
%              Depth                    :   20
%              Number of atoms          :  374 (1676 expanded)
%              Number of equality atoms :  124 ( 370 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f9,axiom,(
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
    inference(ennf_transformation,[],[f9])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f46])).

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

fof(f51,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f78,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f49])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f20,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r1_tarski(k6_relat_1(X2),X3)
       => ( r1_tarski(X2,k2_relset_1(X0,X1,X3))
          & r1_tarski(X2,k1_relset_1(X0,X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( r1_tarski(k6_relat_1(X2),X3)
         => ( r1_tarski(X2,k2_relset_1(X0,X1,X3))
            & r1_tarski(X2,k1_relset_1(X0,X1,X3)) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f40,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X2,k2_relset_1(X0,X1,X3))
        | ~ r1_tarski(X2,k1_relset_1(X0,X1,X3)) )
      & r1_tarski(k6_relat_1(X2),X3)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f41,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X2,k2_relset_1(X0,X1,X3))
        | ~ r1_tarski(X2,k1_relset_1(X0,X1,X3)) )
      & r1_tarski(k6_relat_1(X2),X3)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f40])).

fof(f47,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ r1_tarski(X2,k2_relset_1(X0,X1,X3))
          | ~ r1_tarski(X2,k1_relset_1(X0,X1,X3)) )
        & r1_tarski(k6_relat_1(X2),X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ( ~ r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3))
        | ~ r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3)) )
      & r1_tarski(k6_relat_1(sK2),sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ( ~ r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3))
      | ~ r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3)) )
    & r1_tarski(k6_relat_1(sK2),sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f41,f47])).

fof(f75,plain,(
    r1_tarski(k6_relat_1(sK2),sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f74,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f48])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f76,plain,
    ( ~ r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3))
    | ~ r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3)) ),
    inference(cnf_transformation,[],[f48])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_24,plain,
    ( m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1738,plain,
    ( m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_21,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_10,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_388,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_21,c_10])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_392,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_388,c_19])).

cnf(c_393,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_392])).

cnf(c_1729,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_393])).

cnf(c_2679,plain,
    ( r1_tarski(k1_relat_1(k6_relat_1(X0)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1738,c_1729])).

cnf(c_20,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_12,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_409,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_20,c_12])).

cnf(c_413,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_409,c_19])).

cnf(c_414,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_413])).

cnf(c_1728,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_414])).

cnf(c_2067,plain,
    ( r1_tarski(k2_relat_1(k6_relat_1(X0)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1738,c_1728])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1749,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2924,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0
    | r1_tarski(X0,k2_relat_1(k6_relat_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2067,c_1749])).

cnf(c_31,plain,
    ( m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_1894,plain,
    ( ~ m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | v1_relat_1(k6_relat_1(X0)) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_1895,plain,
    ( m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1894])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1748,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_relat_1(k6_relat_1(X1),X0) = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_6,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_235,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_6])).

cnf(c_236,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_235])).

cnf(c_278,plain,
    ( ~ r1_tarski(X0,X1)
    | k9_relat_1(k6_relat_1(X1),X0) = X0 ),
    inference(bin_hyper_res,[status(thm)],[c_18,c_236])).

cnf(c_1731,plain,
    ( k9_relat_1(k6_relat_1(X0),X1) = X1
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_278])).

cnf(c_3601,plain,
    ( k9_relat_1(k6_relat_1(X0),X0) = X0 ),
    inference(superposition,[status(thm)],[c_1748,c_1731])).

cnf(c_13,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1744,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3803,plain,
    ( r1_tarski(X0,k2_relat_1(k6_relat_1(X0))) = iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3601,c_1744])).

cnf(c_6813,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2924,c_31,c_1895,c_3803])).

cnf(c_17,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(X1)) = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1742,plain,
    ( k5_relat_1(X0,k6_relat_1(X1)) = X0
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_6838,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(X0)
    | r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6813,c_1742])).

cnf(c_9881,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6838,c_31,c_1895])).

cnf(c_9882,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(X0)
    | r1_tarski(X0,X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_9881])).

cnf(c_9895,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(k6_relat_1(X0))),k6_relat_1(X0)) = k6_relat_1(k1_relat_1(k6_relat_1(X0))) ),
    inference(superposition,[status(thm)],[c_2679,c_9882])).

cnf(c_1741,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2229,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1738,c_1741])).

cnf(c_16,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(X1),X0) = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1743,plain,
    ( k5_relat_1(k6_relat_1(X0),X1) = X1
    | r1_tarski(k1_relat_1(X1),X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3641,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1748,c_1743])).

cnf(c_6595,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(k6_relat_1(X0))),k6_relat_1(X0)) = k6_relat_1(X0) ),
    inference(superposition,[status(thm)],[c_2229,c_3641])).

cnf(c_9915,plain,
    ( k6_relat_1(k1_relat_1(k6_relat_1(X0))) = k6_relat_1(X0) ),
    inference(light_normalisation,[status(thm)],[c_9895,c_6595])).

cnf(c_44385,plain,
    ( k2_relat_1(k6_relat_1(X0)) = k1_relat_1(k6_relat_1(X0)) ),
    inference(superposition,[status(thm)],[c_9915,c_6813])).

cnf(c_44435,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_44385,c_6813])).

cnf(c_26,negated_conjecture,
    ( r1_tarski(k6_relat_1(sK2),sK3) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1736,plain,
    ( r1_tarski(k6_relat_1(sK2),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_15,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_171,plain,
    ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15,c_8,c_6])).

cnf(c_172,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(renaming,[status(thm)],[c_171])).

cnf(c_1734,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_172])).

cnf(c_6507,plain,
    ( k9_relat_1(k6_relat_1(k1_relat_1(X0)),k1_relat_1(X1)) = k1_relat_1(X1)
    | r1_tarski(X1,X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1734,c_1731])).

cnf(c_16768,plain,
    ( k9_relat_1(k6_relat_1(k1_relat_1(sK3)),k1_relat_1(k6_relat_1(sK2))) = k1_relat_1(k6_relat_1(sK2))
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1736,c_6507])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1899,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_3711,plain,
    ( ~ r1_tarski(k1_relat_1(k6_relat_1(sK2)),X0)
    | k9_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(sK2))) = k1_relat_1(k6_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_278])).

cnf(c_4281,plain,
    ( ~ r1_tarski(k1_relat_1(k6_relat_1(sK2)),k1_relat_1(X0))
    | k9_relat_1(k6_relat_1(k1_relat_1(X0)),k1_relat_1(k6_relat_1(sK2))) = k1_relat_1(k6_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_3711])).

cnf(c_4284,plain,
    ( ~ r1_tarski(k1_relat_1(k6_relat_1(sK2)),k1_relat_1(sK3))
    | k9_relat_1(k6_relat_1(k1_relat_1(sK3)),k1_relat_1(k6_relat_1(sK2))) = k1_relat_1(k6_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_4281])).

cnf(c_4282,plain,
    ( ~ r1_tarski(k6_relat_1(sK2),X0)
    | r1_tarski(k1_relat_1(k6_relat_1(sK2)),k1_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_172])).

cnf(c_4288,plain,
    ( ~ r1_tarski(k6_relat_1(sK2),sK3)
    | r1_tarski(k1_relat_1(k6_relat_1(sK2)),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_4282])).

cnf(c_16896,plain,
    ( k9_relat_1(k6_relat_1(k1_relat_1(sK3)),k1_relat_1(k6_relat_1(sK2))) = k1_relat_1(k6_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_16768,c_27,c_26,c_1899,c_4284,c_4288])).

cnf(c_6839,plain,
    ( r1_tarski(k9_relat_1(k6_relat_1(X0),X1),X0) = iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6813,c_1744])).

cnf(c_7533,plain,
    ( r1_tarski(k9_relat_1(k6_relat_1(X0),X1),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6839,c_31,c_1895])).

cnf(c_16904,plain,
    ( r1_tarski(k1_relat_1(k6_relat_1(sK2)),k1_relat_1(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_16896,c_7533])).

cnf(c_45438,plain,
    ( r1_tarski(sK2,k1_relat_1(sK3)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_44435,c_16904])).

cnf(c_14,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_176,plain,
    ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14,c_8,c_6])).

cnf(c_177,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(renaming,[status(thm)],[c_176])).

cnf(c_1733,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_177])).

cnf(c_5325,plain,
    ( k9_relat_1(k6_relat_1(k2_relat_1(X0)),k2_relat_1(X1)) = k2_relat_1(X1)
    | r1_tarski(X1,X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1733,c_1731])).

cnf(c_12723,plain,
    ( k9_relat_1(k6_relat_1(k2_relat_1(sK3)),k2_relat_1(k6_relat_1(sK2))) = k2_relat_1(k6_relat_1(sK2))
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1736,c_5325])).

cnf(c_12772,plain,
    ( k9_relat_1(k6_relat_1(k2_relat_1(sK3)),sK2) = sK2
    | v1_relat_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_12723,c_6813])).

cnf(c_28,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_1900,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1899])).

cnf(c_13779,plain,
    ( k9_relat_1(k6_relat_1(k2_relat_1(sK3)),sK2) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12772,c_28,c_1900])).

cnf(c_13786,plain,
    ( r1_tarski(sK2,k2_relat_1(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_13779,c_7533])).

cnf(c_1735,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1739,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2770,plain,
    ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1735,c_1739])).

cnf(c_25,negated_conjecture,
    ( ~ r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3))
    | ~ r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1737,plain,
    ( r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3)) != iProver_top
    | r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3127,plain,
    ( r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3)) != iProver_top
    | r1_tarski(sK2,k2_relat_1(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2770,c_1737])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1740,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2792,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1735,c_1740])).

cnf(c_3443,plain,
    ( r1_tarski(sK2,k2_relat_1(sK3)) != iProver_top
    | r1_tarski(sK2,k1_relat_1(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3127,c_2792])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_45438,c_13786,c_3443])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:02:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 11.21/2.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.21/2.00  
% 11.21/2.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.21/2.00  
% 11.21/2.00  ------  iProver source info
% 11.21/2.00  
% 11.21/2.00  git: date: 2020-06-30 10:37:57 +0100
% 11.21/2.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.21/2.00  git: non_committed_changes: false
% 11.21/2.00  git: last_make_outside_of_git: false
% 11.21/2.00  
% 11.21/2.00  ------ 
% 11.21/2.00  
% 11.21/2.00  ------ Input Options
% 11.21/2.00  
% 11.21/2.00  --out_options                           all
% 11.21/2.00  --tptp_safe_out                         true
% 11.21/2.00  --problem_path                          ""
% 11.21/2.00  --include_path                          ""
% 11.21/2.00  --clausifier                            res/vclausify_rel
% 11.21/2.00  --clausifier_options                    --mode clausify
% 11.21/2.00  --stdin                                 false
% 11.21/2.00  --stats_out                             all
% 11.21/2.00  
% 11.21/2.00  ------ General Options
% 11.21/2.00  
% 11.21/2.00  --fof                                   false
% 11.21/2.00  --time_out_real                         305.
% 11.21/2.00  --time_out_virtual                      -1.
% 11.21/2.00  --symbol_type_check                     false
% 11.21/2.00  --clausify_out                          false
% 11.21/2.00  --sig_cnt_out                           false
% 11.21/2.00  --trig_cnt_out                          false
% 11.21/2.00  --trig_cnt_out_tolerance                1.
% 11.21/2.00  --trig_cnt_out_sk_spl                   false
% 11.21/2.00  --abstr_cl_out                          false
% 11.21/2.00  
% 11.21/2.00  ------ Global Options
% 11.21/2.00  
% 11.21/2.00  --schedule                              default
% 11.21/2.00  --add_important_lit                     false
% 11.21/2.00  --prop_solver_per_cl                    1000
% 11.21/2.00  --min_unsat_core                        false
% 11.21/2.00  --soft_assumptions                      false
% 11.21/2.00  --soft_lemma_size                       3
% 11.21/2.00  --prop_impl_unit_size                   0
% 11.21/2.00  --prop_impl_unit                        []
% 11.21/2.00  --share_sel_clauses                     true
% 11.21/2.00  --reset_solvers                         false
% 11.21/2.00  --bc_imp_inh                            [conj_cone]
% 11.21/2.00  --conj_cone_tolerance                   3.
% 11.21/2.00  --extra_neg_conj                        none
% 11.21/2.00  --large_theory_mode                     true
% 11.21/2.00  --prolific_symb_bound                   200
% 11.21/2.00  --lt_threshold                          2000
% 11.21/2.00  --clause_weak_htbl                      true
% 11.21/2.00  --gc_record_bc_elim                     false
% 11.21/2.00  
% 11.21/2.00  ------ Preprocessing Options
% 11.21/2.00  
% 11.21/2.00  --preprocessing_flag                    true
% 11.21/2.00  --time_out_prep_mult                    0.1
% 11.21/2.00  --splitting_mode                        input
% 11.21/2.00  --splitting_grd                         true
% 11.21/2.00  --splitting_cvd                         false
% 11.21/2.00  --splitting_cvd_svl                     false
% 11.21/2.00  --splitting_nvd                         32
% 11.21/2.00  --sub_typing                            true
% 11.21/2.00  --prep_gs_sim                           true
% 11.21/2.00  --prep_unflatten                        true
% 11.21/2.00  --prep_res_sim                          true
% 11.21/2.00  --prep_upred                            true
% 11.21/2.00  --prep_sem_filter                       exhaustive
% 11.21/2.00  --prep_sem_filter_out                   false
% 11.21/2.00  --pred_elim                             true
% 11.21/2.00  --res_sim_input                         true
% 11.21/2.00  --eq_ax_congr_red                       true
% 11.21/2.00  --pure_diseq_elim                       true
% 11.21/2.00  --brand_transform                       false
% 11.21/2.00  --non_eq_to_eq                          false
% 11.21/2.00  --prep_def_merge                        true
% 11.21/2.00  --prep_def_merge_prop_impl              false
% 11.21/2.00  --prep_def_merge_mbd                    true
% 11.21/2.00  --prep_def_merge_tr_red                 false
% 11.21/2.00  --prep_def_merge_tr_cl                  false
% 11.21/2.00  --smt_preprocessing                     true
% 11.21/2.00  --smt_ac_axioms                         fast
% 11.21/2.00  --preprocessed_out                      false
% 11.21/2.00  --preprocessed_stats                    false
% 11.21/2.00  
% 11.21/2.00  ------ Abstraction refinement Options
% 11.21/2.00  
% 11.21/2.00  --abstr_ref                             []
% 11.21/2.00  --abstr_ref_prep                        false
% 11.21/2.00  --abstr_ref_until_sat                   false
% 11.21/2.00  --abstr_ref_sig_restrict                funpre
% 11.21/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.21/2.00  --abstr_ref_under                       []
% 11.21/2.00  
% 11.21/2.00  ------ SAT Options
% 11.21/2.00  
% 11.21/2.00  --sat_mode                              false
% 11.21/2.00  --sat_fm_restart_options                ""
% 11.21/2.00  --sat_gr_def                            false
% 11.21/2.00  --sat_epr_types                         true
% 11.21/2.00  --sat_non_cyclic_types                  false
% 11.21/2.00  --sat_finite_models                     false
% 11.21/2.00  --sat_fm_lemmas                         false
% 11.21/2.00  --sat_fm_prep                           false
% 11.21/2.00  --sat_fm_uc_incr                        true
% 11.21/2.00  --sat_out_model                         small
% 11.21/2.00  --sat_out_clauses                       false
% 11.21/2.00  
% 11.21/2.00  ------ QBF Options
% 11.21/2.00  
% 11.21/2.00  --qbf_mode                              false
% 11.21/2.00  --qbf_elim_univ                         false
% 11.21/2.00  --qbf_dom_inst                          none
% 11.21/2.00  --qbf_dom_pre_inst                      false
% 11.21/2.00  --qbf_sk_in                             false
% 11.21/2.00  --qbf_pred_elim                         true
% 11.21/2.00  --qbf_split                             512
% 11.21/2.00  
% 11.21/2.00  ------ BMC1 Options
% 11.21/2.00  
% 11.21/2.00  --bmc1_incremental                      false
% 11.21/2.00  --bmc1_axioms                           reachable_all
% 11.21/2.00  --bmc1_min_bound                        0
% 11.21/2.00  --bmc1_max_bound                        -1
% 11.21/2.00  --bmc1_max_bound_default                -1
% 11.21/2.00  --bmc1_symbol_reachability              true
% 11.21/2.00  --bmc1_property_lemmas                  false
% 11.21/2.00  --bmc1_k_induction                      false
% 11.21/2.00  --bmc1_non_equiv_states                 false
% 11.21/2.00  --bmc1_deadlock                         false
% 11.21/2.00  --bmc1_ucm                              false
% 11.21/2.00  --bmc1_add_unsat_core                   none
% 11.21/2.00  --bmc1_unsat_core_children              false
% 11.21/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.21/2.00  --bmc1_out_stat                         full
% 11.21/2.00  --bmc1_ground_init                      false
% 11.21/2.00  --bmc1_pre_inst_next_state              false
% 11.21/2.00  --bmc1_pre_inst_state                   false
% 11.21/2.00  --bmc1_pre_inst_reach_state             false
% 11.21/2.00  --bmc1_out_unsat_core                   false
% 11.21/2.00  --bmc1_aig_witness_out                  false
% 11.21/2.00  --bmc1_verbose                          false
% 11.21/2.00  --bmc1_dump_clauses_tptp                false
% 11.21/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.21/2.00  --bmc1_dump_file                        -
% 11.21/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.21/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.21/2.00  --bmc1_ucm_extend_mode                  1
% 11.21/2.00  --bmc1_ucm_init_mode                    2
% 11.21/2.00  --bmc1_ucm_cone_mode                    none
% 11.21/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.21/2.00  --bmc1_ucm_relax_model                  4
% 11.21/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.21/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.21/2.00  --bmc1_ucm_layered_model                none
% 11.21/2.00  --bmc1_ucm_max_lemma_size               10
% 11.21/2.00  
% 11.21/2.00  ------ AIG Options
% 11.21/2.00  
% 11.21/2.00  --aig_mode                              false
% 11.21/2.00  
% 11.21/2.00  ------ Instantiation Options
% 11.21/2.00  
% 11.21/2.00  --instantiation_flag                    true
% 11.21/2.00  --inst_sos_flag                         false
% 11.21/2.00  --inst_sos_phase                        true
% 11.21/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.21/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.21/2.00  --inst_lit_sel_side                     num_symb
% 11.21/2.00  --inst_solver_per_active                1400
% 11.21/2.00  --inst_solver_calls_frac                1.
% 11.21/2.00  --inst_passive_queue_type               priority_queues
% 11.21/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.21/2.00  --inst_passive_queues_freq              [25;2]
% 11.21/2.00  --inst_dismatching                      true
% 11.21/2.00  --inst_eager_unprocessed_to_passive     true
% 11.21/2.00  --inst_prop_sim_given                   true
% 11.21/2.00  --inst_prop_sim_new                     false
% 11.21/2.00  --inst_subs_new                         false
% 11.21/2.00  --inst_eq_res_simp                      false
% 11.21/2.00  --inst_subs_given                       false
% 11.21/2.00  --inst_orphan_elimination               true
% 11.21/2.00  --inst_learning_loop_flag               true
% 11.21/2.00  --inst_learning_start                   3000
% 11.21/2.00  --inst_learning_factor                  2
% 11.21/2.00  --inst_start_prop_sim_after_learn       3
% 11.21/2.00  --inst_sel_renew                        solver
% 11.21/2.00  --inst_lit_activity_flag                true
% 11.21/2.00  --inst_restr_to_given                   false
% 11.21/2.00  --inst_activity_threshold               500
% 11.21/2.00  --inst_out_proof                        true
% 11.21/2.00  
% 11.21/2.00  ------ Resolution Options
% 11.21/2.00  
% 11.21/2.00  --resolution_flag                       true
% 11.21/2.00  --res_lit_sel                           adaptive
% 11.21/2.00  --res_lit_sel_side                      none
% 11.21/2.00  --res_ordering                          kbo
% 11.21/2.00  --res_to_prop_solver                    active
% 11.21/2.00  --res_prop_simpl_new                    false
% 11.21/2.00  --res_prop_simpl_given                  true
% 11.21/2.00  --res_passive_queue_type                priority_queues
% 11.21/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.21/2.00  --res_passive_queues_freq               [15;5]
% 11.21/2.00  --res_forward_subs                      full
% 11.21/2.00  --res_backward_subs                     full
% 11.21/2.00  --res_forward_subs_resolution           true
% 11.21/2.00  --res_backward_subs_resolution          true
% 11.21/2.00  --res_orphan_elimination                true
% 11.21/2.00  --res_time_limit                        2.
% 11.21/2.00  --res_out_proof                         true
% 11.21/2.00  
% 11.21/2.00  ------ Superposition Options
% 11.21/2.00  
% 11.21/2.00  --superposition_flag                    true
% 11.21/2.00  --sup_passive_queue_type                priority_queues
% 11.21/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.21/2.00  --sup_passive_queues_freq               [8;1;4]
% 11.21/2.00  --demod_completeness_check              fast
% 11.21/2.00  --demod_use_ground                      true
% 11.21/2.00  --sup_to_prop_solver                    passive
% 11.21/2.00  --sup_prop_simpl_new                    true
% 11.21/2.00  --sup_prop_simpl_given                  true
% 11.21/2.00  --sup_fun_splitting                     false
% 11.21/2.00  --sup_smt_interval                      50000
% 11.21/2.00  
% 11.21/2.00  ------ Superposition Simplification Setup
% 11.21/2.00  
% 11.21/2.00  --sup_indices_passive                   []
% 11.21/2.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.21/2.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.21/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.21/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.21/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.21/2.00  --sup_full_bw                           [BwDemod]
% 11.21/2.00  --sup_immed_triv                        [TrivRules]
% 11.21/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.21/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.21/2.00  --sup_immed_bw_main                     []
% 11.21/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.21/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.21/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.21/2.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.21/2.00  
% 11.21/2.00  ------ Combination Options
% 11.21/2.00  
% 11.21/2.00  --comb_res_mult                         3
% 11.21/2.00  --comb_sup_mult                         2
% 11.21/2.00  --comb_inst_mult                        10
% 11.21/2.00  
% 11.21/2.00  ------ Debug Options
% 11.21/2.00  
% 11.21/2.00  --dbg_backtrace                         false
% 11.21/2.00  --dbg_dump_prop_clauses                 false
% 11.21/2.00  --dbg_dump_prop_clauses_file            -
% 11.21/2.00  --dbg_out_stat                          false
% 11.21/2.00  ------ Parsing...
% 11.21/2.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.21/2.00  
% 11.21/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 11.21/2.00  
% 11.21/2.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.21/2.00  
% 11.21/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.21/2.00  ------ Proving...
% 11.21/2.00  ------ Problem Properties 
% 11.21/2.00  
% 11.21/2.00  
% 11.21/2.00  clauses                                 22
% 11.21/2.00  conjectures                             3
% 11.21/2.00  EPR                                     3
% 11.21/2.00  Horn                                    22
% 11.21/2.00  unary                                   5
% 11.21/2.00  binary                                  11
% 11.21/2.00  lits                                    45
% 11.21/2.00  lits eq                                 6
% 11.21/2.00  fd_pure                                 0
% 11.21/2.00  fd_pseudo                               0
% 11.21/2.00  fd_cond                                 0
% 11.21/2.00  fd_pseudo_cond                          1
% 11.21/2.00  AC symbols                              0
% 11.21/2.00  
% 11.21/2.00  ------ Schedule dynamic 5 is on 
% 11.21/2.00  
% 11.21/2.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.21/2.00  
% 11.21/2.00  
% 11.21/2.00  ------ 
% 11.21/2.00  Current options:
% 11.21/2.00  ------ 
% 11.21/2.00  
% 11.21/2.00  ------ Input Options
% 11.21/2.00  
% 11.21/2.00  --out_options                           all
% 11.21/2.00  --tptp_safe_out                         true
% 11.21/2.00  --problem_path                          ""
% 11.21/2.00  --include_path                          ""
% 11.21/2.00  --clausifier                            res/vclausify_rel
% 11.21/2.00  --clausifier_options                    --mode clausify
% 11.21/2.00  --stdin                                 false
% 11.21/2.00  --stats_out                             all
% 11.21/2.00  
% 11.21/2.00  ------ General Options
% 11.21/2.00  
% 11.21/2.00  --fof                                   false
% 11.21/2.00  --time_out_real                         305.
% 11.21/2.00  --time_out_virtual                      -1.
% 11.21/2.00  --symbol_type_check                     false
% 11.21/2.00  --clausify_out                          false
% 11.21/2.00  --sig_cnt_out                           false
% 11.21/2.00  --trig_cnt_out                          false
% 11.21/2.00  --trig_cnt_out_tolerance                1.
% 11.21/2.00  --trig_cnt_out_sk_spl                   false
% 11.21/2.00  --abstr_cl_out                          false
% 11.21/2.00  
% 11.21/2.00  ------ Global Options
% 11.21/2.00  
% 11.21/2.00  --schedule                              default
% 11.21/2.00  --add_important_lit                     false
% 11.21/2.00  --prop_solver_per_cl                    1000
% 11.21/2.00  --min_unsat_core                        false
% 11.21/2.00  --soft_assumptions                      false
% 11.21/2.00  --soft_lemma_size                       3
% 11.21/2.00  --prop_impl_unit_size                   0
% 11.21/2.00  --prop_impl_unit                        []
% 11.21/2.00  --share_sel_clauses                     true
% 11.21/2.00  --reset_solvers                         false
% 11.21/2.00  --bc_imp_inh                            [conj_cone]
% 11.21/2.00  --conj_cone_tolerance                   3.
% 11.21/2.00  --extra_neg_conj                        none
% 11.21/2.00  --large_theory_mode                     true
% 11.21/2.00  --prolific_symb_bound                   200
% 11.21/2.00  --lt_threshold                          2000
% 11.21/2.00  --clause_weak_htbl                      true
% 11.21/2.00  --gc_record_bc_elim                     false
% 11.21/2.00  
% 11.21/2.00  ------ Preprocessing Options
% 11.21/2.00  
% 11.21/2.00  --preprocessing_flag                    true
% 11.21/2.00  --time_out_prep_mult                    0.1
% 11.21/2.00  --splitting_mode                        input
% 11.21/2.00  --splitting_grd                         true
% 11.21/2.00  --splitting_cvd                         false
% 11.21/2.00  --splitting_cvd_svl                     false
% 11.21/2.00  --splitting_nvd                         32
% 11.21/2.00  --sub_typing                            true
% 11.21/2.00  --prep_gs_sim                           true
% 11.21/2.00  --prep_unflatten                        true
% 11.21/2.00  --prep_res_sim                          true
% 11.21/2.00  --prep_upred                            true
% 11.21/2.00  --prep_sem_filter                       exhaustive
% 11.21/2.00  --prep_sem_filter_out                   false
% 11.21/2.00  --pred_elim                             true
% 11.21/2.00  --res_sim_input                         true
% 11.21/2.00  --eq_ax_congr_red                       true
% 11.21/2.00  --pure_diseq_elim                       true
% 11.21/2.00  --brand_transform                       false
% 11.21/2.00  --non_eq_to_eq                          false
% 11.21/2.00  --prep_def_merge                        true
% 11.21/2.00  --prep_def_merge_prop_impl              false
% 11.21/2.00  --prep_def_merge_mbd                    true
% 11.21/2.00  --prep_def_merge_tr_red                 false
% 11.21/2.00  --prep_def_merge_tr_cl                  false
% 11.21/2.00  --smt_preprocessing                     true
% 11.21/2.00  --smt_ac_axioms                         fast
% 11.21/2.00  --preprocessed_out                      false
% 11.21/2.00  --preprocessed_stats                    false
% 11.21/2.00  
% 11.21/2.00  ------ Abstraction refinement Options
% 11.21/2.00  
% 11.21/2.00  --abstr_ref                             []
% 11.21/2.00  --abstr_ref_prep                        false
% 11.21/2.00  --abstr_ref_until_sat                   false
% 11.21/2.00  --abstr_ref_sig_restrict                funpre
% 11.21/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.21/2.00  --abstr_ref_under                       []
% 11.21/2.00  
% 11.21/2.00  ------ SAT Options
% 11.21/2.00  
% 11.21/2.00  --sat_mode                              false
% 11.21/2.00  --sat_fm_restart_options                ""
% 11.21/2.00  --sat_gr_def                            false
% 11.21/2.00  --sat_epr_types                         true
% 11.21/2.00  --sat_non_cyclic_types                  false
% 11.21/2.00  --sat_finite_models                     false
% 11.21/2.00  --sat_fm_lemmas                         false
% 11.21/2.00  --sat_fm_prep                           false
% 11.21/2.00  --sat_fm_uc_incr                        true
% 11.21/2.00  --sat_out_model                         small
% 11.21/2.00  --sat_out_clauses                       false
% 11.21/2.00  
% 11.21/2.00  ------ QBF Options
% 11.21/2.00  
% 11.21/2.00  --qbf_mode                              false
% 11.21/2.00  --qbf_elim_univ                         false
% 11.21/2.00  --qbf_dom_inst                          none
% 11.21/2.00  --qbf_dom_pre_inst                      false
% 11.21/2.00  --qbf_sk_in                             false
% 11.21/2.00  --qbf_pred_elim                         true
% 11.21/2.00  --qbf_split                             512
% 11.21/2.00  
% 11.21/2.00  ------ BMC1 Options
% 11.21/2.00  
% 11.21/2.00  --bmc1_incremental                      false
% 11.21/2.00  --bmc1_axioms                           reachable_all
% 11.21/2.00  --bmc1_min_bound                        0
% 11.21/2.00  --bmc1_max_bound                        -1
% 11.21/2.00  --bmc1_max_bound_default                -1
% 11.21/2.00  --bmc1_symbol_reachability              true
% 11.21/2.00  --bmc1_property_lemmas                  false
% 11.21/2.00  --bmc1_k_induction                      false
% 11.21/2.00  --bmc1_non_equiv_states                 false
% 11.21/2.00  --bmc1_deadlock                         false
% 11.21/2.00  --bmc1_ucm                              false
% 11.21/2.00  --bmc1_add_unsat_core                   none
% 11.21/2.00  --bmc1_unsat_core_children              false
% 11.21/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.21/2.00  --bmc1_out_stat                         full
% 11.21/2.00  --bmc1_ground_init                      false
% 11.21/2.00  --bmc1_pre_inst_next_state              false
% 11.21/2.00  --bmc1_pre_inst_state                   false
% 11.21/2.00  --bmc1_pre_inst_reach_state             false
% 11.21/2.00  --bmc1_out_unsat_core                   false
% 11.21/2.00  --bmc1_aig_witness_out                  false
% 11.21/2.00  --bmc1_verbose                          false
% 11.21/2.00  --bmc1_dump_clauses_tptp                false
% 11.21/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.21/2.00  --bmc1_dump_file                        -
% 11.21/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.21/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.21/2.00  --bmc1_ucm_extend_mode                  1
% 11.21/2.00  --bmc1_ucm_init_mode                    2
% 11.21/2.00  --bmc1_ucm_cone_mode                    none
% 11.21/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.21/2.00  --bmc1_ucm_relax_model                  4
% 11.21/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.21/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.21/2.00  --bmc1_ucm_layered_model                none
% 11.21/2.00  --bmc1_ucm_max_lemma_size               10
% 11.21/2.00  
% 11.21/2.00  ------ AIG Options
% 11.21/2.00  
% 11.21/2.00  --aig_mode                              false
% 11.21/2.00  
% 11.21/2.00  ------ Instantiation Options
% 11.21/2.00  
% 11.21/2.00  --instantiation_flag                    true
% 11.21/2.00  --inst_sos_flag                         false
% 11.21/2.00  --inst_sos_phase                        true
% 11.21/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.21/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.21/2.00  --inst_lit_sel_side                     none
% 11.21/2.00  --inst_solver_per_active                1400
% 11.21/2.00  --inst_solver_calls_frac                1.
% 11.21/2.00  --inst_passive_queue_type               priority_queues
% 11.21/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.21/2.00  --inst_passive_queues_freq              [25;2]
% 11.21/2.00  --inst_dismatching                      true
% 11.21/2.00  --inst_eager_unprocessed_to_passive     true
% 11.21/2.00  --inst_prop_sim_given                   true
% 11.21/2.00  --inst_prop_sim_new                     false
% 11.21/2.00  --inst_subs_new                         false
% 11.21/2.00  --inst_eq_res_simp                      false
% 11.21/2.00  --inst_subs_given                       false
% 11.21/2.00  --inst_orphan_elimination               true
% 11.21/2.00  --inst_learning_loop_flag               true
% 11.21/2.00  --inst_learning_start                   3000
% 11.21/2.00  --inst_learning_factor                  2
% 11.21/2.00  --inst_start_prop_sim_after_learn       3
% 11.21/2.00  --inst_sel_renew                        solver
% 11.21/2.00  --inst_lit_activity_flag                true
% 11.21/2.00  --inst_restr_to_given                   false
% 11.21/2.00  --inst_activity_threshold               500
% 11.21/2.00  --inst_out_proof                        true
% 11.21/2.00  
% 11.21/2.00  ------ Resolution Options
% 11.21/2.00  
% 11.21/2.00  --resolution_flag                       false
% 11.21/2.00  --res_lit_sel                           adaptive
% 11.21/2.00  --res_lit_sel_side                      none
% 11.21/2.00  --res_ordering                          kbo
% 11.21/2.00  --res_to_prop_solver                    active
% 11.21/2.00  --res_prop_simpl_new                    false
% 11.21/2.00  --res_prop_simpl_given                  true
% 11.21/2.00  --res_passive_queue_type                priority_queues
% 11.21/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.21/2.00  --res_passive_queues_freq               [15;5]
% 11.21/2.00  --res_forward_subs                      full
% 11.21/2.00  --res_backward_subs                     full
% 11.21/2.00  --res_forward_subs_resolution           true
% 11.21/2.00  --res_backward_subs_resolution          true
% 11.21/2.00  --res_orphan_elimination                true
% 11.21/2.00  --res_time_limit                        2.
% 11.21/2.00  --res_out_proof                         true
% 11.21/2.00  
% 11.21/2.00  ------ Superposition Options
% 11.21/2.00  
% 11.21/2.00  --superposition_flag                    true
% 11.21/2.00  --sup_passive_queue_type                priority_queues
% 11.21/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.21/2.00  --sup_passive_queues_freq               [8;1;4]
% 11.21/2.00  --demod_completeness_check              fast
% 11.21/2.00  --demod_use_ground                      true
% 11.21/2.00  --sup_to_prop_solver                    passive
% 11.21/2.00  --sup_prop_simpl_new                    true
% 11.21/2.00  --sup_prop_simpl_given                  true
% 11.21/2.00  --sup_fun_splitting                     false
% 11.21/2.00  --sup_smt_interval                      50000
% 11.21/2.00  
% 11.21/2.00  ------ Superposition Simplification Setup
% 11.21/2.00  
% 11.21/2.00  --sup_indices_passive                   []
% 11.21/2.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.21/2.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.21/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.21/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.21/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.21/2.00  --sup_full_bw                           [BwDemod]
% 11.21/2.00  --sup_immed_triv                        [TrivRules]
% 11.21/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.21/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.21/2.00  --sup_immed_bw_main                     []
% 11.21/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.21/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.21/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.21/2.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.21/2.00  
% 11.21/2.00  ------ Combination Options
% 11.21/2.00  
% 11.21/2.00  --comb_res_mult                         3
% 11.21/2.00  --comb_sup_mult                         2
% 11.21/2.00  --comb_inst_mult                        10
% 11.21/2.00  
% 11.21/2.00  ------ Debug Options
% 11.21/2.00  
% 11.21/2.00  --dbg_backtrace                         false
% 11.21/2.00  --dbg_dump_prop_clauses                 false
% 11.21/2.00  --dbg_dump_prop_clauses_file            -
% 11.21/2.00  --dbg_out_stat                          false
% 11.21/2.00  
% 11.21/2.00  
% 11.21/2.00  
% 11.21/2.00  
% 11.21/2.00  ------ Proving...
% 11.21/2.00  
% 11.21/2.00  
% 11.21/2.00  % SZS status Theorem for theBenchmark.p
% 11.21/2.00  
% 11.21/2.00  % SZS output start CNFRefutation for theBenchmark.p
% 11.21/2.00  
% 11.21/2.00  fof(f19,axiom,(
% 11.21/2.00    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 11.21/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.21/2.00  
% 11.21/2.00  fof(f73,plain,(
% 11.21/2.00    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 11.21/2.00    inference(cnf_transformation,[],[f19])).
% 11.21/2.00  
% 11.21/2.00  fof(f16,axiom,(
% 11.21/2.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 11.21/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.21/2.00  
% 11.21/2.00  fof(f37,plain,(
% 11.21/2.00    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.21/2.00    inference(ennf_transformation,[],[f16])).
% 11.21/2.00  
% 11.21/2.00  fof(f69,plain,(
% 11.21/2.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.21/2.00    inference(cnf_transformation,[],[f37])).
% 11.21/2.00  
% 11.21/2.00  fof(f8,axiom,(
% 11.21/2.00    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 11.21/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.21/2.00  
% 11.21/2.00  fof(f26,plain,(
% 11.21/2.00    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 11.21/2.00    inference(ennf_transformation,[],[f8])).
% 11.21/2.00  
% 11.21/2.00  fof(f45,plain,(
% 11.21/2.00    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 11.21/2.00    inference(nnf_transformation,[],[f26])).
% 11.21/2.00  
% 11.21/2.00  fof(f58,plain,(
% 11.21/2.00    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 11.21/2.00    inference(cnf_transformation,[],[f45])).
% 11.21/2.00  
% 11.21/2.00  fof(f15,axiom,(
% 11.21/2.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 11.21/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.21/2.00  
% 11.21/2.00  fof(f36,plain,(
% 11.21/2.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.21/2.00    inference(ennf_transformation,[],[f15])).
% 11.21/2.00  
% 11.21/2.00  fof(f68,plain,(
% 11.21/2.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.21/2.00    inference(cnf_transformation,[],[f36])).
% 11.21/2.00  
% 11.21/2.00  fof(f70,plain,(
% 11.21/2.00    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.21/2.00    inference(cnf_transformation,[],[f37])).
% 11.21/2.00  
% 11.21/2.00  fof(f9,axiom,(
% 11.21/2.00    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 11.21/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.21/2.00  
% 11.21/2.00  fof(f27,plain,(
% 11.21/2.00    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 11.21/2.00    inference(ennf_transformation,[],[f9])).
% 11.21/2.00  
% 11.21/2.00  fof(f46,plain,(
% 11.21/2.00    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 11.21/2.00    inference(nnf_transformation,[],[f27])).
% 11.21/2.00  
% 11.21/2.00  fof(f60,plain,(
% 11.21/2.00    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 11.21/2.00    inference(cnf_transformation,[],[f46])).
% 11.21/2.00  
% 11.21/2.00  fof(f2,axiom,(
% 11.21/2.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.21/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.21/2.00  
% 11.21/2.00  fof(f42,plain,(
% 11.21/2.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.21/2.00    inference(nnf_transformation,[],[f2])).
% 11.21/2.00  
% 11.21/2.00  fof(f43,plain,(
% 11.21/2.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.21/2.00    inference(flattening,[],[f42])).
% 11.21/2.00  
% 11.21/2.00  fof(f51,plain,(
% 11.21/2.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 11.21/2.00    inference(cnf_transformation,[],[f43])).
% 11.21/2.00  
% 11.21/2.00  fof(f49,plain,(
% 11.21/2.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 11.21/2.00    inference(cnf_transformation,[],[f43])).
% 11.21/2.00  
% 11.21/2.00  fof(f78,plain,(
% 11.21/2.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 11.21/2.00    inference(equality_resolution,[],[f49])).
% 11.21/2.00  
% 11.21/2.00  fof(f14,axiom,(
% 11.21/2.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k9_relat_1(k6_relat_1(X0),X1) = X1)),
% 11.21/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.21/2.00  
% 11.21/2.00  fof(f35,plain,(
% 11.21/2.00    ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.21/2.00    inference(ennf_transformation,[],[f14])).
% 11.21/2.00  
% 11.21/2.00  fof(f67,plain,(
% 11.21/2.00    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.21/2.00    inference(cnf_transformation,[],[f35])).
% 11.21/2.00  
% 11.21/2.00  fof(f6,axiom,(
% 11.21/2.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 11.21/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.21/2.00  
% 11.21/2.00  fof(f44,plain,(
% 11.21/2.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 11.21/2.00    inference(nnf_transformation,[],[f6])).
% 11.21/2.00  
% 11.21/2.00  fof(f56,plain,(
% 11.21/2.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 11.21/2.00    inference(cnf_transformation,[],[f44])).
% 11.21/2.00  
% 11.21/2.00  fof(f10,axiom,(
% 11.21/2.00    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 11.21/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.21/2.00  
% 11.21/2.00  fof(f28,plain,(
% 11.21/2.00    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 11.21/2.00    inference(ennf_transformation,[],[f10])).
% 11.21/2.00  
% 11.21/2.00  fof(f62,plain,(
% 11.21/2.00    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 11.21/2.00    inference(cnf_transformation,[],[f28])).
% 11.21/2.00  
% 11.21/2.00  fof(f13,axiom,(
% 11.21/2.00    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 11.21/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.21/2.00  
% 11.21/2.00  fof(f33,plain,(
% 11.21/2.00    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 11.21/2.00    inference(ennf_transformation,[],[f13])).
% 11.21/2.00  
% 11.21/2.00  fof(f34,plain,(
% 11.21/2.00    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 11.21/2.00    inference(flattening,[],[f33])).
% 11.21/2.00  
% 11.21/2.00  fof(f66,plain,(
% 11.21/2.00    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 11.21/2.00    inference(cnf_transformation,[],[f34])).
% 11.21/2.00  
% 11.21/2.00  fof(f12,axiom,(
% 11.21/2.00    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 11.21/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.21/2.00  
% 11.21/2.00  fof(f31,plain,(
% 11.21/2.00    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 11.21/2.00    inference(ennf_transformation,[],[f12])).
% 11.21/2.00  
% 11.21/2.00  fof(f32,plain,(
% 11.21/2.00    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 11.21/2.00    inference(flattening,[],[f31])).
% 11.21/2.00  
% 11.21/2.00  fof(f65,plain,(
% 11.21/2.00    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 11.21/2.00    inference(cnf_transformation,[],[f32])).
% 11.21/2.00  
% 11.21/2.00  fof(f20,conjecture,(
% 11.21/2.00    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(k6_relat_1(X2),X3) => (r1_tarski(X2,k2_relset_1(X0,X1,X3)) & r1_tarski(X2,k1_relset_1(X0,X1,X3)))))),
% 11.21/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.21/2.00  
% 11.21/2.00  fof(f21,negated_conjecture,(
% 11.21/2.00    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(k6_relat_1(X2),X3) => (r1_tarski(X2,k2_relset_1(X0,X1,X3)) & r1_tarski(X2,k1_relset_1(X0,X1,X3)))))),
% 11.21/2.00    inference(negated_conjecture,[],[f20])).
% 11.21/2.00  
% 11.21/2.00  fof(f40,plain,(
% 11.21/2.00    ? [X0,X1,X2,X3] : (((~r1_tarski(X2,k2_relset_1(X0,X1,X3)) | ~r1_tarski(X2,k1_relset_1(X0,X1,X3))) & r1_tarski(k6_relat_1(X2),X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.21/2.00    inference(ennf_transformation,[],[f21])).
% 11.21/2.00  
% 11.21/2.00  fof(f41,plain,(
% 11.21/2.00    ? [X0,X1,X2,X3] : ((~r1_tarski(X2,k2_relset_1(X0,X1,X3)) | ~r1_tarski(X2,k1_relset_1(X0,X1,X3))) & r1_tarski(k6_relat_1(X2),X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.21/2.00    inference(flattening,[],[f40])).
% 11.21/2.00  
% 11.21/2.00  fof(f47,plain,(
% 11.21/2.00    ? [X0,X1,X2,X3] : ((~r1_tarski(X2,k2_relset_1(X0,X1,X3)) | ~r1_tarski(X2,k1_relset_1(X0,X1,X3))) & r1_tarski(k6_relat_1(X2),X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => ((~r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3)) | ~r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3))) & r1_tarski(k6_relat_1(sK2),sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 11.21/2.00    introduced(choice_axiom,[])).
% 11.21/2.00  
% 11.21/2.00  fof(f48,plain,(
% 11.21/2.00    (~r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3)) | ~r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3))) & r1_tarski(k6_relat_1(sK2),sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 11.21/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f41,f47])).
% 11.21/2.00  
% 11.21/2.00  fof(f75,plain,(
% 11.21/2.00    r1_tarski(k6_relat_1(sK2),sK3)),
% 11.21/2.00    inference(cnf_transformation,[],[f48])).
% 11.21/2.00  
% 11.21/2.00  fof(f11,axiom,(
% 11.21/2.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 11.21/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.21/2.00  
% 11.21/2.00  fof(f29,plain,(
% 11.21/2.00    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 11.21/2.00    inference(ennf_transformation,[],[f11])).
% 11.21/2.00  
% 11.21/2.00  fof(f30,plain,(
% 11.21/2.00    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 11.21/2.00    inference(flattening,[],[f29])).
% 11.21/2.00  
% 11.21/2.00  fof(f63,plain,(
% 11.21/2.00    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 11.21/2.00    inference(cnf_transformation,[],[f30])).
% 11.21/2.00  
% 11.21/2.00  fof(f7,axiom,(
% 11.21/2.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 11.21/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.21/2.00  
% 11.21/2.00  fof(f25,plain,(
% 11.21/2.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 11.21/2.00    inference(ennf_transformation,[],[f7])).
% 11.21/2.00  
% 11.21/2.00  fof(f57,plain,(
% 11.21/2.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 11.21/2.00    inference(cnf_transformation,[],[f25])).
% 11.21/2.00  
% 11.21/2.00  fof(f74,plain,(
% 11.21/2.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 11.21/2.00    inference(cnf_transformation,[],[f48])).
% 11.21/2.00  
% 11.21/2.00  fof(f64,plain,(
% 11.21/2.00    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 11.21/2.00    inference(cnf_transformation,[],[f30])).
% 11.21/2.00  
% 11.21/2.00  fof(f18,axiom,(
% 11.21/2.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 11.21/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.21/2.00  
% 11.21/2.00  fof(f39,plain,(
% 11.21/2.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.21/2.00    inference(ennf_transformation,[],[f18])).
% 11.21/2.00  
% 11.21/2.00  fof(f72,plain,(
% 11.21/2.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.21/2.00    inference(cnf_transformation,[],[f39])).
% 11.21/2.00  
% 11.21/2.00  fof(f76,plain,(
% 11.21/2.00    ~r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3)) | ~r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3))),
% 11.21/2.00    inference(cnf_transformation,[],[f48])).
% 11.21/2.00  
% 11.21/2.00  fof(f17,axiom,(
% 11.21/2.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 11.21/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.21/2.00  
% 11.21/2.00  fof(f38,plain,(
% 11.21/2.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.21/2.00    inference(ennf_transformation,[],[f17])).
% 11.21/2.00  
% 11.21/2.00  fof(f71,plain,(
% 11.21/2.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.21/2.00    inference(cnf_transformation,[],[f38])).
% 11.21/2.00  
% 11.21/2.00  cnf(c_24,plain,
% 11.21/2.00      ( m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 11.21/2.00      inference(cnf_transformation,[],[f73]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_1738,plain,
% 11.21/2.00      ( m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 11.21/2.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_21,plain,
% 11.21/2.00      ( v4_relat_1(X0,X1)
% 11.21/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 11.21/2.00      inference(cnf_transformation,[],[f69]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_10,plain,
% 11.21/2.00      ( ~ v4_relat_1(X0,X1)
% 11.21/2.00      | r1_tarski(k1_relat_1(X0),X1)
% 11.21/2.00      | ~ v1_relat_1(X0) ),
% 11.21/2.00      inference(cnf_transformation,[],[f58]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_388,plain,
% 11.21/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.21/2.00      | r1_tarski(k1_relat_1(X0),X1)
% 11.21/2.00      | ~ v1_relat_1(X0) ),
% 11.21/2.00      inference(resolution,[status(thm)],[c_21,c_10]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_19,plain,
% 11.21/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.21/2.00      | v1_relat_1(X0) ),
% 11.21/2.00      inference(cnf_transformation,[],[f68]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_392,plain,
% 11.21/2.00      ( r1_tarski(k1_relat_1(X0),X1)
% 11.21/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 11.21/2.00      inference(global_propositional_subsumption,
% 11.21/2.00                [status(thm)],
% 11.21/2.00                [c_388,c_19]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_393,plain,
% 11.21/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.21/2.00      | r1_tarski(k1_relat_1(X0),X1) ),
% 11.21/2.00      inference(renaming,[status(thm)],[c_392]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_1729,plain,
% 11.21/2.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 11.21/2.00      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 11.21/2.00      inference(predicate_to_equality,[status(thm)],[c_393]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_2679,plain,
% 11.21/2.00      ( r1_tarski(k1_relat_1(k6_relat_1(X0)),X0) = iProver_top ),
% 11.21/2.00      inference(superposition,[status(thm)],[c_1738,c_1729]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_20,plain,
% 11.21/2.00      ( v5_relat_1(X0,X1)
% 11.21/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 11.21/2.00      inference(cnf_transformation,[],[f70]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_12,plain,
% 11.21/2.00      ( ~ v5_relat_1(X0,X1)
% 11.21/2.00      | r1_tarski(k2_relat_1(X0),X1)
% 11.21/2.00      | ~ v1_relat_1(X0) ),
% 11.21/2.00      inference(cnf_transformation,[],[f60]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_409,plain,
% 11.21/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.21/2.00      | r1_tarski(k2_relat_1(X0),X2)
% 11.21/2.00      | ~ v1_relat_1(X0) ),
% 11.21/2.00      inference(resolution,[status(thm)],[c_20,c_12]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_413,plain,
% 11.21/2.00      ( r1_tarski(k2_relat_1(X0),X2)
% 11.21/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 11.21/2.00      inference(global_propositional_subsumption,
% 11.21/2.00                [status(thm)],
% 11.21/2.00                [c_409,c_19]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_414,plain,
% 11.21/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.21/2.00      | r1_tarski(k2_relat_1(X0),X2) ),
% 11.21/2.00      inference(renaming,[status(thm)],[c_413]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_1728,plain,
% 11.21/2.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 11.21/2.00      | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
% 11.21/2.00      inference(predicate_to_equality,[status(thm)],[c_414]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_2067,plain,
% 11.21/2.00      ( r1_tarski(k2_relat_1(k6_relat_1(X0)),X0) = iProver_top ),
% 11.21/2.00      inference(superposition,[status(thm)],[c_1738,c_1728]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_0,plain,
% 11.21/2.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 11.21/2.00      inference(cnf_transformation,[],[f51]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_1749,plain,
% 11.21/2.00      ( X0 = X1
% 11.21/2.00      | r1_tarski(X0,X1) != iProver_top
% 11.21/2.00      | r1_tarski(X1,X0) != iProver_top ),
% 11.21/2.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_2924,plain,
% 11.21/2.00      ( k2_relat_1(k6_relat_1(X0)) = X0
% 11.21/2.00      | r1_tarski(X0,k2_relat_1(k6_relat_1(X0))) != iProver_top ),
% 11.21/2.00      inference(superposition,[status(thm)],[c_2067,c_1749]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_31,plain,
% 11.21/2.00      ( m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 11.21/2.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_1894,plain,
% 11.21/2.00      ( ~ m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 11.21/2.00      | v1_relat_1(k6_relat_1(X0)) ),
% 11.21/2.00      inference(instantiation,[status(thm)],[c_19]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_1895,plain,
% 11.21/2.00      ( m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 11.21/2.00      | v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 11.21/2.00      inference(predicate_to_equality,[status(thm)],[c_1894]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_2,plain,
% 11.21/2.00      ( r1_tarski(X0,X0) ),
% 11.21/2.00      inference(cnf_transformation,[],[f78]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_1748,plain,
% 11.21/2.00      ( r1_tarski(X0,X0) = iProver_top ),
% 11.21/2.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_18,plain,
% 11.21/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.21/2.00      | k9_relat_1(k6_relat_1(X1),X0) = X0 ),
% 11.21/2.00      inference(cnf_transformation,[],[f67]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_6,plain,
% 11.21/2.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 11.21/2.00      inference(cnf_transformation,[],[f56]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_235,plain,
% 11.21/2.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 11.21/2.00      inference(prop_impl,[status(thm)],[c_6]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_236,plain,
% 11.21/2.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 11.21/2.00      inference(renaming,[status(thm)],[c_235]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_278,plain,
% 11.21/2.00      ( ~ r1_tarski(X0,X1) | k9_relat_1(k6_relat_1(X1),X0) = X0 ),
% 11.21/2.00      inference(bin_hyper_res,[status(thm)],[c_18,c_236]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_1731,plain,
% 11.21/2.00      ( k9_relat_1(k6_relat_1(X0),X1) = X1
% 11.21/2.00      | r1_tarski(X1,X0) != iProver_top ),
% 11.21/2.00      inference(predicate_to_equality,[status(thm)],[c_278]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_3601,plain,
% 11.21/2.00      ( k9_relat_1(k6_relat_1(X0),X0) = X0 ),
% 11.21/2.00      inference(superposition,[status(thm)],[c_1748,c_1731]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_13,plain,
% 11.21/2.00      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 11.21/2.00      inference(cnf_transformation,[],[f62]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_1744,plain,
% 11.21/2.00      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) = iProver_top
% 11.21/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.21/2.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_3803,plain,
% 11.21/2.00      ( r1_tarski(X0,k2_relat_1(k6_relat_1(X0))) = iProver_top
% 11.21/2.00      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 11.21/2.00      inference(superposition,[status(thm)],[c_3601,c_1744]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_6813,plain,
% 11.21/2.00      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 11.21/2.00      inference(global_propositional_subsumption,
% 11.21/2.00                [status(thm)],
% 11.21/2.00                [c_2924,c_31,c_1895,c_3803]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_17,plain,
% 11.21/2.00      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 11.21/2.00      | ~ v1_relat_1(X0)
% 11.21/2.00      | k5_relat_1(X0,k6_relat_1(X1)) = X0 ),
% 11.21/2.00      inference(cnf_transformation,[],[f66]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_1742,plain,
% 11.21/2.00      ( k5_relat_1(X0,k6_relat_1(X1)) = X0
% 11.21/2.00      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 11.21/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.21/2.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_6838,plain,
% 11.21/2.00      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(X0)
% 11.21/2.00      | r1_tarski(X0,X1) != iProver_top
% 11.21/2.00      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 11.21/2.00      inference(superposition,[status(thm)],[c_6813,c_1742]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_9881,plain,
% 11.21/2.00      ( r1_tarski(X0,X1) != iProver_top
% 11.21/2.00      | k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(X0) ),
% 11.21/2.00      inference(global_propositional_subsumption,
% 11.21/2.00                [status(thm)],
% 11.21/2.00                [c_6838,c_31,c_1895]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_9882,plain,
% 11.21/2.00      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(X0)
% 11.21/2.00      | r1_tarski(X0,X1) != iProver_top ),
% 11.21/2.00      inference(renaming,[status(thm)],[c_9881]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_9895,plain,
% 11.21/2.00      ( k5_relat_1(k6_relat_1(k1_relat_1(k6_relat_1(X0))),k6_relat_1(X0)) = k6_relat_1(k1_relat_1(k6_relat_1(X0))) ),
% 11.21/2.00      inference(superposition,[status(thm)],[c_2679,c_9882]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_1741,plain,
% 11.21/2.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 11.21/2.00      | v1_relat_1(X0) = iProver_top ),
% 11.21/2.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_2229,plain,
% 11.21/2.00      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 11.21/2.00      inference(superposition,[status(thm)],[c_1738,c_1741]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_16,plain,
% 11.21/2.00      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 11.21/2.00      | ~ v1_relat_1(X0)
% 11.21/2.00      | k5_relat_1(k6_relat_1(X1),X0) = X0 ),
% 11.21/2.00      inference(cnf_transformation,[],[f65]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_1743,plain,
% 11.21/2.00      ( k5_relat_1(k6_relat_1(X0),X1) = X1
% 11.21/2.00      | r1_tarski(k1_relat_1(X1),X0) != iProver_top
% 11.21/2.00      | v1_relat_1(X1) != iProver_top ),
% 11.21/2.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_3641,plain,
% 11.21/2.00      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
% 11.21/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.21/2.00      inference(superposition,[status(thm)],[c_1748,c_1743]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_6595,plain,
% 11.21/2.00      ( k5_relat_1(k6_relat_1(k1_relat_1(k6_relat_1(X0))),k6_relat_1(X0)) = k6_relat_1(X0) ),
% 11.21/2.00      inference(superposition,[status(thm)],[c_2229,c_3641]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_9915,plain,
% 11.21/2.00      ( k6_relat_1(k1_relat_1(k6_relat_1(X0))) = k6_relat_1(X0) ),
% 11.21/2.00      inference(light_normalisation,[status(thm)],[c_9895,c_6595]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_44385,plain,
% 11.21/2.00      ( k2_relat_1(k6_relat_1(X0)) = k1_relat_1(k6_relat_1(X0)) ),
% 11.21/2.00      inference(superposition,[status(thm)],[c_9915,c_6813]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_44435,plain,
% 11.21/2.00      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 11.21/2.00      inference(light_normalisation,[status(thm)],[c_44385,c_6813]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_26,negated_conjecture,
% 11.21/2.00      ( r1_tarski(k6_relat_1(sK2),sK3) ),
% 11.21/2.00      inference(cnf_transformation,[],[f75]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_1736,plain,
% 11.21/2.00      ( r1_tarski(k6_relat_1(sK2),sK3) = iProver_top ),
% 11.21/2.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_15,plain,
% 11.21/2.00      ( ~ r1_tarski(X0,X1)
% 11.21/2.00      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 11.21/2.00      | ~ v1_relat_1(X0)
% 11.21/2.00      | ~ v1_relat_1(X1) ),
% 11.21/2.00      inference(cnf_transformation,[],[f63]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_8,plain,
% 11.21/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.21/2.00      | ~ v1_relat_1(X1)
% 11.21/2.00      | v1_relat_1(X0) ),
% 11.21/2.00      inference(cnf_transformation,[],[f57]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_171,plain,
% 11.21/2.00      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 11.21/2.00      | ~ r1_tarski(X0,X1)
% 11.21/2.00      | ~ v1_relat_1(X1) ),
% 11.21/2.00      inference(global_propositional_subsumption,
% 11.21/2.00                [status(thm)],
% 11.21/2.00                [c_15,c_8,c_6]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_172,plain,
% 11.21/2.00      ( ~ r1_tarski(X0,X1)
% 11.21/2.00      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 11.21/2.00      | ~ v1_relat_1(X1) ),
% 11.21/2.00      inference(renaming,[status(thm)],[c_171]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_1734,plain,
% 11.21/2.00      ( r1_tarski(X0,X1) != iProver_top
% 11.21/2.00      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) = iProver_top
% 11.21/2.00      | v1_relat_1(X1) != iProver_top ),
% 11.21/2.00      inference(predicate_to_equality,[status(thm)],[c_172]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_6507,plain,
% 11.21/2.00      ( k9_relat_1(k6_relat_1(k1_relat_1(X0)),k1_relat_1(X1)) = k1_relat_1(X1)
% 11.21/2.00      | r1_tarski(X1,X0) != iProver_top
% 11.21/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.21/2.00      inference(superposition,[status(thm)],[c_1734,c_1731]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_16768,plain,
% 11.21/2.00      ( k9_relat_1(k6_relat_1(k1_relat_1(sK3)),k1_relat_1(k6_relat_1(sK2))) = k1_relat_1(k6_relat_1(sK2))
% 11.21/2.00      | v1_relat_1(sK3) != iProver_top ),
% 11.21/2.00      inference(superposition,[status(thm)],[c_1736,c_6507]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_27,negated_conjecture,
% 11.21/2.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 11.21/2.00      inference(cnf_transformation,[],[f74]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_1899,plain,
% 11.21/2.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 11.21/2.00      | v1_relat_1(sK3) ),
% 11.21/2.00      inference(instantiation,[status(thm)],[c_19]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_3711,plain,
% 11.21/2.00      ( ~ r1_tarski(k1_relat_1(k6_relat_1(sK2)),X0)
% 11.21/2.00      | k9_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(sK2))) = k1_relat_1(k6_relat_1(sK2)) ),
% 11.21/2.00      inference(instantiation,[status(thm)],[c_278]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_4281,plain,
% 11.21/2.00      ( ~ r1_tarski(k1_relat_1(k6_relat_1(sK2)),k1_relat_1(X0))
% 11.21/2.00      | k9_relat_1(k6_relat_1(k1_relat_1(X0)),k1_relat_1(k6_relat_1(sK2))) = k1_relat_1(k6_relat_1(sK2)) ),
% 11.21/2.00      inference(instantiation,[status(thm)],[c_3711]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_4284,plain,
% 11.21/2.00      ( ~ r1_tarski(k1_relat_1(k6_relat_1(sK2)),k1_relat_1(sK3))
% 11.21/2.00      | k9_relat_1(k6_relat_1(k1_relat_1(sK3)),k1_relat_1(k6_relat_1(sK2))) = k1_relat_1(k6_relat_1(sK2)) ),
% 11.21/2.00      inference(instantiation,[status(thm)],[c_4281]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_4282,plain,
% 11.21/2.00      ( ~ r1_tarski(k6_relat_1(sK2),X0)
% 11.21/2.00      | r1_tarski(k1_relat_1(k6_relat_1(sK2)),k1_relat_1(X0))
% 11.21/2.00      | ~ v1_relat_1(X0) ),
% 11.21/2.00      inference(instantiation,[status(thm)],[c_172]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_4288,plain,
% 11.21/2.00      ( ~ r1_tarski(k6_relat_1(sK2),sK3)
% 11.21/2.00      | r1_tarski(k1_relat_1(k6_relat_1(sK2)),k1_relat_1(sK3))
% 11.21/2.00      | ~ v1_relat_1(sK3) ),
% 11.21/2.00      inference(instantiation,[status(thm)],[c_4282]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_16896,plain,
% 11.21/2.00      ( k9_relat_1(k6_relat_1(k1_relat_1(sK3)),k1_relat_1(k6_relat_1(sK2))) = k1_relat_1(k6_relat_1(sK2)) ),
% 11.21/2.00      inference(global_propositional_subsumption,
% 11.21/2.00                [status(thm)],
% 11.21/2.00                [c_16768,c_27,c_26,c_1899,c_4284,c_4288]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_6839,plain,
% 11.21/2.00      ( r1_tarski(k9_relat_1(k6_relat_1(X0),X1),X0) = iProver_top
% 11.21/2.00      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 11.21/2.00      inference(superposition,[status(thm)],[c_6813,c_1744]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_7533,plain,
% 11.21/2.00      ( r1_tarski(k9_relat_1(k6_relat_1(X0),X1),X0) = iProver_top ),
% 11.21/2.00      inference(global_propositional_subsumption,
% 11.21/2.00                [status(thm)],
% 11.21/2.00                [c_6839,c_31,c_1895]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_16904,plain,
% 11.21/2.00      ( r1_tarski(k1_relat_1(k6_relat_1(sK2)),k1_relat_1(sK3)) = iProver_top ),
% 11.21/2.00      inference(superposition,[status(thm)],[c_16896,c_7533]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_45438,plain,
% 11.21/2.00      ( r1_tarski(sK2,k1_relat_1(sK3)) = iProver_top ),
% 11.21/2.00      inference(demodulation,[status(thm)],[c_44435,c_16904]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_14,plain,
% 11.21/2.00      ( ~ r1_tarski(X0,X1)
% 11.21/2.00      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 11.21/2.00      | ~ v1_relat_1(X0)
% 11.21/2.00      | ~ v1_relat_1(X1) ),
% 11.21/2.00      inference(cnf_transformation,[],[f64]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_176,plain,
% 11.21/2.00      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 11.21/2.00      | ~ r1_tarski(X0,X1)
% 11.21/2.00      | ~ v1_relat_1(X1) ),
% 11.21/2.00      inference(global_propositional_subsumption,
% 11.21/2.00                [status(thm)],
% 11.21/2.00                [c_14,c_8,c_6]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_177,plain,
% 11.21/2.00      ( ~ r1_tarski(X0,X1)
% 11.21/2.00      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 11.21/2.00      | ~ v1_relat_1(X1) ),
% 11.21/2.00      inference(renaming,[status(thm)],[c_176]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_1733,plain,
% 11.21/2.00      ( r1_tarski(X0,X1) != iProver_top
% 11.21/2.00      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) = iProver_top
% 11.21/2.00      | v1_relat_1(X1) != iProver_top ),
% 11.21/2.00      inference(predicate_to_equality,[status(thm)],[c_177]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_5325,plain,
% 11.21/2.00      ( k9_relat_1(k6_relat_1(k2_relat_1(X0)),k2_relat_1(X1)) = k2_relat_1(X1)
% 11.21/2.00      | r1_tarski(X1,X0) != iProver_top
% 11.21/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.21/2.00      inference(superposition,[status(thm)],[c_1733,c_1731]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_12723,plain,
% 11.21/2.00      ( k9_relat_1(k6_relat_1(k2_relat_1(sK3)),k2_relat_1(k6_relat_1(sK2))) = k2_relat_1(k6_relat_1(sK2))
% 11.21/2.00      | v1_relat_1(sK3) != iProver_top ),
% 11.21/2.00      inference(superposition,[status(thm)],[c_1736,c_5325]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_12772,plain,
% 11.21/2.00      ( k9_relat_1(k6_relat_1(k2_relat_1(sK3)),sK2) = sK2
% 11.21/2.00      | v1_relat_1(sK3) != iProver_top ),
% 11.21/2.00      inference(demodulation,[status(thm)],[c_12723,c_6813]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_28,plain,
% 11.21/2.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 11.21/2.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_1900,plain,
% 11.21/2.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 11.21/2.00      | v1_relat_1(sK3) = iProver_top ),
% 11.21/2.00      inference(predicate_to_equality,[status(thm)],[c_1899]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_13779,plain,
% 11.21/2.00      ( k9_relat_1(k6_relat_1(k2_relat_1(sK3)),sK2) = sK2 ),
% 11.21/2.00      inference(global_propositional_subsumption,
% 11.21/2.00                [status(thm)],
% 11.21/2.00                [c_12772,c_28,c_1900]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_13786,plain,
% 11.21/2.00      ( r1_tarski(sK2,k2_relat_1(sK3)) = iProver_top ),
% 11.21/2.00      inference(superposition,[status(thm)],[c_13779,c_7533]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_1735,plain,
% 11.21/2.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 11.21/2.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_23,plain,
% 11.21/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.21/2.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 11.21/2.00      inference(cnf_transformation,[],[f72]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_1739,plain,
% 11.21/2.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 11.21/2.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 11.21/2.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_2770,plain,
% 11.21/2.00      ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
% 11.21/2.00      inference(superposition,[status(thm)],[c_1735,c_1739]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_25,negated_conjecture,
% 11.21/2.00      ( ~ r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3))
% 11.21/2.00      | ~ r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3)) ),
% 11.21/2.00      inference(cnf_transformation,[],[f76]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_1737,plain,
% 11.21/2.00      ( r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3)) != iProver_top
% 11.21/2.00      | r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3)) != iProver_top ),
% 11.21/2.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_3127,plain,
% 11.21/2.00      ( r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3)) != iProver_top
% 11.21/2.00      | r1_tarski(sK2,k2_relat_1(sK3)) != iProver_top ),
% 11.21/2.00      inference(demodulation,[status(thm)],[c_2770,c_1737]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_22,plain,
% 11.21/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.21/2.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 11.21/2.00      inference(cnf_transformation,[],[f71]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_1740,plain,
% 11.21/2.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 11.21/2.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 11.21/2.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_2792,plain,
% 11.21/2.00      ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
% 11.21/2.00      inference(superposition,[status(thm)],[c_1735,c_1740]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(c_3443,plain,
% 11.21/2.00      ( r1_tarski(sK2,k2_relat_1(sK3)) != iProver_top
% 11.21/2.00      | r1_tarski(sK2,k1_relat_1(sK3)) != iProver_top ),
% 11.21/2.00      inference(light_normalisation,[status(thm)],[c_3127,c_2792]) ).
% 11.21/2.00  
% 11.21/2.00  cnf(contradiction,plain,
% 11.21/2.00      ( $false ),
% 11.21/2.00      inference(minisat,[status(thm)],[c_45438,c_13786,c_3443]) ).
% 11.21/2.00  
% 11.21/2.00  
% 11.21/2.00  % SZS output end CNFRefutation for theBenchmark.p
% 11.21/2.00  
% 11.21/2.00  ------                               Statistics
% 11.21/2.00  
% 11.21/2.00  ------ General
% 11.21/2.00  
% 11.21/2.00  abstr_ref_over_cycles:                  0
% 11.21/2.00  abstr_ref_under_cycles:                 0
% 11.21/2.00  gc_basic_clause_elim:                   0
% 11.21/2.00  forced_gc_time:                         0
% 11.21/2.00  parsing_time:                           0.01
% 11.21/2.00  unif_index_cands_time:                  0.
% 11.21/2.00  unif_index_add_time:                    0.
% 11.21/2.00  orderings_time:                         0.
% 11.21/2.00  out_proof_time:                         0.019
% 11.21/2.00  total_time:                             1.227
% 11.21/2.00  num_of_symbols:                         51
% 11.21/2.00  num_of_terms:                           47475
% 11.21/2.00  
% 11.21/2.00  ------ Preprocessing
% 11.21/2.00  
% 11.21/2.00  num_of_splits:                          0
% 11.21/2.00  num_of_split_atoms:                     0
% 11.21/2.00  num_of_reused_defs:                     0
% 11.21/2.00  num_eq_ax_congr_red:                    21
% 11.21/2.00  num_of_sem_filtered_clauses:            1
% 11.21/2.00  num_of_subtypes:                        0
% 11.21/2.00  monotx_restored_types:                  0
% 11.21/2.00  sat_num_of_epr_types:                   0
% 11.21/2.00  sat_num_of_non_cyclic_types:            0
% 11.21/2.00  sat_guarded_non_collapsed_types:        0
% 11.21/2.00  num_pure_diseq_elim:                    0
% 11.21/2.00  simp_replaced_by:                       0
% 11.21/2.00  res_preprocessed:                       116
% 11.21/2.00  prep_upred:                             0
% 11.21/2.00  prep_unflattend:                        58
% 11.21/2.00  smt_new_axioms:                         0
% 11.21/2.00  pred_elim_cands:                        3
% 11.21/2.00  pred_elim:                              3
% 11.21/2.00  pred_elim_cl:                           5
% 11.21/2.00  pred_elim_cycles:                       5
% 11.21/2.00  merged_defs:                            8
% 11.21/2.00  merged_defs_ncl:                        0
% 11.21/2.00  bin_hyper_res:                          10
% 11.21/2.00  prep_cycles:                            4
% 11.21/2.00  pred_elim_time:                         0.01
% 11.21/2.00  splitting_time:                         0.
% 11.21/2.00  sem_filter_time:                        0.
% 11.21/2.00  monotx_time:                            0.
% 11.21/2.00  subtype_inf_time:                       0.
% 11.21/2.00  
% 11.21/2.00  ------ Problem properties
% 11.21/2.00  
% 11.21/2.00  clauses:                                22
% 11.21/2.00  conjectures:                            3
% 11.21/2.00  epr:                                    3
% 11.21/2.00  horn:                                   22
% 11.21/2.00  ground:                                 3
% 11.21/2.00  unary:                                  5
% 11.21/2.00  binary:                                 11
% 11.21/2.00  lits:                                   45
% 11.21/2.00  lits_eq:                                6
% 11.21/2.00  fd_pure:                                0
% 11.21/2.00  fd_pseudo:                              0
% 11.21/2.00  fd_cond:                                0
% 11.21/2.00  fd_pseudo_cond:                         1
% 11.21/2.00  ac_symbols:                             0
% 11.21/2.00  
% 11.21/2.00  ------ Propositional Solver
% 11.21/2.00  
% 11.21/2.00  prop_solver_calls:                      32
% 11.21/2.00  prop_fast_solver_calls:                 1817
% 11.21/2.00  smt_solver_calls:                       0
% 11.21/2.00  smt_fast_solver_calls:                  0
% 11.21/2.00  prop_num_of_clauses:                    17706
% 11.21/2.00  prop_preprocess_simplified:             30634
% 11.21/2.00  prop_fo_subsumed:                       95
% 11.21/2.00  prop_solver_time:                       0.
% 11.21/2.00  smt_solver_time:                        0.
% 11.21/2.00  smt_fast_solver_time:                   0.
% 11.21/2.00  prop_fast_solver_time:                  0.
% 11.21/2.00  prop_unsat_core_time:                   0.002
% 11.21/2.00  
% 11.21/2.00  ------ QBF
% 11.21/2.00  
% 11.21/2.00  qbf_q_res:                              0
% 11.21/2.00  qbf_num_tautologies:                    0
% 11.21/2.00  qbf_prep_cycles:                        0
% 11.21/2.00  
% 11.21/2.00  ------ BMC1
% 11.21/2.00  
% 11.21/2.00  bmc1_current_bound:                     -1
% 11.21/2.00  bmc1_last_solved_bound:                 -1
% 11.21/2.00  bmc1_unsat_core_size:                   -1
% 11.21/2.00  bmc1_unsat_core_parents_size:           -1
% 11.21/2.00  bmc1_merge_next_fun:                    0
% 11.21/2.00  bmc1_unsat_core_clauses_time:           0.
% 11.21/2.00  
% 11.21/2.00  ------ Instantiation
% 11.21/2.00  
% 11.21/2.00  inst_num_of_clauses:                    4915
% 11.21/2.00  inst_num_in_passive:                    639
% 11.21/2.00  inst_num_in_active:                     1952
% 11.21/2.00  inst_num_in_unprocessed:                2326
% 11.21/2.00  inst_num_of_loops:                      2110
% 11.21/2.00  inst_num_of_learning_restarts:          0
% 11.21/2.00  inst_num_moves_active_passive:          154
% 11.21/2.00  inst_lit_activity:                      0
% 11.21/2.00  inst_lit_activity_moves:                0
% 11.21/2.00  inst_num_tautologies:                   0
% 11.21/2.00  inst_num_prop_implied:                  0
% 11.21/2.00  inst_num_existing_simplified:           0
% 11.21/2.00  inst_num_eq_res_simplified:             0
% 11.21/2.00  inst_num_child_elim:                    0
% 11.21/2.00  inst_num_of_dismatching_blockings:      4356
% 11.21/2.00  inst_num_of_non_proper_insts:           7198
% 11.21/2.00  inst_num_of_duplicates:                 0
% 11.21/2.00  inst_inst_num_from_inst_to_res:         0
% 11.21/2.00  inst_dismatching_checking_time:         0.
% 11.21/2.00  
% 11.21/2.00  ------ Resolution
% 11.21/2.00  
% 11.21/2.00  res_num_of_clauses:                     0
% 11.21/2.00  res_num_in_passive:                     0
% 11.21/2.00  res_num_in_active:                      0
% 11.21/2.00  res_num_of_loops:                       120
% 11.21/2.00  res_forward_subset_subsumed:            334
% 11.21/2.00  res_backward_subset_subsumed:           8
% 11.21/2.00  res_forward_subsumed:                   0
% 11.21/2.00  res_backward_subsumed:                  0
% 11.21/2.00  res_forward_subsumption_resolution:     0
% 11.21/2.00  res_backward_subsumption_resolution:    0
% 11.21/2.00  res_clause_to_clause_subsumption:       4069
% 11.21/2.00  res_orphan_elimination:                 0
% 11.21/2.00  res_tautology_del:                      546
% 11.21/2.00  res_num_eq_res_simplified:              0
% 11.21/2.00  res_num_sel_changes:                    0
% 11.21/2.00  res_moves_from_active_to_pass:          0
% 11.21/2.00  
% 11.21/2.00  ------ Superposition
% 11.21/2.00  
% 11.21/2.00  sup_time_total:                         0.
% 11.21/2.00  sup_time_generating:                    0.
% 11.21/2.00  sup_time_sim_full:                      0.
% 11.21/2.00  sup_time_sim_immed:                     0.
% 11.21/2.00  
% 11.21/2.00  sup_num_of_clauses:                     917
% 11.21/2.00  sup_num_in_active:                      306
% 11.21/2.00  sup_num_in_passive:                     611
% 11.21/2.00  sup_num_of_loops:                       420
% 11.21/2.00  sup_fw_superposition:                   540
% 11.21/2.00  sup_bw_superposition:                   781
% 11.21/2.00  sup_immediate_simplified:               305
% 11.21/2.00  sup_given_eliminated:                   1
% 11.21/2.00  comparisons_done:                       0
% 11.21/2.00  comparisons_avoided:                    0
% 11.21/2.00  
% 11.21/2.00  ------ Simplifications
% 11.21/2.00  
% 11.21/2.00  
% 11.21/2.00  sim_fw_subset_subsumed:                 36
% 11.21/2.00  sim_bw_subset_subsumed:                 3
% 11.21/2.00  sim_fw_subsumed:                        63
% 11.21/2.00  sim_bw_subsumed:                        0
% 11.21/2.00  sim_fw_subsumption_res:                 14
% 11.21/2.00  sim_bw_subsumption_res:                 0
% 11.21/2.00  sim_tautology_del:                      11
% 11.21/2.00  sim_eq_tautology_del:                   47
% 11.21/2.00  sim_eq_res_simp:                        0
% 11.21/2.00  sim_fw_demodulated:                     180
% 11.21/2.00  sim_bw_demodulated:                     129
% 11.21/2.00  sim_light_normalised:                   105
% 11.21/2.00  sim_joinable_taut:                      0
% 11.21/2.00  sim_joinable_simp:                      0
% 11.21/2.00  sim_ac_normalised:                      0
% 11.21/2.00  sim_smt_subsumption:                    0
% 11.21/2.00  
%------------------------------------------------------------------------------
