%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1000+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:37 EST 2020

% Result     : Theorem 1.83s
% Output     : CNFRefutation 1.83s
% Verified   : 
% Statistics : Number of formulae       :  140 (1689 expanded)
%              Number of clauses        :   94 ( 684 expanded)
%              Number of leaves         :   15 ( 277 expanded)
%              Depth                    :   25
%              Number of atoms          :  339 (5742 expanded)
%              Number of equality atoms :  223 (3198 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f16])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => k8_relset_1(X0,X1,X2,X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => k8_relset_1(X0,X1,X2,X1) = X0 ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f14,plain,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1) )
       => ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => k8_relset_1(X0,X1,X2,X1) = X0 ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) != X0
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) != X0
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f29,plain,
    ( ? [X0,X1,X2] :
        ( k8_relset_1(X0,X1,X2,X1) != X0
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1) )
   => ( k8_relset_1(sK0,sK1,sK2,sK1) != sK0
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( k8_relset_1(sK0,sK1,sK2,sK1) != sK0
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f29])).

fof(f46,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f47,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f30])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f10])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f43,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f49,plain,(
    k8_relset_1(sK0,sK1,sK2,sK1) != sK0 ),
    inference(cnf_transformation,[],[f30])).

fof(f48,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f30])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f54,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f33])).

cnf(c_6,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_18,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_290,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK2 != X0
    | sK1 != X2
    | sK0 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_18])).

cnf(c_291,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_290])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_293,plain,
    ( k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_291,c_17])).

cnf(c_418,plain,
    ( k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(subtyping,[status(esa)],[c_293])).

cnf(c_422,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_655,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_422])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_429,plain,
    ( ~ m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X1_45,X2_45)))
    | k1_relset_1(X1_45,X2_45,X0_45) = k1_relat_1(X0_45) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_650,plain,
    ( k1_relset_1(X0_45,X1_45,X2_45) = k1_relat_1(X2_45)
    | m1_subset_1(X2_45,k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_429])).

cnf(c_927,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_655,c_650])).

cnf(c_1095,plain,
    ( k1_relat_1(sK2) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_418,c_927])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_428,plain,
    ( ~ m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X1_45,X2_45)))
    | k2_relset_1(X1_45,X2_45,X0_45) = k2_relat_1(X0_45) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_651,plain,
    ( k2_relset_1(X0_45,X1_45,X2_45) = k2_relat_1(X2_45)
    | m1_subset_1(X2_45,k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_428])).

cnf(c_931,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_655,c_651])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_430,plain,
    ( ~ m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X1_45,X2_45)))
    | m1_subset_1(k2_relset_1(X1_45,X2_45,X0_45),k1_zfmisc_1(X2_45)) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_649,plain,
    ( m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X1_45,X2_45))) != iProver_top
    | m1_subset_1(k2_relset_1(X1_45,X2_45,X0_45),k1_zfmisc_1(X2_45)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_430])).

cnf(c_1160,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_931,c_649])).

cnf(c_20,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1281,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1160,c_20])).

cnf(c_14,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_13,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_205,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_xboole_0(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_14,c_13])).

cnf(c_421,plain,
    ( ~ m1_subset_1(X0_45,k1_zfmisc_1(X1_45))
    | k3_xboole_0(X0_45,X1_45) = X0_45 ),
    inference(subtyping,[status(esa)],[c_205])).

cnf(c_656,plain,
    ( k3_xboole_0(X0_45,X1_45) = X0_45
    | m1_subset_1(X0_45,k1_zfmisc_1(X1_45)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_421])).

cnf(c_1286,plain,
    ( k3_xboole_0(k2_relat_1(sK2),sK1) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1281,c_656])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_431,plain,
    ( ~ m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X1_45,X2_45)))
    | v1_relat_1(X0_45) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_648,plain,
    ( m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X1_45,X2_45))) != iProver_top
    | v1_relat_1(X0_45) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_431])).

cnf(c_903,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_655,c_648])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k3_xboole_0(k2_relat_1(X0),X1)) = k10_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_426,plain,
    ( ~ v1_relat_1(X0_45)
    | k10_relat_1(X0_45,k3_xboole_0(k2_relat_1(X0_45),X1_45)) = k10_relat_1(X0_45,X1_45) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_653,plain,
    ( k10_relat_1(X0_45,k3_xboole_0(k2_relat_1(X0_45),X1_45)) = k10_relat_1(X0_45,X1_45)
    | v1_relat_1(X0_45) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_426])).

cnf(c_1015,plain,
    ( k10_relat_1(sK2,k3_xboole_0(k2_relat_1(sK2),X0_45)) = k10_relat_1(sK2,X0_45) ),
    inference(superposition,[status(thm)],[c_903,c_653])).

cnf(c_1449,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) = k10_relat_1(sK2,sK1) ),
    inference(superposition,[status(thm)],[c_1286,c_1015])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_425,plain,
    ( ~ v1_relat_1(X0_45)
    | k10_relat_1(X0_45,k2_relat_1(X0_45)) = k1_relat_1(X0_45) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_654,plain,
    ( k10_relat_1(X0_45,k2_relat_1(X0_45)) = k1_relat_1(X0_45)
    | v1_relat_1(X0_45) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_425])).

cnf(c_1016,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_903,c_654])).

cnf(c_1450,plain,
    ( k10_relat_1(sK2,sK1) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_1449,c_1016])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_427,plain,
    ( ~ m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X1_45,X2_45)))
    | k8_relset_1(X1_45,X2_45,X0_45,X3_45) = k10_relat_1(X0_45,X3_45) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_652,plain,
    ( k8_relset_1(X0_45,X1_45,X2_45,X3_45) = k10_relat_1(X2_45,X3_45)
    | m1_subset_1(X2_45,k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_427])).

cnf(c_1290,plain,
    ( k8_relset_1(sK0,sK1,sK2,X0_45) = k10_relat_1(sK2,X0_45) ),
    inference(superposition,[status(thm)],[c_655,c_652])).

cnf(c_15,negated_conjecture,
    ( k8_relset_1(sK0,sK1,sK2,sK1) != sK0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_424,negated_conjecture,
    ( k8_relset_1(sK0,sK1,sK2,sK1) != sK0 ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1352,plain,
    ( k10_relat_1(sK2,sK1) != sK0 ),
    inference(demodulation,[status(thm)],[c_1290,c_424])).

cnf(c_1452,plain,
    ( k1_relat_1(sK2) != sK0 ),
    inference(demodulation,[status(thm)],[c_1450,c_1352])).

cnf(c_1510,plain,
    ( sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1095,c_1452])).

cnf(c_1512,plain,
    ( k10_relat_1(sK2,k1_xboole_0) = k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1510,c_1450])).

cnf(c_1517,plain,
    ( k1_relset_1(sK0,k1_xboole_0,sK2) = k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1510,c_927])).

cnf(c_16,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_423,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1523,plain,
    ( sK0 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1510,c_423])).

cnf(c_1524,plain,
    ( sK0 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_1523])).

cnf(c_5,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_277,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | sK2 != X0
    | sK1 != X1
    | sK0 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_18])).

cnf(c_278,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | k1_relset_1(k1_xboole_0,sK1,sK2) = k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_277])).

cnf(c_419,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | k1_relset_1(k1_xboole_0,sK1,sK2) = k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_278])).

cnf(c_658,plain,
    ( k1_relset_1(k1_xboole_0,sK1,sK2) = k1_xboole_0
    | sK0 != k1_xboole_0
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_419])).

cnf(c_1520,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) = k1_xboole_0
    | sK0 != k1_xboole_0
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1510,c_658])).

cnf(c_1530,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1520,c_1524])).

cnf(c_1531,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) = k1_xboole_0
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_1530])).

cnf(c_1522,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1510,c_655])).

cnf(c_1527,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1522,c_1524])).

cnf(c_1534,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1531,c_1527])).

cnf(c_1540,plain,
    ( k1_relat_1(sK2) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1517,c_1524,c_1534])).

cnf(c_1553,plain,
    ( k10_relat_1(sK2,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1512,c_1540])).

cnf(c_435,plain,
    ( X0_45 != X1_45
    | X2_45 != X1_45
    | X2_45 = X0_45 ),
    theory(equality)).

cnf(c_801,plain,
    ( X0_45 != X1_45
    | sK0 != X1_45
    | sK0 = X0_45 ),
    inference(instantiation,[status(thm)],[c_435])).

cnf(c_1214,plain,
    ( k10_relat_1(sK2,X0_45) != X1_45
    | sK0 != X1_45
    | sK0 = k10_relat_1(sK2,X0_45) ),
    inference(instantiation,[status(thm)],[c_801])).

cnf(c_1215,plain,
    ( k10_relat_1(sK2,k1_xboole_0) != k1_xboole_0
    | sK0 = k10_relat_1(sK2,k1_xboole_0)
    | sK0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1214])).

cnf(c_441,plain,
    ( X0_45 != X1_45
    | k10_relat_1(X2_45,X0_45) = k10_relat_1(X2_45,X1_45) ),
    theory(equality)).

cnf(c_1116,plain,
    ( k10_relat_1(sK2,sK1) = k10_relat_1(sK2,X0_45)
    | sK1 != X0_45 ),
    inference(instantiation,[status(thm)],[c_441])).

cnf(c_1118,plain,
    ( k10_relat_1(sK2,sK1) = k10_relat_1(sK2,k1_xboole_0)
    | sK1 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1116])).

cnf(c_933,plain,
    ( k10_relat_1(sK2,sK1) != X0_45
    | sK0 != X0_45
    | sK0 = k10_relat_1(sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_801])).

cnf(c_1115,plain,
    ( k10_relat_1(sK2,sK1) != k10_relat_1(sK2,X0_45)
    | sK0 != k10_relat_1(sK2,X0_45)
    | sK0 = k10_relat_1(sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_933])).

cnf(c_1117,plain,
    ( k10_relat_1(sK2,sK1) != k10_relat_1(sK2,k1_xboole_0)
    | sK0 = k10_relat_1(sK2,sK1)
    | sK0 != k10_relat_1(sK2,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1115])).

cnf(c_973,plain,
    ( X0_45 != X1_45
    | X0_45 = sK1
    | sK1 != X1_45 ),
    inference(instantiation,[status(thm)],[c_435])).

cnf(c_974,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_973])).

cnf(c_770,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k8_relset_1(sK0,sK1,sK2,X0_45) = k10_relat_1(sK2,X0_45) ),
    inference(instantiation,[status(thm)],[c_427])).

cnf(c_892,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k8_relset_1(sK0,sK1,sK2,sK1) = k10_relat_1(sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_770])).

cnf(c_750,plain,
    ( k8_relset_1(sK0,sK1,sK2,sK1) != X0_45
    | k8_relset_1(sK0,sK1,sK2,sK1) = sK0
    | sK0 != X0_45 ),
    inference(instantiation,[status(thm)],[c_435])).

cnf(c_891,plain,
    ( k8_relset_1(sK0,sK1,sK2,sK1) != k10_relat_1(sK2,sK1)
    | k8_relset_1(sK0,sK1,sK2,sK1) = sK0
    | sK0 != k10_relat_1(sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_750])).

cnf(c_433,plain,
    ( X0_45 = X0_45 ),
    theory(equality)).

cnf(c_816,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_433])).

cnf(c_749,plain,
    ( sK0 != X0_45
    | sK0 = k1_xboole_0
    | k1_xboole_0 != X0_45 ),
    inference(instantiation,[status(thm)],[c_435])).

cnf(c_815,plain,
    ( sK0 != sK0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_749])).

cnf(c_451,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_433])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1553,c_1452,c_1215,c_1118,c_1117,c_1095,c_974,c_892,c_891,c_816,c_815,c_423,c_424,c_451,c_17])).


%------------------------------------------------------------------------------
