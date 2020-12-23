%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:48 EST 2020

% Result     : Theorem 1.96s
% Output     : CNFRefutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 579 expanded)
%              Number of clauses        :   79 ( 197 expanded)
%              Number of leaves         :   11 ( 108 expanded)
%              Depth                    :   20
%              Number of atoms          :  373 (3019 expanded)
%              Number of equality atoms :  136 ( 549 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f27,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
          | ~ v1_funct_1(k2_funct_1(X2)) )
        & k2_relset_1(X0,X1,X2) = X1
        & v2_funct_1(X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
        | ~ v1_funct_1(k2_funct_1(sK2)) )
      & k2_relset_1(sK0,sK1,sK2) = sK1
      & v2_funct_1(sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
      | ~ v1_funct_1(k2_funct_1(sK2)) )
    & k2_relset_1(sK0,sK1,sK2) = sK1
    & v2_funct_1(sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f27])).

fof(f45,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f28])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f47,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f28])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f17,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f32,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f46,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f43,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f33,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f15,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f30,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f31,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f48,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f28])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_453,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_769,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_453])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_457,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X1_46,X2_46)))
    | k2_relset_1(X1_46,X2_46,X0_46) = k2_relat_1(X0_46) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_766,plain,
    ( k2_relset_1(X0_46,X1_46,X2_46) = k2_relat_1(X2_46)
    | m1_subset_1(X2_46,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_457])).

cnf(c_1061,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_769,c_766])).

cnf(c_15,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_454,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1062,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_1061,c_454])).

cnf(c_4,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_16,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_215,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_16])).

cnf(c_216,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_215])).

cnf(c_19,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_218,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_216,c_19])).

cnf(c_451,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_218])).

cnf(c_771,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_451])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_460,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X1_46,X2_46)))
    | v1_relat_1(X0_46) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_886,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_460])).

cnf(c_897,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_771,c_17,c_451,c_886])).

cnf(c_1091,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
    inference(demodulation,[status(thm)],[c_1062,c_897])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_11,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_293,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X3)))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | X3 != X1
    | k2_relat_1(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_11])).

cnf(c_294,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ m1_subset_1(k2_relat_1(X0),k1_zfmisc_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(unflattening,[status(thm)],[c_293])).

cnf(c_448,plain,
    ( m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_46),X1_46)))
    | ~ m1_subset_1(k2_relat_1(X0_46),k1_zfmisc_1(X1_46))
    | ~ v1_relat_1(X0_46)
    | ~ v1_funct_1(X0_46) ),
    inference(subtyping,[status(esa)],[c_294])).

cnf(c_774,plain,
    ( m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_46),X1_46))) = iProver_top
    | m1_subset_1(k2_relat_1(X0_46),k1_zfmisc_1(X1_46)) != iProver_top
    | v1_relat_1(X0_46) != iProver_top
    | v1_funct_1(X0_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_448])).

cnf(c_1569,plain,
    ( m1_subset_1(k2_relat_1(k2_funct_1(sK2)),k1_zfmisc_1(X0_46)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0_46))) = iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1091,c_774])).

cnf(c_3,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_229,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_16])).

cnf(c_230,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_229])).

cnf(c_54,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_232,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_230,c_19,c_16,c_54])).

cnf(c_450,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_232])).

cnf(c_772,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_450])).

cnf(c_923,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_772,c_17,c_450,c_886])).

cnf(c_1611,plain,
    ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(X0_46)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0_46))) = iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1569,c_923])).

cnf(c_20,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_22,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_56,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_58,plain,
    ( v1_relat_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_56])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_59,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_61,plain,
    ( v1_relat_1(sK2) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_59])).

cnf(c_887,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_886])).

cnf(c_1632,plain,
    ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(X0_46)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0_46))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1611,c_20,c_22,c_58,c_61,c_887])).

cnf(c_12,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_14,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_249,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relat_1(X0) != sK1
    | k2_funct_1(sK2) != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_14])).

cnf(c_250,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
    inference(unflattening,[status(thm)],[c_249])).

cnf(c_262,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_250,c_5])).

cnf(c_311,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_262])).

cnf(c_312,plain,
    ( ~ m1_subset_1(k2_relat_1(k2_funct_1(sK2)),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
    inference(unflattening,[status(thm)],[c_311])).

cnf(c_447,plain,
    ( ~ m1_subset_1(k2_relat_1(k2_funct_1(sK2)),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
    inference(subtyping,[status(esa)],[c_312])).

cnf(c_775,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != sK1
    | m1_subset_1(k2_relat_1(k2_funct_1(sK2)),k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_447])).

cnf(c_510,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != sK1
    | m1_subset_1(k2_relat_1(k2_funct_1(sK2)),k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_447])).

cnf(c_953,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(k2_relat_1(k2_funct_1(sK2)),k1_zfmisc_1(sK0)) != iProver_top
    | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_775,c_20,c_22,c_61,c_510,c_887])).

cnf(c_954,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != sK1
    | m1_subset_1(k2_relat_1(k2_funct_1(sK2)),k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_953])).

cnf(c_957,plain,
    ( k2_relat_1(sK2) != sK1
    | m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_954,c_897,c_923])).

cnf(c_1090,plain,
    ( sK1 != sK1
    | m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1062,c_957])).

cnf(c_1094,plain,
    ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_1090])).

cnf(c_1640,plain,
    ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1632,c_1094])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X2) = k1_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_456,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X1_46,X2_46)))
    | k8_relset_1(X1_46,X2_46,X0_46,X2_46) = k1_relset_1(X1_46,X2_46,X0_46) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_767,plain,
    ( k8_relset_1(X0_46,X1_46,X2_46,X1_46) = k1_relset_1(X0_46,X1_46,X2_46)
    | m1_subset_1(X2_46,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_456])).

cnf(c_1291,plain,
    ( k8_relset_1(sK0,sK1,sK2,sK1) = k1_relset_1(sK0,sK1,sK2) ),
    inference(superposition,[status(thm)],[c_769,c_767])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_458,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X1_46,X2_46)))
    | k1_relset_1(X1_46,X2_46,X0_46) = k1_relat_1(X0_46) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_765,plain,
    ( k1_relset_1(X0_46,X1_46,X2_46) = k1_relat_1(X2_46)
    | m1_subset_1(X2_46,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_458])).

cnf(c_1057,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_769,c_765])).

cnf(c_1298,plain,
    ( k8_relset_1(sK0,sK1,sK2,sK1) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_1291,c_1057])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k8_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_459,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X1_46,X2_46)))
    | m1_subset_1(k8_relset_1(X1_46,X2_46,X0_46,X3_46),k1_zfmisc_1(X1_46)) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_764,plain,
    ( m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X1_46,X2_46))) != iProver_top
    | m1_subset_1(k8_relset_1(X1_46,X2_46,X0_46,X3_46),k1_zfmisc_1(X1_46)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_459])).

cnf(c_1304,plain,
    ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1298,c_764])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1640,c_1304,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:38:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.96/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/1.00  
% 1.96/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.96/1.00  
% 1.96/1.00  ------  iProver source info
% 1.96/1.00  
% 1.96/1.00  git: date: 2020-06-30 10:37:57 +0100
% 1.96/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.96/1.00  git: non_committed_changes: false
% 1.96/1.00  git: last_make_outside_of_git: false
% 1.96/1.00  
% 1.96/1.00  ------ 
% 1.96/1.00  
% 1.96/1.00  ------ Input Options
% 1.96/1.00  
% 1.96/1.00  --out_options                           all
% 1.96/1.00  --tptp_safe_out                         true
% 1.96/1.00  --problem_path                          ""
% 1.96/1.00  --include_path                          ""
% 1.96/1.00  --clausifier                            res/vclausify_rel
% 1.96/1.00  --clausifier_options                    --mode clausify
% 1.96/1.00  --stdin                                 false
% 1.96/1.00  --stats_out                             all
% 1.96/1.00  
% 1.96/1.00  ------ General Options
% 1.96/1.00  
% 1.96/1.00  --fof                                   false
% 1.96/1.00  --time_out_real                         305.
% 1.96/1.00  --time_out_virtual                      -1.
% 1.96/1.00  --symbol_type_check                     false
% 1.96/1.00  --clausify_out                          false
% 1.96/1.00  --sig_cnt_out                           false
% 1.96/1.00  --trig_cnt_out                          false
% 1.96/1.00  --trig_cnt_out_tolerance                1.
% 1.96/1.00  --trig_cnt_out_sk_spl                   false
% 1.96/1.00  --abstr_cl_out                          false
% 1.96/1.00  
% 1.96/1.00  ------ Global Options
% 1.96/1.00  
% 1.96/1.00  --schedule                              default
% 1.96/1.00  --add_important_lit                     false
% 1.96/1.00  --prop_solver_per_cl                    1000
% 1.96/1.00  --min_unsat_core                        false
% 1.96/1.00  --soft_assumptions                      false
% 1.96/1.00  --soft_lemma_size                       3
% 1.96/1.00  --prop_impl_unit_size                   0
% 1.96/1.00  --prop_impl_unit                        []
% 1.96/1.00  --share_sel_clauses                     true
% 1.96/1.00  --reset_solvers                         false
% 1.96/1.00  --bc_imp_inh                            [conj_cone]
% 1.96/1.00  --conj_cone_tolerance                   3.
% 1.96/1.00  --extra_neg_conj                        none
% 1.96/1.00  --large_theory_mode                     true
% 1.96/1.00  --prolific_symb_bound                   200
% 1.96/1.00  --lt_threshold                          2000
% 1.96/1.00  --clause_weak_htbl                      true
% 1.96/1.00  --gc_record_bc_elim                     false
% 1.96/1.00  
% 1.96/1.00  ------ Preprocessing Options
% 1.96/1.00  
% 1.96/1.00  --preprocessing_flag                    true
% 1.96/1.00  --time_out_prep_mult                    0.1
% 1.96/1.00  --splitting_mode                        input
% 1.96/1.00  --splitting_grd                         true
% 1.96/1.00  --splitting_cvd                         false
% 1.96/1.00  --splitting_cvd_svl                     false
% 1.96/1.00  --splitting_nvd                         32
% 1.96/1.00  --sub_typing                            true
% 1.96/1.00  --prep_gs_sim                           true
% 1.96/1.00  --prep_unflatten                        true
% 1.96/1.00  --prep_res_sim                          true
% 1.96/1.00  --prep_upred                            true
% 1.96/1.00  --prep_sem_filter                       exhaustive
% 1.96/1.00  --prep_sem_filter_out                   false
% 1.96/1.00  --pred_elim                             true
% 1.96/1.00  --res_sim_input                         true
% 1.96/1.00  --eq_ax_congr_red                       true
% 1.96/1.00  --pure_diseq_elim                       true
% 1.96/1.00  --brand_transform                       false
% 1.96/1.00  --non_eq_to_eq                          false
% 1.96/1.00  --prep_def_merge                        true
% 1.96/1.00  --prep_def_merge_prop_impl              false
% 1.96/1.00  --prep_def_merge_mbd                    true
% 1.96/1.00  --prep_def_merge_tr_red                 false
% 1.96/1.00  --prep_def_merge_tr_cl                  false
% 1.96/1.00  --smt_preprocessing                     true
% 1.96/1.00  --smt_ac_axioms                         fast
% 1.96/1.00  --preprocessed_out                      false
% 1.96/1.00  --preprocessed_stats                    false
% 1.96/1.00  
% 1.96/1.00  ------ Abstraction refinement Options
% 1.96/1.00  
% 1.96/1.00  --abstr_ref                             []
% 1.96/1.00  --abstr_ref_prep                        false
% 1.96/1.00  --abstr_ref_until_sat                   false
% 1.96/1.00  --abstr_ref_sig_restrict                funpre
% 1.96/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.96/1.00  --abstr_ref_under                       []
% 1.96/1.00  
% 1.96/1.00  ------ SAT Options
% 1.96/1.00  
% 1.96/1.00  --sat_mode                              false
% 1.96/1.00  --sat_fm_restart_options                ""
% 1.96/1.00  --sat_gr_def                            false
% 1.96/1.00  --sat_epr_types                         true
% 1.96/1.00  --sat_non_cyclic_types                  false
% 1.96/1.00  --sat_finite_models                     false
% 1.96/1.00  --sat_fm_lemmas                         false
% 1.96/1.00  --sat_fm_prep                           false
% 1.96/1.00  --sat_fm_uc_incr                        true
% 1.96/1.00  --sat_out_model                         small
% 1.96/1.00  --sat_out_clauses                       false
% 1.96/1.00  
% 1.96/1.00  ------ QBF Options
% 1.96/1.00  
% 1.96/1.00  --qbf_mode                              false
% 1.96/1.00  --qbf_elim_univ                         false
% 1.96/1.00  --qbf_dom_inst                          none
% 1.96/1.00  --qbf_dom_pre_inst                      false
% 1.96/1.00  --qbf_sk_in                             false
% 1.96/1.00  --qbf_pred_elim                         true
% 1.96/1.00  --qbf_split                             512
% 1.96/1.00  
% 1.96/1.00  ------ BMC1 Options
% 1.96/1.00  
% 1.96/1.00  --bmc1_incremental                      false
% 1.96/1.00  --bmc1_axioms                           reachable_all
% 1.96/1.00  --bmc1_min_bound                        0
% 1.96/1.00  --bmc1_max_bound                        -1
% 1.96/1.00  --bmc1_max_bound_default                -1
% 1.96/1.00  --bmc1_symbol_reachability              true
% 1.96/1.00  --bmc1_property_lemmas                  false
% 1.96/1.00  --bmc1_k_induction                      false
% 1.96/1.00  --bmc1_non_equiv_states                 false
% 1.96/1.00  --bmc1_deadlock                         false
% 1.96/1.00  --bmc1_ucm                              false
% 1.96/1.00  --bmc1_add_unsat_core                   none
% 1.96/1.00  --bmc1_unsat_core_children              false
% 1.96/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.96/1.00  --bmc1_out_stat                         full
% 1.96/1.00  --bmc1_ground_init                      false
% 1.96/1.00  --bmc1_pre_inst_next_state              false
% 1.96/1.00  --bmc1_pre_inst_state                   false
% 1.96/1.00  --bmc1_pre_inst_reach_state             false
% 1.96/1.00  --bmc1_out_unsat_core                   false
% 1.96/1.00  --bmc1_aig_witness_out                  false
% 1.96/1.00  --bmc1_verbose                          false
% 1.96/1.00  --bmc1_dump_clauses_tptp                false
% 1.96/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.96/1.00  --bmc1_dump_file                        -
% 1.96/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.96/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.96/1.00  --bmc1_ucm_extend_mode                  1
% 1.96/1.00  --bmc1_ucm_init_mode                    2
% 1.96/1.00  --bmc1_ucm_cone_mode                    none
% 1.96/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.96/1.00  --bmc1_ucm_relax_model                  4
% 1.96/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.96/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.96/1.00  --bmc1_ucm_layered_model                none
% 1.96/1.00  --bmc1_ucm_max_lemma_size               10
% 1.96/1.00  
% 1.96/1.00  ------ AIG Options
% 1.96/1.00  
% 1.96/1.00  --aig_mode                              false
% 1.96/1.00  
% 1.96/1.00  ------ Instantiation Options
% 1.96/1.00  
% 1.96/1.00  --instantiation_flag                    true
% 1.96/1.00  --inst_sos_flag                         false
% 1.96/1.00  --inst_sos_phase                        true
% 1.96/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.96/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.96/1.00  --inst_lit_sel_side                     num_symb
% 1.96/1.00  --inst_solver_per_active                1400
% 1.96/1.00  --inst_solver_calls_frac                1.
% 1.96/1.00  --inst_passive_queue_type               priority_queues
% 1.96/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.96/1.00  --inst_passive_queues_freq              [25;2]
% 1.96/1.00  --inst_dismatching                      true
% 1.96/1.00  --inst_eager_unprocessed_to_passive     true
% 1.96/1.00  --inst_prop_sim_given                   true
% 1.96/1.00  --inst_prop_sim_new                     false
% 1.96/1.00  --inst_subs_new                         false
% 1.96/1.00  --inst_eq_res_simp                      false
% 1.96/1.00  --inst_subs_given                       false
% 1.96/1.00  --inst_orphan_elimination               true
% 1.96/1.00  --inst_learning_loop_flag               true
% 1.96/1.00  --inst_learning_start                   3000
% 1.96/1.00  --inst_learning_factor                  2
% 1.96/1.00  --inst_start_prop_sim_after_learn       3
% 1.96/1.00  --inst_sel_renew                        solver
% 1.96/1.00  --inst_lit_activity_flag                true
% 1.96/1.00  --inst_restr_to_given                   false
% 1.96/1.00  --inst_activity_threshold               500
% 1.96/1.00  --inst_out_proof                        true
% 1.96/1.00  
% 1.96/1.00  ------ Resolution Options
% 1.96/1.00  
% 1.96/1.00  --resolution_flag                       true
% 1.96/1.00  --res_lit_sel                           adaptive
% 1.96/1.00  --res_lit_sel_side                      none
% 1.96/1.00  --res_ordering                          kbo
% 1.96/1.00  --res_to_prop_solver                    active
% 1.96/1.00  --res_prop_simpl_new                    false
% 1.96/1.00  --res_prop_simpl_given                  true
% 1.96/1.00  --res_passive_queue_type                priority_queues
% 1.96/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.96/1.00  --res_passive_queues_freq               [15;5]
% 1.96/1.00  --res_forward_subs                      full
% 1.96/1.00  --res_backward_subs                     full
% 1.96/1.00  --res_forward_subs_resolution           true
% 1.96/1.00  --res_backward_subs_resolution          true
% 1.96/1.00  --res_orphan_elimination                true
% 1.96/1.00  --res_time_limit                        2.
% 1.96/1.00  --res_out_proof                         true
% 1.96/1.00  
% 1.96/1.00  ------ Superposition Options
% 1.96/1.00  
% 1.96/1.00  --superposition_flag                    true
% 1.96/1.00  --sup_passive_queue_type                priority_queues
% 1.96/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.96/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.96/1.00  --demod_completeness_check              fast
% 1.96/1.00  --demod_use_ground                      true
% 1.96/1.00  --sup_to_prop_solver                    passive
% 1.96/1.00  --sup_prop_simpl_new                    true
% 1.96/1.00  --sup_prop_simpl_given                  true
% 1.96/1.00  --sup_fun_splitting                     false
% 1.96/1.00  --sup_smt_interval                      50000
% 1.96/1.00  
% 1.96/1.00  ------ Superposition Simplification Setup
% 1.96/1.00  
% 1.96/1.00  --sup_indices_passive                   []
% 1.96/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.96/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.96/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.96/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.96/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.96/1.00  --sup_full_bw                           [BwDemod]
% 1.96/1.00  --sup_immed_triv                        [TrivRules]
% 1.96/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.96/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.96/1.00  --sup_immed_bw_main                     []
% 1.96/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.96/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.96/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.96/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.96/1.00  
% 1.96/1.00  ------ Combination Options
% 1.96/1.00  
% 1.96/1.00  --comb_res_mult                         3
% 1.96/1.00  --comb_sup_mult                         2
% 1.96/1.00  --comb_inst_mult                        10
% 1.96/1.00  
% 1.96/1.00  ------ Debug Options
% 1.96/1.00  
% 1.96/1.00  --dbg_backtrace                         false
% 1.96/1.00  --dbg_dump_prop_clauses                 false
% 1.96/1.00  --dbg_dump_prop_clauses_file            -
% 1.96/1.00  --dbg_out_stat                          false
% 1.96/1.00  ------ Parsing...
% 1.96/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.96/1.00  
% 1.96/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 1.96/1.00  
% 1.96/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.96/1.00  
% 1.96/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.96/1.00  ------ Proving...
% 1.96/1.00  ------ Problem Properties 
% 1.96/1.00  
% 1.96/1.00  
% 1.96/1.00  clauses                                 16
% 1.96/1.00  conjectures                             3
% 1.96/1.00  EPR                                     1
% 1.96/1.00  Horn                                    16
% 1.96/1.00  unary                                   3
% 1.96/1.00  binary                                  8
% 1.96/1.00  lits                                    37
% 1.96/1.00  lits eq                                 10
% 1.96/1.00  fd_pure                                 0
% 1.96/1.00  fd_pseudo                               0
% 1.96/1.00  fd_cond                                 0
% 1.96/1.00  fd_pseudo_cond                          0
% 1.96/1.00  AC symbols                              0
% 1.96/1.00  
% 1.96/1.00  ------ Schedule dynamic 5 is on 
% 1.96/1.00  
% 1.96/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.96/1.00  
% 1.96/1.00  
% 1.96/1.00  ------ 
% 1.96/1.00  Current options:
% 1.96/1.00  ------ 
% 1.96/1.00  
% 1.96/1.00  ------ Input Options
% 1.96/1.00  
% 1.96/1.00  --out_options                           all
% 1.96/1.00  --tptp_safe_out                         true
% 1.96/1.00  --problem_path                          ""
% 1.96/1.00  --include_path                          ""
% 1.96/1.00  --clausifier                            res/vclausify_rel
% 1.96/1.00  --clausifier_options                    --mode clausify
% 1.96/1.00  --stdin                                 false
% 1.96/1.00  --stats_out                             all
% 1.96/1.00  
% 1.96/1.00  ------ General Options
% 1.96/1.00  
% 1.96/1.00  --fof                                   false
% 1.96/1.00  --time_out_real                         305.
% 1.96/1.00  --time_out_virtual                      -1.
% 1.96/1.00  --symbol_type_check                     false
% 1.96/1.00  --clausify_out                          false
% 1.96/1.00  --sig_cnt_out                           false
% 1.96/1.00  --trig_cnt_out                          false
% 1.96/1.00  --trig_cnt_out_tolerance                1.
% 1.96/1.00  --trig_cnt_out_sk_spl                   false
% 1.96/1.00  --abstr_cl_out                          false
% 1.96/1.00  
% 1.96/1.00  ------ Global Options
% 1.96/1.00  
% 1.96/1.00  --schedule                              default
% 1.96/1.00  --add_important_lit                     false
% 1.96/1.00  --prop_solver_per_cl                    1000
% 1.96/1.00  --min_unsat_core                        false
% 1.96/1.00  --soft_assumptions                      false
% 1.96/1.00  --soft_lemma_size                       3
% 1.96/1.00  --prop_impl_unit_size                   0
% 1.96/1.00  --prop_impl_unit                        []
% 1.96/1.00  --share_sel_clauses                     true
% 1.96/1.00  --reset_solvers                         false
% 1.96/1.00  --bc_imp_inh                            [conj_cone]
% 1.96/1.00  --conj_cone_tolerance                   3.
% 1.96/1.00  --extra_neg_conj                        none
% 1.96/1.00  --large_theory_mode                     true
% 1.96/1.00  --prolific_symb_bound                   200
% 1.96/1.00  --lt_threshold                          2000
% 1.96/1.00  --clause_weak_htbl                      true
% 1.96/1.00  --gc_record_bc_elim                     false
% 1.96/1.00  
% 1.96/1.00  ------ Preprocessing Options
% 1.96/1.00  
% 1.96/1.00  --preprocessing_flag                    true
% 1.96/1.00  --time_out_prep_mult                    0.1
% 1.96/1.00  --splitting_mode                        input
% 1.96/1.00  --splitting_grd                         true
% 1.96/1.00  --splitting_cvd                         false
% 1.96/1.00  --splitting_cvd_svl                     false
% 1.96/1.00  --splitting_nvd                         32
% 1.96/1.00  --sub_typing                            true
% 1.96/1.00  --prep_gs_sim                           true
% 1.96/1.00  --prep_unflatten                        true
% 1.96/1.00  --prep_res_sim                          true
% 1.96/1.00  --prep_upred                            true
% 1.96/1.00  --prep_sem_filter                       exhaustive
% 1.96/1.00  --prep_sem_filter_out                   false
% 1.96/1.00  --pred_elim                             true
% 1.96/1.00  --res_sim_input                         true
% 1.96/1.00  --eq_ax_congr_red                       true
% 1.96/1.00  --pure_diseq_elim                       true
% 1.96/1.00  --brand_transform                       false
% 1.96/1.00  --non_eq_to_eq                          false
% 1.96/1.00  --prep_def_merge                        true
% 1.96/1.00  --prep_def_merge_prop_impl              false
% 1.96/1.00  --prep_def_merge_mbd                    true
% 1.96/1.00  --prep_def_merge_tr_red                 false
% 1.96/1.00  --prep_def_merge_tr_cl                  false
% 1.96/1.00  --smt_preprocessing                     true
% 1.96/1.00  --smt_ac_axioms                         fast
% 1.96/1.00  --preprocessed_out                      false
% 1.96/1.00  --preprocessed_stats                    false
% 1.96/1.00  
% 1.96/1.00  ------ Abstraction refinement Options
% 1.96/1.00  
% 1.96/1.00  --abstr_ref                             []
% 1.96/1.00  --abstr_ref_prep                        false
% 1.96/1.00  --abstr_ref_until_sat                   false
% 1.96/1.00  --abstr_ref_sig_restrict                funpre
% 1.96/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.96/1.00  --abstr_ref_under                       []
% 1.96/1.00  
% 1.96/1.00  ------ SAT Options
% 1.96/1.00  
% 1.96/1.00  --sat_mode                              false
% 1.96/1.00  --sat_fm_restart_options                ""
% 1.96/1.00  --sat_gr_def                            false
% 1.96/1.00  --sat_epr_types                         true
% 1.96/1.00  --sat_non_cyclic_types                  false
% 1.96/1.00  --sat_finite_models                     false
% 1.96/1.00  --sat_fm_lemmas                         false
% 1.96/1.00  --sat_fm_prep                           false
% 1.96/1.00  --sat_fm_uc_incr                        true
% 1.96/1.00  --sat_out_model                         small
% 1.96/1.00  --sat_out_clauses                       false
% 1.96/1.00  
% 1.96/1.00  ------ QBF Options
% 1.96/1.00  
% 1.96/1.00  --qbf_mode                              false
% 1.96/1.00  --qbf_elim_univ                         false
% 1.96/1.00  --qbf_dom_inst                          none
% 1.96/1.00  --qbf_dom_pre_inst                      false
% 1.96/1.00  --qbf_sk_in                             false
% 1.96/1.00  --qbf_pred_elim                         true
% 1.96/1.00  --qbf_split                             512
% 1.96/1.00  
% 1.96/1.00  ------ BMC1 Options
% 1.96/1.00  
% 1.96/1.00  --bmc1_incremental                      false
% 1.96/1.00  --bmc1_axioms                           reachable_all
% 1.96/1.00  --bmc1_min_bound                        0
% 1.96/1.00  --bmc1_max_bound                        -1
% 1.96/1.00  --bmc1_max_bound_default                -1
% 1.96/1.00  --bmc1_symbol_reachability              true
% 1.96/1.00  --bmc1_property_lemmas                  false
% 1.96/1.00  --bmc1_k_induction                      false
% 1.96/1.00  --bmc1_non_equiv_states                 false
% 1.96/1.00  --bmc1_deadlock                         false
% 1.96/1.00  --bmc1_ucm                              false
% 1.96/1.00  --bmc1_add_unsat_core                   none
% 1.96/1.00  --bmc1_unsat_core_children              false
% 1.96/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.96/1.00  --bmc1_out_stat                         full
% 1.96/1.00  --bmc1_ground_init                      false
% 1.96/1.00  --bmc1_pre_inst_next_state              false
% 1.96/1.00  --bmc1_pre_inst_state                   false
% 1.96/1.00  --bmc1_pre_inst_reach_state             false
% 1.96/1.00  --bmc1_out_unsat_core                   false
% 1.96/1.00  --bmc1_aig_witness_out                  false
% 1.96/1.00  --bmc1_verbose                          false
% 1.96/1.00  --bmc1_dump_clauses_tptp                false
% 1.96/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.96/1.00  --bmc1_dump_file                        -
% 1.96/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.96/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.96/1.00  --bmc1_ucm_extend_mode                  1
% 1.96/1.00  --bmc1_ucm_init_mode                    2
% 1.96/1.00  --bmc1_ucm_cone_mode                    none
% 1.96/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.96/1.00  --bmc1_ucm_relax_model                  4
% 1.96/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.96/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.96/1.00  --bmc1_ucm_layered_model                none
% 1.96/1.00  --bmc1_ucm_max_lemma_size               10
% 1.96/1.00  
% 1.96/1.00  ------ AIG Options
% 1.96/1.00  
% 1.96/1.00  --aig_mode                              false
% 1.96/1.00  
% 1.96/1.00  ------ Instantiation Options
% 1.96/1.00  
% 1.96/1.00  --instantiation_flag                    true
% 1.96/1.00  --inst_sos_flag                         false
% 1.96/1.00  --inst_sos_phase                        true
% 1.96/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.96/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.96/1.00  --inst_lit_sel_side                     none
% 1.96/1.00  --inst_solver_per_active                1400
% 1.96/1.00  --inst_solver_calls_frac                1.
% 1.96/1.00  --inst_passive_queue_type               priority_queues
% 1.96/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.96/1.00  --inst_passive_queues_freq              [25;2]
% 1.96/1.00  --inst_dismatching                      true
% 1.96/1.00  --inst_eager_unprocessed_to_passive     true
% 1.96/1.00  --inst_prop_sim_given                   true
% 1.96/1.00  --inst_prop_sim_new                     false
% 1.96/1.00  --inst_subs_new                         false
% 1.96/1.00  --inst_eq_res_simp                      false
% 1.96/1.00  --inst_subs_given                       false
% 1.96/1.00  --inst_orphan_elimination               true
% 1.96/1.00  --inst_learning_loop_flag               true
% 1.96/1.00  --inst_learning_start                   3000
% 1.96/1.00  --inst_learning_factor                  2
% 1.96/1.00  --inst_start_prop_sim_after_learn       3
% 1.96/1.00  --inst_sel_renew                        solver
% 1.96/1.00  --inst_lit_activity_flag                true
% 1.96/1.00  --inst_restr_to_given                   false
% 1.96/1.00  --inst_activity_threshold               500
% 1.96/1.00  --inst_out_proof                        true
% 1.96/1.00  
% 1.96/1.00  ------ Resolution Options
% 1.96/1.00  
% 1.96/1.00  --resolution_flag                       false
% 1.96/1.00  --res_lit_sel                           adaptive
% 1.96/1.00  --res_lit_sel_side                      none
% 1.96/1.00  --res_ordering                          kbo
% 1.96/1.00  --res_to_prop_solver                    active
% 1.96/1.00  --res_prop_simpl_new                    false
% 1.96/1.00  --res_prop_simpl_given                  true
% 1.96/1.00  --res_passive_queue_type                priority_queues
% 1.96/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.96/1.00  --res_passive_queues_freq               [15;5]
% 1.96/1.00  --res_forward_subs                      full
% 1.96/1.00  --res_backward_subs                     full
% 1.96/1.00  --res_forward_subs_resolution           true
% 1.96/1.00  --res_backward_subs_resolution          true
% 1.96/1.00  --res_orphan_elimination                true
% 1.96/1.00  --res_time_limit                        2.
% 1.96/1.00  --res_out_proof                         true
% 1.96/1.00  
% 1.96/1.00  ------ Superposition Options
% 1.96/1.00  
% 1.96/1.00  --superposition_flag                    true
% 1.96/1.00  --sup_passive_queue_type                priority_queues
% 1.96/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.96/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.96/1.00  --demod_completeness_check              fast
% 1.96/1.00  --demod_use_ground                      true
% 1.96/1.00  --sup_to_prop_solver                    passive
% 1.96/1.00  --sup_prop_simpl_new                    true
% 1.96/1.00  --sup_prop_simpl_given                  true
% 1.96/1.00  --sup_fun_splitting                     false
% 1.96/1.00  --sup_smt_interval                      50000
% 1.96/1.00  
% 1.96/1.00  ------ Superposition Simplification Setup
% 1.96/1.00  
% 1.96/1.00  --sup_indices_passive                   []
% 1.96/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.96/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.96/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.96/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.96/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.96/1.00  --sup_full_bw                           [BwDemod]
% 1.96/1.00  --sup_immed_triv                        [TrivRules]
% 1.96/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.96/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.96/1.00  --sup_immed_bw_main                     []
% 1.96/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.96/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.96/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.96/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.96/1.00  
% 1.96/1.00  ------ Combination Options
% 1.96/1.00  
% 1.96/1.00  --comb_res_mult                         3
% 1.96/1.00  --comb_sup_mult                         2
% 1.96/1.00  --comb_inst_mult                        10
% 1.96/1.00  
% 1.96/1.00  ------ Debug Options
% 1.96/1.00  
% 1.96/1.00  --dbg_backtrace                         false
% 1.96/1.00  --dbg_dump_prop_clauses                 false
% 1.96/1.00  --dbg_dump_prop_clauses_file            -
% 1.96/1.00  --dbg_out_stat                          false
% 1.96/1.00  
% 1.96/1.00  
% 1.96/1.00  
% 1.96/1.00  
% 1.96/1.00  ------ Proving...
% 1.96/1.00  
% 1.96/1.00  
% 1.96/1.00  % SZS status Theorem for theBenchmark.p
% 1.96/1.00  
% 1.96/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 1.96/1.00  
% 1.96/1.00  fof(f10,conjecture,(
% 1.96/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/1.00  
% 1.96/1.00  fof(f11,negated_conjecture,(
% 1.96/1.00    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.96/1.00    inference(negated_conjecture,[],[f10])).
% 1.96/1.00  
% 1.96/1.00  fof(f25,plain,(
% 1.96/1.00    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.96/1.00    inference(ennf_transformation,[],[f11])).
% 1.96/1.00  
% 1.96/1.00  fof(f26,plain,(
% 1.96/1.00    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.96/1.00    inference(flattening,[],[f25])).
% 1.96/1.00  
% 1.96/1.00  fof(f27,plain,(
% 1.96/1.00    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & k2_relset_1(sK0,sK1,sK2) = sK1 & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.96/1.00    introduced(choice_axiom,[])).
% 1.96/1.00  
% 1.96/1.00  fof(f28,plain,(
% 1.96/1.00    (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & k2_relset_1(sK0,sK1,sK2) = sK1 & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.96/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f27])).
% 1.96/1.00  
% 1.96/1.00  fof(f45,plain,(
% 1.96/1.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.96/1.00    inference(cnf_transformation,[],[f28])).
% 1.96/1.00  
% 1.96/1.00  fof(f7,axiom,(
% 1.96/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 1.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/1.00  
% 1.96/1.00  fof(f21,plain,(
% 1.96/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.96/1.00    inference(ennf_transformation,[],[f7])).
% 1.96/1.00  
% 1.96/1.00  fof(f37,plain,(
% 1.96/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.96/1.00    inference(cnf_transformation,[],[f21])).
% 1.96/1.00  
% 1.96/1.00  fof(f47,plain,(
% 1.96/1.00    k2_relset_1(sK0,sK1,sK2) = sK1),
% 1.96/1.00    inference(cnf_transformation,[],[f28])).
% 1.96/1.00  
% 1.96/1.00  fof(f3,axiom,(
% 1.96/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 1.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/1.00  
% 1.96/1.00  fof(f16,plain,(
% 1.96/1.00    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.96/1.00    inference(ennf_transformation,[],[f3])).
% 1.96/1.00  
% 1.96/1.00  fof(f17,plain,(
% 1.96/1.00    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.96/1.00    inference(flattening,[],[f16])).
% 1.96/1.00  
% 1.96/1.00  fof(f32,plain,(
% 1.96/1.00    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.96/1.00    inference(cnf_transformation,[],[f17])).
% 1.96/1.00  
% 1.96/1.00  fof(f46,plain,(
% 1.96/1.00    v2_funct_1(sK2)),
% 1.96/1.00    inference(cnf_transformation,[],[f28])).
% 1.96/1.00  
% 1.96/1.00  fof(f43,plain,(
% 1.96/1.00    v1_funct_1(sK2)),
% 1.96/1.00    inference(cnf_transformation,[],[f28])).
% 1.96/1.00  
% 1.96/1.00  fof(f4,axiom,(
% 1.96/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/1.00  
% 1.96/1.00  fof(f18,plain,(
% 1.96/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.96/1.00    inference(ennf_transformation,[],[f4])).
% 1.96/1.00  
% 1.96/1.00  fof(f34,plain,(
% 1.96/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.96/1.00    inference(cnf_transformation,[],[f18])).
% 1.96/1.00  
% 1.96/1.00  fof(f1,axiom,(
% 1.96/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/1.00  
% 1.96/1.00  fof(f12,plain,(
% 1.96/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 1.96/1.00    inference(unused_predicate_definition_removal,[],[f1])).
% 1.96/1.00  
% 1.96/1.00  fof(f13,plain,(
% 1.96/1.00    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 1.96/1.00    inference(ennf_transformation,[],[f12])).
% 1.96/1.00  
% 1.96/1.00  fof(f29,plain,(
% 1.96/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.96/1.00    inference(cnf_transformation,[],[f13])).
% 1.96/1.00  
% 1.96/1.00  fof(f9,axiom,(
% 1.96/1.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 1.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/1.00  
% 1.96/1.00  fof(f23,plain,(
% 1.96/1.00    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.96/1.00    inference(ennf_transformation,[],[f9])).
% 1.96/1.00  
% 1.96/1.00  fof(f24,plain,(
% 1.96/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.96/1.00    inference(flattening,[],[f23])).
% 1.96/1.00  
% 1.96/1.00  fof(f42,plain,(
% 1.96/1.00    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.96/1.00    inference(cnf_transformation,[],[f24])).
% 1.96/1.00  
% 1.96/1.00  fof(f33,plain,(
% 1.96/1.00    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.96/1.00    inference(cnf_transformation,[],[f17])).
% 1.96/1.00  
% 1.96/1.00  fof(f2,axiom,(
% 1.96/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/1.00  
% 1.96/1.00  fof(f14,plain,(
% 1.96/1.00    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.96/1.00    inference(ennf_transformation,[],[f2])).
% 1.96/1.00  
% 1.96/1.00  fof(f15,plain,(
% 1.96/1.00    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.96/1.00    inference(flattening,[],[f14])).
% 1.96/1.00  
% 1.96/1.00  fof(f30,plain,(
% 1.96/1.00    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.96/1.00    inference(cnf_transformation,[],[f15])).
% 1.96/1.00  
% 1.96/1.00  fof(f31,plain,(
% 1.96/1.00    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.96/1.00    inference(cnf_transformation,[],[f15])).
% 1.96/1.00  
% 1.96/1.00  fof(f41,plain,(
% 1.96/1.00    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.96/1.00    inference(cnf_transformation,[],[f24])).
% 1.96/1.00  
% 1.96/1.00  fof(f48,plain,(
% 1.96/1.00    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 1.96/1.00    inference(cnf_transformation,[],[f28])).
% 1.96/1.00  
% 1.96/1.00  fof(f8,axiom,(
% 1.96/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 1.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/1.00  
% 1.96/1.00  fof(f22,plain,(
% 1.96/1.00    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.96/1.00    inference(ennf_transformation,[],[f8])).
% 1.96/1.00  
% 1.96/1.00  fof(f39,plain,(
% 1.96/1.00    ( ! [X2,X0,X1] : (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.96/1.00    inference(cnf_transformation,[],[f22])).
% 1.96/1.00  
% 1.96/1.00  fof(f6,axiom,(
% 1.96/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 1.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/1.00  
% 1.96/1.00  fof(f20,plain,(
% 1.96/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.96/1.00    inference(ennf_transformation,[],[f6])).
% 1.96/1.00  
% 1.96/1.00  fof(f36,plain,(
% 1.96/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.96/1.00    inference(cnf_transformation,[],[f20])).
% 1.96/1.00  
% 1.96/1.00  fof(f5,axiom,(
% 1.96/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)))),
% 1.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/1.00  
% 1.96/1.00  fof(f19,plain,(
% 1.96/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.96/1.00    inference(ennf_transformation,[],[f5])).
% 1.96/1.00  
% 1.96/1.00  fof(f35,plain,(
% 1.96/1.00    ( ! [X2,X0,X3,X1] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.96/1.00    inference(cnf_transformation,[],[f19])).
% 1.96/1.00  
% 1.96/1.00  cnf(c_17,negated_conjecture,
% 1.96/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 1.96/1.00      inference(cnf_transformation,[],[f45]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_453,negated_conjecture,
% 1.96/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 1.96/1.00      inference(subtyping,[status(esa)],[c_17]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_769,plain,
% 1.96/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 1.96/1.00      inference(predicate_to_equality,[status(thm)],[c_453]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_8,plain,
% 1.96/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.96/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 1.96/1.00      inference(cnf_transformation,[],[f37]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_457,plain,
% 1.96/1.00      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X1_46,X2_46)))
% 1.96/1.00      | k2_relset_1(X1_46,X2_46,X0_46) = k2_relat_1(X0_46) ),
% 1.96/1.00      inference(subtyping,[status(esa)],[c_8]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_766,plain,
% 1.96/1.00      ( k2_relset_1(X0_46,X1_46,X2_46) = k2_relat_1(X2_46)
% 1.96/1.00      | m1_subset_1(X2_46,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46))) != iProver_top ),
% 1.96/1.00      inference(predicate_to_equality,[status(thm)],[c_457]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_1061,plain,
% 1.96/1.00      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 1.96/1.00      inference(superposition,[status(thm)],[c_769,c_766]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_15,negated_conjecture,
% 1.96/1.00      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 1.96/1.00      inference(cnf_transformation,[],[f47]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_454,negated_conjecture,
% 1.96/1.00      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 1.96/1.00      inference(subtyping,[status(esa)],[c_15]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_1062,plain,
% 1.96/1.00      ( k2_relat_1(sK2) = sK1 ),
% 1.96/1.00      inference(light_normalisation,[status(thm)],[c_1061,c_454]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_4,plain,
% 1.96/1.00      ( ~ v2_funct_1(X0)
% 1.96/1.00      | ~ v1_relat_1(X0)
% 1.96/1.00      | ~ v1_funct_1(X0)
% 1.96/1.00      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 1.96/1.00      inference(cnf_transformation,[],[f32]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_16,negated_conjecture,
% 1.96/1.00      ( v2_funct_1(sK2) ),
% 1.96/1.00      inference(cnf_transformation,[],[f46]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_215,plain,
% 1.96/1.00      ( ~ v1_relat_1(X0)
% 1.96/1.00      | ~ v1_funct_1(X0)
% 1.96/1.00      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 1.96/1.00      | sK2 != X0 ),
% 1.96/1.00      inference(resolution_lifted,[status(thm)],[c_4,c_16]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_216,plain,
% 1.96/1.00      ( ~ v1_relat_1(sK2)
% 1.96/1.00      | ~ v1_funct_1(sK2)
% 1.96/1.00      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 1.96/1.00      inference(unflattening,[status(thm)],[c_215]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_19,negated_conjecture,
% 1.96/1.00      ( v1_funct_1(sK2) ),
% 1.96/1.00      inference(cnf_transformation,[],[f43]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_218,plain,
% 1.96/1.00      ( ~ v1_relat_1(sK2)
% 1.96/1.00      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 1.96/1.00      inference(global_propositional_subsumption,
% 1.96/1.00                [status(thm)],
% 1.96/1.00                [c_216,c_19]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_451,plain,
% 1.96/1.00      ( ~ v1_relat_1(sK2)
% 1.96/1.00      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 1.96/1.00      inference(subtyping,[status(esa)],[c_218]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_771,plain,
% 1.96/1.00      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 1.96/1.00      | v1_relat_1(sK2) != iProver_top ),
% 1.96/1.00      inference(predicate_to_equality,[status(thm)],[c_451]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_5,plain,
% 1.96/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.96/1.00      | v1_relat_1(X0) ),
% 1.96/1.00      inference(cnf_transformation,[],[f34]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_460,plain,
% 1.96/1.00      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X1_46,X2_46)))
% 1.96/1.00      | v1_relat_1(X0_46) ),
% 1.96/1.00      inference(subtyping,[status(esa)],[c_5]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_886,plain,
% 1.96/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 1.96/1.00      | v1_relat_1(sK2) ),
% 1.96/1.00      inference(instantiation,[status(thm)],[c_460]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_897,plain,
% 1.96/1.00      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 1.96/1.00      inference(global_propositional_subsumption,
% 1.96/1.00                [status(thm)],
% 1.96/1.00                [c_771,c_17,c_451,c_886]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_1091,plain,
% 1.96/1.00      ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
% 1.96/1.00      inference(demodulation,[status(thm)],[c_1062,c_897]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_0,plain,
% 1.96/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 1.96/1.00      inference(cnf_transformation,[],[f29]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_11,plain,
% 1.96/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 1.96/1.00      | ~ r1_tarski(k2_relat_1(X0),X1)
% 1.96/1.00      | ~ v1_relat_1(X0)
% 1.96/1.00      | ~ v1_funct_1(X0) ),
% 1.96/1.00      inference(cnf_transformation,[],[f42]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_293,plain,
% 1.96/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.96/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X3)))
% 1.96/1.00      | ~ v1_relat_1(X2)
% 1.96/1.00      | ~ v1_funct_1(X2)
% 1.96/1.00      | X3 != X1
% 1.96/1.00      | k2_relat_1(X2) != X0 ),
% 1.96/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_11]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_294,plain,
% 1.96/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 1.96/1.00      | ~ m1_subset_1(k2_relat_1(X0),k1_zfmisc_1(X1))
% 1.96/1.00      | ~ v1_relat_1(X0)
% 1.96/1.00      | ~ v1_funct_1(X0) ),
% 1.96/1.00      inference(unflattening,[status(thm)],[c_293]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_448,plain,
% 1.96/1.00      ( m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_46),X1_46)))
% 1.96/1.00      | ~ m1_subset_1(k2_relat_1(X0_46),k1_zfmisc_1(X1_46))
% 1.96/1.00      | ~ v1_relat_1(X0_46)
% 1.96/1.00      | ~ v1_funct_1(X0_46) ),
% 1.96/1.00      inference(subtyping,[status(esa)],[c_294]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_774,plain,
% 1.96/1.00      ( m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_46),X1_46))) = iProver_top
% 1.96/1.00      | m1_subset_1(k2_relat_1(X0_46),k1_zfmisc_1(X1_46)) != iProver_top
% 1.96/1.00      | v1_relat_1(X0_46) != iProver_top
% 1.96/1.00      | v1_funct_1(X0_46) != iProver_top ),
% 1.96/1.00      inference(predicate_to_equality,[status(thm)],[c_448]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_1569,plain,
% 1.96/1.00      ( m1_subset_1(k2_relat_1(k2_funct_1(sK2)),k1_zfmisc_1(X0_46)) != iProver_top
% 1.96/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0_46))) = iProver_top
% 1.96/1.00      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 1.96/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 1.96/1.00      inference(superposition,[status(thm)],[c_1091,c_774]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_3,plain,
% 1.96/1.00      ( ~ v2_funct_1(X0)
% 1.96/1.00      | ~ v1_relat_1(X0)
% 1.96/1.00      | ~ v1_funct_1(X0)
% 1.96/1.00      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 1.96/1.00      inference(cnf_transformation,[],[f33]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_229,plain,
% 1.96/1.00      ( ~ v1_relat_1(X0)
% 1.96/1.00      | ~ v1_funct_1(X0)
% 1.96/1.00      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 1.96/1.00      | sK2 != X0 ),
% 1.96/1.00      inference(resolution_lifted,[status(thm)],[c_3,c_16]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_230,plain,
% 1.96/1.00      ( ~ v1_relat_1(sK2)
% 1.96/1.00      | ~ v1_funct_1(sK2)
% 1.96/1.00      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 1.96/1.00      inference(unflattening,[status(thm)],[c_229]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_54,plain,
% 1.96/1.00      ( ~ v2_funct_1(sK2)
% 1.96/1.00      | ~ v1_relat_1(sK2)
% 1.96/1.00      | ~ v1_funct_1(sK2)
% 1.96/1.00      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 1.96/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_232,plain,
% 1.96/1.00      ( ~ v1_relat_1(sK2)
% 1.96/1.00      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 1.96/1.00      inference(global_propositional_subsumption,
% 1.96/1.00                [status(thm)],
% 1.96/1.00                [c_230,c_19,c_16,c_54]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_450,plain,
% 1.96/1.00      ( ~ v1_relat_1(sK2)
% 1.96/1.00      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 1.96/1.00      inference(subtyping,[status(esa)],[c_232]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_772,plain,
% 1.96/1.00      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 1.96/1.00      | v1_relat_1(sK2) != iProver_top ),
% 1.96/1.00      inference(predicate_to_equality,[status(thm)],[c_450]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_923,plain,
% 1.96/1.00      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 1.96/1.00      inference(global_propositional_subsumption,
% 1.96/1.00                [status(thm)],
% 1.96/1.00                [c_772,c_17,c_450,c_886]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_1611,plain,
% 1.96/1.00      ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(X0_46)) != iProver_top
% 1.96/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0_46))) = iProver_top
% 1.96/1.00      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 1.96/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 1.96/1.00      inference(light_normalisation,[status(thm)],[c_1569,c_923]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_20,plain,
% 1.96/1.00      ( v1_funct_1(sK2) = iProver_top ),
% 1.96/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_22,plain,
% 1.96/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 1.96/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_2,plain,
% 1.96/1.00      ( ~ v1_relat_1(X0)
% 1.96/1.00      | v1_relat_1(k2_funct_1(X0))
% 1.96/1.00      | ~ v1_funct_1(X0) ),
% 1.96/1.00      inference(cnf_transformation,[],[f30]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_56,plain,
% 1.96/1.00      ( v1_relat_1(X0) != iProver_top
% 1.96/1.00      | v1_relat_1(k2_funct_1(X0)) = iProver_top
% 1.96/1.00      | v1_funct_1(X0) != iProver_top ),
% 1.96/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_58,plain,
% 1.96/1.00      ( v1_relat_1(k2_funct_1(sK2)) = iProver_top
% 1.96/1.00      | v1_relat_1(sK2) != iProver_top
% 1.96/1.00      | v1_funct_1(sK2) != iProver_top ),
% 1.96/1.00      inference(instantiation,[status(thm)],[c_56]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_1,plain,
% 1.96/1.00      ( ~ v1_relat_1(X0)
% 1.96/1.00      | ~ v1_funct_1(X0)
% 1.96/1.00      | v1_funct_1(k2_funct_1(X0)) ),
% 1.96/1.00      inference(cnf_transformation,[],[f31]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_59,plain,
% 1.96/1.00      ( v1_relat_1(X0) != iProver_top
% 1.96/1.00      | v1_funct_1(X0) != iProver_top
% 1.96/1.00      | v1_funct_1(k2_funct_1(X0)) = iProver_top ),
% 1.96/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_61,plain,
% 1.96/1.00      ( v1_relat_1(sK2) != iProver_top
% 1.96/1.00      | v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 1.96/1.00      | v1_funct_1(sK2) != iProver_top ),
% 1.96/1.00      inference(instantiation,[status(thm)],[c_59]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_887,plain,
% 1.96/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 1.96/1.00      | v1_relat_1(sK2) = iProver_top ),
% 1.96/1.00      inference(predicate_to_equality,[status(thm)],[c_886]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_1632,plain,
% 1.96/1.00      ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(X0_46)) != iProver_top
% 1.96/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0_46))) = iProver_top ),
% 1.96/1.00      inference(global_propositional_subsumption,
% 1.96/1.00                [status(thm)],
% 1.96/1.00                [c_1611,c_20,c_22,c_58,c_61,c_887]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_12,plain,
% 1.96/1.00      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 1.96/1.00      | ~ r1_tarski(k2_relat_1(X0),X1)
% 1.96/1.00      | ~ v1_relat_1(X0)
% 1.96/1.00      | ~ v1_funct_1(X0) ),
% 1.96/1.00      inference(cnf_transformation,[],[f41]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_14,negated_conjecture,
% 1.96/1.00      ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
% 1.96/1.00      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 1.96/1.00      | ~ v1_funct_1(k2_funct_1(sK2)) ),
% 1.96/1.00      inference(cnf_transformation,[],[f48]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_249,plain,
% 1.96/1.00      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 1.96/1.00      | ~ r1_tarski(k2_relat_1(X0),X1)
% 1.96/1.00      | ~ v1_relat_1(X0)
% 1.96/1.00      | ~ v1_funct_1(X0)
% 1.96/1.00      | ~ v1_funct_1(k2_funct_1(sK2))
% 1.96/1.00      | k1_relat_1(X0) != sK1
% 1.96/1.00      | k2_funct_1(sK2) != X0
% 1.96/1.00      | sK0 != X1 ),
% 1.96/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_14]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_250,plain,
% 1.96/1.00      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 1.96/1.00      | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0)
% 1.96/1.00      | ~ v1_relat_1(k2_funct_1(sK2))
% 1.96/1.00      | ~ v1_funct_1(k2_funct_1(sK2))
% 1.96/1.00      | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
% 1.96/1.00      inference(unflattening,[status(thm)],[c_249]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_262,plain,
% 1.96/1.00      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 1.96/1.00      | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0)
% 1.96/1.00      | ~ v1_funct_1(k2_funct_1(sK2))
% 1.96/1.00      | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
% 1.96/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_250,c_5]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_311,plain,
% 1.96/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.96/1.00      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 1.96/1.00      | ~ v1_funct_1(k2_funct_1(sK2))
% 1.96/1.00      | k1_relat_1(k2_funct_1(sK2)) != sK1
% 1.96/1.00      | k2_relat_1(k2_funct_1(sK2)) != X0
% 1.96/1.00      | sK0 != X1 ),
% 1.96/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_262]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_312,plain,
% 1.96/1.00      ( ~ m1_subset_1(k2_relat_1(k2_funct_1(sK2)),k1_zfmisc_1(sK0))
% 1.96/1.00      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 1.96/1.00      | ~ v1_funct_1(k2_funct_1(sK2))
% 1.96/1.00      | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
% 1.96/1.00      inference(unflattening,[status(thm)],[c_311]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_447,plain,
% 1.96/1.00      ( ~ m1_subset_1(k2_relat_1(k2_funct_1(sK2)),k1_zfmisc_1(sK0))
% 1.96/1.00      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 1.96/1.00      | ~ v1_funct_1(k2_funct_1(sK2))
% 1.96/1.00      | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
% 1.96/1.00      inference(subtyping,[status(esa)],[c_312]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_775,plain,
% 1.96/1.00      ( k1_relat_1(k2_funct_1(sK2)) != sK1
% 1.96/1.00      | m1_subset_1(k2_relat_1(k2_funct_1(sK2)),k1_zfmisc_1(sK0)) != iProver_top
% 1.96/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 1.96/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 1.96/1.00      inference(predicate_to_equality,[status(thm)],[c_447]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_510,plain,
% 1.96/1.00      ( k1_relat_1(k2_funct_1(sK2)) != sK1
% 1.96/1.00      | m1_subset_1(k2_relat_1(k2_funct_1(sK2)),k1_zfmisc_1(sK0)) != iProver_top
% 1.96/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 1.96/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 1.96/1.00      inference(predicate_to_equality,[status(thm)],[c_447]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_953,plain,
% 1.96/1.00      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 1.96/1.00      | m1_subset_1(k2_relat_1(k2_funct_1(sK2)),k1_zfmisc_1(sK0)) != iProver_top
% 1.96/1.00      | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
% 1.96/1.00      inference(global_propositional_subsumption,
% 1.96/1.00                [status(thm)],
% 1.96/1.00                [c_775,c_20,c_22,c_61,c_510,c_887]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_954,plain,
% 1.96/1.00      ( k1_relat_1(k2_funct_1(sK2)) != sK1
% 1.96/1.00      | m1_subset_1(k2_relat_1(k2_funct_1(sK2)),k1_zfmisc_1(sK0)) != iProver_top
% 1.96/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 1.96/1.00      inference(renaming,[status(thm)],[c_953]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_957,plain,
% 1.96/1.00      ( k2_relat_1(sK2) != sK1
% 1.96/1.00      | m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0)) != iProver_top
% 1.96/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 1.96/1.00      inference(light_normalisation,[status(thm)],[c_954,c_897,c_923]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_1090,plain,
% 1.96/1.00      ( sK1 != sK1
% 1.96/1.00      | m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0)) != iProver_top
% 1.96/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 1.96/1.00      inference(demodulation,[status(thm)],[c_1062,c_957]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_1094,plain,
% 1.96/1.00      ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0)) != iProver_top
% 1.96/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 1.96/1.00      inference(equality_resolution_simp,[status(thm)],[c_1090]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_1640,plain,
% 1.96/1.00      ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0)) != iProver_top ),
% 1.96/1.00      inference(superposition,[status(thm)],[c_1632,c_1094]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_9,plain,
% 1.96/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.96/1.00      | k8_relset_1(X1,X2,X0,X2) = k1_relset_1(X1,X2,X0) ),
% 1.96/1.00      inference(cnf_transformation,[],[f39]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_456,plain,
% 1.96/1.00      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X1_46,X2_46)))
% 1.96/1.00      | k8_relset_1(X1_46,X2_46,X0_46,X2_46) = k1_relset_1(X1_46,X2_46,X0_46) ),
% 1.96/1.00      inference(subtyping,[status(esa)],[c_9]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_767,plain,
% 1.96/1.00      ( k8_relset_1(X0_46,X1_46,X2_46,X1_46) = k1_relset_1(X0_46,X1_46,X2_46)
% 1.96/1.00      | m1_subset_1(X2_46,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46))) != iProver_top ),
% 1.96/1.00      inference(predicate_to_equality,[status(thm)],[c_456]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_1291,plain,
% 1.96/1.00      ( k8_relset_1(sK0,sK1,sK2,sK1) = k1_relset_1(sK0,sK1,sK2) ),
% 1.96/1.00      inference(superposition,[status(thm)],[c_769,c_767]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_7,plain,
% 1.96/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.96/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 1.96/1.00      inference(cnf_transformation,[],[f36]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_458,plain,
% 1.96/1.00      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X1_46,X2_46)))
% 1.96/1.00      | k1_relset_1(X1_46,X2_46,X0_46) = k1_relat_1(X0_46) ),
% 1.96/1.00      inference(subtyping,[status(esa)],[c_7]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_765,plain,
% 1.96/1.00      ( k1_relset_1(X0_46,X1_46,X2_46) = k1_relat_1(X2_46)
% 1.96/1.00      | m1_subset_1(X2_46,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46))) != iProver_top ),
% 1.96/1.00      inference(predicate_to_equality,[status(thm)],[c_458]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_1057,plain,
% 1.96/1.00      ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
% 1.96/1.00      inference(superposition,[status(thm)],[c_769,c_765]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_1298,plain,
% 1.96/1.00      ( k8_relset_1(sK0,sK1,sK2,sK1) = k1_relat_1(sK2) ),
% 1.96/1.00      inference(light_normalisation,[status(thm)],[c_1291,c_1057]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_6,plain,
% 1.96/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.96/1.00      | m1_subset_1(k8_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X1)) ),
% 1.96/1.00      inference(cnf_transformation,[],[f35]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_459,plain,
% 1.96/1.00      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X1_46,X2_46)))
% 1.96/1.00      | m1_subset_1(k8_relset_1(X1_46,X2_46,X0_46,X3_46),k1_zfmisc_1(X1_46)) ),
% 1.96/1.00      inference(subtyping,[status(esa)],[c_6]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_764,plain,
% 1.96/1.00      ( m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X1_46,X2_46))) != iProver_top
% 1.96/1.00      | m1_subset_1(k8_relset_1(X1_46,X2_46,X0_46,X3_46),k1_zfmisc_1(X1_46)) = iProver_top ),
% 1.96/1.00      inference(predicate_to_equality,[status(thm)],[c_459]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_1304,plain,
% 1.96/1.00      ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0)) = iProver_top
% 1.96/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 1.96/1.00      inference(superposition,[status(thm)],[c_1298,c_764]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(contradiction,plain,
% 1.96/1.00      ( $false ),
% 1.96/1.00      inference(minisat,[status(thm)],[c_1640,c_1304,c_22]) ).
% 1.96/1.00  
% 1.96/1.00  
% 1.96/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 1.96/1.00  
% 1.96/1.00  ------                               Statistics
% 1.96/1.00  
% 1.96/1.00  ------ General
% 1.96/1.00  
% 1.96/1.00  abstr_ref_over_cycles:                  0
% 1.96/1.00  abstr_ref_under_cycles:                 0
% 1.96/1.00  gc_basic_clause_elim:                   0
% 1.96/1.00  forced_gc_time:                         0
% 1.96/1.00  parsing_time:                           0.009
% 1.96/1.00  unif_index_cands_time:                  0.
% 1.96/1.00  unif_index_add_time:                    0.
% 1.96/1.00  orderings_time:                         0.
% 1.96/1.00  out_proof_time:                         0.014
% 1.96/1.00  total_time:                             0.088
% 1.96/1.00  num_of_symbols:                         51
% 1.96/1.00  num_of_terms:                           1358
% 1.96/1.00  
% 1.96/1.00  ------ Preprocessing
% 1.96/1.00  
% 1.96/1.00  num_of_splits:                          0
% 1.96/1.00  num_of_split_atoms:                     0
% 1.96/1.00  num_of_reused_defs:                     0
% 1.96/1.00  num_eq_ax_congr_red:                    34
% 1.96/1.00  num_of_sem_filtered_clauses:            1
% 1.96/1.00  num_of_subtypes:                        2
% 1.96/1.00  monotx_restored_types:                  0
% 1.96/1.00  sat_num_of_epr_types:                   0
% 1.96/1.00  sat_num_of_non_cyclic_types:            0
% 1.96/1.00  sat_guarded_non_collapsed_types:        0
% 1.96/1.00  num_pure_diseq_elim:                    0
% 1.96/1.00  simp_replaced_by:                       0
% 1.96/1.00  res_preprocessed:                       92
% 1.96/1.00  prep_upred:                             0
% 1.96/1.00  prep_unflattend:                        8
% 1.96/1.00  smt_new_axioms:                         0
% 1.96/1.00  pred_elim_cands:                        3
% 1.96/1.00  pred_elim:                              3
% 1.96/1.00  pred_elim_cl:                           3
% 1.96/1.00  pred_elim_cycles:                       5
% 1.96/1.00  merged_defs:                            0
% 1.96/1.00  merged_defs_ncl:                        0
% 1.96/1.00  bin_hyper_res:                          0
% 1.96/1.00  prep_cycles:                            4
% 1.96/1.00  pred_elim_time:                         0.002
% 1.96/1.00  splitting_time:                         0.
% 1.96/1.00  sem_filter_time:                        0.
% 1.96/1.00  monotx_time:                            0.
% 1.96/1.00  subtype_inf_time:                       0.
% 1.96/1.00  
% 1.96/1.00  ------ Problem properties
% 1.96/1.00  
% 1.96/1.00  clauses:                                16
% 1.96/1.00  conjectures:                            3
% 1.96/1.00  epr:                                    1
% 1.96/1.00  horn:                                   16
% 1.96/1.00  ground:                                 7
% 1.96/1.00  unary:                                  3
% 1.96/1.00  binary:                                 8
% 1.96/1.00  lits:                                   37
% 1.96/1.00  lits_eq:                                10
% 1.96/1.00  fd_pure:                                0
% 1.96/1.00  fd_pseudo:                              0
% 1.96/1.00  fd_cond:                                0
% 1.96/1.00  fd_pseudo_cond:                         0
% 1.96/1.00  ac_symbols:                             0
% 1.96/1.00  
% 1.96/1.00  ------ Propositional Solver
% 1.96/1.00  
% 1.96/1.00  prop_solver_calls:                      27
% 1.96/1.00  prop_fast_solver_calls:                 530
% 1.96/1.00  smt_solver_calls:                       0
% 1.96/1.00  smt_fast_solver_calls:                  0
% 1.96/1.00  prop_num_of_clauses:                    484
% 1.96/1.00  prop_preprocess_simplified:             2634
% 1.96/1.00  prop_fo_subsumed:                       9
% 1.96/1.00  prop_solver_time:                       0.
% 1.96/1.00  smt_solver_time:                        0.
% 1.96/1.00  smt_fast_solver_time:                   0.
% 1.96/1.00  prop_fast_solver_time:                  0.
% 1.96/1.00  prop_unsat_core_time:                   0.
% 1.96/1.00  
% 1.96/1.00  ------ QBF
% 1.96/1.00  
% 1.96/1.00  qbf_q_res:                              0
% 1.96/1.00  qbf_num_tautologies:                    0
% 1.96/1.00  qbf_prep_cycles:                        0
% 1.96/1.00  
% 1.96/1.00  ------ BMC1
% 1.96/1.00  
% 1.96/1.00  bmc1_current_bound:                     -1
% 1.96/1.00  bmc1_last_solved_bound:                 -1
% 1.96/1.00  bmc1_unsat_core_size:                   -1
% 1.96/1.00  bmc1_unsat_core_parents_size:           -1
% 1.96/1.00  bmc1_merge_next_fun:                    0
% 1.96/1.00  bmc1_unsat_core_clauses_time:           0.
% 1.96/1.00  
% 1.96/1.00  ------ Instantiation
% 1.96/1.00  
% 1.96/1.00  inst_num_of_clauses:                    165
% 1.96/1.00  inst_num_in_passive:                    4
% 1.96/1.00  inst_num_in_active:                     121
% 1.96/1.00  inst_num_in_unprocessed:                41
% 1.96/1.00  inst_num_of_loops:                      140
% 1.96/1.00  inst_num_of_learning_restarts:          0
% 1.96/1.00  inst_num_moves_active_passive:          14
% 1.96/1.00  inst_lit_activity:                      0
% 1.96/1.00  inst_lit_activity_moves:                0
% 1.96/1.00  inst_num_tautologies:                   0
% 1.96/1.00  inst_num_prop_implied:                  0
% 1.96/1.00  inst_num_existing_simplified:           0
% 1.96/1.00  inst_num_eq_res_simplified:             0
% 1.96/1.00  inst_num_child_elim:                    0
% 1.96/1.00  inst_num_of_dismatching_blockings:      43
% 1.96/1.00  inst_num_of_non_proper_insts:           158
% 1.96/1.00  inst_num_of_duplicates:                 0
% 1.96/1.00  inst_inst_num_from_inst_to_res:         0
% 1.96/1.00  inst_dismatching_checking_time:         0.
% 1.96/1.00  
% 1.96/1.00  ------ Resolution
% 1.96/1.00  
% 1.96/1.00  res_num_of_clauses:                     0
% 1.96/1.00  res_num_in_passive:                     0
% 1.96/1.00  res_num_in_active:                      0
% 1.96/1.00  res_num_of_loops:                       96
% 1.96/1.00  res_forward_subset_subsumed:            20
% 1.96/1.00  res_backward_subset_subsumed:           2
% 1.96/1.00  res_forward_subsumed:                   0
% 1.96/1.00  res_backward_subsumed:                  0
% 1.96/1.00  res_forward_subsumption_resolution:     1
% 1.96/1.00  res_backward_subsumption_resolution:    0
% 1.96/1.00  res_clause_to_clause_subsumption:       60
% 1.96/1.00  res_orphan_elimination:                 0
% 1.96/1.00  res_tautology_del:                      35
% 1.96/1.00  res_num_eq_res_simplified:              0
% 1.96/1.00  res_num_sel_changes:                    0
% 1.96/1.00  res_moves_from_active_to_pass:          0
% 1.96/1.00  
% 1.96/1.00  ------ Superposition
% 1.96/1.00  
% 1.96/1.00  sup_time_total:                         0.
% 1.96/1.00  sup_time_generating:                    0.
% 1.96/1.00  sup_time_sim_full:                      0.
% 1.96/1.00  sup_time_sim_immed:                     0.
% 1.96/1.00  
% 1.96/1.00  sup_num_of_clauses:                     35
% 1.96/1.00  sup_num_in_active:                      25
% 1.96/1.00  sup_num_in_passive:                     10
% 1.96/1.00  sup_num_of_loops:                       27
% 1.96/1.00  sup_fw_superposition:                   11
% 1.96/1.00  sup_bw_superposition:                   15
% 1.96/1.00  sup_immediate_simplified:               4
% 1.96/1.00  sup_given_eliminated:                   0
% 1.96/1.00  comparisons_done:                       0
% 1.96/1.00  comparisons_avoided:                    0
% 1.96/1.00  
% 1.96/1.00  ------ Simplifications
% 1.96/1.00  
% 1.96/1.00  
% 1.96/1.00  sim_fw_subset_subsumed:                 0
% 1.96/1.00  sim_bw_subset_subsumed:                 1
% 1.96/1.00  sim_fw_subsumed:                        0
% 1.96/1.00  sim_bw_subsumed:                        0
% 1.96/1.00  sim_fw_subsumption_res:                 0
% 1.96/1.00  sim_bw_subsumption_res:                 0
% 1.96/1.00  sim_tautology_del:                      1
% 1.96/1.00  sim_eq_tautology_del:                   0
% 1.96/1.00  sim_eq_res_simp:                        1
% 1.96/1.00  sim_fw_demodulated:                     0
% 1.96/1.00  sim_bw_demodulated:                     2
% 1.96/1.00  sim_light_normalised:                   7
% 1.96/1.00  sim_joinable_taut:                      0
% 1.96/1.00  sim_joinable_simp:                      0
% 1.96/1.00  sim_ac_normalised:                      0
% 1.96/1.00  sim_smt_subsumption:                    0
% 1.96/1.00  
%------------------------------------------------------------------------------
