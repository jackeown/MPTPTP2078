%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1094+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:52 EST 2020

% Result     : Theorem 1.09s
% Output     : CNFRefutation 1.09s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 181 expanded)
%              Number of clauses        :   52 (  60 expanded)
%              Number of leaves         :   11 (  30 expanded)
%              Depth                    :   17
%              Number of atoms          :  263 ( 666 expanded)
%              Number of equality atoms :   72 (  81 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_finset_1(X1)
        & v1_finset_1(X0) )
     => v1_finset_1(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k2_zfmisc_1(X0,X1))
      | ~ v1_finset_1(X1)
      | ~ v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f17,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k2_zfmisc_1(X0,X1))
      | ~ v1_finset_1(X1)
      | ~ v1_finset_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k2_zfmisc_1(X0,X1))
      | ~ v1_finset_1(X1)
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f37,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f9])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_finset_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_finset_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_finset_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_finset_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_finset_1(k1_relat_1(X0))
      <=> v1_finset_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v1_finset_1(k1_relat_1(X0))
        <=> v1_finset_1(X0) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f24,plain,(
    ? [X0] :
      ( ( v1_finset_1(k1_relat_1(X0))
      <~> v1_finset_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f25,plain,(
    ? [X0] :
      ( ( v1_finset_1(k1_relat_1(X0))
      <~> v1_finset_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f26,plain,(
    ? [X0] :
      ( ( ~ v1_finset_1(X0)
        | ~ v1_finset_1(k1_relat_1(X0)) )
      & ( v1_finset_1(X0)
        | v1_finset_1(k1_relat_1(X0)) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f27,plain,(
    ? [X0] :
      ( ( ~ v1_finset_1(X0)
        | ~ v1_finset_1(k1_relat_1(X0)) )
      & ( v1_finset_1(X0)
        | v1_finset_1(k1_relat_1(X0)) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f28,plain,
    ( ? [X0] :
        ( ( ~ v1_finset_1(X0)
          | ~ v1_finset_1(k1_relat_1(X0)) )
        & ( v1_finset_1(X0)
          | v1_finset_1(k1_relat_1(X0)) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ( ~ v1_finset_1(sK0)
        | ~ v1_finset_1(k1_relat_1(sK0)) )
      & ( v1_finset_1(sK0)
        | v1_finset_1(k1_relat_1(sK0)) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ( ~ v1_finset_1(sK0)
      | ~ v1_finset_1(k1_relat_1(sK0)) )
    & ( v1_finset_1(sK0)
      | v1_finset_1(k1_relat_1(sK0)) )
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).

fof(f40,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => k9_relat_1(k9_funct_3(k1_relat_1(X0),k2_relat_1(X0)),X0) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( k9_relat_1(k9_funct_3(k1_relat_1(X0),k2_relat_1(X0)),X0) = k1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f19,plain,(
    ! [X0] :
      ( k9_relat_1(k9_funct_3(k1_relat_1(X0),k2_relat_1(X0)),X0) = k1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f36,plain,(
    ! [X0] :
      ( k9_relat_1(k9_funct_3(k1_relat_1(X0),k2_relat_1(X0)),X0) = k1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f41,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_finset_1(X1)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => v1_finset_1(k9_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k9_relat_1(X0,X1))
      | ~ v1_finset_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f15,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k9_relat_1(X0,X1))
      | ~ v1_finset_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k9_relat_1(X0,X1))
      | ~ v1_finset_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f43,plain,
    ( ~ v1_finset_1(sK0)
    | ~ v1_finset_1(k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f29])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_funct_1(k7_funct_3(X0,X1))
      & v1_relat_1(k7_funct_3(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : v1_funct_1(k7_funct_3(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f5,axiom,(
    ! [X0,X1] : k7_funct_3(X0,X1) = k9_funct_3(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k7_funct_3(X0,X1) = k9_funct_3(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f44,plain,(
    ! [X0,X1] : v1_funct_1(k9_funct_3(X0,X1)) ),
    inference(definition_unfolding,[],[f32,f35])).

fof(f31,plain,(
    ! [X0,X1] : v1_relat_1(k7_funct_3(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f45,plain,(
    ! [X0,X1] : v1_relat_1(k9_funct_3(X0,X1)) ),
    inference(definition_unfolding,[],[f31,f35])).

fof(f42,plain,
    ( v1_finset_1(sK0)
    | v1_finset_1(k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f29])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_finset_1(k1_relat_1(X0))
       => v1_finset_1(k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( v1_finset_1(k2_relat_1(X0))
      | ~ v1_finset_1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f22,plain,(
    ! [X0] :
      ( v1_finset_1(k2_relat_1(X0))
      | ~ v1_finset_1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f38,plain,(
    ! [X0] :
      ( v1_finset_1(k2_relat_1(X0))
      | ~ v1_finset_1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_4,plain,
    ( ~ v1_finset_1(X0)
    | ~ v1_finset_1(X1)
    | v1_finset_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_732,plain,
    ( ~ v1_finset_1(X0_40)
    | ~ v1_finset_1(X1_40)
    | v1_finset_1(k2_zfmisc_1(X0_40,X1_40)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1083,plain,
    ( v1_finset_1(X0_40) != iProver_top
    | v1_finset_1(X1_40) != iProver_top
    | v1_finset_1(k2_zfmisc_1(X0_40,X1_40)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_732])).

cnf(c_6,plain,
    ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_177,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X2)
    | X0 != X2
    | k2_zfmisc_1(k1_relat_1(X2),k2_relat_1(X2)) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_8])).

cnf(c_178,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_177])).

cnf(c_725,plain,
    ( m1_subset_1(X0_40,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_40),k2_relat_1(X0_40))))
    | ~ v1_relat_1(X0_40) ),
    inference(subtyping,[status(esa)],[c_178])).

cnf(c_1090,plain,
    ( m1_subset_1(X0_40,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_40),k2_relat_1(X0_40)))) = iProver_top
    | v1_relat_1(X0_40) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_725])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_finset_1(X1)
    | v1_finset_1(X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_736,plain,
    ( ~ m1_subset_1(X0_40,k1_zfmisc_1(X1_40))
    | ~ v1_finset_1(X1_40)
    | v1_finset_1(X0_40) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1079,plain,
    ( m1_subset_1(X0_40,k1_zfmisc_1(X1_40)) != iProver_top
    | v1_finset_1(X1_40) != iProver_top
    | v1_finset_1(X0_40) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_736])).

cnf(c_1349,plain,
    ( v1_relat_1(X0_40) != iProver_top
    | v1_finset_1(X0_40) = iProver_top
    | v1_finset_1(k2_zfmisc_1(k1_relat_1(X0_40),k2_relat_1(X0_40))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1090,c_1079])).

cnf(c_1903,plain,
    ( v1_relat_1(X0_40) != iProver_top
    | v1_finset_1(X0_40) = iProver_top
    | v1_finset_1(k2_relat_1(X0_40)) != iProver_top
    | v1_finset_1(k1_relat_1(X0_40)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1083,c_1349])).

cnf(c_1905,plain,
    ( v1_relat_1(sK0) != iProver_top
    | v1_finset_1(k2_relat_1(sK0)) != iProver_top
    | v1_finset_1(k1_relat_1(sK0)) != iProver_top
    | v1_finset_1(sK0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1903])).

cnf(c_12,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_726,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1089,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_726])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k9_relat_1(k9_funct_3(k1_relat_1(X0),k2_relat_1(X0)),X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_731,plain,
    ( ~ v1_relat_1(X0_40)
    | ~ v1_funct_1(X0_40)
    | k9_relat_1(k9_funct_3(k1_relat_1(X0_40),k2_relat_1(X0_40)),X0_40) = k1_relat_1(X0_40) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1084,plain,
    ( k9_relat_1(k9_funct_3(k1_relat_1(X0_40),k2_relat_1(X0_40)),X0_40) = k1_relat_1(X0_40)
    | v1_relat_1(X0_40) != iProver_top
    | v1_funct_1(X0_40) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_731])).

cnf(c_1466,plain,
    ( k9_relat_1(k9_funct_3(k1_relat_1(sK0),k2_relat_1(sK0)),sK0) = k1_relat_1(sK0)
    | v1_funct_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1089,c_1084])).

cnf(c_11,negated_conjecture,
    ( v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_768,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK0)
    | k9_relat_1(k9_funct_3(k1_relat_1(sK0),k2_relat_1(sK0)),sK0) = k1_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_731])).

cnf(c_1787,plain,
    ( k9_relat_1(k9_funct_3(k1_relat_1(sK0),k2_relat_1(sK0)),sK0) = k1_relat_1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1466,c_12,c_11,c_768])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_finset_1(X1)
    | v1_finset_1(k9_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_733,plain,
    ( ~ v1_relat_1(X0_40)
    | ~ v1_funct_1(X0_40)
    | ~ v1_finset_1(X1_40)
    | v1_finset_1(k9_relat_1(X0_40,X1_40)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1082,plain,
    ( v1_relat_1(X0_40) != iProver_top
    | v1_funct_1(X0_40) != iProver_top
    | v1_finset_1(X1_40) != iProver_top
    | v1_finset_1(k9_relat_1(X0_40,X1_40)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_733])).

cnf(c_1790,plain,
    ( v1_relat_1(k9_funct_3(k1_relat_1(sK0),k2_relat_1(sK0))) != iProver_top
    | v1_funct_1(k9_funct_3(k1_relat_1(sK0),k2_relat_1(sK0))) != iProver_top
    | v1_finset_1(k1_relat_1(sK0)) = iProver_top
    | v1_finset_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1787,c_1082])).

cnf(c_9,negated_conjecture,
    ( ~ v1_finset_1(k1_relat_1(sK0))
    | ~ v1_finset_1(sK0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_16,plain,
    ( v1_finset_1(k1_relat_1(sK0)) != iProver_top
    | v1_finset_1(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1890,plain,
    ( v1_funct_1(k9_funct_3(k1_relat_1(sK0),k2_relat_1(sK0))) != iProver_top
    | v1_relat_1(k9_funct_3(k1_relat_1(sK0),k2_relat_1(sK0))) != iProver_top
    | v1_finset_1(sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1790,c_16])).

cnf(c_1891,plain,
    ( v1_relat_1(k9_funct_3(k1_relat_1(sK0),k2_relat_1(sK0))) != iProver_top
    | v1_funct_1(k9_funct_3(k1_relat_1(sK0),k2_relat_1(sK0))) != iProver_top
    | v1_finset_1(sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_1890])).

cnf(c_1,plain,
    ( v1_funct_1(k9_funct_3(X0,X1)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_735,plain,
    ( v1_funct_1(k9_funct_3(X0_40,X1_40)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1080,plain,
    ( v1_funct_1(k9_funct_3(X0_40,X1_40)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_735])).

cnf(c_2,plain,
    ( v1_relat_1(k9_funct_3(X0,X1)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_734,plain,
    ( v1_relat_1(k9_funct_3(X0_40,X1_40)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1081,plain,
    ( v1_relat_1(k9_funct_3(X0_40,X1_40)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_734])).

cnf(c_1897,plain,
    ( v1_finset_1(sK0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1891,c_1080,c_1081])).

cnf(c_10,negated_conjecture,
    ( v1_finset_1(k1_relat_1(sK0))
    | v1_finset_1(sK0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_728,negated_conjecture,
    ( v1_finset_1(k1_relat_1(sK0))
    | v1_finset_1(sK0) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1087,plain,
    ( v1_finset_1(k1_relat_1(sK0)) = iProver_top
    | v1_finset_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_728])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_finset_1(k2_relat_1(X0))
    | ~ v1_finset_1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_730,plain,
    ( ~ v1_relat_1(X0_40)
    | ~ v1_funct_1(X0_40)
    | v1_finset_1(k2_relat_1(X0_40))
    | ~ v1_finset_1(k1_relat_1(X0_40)) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1085,plain,
    ( v1_relat_1(X0_40) != iProver_top
    | v1_funct_1(X0_40) != iProver_top
    | v1_finset_1(k2_relat_1(X0_40)) = iProver_top
    | v1_finset_1(k1_relat_1(X0_40)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_730])).

cnf(c_1647,plain,
    ( v1_relat_1(sK0) != iProver_top
    | v1_funct_1(sK0) != iProver_top
    | v1_finset_1(k2_relat_1(sK0)) = iProver_top
    | v1_finset_1(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1087,c_1085])).

cnf(c_13,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_14,plain,
    ( v1_funct_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1793,plain,
    ( v1_finset_1(k2_relat_1(sK0)) = iProver_top
    | v1_finset_1(sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1647,c_13,c_14])).

cnf(c_15,plain,
    ( v1_finset_1(k1_relat_1(sK0)) = iProver_top
    | v1_finset_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1905,c_1897,c_1793,c_15,c_13])).


%------------------------------------------------------------------------------
