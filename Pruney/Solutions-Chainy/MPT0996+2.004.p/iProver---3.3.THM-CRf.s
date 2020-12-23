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
% DateTime   : Thu Dec  3 12:04:14 EST 2020

% Result     : Theorem 3.88s
% Output     : CNFRefutation 3.88s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 286 expanded)
%              Number of clauses        :   62 ( 117 expanded)
%              Number of leaves         :   12 (  49 expanded)
%              Depth                    :   21
%              Number of atoms          :  233 ( 677 expanded)
%              Number of equality atoms :   83 ( 102 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f25])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f48,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f31])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => r1_tarski(k7_relset_1(X0,X1,X3,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => r1_tarski(k7_relset_1(X0,X1,X3,X2),X1) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f13,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
       => r1_tarski(k7_relset_1(X0,X1,X3,X2),X1) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f14,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => r1_tarski(k7_relset_1(X0,X1,X3,X2),X1) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(X0,X1,X3,X2),X1)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f29,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_tarski(k7_relset_1(X0,X1,X3,X2),X1)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ~ r1_tarski(k7_relset_1(sK0,sK1,sK3,sK2),sK1)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ~ r1_tarski(k7_relset_1(sK0,sK1,sK3,sK2),sK1)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f29])).

fof(f45,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f30])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f46,plain,(
    ~ r1_tarski(k7_relset_1(sK0,sK1,sK3,sK2),sK1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_656,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_644,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_653,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_904,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_644,c_653])).

cnf(c_11,plain,
    ( r1_tarski(k7_relat_1(X0,X1),X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_648,plain,
    ( r1_tarski(k7_relat_1(X0,X1),X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_655,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2208,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k7_relat_1(X0,X2),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_648,c_655])).

cnf(c_3388,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(k7_relat_1(X0,X3),X2) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2208,c_655])).

cnf(c_7592,plain,
    ( r1_tarski(k7_relat_1(sK3,X0),X1) = iProver_top
    | r1_tarski(k2_zfmisc_1(sK0,sK1),X1) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_904,c_3388])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_4,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_109,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_4])).

cnf(c_110,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_109])).

cnf(c_137,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_6,c_110])).

cnf(c_839,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[status(thm)],[c_5,c_15])).

cnf(c_919,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK3) ),
    inference(resolution,[status(thm)],[c_137,c_839])).

cnf(c_9,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_924,plain,
    ( v1_relat_1(sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_919,c_9])).

cnf(c_925,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_924])).

cnf(c_8229,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),X1) != iProver_top
    | r1_tarski(k7_relat_1(sK3,X0),X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7592,c_925])).

cnf(c_8230,plain,
    ( r1_tarski(k7_relat_1(sK3,X0),X1) = iProver_top
    | r1_tarski(k2_zfmisc_1(sK0,sK1),X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_8229])).

cnf(c_8237,plain,
    ( r1_tarski(k7_relat_1(sK3,X0),k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_656,c_8230])).

cnf(c_654,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_12,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_647,plain,
    ( v5_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1281,plain,
    ( v5_relat_1(X0,X1) = iProver_top
    | r1_tarski(X0,k2_zfmisc_1(X2,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_654,c_647])).

cnf(c_8416,plain,
    ( v5_relat_1(k7_relat_1(sK3,X0),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_8237,c_1281])).

cnf(c_8,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_651,plain,
    ( v5_relat_1(X0,X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2207,plain,
    ( v5_relat_1(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_651,c_655])).

cnf(c_10795,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),X1) = iProver_top
    | r1_tarski(sK1,X1) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8416,c_2207])).

cnf(c_643,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_137])).

cnf(c_1181,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_904,c_643])).

cnf(c_1672,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1181,c_925])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_649,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1677,plain,
    ( k2_relat_1(k7_relat_1(sK3,X0)) = k9_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_1672,c_649])).

cnf(c_10810,plain,
    ( r1_tarski(k9_relat_1(sK3,X0),X1) = iProver_top
    | r1_tarski(sK1,X1) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10795,c_1677])).

cnf(c_1219,plain,
    ( r1_tarski(X0,k2_zfmisc_1(sK0,sK1))
    | ~ r1_tarski(X0,sK3) ),
    inference(resolution,[status(thm)],[c_3,c_839])).

cnf(c_1349,plain,
    ( ~ r1_tarski(X0,sK3)
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[status(thm)],[c_1219,c_137])).

cnf(c_1394,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1461,plain,
    ( v1_relat_1(X0)
    | ~ r1_tarski(X0,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1349,c_1394])).

cnf(c_1462,plain,
    ( ~ r1_tarski(X0,sK3)
    | v1_relat_1(X0) ),
    inference(renaming,[status(thm)],[c_1461])).

cnf(c_1484,plain,
    ( v1_relat_1(k7_relat_1(sK3,X0))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[status(thm)],[c_1462,c_11])).

cnf(c_1485,plain,
    ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1484])).

cnf(c_18050,plain,
    ( r1_tarski(sK1,X1) != iProver_top
    | r1_tarski(k9_relat_1(sK3,X0),X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10810,c_925,c_1485])).

cnf(c_18051,plain,
    ( r1_tarski(k9_relat_1(sK3,X0),X1) = iProver_top
    | r1_tarski(sK1,X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_18050])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_646,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1441,plain,
    ( k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_644,c_646])).

cnf(c_14,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(sK0,sK1,sK3,sK2),sK1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_645,plain,
    ( r1_tarski(k7_relset_1(sK0,sK1,sK3,sK2),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1571,plain,
    ( r1_tarski(k9_relat_1(sK3,sK2),sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1441,c_645])).

cnf(c_18065,plain,
    ( r1_tarski(sK1,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_18051,c_1571])).

cnf(c_47,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_49,plain,
    ( r1_tarski(sK1,sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_47])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_18065,c_49])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:48:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.88/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.88/0.99  
% 3.88/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.88/0.99  
% 3.88/0.99  ------  iProver source info
% 3.88/0.99  
% 3.88/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.88/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.88/0.99  git: non_committed_changes: false
% 3.88/0.99  git: last_make_outside_of_git: false
% 3.88/0.99  
% 3.88/0.99  ------ 
% 3.88/0.99  ------ Parsing...
% 3.88/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.88/0.99  
% 3.88/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 3.88/0.99  
% 3.88/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.88/0.99  
% 3.88/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.88/0.99  ------ Proving...
% 3.88/0.99  ------ Problem Properties 
% 3.88/0.99  
% 3.88/0.99  
% 3.88/0.99  clauses                                 15
% 3.88/0.99  conjectures                             2
% 3.88/0.99  EPR                                     4
% 3.88/0.99  Horn                                    15
% 3.88/0.99  unary                                   4
% 3.88/0.99  binary                                  6
% 3.88/0.99  lits                                    31
% 3.88/0.99  lits eq                                 3
% 3.88/0.99  fd_pure                                 0
% 3.88/0.99  fd_pseudo                               0
% 3.88/0.99  fd_cond                                 0
% 3.88/0.99  fd_pseudo_cond                          1
% 3.88/0.99  AC symbols                              0
% 3.88/0.99  
% 3.88/0.99  ------ Input Options Time Limit: Unbounded
% 3.88/0.99  
% 3.88/0.99  
% 3.88/0.99  ------ 
% 3.88/0.99  Current options:
% 3.88/0.99  ------ 
% 3.88/0.99  
% 3.88/0.99  
% 3.88/0.99  
% 3.88/0.99  
% 3.88/0.99  ------ Proving...
% 3.88/0.99  
% 3.88/0.99  
% 3.88/0.99  % SZS status Theorem for theBenchmark.p
% 3.88/0.99  
% 3.88/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.88/0.99  
% 3.88/0.99  fof(f1,axiom,(
% 3.88/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.88/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.88/0.99  
% 3.88/0.99  fof(f25,plain,(
% 3.88/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.88/0.99    inference(nnf_transformation,[],[f1])).
% 3.88/0.99  
% 3.88/0.99  fof(f26,plain,(
% 3.88/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.88/0.99    inference(flattening,[],[f25])).
% 3.88/0.99  
% 3.88/0.99  fof(f31,plain,(
% 3.88/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.88/0.99    inference(cnf_transformation,[],[f26])).
% 3.88/0.99  
% 3.88/0.99  fof(f48,plain,(
% 3.88/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.88/0.99    inference(equality_resolution,[],[f31])).
% 3.88/0.99  
% 3.88/0.99  fof(f11,conjecture,(
% 3.88/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => r1_tarski(k7_relset_1(X0,X1,X3,X2),X1))),
% 3.88/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.88/0.99  
% 3.88/0.99  fof(f12,negated_conjecture,(
% 3.88/0.99    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => r1_tarski(k7_relset_1(X0,X1,X3,X2),X1))),
% 3.88/0.99    inference(negated_conjecture,[],[f11])).
% 3.88/0.99  
% 3.88/0.99  fof(f13,plain,(
% 3.88/0.99    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => r1_tarski(k7_relset_1(X0,X1,X3,X2),X1))),
% 3.88/0.99    inference(pure_predicate_removal,[],[f12])).
% 3.88/0.99  
% 3.88/0.99  fof(f14,plain,(
% 3.88/0.99    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => r1_tarski(k7_relset_1(X0,X1,X3,X2),X1))),
% 3.88/0.99    inference(pure_predicate_removal,[],[f13])).
% 3.88/0.99  
% 3.88/0.99  fof(f24,plain,(
% 3.88/0.99    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(X0,X1,X3,X2),X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.88/0.99    inference(ennf_transformation,[],[f14])).
% 3.88/0.99  
% 3.88/0.99  fof(f29,plain,(
% 3.88/0.99    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(X0,X1,X3,X2),X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (~r1_tarski(k7_relset_1(sK0,sK1,sK3,sK2),sK1) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 3.88/0.99    introduced(choice_axiom,[])).
% 3.88/0.99  
% 3.88/0.99  fof(f30,plain,(
% 3.88/0.99    ~r1_tarski(k7_relset_1(sK0,sK1,sK3,sK2),sK1) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.88/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f29])).
% 3.88/0.99  
% 3.88/0.99  fof(f45,plain,(
% 3.88/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.88/0.99    inference(cnf_transformation,[],[f30])).
% 3.88/0.99  
% 3.88/0.99  fof(f3,axiom,(
% 3.88/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.88/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.88/0.99  
% 3.88/0.99  fof(f27,plain,(
% 3.88/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.88/0.99    inference(nnf_transformation,[],[f3])).
% 3.88/0.99  
% 3.88/0.99  fof(f35,plain,(
% 3.88/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.88/0.99    inference(cnf_transformation,[],[f27])).
% 3.88/0.99  
% 3.88/0.99  fof(f8,axiom,(
% 3.88/0.99    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 3.88/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.88/0.99  
% 3.88/0.99  fof(f21,plain,(
% 3.88/0.99    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 3.88/0.99    inference(ennf_transformation,[],[f8])).
% 3.88/0.99  
% 3.88/0.99  fof(f42,plain,(
% 3.88/0.99    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 3.88/0.99    inference(cnf_transformation,[],[f21])).
% 3.88/0.99  
% 3.88/0.99  fof(f2,axiom,(
% 3.88/0.99    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 3.88/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.88/0.99  
% 3.88/0.99  fof(f16,plain,(
% 3.88/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.88/0.99    inference(ennf_transformation,[],[f2])).
% 3.88/0.99  
% 3.88/0.99  fof(f17,plain,(
% 3.88/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 3.88/0.99    inference(flattening,[],[f16])).
% 3.88/0.99  
% 3.88/0.99  fof(f34,plain,(
% 3.88/0.99    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 3.88/0.99    inference(cnf_transformation,[],[f17])).
% 3.88/0.99  
% 3.88/0.99  fof(f4,axiom,(
% 3.88/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.88/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.88/0.99  
% 3.88/0.99  fof(f18,plain,(
% 3.88/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.88/0.99    inference(ennf_transformation,[],[f4])).
% 3.88/0.99  
% 3.88/0.99  fof(f37,plain,(
% 3.88/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.88/0.99    inference(cnf_transformation,[],[f18])).
% 3.88/0.99  
% 3.88/0.99  fof(f36,plain,(
% 3.88/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.88/0.99    inference(cnf_transformation,[],[f27])).
% 3.88/0.99  
% 3.88/0.99  fof(f6,axiom,(
% 3.88/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.88/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.88/0.99  
% 3.88/0.99  fof(f40,plain,(
% 3.88/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.88/0.99    inference(cnf_transformation,[],[f6])).
% 3.88/0.99  
% 3.88/0.99  fof(f9,axiom,(
% 3.88/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.88/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.88/0.99  
% 3.88/0.99  fof(f15,plain,(
% 3.88/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.88/0.99    inference(pure_predicate_removal,[],[f9])).
% 3.88/0.99  
% 3.88/0.99  fof(f22,plain,(
% 3.88/0.99    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.88/0.99    inference(ennf_transformation,[],[f15])).
% 3.88/0.99  
% 3.88/0.99  fof(f43,plain,(
% 3.88/0.99    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.88/0.99    inference(cnf_transformation,[],[f22])).
% 3.88/0.99  
% 3.88/0.99  fof(f5,axiom,(
% 3.88/0.99    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.88/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.88/0.99  
% 3.88/0.99  fof(f19,plain,(
% 3.88/0.99    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.88/0.99    inference(ennf_transformation,[],[f5])).
% 3.88/0.99  
% 3.88/0.99  fof(f28,plain,(
% 3.88/0.99    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.88/0.99    inference(nnf_transformation,[],[f19])).
% 3.88/0.99  
% 3.88/0.99  fof(f38,plain,(
% 3.88/0.99    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.88/0.99    inference(cnf_transformation,[],[f28])).
% 3.88/0.99  
% 3.88/0.99  fof(f7,axiom,(
% 3.88/0.99    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 3.88/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.88/0.99  
% 3.88/0.99  fof(f20,plain,(
% 3.88/0.99    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.88/0.99    inference(ennf_transformation,[],[f7])).
% 3.88/0.99  
% 3.88/0.99  fof(f41,plain,(
% 3.88/0.99    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.88/0.99    inference(cnf_transformation,[],[f20])).
% 3.88/0.99  
% 3.88/0.99  fof(f10,axiom,(
% 3.88/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 3.88/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.88/0.99  
% 3.88/0.99  fof(f23,plain,(
% 3.88/0.99    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.88/0.99    inference(ennf_transformation,[],[f10])).
% 3.88/0.99  
% 3.88/0.99  fof(f44,plain,(
% 3.88/0.99    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.88/0.99    inference(cnf_transformation,[],[f23])).
% 3.88/0.99  
% 3.88/0.99  fof(f46,plain,(
% 3.88/0.99    ~r1_tarski(k7_relset_1(sK0,sK1,sK3,sK2),sK1)),
% 3.88/0.99    inference(cnf_transformation,[],[f30])).
% 3.88/0.99  
% 3.88/0.99  cnf(c_2,plain,
% 3.88/0.99      ( r1_tarski(X0,X0) ),
% 3.88/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_656,plain,
% 3.88/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 3.88/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_15,negated_conjecture,
% 3.88/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.88/0.99      inference(cnf_transformation,[],[f45]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_644,plain,
% 3.88/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.88/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_5,plain,
% 3.88/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.88/0.99      inference(cnf_transformation,[],[f35]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_653,plain,
% 3.88/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.88/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.88/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_904,plain,
% 3.88/0.99      ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 3.88/0.99      inference(superposition,[status(thm)],[c_644,c_653]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_11,plain,
% 3.88/0.99      ( r1_tarski(k7_relat_1(X0,X1),X0) | ~ v1_relat_1(X0) ),
% 3.88/0.99      inference(cnf_transformation,[],[f42]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_648,plain,
% 3.88/0.99      ( r1_tarski(k7_relat_1(X0,X1),X0) = iProver_top
% 3.88/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.88/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_3,plain,
% 3.88/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 3.88/0.99      inference(cnf_transformation,[],[f34]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_655,plain,
% 3.88/0.99      ( r1_tarski(X0,X1) != iProver_top
% 3.88/0.99      | r1_tarski(X1,X2) != iProver_top
% 3.88/0.99      | r1_tarski(X0,X2) = iProver_top ),
% 3.88/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_2208,plain,
% 3.88/0.99      ( r1_tarski(X0,X1) != iProver_top
% 3.88/0.99      | r1_tarski(k7_relat_1(X0,X2),X1) = iProver_top
% 3.88/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.88/0.99      inference(superposition,[status(thm)],[c_648,c_655]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_3388,plain,
% 3.88/0.99      ( r1_tarski(X0,X1) != iProver_top
% 3.88/0.99      | r1_tarski(X1,X2) != iProver_top
% 3.88/0.99      | r1_tarski(k7_relat_1(X0,X3),X2) = iProver_top
% 3.88/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.88/0.99      inference(superposition,[status(thm)],[c_2208,c_655]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_7592,plain,
% 3.88/0.99      ( r1_tarski(k7_relat_1(sK3,X0),X1) = iProver_top
% 3.88/0.99      | r1_tarski(k2_zfmisc_1(sK0,sK1),X1) != iProver_top
% 3.88/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.88/0.99      inference(superposition,[status(thm)],[c_904,c_3388]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_6,plain,
% 3.88/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.88/0.99      | ~ v1_relat_1(X1)
% 3.88/0.99      | v1_relat_1(X0) ),
% 3.88/0.99      inference(cnf_transformation,[],[f37]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_4,plain,
% 3.88/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.88/0.99      inference(cnf_transformation,[],[f36]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_109,plain,
% 3.88/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.88/0.99      inference(prop_impl,[status(thm)],[c_4]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_110,plain,
% 3.88/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.88/0.99      inference(renaming,[status(thm)],[c_109]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_137,plain,
% 3.88/0.99      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.88/0.99      inference(bin_hyper_res,[status(thm)],[c_6,c_110]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_839,plain,
% 3.88/0.99      ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
% 3.88/0.99      inference(resolution,[status(thm)],[c_5,c_15]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_919,plain,
% 3.88/0.99      ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK3) ),
% 3.88/0.99      inference(resolution,[status(thm)],[c_137,c_839]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_9,plain,
% 3.88/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.88/0.99      inference(cnf_transformation,[],[f40]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_924,plain,
% 3.88/0.99      ( v1_relat_1(sK3) ),
% 3.88/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_919,c_9]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_925,plain,
% 3.88/0.99      ( v1_relat_1(sK3) = iProver_top ),
% 3.88/0.99      inference(predicate_to_equality,[status(thm)],[c_924]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_8229,plain,
% 3.88/0.99      ( r1_tarski(k2_zfmisc_1(sK0,sK1),X1) != iProver_top
% 3.88/0.99      | r1_tarski(k7_relat_1(sK3,X0),X1) = iProver_top ),
% 3.88/0.99      inference(global_propositional_subsumption,
% 3.88/0.99                [status(thm)],
% 3.88/0.99                [c_7592,c_925]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_8230,plain,
% 3.88/0.99      ( r1_tarski(k7_relat_1(sK3,X0),X1) = iProver_top
% 3.88/0.99      | r1_tarski(k2_zfmisc_1(sK0,sK1),X1) != iProver_top ),
% 3.88/0.99      inference(renaming,[status(thm)],[c_8229]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_8237,plain,
% 3.88/0.99      ( r1_tarski(k7_relat_1(sK3,X0),k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 3.88/0.99      inference(superposition,[status(thm)],[c_656,c_8230]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_654,plain,
% 3.88/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.88/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 3.88/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_12,plain,
% 3.88/0.99      ( v5_relat_1(X0,X1)
% 3.88/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.88/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_647,plain,
% 3.88/0.99      ( v5_relat_1(X0,X1) = iProver_top
% 3.88/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
% 3.88/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_1281,plain,
% 3.88/0.99      ( v5_relat_1(X0,X1) = iProver_top
% 3.88/0.99      | r1_tarski(X0,k2_zfmisc_1(X2,X1)) != iProver_top ),
% 3.88/0.99      inference(superposition,[status(thm)],[c_654,c_647]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_8416,plain,
% 3.88/0.99      ( v5_relat_1(k7_relat_1(sK3,X0),sK1) = iProver_top ),
% 3.88/0.99      inference(superposition,[status(thm)],[c_8237,c_1281]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_8,plain,
% 3.88/0.99      ( ~ v5_relat_1(X0,X1)
% 3.88/0.99      | r1_tarski(k2_relat_1(X0),X1)
% 3.88/0.99      | ~ v1_relat_1(X0) ),
% 3.88/0.99      inference(cnf_transformation,[],[f38]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_651,plain,
% 3.88/0.99      ( v5_relat_1(X0,X1) != iProver_top
% 3.88/0.99      | r1_tarski(k2_relat_1(X0),X1) = iProver_top
% 3.88/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.88/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_2207,plain,
% 3.88/0.99      ( v5_relat_1(X0,X1) != iProver_top
% 3.88/0.99      | r1_tarski(X1,X2) != iProver_top
% 3.88/0.99      | r1_tarski(k2_relat_1(X0),X2) = iProver_top
% 3.88/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.88/0.99      inference(superposition,[status(thm)],[c_651,c_655]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_10795,plain,
% 3.88/0.99      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),X1) = iProver_top
% 3.88/0.99      | r1_tarski(sK1,X1) != iProver_top
% 3.88/0.99      | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top ),
% 3.88/0.99      inference(superposition,[status(thm)],[c_8416,c_2207]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_643,plain,
% 3.88/0.99      ( r1_tarski(X0,X1) != iProver_top
% 3.88/0.99      | v1_relat_1(X1) != iProver_top
% 3.88/0.99      | v1_relat_1(X0) = iProver_top ),
% 3.88/0.99      inference(predicate_to_equality,[status(thm)],[c_137]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_1181,plain,
% 3.88/0.99      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 3.88/0.99      | v1_relat_1(sK3) = iProver_top ),
% 3.88/0.99      inference(superposition,[status(thm)],[c_904,c_643]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_1672,plain,
% 3.88/0.99      ( v1_relat_1(sK3) = iProver_top ),
% 3.88/0.99      inference(global_propositional_subsumption,
% 3.88/0.99                [status(thm)],
% 3.88/0.99                [c_1181,c_925]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_10,plain,
% 3.88/0.99      ( ~ v1_relat_1(X0)
% 3.88/0.99      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 3.88/0.99      inference(cnf_transformation,[],[f41]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_649,plain,
% 3.88/0.99      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 3.88/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.88/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_1677,plain,
% 3.88/0.99      ( k2_relat_1(k7_relat_1(sK3,X0)) = k9_relat_1(sK3,X0) ),
% 3.88/0.99      inference(superposition,[status(thm)],[c_1672,c_649]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_10810,plain,
% 3.88/0.99      ( r1_tarski(k9_relat_1(sK3,X0),X1) = iProver_top
% 3.88/0.99      | r1_tarski(sK1,X1) != iProver_top
% 3.88/0.99      | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top ),
% 3.88/0.99      inference(light_normalisation,[status(thm)],[c_10795,c_1677]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_1219,plain,
% 3.88/0.99      ( r1_tarski(X0,k2_zfmisc_1(sK0,sK1)) | ~ r1_tarski(X0,sK3) ),
% 3.88/0.99      inference(resolution,[status(thm)],[c_3,c_839]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_1349,plain,
% 3.88/0.99      ( ~ r1_tarski(X0,sK3)
% 3.88/0.99      | v1_relat_1(X0)
% 3.88/0.99      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
% 3.88/0.99      inference(resolution,[status(thm)],[c_1219,c_137]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_1394,plain,
% 3.88/0.99      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
% 3.88/0.99      inference(instantiation,[status(thm)],[c_9]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_1461,plain,
% 3.88/0.99      ( v1_relat_1(X0) | ~ r1_tarski(X0,sK3) ),
% 3.88/0.99      inference(global_propositional_subsumption,
% 3.88/0.99                [status(thm)],
% 3.88/0.99                [c_1349,c_1394]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_1462,plain,
% 3.88/0.99      ( ~ r1_tarski(X0,sK3) | v1_relat_1(X0) ),
% 3.88/0.99      inference(renaming,[status(thm)],[c_1461]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_1484,plain,
% 3.88/0.99      ( v1_relat_1(k7_relat_1(sK3,X0)) | ~ v1_relat_1(sK3) ),
% 3.88/0.99      inference(resolution,[status(thm)],[c_1462,c_11]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_1485,plain,
% 3.88/0.99      ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top
% 3.88/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.88/0.99      inference(predicate_to_equality,[status(thm)],[c_1484]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_18050,plain,
% 3.88/0.99      ( r1_tarski(sK1,X1) != iProver_top
% 3.88/0.99      | r1_tarski(k9_relat_1(sK3,X0),X1) = iProver_top ),
% 3.88/0.99      inference(global_propositional_subsumption,
% 3.88/0.99                [status(thm)],
% 3.88/0.99                [c_10810,c_925,c_1485]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_18051,plain,
% 3.88/0.99      ( r1_tarski(k9_relat_1(sK3,X0),X1) = iProver_top
% 3.88/0.99      | r1_tarski(sK1,X1) != iProver_top ),
% 3.88/0.99      inference(renaming,[status(thm)],[c_18050]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_13,plain,
% 3.88/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.88/0.99      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 3.88/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_646,plain,
% 3.88/0.99      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 3.88/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.88/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_1441,plain,
% 3.88/0.99      ( k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
% 3.88/0.99      inference(superposition,[status(thm)],[c_644,c_646]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_14,negated_conjecture,
% 3.88/0.99      ( ~ r1_tarski(k7_relset_1(sK0,sK1,sK3,sK2),sK1) ),
% 3.88/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_645,plain,
% 3.88/0.99      ( r1_tarski(k7_relset_1(sK0,sK1,sK3,sK2),sK1) != iProver_top ),
% 3.88/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_1571,plain,
% 3.88/0.99      ( r1_tarski(k9_relat_1(sK3,sK2),sK1) != iProver_top ),
% 3.88/0.99      inference(demodulation,[status(thm)],[c_1441,c_645]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_18065,plain,
% 3.88/0.99      ( r1_tarski(sK1,sK1) != iProver_top ),
% 3.88/0.99      inference(superposition,[status(thm)],[c_18051,c_1571]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_47,plain,
% 3.88/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 3.88/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_49,plain,
% 3.88/0.99      ( r1_tarski(sK1,sK1) = iProver_top ),
% 3.88/0.99      inference(instantiation,[status(thm)],[c_47]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(contradiction,plain,
% 3.88/0.99      ( $false ),
% 3.88/0.99      inference(minisat,[status(thm)],[c_18065,c_49]) ).
% 3.88/0.99  
% 3.88/0.99  
% 3.88/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.88/0.99  
% 3.88/0.99  ------                               Statistics
% 3.88/0.99  
% 3.88/0.99  ------ Selected
% 3.88/0.99  
% 3.88/0.99  total_time:                             0.492
% 3.88/0.99  
%------------------------------------------------------------------------------
