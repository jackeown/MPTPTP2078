%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:55:15 EST 2020

% Result     : Theorem 1.51s
% Output     : CNFRefutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 226 expanded)
%              Number of clauses        :   56 (  88 expanded)
%              Number of leaves         :   13 (  43 expanded)
%              Depth                    :   15
%              Number of atoms          :  239 ( 673 expanded)
%              Number of equality atoms :   96 ( 217 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( r1_tarski(k6_relat_1(X1),X2)
       => ( r1_tarski(X1,k2_relset_1(X1,X0,X2))
          & k1_relset_1(X1,X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
       => ( r1_tarski(k6_relat_1(X1),X2)
         => ( r1_tarski(X1,k2_relset_1(X1,X0,X2))
            & k1_relset_1(X1,X0,X2) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_tarski(X1,k2_relset_1(X1,X0,X2))
        | k1_relset_1(X1,X0,X2) != X1 )
      & r1_tarski(k6_relat_1(X1),X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_tarski(X1,k2_relset_1(X1,X0,X2))
        | k1_relset_1(X1,X0,X2) != X1 )
      & r1_tarski(k6_relat_1(X1),X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(flattening,[],[f19])).

fof(f24,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_tarski(X1,k2_relset_1(X1,X0,X2))
          | k1_relset_1(X1,X0,X2) != X1 )
        & r1_tarski(k6_relat_1(X1),X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
   => ( ( ~ r1_tarski(sK1,k2_relset_1(sK1,sK0,sK2))
        | k1_relset_1(sK1,sK0,sK2) != sK1 )
      & r1_tarski(k6_relat_1(sK1),sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ( ~ r1_tarski(sK1,k2_relset_1(sK1,sK0,sK2))
      | k1_relset_1(sK1,sK0,sK2) != sK1 )
    & r1_tarski(k6_relat_1(sK1),sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f24])).

fof(f41,plain,(
    r1_tarski(k6_relat_1(sK1),sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f4,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f35,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f40,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f21])).

fof(f28,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f44,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f26])).

fof(f34,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f42,plain,
    ( ~ r1_tarski(sK1,k2_relset_1(sK1,sK0,sK2))
    | k1_relset_1(sK1,sK0,sK2) != sK1 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_341,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2400,plain,
    ( k2_relat_1(k6_relat_1(X0)) != X1
    | sK1 != X1
    | sK1 = k2_relat_1(k6_relat_1(X0)) ),
    inference(instantiation,[status(thm)],[c_341])).

cnf(c_2401,plain,
    ( k2_relat_1(k6_relat_1(sK1)) != sK1
    | sK1 = k2_relat_1(k6_relat_1(sK1))
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_2400])).

cnf(c_15,negated_conjecture,
    ( r1_tarski(k6_relat_1(sK1),sK2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_713,plain,
    ( r1_tarski(k6_relat_1(sK1),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_8,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_720,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1858,plain,
    ( r1_tarski(X0,k1_relat_1(X1)) = iProver_top
    | r1_tarski(k6_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_720])).

cnf(c_9,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_32,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2064,plain,
    ( v1_relat_1(X1) != iProver_top
    | r1_tarski(k6_relat_1(X0),X1) != iProver_top
    | r1_tarski(X0,k1_relat_1(X1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1858,c_32])).

cnf(c_2065,plain,
    ( r1_tarski(X0,k1_relat_1(X1)) = iProver_top
    | r1_tarski(k6_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_2064])).

cnf(c_2074,plain,
    ( r1_tarski(sK1,k1_relat_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_713,c_2065])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_17,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_831,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_832,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_831])).

cnf(c_2321,plain,
    ( r1_tarski(sK1,k1_relat_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2074,c_17,c_832])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_725,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2326,plain,
    ( k1_relat_1(sK2) = sK1
    | r1_tarski(k1_relat_1(sK2),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2321,c_725])).

cnf(c_712,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_716,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1478,plain,
    ( k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_712,c_716])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_717,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1577,plain,
    ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK1)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1478,c_717])).

cnf(c_1695,plain,
    ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1577,c_17])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_722,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1700,plain,
    ( r1_tarski(k1_relat_1(sK2),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1695,c_722])).

cnf(c_1890,plain,
    ( k1_relat_1(sK2) = sK1
    | r1_tarski(sK1,k1_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1700,c_725])).

cnf(c_2329,plain,
    ( k1_relat_1(sK2) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2326,c_17,c_832,c_1890,c_2074])).

cnf(c_2336,plain,
    ( k1_relset_1(sK1,sK0,sK2) = sK1 ),
    inference(demodulation,[status(thm)],[c_2329,c_1478])).

cnf(c_342,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_860,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK1,k2_relset_1(sK1,sK0,sK2))
    | k2_relset_1(sK1,sK0,sK2) != X1
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_342])).

cnf(c_915,plain,
    ( ~ r1_tarski(X0,k2_relat_1(sK2))
    | r1_tarski(sK1,k2_relset_1(sK1,sK0,sK2))
    | k2_relset_1(sK1,sK0,sK2) != k2_relat_1(sK2)
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_860])).

cnf(c_1553,plain,
    ( ~ r1_tarski(k2_relat_1(k6_relat_1(X0)),k2_relat_1(sK2))
    | r1_tarski(sK1,k2_relset_1(sK1,sK0,sK2))
    | k2_relset_1(sK1,sK0,sK2) != k2_relat_1(sK2)
    | sK1 != k2_relat_1(k6_relat_1(X0)) ),
    inference(instantiation,[status(thm)],[c_915])).

cnf(c_1555,plain,
    ( ~ r1_tarski(k2_relat_1(k6_relat_1(sK1)),k2_relat_1(sK2))
    | r1_tarski(sK1,k2_relset_1(sK1,sK0,sK2))
    | k2_relset_1(sK1,sK0,sK2) != k2_relat_1(sK2)
    | sK1 != k2_relat_1(k6_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_1553])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_883,plain,
    ( ~ r1_tarski(X0,sK2)
    | r1_tarski(k2_relat_1(X0),k2_relat_1(sK2))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1043,plain,
    ( ~ r1_tarski(k6_relat_1(X0),sK2)
    | r1_tarski(k2_relat_1(k6_relat_1(X0)),k2_relat_1(sK2))
    | ~ v1_relat_1(k6_relat_1(X0))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_883])).

cnf(c_1045,plain,
    ( ~ r1_tarski(k6_relat_1(sK1),sK2)
    | r1_tarski(k2_relat_1(k6_relat_1(sK1)),k2_relat_1(sK2))
    | ~ v1_relat_1(k6_relat_1(sK1))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1043])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_857,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_54,plain,
    ( ~ r1_tarski(sK1,sK1)
    | sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_50,plain,
    ( r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_7,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_36,plain,
    ( k2_relat_1(k6_relat_1(sK1)) = sK1 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_33,plain,
    ( v1_relat_1(k6_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_14,negated_conjecture,
    ( ~ r1_tarski(sK1,k2_relset_1(sK1,sK0,sK2))
    | k1_relset_1(sK1,sK0,sK2) != sK1 ),
    inference(cnf_transformation,[],[f42])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2401,c_2336,c_1555,c_1045,c_857,c_831,c_54,c_50,c_36,c_33,c_14,c_15,c_16])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.06  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.07  % Command    : iproveropt_run.sh %d %s
% 0.07/0.25  % Computer   : n009.cluster.edu
% 0.07/0.25  % Model      : x86_64 x86_64
% 0.07/0.25  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.07/0.25  % Memory     : 8042.1875MB
% 0.07/0.25  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.07/0.25  % CPULimit   : 60
% 0.07/0.25  % WCLimit    : 600
% 0.07/0.25  % DateTime   : Tue Dec  1 15:56:26 EST 2020
% 0.07/0.25  % CPUTime    : 
% 0.07/0.26  % Running in FOF mode
% 1.51/0.83  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.51/0.83  
% 1.51/0.83  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.51/0.83  
% 1.51/0.83  ------  iProver source info
% 1.51/0.83  
% 1.51/0.83  git: date: 2020-06-30 10:37:57 +0100
% 1.51/0.83  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.51/0.83  git: non_committed_changes: false
% 1.51/0.83  git: last_make_outside_of_git: false
% 1.51/0.83  
% 1.51/0.83  ------ 
% 1.51/0.83  
% 1.51/0.83  ------ Input Options
% 1.51/0.83  
% 1.51/0.83  --out_options                           all
% 1.51/0.83  --tptp_safe_out                         true
% 1.51/0.83  --problem_path                          ""
% 1.51/0.83  --include_path                          ""
% 1.51/0.83  --clausifier                            res/vclausify_rel
% 1.51/0.83  --clausifier_options                    --mode clausify
% 1.51/0.83  --stdin                                 false
% 1.51/0.83  --stats_out                             all
% 1.51/0.83  
% 1.51/0.83  ------ General Options
% 1.51/0.83  
% 1.51/0.83  --fof                                   false
% 1.51/0.83  --time_out_real                         305.
% 1.51/0.83  --time_out_virtual                      -1.
% 1.51/0.83  --symbol_type_check                     false
% 1.51/0.83  --clausify_out                          false
% 1.51/0.83  --sig_cnt_out                           false
% 1.51/0.83  --trig_cnt_out                          false
% 1.51/0.83  --trig_cnt_out_tolerance                1.
% 1.51/0.83  --trig_cnt_out_sk_spl                   false
% 1.51/0.83  --abstr_cl_out                          false
% 1.51/0.83  
% 1.51/0.83  ------ Global Options
% 1.51/0.83  
% 1.51/0.83  --schedule                              default
% 1.51/0.83  --add_important_lit                     false
% 1.51/0.83  --prop_solver_per_cl                    1000
% 1.51/0.83  --min_unsat_core                        false
% 1.51/0.83  --soft_assumptions                      false
% 1.51/0.83  --soft_lemma_size                       3
% 1.51/0.83  --prop_impl_unit_size                   0
% 1.51/0.83  --prop_impl_unit                        []
% 1.51/0.83  --share_sel_clauses                     true
% 1.51/0.83  --reset_solvers                         false
% 1.51/0.83  --bc_imp_inh                            [conj_cone]
% 1.51/0.83  --conj_cone_tolerance                   3.
% 1.51/0.83  --extra_neg_conj                        none
% 1.51/0.83  --large_theory_mode                     true
% 1.51/0.83  --prolific_symb_bound                   200
% 1.51/0.83  --lt_threshold                          2000
% 1.51/0.83  --clause_weak_htbl                      true
% 1.51/0.83  --gc_record_bc_elim                     false
% 1.51/0.83  
% 1.51/0.83  ------ Preprocessing Options
% 1.51/0.83  
% 1.51/0.83  --preprocessing_flag                    true
% 1.51/0.83  --time_out_prep_mult                    0.1
% 1.51/0.83  --splitting_mode                        input
% 1.51/0.83  --splitting_grd                         true
% 1.51/0.83  --splitting_cvd                         false
% 1.51/0.83  --splitting_cvd_svl                     false
% 1.51/0.83  --splitting_nvd                         32
% 1.51/0.83  --sub_typing                            true
% 1.51/0.83  --prep_gs_sim                           true
% 1.51/0.83  --prep_unflatten                        true
% 1.51/0.83  --prep_res_sim                          true
% 1.51/0.83  --prep_upred                            true
% 1.51/0.83  --prep_sem_filter                       exhaustive
% 1.51/0.83  --prep_sem_filter_out                   false
% 1.51/0.83  --pred_elim                             true
% 1.51/0.83  --res_sim_input                         true
% 1.51/0.83  --eq_ax_congr_red                       true
% 1.51/0.83  --pure_diseq_elim                       true
% 1.51/0.83  --brand_transform                       false
% 1.51/0.83  --non_eq_to_eq                          false
% 1.51/0.83  --prep_def_merge                        true
% 1.51/0.83  --prep_def_merge_prop_impl              false
% 1.51/0.83  --prep_def_merge_mbd                    true
% 1.51/0.83  --prep_def_merge_tr_red                 false
% 1.51/0.83  --prep_def_merge_tr_cl                  false
% 1.51/0.83  --smt_preprocessing                     true
% 1.51/0.83  --smt_ac_axioms                         fast
% 1.51/0.83  --preprocessed_out                      false
% 1.51/0.83  --preprocessed_stats                    false
% 1.51/0.83  
% 1.51/0.83  ------ Abstraction refinement Options
% 1.51/0.83  
% 1.51/0.83  --abstr_ref                             []
% 1.51/0.83  --abstr_ref_prep                        false
% 1.51/0.83  --abstr_ref_until_sat                   false
% 1.51/0.83  --abstr_ref_sig_restrict                funpre
% 1.51/0.83  --abstr_ref_af_restrict_to_split_sk     false
% 1.51/0.83  --abstr_ref_under                       []
% 1.51/0.83  
% 1.51/0.83  ------ SAT Options
% 1.51/0.83  
% 1.51/0.83  --sat_mode                              false
% 1.51/0.83  --sat_fm_restart_options                ""
% 1.51/0.83  --sat_gr_def                            false
% 1.51/0.83  --sat_epr_types                         true
% 1.51/0.83  --sat_non_cyclic_types                  false
% 1.51/0.83  --sat_finite_models                     false
% 1.51/0.83  --sat_fm_lemmas                         false
% 1.51/0.83  --sat_fm_prep                           false
% 1.51/0.83  --sat_fm_uc_incr                        true
% 1.51/0.83  --sat_out_model                         small
% 1.51/0.83  --sat_out_clauses                       false
% 1.51/0.83  
% 1.51/0.83  ------ QBF Options
% 1.51/0.83  
% 1.51/0.83  --qbf_mode                              false
% 1.51/0.83  --qbf_elim_univ                         false
% 1.51/0.83  --qbf_dom_inst                          none
% 1.51/0.83  --qbf_dom_pre_inst                      false
% 1.51/0.83  --qbf_sk_in                             false
% 1.51/0.83  --qbf_pred_elim                         true
% 1.51/0.83  --qbf_split                             512
% 1.51/0.83  
% 1.51/0.83  ------ BMC1 Options
% 1.51/0.83  
% 1.51/0.83  --bmc1_incremental                      false
% 1.51/0.83  --bmc1_axioms                           reachable_all
% 1.51/0.83  --bmc1_min_bound                        0
% 1.51/0.83  --bmc1_max_bound                        -1
% 1.51/0.83  --bmc1_max_bound_default                -1
% 1.51/0.83  --bmc1_symbol_reachability              true
% 1.51/0.83  --bmc1_property_lemmas                  false
% 1.51/0.83  --bmc1_k_induction                      false
% 1.51/0.83  --bmc1_non_equiv_states                 false
% 1.51/0.83  --bmc1_deadlock                         false
% 1.51/0.83  --bmc1_ucm                              false
% 1.51/0.83  --bmc1_add_unsat_core                   none
% 1.51/0.83  --bmc1_unsat_core_children              false
% 1.51/0.83  --bmc1_unsat_core_extrapolate_axioms    false
% 1.51/0.83  --bmc1_out_stat                         full
% 1.51/0.83  --bmc1_ground_init                      false
% 1.51/0.83  --bmc1_pre_inst_next_state              false
% 1.51/0.83  --bmc1_pre_inst_state                   false
% 1.51/0.83  --bmc1_pre_inst_reach_state             false
% 1.51/0.83  --bmc1_out_unsat_core                   false
% 1.51/0.83  --bmc1_aig_witness_out                  false
% 1.51/0.83  --bmc1_verbose                          false
% 1.51/0.83  --bmc1_dump_clauses_tptp                false
% 1.51/0.83  --bmc1_dump_unsat_core_tptp             false
% 1.51/0.83  --bmc1_dump_file                        -
% 1.51/0.83  --bmc1_ucm_expand_uc_limit              128
% 1.51/0.83  --bmc1_ucm_n_expand_iterations          6
% 1.51/0.83  --bmc1_ucm_extend_mode                  1
% 1.51/0.83  --bmc1_ucm_init_mode                    2
% 1.51/0.83  --bmc1_ucm_cone_mode                    none
% 1.51/0.83  --bmc1_ucm_reduced_relation_type        0
% 1.51/0.83  --bmc1_ucm_relax_model                  4
% 1.51/0.83  --bmc1_ucm_full_tr_after_sat            true
% 1.51/0.83  --bmc1_ucm_expand_neg_assumptions       false
% 1.51/0.83  --bmc1_ucm_layered_model                none
% 1.51/0.83  --bmc1_ucm_max_lemma_size               10
% 1.51/0.83  
% 1.51/0.83  ------ AIG Options
% 1.51/0.83  
% 1.51/0.83  --aig_mode                              false
% 1.51/0.83  
% 1.51/0.83  ------ Instantiation Options
% 1.51/0.83  
% 1.51/0.83  --instantiation_flag                    true
% 1.51/0.83  --inst_sos_flag                         false
% 1.51/0.83  --inst_sos_phase                        true
% 1.51/0.83  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.51/0.83  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.51/0.83  --inst_lit_sel_side                     num_symb
% 1.51/0.83  --inst_solver_per_active                1400
% 1.51/0.83  --inst_solver_calls_frac                1.
% 1.51/0.83  --inst_passive_queue_type               priority_queues
% 1.51/0.83  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.51/0.83  --inst_passive_queues_freq              [25;2]
% 1.51/0.83  --inst_dismatching                      true
% 1.51/0.83  --inst_eager_unprocessed_to_passive     true
% 1.51/0.83  --inst_prop_sim_given                   true
% 1.51/0.83  --inst_prop_sim_new                     false
% 1.51/0.83  --inst_subs_new                         false
% 1.51/0.83  --inst_eq_res_simp                      false
% 1.51/0.83  --inst_subs_given                       false
% 1.51/0.83  --inst_orphan_elimination               true
% 1.51/0.83  --inst_learning_loop_flag               true
% 1.51/0.83  --inst_learning_start                   3000
% 1.51/0.83  --inst_learning_factor                  2
% 1.51/0.83  --inst_start_prop_sim_after_learn       3
% 1.51/0.83  --inst_sel_renew                        solver
% 1.51/0.83  --inst_lit_activity_flag                true
% 1.51/0.83  --inst_restr_to_given                   false
% 1.51/0.83  --inst_activity_threshold               500
% 1.51/0.83  --inst_out_proof                        true
% 1.51/0.83  
% 1.51/0.83  ------ Resolution Options
% 1.51/0.83  
% 1.51/0.83  --resolution_flag                       true
% 1.51/0.83  --res_lit_sel                           adaptive
% 1.51/0.83  --res_lit_sel_side                      none
% 1.51/0.83  --res_ordering                          kbo
% 1.51/0.83  --res_to_prop_solver                    active
% 1.51/0.83  --res_prop_simpl_new                    false
% 1.51/0.83  --res_prop_simpl_given                  true
% 1.51/0.83  --res_passive_queue_type                priority_queues
% 1.51/0.83  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.51/0.83  --res_passive_queues_freq               [15;5]
% 1.51/0.83  --res_forward_subs                      full
% 1.51/0.83  --res_backward_subs                     full
% 1.51/0.83  --res_forward_subs_resolution           true
% 1.51/0.83  --res_backward_subs_resolution          true
% 1.51/0.83  --res_orphan_elimination                true
% 1.51/0.83  --res_time_limit                        2.
% 1.51/0.83  --res_out_proof                         true
% 1.51/0.83  
% 1.51/0.83  ------ Superposition Options
% 1.51/0.83  
% 1.51/0.83  --superposition_flag                    true
% 1.51/0.83  --sup_passive_queue_type                priority_queues
% 1.51/0.83  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.51/0.83  --sup_passive_queues_freq               [8;1;4]
% 1.51/0.83  --demod_completeness_check              fast
% 1.51/0.83  --demod_use_ground                      true
% 1.51/0.83  --sup_to_prop_solver                    passive
% 1.51/0.83  --sup_prop_simpl_new                    true
% 1.51/0.83  --sup_prop_simpl_given                  true
% 1.51/0.83  --sup_fun_splitting                     false
% 1.51/0.83  --sup_smt_interval                      50000
% 1.51/0.83  
% 1.51/0.83  ------ Superposition Simplification Setup
% 1.51/0.83  
% 1.51/0.83  --sup_indices_passive                   []
% 1.51/0.83  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.51/0.83  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.51/0.83  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.51/0.83  --sup_full_triv                         [TrivRules;PropSubs]
% 1.51/0.83  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.51/0.83  --sup_full_bw                           [BwDemod]
% 1.51/0.83  --sup_immed_triv                        [TrivRules]
% 1.51/0.83  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.51/0.83  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.51/0.83  --sup_immed_bw_main                     []
% 1.51/0.83  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.51/0.83  --sup_input_triv                        [Unflattening;TrivRules]
% 1.51/0.83  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.51/0.83  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.51/0.83  
% 1.51/0.83  ------ Combination Options
% 1.51/0.83  
% 1.51/0.83  --comb_res_mult                         3
% 1.51/0.83  --comb_sup_mult                         2
% 1.51/0.83  --comb_inst_mult                        10
% 1.51/0.83  
% 1.51/0.83  ------ Debug Options
% 1.51/0.83  
% 1.51/0.83  --dbg_backtrace                         false
% 1.51/0.83  --dbg_dump_prop_clauses                 false
% 1.51/0.83  --dbg_dump_prop_clauses_file            -
% 1.51/0.83  --dbg_out_stat                          false
% 1.51/0.83  ------ Parsing...
% 1.51/0.83  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.51/0.83  
% 1.51/0.83  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 1.51/0.83  
% 1.51/0.83  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.51/0.83  
% 1.51/0.83  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.51/0.83  ------ Proving...
% 1.51/0.83  ------ Problem Properties 
% 1.51/0.83  
% 1.51/0.83  
% 1.51/0.83  clauses                                 16
% 1.51/0.83  conjectures                             3
% 1.51/0.83  EPR                                     2
% 1.51/0.83  Horn                                    16
% 1.51/0.83  unary                                   6
% 1.51/0.83  binary                                  7
% 1.51/0.83  lits                                    31
% 1.51/0.83  lits eq                                 6
% 1.51/0.83  fd_pure                                 0
% 1.51/0.83  fd_pseudo                               0
% 1.51/0.83  fd_cond                                 0
% 1.51/0.83  fd_pseudo_cond                          1
% 1.51/0.83  AC symbols                              0
% 1.51/0.83  
% 1.51/0.83  ------ Schedule dynamic 5 is on 
% 1.51/0.83  
% 1.51/0.83  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.51/0.83  
% 1.51/0.83  
% 1.51/0.83  ------ 
% 1.51/0.83  Current options:
% 1.51/0.83  ------ 
% 1.51/0.83  
% 1.51/0.83  ------ Input Options
% 1.51/0.83  
% 1.51/0.83  --out_options                           all
% 1.51/0.83  --tptp_safe_out                         true
% 1.51/0.83  --problem_path                          ""
% 1.51/0.83  --include_path                          ""
% 1.51/0.83  --clausifier                            res/vclausify_rel
% 1.51/0.83  --clausifier_options                    --mode clausify
% 1.51/0.83  --stdin                                 false
% 1.51/0.83  --stats_out                             all
% 1.51/0.83  
% 1.51/0.83  ------ General Options
% 1.51/0.83  
% 1.51/0.83  --fof                                   false
% 1.51/0.83  --time_out_real                         305.
% 1.51/0.83  --time_out_virtual                      -1.
% 1.51/0.83  --symbol_type_check                     false
% 1.51/0.83  --clausify_out                          false
% 1.51/0.83  --sig_cnt_out                           false
% 1.51/0.83  --trig_cnt_out                          false
% 1.51/0.83  --trig_cnt_out_tolerance                1.
% 1.51/0.83  --trig_cnt_out_sk_spl                   false
% 1.51/0.83  --abstr_cl_out                          false
% 1.51/0.83  
% 1.51/0.83  ------ Global Options
% 1.51/0.83  
% 1.51/0.83  --schedule                              default
% 1.51/0.83  --add_important_lit                     false
% 1.51/0.83  --prop_solver_per_cl                    1000
% 1.51/0.83  --min_unsat_core                        false
% 1.51/0.83  --soft_assumptions                      false
% 1.51/0.83  --soft_lemma_size                       3
% 1.51/0.83  --prop_impl_unit_size                   0
% 1.51/0.83  --prop_impl_unit                        []
% 1.51/0.83  --share_sel_clauses                     true
% 1.51/0.83  --reset_solvers                         false
% 1.51/0.83  --bc_imp_inh                            [conj_cone]
% 1.51/0.83  --conj_cone_tolerance                   3.
% 1.51/0.83  --extra_neg_conj                        none
% 1.51/0.83  --large_theory_mode                     true
% 1.51/0.83  --prolific_symb_bound                   200
% 1.51/0.83  --lt_threshold                          2000
% 1.51/0.83  --clause_weak_htbl                      true
% 1.51/0.83  --gc_record_bc_elim                     false
% 1.51/0.83  
% 1.51/0.83  ------ Preprocessing Options
% 1.51/0.83  
% 1.51/0.83  --preprocessing_flag                    true
% 1.51/0.83  --time_out_prep_mult                    0.1
% 1.51/0.83  --splitting_mode                        input
% 1.51/0.83  --splitting_grd                         true
% 1.51/0.83  --splitting_cvd                         false
% 1.51/0.83  --splitting_cvd_svl                     false
% 1.51/0.83  --splitting_nvd                         32
% 1.51/0.83  --sub_typing                            true
% 1.51/0.83  --prep_gs_sim                           true
% 1.51/0.83  --prep_unflatten                        true
% 1.51/0.83  --prep_res_sim                          true
% 1.51/0.83  --prep_upred                            true
% 1.51/0.83  --prep_sem_filter                       exhaustive
% 1.51/0.83  --prep_sem_filter_out                   false
% 1.51/0.83  --pred_elim                             true
% 1.51/0.83  --res_sim_input                         true
% 1.51/0.83  --eq_ax_congr_red                       true
% 1.51/0.83  --pure_diseq_elim                       true
% 1.51/0.83  --brand_transform                       false
% 1.51/0.83  --non_eq_to_eq                          false
% 1.51/0.83  --prep_def_merge                        true
% 1.51/0.83  --prep_def_merge_prop_impl              false
% 1.51/0.83  --prep_def_merge_mbd                    true
% 1.51/0.83  --prep_def_merge_tr_red                 false
% 1.51/0.83  --prep_def_merge_tr_cl                  false
% 1.51/0.83  --smt_preprocessing                     true
% 1.51/0.83  --smt_ac_axioms                         fast
% 1.51/0.83  --preprocessed_out                      false
% 1.51/0.83  --preprocessed_stats                    false
% 1.51/0.83  
% 1.51/0.83  ------ Abstraction refinement Options
% 1.51/0.83  
% 1.51/0.83  --abstr_ref                             []
% 1.51/0.83  --abstr_ref_prep                        false
% 1.51/0.83  --abstr_ref_until_sat                   false
% 1.51/0.83  --abstr_ref_sig_restrict                funpre
% 1.51/0.83  --abstr_ref_af_restrict_to_split_sk     false
% 1.51/0.83  --abstr_ref_under                       []
% 1.51/0.83  
% 1.51/0.83  ------ SAT Options
% 1.51/0.83  
% 1.51/0.83  --sat_mode                              false
% 1.51/0.83  --sat_fm_restart_options                ""
% 1.51/0.83  --sat_gr_def                            false
% 1.51/0.83  --sat_epr_types                         true
% 1.51/0.83  --sat_non_cyclic_types                  false
% 1.51/0.83  --sat_finite_models                     false
% 1.51/0.83  --sat_fm_lemmas                         false
% 1.51/0.83  --sat_fm_prep                           false
% 1.51/0.83  --sat_fm_uc_incr                        true
% 1.51/0.83  --sat_out_model                         small
% 1.51/0.83  --sat_out_clauses                       false
% 1.51/0.83  
% 1.51/0.83  ------ QBF Options
% 1.51/0.83  
% 1.51/0.83  --qbf_mode                              false
% 1.51/0.83  --qbf_elim_univ                         false
% 1.51/0.83  --qbf_dom_inst                          none
% 1.51/0.83  --qbf_dom_pre_inst                      false
% 1.51/0.83  --qbf_sk_in                             false
% 1.51/0.83  --qbf_pred_elim                         true
% 1.51/0.83  --qbf_split                             512
% 1.51/0.83  
% 1.51/0.83  ------ BMC1 Options
% 1.51/0.83  
% 1.51/0.83  --bmc1_incremental                      false
% 1.51/0.83  --bmc1_axioms                           reachable_all
% 1.51/0.83  --bmc1_min_bound                        0
% 1.51/0.83  --bmc1_max_bound                        -1
% 1.51/0.83  --bmc1_max_bound_default                -1
% 1.51/0.83  --bmc1_symbol_reachability              true
% 1.51/0.83  --bmc1_property_lemmas                  false
% 1.51/0.83  --bmc1_k_induction                      false
% 1.51/0.83  --bmc1_non_equiv_states                 false
% 1.51/0.83  --bmc1_deadlock                         false
% 1.51/0.83  --bmc1_ucm                              false
% 1.51/0.83  --bmc1_add_unsat_core                   none
% 1.51/0.83  --bmc1_unsat_core_children              false
% 1.51/0.83  --bmc1_unsat_core_extrapolate_axioms    false
% 1.51/0.83  --bmc1_out_stat                         full
% 1.51/0.83  --bmc1_ground_init                      false
% 1.51/0.83  --bmc1_pre_inst_next_state              false
% 1.51/0.83  --bmc1_pre_inst_state                   false
% 1.51/0.83  --bmc1_pre_inst_reach_state             false
% 1.51/0.83  --bmc1_out_unsat_core                   false
% 1.51/0.83  --bmc1_aig_witness_out                  false
% 1.51/0.83  --bmc1_verbose                          false
% 1.51/0.83  --bmc1_dump_clauses_tptp                false
% 1.51/0.83  --bmc1_dump_unsat_core_tptp             false
% 1.51/0.83  --bmc1_dump_file                        -
% 1.51/0.83  --bmc1_ucm_expand_uc_limit              128
% 1.51/0.83  --bmc1_ucm_n_expand_iterations          6
% 1.51/0.83  --bmc1_ucm_extend_mode                  1
% 1.51/0.83  --bmc1_ucm_init_mode                    2
% 1.51/0.83  --bmc1_ucm_cone_mode                    none
% 1.51/0.83  --bmc1_ucm_reduced_relation_type        0
% 1.51/0.83  --bmc1_ucm_relax_model                  4
% 1.51/0.83  --bmc1_ucm_full_tr_after_sat            true
% 1.51/0.83  --bmc1_ucm_expand_neg_assumptions       false
% 1.51/0.83  --bmc1_ucm_layered_model                none
% 1.51/0.83  --bmc1_ucm_max_lemma_size               10
% 1.51/0.83  
% 1.51/0.83  ------ AIG Options
% 1.51/0.83  
% 1.51/0.83  --aig_mode                              false
% 1.51/0.83  
% 1.51/0.83  ------ Instantiation Options
% 1.51/0.83  
% 1.51/0.83  --instantiation_flag                    true
% 1.51/0.83  --inst_sos_flag                         false
% 1.51/0.83  --inst_sos_phase                        true
% 1.51/0.83  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.51/0.83  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.51/0.83  --inst_lit_sel_side                     none
% 1.51/0.83  --inst_solver_per_active                1400
% 1.51/0.83  --inst_solver_calls_frac                1.
% 1.51/0.83  --inst_passive_queue_type               priority_queues
% 1.51/0.83  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.51/0.83  --inst_passive_queues_freq              [25;2]
% 1.51/0.83  --inst_dismatching                      true
% 1.51/0.83  --inst_eager_unprocessed_to_passive     true
% 1.51/0.83  --inst_prop_sim_given                   true
% 1.51/0.83  --inst_prop_sim_new                     false
% 1.51/0.83  --inst_subs_new                         false
% 1.51/0.83  --inst_eq_res_simp                      false
% 1.51/0.83  --inst_subs_given                       false
% 1.51/0.83  --inst_orphan_elimination               true
% 1.51/0.83  --inst_learning_loop_flag               true
% 1.51/0.83  --inst_learning_start                   3000
% 1.51/0.83  --inst_learning_factor                  2
% 1.51/0.83  --inst_start_prop_sim_after_learn       3
% 1.51/0.83  --inst_sel_renew                        solver
% 1.51/0.83  --inst_lit_activity_flag                true
% 1.51/0.83  --inst_restr_to_given                   false
% 1.51/0.83  --inst_activity_threshold               500
% 1.51/0.83  --inst_out_proof                        true
% 1.51/0.83  
% 1.51/0.83  ------ Resolution Options
% 1.51/0.83  
% 1.51/0.83  --resolution_flag                       false
% 1.51/0.83  --res_lit_sel                           adaptive
% 1.51/0.83  --res_lit_sel_side                      none
% 1.51/0.83  --res_ordering                          kbo
% 1.51/0.83  --res_to_prop_solver                    active
% 1.51/0.83  --res_prop_simpl_new                    false
% 1.51/0.83  --res_prop_simpl_given                  true
% 1.51/0.83  --res_passive_queue_type                priority_queues
% 1.51/0.83  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.51/0.83  --res_passive_queues_freq               [15;5]
% 1.51/0.83  --res_forward_subs                      full
% 1.51/0.83  --res_backward_subs                     full
% 1.51/0.83  --res_forward_subs_resolution           true
% 1.51/0.83  --res_backward_subs_resolution          true
% 1.51/0.83  --res_orphan_elimination                true
% 1.51/0.83  --res_time_limit                        2.
% 1.51/0.83  --res_out_proof                         true
% 1.51/0.83  
% 1.51/0.83  ------ Superposition Options
% 1.51/0.83  
% 1.51/0.83  --superposition_flag                    true
% 1.51/0.83  --sup_passive_queue_type                priority_queues
% 1.51/0.83  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.51/0.83  --sup_passive_queues_freq               [8;1;4]
% 1.51/0.83  --demod_completeness_check              fast
% 1.51/0.83  --demod_use_ground                      true
% 1.51/0.83  --sup_to_prop_solver                    passive
% 1.51/0.83  --sup_prop_simpl_new                    true
% 1.51/0.83  --sup_prop_simpl_given                  true
% 1.51/0.83  --sup_fun_splitting                     false
% 1.51/0.83  --sup_smt_interval                      50000
% 1.51/0.83  
% 1.51/0.83  ------ Superposition Simplification Setup
% 1.51/0.83  
% 1.51/0.83  --sup_indices_passive                   []
% 1.51/0.83  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.51/0.83  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.51/0.83  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.51/0.83  --sup_full_triv                         [TrivRules;PropSubs]
% 1.51/0.83  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.51/0.83  --sup_full_bw                           [BwDemod]
% 1.51/0.83  --sup_immed_triv                        [TrivRules]
% 1.51/0.83  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.51/0.83  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.51/0.83  --sup_immed_bw_main                     []
% 1.51/0.83  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.51/0.83  --sup_input_triv                        [Unflattening;TrivRules]
% 1.51/0.83  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.51/0.83  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.51/0.83  
% 1.51/0.83  ------ Combination Options
% 1.51/0.83  
% 1.51/0.83  --comb_res_mult                         3
% 1.51/0.83  --comb_sup_mult                         2
% 1.51/0.83  --comb_inst_mult                        10
% 1.51/0.83  
% 1.51/0.83  ------ Debug Options
% 1.51/0.83  
% 1.51/0.83  --dbg_backtrace                         false
% 1.51/0.83  --dbg_dump_prop_clauses                 false
% 1.51/0.83  --dbg_dump_prop_clauses_file            -
% 1.51/0.83  --dbg_out_stat                          false
% 1.51/0.83  
% 1.51/0.83  
% 1.51/0.83  
% 1.51/0.83  
% 1.51/0.83  ------ Proving...
% 1.51/0.83  
% 1.51/0.83  
% 1.51/0.83  % SZS status Theorem for theBenchmark.p
% 1.51/0.83  
% 1.51/0.83  % SZS output start CNFRefutation for theBenchmark.p
% 1.51/0.83  
% 1.51/0.83  fof(f10,conjecture,(
% 1.51/0.83    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (r1_tarski(k6_relat_1(X1),X2) => (r1_tarski(X1,k2_relset_1(X1,X0,X2)) & k1_relset_1(X1,X0,X2) = X1)))),
% 1.51/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.51/0.83  
% 1.51/0.83  fof(f11,negated_conjecture,(
% 1.51/0.83    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (r1_tarski(k6_relat_1(X1),X2) => (r1_tarski(X1,k2_relset_1(X1,X0,X2)) & k1_relset_1(X1,X0,X2) = X1)))),
% 1.51/0.83    inference(negated_conjecture,[],[f10])).
% 1.51/0.83  
% 1.51/0.83  fof(f19,plain,(
% 1.51/0.83    ? [X0,X1,X2] : (((~r1_tarski(X1,k2_relset_1(X1,X0,X2)) | k1_relset_1(X1,X0,X2) != X1) & r1_tarski(k6_relat_1(X1),X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 1.51/0.83    inference(ennf_transformation,[],[f11])).
% 1.51/0.83  
% 1.51/0.83  fof(f20,plain,(
% 1.51/0.83    ? [X0,X1,X2] : ((~r1_tarski(X1,k2_relset_1(X1,X0,X2)) | k1_relset_1(X1,X0,X2) != X1) & r1_tarski(k6_relat_1(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 1.51/0.83    inference(flattening,[],[f19])).
% 1.51/0.83  
% 1.51/0.83  fof(f24,plain,(
% 1.51/0.83    ? [X0,X1,X2] : ((~r1_tarski(X1,k2_relset_1(X1,X0,X2)) | k1_relset_1(X1,X0,X2) != X1) & r1_tarski(k6_relat_1(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) => ((~r1_tarski(sK1,k2_relset_1(sK1,sK0,sK2)) | k1_relset_1(sK1,sK0,sK2) != sK1) & r1_tarski(k6_relat_1(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))))),
% 1.51/0.83    introduced(choice_axiom,[])).
% 1.51/0.83  
% 1.51/0.83  fof(f25,plain,(
% 1.51/0.83    (~r1_tarski(sK1,k2_relset_1(sK1,sK0,sK2)) | k1_relset_1(sK1,sK0,sK2) != sK1) & r1_tarski(k6_relat_1(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.51/0.83    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f24])).
% 1.51/0.83  
% 1.51/0.83  fof(f41,plain,(
% 1.51/0.83    r1_tarski(k6_relat_1(sK1),sK2)),
% 1.51/0.83    inference(cnf_transformation,[],[f25])).
% 1.51/0.83  
% 1.51/0.83  fof(f4,axiom,(
% 1.51/0.83    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.51/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.51/0.83  
% 1.51/0.83  fof(f33,plain,(
% 1.51/0.83    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.51/0.83    inference(cnf_transformation,[],[f4])).
% 1.51/0.83  
% 1.51/0.83  fof(f3,axiom,(
% 1.51/0.83    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 1.51/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.51/0.83  
% 1.51/0.83  fof(f13,plain,(
% 1.51/0.83    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.51/0.83    inference(ennf_transformation,[],[f3])).
% 1.51/0.83  
% 1.51/0.83  fof(f14,plain,(
% 1.51/0.83    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.51/0.83    inference(flattening,[],[f13])).
% 1.51/0.83  
% 1.51/0.83  fof(f31,plain,(
% 1.51/0.83    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.51/0.83    inference(cnf_transformation,[],[f14])).
% 1.51/0.83  
% 1.51/0.83  fof(f5,axiom,(
% 1.51/0.83    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.51/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.51/0.83  
% 1.51/0.83  fof(f12,plain,(
% 1.51/0.83    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 1.51/0.83    inference(pure_predicate_removal,[],[f5])).
% 1.51/0.83  
% 1.51/0.83  fof(f35,plain,(
% 1.51/0.83    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.51/0.83    inference(cnf_transformation,[],[f12])).
% 1.51/0.83  
% 1.51/0.83  fof(f40,plain,(
% 1.51/0.83    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.51/0.83    inference(cnf_transformation,[],[f25])).
% 1.51/0.83  
% 1.51/0.83  fof(f6,axiom,(
% 1.51/0.83    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.51/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.51/0.83  
% 1.51/0.83  fof(f15,plain,(
% 1.51/0.83    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.51/0.83    inference(ennf_transformation,[],[f6])).
% 1.51/0.83  
% 1.51/0.83  fof(f36,plain,(
% 1.51/0.83    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.51/0.83    inference(cnf_transformation,[],[f15])).
% 1.51/0.83  
% 1.51/0.83  fof(f1,axiom,(
% 1.51/0.83    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.51/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.51/0.83  
% 1.51/0.83  fof(f21,plain,(
% 1.51/0.83    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.51/0.83    inference(nnf_transformation,[],[f1])).
% 1.51/0.83  
% 1.51/0.83  fof(f22,plain,(
% 1.51/0.83    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.51/0.83    inference(flattening,[],[f21])).
% 1.51/0.83  
% 1.51/0.83  fof(f28,plain,(
% 1.51/0.83    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 1.51/0.83    inference(cnf_transformation,[],[f22])).
% 1.51/0.83  
% 1.51/0.83  fof(f8,axiom,(
% 1.51/0.83    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 1.51/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.51/0.83  
% 1.51/0.83  fof(f17,plain,(
% 1.51/0.83    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.51/0.83    inference(ennf_transformation,[],[f8])).
% 1.51/0.83  
% 1.51/0.83  fof(f38,plain,(
% 1.51/0.83    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.51/0.83    inference(cnf_transformation,[],[f17])).
% 1.51/0.83  
% 1.51/0.83  fof(f7,axiom,(
% 1.51/0.83    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 1.51/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.51/0.83  
% 1.51/0.83  fof(f16,plain,(
% 1.51/0.83    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.51/0.83    inference(ennf_transformation,[],[f7])).
% 1.51/0.83  
% 1.51/0.83  fof(f37,plain,(
% 1.51/0.83    ( ! [X2,X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.51/0.83    inference(cnf_transformation,[],[f16])).
% 1.51/0.83  
% 1.51/0.83  fof(f2,axiom,(
% 1.51/0.83    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.51/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.51/0.83  
% 1.51/0.83  fof(f23,plain,(
% 1.51/0.83    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.51/0.83    inference(nnf_transformation,[],[f2])).
% 1.51/0.83  
% 1.51/0.83  fof(f29,plain,(
% 1.51/0.83    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.51/0.83    inference(cnf_transformation,[],[f23])).
% 1.51/0.83  
% 1.51/0.83  fof(f32,plain,(
% 1.51/0.83    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.51/0.83    inference(cnf_transformation,[],[f14])).
% 1.51/0.83  
% 1.51/0.83  fof(f9,axiom,(
% 1.51/0.83    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 1.51/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.51/0.83  
% 1.51/0.83  fof(f18,plain,(
% 1.51/0.83    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.51/0.83    inference(ennf_transformation,[],[f9])).
% 1.51/0.83  
% 1.51/0.83  fof(f39,plain,(
% 1.51/0.83    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.51/0.83    inference(cnf_transformation,[],[f18])).
% 1.51/0.83  
% 1.51/0.83  fof(f26,plain,(
% 1.51/0.83    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.51/0.83    inference(cnf_transformation,[],[f22])).
% 1.51/0.83  
% 1.51/0.83  fof(f44,plain,(
% 1.51/0.83    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.51/0.83    inference(equality_resolution,[],[f26])).
% 1.51/0.83  
% 1.51/0.83  fof(f34,plain,(
% 1.51/0.83    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.51/0.83    inference(cnf_transformation,[],[f4])).
% 1.51/0.83  
% 1.51/0.83  fof(f42,plain,(
% 1.51/0.83    ~r1_tarski(sK1,k2_relset_1(sK1,sK0,sK2)) | k1_relset_1(sK1,sK0,sK2) != sK1),
% 1.51/0.83    inference(cnf_transformation,[],[f25])).
% 1.51/0.83  
% 1.51/0.83  cnf(c_341,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 1.51/0.83  
% 1.51/0.83  cnf(c_2400,plain,
% 1.51/0.83      ( k2_relat_1(k6_relat_1(X0)) != X1
% 1.51/0.83      | sK1 != X1
% 1.51/0.83      | sK1 = k2_relat_1(k6_relat_1(X0)) ),
% 1.51/0.83      inference(instantiation,[status(thm)],[c_341]) ).
% 1.51/0.83  
% 1.51/0.83  cnf(c_2401,plain,
% 1.51/0.83      ( k2_relat_1(k6_relat_1(sK1)) != sK1
% 1.51/0.83      | sK1 = k2_relat_1(k6_relat_1(sK1))
% 1.51/0.83      | sK1 != sK1 ),
% 1.51/0.83      inference(instantiation,[status(thm)],[c_2400]) ).
% 1.51/0.83  
% 1.51/0.83  cnf(c_15,negated_conjecture,
% 1.51/0.83      ( r1_tarski(k6_relat_1(sK1),sK2) ),
% 1.51/0.83      inference(cnf_transformation,[],[f41]) ).
% 1.51/0.83  
% 1.51/0.83  cnf(c_713,plain,
% 1.51/0.83      ( r1_tarski(k6_relat_1(sK1),sK2) = iProver_top ),
% 1.51/0.83      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 1.51/0.83  
% 1.51/0.83  cnf(c_8,plain,
% 1.51/0.83      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 1.51/0.83      inference(cnf_transformation,[],[f33]) ).
% 1.51/0.83  
% 1.51/0.83  cnf(c_6,plain,
% 1.51/0.83      ( ~ r1_tarski(X0,X1)
% 1.51/0.83      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 1.51/0.83      | ~ v1_relat_1(X1)
% 1.51/0.83      | ~ v1_relat_1(X0) ),
% 1.51/0.83      inference(cnf_transformation,[],[f31]) ).
% 1.51/0.83  
% 1.51/0.83  cnf(c_720,plain,
% 1.51/0.83      ( r1_tarski(X0,X1) != iProver_top
% 1.51/0.83      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) = iProver_top
% 1.51/0.83      | v1_relat_1(X0) != iProver_top
% 1.51/0.83      | v1_relat_1(X1) != iProver_top ),
% 1.51/0.83      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 1.51/0.83  
% 1.51/0.83  cnf(c_1858,plain,
% 1.51/0.83      ( r1_tarski(X0,k1_relat_1(X1)) = iProver_top
% 1.51/0.83      | r1_tarski(k6_relat_1(X0),X1) != iProver_top
% 1.51/0.83      | v1_relat_1(X1) != iProver_top
% 1.51/0.83      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 1.51/0.83      inference(superposition,[status(thm)],[c_8,c_720]) ).
% 1.51/0.83  
% 1.51/0.83  cnf(c_9,plain,
% 1.51/0.83      ( v1_relat_1(k6_relat_1(X0)) ),
% 1.51/0.83      inference(cnf_transformation,[],[f35]) ).
% 1.51/0.83  
% 1.51/0.83  cnf(c_32,plain,
% 1.51/0.83      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 1.51/0.83      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 1.51/0.83  
% 1.51/0.83  cnf(c_2064,plain,
% 1.51/0.83      ( v1_relat_1(X1) != iProver_top
% 1.51/0.83      | r1_tarski(k6_relat_1(X0),X1) != iProver_top
% 1.51/0.83      | r1_tarski(X0,k1_relat_1(X1)) = iProver_top ),
% 1.51/0.83      inference(global_propositional_subsumption,
% 1.51/0.83                [status(thm)],
% 1.51/0.83                [c_1858,c_32]) ).
% 1.51/0.83  
% 1.51/0.83  cnf(c_2065,plain,
% 1.51/0.83      ( r1_tarski(X0,k1_relat_1(X1)) = iProver_top
% 1.51/0.83      | r1_tarski(k6_relat_1(X0),X1) != iProver_top
% 1.51/0.83      | v1_relat_1(X1) != iProver_top ),
% 1.51/0.83      inference(renaming,[status(thm)],[c_2064]) ).
% 1.51/0.83  
% 1.51/0.83  cnf(c_2074,plain,
% 1.51/0.83      ( r1_tarski(sK1,k1_relat_1(sK2)) = iProver_top
% 1.51/0.83      | v1_relat_1(sK2) != iProver_top ),
% 1.51/0.83      inference(superposition,[status(thm)],[c_713,c_2065]) ).
% 1.51/0.83  
% 1.51/0.83  cnf(c_16,negated_conjecture,
% 1.51/0.83      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 1.51/0.83      inference(cnf_transformation,[],[f40]) ).
% 1.51/0.83  
% 1.51/0.83  cnf(c_17,plain,
% 1.51/0.83      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 1.51/0.83      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 1.51/0.83  
% 1.51/0.83  cnf(c_10,plain,
% 1.51/0.83      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.51/0.83      | v1_relat_1(X0) ),
% 1.51/0.83      inference(cnf_transformation,[],[f36]) ).
% 1.51/0.83  
% 1.51/0.83  cnf(c_831,plain,
% 1.51/0.83      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 1.51/0.83      | v1_relat_1(sK2) ),
% 1.51/0.83      inference(instantiation,[status(thm)],[c_10]) ).
% 1.51/0.83  
% 1.51/0.83  cnf(c_832,plain,
% 1.51/0.83      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 1.51/0.83      | v1_relat_1(sK2) = iProver_top ),
% 1.51/0.83      inference(predicate_to_equality,[status(thm)],[c_831]) ).
% 1.51/0.83  
% 1.51/0.83  cnf(c_2321,plain,
% 1.51/0.83      ( r1_tarski(sK1,k1_relat_1(sK2)) = iProver_top ),
% 1.51/0.83      inference(global_propositional_subsumption,
% 1.51/0.83                [status(thm)],
% 1.51/0.83                [c_2074,c_17,c_832]) ).
% 1.51/0.83  
% 1.51/0.83  cnf(c_0,plain,
% 1.51/0.83      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 1.51/0.83      inference(cnf_transformation,[],[f28]) ).
% 1.51/0.83  
% 1.51/0.83  cnf(c_725,plain,
% 1.51/0.83      ( X0 = X1
% 1.51/0.83      | r1_tarski(X0,X1) != iProver_top
% 1.51/0.83      | r1_tarski(X1,X0) != iProver_top ),
% 1.51/0.83      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 1.51/0.83  
% 1.51/0.83  cnf(c_2326,plain,
% 1.51/0.83      ( k1_relat_1(sK2) = sK1
% 1.51/0.83      | r1_tarski(k1_relat_1(sK2),sK1) != iProver_top ),
% 1.51/0.83      inference(superposition,[status(thm)],[c_2321,c_725]) ).
% 1.51/0.83  
% 1.51/0.83  cnf(c_712,plain,
% 1.51/0.83      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 1.51/0.83      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 1.51/0.83  
% 1.51/0.83  cnf(c_12,plain,
% 1.51/0.83      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.51/0.83      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 1.51/0.83      inference(cnf_transformation,[],[f38]) ).
% 1.51/0.83  
% 1.51/0.83  cnf(c_716,plain,
% 1.51/0.83      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 1.51/0.83      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 1.51/0.83      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 1.51/0.83  
% 1.51/0.83  cnf(c_1478,plain,
% 1.51/0.83      ( k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2) ),
% 1.51/0.83      inference(superposition,[status(thm)],[c_712,c_716]) ).
% 1.51/0.83  
% 1.51/0.83  cnf(c_11,plain,
% 1.51/0.83      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.51/0.83      | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 1.51/0.83      inference(cnf_transformation,[],[f37]) ).
% 1.51/0.83  
% 1.51/0.83  cnf(c_717,plain,
% 1.51/0.83      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 1.51/0.83      | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 1.51/0.83      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 1.51/0.83  
% 1.51/0.83  cnf(c_1577,plain,
% 1.51/0.83      ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK1)) = iProver_top
% 1.51/0.83      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 1.51/0.83      inference(superposition,[status(thm)],[c_1478,c_717]) ).
% 1.51/0.83  
% 1.51/0.83  cnf(c_1695,plain,
% 1.51/0.83      ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK1)) = iProver_top ),
% 1.51/0.83      inference(global_propositional_subsumption,
% 1.51/0.83                [status(thm)],
% 1.51/0.83                [c_1577,c_17]) ).
% 1.51/0.83  
% 1.51/0.83  cnf(c_4,plain,
% 1.51/0.83      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 1.51/0.83      inference(cnf_transformation,[],[f29]) ).
% 1.51/0.83  
% 1.51/0.83  cnf(c_722,plain,
% 1.51/0.83      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 1.51/0.83      | r1_tarski(X0,X1) = iProver_top ),
% 1.51/0.83      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 1.51/0.83  
% 1.51/0.83  cnf(c_1700,plain,
% 1.51/0.83      ( r1_tarski(k1_relat_1(sK2),sK1) = iProver_top ),
% 1.51/0.83      inference(superposition,[status(thm)],[c_1695,c_722]) ).
% 1.51/0.83  
% 1.51/0.83  cnf(c_1890,plain,
% 1.51/0.83      ( k1_relat_1(sK2) = sK1
% 1.51/0.83      | r1_tarski(sK1,k1_relat_1(sK2)) != iProver_top ),
% 1.51/0.83      inference(superposition,[status(thm)],[c_1700,c_725]) ).
% 1.51/0.83  
% 1.51/0.83  cnf(c_2329,plain,
% 1.51/0.83      ( k1_relat_1(sK2) = sK1 ),
% 1.51/0.83      inference(global_propositional_subsumption,
% 1.51/0.83                [status(thm)],
% 1.51/0.83                [c_2326,c_17,c_832,c_1890,c_2074]) ).
% 1.51/0.83  
% 1.51/0.83  cnf(c_2336,plain,
% 1.51/0.83      ( k1_relset_1(sK1,sK0,sK2) = sK1 ),
% 1.51/0.83      inference(demodulation,[status(thm)],[c_2329,c_1478]) ).
% 1.51/0.83  
% 1.51/0.83  cnf(c_342,plain,
% 1.51/0.83      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 1.51/0.83      theory(equality) ).
% 1.51/0.83  
% 1.51/0.83  cnf(c_860,plain,
% 1.51/0.83      ( ~ r1_tarski(X0,X1)
% 1.51/0.83      | r1_tarski(sK1,k2_relset_1(sK1,sK0,sK2))
% 1.51/0.83      | k2_relset_1(sK1,sK0,sK2) != X1
% 1.51/0.83      | sK1 != X0 ),
% 1.51/0.83      inference(instantiation,[status(thm)],[c_342]) ).
% 1.51/0.83  
% 1.51/0.83  cnf(c_915,plain,
% 1.51/0.83      ( ~ r1_tarski(X0,k2_relat_1(sK2))
% 1.51/0.83      | r1_tarski(sK1,k2_relset_1(sK1,sK0,sK2))
% 1.51/0.83      | k2_relset_1(sK1,sK0,sK2) != k2_relat_1(sK2)
% 1.51/0.83      | sK1 != X0 ),
% 1.51/0.83      inference(instantiation,[status(thm)],[c_860]) ).
% 1.51/0.83  
% 1.51/0.83  cnf(c_1553,plain,
% 1.51/0.83      ( ~ r1_tarski(k2_relat_1(k6_relat_1(X0)),k2_relat_1(sK2))
% 1.51/0.83      | r1_tarski(sK1,k2_relset_1(sK1,sK0,sK2))
% 1.51/0.83      | k2_relset_1(sK1,sK0,sK2) != k2_relat_1(sK2)
% 1.51/0.83      | sK1 != k2_relat_1(k6_relat_1(X0)) ),
% 1.51/0.83      inference(instantiation,[status(thm)],[c_915]) ).
% 1.51/0.83  
% 1.51/0.83  cnf(c_1555,plain,
% 1.51/0.83      ( ~ r1_tarski(k2_relat_1(k6_relat_1(sK1)),k2_relat_1(sK2))
% 1.51/0.83      | r1_tarski(sK1,k2_relset_1(sK1,sK0,sK2))
% 1.51/0.83      | k2_relset_1(sK1,sK0,sK2) != k2_relat_1(sK2)
% 1.51/0.83      | sK1 != k2_relat_1(k6_relat_1(sK1)) ),
% 1.51/0.83      inference(instantiation,[status(thm)],[c_1553]) ).
% 1.51/0.83  
% 1.51/0.83  cnf(c_5,plain,
% 1.51/0.83      ( ~ r1_tarski(X0,X1)
% 1.51/0.83      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 1.51/0.83      | ~ v1_relat_1(X1)
% 1.51/0.83      | ~ v1_relat_1(X0) ),
% 1.51/0.83      inference(cnf_transformation,[],[f32]) ).
% 1.51/0.83  
% 1.51/0.83  cnf(c_883,plain,
% 1.51/0.83      ( ~ r1_tarski(X0,sK2)
% 1.51/0.83      | r1_tarski(k2_relat_1(X0),k2_relat_1(sK2))
% 1.51/0.83      | ~ v1_relat_1(X0)
% 1.51/0.83      | ~ v1_relat_1(sK2) ),
% 1.51/0.83      inference(instantiation,[status(thm)],[c_5]) ).
% 1.51/0.83  
% 1.51/0.83  cnf(c_1043,plain,
% 1.51/0.83      ( ~ r1_tarski(k6_relat_1(X0),sK2)
% 1.51/0.83      | r1_tarski(k2_relat_1(k6_relat_1(X0)),k2_relat_1(sK2))
% 1.51/0.83      | ~ v1_relat_1(k6_relat_1(X0))
% 1.51/0.83      | ~ v1_relat_1(sK2) ),
% 1.51/0.83      inference(instantiation,[status(thm)],[c_883]) ).
% 1.51/0.83  
% 1.51/0.83  cnf(c_1045,plain,
% 1.51/0.83      ( ~ r1_tarski(k6_relat_1(sK1),sK2)
% 1.51/0.83      | r1_tarski(k2_relat_1(k6_relat_1(sK1)),k2_relat_1(sK2))
% 1.51/0.83      | ~ v1_relat_1(k6_relat_1(sK1))
% 1.51/0.83      | ~ v1_relat_1(sK2) ),
% 1.51/0.83      inference(instantiation,[status(thm)],[c_1043]) ).
% 1.51/0.83  
% 1.51/0.83  cnf(c_13,plain,
% 1.51/0.83      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.51/0.83      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 1.51/0.83      inference(cnf_transformation,[],[f39]) ).
% 1.51/0.83  
% 1.51/0.83  cnf(c_857,plain,
% 1.51/0.83      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 1.51/0.83      | k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2) ),
% 1.51/0.83      inference(instantiation,[status(thm)],[c_13]) ).
% 1.51/0.83  
% 1.51/0.83  cnf(c_54,plain,
% 1.51/0.83      ( ~ r1_tarski(sK1,sK1) | sK1 = sK1 ),
% 1.51/0.83      inference(instantiation,[status(thm)],[c_0]) ).
% 1.51/0.83  
% 1.51/0.83  cnf(c_2,plain,
% 1.51/0.83      ( r1_tarski(X0,X0) ),
% 1.51/0.83      inference(cnf_transformation,[],[f44]) ).
% 1.51/0.83  
% 1.51/0.83  cnf(c_50,plain,
% 1.51/0.83      ( r1_tarski(sK1,sK1) ),
% 1.51/0.83      inference(instantiation,[status(thm)],[c_2]) ).
% 1.51/0.83  
% 1.51/0.83  cnf(c_7,plain,
% 1.51/0.83      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 1.51/0.83      inference(cnf_transformation,[],[f34]) ).
% 1.51/0.83  
% 1.51/0.83  cnf(c_36,plain,
% 1.51/0.83      ( k2_relat_1(k6_relat_1(sK1)) = sK1 ),
% 1.51/0.83      inference(instantiation,[status(thm)],[c_7]) ).
% 1.51/0.83  
% 1.51/0.83  cnf(c_33,plain,
% 1.51/0.83      ( v1_relat_1(k6_relat_1(sK1)) ),
% 1.51/0.83      inference(instantiation,[status(thm)],[c_9]) ).
% 1.51/0.83  
% 1.51/0.83  cnf(c_14,negated_conjecture,
% 1.51/0.83      ( ~ r1_tarski(sK1,k2_relset_1(sK1,sK0,sK2))
% 1.51/0.83      | k1_relset_1(sK1,sK0,sK2) != sK1 ),
% 1.51/0.83      inference(cnf_transformation,[],[f42]) ).
% 1.51/0.83  
% 1.51/0.83  cnf(contradiction,plain,
% 1.51/0.83      ( $false ),
% 1.51/0.83      inference(minisat,
% 1.51/0.83                [status(thm)],
% 1.51/0.83                [c_2401,c_2336,c_1555,c_1045,c_857,c_831,c_54,c_50,c_36,
% 1.51/0.83                 c_33,c_14,c_15,c_16]) ).
% 1.51/0.83  
% 1.51/0.83  
% 1.51/0.83  % SZS output end CNFRefutation for theBenchmark.p
% 1.51/0.83  
% 1.51/0.83  ------                               Statistics
% 1.51/0.83  
% 1.51/0.83  ------ General
% 1.51/0.83  
% 1.51/0.83  abstr_ref_over_cycles:                  0
% 1.51/0.83  abstr_ref_under_cycles:                 0
% 1.51/0.83  gc_basic_clause_elim:                   0
% 1.51/0.83  forced_gc_time:                         0
% 1.51/0.83  parsing_time:                           0.006
% 1.51/0.83  unif_index_cands_time:                  0.
% 1.51/0.83  unif_index_add_time:                    0.
% 1.51/0.83  orderings_time:                         0.
% 1.51/0.83  out_proof_time:                         0.01
% 1.51/0.83  total_time:                             0.081
% 1.51/0.83  num_of_symbols:                         44
% 1.51/0.83  num_of_terms:                           2417
% 1.51/0.83  
% 1.51/0.83  ------ Preprocessing
% 1.51/0.83  
% 1.51/0.83  num_of_splits:                          0
% 1.51/0.83  num_of_split_atoms:                     0
% 1.51/0.83  num_of_reused_defs:                     0
% 1.51/0.83  num_eq_ax_congr_red:                    0
% 1.51/0.83  num_of_sem_filtered_clauses:            1
% 1.51/0.83  num_of_subtypes:                        0
% 1.51/0.83  monotx_restored_types:                  0
% 1.51/0.83  sat_num_of_epr_types:                   0
% 1.51/0.83  sat_num_of_non_cyclic_types:            0
% 1.51/0.83  sat_guarded_non_collapsed_types:        0
% 1.51/0.83  num_pure_diseq_elim:                    0
% 1.51/0.83  simp_replaced_by:                       0
% 1.51/0.83  res_preprocessed:                       89
% 1.51/0.83  prep_upred:                             0
% 1.51/0.83  prep_unflattend:                        0
% 1.51/0.83  smt_new_axioms:                         0
% 1.51/0.83  pred_elim_cands:                        3
% 1.51/0.83  pred_elim:                              0
% 1.51/0.83  pred_elim_cl:                           0
% 1.51/0.83  pred_elim_cycles:                       2
% 1.51/0.83  merged_defs:                            8
% 1.51/0.83  merged_defs_ncl:                        0
% 1.51/0.83  bin_hyper_res:                          8
% 1.51/0.83  prep_cycles:                            4
% 1.51/0.83  pred_elim_time:                         0.
% 1.51/0.83  splitting_time:                         0.
% 1.51/0.83  sem_filter_time:                        0.
% 1.51/0.83  monotx_time:                            0.
% 1.51/0.83  subtype_inf_time:                       0.
% 1.51/0.83  
% 1.51/0.83  ------ Problem properties
% 1.51/0.83  
% 1.51/0.83  clauses:                                16
% 1.51/0.83  conjectures:                            3
% 1.51/0.83  epr:                                    2
% 1.51/0.83  horn:                                   16
% 1.51/0.83  ground:                                 3
% 1.51/0.83  unary:                                  6
% 1.51/0.83  binary:                                 7
% 1.51/0.83  lits:                                   31
% 1.51/0.83  lits_eq:                                6
% 1.51/0.83  fd_pure:                                0
% 1.51/0.83  fd_pseudo:                              0
% 1.51/0.83  fd_cond:                                0
% 1.51/0.83  fd_pseudo_cond:                         1
% 1.51/0.83  ac_symbols:                             0
% 1.51/0.83  
% 1.51/0.83  ------ Propositional Solver
% 1.51/0.83  
% 1.51/0.83  prop_solver_calls:                      26
% 1.51/0.83  prop_fast_solver_calls:                 452
% 1.51/0.83  smt_solver_calls:                       0
% 1.51/0.83  smt_fast_solver_calls:                  0
% 1.51/0.83  prop_num_of_clauses:                    921
% 1.51/0.83  prop_preprocess_simplified:             3811
% 1.51/0.83  prop_fo_subsumed:                       4
% 1.51/0.83  prop_solver_time:                       0.
% 1.51/0.83  smt_solver_time:                        0.
% 1.51/0.83  smt_fast_solver_time:                   0.
% 1.51/0.83  prop_fast_solver_time:                  0.
% 1.51/0.83  prop_unsat_core_time:                   0.
% 1.51/0.83  
% 1.51/0.83  ------ QBF
% 1.51/0.83  
% 1.51/0.83  qbf_q_res:                              0
% 1.51/0.83  qbf_num_tautologies:                    0
% 1.51/0.83  qbf_prep_cycles:                        0
% 1.51/0.83  
% 1.51/0.83  ------ BMC1
% 1.51/0.83  
% 1.51/0.83  bmc1_current_bound:                     -1
% 1.51/0.83  bmc1_last_solved_bound:                 -1
% 1.51/0.83  bmc1_unsat_core_size:                   -1
% 1.51/0.83  bmc1_unsat_core_parents_size:           -1
% 1.51/0.83  bmc1_merge_next_fun:                    0
% 1.51/0.83  bmc1_unsat_core_clauses_time:           0.
% 1.51/0.83  
% 1.51/0.83  ------ Instantiation
% 1.51/0.83  
% 1.51/0.83  inst_num_of_clauses:                    279
% 1.51/0.83  inst_num_in_passive:                    113
% 1.51/0.83  inst_num_in_active:                     144
% 1.51/0.83  inst_num_in_unprocessed:                21
% 1.51/0.83  inst_num_of_loops:                      147
% 1.51/0.83  inst_num_of_learning_restarts:          0
% 1.51/0.83  inst_num_moves_active_passive:          1
% 1.51/0.83  inst_lit_activity:                      0
% 1.51/0.83  inst_lit_activity_moves:                0
% 1.51/0.83  inst_num_tautologies:                   0
% 1.51/0.83  inst_num_prop_implied:                  0
% 1.51/0.83  inst_num_existing_simplified:           0
% 1.51/0.83  inst_num_eq_res_simplified:             0
% 1.51/0.83  inst_num_child_elim:                    0
% 1.51/0.83  inst_num_of_dismatching_blockings:      48
% 1.51/0.83  inst_num_of_non_proper_insts:           267
% 1.51/0.83  inst_num_of_duplicates:                 0
% 1.51/0.83  inst_inst_num_from_inst_to_res:         0
% 1.51/0.83  inst_dismatching_checking_time:         0.
% 1.51/0.83  
% 1.51/0.83  ------ Resolution
% 1.51/0.83  
% 1.51/0.83  res_num_of_clauses:                     0
% 1.51/0.83  res_num_in_passive:                     0
% 1.51/0.83  res_num_in_active:                      0
% 1.51/0.83  res_num_of_loops:                       93
% 1.51/0.83  res_forward_subset_subsumed:            21
% 1.51/0.83  res_backward_subset_subsumed:           0
% 1.51/0.83  res_forward_subsumed:                   0
% 1.51/0.83  res_backward_subsumed:                  0
% 1.51/0.83  res_forward_subsumption_resolution:     0
% 1.51/0.83  res_backward_subsumption_resolution:    0
% 1.51/0.83  res_clause_to_clause_subsumption:       131
% 1.51/0.83  res_orphan_elimination:                 0
% 1.51/0.83  res_tautology_del:                      28
% 1.51/0.83  res_num_eq_res_simplified:              0
% 1.51/0.83  res_num_sel_changes:                    0
% 1.51/0.83  res_moves_from_active_to_pass:          0
% 1.51/0.83  
% 1.51/0.83  ------ Superposition
% 1.51/0.83  
% 1.51/0.83  sup_time_total:                         0.
% 1.51/0.83  sup_time_generating:                    0.
% 1.51/0.83  sup_time_sim_full:                      0.
% 1.51/0.83  sup_time_sim_immed:                     0.
% 1.51/0.83  
% 1.51/0.83  sup_num_of_clauses:                     40
% 1.51/0.83  sup_num_in_active:                      22
% 1.51/0.83  sup_num_in_passive:                     18
% 1.51/0.83  sup_num_of_loops:                       28
% 1.51/0.83  sup_fw_superposition:                   22
% 1.51/0.83  sup_bw_superposition:                   8
% 1.51/0.83  sup_immediate_simplified:               3
% 1.51/0.83  sup_given_eliminated:                   0
% 1.51/0.83  comparisons_done:                       0
% 1.51/0.83  comparisons_avoided:                    0
% 1.51/0.83  
% 1.51/0.83  ------ Simplifications
% 1.51/0.83  
% 1.51/0.83  
% 1.51/0.83  sim_fw_subset_subsumed:                 0
% 1.51/0.83  sim_bw_subset_subsumed:                 1
% 1.51/0.83  sim_fw_subsumed:                        3
% 1.51/0.83  sim_bw_subsumed:                        0
% 1.51/0.83  sim_fw_subsumption_res:                 1
% 1.51/0.83  sim_bw_subsumption_res:                 0
% 1.51/0.83  sim_tautology_del:                      1
% 1.51/0.83  sim_eq_tautology_del:                   1
% 1.51/0.83  sim_eq_res_simp:                        1
% 1.51/0.83  sim_fw_demodulated:                     0
% 1.51/0.83  sim_bw_demodulated:                     6
% 1.51/0.83  sim_light_normalised:                   3
% 1.51/0.83  sim_joinable_taut:                      0
% 1.51/0.83  sim_joinable_simp:                      0
% 1.51/0.83  sim_ac_normalised:                      0
% 1.51/0.83  sim_smt_subsumption:                    0
% 1.51/0.83  
%------------------------------------------------------------------------------
