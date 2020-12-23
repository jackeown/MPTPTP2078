%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:04:26 EST 2020

% Result     : Theorem 0.64s
% Output     : CNFRefutation 0.64s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 274 expanded)
%              Number of clauses        :   53 ( 100 expanded)
%              Number of leaves         :   15 (  49 expanded)
%              Depth                    :   19
%              Number of atoms          :  202 ( 697 expanded)
%              Number of equality atoms :  117 ( 415 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        & v1_funct_2(X2,k1_xboole_0,X0)
        & v1_funct_1(X2) )
     => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
          & v1_funct_2(X2,k1_xboole_0,X0)
          & v1_funct_1(X2) )
       => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f15,plain,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
          & v1_funct_1(X2) )
       => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f16,plain,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
       => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k7_relset_1(k1_xboole_0,X0,X2,X1)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f30,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != k7_relset_1(k1_xboole_0,X0,X2,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) )
   => ( k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f30])).

fof(f46,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    inference(cnf_transformation,[],[f31])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f28])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f49,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f35])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f33,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f9,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f47,plain,(
    k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_192,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)) != k1_zfmisc_1(X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_15])).

cnf(c_193,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_192])).

cnf(c_419,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)) != k1_zfmisc_1(X0)
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_193])).

cnf(c_3,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_472,plain,
    ( k1_zfmisc_1(X0) != k1_zfmisc_1(k1_xboole_0)
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_419,c_3])).

cnf(c_4,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_36,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_37,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_41,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_282,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_291,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_282])).

cnf(c_485,plain,
    ( k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0)
    | v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_472])).

cnf(c_554,plain,
    ( v1_xboole_0(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_472,c_36,c_37,c_41,c_291,c_485])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_422,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_867,plain,
    ( sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_554,c_422])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_225,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_15])).

cnf(c_226,plain,
    ( v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)) ),
    inference(unflattening,[status(thm)],[c_225])).

cnf(c_418,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_226])).

cnf(c_458,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k1_xboole_0)
    | v1_relat_1(sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_418,c_3])).

cnf(c_278,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_510,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)) ),
    inference(instantiation,[status(thm)],[c_278])).

cnf(c_513,plain,
    ( v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)) ),
    inference(instantiation,[status(thm)],[c_226])).

cnf(c_514,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_513])).

cnf(c_533,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_458,c_510,c_514])).

cnf(c_936,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_867,c_533])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_421,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1171,plain,
    ( k2_relat_1(k7_relat_1(k1_xboole_0,X0)) = k9_relat_1(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_936,c_421])).

cnf(c_9,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_5,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_12,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_8,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_127,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_12,c_8])).

cnf(c_131,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relat_1(X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_127,c_12,c_11,c_8])).

cnf(c_162,plain,
    ( k7_relat_1(X0,X1) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(X3)
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_131])).

cnf(c_163,plain,
    ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(X2) ),
    inference(unflattening,[status(thm)],[c_162])).

cnf(c_608,plain,
    ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_163])).

cnf(c_1172,plain,
    ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1171,c_9,c_608])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_216,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_15])).

cnf(c_217,plain,
    ( k7_relset_1(X0,X1,sK2,X2) = k9_relat_1(sK2,X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)) ),
    inference(unflattening,[status(thm)],[c_216])).

cnf(c_479,plain,
    ( k7_relset_1(X0,X1,sK2,X2) = k9_relat_1(sK2,X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_217,c_3])).

cnf(c_673,plain,
    ( k7_relset_1(k1_xboole_0,X0,sK2,X1) = k9_relat_1(sK2,X1) ),
    inference(superposition,[status(thm)],[c_3,c_479])).

cnf(c_14,negated_conjecture,
    ( k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_792,plain,
    ( k9_relat_1(sK2,sK1) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_673,c_14])).

cnf(c_931,plain,
    ( k9_relat_1(k1_xboole_0,sK1) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_867,c_792])).

cnf(c_1205,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1172,c_931])).

cnf(c_1206,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_1205])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:59:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 0.64/1.03  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.64/1.03  
% 0.64/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.64/1.03  
% 0.64/1.03  ------  iProver source info
% 0.64/1.03  
% 0.64/1.03  git: date: 2020-06-30 10:37:57 +0100
% 0.64/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.64/1.03  git: non_committed_changes: false
% 0.64/1.03  git: last_make_outside_of_git: false
% 0.64/1.03  
% 0.64/1.03  ------ 
% 0.64/1.03  
% 0.64/1.03  ------ Input Options
% 0.64/1.03  
% 0.64/1.03  --out_options                           all
% 0.64/1.03  --tptp_safe_out                         true
% 0.64/1.03  --problem_path                          ""
% 0.64/1.03  --include_path                          ""
% 0.64/1.03  --clausifier                            res/vclausify_rel
% 0.64/1.03  --clausifier_options                    --mode clausify
% 0.64/1.03  --stdin                                 false
% 0.64/1.03  --stats_out                             all
% 0.64/1.03  
% 0.64/1.03  ------ General Options
% 0.64/1.03  
% 0.64/1.03  --fof                                   false
% 0.64/1.03  --time_out_real                         305.
% 0.64/1.03  --time_out_virtual                      -1.
% 0.64/1.03  --symbol_type_check                     false
% 0.64/1.03  --clausify_out                          false
% 0.64/1.03  --sig_cnt_out                           false
% 0.64/1.03  --trig_cnt_out                          false
% 0.64/1.03  --trig_cnt_out_tolerance                1.
% 0.64/1.03  --trig_cnt_out_sk_spl                   false
% 0.64/1.03  --abstr_cl_out                          false
% 0.64/1.03  
% 0.64/1.03  ------ Global Options
% 0.64/1.03  
% 0.64/1.03  --schedule                              default
% 0.64/1.03  --add_important_lit                     false
% 0.64/1.03  --prop_solver_per_cl                    1000
% 0.64/1.03  --min_unsat_core                        false
% 0.64/1.03  --soft_assumptions                      false
% 0.64/1.03  --soft_lemma_size                       3
% 0.64/1.03  --prop_impl_unit_size                   0
% 0.64/1.03  --prop_impl_unit                        []
% 0.64/1.03  --share_sel_clauses                     true
% 0.64/1.03  --reset_solvers                         false
% 0.64/1.03  --bc_imp_inh                            [conj_cone]
% 0.64/1.03  --conj_cone_tolerance                   3.
% 0.64/1.03  --extra_neg_conj                        none
% 0.64/1.03  --large_theory_mode                     true
% 0.64/1.03  --prolific_symb_bound                   200
% 0.64/1.03  --lt_threshold                          2000
% 0.64/1.03  --clause_weak_htbl                      true
% 0.64/1.03  --gc_record_bc_elim                     false
% 0.64/1.03  
% 0.64/1.03  ------ Preprocessing Options
% 0.64/1.03  
% 0.64/1.03  --preprocessing_flag                    true
% 0.64/1.03  --time_out_prep_mult                    0.1
% 0.64/1.03  --splitting_mode                        input
% 0.64/1.03  --splitting_grd                         true
% 0.64/1.03  --splitting_cvd                         false
% 0.64/1.03  --splitting_cvd_svl                     false
% 0.64/1.03  --splitting_nvd                         32
% 0.64/1.03  --sub_typing                            true
% 0.64/1.03  --prep_gs_sim                           true
% 0.64/1.03  --prep_unflatten                        true
% 0.64/1.03  --prep_res_sim                          true
% 0.64/1.03  --prep_upred                            true
% 0.64/1.03  --prep_sem_filter                       exhaustive
% 0.64/1.03  --prep_sem_filter_out                   false
% 0.64/1.03  --pred_elim                             true
% 0.64/1.03  --res_sim_input                         true
% 0.64/1.03  --eq_ax_congr_red                       true
% 0.64/1.03  --pure_diseq_elim                       true
% 0.64/1.03  --brand_transform                       false
% 0.64/1.03  --non_eq_to_eq                          false
% 0.64/1.03  --prep_def_merge                        true
% 0.64/1.03  --prep_def_merge_prop_impl              false
% 0.64/1.03  --prep_def_merge_mbd                    true
% 0.64/1.03  --prep_def_merge_tr_red                 false
% 0.64/1.03  --prep_def_merge_tr_cl                  false
% 0.64/1.03  --smt_preprocessing                     true
% 0.64/1.03  --smt_ac_axioms                         fast
% 0.64/1.03  --preprocessed_out                      false
% 0.64/1.03  --preprocessed_stats                    false
% 0.64/1.03  
% 0.64/1.03  ------ Abstraction refinement Options
% 0.64/1.03  
% 0.64/1.03  --abstr_ref                             []
% 0.64/1.03  --abstr_ref_prep                        false
% 0.64/1.03  --abstr_ref_until_sat                   false
% 0.64/1.03  --abstr_ref_sig_restrict                funpre
% 0.64/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 0.64/1.03  --abstr_ref_under                       []
% 0.64/1.03  
% 0.64/1.03  ------ SAT Options
% 0.64/1.03  
% 0.64/1.03  --sat_mode                              false
% 0.64/1.03  --sat_fm_restart_options                ""
% 0.64/1.03  --sat_gr_def                            false
% 0.64/1.03  --sat_epr_types                         true
% 0.64/1.03  --sat_non_cyclic_types                  false
% 0.64/1.03  --sat_finite_models                     false
% 0.64/1.03  --sat_fm_lemmas                         false
% 0.64/1.03  --sat_fm_prep                           false
% 0.64/1.03  --sat_fm_uc_incr                        true
% 0.64/1.03  --sat_out_model                         small
% 0.64/1.03  --sat_out_clauses                       false
% 0.64/1.03  
% 0.64/1.03  ------ QBF Options
% 0.64/1.03  
% 0.64/1.03  --qbf_mode                              false
% 0.64/1.03  --qbf_elim_univ                         false
% 0.64/1.03  --qbf_dom_inst                          none
% 0.64/1.03  --qbf_dom_pre_inst                      false
% 0.64/1.03  --qbf_sk_in                             false
% 0.64/1.03  --qbf_pred_elim                         true
% 0.64/1.03  --qbf_split                             512
% 0.64/1.03  
% 0.64/1.03  ------ BMC1 Options
% 0.64/1.03  
% 0.64/1.03  --bmc1_incremental                      false
% 0.64/1.03  --bmc1_axioms                           reachable_all
% 0.64/1.03  --bmc1_min_bound                        0
% 0.64/1.03  --bmc1_max_bound                        -1
% 0.64/1.03  --bmc1_max_bound_default                -1
% 0.64/1.03  --bmc1_symbol_reachability              true
% 0.64/1.03  --bmc1_property_lemmas                  false
% 0.64/1.03  --bmc1_k_induction                      false
% 0.64/1.03  --bmc1_non_equiv_states                 false
% 0.64/1.03  --bmc1_deadlock                         false
% 0.64/1.03  --bmc1_ucm                              false
% 0.64/1.03  --bmc1_add_unsat_core                   none
% 0.64/1.03  --bmc1_unsat_core_children              false
% 0.64/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 0.64/1.03  --bmc1_out_stat                         full
% 0.64/1.03  --bmc1_ground_init                      false
% 0.64/1.03  --bmc1_pre_inst_next_state              false
% 0.64/1.03  --bmc1_pre_inst_state                   false
% 0.64/1.03  --bmc1_pre_inst_reach_state             false
% 0.64/1.03  --bmc1_out_unsat_core                   false
% 0.64/1.03  --bmc1_aig_witness_out                  false
% 0.64/1.03  --bmc1_verbose                          false
% 0.64/1.03  --bmc1_dump_clauses_tptp                false
% 0.64/1.03  --bmc1_dump_unsat_core_tptp             false
% 0.64/1.03  --bmc1_dump_file                        -
% 0.64/1.03  --bmc1_ucm_expand_uc_limit              128
% 0.64/1.03  --bmc1_ucm_n_expand_iterations          6
% 0.64/1.03  --bmc1_ucm_extend_mode                  1
% 0.64/1.03  --bmc1_ucm_init_mode                    2
% 0.64/1.03  --bmc1_ucm_cone_mode                    none
% 0.64/1.03  --bmc1_ucm_reduced_relation_type        0
% 0.64/1.03  --bmc1_ucm_relax_model                  4
% 0.64/1.03  --bmc1_ucm_full_tr_after_sat            true
% 0.64/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 0.64/1.03  --bmc1_ucm_layered_model                none
% 0.64/1.03  --bmc1_ucm_max_lemma_size               10
% 0.64/1.03  
% 0.64/1.03  ------ AIG Options
% 0.64/1.03  
% 0.64/1.03  --aig_mode                              false
% 0.64/1.03  
% 0.64/1.03  ------ Instantiation Options
% 0.64/1.03  
% 0.64/1.03  --instantiation_flag                    true
% 0.64/1.03  --inst_sos_flag                         false
% 0.64/1.03  --inst_sos_phase                        true
% 0.64/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.64/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.64/1.03  --inst_lit_sel_side                     num_symb
% 0.64/1.03  --inst_solver_per_active                1400
% 0.64/1.03  --inst_solver_calls_frac                1.
% 0.64/1.03  --inst_passive_queue_type               priority_queues
% 0.64/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.64/1.03  --inst_passive_queues_freq              [25;2]
% 0.64/1.03  --inst_dismatching                      true
% 0.64/1.03  --inst_eager_unprocessed_to_passive     true
% 0.64/1.03  --inst_prop_sim_given                   true
% 0.64/1.03  --inst_prop_sim_new                     false
% 0.64/1.03  --inst_subs_new                         false
% 0.64/1.03  --inst_eq_res_simp                      false
% 0.64/1.03  --inst_subs_given                       false
% 0.64/1.03  --inst_orphan_elimination               true
% 0.64/1.03  --inst_learning_loop_flag               true
% 0.64/1.03  --inst_learning_start                   3000
% 0.64/1.03  --inst_learning_factor                  2
% 0.64/1.03  --inst_start_prop_sim_after_learn       3
% 0.64/1.03  --inst_sel_renew                        solver
% 0.64/1.03  --inst_lit_activity_flag                true
% 0.64/1.03  --inst_restr_to_given                   false
% 0.64/1.03  --inst_activity_threshold               500
% 0.64/1.03  --inst_out_proof                        true
% 0.64/1.03  
% 0.64/1.03  ------ Resolution Options
% 0.64/1.03  
% 0.64/1.03  --resolution_flag                       true
% 0.64/1.03  --res_lit_sel                           adaptive
% 0.64/1.03  --res_lit_sel_side                      none
% 0.64/1.03  --res_ordering                          kbo
% 0.64/1.03  --res_to_prop_solver                    active
% 0.64/1.03  --res_prop_simpl_new                    false
% 0.64/1.03  --res_prop_simpl_given                  true
% 0.64/1.03  --res_passive_queue_type                priority_queues
% 0.64/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.64/1.03  --res_passive_queues_freq               [15;5]
% 0.64/1.03  --res_forward_subs                      full
% 0.64/1.03  --res_backward_subs                     full
% 0.64/1.03  --res_forward_subs_resolution           true
% 0.64/1.03  --res_backward_subs_resolution          true
% 0.64/1.03  --res_orphan_elimination                true
% 0.64/1.03  --res_time_limit                        2.
% 0.64/1.03  --res_out_proof                         true
% 0.64/1.03  
% 0.64/1.03  ------ Superposition Options
% 0.64/1.03  
% 0.64/1.03  --superposition_flag                    true
% 0.64/1.03  --sup_passive_queue_type                priority_queues
% 0.64/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.64/1.03  --sup_passive_queues_freq               [8;1;4]
% 0.64/1.03  --demod_completeness_check              fast
% 0.64/1.03  --demod_use_ground                      true
% 0.64/1.03  --sup_to_prop_solver                    passive
% 0.64/1.03  --sup_prop_simpl_new                    true
% 0.64/1.03  --sup_prop_simpl_given                  true
% 0.64/1.03  --sup_fun_splitting                     false
% 0.64/1.03  --sup_smt_interval                      50000
% 0.64/1.03  
% 0.64/1.03  ------ Superposition Simplification Setup
% 0.64/1.03  
% 0.64/1.03  --sup_indices_passive                   []
% 0.64/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.64/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.64/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.64/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 0.64/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.64/1.03  --sup_full_bw                           [BwDemod]
% 0.64/1.03  --sup_immed_triv                        [TrivRules]
% 0.64/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.64/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.64/1.03  --sup_immed_bw_main                     []
% 0.64/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.64/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 0.64/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.64/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.64/1.03  
% 0.64/1.03  ------ Combination Options
% 0.64/1.03  
% 0.64/1.03  --comb_res_mult                         3
% 0.64/1.03  --comb_sup_mult                         2
% 0.64/1.03  --comb_inst_mult                        10
% 0.64/1.03  
% 0.64/1.03  ------ Debug Options
% 0.64/1.03  
% 0.64/1.03  --dbg_backtrace                         false
% 0.64/1.03  --dbg_dump_prop_clauses                 false
% 0.64/1.03  --dbg_dump_prop_clauses_file            -
% 0.64/1.03  --dbg_out_stat                          false
% 0.64/1.03  ------ Parsing...
% 0.64/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.64/1.03  
% 0.64/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 0.64/1.03  
% 0.64/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.64/1.03  
% 0.64/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.64/1.03  ------ Proving...
% 0.64/1.03  ------ Problem Properties 
% 0.64/1.03  
% 0.64/1.03  
% 0.64/1.03  clauses                                 16
% 0.64/1.03  conjectures                             1
% 0.64/1.03  EPR                                     2
% 0.64/1.03  Horn                                    15
% 0.64/1.03  unary                                   6
% 0.64/1.03  binary                                  8
% 0.64/1.03  lits                                    28
% 0.64/1.03  lits eq                                 21
% 0.64/1.03  fd_pure                                 0
% 0.64/1.03  fd_pseudo                               0
% 0.64/1.03  fd_cond                                 2
% 0.64/1.03  fd_pseudo_cond                          0
% 0.64/1.03  AC symbols                              0
% 0.64/1.03  
% 0.64/1.03  ------ Schedule dynamic 5 is on 
% 0.64/1.03  
% 0.64/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.64/1.03  
% 0.64/1.03  
% 0.64/1.03  ------ 
% 0.64/1.03  Current options:
% 0.64/1.03  ------ 
% 0.64/1.03  
% 0.64/1.03  ------ Input Options
% 0.64/1.03  
% 0.64/1.03  --out_options                           all
% 0.64/1.03  --tptp_safe_out                         true
% 0.64/1.03  --problem_path                          ""
% 0.64/1.03  --include_path                          ""
% 0.64/1.03  --clausifier                            res/vclausify_rel
% 0.64/1.03  --clausifier_options                    --mode clausify
% 0.64/1.03  --stdin                                 false
% 0.64/1.03  --stats_out                             all
% 0.64/1.03  
% 0.64/1.03  ------ General Options
% 0.64/1.03  
% 0.64/1.03  --fof                                   false
% 0.64/1.03  --time_out_real                         305.
% 0.64/1.03  --time_out_virtual                      -1.
% 0.64/1.03  --symbol_type_check                     false
% 0.64/1.03  --clausify_out                          false
% 0.64/1.03  --sig_cnt_out                           false
% 0.64/1.03  --trig_cnt_out                          false
% 0.64/1.03  --trig_cnt_out_tolerance                1.
% 0.64/1.03  --trig_cnt_out_sk_spl                   false
% 0.64/1.03  --abstr_cl_out                          false
% 0.64/1.03  
% 0.64/1.03  ------ Global Options
% 0.64/1.03  
% 0.64/1.03  --schedule                              default
% 0.64/1.03  --add_important_lit                     false
% 0.64/1.03  --prop_solver_per_cl                    1000
% 0.64/1.03  --min_unsat_core                        false
% 0.64/1.03  --soft_assumptions                      false
% 0.64/1.03  --soft_lemma_size                       3
% 0.64/1.03  --prop_impl_unit_size                   0
% 0.64/1.03  --prop_impl_unit                        []
% 0.64/1.03  --share_sel_clauses                     true
% 0.64/1.03  --reset_solvers                         false
% 0.64/1.03  --bc_imp_inh                            [conj_cone]
% 0.64/1.03  --conj_cone_tolerance                   3.
% 0.64/1.03  --extra_neg_conj                        none
% 0.64/1.03  --large_theory_mode                     true
% 0.64/1.03  --prolific_symb_bound                   200
% 0.64/1.03  --lt_threshold                          2000
% 0.64/1.03  --clause_weak_htbl                      true
% 0.64/1.03  --gc_record_bc_elim                     false
% 0.64/1.03  
% 0.64/1.03  ------ Preprocessing Options
% 0.64/1.03  
% 0.64/1.03  --preprocessing_flag                    true
% 0.64/1.03  --time_out_prep_mult                    0.1
% 0.64/1.03  --splitting_mode                        input
% 0.64/1.03  --splitting_grd                         true
% 0.64/1.03  --splitting_cvd                         false
% 0.64/1.03  --splitting_cvd_svl                     false
% 0.64/1.03  --splitting_nvd                         32
% 0.64/1.03  --sub_typing                            true
% 0.64/1.03  --prep_gs_sim                           true
% 0.64/1.03  --prep_unflatten                        true
% 0.64/1.03  --prep_res_sim                          true
% 0.64/1.03  --prep_upred                            true
% 0.64/1.03  --prep_sem_filter                       exhaustive
% 0.64/1.03  --prep_sem_filter_out                   false
% 0.64/1.03  --pred_elim                             true
% 0.64/1.03  --res_sim_input                         true
% 0.64/1.03  --eq_ax_congr_red                       true
% 0.64/1.03  --pure_diseq_elim                       true
% 0.64/1.03  --brand_transform                       false
% 0.64/1.03  --non_eq_to_eq                          false
% 0.64/1.03  --prep_def_merge                        true
% 0.64/1.03  --prep_def_merge_prop_impl              false
% 0.64/1.03  --prep_def_merge_mbd                    true
% 0.64/1.03  --prep_def_merge_tr_red                 false
% 0.64/1.03  --prep_def_merge_tr_cl                  false
% 0.64/1.03  --smt_preprocessing                     true
% 0.64/1.03  --smt_ac_axioms                         fast
% 0.64/1.03  --preprocessed_out                      false
% 0.64/1.03  --preprocessed_stats                    false
% 0.64/1.03  
% 0.64/1.03  ------ Abstraction refinement Options
% 0.64/1.03  
% 0.64/1.03  --abstr_ref                             []
% 0.64/1.03  --abstr_ref_prep                        false
% 0.64/1.03  --abstr_ref_until_sat                   false
% 0.64/1.03  --abstr_ref_sig_restrict                funpre
% 0.64/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 0.64/1.03  --abstr_ref_under                       []
% 0.64/1.03  
% 0.64/1.03  ------ SAT Options
% 0.64/1.03  
% 0.64/1.03  --sat_mode                              false
% 0.64/1.03  --sat_fm_restart_options                ""
% 0.64/1.03  --sat_gr_def                            false
% 0.64/1.03  --sat_epr_types                         true
% 0.64/1.03  --sat_non_cyclic_types                  false
% 0.64/1.03  --sat_finite_models                     false
% 0.64/1.03  --sat_fm_lemmas                         false
% 0.64/1.03  --sat_fm_prep                           false
% 0.64/1.03  --sat_fm_uc_incr                        true
% 0.64/1.03  --sat_out_model                         small
% 0.64/1.03  --sat_out_clauses                       false
% 0.64/1.03  
% 0.64/1.03  ------ QBF Options
% 0.64/1.03  
% 0.64/1.03  --qbf_mode                              false
% 0.64/1.03  --qbf_elim_univ                         false
% 0.64/1.03  --qbf_dom_inst                          none
% 0.64/1.03  --qbf_dom_pre_inst                      false
% 0.64/1.03  --qbf_sk_in                             false
% 0.64/1.03  --qbf_pred_elim                         true
% 0.64/1.03  --qbf_split                             512
% 0.64/1.03  
% 0.64/1.03  ------ BMC1 Options
% 0.64/1.03  
% 0.64/1.03  --bmc1_incremental                      false
% 0.64/1.03  --bmc1_axioms                           reachable_all
% 0.64/1.03  --bmc1_min_bound                        0
% 0.64/1.03  --bmc1_max_bound                        -1
% 0.64/1.03  --bmc1_max_bound_default                -1
% 0.64/1.03  --bmc1_symbol_reachability              true
% 0.64/1.03  --bmc1_property_lemmas                  false
% 0.64/1.03  --bmc1_k_induction                      false
% 0.64/1.03  --bmc1_non_equiv_states                 false
% 0.64/1.03  --bmc1_deadlock                         false
% 0.64/1.03  --bmc1_ucm                              false
% 0.64/1.03  --bmc1_add_unsat_core                   none
% 0.64/1.03  --bmc1_unsat_core_children              false
% 0.64/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 0.64/1.03  --bmc1_out_stat                         full
% 0.64/1.03  --bmc1_ground_init                      false
% 0.64/1.03  --bmc1_pre_inst_next_state              false
% 0.64/1.03  --bmc1_pre_inst_state                   false
% 0.64/1.03  --bmc1_pre_inst_reach_state             false
% 0.64/1.03  --bmc1_out_unsat_core                   false
% 0.64/1.03  --bmc1_aig_witness_out                  false
% 0.64/1.03  --bmc1_verbose                          false
% 0.64/1.03  --bmc1_dump_clauses_tptp                false
% 0.64/1.03  --bmc1_dump_unsat_core_tptp             false
% 0.64/1.03  --bmc1_dump_file                        -
% 0.64/1.03  --bmc1_ucm_expand_uc_limit              128
% 0.64/1.03  --bmc1_ucm_n_expand_iterations          6
% 0.64/1.03  --bmc1_ucm_extend_mode                  1
% 0.64/1.03  --bmc1_ucm_init_mode                    2
% 0.64/1.03  --bmc1_ucm_cone_mode                    none
% 0.64/1.03  --bmc1_ucm_reduced_relation_type        0
% 0.64/1.03  --bmc1_ucm_relax_model                  4
% 0.64/1.03  --bmc1_ucm_full_tr_after_sat            true
% 0.64/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 0.64/1.03  --bmc1_ucm_layered_model                none
% 0.64/1.03  --bmc1_ucm_max_lemma_size               10
% 0.64/1.03  
% 0.64/1.03  ------ AIG Options
% 0.64/1.03  
% 0.64/1.03  --aig_mode                              false
% 0.64/1.03  
% 0.64/1.03  ------ Instantiation Options
% 0.64/1.03  
% 0.64/1.03  --instantiation_flag                    true
% 0.64/1.03  --inst_sos_flag                         false
% 0.64/1.03  --inst_sos_phase                        true
% 0.64/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.64/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.64/1.03  --inst_lit_sel_side                     none
% 0.64/1.03  --inst_solver_per_active                1400
% 0.64/1.03  --inst_solver_calls_frac                1.
% 0.64/1.03  --inst_passive_queue_type               priority_queues
% 0.64/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.64/1.03  --inst_passive_queues_freq              [25;2]
% 0.64/1.03  --inst_dismatching                      true
% 0.64/1.03  --inst_eager_unprocessed_to_passive     true
% 0.64/1.03  --inst_prop_sim_given                   true
% 0.64/1.03  --inst_prop_sim_new                     false
% 0.64/1.03  --inst_subs_new                         false
% 0.64/1.03  --inst_eq_res_simp                      false
% 0.64/1.03  --inst_subs_given                       false
% 0.64/1.03  --inst_orphan_elimination               true
% 0.64/1.03  --inst_learning_loop_flag               true
% 0.64/1.03  --inst_learning_start                   3000
% 0.64/1.03  --inst_learning_factor                  2
% 0.64/1.03  --inst_start_prop_sim_after_learn       3
% 0.64/1.03  --inst_sel_renew                        solver
% 0.64/1.03  --inst_lit_activity_flag                true
% 0.64/1.03  --inst_restr_to_given                   false
% 0.64/1.03  --inst_activity_threshold               500
% 0.64/1.03  --inst_out_proof                        true
% 0.64/1.03  
% 0.64/1.03  ------ Resolution Options
% 0.64/1.03  
% 0.64/1.03  --resolution_flag                       false
% 0.64/1.03  --res_lit_sel                           adaptive
% 0.64/1.03  --res_lit_sel_side                      none
% 0.64/1.03  --res_ordering                          kbo
% 0.64/1.03  --res_to_prop_solver                    active
% 0.64/1.03  --res_prop_simpl_new                    false
% 0.64/1.03  --res_prop_simpl_given                  true
% 0.64/1.03  --res_passive_queue_type                priority_queues
% 0.64/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.64/1.03  --res_passive_queues_freq               [15;5]
% 0.64/1.03  --res_forward_subs                      full
% 0.64/1.03  --res_backward_subs                     full
% 0.64/1.03  --res_forward_subs_resolution           true
% 0.64/1.03  --res_backward_subs_resolution          true
% 0.64/1.03  --res_orphan_elimination                true
% 0.64/1.03  --res_time_limit                        2.
% 0.64/1.03  --res_out_proof                         true
% 0.64/1.03  
% 0.64/1.03  ------ Superposition Options
% 0.64/1.03  
% 0.64/1.03  --superposition_flag                    true
% 0.64/1.03  --sup_passive_queue_type                priority_queues
% 0.64/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.64/1.03  --sup_passive_queues_freq               [8;1;4]
% 0.64/1.03  --demod_completeness_check              fast
% 0.64/1.03  --demod_use_ground                      true
% 0.64/1.03  --sup_to_prop_solver                    passive
% 0.64/1.03  --sup_prop_simpl_new                    true
% 0.64/1.03  --sup_prop_simpl_given                  true
% 0.64/1.03  --sup_fun_splitting                     false
% 0.64/1.03  --sup_smt_interval                      50000
% 0.64/1.03  
% 0.64/1.03  ------ Superposition Simplification Setup
% 0.64/1.03  
% 0.64/1.03  --sup_indices_passive                   []
% 0.64/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.64/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.64/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.64/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 0.64/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.64/1.03  --sup_full_bw                           [BwDemod]
% 0.64/1.03  --sup_immed_triv                        [TrivRules]
% 0.64/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.64/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.64/1.03  --sup_immed_bw_main                     []
% 0.64/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.64/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 0.64/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.64/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.64/1.03  
% 0.64/1.03  ------ Combination Options
% 0.64/1.03  
% 0.64/1.03  --comb_res_mult                         3
% 0.64/1.03  --comb_sup_mult                         2
% 0.64/1.03  --comb_inst_mult                        10
% 0.64/1.03  
% 0.64/1.03  ------ Debug Options
% 0.64/1.03  
% 0.64/1.03  --dbg_backtrace                         false
% 0.64/1.03  --dbg_dump_prop_clauses                 false
% 0.64/1.03  --dbg_dump_prop_clauses_file            -
% 0.64/1.03  --dbg_out_stat                          false
% 0.64/1.03  
% 0.64/1.03  
% 0.64/1.03  
% 0.64/1.03  
% 0.64/1.03  ------ Proving...
% 0.64/1.03  
% 0.64/1.03  
% 0.64/1.03  % SZS status Theorem for theBenchmark.p
% 0.64/1.03  
% 0.64/1.03   Resolution empty clause
% 0.64/1.03  
% 0.64/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 0.64/1.03  
% 0.64/1.03  fof(f5,axiom,(
% 0.64/1.03    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.64/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.64/1.03  
% 0.64/1.03  fof(f20,plain,(
% 0.64/1.03    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.64/1.03    inference(ennf_transformation,[],[f5])).
% 0.64/1.03  
% 0.64/1.03  fof(f38,plain,(
% 0.64/1.03    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 0.64/1.03    inference(cnf_transformation,[],[f20])).
% 0.64/1.03  
% 0.64/1.03  fof(f13,conjecture,(
% 0.64/1.03    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.64/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.64/1.03  
% 0.64/1.03  fof(f14,negated_conjecture,(
% 0.64/1.03    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.64/1.03    inference(negated_conjecture,[],[f13])).
% 0.64/1.03  
% 0.64/1.03  fof(f15,plain,(
% 0.64/1.03    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_1(X2)) => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.64/1.03    inference(pure_predicate_removal,[],[f14])).
% 0.64/1.03  
% 0.64/1.03  fof(f16,plain,(
% 0.64/1.03    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.64/1.03    inference(pure_predicate_removal,[],[f15])).
% 0.64/1.03  
% 0.64/1.03  fof(f27,plain,(
% 0.64/1.03    ? [X0,X1,X2] : (k1_xboole_0 != k7_relset_1(k1_xboole_0,X0,X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))))),
% 0.64/1.03    inference(ennf_transformation,[],[f16])).
% 0.64/1.03  
% 0.64/1.03  fof(f30,plain,(
% 0.64/1.03    ? [X0,X1,X2] : (k1_xboole_0 != k7_relset_1(k1_xboole_0,X0,X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) => (k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))))),
% 0.64/1.03    introduced(choice_axiom,[])).
% 0.64/1.03  
% 0.64/1.03  fof(f31,plain,(
% 0.64/1.03    k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.64/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f30])).
% 0.64/1.03  
% 0.64/1.03  fof(f46,plain,(
% 0.64/1.03    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.64/1.03    inference(cnf_transformation,[],[f31])).
% 0.64/1.03  
% 0.64/1.03  fof(f3,axiom,(
% 0.64/1.03    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.64/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.64/1.03  
% 0.64/1.03  fof(f28,plain,(
% 0.64/1.03    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.64/1.03    inference(nnf_transformation,[],[f3])).
% 0.64/1.03  
% 0.64/1.03  fof(f29,plain,(
% 0.64/1.03    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.64/1.03    inference(flattening,[],[f28])).
% 0.64/1.03  
% 0.64/1.03  fof(f35,plain,(
% 0.64/1.03    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.64/1.03    inference(cnf_transformation,[],[f29])).
% 0.64/1.03  
% 0.64/1.03  fof(f49,plain,(
% 0.64/1.03    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.64/1.03    inference(equality_resolution,[],[f35])).
% 0.64/1.03  
% 0.64/1.03  fof(f34,plain,(
% 0.64/1.03    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 0.64/1.03    inference(cnf_transformation,[],[f29])).
% 0.64/1.03  
% 0.64/1.03  fof(f1,axiom,(
% 0.64/1.03    v1_xboole_0(k1_xboole_0)),
% 0.64/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.64/1.03  
% 0.64/1.03  fof(f32,plain,(
% 0.64/1.03    v1_xboole_0(k1_xboole_0)),
% 0.64/1.03    inference(cnf_transformation,[],[f1])).
% 0.64/1.03  
% 0.64/1.03  fof(f2,axiom,(
% 0.64/1.03    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.64/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.64/1.03  
% 0.64/1.03  fof(f19,plain,(
% 0.64/1.03    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.64/1.03    inference(ennf_transformation,[],[f2])).
% 0.64/1.03  
% 0.64/1.03  fof(f33,plain,(
% 0.64/1.03    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.64/1.03    inference(cnf_transformation,[],[f19])).
% 0.64/1.03  
% 0.64/1.03  fof(f10,axiom,(
% 0.64/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.64/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.64/1.03  
% 0.64/1.03  fof(f24,plain,(
% 0.64/1.03    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.64/1.03    inference(ennf_transformation,[],[f10])).
% 0.64/1.03  
% 0.64/1.03  fof(f43,plain,(
% 0.64/1.03    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.64/1.03    inference(cnf_transformation,[],[f24])).
% 0.64/1.03  
% 0.64/1.03  fof(f7,axiom,(
% 0.64/1.03    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.64/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.64/1.03  
% 0.64/1.03  fof(f21,plain,(
% 0.64/1.03    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.64/1.03    inference(ennf_transformation,[],[f7])).
% 0.64/1.03  
% 0.64/1.03  fof(f39,plain,(
% 0.64/1.03    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.64/1.03    inference(cnf_transformation,[],[f21])).
% 0.64/1.03  
% 0.64/1.03  fof(f9,axiom,(
% 0.64/1.03    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.64/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.64/1.03  
% 0.64/1.03  fof(f42,plain,(
% 0.64/1.03    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.64/1.03    inference(cnf_transformation,[],[f9])).
% 0.64/1.03  
% 0.64/1.03  fof(f4,axiom,(
% 0.64/1.03    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.64/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.64/1.03  
% 0.64/1.03  fof(f37,plain,(
% 0.64/1.03    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.64/1.03    inference(cnf_transformation,[],[f4])).
% 0.64/1.03  
% 0.64/1.03  fof(f11,axiom,(
% 0.64/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.64/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.64/1.03  
% 0.64/1.03  fof(f17,plain,(
% 0.64/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.64/1.03    inference(pure_predicate_removal,[],[f11])).
% 0.64/1.03  
% 0.64/1.03  fof(f25,plain,(
% 0.64/1.03    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.64/1.03    inference(ennf_transformation,[],[f17])).
% 0.64/1.03  
% 0.64/1.03  fof(f44,plain,(
% 0.64/1.03    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.64/1.03    inference(cnf_transformation,[],[f25])).
% 0.64/1.03  
% 0.64/1.03  fof(f8,axiom,(
% 0.64/1.03    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.64/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.64/1.03  
% 0.64/1.03  fof(f22,plain,(
% 0.64/1.03    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.64/1.03    inference(ennf_transformation,[],[f8])).
% 0.64/1.03  
% 0.64/1.03  fof(f23,plain,(
% 0.64/1.03    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.64/1.03    inference(flattening,[],[f22])).
% 0.64/1.03  
% 0.64/1.03  fof(f40,plain,(
% 0.64/1.03    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.64/1.03    inference(cnf_transformation,[],[f23])).
% 0.64/1.03  
% 0.64/1.03  fof(f12,axiom,(
% 0.64/1.03    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 0.64/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.64/1.03  
% 0.64/1.03  fof(f26,plain,(
% 0.64/1.03    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.64/1.03    inference(ennf_transformation,[],[f12])).
% 0.64/1.03  
% 0.64/1.03  fof(f45,plain,(
% 0.64/1.03    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.64/1.03    inference(cnf_transformation,[],[f26])).
% 0.64/1.03  
% 0.64/1.03  fof(f47,plain,(
% 0.64/1.03    k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1)),
% 0.64/1.03    inference(cnf_transformation,[],[f31])).
% 0.64/1.03  
% 0.64/1.03  cnf(c_6,plain,
% 0.64/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 0.64/1.03      | ~ v1_xboole_0(X1)
% 0.64/1.03      | v1_xboole_0(X0) ),
% 0.64/1.03      inference(cnf_transformation,[],[f38]) ).
% 0.64/1.03  
% 0.64/1.03  cnf(c_15,negated_conjecture,
% 0.64/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
% 0.64/1.03      inference(cnf_transformation,[],[f46]) ).
% 0.64/1.03  
% 0.64/1.03  cnf(c_192,plain,
% 0.64/1.03      ( ~ v1_xboole_0(X0)
% 0.64/1.03      | v1_xboole_0(X1)
% 0.64/1.03      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)) != k1_zfmisc_1(X0)
% 0.64/1.03      | sK2 != X1 ),
% 0.64/1.03      inference(resolution_lifted,[status(thm)],[c_6,c_15]) ).
% 0.64/1.03  
% 0.64/1.03  cnf(c_193,plain,
% 0.64/1.03      ( ~ v1_xboole_0(X0)
% 0.64/1.03      | v1_xboole_0(sK2)
% 0.64/1.03      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)) != k1_zfmisc_1(X0) ),
% 0.64/1.03      inference(unflattening,[status(thm)],[c_192]) ).
% 0.64/1.03  
% 0.64/1.03  cnf(c_419,plain,
% 0.64/1.03      ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)) != k1_zfmisc_1(X0)
% 0.64/1.03      | v1_xboole_0(X0) != iProver_top
% 0.64/1.03      | v1_xboole_0(sK2) = iProver_top ),
% 0.64/1.03      inference(predicate_to_equality,[status(thm)],[c_193]) ).
% 0.64/1.03  
% 0.64/1.03  cnf(c_3,plain,
% 0.64/1.03      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 0.64/1.03      inference(cnf_transformation,[],[f49]) ).
% 0.64/1.03  
% 0.64/1.03  cnf(c_472,plain,
% 0.64/1.03      ( k1_zfmisc_1(X0) != k1_zfmisc_1(k1_xboole_0)
% 0.64/1.03      | v1_xboole_0(X0) != iProver_top
% 0.64/1.03      | v1_xboole_0(sK2) = iProver_top ),
% 0.64/1.03      inference(demodulation,[status(thm)],[c_419,c_3]) ).
% 0.64/1.03  
% 0.64/1.03  cnf(c_4,plain,
% 0.64/1.03      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 0.64/1.03      | k1_xboole_0 = X0
% 0.64/1.03      | k1_xboole_0 = X1 ),
% 0.64/1.03      inference(cnf_transformation,[],[f34]) ).
% 0.64/1.03  
% 0.64/1.03  cnf(c_36,plain,
% 0.64/1.03      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 0.64/1.03      | k1_xboole_0 = k1_xboole_0 ),
% 0.64/1.03      inference(instantiation,[status(thm)],[c_4]) ).
% 0.64/1.03  
% 0.64/1.03  cnf(c_37,plain,
% 0.64/1.03      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 0.64/1.03      inference(instantiation,[status(thm)],[c_3]) ).
% 0.64/1.03  
% 0.64/1.03  cnf(c_0,plain,
% 0.64/1.03      ( v1_xboole_0(k1_xboole_0) ),
% 0.64/1.03      inference(cnf_transformation,[],[f32]) ).
% 0.64/1.03  
% 0.64/1.03  cnf(c_41,plain,
% 0.64/1.03      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 0.64/1.03      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 0.64/1.03  
% 0.64/1.03  cnf(c_282,plain,
% 0.64/1.03      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 0.64/1.03      theory(equality) ).
% 0.64/1.03  
% 0.64/1.03  cnf(c_291,plain,
% 0.64/1.03      ( k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0)
% 0.64/1.03      | k1_xboole_0 != k1_xboole_0 ),
% 0.64/1.03      inference(instantiation,[status(thm)],[c_282]) ).
% 0.64/1.03  
% 0.64/1.03  cnf(c_485,plain,
% 0.64/1.03      ( k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0)
% 0.64/1.03      | v1_xboole_0(sK2) = iProver_top
% 0.64/1.03      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 0.64/1.03      inference(instantiation,[status(thm)],[c_472]) ).
% 0.64/1.03  
% 0.64/1.03  cnf(c_554,plain,
% 0.64/1.03      ( v1_xboole_0(sK2) = iProver_top ),
% 0.64/1.03      inference(global_propositional_subsumption,
% 0.64/1.03                [status(thm)],
% 0.64/1.03                [c_472,c_36,c_37,c_41,c_291,c_485]) ).
% 0.64/1.03  
% 0.64/1.03  cnf(c_1,plain,
% 0.64/1.03      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 0.64/1.03      inference(cnf_transformation,[],[f33]) ).
% 0.64/1.03  
% 0.64/1.03  cnf(c_422,plain,
% 0.64/1.03      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 0.64/1.03      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 0.64/1.03  
% 0.64/1.03  cnf(c_867,plain,
% 0.64/1.03      ( sK2 = k1_xboole_0 ),
% 0.64/1.03      inference(superposition,[status(thm)],[c_554,c_422]) ).
% 0.64/1.03  
% 0.64/1.03  cnf(c_11,plain,
% 0.64/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 0.64/1.03      inference(cnf_transformation,[],[f43]) ).
% 0.64/1.03  
% 0.64/1.03  cnf(c_225,plain,
% 0.64/1.03      ( v1_relat_1(X0)
% 0.64/1.03      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))
% 0.64/1.03      | sK2 != X0 ),
% 0.64/1.03      inference(resolution_lifted,[status(thm)],[c_11,c_15]) ).
% 0.64/1.03  
% 0.64/1.03  cnf(c_226,plain,
% 0.64/1.03      ( v1_relat_1(sK2)
% 0.64/1.03      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)) ),
% 0.64/1.03      inference(unflattening,[status(thm)],[c_225]) ).
% 0.64/1.03  
% 0.64/1.03  cnf(c_418,plain,
% 0.64/1.03      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))
% 0.64/1.03      | v1_relat_1(sK2) = iProver_top ),
% 0.64/1.03      inference(predicate_to_equality,[status(thm)],[c_226]) ).
% 0.64/1.03  
% 0.64/1.03  cnf(c_458,plain,
% 0.64/1.03      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k1_xboole_0)
% 0.64/1.03      | v1_relat_1(sK2) = iProver_top ),
% 0.64/1.03      inference(demodulation,[status(thm)],[c_418,c_3]) ).
% 0.64/1.03  
% 0.64/1.03  cnf(c_278,plain,( X0 = X0 ),theory(equality) ).
% 0.64/1.03  
% 0.64/1.03  cnf(c_510,plain,
% 0.64/1.03      ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)) ),
% 0.64/1.03      inference(instantiation,[status(thm)],[c_278]) ).
% 0.64/1.03  
% 0.64/1.03  cnf(c_513,plain,
% 0.64/1.03      ( v1_relat_1(sK2)
% 0.64/1.03      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)) ),
% 0.64/1.03      inference(instantiation,[status(thm)],[c_226]) ).
% 0.64/1.03  
% 0.64/1.03  cnf(c_514,plain,
% 0.64/1.03      ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))
% 0.64/1.03      | v1_relat_1(sK2) = iProver_top ),
% 0.64/1.03      inference(predicate_to_equality,[status(thm)],[c_513]) ).
% 0.64/1.03  
% 0.64/1.03  cnf(c_533,plain,
% 0.64/1.03      ( v1_relat_1(sK2) = iProver_top ),
% 0.64/1.03      inference(global_propositional_subsumption,
% 0.64/1.03                [status(thm)],
% 0.64/1.03                [c_458,c_510,c_514]) ).
% 0.64/1.03  
% 0.64/1.03  cnf(c_936,plain,
% 0.64/1.03      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 0.64/1.03      inference(demodulation,[status(thm)],[c_867,c_533]) ).
% 0.64/1.03  
% 0.64/1.03  cnf(c_7,plain,
% 0.64/1.03      ( ~ v1_relat_1(X0) | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 0.64/1.03      inference(cnf_transformation,[],[f39]) ).
% 0.64/1.03  
% 0.64/1.03  cnf(c_421,plain,
% 0.64/1.03      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 0.64/1.03      | v1_relat_1(X0) != iProver_top ),
% 0.64/1.03      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 0.64/1.03  
% 0.64/1.03  cnf(c_1171,plain,
% 0.64/1.03      ( k2_relat_1(k7_relat_1(k1_xboole_0,X0)) = k9_relat_1(k1_xboole_0,X0) ),
% 0.64/1.03      inference(superposition,[status(thm)],[c_936,c_421]) ).
% 0.64/1.03  
% 0.64/1.03  cnf(c_9,plain,
% 0.64/1.03      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 0.64/1.03      inference(cnf_transformation,[],[f42]) ).
% 0.64/1.03  
% 0.64/1.03  cnf(c_5,plain,
% 0.64/1.03      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 0.64/1.03      inference(cnf_transformation,[],[f37]) ).
% 0.64/1.03  
% 0.64/1.03  cnf(c_12,plain,
% 0.64/1.03      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 0.64/1.03      inference(cnf_transformation,[],[f44]) ).
% 0.64/1.03  
% 0.64/1.03  cnf(c_8,plain,
% 0.64/1.03      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 0.64/1.03      inference(cnf_transformation,[],[f40]) ).
% 0.64/1.03  
% 0.64/1.03  cnf(c_127,plain,
% 0.64/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.64/1.03      | ~ v1_relat_1(X0)
% 0.64/1.03      | k7_relat_1(X0,X1) = X0 ),
% 0.64/1.03      inference(resolution,[status(thm)],[c_12,c_8]) ).
% 0.64/1.03  
% 0.64/1.03  cnf(c_131,plain,
% 0.64/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.64/1.03      | k7_relat_1(X0,X1) = X0 ),
% 0.64/1.03      inference(global_propositional_subsumption,
% 0.64/1.03                [status(thm)],
% 0.64/1.03                [c_127,c_12,c_11,c_8]) ).
% 0.64/1.03  
% 0.64/1.03  cnf(c_162,plain,
% 0.64/1.03      ( k7_relat_1(X0,X1) = X0
% 0.64/1.03      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(X3)
% 0.64/1.03      | k1_xboole_0 != X0 ),
% 0.64/1.03      inference(resolution_lifted,[status(thm)],[c_5,c_131]) ).
% 0.64/1.03  
% 0.64/1.03  cnf(c_163,plain,
% 0.64/1.03      ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0
% 0.64/1.03      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(X2) ),
% 0.64/1.03      inference(unflattening,[status(thm)],[c_162]) ).
% 0.64/1.03  
% 0.64/1.03  cnf(c_608,plain,
% 0.64/1.03      ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 0.64/1.03      inference(equality_resolution,[status(thm)],[c_163]) ).
% 0.64/1.03  
% 0.64/1.03  cnf(c_1172,plain,
% 0.64/1.03      ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 0.64/1.03      inference(light_normalisation,[status(thm)],[c_1171,c_9,c_608]) ).
% 0.64/1.03  
% 0.64/1.03  cnf(c_13,plain,
% 0.64/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.64/1.03      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 0.64/1.03      inference(cnf_transformation,[],[f45]) ).
% 0.64/1.03  
% 0.64/1.03  cnf(c_216,plain,
% 0.64/1.03      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 0.64/1.03      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))
% 0.64/1.03      | sK2 != X2 ),
% 0.64/1.03      inference(resolution_lifted,[status(thm)],[c_13,c_15]) ).
% 0.64/1.03  
% 0.64/1.03  cnf(c_217,plain,
% 0.64/1.03      ( k7_relset_1(X0,X1,sK2,X2) = k9_relat_1(sK2,X2)
% 0.64/1.03      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)) ),
% 0.64/1.03      inference(unflattening,[status(thm)],[c_216]) ).
% 0.64/1.03  
% 0.64/1.03  cnf(c_479,plain,
% 0.64/1.03      ( k7_relset_1(X0,X1,sK2,X2) = k9_relat_1(sK2,X2)
% 0.64/1.03      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k1_xboole_0) ),
% 0.64/1.03      inference(demodulation,[status(thm)],[c_217,c_3]) ).
% 0.64/1.03  
% 0.64/1.03  cnf(c_673,plain,
% 0.64/1.03      ( k7_relset_1(k1_xboole_0,X0,sK2,X1) = k9_relat_1(sK2,X1) ),
% 0.64/1.03      inference(superposition,[status(thm)],[c_3,c_479]) ).
% 0.64/1.03  
% 0.64/1.03  cnf(c_14,negated_conjecture,
% 0.64/1.03      ( k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1) ),
% 0.64/1.03      inference(cnf_transformation,[],[f47]) ).
% 0.64/1.03  
% 0.64/1.03  cnf(c_792,plain,
% 0.64/1.03      ( k9_relat_1(sK2,sK1) != k1_xboole_0 ),
% 0.64/1.03      inference(demodulation,[status(thm)],[c_673,c_14]) ).
% 0.64/1.03  
% 0.64/1.03  cnf(c_931,plain,
% 0.64/1.03      ( k9_relat_1(k1_xboole_0,sK1) != k1_xboole_0 ),
% 0.64/1.03      inference(demodulation,[status(thm)],[c_867,c_792]) ).
% 0.64/1.03  
% 0.64/1.03  cnf(c_1205,plain,
% 0.64/1.03      ( k1_xboole_0 != k1_xboole_0 ),
% 0.64/1.03      inference(demodulation,[status(thm)],[c_1172,c_931]) ).
% 0.64/1.03  
% 0.64/1.03  cnf(c_1206,plain,
% 0.64/1.03      ( $false ),
% 0.64/1.03      inference(equality_resolution_simp,[status(thm)],[c_1205]) ).
% 0.64/1.03  
% 0.64/1.03  
% 0.64/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 0.64/1.03  
% 0.64/1.03  ------                               Statistics
% 0.64/1.03  
% 0.64/1.03  ------ General
% 0.64/1.03  
% 0.64/1.03  abstr_ref_over_cycles:                  0
% 0.64/1.03  abstr_ref_under_cycles:                 0
% 0.64/1.03  gc_basic_clause_elim:                   0
% 0.64/1.03  forced_gc_time:                         0
% 0.64/1.03  parsing_time:                           0.006
% 0.64/1.03  unif_index_cands_time:                  0.
% 0.64/1.03  unif_index_add_time:                    0.
% 0.64/1.03  orderings_time:                         0.
% 0.64/1.03  out_proof_time:                         0.006
% 0.64/1.03  total_time:                             0.055
% 0.64/1.03  num_of_symbols:                         46
% 0.64/1.03  num_of_terms:                           1272
% 0.64/1.03  
% 0.64/1.03  ------ Preprocessing
% 0.64/1.03  
% 0.64/1.03  num_of_splits:                          0
% 0.64/1.03  num_of_split_atoms:                     0
% 0.64/1.03  num_of_reused_defs:                     0
% 0.64/1.03  num_eq_ax_congr_red:                    9
% 0.64/1.03  num_of_sem_filtered_clauses:            1
% 0.64/1.03  num_of_subtypes:                        0
% 0.64/1.03  monotx_restored_types:                  0
% 0.64/1.03  sat_num_of_epr_types:                   0
% 0.64/1.03  sat_num_of_non_cyclic_types:            0
% 0.64/1.03  sat_guarded_non_collapsed_types:        0
% 0.64/1.03  num_pure_diseq_elim:                    0
% 0.64/1.03  simp_replaced_by:                       0
% 0.64/1.03  res_preprocessed:                       71
% 0.64/1.03  prep_upred:                             0
% 0.64/1.03  prep_unflattend:                        10
% 0.64/1.03  smt_new_axioms:                         0
% 0.64/1.03  pred_elim_cands:                        4
% 0.64/1.03  pred_elim:                              2
% 0.64/1.03  pred_elim_cl:                           0
% 0.64/1.03  pred_elim_cycles:                       4
% 0.64/1.03  merged_defs:                            0
% 0.64/1.03  merged_defs_ncl:                        0
% 0.64/1.03  bin_hyper_res:                          0
% 0.64/1.03  prep_cycles:                            3
% 0.64/1.03  pred_elim_time:                         0.002
% 0.64/1.03  splitting_time:                         0.
% 0.64/1.03  sem_filter_time:                        0.
% 0.64/1.03  monotx_time:                            0.
% 0.64/1.03  subtype_inf_time:                       0.
% 0.64/1.03  
% 0.64/1.03  ------ Problem properties
% 0.64/1.03  
% 0.64/1.03  clauses:                                16
% 0.64/1.03  conjectures:                            1
% 0.64/1.03  epr:                                    2
% 0.64/1.03  horn:                                   15
% 0.64/1.03  ground:                                 4
% 0.64/1.03  unary:                                  6
% 0.64/1.03  binary:                                 8
% 0.64/1.03  lits:                                   28
% 0.64/1.03  lits_eq:                                21
% 0.64/1.03  fd_pure:                                0
% 0.64/1.03  fd_pseudo:                              0
% 0.64/1.03  fd_cond:                                2
% 0.64/1.03  fd_pseudo_cond:                         0
% 0.64/1.03  ac_symbols:                             0
% 0.64/1.03  
% 0.64/1.03  ------ Propositional Solver
% 0.64/1.03  
% 0.64/1.03  prop_solver_calls:                      25
% 0.64/1.03  prop_fast_solver_calls:                 347
% 0.64/1.03  smt_solver_calls:                       0
% 0.64/1.03  smt_fast_solver_calls:                  0
% 0.64/1.03  prop_num_of_clauses:                    477
% 0.64/1.03  prop_preprocess_simplified:             2066
% 0.64/1.03  prop_fo_subsumed:                       4
% 0.64/1.03  prop_solver_time:                       0.
% 0.64/1.03  smt_solver_time:                        0.
% 0.64/1.03  smt_fast_solver_time:                   0.
% 0.64/1.03  prop_fast_solver_time:                  0.
% 0.64/1.03  prop_unsat_core_time:                   0.
% 0.64/1.03  
% 0.64/1.03  ------ QBF
% 0.64/1.03  
% 0.64/1.03  qbf_q_res:                              0
% 0.64/1.03  qbf_num_tautologies:                    0
% 0.64/1.03  qbf_prep_cycles:                        0
% 0.64/1.03  
% 0.64/1.03  ------ BMC1
% 0.64/1.03  
% 0.64/1.03  bmc1_current_bound:                     -1
% 0.64/1.03  bmc1_last_solved_bound:                 -1
% 0.64/1.03  bmc1_unsat_core_size:                   -1
% 0.64/1.03  bmc1_unsat_core_parents_size:           -1
% 0.64/1.03  bmc1_merge_next_fun:                    0
% 0.64/1.03  bmc1_unsat_core_clauses_time:           0.
% 0.64/1.03  
% 0.64/1.03  ------ Instantiation
% 0.64/1.03  
% 0.64/1.03  inst_num_of_clauses:                    245
% 0.64/1.03  inst_num_in_passive:                    115
% 0.64/1.03  inst_num_in_active:                     126
% 0.64/1.03  inst_num_in_unprocessed:                4
% 0.64/1.03  inst_num_of_loops:                      140
% 0.64/1.03  inst_num_of_learning_restarts:          0
% 0.64/1.03  inst_num_moves_active_passive:          10
% 0.64/1.03  inst_lit_activity:                      0
% 0.64/1.03  inst_lit_activity_moves:                0
% 0.64/1.03  inst_num_tautologies:                   0
% 0.64/1.03  inst_num_prop_implied:                  0
% 0.64/1.03  inst_num_existing_simplified:           0
% 0.64/1.03  inst_num_eq_res_simplified:             0
% 0.64/1.03  inst_num_child_elim:                    0
% 0.64/1.03  inst_num_of_dismatching_blockings:      17
% 0.64/1.03  inst_num_of_non_proper_insts:           171
% 0.64/1.03  inst_num_of_duplicates:                 0
% 0.64/1.03  inst_inst_num_from_inst_to_res:         0
% 0.64/1.03  inst_dismatching_checking_time:         0.
% 0.64/1.03  
% 0.64/1.03  ------ Resolution
% 0.64/1.03  
% 0.64/1.03  res_num_of_clauses:                     0
% 0.64/1.03  res_num_in_passive:                     0
% 0.64/1.03  res_num_in_active:                      0
% 0.64/1.03  res_num_of_loops:                       74
% 0.64/1.03  res_forward_subset_subsumed:            16
% 0.64/1.03  res_backward_subset_subsumed:           0
% 0.64/1.03  res_forward_subsumed:                   0
% 0.64/1.03  res_backward_subsumed:                  0
% 0.64/1.03  res_forward_subsumption_resolution:     0
% 0.64/1.03  res_backward_subsumption_resolution:    0
% 0.64/1.03  res_clause_to_clause_subsumption:       33
% 0.64/1.03  res_orphan_elimination:                 0
% 0.64/1.03  res_tautology_del:                      22
% 0.64/1.03  res_num_eq_res_simplified:              0
% 0.64/1.03  res_num_sel_changes:                    0
% 0.64/1.03  res_moves_from_active_to_pass:          0
% 0.64/1.03  
% 0.64/1.03  ------ Superposition
% 0.64/1.03  
% 0.64/1.03  sup_time_total:                         0.
% 0.64/1.03  sup_time_generating:                    0.
% 0.64/1.03  sup_time_sim_full:                      0.
% 0.64/1.03  sup_time_sim_immed:                     0.
% 0.64/1.03  
% 0.64/1.03  sup_num_of_clauses:                     15
% 0.64/1.03  sup_num_in_active:                      11
% 0.64/1.03  sup_num_in_passive:                     4
% 0.64/1.03  sup_num_of_loops:                       26
% 0.64/1.03  sup_fw_superposition:                   8
% 0.64/1.03  sup_bw_superposition:                   4
% 0.64/1.03  sup_immediate_simplified:               5
% 0.64/1.03  sup_given_eliminated:                   0
% 0.64/1.03  comparisons_done:                       0
% 0.64/1.03  comparisons_avoided:                    0
% 0.64/1.03  
% 0.64/1.03  ------ Simplifications
% 0.64/1.03  
% 0.64/1.03  
% 0.64/1.03  sim_fw_subset_subsumed:                 2
% 0.64/1.03  sim_bw_subset_subsumed:                 6
% 0.64/1.03  sim_fw_subsumed:                        0
% 0.64/1.03  sim_bw_subsumed:                        0
% 0.64/1.03  sim_fw_subsumption_res:                 0
% 0.64/1.03  sim_bw_subsumption_res:                 0
% 0.64/1.03  sim_tautology_del:                      0
% 0.64/1.03  sim_eq_tautology_del:                   2
% 0.64/1.03  sim_eq_res_simp:                        0
% 0.64/1.03  sim_fw_demodulated:                     4
% 0.64/1.03  sim_bw_demodulated:                     11
% 0.64/1.03  sim_light_normalised:                   1
% 0.64/1.03  sim_joinable_taut:                      0
% 0.64/1.03  sim_joinable_simp:                      0
% 0.64/1.03  sim_ac_normalised:                      0
% 0.64/1.03  sim_smt_subsumption:                    0
% 0.64/1.03  
%------------------------------------------------------------------------------
