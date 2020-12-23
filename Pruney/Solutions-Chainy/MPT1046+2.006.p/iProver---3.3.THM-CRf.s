%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:08:51 EST 2020

% Result     : Theorem 1.02s
% Output     : CNFRefutation 1.02s
% Verified   : 
% Statistics : Number of formulae       :  103 (1081 expanded)
%              Number of clauses        :   69 ( 334 expanded)
%              Number of leaves         :   11 ( 226 expanded)
%              Depth                    :   19
%              Number of atoms          :  291 (3638 expanded)
%              Number of equality atoms :  139 (1168 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => v1_partfun1(k3_partfun1(X2,X0,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(k3_partfun1(X2,X0,X1),X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(k3_partfun1(X2,X0,X1),X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f8])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(k3_partfun1(X2,X0,X1),X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_tarski(X1) = k5_partfun1(X0,X0,k3_partfun1(X1,X0,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => k1_tarski(X1) = k5_partfun1(X0,X0,k3_partfun1(X1,X0,X0)) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f14,plain,(
    ? [X0,X1] :
      ( k1_tarski(X1) != k5_partfun1(X0,X0,k3_partfun1(X1,X0,X0))
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f15,plain,(
    ? [X0,X1] :
      ( k1_tarski(X1) != k5_partfun1(X0,X0,k3_partfun1(X1,X0,X0))
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f17,plain,
    ( ? [X0,X1] :
        ( k1_tarski(X1) != k5_partfun1(X0,X0,k3_partfun1(X1,X0,X0))
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( k1_tarski(sK1) != k5_partfun1(sK0,sK0,k3_partfun1(sK1,sK0,sK0))
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( k1_tarski(sK1) != k5_partfun1(sK0,sK0,k3_partfun1(sK1,sK0,sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f17])).

fof(f27,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f26,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f28,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k3_partfun1(X2,X0,X1) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k3_partfun1(X2,X0,X1) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k3_partfun1(X2,X0,X1) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( k3_partfun1(X2,X0,X1) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( v1_partfun1(X2,X0)
      <=> k1_tarski(X2) = k5_partfun1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( v1_partfun1(X2,X0)
      <=> k1_tarski(X2) = k5_partfun1(X0,X1,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( v1_partfun1(X2,X0)
      <=> k1_tarski(X2) = k5_partfun1(X0,X1,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_partfun1(X2,X0)
          | k1_tarski(X2) != k5_partfun1(X0,X1,X2) )
        & ( k1_tarski(X2) = k5_partfun1(X0,X1,X2)
          | ~ v1_partfun1(X2,X0) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X2) = k5_partfun1(X0,X1,X2)
      | ~ v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f30,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f19,f20])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k1_enumset1(X2,X2,X2) = k5_partfun1(X0,X1,X2)
      | ~ v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(definition_unfolding,[],[f23,f30])).

fof(f29,plain,(
    k1_tarski(sK1) != k5_partfun1(sK0,sK0,k3_partfun1(sK1,sK0,sK0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f33,plain,(
    k1_enumset1(sK1,sK1,sK1) != k5_partfun1(sK0,sK0,k3_partfun1(sK1,sK0,sK0)) ),
    inference(definition_unfolding,[],[f29,f30])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(k3_partfun1(X2,X0,X1),X0)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f34,plain,(
    ! [X2,X1] :
      ( v1_partfun1(k3_partfun1(X2,k1_xboole_0,X1),k1_xboole_0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f22])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_tarski(X2) != k5_partfun1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_enumset1(X2,X2,X2) != k5_partfun1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(definition_unfolding,[],[f24,f30])).

cnf(c_1,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_partfun1(k3_partfun1(X0,X1,X2),X1)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f21])).

cnf(c_7,negated_conjecture,
    ( v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_112,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_partfun1(k3_partfun1(X0,X1,X2),X1)
    | ~ v1_funct_1(X0)
    | sK0 != X1
    | sK0 != X2
    | sK1 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_7])).

cnf(c_113,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v1_partfun1(k3_partfun1(sK1,sK0,sK0),sK0)
    | ~ v1_funct_1(sK1)
    | k1_xboole_0 = sK0 ),
    inference(unflattening,[status(thm)],[c_112])).

cnf(c_8,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_6,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_115,plain,
    ( v1_partfun1(k3_partfun1(sK1,sK0,sK0),sK0)
    | k1_xboole_0 = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_113,c_8,c_6])).

cnf(c_515,plain,
    ( v1_partfun1(k3_partfun1(sK1,sK0,sK0),sK0)
    | k1_xboole_0 = sK0 ),
    inference(subtyping,[status(esa)],[c_115])).

cnf(c_670,plain,
    ( k1_xboole_0 = sK0
    | v1_partfun1(k3_partfun1(sK1,sK0,sK0),sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_515])).

cnf(c_520,plain,
    ( X0_40 = X0_40 ),
    theory(equality)).

cnf(c_543,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_520])).

cnf(c_523,plain,
    ( X0_43 = X0_43 ),
    theory(equality)).

cnf(c_546,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_523])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k3_partfun1(X0,X1,X2) = X0 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_133,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k3_partfun1(X0,X1,X2) = X0
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_8])).

cnf(c_134,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k3_partfun1(sK1,X0,X1) = sK1 ),
    inference(unflattening,[status(thm)],[c_133])).

cnf(c_514,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0_43,X1_43)))
    | k3_partfun1(sK1,X0_43,X1_43) = sK1 ),
    inference(subtyping,[status(esa)],[c_134])).

cnf(c_552,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k3_partfun1(sK1,sK0,sK0) = sK1 ),
    inference(instantiation,[status(thm)],[c_514])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_partfun1(X0,X1)
    | ~ v1_funct_1(X0)
    | k5_partfun1(X1,X2,X0) = k1_enumset1(X0,X0,X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_145,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_partfun1(X0,X1)
    | k5_partfun1(X1,X2,X0) = k1_enumset1(X0,X0,X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_8])).

cnf(c_146,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_partfun1(sK1,X0)
    | k5_partfun1(X0,X1,sK1) = k1_enumset1(sK1,sK1,sK1) ),
    inference(unflattening,[status(thm)],[c_145])).

cnf(c_513,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0_43,X1_43)))
    | ~ v1_partfun1(sK1,X0_43)
    | k5_partfun1(X0_43,X1_43,sK1) = k1_enumset1(sK1,sK1,sK1) ),
    inference(subtyping,[status(esa)],[c_146])).

cnf(c_555,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_partfun1(sK1,sK0)
    | k5_partfun1(sK0,sK0,sK1) = k1_enumset1(sK1,sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_513])).

cnf(c_529,plain,
    ( ~ v1_partfun1(X0_40,X0_43)
    | v1_partfun1(X1_40,X1_43)
    | X1_43 != X0_43
    | X1_40 != X0_40 ),
    theory(equality)).

cnf(c_727,plain,
    ( v1_partfun1(X0_40,X0_43)
    | ~ v1_partfun1(k3_partfun1(sK1,sK0,sK0),sK0)
    | X0_43 != sK0
    | X0_40 != k3_partfun1(sK1,sK0,sK0) ),
    inference(instantiation,[status(thm)],[c_529])).

cnf(c_729,plain,
    ( ~ v1_partfun1(k3_partfun1(sK1,sK0,sK0),sK0)
    | v1_partfun1(sK1,sK0)
    | sK0 != sK0
    | sK1 != k3_partfun1(sK1,sK0,sK0) ),
    inference(instantiation,[status(thm)],[c_727])).

cnf(c_517,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_668,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_517])).

cnf(c_671,plain,
    ( k3_partfun1(sK1,X0_43,X1_43) = sK1
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0_43,X1_43))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_514])).

cnf(c_740,plain,
    ( k3_partfun1(sK1,sK0,sK0) = sK1 ),
    inference(superposition,[status(thm)],[c_668,c_671])).

cnf(c_5,negated_conjecture,
    ( k1_enumset1(sK1,sK1,sK1) != k5_partfun1(sK0,sK0,k3_partfun1(sK1,sK0,sK0)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_518,negated_conjecture,
    ( k1_enumset1(sK1,sK1,sK1) != k5_partfun1(sK0,sK0,k3_partfun1(sK1,sK0,sK0)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_742,plain,
    ( k5_partfun1(sK0,sK0,sK1) != k1_enumset1(sK1,sK1,sK1) ),
    inference(demodulation,[status(thm)],[c_740,c_518])).

cnf(c_525,plain,
    ( X0_40 != X1_40
    | X2_40 != X1_40
    | X2_40 = X0_40 ),
    theory(equality)).

cnf(c_769,plain,
    ( X0_40 != X1_40
    | X0_40 = k3_partfun1(sK1,sK0,sK0)
    | k3_partfun1(sK1,sK0,sK0) != X1_40 ),
    inference(instantiation,[status(thm)],[c_525])).

cnf(c_770,plain,
    ( k3_partfun1(sK1,sK0,sK0) != sK1
    | sK1 = k3_partfun1(sK1,sK0,sK0)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_769])).

cnf(c_833,plain,
    ( k1_xboole_0 = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_670,c_6,c_543,c_546,c_515,c_552,c_555,c_729,c_742,c_770])).

cnf(c_672,plain,
    ( k5_partfun1(X0_43,X1_43,sK1) = k1_enumset1(sK1,sK1,sK1)
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0_43,X1_43))) != iProver_top
    | v1_partfun1(sK1,X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_513])).

cnf(c_813,plain,
    ( k5_partfun1(sK0,sK0,sK1) = k1_enumset1(sK1,sK1,sK1)
    | v1_partfun1(sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_668,c_672])).

cnf(c_11,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_554,plain,
    ( k5_partfun1(X0_43,X1_43,sK1) = k1_enumset1(sK1,sK1,sK1)
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0_43,X1_43))) != iProver_top
    | v1_partfun1(sK1,X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_513])).

cnf(c_556,plain,
    ( k5_partfun1(sK0,sK0,sK1) = k1_enumset1(sK1,sK1,sK1)
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_partfun1(sK1,sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_554])).

cnf(c_816,plain,
    ( v1_partfun1(sK1,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_813,c_11,c_556,c_742])).

cnf(c_836,plain,
    ( v1_partfun1(sK1,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_833,c_816])).

cnf(c_0,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | v1_partfun1(k3_partfun1(X0,k1_xboole_0,X1),k1_xboole_0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_95,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | v1_partfun1(k3_partfun1(X0,k1_xboole_0,X1),k1_xboole_0)
    | ~ v1_funct_1(X0)
    | sK0 != X1
    | sK0 != k1_xboole_0
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_7])).

cnf(c_96,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | v1_partfun1(k3_partfun1(sK1,k1_xboole_0,sK0),k1_xboole_0)
    | ~ v1_funct_1(sK1)
    | sK0 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_95])).

cnf(c_98,plain,
    ( v1_partfun1(k3_partfun1(sK1,k1_xboole_0,sK0),k1_xboole_0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | sK0 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_96,c_8])).

cnf(c_99,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | v1_partfun1(k3_partfun1(sK1,k1_xboole_0,sK0),k1_xboole_0)
    | sK0 != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_98])).

cnf(c_516,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | v1_partfun1(k3_partfun1(sK1,k1_xboole_0,sK0),k1_xboole_0)
    | sK0 != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_99])).

cnf(c_669,plain,
    ( sK0 != k1_xboole_0
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
    | v1_partfun1(k3_partfun1(sK1,k1_xboole_0,sK0),k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_516])).

cnf(c_100,plain,
    ( sK0 != k1_xboole_0
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
    | v1_partfun1(k3_partfun1(sK1,k1_xboole_0,sK0),k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_99])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_partfun1(X0,X1)
    | ~ v1_funct_1(X0)
    | k5_partfun1(X1,X2,X0) != k1_enumset1(X0,X0,X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_160,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_partfun1(X0,X1)
    | k5_partfun1(X1,X2,X0) != k1_enumset1(X0,X0,X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_8])).

cnf(c_161,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_partfun1(sK1,X0)
    | k5_partfun1(X0,X1,sK1) != k1_enumset1(sK1,sK1,sK1) ),
    inference(unflattening,[status(thm)],[c_160])).

cnf(c_163,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v1_partfun1(sK1,sK0)
    | k5_partfun1(sK0,sK0,sK1) != k1_enumset1(sK1,sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_161])).

cnf(c_299,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k5_partfun1(X0,X1,sK1) = k1_enumset1(sK1,sK1,sK1)
    | k3_partfun1(sK1,sK0,sK0) != sK1
    | sK0 != X0
    | sK0 = k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_115,c_146])).

cnf(c_300,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
    | k5_partfun1(sK0,X0,sK1) = k1_enumset1(sK1,sK1,sK1)
    | k3_partfun1(sK1,sK0,sK0) != sK1
    | sK0 = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_299])).

cnf(c_136,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k3_partfun1(sK1,sK0,sK0) = sK1 ),
    inference(instantiation,[status(thm)],[c_134])).

cnf(c_304,plain,
    ( k5_partfun1(sK0,X0,sK1) = k1_enumset1(sK1,sK1,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
    | sK0 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_300,c_6,c_136])).

cnf(c_305,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
    | k5_partfun1(sK0,X0,sK1) = k1_enumset1(sK1,sK1,sK1)
    | sK0 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_304])).

cnf(c_307,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k5_partfun1(sK0,sK0,sK1) = k1_enumset1(sK1,sK1,sK1)
    | sK0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_305])).

cnf(c_779,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
    | v1_partfun1(k3_partfun1(sK1,k1_xboole_0,sK0),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_669,c_6,c_100,c_163,c_307,c_555,c_742])).

cnf(c_837,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v1_partfun1(k3_partfun1(sK1,k1_xboole_0,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_833,c_779])).

cnf(c_839,plain,
    ( k3_partfun1(sK1,k1_xboole_0,k1_xboole_0) = sK1 ),
    inference(demodulation,[status(thm)],[c_833,c_740])).

cnf(c_847,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v1_partfun1(sK1,k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_837,c_839])).

cnf(c_840,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_833,c_668])).

cnf(c_850,plain,
    ( v1_partfun1(sK1,k1_xboole_0) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_847,c_840])).

cnf(c_853,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_836,c_850])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:48:42 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.02/0.93  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.02/0.93  
% 1.02/0.93  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.02/0.93  
% 1.02/0.93  ------  iProver source info
% 1.02/0.93  
% 1.02/0.93  git: date: 2020-06-30 10:37:57 +0100
% 1.02/0.93  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.02/0.93  git: non_committed_changes: false
% 1.02/0.93  git: last_make_outside_of_git: false
% 1.02/0.93  
% 1.02/0.93  ------ 
% 1.02/0.93  
% 1.02/0.93  ------ Input Options
% 1.02/0.93  
% 1.02/0.93  --out_options                           all
% 1.02/0.93  --tptp_safe_out                         true
% 1.02/0.93  --problem_path                          ""
% 1.02/0.93  --include_path                          ""
% 1.02/0.93  --clausifier                            res/vclausify_rel
% 1.02/0.93  --clausifier_options                    --mode clausify
% 1.02/0.93  --stdin                                 false
% 1.02/0.93  --stats_out                             all
% 1.02/0.93  
% 1.02/0.93  ------ General Options
% 1.02/0.93  
% 1.02/0.93  --fof                                   false
% 1.02/0.93  --time_out_real                         305.
% 1.02/0.93  --time_out_virtual                      -1.
% 1.02/0.93  --symbol_type_check                     false
% 1.02/0.93  --clausify_out                          false
% 1.02/0.93  --sig_cnt_out                           false
% 1.02/0.93  --trig_cnt_out                          false
% 1.02/0.93  --trig_cnt_out_tolerance                1.
% 1.02/0.93  --trig_cnt_out_sk_spl                   false
% 1.02/0.93  --abstr_cl_out                          false
% 1.02/0.93  
% 1.02/0.93  ------ Global Options
% 1.02/0.93  
% 1.02/0.93  --schedule                              default
% 1.02/0.93  --add_important_lit                     false
% 1.02/0.93  --prop_solver_per_cl                    1000
% 1.02/0.93  --min_unsat_core                        false
% 1.02/0.93  --soft_assumptions                      false
% 1.02/0.93  --soft_lemma_size                       3
% 1.02/0.93  --prop_impl_unit_size                   0
% 1.02/0.93  --prop_impl_unit                        []
% 1.02/0.93  --share_sel_clauses                     true
% 1.02/0.93  --reset_solvers                         false
% 1.02/0.93  --bc_imp_inh                            [conj_cone]
% 1.02/0.93  --conj_cone_tolerance                   3.
% 1.02/0.93  --extra_neg_conj                        none
% 1.02/0.93  --large_theory_mode                     true
% 1.02/0.93  --prolific_symb_bound                   200
% 1.02/0.93  --lt_threshold                          2000
% 1.02/0.93  --clause_weak_htbl                      true
% 1.02/0.93  --gc_record_bc_elim                     false
% 1.02/0.93  
% 1.02/0.93  ------ Preprocessing Options
% 1.02/0.93  
% 1.02/0.93  --preprocessing_flag                    true
% 1.02/0.93  --time_out_prep_mult                    0.1
% 1.02/0.93  --splitting_mode                        input
% 1.02/0.93  --splitting_grd                         true
% 1.02/0.93  --splitting_cvd                         false
% 1.02/0.93  --splitting_cvd_svl                     false
% 1.02/0.93  --splitting_nvd                         32
% 1.02/0.93  --sub_typing                            true
% 1.02/0.93  --prep_gs_sim                           true
% 1.02/0.93  --prep_unflatten                        true
% 1.02/0.93  --prep_res_sim                          true
% 1.02/0.93  --prep_upred                            true
% 1.02/0.93  --prep_sem_filter                       exhaustive
% 1.02/0.93  --prep_sem_filter_out                   false
% 1.02/0.93  --pred_elim                             true
% 1.02/0.93  --res_sim_input                         true
% 1.02/0.93  --eq_ax_congr_red                       true
% 1.02/0.93  --pure_diseq_elim                       true
% 1.02/0.93  --brand_transform                       false
% 1.02/0.93  --non_eq_to_eq                          false
% 1.02/0.93  --prep_def_merge                        true
% 1.02/0.93  --prep_def_merge_prop_impl              false
% 1.02/0.93  --prep_def_merge_mbd                    true
% 1.02/0.93  --prep_def_merge_tr_red                 false
% 1.02/0.93  --prep_def_merge_tr_cl                  false
% 1.02/0.93  --smt_preprocessing                     true
% 1.02/0.93  --smt_ac_axioms                         fast
% 1.02/0.93  --preprocessed_out                      false
% 1.02/0.93  --preprocessed_stats                    false
% 1.02/0.93  
% 1.02/0.93  ------ Abstraction refinement Options
% 1.02/0.93  
% 1.02/0.93  --abstr_ref                             []
% 1.02/0.93  --abstr_ref_prep                        false
% 1.02/0.93  --abstr_ref_until_sat                   false
% 1.02/0.93  --abstr_ref_sig_restrict                funpre
% 1.02/0.93  --abstr_ref_af_restrict_to_split_sk     false
% 1.02/0.93  --abstr_ref_under                       []
% 1.02/0.93  
% 1.02/0.93  ------ SAT Options
% 1.02/0.93  
% 1.02/0.93  --sat_mode                              false
% 1.02/0.93  --sat_fm_restart_options                ""
% 1.02/0.93  --sat_gr_def                            false
% 1.02/0.93  --sat_epr_types                         true
% 1.02/0.93  --sat_non_cyclic_types                  false
% 1.02/0.93  --sat_finite_models                     false
% 1.02/0.93  --sat_fm_lemmas                         false
% 1.02/0.93  --sat_fm_prep                           false
% 1.02/0.93  --sat_fm_uc_incr                        true
% 1.02/0.93  --sat_out_model                         small
% 1.02/0.93  --sat_out_clauses                       false
% 1.02/0.93  
% 1.02/0.93  ------ QBF Options
% 1.02/0.93  
% 1.02/0.93  --qbf_mode                              false
% 1.02/0.93  --qbf_elim_univ                         false
% 1.02/0.93  --qbf_dom_inst                          none
% 1.02/0.93  --qbf_dom_pre_inst                      false
% 1.02/0.93  --qbf_sk_in                             false
% 1.02/0.93  --qbf_pred_elim                         true
% 1.02/0.93  --qbf_split                             512
% 1.02/0.93  
% 1.02/0.93  ------ BMC1 Options
% 1.02/0.93  
% 1.02/0.93  --bmc1_incremental                      false
% 1.02/0.93  --bmc1_axioms                           reachable_all
% 1.02/0.93  --bmc1_min_bound                        0
% 1.02/0.93  --bmc1_max_bound                        -1
% 1.02/0.93  --bmc1_max_bound_default                -1
% 1.02/0.93  --bmc1_symbol_reachability              true
% 1.02/0.93  --bmc1_property_lemmas                  false
% 1.02/0.93  --bmc1_k_induction                      false
% 1.02/0.93  --bmc1_non_equiv_states                 false
% 1.02/0.93  --bmc1_deadlock                         false
% 1.02/0.93  --bmc1_ucm                              false
% 1.02/0.93  --bmc1_add_unsat_core                   none
% 1.02/0.93  --bmc1_unsat_core_children              false
% 1.02/0.93  --bmc1_unsat_core_extrapolate_axioms    false
% 1.02/0.93  --bmc1_out_stat                         full
% 1.02/0.93  --bmc1_ground_init                      false
% 1.02/0.93  --bmc1_pre_inst_next_state              false
% 1.02/0.93  --bmc1_pre_inst_state                   false
% 1.02/0.93  --bmc1_pre_inst_reach_state             false
% 1.02/0.93  --bmc1_out_unsat_core                   false
% 1.02/0.93  --bmc1_aig_witness_out                  false
% 1.02/0.93  --bmc1_verbose                          false
% 1.02/0.93  --bmc1_dump_clauses_tptp                false
% 1.02/0.93  --bmc1_dump_unsat_core_tptp             false
% 1.02/0.93  --bmc1_dump_file                        -
% 1.02/0.93  --bmc1_ucm_expand_uc_limit              128
% 1.02/0.93  --bmc1_ucm_n_expand_iterations          6
% 1.02/0.93  --bmc1_ucm_extend_mode                  1
% 1.02/0.93  --bmc1_ucm_init_mode                    2
% 1.02/0.93  --bmc1_ucm_cone_mode                    none
% 1.02/0.93  --bmc1_ucm_reduced_relation_type        0
% 1.02/0.93  --bmc1_ucm_relax_model                  4
% 1.02/0.93  --bmc1_ucm_full_tr_after_sat            true
% 1.02/0.93  --bmc1_ucm_expand_neg_assumptions       false
% 1.02/0.93  --bmc1_ucm_layered_model                none
% 1.02/0.93  --bmc1_ucm_max_lemma_size               10
% 1.02/0.93  
% 1.02/0.93  ------ AIG Options
% 1.02/0.93  
% 1.02/0.93  --aig_mode                              false
% 1.02/0.93  
% 1.02/0.93  ------ Instantiation Options
% 1.02/0.93  
% 1.02/0.93  --instantiation_flag                    true
% 1.02/0.93  --inst_sos_flag                         false
% 1.02/0.93  --inst_sos_phase                        true
% 1.02/0.93  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.02/0.93  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.02/0.93  --inst_lit_sel_side                     num_symb
% 1.02/0.93  --inst_solver_per_active                1400
% 1.02/0.93  --inst_solver_calls_frac                1.
% 1.02/0.93  --inst_passive_queue_type               priority_queues
% 1.02/0.93  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.02/0.93  --inst_passive_queues_freq              [25;2]
% 1.02/0.93  --inst_dismatching                      true
% 1.02/0.93  --inst_eager_unprocessed_to_passive     true
% 1.02/0.93  --inst_prop_sim_given                   true
% 1.02/0.93  --inst_prop_sim_new                     false
% 1.02/0.93  --inst_subs_new                         false
% 1.02/0.93  --inst_eq_res_simp                      false
% 1.02/0.93  --inst_subs_given                       false
% 1.02/0.93  --inst_orphan_elimination               true
% 1.02/0.93  --inst_learning_loop_flag               true
% 1.02/0.93  --inst_learning_start                   3000
% 1.02/0.93  --inst_learning_factor                  2
% 1.02/0.93  --inst_start_prop_sim_after_learn       3
% 1.02/0.93  --inst_sel_renew                        solver
% 1.02/0.93  --inst_lit_activity_flag                true
% 1.02/0.93  --inst_restr_to_given                   false
% 1.02/0.93  --inst_activity_threshold               500
% 1.02/0.93  --inst_out_proof                        true
% 1.02/0.93  
% 1.02/0.93  ------ Resolution Options
% 1.02/0.93  
% 1.02/0.93  --resolution_flag                       true
% 1.02/0.93  --res_lit_sel                           adaptive
% 1.02/0.93  --res_lit_sel_side                      none
% 1.02/0.93  --res_ordering                          kbo
% 1.02/0.93  --res_to_prop_solver                    active
% 1.02/0.93  --res_prop_simpl_new                    false
% 1.02/0.93  --res_prop_simpl_given                  true
% 1.02/0.93  --res_passive_queue_type                priority_queues
% 1.02/0.93  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.02/0.93  --res_passive_queues_freq               [15;5]
% 1.02/0.93  --res_forward_subs                      full
% 1.02/0.93  --res_backward_subs                     full
% 1.02/0.93  --res_forward_subs_resolution           true
% 1.02/0.93  --res_backward_subs_resolution          true
% 1.02/0.93  --res_orphan_elimination                true
% 1.02/0.93  --res_time_limit                        2.
% 1.02/0.93  --res_out_proof                         true
% 1.02/0.93  
% 1.02/0.93  ------ Superposition Options
% 1.02/0.93  
% 1.02/0.93  --superposition_flag                    true
% 1.02/0.93  --sup_passive_queue_type                priority_queues
% 1.02/0.93  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.02/0.93  --sup_passive_queues_freq               [8;1;4]
% 1.02/0.93  --demod_completeness_check              fast
% 1.02/0.93  --demod_use_ground                      true
% 1.02/0.93  --sup_to_prop_solver                    passive
% 1.02/0.93  --sup_prop_simpl_new                    true
% 1.02/0.93  --sup_prop_simpl_given                  true
% 1.02/0.93  --sup_fun_splitting                     false
% 1.02/0.93  --sup_smt_interval                      50000
% 1.02/0.93  
% 1.02/0.93  ------ Superposition Simplification Setup
% 1.02/0.93  
% 1.02/0.93  --sup_indices_passive                   []
% 1.02/0.93  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.02/0.93  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.02/0.93  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.02/0.93  --sup_full_triv                         [TrivRules;PropSubs]
% 1.02/0.93  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.02/0.93  --sup_full_bw                           [BwDemod]
% 1.02/0.93  --sup_immed_triv                        [TrivRules]
% 1.02/0.93  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.02/0.93  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.02/0.93  --sup_immed_bw_main                     []
% 1.02/0.93  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.02/0.93  --sup_input_triv                        [Unflattening;TrivRules]
% 1.02/0.93  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.02/0.93  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.02/0.93  
% 1.02/0.93  ------ Combination Options
% 1.02/0.93  
% 1.02/0.93  --comb_res_mult                         3
% 1.02/0.93  --comb_sup_mult                         2
% 1.02/0.93  --comb_inst_mult                        10
% 1.02/0.93  
% 1.02/0.93  ------ Debug Options
% 1.02/0.93  
% 1.02/0.93  --dbg_backtrace                         false
% 1.02/0.93  --dbg_dump_prop_clauses                 false
% 1.02/0.93  --dbg_dump_prop_clauses_file            -
% 1.02/0.93  --dbg_out_stat                          false
% 1.02/0.93  ------ Parsing...
% 1.02/0.93  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.02/0.93  
% 1.02/0.93  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 1.02/0.93  
% 1.02/0.93  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.02/0.93  
% 1.02/0.93  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.02/0.93  ------ Proving...
% 1.02/0.93  ------ Problem Properties 
% 1.02/0.93  
% 1.02/0.93  
% 1.02/0.93  clauses                                 7
% 1.02/0.93  conjectures                             2
% 1.02/0.93  EPR                                     0
% 1.02/0.93  Horn                                    6
% 1.02/0.93  unary                                   2
% 1.02/0.93  binary                                  2
% 1.02/0.93  lits                                    15
% 1.02/0.93  lits eq                                 6
% 1.02/0.93  fd_pure                                 0
% 1.02/0.93  fd_pseudo                               0
% 1.02/0.93  fd_cond                                 0
% 1.02/0.93  fd_pseudo_cond                          0
% 1.02/0.93  AC symbols                              0
% 1.02/0.93  
% 1.02/0.93  ------ Schedule dynamic 5 is on 
% 1.02/0.93  
% 1.02/0.93  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.02/0.93  
% 1.02/0.93  
% 1.02/0.93  ------ 
% 1.02/0.93  Current options:
% 1.02/0.93  ------ 
% 1.02/0.93  
% 1.02/0.93  ------ Input Options
% 1.02/0.93  
% 1.02/0.93  --out_options                           all
% 1.02/0.93  --tptp_safe_out                         true
% 1.02/0.93  --problem_path                          ""
% 1.02/0.93  --include_path                          ""
% 1.02/0.93  --clausifier                            res/vclausify_rel
% 1.02/0.93  --clausifier_options                    --mode clausify
% 1.02/0.93  --stdin                                 false
% 1.02/0.93  --stats_out                             all
% 1.02/0.93  
% 1.02/0.93  ------ General Options
% 1.02/0.93  
% 1.02/0.93  --fof                                   false
% 1.02/0.93  --time_out_real                         305.
% 1.02/0.93  --time_out_virtual                      -1.
% 1.02/0.93  --symbol_type_check                     false
% 1.02/0.93  --clausify_out                          false
% 1.02/0.93  --sig_cnt_out                           false
% 1.02/0.93  --trig_cnt_out                          false
% 1.02/0.93  --trig_cnt_out_tolerance                1.
% 1.02/0.93  --trig_cnt_out_sk_spl                   false
% 1.02/0.93  --abstr_cl_out                          false
% 1.02/0.93  
% 1.02/0.93  ------ Global Options
% 1.02/0.93  
% 1.02/0.93  --schedule                              default
% 1.02/0.93  --add_important_lit                     false
% 1.02/0.93  --prop_solver_per_cl                    1000
% 1.02/0.93  --min_unsat_core                        false
% 1.02/0.93  --soft_assumptions                      false
% 1.02/0.93  --soft_lemma_size                       3
% 1.02/0.93  --prop_impl_unit_size                   0
% 1.02/0.93  --prop_impl_unit                        []
% 1.02/0.93  --share_sel_clauses                     true
% 1.02/0.93  --reset_solvers                         false
% 1.02/0.93  --bc_imp_inh                            [conj_cone]
% 1.02/0.93  --conj_cone_tolerance                   3.
% 1.02/0.93  --extra_neg_conj                        none
% 1.02/0.93  --large_theory_mode                     true
% 1.02/0.93  --prolific_symb_bound                   200
% 1.02/0.93  --lt_threshold                          2000
% 1.02/0.93  --clause_weak_htbl                      true
% 1.02/0.93  --gc_record_bc_elim                     false
% 1.02/0.93  
% 1.02/0.93  ------ Preprocessing Options
% 1.02/0.93  
% 1.02/0.93  --preprocessing_flag                    true
% 1.02/0.93  --time_out_prep_mult                    0.1
% 1.02/0.93  --splitting_mode                        input
% 1.02/0.93  --splitting_grd                         true
% 1.02/0.93  --splitting_cvd                         false
% 1.02/0.93  --splitting_cvd_svl                     false
% 1.02/0.93  --splitting_nvd                         32
% 1.02/0.93  --sub_typing                            true
% 1.02/0.93  --prep_gs_sim                           true
% 1.02/0.93  --prep_unflatten                        true
% 1.02/0.93  --prep_res_sim                          true
% 1.02/0.93  --prep_upred                            true
% 1.02/0.93  --prep_sem_filter                       exhaustive
% 1.02/0.93  --prep_sem_filter_out                   false
% 1.02/0.93  --pred_elim                             true
% 1.02/0.93  --res_sim_input                         true
% 1.02/0.93  --eq_ax_congr_red                       true
% 1.02/0.93  --pure_diseq_elim                       true
% 1.02/0.93  --brand_transform                       false
% 1.02/0.93  --non_eq_to_eq                          false
% 1.02/0.93  --prep_def_merge                        true
% 1.02/0.93  --prep_def_merge_prop_impl              false
% 1.02/0.93  --prep_def_merge_mbd                    true
% 1.02/0.93  --prep_def_merge_tr_red                 false
% 1.02/0.93  --prep_def_merge_tr_cl                  false
% 1.02/0.93  --smt_preprocessing                     true
% 1.02/0.93  --smt_ac_axioms                         fast
% 1.02/0.93  --preprocessed_out                      false
% 1.02/0.93  --preprocessed_stats                    false
% 1.02/0.93  
% 1.02/0.93  ------ Abstraction refinement Options
% 1.02/0.93  
% 1.02/0.93  --abstr_ref                             []
% 1.02/0.93  --abstr_ref_prep                        false
% 1.02/0.93  --abstr_ref_until_sat                   false
% 1.02/0.93  --abstr_ref_sig_restrict                funpre
% 1.02/0.93  --abstr_ref_af_restrict_to_split_sk     false
% 1.02/0.93  --abstr_ref_under                       []
% 1.02/0.93  
% 1.02/0.93  ------ SAT Options
% 1.02/0.93  
% 1.02/0.93  --sat_mode                              false
% 1.02/0.93  --sat_fm_restart_options                ""
% 1.02/0.93  --sat_gr_def                            false
% 1.02/0.93  --sat_epr_types                         true
% 1.02/0.93  --sat_non_cyclic_types                  false
% 1.02/0.93  --sat_finite_models                     false
% 1.02/0.93  --sat_fm_lemmas                         false
% 1.02/0.93  --sat_fm_prep                           false
% 1.02/0.93  --sat_fm_uc_incr                        true
% 1.02/0.93  --sat_out_model                         small
% 1.02/0.93  --sat_out_clauses                       false
% 1.02/0.93  
% 1.02/0.93  ------ QBF Options
% 1.02/0.93  
% 1.02/0.93  --qbf_mode                              false
% 1.02/0.93  --qbf_elim_univ                         false
% 1.02/0.93  --qbf_dom_inst                          none
% 1.02/0.93  --qbf_dom_pre_inst                      false
% 1.02/0.93  --qbf_sk_in                             false
% 1.02/0.93  --qbf_pred_elim                         true
% 1.02/0.93  --qbf_split                             512
% 1.02/0.93  
% 1.02/0.93  ------ BMC1 Options
% 1.02/0.93  
% 1.02/0.93  --bmc1_incremental                      false
% 1.02/0.93  --bmc1_axioms                           reachable_all
% 1.02/0.93  --bmc1_min_bound                        0
% 1.02/0.93  --bmc1_max_bound                        -1
% 1.02/0.93  --bmc1_max_bound_default                -1
% 1.02/0.93  --bmc1_symbol_reachability              true
% 1.02/0.93  --bmc1_property_lemmas                  false
% 1.02/0.93  --bmc1_k_induction                      false
% 1.02/0.93  --bmc1_non_equiv_states                 false
% 1.02/0.93  --bmc1_deadlock                         false
% 1.02/0.93  --bmc1_ucm                              false
% 1.02/0.93  --bmc1_add_unsat_core                   none
% 1.02/0.93  --bmc1_unsat_core_children              false
% 1.02/0.93  --bmc1_unsat_core_extrapolate_axioms    false
% 1.02/0.93  --bmc1_out_stat                         full
% 1.02/0.93  --bmc1_ground_init                      false
% 1.02/0.93  --bmc1_pre_inst_next_state              false
% 1.02/0.93  --bmc1_pre_inst_state                   false
% 1.02/0.93  --bmc1_pre_inst_reach_state             false
% 1.02/0.93  --bmc1_out_unsat_core                   false
% 1.02/0.93  --bmc1_aig_witness_out                  false
% 1.02/0.93  --bmc1_verbose                          false
% 1.02/0.93  --bmc1_dump_clauses_tptp                false
% 1.02/0.93  --bmc1_dump_unsat_core_tptp             false
% 1.02/0.93  --bmc1_dump_file                        -
% 1.02/0.93  --bmc1_ucm_expand_uc_limit              128
% 1.02/0.93  --bmc1_ucm_n_expand_iterations          6
% 1.02/0.93  --bmc1_ucm_extend_mode                  1
% 1.02/0.93  --bmc1_ucm_init_mode                    2
% 1.02/0.93  --bmc1_ucm_cone_mode                    none
% 1.02/0.93  --bmc1_ucm_reduced_relation_type        0
% 1.02/0.93  --bmc1_ucm_relax_model                  4
% 1.02/0.93  --bmc1_ucm_full_tr_after_sat            true
% 1.02/0.93  --bmc1_ucm_expand_neg_assumptions       false
% 1.02/0.93  --bmc1_ucm_layered_model                none
% 1.02/0.93  --bmc1_ucm_max_lemma_size               10
% 1.02/0.93  
% 1.02/0.93  ------ AIG Options
% 1.02/0.93  
% 1.02/0.93  --aig_mode                              false
% 1.02/0.93  
% 1.02/0.93  ------ Instantiation Options
% 1.02/0.93  
% 1.02/0.93  --instantiation_flag                    true
% 1.02/0.93  --inst_sos_flag                         false
% 1.02/0.93  --inst_sos_phase                        true
% 1.02/0.93  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.02/0.93  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.02/0.93  --inst_lit_sel_side                     none
% 1.02/0.93  --inst_solver_per_active                1400
% 1.02/0.93  --inst_solver_calls_frac                1.
% 1.02/0.93  --inst_passive_queue_type               priority_queues
% 1.02/0.93  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.02/0.93  --inst_passive_queues_freq              [25;2]
% 1.02/0.93  --inst_dismatching                      true
% 1.02/0.93  --inst_eager_unprocessed_to_passive     true
% 1.02/0.93  --inst_prop_sim_given                   true
% 1.02/0.93  --inst_prop_sim_new                     false
% 1.02/0.93  --inst_subs_new                         false
% 1.02/0.93  --inst_eq_res_simp                      false
% 1.02/0.93  --inst_subs_given                       false
% 1.02/0.93  --inst_orphan_elimination               true
% 1.02/0.93  --inst_learning_loop_flag               true
% 1.02/0.93  --inst_learning_start                   3000
% 1.02/0.93  --inst_learning_factor                  2
% 1.02/0.93  --inst_start_prop_sim_after_learn       3
% 1.02/0.93  --inst_sel_renew                        solver
% 1.02/0.93  --inst_lit_activity_flag                true
% 1.02/0.93  --inst_restr_to_given                   false
% 1.02/0.93  --inst_activity_threshold               500
% 1.02/0.93  --inst_out_proof                        true
% 1.02/0.93  
% 1.02/0.93  ------ Resolution Options
% 1.02/0.93  
% 1.02/0.93  --resolution_flag                       false
% 1.02/0.93  --res_lit_sel                           adaptive
% 1.02/0.93  --res_lit_sel_side                      none
% 1.02/0.93  --res_ordering                          kbo
% 1.02/0.93  --res_to_prop_solver                    active
% 1.02/0.93  --res_prop_simpl_new                    false
% 1.02/0.93  --res_prop_simpl_given                  true
% 1.02/0.93  --res_passive_queue_type                priority_queues
% 1.02/0.93  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.02/0.93  --res_passive_queues_freq               [15;5]
% 1.02/0.93  --res_forward_subs                      full
% 1.02/0.93  --res_backward_subs                     full
% 1.02/0.93  --res_forward_subs_resolution           true
% 1.02/0.93  --res_backward_subs_resolution          true
% 1.02/0.93  --res_orphan_elimination                true
% 1.02/0.93  --res_time_limit                        2.
% 1.02/0.93  --res_out_proof                         true
% 1.02/0.93  
% 1.02/0.93  ------ Superposition Options
% 1.02/0.93  
% 1.02/0.93  --superposition_flag                    true
% 1.02/0.93  --sup_passive_queue_type                priority_queues
% 1.02/0.93  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.02/0.93  --sup_passive_queues_freq               [8;1;4]
% 1.02/0.93  --demod_completeness_check              fast
% 1.02/0.93  --demod_use_ground                      true
% 1.02/0.93  --sup_to_prop_solver                    passive
% 1.02/0.93  --sup_prop_simpl_new                    true
% 1.02/0.93  --sup_prop_simpl_given                  true
% 1.02/0.93  --sup_fun_splitting                     false
% 1.02/0.93  --sup_smt_interval                      50000
% 1.02/0.93  
% 1.02/0.93  ------ Superposition Simplification Setup
% 1.02/0.93  
% 1.02/0.93  --sup_indices_passive                   []
% 1.02/0.93  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.02/0.93  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.02/0.93  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.02/0.93  --sup_full_triv                         [TrivRules;PropSubs]
% 1.02/0.93  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.02/0.93  --sup_full_bw                           [BwDemod]
% 1.02/0.93  --sup_immed_triv                        [TrivRules]
% 1.02/0.93  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.02/0.93  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.02/0.93  --sup_immed_bw_main                     []
% 1.02/0.93  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.02/0.93  --sup_input_triv                        [Unflattening;TrivRules]
% 1.02/0.93  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.02/0.93  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.02/0.93  
% 1.02/0.93  ------ Combination Options
% 1.02/0.93  
% 1.02/0.93  --comb_res_mult                         3
% 1.02/0.93  --comb_sup_mult                         2
% 1.02/0.93  --comb_inst_mult                        10
% 1.02/0.93  
% 1.02/0.93  ------ Debug Options
% 1.02/0.93  
% 1.02/0.93  --dbg_backtrace                         false
% 1.02/0.93  --dbg_dump_prop_clauses                 false
% 1.02/0.93  --dbg_dump_prop_clauses_file            -
% 1.02/0.93  --dbg_out_stat                          false
% 1.02/0.93  
% 1.02/0.93  
% 1.02/0.93  
% 1.02/0.93  
% 1.02/0.93  ------ Proving...
% 1.02/0.93  
% 1.02/0.93  
% 1.02/0.93  % SZS status Theorem for theBenchmark.p
% 1.02/0.93  
% 1.02/0.93   Resolution empty clause
% 1.02/0.93  
% 1.02/0.93  % SZS output start CNFRefutation for theBenchmark.p
% 1.02/0.93  
% 1.02/0.93  fof(f3,axiom,(
% 1.02/0.93    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => v1_partfun1(k3_partfun1(X2,X0,X1),X0)))),
% 1.02/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.02/0.93  
% 1.02/0.93  fof(f8,plain,(
% 1.02/0.93    ! [X0,X1,X2] : ((v1_partfun1(k3_partfun1(X2,X0,X1),X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.02/0.93    inference(ennf_transformation,[],[f3])).
% 1.02/0.93  
% 1.02/0.93  fof(f9,plain,(
% 1.02/0.93    ! [X0,X1,X2] : (v1_partfun1(k3_partfun1(X2,X0,X1),X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.02/0.93    inference(flattening,[],[f8])).
% 1.02/0.93  
% 1.02/0.93  fof(f21,plain,(
% 1.02/0.93    ( ! [X2,X0,X1] : (v1_partfun1(k3_partfun1(X2,X0,X1),X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.02/0.93    inference(cnf_transformation,[],[f9])).
% 1.02/0.93  
% 1.02/0.93  fof(f6,conjecture,(
% 1.02/0.93    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_tarski(X1) = k5_partfun1(X0,X0,k3_partfun1(X1,X0,X0)))),
% 1.02/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.02/0.93  
% 1.02/0.93  fof(f7,negated_conjecture,(
% 1.02/0.93    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_tarski(X1) = k5_partfun1(X0,X0,k3_partfun1(X1,X0,X0)))),
% 1.02/0.93    inference(negated_conjecture,[],[f6])).
% 1.02/0.93  
% 1.02/0.93  fof(f14,plain,(
% 1.02/0.93    ? [X0,X1] : (k1_tarski(X1) != k5_partfun1(X0,X0,k3_partfun1(X1,X0,X0)) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 1.02/0.93    inference(ennf_transformation,[],[f7])).
% 1.02/0.93  
% 1.02/0.93  fof(f15,plain,(
% 1.02/0.93    ? [X0,X1] : (k1_tarski(X1) != k5_partfun1(X0,X0,k3_partfun1(X1,X0,X0)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 1.02/0.93    inference(flattening,[],[f14])).
% 1.02/0.93  
% 1.02/0.93  fof(f17,plain,(
% 1.02/0.93    ? [X0,X1] : (k1_tarski(X1) != k5_partfun1(X0,X0,k3_partfun1(X1,X0,X0)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (k1_tarski(sK1) != k5_partfun1(sK0,sK0,k3_partfun1(sK1,sK0,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 1.02/0.93    introduced(choice_axiom,[])).
% 1.02/0.93  
% 1.02/0.93  fof(f18,plain,(
% 1.02/0.93    k1_tarski(sK1) != k5_partfun1(sK0,sK0,k3_partfun1(sK1,sK0,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 1.02/0.93    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f17])).
% 1.02/0.93  
% 1.02/0.93  fof(f27,plain,(
% 1.02/0.93    v1_funct_2(sK1,sK0,sK0)),
% 1.02/0.93    inference(cnf_transformation,[],[f18])).
% 1.02/0.93  
% 1.02/0.93  fof(f26,plain,(
% 1.02/0.93    v1_funct_1(sK1)),
% 1.02/0.93    inference(cnf_transformation,[],[f18])).
% 1.02/0.93  
% 1.02/0.93  fof(f28,plain,(
% 1.02/0.93    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.02/0.93    inference(cnf_transformation,[],[f18])).
% 1.02/0.93  
% 1.02/0.93  fof(f5,axiom,(
% 1.02/0.93    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k3_partfun1(X2,X0,X1) = X2)),
% 1.02/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.02/0.93  
% 1.02/0.93  fof(f12,plain,(
% 1.02/0.93    ! [X0,X1,X2] : (k3_partfun1(X2,X0,X1) = X2 | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.02/0.93    inference(ennf_transformation,[],[f5])).
% 1.02/0.93  
% 1.02/0.93  fof(f13,plain,(
% 1.02/0.93    ! [X0,X1,X2] : (k3_partfun1(X2,X0,X1) = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.02/0.93    inference(flattening,[],[f12])).
% 1.02/0.93  
% 1.02/0.93  fof(f25,plain,(
% 1.02/0.93    ( ! [X2,X0,X1] : (k3_partfun1(X2,X0,X1) = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.02/0.93    inference(cnf_transformation,[],[f13])).
% 1.02/0.93  
% 1.02/0.93  fof(f4,axiom,(
% 1.02/0.93    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) <=> k1_tarski(X2) = k5_partfun1(X0,X1,X2)))),
% 1.02/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.02/0.93  
% 1.02/0.93  fof(f10,plain,(
% 1.02/0.93    ! [X0,X1,X2] : ((v1_partfun1(X2,X0) <=> k1_tarski(X2) = k5_partfun1(X0,X1,X2)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.02/0.93    inference(ennf_transformation,[],[f4])).
% 1.02/0.93  
% 1.02/0.93  fof(f11,plain,(
% 1.02/0.93    ! [X0,X1,X2] : ((v1_partfun1(X2,X0) <=> k1_tarski(X2) = k5_partfun1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.02/0.93    inference(flattening,[],[f10])).
% 1.02/0.93  
% 1.02/0.93  fof(f16,plain,(
% 1.02/0.93    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | k1_tarski(X2) != k5_partfun1(X0,X1,X2)) & (k1_tarski(X2) = k5_partfun1(X0,X1,X2) | ~v1_partfun1(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.02/0.93    inference(nnf_transformation,[],[f11])).
% 1.02/0.93  
% 1.02/0.93  fof(f23,plain,(
% 1.02/0.93    ( ! [X2,X0,X1] : (k1_tarski(X2) = k5_partfun1(X0,X1,X2) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.02/0.93    inference(cnf_transformation,[],[f16])).
% 1.02/0.93  
% 1.02/0.93  fof(f1,axiom,(
% 1.02/0.93    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.02/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.02/0.93  
% 1.02/0.93  fof(f19,plain,(
% 1.02/0.93    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.02/0.93    inference(cnf_transformation,[],[f1])).
% 1.02/0.93  
% 1.02/0.93  fof(f2,axiom,(
% 1.02/0.93    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.02/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.02/0.93  
% 1.02/0.93  fof(f20,plain,(
% 1.02/0.93    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.02/0.93    inference(cnf_transformation,[],[f2])).
% 1.02/0.93  
% 1.02/0.93  fof(f30,plain,(
% 1.02/0.93    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 1.02/0.93    inference(definition_unfolding,[],[f19,f20])).
% 1.02/0.93  
% 1.02/0.93  fof(f32,plain,(
% 1.02/0.93    ( ! [X2,X0,X1] : (k1_enumset1(X2,X2,X2) = k5_partfun1(X0,X1,X2) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.02/0.93    inference(definition_unfolding,[],[f23,f30])).
% 1.02/0.93  
% 1.02/0.93  fof(f29,plain,(
% 1.02/0.93    k1_tarski(sK1) != k5_partfun1(sK0,sK0,k3_partfun1(sK1,sK0,sK0))),
% 1.02/0.93    inference(cnf_transformation,[],[f18])).
% 1.02/0.93  
% 1.02/0.93  fof(f33,plain,(
% 1.02/0.93    k1_enumset1(sK1,sK1,sK1) != k5_partfun1(sK0,sK0,k3_partfun1(sK1,sK0,sK0))),
% 1.02/0.93    inference(definition_unfolding,[],[f29,f30])).
% 1.02/0.93  
% 1.02/0.93  fof(f22,plain,(
% 1.02/0.93    ( ! [X2,X0,X1] : (v1_partfun1(k3_partfun1(X2,X0,X1),X0) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.02/0.93    inference(cnf_transformation,[],[f9])).
% 1.02/0.93  
% 1.02/0.93  fof(f34,plain,(
% 1.02/0.93    ( ! [X2,X1] : (v1_partfun1(k3_partfun1(X2,k1_xboole_0,X1),k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~v1_funct_1(X2)) )),
% 1.02/0.93    inference(equality_resolution,[],[f22])).
% 1.02/0.93  
% 1.02/0.93  fof(f24,plain,(
% 1.02/0.93    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_tarski(X2) != k5_partfun1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.02/0.93    inference(cnf_transformation,[],[f16])).
% 1.02/0.93  
% 1.02/0.93  fof(f31,plain,(
% 1.02/0.93    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_enumset1(X2,X2,X2) != k5_partfun1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.02/0.93    inference(definition_unfolding,[],[f24,f30])).
% 1.02/0.93  
% 1.02/0.93  cnf(c_1,plain,
% 1.02/0.93      ( ~ v1_funct_2(X0,X1,X2)
% 1.02/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.02/0.93      | v1_partfun1(k3_partfun1(X0,X1,X2),X1)
% 1.02/0.93      | ~ v1_funct_1(X0)
% 1.02/0.93      | k1_xboole_0 = X2 ),
% 1.02/0.93      inference(cnf_transformation,[],[f21]) ).
% 1.02/0.93  
% 1.02/0.93  cnf(c_7,negated_conjecture,
% 1.02/0.93      ( v1_funct_2(sK1,sK0,sK0) ),
% 1.02/0.93      inference(cnf_transformation,[],[f27]) ).
% 1.02/0.93  
% 1.02/0.93  cnf(c_112,plain,
% 1.02/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.02/0.93      | v1_partfun1(k3_partfun1(X0,X1,X2),X1)
% 1.02/0.93      | ~ v1_funct_1(X0)
% 1.02/0.93      | sK0 != X1
% 1.02/0.93      | sK0 != X2
% 1.02/0.93      | sK1 != X0
% 1.02/0.93      | k1_xboole_0 = X2 ),
% 1.02/0.93      inference(resolution_lifted,[status(thm)],[c_1,c_7]) ).
% 1.02/0.93  
% 1.02/0.93  cnf(c_113,plain,
% 1.02/0.93      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 1.02/0.93      | v1_partfun1(k3_partfun1(sK1,sK0,sK0),sK0)
% 1.02/0.93      | ~ v1_funct_1(sK1)
% 1.02/0.93      | k1_xboole_0 = sK0 ),
% 1.02/0.93      inference(unflattening,[status(thm)],[c_112]) ).
% 1.02/0.93  
% 1.02/0.93  cnf(c_8,negated_conjecture,
% 1.02/0.93      ( v1_funct_1(sK1) ),
% 1.02/0.93      inference(cnf_transformation,[],[f26]) ).
% 1.02/0.93  
% 1.02/0.93  cnf(c_6,negated_conjecture,
% 1.02/0.93      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 1.02/0.93      inference(cnf_transformation,[],[f28]) ).
% 1.02/0.93  
% 1.02/0.93  cnf(c_115,plain,
% 1.02/0.93      ( v1_partfun1(k3_partfun1(sK1,sK0,sK0),sK0) | k1_xboole_0 = sK0 ),
% 1.02/0.93      inference(global_propositional_subsumption,[status(thm)],[c_113,c_8,c_6]) ).
% 1.02/0.93  
% 1.02/0.93  cnf(c_515,plain,
% 1.02/0.93      ( v1_partfun1(k3_partfun1(sK1,sK0,sK0),sK0) | k1_xboole_0 = sK0 ),
% 1.02/0.93      inference(subtyping,[status(esa)],[c_115]) ).
% 1.02/0.93  
% 1.02/0.93  cnf(c_670,plain,
% 1.02/0.93      ( k1_xboole_0 = sK0
% 1.02/0.93      | v1_partfun1(k3_partfun1(sK1,sK0,sK0),sK0) = iProver_top ),
% 1.02/0.93      inference(predicate_to_equality,[status(thm)],[c_515]) ).
% 1.02/0.93  
% 1.02/0.93  cnf(c_520,plain,( X0_40 = X0_40 ),theory(equality) ).
% 1.02/0.93  
% 1.02/0.93  cnf(c_543,plain,
% 1.02/0.93      ( sK1 = sK1 ),
% 1.02/0.93      inference(instantiation,[status(thm)],[c_520]) ).
% 1.02/0.93  
% 1.02/0.93  cnf(c_523,plain,( X0_43 = X0_43 ),theory(equality) ).
% 1.02/0.93  
% 1.02/0.93  cnf(c_546,plain,
% 1.02/0.93      ( sK0 = sK0 ),
% 1.02/0.93      inference(instantiation,[status(thm)],[c_523]) ).
% 1.02/0.93  
% 1.02/0.93  cnf(c_4,plain,
% 1.02/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.02/0.93      | ~ v1_funct_1(X0)
% 1.02/0.93      | k3_partfun1(X0,X1,X2) = X0 ),
% 1.02/0.93      inference(cnf_transformation,[],[f25]) ).
% 1.02/0.93  
% 1.02/0.93  cnf(c_133,plain,
% 1.02/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.02/0.93      | k3_partfun1(X0,X1,X2) = X0
% 1.02/0.93      | sK1 != X0 ),
% 1.02/0.93      inference(resolution_lifted,[status(thm)],[c_4,c_8]) ).
% 1.02/0.93  
% 1.02/0.93  cnf(c_134,plain,
% 1.02/0.93      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.02/0.93      | k3_partfun1(sK1,X0,X1) = sK1 ),
% 1.02/0.93      inference(unflattening,[status(thm)],[c_133]) ).
% 1.02/0.93  
% 1.02/0.93  cnf(c_514,plain,
% 1.02/0.93      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0_43,X1_43)))
% 1.02/0.93      | k3_partfun1(sK1,X0_43,X1_43) = sK1 ),
% 1.02/0.93      inference(subtyping,[status(esa)],[c_134]) ).
% 1.02/0.93  
% 1.02/0.93  cnf(c_552,plain,
% 1.02/0.93      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 1.02/0.93      | k3_partfun1(sK1,sK0,sK0) = sK1 ),
% 1.02/0.93      inference(instantiation,[status(thm)],[c_514]) ).
% 1.02/0.93  
% 1.02/0.93  cnf(c_3,plain,
% 1.02/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.02/0.93      | ~ v1_partfun1(X0,X1)
% 1.02/0.93      | ~ v1_funct_1(X0)
% 1.02/0.93      | k5_partfun1(X1,X2,X0) = k1_enumset1(X0,X0,X0) ),
% 1.02/0.93      inference(cnf_transformation,[],[f32]) ).
% 1.02/0.93  
% 1.02/0.93  cnf(c_145,plain,
% 1.02/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.02/0.93      | ~ v1_partfun1(X0,X1)
% 1.02/0.93      | k5_partfun1(X1,X2,X0) = k1_enumset1(X0,X0,X0)
% 1.02/0.93      | sK1 != X0 ),
% 1.02/0.93      inference(resolution_lifted,[status(thm)],[c_3,c_8]) ).
% 1.02/0.93  
% 1.02/0.93  cnf(c_146,plain,
% 1.02/0.93      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.02/0.93      | ~ v1_partfun1(sK1,X0)
% 1.02/0.93      | k5_partfun1(X0,X1,sK1) = k1_enumset1(sK1,sK1,sK1) ),
% 1.02/0.93      inference(unflattening,[status(thm)],[c_145]) ).
% 1.02/0.93  
% 1.02/0.93  cnf(c_513,plain,
% 1.02/0.93      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0_43,X1_43)))
% 1.02/0.93      | ~ v1_partfun1(sK1,X0_43)
% 1.02/0.93      | k5_partfun1(X0_43,X1_43,sK1) = k1_enumset1(sK1,sK1,sK1) ),
% 1.02/0.93      inference(subtyping,[status(esa)],[c_146]) ).
% 1.02/0.93  
% 1.02/0.93  cnf(c_555,plain,
% 1.02/0.93      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 1.02/0.93      | ~ v1_partfun1(sK1,sK0)
% 1.02/0.93      | k5_partfun1(sK0,sK0,sK1) = k1_enumset1(sK1,sK1,sK1) ),
% 1.02/0.93      inference(instantiation,[status(thm)],[c_513]) ).
% 1.02/0.93  
% 1.02/0.93  cnf(c_529,plain,
% 1.02/0.93      ( ~ v1_partfun1(X0_40,X0_43)
% 1.02/0.93      | v1_partfun1(X1_40,X1_43)
% 1.02/0.93      | X1_43 != X0_43
% 1.02/0.93      | X1_40 != X0_40 ),
% 1.02/0.93      theory(equality) ).
% 1.02/0.93  
% 1.02/0.93  cnf(c_727,plain,
% 1.02/0.93      ( v1_partfun1(X0_40,X0_43)
% 1.02/0.93      | ~ v1_partfun1(k3_partfun1(sK1,sK0,sK0),sK0)
% 1.02/0.93      | X0_43 != sK0
% 1.02/0.93      | X0_40 != k3_partfun1(sK1,sK0,sK0) ),
% 1.02/0.93      inference(instantiation,[status(thm)],[c_529]) ).
% 1.02/0.93  
% 1.02/0.93  cnf(c_729,plain,
% 1.02/0.93      ( ~ v1_partfun1(k3_partfun1(sK1,sK0,sK0),sK0)
% 1.02/0.93      | v1_partfun1(sK1,sK0)
% 1.02/0.93      | sK0 != sK0
% 1.02/0.93      | sK1 != k3_partfun1(sK1,sK0,sK0) ),
% 1.02/0.93      inference(instantiation,[status(thm)],[c_727]) ).
% 1.02/0.93  
% 1.02/0.93  cnf(c_517,negated_conjecture,
% 1.02/0.93      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 1.02/0.93      inference(subtyping,[status(esa)],[c_6]) ).
% 1.02/0.93  
% 1.02/0.93  cnf(c_668,plain,
% 1.02/0.93      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 1.02/0.93      inference(predicate_to_equality,[status(thm)],[c_517]) ).
% 1.02/0.93  
% 1.02/0.93  cnf(c_671,plain,
% 1.02/0.93      ( k3_partfun1(sK1,X0_43,X1_43) = sK1
% 1.02/0.93      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0_43,X1_43))) != iProver_top ),
% 1.02/0.93      inference(predicate_to_equality,[status(thm)],[c_514]) ).
% 1.02/0.93  
% 1.02/0.93  cnf(c_740,plain,
% 1.02/0.93      ( k3_partfun1(sK1,sK0,sK0) = sK1 ),
% 1.02/0.93      inference(superposition,[status(thm)],[c_668,c_671]) ).
% 1.02/0.93  
% 1.02/0.93  cnf(c_5,negated_conjecture,
% 1.02/0.93      ( k1_enumset1(sK1,sK1,sK1) != k5_partfun1(sK0,sK0,k3_partfun1(sK1,sK0,sK0)) ),
% 1.02/0.93      inference(cnf_transformation,[],[f33]) ).
% 1.02/0.93  
% 1.02/0.93  cnf(c_518,negated_conjecture,
% 1.02/0.93      ( k1_enumset1(sK1,sK1,sK1) != k5_partfun1(sK0,sK0,k3_partfun1(sK1,sK0,sK0)) ),
% 1.02/0.93      inference(subtyping,[status(esa)],[c_5]) ).
% 1.02/0.93  
% 1.02/0.93  cnf(c_742,plain,
% 1.02/0.93      ( k5_partfun1(sK0,sK0,sK1) != k1_enumset1(sK1,sK1,sK1) ),
% 1.02/0.93      inference(demodulation,[status(thm)],[c_740,c_518]) ).
% 1.02/0.93  
% 1.02/0.93  cnf(c_525,plain,
% 1.02/0.93      ( X0_40 != X1_40 | X2_40 != X1_40 | X2_40 = X0_40 ),
% 1.02/0.93      theory(equality) ).
% 1.02/0.93  
% 1.02/0.93  cnf(c_769,plain,
% 1.02/0.93      ( X0_40 != X1_40
% 1.02/0.93      | X0_40 = k3_partfun1(sK1,sK0,sK0)
% 1.02/0.93      | k3_partfun1(sK1,sK0,sK0) != X1_40 ),
% 1.02/0.93      inference(instantiation,[status(thm)],[c_525]) ).
% 1.02/0.93  
% 1.02/0.93  cnf(c_770,plain,
% 1.02/0.93      ( k3_partfun1(sK1,sK0,sK0) != sK1
% 1.02/0.93      | sK1 = k3_partfun1(sK1,sK0,sK0)
% 1.02/0.93      | sK1 != sK1 ),
% 1.02/0.93      inference(instantiation,[status(thm)],[c_769]) ).
% 1.02/0.93  
% 1.02/0.93  cnf(c_833,plain,
% 1.02/0.93      ( k1_xboole_0 = sK0 ),
% 1.02/0.93      inference(global_propositional_subsumption,
% 1.02/0.93                [status(thm)],
% 1.02/0.93                [c_670,c_6,c_543,c_546,c_515,c_552,c_555,c_729,c_742,c_770]) ).
% 1.02/0.93  
% 1.02/0.93  cnf(c_672,plain,
% 1.02/0.93      ( k5_partfun1(X0_43,X1_43,sK1) = k1_enumset1(sK1,sK1,sK1)
% 1.02/0.93      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0_43,X1_43))) != iProver_top
% 1.02/0.93      | v1_partfun1(sK1,X0_43) != iProver_top ),
% 1.02/0.93      inference(predicate_to_equality,[status(thm)],[c_513]) ).
% 1.02/0.93  
% 1.02/0.93  cnf(c_813,plain,
% 1.02/0.93      ( k5_partfun1(sK0,sK0,sK1) = k1_enumset1(sK1,sK1,sK1)
% 1.02/0.93      | v1_partfun1(sK1,sK0) != iProver_top ),
% 1.02/0.93      inference(superposition,[status(thm)],[c_668,c_672]) ).
% 1.02/0.93  
% 1.02/0.93  cnf(c_11,plain,
% 1.02/0.93      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 1.02/0.93      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 1.02/0.93  
% 1.02/0.93  cnf(c_554,plain,
% 1.02/0.93      ( k5_partfun1(X0_43,X1_43,sK1) = k1_enumset1(sK1,sK1,sK1)
% 1.02/0.93      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0_43,X1_43))) != iProver_top
% 1.02/0.93      | v1_partfun1(sK1,X0_43) != iProver_top ),
% 1.02/0.93      inference(predicate_to_equality,[status(thm)],[c_513]) ).
% 1.02/0.93  
% 1.02/0.93  cnf(c_556,plain,
% 1.02/0.93      ( k5_partfun1(sK0,sK0,sK1) = k1_enumset1(sK1,sK1,sK1)
% 1.02/0.93      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 1.02/0.93      | v1_partfun1(sK1,sK0) != iProver_top ),
% 1.02/0.93      inference(instantiation,[status(thm)],[c_554]) ).
% 1.02/0.93  
% 1.02/0.93  cnf(c_816,plain,
% 1.02/0.93      ( v1_partfun1(sK1,sK0) != iProver_top ),
% 1.02/0.93      inference(global_propositional_subsumption,
% 1.02/0.93                [status(thm)],
% 1.02/0.93                [c_813,c_11,c_556,c_742]) ).
% 1.02/0.93  
% 1.02/0.93  cnf(c_836,plain,
% 1.02/0.93      ( v1_partfun1(sK1,k1_xboole_0) != iProver_top ),
% 1.02/0.93      inference(demodulation,[status(thm)],[c_833,c_816]) ).
% 1.02/0.93  
% 1.02/0.93  cnf(c_0,plain,
% 1.02/0.93      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 1.02/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 1.02/0.93      | v1_partfun1(k3_partfun1(X0,k1_xboole_0,X1),k1_xboole_0)
% 1.02/0.93      | ~ v1_funct_1(X0) ),
% 1.02/0.93      inference(cnf_transformation,[],[f34]) ).
% 1.02/0.93  
% 1.02/0.93  cnf(c_95,plain,
% 1.02/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 1.02/0.93      | v1_partfun1(k3_partfun1(X0,k1_xboole_0,X1),k1_xboole_0)
% 1.02/0.93      | ~ v1_funct_1(X0)
% 1.02/0.93      | sK0 != X1
% 1.02/0.93      | sK0 != k1_xboole_0
% 1.02/0.93      | sK1 != X0 ),
% 1.02/0.93      inference(resolution_lifted,[status(thm)],[c_0,c_7]) ).
% 1.02/0.93  
% 1.02/0.93  cnf(c_96,plain,
% 1.02/0.93      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
% 1.02/0.93      | v1_partfun1(k3_partfun1(sK1,k1_xboole_0,sK0),k1_xboole_0)
% 1.02/0.93      | ~ v1_funct_1(sK1)
% 1.02/0.93      | sK0 != k1_xboole_0 ),
% 1.02/0.93      inference(unflattening,[status(thm)],[c_95]) ).
% 1.02/0.93  
% 1.02/0.93  cnf(c_98,plain,
% 1.02/0.93      ( v1_partfun1(k3_partfun1(sK1,k1_xboole_0,sK0),k1_xboole_0)
% 1.02/0.93      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
% 1.02/0.93      | sK0 != k1_xboole_0 ),
% 1.02/0.93      inference(global_propositional_subsumption,[status(thm)],[c_96,c_8]) ).
% 1.02/0.93  
% 1.02/0.93  cnf(c_99,plain,
% 1.02/0.93      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
% 1.02/0.93      | v1_partfun1(k3_partfun1(sK1,k1_xboole_0,sK0),k1_xboole_0)
% 1.02/0.93      | sK0 != k1_xboole_0 ),
% 1.02/0.93      inference(renaming,[status(thm)],[c_98]) ).
% 1.02/0.93  
% 1.02/0.93  cnf(c_516,plain,
% 1.02/0.93      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
% 1.02/0.93      | v1_partfun1(k3_partfun1(sK1,k1_xboole_0,sK0),k1_xboole_0)
% 1.02/0.93      | sK0 != k1_xboole_0 ),
% 1.02/0.93      inference(subtyping,[status(esa)],[c_99]) ).
% 1.02/0.93  
% 1.02/0.93  cnf(c_669,plain,
% 1.02/0.93      ( sK0 != k1_xboole_0
% 1.02/0.93      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
% 1.02/0.93      | v1_partfun1(k3_partfun1(sK1,k1_xboole_0,sK0),k1_xboole_0) = iProver_top ),
% 1.02/0.93      inference(predicate_to_equality,[status(thm)],[c_516]) ).
% 1.02/0.93  
% 1.02/0.93  cnf(c_100,plain,
% 1.02/0.93      ( sK0 != k1_xboole_0
% 1.02/0.93      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
% 1.02/0.93      | v1_partfun1(k3_partfun1(sK1,k1_xboole_0,sK0),k1_xboole_0) = iProver_top ),
% 1.02/0.93      inference(predicate_to_equality,[status(thm)],[c_99]) ).
% 1.02/0.93  
% 1.02/0.93  cnf(c_2,plain,
% 1.02/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.02/0.93      | v1_partfun1(X0,X1)
% 1.02/0.93      | ~ v1_funct_1(X0)
% 1.02/0.93      | k5_partfun1(X1,X2,X0) != k1_enumset1(X0,X0,X0) ),
% 1.02/0.93      inference(cnf_transformation,[],[f31]) ).
% 1.02/0.93  
% 1.02/0.93  cnf(c_160,plain,
% 1.02/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.02/0.93      | v1_partfun1(X0,X1)
% 1.02/0.93      | k5_partfun1(X1,X2,X0) != k1_enumset1(X0,X0,X0)
% 1.02/0.93      | sK1 != X0 ),
% 1.02/0.93      inference(resolution_lifted,[status(thm)],[c_2,c_8]) ).
% 1.02/0.93  
% 1.02/0.93  cnf(c_161,plain,
% 1.02/0.93      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.02/0.93      | v1_partfun1(sK1,X0)
% 1.02/0.93      | k5_partfun1(X0,X1,sK1) != k1_enumset1(sK1,sK1,sK1) ),
% 1.02/0.93      inference(unflattening,[status(thm)],[c_160]) ).
% 1.02/0.93  
% 1.02/0.93  cnf(c_163,plain,
% 1.02/0.93      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 1.02/0.93      | v1_partfun1(sK1,sK0)
% 1.02/0.93      | k5_partfun1(sK0,sK0,sK1) != k1_enumset1(sK1,sK1,sK1) ),
% 1.02/0.93      inference(instantiation,[status(thm)],[c_161]) ).
% 1.02/0.93  
% 1.02/0.93  cnf(c_299,plain,
% 1.02/0.93      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.02/0.93      | k5_partfun1(X0,X1,sK1) = k1_enumset1(sK1,sK1,sK1)
% 1.02/0.93      | k3_partfun1(sK1,sK0,sK0) != sK1
% 1.02/0.93      | sK0 != X0
% 1.02/0.93      | sK0 = k1_xboole_0 ),
% 1.02/0.93      inference(resolution_lifted,[status(thm)],[c_115,c_146]) ).
% 1.02/0.93  
% 1.02/0.93  cnf(c_300,plain,
% 1.02/0.93      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
% 1.02/0.93      | k5_partfun1(sK0,X0,sK1) = k1_enumset1(sK1,sK1,sK1)
% 1.02/0.93      | k3_partfun1(sK1,sK0,sK0) != sK1
% 1.02/0.93      | sK0 = k1_xboole_0 ),
% 1.02/0.93      inference(unflattening,[status(thm)],[c_299]) ).
% 1.02/0.93  
% 1.02/0.93  cnf(c_136,plain,
% 1.02/0.93      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 1.02/0.93      | k3_partfun1(sK1,sK0,sK0) = sK1 ),
% 1.02/0.93      inference(instantiation,[status(thm)],[c_134]) ).
% 1.02/0.93  
% 1.02/0.93  cnf(c_304,plain,
% 1.02/0.93      ( k5_partfun1(sK0,X0,sK1) = k1_enumset1(sK1,sK1,sK1)
% 1.02/0.93      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
% 1.02/0.93      | sK0 = k1_xboole_0 ),
% 1.02/0.93      inference(global_propositional_subsumption,
% 1.02/0.93                [status(thm)],
% 1.02/0.93                [c_300,c_6,c_136]) ).
% 1.02/0.93  
% 1.02/0.93  cnf(c_305,plain,
% 1.02/0.93      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
% 1.02/0.93      | k5_partfun1(sK0,X0,sK1) = k1_enumset1(sK1,sK1,sK1)
% 1.02/0.93      | sK0 = k1_xboole_0 ),
% 1.02/0.93      inference(renaming,[status(thm)],[c_304]) ).
% 1.02/0.93  
% 1.02/0.93  cnf(c_307,plain,
% 1.02/0.93      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 1.02/0.93      | k5_partfun1(sK0,sK0,sK1) = k1_enumset1(sK1,sK1,sK1)
% 1.02/0.93      | sK0 = k1_xboole_0 ),
% 1.02/0.93      inference(instantiation,[status(thm)],[c_305]) ).
% 1.02/0.93  
% 1.02/0.93  cnf(c_779,plain,
% 1.02/0.93      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
% 1.02/0.93      | v1_partfun1(k3_partfun1(sK1,k1_xboole_0,sK0),k1_xboole_0) = iProver_top ),
% 1.02/0.93      inference(global_propositional_subsumption,
% 1.02/0.93                [status(thm)],
% 1.02/0.93                [c_669,c_6,c_100,c_163,c_307,c_555,c_742]) ).
% 1.02/0.93  
% 1.02/0.93  cnf(c_837,plain,
% 1.02/0.93      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 1.02/0.93      | v1_partfun1(k3_partfun1(sK1,k1_xboole_0,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 1.02/0.93      inference(demodulation,[status(thm)],[c_833,c_779]) ).
% 1.02/0.93  
% 1.02/0.93  cnf(c_839,plain,
% 1.02/0.93      ( k3_partfun1(sK1,k1_xboole_0,k1_xboole_0) = sK1 ),
% 1.02/0.93      inference(demodulation,[status(thm)],[c_833,c_740]) ).
% 1.02/0.93  
% 1.02/0.93  cnf(c_847,plain,
% 1.02/0.93      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 1.02/0.93      | v1_partfun1(sK1,k1_xboole_0) = iProver_top ),
% 1.02/0.93      inference(light_normalisation,[status(thm)],[c_837,c_839]) ).
% 1.02/0.93  
% 1.02/0.93  cnf(c_840,plain,
% 1.02/0.93      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 1.02/0.93      inference(demodulation,[status(thm)],[c_833,c_668]) ).
% 1.02/0.93  
% 1.02/0.93  cnf(c_850,plain,
% 1.02/0.93      ( v1_partfun1(sK1,k1_xboole_0) = iProver_top ),
% 1.02/0.93      inference(forward_subsumption_resolution,[status(thm)],[c_847,c_840]) ).
% 1.02/0.93  
% 1.02/0.93  cnf(c_853,plain,
% 1.02/0.93      ( $false ),
% 1.02/0.93      inference(forward_subsumption_resolution,[status(thm)],[c_836,c_850]) ).
% 1.02/0.93  
% 1.02/0.93  
% 1.02/0.93  % SZS output end CNFRefutation for theBenchmark.p
% 1.02/0.93  
% 1.02/0.93  ------                               Statistics
% 1.02/0.93  
% 1.02/0.93  ------ General
% 1.02/0.93  
% 1.02/0.93  abstr_ref_over_cycles:                  0
% 1.02/0.93  abstr_ref_under_cycles:                 0
% 1.02/0.93  gc_basic_clause_elim:                   0
% 1.02/0.93  forced_gc_time:                         0
% 1.02/0.93  parsing_time:                           0.009
% 1.02/0.93  unif_index_cands_time:                  0.
% 1.02/0.93  unif_index_add_time:                    0.
% 1.02/0.93  orderings_time:                         0.
% 1.02/0.93  out_proof_time:                         0.009
% 1.02/0.93  total_time:                             0.059
% 1.02/0.93  num_of_symbols:                         45
% 1.02/0.93  num_of_terms:                           754
% 1.02/0.93  
% 1.02/0.93  ------ Preprocessing
% 1.02/0.93  
% 1.02/0.93  num_of_splits:                          0
% 1.02/0.93  num_of_split_atoms:                     0
% 1.02/0.93  num_of_reused_defs:                     0
% 1.02/0.93  num_eq_ax_congr_red:                    0
% 1.02/0.93  num_of_sem_filtered_clauses:            1
% 1.02/0.93  num_of_subtypes:                        5
% 1.02/0.93  monotx_restored_types:                  0
% 1.02/0.93  sat_num_of_epr_types:                   0
% 1.02/0.93  sat_num_of_non_cyclic_types:            0
% 1.02/0.93  sat_guarded_non_collapsed_types:        0
% 1.02/0.93  num_pure_diseq_elim:                    0
% 1.02/0.93  simp_replaced_by:                       0
% 1.02/0.93  res_preprocessed:                       61
% 1.02/0.93  prep_upred:                             0
% 1.02/0.93  prep_unflattend:                        12
% 1.02/0.93  smt_new_axioms:                         0
% 1.02/0.93  pred_elim_cands:                        2
% 1.02/0.93  pred_elim:                              2
% 1.02/0.93  pred_elim_cl:                           2
% 1.02/0.93  pred_elim_cycles:                       6
% 1.02/0.93  merged_defs:                            0
% 1.02/0.93  merged_defs_ncl:                        0
% 1.02/0.93  bin_hyper_res:                          0
% 1.02/0.93  prep_cycles:                            4
% 1.02/0.93  pred_elim_time:                         0.008
% 1.02/0.93  splitting_time:                         0.
% 1.02/0.93  sem_filter_time:                        0.
% 1.02/0.93  monotx_time:                            0.
% 1.02/0.93  subtype_inf_time:                       0.
% 1.02/0.93  
% 1.02/0.93  ------ Problem properties
% 1.02/0.93  
% 1.02/0.93  clauses:                                7
% 1.02/0.93  conjectures:                            2
% 1.02/0.93  epr:                                    0
% 1.02/0.93  horn:                                   6
% 1.02/0.93  ground:                                 4
% 1.02/0.93  unary:                                  2
% 1.02/0.93  binary:                                 2
% 1.02/0.93  lits:                                   15
% 1.02/0.93  lits_eq:                                6
% 1.02/0.93  fd_pure:                                0
% 1.02/0.93  fd_pseudo:                              0
% 1.02/0.93  fd_cond:                                0
% 1.02/0.93  fd_pseudo_cond:                         0
% 1.02/0.93  ac_symbols:                             0
% 1.02/0.93  
% 1.02/0.93  ------ Propositional Solver
% 1.02/0.93  
% 1.02/0.93  prop_solver_calls:                      25
% 1.02/0.93  prop_fast_solver_calls:                 403
% 1.02/0.93  smt_solver_calls:                       0
% 1.02/0.93  smt_fast_solver_calls:                  0
% 1.02/0.93  prop_num_of_clauses:                    183
% 1.02/0.93  prop_preprocess_simplified:             1358
% 1.02/0.93  prop_fo_subsumed:                       9
% 1.02/0.93  prop_solver_time:                       0.
% 1.02/0.93  smt_solver_time:                        0.
% 1.02/0.93  smt_fast_solver_time:                   0.
% 1.02/0.93  prop_fast_solver_time:                  0.
% 1.02/0.93  prop_unsat_core_time:                   0.
% 1.02/0.93  
% 1.02/0.93  ------ QBF
% 1.02/0.93  
% 1.02/0.93  qbf_q_res:                              0
% 1.02/0.93  qbf_num_tautologies:                    0
% 1.02/0.93  qbf_prep_cycles:                        0
% 1.02/0.93  
% 1.02/0.93  ------ BMC1
% 1.02/0.93  
% 1.02/0.93  bmc1_current_bound:                     -1
% 1.02/0.93  bmc1_last_solved_bound:                 -1
% 1.02/0.93  bmc1_unsat_core_size:                   -1
% 1.02/0.93  bmc1_unsat_core_parents_size:           -1
% 1.02/0.93  bmc1_merge_next_fun:                    0
% 1.02/0.93  bmc1_unsat_core_clauses_time:           0.
% 1.02/0.93  
% 1.02/0.93  ------ Instantiation
% 1.02/0.93  
% 1.02/0.93  inst_num_of_clauses:                    52
% 1.02/0.93  inst_num_in_passive:                    2
% 1.02/0.93  inst_num_in_active:                     44
% 1.02/0.93  inst_num_in_unprocessed:                6
% 1.02/0.93  inst_num_of_loops:                      50
% 1.02/0.93  inst_num_of_learning_restarts:          0
% 1.02/0.93  inst_num_moves_active_passive:          4
% 1.02/0.93  inst_lit_activity:                      0
% 1.02/0.93  inst_lit_activity_moves:                0
% 1.02/0.93  inst_num_tautologies:                   0
% 1.02/0.93  inst_num_prop_implied:                  0
% 1.02/0.93  inst_num_existing_simplified:           0
% 1.02/0.93  inst_num_eq_res_simplified:             0
% 1.02/0.93  inst_num_child_elim:                    0
% 1.02/0.93  inst_num_of_dismatching_blockings:      1
% 1.02/0.93  inst_num_of_non_proper_insts:           24
% 1.02/0.93  inst_num_of_duplicates:                 0
% 1.02/0.93  inst_inst_num_from_inst_to_res:         0
% 1.02/0.93  inst_dismatching_checking_time:         0.
% 1.02/0.93  
% 1.02/0.93  ------ Resolution
% 1.02/0.93  
% 1.02/0.93  res_num_of_clauses:                     0
% 1.02/0.93  res_num_in_passive:                     0
% 1.02/0.93  res_num_in_active:                      0
% 1.02/0.93  res_num_of_loops:                       65
% 1.02/0.93  res_forward_subset_subsumed:            1
% 1.02/0.93  res_backward_subset_subsumed:           0
% 1.02/0.93  res_forward_subsumed:                   0
% 1.02/0.93  res_backward_subsumed:                  0
% 1.02/0.93  res_forward_subsumption_resolution:     1
% 1.02/0.93  res_backward_subsumption_resolution:    0
% 1.02/0.93  res_clause_to_clause_subsumption:       14
% 1.02/0.93  res_orphan_elimination:                 0
% 1.02/0.93  res_tautology_del:                      5
% 1.02/0.93  res_num_eq_res_simplified:              0
% 1.02/0.93  res_num_sel_changes:                    0
% 1.02/0.93  res_moves_from_active_to_pass:          0
% 1.02/0.93  
% 1.02/0.93  ------ Superposition
% 1.02/0.93  
% 1.02/0.93  sup_time_total:                         0.
% 1.02/0.93  sup_time_generating:                    0.
% 1.02/0.93  sup_time_sim_full:                      0.
% 1.02/0.93  sup_time_sim_immed:                     0.
% 1.02/0.93  
% 1.02/0.93  sup_num_of_clauses:                     4
% 1.02/0.93  sup_num_in_active:                      2
% 1.02/0.93  sup_num_in_passive:                     2
% 1.02/0.93  sup_num_of_loops:                       8
% 1.02/0.93  sup_fw_superposition:                   2
% 1.02/0.93  sup_bw_superposition:                   0
% 1.02/0.93  sup_immediate_simplified:               0
% 1.02/0.93  sup_given_eliminated:                   0
% 1.02/0.93  comparisons_done:                       0
% 1.02/0.93  comparisons_avoided:                    0
% 1.02/0.93  
% 1.02/0.93  ------ Simplifications
% 1.02/0.93  
% 1.02/0.93  
% 1.02/0.93  sim_fw_subset_subsumed:                 0
% 1.02/0.93  sim_bw_subset_subsumed:                 0
% 1.02/0.93  sim_fw_subsumed:                        0
% 1.02/0.93  sim_bw_subsumed:                        0
% 1.02/0.93  sim_fw_subsumption_res:                 2
% 1.02/0.93  sim_bw_subsumption_res:                 0
% 1.02/0.93  sim_tautology_del:                      0
% 1.02/0.93  sim_eq_tautology_del:                   0
% 1.02/0.93  sim_eq_res_simp:                        0
% 1.02/0.93  sim_fw_demodulated:                     0
% 1.02/0.93  sim_bw_demodulated:                     6
% 1.02/0.93  sim_light_normalised:                   1
% 1.02/0.93  sim_joinable_taut:                      0
% 1.02/0.93  sim_joinable_simp:                      0
% 1.02/0.93  sim_ac_normalised:                      0
% 1.02/0.93  sim_smt_subsumption:                    0
% 1.02/0.93  
%------------------------------------------------------------------------------
