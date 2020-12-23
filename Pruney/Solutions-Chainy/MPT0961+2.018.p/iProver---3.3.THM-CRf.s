%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:59:58 EST 2020

% Result     : Theorem 1.87s
% Output     : CNFRefutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 314 expanded)
%              Number of clauses        :   67 ( 128 expanded)
%              Number of leaves         :   13 (  58 expanded)
%              Depth                    :   22
%              Number of atoms          :  296 (1022 expanded)
%              Number of equality atoms :  179 ( 482 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f38,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f41,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f24])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f55,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f32])).

fof(f9,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f5,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f54,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f33])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f11,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
          & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
          & v1_funct_1(X0) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f22,plain,(
    ? [X0] :
      ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        | ~ v1_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f23,plain,(
    ? [X0] :
      ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        | ~ v1_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f28,plain,
    ( ? [X0] :
        ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
          | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
          | ~ v1_funct_1(X0) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
        | ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
        | ~ v1_funct_1(sK0) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
      | ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
      | ~ v1_funct_1(sK0) )
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f28])).

fof(f53,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
    | ~ v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f52,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f51,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f1,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f30,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f59,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f48])).

cnf(c_11,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_8,plain,
    ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1044,plain,
    ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1700,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0)) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_1044])).

cnf(c_12,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1709,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1700,c_12])).

cnf(c_2,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1710,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1709,c_2])).

cnf(c_13,plain,
    ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_7,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_57,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_59,plain,
    ( v1_relat_1(k6_relat_1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_57])).

cnf(c_3,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_67,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_68,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_672,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1183,plain,
    ( v1_relat_1(X0)
    | ~ v1_relat_1(k6_relat_1(X1))
    | X0 != k6_relat_1(X1) ),
    inference(instantiation,[status(thm)],[c_672])).

cnf(c_1184,plain,
    ( X0 != k6_relat_1(X1)
    | v1_relat_1(X0) = iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1183])).

cnf(c_1186,plain,
    ( k1_xboole_0 != k6_relat_1(k1_xboole_0)
    | v1_relat_1(k6_relat_1(k1_xboole_0)) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1184])).

cnf(c_667,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1278,plain,
    ( X0 != X1
    | X0 = k6_relat_1(X2)
    | k6_relat_1(X2) != X1 ),
    inference(instantiation,[status(thm)],[c_667])).

cnf(c_1279,plain,
    ( k6_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k6_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1278])).

cnf(c_1807,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1710,c_13,c_59,c_67,c_68,c_1186,c_1279])).

cnf(c_4,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1047,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1043,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1902,plain,
    ( k1_relset_1(X0,k1_xboole_0,X1) = k1_relat_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_1043])).

cnf(c_1926,plain,
    ( k1_relset_1(X0,k1_xboole_0,X1) = k1_relat_1(X1)
    | r1_tarski(X1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1047,c_1902])).

cnf(c_2245,plain,
    ( k1_relset_1(X0,k1_xboole_0,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1807,c_1926])).

cnf(c_2246,plain,
    ( k1_relset_1(X0,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2245,c_12])).

cnf(c_2247,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2246])).

cnf(c_18,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_21,negated_conjecture,
    ( ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
    | ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | ~ v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_22,negated_conjecture,
    ( v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_111,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_21,c_22])).

cnf(c_112,negated_conjecture,
    ( ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
    | ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) ),
    inference(renaming,[status(thm)],[c_111])).

cnf(c_504,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | k1_relset_1(X1,X2,X0) != X1
    | k2_relat_1(sK0) != X2
    | k1_relat_1(sK0) != X1
    | sK0 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_112])).

cnf(c_505,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0) != k1_relat_1(sK0)
    | k1_xboole_0 = k2_relat_1(sK0) ),
    inference(unflattening,[status(thm)],[c_504])).

cnf(c_513,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | k1_xboole_0 = k2_relat_1(sK0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_505,c_14])).

cnf(c_1036,plain,
    ( k1_xboole_0 = k2_relat_1(sK0)
    | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_513])).

cnf(c_1504,plain,
    ( k2_relat_1(sK0) = k1_xboole_0
    | r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1047,c_1036])).

cnf(c_23,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_24,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1170,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))
    | ~ v1_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1171,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) = iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1170])).

cnf(c_1511,plain,
    ( k2_relat_1(sK0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1504,c_24,c_1171])).

cnf(c_1701,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0)) = iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1511,c_1044])).

cnf(c_1704,plain,
    ( r1_tarski(sK0,k1_xboole_0) = iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1701,c_1])).

cnf(c_1720,plain,
    ( r1_tarski(sK0,k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1704,c_24])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_1048,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1725,plain,
    ( sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1720,c_1048])).

cnf(c_17,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_488,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | k2_relat_1(sK0) != X1
    | k1_relat_1(sK0) != k1_xboole_0
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_112])).

cnf(c_489,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK0))))
    | k1_relset_1(k1_xboole_0,k2_relat_1(sK0),sK0) != k1_xboole_0
    | k1_relat_1(sK0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_488])).

cnf(c_1037,plain,
    ( k1_relset_1(k1_xboole_0,k2_relat_1(sK0),sK0) != k1_xboole_0
    | k1_relat_1(sK0) != k1_xboole_0
    | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) != iProver_top
    | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK0)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_489])).

cnf(c_1111,plain,
    ( k1_relset_1(k1_xboole_0,k2_relat_1(sK0),sK0) != k1_xboole_0
    | k1_relat_1(sK0) != k1_xboole_0
    | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) != iProver_top
    | m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1037,c_2])).

cnf(c_1515,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK0) != k1_xboole_0
    | k1_relat_1(sK0) != k1_xboole_0
    | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0))) != iProver_top
    | m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1511,c_1111])).

cnf(c_1521,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK0) != k1_xboole_0
    | k1_relat_1(sK0) != k1_xboole_0
    | m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1515,c_1])).

cnf(c_2050,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1725,c_1521])).

cnf(c_2056,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2050,c_12])).

cnf(c_2057,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2056])).

cnf(c_64,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_66,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_64])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2247,c_2057,c_1710,c_1279,c_1186,c_68,c_67,c_66,c_59,c_13])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:05:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 1.87/1.02  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.02  
% 1.87/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.87/1.02  
% 1.87/1.02  ------  iProver source info
% 1.87/1.02  
% 1.87/1.02  git: date: 2020-06-30 10:37:57 +0100
% 1.87/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.87/1.02  git: non_committed_changes: false
% 1.87/1.02  git: last_make_outside_of_git: false
% 1.87/1.02  
% 1.87/1.02  ------ 
% 1.87/1.02  
% 1.87/1.02  ------ Input Options
% 1.87/1.02  
% 1.87/1.02  --out_options                           all
% 1.87/1.02  --tptp_safe_out                         true
% 1.87/1.02  --problem_path                          ""
% 1.87/1.02  --include_path                          ""
% 1.87/1.02  --clausifier                            res/vclausify_rel
% 1.87/1.02  --clausifier_options                    --mode clausify
% 1.87/1.02  --stdin                                 false
% 1.87/1.02  --stats_out                             all
% 1.87/1.02  
% 1.87/1.02  ------ General Options
% 1.87/1.02  
% 1.87/1.02  --fof                                   false
% 1.87/1.02  --time_out_real                         305.
% 1.87/1.02  --time_out_virtual                      -1.
% 1.87/1.02  --symbol_type_check                     false
% 1.87/1.02  --clausify_out                          false
% 1.87/1.02  --sig_cnt_out                           false
% 1.87/1.02  --trig_cnt_out                          false
% 1.87/1.02  --trig_cnt_out_tolerance                1.
% 1.87/1.02  --trig_cnt_out_sk_spl                   false
% 1.87/1.02  --abstr_cl_out                          false
% 1.87/1.02  
% 1.87/1.02  ------ Global Options
% 1.87/1.02  
% 1.87/1.02  --schedule                              default
% 1.87/1.02  --add_important_lit                     false
% 1.87/1.02  --prop_solver_per_cl                    1000
% 1.87/1.02  --min_unsat_core                        false
% 1.87/1.02  --soft_assumptions                      false
% 1.87/1.02  --soft_lemma_size                       3
% 1.87/1.02  --prop_impl_unit_size                   0
% 1.87/1.02  --prop_impl_unit                        []
% 1.87/1.02  --share_sel_clauses                     true
% 1.87/1.02  --reset_solvers                         false
% 1.87/1.02  --bc_imp_inh                            [conj_cone]
% 1.87/1.02  --conj_cone_tolerance                   3.
% 1.87/1.02  --extra_neg_conj                        none
% 1.87/1.02  --large_theory_mode                     true
% 1.87/1.02  --prolific_symb_bound                   200
% 1.87/1.02  --lt_threshold                          2000
% 1.87/1.02  --clause_weak_htbl                      true
% 1.87/1.02  --gc_record_bc_elim                     false
% 1.87/1.02  
% 1.87/1.02  ------ Preprocessing Options
% 1.87/1.02  
% 1.87/1.02  --preprocessing_flag                    true
% 1.87/1.02  --time_out_prep_mult                    0.1
% 1.87/1.02  --splitting_mode                        input
% 1.87/1.02  --splitting_grd                         true
% 1.87/1.02  --splitting_cvd                         false
% 1.87/1.02  --splitting_cvd_svl                     false
% 1.87/1.02  --splitting_nvd                         32
% 1.87/1.02  --sub_typing                            true
% 1.87/1.02  --prep_gs_sim                           true
% 1.87/1.02  --prep_unflatten                        true
% 1.87/1.02  --prep_res_sim                          true
% 1.87/1.02  --prep_upred                            true
% 1.87/1.02  --prep_sem_filter                       exhaustive
% 1.87/1.02  --prep_sem_filter_out                   false
% 1.87/1.02  --pred_elim                             true
% 1.87/1.02  --res_sim_input                         true
% 1.87/1.02  --eq_ax_congr_red                       true
% 1.87/1.02  --pure_diseq_elim                       true
% 1.87/1.02  --brand_transform                       false
% 1.87/1.02  --non_eq_to_eq                          false
% 1.87/1.02  --prep_def_merge                        true
% 1.87/1.02  --prep_def_merge_prop_impl              false
% 1.87/1.02  --prep_def_merge_mbd                    true
% 1.87/1.02  --prep_def_merge_tr_red                 false
% 1.87/1.02  --prep_def_merge_tr_cl                  false
% 1.87/1.02  --smt_preprocessing                     true
% 1.87/1.02  --smt_ac_axioms                         fast
% 1.87/1.02  --preprocessed_out                      false
% 1.87/1.02  --preprocessed_stats                    false
% 1.87/1.02  
% 1.87/1.02  ------ Abstraction refinement Options
% 1.87/1.02  
% 1.87/1.02  --abstr_ref                             []
% 1.87/1.02  --abstr_ref_prep                        false
% 1.87/1.02  --abstr_ref_until_sat                   false
% 1.87/1.02  --abstr_ref_sig_restrict                funpre
% 1.87/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 1.87/1.02  --abstr_ref_under                       []
% 1.87/1.02  
% 1.87/1.02  ------ SAT Options
% 1.87/1.02  
% 1.87/1.02  --sat_mode                              false
% 1.87/1.02  --sat_fm_restart_options                ""
% 1.87/1.02  --sat_gr_def                            false
% 1.87/1.02  --sat_epr_types                         true
% 1.87/1.02  --sat_non_cyclic_types                  false
% 1.87/1.02  --sat_finite_models                     false
% 1.87/1.02  --sat_fm_lemmas                         false
% 1.87/1.02  --sat_fm_prep                           false
% 1.87/1.02  --sat_fm_uc_incr                        true
% 1.87/1.02  --sat_out_model                         small
% 1.87/1.02  --sat_out_clauses                       false
% 1.87/1.02  
% 1.87/1.02  ------ QBF Options
% 1.87/1.02  
% 1.87/1.02  --qbf_mode                              false
% 1.87/1.02  --qbf_elim_univ                         false
% 1.87/1.02  --qbf_dom_inst                          none
% 1.87/1.02  --qbf_dom_pre_inst                      false
% 1.87/1.02  --qbf_sk_in                             false
% 1.87/1.02  --qbf_pred_elim                         true
% 1.87/1.02  --qbf_split                             512
% 1.87/1.02  
% 1.87/1.02  ------ BMC1 Options
% 1.87/1.02  
% 1.87/1.02  --bmc1_incremental                      false
% 1.87/1.02  --bmc1_axioms                           reachable_all
% 1.87/1.02  --bmc1_min_bound                        0
% 1.87/1.02  --bmc1_max_bound                        -1
% 1.87/1.02  --bmc1_max_bound_default                -1
% 1.87/1.02  --bmc1_symbol_reachability              true
% 1.87/1.02  --bmc1_property_lemmas                  false
% 1.87/1.02  --bmc1_k_induction                      false
% 1.87/1.02  --bmc1_non_equiv_states                 false
% 1.87/1.02  --bmc1_deadlock                         false
% 1.87/1.02  --bmc1_ucm                              false
% 1.87/1.02  --bmc1_add_unsat_core                   none
% 1.87/1.02  --bmc1_unsat_core_children              false
% 1.87/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 1.87/1.02  --bmc1_out_stat                         full
% 1.87/1.02  --bmc1_ground_init                      false
% 1.87/1.02  --bmc1_pre_inst_next_state              false
% 1.87/1.02  --bmc1_pre_inst_state                   false
% 1.87/1.02  --bmc1_pre_inst_reach_state             false
% 1.87/1.02  --bmc1_out_unsat_core                   false
% 1.87/1.02  --bmc1_aig_witness_out                  false
% 1.87/1.02  --bmc1_verbose                          false
% 1.87/1.02  --bmc1_dump_clauses_tptp                false
% 1.87/1.02  --bmc1_dump_unsat_core_tptp             false
% 1.87/1.02  --bmc1_dump_file                        -
% 1.87/1.02  --bmc1_ucm_expand_uc_limit              128
% 1.87/1.02  --bmc1_ucm_n_expand_iterations          6
% 1.87/1.02  --bmc1_ucm_extend_mode                  1
% 1.87/1.02  --bmc1_ucm_init_mode                    2
% 1.87/1.02  --bmc1_ucm_cone_mode                    none
% 1.87/1.02  --bmc1_ucm_reduced_relation_type        0
% 1.87/1.02  --bmc1_ucm_relax_model                  4
% 1.87/1.02  --bmc1_ucm_full_tr_after_sat            true
% 1.87/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 1.87/1.02  --bmc1_ucm_layered_model                none
% 1.87/1.02  --bmc1_ucm_max_lemma_size               10
% 1.87/1.02  
% 1.87/1.02  ------ AIG Options
% 1.87/1.02  
% 1.87/1.02  --aig_mode                              false
% 1.87/1.02  
% 1.87/1.02  ------ Instantiation Options
% 1.87/1.02  
% 1.87/1.02  --instantiation_flag                    true
% 1.87/1.02  --inst_sos_flag                         false
% 1.87/1.02  --inst_sos_phase                        true
% 1.87/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.87/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.87/1.02  --inst_lit_sel_side                     num_symb
% 1.87/1.02  --inst_solver_per_active                1400
% 1.87/1.02  --inst_solver_calls_frac                1.
% 1.87/1.02  --inst_passive_queue_type               priority_queues
% 1.87/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.87/1.02  --inst_passive_queues_freq              [25;2]
% 1.87/1.02  --inst_dismatching                      true
% 1.87/1.02  --inst_eager_unprocessed_to_passive     true
% 1.87/1.02  --inst_prop_sim_given                   true
% 1.87/1.02  --inst_prop_sim_new                     false
% 1.87/1.02  --inst_subs_new                         false
% 1.87/1.02  --inst_eq_res_simp                      false
% 1.87/1.02  --inst_subs_given                       false
% 1.87/1.02  --inst_orphan_elimination               true
% 1.87/1.02  --inst_learning_loop_flag               true
% 1.87/1.02  --inst_learning_start                   3000
% 1.87/1.02  --inst_learning_factor                  2
% 1.87/1.02  --inst_start_prop_sim_after_learn       3
% 1.87/1.02  --inst_sel_renew                        solver
% 1.87/1.02  --inst_lit_activity_flag                true
% 1.87/1.02  --inst_restr_to_given                   false
% 1.87/1.02  --inst_activity_threshold               500
% 1.87/1.02  --inst_out_proof                        true
% 1.87/1.02  
% 1.87/1.02  ------ Resolution Options
% 1.87/1.02  
% 1.87/1.02  --resolution_flag                       true
% 1.87/1.02  --res_lit_sel                           adaptive
% 1.87/1.02  --res_lit_sel_side                      none
% 1.87/1.02  --res_ordering                          kbo
% 1.87/1.02  --res_to_prop_solver                    active
% 1.87/1.02  --res_prop_simpl_new                    false
% 1.87/1.02  --res_prop_simpl_given                  true
% 1.87/1.02  --res_passive_queue_type                priority_queues
% 1.87/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.87/1.02  --res_passive_queues_freq               [15;5]
% 1.87/1.02  --res_forward_subs                      full
% 1.87/1.02  --res_backward_subs                     full
% 1.87/1.02  --res_forward_subs_resolution           true
% 1.87/1.02  --res_backward_subs_resolution          true
% 1.87/1.02  --res_orphan_elimination                true
% 1.87/1.02  --res_time_limit                        2.
% 1.87/1.02  --res_out_proof                         true
% 1.87/1.02  
% 1.87/1.02  ------ Superposition Options
% 1.87/1.02  
% 1.87/1.02  --superposition_flag                    true
% 1.87/1.02  --sup_passive_queue_type                priority_queues
% 1.87/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.87/1.02  --sup_passive_queues_freq               [8;1;4]
% 1.87/1.02  --demod_completeness_check              fast
% 1.87/1.02  --demod_use_ground                      true
% 1.87/1.02  --sup_to_prop_solver                    passive
% 1.87/1.02  --sup_prop_simpl_new                    true
% 1.87/1.02  --sup_prop_simpl_given                  true
% 1.87/1.02  --sup_fun_splitting                     false
% 1.87/1.02  --sup_smt_interval                      50000
% 1.87/1.02  
% 1.87/1.02  ------ Superposition Simplification Setup
% 1.87/1.02  
% 1.87/1.02  --sup_indices_passive                   []
% 1.87/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.87/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.87/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.87/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 1.87/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.87/1.02  --sup_full_bw                           [BwDemod]
% 1.87/1.02  --sup_immed_triv                        [TrivRules]
% 1.87/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.87/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.87/1.02  --sup_immed_bw_main                     []
% 1.87/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.87/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 1.87/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.87/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.87/1.02  
% 1.87/1.02  ------ Combination Options
% 1.87/1.02  
% 1.87/1.02  --comb_res_mult                         3
% 1.87/1.02  --comb_sup_mult                         2
% 1.87/1.02  --comb_inst_mult                        10
% 1.87/1.02  
% 1.87/1.02  ------ Debug Options
% 1.87/1.02  
% 1.87/1.02  --dbg_backtrace                         false
% 1.87/1.02  --dbg_dump_prop_clauses                 false
% 1.87/1.02  --dbg_dump_prop_clauses_file            -
% 1.87/1.02  --dbg_out_stat                          false
% 1.87/1.02  ------ Parsing...
% 1.87/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.87/1.02  
% 1.87/1.02  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 1.87/1.02  
% 1.87/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.87/1.02  
% 1.87/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.87/1.02  ------ Proving...
% 1.87/1.02  ------ Problem Properties 
% 1.87/1.02  
% 1.87/1.02  
% 1.87/1.02  clauses                                 19
% 1.87/1.02  conjectures                             1
% 1.87/1.02  EPR                                     3
% 1.87/1.02  Horn                                    18
% 1.87/1.02  unary                                   7
% 1.87/1.02  binary                                  6
% 1.87/1.02  lits                                    40
% 1.87/1.02  lits eq                                 16
% 1.87/1.02  fd_pure                                 0
% 1.87/1.02  fd_pseudo                               0
% 1.87/1.02  fd_cond                                 2
% 1.87/1.02  fd_pseudo_cond                          0
% 1.87/1.02  AC symbols                              0
% 1.87/1.02  
% 1.87/1.02  ------ Schedule dynamic 5 is on 
% 1.87/1.02  
% 1.87/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.87/1.02  
% 1.87/1.02  
% 1.87/1.02  ------ 
% 1.87/1.02  Current options:
% 1.87/1.02  ------ 
% 1.87/1.02  
% 1.87/1.02  ------ Input Options
% 1.87/1.02  
% 1.87/1.02  --out_options                           all
% 1.87/1.02  --tptp_safe_out                         true
% 1.87/1.02  --problem_path                          ""
% 1.87/1.02  --include_path                          ""
% 1.87/1.02  --clausifier                            res/vclausify_rel
% 1.87/1.02  --clausifier_options                    --mode clausify
% 1.87/1.02  --stdin                                 false
% 1.87/1.02  --stats_out                             all
% 1.87/1.02  
% 1.87/1.02  ------ General Options
% 1.87/1.02  
% 1.87/1.02  --fof                                   false
% 1.87/1.02  --time_out_real                         305.
% 1.87/1.02  --time_out_virtual                      -1.
% 1.87/1.02  --symbol_type_check                     false
% 1.87/1.02  --clausify_out                          false
% 1.87/1.02  --sig_cnt_out                           false
% 1.87/1.02  --trig_cnt_out                          false
% 1.87/1.02  --trig_cnt_out_tolerance                1.
% 1.87/1.02  --trig_cnt_out_sk_spl                   false
% 1.87/1.02  --abstr_cl_out                          false
% 1.87/1.02  
% 1.87/1.02  ------ Global Options
% 1.87/1.02  
% 1.87/1.02  --schedule                              default
% 1.87/1.02  --add_important_lit                     false
% 1.87/1.02  --prop_solver_per_cl                    1000
% 1.87/1.02  --min_unsat_core                        false
% 1.87/1.02  --soft_assumptions                      false
% 1.87/1.02  --soft_lemma_size                       3
% 1.87/1.02  --prop_impl_unit_size                   0
% 1.87/1.02  --prop_impl_unit                        []
% 1.87/1.02  --share_sel_clauses                     true
% 1.87/1.02  --reset_solvers                         false
% 1.87/1.02  --bc_imp_inh                            [conj_cone]
% 1.87/1.02  --conj_cone_tolerance                   3.
% 1.87/1.02  --extra_neg_conj                        none
% 1.87/1.02  --large_theory_mode                     true
% 1.87/1.02  --prolific_symb_bound                   200
% 1.87/1.02  --lt_threshold                          2000
% 1.87/1.02  --clause_weak_htbl                      true
% 1.87/1.02  --gc_record_bc_elim                     false
% 1.87/1.02  
% 1.87/1.02  ------ Preprocessing Options
% 1.87/1.02  
% 1.87/1.02  --preprocessing_flag                    true
% 1.87/1.02  --time_out_prep_mult                    0.1
% 1.87/1.02  --splitting_mode                        input
% 1.87/1.02  --splitting_grd                         true
% 1.87/1.02  --splitting_cvd                         false
% 1.87/1.02  --splitting_cvd_svl                     false
% 1.87/1.02  --splitting_nvd                         32
% 1.87/1.02  --sub_typing                            true
% 1.87/1.02  --prep_gs_sim                           true
% 1.87/1.02  --prep_unflatten                        true
% 1.87/1.02  --prep_res_sim                          true
% 1.87/1.02  --prep_upred                            true
% 1.87/1.02  --prep_sem_filter                       exhaustive
% 1.87/1.02  --prep_sem_filter_out                   false
% 1.87/1.02  --pred_elim                             true
% 1.87/1.02  --res_sim_input                         true
% 1.87/1.02  --eq_ax_congr_red                       true
% 1.87/1.02  --pure_diseq_elim                       true
% 1.87/1.02  --brand_transform                       false
% 1.87/1.02  --non_eq_to_eq                          false
% 1.87/1.02  --prep_def_merge                        true
% 1.87/1.02  --prep_def_merge_prop_impl              false
% 1.87/1.02  --prep_def_merge_mbd                    true
% 1.87/1.02  --prep_def_merge_tr_red                 false
% 1.87/1.02  --prep_def_merge_tr_cl                  false
% 1.87/1.02  --smt_preprocessing                     true
% 1.87/1.02  --smt_ac_axioms                         fast
% 1.87/1.02  --preprocessed_out                      false
% 1.87/1.02  --preprocessed_stats                    false
% 1.87/1.02  
% 1.87/1.02  ------ Abstraction refinement Options
% 1.87/1.02  
% 1.87/1.02  --abstr_ref                             []
% 1.87/1.02  --abstr_ref_prep                        false
% 1.87/1.02  --abstr_ref_until_sat                   false
% 1.87/1.02  --abstr_ref_sig_restrict                funpre
% 1.87/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 1.87/1.02  --abstr_ref_under                       []
% 1.87/1.02  
% 1.87/1.02  ------ SAT Options
% 1.87/1.02  
% 1.87/1.02  --sat_mode                              false
% 1.87/1.02  --sat_fm_restart_options                ""
% 1.87/1.02  --sat_gr_def                            false
% 1.87/1.02  --sat_epr_types                         true
% 1.87/1.02  --sat_non_cyclic_types                  false
% 1.87/1.02  --sat_finite_models                     false
% 1.87/1.02  --sat_fm_lemmas                         false
% 1.87/1.02  --sat_fm_prep                           false
% 1.87/1.02  --sat_fm_uc_incr                        true
% 1.87/1.02  --sat_out_model                         small
% 1.87/1.02  --sat_out_clauses                       false
% 1.87/1.02  
% 1.87/1.02  ------ QBF Options
% 1.87/1.02  
% 1.87/1.02  --qbf_mode                              false
% 1.87/1.02  --qbf_elim_univ                         false
% 1.87/1.02  --qbf_dom_inst                          none
% 1.87/1.02  --qbf_dom_pre_inst                      false
% 1.87/1.02  --qbf_sk_in                             false
% 1.87/1.02  --qbf_pred_elim                         true
% 1.87/1.02  --qbf_split                             512
% 1.87/1.02  
% 1.87/1.02  ------ BMC1 Options
% 1.87/1.02  
% 1.87/1.02  --bmc1_incremental                      false
% 1.87/1.02  --bmc1_axioms                           reachable_all
% 1.87/1.02  --bmc1_min_bound                        0
% 1.87/1.02  --bmc1_max_bound                        -1
% 1.87/1.02  --bmc1_max_bound_default                -1
% 1.87/1.02  --bmc1_symbol_reachability              true
% 1.87/1.02  --bmc1_property_lemmas                  false
% 1.87/1.02  --bmc1_k_induction                      false
% 1.87/1.02  --bmc1_non_equiv_states                 false
% 1.87/1.02  --bmc1_deadlock                         false
% 1.87/1.02  --bmc1_ucm                              false
% 1.87/1.02  --bmc1_add_unsat_core                   none
% 1.87/1.02  --bmc1_unsat_core_children              false
% 1.87/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 1.87/1.02  --bmc1_out_stat                         full
% 1.87/1.02  --bmc1_ground_init                      false
% 1.87/1.02  --bmc1_pre_inst_next_state              false
% 1.87/1.02  --bmc1_pre_inst_state                   false
% 1.87/1.02  --bmc1_pre_inst_reach_state             false
% 1.87/1.02  --bmc1_out_unsat_core                   false
% 1.87/1.02  --bmc1_aig_witness_out                  false
% 1.87/1.02  --bmc1_verbose                          false
% 1.87/1.02  --bmc1_dump_clauses_tptp                false
% 1.87/1.02  --bmc1_dump_unsat_core_tptp             false
% 1.87/1.02  --bmc1_dump_file                        -
% 1.87/1.02  --bmc1_ucm_expand_uc_limit              128
% 1.87/1.02  --bmc1_ucm_n_expand_iterations          6
% 1.87/1.02  --bmc1_ucm_extend_mode                  1
% 1.87/1.02  --bmc1_ucm_init_mode                    2
% 1.87/1.02  --bmc1_ucm_cone_mode                    none
% 1.87/1.02  --bmc1_ucm_reduced_relation_type        0
% 1.87/1.02  --bmc1_ucm_relax_model                  4
% 1.87/1.02  --bmc1_ucm_full_tr_after_sat            true
% 1.87/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 1.87/1.02  --bmc1_ucm_layered_model                none
% 1.87/1.02  --bmc1_ucm_max_lemma_size               10
% 1.87/1.02  
% 1.87/1.02  ------ AIG Options
% 1.87/1.02  
% 1.87/1.02  --aig_mode                              false
% 1.87/1.02  
% 1.87/1.02  ------ Instantiation Options
% 1.87/1.02  
% 1.87/1.02  --instantiation_flag                    true
% 1.87/1.02  --inst_sos_flag                         false
% 1.87/1.02  --inst_sos_phase                        true
% 1.87/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.87/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.87/1.02  --inst_lit_sel_side                     none
% 1.87/1.02  --inst_solver_per_active                1400
% 1.87/1.02  --inst_solver_calls_frac                1.
% 1.87/1.02  --inst_passive_queue_type               priority_queues
% 1.87/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.87/1.02  --inst_passive_queues_freq              [25;2]
% 1.87/1.02  --inst_dismatching                      true
% 1.87/1.02  --inst_eager_unprocessed_to_passive     true
% 1.87/1.02  --inst_prop_sim_given                   true
% 1.87/1.02  --inst_prop_sim_new                     false
% 1.87/1.02  --inst_subs_new                         false
% 1.87/1.02  --inst_eq_res_simp                      false
% 1.87/1.02  --inst_subs_given                       false
% 1.87/1.02  --inst_orphan_elimination               true
% 1.87/1.02  --inst_learning_loop_flag               true
% 1.87/1.02  --inst_learning_start                   3000
% 1.87/1.02  --inst_learning_factor                  2
% 1.87/1.02  --inst_start_prop_sim_after_learn       3
% 1.87/1.02  --inst_sel_renew                        solver
% 1.87/1.02  --inst_lit_activity_flag                true
% 1.87/1.02  --inst_restr_to_given                   false
% 1.87/1.02  --inst_activity_threshold               500
% 1.87/1.02  --inst_out_proof                        true
% 1.87/1.02  
% 1.87/1.02  ------ Resolution Options
% 1.87/1.02  
% 1.87/1.02  --resolution_flag                       false
% 1.87/1.02  --res_lit_sel                           adaptive
% 1.87/1.02  --res_lit_sel_side                      none
% 1.87/1.02  --res_ordering                          kbo
% 1.87/1.02  --res_to_prop_solver                    active
% 1.87/1.02  --res_prop_simpl_new                    false
% 1.87/1.02  --res_prop_simpl_given                  true
% 1.87/1.02  --res_passive_queue_type                priority_queues
% 1.87/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.87/1.02  --res_passive_queues_freq               [15;5]
% 1.87/1.02  --res_forward_subs                      full
% 1.87/1.02  --res_backward_subs                     full
% 1.87/1.02  --res_forward_subs_resolution           true
% 1.87/1.02  --res_backward_subs_resolution          true
% 1.87/1.02  --res_orphan_elimination                true
% 1.87/1.02  --res_time_limit                        2.
% 1.87/1.02  --res_out_proof                         true
% 1.87/1.02  
% 1.87/1.02  ------ Superposition Options
% 1.87/1.02  
% 1.87/1.02  --superposition_flag                    true
% 1.87/1.02  --sup_passive_queue_type                priority_queues
% 1.87/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.87/1.02  --sup_passive_queues_freq               [8;1;4]
% 1.87/1.02  --demod_completeness_check              fast
% 1.87/1.02  --demod_use_ground                      true
% 1.87/1.02  --sup_to_prop_solver                    passive
% 1.87/1.02  --sup_prop_simpl_new                    true
% 1.87/1.02  --sup_prop_simpl_given                  true
% 1.87/1.02  --sup_fun_splitting                     false
% 1.87/1.02  --sup_smt_interval                      50000
% 1.87/1.02  
% 1.87/1.02  ------ Superposition Simplification Setup
% 1.87/1.02  
% 1.87/1.02  --sup_indices_passive                   []
% 1.87/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.87/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.87/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.87/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 1.87/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.87/1.02  --sup_full_bw                           [BwDemod]
% 1.87/1.02  --sup_immed_triv                        [TrivRules]
% 1.87/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.87/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.87/1.02  --sup_immed_bw_main                     []
% 1.87/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.87/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 1.87/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.87/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.87/1.02  
% 1.87/1.02  ------ Combination Options
% 1.87/1.02  
% 1.87/1.02  --comb_res_mult                         3
% 1.87/1.02  --comb_sup_mult                         2
% 1.87/1.02  --comb_inst_mult                        10
% 1.87/1.02  
% 1.87/1.02  ------ Debug Options
% 1.87/1.02  
% 1.87/1.02  --dbg_backtrace                         false
% 1.87/1.02  --dbg_dump_prop_clauses                 false
% 1.87/1.02  --dbg_dump_prop_clauses_file            -
% 1.87/1.02  --dbg_out_stat                          false
% 1.87/1.02  
% 1.87/1.02  
% 1.87/1.02  
% 1.87/1.02  
% 1.87/1.02  ------ Proving...
% 1.87/1.02  
% 1.87/1.02  
% 1.87/1.02  % SZS status Theorem for theBenchmark.p
% 1.87/1.02  
% 1.87/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 1.87/1.02  
% 1.87/1.02  fof(f8,axiom,(
% 1.87/1.02    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.87/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/1.02  
% 1.87/1.02  fof(f42,plain,(
% 1.87/1.02    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.87/1.02    inference(cnf_transformation,[],[f8])).
% 1.87/1.02  
% 1.87/1.02  fof(f6,axiom,(
% 1.87/1.02    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 1.87/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/1.02  
% 1.87/1.02  fof(f16,plain,(
% 1.87/1.02    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.87/1.02    inference(ennf_transformation,[],[f6])).
% 1.87/1.02  
% 1.87/1.02  fof(f38,plain,(
% 1.87/1.02    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 1.87/1.02    inference(cnf_transformation,[],[f16])).
% 1.87/1.02  
% 1.87/1.02  fof(f41,plain,(
% 1.87/1.02    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.87/1.02    inference(cnf_transformation,[],[f8])).
% 1.87/1.02  
% 1.87/1.02  fof(f2,axiom,(
% 1.87/1.02    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.87/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/1.02  
% 1.87/1.02  fof(f24,plain,(
% 1.87/1.02    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.87/1.02    inference(nnf_transformation,[],[f2])).
% 1.87/1.02  
% 1.87/1.02  fof(f25,plain,(
% 1.87/1.02    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.87/1.02    inference(flattening,[],[f24])).
% 1.87/1.02  
% 1.87/1.02  fof(f32,plain,(
% 1.87/1.02    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 1.87/1.02    inference(cnf_transformation,[],[f25])).
% 1.87/1.02  
% 1.87/1.02  fof(f55,plain,(
% 1.87/1.02    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.87/1.02    inference(equality_resolution,[],[f32])).
% 1.87/1.02  
% 1.87/1.02  fof(f9,axiom,(
% 1.87/1.02    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.87/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/1.02  
% 1.87/1.02  fof(f43,plain,(
% 1.87/1.02    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.87/1.02    inference(cnf_transformation,[],[f9])).
% 1.87/1.02  
% 1.87/1.02  fof(f5,axiom,(
% 1.87/1.02    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 1.87/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/1.02  
% 1.87/1.02  fof(f37,plain,(
% 1.87/1.02    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.87/1.02    inference(cnf_transformation,[],[f5])).
% 1.87/1.02  
% 1.87/1.02  fof(f31,plain,(
% 1.87/1.02    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 1.87/1.02    inference(cnf_transformation,[],[f25])).
% 1.87/1.02  
% 1.87/1.02  fof(f3,axiom,(
% 1.87/1.02    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.87/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/1.02  
% 1.87/1.02  fof(f26,plain,(
% 1.87/1.02    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.87/1.02    inference(nnf_transformation,[],[f3])).
% 1.87/1.02  
% 1.87/1.02  fof(f35,plain,(
% 1.87/1.02    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.87/1.02    inference(cnf_transformation,[],[f26])).
% 1.87/1.02  
% 1.87/1.02  fof(f33,plain,(
% 1.87/1.02    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.87/1.02    inference(cnf_transformation,[],[f25])).
% 1.87/1.02  
% 1.87/1.02  fof(f54,plain,(
% 1.87/1.02    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.87/1.02    inference(equality_resolution,[],[f33])).
% 1.87/1.02  
% 1.87/1.02  fof(f10,axiom,(
% 1.87/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 1.87/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/1.02  
% 1.87/1.02  fof(f19,plain,(
% 1.87/1.02    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.87/1.02    inference(ennf_transformation,[],[f10])).
% 1.87/1.02  
% 1.87/1.02  fof(f44,plain,(
% 1.87/1.02    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.87/1.02    inference(cnf_transformation,[],[f19])).
% 1.87/1.02  
% 1.87/1.02  fof(f11,axiom,(
% 1.87/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.87/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/1.02  
% 1.87/1.02  fof(f20,plain,(
% 1.87/1.02    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.87/1.02    inference(ennf_transformation,[],[f11])).
% 1.87/1.02  
% 1.87/1.02  fof(f21,plain,(
% 1.87/1.02    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.87/1.02    inference(flattening,[],[f20])).
% 1.87/1.02  
% 1.87/1.02  fof(f27,plain,(
% 1.87/1.02    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.87/1.02    inference(nnf_transformation,[],[f21])).
% 1.87/1.02  
% 1.87/1.02  fof(f47,plain,(
% 1.87/1.02    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.87/1.02    inference(cnf_transformation,[],[f27])).
% 1.87/1.02  
% 1.87/1.02  fof(f12,conjecture,(
% 1.87/1.02    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 1.87/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/1.02  
% 1.87/1.02  fof(f13,negated_conjecture,(
% 1.87/1.02    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 1.87/1.02    inference(negated_conjecture,[],[f12])).
% 1.87/1.02  
% 1.87/1.02  fof(f22,plain,(
% 1.87/1.02    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 1.87/1.02    inference(ennf_transformation,[],[f13])).
% 1.87/1.02  
% 1.87/1.02  fof(f23,plain,(
% 1.87/1.02    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 1.87/1.02    inference(flattening,[],[f22])).
% 1.87/1.02  
% 1.87/1.02  fof(f28,plain,(
% 1.87/1.02    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0)) => ((~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | ~v1_funct_1(sK0)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 1.87/1.02    introduced(choice_axiom,[])).
% 1.87/1.02  
% 1.87/1.02  fof(f29,plain,(
% 1.87/1.02    (~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | ~v1_funct_1(sK0)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 1.87/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f28])).
% 1.87/1.02  
% 1.87/1.02  fof(f53,plain,(
% 1.87/1.02    ~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | ~v1_funct_1(sK0)),
% 1.87/1.02    inference(cnf_transformation,[],[f29])).
% 1.87/1.02  
% 1.87/1.02  fof(f52,plain,(
% 1.87/1.02    v1_funct_1(sK0)),
% 1.87/1.02    inference(cnf_transformation,[],[f29])).
% 1.87/1.02  
% 1.87/1.02  fof(f51,plain,(
% 1.87/1.02    v1_relat_1(sK0)),
% 1.87/1.02    inference(cnf_transformation,[],[f29])).
% 1.87/1.02  
% 1.87/1.02  fof(f1,axiom,(
% 1.87/1.02    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 1.87/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/1.02  
% 1.87/1.02  fof(f14,plain,(
% 1.87/1.02    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 1.87/1.02    inference(ennf_transformation,[],[f1])).
% 1.87/1.02  
% 1.87/1.02  fof(f30,plain,(
% 1.87/1.02    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 1.87/1.02    inference(cnf_transformation,[],[f14])).
% 1.87/1.02  
% 1.87/1.02  fof(f48,plain,(
% 1.87/1.02    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.87/1.02    inference(cnf_transformation,[],[f27])).
% 1.87/1.02  
% 1.87/1.02  fof(f59,plain,(
% 1.87/1.02    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 1.87/1.02    inference(equality_resolution,[],[f48])).
% 1.87/1.02  
% 1.87/1.02  cnf(c_11,plain,
% 1.87/1.02      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 1.87/1.02      inference(cnf_transformation,[],[f42]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_8,plain,
% 1.87/1.02      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
% 1.87/1.02      | ~ v1_relat_1(X0) ),
% 1.87/1.02      inference(cnf_transformation,[],[f38]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_1044,plain,
% 1.87/1.02      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = iProver_top
% 1.87/1.02      | v1_relat_1(X0) != iProver_top ),
% 1.87/1.02      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_1700,plain,
% 1.87/1.02      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0)) = iProver_top
% 1.87/1.02      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 1.87/1.02      inference(superposition,[status(thm)],[c_11,c_1044]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_12,plain,
% 1.87/1.02      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 1.87/1.02      inference(cnf_transformation,[],[f41]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_1709,plain,
% 1.87/1.02      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top
% 1.87/1.02      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 1.87/1.02      inference(light_normalisation,[status(thm)],[c_1700,c_12]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_2,plain,
% 1.87/1.02      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 1.87/1.02      inference(cnf_transformation,[],[f55]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_1710,plain,
% 1.87/1.02      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top
% 1.87/1.02      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 1.87/1.02      inference(demodulation,[status(thm)],[c_1709,c_2]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_13,plain,
% 1.87/1.02      ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 1.87/1.02      inference(cnf_transformation,[],[f43]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_7,plain,
% 1.87/1.02      ( v1_relat_1(k6_relat_1(X0)) ),
% 1.87/1.02      inference(cnf_transformation,[],[f37]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_57,plain,
% 1.87/1.02      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 1.87/1.02      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_59,plain,
% 1.87/1.02      ( v1_relat_1(k6_relat_1(k1_xboole_0)) = iProver_top ),
% 1.87/1.02      inference(instantiation,[status(thm)],[c_57]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_3,plain,
% 1.87/1.02      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 1.87/1.02      | k1_xboole_0 = X0
% 1.87/1.02      | k1_xboole_0 = X1 ),
% 1.87/1.02      inference(cnf_transformation,[],[f31]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_67,plain,
% 1.87/1.02      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 1.87/1.02      | k1_xboole_0 = k1_xboole_0 ),
% 1.87/1.02      inference(instantiation,[status(thm)],[c_3]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_68,plain,
% 1.87/1.02      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 1.87/1.02      inference(instantiation,[status(thm)],[c_2]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_672,plain,
% 1.87/1.02      ( ~ v1_relat_1(X0) | v1_relat_1(X1) | X1 != X0 ),
% 1.87/1.02      theory(equality) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_1183,plain,
% 1.87/1.02      ( v1_relat_1(X0)
% 1.87/1.02      | ~ v1_relat_1(k6_relat_1(X1))
% 1.87/1.02      | X0 != k6_relat_1(X1) ),
% 1.87/1.02      inference(instantiation,[status(thm)],[c_672]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_1184,plain,
% 1.87/1.02      ( X0 != k6_relat_1(X1)
% 1.87/1.02      | v1_relat_1(X0) = iProver_top
% 1.87/1.02      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 1.87/1.02      inference(predicate_to_equality,[status(thm)],[c_1183]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_1186,plain,
% 1.87/1.02      ( k1_xboole_0 != k6_relat_1(k1_xboole_0)
% 1.87/1.02      | v1_relat_1(k6_relat_1(k1_xboole_0)) != iProver_top
% 1.87/1.02      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 1.87/1.02      inference(instantiation,[status(thm)],[c_1184]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_667,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_1278,plain,
% 1.87/1.02      ( X0 != X1 | X0 = k6_relat_1(X2) | k6_relat_1(X2) != X1 ),
% 1.87/1.02      inference(instantiation,[status(thm)],[c_667]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_1279,plain,
% 1.87/1.02      ( k6_relat_1(k1_xboole_0) != k1_xboole_0
% 1.87/1.02      | k1_xboole_0 = k6_relat_1(k1_xboole_0)
% 1.87/1.02      | k1_xboole_0 != k1_xboole_0 ),
% 1.87/1.02      inference(instantiation,[status(thm)],[c_1278]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_1807,plain,
% 1.87/1.02      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 1.87/1.02      inference(global_propositional_subsumption,
% 1.87/1.02                [status(thm)],
% 1.87/1.02                [c_1710,c_13,c_59,c_67,c_68,c_1186,c_1279]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_4,plain,
% 1.87/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 1.87/1.02      inference(cnf_transformation,[],[f35]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_1047,plain,
% 1.87/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 1.87/1.02      | r1_tarski(X0,X1) != iProver_top ),
% 1.87/1.02      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_1,plain,
% 1.87/1.02      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 1.87/1.02      inference(cnf_transformation,[],[f54]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_14,plain,
% 1.87/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.87/1.02      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 1.87/1.02      inference(cnf_transformation,[],[f44]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_1043,plain,
% 1.87/1.02      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 1.87/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 1.87/1.02      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_1902,plain,
% 1.87/1.02      ( k1_relset_1(X0,k1_xboole_0,X1) = k1_relat_1(X1)
% 1.87/1.02      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 1.87/1.02      inference(superposition,[status(thm)],[c_1,c_1043]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_1926,plain,
% 1.87/1.02      ( k1_relset_1(X0,k1_xboole_0,X1) = k1_relat_1(X1)
% 1.87/1.02      | r1_tarski(X1,k1_xboole_0) != iProver_top ),
% 1.87/1.02      inference(superposition,[status(thm)],[c_1047,c_1902]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_2245,plain,
% 1.87/1.02      ( k1_relset_1(X0,k1_xboole_0,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
% 1.87/1.02      inference(superposition,[status(thm)],[c_1807,c_1926]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_2246,plain,
% 1.87/1.02      ( k1_relset_1(X0,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 1.87/1.02      inference(light_normalisation,[status(thm)],[c_2245,c_12]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_2247,plain,
% 1.87/1.02      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 1.87/1.02      inference(instantiation,[status(thm)],[c_2246]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_18,plain,
% 1.87/1.02      ( v1_funct_2(X0,X1,X2)
% 1.87/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.87/1.02      | k1_relset_1(X1,X2,X0) != X1
% 1.87/1.02      | k1_xboole_0 = X2 ),
% 1.87/1.02      inference(cnf_transformation,[],[f47]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_21,negated_conjecture,
% 1.87/1.02      ( ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
% 1.87/1.02      | ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
% 1.87/1.02      | ~ v1_funct_1(sK0) ),
% 1.87/1.02      inference(cnf_transformation,[],[f53]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_22,negated_conjecture,
% 1.87/1.02      ( v1_funct_1(sK0) ),
% 1.87/1.02      inference(cnf_transformation,[],[f52]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_111,plain,
% 1.87/1.02      ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
% 1.87/1.02      | ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) ),
% 1.87/1.02      inference(global_propositional_subsumption,
% 1.87/1.02                [status(thm)],
% 1.87/1.02                [c_21,c_22]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_112,negated_conjecture,
% 1.87/1.02      ( ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
% 1.87/1.02      | ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) ),
% 1.87/1.02      inference(renaming,[status(thm)],[c_111]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_504,plain,
% 1.87/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.87/1.02      | ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
% 1.87/1.02      | k1_relset_1(X1,X2,X0) != X1
% 1.87/1.02      | k2_relat_1(sK0) != X2
% 1.87/1.02      | k1_relat_1(sK0) != X1
% 1.87/1.02      | sK0 != X0
% 1.87/1.02      | k1_xboole_0 = X2 ),
% 1.87/1.02      inference(resolution_lifted,[status(thm)],[c_18,c_112]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_505,plain,
% 1.87/1.02      ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
% 1.87/1.02      | k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0) != k1_relat_1(sK0)
% 1.87/1.02      | k1_xboole_0 = k2_relat_1(sK0) ),
% 1.87/1.02      inference(unflattening,[status(thm)],[c_504]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_513,plain,
% 1.87/1.02      ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
% 1.87/1.02      | k1_xboole_0 = k2_relat_1(sK0) ),
% 1.87/1.02      inference(forward_subsumption_resolution,
% 1.87/1.02                [status(thm)],
% 1.87/1.02                [c_505,c_14]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_1036,plain,
% 1.87/1.02      ( k1_xboole_0 = k2_relat_1(sK0)
% 1.87/1.02      | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) != iProver_top ),
% 1.87/1.02      inference(predicate_to_equality,[status(thm)],[c_513]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_1504,plain,
% 1.87/1.02      ( k2_relat_1(sK0) = k1_xboole_0
% 1.87/1.02      | r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) != iProver_top ),
% 1.87/1.02      inference(superposition,[status(thm)],[c_1047,c_1036]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_23,negated_conjecture,
% 1.87/1.02      ( v1_relat_1(sK0) ),
% 1.87/1.02      inference(cnf_transformation,[],[f51]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_24,plain,
% 1.87/1.02      ( v1_relat_1(sK0) = iProver_top ),
% 1.87/1.02      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_1170,plain,
% 1.87/1.02      ( r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))
% 1.87/1.02      | ~ v1_relat_1(sK0) ),
% 1.87/1.02      inference(instantiation,[status(thm)],[c_8]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_1171,plain,
% 1.87/1.02      ( r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) = iProver_top
% 1.87/1.02      | v1_relat_1(sK0) != iProver_top ),
% 1.87/1.02      inference(predicate_to_equality,[status(thm)],[c_1170]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_1511,plain,
% 1.87/1.02      ( k2_relat_1(sK0) = k1_xboole_0 ),
% 1.87/1.02      inference(global_propositional_subsumption,
% 1.87/1.02                [status(thm)],
% 1.87/1.02                [c_1504,c_24,c_1171]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_1701,plain,
% 1.87/1.02      ( r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0)) = iProver_top
% 1.87/1.02      | v1_relat_1(sK0) != iProver_top ),
% 1.87/1.02      inference(superposition,[status(thm)],[c_1511,c_1044]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_1704,plain,
% 1.87/1.02      ( r1_tarski(sK0,k1_xboole_0) = iProver_top
% 1.87/1.02      | v1_relat_1(sK0) != iProver_top ),
% 1.87/1.02      inference(demodulation,[status(thm)],[c_1701,c_1]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_1720,plain,
% 1.87/1.02      ( r1_tarski(sK0,k1_xboole_0) = iProver_top ),
% 1.87/1.02      inference(global_propositional_subsumption,
% 1.87/1.02                [status(thm)],
% 1.87/1.02                [c_1704,c_24]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_0,plain,
% 1.87/1.02      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 1.87/1.02      inference(cnf_transformation,[],[f30]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_1048,plain,
% 1.87/1.02      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 1.87/1.02      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_1725,plain,
% 1.87/1.02      ( sK0 = k1_xboole_0 ),
% 1.87/1.02      inference(superposition,[status(thm)],[c_1720,c_1048]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_17,plain,
% 1.87/1.02      ( v1_funct_2(X0,k1_xboole_0,X1)
% 1.87/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 1.87/1.02      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 1.87/1.02      inference(cnf_transformation,[],[f59]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_488,plain,
% 1.87/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 1.87/1.02      | ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
% 1.87/1.02      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 1.87/1.02      | k2_relat_1(sK0) != X1
% 1.87/1.02      | k1_relat_1(sK0) != k1_xboole_0
% 1.87/1.02      | sK0 != X0 ),
% 1.87/1.02      inference(resolution_lifted,[status(thm)],[c_17,c_112]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_489,plain,
% 1.87/1.02      ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
% 1.87/1.02      | ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK0))))
% 1.87/1.02      | k1_relset_1(k1_xboole_0,k2_relat_1(sK0),sK0) != k1_xboole_0
% 1.87/1.02      | k1_relat_1(sK0) != k1_xboole_0 ),
% 1.87/1.02      inference(unflattening,[status(thm)],[c_488]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_1037,plain,
% 1.87/1.02      ( k1_relset_1(k1_xboole_0,k2_relat_1(sK0),sK0) != k1_xboole_0
% 1.87/1.02      | k1_relat_1(sK0) != k1_xboole_0
% 1.87/1.02      | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) != iProver_top
% 1.87/1.02      | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK0)))) != iProver_top ),
% 1.87/1.02      inference(predicate_to_equality,[status(thm)],[c_489]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_1111,plain,
% 1.87/1.02      ( k1_relset_1(k1_xboole_0,k2_relat_1(sK0),sK0) != k1_xboole_0
% 1.87/1.02      | k1_relat_1(sK0) != k1_xboole_0
% 1.87/1.02      | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) != iProver_top
% 1.87/1.02      | m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 1.87/1.02      inference(demodulation,[status(thm)],[c_1037,c_2]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_1515,plain,
% 1.87/1.02      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK0) != k1_xboole_0
% 1.87/1.02      | k1_relat_1(sK0) != k1_xboole_0
% 1.87/1.02      | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0))) != iProver_top
% 1.87/1.02      | m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 1.87/1.02      inference(demodulation,[status(thm)],[c_1511,c_1111]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_1521,plain,
% 1.87/1.02      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK0) != k1_xboole_0
% 1.87/1.02      | k1_relat_1(sK0) != k1_xboole_0
% 1.87/1.02      | m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 1.87/1.02      inference(demodulation,[status(thm)],[c_1515,c_1]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_2050,plain,
% 1.87/1.02      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 1.87/1.02      | k1_relat_1(k1_xboole_0) != k1_xboole_0
% 1.87/1.02      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 1.87/1.02      inference(demodulation,[status(thm)],[c_1725,c_1521]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_2056,plain,
% 1.87/1.02      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 1.87/1.02      | k1_xboole_0 != k1_xboole_0
% 1.87/1.02      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 1.87/1.02      inference(light_normalisation,[status(thm)],[c_2050,c_12]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_2057,plain,
% 1.87/1.02      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 1.87/1.02      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 1.87/1.02      inference(equality_resolution_simp,[status(thm)],[c_2056]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_64,plain,
% 1.87/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 1.87/1.02      | r1_tarski(X0,X1) != iProver_top ),
% 1.87/1.02      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_66,plain,
% 1.87/1.02      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 1.87/1.02      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 1.87/1.02      inference(instantiation,[status(thm)],[c_64]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(contradiction,plain,
% 1.87/1.02      ( $false ),
% 1.87/1.02      inference(minisat,
% 1.87/1.02                [status(thm)],
% 1.87/1.02                [c_2247,c_2057,c_1710,c_1279,c_1186,c_68,c_67,c_66,c_59,
% 1.87/1.02                 c_13]) ).
% 1.87/1.02  
% 1.87/1.02  
% 1.87/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 1.87/1.02  
% 1.87/1.02  ------                               Statistics
% 1.87/1.02  
% 1.87/1.02  ------ General
% 1.87/1.02  
% 1.87/1.02  abstr_ref_over_cycles:                  0
% 1.87/1.02  abstr_ref_under_cycles:                 0
% 1.87/1.02  gc_basic_clause_elim:                   0
% 1.87/1.02  forced_gc_time:                         0
% 1.87/1.02  parsing_time:                           0.017
% 1.87/1.02  unif_index_cands_time:                  0.
% 1.87/1.02  unif_index_add_time:                    0.
% 1.87/1.02  orderings_time:                         0.
% 1.87/1.02  out_proof_time:                         0.01
% 1.87/1.02  total_time:                             0.156
% 1.87/1.02  num_of_symbols:                         44
% 1.87/1.02  num_of_terms:                           2047
% 1.87/1.02  
% 1.87/1.02  ------ Preprocessing
% 1.87/1.02  
% 1.87/1.02  num_of_splits:                          0
% 1.87/1.02  num_of_split_atoms:                     0
% 1.87/1.02  num_of_reused_defs:                     0
% 1.87/1.02  num_eq_ax_congr_red:                    2
% 1.87/1.02  num_of_sem_filtered_clauses:            2
% 1.87/1.02  num_of_subtypes:                        0
% 1.87/1.02  monotx_restored_types:                  0
% 1.87/1.02  sat_num_of_epr_types:                   0
% 1.87/1.02  sat_num_of_non_cyclic_types:            0
% 1.87/1.02  sat_guarded_non_collapsed_types:        0
% 1.87/1.02  num_pure_diseq_elim:                    0
% 1.87/1.02  simp_replaced_by:                       0
% 1.87/1.02  res_preprocessed:                       104
% 1.87/1.02  prep_upred:                             0
% 1.87/1.02  prep_unflattend:                        34
% 1.87/1.02  smt_new_axioms:                         0
% 1.87/1.02  pred_elim_cands:                        3
% 1.87/1.02  pred_elim:                              1
% 1.87/1.02  pred_elim_cl:                           4
% 1.87/1.02  pred_elim_cycles:                       4
% 1.87/1.02  merged_defs:                            8
% 1.87/1.02  merged_defs_ncl:                        0
% 1.87/1.02  bin_hyper_res:                          9
% 1.87/1.02  prep_cycles:                            4
% 1.87/1.02  pred_elim_time:                         0.008
% 1.87/1.02  splitting_time:                         0.
% 1.87/1.02  sem_filter_time:                        0.
% 1.87/1.02  monotx_time:                            0.001
% 1.87/1.02  subtype_inf_time:                       0.
% 1.87/1.02  
% 1.87/1.02  ------ Problem properties
% 1.87/1.02  
% 1.87/1.02  clauses:                                19
% 1.87/1.02  conjectures:                            1
% 1.87/1.02  epr:                                    3
% 1.87/1.02  horn:                                   18
% 1.87/1.02  ground:                                 7
% 1.87/1.02  unary:                                  7
% 1.87/1.02  binary:                                 6
% 1.87/1.02  lits:                                   40
% 1.87/1.02  lits_eq:                                16
% 1.87/1.02  fd_pure:                                0
% 1.87/1.02  fd_pseudo:                              0
% 1.87/1.02  fd_cond:                                2
% 1.87/1.02  fd_pseudo_cond:                         0
% 1.87/1.02  ac_symbols:                             0
% 1.87/1.02  
% 1.87/1.02  ------ Propositional Solver
% 1.87/1.02  
% 1.87/1.02  prop_solver_calls:                      27
% 1.87/1.02  prop_fast_solver_calls:                 587
% 1.87/1.02  smt_solver_calls:                       0
% 1.87/1.02  smt_fast_solver_calls:                  0
% 1.87/1.02  prop_num_of_clauses:                    707
% 1.87/1.02  prop_preprocess_simplified:             3398
% 1.87/1.02  prop_fo_subsumed:                       9
% 1.87/1.02  prop_solver_time:                       0.
% 1.87/1.02  smt_solver_time:                        0.
% 1.87/1.02  smt_fast_solver_time:                   0.
% 1.87/1.02  prop_fast_solver_time:                  0.
% 1.87/1.02  prop_unsat_core_time:                   0.
% 1.87/1.02  
% 1.87/1.02  ------ QBF
% 1.87/1.02  
% 1.87/1.02  qbf_q_res:                              0
% 1.87/1.02  qbf_num_tautologies:                    0
% 1.87/1.02  qbf_prep_cycles:                        0
% 1.87/1.02  
% 1.87/1.02  ------ BMC1
% 1.87/1.02  
% 1.87/1.02  bmc1_current_bound:                     -1
% 1.87/1.02  bmc1_last_solved_bound:                 -1
% 1.87/1.02  bmc1_unsat_core_size:                   -1
% 1.87/1.02  bmc1_unsat_core_parents_size:           -1
% 1.87/1.02  bmc1_merge_next_fun:                    0
% 1.87/1.02  bmc1_unsat_core_clauses_time:           0.
% 1.87/1.02  
% 1.87/1.02  ------ Instantiation
% 1.87/1.02  
% 1.87/1.02  inst_num_of_clauses:                    269
% 1.87/1.02  inst_num_in_passive:                    142
% 1.87/1.02  inst_num_in_active:                     118
% 1.87/1.02  inst_num_in_unprocessed:                9
% 1.87/1.02  inst_num_of_loops:                      140
% 1.87/1.02  inst_num_of_learning_restarts:          0
% 1.87/1.02  inst_num_moves_active_passive:          20
% 1.87/1.02  inst_lit_activity:                      0
% 1.87/1.02  inst_lit_activity_moves:                0
% 1.87/1.02  inst_num_tautologies:                   0
% 1.87/1.02  inst_num_prop_implied:                  0
% 1.87/1.02  inst_num_existing_simplified:           0
% 1.87/1.02  inst_num_eq_res_simplified:             0
% 1.87/1.02  inst_num_child_elim:                    0
% 1.87/1.02  inst_num_of_dismatching_blockings:      18
% 1.87/1.02  inst_num_of_non_proper_insts:           152
% 1.87/1.02  inst_num_of_duplicates:                 0
% 1.87/1.02  inst_inst_num_from_inst_to_res:         0
% 1.87/1.02  inst_dismatching_checking_time:         0.
% 1.87/1.02  
% 1.87/1.02  ------ Resolution
% 1.87/1.02  
% 1.87/1.02  res_num_of_clauses:                     0
% 1.87/1.02  res_num_in_passive:                     0
% 1.87/1.02  res_num_in_active:                      0
% 1.87/1.02  res_num_of_loops:                       108
% 1.87/1.02  res_forward_subset_subsumed:            9
% 1.87/1.02  res_backward_subset_subsumed:           0
% 1.87/1.02  res_forward_subsumed:                   0
% 1.87/1.02  res_backward_subsumed:                  0
% 1.87/1.02  res_forward_subsumption_resolution:     1
% 1.87/1.02  res_backward_subsumption_resolution:    0
% 1.87/1.02  res_clause_to_clause_subsumption:       68
% 1.87/1.02  res_orphan_elimination:                 0
% 1.87/1.02  res_tautology_del:                      43
% 1.87/1.02  res_num_eq_res_simplified:              0
% 1.87/1.02  res_num_sel_changes:                    0
% 1.87/1.02  res_moves_from_active_to_pass:          0
% 1.87/1.02  
% 1.87/1.02  ------ Superposition
% 1.87/1.02  
% 1.87/1.02  sup_time_total:                         0.
% 1.87/1.02  sup_time_generating:                    0.
% 1.87/1.02  sup_time_sim_full:                      0.
% 1.87/1.02  sup_time_sim_immed:                     0.
% 1.87/1.02  
% 1.87/1.02  sup_num_of_clauses:                     26
% 1.87/1.02  sup_num_in_active:                      20
% 1.87/1.02  sup_num_in_passive:                     6
% 1.87/1.02  sup_num_of_loops:                       27
% 1.87/1.02  sup_fw_superposition:                   14
% 1.87/1.02  sup_bw_superposition:                   5
% 1.87/1.02  sup_immediate_simplified:               9
% 1.87/1.02  sup_given_eliminated:                   0
% 1.87/1.02  comparisons_done:                       0
% 1.87/1.02  comparisons_avoided:                    0
% 1.87/1.02  
% 1.87/1.02  ------ Simplifications
% 1.87/1.02  
% 1.87/1.02  
% 1.87/1.02  sim_fw_subset_subsumed:                 2
% 1.87/1.02  sim_bw_subset_subsumed:                 0
% 1.87/1.02  sim_fw_subsumed:                        0
% 1.87/1.02  sim_bw_subsumed:                        0
% 1.87/1.02  sim_fw_subsumption_res:                 0
% 1.87/1.02  sim_bw_subsumption_res:                 0
% 1.87/1.02  sim_tautology_del:                      3
% 1.87/1.02  sim_eq_tautology_del:                   3
% 1.87/1.02  sim_eq_res_simp:                        3
% 1.87/1.02  sim_fw_demodulated:                     7
% 1.87/1.02  sim_bw_demodulated:                     8
% 1.87/1.02  sim_light_normalised:                   4
% 1.87/1.02  sim_joinable_taut:                      0
% 1.87/1.02  sim_joinable_simp:                      0
% 1.87/1.02  sim_ac_normalised:                      0
% 1.87/1.02  sim_smt_subsumption:                    0
% 1.87/1.02  
%------------------------------------------------------------------------------
