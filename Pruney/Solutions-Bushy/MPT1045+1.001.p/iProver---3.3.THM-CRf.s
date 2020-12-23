%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1045+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:45 EST 2020

% Result     : Theorem 0.96s
% Output     : CNFRefutation 0.96s
% Verified   : 
% Statistics : Number of formulae       :   88 (1398 expanded)
%              Number of clauses        :   58 ( 456 expanded)
%              Number of leaves         :    8 ( 272 expanded)
%              Depth                    :   20
%              Number of atoms          :  259 (6439 expanded)
%              Number of equality atoms :  119 (2851 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f9])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1)) = k1_tarski(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1)) = k1_tarski(X2) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1)) != k1_tarski(X2)
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1)) != k1_tarski(X2)
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f19,plain,
    ( ? [X0,X1,X2] :
        ( k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1)) != k1_tarski(X2)
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( k5_partfun1(sK0,sK1,k3_partfun1(sK2,sK0,sK1)) != k1_tarski(sK2)
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( k5_partfun1(sK0,sK1,k3_partfun1(sK2,sK0,sK1)) != k1_tarski(sK2)
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f19])).

fof(f29,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f28,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f30,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( v1_partfun1(X2,X0)
      <=> k5_partfun1(X0,X1,X2) = k1_tarski(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( v1_partfun1(X2,X0)
      <=> k5_partfun1(X0,X1,X2) = k1_tarski(X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( v1_partfun1(X2,X0)
      <=> k5_partfun1(X0,X1,X2) = k1_tarski(X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_partfun1(X2,X0)
          | k5_partfun1(X0,X1,X2) != k1_tarski(X2) )
        & ( k5_partfun1(X0,X1,X2) = k1_tarski(X2)
          | ~ v1_partfun1(X2,X0) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( k5_partfun1(X0,X1,X2) = k1_tarski(X2)
      | ~ v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k3_partfun1(X2,X0,X1) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k3_partfun1(X2,X0,X1) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k3_partfun1(X2,X0,X1) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k3_partfun1(X2,X0,X1) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f32,plain,(
    k5_partfun1(sK0,sK1,k3_partfun1(sK2,sK0,sK1)) != k1_tarski(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f31,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f20])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f8])).

cnf(c_5,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_1,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_partfun1(X0,X1)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_10,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_111,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_partfun1(X0,X1)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | sK2 != X0
    | sK1 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_10])).

cnf(c_112,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_partfun1(sK2,sK0)
    | ~ v1_funct_1(sK2)
    | v1_xboole_0(sK1) ),
    inference(unflattening,[status(thm)],[c_111])).

cnf(c_11,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_9,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_114,plain,
    ( v1_partfun1(sK2,sK0)
    | v1_xboole_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_112,c_11,c_9])).

cnf(c_143,plain,
    ( v1_partfun1(sK2,sK0)
    | sK1 != X0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_114])).

cnf(c_144,plain,
    ( v1_partfun1(sK2,sK0)
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_143])).

cnf(c_336,plain,
    ( v1_partfun1(sK2,sK0)
    | k1_xboole_0 = sK1 ),
    inference(subtyping,[status(esa)],[c_144])).

cnf(c_463,plain,
    ( k1_xboole_0 = sK1
    | v1_partfun1(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_336])).

cnf(c_345,plain,
    ( X0_45 = X0_45 ),
    theory(equality)).

cnf(c_518,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_345])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_partfun1(X0,X1)
    | ~ v1_funct_1(X0)
    | k5_partfun1(X1,X2,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_172,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_partfun1(X0,X1)
    | k5_partfun1(X1,X2,X0) = k1_tarski(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_11])).

cnf(c_173,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_partfun1(sK2,X0)
    | k5_partfun1(X0,X1,sK2) = k1_tarski(sK2) ),
    inference(unflattening,[status(thm)],[c_172])).

cnf(c_245,plain,
    ( ~ v1_partfun1(sK2,X0)
    | k5_partfun1(X0,X1,sK2) = k1_tarski(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_173])).

cnf(c_296,plain,
    ( ~ v1_partfun1(sK2,X0)
    | k5_partfun1(X0,X1,sK2) = k1_tarski(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(equality_resolution_simp,[status(thm)],[c_245])).

cnf(c_333,plain,
    ( ~ v1_partfun1(sK2,X0_43)
    | k1_zfmisc_1(k2_zfmisc_1(X0_43,X1_43)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | k5_partfun1(X0_43,X1_43,sK2) = k1_tarski(sK2) ),
    inference(subtyping,[status(esa)],[c_296])).

cnf(c_519,plain,
    ( ~ v1_partfun1(sK2,sK0)
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | k5_partfun1(sK0,sK1,sK2) = k1_tarski(sK2) ),
    inference(instantiation,[status(thm)],[c_333])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k3_partfun1(X0,X1,X2) = X0 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_160,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k3_partfun1(X0,X1,X2) = X0
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_11])).

cnf(c_161,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k3_partfun1(sK2,X0,X1) = sK2 ),
    inference(unflattening,[status(thm)],[c_160])).

cnf(c_262,plain,
    ( k3_partfun1(sK2,X0,X1) = sK2
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_161])).

cnf(c_294,plain,
    ( k3_partfun1(sK2,X0,X1) = sK2
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(equality_resolution_simp,[status(thm)],[c_262])).

cnf(c_334,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_43,X1_43)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | k3_partfun1(sK2,X0_43,X1_43) = sK2 ),
    inference(subtyping,[status(esa)],[c_294])).

cnf(c_536,plain,
    ( k3_partfun1(sK2,sK0,sK1) = sK2 ),
    inference(equality_resolution,[status(thm)],[c_334])).

cnf(c_7,negated_conjecture,
    ( k5_partfun1(sK0,sK1,k3_partfun1(sK2,sK0,sK1)) != k1_tarski(sK2) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_338,negated_conjecture,
    ( k5_partfun1(sK0,sK1,k3_partfun1(sK2,sK0,sK1)) != k1_tarski(sK2) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_551,plain,
    ( k5_partfun1(sK0,sK1,sK2) != k1_tarski(sK2) ),
    inference(demodulation,[status(thm)],[c_536,c_338])).

cnf(c_605,plain,
    ( k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_463,c_336,c_518,c_519,c_551])).

cnf(c_466,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_43,X1_43)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | k5_partfun1(X0_43,X1_43,sK2) = k1_tarski(sK2)
    | v1_partfun1(sK2,X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_333])).

cnf(c_608,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_43,X1_43)) != k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))
    | k5_partfun1(X0_43,X1_43,sK2) = k1_tarski(sK2)
    | v1_partfun1(sK2,X0_43) != iProver_top ),
    inference(demodulation,[status(thm)],[c_605,c_466])).

cnf(c_8,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_337,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_614,plain,
    ( sK0 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_605,c_337])).

cnf(c_615,plain,
    ( sK0 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_614])).

cnf(c_639,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_43,X1_43)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | k5_partfun1(X0_43,X1_43,sK2) = k1_tarski(sK2)
    | v1_partfun1(sK2,X0_43) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_608,c_615])).

cnf(c_887,plain,
    ( k5_partfun1(k1_xboole_0,k1_xboole_0,sK2) = k1_tarski(sK2)
    | v1_partfun1(sK2,k1_xboole_0) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_639])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_partfun1(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_128,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_partfun1(X0,X1)
    | v1_partfun1(sK2,sK0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_114])).

cnf(c_129,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
    | v1_partfun1(X0,sK1)
    | v1_partfun1(sK2,sK0) ),
    inference(unflattening,[status(thm)],[c_128])).

cnf(c_213,plain,
    ( v1_partfun1(X0,sK1)
    | v1_partfun1(sK2,sK0)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_129])).

cnf(c_214,plain,
    ( v1_partfun1(sK2,sK1)
    | v1_partfun1(sK2,sK0)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(unflattening,[status(thm)],[c_213])).

cnf(c_335,plain,
    ( v1_partfun1(sK2,sK1)
    | v1_partfun1(sK2,sK0)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,X0_43)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(subtyping,[status(esa)],[c_214])).

cnf(c_339,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,X0_43)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_335])).

cnf(c_465,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,X0_43)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_339])).

cnf(c_613,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0_43)) != k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))
    | sP0_iProver_split != iProver_top ),
    inference(demodulation,[status(thm)],[c_605,c_465])).

cnf(c_618,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0_43)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | sP0_iProver_split != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_613,c_615])).

cnf(c_749,plain,
    ( sP0_iProver_split != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_618])).

cnf(c_609,plain,
    ( k5_partfun1(sK0,k1_xboole_0,sK2) != k1_tarski(sK2) ),
    inference(demodulation,[status(thm)],[c_605,c_551])).

cnf(c_636,plain,
    ( k5_partfun1(k1_xboole_0,k1_xboole_0,sK2) != k1_tarski(sK2) ),
    inference(light_normalisation,[status(thm)],[c_609,c_615])).

cnf(c_340,plain,
    ( v1_partfun1(sK2,sK1)
    | v1_partfun1(sK2,sK0)
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_335])).

cnf(c_464,plain,
    ( v1_partfun1(sK2,sK1) = iProver_top
    | v1_partfun1(sK2,sK0) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_340])).

cnf(c_611,plain,
    ( v1_partfun1(sK2,sK0) = iProver_top
    | v1_partfun1(sK2,k1_xboole_0) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(demodulation,[status(thm)],[c_605,c_464])).

cnf(c_628,plain,
    ( v1_partfun1(sK2,k1_xboole_0) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_611,c_615])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_887,c_749,c_636,c_628])).


%------------------------------------------------------------------------------
