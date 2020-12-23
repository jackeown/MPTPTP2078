%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1030+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:42 EST 2020

% Result     : Theorem 0.86s
% Output     : CNFRefutation 0.86s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 941 expanded)
%              Number of clauses        :   46 ( 278 expanded)
%              Number of leaves         :    6 ( 188 expanded)
%              Depth                    :   21
%              Number of atoms          :  200 (4457 expanded)
%              Number of equality atoms :   83 (1431 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => v1_partfun1(k3_partfun1(X2,X0,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => v1_partfun1(k3_partfun1(X2,X0,X1),X0) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ~ v1_partfun1(k3_partfun1(X2,X0,X1),X0)
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ~ v1_partfun1(k3_partfun1(X2,X0,X1),X0)
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( ~ v1_partfun1(k3_partfun1(X2,X0,X1),X0)
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ~ v1_partfun1(k3_partfun1(sK2,sK0,sK1),sK0)
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ~ v1_partfun1(k3_partfun1(sK2,sK0,sK1),sK0)
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f15])).

fof(f26,plain,(
    ~ v1_partfun1(k3_partfun1(sK2,sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f16])).

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

fof(f8,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f8])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f23,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f22,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f24,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f16])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k3_partfun1(X2,X0,X1) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( k3_partfun1(X2,X0,X1) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k3_partfun1(X2,X0,X1) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( k3_partfun1(X2,X0,X1) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f25,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f16])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f7])).

cnf(c_3,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f20])).

cnf(c_5,negated_conjecture,
    ( ~ v1_partfun1(k3_partfun1(sK2,sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_1,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_partfun1(X0,X1)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_8,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_96,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_partfun1(X0,X1)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | sK1 != X2
    | sK0 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_8])).

cnf(c_97,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_partfun1(sK2,sK0)
    | ~ v1_funct_1(sK2)
    | v1_xboole_0(sK1) ),
    inference(unflattening,[status(thm)],[c_96])).

cnf(c_9,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_7,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_99,plain,
    ( v1_partfun1(sK2,sK0)
    | v1_xboole_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_97,c_9,c_7])).

cnf(c_140,plain,
    ( v1_xboole_0(sK1)
    | k3_partfun1(sK2,sK0,sK1) != sK2
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_99])).

cnf(c_190,plain,
    ( k3_partfun1(sK2,sK0,sK1) != sK2
    | sK1 != X0
    | sK0 != sK0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_140])).

cnf(c_191,plain,
    ( k3_partfun1(sK2,sK0,sK1) != sK2
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_190])).

cnf(c_310,plain,
    ( k1_xboole_0 = sK1
    | k3_partfun1(sK2,sK0,sK1) != sK2 ),
    inference(subtyping,[status(esa)],[c_191])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k3_partfun1(X0,X1,X2) = X0 ),
    inference(cnf_transformation,[],[f21])).

cnf(c_113,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k3_partfun1(X0,X1,X2) = X0
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_9])).

cnf(c_114,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k3_partfun1(sK2,X0,X1) = sK2 ),
    inference(unflattening,[status(thm)],[c_113])).

cnf(c_311,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_42,X1_42)))
    | k3_partfun1(sK2,X0_42,X1_42) = sK2 ),
    inference(subtyping,[status(esa)],[c_114])).

cnf(c_450,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k3_partfun1(sK2,sK0,sK1) = sK2 ),
    inference(instantiation,[status(thm)],[c_311])).

cnf(c_469,plain,
    ( k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_310,c_7,c_450])).

cnf(c_312,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_413,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_312])).

cnf(c_6,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_313,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_453,negated_conjecture,
    ( k1_xboole_0 = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_313,c_7,c_310,c_450])).

cnf(c_457,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_413,c_453])).

cnf(c_472,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_469,c_457])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_partfun1(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_128,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1)
    | k3_partfun1(sK2,sK0,sK1) != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_5])).

cnf(c_129,plain,
    ( ~ m1_subset_1(k3_partfun1(sK2,sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
    | ~ v1_xboole_0(sK0) ),
    inference(unflattening,[status(thm)],[c_128])).

cnf(c_198,plain,
    ( ~ m1_subset_1(k3_partfun1(sK2,sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
    | k3_partfun1(sK2,sK0,sK1) != sK2
    | sK1 != sK0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_129,c_140])).

cnf(c_256,plain,
    ( ~ m1_subset_1(k3_partfun1(sK2,sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
    | k3_partfun1(sK2,sK0,sK1) != sK2
    | sK1 != sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_198])).

cnf(c_309,plain,
    ( ~ m1_subset_1(k3_partfun1(sK2,sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,X0_42)))
    | sK1 != sK0
    | k3_partfun1(sK2,sK0,sK1) != sK2 ),
    inference(subtyping,[status(esa)],[c_256])).

cnf(c_314,plain,
    ( ~ m1_subset_1(k3_partfun1(sK2,sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,X0_42)))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_309])).

cnf(c_416,plain,
    ( m1_subset_1(k3_partfun1(sK2,sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,X0_42))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_314])).

cnf(c_341,plain,
    ( m1_subset_1(k3_partfun1(sK2,sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,X0_42))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_314])).

cnf(c_315,plain,
    ( sP0_iProver_split
    | sK1 != sK0
    | k3_partfun1(sK2,sK0,sK1) != sK2 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_309])).

cnf(c_415,plain,
    ( sK1 != sK0
    | k3_partfun1(sK2,sK0,sK1) != sK2
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_315])).

cnf(c_340,plain,
    ( sK1 != sK0
    | k3_partfun1(sK2,sK0,sK1) != sK2
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_315])).

cnf(c_548,plain,
    ( sK1 != sK0
    | sP0_iProver_split = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_415,c_7,c_340,c_450])).

cnf(c_552,plain,
    ( k1_xboole_0 != k1_xboole_0
    | sP0_iProver_split = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_548,c_453,c_469])).

cnf(c_553,plain,
    ( sP0_iProver_split = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_552])).

cnf(c_557,plain,
    ( m1_subset_1(k3_partfun1(sK2,sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,X0_42))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_416,c_341,c_553])).

cnf(c_414,plain,
    ( k3_partfun1(sK2,X0_42,X1_42) = sK2
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_42,X1_42))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_311])).

cnf(c_511,plain,
    ( k3_partfun1(sK2,k1_xboole_0,k1_xboole_0) = sK2 ),
    inference(superposition,[status(thm)],[c_472,c_414])).

cnf(c_563,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0_42))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_557,c_453,c_469,c_511])).

cnf(c_568,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_472,c_563])).


%------------------------------------------------------------------------------
