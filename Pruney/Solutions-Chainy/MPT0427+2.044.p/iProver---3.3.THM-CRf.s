%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:42:35 EST 2020

% Result     : Theorem 1.92s
% Output     : CNFRefutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :  132 (1593 expanded)
%              Number of clauses        :   87 ( 639 expanded)
%              Number of leaves         :   17 ( 382 expanded)
%              Depth                    :   23
%              Number of atoms          :  321 (5073 expanded)
%              Number of equality atoms :  158 (1402 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( r1_tarski(X1,X2)
           => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( r1_tarski(X1,X2)
             => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f24,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f23])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
     => ( ~ r1_tarski(k8_setfam_1(X0,sK2),k8_setfam_1(X0,X1))
        & r1_tarski(X1,sK2)
        & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
            & r1_tarski(X1,X2)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(sK0,X2),k8_setfam_1(sK0,sK1))
          & r1_tarski(sK1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f27,f26])).

fof(f42,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ( k1_xboole_0 = X1
         => k8_setfam_1(X0,X1) = X0 )
        & ( k1_xboole_0 != X1
         => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ( k8_setfam_1(X0,X1) = X0
          | k1_xboole_0 != X1 )
        & ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
          | k1_xboole_0 = X1 ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f41,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f28])).

fof(f44,plain,(
    ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f28])).

fof(f43,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f31,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | r1_xboole_0(X0,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f45,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f31])).

fof(f32,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f46,plain,(
    ! [X0] :
      ( k8_setfam_1(X0,k1_xboole_0) = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f35])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f16])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f29,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_716,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k6_setfam_1(X1,X0) = k8_setfam_1(X1,X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_724,plain,
    ( k6_setfam_1(X0,X1) = k8_setfam_1(X0,X1)
    | k1_xboole_0 = X1
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1724,plain,
    ( k6_setfam_1(sK0,sK2) = k8_setfam_1(sK0,sK2)
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_716,c_724])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k6_setfam_1(X1,X0) = k1_setfam_1(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_722,plain,
    ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1240,plain,
    ( k6_setfam_1(sK0,sK2) = k1_setfam_1(sK2) ),
    inference(superposition,[status(thm)],[c_716,c_722])).

cnf(c_1733,plain,
    ( k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | sK2 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1724,c_1240])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_715,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1725,plain,
    ( k6_setfam_1(sK0,sK1) = k8_setfam_1(sK0,sK1)
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_715,c_724])).

cnf(c_1241,plain,
    ( k6_setfam_1(sK0,sK1) = k1_setfam_1(sK1) ),
    inference(superposition,[status(thm)],[c_715,c_722])).

cnf(c_1728,plain,
    ( k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1)
    | sK1 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1725,c_1241])).

cnf(c_12,negated_conjecture,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_718,plain,
    ( r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2033,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k8_setfam_1(sK0,sK2),k1_setfam_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1728,c_718])).

cnf(c_2067,plain,
    ( sK1 = k1_xboole_0
    | sK2 = k1_xboole_0
    | r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1733,c_2033])).

cnf(c_13,negated_conjecture,
    ( r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_18,plain,
    ( r1_tarski(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_358,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_926,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_358])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_908,plain,
    ( r1_tarski(k1_setfam_1(X0),k1_setfam_1(sK1))
    | ~ r1_tarski(sK1,X0)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1026,plain,
    ( r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1))
    | ~ r1_tarski(sK1,sK2)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_908])).

cnf(c_1027,plain,
    ( k1_xboole_0 = sK1
    | r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) = iProver_top
    | r1_tarski(sK1,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1026])).

cnf(c_359,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1140,plain,
    ( X0 != X1
    | sK1 != X1
    | sK1 = X0 ),
    inference(instantiation,[status(thm)],[c_359])).

cnf(c_1657,plain,
    ( X0 != sK1
    | sK1 = X0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1140])).

cnf(c_1658,plain,
    ( sK1 != sK1
    | sK1 = k1_xboole_0
    | k1_xboole_0 != sK1 ),
    inference(instantiation,[status(thm)],[c_1657])).

cnf(c_2143,plain,
    ( sK2 = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2067,c_18,c_926,c_1027,c_1658])).

cnf(c_2144,plain,
    ( sK1 = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_2143])).

cnf(c_2155,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2144,c_715])).

cnf(c_17,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_46,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_973,plain,
    ( X0 != X1
    | X0 = sK2
    | sK2 != X1 ),
    inference(instantiation,[status(thm)],[c_359])).

cnf(c_974,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_973])).

cnf(c_1184,plain,
    ( k1_zfmisc_1(k1_zfmisc_1(sK0)) = k1_zfmisc_1(k1_zfmisc_1(sK0)) ),
    inference(instantiation,[status(thm)],[c_358])).

cnf(c_364,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_850,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | X1 != k1_zfmisc_1(k1_zfmisc_1(sK0))
    | X0 != sK2 ),
    inference(instantiation,[status(thm)],[c_364])).

cnf(c_1793,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | X0 != sK2
    | k1_zfmisc_1(k1_zfmisc_1(sK0)) != k1_zfmisc_1(k1_zfmisc_1(sK0)) ),
    inference(instantiation,[status(thm)],[c_850])).

cnf(c_1794,plain,
    ( X0 != sK2
    | k1_zfmisc_1(k1_zfmisc_1(sK0)) != k1_zfmisc_1(k1_zfmisc_1(sK0))
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1793])).

cnf(c_1796,plain,
    ( k1_zfmisc_1(k1_zfmisc_1(sK0)) != k1_zfmisc_1(k1_zfmisc_1(sK0))
    | k1_xboole_0 != sK2
    | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1794])).

cnf(c_2312,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2155,c_17,c_3,c_46,c_974,c_1184,c_1796])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | m1_subset_1(k8_setfam_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_723,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | m1_subset_1(k8_setfam_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_720,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1256,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | r1_tarski(k8_setfam_1(X1,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_723,c_720])).

cnf(c_2926,plain,
    ( r1_tarski(k8_setfam_1(sK0,k1_xboole_0),sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2312,c_1256])).

cnf(c_5,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
    | k8_setfam_1(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_725,plain,
    ( k8_setfam_1(X0,k1_xboole_0) = X0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2317,plain,
    ( k8_setfam_1(sK0,k1_xboole_0) = sK0 ),
    inference(superposition,[status(thm)],[c_2312,c_725])).

cnf(c_2928,plain,
    ( r1_tarski(sK0,sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2926,c_2317])).

cnf(c_2154,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2144,c_718])).

cnf(c_2329,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(k8_setfam_1(sK0,sK2),sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2317,c_2154])).

cnf(c_829,plain,
    ( m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_830,plain,
    ( m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(sK0)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_829])).

cnf(c_882,plain,
    ( ~ m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(sK0))
    | r1_tarski(k8_setfam_1(sK0,sK2),sK0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_883,plain,
    ( m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(sK0)) != iProver_top
    | r1_tarski(k8_setfam_1(sK0,sK2),sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_882])).

cnf(c_2497,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2329,c_17,c_830,c_883])).

cnf(c_717,plain,
    ( r1_tarski(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_xboole_0(X0,X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_0,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_208,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_xboole_0(X0,X1)
    | k1_xboole_0 = X0 ),
    inference(resolution,[status(thm)],[c_4,c_0])).

cnf(c_714,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,X1) != iProver_top
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_208])).

cnf(c_1047,plain,
    ( sK1 = k1_xboole_0
    | r1_xboole_0(sK1,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_717,c_714])).

cnf(c_2506,plain,
    ( sK1 = k1_xboole_0
    | r1_xboole_0(sK1,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2497,c_1047])).

cnf(c_361,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_845,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(sK1,sK2)
    | X0 != sK1
    | X1 != sK2 ),
    inference(instantiation,[status(thm)],[c_361])).

cnf(c_925,plain,
    ( r1_tarski(sK1,X0)
    | ~ r1_tarski(sK1,sK2)
    | X0 != sK2
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_845])).

cnf(c_928,plain,
    ( ~ r1_tarski(sK1,sK2)
    | r1_tarski(sK1,k1_xboole_0)
    | sK1 != sK1
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_925])).

cnf(c_1048,plain,
    ( ~ r1_xboole_0(sK1,sK2)
    | sK1 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1047])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_xboole_0(X1,X2)
    | r1_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_1353,plain,
    ( ~ r1_tarski(sK1,X0)
    | ~ r1_xboole_0(X0,sK2)
    | r1_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1355,plain,
    ( ~ r1_tarski(sK1,k1_xboole_0)
    | r1_xboole_0(sK1,sK2)
    | ~ r1_xboole_0(k1_xboole_0,sK2) ),
    inference(instantiation,[status(thm)],[c_1353])).

cnf(c_360,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2245,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,sK2)
    | X2 != X0
    | sK2 != X1 ),
    inference(instantiation,[status(thm)],[c_360])).

cnf(c_2247,plain,
    ( r1_xboole_0(k1_xboole_0,sK2)
    | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | sK2 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2245])).

cnf(c_2713,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2506,c_17,c_13,c_3,c_46,c_830,c_883,c_928,c_926,c_974,c_1048,c_1355,c_2247,c_2329])).

cnf(c_2509,plain,
    ( r1_tarski(k8_setfam_1(sK0,k1_xboole_0),k8_setfam_1(sK0,sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2497,c_718])).

cnf(c_2515,plain,
    ( r1_tarski(sK0,k8_setfam_1(sK0,sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2509,c_2317])).

cnf(c_2716,plain,
    ( r1_tarski(sK0,k8_setfam_1(sK0,k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2713,c_2515])).

cnf(c_2724,plain,
    ( r1_tarski(sK0,sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2716,c_2317])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2928,c_2724])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:12:16 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.92/1.03  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.03  
% 1.92/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.92/1.03  
% 1.92/1.03  ------  iProver source info
% 1.92/1.03  
% 1.92/1.03  git: date: 2020-06-30 10:37:57 +0100
% 1.92/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.92/1.03  git: non_committed_changes: false
% 1.92/1.03  git: last_make_outside_of_git: false
% 1.92/1.03  
% 1.92/1.03  ------ 
% 1.92/1.03  
% 1.92/1.03  ------ Input Options
% 1.92/1.03  
% 1.92/1.03  --out_options                           all
% 1.92/1.03  --tptp_safe_out                         true
% 1.92/1.03  --problem_path                          ""
% 1.92/1.03  --include_path                          ""
% 1.92/1.03  --clausifier                            res/vclausify_rel
% 1.92/1.03  --clausifier_options                    --mode clausify
% 1.92/1.03  --stdin                                 false
% 1.92/1.03  --stats_out                             all
% 1.92/1.03  
% 1.92/1.03  ------ General Options
% 1.92/1.03  
% 1.92/1.03  --fof                                   false
% 1.92/1.03  --time_out_real                         305.
% 1.92/1.03  --time_out_virtual                      -1.
% 1.92/1.03  --symbol_type_check                     false
% 1.92/1.03  --clausify_out                          false
% 1.92/1.03  --sig_cnt_out                           false
% 1.92/1.03  --trig_cnt_out                          false
% 1.92/1.03  --trig_cnt_out_tolerance                1.
% 1.92/1.03  --trig_cnt_out_sk_spl                   false
% 1.92/1.03  --abstr_cl_out                          false
% 1.92/1.03  
% 1.92/1.03  ------ Global Options
% 1.92/1.03  
% 1.92/1.03  --schedule                              default
% 1.92/1.03  --add_important_lit                     false
% 1.92/1.03  --prop_solver_per_cl                    1000
% 1.92/1.03  --min_unsat_core                        false
% 1.92/1.03  --soft_assumptions                      false
% 1.92/1.03  --soft_lemma_size                       3
% 1.92/1.03  --prop_impl_unit_size                   0
% 1.92/1.03  --prop_impl_unit                        []
% 1.92/1.03  --share_sel_clauses                     true
% 1.92/1.03  --reset_solvers                         false
% 1.92/1.03  --bc_imp_inh                            [conj_cone]
% 1.92/1.03  --conj_cone_tolerance                   3.
% 1.92/1.03  --extra_neg_conj                        none
% 1.92/1.03  --large_theory_mode                     true
% 1.92/1.03  --prolific_symb_bound                   200
% 1.92/1.03  --lt_threshold                          2000
% 1.92/1.03  --clause_weak_htbl                      true
% 1.92/1.03  --gc_record_bc_elim                     false
% 1.92/1.03  
% 1.92/1.03  ------ Preprocessing Options
% 1.92/1.03  
% 1.92/1.03  --preprocessing_flag                    true
% 1.92/1.03  --time_out_prep_mult                    0.1
% 1.92/1.03  --splitting_mode                        input
% 1.92/1.03  --splitting_grd                         true
% 1.92/1.03  --splitting_cvd                         false
% 1.92/1.03  --splitting_cvd_svl                     false
% 1.92/1.03  --splitting_nvd                         32
% 1.92/1.03  --sub_typing                            true
% 1.92/1.03  --prep_gs_sim                           true
% 1.92/1.03  --prep_unflatten                        true
% 1.92/1.03  --prep_res_sim                          true
% 1.92/1.03  --prep_upred                            true
% 1.92/1.03  --prep_sem_filter                       exhaustive
% 1.92/1.03  --prep_sem_filter_out                   false
% 1.92/1.03  --pred_elim                             true
% 1.92/1.03  --res_sim_input                         true
% 1.92/1.03  --eq_ax_congr_red                       true
% 1.92/1.03  --pure_diseq_elim                       true
% 1.92/1.03  --brand_transform                       false
% 1.92/1.03  --non_eq_to_eq                          false
% 1.92/1.03  --prep_def_merge                        true
% 1.92/1.03  --prep_def_merge_prop_impl              false
% 1.92/1.03  --prep_def_merge_mbd                    true
% 1.92/1.03  --prep_def_merge_tr_red                 false
% 1.92/1.03  --prep_def_merge_tr_cl                  false
% 1.92/1.03  --smt_preprocessing                     true
% 1.92/1.03  --smt_ac_axioms                         fast
% 1.92/1.03  --preprocessed_out                      false
% 1.92/1.03  --preprocessed_stats                    false
% 1.92/1.03  
% 1.92/1.03  ------ Abstraction refinement Options
% 1.92/1.03  
% 1.92/1.03  --abstr_ref                             []
% 1.92/1.03  --abstr_ref_prep                        false
% 1.92/1.03  --abstr_ref_until_sat                   false
% 1.92/1.03  --abstr_ref_sig_restrict                funpre
% 1.92/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 1.92/1.03  --abstr_ref_under                       []
% 1.92/1.03  
% 1.92/1.03  ------ SAT Options
% 1.92/1.03  
% 1.92/1.03  --sat_mode                              false
% 1.92/1.03  --sat_fm_restart_options                ""
% 1.92/1.03  --sat_gr_def                            false
% 1.92/1.03  --sat_epr_types                         true
% 1.92/1.03  --sat_non_cyclic_types                  false
% 1.92/1.03  --sat_finite_models                     false
% 1.92/1.03  --sat_fm_lemmas                         false
% 1.92/1.03  --sat_fm_prep                           false
% 1.92/1.03  --sat_fm_uc_incr                        true
% 1.92/1.03  --sat_out_model                         small
% 1.92/1.03  --sat_out_clauses                       false
% 1.92/1.03  
% 1.92/1.03  ------ QBF Options
% 1.92/1.03  
% 1.92/1.03  --qbf_mode                              false
% 1.92/1.03  --qbf_elim_univ                         false
% 1.92/1.03  --qbf_dom_inst                          none
% 1.92/1.03  --qbf_dom_pre_inst                      false
% 1.92/1.03  --qbf_sk_in                             false
% 1.92/1.03  --qbf_pred_elim                         true
% 1.92/1.03  --qbf_split                             512
% 1.92/1.03  
% 1.92/1.03  ------ BMC1 Options
% 1.92/1.03  
% 1.92/1.03  --bmc1_incremental                      false
% 1.92/1.03  --bmc1_axioms                           reachable_all
% 1.92/1.03  --bmc1_min_bound                        0
% 1.92/1.03  --bmc1_max_bound                        -1
% 1.92/1.03  --bmc1_max_bound_default                -1
% 1.92/1.03  --bmc1_symbol_reachability              true
% 1.92/1.03  --bmc1_property_lemmas                  false
% 1.92/1.03  --bmc1_k_induction                      false
% 1.92/1.03  --bmc1_non_equiv_states                 false
% 1.92/1.03  --bmc1_deadlock                         false
% 1.92/1.03  --bmc1_ucm                              false
% 1.92/1.03  --bmc1_add_unsat_core                   none
% 1.92/1.03  --bmc1_unsat_core_children              false
% 1.92/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 1.92/1.03  --bmc1_out_stat                         full
% 1.92/1.03  --bmc1_ground_init                      false
% 1.92/1.03  --bmc1_pre_inst_next_state              false
% 1.92/1.03  --bmc1_pre_inst_state                   false
% 1.92/1.03  --bmc1_pre_inst_reach_state             false
% 1.92/1.03  --bmc1_out_unsat_core                   false
% 1.92/1.03  --bmc1_aig_witness_out                  false
% 1.92/1.03  --bmc1_verbose                          false
% 1.92/1.03  --bmc1_dump_clauses_tptp                false
% 1.92/1.03  --bmc1_dump_unsat_core_tptp             false
% 1.92/1.03  --bmc1_dump_file                        -
% 1.92/1.03  --bmc1_ucm_expand_uc_limit              128
% 1.92/1.03  --bmc1_ucm_n_expand_iterations          6
% 1.92/1.03  --bmc1_ucm_extend_mode                  1
% 1.92/1.03  --bmc1_ucm_init_mode                    2
% 1.92/1.03  --bmc1_ucm_cone_mode                    none
% 1.92/1.03  --bmc1_ucm_reduced_relation_type        0
% 1.92/1.03  --bmc1_ucm_relax_model                  4
% 1.92/1.03  --bmc1_ucm_full_tr_after_sat            true
% 1.92/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 1.92/1.03  --bmc1_ucm_layered_model                none
% 1.92/1.03  --bmc1_ucm_max_lemma_size               10
% 1.92/1.03  
% 1.92/1.03  ------ AIG Options
% 1.92/1.03  
% 1.92/1.03  --aig_mode                              false
% 1.92/1.03  
% 1.92/1.03  ------ Instantiation Options
% 1.92/1.03  
% 1.92/1.03  --instantiation_flag                    true
% 1.92/1.03  --inst_sos_flag                         false
% 1.92/1.03  --inst_sos_phase                        true
% 1.92/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.92/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.92/1.03  --inst_lit_sel_side                     num_symb
% 1.92/1.03  --inst_solver_per_active                1400
% 1.92/1.03  --inst_solver_calls_frac                1.
% 1.92/1.03  --inst_passive_queue_type               priority_queues
% 1.92/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.92/1.03  --inst_passive_queues_freq              [25;2]
% 1.92/1.03  --inst_dismatching                      true
% 1.92/1.03  --inst_eager_unprocessed_to_passive     true
% 1.92/1.03  --inst_prop_sim_given                   true
% 1.92/1.03  --inst_prop_sim_new                     false
% 1.92/1.03  --inst_subs_new                         false
% 1.92/1.03  --inst_eq_res_simp                      false
% 1.92/1.03  --inst_subs_given                       false
% 1.92/1.03  --inst_orphan_elimination               true
% 1.92/1.03  --inst_learning_loop_flag               true
% 1.92/1.03  --inst_learning_start                   3000
% 1.92/1.03  --inst_learning_factor                  2
% 1.92/1.03  --inst_start_prop_sim_after_learn       3
% 1.92/1.03  --inst_sel_renew                        solver
% 1.92/1.03  --inst_lit_activity_flag                true
% 1.92/1.03  --inst_restr_to_given                   false
% 1.92/1.03  --inst_activity_threshold               500
% 1.92/1.03  --inst_out_proof                        true
% 1.92/1.03  
% 1.92/1.03  ------ Resolution Options
% 1.92/1.03  
% 1.92/1.03  --resolution_flag                       true
% 1.92/1.03  --res_lit_sel                           adaptive
% 1.92/1.03  --res_lit_sel_side                      none
% 1.92/1.03  --res_ordering                          kbo
% 1.92/1.03  --res_to_prop_solver                    active
% 1.92/1.03  --res_prop_simpl_new                    false
% 1.92/1.03  --res_prop_simpl_given                  true
% 1.92/1.03  --res_passive_queue_type                priority_queues
% 1.92/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.92/1.03  --res_passive_queues_freq               [15;5]
% 1.92/1.03  --res_forward_subs                      full
% 1.92/1.03  --res_backward_subs                     full
% 1.92/1.03  --res_forward_subs_resolution           true
% 1.92/1.03  --res_backward_subs_resolution          true
% 1.92/1.03  --res_orphan_elimination                true
% 1.92/1.03  --res_time_limit                        2.
% 1.92/1.03  --res_out_proof                         true
% 1.92/1.03  
% 1.92/1.03  ------ Superposition Options
% 1.92/1.03  
% 1.92/1.03  --superposition_flag                    true
% 1.92/1.03  --sup_passive_queue_type                priority_queues
% 1.92/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.92/1.03  --sup_passive_queues_freq               [8;1;4]
% 1.92/1.03  --demod_completeness_check              fast
% 1.92/1.03  --demod_use_ground                      true
% 1.92/1.03  --sup_to_prop_solver                    passive
% 1.92/1.03  --sup_prop_simpl_new                    true
% 1.92/1.03  --sup_prop_simpl_given                  true
% 1.92/1.03  --sup_fun_splitting                     false
% 1.92/1.03  --sup_smt_interval                      50000
% 1.92/1.03  
% 1.92/1.03  ------ Superposition Simplification Setup
% 1.92/1.03  
% 1.92/1.03  --sup_indices_passive                   []
% 1.92/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.92/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.92/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.92/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 1.92/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.92/1.03  --sup_full_bw                           [BwDemod]
% 1.92/1.03  --sup_immed_triv                        [TrivRules]
% 1.92/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.92/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.92/1.03  --sup_immed_bw_main                     []
% 1.92/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.92/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 1.92/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.92/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.92/1.03  
% 1.92/1.03  ------ Combination Options
% 1.92/1.03  
% 1.92/1.03  --comb_res_mult                         3
% 1.92/1.03  --comb_sup_mult                         2
% 1.92/1.03  --comb_inst_mult                        10
% 1.92/1.03  
% 1.92/1.03  ------ Debug Options
% 1.92/1.03  
% 1.92/1.03  --dbg_backtrace                         false
% 1.92/1.03  --dbg_dump_prop_clauses                 false
% 1.92/1.03  --dbg_dump_prop_clauses_file            -
% 1.92/1.03  --dbg_out_stat                          false
% 1.92/1.03  ------ Parsing...
% 1.92/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.92/1.03  
% 1.92/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 1.92/1.03  
% 1.92/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.92/1.03  
% 1.92/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.92/1.03  ------ Proving...
% 1.92/1.03  ------ Problem Properties 
% 1.92/1.03  
% 1.92/1.03  
% 1.92/1.03  clauses                                 15
% 1.92/1.03  conjectures                             4
% 1.92/1.03  EPR                                     5
% 1.92/1.03  Horn                                    13
% 1.92/1.03  unary                                   5
% 1.92/1.03  binary                                  6
% 1.92/1.03  lits                                    29
% 1.92/1.03  lits eq                                 7
% 1.92/1.03  fd_pure                                 0
% 1.92/1.03  fd_pseudo                               0
% 1.92/1.03  fd_cond                                 4
% 1.92/1.03  fd_pseudo_cond                          0
% 1.92/1.03  AC symbols                              0
% 1.92/1.03  
% 1.92/1.03  ------ Schedule dynamic 5 is on 
% 1.92/1.03  
% 1.92/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.92/1.03  
% 1.92/1.03  
% 1.92/1.03  ------ 
% 1.92/1.03  Current options:
% 1.92/1.03  ------ 
% 1.92/1.03  
% 1.92/1.03  ------ Input Options
% 1.92/1.03  
% 1.92/1.03  --out_options                           all
% 1.92/1.03  --tptp_safe_out                         true
% 1.92/1.03  --problem_path                          ""
% 1.92/1.03  --include_path                          ""
% 1.92/1.03  --clausifier                            res/vclausify_rel
% 1.92/1.03  --clausifier_options                    --mode clausify
% 1.92/1.03  --stdin                                 false
% 1.92/1.03  --stats_out                             all
% 1.92/1.03  
% 1.92/1.03  ------ General Options
% 1.92/1.03  
% 1.92/1.03  --fof                                   false
% 1.92/1.03  --time_out_real                         305.
% 1.92/1.03  --time_out_virtual                      -1.
% 1.92/1.03  --symbol_type_check                     false
% 1.92/1.03  --clausify_out                          false
% 1.92/1.03  --sig_cnt_out                           false
% 1.92/1.03  --trig_cnt_out                          false
% 1.92/1.03  --trig_cnt_out_tolerance                1.
% 1.92/1.03  --trig_cnt_out_sk_spl                   false
% 1.92/1.03  --abstr_cl_out                          false
% 1.92/1.03  
% 1.92/1.03  ------ Global Options
% 1.92/1.03  
% 1.92/1.03  --schedule                              default
% 1.92/1.03  --add_important_lit                     false
% 1.92/1.03  --prop_solver_per_cl                    1000
% 1.92/1.03  --min_unsat_core                        false
% 1.92/1.03  --soft_assumptions                      false
% 1.92/1.03  --soft_lemma_size                       3
% 1.92/1.03  --prop_impl_unit_size                   0
% 1.92/1.03  --prop_impl_unit                        []
% 1.92/1.03  --share_sel_clauses                     true
% 1.92/1.03  --reset_solvers                         false
% 1.92/1.03  --bc_imp_inh                            [conj_cone]
% 1.92/1.03  --conj_cone_tolerance                   3.
% 1.92/1.03  --extra_neg_conj                        none
% 1.92/1.03  --large_theory_mode                     true
% 1.92/1.03  --prolific_symb_bound                   200
% 1.92/1.03  --lt_threshold                          2000
% 1.92/1.03  --clause_weak_htbl                      true
% 1.92/1.03  --gc_record_bc_elim                     false
% 1.92/1.03  
% 1.92/1.03  ------ Preprocessing Options
% 1.92/1.03  
% 1.92/1.03  --preprocessing_flag                    true
% 1.92/1.03  --time_out_prep_mult                    0.1
% 1.92/1.03  --splitting_mode                        input
% 1.92/1.03  --splitting_grd                         true
% 1.92/1.03  --splitting_cvd                         false
% 1.92/1.03  --splitting_cvd_svl                     false
% 1.92/1.03  --splitting_nvd                         32
% 1.92/1.03  --sub_typing                            true
% 1.92/1.03  --prep_gs_sim                           true
% 1.92/1.03  --prep_unflatten                        true
% 1.92/1.03  --prep_res_sim                          true
% 1.92/1.03  --prep_upred                            true
% 1.92/1.03  --prep_sem_filter                       exhaustive
% 1.92/1.03  --prep_sem_filter_out                   false
% 1.92/1.03  --pred_elim                             true
% 1.92/1.03  --res_sim_input                         true
% 1.92/1.03  --eq_ax_congr_red                       true
% 1.92/1.03  --pure_diseq_elim                       true
% 1.92/1.03  --brand_transform                       false
% 1.92/1.03  --non_eq_to_eq                          false
% 1.92/1.03  --prep_def_merge                        true
% 1.92/1.03  --prep_def_merge_prop_impl              false
% 1.92/1.03  --prep_def_merge_mbd                    true
% 1.92/1.03  --prep_def_merge_tr_red                 false
% 1.92/1.03  --prep_def_merge_tr_cl                  false
% 1.92/1.03  --smt_preprocessing                     true
% 1.92/1.03  --smt_ac_axioms                         fast
% 1.92/1.03  --preprocessed_out                      false
% 1.92/1.03  --preprocessed_stats                    false
% 1.92/1.03  
% 1.92/1.03  ------ Abstraction refinement Options
% 1.92/1.03  
% 1.92/1.03  --abstr_ref                             []
% 1.92/1.03  --abstr_ref_prep                        false
% 1.92/1.03  --abstr_ref_until_sat                   false
% 1.92/1.03  --abstr_ref_sig_restrict                funpre
% 1.92/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 1.92/1.03  --abstr_ref_under                       []
% 1.92/1.03  
% 1.92/1.03  ------ SAT Options
% 1.92/1.03  
% 1.92/1.03  --sat_mode                              false
% 1.92/1.03  --sat_fm_restart_options                ""
% 1.92/1.03  --sat_gr_def                            false
% 1.92/1.03  --sat_epr_types                         true
% 1.92/1.03  --sat_non_cyclic_types                  false
% 1.92/1.03  --sat_finite_models                     false
% 1.92/1.03  --sat_fm_lemmas                         false
% 1.92/1.03  --sat_fm_prep                           false
% 1.92/1.03  --sat_fm_uc_incr                        true
% 1.92/1.03  --sat_out_model                         small
% 1.92/1.03  --sat_out_clauses                       false
% 1.92/1.03  
% 1.92/1.03  ------ QBF Options
% 1.92/1.03  
% 1.92/1.03  --qbf_mode                              false
% 1.92/1.03  --qbf_elim_univ                         false
% 1.92/1.03  --qbf_dom_inst                          none
% 1.92/1.03  --qbf_dom_pre_inst                      false
% 1.92/1.03  --qbf_sk_in                             false
% 1.92/1.03  --qbf_pred_elim                         true
% 1.92/1.03  --qbf_split                             512
% 1.92/1.03  
% 1.92/1.03  ------ BMC1 Options
% 1.92/1.03  
% 1.92/1.03  --bmc1_incremental                      false
% 1.92/1.03  --bmc1_axioms                           reachable_all
% 1.92/1.03  --bmc1_min_bound                        0
% 1.92/1.03  --bmc1_max_bound                        -1
% 1.92/1.03  --bmc1_max_bound_default                -1
% 1.92/1.03  --bmc1_symbol_reachability              true
% 1.92/1.03  --bmc1_property_lemmas                  false
% 1.92/1.03  --bmc1_k_induction                      false
% 1.92/1.03  --bmc1_non_equiv_states                 false
% 1.92/1.03  --bmc1_deadlock                         false
% 1.92/1.03  --bmc1_ucm                              false
% 1.92/1.03  --bmc1_add_unsat_core                   none
% 1.92/1.03  --bmc1_unsat_core_children              false
% 1.92/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 1.92/1.03  --bmc1_out_stat                         full
% 1.92/1.03  --bmc1_ground_init                      false
% 1.92/1.03  --bmc1_pre_inst_next_state              false
% 1.92/1.03  --bmc1_pre_inst_state                   false
% 1.92/1.03  --bmc1_pre_inst_reach_state             false
% 1.92/1.03  --bmc1_out_unsat_core                   false
% 1.92/1.03  --bmc1_aig_witness_out                  false
% 1.92/1.03  --bmc1_verbose                          false
% 1.92/1.03  --bmc1_dump_clauses_tptp                false
% 1.92/1.03  --bmc1_dump_unsat_core_tptp             false
% 1.92/1.03  --bmc1_dump_file                        -
% 1.92/1.03  --bmc1_ucm_expand_uc_limit              128
% 1.92/1.03  --bmc1_ucm_n_expand_iterations          6
% 1.92/1.03  --bmc1_ucm_extend_mode                  1
% 1.92/1.03  --bmc1_ucm_init_mode                    2
% 1.92/1.03  --bmc1_ucm_cone_mode                    none
% 1.92/1.03  --bmc1_ucm_reduced_relation_type        0
% 1.92/1.03  --bmc1_ucm_relax_model                  4
% 1.92/1.03  --bmc1_ucm_full_tr_after_sat            true
% 1.92/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 1.92/1.03  --bmc1_ucm_layered_model                none
% 1.92/1.03  --bmc1_ucm_max_lemma_size               10
% 1.92/1.03  
% 1.92/1.03  ------ AIG Options
% 1.92/1.03  
% 1.92/1.03  --aig_mode                              false
% 1.92/1.03  
% 1.92/1.03  ------ Instantiation Options
% 1.92/1.03  
% 1.92/1.03  --instantiation_flag                    true
% 1.92/1.03  --inst_sos_flag                         false
% 1.92/1.03  --inst_sos_phase                        true
% 1.92/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.92/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.92/1.03  --inst_lit_sel_side                     none
% 1.92/1.03  --inst_solver_per_active                1400
% 1.92/1.03  --inst_solver_calls_frac                1.
% 1.92/1.03  --inst_passive_queue_type               priority_queues
% 1.92/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.92/1.03  --inst_passive_queues_freq              [25;2]
% 1.92/1.03  --inst_dismatching                      true
% 1.92/1.03  --inst_eager_unprocessed_to_passive     true
% 1.92/1.03  --inst_prop_sim_given                   true
% 1.92/1.03  --inst_prop_sim_new                     false
% 1.92/1.03  --inst_subs_new                         false
% 1.92/1.03  --inst_eq_res_simp                      false
% 1.92/1.03  --inst_subs_given                       false
% 1.92/1.03  --inst_orphan_elimination               true
% 1.92/1.03  --inst_learning_loop_flag               true
% 1.92/1.03  --inst_learning_start                   3000
% 1.92/1.03  --inst_learning_factor                  2
% 1.92/1.03  --inst_start_prop_sim_after_learn       3
% 1.92/1.03  --inst_sel_renew                        solver
% 1.92/1.03  --inst_lit_activity_flag                true
% 1.92/1.03  --inst_restr_to_given                   false
% 1.92/1.03  --inst_activity_threshold               500
% 1.92/1.03  --inst_out_proof                        true
% 1.92/1.03  
% 1.92/1.03  ------ Resolution Options
% 1.92/1.03  
% 1.92/1.03  --resolution_flag                       false
% 1.92/1.03  --res_lit_sel                           adaptive
% 1.92/1.03  --res_lit_sel_side                      none
% 1.92/1.03  --res_ordering                          kbo
% 1.92/1.03  --res_to_prop_solver                    active
% 1.92/1.03  --res_prop_simpl_new                    false
% 1.92/1.03  --res_prop_simpl_given                  true
% 1.92/1.03  --res_passive_queue_type                priority_queues
% 1.92/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.92/1.03  --res_passive_queues_freq               [15;5]
% 1.92/1.03  --res_forward_subs                      full
% 1.92/1.03  --res_backward_subs                     full
% 1.92/1.03  --res_forward_subs_resolution           true
% 1.92/1.03  --res_backward_subs_resolution          true
% 1.92/1.03  --res_orphan_elimination                true
% 1.92/1.03  --res_time_limit                        2.
% 1.92/1.03  --res_out_proof                         true
% 1.92/1.03  
% 1.92/1.03  ------ Superposition Options
% 1.92/1.03  
% 1.92/1.03  --superposition_flag                    true
% 1.92/1.03  --sup_passive_queue_type                priority_queues
% 1.92/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.92/1.03  --sup_passive_queues_freq               [8;1;4]
% 1.92/1.03  --demod_completeness_check              fast
% 1.92/1.03  --demod_use_ground                      true
% 1.92/1.03  --sup_to_prop_solver                    passive
% 1.92/1.03  --sup_prop_simpl_new                    true
% 1.92/1.03  --sup_prop_simpl_given                  true
% 1.92/1.03  --sup_fun_splitting                     false
% 1.92/1.03  --sup_smt_interval                      50000
% 1.92/1.03  
% 1.92/1.03  ------ Superposition Simplification Setup
% 1.92/1.03  
% 1.92/1.03  --sup_indices_passive                   []
% 1.92/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.92/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.92/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.92/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 1.92/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.92/1.03  --sup_full_bw                           [BwDemod]
% 1.92/1.03  --sup_immed_triv                        [TrivRules]
% 1.92/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.92/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.92/1.03  --sup_immed_bw_main                     []
% 1.92/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.92/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 1.92/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.92/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.92/1.03  
% 1.92/1.03  ------ Combination Options
% 1.92/1.03  
% 1.92/1.03  --comb_res_mult                         3
% 1.92/1.03  --comb_sup_mult                         2
% 1.92/1.03  --comb_inst_mult                        10
% 1.92/1.03  
% 1.92/1.03  ------ Debug Options
% 1.92/1.03  
% 1.92/1.03  --dbg_backtrace                         false
% 1.92/1.03  --dbg_dump_prop_clauses                 false
% 1.92/1.03  --dbg_dump_prop_clauses_file            -
% 1.92/1.03  --dbg_out_stat                          false
% 1.92/1.03  
% 1.92/1.03  
% 1.92/1.03  
% 1.92/1.03  
% 1.92/1.03  ------ Proving...
% 1.92/1.03  
% 1.92/1.03  
% 1.92/1.03  % SZS status Theorem for theBenchmark.p
% 1.92/1.03  
% 1.92/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 1.92/1.03  
% 1.92/1.03  fof(f10,conjecture,(
% 1.92/1.03    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 1.92/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.92/1.03  
% 1.92/1.03  fof(f11,negated_conjecture,(
% 1.92/1.03    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 1.92/1.03    inference(negated_conjecture,[],[f10])).
% 1.92/1.03  
% 1.92/1.03  fof(f23,plain,(
% 1.92/1.03    ? [X0,X1] : (? [X2] : ((~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.92/1.03    inference(ennf_transformation,[],[f11])).
% 1.92/1.03  
% 1.92/1.03  fof(f24,plain,(
% 1.92/1.03    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.92/1.03    inference(flattening,[],[f23])).
% 1.92/1.03  
% 1.92/1.03  fof(f27,plain,(
% 1.92/1.03    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (~r1_tarski(k8_setfam_1(X0,sK2),k8_setfam_1(X0,X1)) & r1_tarski(X1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(X0))))) )),
% 1.92/1.03    introduced(choice_axiom,[])).
% 1.92/1.03  
% 1.92/1.03  fof(f26,plain,(
% 1.92/1.03    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (? [X2] : (~r1_tarski(k8_setfam_1(sK0,X2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 1.92/1.03    introduced(choice_axiom,[])).
% 1.92/1.03  
% 1.92/1.03  fof(f28,plain,(
% 1.92/1.03    (~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 1.92/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f27,f26])).
% 1.92/1.03  
% 1.92/1.03  fof(f42,plain,(
% 1.92/1.03    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 1.92/1.03    inference(cnf_transformation,[],[f28])).
% 1.92/1.03  
% 1.92/1.03  fof(f5,axiom,(
% 1.92/1.03    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((k1_xboole_0 = X1 => k8_setfam_1(X0,X1) = X0) & (k1_xboole_0 != X1 => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1))))),
% 1.92/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.92/1.03  
% 1.92/1.03  fof(f18,plain,(
% 1.92/1.03    ! [X0,X1] : (((k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1) & (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.92/1.03    inference(ennf_transformation,[],[f5])).
% 1.92/1.03  
% 1.92/1.03  fof(f34,plain,(
% 1.92/1.03    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.92/1.03    inference(cnf_transformation,[],[f18])).
% 1.92/1.03  
% 1.92/1.03  fof(f7,axiom,(
% 1.92/1.03    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k6_setfam_1(X0,X1) = k1_setfam_1(X1))),
% 1.92/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.92/1.03  
% 1.92/1.03  fof(f20,plain,(
% 1.92/1.03    ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.92/1.03    inference(ennf_transformation,[],[f7])).
% 1.92/1.03  
% 1.92/1.03  fof(f37,plain,(
% 1.92/1.03    ( ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.92/1.03    inference(cnf_transformation,[],[f20])).
% 1.92/1.03  
% 1.92/1.03  fof(f41,plain,(
% 1.92/1.03    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 1.92/1.03    inference(cnf_transformation,[],[f28])).
% 1.92/1.03  
% 1.92/1.03  fof(f44,plain,(
% 1.92/1.03    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))),
% 1.92/1.03    inference(cnf_transformation,[],[f28])).
% 1.92/1.03  
% 1.92/1.03  fof(f43,plain,(
% 1.92/1.03    r1_tarski(sK1,sK2)),
% 1.92/1.03    inference(cnf_transformation,[],[f28])).
% 1.92/1.03  
% 1.92/1.03  fof(f9,axiom,(
% 1.92/1.03    ! [X0,X1] : (r1_tarski(X0,X1) => (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 1.92/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.92/1.03  
% 1.92/1.03  fof(f21,plain,(
% 1.92/1.03    ! [X0,X1] : ((r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0) | ~r1_tarski(X0,X1))),
% 1.92/1.03    inference(ennf_transformation,[],[f9])).
% 1.92/1.03  
% 1.92/1.03  fof(f22,plain,(
% 1.92/1.03    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1))),
% 1.92/1.03    inference(flattening,[],[f21])).
% 1.92/1.03  
% 1.92/1.03  fof(f40,plain,(
% 1.92/1.03    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1)) )),
% 1.92/1.03    inference(cnf_transformation,[],[f22])).
% 1.92/1.03  
% 1.92/1.03  fof(f3,axiom,(
% 1.92/1.03    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 1.92/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.92/1.03  
% 1.92/1.03  fof(f15,plain,(
% 1.92/1.03    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 1.92/1.03    inference(ennf_transformation,[],[f3])).
% 1.92/1.03  
% 1.92/1.03  fof(f31,plain,(
% 1.92/1.03    ( ! [X0] : (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)) )),
% 1.92/1.03    inference(cnf_transformation,[],[f15])).
% 1.92/1.03  
% 1.92/1.03  fof(f45,plain,(
% 1.92/1.03    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.92/1.03    inference(equality_resolution,[],[f31])).
% 1.92/1.03  
% 1.92/1.03  fof(f32,plain,(
% 1.92/1.03    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 1.92/1.03    inference(cnf_transformation,[],[f15])).
% 1.92/1.03  
% 1.92/1.03  fof(f6,axiom,(
% 1.92/1.03    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.92/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.92/1.03  
% 1.92/1.03  fof(f19,plain,(
% 1.92/1.03    ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.92/1.03    inference(ennf_transformation,[],[f6])).
% 1.92/1.03  
% 1.92/1.03  fof(f36,plain,(
% 1.92/1.03    ( ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.92/1.03    inference(cnf_transformation,[],[f19])).
% 1.92/1.03  
% 1.92/1.03  fof(f8,axiom,(
% 1.92/1.03    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.92/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.92/1.03  
% 1.92/1.03  fof(f25,plain,(
% 1.92/1.03    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.92/1.03    inference(nnf_transformation,[],[f8])).
% 1.92/1.03  
% 1.92/1.03  fof(f38,plain,(
% 1.92/1.03    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.92/1.03    inference(cnf_transformation,[],[f25])).
% 1.92/1.03  
% 1.92/1.03  fof(f35,plain,(
% 1.92/1.03    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.92/1.03    inference(cnf_transformation,[],[f18])).
% 1.92/1.03  
% 1.92/1.03  fof(f46,plain,(
% 1.92/1.03    ( ! [X0] : (k8_setfam_1(X0,k1_xboole_0) = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.92/1.03    inference(equality_resolution,[],[f35])).
% 1.92/1.03  
% 1.92/1.03  fof(f4,axiom,(
% 1.92/1.03    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 1.92/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.92/1.03  
% 1.92/1.03  fof(f16,plain,(
% 1.92/1.03    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 1.92/1.03    inference(ennf_transformation,[],[f4])).
% 1.92/1.03  
% 1.92/1.03  fof(f17,plain,(
% 1.92/1.03    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 1.92/1.03    inference(flattening,[],[f16])).
% 1.92/1.03  
% 1.92/1.03  fof(f33,plain,(
% 1.92/1.03    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 1.92/1.03    inference(cnf_transformation,[],[f17])).
% 1.92/1.03  
% 1.92/1.03  fof(f1,axiom,(
% 1.92/1.03    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.92/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.92/1.03  
% 1.92/1.03  fof(f12,plain,(
% 1.92/1.03    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.92/1.03    inference(ennf_transformation,[],[f1])).
% 1.92/1.03  
% 1.92/1.03  fof(f29,plain,(
% 1.92/1.03    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 1.92/1.03    inference(cnf_transformation,[],[f12])).
% 1.92/1.03  
% 1.92/1.03  fof(f2,axiom,(
% 1.92/1.03    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 1.92/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.92/1.03  
% 1.92/1.03  fof(f13,plain,(
% 1.92/1.03    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.92/1.03    inference(ennf_transformation,[],[f2])).
% 1.92/1.03  
% 1.92/1.03  fof(f14,plain,(
% 1.92/1.03    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 1.92/1.03    inference(flattening,[],[f13])).
% 1.92/1.03  
% 1.92/1.03  fof(f30,plain,(
% 1.92/1.03    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 1.92/1.03    inference(cnf_transformation,[],[f14])).
% 1.92/1.03  
% 1.92/1.03  cnf(c_14,negated_conjecture,
% 1.92/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
% 1.92/1.03      inference(cnf_transformation,[],[f42]) ).
% 1.92/1.03  
% 1.92/1.03  cnf(c_716,plain,
% 1.92/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) = iProver_top ),
% 1.92/1.03      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 1.92/1.04  
% 1.92/1.04  cnf(c_6,plain,
% 1.92/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 1.92/1.04      | k6_setfam_1(X1,X0) = k8_setfam_1(X1,X0)
% 1.92/1.04      | k1_xboole_0 = X0 ),
% 1.92/1.04      inference(cnf_transformation,[],[f34]) ).
% 1.92/1.04  
% 1.92/1.04  cnf(c_724,plain,
% 1.92/1.04      ( k6_setfam_1(X0,X1) = k8_setfam_1(X0,X1)
% 1.92/1.04      | k1_xboole_0 = X1
% 1.92/1.04      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 1.92/1.04      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 1.92/1.04  
% 1.92/1.04  cnf(c_1724,plain,
% 1.92/1.04      ( k6_setfam_1(sK0,sK2) = k8_setfam_1(sK0,sK2) | sK2 = k1_xboole_0 ),
% 1.92/1.04      inference(superposition,[status(thm)],[c_716,c_724]) ).
% 1.92/1.04  
% 1.92/1.04  cnf(c_8,plain,
% 1.92/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 1.92/1.04      | k6_setfam_1(X1,X0) = k1_setfam_1(X0) ),
% 1.92/1.04      inference(cnf_transformation,[],[f37]) ).
% 1.92/1.04  
% 1.92/1.04  cnf(c_722,plain,
% 1.92/1.04      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
% 1.92/1.04      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 1.92/1.04      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 1.92/1.04  
% 1.92/1.04  cnf(c_1240,plain,
% 1.92/1.04      ( k6_setfam_1(sK0,sK2) = k1_setfam_1(sK2) ),
% 1.92/1.04      inference(superposition,[status(thm)],[c_716,c_722]) ).
% 1.92/1.04  
% 1.92/1.04  cnf(c_1733,plain,
% 1.92/1.04      ( k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) | sK2 = k1_xboole_0 ),
% 1.92/1.04      inference(light_normalisation,[status(thm)],[c_1724,c_1240]) ).
% 1.92/1.04  
% 1.92/1.04  cnf(c_15,negated_conjecture,
% 1.92/1.04      ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
% 1.92/1.04      inference(cnf_transformation,[],[f41]) ).
% 1.92/1.04  
% 1.92/1.04  cnf(c_715,plain,
% 1.92/1.04      ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) = iProver_top ),
% 1.92/1.04      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 1.92/1.04  
% 1.92/1.04  cnf(c_1725,plain,
% 1.92/1.04      ( k6_setfam_1(sK0,sK1) = k8_setfam_1(sK0,sK1) | sK1 = k1_xboole_0 ),
% 1.92/1.04      inference(superposition,[status(thm)],[c_715,c_724]) ).
% 1.92/1.04  
% 1.92/1.04  cnf(c_1241,plain,
% 1.92/1.04      ( k6_setfam_1(sK0,sK1) = k1_setfam_1(sK1) ),
% 1.92/1.04      inference(superposition,[status(thm)],[c_715,c_722]) ).
% 1.92/1.04  
% 1.92/1.04  cnf(c_1728,plain,
% 1.92/1.04      ( k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1) | sK1 = k1_xboole_0 ),
% 1.92/1.04      inference(light_normalisation,[status(thm)],[c_1725,c_1241]) ).
% 1.92/1.04  
% 1.92/1.04  cnf(c_12,negated_conjecture,
% 1.92/1.04      ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) ),
% 1.92/1.04      inference(cnf_transformation,[],[f44]) ).
% 1.92/1.04  
% 1.92/1.04  cnf(c_718,plain,
% 1.92/1.04      ( r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) != iProver_top ),
% 1.92/1.04      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 1.92/1.04  
% 1.92/1.04  cnf(c_2033,plain,
% 1.92/1.04      ( sK1 = k1_xboole_0
% 1.92/1.04      | r1_tarski(k8_setfam_1(sK0,sK2),k1_setfam_1(sK1)) != iProver_top ),
% 1.92/1.04      inference(superposition,[status(thm)],[c_1728,c_718]) ).
% 1.92/1.04  
% 1.92/1.04  cnf(c_2067,plain,
% 1.92/1.04      ( sK1 = k1_xboole_0
% 1.92/1.04      | sK2 = k1_xboole_0
% 1.92/1.04      | r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) != iProver_top ),
% 1.92/1.04      inference(superposition,[status(thm)],[c_1733,c_2033]) ).
% 1.92/1.04  
% 1.92/1.04  cnf(c_13,negated_conjecture,
% 1.92/1.04      ( r1_tarski(sK1,sK2) ),
% 1.92/1.04      inference(cnf_transformation,[],[f43]) ).
% 1.92/1.04  
% 1.92/1.04  cnf(c_18,plain,
% 1.92/1.04      ( r1_tarski(sK1,sK2) = iProver_top ),
% 1.92/1.04      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 1.92/1.04  
% 1.92/1.04  cnf(c_358,plain,( X0 = X0 ),theory(equality) ).
% 1.92/1.04  
% 1.92/1.04  cnf(c_926,plain,
% 1.92/1.04      ( sK1 = sK1 ),
% 1.92/1.04      inference(instantiation,[status(thm)],[c_358]) ).
% 1.92/1.04  
% 1.92/1.04  cnf(c_11,plain,
% 1.92/1.04      ( ~ r1_tarski(X0,X1)
% 1.92/1.04      | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
% 1.92/1.04      | k1_xboole_0 = X0 ),
% 1.92/1.04      inference(cnf_transformation,[],[f40]) ).
% 1.92/1.04  
% 1.92/1.04  cnf(c_908,plain,
% 1.92/1.04      ( r1_tarski(k1_setfam_1(X0),k1_setfam_1(sK1))
% 1.92/1.04      | ~ r1_tarski(sK1,X0)
% 1.92/1.04      | k1_xboole_0 = sK1 ),
% 1.92/1.04      inference(instantiation,[status(thm)],[c_11]) ).
% 1.92/1.04  
% 1.92/1.04  cnf(c_1026,plain,
% 1.92/1.04      ( r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1))
% 1.92/1.04      | ~ r1_tarski(sK1,sK2)
% 1.92/1.04      | k1_xboole_0 = sK1 ),
% 1.92/1.04      inference(instantiation,[status(thm)],[c_908]) ).
% 1.92/1.04  
% 1.92/1.04  cnf(c_1027,plain,
% 1.92/1.04      ( k1_xboole_0 = sK1
% 1.92/1.04      | r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) = iProver_top
% 1.92/1.04      | r1_tarski(sK1,sK2) != iProver_top ),
% 1.92/1.04      inference(predicate_to_equality,[status(thm)],[c_1026]) ).
% 1.92/1.04  
% 1.92/1.04  cnf(c_359,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 1.92/1.04  
% 1.92/1.04  cnf(c_1140,plain,
% 1.92/1.04      ( X0 != X1 | sK1 != X1 | sK1 = X0 ),
% 1.92/1.04      inference(instantiation,[status(thm)],[c_359]) ).
% 1.92/1.04  
% 1.92/1.04  cnf(c_1657,plain,
% 1.92/1.04      ( X0 != sK1 | sK1 = X0 | sK1 != sK1 ),
% 1.92/1.04      inference(instantiation,[status(thm)],[c_1140]) ).
% 1.92/1.04  
% 1.92/1.04  cnf(c_1658,plain,
% 1.92/1.04      ( sK1 != sK1 | sK1 = k1_xboole_0 | k1_xboole_0 != sK1 ),
% 1.92/1.04      inference(instantiation,[status(thm)],[c_1657]) ).
% 1.92/1.04  
% 1.92/1.04  cnf(c_2143,plain,
% 1.92/1.04      ( sK2 = k1_xboole_0 | sK1 = k1_xboole_0 ),
% 1.92/1.04      inference(global_propositional_subsumption,
% 1.92/1.04                [status(thm)],
% 1.92/1.04                [c_2067,c_18,c_926,c_1027,c_1658]) ).
% 1.92/1.04  
% 1.92/1.04  cnf(c_2144,plain,
% 1.92/1.04      ( sK1 = k1_xboole_0 | sK2 = k1_xboole_0 ),
% 1.92/1.04      inference(renaming,[status(thm)],[c_2143]) ).
% 1.92/1.04  
% 1.92/1.04  cnf(c_2155,plain,
% 1.92/1.04      ( sK2 = k1_xboole_0
% 1.92/1.04      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) = iProver_top ),
% 1.92/1.04      inference(superposition,[status(thm)],[c_2144,c_715]) ).
% 1.92/1.04  
% 1.92/1.04  cnf(c_17,plain,
% 1.92/1.04      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) = iProver_top ),
% 1.92/1.04      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 1.92/1.04  
% 1.92/1.04  cnf(c_3,plain,
% 1.92/1.04      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 1.92/1.04      inference(cnf_transformation,[],[f45]) ).
% 1.92/1.04  
% 1.92/1.04  cnf(c_2,plain,
% 1.92/1.04      ( ~ r1_xboole_0(X0,X0) | k1_xboole_0 = X0 ),
% 1.92/1.04      inference(cnf_transformation,[],[f32]) ).
% 1.92/1.04  
% 1.92/1.04  cnf(c_46,plain,
% 1.92/1.04      ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
% 1.92/1.04      | k1_xboole_0 = k1_xboole_0 ),
% 1.92/1.04      inference(instantiation,[status(thm)],[c_2]) ).
% 1.92/1.04  
% 1.92/1.04  cnf(c_973,plain,
% 1.92/1.04      ( X0 != X1 | X0 = sK2 | sK2 != X1 ),
% 1.92/1.04      inference(instantiation,[status(thm)],[c_359]) ).
% 1.92/1.04  
% 1.92/1.04  cnf(c_974,plain,
% 1.92/1.04      ( sK2 != k1_xboole_0
% 1.92/1.04      | k1_xboole_0 = sK2
% 1.92/1.04      | k1_xboole_0 != k1_xboole_0 ),
% 1.92/1.04      inference(instantiation,[status(thm)],[c_973]) ).
% 1.92/1.04  
% 1.92/1.04  cnf(c_1184,plain,
% 1.92/1.04      ( k1_zfmisc_1(k1_zfmisc_1(sK0)) = k1_zfmisc_1(k1_zfmisc_1(sK0)) ),
% 1.92/1.04      inference(instantiation,[status(thm)],[c_358]) ).
% 1.92/1.04  
% 1.92/1.04  cnf(c_364,plain,
% 1.92/1.04      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 1.92/1.04      theory(equality) ).
% 1.92/1.04  
% 1.92/1.04  cnf(c_850,plain,
% 1.92/1.04      ( m1_subset_1(X0,X1)
% 1.92/1.04      | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
% 1.92/1.04      | X1 != k1_zfmisc_1(k1_zfmisc_1(sK0))
% 1.92/1.04      | X0 != sK2 ),
% 1.92/1.04      inference(instantiation,[status(thm)],[c_364]) ).
% 1.92/1.04  
% 1.92/1.04  cnf(c_1793,plain,
% 1.92/1.04      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
% 1.92/1.04      | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
% 1.92/1.04      | X0 != sK2
% 1.92/1.04      | k1_zfmisc_1(k1_zfmisc_1(sK0)) != k1_zfmisc_1(k1_zfmisc_1(sK0)) ),
% 1.92/1.04      inference(instantiation,[status(thm)],[c_850]) ).
% 1.92/1.04  
% 1.92/1.04  cnf(c_1794,plain,
% 1.92/1.04      ( X0 != sK2
% 1.92/1.04      | k1_zfmisc_1(k1_zfmisc_1(sK0)) != k1_zfmisc_1(k1_zfmisc_1(sK0))
% 1.92/1.04      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0))) = iProver_top
% 1.92/1.04      | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) != iProver_top ),
% 1.92/1.04      inference(predicate_to_equality,[status(thm)],[c_1793]) ).
% 1.92/1.04  
% 1.92/1.04  cnf(c_1796,plain,
% 1.92/1.04      ( k1_zfmisc_1(k1_zfmisc_1(sK0)) != k1_zfmisc_1(k1_zfmisc_1(sK0))
% 1.92/1.04      | k1_xboole_0 != sK2
% 1.92/1.04      | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) != iProver_top
% 1.92/1.04      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) = iProver_top ),
% 1.92/1.04      inference(instantiation,[status(thm)],[c_1794]) ).
% 1.92/1.04  
% 1.92/1.04  cnf(c_2312,plain,
% 1.92/1.04      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) = iProver_top ),
% 1.92/1.04      inference(global_propositional_subsumption,
% 1.92/1.04                [status(thm)],
% 1.92/1.04                [c_2155,c_17,c_3,c_46,c_974,c_1184,c_1796]) ).
% 1.92/1.04  
% 1.92/1.04  cnf(c_7,plain,
% 1.92/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 1.92/1.04      | m1_subset_1(k8_setfam_1(X1,X0),k1_zfmisc_1(X1)) ),
% 1.92/1.04      inference(cnf_transformation,[],[f36]) ).
% 1.92/1.04  
% 1.92/1.04  cnf(c_723,plain,
% 1.92/1.04      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 1.92/1.04      | m1_subset_1(k8_setfam_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 1.92/1.04      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 1.92/1.04  
% 1.92/1.04  cnf(c_10,plain,
% 1.92/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 1.92/1.04      inference(cnf_transformation,[],[f38]) ).
% 1.92/1.04  
% 1.92/1.04  cnf(c_720,plain,
% 1.92/1.04      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 1.92/1.04      | r1_tarski(X0,X1) = iProver_top ),
% 1.92/1.04      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 1.92/1.04  
% 1.92/1.04  cnf(c_1256,plain,
% 1.92/1.04      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 1.92/1.04      | r1_tarski(k8_setfam_1(X1,X0),X1) = iProver_top ),
% 1.92/1.04      inference(superposition,[status(thm)],[c_723,c_720]) ).
% 1.92/1.04  
% 1.92/1.04  cnf(c_2926,plain,
% 1.92/1.04      ( r1_tarski(k8_setfam_1(sK0,k1_xboole_0),sK0) = iProver_top ),
% 1.92/1.04      inference(superposition,[status(thm)],[c_2312,c_1256]) ).
% 1.92/1.04  
% 1.92/1.04  cnf(c_5,plain,
% 1.92/1.04      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
% 1.92/1.04      | k8_setfam_1(X0,k1_xboole_0) = X0 ),
% 1.92/1.04      inference(cnf_transformation,[],[f46]) ).
% 1.92/1.04  
% 1.92/1.04  cnf(c_725,plain,
% 1.92/1.04      ( k8_setfam_1(X0,k1_xboole_0) = X0
% 1.92/1.04      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 1.92/1.04      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 1.92/1.04  
% 1.92/1.04  cnf(c_2317,plain,
% 1.92/1.04      ( k8_setfam_1(sK0,k1_xboole_0) = sK0 ),
% 1.92/1.04      inference(superposition,[status(thm)],[c_2312,c_725]) ).
% 1.92/1.04  
% 1.92/1.04  cnf(c_2928,plain,
% 1.92/1.04      ( r1_tarski(sK0,sK0) = iProver_top ),
% 1.92/1.04      inference(light_normalisation,[status(thm)],[c_2926,c_2317]) ).
% 1.92/1.04  
% 1.92/1.04  cnf(c_2154,plain,
% 1.92/1.04      ( sK2 = k1_xboole_0
% 1.92/1.04      | r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,k1_xboole_0)) != iProver_top ),
% 1.92/1.04      inference(superposition,[status(thm)],[c_2144,c_718]) ).
% 1.92/1.04  
% 1.92/1.04  cnf(c_2329,plain,
% 1.92/1.04      ( sK2 = k1_xboole_0
% 1.92/1.04      | r1_tarski(k8_setfam_1(sK0,sK2),sK0) != iProver_top ),
% 1.92/1.04      inference(demodulation,[status(thm)],[c_2317,c_2154]) ).
% 1.92/1.04  
% 1.92/1.04  cnf(c_829,plain,
% 1.92/1.04      ( m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(sK0))
% 1.92/1.04      | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
% 1.92/1.04      inference(instantiation,[status(thm)],[c_7]) ).
% 1.92/1.04  
% 1.92/1.04  cnf(c_830,plain,
% 1.92/1.04      ( m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(sK0)) = iProver_top
% 1.92/1.04      | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) != iProver_top ),
% 1.92/1.04      inference(predicate_to_equality,[status(thm)],[c_829]) ).
% 1.92/1.04  
% 1.92/1.04  cnf(c_882,plain,
% 1.92/1.04      ( ~ m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(sK0))
% 1.92/1.04      | r1_tarski(k8_setfam_1(sK0,sK2),sK0) ),
% 1.92/1.04      inference(instantiation,[status(thm)],[c_10]) ).
% 1.92/1.04  
% 1.92/1.04  cnf(c_883,plain,
% 1.92/1.04      ( m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(sK0)) != iProver_top
% 1.92/1.04      | r1_tarski(k8_setfam_1(sK0,sK2),sK0) = iProver_top ),
% 1.92/1.04      inference(predicate_to_equality,[status(thm)],[c_882]) ).
% 1.92/1.04  
% 1.92/1.04  cnf(c_2497,plain,
% 1.92/1.04      ( sK2 = k1_xboole_0 ),
% 1.92/1.04      inference(global_propositional_subsumption,
% 1.92/1.04                [status(thm)],
% 1.92/1.04                [c_2329,c_17,c_830,c_883]) ).
% 1.92/1.04  
% 1.92/1.04  cnf(c_717,plain,
% 1.92/1.04      ( r1_tarski(sK1,sK2) = iProver_top ),
% 1.92/1.04      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 1.92/1.04  
% 1.92/1.04  cnf(c_4,plain,
% 1.92/1.04      ( ~ r1_tarski(X0,X1) | ~ r1_xboole_0(X0,X1) | v1_xboole_0(X0) ),
% 1.92/1.04      inference(cnf_transformation,[],[f33]) ).
% 1.92/1.04  
% 1.92/1.04  cnf(c_0,plain,
% 1.92/1.04      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 1.92/1.04      inference(cnf_transformation,[],[f29]) ).
% 1.92/1.04  
% 1.92/1.04  cnf(c_208,plain,
% 1.92/1.04      ( ~ r1_tarski(X0,X1) | ~ r1_xboole_0(X0,X1) | k1_xboole_0 = X0 ),
% 1.92/1.04      inference(resolution,[status(thm)],[c_4,c_0]) ).
% 1.92/1.04  
% 1.92/1.04  cnf(c_714,plain,
% 1.92/1.04      ( k1_xboole_0 = X0
% 1.92/1.04      | r1_tarski(X0,X1) != iProver_top
% 1.92/1.04      | r1_xboole_0(X0,X1) != iProver_top ),
% 1.92/1.04      inference(predicate_to_equality,[status(thm)],[c_208]) ).
% 1.92/1.04  
% 1.92/1.04  cnf(c_1047,plain,
% 1.92/1.04      ( sK1 = k1_xboole_0 | r1_xboole_0(sK1,sK2) != iProver_top ),
% 1.92/1.04      inference(superposition,[status(thm)],[c_717,c_714]) ).
% 1.92/1.04  
% 1.92/1.04  cnf(c_2506,plain,
% 1.92/1.04      ( sK1 = k1_xboole_0 | r1_xboole_0(sK1,k1_xboole_0) != iProver_top ),
% 1.92/1.04      inference(demodulation,[status(thm)],[c_2497,c_1047]) ).
% 1.92/1.04  
% 1.92/1.04  cnf(c_361,plain,
% 1.92/1.04      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 1.92/1.04      theory(equality) ).
% 1.92/1.04  
% 1.92/1.04  cnf(c_845,plain,
% 1.92/1.04      ( r1_tarski(X0,X1) | ~ r1_tarski(sK1,sK2) | X0 != sK1 | X1 != sK2 ),
% 1.92/1.04      inference(instantiation,[status(thm)],[c_361]) ).
% 1.92/1.04  
% 1.92/1.04  cnf(c_925,plain,
% 1.92/1.04      ( r1_tarski(sK1,X0)
% 1.92/1.04      | ~ r1_tarski(sK1,sK2)
% 1.92/1.04      | X0 != sK2
% 1.92/1.04      | sK1 != sK1 ),
% 1.92/1.04      inference(instantiation,[status(thm)],[c_845]) ).
% 1.92/1.04  
% 1.92/1.04  cnf(c_928,plain,
% 1.92/1.04      ( ~ r1_tarski(sK1,sK2)
% 1.92/1.04      | r1_tarski(sK1,k1_xboole_0)
% 1.92/1.04      | sK1 != sK1
% 1.92/1.04      | k1_xboole_0 != sK2 ),
% 1.92/1.04      inference(instantiation,[status(thm)],[c_925]) ).
% 1.92/1.04  
% 1.92/1.04  cnf(c_1048,plain,
% 1.92/1.04      ( ~ r1_xboole_0(sK1,sK2) | sK1 = k1_xboole_0 ),
% 1.92/1.04      inference(predicate_to_equality_rev,[status(thm)],[c_1047]) ).
% 1.92/1.04  
% 1.92/1.04  cnf(c_1,plain,
% 1.92/1.04      ( ~ r1_tarski(X0,X1) | ~ r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2) ),
% 1.92/1.04      inference(cnf_transformation,[],[f30]) ).
% 1.92/1.04  
% 1.92/1.04  cnf(c_1353,plain,
% 1.92/1.04      ( ~ r1_tarski(sK1,X0)
% 1.92/1.04      | ~ r1_xboole_0(X0,sK2)
% 1.92/1.04      | r1_xboole_0(sK1,sK2) ),
% 1.92/1.04      inference(instantiation,[status(thm)],[c_1]) ).
% 1.92/1.04  
% 1.92/1.04  cnf(c_1355,plain,
% 1.92/1.04      ( ~ r1_tarski(sK1,k1_xboole_0)
% 1.92/1.04      | r1_xboole_0(sK1,sK2)
% 1.92/1.04      | ~ r1_xboole_0(k1_xboole_0,sK2) ),
% 1.92/1.04      inference(instantiation,[status(thm)],[c_1353]) ).
% 1.92/1.04  
% 1.92/1.04  cnf(c_360,plain,
% 1.92/1.04      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X3) | X2 != X0 | X3 != X1 ),
% 1.92/1.04      theory(equality) ).
% 1.92/1.04  
% 1.92/1.04  cnf(c_2245,plain,
% 1.92/1.04      ( ~ r1_xboole_0(X0,X1)
% 1.92/1.04      | r1_xboole_0(X2,sK2)
% 1.92/1.04      | X2 != X0
% 1.92/1.04      | sK2 != X1 ),
% 1.92/1.04      inference(instantiation,[status(thm)],[c_360]) ).
% 1.92/1.04  
% 1.92/1.04  cnf(c_2247,plain,
% 1.92/1.04      ( r1_xboole_0(k1_xboole_0,sK2)
% 1.92/1.04      | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
% 1.92/1.04      | sK2 != k1_xboole_0
% 1.92/1.04      | k1_xboole_0 != k1_xboole_0 ),
% 1.92/1.04      inference(instantiation,[status(thm)],[c_2245]) ).
% 1.92/1.04  
% 1.92/1.04  cnf(c_2713,plain,
% 1.92/1.04      ( sK1 = k1_xboole_0 ),
% 1.92/1.04      inference(global_propositional_subsumption,
% 1.92/1.04                [status(thm)],
% 1.92/1.04                [c_2506,c_17,c_13,c_3,c_46,c_830,c_883,c_928,c_926,c_974,
% 1.92/1.04                 c_1048,c_1355,c_2247,c_2329]) ).
% 1.92/1.04  
% 1.92/1.04  cnf(c_2509,plain,
% 1.92/1.04      ( r1_tarski(k8_setfam_1(sK0,k1_xboole_0),k8_setfam_1(sK0,sK1)) != iProver_top ),
% 1.92/1.04      inference(demodulation,[status(thm)],[c_2497,c_718]) ).
% 1.92/1.04  
% 1.92/1.04  cnf(c_2515,plain,
% 1.92/1.04      ( r1_tarski(sK0,k8_setfam_1(sK0,sK1)) != iProver_top ),
% 1.92/1.04      inference(light_normalisation,[status(thm)],[c_2509,c_2317]) ).
% 1.92/1.04  
% 1.92/1.04  cnf(c_2716,plain,
% 1.92/1.04      ( r1_tarski(sK0,k8_setfam_1(sK0,k1_xboole_0)) != iProver_top ),
% 1.92/1.04      inference(demodulation,[status(thm)],[c_2713,c_2515]) ).
% 1.92/1.04  
% 1.92/1.04  cnf(c_2724,plain,
% 1.92/1.04      ( r1_tarski(sK0,sK0) != iProver_top ),
% 1.92/1.04      inference(light_normalisation,[status(thm)],[c_2716,c_2317]) ).
% 1.92/1.04  
% 1.92/1.04  cnf(contradiction,plain,
% 1.92/1.04      ( $false ),
% 1.92/1.04      inference(minisat,[status(thm)],[c_2928,c_2724]) ).
% 1.92/1.04  
% 1.92/1.04  
% 1.92/1.04  % SZS output end CNFRefutation for theBenchmark.p
% 1.92/1.04  
% 1.92/1.04  ------                               Statistics
% 1.92/1.04  
% 1.92/1.04  ------ General
% 1.92/1.04  
% 1.92/1.04  abstr_ref_over_cycles:                  0
% 1.92/1.04  abstr_ref_under_cycles:                 0
% 1.92/1.04  gc_basic_clause_elim:                   0
% 1.92/1.04  forced_gc_time:                         0
% 1.92/1.04  parsing_time:                           0.011
% 1.92/1.04  unif_index_cands_time:                  0.
% 1.92/1.04  unif_index_add_time:                    0.
% 1.92/1.04  orderings_time:                         0.
% 1.92/1.04  out_proof_time:                         0.008
% 1.92/1.04  total_time:                             0.121
% 1.92/1.04  num_of_symbols:                         43
% 1.92/1.04  num_of_terms:                           1716
% 1.92/1.04  
% 1.92/1.04  ------ Preprocessing
% 1.92/1.04  
% 1.92/1.04  num_of_splits:                          0
% 1.92/1.04  num_of_split_atoms:                     0
% 1.92/1.04  num_of_reused_defs:                     0
% 1.92/1.04  num_eq_ax_congr_red:                    10
% 1.92/1.04  num_of_sem_filtered_clauses:            1
% 1.92/1.04  num_of_subtypes:                        0
% 1.92/1.04  monotx_restored_types:                  0
% 1.92/1.04  sat_num_of_epr_types:                   0
% 1.92/1.04  sat_num_of_non_cyclic_types:            0
% 1.92/1.04  sat_guarded_non_collapsed_types:        0
% 1.92/1.04  num_pure_diseq_elim:                    0
% 1.92/1.04  simp_replaced_by:                       0
% 1.92/1.04  res_preprocessed:                       76
% 1.92/1.04  prep_upred:                             0
% 1.92/1.04  prep_unflattend:                        0
% 1.92/1.04  smt_new_axioms:                         0
% 1.92/1.04  pred_elim_cands:                        3
% 1.92/1.04  pred_elim:                              1
% 1.92/1.04  pred_elim_cl:                           1
% 1.92/1.04  pred_elim_cycles:                       3
% 1.92/1.04  merged_defs:                            8
% 1.92/1.04  merged_defs_ncl:                        0
% 1.92/1.04  bin_hyper_res:                          8
% 1.92/1.04  prep_cycles:                            4
% 1.92/1.04  pred_elim_time:                         0.001
% 1.92/1.04  splitting_time:                         0.
% 1.92/1.04  sem_filter_time:                        0.
% 1.92/1.04  monotx_time:                            0.
% 1.92/1.04  subtype_inf_time:                       0.
% 1.92/1.04  
% 1.92/1.04  ------ Problem properties
% 1.92/1.04  
% 1.92/1.04  clauses:                                15
% 1.92/1.04  conjectures:                            4
% 1.92/1.04  epr:                                    5
% 1.92/1.04  horn:                                   13
% 1.92/1.04  ground:                                 5
% 1.92/1.04  unary:                                  5
% 1.92/1.04  binary:                                 6
% 1.92/1.04  lits:                                   29
% 1.92/1.04  lits_eq:                                7
% 1.92/1.04  fd_pure:                                0
% 1.92/1.04  fd_pseudo:                              0
% 1.92/1.04  fd_cond:                                4
% 1.92/1.04  fd_pseudo_cond:                         0
% 1.92/1.04  ac_symbols:                             0
% 1.92/1.04  
% 1.92/1.04  ------ Propositional Solver
% 1.92/1.04  
% 1.92/1.04  prop_solver_calls:                      28
% 1.92/1.04  prop_fast_solver_calls:                 413
% 1.92/1.04  smt_solver_calls:                       0
% 1.92/1.04  smt_fast_solver_calls:                  0
% 1.92/1.04  prop_num_of_clauses:                    1024
% 1.92/1.04  prop_preprocess_simplified:             3172
% 1.92/1.04  prop_fo_subsumed:                       5
% 1.92/1.04  prop_solver_time:                       0.
% 1.92/1.04  smt_solver_time:                        0.
% 1.92/1.04  smt_fast_solver_time:                   0.
% 1.92/1.04  prop_fast_solver_time:                  0.
% 1.92/1.04  prop_unsat_core_time:                   0.
% 1.92/1.04  
% 1.92/1.04  ------ QBF
% 1.92/1.04  
% 1.92/1.04  qbf_q_res:                              0
% 1.92/1.04  qbf_num_tautologies:                    0
% 1.92/1.04  qbf_prep_cycles:                        0
% 1.92/1.04  
% 1.92/1.04  ------ BMC1
% 1.92/1.04  
% 1.92/1.04  bmc1_current_bound:                     -1
% 1.92/1.04  bmc1_last_solved_bound:                 -1
% 1.92/1.04  bmc1_unsat_core_size:                   -1
% 1.92/1.04  bmc1_unsat_core_parents_size:           -1
% 1.92/1.04  bmc1_merge_next_fun:                    0
% 1.92/1.04  bmc1_unsat_core_clauses_time:           0.
% 1.92/1.04  
% 1.92/1.04  ------ Instantiation
% 1.92/1.04  
% 1.92/1.04  inst_num_of_clauses:                    299
% 1.92/1.04  inst_num_in_passive:                    15
% 1.92/1.04  inst_num_in_active:                     181
% 1.92/1.04  inst_num_in_unprocessed:                103
% 1.92/1.04  inst_num_of_loops:                      230
% 1.92/1.04  inst_num_of_learning_restarts:          0
% 1.92/1.04  inst_num_moves_active_passive:          46
% 1.92/1.04  inst_lit_activity:                      0
% 1.92/1.04  inst_lit_activity_moves:                0
% 1.92/1.04  inst_num_tautologies:                   0
% 1.92/1.04  inst_num_prop_implied:                  0
% 1.92/1.04  inst_num_existing_simplified:           0
% 1.92/1.04  inst_num_eq_res_simplified:             0
% 1.92/1.04  inst_num_child_elim:                    0
% 1.92/1.04  inst_num_of_dismatching_blockings:      83
% 1.92/1.04  inst_num_of_non_proper_insts:           296
% 1.92/1.04  inst_num_of_duplicates:                 0
% 1.92/1.04  inst_inst_num_from_inst_to_res:         0
% 1.92/1.04  inst_dismatching_checking_time:         0.
% 1.92/1.04  
% 1.92/1.04  ------ Resolution
% 1.92/1.04  
% 1.92/1.04  res_num_of_clauses:                     0
% 1.92/1.04  res_num_in_passive:                     0
% 1.92/1.04  res_num_in_active:                      0
% 1.92/1.04  res_num_of_loops:                       80
% 1.92/1.04  res_forward_subset_subsumed:            35
% 1.92/1.04  res_backward_subset_subsumed:           0
% 1.92/1.04  res_forward_subsumed:                   0
% 1.92/1.04  res_backward_subsumed:                  0
% 1.92/1.04  res_forward_subsumption_resolution:     0
% 1.92/1.04  res_backward_subsumption_resolution:    0
% 1.92/1.04  res_clause_to_clause_subsumption:       104
% 1.92/1.04  res_orphan_elimination:                 0
% 1.92/1.04  res_tautology_del:                      39
% 1.92/1.04  res_num_eq_res_simplified:              0
% 1.92/1.04  res_num_sel_changes:                    0
% 1.92/1.04  res_moves_from_active_to_pass:          0
% 1.92/1.04  
% 1.92/1.04  ------ Superposition
% 1.92/1.04  
% 1.92/1.04  sup_time_total:                         0.
% 1.92/1.04  sup_time_generating:                    0.
% 1.92/1.04  sup_time_sim_full:                      0.
% 1.92/1.04  sup_time_sim_immed:                     0.
% 1.92/1.04  
% 1.92/1.04  sup_num_of_clauses:                     36
% 1.92/1.04  sup_num_in_active:                      21
% 1.92/1.04  sup_num_in_passive:                     15
% 1.92/1.04  sup_num_of_loops:                       44
% 1.92/1.04  sup_fw_superposition:                   26
% 1.92/1.04  sup_bw_superposition:                   36
% 1.92/1.04  sup_immediate_simplified:               12
% 1.92/1.04  sup_given_eliminated:                   0
% 1.92/1.04  comparisons_done:                       0
% 1.92/1.04  comparisons_avoided:                    8
% 1.92/1.04  
% 1.92/1.04  ------ Simplifications
% 1.92/1.04  
% 1.92/1.04  
% 1.92/1.04  sim_fw_subset_subsumed:                 6
% 1.92/1.04  sim_bw_subset_subsumed:                 9
% 1.92/1.04  sim_fw_subsumed:                        0
% 1.92/1.04  sim_bw_subsumed:                        0
% 1.92/1.04  sim_fw_subsumption_res:                 0
% 1.92/1.04  sim_bw_subsumption_res:                 0
% 1.92/1.04  sim_tautology_del:                      4
% 1.92/1.04  sim_eq_tautology_del:                   7
% 1.92/1.04  sim_eq_res_simp:                        0
% 1.92/1.04  sim_fw_demodulated:                     0
% 1.92/1.04  sim_bw_demodulated:                     20
% 1.92/1.04  sim_light_normalised:                   7
% 1.92/1.04  sim_joinable_taut:                      0
% 1.92/1.04  sim_joinable_simp:                      0
% 1.92/1.04  sim_ac_normalised:                      0
% 1.92/1.04  sim_smt_subsumption:                    0
% 1.92/1.04  
%------------------------------------------------------------------------------
