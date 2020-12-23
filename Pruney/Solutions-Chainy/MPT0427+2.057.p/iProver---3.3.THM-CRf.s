%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:42:37 EST 2020

% Result     : Theorem 2.32s
% Output     : CNFRefutation 2.32s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 595 expanded)
%              Number of clauses        :   87 ( 233 expanded)
%              Number of leaves         :   19 ( 134 expanded)
%              Depth                    :   23
%              Number of atoms          :  301 (1787 expanded)
%              Number of equality atoms :  150 ( 491 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( r1_tarski(X1,X2)
           => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( r1_tarski(X1,X2)
             => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f27,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f26])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
     => ( ~ r1_tarski(k8_setfam_1(X0,sK3),k8_setfam_1(X0,X1))
        & r1_tarski(X1,sK3)
        & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
            & r1_tarski(X1,X2)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(sK1,X2),k8_setfam_1(sK1,sK2))
          & r1_tarski(sK2,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK1))) )
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ~ r1_tarski(k8_setfam_1(sK1,sK3),k8_setfam_1(sK1,sK2))
    & r1_tarski(sK2,sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1)))
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f27,f32,f31])).

fof(f49,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(cnf_transformation,[],[f33])).

fof(f6,axiom,(
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
    inference(ennf_transformation,[],[f6])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f48,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(cnf_transformation,[],[f33])).

fof(f51,plain,(
    ~ r1_tarski(k8_setfam_1(sK1,sK3),k8_setfam_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f33])).

fof(f50,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f52,plain,(
    ! [X0] :
      ( k8_setfam_1(X0,k1_xboole_0) = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f40])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f1,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f28])).

fof(f34,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
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
    inference(ennf_transformation,[],[f3])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f16])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f4])).

cnf(c_13,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_848,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_845,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k6_setfam_1(X1,X0) = k8_setfam_1(X1,X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_853,plain,
    ( k6_setfam_1(X0,X1) = k8_setfam_1(X0,X1)
    | k1_xboole_0 = X1
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1869,plain,
    ( k6_setfam_1(sK1,sK3) = k8_setfam_1(sK1,sK3)
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_845,c_853])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k6_setfam_1(X1,X0) = k1_setfam_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_851,plain,
    ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1298,plain,
    ( k6_setfam_1(sK1,sK3) = k1_setfam_1(sK3) ),
    inference(superposition,[status(thm)],[c_845,c_851])).

cnf(c_1887,plain,
    ( k8_setfam_1(sK1,sK3) = k1_setfam_1(sK3)
    | sK3 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1869,c_1298])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_844,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1870,plain,
    ( k6_setfam_1(sK1,sK2) = k8_setfam_1(sK1,sK2)
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_844,c_853])).

cnf(c_1299,plain,
    ( k6_setfam_1(sK1,sK2) = k1_setfam_1(sK2) ),
    inference(superposition,[status(thm)],[c_844,c_851])).

cnf(c_1882,plain,
    ( k8_setfam_1(sK1,sK2) = k1_setfam_1(sK2)
    | sK2 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1870,c_1299])).

cnf(c_14,negated_conjecture,
    ( ~ r1_tarski(k8_setfam_1(sK1,sK3),k8_setfam_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_847,plain,
    ( r1_tarski(k8_setfam_1(sK1,sK3),k8_setfam_1(sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2253,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(k8_setfam_1(sK1,sK3),k1_setfam_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1882,c_847])).

cnf(c_2336,plain,
    ( sK2 = k1_xboole_0
    | sK3 = k1_xboole_0
    | r1_tarski(k1_setfam_1(sK3),k1_setfam_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1887,c_2253])).

cnf(c_2446,plain,
    ( sK2 = k1_xboole_0
    | sK3 = k1_xboole_0
    | r1_tarski(sK2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_848,c_2336])).

cnf(c_15,negated_conjecture,
    ( r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2447,plain,
    ( ~ r1_tarski(sK2,sK3)
    | sK2 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2446])).

cnf(c_2491,plain,
    ( sK3 = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2446,c_15,c_2447])).

cnf(c_2492,plain,
    ( sK2 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_2491])).

cnf(c_2500,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(k8_setfam_1(sK1,sK3),k8_setfam_1(sK1,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2492,c_847])).

cnf(c_5,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
    | k8_setfam_1(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_854,plain,
    ( k8_setfam_1(X0,k1_xboole_0) = X0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_855,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_878,plain,
    ( k8_setfam_1(X0,k1_xboole_0) = X0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_854,c_855])).

cnf(c_2509,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(k8_setfam_1(sK1,sK3),sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2500,c_878])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | m1_subset_1(k8_setfam_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_852,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | m1_subset_1(k8_setfam_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_849,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1325,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | r1_tarski(k8_setfam_1(X1,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_852,c_849])).

cnf(c_2688,plain,
    ( r1_tarski(k8_setfam_1(sK1,sK3),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_845,c_1325])).

cnf(c_3054,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2509,c_2688])).

cnf(c_846,plain,
    ( r1_tarski(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_9,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_138,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_9])).

cnf(c_139,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_138])).

cnf(c_169,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(bin_hyper_res,[status(thm)],[c_12,c_139])).

cnf(c_281,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_xboole_0(X1)
    | X0 != X2
    | sK0(X2) != X3
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_169])).

cnf(c_282,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_xboole_0(X1)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_281])).

cnf(c_842,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_282])).

cnf(c_1834,plain,
    ( sK2 = k1_xboole_0
    | v1_xboole_0(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_846,c_842])).

cnf(c_3060,plain,
    ( sK2 = k1_xboole_0
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3054,c_1834])).

cnf(c_31,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_33,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_49,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_51,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_49])).

cnf(c_1,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_58,plain,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_xboole_0(X0,X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_3,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_233,plain,
    ( ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0)
    | X2 != X1
    | k4_xboole_0(X3,X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_3])).

cnf(c_234,plain,
    ( ~ r1_tarski(k4_xboole_0(X0,X1),X1)
    | v1_xboole_0(k4_xboole_0(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_233])).

cnf(c_235,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X1) != iProver_top
    | v1_xboole_0(k4_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_234])).

cnf(c_237,plain,
    ( r1_tarski(k4_xboole_0(k1_xboole_0,k1_xboole_0),k1_xboole_0) != iProver_top
    | v1_xboole_0(k4_xboole_0(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_235])).

cnf(c_475,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_490,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_475])).

cnf(c_478,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_992,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k4_xboole_0(X2,X3),X3)
    | X3 != X1
    | k4_xboole_0(X2,X3) != X0 ),
    inference(instantiation,[status(thm)],[c_478])).

cnf(c_993,plain,
    ( X0 != X1
    | k4_xboole_0(X2,X0) != X3
    | r1_tarski(X3,X1) != iProver_top
    | r1_tarski(k4_xboole_0(X2,X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_992])).

cnf(c_995,plain,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | r1_tarski(k4_xboole_0(k1_xboole_0,k1_xboole_0),k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_993])).

cnf(c_479,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1034,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(k4_xboole_0(X1,X2))
    | X0 != k4_xboole_0(X1,X2) ),
    inference(instantiation,[status(thm)],[c_479])).

cnf(c_1035,plain,
    ( X0 != k4_xboole_0(X1,X2)
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(k4_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1034])).

cnf(c_1037,plain,
    ( k1_xboole_0 != k4_xboole_0(k1_xboole_0,k1_xboole_0)
    | v1_xboole_0(k4_xboole_0(k1_xboole_0,k1_xboole_0)) != iProver_top
    | v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1035])).

cnf(c_476,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1287,plain,
    ( X0 != X1
    | X0 = k4_xboole_0(X2,X3)
    | k4_xboole_0(X2,X3) != X1 ),
    inference(instantiation,[status(thm)],[c_476])).

cnf(c_1288,plain,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1287])).

cnf(c_3178,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3060,c_33,c_51,c_58,c_237,c_490,c_995,c_1037,c_1288])).

cnf(c_3063,plain,
    ( r1_tarski(k8_setfam_1(sK1,k1_xboole_0),k8_setfam_1(sK1,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3054,c_847])).

cnf(c_3070,plain,
    ( r1_tarski(sK1,k8_setfam_1(sK1,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3063,c_878])).

cnf(c_3181,plain,
    ( r1_tarski(sK1,k8_setfam_1(sK1,k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3178,c_3070])).

cnf(c_3190,plain,
    ( r1_tarski(sK1,sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3181,c_878])).

cnf(c_1323,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_878,c_852])).

cnf(c_957,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_960,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_957])).

cnf(c_1941,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1323,c_960])).

cnf(c_1948,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1941,c_849])).

cnf(c_3358,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3190,c_1948])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n002.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:05:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.32/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.32/0.99  
% 2.32/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.32/0.99  
% 2.32/0.99  ------  iProver source info
% 2.32/0.99  
% 2.32/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.32/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.32/0.99  git: non_committed_changes: false
% 2.32/0.99  git: last_make_outside_of_git: false
% 2.32/0.99  
% 2.32/0.99  ------ 
% 2.32/0.99  
% 2.32/0.99  ------ Input Options
% 2.32/0.99  
% 2.32/0.99  --out_options                           all
% 2.32/0.99  --tptp_safe_out                         true
% 2.32/0.99  --problem_path                          ""
% 2.32/0.99  --include_path                          ""
% 2.32/0.99  --clausifier                            res/vclausify_rel
% 2.32/0.99  --clausifier_options                    --mode clausify
% 2.32/0.99  --stdin                                 false
% 2.32/0.99  --stats_out                             all
% 2.32/0.99  
% 2.32/0.99  ------ General Options
% 2.32/0.99  
% 2.32/0.99  --fof                                   false
% 2.32/0.99  --time_out_real                         305.
% 2.32/0.99  --time_out_virtual                      -1.
% 2.32/0.99  --symbol_type_check                     false
% 2.32/0.99  --clausify_out                          false
% 2.32/0.99  --sig_cnt_out                           false
% 2.32/0.99  --trig_cnt_out                          false
% 2.32/0.99  --trig_cnt_out_tolerance                1.
% 2.32/0.99  --trig_cnt_out_sk_spl                   false
% 2.32/0.99  --abstr_cl_out                          false
% 2.32/0.99  
% 2.32/0.99  ------ Global Options
% 2.32/0.99  
% 2.32/0.99  --schedule                              default
% 2.32/0.99  --add_important_lit                     false
% 2.32/0.99  --prop_solver_per_cl                    1000
% 2.32/0.99  --min_unsat_core                        false
% 2.32/0.99  --soft_assumptions                      false
% 2.32/0.99  --soft_lemma_size                       3
% 2.32/0.99  --prop_impl_unit_size                   0
% 2.32/0.99  --prop_impl_unit                        []
% 2.32/0.99  --share_sel_clauses                     true
% 2.32/0.99  --reset_solvers                         false
% 2.32/0.99  --bc_imp_inh                            [conj_cone]
% 2.32/0.99  --conj_cone_tolerance                   3.
% 2.32/0.99  --extra_neg_conj                        none
% 2.32/0.99  --large_theory_mode                     true
% 2.32/0.99  --prolific_symb_bound                   200
% 2.32/0.99  --lt_threshold                          2000
% 2.32/0.99  --clause_weak_htbl                      true
% 2.32/0.99  --gc_record_bc_elim                     false
% 2.32/0.99  
% 2.32/0.99  ------ Preprocessing Options
% 2.32/0.99  
% 2.32/0.99  --preprocessing_flag                    true
% 2.32/0.99  --time_out_prep_mult                    0.1
% 2.32/0.99  --splitting_mode                        input
% 2.32/0.99  --splitting_grd                         true
% 2.32/0.99  --splitting_cvd                         false
% 2.32/0.99  --splitting_cvd_svl                     false
% 2.32/0.99  --splitting_nvd                         32
% 2.32/0.99  --sub_typing                            true
% 2.32/0.99  --prep_gs_sim                           true
% 2.32/0.99  --prep_unflatten                        true
% 2.32/0.99  --prep_res_sim                          true
% 2.32/0.99  --prep_upred                            true
% 2.32/0.99  --prep_sem_filter                       exhaustive
% 2.32/0.99  --prep_sem_filter_out                   false
% 2.32/0.99  --pred_elim                             true
% 2.32/0.99  --res_sim_input                         true
% 2.32/0.99  --eq_ax_congr_red                       true
% 2.32/0.99  --pure_diseq_elim                       true
% 2.32/0.99  --brand_transform                       false
% 2.32/0.99  --non_eq_to_eq                          false
% 2.32/0.99  --prep_def_merge                        true
% 2.32/0.99  --prep_def_merge_prop_impl              false
% 2.32/0.99  --prep_def_merge_mbd                    true
% 2.32/0.99  --prep_def_merge_tr_red                 false
% 2.32/0.99  --prep_def_merge_tr_cl                  false
% 2.32/0.99  --smt_preprocessing                     true
% 2.32/0.99  --smt_ac_axioms                         fast
% 2.32/0.99  --preprocessed_out                      false
% 2.32/0.99  --preprocessed_stats                    false
% 2.32/0.99  
% 2.32/0.99  ------ Abstraction refinement Options
% 2.32/0.99  
% 2.32/0.99  --abstr_ref                             []
% 2.32/0.99  --abstr_ref_prep                        false
% 2.32/0.99  --abstr_ref_until_sat                   false
% 2.32/0.99  --abstr_ref_sig_restrict                funpre
% 2.32/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.32/0.99  --abstr_ref_under                       []
% 2.32/0.99  
% 2.32/0.99  ------ SAT Options
% 2.32/0.99  
% 2.32/0.99  --sat_mode                              false
% 2.32/0.99  --sat_fm_restart_options                ""
% 2.32/0.99  --sat_gr_def                            false
% 2.32/0.99  --sat_epr_types                         true
% 2.32/0.99  --sat_non_cyclic_types                  false
% 2.32/0.99  --sat_finite_models                     false
% 2.32/0.99  --sat_fm_lemmas                         false
% 2.32/0.99  --sat_fm_prep                           false
% 2.32/0.99  --sat_fm_uc_incr                        true
% 2.32/0.99  --sat_out_model                         small
% 2.32/0.99  --sat_out_clauses                       false
% 2.32/0.99  
% 2.32/0.99  ------ QBF Options
% 2.32/0.99  
% 2.32/0.99  --qbf_mode                              false
% 2.32/0.99  --qbf_elim_univ                         false
% 2.32/0.99  --qbf_dom_inst                          none
% 2.32/0.99  --qbf_dom_pre_inst                      false
% 2.32/0.99  --qbf_sk_in                             false
% 2.32/0.99  --qbf_pred_elim                         true
% 2.32/0.99  --qbf_split                             512
% 2.32/0.99  
% 2.32/0.99  ------ BMC1 Options
% 2.32/0.99  
% 2.32/0.99  --bmc1_incremental                      false
% 2.32/0.99  --bmc1_axioms                           reachable_all
% 2.32/0.99  --bmc1_min_bound                        0
% 2.32/0.99  --bmc1_max_bound                        -1
% 2.32/0.99  --bmc1_max_bound_default                -1
% 2.32/0.99  --bmc1_symbol_reachability              true
% 2.32/0.99  --bmc1_property_lemmas                  false
% 2.32/0.99  --bmc1_k_induction                      false
% 2.32/0.99  --bmc1_non_equiv_states                 false
% 2.32/0.99  --bmc1_deadlock                         false
% 2.32/0.99  --bmc1_ucm                              false
% 2.32/0.99  --bmc1_add_unsat_core                   none
% 2.32/0.99  --bmc1_unsat_core_children              false
% 2.32/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.32/0.99  --bmc1_out_stat                         full
% 2.32/0.99  --bmc1_ground_init                      false
% 2.32/0.99  --bmc1_pre_inst_next_state              false
% 2.32/0.99  --bmc1_pre_inst_state                   false
% 2.32/0.99  --bmc1_pre_inst_reach_state             false
% 2.32/0.99  --bmc1_out_unsat_core                   false
% 2.32/0.99  --bmc1_aig_witness_out                  false
% 2.32/0.99  --bmc1_verbose                          false
% 2.32/0.99  --bmc1_dump_clauses_tptp                false
% 2.32/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.32/0.99  --bmc1_dump_file                        -
% 2.32/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.32/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.32/0.99  --bmc1_ucm_extend_mode                  1
% 2.32/0.99  --bmc1_ucm_init_mode                    2
% 2.32/0.99  --bmc1_ucm_cone_mode                    none
% 2.32/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.32/0.99  --bmc1_ucm_relax_model                  4
% 2.32/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.32/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.32/0.99  --bmc1_ucm_layered_model                none
% 2.32/0.99  --bmc1_ucm_max_lemma_size               10
% 2.32/0.99  
% 2.32/0.99  ------ AIG Options
% 2.32/0.99  
% 2.32/0.99  --aig_mode                              false
% 2.32/0.99  
% 2.32/0.99  ------ Instantiation Options
% 2.32/0.99  
% 2.32/0.99  --instantiation_flag                    true
% 2.32/0.99  --inst_sos_flag                         false
% 2.32/0.99  --inst_sos_phase                        true
% 2.32/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.32/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.32/0.99  --inst_lit_sel_side                     num_symb
% 2.32/0.99  --inst_solver_per_active                1400
% 2.32/0.99  --inst_solver_calls_frac                1.
% 2.32/0.99  --inst_passive_queue_type               priority_queues
% 2.32/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.32/0.99  --inst_passive_queues_freq              [25;2]
% 2.32/0.99  --inst_dismatching                      true
% 2.32/0.99  --inst_eager_unprocessed_to_passive     true
% 2.32/0.99  --inst_prop_sim_given                   true
% 2.32/0.99  --inst_prop_sim_new                     false
% 2.32/0.99  --inst_subs_new                         false
% 2.32/0.99  --inst_eq_res_simp                      false
% 2.32/0.99  --inst_subs_given                       false
% 2.32/0.99  --inst_orphan_elimination               true
% 2.32/0.99  --inst_learning_loop_flag               true
% 2.32/0.99  --inst_learning_start                   3000
% 2.32/0.99  --inst_learning_factor                  2
% 2.32/0.99  --inst_start_prop_sim_after_learn       3
% 2.32/0.99  --inst_sel_renew                        solver
% 2.32/0.99  --inst_lit_activity_flag                true
% 2.32/0.99  --inst_restr_to_given                   false
% 2.32/0.99  --inst_activity_threshold               500
% 2.32/0.99  --inst_out_proof                        true
% 2.32/0.99  
% 2.32/0.99  ------ Resolution Options
% 2.32/0.99  
% 2.32/0.99  --resolution_flag                       true
% 2.32/0.99  --res_lit_sel                           adaptive
% 2.32/0.99  --res_lit_sel_side                      none
% 2.32/0.99  --res_ordering                          kbo
% 2.32/0.99  --res_to_prop_solver                    active
% 2.32/0.99  --res_prop_simpl_new                    false
% 2.32/0.99  --res_prop_simpl_given                  true
% 2.32/0.99  --res_passive_queue_type                priority_queues
% 2.32/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.32/0.99  --res_passive_queues_freq               [15;5]
% 2.32/0.99  --res_forward_subs                      full
% 2.32/0.99  --res_backward_subs                     full
% 2.32/0.99  --res_forward_subs_resolution           true
% 2.32/0.99  --res_backward_subs_resolution          true
% 2.32/0.99  --res_orphan_elimination                true
% 2.32/0.99  --res_time_limit                        2.
% 2.32/0.99  --res_out_proof                         true
% 2.32/0.99  
% 2.32/0.99  ------ Superposition Options
% 2.32/0.99  
% 2.32/0.99  --superposition_flag                    true
% 2.32/0.99  --sup_passive_queue_type                priority_queues
% 2.32/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.32/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.32/0.99  --demod_completeness_check              fast
% 2.32/0.99  --demod_use_ground                      true
% 2.32/0.99  --sup_to_prop_solver                    passive
% 2.32/0.99  --sup_prop_simpl_new                    true
% 2.32/0.99  --sup_prop_simpl_given                  true
% 2.32/0.99  --sup_fun_splitting                     false
% 2.32/0.99  --sup_smt_interval                      50000
% 2.32/0.99  
% 2.32/0.99  ------ Superposition Simplification Setup
% 2.32/0.99  
% 2.32/0.99  --sup_indices_passive                   []
% 2.32/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.32/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/0.99  --sup_full_bw                           [BwDemod]
% 2.32/0.99  --sup_immed_triv                        [TrivRules]
% 2.32/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.32/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/0.99  --sup_immed_bw_main                     []
% 2.32/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.32/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.32/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.32/0.99  
% 2.32/0.99  ------ Combination Options
% 2.32/0.99  
% 2.32/0.99  --comb_res_mult                         3
% 2.32/0.99  --comb_sup_mult                         2
% 2.32/0.99  --comb_inst_mult                        10
% 2.32/0.99  
% 2.32/0.99  ------ Debug Options
% 2.32/0.99  
% 2.32/0.99  --dbg_backtrace                         false
% 2.32/0.99  --dbg_dump_prop_clauses                 false
% 2.32/0.99  --dbg_dump_prop_clauses_file            -
% 2.32/0.99  --dbg_out_stat                          false
% 2.32/0.99  ------ Parsing...
% 2.32/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.32/0.99  
% 2.32/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.32/0.99  
% 2.32/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.32/0.99  
% 2.32/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.32/0.99  ------ Proving...
% 2.32/0.99  ------ Problem Properties 
% 2.32/0.99  
% 2.32/0.99  
% 2.32/0.99  clauses                                 16
% 2.32/0.99  conjectures                             4
% 2.32/0.99  EPR                                     2
% 2.32/0.99  Horn                                    13
% 2.32/0.99  unary                                   6
% 2.32/0.99  binary                                  6
% 2.32/0.99  lits                                    30
% 2.32/0.99  lits eq                                 8
% 2.32/0.99  fd_pure                                 0
% 2.32/0.99  fd_pseudo                               0
% 2.32/0.99  fd_cond                                 4
% 2.32/0.99  fd_pseudo_cond                          0
% 2.32/0.99  AC symbols                              0
% 2.32/0.99  
% 2.32/0.99  ------ Schedule dynamic 5 is on 
% 2.32/0.99  
% 2.32/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.32/0.99  
% 2.32/0.99  
% 2.32/0.99  ------ 
% 2.32/0.99  Current options:
% 2.32/0.99  ------ 
% 2.32/0.99  
% 2.32/0.99  ------ Input Options
% 2.32/0.99  
% 2.32/0.99  --out_options                           all
% 2.32/0.99  --tptp_safe_out                         true
% 2.32/0.99  --problem_path                          ""
% 2.32/0.99  --include_path                          ""
% 2.32/0.99  --clausifier                            res/vclausify_rel
% 2.32/0.99  --clausifier_options                    --mode clausify
% 2.32/0.99  --stdin                                 false
% 2.32/0.99  --stats_out                             all
% 2.32/0.99  
% 2.32/0.99  ------ General Options
% 2.32/0.99  
% 2.32/0.99  --fof                                   false
% 2.32/0.99  --time_out_real                         305.
% 2.32/0.99  --time_out_virtual                      -1.
% 2.32/0.99  --symbol_type_check                     false
% 2.32/0.99  --clausify_out                          false
% 2.32/0.99  --sig_cnt_out                           false
% 2.32/0.99  --trig_cnt_out                          false
% 2.32/0.99  --trig_cnt_out_tolerance                1.
% 2.32/0.99  --trig_cnt_out_sk_spl                   false
% 2.32/0.99  --abstr_cl_out                          false
% 2.32/0.99  
% 2.32/0.99  ------ Global Options
% 2.32/0.99  
% 2.32/0.99  --schedule                              default
% 2.32/0.99  --add_important_lit                     false
% 2.32/0.99  --prop_solver_per_cl                    1000
% 2.32/0.99  --min_unsat_core                        false
% 2.32/0.99  --soft_assumptions                      false
% 2.32/0.99  --soft_lemma_size                       3
% 2.32/0.99  --prop_impl_unit_size                   0
% 2.32/0.99  --prop_impl_unit                        []
% 2.32/0.99  --share_sel_clauses                     true
% 2.32/0.99  --reset_solvers                         false
% 2.32/0.99  --bc_imp_inh                            [conj_cone]
% 2.32/0.99  --conj_cone_tolerance                   3.
% 2.32/0.99  --extra_neg_conj                        none
% 2.32/0.99  --large_theory_mode                     true
% 2.32/0.99  --prolific_symb_bound                   200
% 2.32/0.99  --lt_threshold                          2000
% 2.32/0.99  --clause_weak_htbl                      true
% 2.32/0.99  --gc_record_bc_elim                     false
% 2.32/0.99  
% 2.32/0.99  ------ Preprocessing Options
% 2.32/0.99  
% 2.32/0.99  --preprocessing_flag                    true
% 2.32/0.99  --time_out_prep_mult                    0.1
% 2.32/0.99  --splitting_mode                        input
% 2.32/0.99  --splitting_grd                         true
% 2.32/0.99  --splitting_cvd                         false
% 2.32/0.99  --splitting_cvd_svl                     false
% 2.32/0.99  --splitting_nvd                         32
% 2.32/0.99  --sub_typing                            true
% 2.32/0.99  --prep_gs_sim                           true
% 2.32/0.99  --prep_unflatten                        true
% 2.32/0.99  --prep_res_sim                          true
% 2.32/0.99  --prep_upred                            true
% 2.32/0.99  --prep_sem_filter                       exhaustive
% 2.32/0.99  --prep_sem_filter_out                   false
% 2.32/0.99  --pred_elim                             true
% 2.32/0.99  --res_sim_input                         true
% 2.32/0.99  --eq_ax_congr_red                       true
% 2.32/0.99  --pure_diseq_elim                       true
% 2.32/0.99  --brand_transform                       false
% 2.32/0.99  --non_eq_to_eq                          false
% 2.32/0.99  --prep_def_merge                        true
% 2.32/0.99  --prep_def_merge_prop_impl              false
% 2.32/0.99  --prep_def_merge_mbd                    true
% 2.32/0.99  --prep_def_merge_tr_red                 false
% 2.32/0.99  --prep_def_merge_tr_cl                  false
% 2.32/0.99  --smt_preprocessing                     true
% 2.32/0.99  --smt_ac_axioms                         fast
% 2.32/0.99  --preprocessed_out                      false
% 2.32/0.99  --preprocessed_stats                    false
% 2.32/0.99  
% 2.32/0.99  ------ Abstraction refinement Options
% 2.32/0.99  
% 2.32/0.99  --abstr_ref                             []
% 2.32/0.99  --abstr_ref_prep                        false
% 2.32/0.99  --abstr_ref_until_sat                   false
% 2.32/0.99  --abstr_ref_sig_restrict                funpre
% 2.32/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.32/0.99  --abstr_ref_under                       []
% 2.32/0.99  
% 2.32/0.99  ------ SAT Options
% 2.32/0.99  
% 2.32/0.99  --sat_mode                              false
% 2.32/0.99  --sat_fm_restart_options                ""
% 2.32/0.99  --sat_gr_def                            false
% 2.32/0.99  --sat_epr_types                         true
% 2.32/0.99  --sat_non_cyclic_types                  false
% 2.32/0.99  --sat_finite_models                     false
% 2.32/0.99  --sat_fm_lemmas                         false
% 2.32/0.99  --sat_fm_prep                           false
% 2.32/0.99  --sat_fm_uc_incr                        true
% 2.32/0.99  --sat_out_model                         small
% 2.32/0.99  --sat_out_clauses                       false
% 2.32/0.99  
% 2.32/0.99  ------ QBF Options
% 2.32/0.99  
% 2.32/0.99  --qbf_mode                              false
% 2.32/0.99  --qbf_elim_univ                         false
% 2.32/0.99  --qbf_dom_inst                          none
% 2.32/0.99  --qbf_dom_pre_inst                      false
% 2.32/0.99  --qbf_sk_in                             false
% 2.32/0.99  --qbf_pred_elim                         true
% 2.32/0.99  --qbf_split                             512
% 2.32/0.99  
% 2.32/0.99  ------ BMC1 Options
% 2.32/0.99  
% 2.32/0.99  --bmc1_incremental                      false
% 2.32/0.99  --bmc1_axioms                           reachable_all
% 2.32/0.99  --bmc1_min_bound                        0
% 2.32/0.99  --bmc1_max_bound                        -1
% 2.32/0.99  --bmc1_max_bound_default                -1
% 2.32/0.99  --bmc1_symbol_reachability              true
% 2.32/0.99  --bmc1_property_lemmas                  false
% 2.32/0.99  --bmc1_k_induction                      false
% 2.32/0.99  --bmc1_non_equiv_states                 false
% 2.32/0.99  --bmc1_deadlock                         false
% 2.32/0.99  --bmc1_ucm                              false
% 2.32/0.99  --bmc1_add_unsat_core                   none
% 2.32/0.99  --bmc1_unsat_core_children              false
% 2.32/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.32/0.99  --bmc1_out_stat                         full
% 2.32/0.99  --bmc1_ground_init                      false
% 2.32/0.99  --bmc1_pre_inst_next_state              false
% 2.32/0.99  --bmc1_pre_inst_state                   false
% 2.32/0.99  --bmc1_pre_inst_reach_state             false
% 2.32/0.99  --bmc1_out_unsat_core                   false
% 2.32/0.99  --bmc1_aig_witness_out                  false
% 2.32/0.99  --bmc1_verbose                          false
% 2.32/0.99  --bmc1_dump_clauses_tptp                false
% 2.32/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.32/0.99  --bmc1_dump_file                        -
% 2.32/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.32/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.32/0.99  --bmc1_ucm_extend_mode                  1
% 2.32/0.99  --bmc1_ucm_init_mode                    2
% 2.32/0.99  --bmc1_ucm_cone_mode                    none
% 2.32/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.32/0.99  --bmc1_ucm_relax_model                  4
% 2.32/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.32/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.32/0.99  --bmc1_ucm_layered_model                none
% 2.32/0.99  --bmc1_ucm_max_lemma_size               10
% 2.32/0.99  
% 2.32/0.99  ------ AIG Options
% 2.32/0.99  
% 2.32/0.99  --aig_mode                              false
% 2.32/0.99  
% 2.32/0.99  ------ Instantiation Options
% 2.32/0.99  
% 2.32/0.99  --instantiation_flag                    true
% 2.32/0.99  --inst_sos_flag                         false
% 2.32/0.99  --inst_sos_phase                        true
% 2.32/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.32/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.32/0.99  --inst_lit_sel_side                     none
% 2.32/0.99  --inst_solver_per_active                1400
% 2.32/0.99  --inst_solver_calls_frac                1.
% 2.32/0.99  --inst_passive_queue_type               priority_queues
% 2.32/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.32/0.99  --inst_passive_queues_freq              [25;2]
% 2.32/0.99  --inst_dismatching                      true
% 2.32/0.99  --inst_eager_unprocessed_to_passive     true
% 2.32/0.99  --inst_prop_sim_given                   true
% 2.32/0.99  --inst_prop_sim_new                     false
% 2.32/0.99  --inst_subs_new                         false
% 2.32/0.99  --inst_eq_res_simp                      false
% 2.32/0.99  --inst_subs_given                       false
% 2.32/0.99  --inst_orphan_elimination               true
% 2.32/0.99  --inst_learning_loop_flag               true
% 2.32/0.99  --inst_learning_start                   3000
% 2.32/0.99  --inst_learning_factor                  2
% 2.32/0.99  --inst_start_prop_sim_after_learn       3
% 2.32/0.99  --inst_sel_renew                        solver
% 2.32/0.99  --inst_lit_activity_flag                true
% 2.32/0.99  --inst_restr_to_given                   false
% 2.32/0.99  --inst_activity_threshold               500
% 2.32/0.99  --inst_out_proof                        true
% 2.32/0.99  
% 2.32/0.99  ------ Resolution Options
% 2.32/0.99  
% 2.32/0.99  --resolution_flag                       false
% 2.32/0.99  --res_lit_sel                           adaptive
% 2.32/0.99  --res_lit_sel_side                      none
% 2.32/0.99  --res_ordering                          kbo
% 2.32/0.99  --res_to_prop_solver                    active
% 2.32/0.99  --res_prop_simpl_new                    false
% 2.32/0.99  --res_prop_simpl_given                  true
% 2.32/0.99  --res_passive_queue_type                priority_queues
% 2.32/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.32/0.99  --res_passive_queues_freq               [15;5]
% 2.32/0.99  --res_forward_subs                      full
% 2.32/0.99  --res_backward_subs                     full
% 2.32/0.99  --res_forward_subs_resolution           true
% 2.32/0.99  --res_backward_subs_resolution          true
% 2.32/0.99  --res_orphan_elimination                true
% 2.32/0.99  --res_time_limit                        2.
% 2.32/0.99  --res_out_proof                         true
% 2.32/0.99  
% 2.32/0.99  ------ Superposition Options
% 2.32/0.99  
% 2.32/0.99  --superposition_flag                    true
% 2.32/0.99  --sup_passive_queue_type                priority_queues
% 2.32/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.32/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.32/0.99  --demod_completeness_check              fast
% 2.32/0.99  --demod_use_ground                      true
% 2.32/0.99  --sup_to_prop_solver                    passive
% 2.32/0.99  --sup_prop_simpl_new                    true
% 2.32/0.99  --sup_prop_simpl_given                  true
% 2.32/0.99  --sup_fun_splitting                     false
% 2.32/0.99  --sup_smt_interval                      50000
% 2.32/0.99  
% 2.32/0.99  ------ Superposition Simplification Setup
% 2.32/0.99  
% 2.32/0.99  --sup_indices_passive                   []
% 2.32/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.32/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/0.99  --sup_full_bw                           [BwDemod]
% 2.32/0.99  --sup_immed_triv                        [TrivRules]
% 2.32/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.32/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/0.99  --sup_immed_bw_main                     []
% 2.32/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.32/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.32/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.32/0.99  
% 2.32/0.99  ------ Combination Options
% 2.32/0.99  
% 2.32/0.99  --comb_res_mult                         3
% 2.32/0.99  --comb_sup_mult                         2
% 2.32/0.99  --comb_inst_mult                        10
% 2.32/0.99  
% 2.32/0.99  ------ Debug Options
% 2.32/0.99  
% 2.32/0.99  --dbg_backtrace                         false
% 2.32/0.99  --dbg_dump_prop_clauses                 false
% 2.32/0.99  --dbg_dump_prop_clauses_file            -
% 2.32/0.99  --dbg_out_stat                          false
% 2.32/0.99  
% 2.32/0.99  
% 2.32/0.99  
% 2.32/0.99  
% 2.32/0.99  ------ Proving...
% 2.32/0.99  
% 2.32/0.99  
% 2.32/0.99  % SZS status Theorem for theBenchmark.p
% 2.32/0.99  
% 2.32/0.99   Resolution empty clause
% 2.32/0.99  
% 2.32/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.32/0.99  
% 2.32/0.99  fof(f12,axiom,(
% 2.32/0.99    ! [X0,X1] : (r1_tarski(X0,X1) => (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 2.32/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.32/0.99  
% 2.32/0.99  fof(f24,plain,(
% 2.32/0.99    ! [X0,X1] : ((r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0) | ~r1_tarski(X0,X1))),
% 2.32/0.99    inference(ennf_transformation,[],[f12])).
% 2.32/0.99  
% 2.32/0.99  fof(f25,plain,(
% 2.32/0.99    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1))),
% 2.32/0.99    inference(flattening,[],[f24])).
% 2.32/0.99  
% 2.32/0.99  fof(f47,plain,(
% 2.32/0.99    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1)) )),
% 2.32/0.99    inference(cnf_transformation,[],[f25])).
% 2.32/0.99  
% 2.32/0.99  fof(f13,conjecture,(
% 2.32/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 2.32/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.32/0.99  
% 2.32/0.99  fof(f14,negated_conjecture,(
% 2.32/0.99    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 2.32/0.99    inference(negated_conjecture,[],[f13])).
% 2.32/0.99  
% 2.32/0.99  fof(f26,plain,(
% 2.32/0.99    ? [X0,X1] : (? [X2] : ((~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.32/0.99    inference(ennf_transformation,[],[f14])).
% 2.32/0.99  
% 2.32/0.99  fof(f27,plain,(
% 2.32/0.99    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.32/0.99    inference(flattening,[],[f26])).
% 2.32/0.99  
% 2.32/0.99  fof(f32,plain,(
% 2.32/0.99    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (~r1_tarski(k8_setfam_1(X0,sK3),k8_setfam_1(X0,X1)) & r1_tarski(X1,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(X0))))) )),
% 2.32/0.99    introduced(choice_axiom,[])).
% 2.32/0.99  
% 2.32/0.99  fof(f31,plain,(
% 2.32/0.99    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (? [X2] : (~r1_tarski(k8_setfam_1(sK1,X2),k8_setfam_1(sK1,sK2)) & r1_tarski(sK2,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK1)))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))))),
% 2.32/0.99    introduced(choice_axiom,[])).
% 2.32/0.99  
% 2.32/0.99  fof(f33,plain,(
% 2.32/0.99    (~r1_tarski(k8_setfam_1(sK1,sK3),k8_setfam_1(sK1,sK2)) & r1_tarski(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1)))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1)))),
% 2.32/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f27,f32,f31])).
% 2.32/0.99  
% 2.32/0.99  fof(f49,plain,(
% 2.32/0.99    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1)))),
% 2.32/0.99    inference(cnf_transformation,[],[f33])).
% 2.32/0.99  
% 2.32/0.99  fof(f6,axiom,(
% 2.32/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((k1_xboole_0 = X1 => k8_setfam_1(X0,X1) = X0) & (k1_xboole_0 != X1 => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1))))),
% 2.32/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.32/0.99  
% 2.32/0.99  fof(f18,plain,(
% 2.32/0.99    ! [X0,X1] : (((k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1) & (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.32/0.99    inference(ennf_transformation,[],[f6])).
% 2.32/0.99  
% 2.32/0.99  fof(f39,plain,(
% 2.32/0.99    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.32/0.99    inference(cnf_transformation,[],[f18])).
% 2.32/0.99  
% 2.32/0.99  fof(f8,axiom,(
% 2.32/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k6_setfam_1(X0,X1) = k1_setfam_1(X1))),
% 2.32/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.32/0.99  
% 2.32/0.99  fof(f20,plain,(
% 2.32/0.99    ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.32/0.99    inference(ennf_transformation,[],[f8])).
% 2.32/0.99  
% 2.32/0.99  fof(f42,plain,(
% 2.32/0.99    ( ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.32/0.99    inference(cnf_transformation,[],[f20])).
% 2.32/0.99  
% 2.32/0.99  fof(f48,plain,(
% 2.32/0.99    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1)))),
% 2.32/0.99    inference(cnf_transformation,[],[f33])).
% 2.32/0.99  
% 2.32/0.99  fof(f51,plain,(
% 2.32/0.99    ~r1_tarski(k8_setfam_1(sK1,sK3),k8_setfam_1(sK1,sK2))),
% 2.32/0.99    inference(cnf_transformation,[],[f33])).
% 2.32/0.99  
% 2.32/0.99  fof(f50,plain,(
% 2.32/0.99    r1_tarski(sK2,sK3)),
% 2.32/0.99    inference(cnf_transformation,[],[f33])).
% 2.32/0.99  
% 2.32/0.99  fof(f40,plain,(
% 2.32/0.99    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.32/0.99    inference(cnf_transformation,[],[f18])).
% 2.32/0.99  
% 2.32/0.99  fof(f52,plain,(
% 2.32/0.99    ( ! [X0] : (k8_setfam_1(X0,k1_xboole_0) = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.32/0.99    inference(equality_resolution,[],[f40])).
% 2.32/0.99  
% 2.32/0.99  fof(f5,axiom,(
% 2.32/0.99    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.32/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.32/0.99  
% 2.32/0.99  fof(f38,plain,(
% 2.32/0.99    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.32/0.99    inference(cnf_transformation,[],[f5])).
% 2.32/0.99  
% 2.32/0.99  fof(f7,axiom,(
% 2.32/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.32/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.32/0.99  
% 2.32/0.99  fof(f19,plain,(
% 2.32/0.99    ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.32/0.99    inference(ennf_transformation,[],[f7])).
% 2.32/0.99  
% 2.32/0.99  fof(f41,plain,(
% 2.32/0.99    ( ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.32/0.99    inference(cnf_transformation,[],[f19])).
% 2.32/0.99  
% 2.32/0.99  fof(f9,axiom,(
% 2.32/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.32/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.32/0.99  
% 2.32/0.99  fof(f30,plain,(
% 2.32/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.32/0.99    inference(nnf_transformation,[],[f9])).
% 2.32/0.99  
% 2.32/0.99  fof(f43,plain,(
% 2.32/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.32/0.99    inference(cnf_transformation,[],[f30])).
% 2.32/0.99  
% 2.32/0.99  fof(f1,axiom,(
% 2.32/0.99    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 2.32/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.32/0.99  
% 2.32/0.99  fof(f15,plain,(
% 2.32/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 2.32/0.99    inference(ennf_transformation,[],[f1])).
% 2.32/0.99  
% 2.32/0.99  fof(f28,plain,(
% 2.32/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.32/0.99    introduced(choice_axiom,[])).
% 2.32/0.99  
% 2.32/0.99  fof(f29,plain,(
% 2.32/0.99    ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0)),
% 2.32/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f28])).
% 2.32/0.99  
% 2.32/0.99  fof(f34,plain,(
% 2.32/0.99    ( ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0) )),
% 2.32/0.99    inference(cnf_transformation,[],[f29])).
% 2.32/0.99  
% 2.32/0.99  fof(f11,axiom,(
% 2.32/0.99    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 2.32/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.32/0.99  
% 2.32/0.99  fof(f23,plain,(
% 2.32/0.99    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.32/0.99    inference(ennf_transformation,[],[f11])).
% 2.32/0.99  
% 2.32/0.99  fof(f46,plain,(
% 2.32/0.99    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.32/0.99    inference(cnf_transformation,[],[f23])).
% 2.32/0.99  
% 2.32/0.99  fof(f44,plain,(
% 2.32/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.32/0.99    inference(cnf_transformation,[],[f30])).
% 2.32/0.99  
% 2.32/0.99  fof(f2,axiom,(
% 2.32/0.99    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 2.32/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.32/0.99  
% 2.32/0.99  fof(f35,plain,(
% 2.32/0.99    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 2.32/0.99    inference(cnf_transformation,[],[f2])).
% 2.32/0.99  
% 2.32/0.99  fof(f3,axiom,(
% 2.32/0.99    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 2.32/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.32/0.99  
% 2.32/0.99  fof(f16,plain,(
% 2.32/0.99    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 2.32/0.99    inference(ennf_transformation,[],[f3])).
% 2.32/0.99  
% 2.32/0.99  fof(f17,plain,(
% 2.32/0.99    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 2.32/0.99    inference(flattening,[],[f16])).
% 2.32/0.99  
% 2.32/0.99  fof(f36,plain,(
% 2.32/0.99    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 2.32/0.99    inference(cnf_transformation,[],[f17])).
% 2.32/0.99  
% 2.32/0.99  fof(f4,axiom,(
% 2.32/0.99    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 2.32/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.32/0.99  
% 2.32/0.99  fof(f37,plain,(
% 2.32/0.99    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 2.32/0.99    inference(cnf_transformation,[],[f4])).
% 2.32/0.99  
% 2.32/0.99  cnf(c_13,plain,
% 2.32/0.99      ( ~ r1_tarski(X0,X1)
% 2.32/0.99      | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
% 2.32/0.99      | k1_xboole_0 = X0 ),
% 2.32/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_848,plain,
% 2.32/0.99      ( k1_xboole_0 = X0
% 2.32/0.99      | r1_tarski(X0,X1) != iProver_top
% 2.32/0.99      | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) = iProver_top ),
% 2.32/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_16,negated_conjecture,
% 2.32/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
% 2.32/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_845,plain,
% 2.32/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
% 2.32/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_6,plain,
% 2.32/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.32/0.99      | k6_setfam_1(X1,X0) = k8_setfam_1(X1,X0)
% 2.32/0.99      | k1_xboole_0 = X0 ),
% 2.32/0.99      inference(cnf_transformation,[],[f39]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_853,plain,
% 2.32/0.99      ( k6_setfam_1(X0,X1) = k8_setfam_1(X0,X1)
% 2.32/0.99      | k1_xboole_0 = X1
% 2.32/0.99      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 2.32/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_1869,plain,
% 2.32/0.99      ( k6_setfam_1(sK1,sK3) = k8_setfam_1(sK1,sK3) | sK3 = k1_xboole_0 ),
% 2.32/0.99      inference(superposition,[status(thm)],[c_845,c_853]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_8,plain,
% 2.32/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.32/0.99      | k6_setfam_1(X1,X0) = k1_setfam_1(X0) ),
% 2.32/0.99      inference(cnf_transformation,[],[f42]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_851,plain,
% 2.32/0.99      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
% 2.32/0.99      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 2.32/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_1298,plain,
% 2.32/0.99      ( k6_setfam_1(sK1,sK3) = k1_setfam_1(sK3) ),
% 2.32/0.99      inference(superposition,[status(thm)],[c_845,c_851]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_1887,plain,
% 2.32/0.99      ( k8_setfam_1(sK1,sK3) = k1_setfam_1(sK3) | sK3 = k1_xboole_0 ),
% 2.32/0.99      inference(light_normalisation,[status(thm)],[c_1869,c_1298]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_17,negated_conjecture,
% 2.32/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
% 2.32/0.99      inference(cnf_transformation,[],[f48]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_844,plain,
% 2.32/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
% 2.32/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_1870,plain,
% 2.32/0.99      ( k6_setfam_1(sK1,sK2) = k8_setfam_1(sK1,sK2) | sK2 = k1_xboole_0 ),
% 2.32/0.99      inference(superposition,[status(thm)],[c_844,c_853]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_1299,plain,
% 2.32/0.99      ( k6_setfam_1(sK1,sK2) = k1_setfam_1(sK2) ),
% 2.32/0.99      inference(superposition,[status(thm)],[c_844,c_851]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_1882,plain,
% 2.32/0.99      ( k8_setfam_1(sK1,sK2) = k1_setfam_1(sK2) | sK2 = k1_xboole_0 ),
% 2.32/0.99      inference(light_normalisation,[status(thm)],[c_1870,c_1299]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_14,negated_conjecture,
% 2.32/0.99      ( ~ r1_tarski(k8_setfam_1(sK1,sK3),k8_setfam_1(sK1,sK2)) ),
% 2.32/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_847,plain,
% 2.32/0.99      ( r1_tarski(k8_setfam_1(sK1,sK3),k8_setfam_1(sK1,sK2)) != iProver_top ),
% 2.32/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_2253,plain,
% 2.32/0.99      ( sK2 = k1_xboole_0
% 2.32/0.99      | r1_tarski(k8_setfam_1(sK1,sK3),k1_setfam_1(sK2)) != iProver_top ),
% 2.32/0.99      inference(superposition,[status(thm)],[c_1882,c_847]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_2336,plain,
% 2.32/0.99      ( sK2 = k1_xboole_0
% 2.32/0.99      | sK3 = k1_xboole_0
% 2.32/0.99      | r1_tarski(k1_setfam_1(sK3),k1_setfam_1(sK2)) != iProver_top ),
% 2.32/0.99      inference(superposition,[status(thm)],[c_1887,c_2253]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_2446,plain,
% 2.32/0.99      ( sK2 = k1_xboole_0
% 2.32/0.99      | sK3 = k1_xboole_0
% 2.32/0.99      | r1_tarski(sK2,sK3) != iProver_top ),
% 2.32/0.99      inference(superposition,[status(thm)],[c_848,c_2336]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_15,negated_conjecture,
% 2.32/0.99      ( r1_tarski(sK2,sK3) ),
% 2.32/0.99      inference(cnf_transformation,[],[f50]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_2447,plain,
% 2.32/0.99      ( ~ r1_tarski(sK2,sK3) | sK2 = k1_xboole_0 | sK3 = k1_xboole_0 ),
% 2.32/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_2446]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_2491,plain,
% 2.32/0.99      ( sK3 = k1_xboole_0 | sK2 = k1_xboole_0 ),
% 2.32/0.99      inference(global_propositional_subsumption,
% 2.32/0.99                [status(thm)],
% 2.32/0.99                [c_2446,c_15,c_2447]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_2492,plain,
% 2.32/0.99      ( sK2 = k1_xboole_0 | sK3 = k1_xboole_0 ),
% 2.32/0.99      inference(renaming,[status(thm)],[c_2491]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_2500,plain,
% 2.32/0.99      ( sK3 = k1_xboole_0
% 2.32/0.99      | r1_tarski(k8_setfam_1(sK1,sK3),k8_setfam_1(sK1,k1_xboole_0)) != iProver_top ),
% 2.32/0.99      inference(superposition,[status(thm)],[c_2492,c_847]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_5,plain,
% 2.32/0.99      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
% 2.32/0.99      | k8_setfam_1(X0,k1_xboole_0) = X0 ),
% 2.32/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_854,plain,
% 2.32/0.99      ( k8_setfam_1(X0,k1_xboole_0) = X0
% 2.32/0.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 2.32/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_4,plain,
% 2.32/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.32/0.99      inference(cnf_transformation,[],[f38]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_855,plain,
% 2.32/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.32/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_878,plain,
% 2.32/0.99      ( k8_setfam_1(X0,k1_xboole_0) = X0 ),
% 2.32/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_854,c_855]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_2509,plain,
% 2.32/0.99      ( sK3 = k1_xboole_0
% 2.32/0.99      | r1_tarski(k8_setfam_1(sK1,sK3),sK1) != iProver_top ),
% 2.32/0.99      inference(demodulation,[status(thm)],[c_2500,c_878]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_7,plain,
% 2.32/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.32/0.99      | m1_subset_1(k8_setfam_1(X1,X0),k1_zfmisc_1(X1)) ),
% 2.32/0.99      inference(cnf_transformation,[],[f41]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_852,plain,
% 2.32/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 2.32/0.99      | m1_subset_1(k8_setfam_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 2.32/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_10,plain,
% 2.32/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.32/0.99      inference(cnf_transformation,[],[f43]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_849,plain,
% 2.32/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.32/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 2.32/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_1325,plain,
% 2.32/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 2.32/0.99      | r1_tarski(k8_setfam_1(X1,X0),X1) = iProver_top ),
% 2.32/0.99      inference(superposition,[status(thm)],[c_852,c_849]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_2688,plain,
% 2.32/0.99      ( r1_tarski(k8_setfam_1(sK1,sK3),sK1) = iProver_top ),
% 2.32/0.99      inference(superposition,[status(thm)],[c_845,c_1325]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_3054,plain,
% 2.32/0.99      ( sK3 = k1_xboole_0 ),
% 2.32/0.99      inference(global_propositional_subsumption,[status(thm)],[c_2509,c_2688]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_846,plain,
% 2.32/0.99      ( r1_tarski(sK2,sK3) = iProver_top ),
% 2.32/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_0,plain,
% 2.32/0.99      ( r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0 ),
% 2.32/0.99      inference(cnf_transformation,[],[f34]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_12,plain,
% 2.32/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.32/0.99      | ~ r2_hidden(X2,X0)
% 2.32/0.99      | ~ v1_xboole_0(X1) ),
% 2.32/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_9,plain,
% 2.32/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.32/0.99      inference(cnf_transformation,[],[f44]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_138,plain,
% 2.32/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.32/0.99      inference(prop_impl,[status(thm)],[c_9]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_139,plain,
% 2.32/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.32/0.99      inference(renaming,[status(thm)],[c_138]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_169,plain,
% 2.32/0.99      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | ~ v1_xboole_0(X1) ),
% 2.32/0.99      inference(bin_hyper_res,[status(thm)],[c_12,c_139]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_281,plain,
% 2.32/0.99      ( ~ r1_tarski(X0,X1)
% 2.32/0.99      | ~ v1_xboole_0(X1)
% 2.32/0.99      | X0 != X2
% 2.32/0.99      | sK0(X2) != X3
% 2.32/0.99      | k1_xboole_0 = X2 ),
% 2.32/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_169]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_282,plain,
% 2.32/0.99      ( ~ r1_tarski(X0,X1) | ~ v1_xboole_0(X1) | k1_xboole_0 = X0 ),
% 2.32/0.99      inference(unflattening,[status(thm)],[c_281]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_842,plain,
% 2.32/0.99      ( k1_xboole_0 = X0
% 2.32/0.99      | r1_tarski(X0,X1) != iProver_top
% 2.32/0.99      | v1_xboole_0(X1) != iProver_top ),
% 2.32/0.99      inference(predicate_to_equality,[status(thm)],[c_282]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_1834,plain,
% 2.32/0.99      ( sK2 = k1_xboole_0 | v1_xboole_0(sK3) != iProver_top ),
% 2.32/0.99      inference(superposition,[status(thm)],[c_846,c_842]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_3060,plain,
% 2.32/0.99      ( sK2 = k1_xboole_0 | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.32/0.99      inference(demodulation,[status(thm)],[c_3054,c_1834]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_31,plain,
% 2.32/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.32/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 2.32/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_33,plain,
% 2.32/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.32/0.99      | r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 2.32/0.99      inference(instantiation,[status(thm)],[c_31]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_49,plain,
% 2.32/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.32/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_51,plain,
% 2.32/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.32/0.99      inference(instantiation,[status(thm)],[c_49]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_1,plain,
% 2.32/0.99      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.32/0.99      inference(cnf_transformation,[],[f35]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_58,plain,
% 2.32/0.99      ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 2.32/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_2,plain,
% 2.32/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_xboole_0(X0,X1) | v1_xboole_0(X0) ),
% 2.32/0.99      inference(cnf_transformation,[],[f36]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_3,plain,
% 2.32/0.99      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 2.32/0.99      inference(cnf_transformation,[],[f37]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_233,plain,
% 2.32/0.99      ( ~ r1_tarski(X0,X1)
% 2.32/0.99      | v1_xboole_0(X0)
% 2.32/0.99      | X2 != X1
% 2.32/0.99      | k4_xboole_0(X3,X2) != X0 ),
% 2.32/0.99      inference(resolution_lifted,[status(thm)],[c_2,c_3]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_234,plain,
% 2.32/0.99      ( ~ r1_tarski(k4_xboole_0(X0,X1),X1) | v1_xboole_0(k4_xboole_0(X0,X1)) ),
% 2.32/0.99      inference(unflattening,[status(thm)],[c_233]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_235,plain,
% 2.32/0.99      ( r1_tarski(k4_xboole_0(X0,X1),X1) != iProver_top
% 2.32/0.99      | v1_xboole_0(k4_xboole_0(X0,X1)) = iProver_top ),
% 2.32/0.99      inference(predicate_to_equality,[status(thm)],[c_234]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_237,plain,
% 2.32/0.99      ( r1_tarski(k4_xboole_0(k1_xboole_0,k1_xboole_0),k1_xboole_0) != iProver_top
% 2.32/0.99      | v1_xboole_0(k4_xboole_0(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 2.32/0.99      inference(instantiation,[status(thm)],[c_235]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_475,plain,( X0 = X0 ),theory(equality) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_490,plain,
% 2.32/0.99      ( k1_xboole_0 = k1_xboole_0 ),
% 2.32/0.99      inference(instantiation,[status(thm)],[c_475]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_478,plain,
% 2.32/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.32/0.99      theory(equality) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_992,plain,
% 2.32/0.99      ( ~ r1_tarski(X0,X1)
% 2.32/0.99      | r1_tarski(k4_xboole_0(X2,X3),X3)
% 2.32/0.99      | X3 != X1
% 2.32/0.99      | k4_xboole_0(X2,X3) != X0 ),
% 2.32/0.99      inference(instantiation,[status(thm)],[c_478]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_993,plain,
% 2.32/0.99      ( X0 != X1
% 2.32/0.99      | k4_xboole_0(X2,X0) != X3
% 2.32/0.99      | r1_tarski(X3,X1) != iProver_top
% 2.32/0.99      | r1_tarski(k4_xboole_0(X2,X0),X0) = iProver_top ),
% 2.32/0.99      inference(predicate_to_equality,[status(thm)],[c_992]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_995,plain,
% 2.32/0.99      ( k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 2.32/0.99      | k1_xboole_0 != k1_xboole_0
% 2.32/0.99      | r1_tarski(k4_xboole_0(k1_xboole_0,k1_xboole_0),k1_xboole_0) = iProver_top
% 2.32/0.99      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 2.32/0.99      inference(instantiation,[status(thm)],[c_993]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_479,plain,
% 2.32/0.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 2.32/0.99      theory(equality) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_1034,plain,
% 2.32/0.99      ( v1_xboole_0(X0)
% 2.32/0.99      | ~ v1_xboole_0(k4_xboole_0(X1,X2))
% 2.32/0.99      | X0 != k4_xboole_0(X1,X2) ),
% 2.32/0.99      inference(instantiation,[status(thm)],[c_479]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_1035,plain,
% 2.32/0.99      ( X0 != k4_xboole_0(X1,X2)
% 2.32/0.99      | v1_xboole_0(X0) = iProver_top
% 2.32/0.99      | v1_xboole_0(k4_xboole_0(X1,X2)) != iProver_top ),
% 2.32/0.99      inference(predicate_to_equality,[status(thm)],[c_1034]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_1037,plain,
% 2.32/0.99      ( k1_xboole_0 != k4_xboole_0(k1_xboole_0,k1_xboole_0)
% 2.32/0.99      | v1_xboole_0(k4_xboole_0(k1_xboole_0,k1_xboole_0)) != iProver_top
% 2.32/0.99      | v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.32/0.99      inference(instantiation,[status(thm)],[c_1035]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_476,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_1287,plain,
% 2.32/0.99      ( X0 != X1 | X0 = k4_xboole_0(X2,X3) | k4_xboole_0(X2,X3) != X1 ),
% 2.32/0.99      inference(instantiation,[status(thm)],[c_476]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_1288,plain,
% 2.32/0.99      ( k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 2.32/0.99      | k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)
% 2.32/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 2.32/0.99      inference(instantiation,[status(thm)],[c_1287]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_3178,plain,
% 2.32/0.99      ( sK2 = k1_xboole_0 ),
% 2.32/0.99      inference(global_propositional_subsumption,
% 2.32/0.99                [status(thm)],
% 2.32/0.99                [c_3060,c_33,c_51,c_58,c_237,c_490,c_995,c_1037,c_1288]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_3063,plain,
% 2.32/0.99      ( r1_tarski(k8_setfam_1(sK1,k1_xboole_0),k8_setfam_1(sK1,sK2)) != iProver_top ),
% 2.32/0.99      inference(demodulation,[status(thm)],[c_3054,c_847]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_3070,plain,
% 2.32/0.99      ( r1_tarski(sK1,k8_setfam_1(sK1,sK2)) != iProver_top ),
% 2.32/0.99      inference(demodulation,[status(thm)],[c_3063,c_878]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_3181,plain,
% 2.32/0.99      ( r1_tarski(sK1,k8_setfam_1(sK1,k1_xboole_0)) != iProver_top ),
% 2.32/0.99      inference(demodulation,[status(thm)],[c_3178,c_3070]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_3190,plain,
% 2.32/0.99      ( r1_tarski(sK1,sK1) != iProver_top ),
% 2.32/0.99      inference(demodulation,[status(thm)],[c_3181,c_878]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_1323,plain,
% 2.32/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top
% 2.32/0.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 2.32/0.99      inference(superposition,[status(thm)],[c_878,c_852]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_957,plain,
% 2.32/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ),
% 2.32/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_960,plain,
% 2.32/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) = iProver_top ),
% 2.32/0.99      inference(predicate_to_equality,[status(thm)],[c_957]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_1941,plain,
% 2.32/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.32/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1323,c_960]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_1948,plain,
% 2.32/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 2.32/0.99      inference(superposition,[status(thm)],[c_1941,c_849]) ).
% 2.32/0.99  
% 2.32/0.99  cnf(c_3358,plain,
% 2.32/0.99      ( $false ),
% 2.32/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_3190,c_1948]) ).
% 2.32/0.99  
% 2.32/0.99  
% 2.32/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.32/0.99  
% 2.32/0.99  ------                               Statistics
% 2.32/0.99  
% 2.32/0.99  ------ General
% 2.32/0.99  
% 2.32/0.99  abstr_ref_over_cycles:                  0
% 2.32/0.99  abstr_ref_under_cycles:                 0
% 2.32/0.99  gc_basic_clause_elim:                   0
% 2.32/0.99  forced_gc_time:                         0
% 2.32/0.99  parsing_time:                           0.009
% 2.32/0.99  unif_index_cands_time:                  0.
% 2.32/0.99  unif_index_add_time:                    0.
% 2.32/0.99  orderings_time:                         0.
% 2.32/0.99  out_proof_time:                         0.011
% 2.32/0.99  total_time:                             0.133
% 2.32/0.99  num_of_symbols:                         46
% 2.32/0.99  num_of_terms:                           2885
% 2.32/0.99  
% 2.32/0.99  ------ Preprocessing
% 2.32/0.99  
% 2.32/0.99  num_of_splits:                          0
% 2.32/0.99  num_of_split_atoms:                     0
% 2.32/0.99  num_of_reused_defs:                     0
% 2.32/0.99  num_eq_ax_congr_red:                    18
% 2.32/0.99  num_of_sem_filtered_clauses:            1
% 2.32/0.99  num_of_subtypes:                        0
% 2.32/0.99  monotx_restored_types:                  0
% 2.32/0.99  sat_num_of_epr_types:                   0
% 2.32/0.99  sat_num_of_non_cyclic_types:            0
% 2.32/0.99  sat_guarded_non_collapsed_types:        0
% 2.32/0.99  num_pure_diseq_elim:                    0
% 2.32/0.99  simp_replaced_by:                       0
% 2.32/0.99  res_preprocessed:                       83
% 2.32/0.99  prep_upred:                             0
% 2.32/0.99  prep_unflattend:                        9
% 2.32/0.99  smt_new_axioms:                         0
% 2.32/0.99  pred_elim_cands:                        3
% 2.32/0.99  pred_elim:                              2
% 2.32/0.99  pred_elim_cl:                           2
% 2.32/0.99  pred_elim_cycles:                       5
% 2.32/0.99  merged_defs:                            8
% 2.32/0.99  merged_defs_ncl:                        0
% 2.32/0.99  bin_hyper_res:                          10
% 2.32/0.99  prep_cycles:                            4
% 2.32/0.99  pred_elim_time:                         0.002
% 2.32/0.99  splitting_time:                         0.
% 2.32/0.99  sem_filter_time:                        0.
% 2.32/0.99  monotx_time:                            0.
% 2.32/0.99  subtype_inf_time:                       0.
% 2.32/0.99  
% 2.32/0.99  ------ Problem properties
% 2.32/0.99  
% 2.32/0.99  clauses:                                16
% 2.32/0.99  conjectures:                            4
% 2.32/0.99  epr:                                    2
% 2.32/0.99  horn:                                   13
% 2.32/0.99  ground:                                 4
% 2.32/0.99  unary:                                  6
% 2.32/0.99  binary:                                 6
% 2.32/0.99  lits:                                   30
% 2.32/0.99  lits_eq:                                8
% 2.32/0.99  fd_pure:                                0
% 2.32/0.99  fd_pseudo:                              0
% 2.32/0.99  fd_cond:                                4
% 2.32/0.99  fd_pseudo_cond:                         0
% 2.32/0.99  ac_symbols:                             0
% 2.32/0.99  
% 2.32/0.99  ------ Propositional Solver
% 2.32/0.99  
% 2.32/0.99  prop_solver_calls:                      28
% 2.32/0.99  prop_fast_solver_calls:                 452
% 2.32/0.99  smt_solver_calls:                       0
% 2.32/0.99  smt_fast_solver_calls:                  0
% 2.32/0.99  prop_num_of_clauses:                    1199
% 2.32/0.99  prop_preprocess_simplified:             3685
% 2.32/0.99  prop_fo_subsumed:                       8
% 2.32/0.99  prop_solver_time:                       0.
% 2.32/0.99  smt_solver_time:                        0.
% 2.32/0.99  smt_fast_solver_time:                   0.
% 2.32/0.99  prop_fast_solver_time:                  0.
% 2.32/0.99  prop_unsat_core_time:                   0.
% 2.32/0.99  
% 2.32/0.99  ------ QBF
% 2.32/0.99  
% 2.32/0.99  qbf_q_res:                              0
% 2.32/0.99  qbf_num_tautologies:                    0
% 2.32/0.99  qbf_prep_cycles:                        0
% 2.32/0.99  
% 2.32/0.99  ------ BMC1
% 2.32/0.99  
% 2.32/0.99  bmc1_current_bound:                     -1
% 2.32/0.99  bmc1_last_solved_bound:                 -1
% 2.32/0.99  bmc1_unsat_core_size:                   -1
% 2.32/0.99  bmc1_unsat_core_parents_size:           -1
% 2.32/0.99  bmc1_merge_next_fun:                    0
% 2.32/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.32/0.99  
% 2.32/0.99  ------ Instantiation
% 2.32/0.99  
% 2.32/0.99  inst_num_of_clauses:                    370
% 2.32/0.99  inst_num_in_passive:                    8
% 2.32/0.99  inst_num_in_active:                     217
% 2.32/0.99  inst_num_in_unprocessed:                145
% 2.32/0.99  inst_num_of_loops:                      240
% 2.32/0.99  inst_num_of_learning_restarts:          0
% 2.32/0.99  inst_num_moves_active_passive:          20
% 2.32/0.99  inst_lit_activity:                      0
% 2.32/0.99  inst_lit_activity_moves:                0
% 2.32/0.99  inst_num_tautologies:                   0
% 2.32/0.99  inst_num_prop_implied:                  0
% 2.32/0.99  inst_num_existing_simplified:           0
% 2.32/0.99  inst_num_eq_res_simplified:             0
% 2.32/0.99  inst_num_child_elim:                    0
% 2.32/0.99  inst_num_of_dismatching_blockings:      111
% 2.32/0.99  inst_num_of_non_proper_insts:           375
% 2.32/0.99  inst_num_of_duplicates:                 0
% 2.32/0.99  inst_inst_num_from_inst_to_res:         0
% 2.32/0.99  inst_dismatching_checking_time:         0.
% 2.32/0.99  
% 2.32/0.99  ------ Resolution
% 2.32/0.99  
% 2.32/0.99  res_num_of_clauses:                     0
% 2.32/0.99  res_num_in_passive:                     0
% 2.32/0.99  res_num_in_active:                      0
% 2.32/0.99  res_num_of_loops:                       87
% 2.32/0.99  res_forward_subset_subsumed:            45
% 2.32/0.99  res_backward_subset_subsumed:           0
% 2.32/0.99  res_forward_subsumed:                   0
% 2.32/0.99  res_backward_subsumed:                  0
% 2.32/0.99  res_forward_subsumption_resolution:     0
% 2.32/0.99  res_backward_subsumption_resolution:    0
% 2.32/0.99  res_clause_to_clause_subsumption:       165
% 2.32/0.99  res_orphan_elimination:                 0
% 2.32/0.99  res_tautology_del:                      29
% 2.32/0.99  res_num_eq_res_simplified:              0
% 2.32/0.99  res_num_sel_changes:                    0
% 2.32/0.99  res_moves_from_active_to_pass:          0
% 2.32/0.99  
% 2.32/0.99  ------ Superposition
% 2.32/0.99  
% 2.32/0.99  sup_time_total:                         0.
% 2.32/0.99  sup_time_generating:                    0.
% 2.32/0.99  sup_time_sim_full:                      0.
% 2.32/0.99  sup_time_sim_immed:                     0.
% 2.32/0.99  
% 2.32/0.99  sup_num_of_clauses:                     43
% 2.32/0.99  sup_num_in_active:                      26
% 2.32/0.99  sup_num_in_passive:                     17
% 2.32/0.99  sup_num_of_loops:                       47
% 2.32/0.99  sup_fw_superposition:                   45
% 2.32/0.99  sup_bw_superposition:                   28
% 2.32/0.99  sup_immediate_simplified:               25
% 2.32/0.99  sup_given_eliminated:                   0
% 2.32/0.99  comparisons_done:                       0
% 2.32/0.99  comparisons_avoided:                    10
% 2.32/0.99  
% 2.32/0.99  ------ Simplifications
% 2.32/0.99  
% 2.32/0.99  
% 2.32/0.99  sim_fw_subset_subsumed:                 5
% 2.32/0.99  sim_bw_subset_subsumed:                 11
% 2.32/0.99  sim_fw_subsumed:                        9
% 2.32/0.99  sim_bw_subsumed:                        0
% 2.32/0.99  sim_fw_subsumption_res:                 2
% 2.32/0.99  sim_bw_subsumption_res:                 0
% 2.32/0.99  sim_tautology_del:                      1
% 2.32/0.99  sim_eq_tautology_del:                   6
% 2.32/0.99  sim_eq_res_simp:                        0
% 2.32/0.99  sim_fw_demodulated:                     8
% 2.32/0.99  sim_bw_demodulated:                     16
% 2.32/0.99  sim_light_normalised:                   5
% 2.32/0.99  sim_joinable_taut:                      0
% 2.32/0.99  sim_joinable_simp:                      0
% 2.32/0.99  sim_ac_normalised:                      0
% 2.32/0.99  sim_smt_subsumption:                    0
% 2.32/0.99  
%------------------------------------------------------------------------------
