%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:42:28 EST 2020

% Result     : Theorem 2.33s
% Output     : CNFRefutation 2.33s
% Verified   : 
% Statistics : Number of formulae       :  130 (1019 expanded)
%              Number of clauses        :   79 ( 376 expanded)
%              Number of leaves         :   17 ( 236 expanded)
%              Depth                    :   23
%              Number of atoms          :  288 (3172 expanded)
%              Number of equality atoms :  143 ( 853 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( r1_tarski(X1,X2)
           => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( r1_tarski(X1,X2)
             => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f21])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
     => ( ~ r1_tarski(k8_setfam_1(X0,sK3),k8_setfam_1(X0,X1))
        & r1_tarski(X1,sK3)
        & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
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

fof(f32,plain,
    ( ~ r1_tarski(k8_setfam_1(sK1,sK3),k8_setfam_1(sK1,sK2))
    & r1_tarski(sK2,sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1)))
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f22,f31,f30])).

fof(f50,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(cnf_transformation,[],[f32])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ( k1_xboole_0 = X1
         => k8_setfam_1(X0,X1) = X0 )
        & ( k1_xboole_0 != X1
         => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ( k8_setfam_1(X0,X1) = X0
          | k1_xboole_0 != X1 )
        & ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
          | k1_xboole_0 = X1 ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f49,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(cnf_transformation,[],[f32])).

fof(f52,plain,(
    ~ r1_tarski(k8_setfam_1(sK1,sK3),k8_setfam_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f32])).

fof(f51,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f55,plain,(
    ! [X0] :
      ( k8_setfam_1(X0,k1_xboole_0) = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f43])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f27])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f53,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f39])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f23])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).

fof(f34,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f35,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_771,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k6_setfam_1(X1,X0) = k8_setfam_1(X1,X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_779,plain,
    ( k6_setfam_1(X0,X1) = k8_setfam_1(X0,X1)
    | k1_xboole_0 = X1
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2225,plain,
    ( k6_setfam_1(sK1,sK3) = k8_setfam_1(sK1,sK3)
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_771,c_779])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k6_setfam_1(X1,X0) = k1_setfam_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_777,plain,
    ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1721,plain,
    ( k6_setfam_1(sK1,sK3) = k1_setfam_1(sK3) ),
    inference(superposition,[status(thm)],[c_771,c_777])).

cnf(c_2240,plain,
    ( k8_setfam_1(sK1,sK3) = k1_setfam_1(sK3)
    | sK3 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2225,c_1721])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_770,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2226,plain,
    ( k6_setfam_1(sK1,sK2) = k8_setfam_1(sK1,sK2)
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_770,c_779])).

cnf(c_1722,plain,
    ( k6_setfam_1(sK1,sK2) = k1_setfam_1(sK2) ),
    inference(superposition,[status(thm)],[c_770,c_777])).

cnf(c_2235,plain,
    ( k8_setfam_1(sK1,sK2) = k1_setfam_1(sK2)
    | sK2 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2226,c_1722])).

cnf(c_16,negated_conjecture,
    ( ~ r1_tarski(k8_setfam_1(sK1,sK3),k8_setfam_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_773,plain,
    ( r1_tarski(k8_setfam_1(sK1,sK3),k8_setfam_1(sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2646,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(k8_setfam_1(sK1,sK3),k1_setfam_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2235,c_773])).

cnf(c_2756,plain,
    ( sK2 = k1_xboole_0
    | sK3 = k1_xboole_0
    | r1_tarski(k1_setfam_1(sK3),k1_setfam_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2240,c_2646])).

cnf(c_17,negated_conjecture,
    ( r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_390,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1036,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_390])).

cnf(c_391,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1038,plain,
    ( X0 != X1
    | sK2 != X1
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_391])).

cnf(c_1273,plain,
    ( X0 != sK2
    | sK2 = X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1038])).

cnf(c_1274,plain,
    ( sK2 != sK2
    | sK2 = k1_xboole_0
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_1273])).

cnf(c_15,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1465,plain,
    ( r1_tarski(k1_setfam_1(X0),k1_setfam_1(sK2))
    | ~ r1_tarski(sK2,X0)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_2377,plain,
    ( r1_tarski(k1_setfam_1(sK3),k1_setfam_1(sK2))
    | ~ r1_tarski(sK2,sK3)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_1465])).

cnf(c_2780,plain,
    ( ~ r1_tarski(k1_setfam_1(sK3),k1_setfam_1(sK2))
    | sK2 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2756])).

cnf(c_3365,plain,
    ( sK3 = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2756,c_17,c_1036,c_1274,c_2377,c_2780])).

cnf(c_3366,plain,
    ( sK2 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_3365])).

cnf(c_3379,plain,
    ( sK3 = k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3366,c_770])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | m1_subset_1(k8_setfam_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_778,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | m1_subset_1(k8_setfam_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_775,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1738,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | r1_tarski(k8_setfam_1(X1,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_778,c_775])).

cnf(c_2265,plain,
    ( r1_tarski(k8_setfam_1(sK1,sK3),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_771,c_1738])).

cnf(c_3378,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(k8_setfam_1(sK1,sK3),k8_setfam_1(sK1,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3366,c_773])).

cnf(c_9,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
    | k8_setfam_1(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_780,plain,
    ( k8_setfam_1(X0,k1_xboole_0) = X0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_13,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_882,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
    | ~ r1_tarski(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_953,plain,
    ( r1_tarski(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1668,plain,
    ( k8_setfam_1(X0,k1_xboole_0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_780,c_9,c_882,c_953])).

cnf(c_3389,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(k8_setfam_1(sK1,sK3),sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3378,c_1668])).

cnf(c_3479,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3379,c_2265,c_3389])).

cnf(c_772,plain,
    ( r1_tarski(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_141,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_13])).

cnf(c_142,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_141])).

cnf(c_170,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_8,c_142])).

cnf(c_769,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_170])).

cnf(c_1083,plain,
    ( v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_772,c_769])).

cnf(c_3488,plain,
    ( v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3479,c_1083])).

cnf(c_4,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_235,plain,
    ( v1_xboole_0(X0)
    | k2_zfmisc_1(X1,X2) != X0
    | sK0(X0) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_7])).

cnf(c_236,plain,
    ( v1_xboole_0(k2_zfmisc_1(X0,X1))
    | sK0(k2_zfmisc_1(X0,X1)) != X0 ),
    inference(unflattening,[status(thm)],[c_235])).

cnf(c_768,plain,
    ( sK0(k2_zfmisc_1(X0,X1)) != X0
    | v1_xboole_0(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_236])).

cnf(c_1569,plain,
    ( sK0(k1_xboole_0) != X0
    | v1_xboole_0(k2_zfmisc_1(X0,k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_768])).

cnf(c_1578,plain,
    ( sK0(k1_xboole_0) != X0
    | v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1569,c_4])).

cnf(c_1665,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1578])).

cnf(c_3832,plain,
    ( v1_xboole_0(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3488,c_1665])).

cnf(c_2,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_782,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3839,plain,
    ( sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3832,c_782])).

cnf(c_3490,plain,
    ( r1_tarski(k8_setfam_1(sK1,k1_xboole_0),k8_setfam_1(sK1,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3479,c_773])).

cnf(c_3498,plain,
    ( r1_tarski(sK1,k8_setfam_1(sK1,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3490,c_1668])).

cnf(c_3889,plain,
    ( r1_tarski(sK1,k8_setfam_1(sK1,k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3839,c_3498])).

cnf(c_3899,plain,
    ( r1_tarski(sK1,sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3889,c_1668])).

cnf(c_1737,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1668,c_778])).

cnf(c_883,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) = iProver_top
    | r1_tarski(k1_xboole_0,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_882])).

cnf(c_954,plain,
    ( r1_tarski(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_953])).

cnf(c_2085,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1737,c_883,c_954])).

cnf(c_2092,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2085,c_775])).

cnf(c_4429,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3899,c_2092])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:20:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.33/1.06  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.33/1.06  
% 2.33/1.06  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.33/1.06  
% 2.33/1.06  ------  iProver source info
% 2.33/1.06  
% 2.33/1.06  git: date: 2020-06-30 10:37:57 +0100
% 2.33/1.06  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.33/1.06  git: non_committed_changes: false
% 2.33/1.06  git: last_make_outside_of_git: false
% 2.33/1.06  
% 2.33/1.06  ------ 
% 2.33/1.06  
% 2.33/1.06  ------ Input Options
% 2.33/1.06  
% 2.33/1.06  --out_options                           all
% 2.33/1.06  --tptp_safe_out                         true
% 2.33/1.06  --problem_path                          ""
% 2.33/1.06  --include_path                          ""
% 2.33/1.06  --clausifier                            res/vclausify_rel
% 2.33/1.06  --clausifier_options                    --mode clausify
% 2.33/1.06  --stdin                                 false
% 2.33/1.06  --stats_out                             all
% 2.33/1.06  
% 2.33/1.06  ------ General Options
% 2.33/1.06  
% 2.33/1.06  --fof                                   false
% 2.33/1.06  --time_out_real                         305.
% 2.33/1.06  --time_out_virtual                      -1.
% 2.33/1.06  --symbol_type_check                     false
% 2.33/1.06  --clausify_out                          false
% 2.33/1.06  --sig_cnt_out                           false
% 2.33/1.06  --trig_cnt_out                          false
% 2.33/1.06  --trig_cnt_out_tolerance                1.
% 2.33/1.06  --trig_cnt_out_sk_spl                   false
% 2.33/1.06  --abstr_cl_out                          false
% 2.33/1.06  
% 2.33/1.06  ------ Global Options
% 2.33/1.06  
% 2.33/1.06  --schedule                              default
% 2.33/1.06  --add_important_lit                     false
% 2.33/1.06  --prop_solver_per_cl                    1000
% 2.33/1.06  --min_unsat_core                        false
% 2.33/1.06  --soft_assumptions                      false
% 2.33/1.06  --soft_lemma_size                       3
% 2.33/1.06  --prop_impl_unit_size                   0
% 2.33/1.06  --prop_impl_unit                        []
% 2.33/1.06  --share_sel_clauses                     true
% 2.33/1.06  --reset_solvers                         false
% 2.33/1.06  --bc_imp_inh                            [conj_cone]
% 2.33/1.06  --conj_cone_tolerance                   3.
% 2.33/1.06  --extra_neg_conj                        none
% 2.33/1.06  --large_theory_mode                     true
% 2.33/1.06  --prolific_symb_bound                   200
% 2.33/1.06  --lt_threshold                          2000
% 2.33/1.06  --clause_weak_htbl                      true
% 2.33/1.06  --gc_record_bc_elim                     false
% 2.33/1.06  
% 2.33/1.06  ------ Preprocessing Options
% 2.33/1.06  
% 2.33/1.06  --preprocessing_flag                    true
% 2.33/1.06  --time_out_prep_mult                    0.1
% 2.33/1.06  --splitting_mode                        input
% 2.33/1.06  --splitting_grd                         true
% 2.33/1.06  --splitting_cvd                         false
% 2.33/1.06  --splitting_cvd_svl                     false
% 2.33/1.06  --splitting_nvd                         32
% 2.33/1.06  --sub_typing                            true
% 2.33/1.06  --prep_gs_sim                           true
% 2.33/1.06  --prep_unflatten                        true
% 2.33/1.06  --prep_res_sim                          true
% 2.33/1.06  --prep_upred                            true
% 2.33/1.06  --prep_sem_filter                       exhaustive
% 2.33/1.06  --prep_sem_filter_out                   false
% 2.33/1.06  --pred_elim                             true
% 2.33/1.06  --res_sim_input                         true
% 2.33/1.06  --eq_ax_congr_red                       true
% 2.33/1.06  --pure_diseq_elim                       true
% 2.33/1.06  --brand_transform                       false
% 2.33/1.06  --non_eq_to_eq                          false
% 2.33/1.06  --prep_def_merge                        true
% 2.33/1.06  --prep_def_merge_prop_impl              false
% 2.33/1.06  --prep_def_merge_mbd                    true
% 2.33/1.06  --prep_def_merge_tr_red                 false
% 2.33/1.06  --prep_def_merge_tr_cl                  false
% 2.33/1.06  --smt_preprocessing                     true
% 2.33/1.06  --smt_ac_axioms                         fast
% 2.33/1.06  --preprocessed_out                      false
% 2.33/1.06  --preprocessed_stats                    false
% 2.33/1.06  
% 2.33/1.06  ------ Abstraction refinement Options
% 2.33/1.06  
% 2.33/1.06  --abstr_ref                             []
% 2.33/1.06  --abstr_ref_prep                        false
% 2.33/1.06  --abstr_ref_until_sat                   false
% 2.33/1.06  --abstr_ref_sig_restrict                funpre
% 2.33/1.06  --abstr_ref_af_restrict_to_split_sk     false
% 2.33/1.06  --abstr_ref_under                       []
% 2.33/1.06  
% 2.33/1.06  ------ SAT Options
% 2.33/1.06  
% 2.33/1.06  --sat_mode                              false
% 2.33/1.06  --sat_fm_restart_options                ""
% 2.33/1.06  --sat_gr_def                            false
% 2.33/1.06  --sat_epr_types                         true
% 2.33/1.06  --sat_non_cyclic_types                  false
% 2.33/1.06  --sat_finite_models                     false
% 2.33/1.06  --sat_fm_lemmas                         false
% 2.33/1.06  --sat_fm_prep                           false
% 2.33/1.06  --sat_fm_uc_incr                        true
% 2.33/1.06  --sat_out_model                         small
% 2.33/1.06  --sat_out_clauses                       false
% 2.33/1.06  
% 2.33/1.06  ------ QBF Options
% 2.33/1.06  
% 2.33/1.06  --qbf_mode                              false
% 2.33/1.06  --qbf_elim_univ                         false
% 2.33/1.06  --qbf_dom_inst                          none
% 2.33/1.06  --qbf_dom_pre_inst                      false
% 2.33/1.06  --qbf_sk_in                             false
% 2.33/1.06  --qbf_pred_elim                         true
% 2.33/1.06  --qbf_split                             512
% 2.33/1.06  
% 2.33/1.06  ------ BMC1 Options
% 2.33/1.06  
% 2.33/1.06  --bmc1_incremental                      false
% 2.33/1.06  --bmc1_axioms                           reachable_all
% 2.33/1.06  --bmc1_min_bound                        0
% 2.33/1.06  --bmc1_max_bound                        -1
% 2.33/1.06  --bmc1_max_bound_default                -1
% 2.33/1.06  --bmc1_symbol_reachability              true
% 2.33/1.06  --bmc1_property_lemmas                  false
% 2.33/1.06  --bmc1_k_induction                      false
% 2.33/1.06  --bmc1_non_equiv_states                 false
% 2.33/1.06  --bmc1_deadlock                         false
% 2.33/1.06  --bmc1_ucm                              false
% 2.33/1.06  --bmc1_add_unsat_core                   none
% 2.33/1.06  --bmc1_unsat_core_children              false
% 2.33/1.06  --bmc1_unsat_core_extrapolate_axioms    false
% 2.33/1.06  --bmc1_out_stat                         full
% 2.33/1.06  --bmc1_ground_init                      false
% 2.33/1.06  --bmc1_pre_inst_next_state              false
% 2.33/1.06  --bmc1_pre_inst_state                   false
% 2.33/1.06  --bmc1_pre_inst_reach_state             false
% 2.33/1.06  --bmc1_out_unsat_core                   false
% 2.33/1.06  --bmc1_aig_witness_out                  false
% 2.33/1.06  --bmc1_verbose                          false
% 2.33/1.06  --bmc1_dump_clauses_tptp                false
% 2.33/1.06  --bmc1_dump_unsat_core_tptp             false
% 2.33/1.06  --bmc1_dump_file                        -
% 2.33/1.06  --bmc1_ucm_expand_uc_limit              128
% 2.33/1.06  --bmc1_ucm_n_expand_iterations          6
% 2.33/1.06  --bmc1_ucm_extend_mode                  1
% 2.33/1.06  --bmc1_ucm_init_mode                    2
% 2.33/1.06  --bmc1_ucm_cone_mode                    none
% 2.33/1.06  --bmc1_ucm_reduced_relation_type        0
% 2.33/1.06  --bmc1_ucm_relax_model                  4
% 2.33/1.06  --bmc1_ucm_full_tr_after_sat            true
% 2.33/1.06  --bmc1_ucm_expand_neg_assumptions       false
% 2.33/1.06  --bmc1_ucm_layered_model                none
% 2.33/1.06  --bmc1_ucm_max_lemma_size               10
% 2.33/1.06  
% 2.33/1.06  ------ AIG Options
% 2.33/1.06  
% 2.33/1.06  --aig_mode                              false
% 2.33/1.06  
% 2.33/1.06  ------ Instantiation Options
% 2.33/1.06  
% 2.33/1.06  --instantiation_flag                    true
% 2.33/1.06  --inst_sos_flag                         false
% 2.33/1.06  --inst_sos_phase                        true
% 2.33/1.06  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.33/1.06  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.33/1.06  --inst_lit_sel_side                     num_symb
% 2.33/1.06  --inst_solver_per_active                1400
% 2.33/1.06  --inst_solver_calls_frac                1.
% 2.33/1.06  --inst_passive_queue_type               priority_queues
% 2.33/1.06  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.33/1.06  --inst_passive_queues_freq              [25;2]
% 2.33/1.06  --inst_dismatching                      true
% 2.33/1.06  --inst_eager_unprocessed_to_passive     true
% 2.33/1.06  --inst_prop_sim_given                   true
% 2.33/1.06  --inst_prop_sim_new                     false
% 2.33/1.06  --inst_subs_new                         false
% 2.33/1.06  --inst_eq_res_simp                      false
% 2.33/1.06  --inst_subs_given                       false
% 2.33/1.06  --inst_orphan_elimination               true
% 2.33/1.06  --inst_learning_loop_flag               true
% 2.33/1.06  --inst_learning_start                   3000
% 2.33/1.06  --inst_learning_factor                  2
% 2.33/1.06  --inst_start_prop_sim_after_learn       3
% 2.33/1.06  --inst_sel_renew                        solver
% 2.33/1.06  --inst_lit_activity_flag                true
% 2.33/1.06  --inst_restr_to_given                   false
% 2.33/1.06  --inst_activity_threshold               500
% 2.33/1.06  --inst_out_proof                        true
% 2.33/1.06  
% 2.33/1.06  ------ Resolution Options
% 2.33/1.06  
% 2.33/1.06  --resolution_flag                       true
% 2.33/1.06  --res_lit_sel                           adaptive
% 2.33/1.06  --res_lit_sel_side                      none
% 2.33/1.06  --res_ordering                          kbo
% 2.33/1.06  --res_to_prop_solver                    active
% 2.33/1.06  --res_prop_simpl_new                    false
% 2.33/1.06  --res_prop_simpl_given                  true
% 2.33/1.06  --res_passive_queue_type                priority_queues
% 2.33/1.06  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.33/1.06  --res_passive_queues_freq               [15;5]
% 2.33/1.06  --res_forward_subs                      full
% 2.33/1.06  --res_backward_subs                     full
% 2.33/1.06  --res_forward_subs_resolution           true
% 2.33/1.06  --res_backward_subs_resolution          true
% 2.33/1.06  --res_orphan_elimination                true
% 2.33/1.06  --res_time_limit                        2.
% 2.33/1.06  --res_out_proof                         true
% 2.33/1.06  
% 2.33/1.06  ------ Superposition Options
% 2.33/1.06  
% 2.33/1.06  --superposition_flag                    true
% 2.33/1.06  --sup_passive_queue_type                priority_queues
% 2.33/1.06  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.33/1.06  --sup_passive_queues_freq               [8;1;4]
% 2.33/1.06  --demod_completeness_check              fast
% 2.33/1.06  --demod_use_ground                      true
% 2.33/1.06  --sup_to_prop_solver                    passive
% 2.33/1.06  --sup_prop_simpl_new                    true
% 2.33/1.06  --sup_prop_simpl_given                  true
% 2.33/1.06  --sup_fun_splitting                     false
% 2.33/1.06  --sup_smt_interval                      50000
% 2.33/1.06  
% 2.33/1.06  ------ Superposition Simplification Setup
% 2.33/1.06  
% 2.33/1.06  --sup_indices_passive                   []
% 2.33/1.06  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/1.06  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/1.06  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/1.06  --sup_full_triv                         [TrivRules;PropSubs]
% 2.33/1.06  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/1.06  --sup_full_bw                           [BwDemod]
% 2.33/1.06  --sup_immed_triv                        [TrivRules]
% 2.33/1.06  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.33/1.06  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/1.06  --sup_immed_bw_main                     []
% 2.33/1.06  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.33/1.06  --sup_input_triv                        [Unflattening;TrivRules]
% 2.33/1.06  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/1.06  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.33/1.06  
% 2.33/1.06  ------ Combination Options
% 2.33/1.06  
% 2.33/1.06  --comb_res_mult                         3
% 2.33/1.06  --comb_sup_mult                         2
% 2.33/1.06  --comb_inst_mult                        10
% 2.33/1.06  
% 2.33/1.06  ------ Debug Options
% 2.33/1.06  
% 2.33/1.06  --dbg_backtrace                         false
% 2.33/1.06  --dbg_dump_prop_clauses                 false
% 2.33/1.06  --dbg_dump_prop_clauses_file            -
% 2.33/1.06  --dbg_out_stat                          false
% 2.33/1.06  ------ Parsing...
% 2.33/1.06  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.33/1.06  
% 2.33/1.06  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.33/1.06  
% 2.33/1.06  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.33/1.06  
% 2.33/1.06  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.33/1.06  ------ Proving...
% 2.33/1.06  ------ Problem Properties 
% 2.33/1.06  
% 2.33/1.06  
% 2.33/1.06  clauses                                 18
% 2.33/1.06  conjectures                             4
% 2.33/1.06  EPR                                     4
% 2.33/1.06  Horn                                    15
% 2.33/1.06  unary                                   7
% 2.33/1.06  binary                                  7
% 2.33/1.06  lits                                    33
% 2.33/1.06  lits eq                                 12
% 2.33/1.06  fd_pure                                 0
% 2.33/1.06  fd_pseudo                               0
% 2.33/1.06  fd_cond                                 4
% 2.33/1.06  fd_pseudo_cond                          0
% 2.33/1.06  AC symbols                              0
% 2.33/1.06  
% 2.33/1.06  ------ Schedule dynamic 5 is on 
% 2.33/1.06  
% 2.33/1.06  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.33/1.06  
% 2.33/1.06  
% 2.33/1.06  ------ 
% 2.33/1.06  Current options:
% 2.33/1.06  ------ 
% 2.33/1.06  
% 2.33/1.06  ------ Input Options
% 2.33/1.06  
% 2.33/1.06  --out_options                           all
% 2.33/1.06  --tptp_safe_out                         true
% 2.33/1.06  --problem_path                          ""
% 2.33/1.06  --include_path                          ""
% 2.33/1.06  --clausifier                            res/vclausify_rel
% 2.33/1.06  --clausifier_options                    --mode clausify
% 2.33/1.06  --stdin                                 false
% 2.33/1.06  --stats_out                             all
% 2.33/1.06  
% 2.33/1.06  ------ General Options
% 2.33/1.06  
% 2.33/1.06  --fof                                   false
% 2.33/1.06  --time_out_real                         305.
% 2.33/1.06  --time_out_virtual                      -1.
% 2.33/1.06  --symbol_type_check                     false
% 2.33/1.06  --clausify_out                          false
% 2.33/1.06  --sig_cnt_out                           false
% 2.33/1.06  --trig_cnt_out                          false
% 2.33/1.06  --trig_cnt_out_tolerance                1.
% 2.33/1.06  --trig_cnt_out_sk_spl                   false
% 2.33/1.06  --abstr_cl_out                          false
% 2.33/1.06  
% 2.33/1.06  ------ Global Options
% 2.33/1.06  
% 2.33/1.06  --schedule                              default
% 2.33/1.06  --add_important_lit                     false
% 2.33/1.06  --prop_solver_per_cl                    1000
% 2.33/1.06  --min_unsat_core                        false
% 2.33/1.06  --soft_assumptions                      false
% 2.33/1.06  --soft_lemma_size                       3
% 2.33/1.06  --prop_impl_unit_size                   0
% 2.33/1.06  --prop_impl_unit                        []
% 2.33/1.06  --share_sel_clauses                     true
% 2.33/1.06  --reset_solvers                         false
% 2.33/1.06  --bc_imp_inh                            [conj_cone]
% 2.33/1.06  --conj_cone_tolerance                   3.
% 2.33/1.06  --extra_neg_conj                        none
% 2.33/1.06  --large_theory_mode                     true
% 2.33/1.06  --prolific_symb_bound                   200
% 2.33/1.06  --lt_threshold                          2000
% 2.33/1.06  --clause_weak_htbl                      true
% 2.33/1.06  --gc_record_bc_elim                     false
% 2.33/1.06  
% 2.33/1.06  ------ Preprocessing Options
% 2.33/1.06  
% 2.33/1.06  --preprocessing_flag                    true
% 2.33/1.06  --time_out_prep_mult                    0.1
% 2.33/1.06  --splitting_mode                        input
% 2.33/1.06  --splitting_grd                         true
% 2.33/1.06  --splitting_cvd                         false
% 2.33/1.06  --splitting_cvd_svl                     false
% 2.33/1.06  --splitting_nvd                         32
% 2.33/1.06  --sub_typing                            true
% 2.33/1.06  --prep_gs_sim                           true
% 2.33/1.06  --prep_unflatten                        true
% 2.33/1.06  --prep_res_sim                          true
% 2.33/1.06  --prep_upred                            true
% 2.33/1.06  --prep_sem_filter                       exhaustive
% 2.33/1.06  --prep_sem_filter_out                   false
% 2.33/1.06  --pred_elim                             true
% 2.33/1.06  --res_sim_input                         true
% 2.33/1.06  --eq_ax_congr_red                       true
% 2.33/1.06  --pure_diseq_elim                       true
% 2.33/1.06  --brand_transform                       false
% 2.33/1.06  --non_eq_to_eq                          false
% 2.33/1.06  --prep_def_merge                        true
% 2.33/1.06  --prep_def_merge_prop_impl              false
% 2.33/1.06  --prep_def_merge_mbd                    true
% 2.33/1.06  --prep_def_merge_tr_red                 false
% 2.33/1.06  --prep_def_merge_tr_cl                  false
% 2.33/1.06  --smt_preprocessing                     true
% 2.33/1.06  --smt_ac_axioms                         fast
% 2.33/1.06  --preprocessed_out                      false
% 2.33/1.06  --preprocessed_stats                    false
% 2.33/1.06  
% 2.33/1.06  ------ Abstraction refinement Options
% 2.33/1.06  
% 2.33/1.06  --abstr_ref                             []
% 2.33/1.06  --abstr_ref_prep                        false
% 2.33/1.06  --abstr_ref_until_sat                   false
% 2.33/1.06  --abstr_ref_sig_restrict                funpre
% 2.33/1.06  --abstr_ref_af_restrict_to_split_sk     false
% 2.33/1.06  --abstr_ref_under                       []
% 2.33/1.06  
% 2.33/1.06  ------ SAT Options
% 2.33/1.06  
% 2.33/1.06  --sat_mode                              false
% 2.33/1.06  --sat_fm_restart_options                ""
% 2.33/1.06  --sat_gr_def                            false
% 2.33/1.06  --sat_epr_types                         true
% 2.33/1.06  --sat_non_cyclic_types                  false
% 2.33/1.06  --sat_finite_models                     false
% 2.33/1.06  --sat_fm_lemmas                         false
% 2.33/1.06  --sat_fm_prep                           false
% 2.33/1.06  --sat_fm_uc_incr                        true
% 2.33/1.06  --sat_out_model                         small
% 2.33/1.06  --sat_out_clauses                       false
% 2.33/1.06  
% 2.33/1.06  ------ QBF Options
% 2.33/1.06  
% 2.33/1.06  --qbf_mode                              false
% 2.33/1.06  --qbf_elim_univ                         false
% 2.33/1.06  --qbf_dom_inst                          none
% 2.33/1.06  --qbf_dom_pre_inst                      false
% 2.33/1.06  --qbf_sk_in                             false
% 2.33/1.06  --qbf_pred_elim                         true
% 2.33/1.06  --qbf_split                             512
% 2.33/1.06  
% 2.33/1.06  ------ BMC1 Options
% 2.33/1.06  
% 2.33/1.06  --bmc1_incremental                      false
% 2.33/1.06  --bmc1_axioms                           reachable_all
% 2.33/1.06  --bmc1_min_bound                        0
% 2.33/1.06  --bmc1_max_bound                        -1
% 2.33/1.06  --bmc1_max_bound_default                -1
% 2.33/1.06  --bmc1_symbol_reachability              true
% 2.33/1.06  --bmc1_property_lemmas                  false
% 2.33/1.06  --bmc1_k_induction                      false
% 2.33/1.06  --bmc1_non_equiv_states                 false
% 2.33/1.06  --bmc1_deadlock                         false
% 2.33/1.06  --bmc1_ucm                              false
% 2.33/1.06  --bmc1_add_unsat_core                   none
% 2.33/1.06  --bmc1_unsat_core_children              false
% 2.33/1.06  --bmc1_unsat_core_extrapolate_axioms    false
% 2.33/1.06  --bmc1_out_stat                         full
% 2.33/1.06  --bmc1_ground_init                      false
% 2.33/1.06  --bmc1_pre_inst_next_state              false
% 2.33/1.06  --bmc1_pre_inst_state                   false
% 2.33/1.06  --bmc1_pre_inst_reach_state             false
% 2.33/1.06  --bmc1_out_unsat_core                   false
% 2.33/1.06  --bmc1_aig_witness_out                  false
% 2.33/1.06  --bmc1_verbose                          false
% 2.33/1.06  --bmc1_dump_clauses_tptp                false
% 2.33/1.06  --bmc1_dump_unsat_core_tptp             false
% 2.33/1.06  --bmc1_dump_file                        -
% 2.33/1.06  --bmc1_ucm_expand_uc_limit              128
% 2.33/1.06  --bmc1_ucm_n_expand_iterations          6
% 2.33/1.06  --bmc1_ucm_extend_mode                  1
% 2.33/1.06  --bmc1_ucm_init_mode                    2
% 2.33/1.06  --bmc1_ucm_cone_mode                    none
% 2.33/1.06  --bmc1_ucm_reduced_relation_type        0
% 2.33/1.06  --bmc1_ucm_relax_model                  4
% 2.33/1.06  --bmc1_ucm_full_tr_after_sat            true
% 2.33/1.06  --bmc1_ucm_expand_neg_assumptions       false
% 2.33/1.06  --bmc1_ucm_layered_model                none
% 2.33/1.06  --bmc1_ucm_max_lemma_size               10
% 2.33/1.06  
% 2.33/1.06  ------ AIG Options
% 2.33/1.06  
% 2.33/1.06  --aig_mode                              false
% 2.33/1.06  
% 2.33/1.06  ------ Instantiation Options
% 2.33/1.06  
% 2.33/1.06  --instantiation_flag                    true
% 2.33/1.06  --inst_sos_flag                         false
% 2.33/1.06  --inst_sos_phase                        true
% 2.33/1.06  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.33/1.06  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.33/1.06  --inst_lit_sel_side                     none
% 2.33/1.06  --inst_solver_per_active                1400
% 2.33/1.06  --inst_solver_calls_frac                1.
% 2.33/1.06  --inst_passive_queue_type               priority_queues
% 2.33/1.06  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.33/1.06  --inst_passive_queues_freq              [25;2]
% 2.33/1.06  --inst_dismatching                      true
% 2.33/1.06  --inst_eager_unprocessed_to_passive     true
% 2.33/1.06  --inst_prop_sim_given                   true
% 2.33/1.06  --inst_prop_sim_new                     false
% 2.33/1.06  --inst_subs_new                         false
% 2.33/1.06  --inst_eq_res_simp                      false
% 2.33/1.06  --inst_subs_given                       false
% 2.33/1.06  --inst_orphan_elimination               true
% 2.33/1.06  --inst_learning_loop_flag               true
% 2.33/1.06  --inst_learning_start                   3000
% 2.33/1.06  --inst_learning_factor                  2
% 2.33/1.06  --inst_start_prop_sim_after_learn       3
% 2.33/1.06  --inst_sel_renew                        solver
% 2.33/1.06  --inst_lit_activity_flag                true
% 2.33/1.06  --inst_restr_to_given                   false
% 2.33/1.06  --inst_activity_threshold               500
% 2.33/1.06  --inst_out_proof                        true
% 2.33/1.06  
% 2.33/1.06  ------ Resolution Options
% 2.33/1.06  
% 2.33/1.06  --resolution_flag                       false
% 2.33/1.06  --res_lit_sel                           adaptive
% 2.33/1.06  --res_lit_sel_side                      none
% 2.33/1.06  --res_ordering                          kbo
% 2.33/1.06  --res_to_prop_solver                    active
% 2.33/1.06  --res_prop_simpl_new                    false
% 2.33/1.06  --res_prop_simpl_given                  true
% 2.33/1.06  --res_passive_queue_type                priority_queues
% 2.33/1.06  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.33/1.06  --res_passive_queues_freq               [15;5]
% 2.33/1.06  --res_forward_subs                      full
% 2.33/1.06  --res_backward_subs                     full
% 2.33/1.06  --res_forward_subs_resolution           true
% 2.33/1.06  --res_backward_subs_resolution          true
% 2.33/1.06  --res_orphan_elimination                true
% 2.33/1.06  --res_time_limit                        2.
% 2.33/1.06  --res_out_proof                         true
% 2.33/1.06  
% 2.33/1.06  ------ Superposition Options
% 2.33/1.06  
% 2.33/1.06  --superposition_flag                    true
% 2.33/1.06  --sup_passive_queue_type                priority_queues
% 2.33/1.06  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.33/1.06  --sup_passive_queues_freq               [8;1;4]
% 2.33/1.06  --demod_completeness_check              fast
% 2.33/1.06  --demod_use_ground                      true
% 2.33/1.06  --sup_to_prop_solver                    passive
% 2.33/1.06  --sup_prop_simpl_new                    true
% 2.33/1.06  --sup_prop_simpl_given                  true
% 2.33/1.06  --sup_fun_splitting                     false
% 2.33/1.06  --sup_smt_interval                      50000
% 2.33/1.06  
% 2.33/1.06  ------ Superposition Simplification Setup
% 2.33/1.06  
% 2.33/1.06  --sup_indices_passive                   []
% 2.33/1.06  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/1.06  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/1.06  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/1.06  --sup_full_triv                         [TrivRules;PropSubs]
% 2.33/1.06  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/1.06  --sup_full_bw                           [BwDemod]
% 2.33/1.06  --sup_immed_triv                        [TrivRules]
% 2.33/1.06  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.33/1.06  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/1.06  --sup_immed_bw_main                     []
% 2.33/1.06  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.33/1.06  --sup_input_triv                        [Unflattening;TrivRules]
% 2.33/1.06  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/1.06  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.33/1.06  
% 2.33/1.06  ------ Combination Options
% 2.33/1.06  
% 2.33/1.06  --comb_res_mult                         3
% 2.33/1.06  --comb_sup_mult                         2
% 2.33/1.06  --comb_inst_mult                        10
% 2.33/1.06  
% 2.33/1.06  ------ Debug Options
% 2.33/1.06  
% 2.33/1.06  --dbg_backtrace                         false
% 2.33/1.06  --dbg_dump_prop_clauses                 false
% 2.33/1.06  --dbg_dump_prop_clauses_file            -
% 2.33/1.06  --dbg_out_stat                          false
% 2.33/1.06  
% 2.33/1.06  
% 2.33/1.06  
% 2.33/1.06  
% 2.33/1.06  ------ Proving...
% 2.33/1.06  
% 2.33/1.06  
% 2.33/1.06  % SZS status Theorem for theBenchmark.p
% 2.33/1.06  
% 2.33/1.06   Resolution empty clause
% 2.33/1.06  
% 2.33/1.06  % SZS output start CNFRefutation for theBenchmark.p
% 2.33/1.06  
% 2.33/1.06  fof(f12,conjecture,(
% 2.33/1.06    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 2.33/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/1.06  
% 2.33/1.06  fof(f13,negated_conjecture,(
% 2.33/1.06    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 2.33/1.06    inference(negated_conjecture,[],[f12])).
% 2.33/1.06  
% 2.33/1.06  fof(f21,plain,(
% 2.33/1.06    ? [X0,X1] : (? [X2] : ((~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.33/1.06    inference(ennf_transformation,[],[f13])).
% 2.33/1.06  
% 2.33/1.06  fof(f22,plain,(
% 2.33/1.06    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.33/1.06    inference(flattening,[],[f21])).
% 2.33/1.06  
% 2.33/1.06  fof(f31,plain,(
% 2.33/1.06    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (~r1_tarski(k8_setfam_1(X0,sK3),k8_setfam_1(X0,X1)) & r1_tarski(X1,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(X0))))) )),
% 2.33/1.06    introduced(choice_axiom,[])).
% 2.33/1.06  
% 2.33/1.06  fof(f30,plain,(
% 2.33/1.06    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (? [X2] : (~r1_tarski(k8_setfam_1(sK1,X2),k8_setfam_1(sK1,sK2)) & r1_tarski(sK2,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK1)))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))))),
% 2.33/1.06    introduced(choice_axiom,[])).
% 2.33/1.06  
% 2.33/1.06  fof(f32,plain,(
% 2.33/1.06    (~r1_tarski(k8_setfam_1(sK1,sK3),k8_setfam_1(sK1,sK2)) & r1_tarski(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1)))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1)))),
% 2.33/1.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f22,f31,f30])).
% 2.33/1.06  
% 2.33/1.06  fof(f50,plain,(
% 2.33/1.06    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1)))),
% 2.33/1.06    inference(cnf_transformation,[],[f32])).
% 2.33/1.06  
% 2.33/1.06  fof(f7,axiom,(
% 2.33/1.06    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((k1_xboole_0 = X1 => k8_setfam_1(X0,X1) = X0) & (k1_xboole_0 != X1 => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1))))),
% 2.33/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/1.06  
% 2.33/1.06  fof(f16,plain,(
% 2.33/1.06    ! [X0,X1] : (((k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1) & (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.33/1.06    inference(ennf_transformation,[],[f7])).
% 2.33/1.06  
% 2.33/1.06  fof(f42,plain,(
% 2.33/1.06    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.33/1.06    inference(cnf_transformation,[],[f16])).
% 2.33/1.06  
% 2.33/1.06  fof(f9,axiom,(
% 2.33/1.06    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k6_setfam_1(X0,X1) = k1_setfam_1(X1))),
% 2.33/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/1.06  
% 2.33/1.06  fof(f18,plain,(
% 2.33/1.06    ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.33/1.06    inference(ennf_transformation,[],[f9])).
% 2.33/1.06  
% 2.33/1.06  fof(f45,plain,(
% 2.33/1.06    ( ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.33/1.06    inference(cnf_transformation,[],[f18])).
% 2.33/1.06  
% 2.33/1.06  fof(f49,plain,(
% 2.33/1.06    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1)))),
% 2.33/1.06    inference(cnf_transformation,[],[f32])).
% 2.33/1.06  
% 2.33/1.06  fof(f52,plain,(
% 2.33/1.06    ~r1_tarski(k8_setfam_1(sK1,sK3),k8_setfam_1(sK1,sK2))),
% 2.33/1.06    inference(cnf_transformation,[],[f32])).
% 2.33/1.06  
% 2.33/1.06  fof(f51,plain,(
% 2.33/1.06    r1_tarski(sK2,sK3)),
% 2.33/1.06    inference(cnf_transformation,[],[f32])).
% 2.33/1.06  
% 2.33/1.06  fof(f11,axiom,(
% 2.33/1.06    ! [X0,X1] : (r1_tarski(X0,X1) => (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 2.33/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/1.06  
% 2.33/1.06  fof(f19,plain,(
% 2.33/1.06    ! [X0,X1] : ((r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0) | ~r1_tarski(X0,X1))),
% 2.33/1.06    inference(ennf_transformation,[],[f11])).
% 2.33/1.06  
% 2.33/1.06  fof(f20,plain,(
% 2.33/1.06    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1))),
% 2.33/1.06    inference(flattening,[],[f19])).
% 2.33/1.06  
% 2.33/1.06  fof(f48,plain,(
% 2.33/1.06    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1)) )),
% 2.33/1.06    inference(cnf_transformation,[],[f20])).
% 2.33/1.06  
% 2.33/1.06  fof(f8,axiom,(
% 2.33/1.06    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.33/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/1.06  
% 2.33/1.06  fof(f17,plain,(
% 2.33/1.06    ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.33/1.06    inference(ennf_transformation,[],[f8])).
% 2.33/1.06  
% 2.33/1.06  fof(f44,plain,(
% 2.33/1.06    ( ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.33/1.06    inference(cnf_transformation,[],[f17])).
% 2.33/1.06  
% 2.33/1.06  fof(f10,axiom,(
% 2.33/1.06    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.33/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/1.06  
% 2.33/1.06  fof(f29,plain,(
% 2.33/1.06    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.33/1.06    inference(nnf_transformation,[],[f10])).
% 2.33/1.06  
% 2.33/1.06  fof(f46,plain,(
% 2.33/1.06    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.33/1.06    inference(cnf_transformation,[],[f29])).
% 2.33/1.06  
% 2.33/1.06  fof(f43,plain,(
% 2.33/1.06    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.33/1.06    inference(cnf_transformation,[],[f16])).
% 2.33/1.06  
% 2.33/1.06  fof(f55,plain,(
% 2.33/1.06    ( ! [X0] : (k8_setfam_1(X0,k1_xboole_0) = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.33/1.06    inference(equality_resolution,[],[f43])).
% 2.33/1.06  
% 2.33/1.06  fof(f47,plain,(
% 2.33/1.06    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.33/1.06    inference(cnf_transformation,[],[f29])).
% 2.33/1.06  
% 2.33/1.06  fof(f3,axiom,(
% 2.33/1.06    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.33/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/1.06  
% 2.33/1.06  fof(f36,plain,(
% 2.33/1.06    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.33/1.06    inference(cnf_transformation,[],[f3])).
% 2.33/1.06  
% 2.33/1.06  fof(f6,axiom,(
% 2.33/1.06    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 2.33/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/1.06  
% 2.33/1.06  fof(f15,plain,(
% 2.33/1.06    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 2.33/1.06    inference(ennf_transformation,[],[f6])).
% 2.33/1.06  
% 2.33/1.06  fof(f41,plain,(
% 2.33/1.06    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 2.33/1.06    inference(cnf_transformation,[],[f15])).
% 2.33/1.06  
% 2.33/1.06  fof(f4,axiom,(
% 2.33/1.06    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.33/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/1.06  
% 2.33/1.06  fof(f27,plain,(
% 2.33/1.06    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.33/1.06    inference(nnf_transformation,[],[f4])).
% 2.33/1.06  
% 2.33/1.06  fof(f28,plain,(
% 2.33/1.06    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.33/1.06    inference(flattening,[],[f27])).
% 2.33/1.06  
% 2.33/1.06  fof(f39,plain,(
% 2.33/1.06    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 2.33/1.06    inference(cnf_transformation,[],[f28])).
% 2.33/1.06  
% 2.33/1.06  fof(f53,plain,(
% 2.33/1.06    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.33/1.06    inference(equality_resolution,[],[f39])).
% 2.33/1.06  
% 2.33/1.06  fof(f1,axiom,(
% 2.33/1.06    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.33/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/1.06  
% 2.33/1.06  fof(f23,plain,(
% 2.33/1.06    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.33/1.06    inference(nnf_transformation,[],[f1])).
% 2.33/1.06  
% 2.33/1.06  fof(f24,plain,(
% 2.33/1.06    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.33/1.06    inference(rectify,[],[f23])).
% 2.33/1.06  
% 2.33/1.06  fof(f25,plain,(
% 2.33/1.06    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.33/1.06    introduced(choice_axiom,[])).
% 2.33/1.06  
% 2.33/1.06  fof(f26,plain,(
% 2.33/1.06    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.33/1.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).
% 2.33/1.06  
% 2.33/1.06  fof(f34,plain,(
% 2.33/1.06    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 2.33/1.06    inference(cnf_transformation,[],[f26])).
% 2.33/1.06  
% 2.33/1.06  fof(f5,axiom,(
% 2.33/1.06    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 2.33/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/1.06  
% 2.33/1.06  fof(f40,plain,(
% 2.33/1.06    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 2.33/1.06    inference(cnf_transformation,[],[f5])).
% 2.33/1.06  
% 2.33/1.06  fof(f2,axiom,(
% 2.33/1.06    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.33/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/1.06  
% 2.33/1.06  fof(f14,plain,(
% 2.33/1.06    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.33/1.06    inference(ennf_transformation,[],[f2])).
% 2.33/1.06  
% 2.33/1.06  fof(f35,plain,(
% 2.33/1.06    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 2.33/1.06    inference(cnf_transformation,[],[f14])).
% 2.33/1.06  
% 2.33/1.06  cnf(c_18,negated_conjecture,
% 2.33/1.06      ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
% 2.33/1.06      inference(cnf_transformation,[],[f50]) ).
% 2.33/1.06  
% 2.33/1.06  cnf(c_771,plain,
% 2.33/1.06      ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
% 2.33/1.06      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.33/1.06  
% 2.33/1.06  cnf(c_10,plain,
% 2.33/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.33/1.06      | k6_setfam_1(X1,X0) = k8_setfam_1(X1,X0)
% 2.33/1.06      | k1_xboole_0 = X0 ),
% 2.33/1.06      inference(cnf_transformation,[],[f42]) ).
% 2.33/1.06  
% 2.33/1.06  cnf(c_779,plain,
% 2.33/1.06      ( k6_setfam_1(X0,X1) = k8_setfam_1(X0,X1)
% 2.33/1.06      | k1_xboole_0 = X1
% 2.33/1.06      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 2.33/1.06      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.33/1.06  
% 2.33/1.06  cnf(c_2225,plain,
% 2.33/1.06      ( k6_setfam_1(sK1,sK3) = k8_setfam_1(sK1,sK3) | sK3 = k1_xboole_0 ),
% 2.33/1.06      inference(superposition,[status(thm)],[c_771,c_779]) ).
% 2.33/1.06  
% 2.33/1.06  cnf(c_12,plain,
% 2.33/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.33/1.06      | k6_setfam_1(X1,X0) = k1_setfam_1(X0) ),
% 2.33/1.06      inference(cnf_transformation,[],[f45]) ).
% 2.33/1.06  
% 2.33/1.06  cnf(c_777,plain,
% 2.33/1.06      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
% 2.33/1.06      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 2.33/1.06      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.33/1.06  
% 2.33/1.06  cnf(c_1721,plain,
% 2.33/1.06      ( k6_setfam_1(sK1,sK3) = k1_setfam_1(sK3) ),
% 2.33/1.06      inference(superposition,[status(thm)],[c_771,c_777]) ).
% 2.33/1.06  
% 2.33/1.06  cnf(c_2240,plain,
% 2.33/1.06      ( k8_setfam_1(sK1,sK3) = k1_setfam_1(sK3) | sK3 = k1_xboole_0 ),
% 2.33/1.06      inference(light_normalisation,[status(thm)],[c_2225,c_1721]) ).
% 2.33/1.06  
% 2.33/1.06  cnf(c_19,negated_conjecture,
% 2.33/1.06      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
% 2.33/1.06      inference(cnf_transformation,[],[f49]) ).
% 2.33/1.06  
% 2.33/1.06  cnf(c_770,plain,
% 2.33/1.06      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
% 2.33/1.06      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.33/1.06  
% 2.33/1.06  cnf(c_2226,plain,
% 2.33/1.06      ( k6_setfam_1(sK1,sK2) = k8_setfam_1(sK1,sK2) | sK2 = k1_xboole_0 ),
% 2.33/1.06      inference(superposition,[status(thm)],[c_770,c_779]) ).
% 2.33/1.06  
% 2.33/1.06  cnf(c_1722,plain,
% 2.33/1.06      ( k6_setfam_1(sK1,sK2) = k1_setfam_1(sK2) ),
% 2.33/1.06      inference(superposition,[status(thm)],[c_770,c_777]) ).
% 2.33/1.06  
% 2.33/1.06  cnf(c_2235,plain,
% 2.33/1.06      ( k8_setfam_1(sK1,sK2) = k1_setfam_1(sK2) | sK2 = k1_xboole_0 ),
% 2.33/1.06      inference(light_normalisation,[status(thm)],[c_2226,c_1722]) ).
% 2.33/1.06  
% 2.33/1.06  cnf(c_16,negated_conjecture,
% 2.33/1.06      ( ~ r1_tarski(k8_setfam_1(sK1,sK3),k8_setfam_1(sK1,sK2)) ),
% 2.33/1.06      inference(cnf_transformation,[],[f52]) ).
% 2.33/1.06  
% 2.33/1.06  cnf(c_773,plain,
% 2.33/1.06      ( r1_tarski(k8_setfam_1(sK1,sK3),k8_setfam_1(sK1,sK2)) != iProver_top ),
% 2.33/1.06      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.33/1.06  
% 2.33/1.06  cnf(c_2646,plain,
% 2.33/1.06      ( sK2 = k1_xboole_0
% 2.33/1.06      | r1_tarski(k8_setfam_1(sK1,sK3),k1_setfam_1(sK2)) != iProver_top ),
% 2.33/1.06      inference(superposition,[status(thm)],[c_2235,c_773]) ).
% 2.33/1.06  
% 2.33/1.06  cnf(c_2756,plain,
% 2.33/1.06      ( sK2 = k1_xboole_0
% 2.33/1.06      | sK3 = k1_xboole_0
% 2.33/1.06      | r1_tarski(k1_setfam_1(sK3),k1_setfam_1(sK2)) != iProver_top ),
% 2.33/1.06      inference(superposition,[status(thm)],[c_2240,c_2646]) ).
% 2.33/1.06  
% 2.33/1.06  cnf(c_17,negated_conjecture,
% 2.33/1.06      ( r1_tarski(sK2,sK3) ),
% 2.33/1.06      inference(cnf_transformation,[],[f51]) ).
% 2.33/1.06  
% 2.33/1.06  cnf(c_390,plain,( X0 = X0 ),theory(equality) ).
% 2.33/1.06  
% 2.33/1.06  cnf(c_1036,plain,
% 2.33/1.06      ( sK2 = sK2 ),
% 2.33/1.06      inference(instantiation,[status(thm)],[c_390]) ).
% 2.33/1.06  
% 2.33/1.06  cnf(c_391,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.33/1.06  
% 2.33/1.06  cnf(c_1038,plain,
% 2.33/1.06      ( X0 != X1 | sK2 != X1 | sK2 = X0 ),
% 2.33/1.06      inference(instantiation,[status(thm)],[c_391]) ).
% 2.33/1.06  
% 2.33/1.06  cnf(c_1273,plain,
% 2.33/1.06      ( X0 != sK2 | sK2 = X0 | sK2 != sK2 ),
% 2.33/1.06      inference(instantiation,[status(thm)],[c_1038]) ).
% 2.33/1.06  
% 2.33/1.06  cnf(c_1274,plain,
% 2.33/1.06      ( sK2 != sK2 | sK2 = k1_xboole_0 | k1_xboole_0 != sK2 ),
% 2.33/1.06      inference(instantiation,[status(thm)],[c_1273]) ).
% 2.33/1.06  
% 2.33/1.06  cnf(c_15,plain,
% 2.33/1.06      ( ~ r1_tarski(X0,X1)
% 2.33/1.06      | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
% 2.33/1.06      | k1_xboole_0 = X0 ),
% 2.33/1.06      inference(cnf_transformation,[],[f48]) ).
% 2.33/1.06  
% 2.33/1.06  cnf(c_1465,plain,
% 2.33/1.06      ( r1_tarski(k1_setfam_1(X0),k1_setfam_1(sK2))
% 2.33/1.06      | ~ r1_tarski(sK2,X0)
% 2.33/1.06      | k1_xboole_0 = sK2 ),
% 2.33/1.06      inference(instantiation,[status(thm)],[c_15]) ).
% 2.33/1.06  
% 2.33/1.06  cnf(c_2377,plain,
% 2.33/1.06      ( r1_tarski(k1_setfam_1(sK3),k1_setfam_1(sK2))
% 2.33/1.06      | ~ r1_tarski(sK2,sK3)
% 2.33/1.06      | k1_xboole_0 = sK2 ),
% 2.33/1.06      inference(instantiation,[status(thm)],[c_1465]) ).
% 2.33/1.06  
% 2.33/1.06  cnf(c_2780,plain,
% 2.33/1.06      ( ~ r1_tarski(k1_setfam_1(sK3),k1_setfam_1(sK2))
% 2.33/1.06      | sK2 = k1_xboole_0
% 2.33/1.06      | sK3 = k1_xboole_0 ),
% 2.33/1.06      inference(predicate_to_equality_rev,[status(thm)],[c_2756]) ).
% 2.33/1.06  
% 2.33/1.06  cnf(c_3365,plain,
% 2.33/1.06      ( sK3 = k1_xboole_0 | sK2 = k1_xboole_0 ),
% 2.33/1.06      inference(global_propositional_subsumption,
% 2.33/1.06                [status(thm)],
% 2.33/1.06                [c_2756,c_17,c_1036,c_1274,c_2377,c_2780]) ).
% 2.33/1.06  
% 2.33/1.06  cnf(c_3366,plain,
% 2.33/1.06      ( sK2 = k1_xboole_0 | sK3 = k1_xboole_0 ),
% 2.33/1.06      inference(renaming,[status(thm)],[c_3365]) ).
% 2.33/1.06  
% 2.33/1.06  cnf(c_3379,plain,
% 2.33/1.06      ( sK3 = k1_xboole_0
% 2.33/1.06      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
% 2.33/1.06      inference(superposition,[status(thm)],[c_3366,c_770]) ).
% 2.33/1.06  
% 2.33/1.06  cnf(c_11,plain,
% 2.33/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.33/1.06      | m1_subset_1(k8_setfam_1(X1,X0),k1_zfmisc_1(X1)) ),
% 2.33/1.06      inference(cnf_transformation,[],[f44]) ).
% 2.33/1.06  
% 2.33/1.06  cnf(c_778,plain,
% 2.33/1.06      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 2.33/1.06      | m1_subset_1(k8_setfam_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 2.33/1.06      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.33/1.06  
% 2.33/1.06  cnf(c_14,plain,
% 2.33/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.33/1.06      inference(cnf_transformation,[],[f46]) ).
% 2.33/1.06  
% 2.33/1.06  cnf(c_775,plain,
% 2.33/1.06      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.33/1.06      | r1_tarski(X0,X1) = iProver_top ),
% 2.33/1.06      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.33/1.06  
% 2.33/1.06  cnf(c_1738,plain,
% 2.33/1.06      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 2.33/1.06      | r1_tarski(k8_setfam_1(X1,X0),X1) = iProver_top ),
% 2.33/1.06      inference(superposition,[status(thm)],[c_778,c_775]) ).
% 2.33/1.06  
% 2.33/1.06  cnf(c_2265,plain,
% 2.33/1.06      ( r1_tarski(k8_setfam_1(sK1,sK3),sK1) = iProver_top ),
% 2.33/1.06      inference(superposition,[status(thm)],[c_771,c_1738]) ).
% 2.33/1.06  
% 2.33/1.06  cnf(c_3378,plain,
% 2.33/1.06      ( sK3 = k1_xboole_0
% 2.33/1.06      | r1_tarski(k8_setfam_1(sK1,sK3),k8_setfam_1(sK1,k1_xboole_0)) != iProver_top ),
% 2.33/1.06      inference(superposition,[status(thm)],[c_3366,c_773]) ).
% 2.33/1.06  
% 2.33/1.06  cnf(c_9,plain,
% 2.33/1.06      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
% 2.33/1.06      | k8_setfam_1(X0,k1_xboole_0) = X0 ),
% 2.33/1.06      inference(cnf_transformation,[],[f55]) ).
% 2.33/1.06  
% 2.33/1.06  cnf(c_780,plain,
% 2.33/1.06      ( k8_setfam_1(X0,k1_xboole_0) = X0
% 2.33/1.06      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 2.33/1.06      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.33/1.06  
% 2.33/1.06  cnf(c_13,plain,
% 2.33/1.06      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.33/1.06      inference(cnf_transformation,[],[f47]) ).
% 2.33/1.06  
% 2.33/1.06  cnf(c_882,plain,
% 2.33/1.06      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
% 2.33/1.06      | ~ r1_tarski(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.33/1.06      inference(instantiation,[status(thm)],[c_13]) ).
% 2.33/1.06  
% 2.33/1.06  cnf(c_3,plain,
% 2.33/1.06      ( r1_tarski(k1_xboole_0,X0) ),
% 2.33/1.06      inference(cnf_transformation,[],[f36]) ).
% 2.33/1.06  
% 2.33/1.06  cnf(c_953,plain,
% 2.33/1.06      ( r1_tarski(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.33/1.06      inference(instantiation,[status(thm)],[c_3]) ).
% 2.33/1.06  
% 2.33/1.06  cnf(c_1668,plain,
% 2.33/1.06      ( k8_setfam_1(X0,k1_xboole_0) = X0 ),
% 2.33/1.06      inference(global_propositional_subsumption,
% 2.33/1.06                [status(thm)],
% 2.33/1.06                [c_780,c_9,c_882,c_953]) ).
% 2.33/1.06  
% 2.33/1.06  cnf(c_3389,plain,
% 2.33/1.06      ( sK3 = k1_xboole_0
% 2.33/1.06      | r1_tarski(k8_setfam_1(sK1,sK3),sK1) != iProver_top ),
% 2.33/1.06      inference(demodulation,[status(thm)],[c_3378,c_1668]) ).
% 2.33/1.06  
% 2.33/1.06  cnf(c_3479,plain,
% 2.33/1.06      ( sK3 = k1_xboole_0 ),
% 2.33/1.06      inference(global_propositional_subsumption,
% 2.33/1.06                [status(thm)],
% 2.33/1.06                [c_3379,c_2265,c_3389]) ).
% 2.33/1.06  
% 2.33/1.06  cnf(c_772,plain,
% 2.33/1.06      ( r1_tarski(sK2,sK3) = iProver_top ),
% 2.33/1.06      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.33/1.06  
% 2.33/1.06  cnf(c_8,plain,
% 2.33/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.33/1.06      | ~ v1_xboole_0(X1)
% 2.33/1.06      | v1_xboole_0(X0) ),
% 2.33/1.06      inference(cnf_transformation,[],[f41]) ).
% 2.33/1.06  
% 2.33/1.06  cnf(c_141,plain,
% 2.33/1.06      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.33/1.06      inference(prop_impl,[status(thm)],[c_13]) ).
% 2.33/1.06  
% 2.33/1.06  cnf(c_142,plain,
% 2.33/1.06      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.33/1.06      inference(renaming,[status(thm)],[c_141]) ).
% 2.33/1.06  
% 2.33/1.06  cnf(c_170,plain,
% 2.33/1.06      ( ~ r1_tarski(X0,X1) | ~ v1_xboole_0(X1) | v1_xboole_0(X0) ),
% 2.33/1.06      inference(bin_hyper_res,[status(thm)],[c_8,c_142]) ).
% 2.33/1.06  
% 2.33/1.06  cnf(c_769,plain,
% 2.33/1.06      ( r1_tarski(X0,X1) != iProver_top
% 2.33/1.06      | v1_xboole_0(X1) != iProver_top
% 2.33/1.06      | v1_xboole_0(X0) = iProver_top ),
% 2.33/1.06      inference(predicate_to_equality,[status(thm)],[c_170]) ).
% 2.33/1.06  
% 2.33/1.06  cnf(c_1083,plain,
% 2.33/1.06      ( v1_xboole_0(sK2) = iProver_top | v1_xboole_0(sK3) != iProver_top ),
% 2.33/1.06      inference(superposition,[status(thm)],[c_772,c_769]) ).
% 2.33/1.06  
% 2.33/1.06  cnf(c_3488,plain,
% 2.33/1.06      ( v1_xboole_0(sK2) = iProver_top
% 2.33/1.06      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.33/1.06      inference(demodulation,[status(thm)],[c_3479,c_1083]) ).
% 2.33/1.06  
% 2.33/1.06  cnf(c_4,plain,
% 2.33/1.06      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 2.33/1.06      inference(cnf_transformation,[],[f53]) ).
% 2.33/1.06  
% 2.33/1.06  cnf(c_0,plain,
% 2.33/1.06      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 2.33/1.06      inference(cnf_transformation,[],[f34]) ).
% 2.33/1.06  
% 2.33/1.06  cnf(c_7,plain,
% 2.33/1.06      ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
% 2.33/1.06      inference(cnf_transformation,[],[f40]) ).
% 2.33/1.06  
% 2.33/1.06  cnf(c_235,plain,
% 2.33/1.06      ( v1_xboole_0(X0) | k2_zfmisc_1(X1,X2) != X0 | sK0(X0) != X1 ),
% 2.33/1.06      inference(resolution_lifted,[status(thm)],[c_0,c_7]) ).
% 2.33/1.06  
% 2.33/1.06  cnf(c_236,plain,
% 2.33/1.06      ( v1_xboole_0(k2_zfmisc_1(X0,X1)) | sK0(k2_zfmisc_1(X0,X1)) != X0 ),
% 2.33/1.06      inference(unflattening,[status(thm)],[c_235]) ).
% 2.33/1.06  
% 2.33/1.06  cnf(c_768,plain,
% 2.33/1.06      ( sK0(k2_zfmisc_1(X0,X1)) != X0
% 2.33/1.06      | v1_xboole_0(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 2.33/1.06      inference(predicate_to_equality,[status(thm)],[c_236]) ).
% 2.33/1.06  
% 2.33/1.06  cnf(c_1569,plain,
% 2.33/1.06      ( sK0(k1_xboole_0) != X0
% 2.33/1.06      | v1_xboole_0(k2_zfmisc_1(X0,k1_xboole_0)) = iProver_top ),
% 2.33/1.06      inference(superposition,[status(thm)],[c_4,c_768]) ).
% 2.33/1.06  
% 2.33/1.06  cnf(c_1578,plain,
% 2.33/1.06      ( sK0(k1_xboole_0) != X0 | v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.33/1.06      inference(light_normalisation,[status(thm)],[c_1569,c_4]) ).
% 2.33/1.06  
% 2.33/1.06  cnf(c_1665,plain,
% 2.33/1.06      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.33/1.06      inference(equality_resolution,[status(thm)],[c_1578]) ).
% 2.33/1.06  
% 2.33/1.06  cnf(c_3832,plain,
% 2.33/1.06      ( v1_xboole_0(sK2) = iProver_top ),
% 2.33/1.06      inference(global_propositional_subsumption,[status(thm)],[c_3488,c_1665]) ).
% 2.33/1.06  
% 2.33/1.06  cnf(c_2,plain,
% 2.33/1.06      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 2.33/1.06      inference(cnf_transformation,[],[f35]) ).
% 2.33/1.06  
% 2.33/1.06  cnf(c_782,plain,
% 2.33/1.06      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 2.33/1.06      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.33/1.06  
% 2.33/1.06  cnf(c_3839,plain,
% 2.33/1.06      ( sK2 = k1_xboole_0 ),
% 2.33/1.06      inference(superposition,[status(thm)],[c_3832,c_782]) ).
% 2.33/1.06  
% 2.33/1.06  cnf(c_3490,plain,
% 2.33/1.06      ( r1_tarski(k8_setfam_1(sK1,k1_xboole_0),k8_setfam_1(sK1,sK2)) != iProver_top ),
% 2.33/1.06      inference(demodulation,[status(thm)],[c_3479,c_773]) ).
% 2.33/1.06  
% 2.33/1.06  cnf(c_3498,plain,
% 2.33/1.06      ( r1_tarski(sK1,k8_setfam_1(sK1,sK2)) != iProver_top ),
% 2.33/1.06      inference(demodulation,[status(thm)],[c_3490,c_1668]) ).
% 2.33/1.06  
% 2.33/1.06  cnf(c_3889,plain,
% 2.33/1.06      ( r1_tarski(sK1,k8_setfam_1(sK1,k1_xboole_0)) != iProver_top ),
% 2.33/1.06      inference(demodulation,[status(thm)],[c_3839,c_3498]) ).
% 2.33/1.06  
% 2.33/1.06  cnf(c_3899,plain,
% 2.33/1.06      ( r1_tarski(sK1,sK1) != iProver_top ),
% 2.33/1.06      inference(demodulation,[status(thm)],[c_3889,c_1668]) ).
% 2.33/1.06  
% 2.33/1.06  cnf(c_1737,plain,
% 2.33/1.06      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top
% 2.33/1.06      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 2.33/1.06      inference(superposition,[status(thm)],[c_1668,c_778]) ).
% 2.33/1.06  
% 2.33/1.06  cnf(c_883,plain,
% 2.33/1.06      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) = iProver_top
% 2.33/1.06      | r1_tarski(k1_xboole_0,k1_zfmisc_1(X0)) != iProver_top ),
% 2.33/1.06      inference(predicate_to_equality,[status(thm)],[c_882]) ).
% 2.33/1.06  
% 2.33/1.06  cnf(c_954,plain,
% 2.33/1.06      ( r1_tarski(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.33/1.06      inference(predicate_to_equality,[status(thm)],[c_953]) ).
% 2.33/1.06  
% 2.33/1.06  cnf(c_2085,plain,
% 2.33/1.06      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.33/1.06      inference(global_propositional_subsumption,
% 2.33/1.06                [status(thm)],
% 2.33/1.06                [c_1737,c_883,c_954]) ).
% 2.33/1.06  
% 2.33/1.06  cnf(c_2092,plain,
% 2.33/1.06      ( r1_tarski(X0,X0) = iProver_top ),
% 2.33/1.06      inference(superposition,[status(thm)],[c_2085,c_775]) ).
% 2.33/1.06  
% 2.33/1.06  cnf(c_4429,plain,
% 2.33/1.06      ( $false ),
% 2.33/1.06      inference(forward_subsumption_resolution,[status(thm)],[c_3899,c_2092]) ).
% 2.33/1.06  
% 2.33/1.06  
% 2.33/1.06  % SZS output end CNFRefutation for theBenchmark.p
% 2.33/1.06  
% 2.33/1.06  ------                               Statistics
% 2.33/1.06  
% 2.33/1.06  ------ General
% 2.33/1.06  
% 2.33/1.06  abstr_ref_over_cycles:                  0
% 2.33/1.06  abstr_ref_under_cycles:                 0
% 2.33/1.06  gc_basic_clause_elim:                   0
% 2.33/1.06  forced_gc_time:                         0
% 2.33/1.06  parsing_time:                           0.007
% 2.33/1.06  unif_index_cands_time:                  0.
% 2.33/1.06  unif_index_add_time:                    0.
% 2.33/1.06  orderings_time:                         0.
% 2.33/1.06  out_proof_time:                         0.03
% 2.33/1.06  total_time:                             0.274
% 2.33/1.06  num_of_symbols:                         45
% 2.33/1.06  num_of_terms:                           4101
% 2.33/1.06  
% 2.33/1.06  ------ Preprocessing
% 2.33/1.06  
% 2.33/1.06  num_of_splits:                          0
% 2.33/1.06  num_of_split_atoms:                     0
% 2.33/1.06  num_of_reused_defs:                     0
% 2.33/1.06  num_eq_ax_congr_red:                    11
% 2.33/1.06  num_of_sem_filtered_clauses:            1
% 2.33/1.06  num_of_subtypes:                        0
% 2.33/1.06  monotx_restored_types:                  0
% 2.33/1.06  sat_num_of_epr_types:                   0
% 2.33/1.06  sat_num_of_non_cyclic_types:            0
% 2.33/1.06  sat_guarded_non_collapsed_types:        0
% 2.33/1.06  num_pure_diseq_elim:                    0
% 2.33/1.06  simp_replaced_by:                       0
% 2.33/1.06  res_preprocessed:                       93
% 2.33/1.06  prep_upred:                             0
% 2.33/1.06  prep_unflattend:                        3
% 2.33/1.06  smt_new_axioms:                         0
% 2.33/1.06  pred_elim_cands:                        3
% 2.33/1.06  pred_elim:                              1
% 2.33/1.06  pred_elim_cl:                           2
% 2.33/1.06  pred_elim_cycles:                       3
% 2.33/1.06  merged_defs:                            8
% 2.33/1.06  merged_defs_ncl:                        0
% 2.33/1.06  bin_hyper_res:                          9
% 2.33/1.06  prep_cycles:                            4
% 2.33/1.06  pred_elim_time:                         0.001
% 2.33/1.06  splitting_time:                         0.
% 2.33/1.06  sem_filter_time:                        0.
% 2.33/1.06  monotx_time:                            0.
% 2.33/1.06  subtype_inf_time:                       0.
% 2.33/1.06  
% 2.33/1.06  ------ Problem properties
% 2.33/1.06  
% 2.33/1.06  clauses:                                18
% 2.33/1.06  conjectures:                            4
% 2.33/1.06  epr:                                    4
% 2.33/1.06  horn:                                   15
% 2.33/1.06  ground:                                 4
% 2.33/1.06  unary:                                  7
% 2.33/1.06  binary:                                 7
% 2.33/1.06  lits:                                   33
% 2.33/1.06  lits_eq:                                12
% 2.33/1.06  fd_pure:                                0
% 2.33/1.06  fd_pseudo:                              0
% 2.33/1.06  fd_cond:                                4
% 2.33/1.06  fd_pseudo_cond:                         0
% 2.33/1.06  ac_symbols:                             0
% 2.33/1.06  
% 2.33/1.06  ------ Propositional Solver
% 2.33/1.06  
% 2.33/1.06  prop_solver_calls:                      30
% 2.33/1.06  prop_fast_solver_calls:                 533
% 2.33/1.06  smt_solver_calls:                       0
% 2.33/1.06  smt_fast_solver_calls:                  0
% 2.33/1.06  prop_num_of_clauses:                    1596
% 2.33/1.06  prop_preprocess_simplified:             4385
% 2.33/1.06  prop_fo_subsumed:                       16
% 2.33/1.06  prop_solver_time:                       0.
% 2.33/1.06  smt_solver_time:                        0.
% 2.33/1.06  smt_fast_solver_time:                   0.
% 2.33/1.06  prop_fast_solver_time:                  0.
% 2.33/1.06  prop_unsat_core_time:                   0.
% 2.33/1.06  
% 2.33/1.06  ------ QBF
% 2.33/1.06  
% 2.33/1.06  qbf_q_res:                              0
% 2.33/1.06  qbf_num_tautologies:                    0
% 2.33/1.06  qbf_prep_cycles:                        0
% 2.33/1.06  
% 2.33/1.06  ------ BMC1
% 2.33/1.06  
% 2.33/1.06  bmc1_current_bound:                     -1
% 2.33/1.06  bmc1_last_solved_bound:                 -1
% 2.33/1.06  bmc1_unsat_core_size:                   -1
% 2.33/1.06  bmc1_unsat_core_parents_size:           -1
% 2.33/1.06  bmc1_merge_next_fun:                    0
% 2.33/1.06  bmc1_unsat_core_clauses_time:           0.
% 2.33/1.06  
% 2.33/1.06  ------ Instantiation
% 2.33/1.06  
% 2.33/1.06  inst_num_of_clauses:                    568
% 2.33/1.06  inst_num_in_passive:                    216
% 2.33/1.06  inst_num_in_active:                     272
% 2.33/1.06  inst_num_in_unprocessed:                80
% 2.33/1.06  inst_num_of_loops:                      330
% 2.33/1.06  inst_num_of_learning_restarts:          0
% 2.33/1.06  inst_num_moves_active_passive:          54
% 2.33/1.06  inst_lit_activity:                      0
% 2.33/1.06  inst_lit_activity_moves:                0
% 2.33/1.06  inst_num_tautologies:                   0
% 2.33/1.06  inst_num_prop_implied:                  0
% 2.33/1.06  inst_num_existing_simplified:           0
% 2.33/1.06  inst_num_eq_res_simplified:             0
% 2.33/1.06  inst_num_child_elim:                    0
% 2.33/1.06  inst_num_of_dismatching_blockings:      176
% 2.33/1.06  inst_num_of_non_proper_insts:           608
% 2.33/1.06  inst_num_of_duplicates:                 0
% 2.33/1.06  inst_inst_num_from_inst_to_res:         0
% 2.33/1.06  inst_dismatching_checking_time:         0.
% 2.33/1.06  
% 2.33/1.06  ------ Resolution
% 2.33/1.06  
% 2.33/1.06  res_num_of_clauses:                     0
% 2.33/1.06  res_num_in_passive:                     0
% 2.33/1.06  res_num_in_active:                      0
% 2.33/1.06  res_num_of_loops:                       97
% 2.33/1.06  res_forward_subset_subsumed:            60
% 2.33/1.06  res_backward_subset_subsumed:           0
% 2.33/1.06  res_forward_subsumed:                   0
% 2.33/1.06  res_backward_subsumed:                  0
% 2.33/1.06  res_forward_subsumption_resolution:     0
% 2.33/1.06  res_backward_subsumption_resolution:    0
% 2.33/1.06  res_clause_to_clause_subsumption:       248
% 2.33/1.06  res_orphan_elimination:                 0
% 2.33/1.06  res_tautology_del:                      87
% 2.33/1.06  res_num_eq_res_simplified:              0
% 2.33/1.06  res_num_sel_changes:                    0
% 2.33/1.06  res_moves_from_active_to_pass:          0
% 2.33/1.06  
% 2.33/1.06  ------ Superposition
% 2.33/1.06  
% 2.33/1.06  sup_time_total:                         0.
% 2.33/1.06  sup_time_generating:                    0.
% 2.33/1.06  sup_time_sim_full:                      0.
% 2.33/1.06  sup_time_sim_immed:                     0.
% 2.33/1.06  
% 2.33/1.06  sup_num_of_clauses:                     61
% 2.33/1.06  sup_num_in_active:                      39
% 2.33/1.06  sup_num_in_passive:                     22
% 2.33/1.06  sup_num_of_loops:                       64
% 2.33/1.06  sup_fw_superposition:                   55
% 2.33/1.06  sup_bw_superposition:                   66
% 2.33/1.06  sup_immediate_simplified:               34
% 2.33/1.06  sup_given_eliminated:                   1
% 2.33/1.06  comparisons_done:                       0
% 2.33/1.06  comparisons_avoided:                    25
% 2.33/1.06  
% 2.33/1.06  ------ Simplifications
% 2.33/1.06  
% 2.33/1.06  
% 2.33/1.06  sim_fw_subset_subsumed:                 15
% 2.33/1.06  sim_bw_subset_subsumed:                 13
% 2.33/1.06  sim_fw_subsumed:                        7
% 2.33/1.06  sim_bw_subsumed:                        1
% 2.33/1.06  sim_fw_subsumption_res:                 2
% 2.33/1.06  sim_bw_subsumption_res:                 0
% 2.33/1.06  sim_tautology_del:                      5
% 2.33/1.06  sim_eq_tautology_del:                   7
% 2.33/1.06  sim_eq_res_simp:                        0
% 2.33/1.06  sim_fw_demodulated:                     10
% 2.33/1.06  sim_bw_demodulated:                     20
% 2.33/1.06  sim_light_normalised:                   7
% 2.33/1.06  sim_joinable_taut:                      0
% 2.33/1.06  sim_joinable_simp:                      0
% 2.33/1.06  sim_ac_normalised:                      0
% 2.33/1.06  sim_smt_subsumption:                    0
% 2.33/1.06  
%------------------------------------------------------------------------------
