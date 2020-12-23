%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:24:43 EST 2020

% Result     : Theorem 2.39s
% Output     : CNFRefutation 2.39s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 332 expanded)
%              Number of clauses        :   75 ( 114 expanded)
%              Number of leaves         :   22 (  84 expanded)
%              Depth                    :   18
%              Number of atoms          :  330 ( 865 expanded)
%              Number of equality atoms :  130 ( 258 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f13,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f58,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X0,X1)
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( ~ v1_xboole_0(k3_xboole_0(X0,X1))
         => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_zfmisc_1(X0)
          & ~ v1_xboole_0(X0) )
       => ! [X1] :
            ( ~ v1_xboole_0(k3_xboole_0(X0,X1))
           => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X0,X1)
          & ~ v1_xboole_0(k3_xboole_0(X0,X1)) )
      & v1_zfmisc_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X0,X1)
          & ~ v1_xboole_0(k3_xboole_0(X0,X1)) )
      & v1_zfmisc_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X0,X1)
          & ~ v1_xboole_0(k3_xboole_0(X0,X1)) )
     => ( ~ r1_tarski(X0,sK3)
        & ~ v1_xboole_0(k3_xboole_0(X0,sK3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(X0,X1)
            & ~ v1_xboole_0(k3_xboole_0(X0,X1)) )
        & v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(sK2,X1)
          & ~ v1_xboole_0(k3_xboole_0(sK2,X1)) )
      & v1_zfmisc_1(sK2)
      & ~ v1_xboole_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ~ r1_tarski(sK2,sK3)
    & ~ v1_xboole_0(k3_xboole_0(sK2,sK3))
    & v1_zfmisc_1(sK2)
    & ~ v1_xboole_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f25,f38,f37])).

fof(f60,plain,(
    v1_zfmisc_1(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f59,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f30])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f32])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f26])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).

fof(f40,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f7,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f52,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f11,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f64,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f57,f53,f56])).

fof(f61,plain,(
    ~ v1_xboole_0(k3_xboole_0(sK2,sK3)) ),
    inference(cnf_transformation,[],[f39])).

fof(f65,plain,(
    ~ v1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) ),
    inference(definition_unfolding,[],[f61,f53])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f34])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f66,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f47])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f9,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
     => r1_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(ennf_transformation,[],[f16])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f45,f53])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f20])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f62,plain,(
    ~ r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_11,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1017,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_16,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_19,negated_conjecture,
    ( v1_zfmisc_1(sK2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_259,plain,
    ( ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 = X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_19])).

cnf(c_260,plain,
    ( ~ r1_tarski(X0,sK2)
    | v1_xboole_0(X0)
    | v1_xboole_0(sK2)
    | sK2 = X0 ),
    inference(unflattening,[status(thm)],[c_259])).

cnf(c_20,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_264,plain,
    ( v1_xboole_0(X0)
    | ~ r1_tarski(X0,sK2)
    | sK2 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_260,c_20])).

cnf(c_265,plain,
    ( ~ r1_tarski(X0,sK2)
    | v1_xboole_0(X0)
    | sK2 = X0 ),
    inference(renaming,[status(thm)],[c_264])).

cnf(c_1011,plain,
    ( sK2 = X0
    | r1_tarski(X0,sK2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_265])).

cnf(c_1360,plain,
    ( k4_xboole_0(sK2,X0) = sK2
    | v1_xboole_0(k4_xboole_0(sK2,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1017,c_1011])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1023,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1025,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2429,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1023,c_1025])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1016,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2631,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2429,c_1016])).

cnf(c_2733,plain,
    ( k4_xboole_0(sK2,X0) = sK2
    | k4_xboole_0(sK2,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1360,c_2631])).

cnf(c_15,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1374,plain,
    ( r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_15,c_1017])).

cnf(c_1531,plain,
    ( k1_setfam_1(k1_enumset1(sK2,sK2,X0)) = sK2
    | v1_xboole_0(k1_setfam_1(k1_enumset1(sK2,sK2,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1374,c_1011])).

cnf(c_18,negated_conjecture,
    ( ~ v1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1014,plain,
    ( v1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1044,plain,
    ( v1_xboole_0(k1_setfam_1(k1_enumset1(sK2,sK2,sK3))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_15,c_1014])).

cnf(c_1779,plain,
    ( k1_setfam_1(k1_enumset1(sK2,sK2,sK3)) = sK2 ),
    inference(superposition,[status(thm)],[c_1531,c_1044])).

cnf(c_1373,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) ),
    inference(superposition,[status(thm)],[c_15,c_15])).

cnf(c_3181,plain,
    ( k1_setfam_1(k1_enumset1(sK2,sK2,k4_xboole_0(sK2,sK3))) = k4_xboole_0(sK2,sK2) ),
    inference(superposition,[status(thm)],[c_1779,c_1373])).

cnf(c_7,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1020,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1019,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2113,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1020,c_1019])).

cnf(c_3219,plain,
    ( k1_setfam_1(k1_enumset1(sK2,sK2,k4_xboole_0(sK2,sK3))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3181,c_2113])).

cnf(c_3483,plain,
    ( k4_xboole_0(sK2,sK3) = k1_xboole_0
    | k1_setfam_1(k1_enumset1(sK2,sK2,sK2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2733,c_3219])).

cnf(c_2127,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2113,c_15])).

cnf(c_3503,plain,
    ( k4_xboole_0(sK2,sK3) = k1_xboole_0
    | k4_xboole_0(sK2,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3483,c_2127])).

cnf(c_633,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1297,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),X2)
    | X2 != X1
    | k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) != X0 ),
    inference(instantiation,[status(thm)],[c_633])).

cnf(c_2328,plain,
    ( r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),X0)
    | ~ r1_tarski(sK2,X1)
    | X0 != X1
    | k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) != sK2 ),
    inference(instantiation,[status(thm)],[c_1297])).

cnf(c_2331,plain,
    ( r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k1_xboole_0)
    | ~ r1_tarski(sK2,k1_xboole_0)
    | k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) != sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2328])).

cnf(c_630,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1229,plain,
    ( X0 != X1
    | k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) != X1
    | k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = X0 ),
    inference(instantiation,[status(thm)],[c_630])).

cnf(c_1543,plain,
    ( X0 != k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))
    | k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = X0
    | k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) != k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_1229])).

cnf(c_1977,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) != k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))
    | k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = sK2
    | sK2 != k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_1543])).

cnf(c_1967,plain,
    ( ~ r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k1_xboole_0)
    | k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_629,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1544,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_629])).

cnf(c_1545,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) != k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))
    | k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = k1_xboole_0
    | k1_xboole_0 != k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_1543])).

cnf(c_13,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1375,plain,
    ( k1_setfam_1(k1_enumset1(k1_xboole_0,k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_15,c_13])).

cnf(c_1384,plain,
    ( k1_setfam_1(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1375])).

cnf(c_10,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1304,plain,
    ( r1_tarski(sK2,X0)
    | k4_xboole_0(sK2,X0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1306,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | k4_xboole_0(sK2,k1_xboole_0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1304])).

cnf(c_631,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1153,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
    | k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) != X0 ),
    inference(instantiation,[status(thm)],[c_631])).

cnf(c_1155,plain,
    ( v1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
    | ~ v1_xboole_0(k1_xboole_0)
    | k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1153])).

cnf(c_1150,plain,
    ( r1_tarski(sK2,sK3)
    | k4_xboole_0(sK2,sK3) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_5,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_14,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_241,plain,
    ( ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_5,c_14])).

cnf(c_1012,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_241])).

cnf(c_1090,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,X1)) != k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1012,c_15])).

cnf(c_1109,plain,
    ( ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0)
    | k1_setfam_1(k1_enumset1(X0,X0,X1)) != k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1090])).

cnf(c_1111,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | v1_xboole_0(k1_xboole_0)
    | k1_setfam_1(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1109])).

cnf(c_326,plain,
    ( ~ r1_tarski(X0,sK2)
    | k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) != X0
    | sK2 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_265,c_18])).

cnf(c_327,plain,
    ( ~ r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),sK2)
    | sK2 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_326])).

cnf(c_333,plain,
    ( sK2 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_327,c_11])).

cnf(c_40,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0)
    | k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_34,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_32,plain,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_17,negated_conjecture,
    ( ~ r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f62])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3503,c_2331,c_1977,c_1967,c_1544,c_1545,c_1384,c_1306,c_1155,c_1150,c_1111,c_333,c_40,c_34,c_32,c_17,c_18])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:26:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.39/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.39/1.02  
% 2.39/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.39/1.02  
% 2.39/1.02  ------  iProver source info
% 2.39/1.02  
% 2.39/1.02  git: date: 2020-06-30 10:37:57 +0100
% 2.39/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.39/1.02  git: non_committed_changes: false
% 2.39/1.02  git: last_make_outside_of_git: false
% 2.39/1.02  
% 2.39/1.02  ------ 
% 2.39/1.02  
% 2.39/1.02  ------ Input Options
% 2.39/1.02  
% 2.39/1.02  --out_options                           all
% 2.39/1.02  --tptp_safe_out                         true
% 2.39/1.02  --problem_path                          ""
% 2.39/1.02  --include_path                          ""
% 2.39/1.02  --clausifier                            res/vclausify_rel
% 2.39/1.02  --clausifier_options                    --mode clausify
% 2.39/1.02  --stdin                                 false
% 2.39/1.02  --stats_out                             all
% 2.39/1.02  
% 2.39/1.02  ------ General Options
% 2.39/1.02  
% 2.39/1.02  --fof                                   false
% 2.39/1.02  --time_out_real                         305.
% 2.39/1.02  --time_out_virtual                      -1.
% 2.39/1.02  --symbol_type_check                     false
% 2.39/1.02  --clausify_out                          false
% 2.39/1.02  --sig_cnt_out                           false
% 2.39/1.02  --trig_cnt_out                          false
% 2.39/1.02  --trig_cnt_out_tolerance                1.
% 2.39/1.02  --trig_cnt_out_sk_spl                   false
% 2.39/1.02  --abstr_cl_out                          false
% 2.39/1.02  
% 2.39/1.02  ------ Global Options
% 2.39/1.02  
% 2.39/1.02  --schedule                              default
% 2.39/1.02  --add_important_lit                     false
% 2.39/1.02  --prop_solver_per_cl                    1000
% 2.39/1.02  --min_unsat_core                        false
% 2.39/1.02  --soft_assumptions                      false
% 2.39/1.02  --soft_lemma_size                       3
% 2.39/1.02  --prop_impl_unit_size                   0
% 2.39/1.02  --prop_impl_unit                        []
% 2.39/1.02  --share_sel_clauses                     true
% 2.39/1.02  --reset_solvers                         false
% 2.39/1.02  --bc_imp_inh                            [conj_cone]
% 2.39/1.02  --conj_cone_tolerance                   3.
% 2.39/1.02  --extra_neg_conj                        none
% 2.39/1.02  --large_theory_mode                     true
% 2.39/1.02  --prolific_symb_bound                   200
% 2.39/1.02  --lt_threshold                          2000
% 2.39/1.02  --clause_weak_htbl                      true
% 2.39/1.02  --gc_record_bc_elim                     false
% 2.39/1.02  
% 2.39/1.02  ------ Preprocessing Options
% 2.39/1.02  
% 2.39/1.02  --preprocessing_flag                    true
% 2.39/1.02  --time_out_prep_mult                    0.1
% 2.39/1.02  --splitting_mode                        input
% 2.39/1.02  --splitting_grd                         true
% 2.39/1.02  --splitting_cvd                         false
% 2.39/1.02  --splitting_cvd_svl                     false
% 2.39/1.02  --splitting_nvd                         32
% 2.39/1.02  --sub_typing                            true
% 2.39/1.02  --prep_gs_sim                           true
% 2.39/1.02  --prep_unflatten                        true
% 2.39/1.02  --prep_res_sim                          true
% 2.39/1.02  --prep_upred                            true
% 2.39/1.02  --prep_sem_filter                       exhaustive
% 2.39/1.02  --prep_sem_filter_out                   false
% 2.39/1.02  --pred_elim                             true
% 2.39/1.02  --res_sim_input                         true
% 2.39/1.02  --eq_ax_congr_red                       true
% 2.39/1.02  --pure_diseq_elim                       true
% 2.39/1.02  --brand_transform                       false
% 2.39/1.02  --non_eq_to_eq                          false
% 2.39/1.02  --prep_def_merge                        true
% 2.39/1.02  --prep_def_merge_prop_impl              false
% 2.39/1.02  --prep_def_merge_mbd                    true
% 2.39/1.02  --prep_def_merge_tr_red                 false
% 2.39/1.02  --prep_def_merge_tr_cl                  false
% 2.39/1.02  --smt_preprocessing                     true
% 2.39/1.02  --smt_ac_axioms                         fast
% 2.39/1.02  --preprocessed_out                      false
% 2.39/1.02  --preprocessed_stats                    false
% 2.39/1.02  
% 2.39/1.02  ------ Abstraction refinement Options
% 2.39/1.02  
% 2.39/1.02  --abstr_ref                             []
% 2.39/1.02  --abstr_ref_prep                        false
% 2.39/1.02  --abstr_ref_until_sat                   false
% 2.39/1.02  --abstr_ref_sig_restrict                funpre
% 2.39/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.39/1.02  --abstr_ref_under                       []
% 2.39/1.02  
% 2.39/1.02  ------ SAT Options
% 2.39/1.02  
% 2.39/1.02  --sat_mode                              false
% 2.39/1.02  --sat_fm_restart_options                ""
% 2.39/1.02  --sat_gr_def                            false
% 2.39/1.02  --sat_epr_types                         true
% 2.39/1.02  --sat_non_cyclic_types                  false
% 2.39/1.02  --sat_finite_models                     false
% 2.39/1.02  --sat_fm_lemmas                         false
% 2.39/1.02  --sat_fm_prep                           false
% 2.39/1.02  --sat_fm_uc_incr                        true
% 2.39/1.02  --sat_out_model                         small
% 2.39/1.02  --sat_out_clauses                       false
% 2.39/1.02  
% 2.39/1.02  ------ QBF Options
% 2.39/1.02  
% 2.39/1.02  --qbf_mode                              false
% 2.39/1.02  --qbf_elim_univ                         false
% 2.39/1.02  --qbf_dom_inst                          none
% 2.39/1.02  --qbf_dom_pre_inst                      false
% 2.39/1.02  --qbf_sk_in                             false
% 2.39/1.02  --qbf_pred_elim                         true
% 2.39/1.02  --qbf_split                             512
% 2.39/1.02  
% 2.39/1.02  ------ BMC1 Options
% 2.39/1.02  
% 2.39/1.02  --bmc1_incremental                      false
% 2.39/1.02  --bmc1_axioms                           reachable_all
% 2.39/1.02  --bmc1_min_bound                        0
% 2.39/1.02  --bmc1_max_bound                        -1
% 2.39/1.02  --bmc1_max_bound_default                -1
% 2.39/1.02  --bmc1_symbol_reachability              true
% 2.39/1.02  --bmc1_property_lemmas                  false
% 2.39/1.02  --bmc1_k_induction                      false
% 2.39/1.02  --bmc1_non_equiv_states                 false
% 2.39/1.02  --bmc1_deadlock                         false
% 2.39/1.02  --bmc1_ucm                              false
% 2.39/1.02  --bmc1_add_unsat_core                   none
% 2.39/1.02  --bmc1_unsat_core_children              false
% 2.39/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.39/1.02  --bmc1_out_stat                         full
% 2.39/1.02  --bmc1_ground_init                      false
% 2.39/1.02  --bmc1_pre_inst_next_state              false
% 2.39/1.02  --bmc1_pre_inst_state                   false
% 2.39/1.02  --bmc1_pre_inst_reach_state             false
% 2.39/1.02  --bmc1_out_unsat_core                   false
% 2.39/1.02  --bmc1_aig_witness_out                  false
% 2.39/1.02  --bmc1_verbose                          false
% 2.39/1.02  --bmc1_dump_clauses_tptp                false
% 2.39/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.39/1.02  --bmc1_dump_file                        -
% 2.39/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.39/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.39/1.02  --bmc1_ucm_extend_mode                  1
% 2.39/1.02  --bmc1_ucm_init_mode                    2
% 2.39/1.02  --bmc1_ucm_cone_mode                    none
% 2.39/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.39/1.02  --bmc1_ucm_relax_model                  4
% 2.39/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.39/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.39/1.02  --bmc1_ucm_layered_model                none
% 2.39/1.02  --bmc1_ucm_max_lemma_size               10
% 2.39/1.02  
% 2.39/1.02  ------ AIG Options
% 2.39/1.02  
% 2.39/1.02  --aig_mode                              false
% 2.39/1.02  
% 2.39/1.02  ------ Instantiation Options
% 2.39/1.02  
% 2.39/1.02  --instantiation_flag                    true
% 2.39/1.02  --inst_sos_flag                         false
% 2.39/1.02  --inst_sos_phase                        true
% 2.39/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.39/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.39/1.02  --inst_lit_sel_side                     num_symb
% 2.39/1.02  --inst_solver_per_active                1400
% 2.39/1.02  --inst_solver_calls_frac                1.
% 2.39/1.02  --inst_passive_queue_type               priority_queues
% 2.39/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.39/1.02  --inst_passive_queues_freq              [25;2]
% 2.39/1.02  --inst_dismatching                      true
% 2.39/1.02  --inst_eager_unprocessed_to_passive     true
% 2.39/1.02  --inst_prop_sim_given                   true
% 2.39/1.02  --inst_prop_sim_new                     false
% 2.39/1.02  --inst_subs_new                         false
% 2.39/1.02  --inst_eq_res_simp                      false
% 2.39/1.02  --inst_subs_given                       false
% 2.39/1.02  --inst_orphan_elimination               true
% 2.39/1.02  --inst_learning_loop_flag               true
% 2.39/1.02  --inst_learning_start                   3000
% 2.39/1.02  --inst_learning_factor                  2
% 2.39/1.02  --inst_start_prop_sim_after_learn       3
% 2.39/1.02  --inst_sel_renew                        solver
% 2.39/1.02  --inst_lit_activity_flag                true
% 2.39/1.02  --inst_restr_to_given                   false
% 2.39/1.02  --inst_activity_threshold               500
% 2.39/1.02  --inst_out_proof                        true
% 2.39/1.02  
% 2.39/1.02  ------ Resolution Options
% 2.39/1.02  
% 2.39/1.02  --resolution_flag                       true
% 2.39/1.02  --res_lit_sel                           adaptive
% 2.39/1.02  --res_lit_sel_side                      none
% 2.39/1.02  --res_ordering                          kbo
% 2.39/1.02  --res_to_prop_solver                    active
% 2.39/1.02  --res_prop_simpl_new                    false
% 2.39/1.02  --res_prop_simpl_given                  true
% 2.39/1.02  --res_passive_queue_type                priority_queues
% 2.39/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.39/1.02  --res_passive_queues_freq               [15;5]
% 2.39/1.02  --res_forward_subs                      full
% 2.39/1.02  --res_backward_subs                     full
% 2.39/1.02  --res_forward_subs_resolution           true
% 2.39/1.02  --res_backward_subs_resolution          true
% 2.39/1.02  --res_orphan_elimination                true
% 2.39/1.02  --res_time_limit                        2.
% 2.39/1.02  --res_out_proof                         true
% 2.39/1.02  
% 2.39/1.02  ------ Superposition Options
% 2.39/1.02  
% 2.39/1.02  --superposition_flag                    true
% 2.39/1.02  --sup_passive_queue_type                priority_queues
% 2.39/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.39/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.39/1.02  --demod_completeness_check              fast
% 2.39/1.02  --demod_use_ground                      true
% 2.39/1.02  --sup_to_prop_solver                    passive
% 2.39/1.02  --sup_prop_simpl_new                    true
% 2.39/1.02  --sup_prop_simpl_given                  true
% 2.39/1.02  --sup_fun_splitting                     false
% 2.39/1.02  --sup_smt_interval                      50000
% 2.39/1.02  
% 2.39/1.02  ------ Superposition Simplification Setup
% 2.39/1.02  
% 2.39/1.02  --sup_indices_passive                   []
% 2.39/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.39/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.39/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.39/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.39/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.39/1.02  --sup_full_bw                           [BwDemod]
% 2.39/1.02  --sup_immed_triv                        [TrivRules]
% 2.39/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.39/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.39/1.02  --sup_immed_bw_main                     []
% 2.39/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.39/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.39/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.39/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.39/1.02  
% 2.39/1.02  ------ Combination Options
% 2.39/1.02  
% 2.39/1.02  --comb_res_mult                         3
% 2.39/1.02  --comb_sup_mult                         2
% 2.39/1.02  --comb_inst_mult                        10
% 2.39/1.02  
% 2.39/1.02  ------ Debug Options
% 2.39/1.02  
% 2.39/1.02  --dbg_backtrace                         false
% 2.39/1.02  --dbg_dump_prop_clauses                 false
% 2.39/1.02  --dbg_dump_prop_clauses_file            -
% 2.39/1.02  --dbg_out_stat                          false
% 2.39/1.02  ------ Parsing...
% 2.39/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.39/1.02  
% 2.39/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.39/1.02  
% 2.39/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.39/1.02  
% 2.39/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.39/1.02  ------ Proving...
% 2.39/1.02  ------ Problem Properties 
% 2.39/1.02  
% 2.39/1.02  
% 2.39/1.02  clauses                                 18
% 2.39/1.02  conjectures                             3
% 2.39/1.02  EPR                                     8
% 2.39/1.02  Horn                                    15
% 2.39/1.02  unary                                   7
% 2.39/1.02  binary                                  7
% 2.39/1.02  lits                                    33
% 2.39/1.02  lits eq                                 8
% 2.39/1.02  fd_pure                                 0
% 2.39/1.02  fd_pseudo                               0
% 2.39/1.02  fd_cond                                 2
% 2.39/1.02  fd_pseudo_cond                          1
% 2.39/1.02  AC symbols                              0
% 2.39/1.02  
% 2.39/1.02  ------ Schedule dynamic 5 is on 
% 2.39/1.02  
% 2.39/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.39/1.02  
% 2.39/1.02  
% 2.39/1.02  ------ 
% 2.39/1.02  Current options:
% 2.39/1.02  ------ 
% 2.39/1.02  
% 2.39/1.02  ------ Input Options
% 2.39/1.02  
% 2.39/1.02  --out_options                           all
% 2.39/1.02  --tptp_safe_out                         true
% 2.39/1.02  --problem_path                          ""
% 2.39/1.02  --include_path                          ""
% 2.39/1.02  --clausifier                            res/vclausify_rel
% 2.39/1.02  --clausifier_options                    --mode clausify
% 2.39/1.02  --stdin                                 false
% 2.39/1.02  --stats_out                             all
% 2.39/1.02  
% 2.39/1.02  ------ General Options
% 2.39/1.02  
% 2.39/1.02  --fof                                   false
% 2.39/1.02  --time_out_real                         305.
% 2.39/1.02  --time_out_virtual                      -1.
% 2.39/1.02  --symbol_type_check                     false
% 2.39/1.02  --clausify_out                          false
% 2.39/1.02  --sig_cnt_out                           false
% 2.39/1.02  --trig_cnt_out                          false
% 2.39/1.02  --trig_cnt_out_tolerance                1.
% 2.39/1.02  --trig_cnt_out_sk_spl                   false
% 2.39/1.02  --abstr_cl_out                          false
% 2.39/1.02  
% 2.39/1.02  ------ Global Options
% 2.39/1.02  
% 2.39/1.02  --schedule                              default
% 2.39/1.02  --add_important_lit                     false
% 2.39/1.02  --prop_solver_per_cl                    1000
% 2.39/1.02  --min_unsat_core                        false
% 2.39/1.02  --soft_assumptions                      false
% 2.39/1.02  --soft_lemma_size                       3
% 2.39/1.02  --prop_impl_unit_size                   0
% 2.39/1.02  --prop_impl_unit                        []
% 2.39/1.02  --share_sel_clauses                     true
% 2.39/1.02  --reset_solvers                         false
% 2.39/1.02  --bc_imp_inh                            [conj_cone]
% 2.39/1.02  --conj_cone_tolerance                   3.
% 2.39/1.03  --extra_neg_conj                        none
% 2.39/1.03  --large_theory_mode                     true
% 2.39/1.03  --prolific_symb_bound                   200
% 2.39/1.03  --lt_threshold                          2000
% 2.39/1.03  --clause_weak_htbl                      true
% 2.39/1.03  --gc_record_bc_elim                     false
% 2.39/1.03  
% 2.39/1.03  ------ Preprocessing Options
% 2.39/1.03  
% 2.39/1.03  --preprocessing_flag                    true
% 2.39/1.03  --time_out_prep_mult                    0.1
% 2.39/1.03  --splitting_mode                        input
% 2.39/1.03  --splitting_grd                         true
% 2.39/1.03  --splitting_cvd                         false
% 2.39/1.03  --splitting_cvd_svl                     false
% 2.39/1.03  --splitting_nvd                         32
% 2.39/1.03  --sub_typing                            true
% 2.39/1.03  --prep_gs_sim                           true
% 2.39/1.03  --prep_unflatten                        true
% 2.39/1.03  --prep_res_sim                          true
% 2.39/1.03  --prep_upred                            true
% 2.39/1.03  --prep_sem_filter                       exhaustive
% 2.39/1.03  --prep_sem_filter_out                   false
% 2.39/1.03  --pred_elim                             true
% 2.39/1.03  --res_sim_input                         true
% 2.39/1.03  --eq_ax_congr_red                       true
% 2.39/1.03  --pure_diseq_elim                       true
% 2.39/1.03  --brand_transform                       false
% 2.39/1.03  --non_eq_to_eq                          false
% 2.39/1.03  --prep_def_merge                        true
% 2.39/1.03  --prep_def_merge_prop_impl              false
% 2.39/1.03  --prep_def_merge_mbd                    true
% 2.39/1.03  --prep_def_merge_tr_red                 false
% 2.39/1.03  --prep_def_merge_tr_cl                  false
% 2.39/1.03  --smt_preprocessing                     true
% 2.39/1.03  --smt_ac_axioms                         fast
% 2.39/1.03  --preprocessed_out                      false
% 2.39/1.03  --preprocessed_stats                    false
% 2.39/1.03  
% 2.39/1.03  ------ Abstraction refinement Options
% 2.39/1.03  
% 2.39/1.03  --abstr_ref                             []
% 2.39/1.03  --abstr_ref_prep                        false
% 2.39/1.03  --abstr_ref_until_sat                   false
% 2.39/1.03  --abstr_ref_sig_restrict                funpre
% 2.39/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.39/1.03  --abstr_ref_under                       []
% 2.39/1.03  
% 2.39/1.03  ------ SAT Options
% 2.39/1.03  
% 2.39/1.03  --sat_mode                              false
% 2.39/1.03  --sat_fm_restart_options                ""
% 2.39/1.03  --sat_gr_def                            false
% 2.39/1.03  --sat_epr_types                         true
% 2.39/1.03  --sat_non_cyclic_types                  false
% 2.39/1.03  --sat_finite_models                     false
% 2.39/1.03  --sat_fm_lemmas                         false
% 2.39/1.03  --sat_fm_prep                           false
% 2.39/1.03  --sat_fm_uc_incr                        true
% 2.39/1.03  --sat_out_model                         small
% 2.39/1.03  --sat_out_clauses                       false
% 2.39/1.03  
% 2.39/1.03  ------ QBF Options
% 2.39/1.03  
% 2.39/1.03  --qbf_mode                              false
% 2.39/1.03  --qbf_elim_univ                         false
% 2.39/1.03  --qbf_dom_inst                          none
% 2.39/1.03  --qbf_dom_pre_inst                      false
% 2.39/1.03  --qbf_sk_in                             false
% 2.39/1.03  --qbf_pred_elim                         true
% 2.39/1.03  --qbf_split                             512
% 2.39/1.03  
% 2.39/1.03  ------ BMC1 Options
% 2.39/1.03  
% 2.39/1.03  --bmc1_incremental                      false
% 2.39/1.03  --bmc1_axioms                           reachable_all
% 2.39/1.03  --bmc1_min_bound                        0
% 2.39/1.03  --bmc1_max_bound                        -1
% 2.39/1.03  --bmc1_max_bound_default                -1
% 2.39/1.03  --bmc1_symbol_reachability              true
% 2.39/1.03  --bmc1_property_lemmas                  false
% 2.39/1.03  --bmc1_k_induction                      false
% 2.39/1.03  --bmc1_non_equiv_states                 false
% 2.39/1.03  --bmc1_deadlock                         false
% 2.39/1.03  --bmc1_ucm                              false
% 2.39/1.03  --bmc1_add_unsat_core                   none
% 2.39/1.03  --bmc1_unsat_core_children              false
% 2.39/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.39/1.03  --bmc1_out_stat                         full
% 2.39/1.03  --bmc1_ground_init                      false
% 2.39/1.03  --bmc1_pre_inst_next_state              false
% 2.39/1.03  --bmc1_pre_inst_state                   false
% 2.39/1.03  --bmc1_pre_inst_reach_state             false
% 2.39/1.03  --bmc1_out_unsat_core                   false
% 2.39/1.03  --bmc1_aig_witness_out                  false
% 2.39/1.03  --bmc1_verbose                          false
% 2.39/1.03  --bmc1_dump_clauses_tptp                false
% 2.39/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.39/1.03  --bmc1_dump_file                        -
% 2.39/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.39/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.39/1.03  --bmc1_ucm_extend_mode                  1
% 2.39/1.03  --bmc1_ucm_init_mode                    2
% 2.39/1.03  --bmc1_ucm_cone_mode                    none
% 2.39/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.39/1.03  --bmc1_ucm_relax_model                  4
% 2.39/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.39/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.39/1.03  --bmc1_ucm_layered_model                none
% 2.39/1.03  --bmc1_ucm_max_lemma_size               10
% 2.39/1.03  
% 2.39/1.03  ------ AIG Options
% 2.39/1.03  
% 2.39/1.03  --aig_mode                              false
% 2.39/1.03  
% 2.39/1.03  ------ Instantiation Options
% 2.39/1.03  
% 2.39/1.03  --instantiation_flag                    true
% 2.39/1.03  --inst_sos_flag                         false
% 2.39/1.03  --inst_sos_phase                        true
% 2.39/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.39/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.39/1.03  --inst_lit_sel_side                     none
% 2.39/1.03  --inst_solver_per_active                1400
% 2.39/1.03  --inst_solver_calls_frac                1.
% 2.39/1.03  --inst_passive_queue_type               priority_queues
% 2.39/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.39/1.03  --inst_passive_queues_freq              [25;2]
% 2.39/1.03  --inst_dismatching                      true
% 2.39/1.03  --inst_eager_unprocessed_to_passive     true
% 2.39/1.03  --inst_prop_sim_given                   true
% 2.39/1.03  --inst_prop_sim_new                     false
% 2.39/1.03  --inst_subs_new                         false
% 2.39/1.03  --inst_eq_res_simp                      false
% 2.39/1.03  --inst_subs_given                       false
% 2.39/1.03  --inst_orphan_elimination               true
% 2.39/1.03  --inst_learning_loop_flag               true
% 2.39/1.03  --inst_learning_start                   3000
% 2.39/1.03  --inst_learning_factor                  2
% 2.39/1.03  --inst_start_prop_sim_after_learn       3
% 2.39/1.03  --inst_sel_renew                        solver
% 2.39/1.03  --inst_lit_activity_flag                true
% 2.39/1.03  --inst_restr_to_given                   false
% 2.39/1.03  --inst_activity_threshold               500
% 2.39/1.03  --inst_out_proof                        true
% 2.39/1.03  
% 2.39/1.03  ------ Resolution Options
% 2.39/1.03  
% 2.39/1.03  --resolution_flag                       false
% 2.39/1.03  --res_lit_sel                           adaptive
% 2.39/1.03  --res_lit_sel_side                      none
% 2.39/1.03  --res_ordering                          kbo
% 2.39/1.03  --res_to_prop_solver                    active
% 2.39/1.03  --res_prop_simpl_new                    false
% 2.39/1.03  --res_prop_simpl_given                  true
% 2.39/1.03  --res_passive_queue_type                priority_queues
% 2.39/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.39/1.03  --res_passive_queues_freq               [15;5]
% 2.39/1.03  --res_forward_subs                      full
% 2.39/1.03  --res_backward_subs                     full
% 2.39/1.03  --res_forward_subs_resolution           true
% 2.39/1.03  --res_backward_subs_resolution          true
% 2.39/1.03  --res_orphan_elimination                true
% 2.39/1.03  --res_time_limit                        2.
% 2.39/1.03  --res_out_proof                         true
% 2.39/1.03  
% 2.39/1.03  ------ Superposition Options
% 2.39/1.03  
% 2.39/1.03  --superposition_flag                    true
% 2.39/1.03  --sup_passive_queue_type                priority_queues
% 2.39/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.39/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.39/1.03  --demod_completeness_check              fast
% 2.39/1.03  --demod_use_ground                      true
% 2.39/1.03  --sup_to_prop_solver                    passive
% 2.39/1.03  --sup_prop_simpl_new                    true
% 2.39/1.03  --sup_prop_simpl_given                  true
% 2.39/1.03  --sup_fun_splitting                     false
% 2.39/1.03  --sup_smt_interval                      50000
% 2.39/1.03  
% 2.39/1.03  ------ Superposition Simplification Setup
% 2.39/1.03  
% 2.39/1.03  --sup_indices_passive                   []
% 2.39/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.39/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.39/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.39/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.39/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.39/1.03  --sup_full_bw                           [BwDemod]
% 2.39/1.03  --sup_immed_triv                        [TrivRules]
% 2.39/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.39/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.39/1.03  --sup_immed_bw_main                     []
% 2.39/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.39/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.39/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.39/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.39/1.03  
% 2.39/1.03  ------ Combination Options
% 2.39/1.03  
% 2.39/1.03  --comb_res_mult                         3
% 2.39/1.03  --comb_sup_mult                         2
% 2.39/1.03  --comb_inst_mult                        10
% 2.39/1.03  
% 2.39/1.03  ------ Debug Options
% 2.39/1.03  
% 2.39/1.03  --dbg_backtrace                         false
% 2.39/1.03  --dbg_dump_prop_clauses                 false
% 2.39/1.03  --dbg_dump_prop_clauses_file            -
% 2.39/1.03  --dbg_out_stat                          false
% 2.39/1.03  
% 2.39/1.03  
% 2.39/1.03  
% 2.39/1.03  
% 2.39/1.03  ------ Proving...
% 2.39/1.03  
% 2.39/1.03  
% 2.39/1.03  % SZS status Theorem for theBenchmark.p
% 2.39/1.03  
% 2.39/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 2.39/1.03  
% 2.39/1.03  fof(f6,axiom,(
% 2.39/1.03    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.39/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.39/1.03  
% 2.39/1.03  fof(f51,plain,(
% 2.39/1.03    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.39/1.03    inference(cnf_transformation,[],[f6])).
% 2.39/1.03  
% 2.39/1.03  fof(f13,axiom,(
% 2.39/1.03    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 2.39/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.39/1.03  
% 2.39/1.03  fof(f22,plain,(
% 2.39/1.03    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 2.39/1.03    inference(ennf_transformation,[],[f13])).
% 2.39/1.03  
% 2.39/1.03  fof(f23,plain,(
% 2.39/1.03    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.39/1.03    inference(flattening,[],[f22])).
% 2.39/1.03  
% 2.39/1.03  fof(f58,plain,(
% 2.39/1.03    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.39/1.03    inference(cnf_transformation,[],[f23])).
% 2.39/1.03  
% 2.39/1.03  fof(f14,conjecture,(
% 2.39/1.03    ! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (~v1_xboole_0(k3_xboole_0(X0,X1)) => r1_tarski(X0,X1)))),
% 2.39/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.39/1.03  
% 2.39/1.03  fof(f15,negated_conjecture,(
% 2.39/1.03    ~! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (~v1_xboole_0(k3_xboole_0(X0,X1)) => r1_tarski(X0,X1)))),
% 2.39/1.03    inference(negated_conjecture,[],[f14])).
% 2.39/1.03  
% 2.39/1.03  fof(f24,plain,(
% 2.39/1.03    ? [X0] : (? [X1] : (~r1_tarski(X0,X1) & ~v1_xboole_0(k3_xboole_0(X0,X1))) & (v1_zfmisc_1(X0) & ~v1_xboole_0(X0)))),
% 2.39/1.03    inference(ennf_transformation,[],[f15])).
% 2.39/1.03  
% 2.39/1.03  fof(f25,plain,(
% 2.39/1.03    ? [X0] : (? [X1] : (~r1_tarski(X0,X1) & ~v1_xboole_0(k3_xboole_0(X0,X1))) & v1_zfmisc_1(X0) & ~v1_xboole_0(X0))),
% 2.39/1.03    inference(flattening,[],[f24])).
% 2.39/1.03  
% 2.39/1.03  fof(f38,plain,(
% 2.39/1.03    ( ! [X0] : (? [X1] : (~r1_tarski(X0,X1) & ~v1_xboole_0(k3_xboole_0(X0,X1))) => (~r1_tarski(X0,sK3) & ~v1_xboole_0(k3_xboole_0(X0,sK3)))) )),
% 2.39/1.03    introduced(choice_axiom,[])).
% 2.39/1.03  
% 2.39/1.03  fof(f37,plain,(
% 2.39/1.03    ? [X0] : (? [X1] : (~r1_tarski(X0,X1) & ~v1_xboole_0(k3_xboole_0(X0,X1))) & v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => (? [X1] : (~r1_tarski(sK2,X1) & ~v1_xboole_0(k3_xboole_0(sK2,X1))) & v1_zfmisc_1(sK2) & ~v1_xboole_0(sK2))),
% 2.39/1.03    introduced(choice_axiom,[])).
% 2.39/1.03  
% 2.39/1.03  fof(f39,plain,(
% 2.39/1.03    (~r1_tarski(sK2,sK3) & ~v1_xboole_0(k3_xboole_0(sK2,sK3))) & v1_zfmisc_1(sK2) & ~v1_xboole_0(sK2)),
% 2.39/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f25,f38,f37])).
% 2.39/1.03  
% 2.39/1.03  fof(f60,plain,(
% 2.39/1.03    v1_zfmisc_1(sK2)),
% 2.39/1.03    inference(cnf_transformation,[],[f39])).
% 2.39/1.03  
% 2.39/1.03  fof(f59,plain,(
% 2.39/1.03    ~v1_xboole_0(sK2)),
% 2.39/1.03    inference(cnf_transformation,[],[f39])).
% 2.39/1.03  
% 2.39/1.03  fof(f2,axiom,(
% 2.39/1.03    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.39/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.39/1.03  
% 2.39/1.03  fof(f17,plain,(
% 2.39/1.03    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.39/1.03    inference(ennf_transformation,[],[f2])).
% 2.39/1.03  
% 2.39/1.03  fof(f30,plain,(
% 2.39/1.03    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.39/1.03    inference(nnf_transformation,[],[f17])).
% 2.39/1.03  
% 2.39/1.03  fof(f31,plain,(
% 2.39/1.03    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.39/1.03    inference(rectify,[],[f30])).
% 2.39/1.03  
% 2.39/1.03  fof(f32,plain,(
% 2.39/1.03    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 2.39/1.03    introduced(choice_axiom,[])).
% 2.39/1.03  
% 2.39/1.03  fof(f33,plain,(
% 2.39/1.03    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.39/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f32])).
% 2.39/1.03  
% 2.39/1.03  fof(f43,plain,(
% 2.39/1.03    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 2.39/1.03    inference(cnf_transformation,[],[f33])).
% 2.39/1.03  
% 2.39/1.03  fof(f1,axiom,(
% 2.39/1.03    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.39/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.39/1.03  
% 2.39/1.03  fof(f26,plain,(
% 2.39/1.03    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.39/1.03    inference(nnf_transformation,[],[f1])).
% 2.39/1.03  
% 2.39/1.03  fof(f27,plain,(
% 2.39/1.03    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.39/1.03    inference(rectify,[],[f26])).
% 2.39/1.03  
% 2.39/1.03  fof(f28,plain,(
% 2.39/1.03    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.39/1.03    introduced(choice_axiom,[])).
% 2.39/1.03  
% 2.39/1.03  fof(f29,plain,(
% 2.39/1.03    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.39/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).
% 2.39/1.03  
% 2.39/1.03  fof(f40,plain,(
% 2.39/1.03    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 2.39/1.03    inference(cnf_transformation,[],[f29])).
% 2.39/1.03  
% 2.39/1.03  fof(f7,axiom,(
% 2.39/1.03    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 2.39/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.39/1.03  
% 2.39/1.03  fof(f19,plain,(
% 2.39/1.03    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 2.39/1.03    inference(ennf_transformation,[],[f7])).
% 2.39/1.03  
% 2.39/1.03  fof(f52,plain,(
% 2.39/1.03    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 2.39/1.03    inference(cnf_transformation,[],[f19])).
% 2.39/1.03  
% 2.39/1.03  fof(f12,axiom,(
% 2.39/1.03    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.39/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.39/1.03  
% 2.39/1.03  fof(f57,plain,(
% 2.39/1.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.39/1.03    inference(cnf_transformation,[],[f12])).
% 2.39/1.03  
% 2.39/1.03  fof(f8,axiom,(
% 2.39/1.03    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.39/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.39/1.03  
% 2.39/1.03  fof(f53,plain,(
% 2.39/1.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.39/1.03    inference(cnf_transformation,[],[f8])).
% 2.39/1.03  
% 2.39/1.03  fof(f11,axiom,(
% 2.39/1.03    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.39/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.39/1.03  
% 2.39/1.03  fof(f56,plain,(
% 2.39/1.03    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.39/1.03    inference(cnf_transformation,[],[f11])).
% 2.39/1.03  
% 2.39/1.03  fof(f64,plain,(
% 2.39/1.03    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 2.39/1.03    inference(definition_unfolding,[],[f57,f53,f56])).
% 2.39/1.03  
% 2.39/1.03  fof(f61,plain,(
% 2.39/1.03    ~v1_xboole_0(k3_xboole_0(sK2,sK3))),
% 2.39/1.03    inference(cnf_transformation,[],[f39])).
% 2.39/1.03  
% 2.39/1.03  fof(f65,plain,(
% 2.39/1.03    ~v1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))),
% 2.39/1.03    inference(definition_unfolding,[],[f61,f53])).
% 2.39/1.03  
% 2.39/1.03  fof(f4,axiom,(
% 2.39/1.03    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.39/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.39/1.03  
% 2.39/1.03  fof(f34,plain,(
% 2.39/1.03    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.39/1.03    inference(nnf_transformation,[],[f4])).
% 2.39/1.03  
% 2.39/1.03  fof(f35,plain,(
% 2.39/1.03    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.39/1.03    inference(flattening,[],[f34])).
% 2.39/1.03  
% 2.39/1.03  fof(f47,plain,(
% 2.39/1.03    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.39/1.03    inference(cnf_transformation,[],[f35])).
% 2.39/1.03  
% 2.39/1.03  fof(f66,plain,(
% 2.39/1.03    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.39/1.03    inference(equality_resolution,[],[f47])).
% 2.39/1.03  
% 2.39/1.03  fof(f5,axiom,(
% 2.39/1.03    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 2.39/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.39/1.03  
% 2.39/1.03  fof(f36,plain,(
% 2.39/1.03    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 2.39/1.03    inference(nnf_transformation,[],[f5])).
% 2.39/1.03  
% 2.39/1.03  fof(f50,plain,(
% 2.39/1.03    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 2.39/1.03    inference(cnf_transformation,[],[f36])).
% 2.39/1.03  
% 2.39/1.03  fof(f9,axiom,(
% 2.39/1.03    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 2.39/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.39/1.03  
% 2.39/1.03  fof(f54,plain,(
% 2.39/1.03    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 2.39/1.03    inference(cnf_transformation,[],[f9])).
% 2.39/1.03  
% 2.39/1.03  fof(f49,plain,(
% 2.39/1.03    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 2.39/1.03    inference(cnf_transformation,[],[f36])).
% 2.39/1.03  
% 2.39/1.03  fof(f3,axiom,(
% 2.39/1.03    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 2.39/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.39/1.03  
% 2.39/1.03  fof(f16,plain,(
% 2.39/1.03    ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 => r1_xboole_0(X0,X1))),
% 2.39/1.03    inference(unused_predicate_definition_removal,[],[f3])).
% 2.39/1.03  
% 2.39/1.03  fof(f18,plain,(
% 2.39/1.03    ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0)),
% 2.39/1.03    inference(ennf_transformation,[],[f16])).
% 2.39/1.03  
% 2.39/1.03  fof(f45,plain,(
% 2.39/1.03    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 2.39/1.03    inference(cnf_transformation,[],[f18])).
% 2.39/1.03  
% 2.39/1.03  fof(f63,plain,(
% 2.39/1.03    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.39/1.03    inference(definition_unfolding,[],[f45,f53])).
% 2.39/1.03  
% 2.39/1.03  fof(f10,axiom,(
% 2.39/1.03    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 2.39/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.39/1.03  
% 2.39/1.03  fof(f20,plain,(
% 2.39/1.03    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 2.39/1.03    inference(ennf_transformation,[],[f10])).
% 2.39/1.03  
% 2.39/1.03  fof(f21,plain,(
% 2.39/1.03    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 2.39/1.03    inference(flattening,[],[f20])).
% 2.39/1.03  
% 2.39/1.03  fof(f55,plain,(
% 2.39/1.03    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 2.39/1.03    inference(cnf_transformation,[],[f21])).
% 2.39/1.03  
% 2.39/1.03  fof(f62,plain,(
% 2.39/1.03    ~r1_tarski(sK2,sK3)),
% 2.39/1.03    inference(cnf_transformation,[],[f39])).
% 2.39/1.03  
% 2.39/1.03  cnf(c_11,plain,
% 2.39/1.03      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 2.39/1.03      inference(cnf_transformation,[],[f51]) ).
% 2.39/1.03  
% 2.39/1.03  cnf(c_1017,plain,
% 2.39/1.03      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 2.39/1.03      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.39/1.03  
% 2.39/1.03  cnf(c_16,plain,
% 2.39/1.03      ( ~ r1_tarski(X0,X1)
% 2.39/1.03      | ~ v1_zfmisc_1(X1)
% 2.39/1.03      | v1_xboole_0(X0)
% 2.39/1.03      | v1_xboole_0(X1)
% 2.39/1.03      | X1 = X0 ),
% 2.39/1.03      inference(cnf_transformation,[],[f58]) ).
% 2.39/1.03  
% 2.39/1.03  cnf(c_19,negated_conjecture,
% 2.39/1.03      ( v1_zfmisc_1(sK2) ),
% 2.39/1.03      inference(cnf_transformation,[],[f60]) ).
% 2.39/1.03  
% 2.39/1.03  cnf(c_259,plain,
% 2.39/1.03      ( ~ r1_tarski(X0,X1)
% 2.39/1.03      | v1_xboole_0(X0)
% 2.39/1.03      | v1_xboole_0(X1)
% 2.39/1.03      | X1 = X0
% 2.39/1.03      | sK2 != X1 ),
% 2.39/1.03      inference(resolution_lifted,[status(thm)],[c_16,c_19]) ).
% 2.39/1.03  
% 2.39/1.03  cnf(c_260,plain,
% 2.39/1.03      ( ~ r1_tarski(X0,sK2)
% 2.39/1.03      | v1_xboole_0(X0)
% 2.39/1.03      | v1_xboole_0(sK2)
% 2.39/1.03      | sK2 = X0 ),
% 2.39/1.03      inference(unflattening,[status(thm)],[c_259]) ).
% 2.39/1.03  
% 2.39/1.03  cnf(c_20,negated_conjecture,
% 2.39/1.03      ( ~ v1_xboole_0(sK2) ),
% 2.39/1.03      inference(cnf_transformation,[],[f59]) ).
% 2.39/1.03  
% 2.39/1.03  cnf(c_264,plain,
% 2.39/1.03      ( v1_xboole_0(X0) | ~ r1_tarski(X0,sK2) | sK2 = X0 ),
% 2.39/1.03      inference(global_propositional_subsumption,
% 2.39/1.03                [status(thm)],
% 2.39/1.03                [c_260,c_20]) ).
% 2.39/1.03  
% 2.39/1.03  cnf(c_265,plain,
% 2.39/1.03      ( ~ r1_tarski(X0,sK2) | v1_xboole_0(X0) | sK2 = X0 ),
% 2.39/1.03      inference(renaming,[status(thm)],[c_264]) ).
% 2.39/1.03  
% 2.39/1.03  cnf(c_1011,plain,
% 2.39/1.03      ( sK2 = X0
% 2.39/1.03      | r1_tarski(X0,sK2) != iProver_top
% 2.39/1.03      | v1_xboole_0(X0) = iProver_top ),
% 2.39/1.03      inference(predicate_to_equality,[status(thm)],[c_265]) ).
% 2.39/1.03  
% 2.39/1.03  cnf(c_1360,plain,
% 2.39/1.03      ( k4_xboole_0(sK2,X0) = sK2
% 2.39/1.03      | v1_xboole_0(k4_xboole_0(sK2,X0)) = iProver_top ),
% 2.39/1.03      inference(superposition,[status(thm)],[c_1017,c_1011]) ).
% 2.39/1.03  
% 2.39/1.03  cnf(c_3,plain,
% 2.39/1.03      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 2.39/1.03      inference(cnf_transformation,[],[f43]) ).
% 2.39/1.03  
% 2.39/1.03  cnf(c_1023,plain,
% 2.39/1.03      ( r1_tarski(X0,X1) = iProver_top
% 2.39/1.03      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 2.39/1.03      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.39/1.03  
% 2.39/1.03  cnf(c_1,plain,
% 2.39/1.03      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 2.39/1.03      inference(cnf_transformation,[],[f40]) ).
% 2.39/1.03  
% 2.39/1.03  cnf(c_1025,plain,
% 2.39/1.03      ( r2_hidden(X0,X1) != iProver_top
% 2.39/1.03      | v1_xboole_0(X1) != iProver_top ),
% 2.39/1.03      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.39/1.03  
% 2.39/1.03  cnf(c_2429,plain,
% 2.39/1.03      ( r1_tarski(X0,X1) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 2.39/1.03      inference(superposition,[status(thm)],[c_1023,c_1025]) ).
% 2.39/1.03  
% 2.39/1.03  cnf(c_12,plain,
% 2.39/1.03      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 2.39/1.03      inference(cnf_transformation,[],[f52]) ).
% 2.39/1.03  
% 2.39/1.03  cnf(c_1016,plain,
% 2.39/1.03      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 2.39/1.03      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.39/1.03  
% 2.39/1.03  cnf(c_2631,plain,
% 2.39/1.03      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 2.39/1.03      inference(superposition,[status(thm)],[c_2429,c_1016]) ).
% 2.39/1.03  
% 2.39/1.03  cnf(c_2733,plain,
% 2.39/1.03      ( k4_xboole_0(sK2,X0) = sK2 | k4_xboole_0(sK2,X0) = k1_xboole_0 ),
% 2.39/1.03      inference(superposition,[status(thm)],[c_1360,c_2631]) ).
% 2.39/1.03  
% 2.39/1.03  cnf(c_15,plain,
% 2.39/1.03      ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 2.39/1.03      inference(cnf_transformation,[],[f64]) ).
% 2.39/1.03  
% 2.39/1.03  cnf(c_1374,plain,
% 2.39/1.03      ( r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0) = iProver_top ),
% 2.39/1.03      inference(superposition,[status(thm)],[c_15,c_1017]) ).
% 2.39/1.03  
% 2.39/1.03  cnf(c_1531,plain,
% 2.39/1.03      ( k1_setfam_1(k1_enumset1(sK2,sK2,X0)) = sK2
% 2.39/1.03      | v1_xboole_0(k1_setfam_1(k1_enumset1(sK2,sK2,X0))) = iProver_top ),
% 2.39/1.03      inference(superposition,[status(thm)],[c_1374,c_1011]) ).
% 2.39/1.03  
% 2.39/1.03  cnf(c_18,negated_conjecture,
% 2.39/1.03      ( ~ v1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) ),
% 2.39/1.03      inference(cnf_transformation,[],[f65]) ).
% 2.39/1.03  
% 2.39/1.03  cnf(c_1014,plain,
% 2.39/1.03      ( v1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) != iProver_top ),
% 2.39/1.03      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.39/1.03  
% 2.39/1.03  cnf(c_1044,plain,
% 2.39/1.03      ( v1_xboole_0(k1_setfam_1(k1_enumset1(sK2,sK2,sK3))) != iProver_top ),
% 2.39/1.03      inference(demodulation,[status(thm)],[c_15,c_1014]) ).
% 2.39/1.03  
% 2.39/1.03  cnf(c_1779,plain,
% 2.39/1.03      ( k1_setfam_1(k1_enumset1(sK2,sK2,sK3)) = sK2 ),
% 2.39/1.03      inference(superposition,[status(thm)],[c_1531,c_1044]) ).
% 2.39/1.03  
% 2.39/1.03  cnf(c_1373,plain,
% 2.39/1.03      ( k1_setfam_1(k1_enumset1(X0,X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) ),
% 2.39/1.03      inference(superposition,[status(thm)],[c_15,c_15]) ).
% 2.39/1.03  
% 2.39/1.03  cnf(c_3181,plain,
% 2.39/1.03      ( k1_setfam_1(k1_enumset1(sK2,sK2,k4_xboole_0(sK2,sK3))) = k4_xboole_0(sK2,sK2) ),
% 2.39/1.03      inference(superposition,[status(thm)],[c_1779,c_1373]) ).
% 2.39/1.03  
% 2.39/1.03  cnf(c_7,plain,
% 2.39/1.03      ( r1_tarski(X0,X0) ),
% 2.39/1.03      inference(cnf_transformation,[],[f66]) ).
% 2.39/1.03  
% 2.39/1.03  cnf(c_1020,plain,
% 2.39/1.03      ( r1_tarski(X0,X0) = iProver_top ),
% 2.39/1.03      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.39/1.03  
% 2.39/1.03  cnf(c_9,plain,
% 2.39/1.03      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 2.39/1.03      inference(cnf_transformation,[],[f50]) ).
% 2.39/1.03  
% 2.39/1.03  cnf(c_1019,plain,
% 2.39/1.03      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 2.39/1.03      | r1_tarski(X0,X1) != iProver_top ),
% 2.39/1.03      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.39/1.03  
% 2.39/1.03  cnf(c_2113,plain,
% 2.39/1.03      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 2.39/1.03      inference(superposition,[status(thm)],[c_1020,c_1019]) ).
% 2.39/1.03  
% 2.39/1.03  cnf(c_3219,plain,
% 2.39/1.03      ( k1_setfam_1(k1_enumset1(sK2,sK2,k4_xboole_0(sK2,sK3))) = k1_xboole_0 ),
% 2.39/1.03      inference(demodulation,[status(thm)],[c_3181,c_2113]) ).
% 2.39/1.03  
% 2.39/1.03  cnf(c_3483,plain,
% 2.39/1.03      ( k4_xboole_0(sK2,sK3) = k1_xboole_0
% 2.39/1.03      | k1_setfam_1(k1_enumset1(sK2,sK2,sK2)) = k1_xboole_0 ),
% 2.39/1.03      inference(superposition,[status(thm)],[c_2733,c_3219]) ).
% 2.39/1.03  
% 2.39/1.03  cnf(c_2127,plain,
% 2.39/1.03      ( k1_setfam_1(k1_enumset1(X0,X0,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
% 2.39/1.03      inference(superposition,[status(thm)],[c_2113,c_15]) ).
% 2.39/1.03  
% 2.39/1.03  cnf(c_3503,plain,
% 2.39/1.03      ( k4_xboole_0(sK2,sK3) = k1_xboole_0
% 2.39/1.03      | k4_xboole_0(sK2,k1_xboole_0) = k1_xboole_0 ),
% 2.39/1.03      inference(demodulation,[status(thm)],[c_3483,c_2127]) ).
% 2.39/1.03  
% 2.39/1.03  cnf(c_633,plain,
% 2.39/1.03      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.39/1.03      theory(equality) ).
% 2.39/1.03  
% 2.39/1.03  cnf(c_1297,plain,
% 2.39/1.03      ( ~ r1_tarski(X0,X1)
% 2.39/1.03      | r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),X2)
% 2.39/1.03      | X2 != X1
% 2.39/1.03      | k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) != X0 ),
% 2.39/1.03      inference(instantiation,[status(thm)],[c_633]) ).
% 2.39/1.03  
% 2.39/1.03  cnf(c_2328,plain,
% 2.39/1.03      ( r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),X0)
% 2.39/1.03      | ~ r1_tarski(sK2,X1)
% 2.39/1.03      | X0 != X1
% 2.39/1.03      | k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) != sK2 ),
% 2.39/1.03      inference(instantiation,[status(thm)],[c_1297]) ).
% 2.39/1.03  
% 2.39/1.03  cnf(c_2331,plain,
% 2.39/1.03      ( r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k1_xboole_0)
% 2.39/1.03      | ~ r1_tarski(sK2,k1_xboole_0)
% 2.39/1.03      | k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) != sK2
% 2.39/1.03      | k1_xboole_0 != k1_xboole_0 ),
% 2.39/1.03      inference(instantiation,[status(thm)],[c_2328]) ).
% 2.39/1.03  
% 2.39/1.03  cnf(c_630,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.39/1.03  
% 2.39/1.03  cnf(c_1229,plain,
% 2.39/1.03      ( X0 != X1
% 2.39/1.03      | k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) != X1
% 2.39/1.03      | k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = X0 ),
% 2.39/1.03      inference(instantiation,[status(thm)],[c_630]) ).
% 2.39/1.03  
% 2.39/1.03  cnf(c_1543,plain,
% 2.39/1.03      ( X0 != k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))
% 2.39/1.03      | k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = X0
% 2.39/1.03      | k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) != k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
% 2.39/1.03      inference(instantiation,[status(thm)],[c_1229]) ).
% 2.39/1.03  
% 2.39/1.03  cnf(c_1977,plain,
% 2.39/1.03      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) != k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))
% 2.39/1.03      | k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = sK2
% 2.39/1.03      | sK2 != k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
% 2.39/1.03      inference(instantiation,[status(thm)],[c_1543]) ).
% 2.39/1.03  
% 2.39/1.03  cnf(c_1967,plain,
% 2.39/1.03      ( ~ r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k1_xboole_0)
% 2.39/1.03      | k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
% 2.39/1.03      inference(instantiation,[status(thm)],[c_12]) ).
% 2.39/1.03  
% 2.39/1.03  cnf(c_629,plain,( X0 = X0 ),theory(equality) ).
% 2.39/1.03  
% 2.39/1.03  cnf(c_1544,plain,
% 2.39/1.03      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
% 2.39/1.03      inference(instantiation,[status(thm)],[c_629]) ).
% 2.39/1.03  
% 2.39/1.03  cnf(c_1545,plain,
% 2.39/1.03      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) != k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))
% 2.39/1.03      | k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = k1_xboole_0
% 2.39/1.03      | k1_xboole_0 != k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
% 2.39/1.03      inference(instantiation,[status(thm)],[c_1543]) ).
% 2.39/1.03  
% 2.39/1.03  cnf(c_13,plain,
% 2.39/1.03      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.39/1.03      inference(cnf_transformation,[],[f54]) ).
% 2.39/1.03  
% 2.39/1.03  cnf(c_1375,plain,
% 2.39/1.03      ( k1_setfam_1(k1_enumset1(k1_xboole_0,k1_xboole_0,X0)) = k1_xboole_0 ),
% 2.39/1.03      inference(superposition,[status(thm)],[c_15,c_13]) ).
% 2.39/1.03  
% 2.39/1.03  cnf(c_1384,plain,
% 2.39/1.03      ( k1_setfam_1(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
% 2.39/1.03      inference(instantiation,[status(thm)],[c_1375]) ).
% 2.39/1.03  
% 2.39/1.03  cnf(c_10,plain,
% 2.39/1.03      ( r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0 ),
% 2.39/1.03      inference(cnf_transformation,[],[f49]) ).
% 2.39/1.03  
% 2.39/1.03  cnf(c_1304,plain,
% 2.39/1.03      ( r1_tarski(sK2,X0) | k4_xboole_0(sK2,X0) != k1_xboole_0 ),
% 2.39/1.03      inference(instantiation,[status(thm)],[c_10]) ).
% 2.39/1.03  
% 2.39/1.03  cnf(c_1306,plain,
% 2.39/1.03      ( r1_tarski(sK2,k1_xboole_0)
% 2.39/1.03      | k4_xboole_0(sK2,k1_xboole_0) != k1_xboole_0 ),
% 2.39/1.03      inference(instantiation,[status(thm)],[c_1304]) ).
% 2.39/1.03  
% 2.39/1.03  cnf(c_631,plain,
% 2.39/1.03      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 2.39/1.03      theory(equality) ).
% 2.39/1.03  
% 2.39/1.03  cnf(c_1153,plain,
% 2.39/1.03      ( ~ v1_xboole_0(X0)
% 2.39/1.03      | v1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
% 2.39/1.03      | k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) != X0 ),
% 2.39/1.03      inference(instantiation,[status(thm)],[c_631]) ).
% 2.39/1.03  
% 2.39/1.03  cnf(c_1155,plain,
% 2.39/1.03      ( v1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
% 2.39/1.03      | ~ v1_xboole_0(k1_xboole_0)
% 2.39/1.03      | k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) != k1_xboole_0 ),
% 2.39/1.03      inference(instantiation,[status(thm)],[c_1153]) ).
% 2.39/1.03  
% 2.39/1.03  cnf(c_1150,plain,
% 2.39/1.03      ( r1_tarski(sK2,sK3) | k4_xboole_0(sK2,sK3) != k1_xboole_0 ),
% 2.39/1.03      inference(instantiation,[status(thm)],[c_10]) ).
% 2.39/1.03  
% 2.39/1.03  cnf(c_5,plain,
% 2.39/1.03      ( r1_xboole_0(X0,X1)
% 2.39/1.03      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
% 2.39/1.03      inference(cnf_transformation,[],[f63]) ).
% 2.39/1.03  
% 2.39/1.03  cnf(c_14,plain,
% 2.39/1.03      ( ~ r1_xboole_0(X0,X1) | ~ r1_tarski(X0,X1) | v1_xboole_0(X0) ),
% 2.39/1.03      inference(cnf_transformation,[],[f55]) ).
% 2.39/1.03  
% 2.39/1.03  cnf(c_241,plain,
% 2.39/1.03      ( ~ r1_tarski(X0,X1)
% 2.39/1.03      | v1_xboole_0(X0)
% 2.39/1.03      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
% 2.39/1.03      inference(resolution,[status(thm)],[c_5,c_14]) ).
% 2.39/1.03  
% 2.39/1.03  cnf(c_1012,plain,
% 2.39/1.03      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
% 2.39/1.03      | r1_tarski(X0,X1) != iProver_top
% 2.39/1.03      | v1_xboole_0(X0) = iProver_top ),
% 2.39/1.03      inference(predicate_to_equality,[status(thm)],[c_241]) ).
% 2.39/1.03  
% 2.39/1.03  cnf(c_1090,plain,
% 2.39/1.03      ( k1_setfam_1(k1_enumset1(X0,X0,X1)) != k1_xboole_0
% 2.39/1.03      | r1_tarski(X0,X1) != iProver_top
% 2.39/1.03      | v1_xboole_0(X0) = iProver_top ),
% 2.39/1.03      inference(light_normalisation,[status(thm)],[c_1012,c_15]) ).
% 2.39/1.03  
% 2.39/1.03  cnf(c_1109,plain,
% 2.39/1.03      ( ~ r1_tarski(X0,X1)
% 2.39/1.03      | v1_xboole_0(X0)
% 2.39/1.03      | k1_setfam_1(k1_enumset1(X0,X0,X1)) != k1_xboole_0 ),
% 2.39/1.03      inference(predicate_to_equality_rev,[status(thm)],[c_1090]) ).
% 2.39/1.03  
% 2.39/1.03  cnf(c_1111,plain,
% 2.39/1.03      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 2.39/1.03      | v1_xboole_0(k1_xboole_0)
% 2.39/1.03      | k1_setfam_1(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) != k1_xboole_0 ),
% 2.39/1.03      inference(instantiation,[status(thm)],[c_1109]) ).
% 2.39/1.03  
% 2.39/1.03  cnf(c_326,plain,
% 2.39/1.03      ( ~ r1_tarski(X0,sK2)
% 2.39/1.03      | k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) != X0
% 2.39/1.03      | sK2 = X0 ),
% 2.39/1.03      inference(resolution_lifted,[status(thm)],[c_265,c_18]) ).
% 2.39/1.03  
% 2.39/1.03  cnf(c_327,plain,
% 2.39/1.03      ( ~ r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),sK2)
% 2.39/1.03      | sK2 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
% 2.39/1.03      inference(unflattening,[status(thm)],[c_326]) ).
% 2.39/1.03  
% 2.39/1.03  cnf(c_333,plain,
% 2.39/1.03      ( sK2 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
% 2.39/1.03      inference(forward_subsumption_resolution,
% 2.39/1.03                [status(thm)],
% 2.39/1.03                [c_327,c_11]) ).
% 2.39/1.03  
% 2.39/1.03  cnf(c_40,plain,
% 2.39/1.03      ( r1_tarski(k1_xboole_0,k1_xboole_0)
% 2.39/1.03      | k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
% 2.39/1.03      inference(instantiation,[status(thm)],[c_10]) ).
% 2.39/1.03  
% 2.39/1.03  cnf(c_34,plain,
% 2.39/1.03      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 2.39/1.03      | k1_xboole_0 = k1_xboole_0 ),
% 2.39/1.03      inference(instantiation,[status(thm)],[c_12]) ).
% 2.39/1.03  
% 2.39/1.03  cnf(c_32,plain,
% 2.39/1.03      ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 2.39/1.03      inference(instantiation,[status(thm)],[c_13]) ).
% 2.39/1.03  
% 2.39/1.03  cnf(c_17,negated_conjecture,
% 2.39/1.03      ( ~ r1_tarski(sK2,sK3) ),
% 2.39/1.03      inference(cnf_transformation,[],[f62]) ).
% 2.39/1.03  
% 2.39/1.03  cnf(contradiction,plain,
% 2.39/1.03      ( $false ),
% 2.39/1.03      inference(minisat,
% 2.39/1.03                [status(thm)],
% 2.39/1.03                [c_3503,c_2331,c_1977,c_1967,c_1544,c_1545,c_1384,c_1306,
% 2.39/1.03                 c_1155,c_1150,c_1111,c_333,c_40,c_34,c_32,c_17,c_18]) ).
% 2.39/1.03  
% 2.39/1.03  
% 2.39/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 2.39/1.03  
% 2.39/1.03  ------                               Statistics
% 2.39/1.03  
% 2.39/1.03  ------ General
% 2.39/1.03  
% 2.39/1.03  abstr_ref_over_cycles:                  0
% 2.39/1.03  abstr_ref_under_cycles:                 0
% 2.39/1.03  gc_basic_clause_elim:                   0
% 2.39/1.03  forced_gc_time:                         0
% 2.39/1.03  parsing_time:                           0.008
% 2.39/1.03  unif_index_cands_time:                  0.
% 2.39/1.03  unif_index_add_time:                    0.
% 2.39/1.03  orderings_time:                         0.
% 2.39/1.03  out_proof_time:                         0.009
% 2.39/1.03  total_time:                             0.118
% 2.39/1.03  num_of_symbols:                         44
% 2.39/1.03  num_of_terms:                           2475
% 2.39/1.03  
% 2.39/1.03  ------ Preprocessing
% 2.39/1.03  
% 2.39/1.03  num_of_splits:                          0
% 2.39/1.03  num_of_split_atoms:                     0
% 2.39/1.03  num_of_reused_defs:                     0
% 2.39/1.03  num_eq_ax_congr_red:                    23
% 2.39/1.03  num_of_sem_filtered_clauses:            1
% 2.39/1.03  num_of_subtypes:                        0
% 2.39/1.03  monotx_restored_types:                  0
% 2.39/1.03  sat_num_of_epr_types:                   0
% 2.39/1.03  sat_num_of_non_cyclic_types:            0
% 2.39/1.03  sat_guarded_non_collapsed_types:        0
% 2.39/1.03  num_pure_diseq_elim:                    0
% 2.39/1.03  simp_replaced_by:                       0
% 2.39/1.03  res_preprocessed:                       89
% 2.39/1.03  prep_upred:                             0
% 2.39/1.03  prep_unflattend:                        19
% 2.39/1.03  smt_new_axioms:                         0
% 2.39/1.03  pred_elim_cands:                        3
% 2.39/1.03  pred_elim:                              2
% 2.39/1.03  pred_elim_cl:                           2
% 2.39/1.03  pred_elim_cycles:                       4
% 2.39/1.03  merged_defs:                            8
% 2.39/1.03  merged_defs_ncl:                        0
% 2.39/1.03  bin_hyper_res:                          8
% 2.39/1.03  prep_cycles:                            4
% 2.39/1.03  pred_elim_time:                         0.003
% 2.39/1.03  splitting_time:                         0.
% 2.39/1.03  sem_filter_time:                        0.
% 2.39/1.03  monotx_time:                            0.
% 2.39/1.03  subtype_inf_time:                       0.
% 2.39/1.03  
% 2.39/1.03  ------ Problem properties
% 2.39/1.03  
% 2.39/1.03  clauses:                                18
% 2.39/1.03  conjectures:                            3
% 2.39/1.03  epr:                                    8
% 2.39/1.03  horn:                                   15
% 2.39/1.03  ground:                                 3
% 2.39/1.03  unary:                                  7
% 2.39/1.03  binary:                                 7
% 2.39/1.03  lits:                                   33
% 2.39/1.03  lits_eq:                                8
% 2.39/1.03  fd_pure:                                0
% 2.39/1.03  fd_pseudo:                              0
% 2.39/1.03  fd_cond:                                2
% 2.39/1.03  fd_pseudo_cond:                         1
% 2.39/1.03  ac_symbols:                             0
% 2.39/1.03  
% 2.39/1.03  ------ Propositional Solver
% 2.39/1.03  
% 2.39/1.03  prop_solver_calls:                      26
% 2.39/1.03  prop_fast_solver_calls:                 459
% 2.39/1.03  smt_solver_calls:                       0
% 2.39/1.03  smt_fast_solver_calls:                  0
% 2.39/1.03  prop_num_of_clauses:                    1114
% 2.39/1.03  prop_preprocess_simplified:             4133
% 2.39/1.03  prop_fo_subsumed:                       5
% 2.39/1.03  prop_solver_time:                       0.
% 2.39/1.03  smt_solver_time:                        0.
% 2.39/1.03  smt_fast_solver_time:                   0.
% 2.39/1.03  prop_fast_solver_time:                  0.
% 2.39/1.03  prop_unsat_core_time:                   0.
% 2.39/1.03  
% 2.39/1.03  ------ QBF
% 2.39/1.03  
% 2.39/1.03  qbf_q_res:                              0
% 2.39/1.03  qbf_num_tautologies:                    0
% 2.39/1.03  qbf_prep_cycles:                        0
% 2.39/1.03  
% 2.39/1.03  ------ BMC1
% 2.39/1.03  
% 2.39/1.03  bmc1_current_bound:                     -1
% 2.39/1.03  bmc1_last_solved_bound:                 -1
% 2.39/1.03  bmc1_unsat_core_size:                   -1
% 2.39/1.03  bmc1_unsat_core_parents_size:           -1
% 2.39/1.03  bmc1_merge_next_fun:                    0
% 2.39/1.03  bmc1_unsat_core_clauses_time:           0.
% 2.39/1.03  
% 2.39/1.03  ------ Instantiation
% 2.39/1.03  
% 2.39/1.03  inst_num_of_clauses:                    377
% 2.39/1.03  inst_num_in_passive:                    61
% 2.39/1.03  inst_num_in_active:                     164
% 2.39/1.03  inst_num_in_unprocessed:                152
% 2.39/1.03  inst_num_of_loops:                      190
% 2.39/1.03  inst_num_of_learning_restarts:          0
% 2.39/1.03  inst_num_moves_active_passive:          25
% 2.39/1.03  inst_lit_activity:                      0
% 2.39/1.03  inst_lit_activity_moves:                0
% 2.39/1.03  inst_num_tautologies:                   0
% 2.39/1.03  inst_num_prop_implied:                  0
% 2.39/1.03  inst_num_existing_simplified:           0
% 2.39/1.03  inst_num_eq_res_simplified:             0
% 2.39/1.03  inst_num_child_elim:                    0
% 2.39/1.03  inst_num_of_dismatching_blockings:      52
% 2.39/1.03  inst_num_of_non_proper_insts:           290
% 2.39/1.03  inst_num_of_duplicates:                 0
% 2.39/1.03  inst_inst_num_from_inst_to_res:         0
% 2.39/1.03  inst_dismatching_checking_time:         0.
% 2.39/1.03  
% 2.39/1.03  ------ Resolution
% 2.39/1.03  
% 2.39/1.03  res_num_of_clauses:                     0
% 2.39/1.03  res_num_in_passive:                     0
% 2.39/1.03  res_num_in_active:                      0
% 2.39/1.03  res_num_of_loops:                       93
% 2.39/1.03  res_forward_subset_subsumed:            113
% 2.39/1.03  res_backward_subset_subsumed:           0
% 2.39/1.03  res_forward_subsumed:                   0
% 2.39/1.03  res_backward_subsumed:                  0
% 2.39/1.03  res_forward_subsumption_resolution:     1
% 2.39/1.03  res_backward_subsumption_resolution:    0
% 2.39/1.03  res_clause_to_clause_subsumption:       237
% 2.39/1.03  res_orphan_elimination:                 0
% 2.39/1.03  res_tautology_del:                      45
% 2.39/1.03  res_num_eq_res_simplified:              0
% 2.39/1.03  res_num_sel_changes:                    0
% 2.39/1.03  res_moves_from_active_to_pass:          0
% 2.39/1.03  
% 2.39/1.03  ------ Superposition
% 2.39/1.03  
% 2.39/1.03  sup_time_total:                         0.
% 2.39/1.03  sup_time_generating:                    0.
% 2.39/1.03  sup_time_sim_full:                      0.
% 2.39/1.03  sup_time_sim_immed:                     0.
% 2.39/1.03  
% 2.39/1.03  sup_num_of_clauses:                     62
% 2.39/1.03  sup_num_in_active:                      37
% 2.39/1.03  sup_num_in_passive:                     25
% 2.39/1.03  sup_num_of_loops:                       37
% 2.39/1.03  sup_fw_superposition:                   80
% 2.39/1.03  sup_bw_superposition:                   71
% 2.39/1.03  sup_immediate_simplified:               77
% 2.39/1.03  sup_given_eliminated:                   0
% 2.39/1.03  comparisons_done:                       0
% 2.39/1.03  comparisons_avoided:                    0
% 2.39/1.03  
% 2.39/1.03  ------ Simplifications
% 2.39/1.03  
% 2.39/1.03  
% 2.39/1.03  sim_fw_subset_subsumed:                 8
% 2.39/1.03  sim_bw_subset_subsumed:                 0
% 2.39/1.03  sim_fw_subsumed:                        37
% 2.39/1.03  sim_bw_subsumed:                        0
% 2.39/1.03  sim_fw_subsumption_res:                 0
% 2.39/1.03  sim_bw_subsumption_res:                 0
% 2.39/1.03  sim_tautology_del:                      3
% 2.39/1.03  sim_eq_tautology_del:                   15
% 2.39/1.03  sim_eq_res_simp:                        0
% 2.39/1.03  sim_fw_demodulated:                     27
% 2.39/1.03  sim_bw_demodulated:                     2
% 2.39/1.03  sim_light_normalised:                   25
% 2.39/1.03  sim_joinable_taut:                      0
% 2.39/1.03  sim_joinable_simp:                      0
% 2.39/1.03  sim_ac_normalised:                      0
% 2.39/1.03  sim_smt_subsumption:                    0
% 2.39/1.03  
%------------------------------------------------------------------------------
