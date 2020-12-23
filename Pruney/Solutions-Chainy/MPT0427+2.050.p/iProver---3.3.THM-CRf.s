%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:42:36 EST 2020

% Result     : Theorem 3.75s
% Output     : CNFRefutation 3.75s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 431 expanded)
%              Number of clauses        :   98 ( 178 expanded)
%              Number of leaves         :   20 (  98 expanded)
%              Depth                    :   18
%              Number of atoms          :  355 (1320 expanded)
%              Number of equality atoms :  179 ( 363 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f25])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( r1_tarski(X1,X2)
           => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( r1_tarski(X1,X2)
             => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f24,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f23])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f24,f31,f30])).

fof(f52,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f51,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(cnf_transformation,[],[f32])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ( k1_xboole_0 = X1
         => k8_setfam_1(X0,X1) = X0 )
        & ( k1_xboole_0 != X1
         => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ( k8_setfam_1(X0,X1) = X0
          | k1_xboole_0 != X1 )
        & ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
          | k1_xboole_0 = X1 ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f50,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(cnf_transformation,[],[f32])).

fof(f53,plain,(
    ~ r1_tarski(k8_setfam_1(sK1,sK3),k8_setfam_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f32])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f54,plain,(
    ! [X0] :
      ( k8_setfam_1(X0,k1_xboole_0) = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f43])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_5,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_6,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) != X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_853,plain,
    ( k4_xboole_0(X0,X1) != X0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1170,plain,
    ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_853])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_857,plain,
    ( r2_hidden(sK0(X0,X1),X1) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_858,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r1_xboole_0(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2746,plain,
    ( r2_hidden(sK0(X0,X1),X2) != iProver_top
    | r1_xboole_0(X2,X1) != iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_857,c_858])).

cnf(c_13584,plain,
    ( r1_xboole_0(X0,X0) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_857,c_2746])).

cnf(c_13594,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1170,c_13584])).

cnf(c_7,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_852,plain,
    ( k4_xboole_0(X0,X1) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_13840,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(superposition,[status(thm)],[c_13594,c_852])).

cnf(c_18,negated_conjecture,
    ( r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_841,plain,
    ( r1_tarski(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_16,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_843,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_855,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1354,plain,
    ( k4_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) = k1_xboole_0
    | k1_xboole_0 = X1
    | r1_tarski(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_843,c_855])).

cnf(c_3282,plain,
    ( k4_xboole_0(k1_setfam_1(sK3),k1_setfam_1(sK2)) = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_841,c_1354])).

cnf(c_4,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_854,plain,
    ( k4_xboole_0(X0,X1) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3440,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(k1_setfam_1(sK3),k1_setfam_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3282,c_854])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_840,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k6_setfam_1(X1,X0) = k8_setfam_1(X1,X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_849,plain,
    ( k6_setfam_1(X0,X1) = k8_setfam_1(X0,X1)
    | k1_xboole_0 = X1
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2647,plain,
    ( k6_setfam_1(sK1,sK3) = k8_setfam_1(sK1,sK3)
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_840,c_849])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k6_setfam_1(X1,X0) = k1_setfam_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_847,plain,
    ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1974,plain,
    ( k6_setfam_1(sK1,sK3) = k1_setfam_1(sK3) ),
    inference(superposition,[status(thm)],[c_840,c_847])).

cnf(c_2656,plain,
    ( k8_setfam_1(sK1,sK3) = k1_setfam_1(sK3)
    | sK3 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2647,c_1974])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_839,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2648,plain,
    ( k6_setfam_1(sK1,sK2) = k8_setfam_1(sK1,sK2)
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_839,c_849])).

cnf(c_1975,plain,
    ( k6_setfam_1(sK1,sK2) = k1_setfam_1(sK2) ),
    inference(superposition,[status(thm)],[c_839,c_847])).

cnf(c_2651,plain,
    ( k8_setfam_1(sK1,sK2) = k1_setfam_1(sK2)
    | sK2 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2648,c_1975])).

cnf(c_17,negated_conjecture,
    ( ~ r1_tarski(k8_setfam_1(sK1,sK3),k8_setfam_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_842,plain,
    ( r1_tarski(k8_setfam_1(sK1,sK3),k8_setfam_1(sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2807,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(k8_setfam_1(sK1,sK3),k1_setfam_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2651,c_842])).

cnf(c_2902,plain,
    ( sK2 = k1_xboole_0
    | sK3 = k1_xboole_0
    | r1_tarski(k1_setfam_1(sK3),k1_setfam_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2656,c_2807])).

cnf(c_3459,plain,
    ( sK2 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3440,c_2902])).

cnf(c_3884,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(k8_setfam_1(sK1,sK3),k8_setfam_1(sK1,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3459,c_842])).

cnf(c_9,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
    | k8_setfam_1(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_850,plain,
    ( k8_setfam_1(X0,k1_xboole_0) = X0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_8,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_851,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_905,plain,
    ( k8_setfam_1(X0,k1_xboole_0) = X0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_850,c_851])).

cnf(c_3893,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(k8_setfam_1(sK1,sK3),sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3884,c_905])).

cnf(c_22,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | m1_subset_1(k8_setfam_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1003,plain,
    ( m1_subset_1(k8_setfam_1(sK1,sK3),k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1004,plain,
    ( m1_subset_1(k8_setfam_1(sK1,sK3),k1_zfmisc_1(sK1)) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1003])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1624,plain,
    ( ~ m1_subset_1(k8_setfam_1(sK1,sK3),k1_zfmisc_1(X0))
    | r1_tarski(k8_setfam_1(sK1,sK3),X0) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_2852,plain,
    ( ~ m1_subset_1(k8_setfam_1(sK1,sK3),k1_zfmisc_1(sK1))
    | r1_tarski(k8_setfam_1(sK1,sK3),sK1) ),
    inference(instantiation,[status(thm)],[c_1624])).

cnf(c_2853,plain,
    ( m1_subset_1(k8_setfam_1(sK1,sK3),k1_zfmisc_1(sK1)) != iProver_top
    | r1_tarski(k8_setfam_1(sK1,sK3),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2852])).

cnf(c_4096,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3893,c_22,c_1004,c_2853])).

cnf(c_1355,plain,
    ( k4_xboole_0(sK2,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_841,c_855])).

cnf(c_4115,plain,
    ( k4_xboole_0(sK2,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4096,c_1355])).

cnf(c_13850,plain,
    ( sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_13840,c_4115])).

cnf(c_361,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1028,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | X0 != X2
    | X1 != k1_zfmisc_1(X3) ),
    inference(instantiation,[status(thm)],[c_361])).

cnf(c_1120,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(X2,k1_zfmisc_1(X3))
    | X2 != X0
    | k1_zfmisc_1(X3) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_1028])).

cnf(c_1407,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(X2,k1_zfmisc_1(k8_setfam_1(sK1,sK2)))
    | X2 != X0
    | k1_zfmisc_1(k8_setfam_1(sK1,sK2)) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_1120])).

cnf(c_2235,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k8_setfam_1(sK1,sK2),k1_zfmisc_1(k8_setfam_1(sK1,sK2)))
    | k8_setfam_1(sK1,sK2) != X0
    | k1_zfmisc_1(k8_setfam_1(sK1,sK2)) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_1407])).

cnf(c_3529,plain,
    ( ~ m1_subset_1(k8_setfam_1(k8_setfam_1(sK1,sK2),k1_xboole_0),k1_zfmisc_1(X0))
    | m1_subset_1(k8_setfam_1(sK1,sK2),k1_zfmisc_1(k8_setfam_1(sK1,sK2)))
    | k8_setfam_1(sK1,sK2) != k8_setfam_1(k8_setfam_1(sK1,sK2),k1_xboole_0)
    | k1_zfmisc_1(k8_setfam_1(sK1,sK2)) != k1_zfmisc_1(X0) ),
    inference(instantiation,[status(thm)],[c_2235])).

cnf(c_11956,plain,
    ( ~ m1_subset_1(k8_setfam_1(k8_setfam_1(sK1,sK2),k1_xboole_0),k1_zfmisc_1(k8_setfam_1(sK1,sK2)))
    | m1_subset_1(k8_setfam_1(sK1,sK2),k1_zfmisc_1(k8_setfam_1(sK1,sK2)))
    | k8_setfam_1(sK1,sK2) != k8_setfam_1(k8_setfam_1(sK1,sK2),k1_xboole_0)
    | k1_zfmisc_1(k8_setfam_1(sK1,sK2)) != k1_zfmisc_1(k8_setfam_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_3529])).

cnf(c_362,plain,
    ( X0 != X1
    | X2 != X3
    | k8_setfam_1(X0,X2) = k8_setfam_1(X1,X3) ),
    theory(equality)).

cnf(c_1182,plain,
    ( k8_setfam_1(sK1,sK3) = k8_setfam_1(X0,X1)
    | sK3 != X1
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_362])).

cnf(c_4959,plain,
    ( k8_setfam_1(sK1,sK3) = k8_setfam_1(sK1,X0)
    | sK3 != X0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1182])).

cnf(c_10831,plain,
    ( k8_setfam_1(sK1,sK3) = k8_setfam_1(sK1,sK2)
    | sK3 != sK2
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_4959])).

cnf(c_356,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1545,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_356])).

cnf(c_10148,plain,
    ( sK2 != X0
    | sK3 != X0
    | sK3 = sK2 ),
    inference(instantiation,[status(thm)],[c_1545])).

cnf(c_10149,plain,
    ( sK2 != k1_xboole_0
    | sK3 = sK2
    | sK3 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_10148])).

cnf(c_359,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1018,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k8_setfam_1(sK1,sK3),k8_setfam_1(sK1,sK2))
    | k8_setfam_1(sK1,sK2) != X1
    | k8_setfam_1(sK1,sK3) != X0 ),
    inference(instantiation,[status(thm)],[c_359])).

cnf(c_1044,plain,
    ( ~ r1_tarski(X0,k8_setfam_1(sK1,sK2))
    | r1_tarski(k8_setfam_1(sK1,sK3),k8_setfam_1(sK1,sK2))
    | k8_setfam_1(sK1,sK2) != k8_setfam_1(sK1,sK2)
    | k8_setfam_1(sK1,sK3) != X0 ),
    inference(instantiation,[status(thm)],[c_1018])).

cnf(c_4873,plain,
    ( ~ r1_tarski(k8_setfam_1(sK1,sK2),k8_setfam_1(sK1,sK2))
    | r1_tarski(k8_setfam_1(sK1,sK3),k8_setfam_1(sK1,sK2))
    | k8_setfam_1(sK1,sK2) != k8_setfam_1(sK1,sK2)
    | k8_setfam_1(sK1,sK3) != k8_setfam_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1044])).

cnf(c_360,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_3243,plain,
    ( k8_setfam_1(sK1,sK2) != k8_setfam_1(sK1,sK2)
    | k1_zfmisc_1(k8_setfam_1(sK1,sK2)) = k1_zfmisc_1(k8_setfam_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_360])).

cnf(c_355,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1963,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_355])).

cnf(c_1137,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k8_setfam_1(sK1,sK2)))
    | r1_tarski(X0,k8_setfam_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1831,plain,
    ( ~ m1_subset_1(k8_setfam_1(sK1,sK2),k1_zfmisc_1(k8_setfam_1(sK1,sK2)))
    | r1_tarski(k8_setfam_1(sK1,sK2),k8_setfam_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_1137])).

cnf(c_993,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1613,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k8_setfam_1(sK1,sK2)))) ),
    inference(instantiation,[status(thm)],[c_993])).

cnf(c_1429,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k8_setfam_1(sK1,sK2))))
    | k8_setfam_1(k8_setfam_1(sK1,sK2),k1_xboole_0) = k8_setfam_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1050,plain,
    ( X0 != X1
    | k8_setfam_1(sK1,sK2) != X1
    | k8_setfam_1(sK1,sK2) = X0 ),
    inference(instantiation,[status(thm)],[c_356])).

cnf(c_1157,plain,
    ( X0 != k8_setfam_1(sK1,sK2)
    | k8_setfam_1(sK1,sK2) = X0
    | k8_setfam_1(sK1,sK2) != k8_setfam_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1050])).

cnf(c_1428,plain,
    ( k8_setfam_1(k8_setfam_1(sK1,sK2),k1_xboole_0) != k8_setfam_1(sK1,sK2)
    | k8_setfam_1(sK1,sK2) = k8_setfam_1(k8_setfam_1(sK1,sK2),k1_xboole_0)
    | k8_setfam_1(sK1,sK2) != k8_setfam_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1157])).

cnf(c_1388,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(k8_setfam_1(sK1,sK2))))
    | m1_subset_1(k8_setfam_1(k8_setfam_1(sK1,sK2),X0),k1_zfmisc_1(k8_setfam_1(sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1394,plain,
    ( m1_subset_1(k8_setfam_1(k8_setfam_1(sK1,sK2),k1_xboole_0),k1_zfmisc_1(k8_setfam_1(sK1,sK2)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k8_setfam_1(sK1,sK2)))) ),
    inference(instantiation,[status(thm)],[c_1388])).

cnf(c_1045,plain,
    ( k8_setfam_1(sK1,sK2) = k8_setfam_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_355])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13850,c_11956,c_10831,c_10149,c_4873,c_3893,c_3243,c_2853,c_1963,c_1831,c_1613,c_1429,c_1428,c_1394,c_1045,c_1004,c_17,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:40:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.75/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.75/1.01  
% 3.75/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.75/1.01  
% 3.75/1.01  ------  iProver source info
% 3.75/1.01  
% 3.75/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.75/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.75/1.01  git: non_committed_changes: false
% 3.75/1.01  git: last_make_outside_of_git: false
% 3.75/1.01  
% 3.75/1.01  ------ 
% 3.75/1.01  
% 3.75/1.01  ------ Input Options
% 3.75/1.01  
% 3.75/1.01  --out_options                           all
% 3.75/1.01  --tptp_safe_out                         true
% 3.75/1.01  --problem_path                          ""
% 3.75/1.01  --include_path                          ""
% 3.75/1.01  --clausifier                            res/vclausify_rel
% 3.75/1.01  --clausifier_options                    --mode clausify
% 3.75/1.01  --stdin                                 false
% 3.75/1.01  --stats_out                             all
% 3.75/1.01  
% 3.75/1.01  ------ General Options
% 3.75/1.01  
% 3.75/1.01  --fof                                   false
% 3.75/1.01  --time_out_real                         305.
% 3.75/1.01  --time_out_virtual                      -1.
% 3.75/1.01  --symbol_type_check                     false
% 3.75/1.01  --clausify_out                          false
% 3.75/1.01  --sig_cnt_out                           false
% 3.75/1.01  --trig_cnt_out                          false
% 3.75/1.01  --trig_cnt_out_tolerance                1.
% 3.75/1.01  --trig_cnt_out_sk_spl                   false
% 3.75/1.01  --abstr_cl_out                          false
% 3.75/1.01  
% 3.75/1.01  ------ Global Options
% 3.75/1.01  
% 3.75/1.01  --schedule                              default
% 3.75/1.01  --add_important_lit                     false
% 3.75/1.01  --prop_solver_per_cl                    1000
% 3.75/1.01  --min_unsat_core                        false
% 3.75/1.01  --soft_assumptions                      false
% 3.75/1.01  --soft_lemma_size                       3
% 3.75/1.01  --prop_impl_unit_size                   0
% 3.75/1.01  --prop_impl_unit                        []
% 3.75/1.01  --share_sel_clauses                     true
% 3.75/1.01  --reset_solvers                         false
% 3.75/1.01  --bc_imp_inh                            [conj_cone]
% 3.75/1.01  --conj_cone_tolerance                   3.
% 3.75/1.01  --extra_neg_conj                        none
% 3.75/1.01  --large_theory_mode                     true
% 3.75/1.01  --prolific_symb_bound                   200
% 3.75/1.01  --lt_threshold                          2000
% 3.75/1.01  --clause_weak_htbl                      true
% 3.75/1.01  --gc_record_bc_elim                     false
% 3.75/1.01  
% 3.75/1.01  ------ Preprocessing Options
% 3.75/1.01  
% 3.75/1.01  --preprocessing_flag                    true
% 3.75/1.01  --time_out_prep_mult                    0.1
% 3.75/1.01  --splitting_mode                        input
% 3.75/1.01  --splitting_grd                         true
% 3.75/1.01  --splitting_cvd                         false
% 3.75/1.01  --splitting_cvd_svl                     false
% 3.75/1.01  --splitting_nvd                         32
% 3.75/1.01  --sub_typing                            true
% 3.75/1.01  --prep_gs_sim                           true
% 3.75/1.01  --prep_unflatten                        true
% 3.75/1.01  --prep_res_sim                          true
% 3.75/1.01  --prep_upred                            true
% 3.75/1.01  --prep_sem_filter                       exhaustive
% 3.75/1.01  --prep_sem_filter_out                   false
% 3.75/1.01  --pred_elim                             true
% 3.75/1.01  --res_sim_input                         true
% 3.75/1.01  --eq_ax_congr_red                       true
% 3.75/1.01  --pure_diseq_elim                       true
% 3.75/1.01  --brand_transform                       false
% 3.75/1.01  --non_eq_to_eq                          false
% 3.75/1.01  --prep_def_merge                        true
% 3.75/1.01  --prep_def_merge_prop_impl              false
% 3.75/1.01  --prep_def_merge_mbd                    true
% 3.75/1.01  --prep_def_merge_tr_red                 false
% 3.75/1.01  --prep_def_merge_tr_cl                  false
% 3.75/1.01  --smt_preprocessing                     true
% 3.75/1.01  --smt_ac_axioms                         fast
% 3.75/1.01  --preprocessed_out                      false
% 3.75/1.01  --preprocessed_stats                    false
% 3.75/1.01  
% 3.75/1.01  ------ Abstraction refinement Options
% 3.75/1.01  
% 3.75/1.01  --abstr_ref                             []
% 3.75/1.01  --abstr_ref_prep                        false
% 3.75/1.01  --abstr_ref_until_sat                   false
% 3.75/1.01  --abstr_ref_sig_restrict                funpre
% 3.75/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.75/1.01  --abstr_ref_under                       []
% 3.75/1.01  
% 3.75/1.01  ------ SAT Options
% 3.75/1.01  
% 3.75/1.01  --sat_mode                              false
% 3.75/1.01  --sat_fm_restart_options                ""
% 3.75/1.01  --sat_gr_def                            false
% 3.75/1.01  --sat_epr_types                         true
% 3.75/1.01  --sat_non_cyclic_types                  false
% 3.75/1.01  --sat_finite_models                     false
% 3.75/1.01  --sat_fm_lemmas                         false
% 3.75/1.01  --sat_fm_prep                           false
% 3.75/1.01  --sat_fm_uc_incr                        true
% 3.75/1.01  --sat_out_model                         small
% 3.75/1.01  --sat_out_clauses                       false
% 3.75/1.01  
% 3.75/1.01  ------ QBF Options
% 3.75/1.01  
% 3.75/1.01  --qbf_mode                              false
% 3.75/1.01  --qbf_elim_univ                         false
% 3.75/1.01  --qbf_dom_inst                          none
% 3.75/1.01  --qbf_dom_pre_inst                      false
% 3.75/1.01  --qbf_sk_in                             false
% 3.75/1.01  --qbf_pred_elim                         true
% 3.75/1.01  --qbf_split                             512
% 3.75/1.01  
% 3.75/1.01  ------ BMC1 Options
% 3.75/1.01  
% 3.75/1.01  --bmc1_incremental                      false
% 3.75/1.01  --bmc1_axioms                           reachable_all
% 3.75/1.01  --bmc1_min_bound                        0
% 3.75/1.01  --bmc1_max_bound                        -1
% 3.75/1.01  --bmc1_max_bound_default                -1
% 3.75/1.01  --bmc1_symbol_reachability              true
% 3.75/1.01  --bmc1_property_lemmas                  false
% 3.75/1.01  --bmc1_k_induction                      false
% 3.75/1.01  --bmc1_non_equiv_states                 false
% 3.75/1.01  --bmc1_deadlock                         false
% 3.75/1.01  --bmc1_ucm                              false
% 3.75/1.01  --bmc1_add_unsat_core                   none
% 3.75/1.01  --bmc1_unsat_core_children              false
% 3.75/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.75/1.01  --bmc1_out_stat                         full
% 3.75/1.01  --bmc1_ground_init                      false
% 3.75/1.01  --bmc1_pre_inst_next_state              false
% 3.75/1.01  --bmc1_pre_inst_state                   false
% 3.75/1.01  --bmc1_pre_inst_reach_state             false
% 3.75/1.01  --bmc1_out_unsat_core                   false
% 3.75/1.01  --bmc1_aig_witness_out                  false
% 3.75/1.01  --bmc1_verbose                          false
% 3.75/1.01  --bmc1_dump_clauses_tptp                false
% 3.75/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.75/1.01  --bmc1_dump_file                        -
% 3.75/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.75/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.75/1.01  --bmc1_ucm_extend_mode                  1
% 3.75/1.01  --bmc1_ucm_init_mode                    2
% 3.75/1.01  --bmc1_ucm_cone_mode                    none
% 3.75/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.75/1.01  --bmc1_ucm_relax_model                  4
% 3.75/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.75/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.75/1.01  --bmc1_ucm_layered_model                none
% 3.75/1.01  --bmc1_ucm_max_lemma_size               10
% 3.75/1.01  
% 3.75/1.01  ------ AIG Options
% 3.75/1.01  
% 3.75/1.01  --aig_mode                              false
% 3.75/1.01  
% 3.75/1.01  ------ Instantiation Options
% 3.75/1.01  
% 3.75/1.01  --instantiation_flag                    true
% 3.75/1.01  --inst_sos_flag                         false
% 3.75/1.01  --inst_sos_phase                        true
% 3.75/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.75/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.75/1.01  --inst_lit_sel_side                     num_symb
% 3.75/1.01  --inst_solver_per_active                1400
% 3.75/1.01  --inst_solver_calls_frac                1.
% 3.75/1.01  --inst_passive_queue_type               priority_queues
% 3.75/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.75/1.01  --inst_passive_queues_freq              [25;2]
% 3.75/1.01  --inst_dismatching                      true
% 3.75/1.01  --inst_eager_unprocessed_to_passive     true
% 3.75/1.01  --inst_prop_sim_given                   true
% 3.75/1.01  --inst_prop_sim_new                     false
% 3.75/1.01  --inst_subs_new                         false
% 3.75/1.01  --inst_eq_res_simp                      false
% 3.75/1.01  --inst_subs_given                       false
% 3.75/1.01  --inst_orphan_elimination               true
% 3.75/1.01  --inst_learning_loop_flag               true
% 3.75/1.01  --inst_learning_start                   3000
% 3.75/1.01  --inst_learning_factor                  2
% 3.75/1.01  --inst_start_prop_sim_after_learn       3
% 3.75/1.01  --inst_sel_renew                        solver
% 3.75/1.01  --inst_lit_activity_flag                true
% 3.75/1.01  --inst_restr_to_given                   false
% 3.75/1.01  --inst_activity_threshold               500
% 3.75/1.01  --inst_out_proof                        true
% 3.75/1.01  
% 3.75/1.01  ------ Resolution Options
% 3.75/1.01  
% 3.75/1.01  --resolution_flag                       true
% 3.75/1.01  --res_lit_sel                           adaptive
% 3.75/1.01  --res_lit_sel_side                      none
% 3.75/1.01  --res_ordering                          kbo
% 3.75/1.01  --res_to_prop_solver                    active
% 3.75/1.01  --res_prop_simpl_new                    false
% 3.75/1.01  --res_prop_simpl_given                  true
% 3.75/1.01  --res_passive_queue_type                priority_queues
% 3.75/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.75/1.01  --res_passive_queues_freq               [15;5]
% 3.75/1.01  --res_forward_subs                      full
% 3.75/1.01  --res_backward_subs                     full
% 3.75/1.01  --res_forward_subs_resolution           true
% 3.75/1.01  --res_backward_subs_resolution          true
% 3.75/1.01  --res_orphan_elimination                true
% 3.75/1.01  --res_time_limit                        2.
% 3.75/1.01  --res_out_proof                         true
% 3.75/1.01  
% 3.75/1.01  ------ Superposition Options
% 3.75/1.01  
% 3.75/1.01  --superposition_flag                    true
% 3.75/1.01  --sup_passive_queue_type                priority_queues
% 3.75/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.75/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.75/1.01  --demod_completeness_check              fast
% 3.75/1.01  --demod_use_ground                      true
% 3.75/1.01  --sup_to_prop_solver                    passive
% 3.75/1.01  --sup_prop_simpl_new                    true
% 3.75/1.01  --sup_prop_simpl_given                  true
% 3.75/1.01  --sup_fun_splitting                     false
% 3.75/1.01  --sup_smt_interval                      50000
% 3.75/1.01  
% 3.75/1.01  ------ Superposition Simplification Setup
% 3.75/1.01  
% 3.75/1.01  --sup_indices_passive                   []
% 3.75/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.75/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.75/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.75/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.75/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.75/1.01  --sup_full_bw                           [BwDemod]
% 3.75/1.01  --sup_immed_triv                        [TrivRules]
% 3.75/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.75/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.75/1.01  --sup_immed_bw_main                     []
% 3.75/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.75/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.75/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.75/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.75/1.01  
% 3.75/1.01  ------ Combination Options
% 3.75/1.01  
% 3.75/1.01  --comb_res_mult                         3
% 3.75/1.01  --comb_sup_mult                         2
% 3.75/1.01  --comb_inst_mult                        10
% 3.75/1.01  
% 3.75/1.01  ------ Debug Options
% 3.75/1.01  
% 3.75/1.01  --dbg_backtrace                         false
% 3.75/1.01  --dbg_dump_prop_clauses                 false
% 3.75/1.01  --dbg_dump_prop_clauses_file            -
% 3.75/1.01  --dbg_out_stat                          false
% 3.75/1.01  ------ Parsing...
% 3.75/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.75/1.01  
% 3.75/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.75/1.01  
% 3.75/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.75/1.01  
% 3.75/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.75/1.01  ------ Proving...
% 3.75/1.01  ------ Problem Properties 
% 3.75/1.01  
% 3.75/1.01  
% 3.75/1.01  clauses                                 21
% 3.75/1.01  conjectures                             4
% 3.75/1.01  EPR                                     2
% 3.75/1.01  Horn                                    17
% 3.75/1.01  unary                                   6
% 3.75/1.01  binary                                  11
% 3.75/1.01  lits                                    40
% 3.75/1.01  lits eq                                 10
% 3.75/1.01  fd_pure                                 0
% 3.75/1.01  fd_pseudo                               0
% 3.75/1.01  fd_cond                                 2
% 3.75/1.01  fd_pseudo_cond                          0
% 3.75/1.01  AC symbols                              0
% 3.75/1.01  
% 3.75/1.01  ------ Schedule dynamic 5 is on 
% 3.75/1.01  
% 3.75/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.75/1.01  
% 3.75/1.01  
% 3.75/1.01  ------ 
% 3.75/1.01  Current options:
% 3.75/1.01  ------ 
% 3.75/1.01  
% 3.75/1.01  ------ Input Options
% 3.75/1.01  
% 3.75/1.01  --out_options                           all
% 3.75/1.01  --tptp_safe_out                         true
% 3.75/1.01  --problem_path                          ""
% 3.75/1.01  --include_path                          ""
% 3.75/1.01  --clausifier                            res/vclausify_rel
% 3.75/1.01  --clausifier_options                    --mode clausify
% 3.75/1.01  --stdin                                 false
% 3.75/1.01  --stats_out                             all
% 3.75/1.01  
% 3.75/1.01  ------ General Options
% 3.75/1.01  
% 3.75/1.01  --fof                                   false
% 3.75/1.01  --time_out_real                         305.
% 3.75/1.01  --time_out_virtual                      -1.
% 3.75/1.01  --symbol_type_check                     false
% 3.75/1.01  --clausify_out                          false
% 3.75/1.01  --sig_cnt_out                           false
% 3.75/1.01  --trig_cnt_out                          false
% 3.75/1.01  --trig_cnt_out_tolerance                1.
% 3.75/1.01  --trig_cnt_out_sk_spl                   false
% 3.75/1.01  --abstr_cl_out                          false
% 3.75/1.01  
% 3.75/1.01  ------ Global Options
% 3.75/1.01  
% 3.75/1.01  --schedule                              default
% 3.75/1.01  --add_important_lit                     false
% 3.75/1.01  --prop_solver_per_cl                    1000
% 3.75/1.01  --min_unsat_core                        false
% 3.75/1.01  --soft_assumptions                      false
% 3.75/1.01  --soft_lemma_size                       3
% 3.75/1.01  --prop_impl_unit_size                   0
% 3.75/1.01  --prop_impl_unit                        []
% 3.75/1.01  --share_sel_clauses                     true
% 3.75/1.01  --reset_solvers                         false
% 3.75/1.01  --bc_imp_inh                            [conj_cone]
% 3.75/1.01  --conj_cone_tolerance                   3.
% 3.75/1.01  --extra_neg_conj                        none
% 3.75/1.01  --large_theory_mode                     true
% 3.75/1.01  --prolific_symb_bound                   200
% 3.75/1.01  --lt_threshold                          2000
% 3.75/1.01  --clause_weak_htbl                      true
% 3.75/1.01  --gc_record_bc_elim                     false
% 3.75/1.01  
% 3.75/1.01  ------ Preprocessing Options
% 3.75/1.01  
% 3.75/1.01  --preprocessing_flag                    true
% 3.75/1.01  --time_out_prep_mult                    0.1
% 3.75/1.01  --splitting_mode                        input
% 3.75/1.01  --splitting_grd                         true
% 3.75/1.01  --splitting_cvd                         false
% 3.75/1.01  --splitting_cvd_svl                     false
% 3.75/1.01  --splitting_nvd                         32
% 3.75/1.01  --sub_typing                            true
% 3.75/1.01  --prep_gs_sim                           true
% 3.75/1.01  --prep_unflatten                        true
% 3.75/1.01  --prep_res_sim                          true
% 3.75/1.01  --prep_upred                            true
% 3.75/1.01  --prep_sem_filter                       exhaustive
% 3.75/1.01  --prep_sem_filter_out                   false
% 3.75/1.01  --pred_elim                             true
% 3.75/1.01  --res_sim_input                         true
% 3.75/1.01  --eq_ax_congr_red                       true
% 3.75/1.01  --pure_diseq_elim                       true
% 3.75/1.01  --brand_transform                       false
% 3.75/1.01  --non_eq_to_eq                          false
% 3.75/1.01  --prep_def_merge                        true
% 3.75/1.01  --prep_def_merge_prop_impl              false
% 3.75/1.01  --prep_def_merge_mbd                    true
% 3.75/1.01  --prep_def_merge_tr_red                 false
% 3.75/1.01  --prep_def_merge_tr_cl                  false
% 3.75/1.01  --smt_preprocessing                     true
% 3.75/1.01  --smt_ac_axioms                         fast
% 3.75/1.01  --preprocessed_out                      false
% 3.75/1.01  --preprocessed_stats                    false
% 3.75/1.01  
% 3.75/1.01  ------ Abstraction refinement Options
% 3.75/1.01  
% 3.75/1.01  --abstr_ref                             []
% 3.75/1.01  --abstr_ref_prep                        false
% 3.75/1.01  --abstr_ref_until_sat                   false
% 3.75/1.01  --abstr_ref_sig_restrict                funpre
% 3.75/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.75/1.01  --abstr_ref_under                       []
% 3.75/1.01  
% 3.75/1.01  ------ SAT Options
% 3.75/1.01  
% 3.75/1.01  --sat_mode                              false
% 3.75/1.01  --sat_fm_restart_options                ""
% 3.75/1.01  --sat_gr_def                            false
% 3.75/1.01  --sat_epr_types                         true
% 3.75/1.01  --sat_non_cyclic_types                  false
% 3.75/1.01  --sat_finite_models                     false
% 3.75/1.01  --sat_fm_lemmas                         false
% 3.75/1.01  --sat_fm_prep                           false
% 3.75/1.01  --sat_fm_uc_incr                        true
% 3.75/1.01  --sat_out_model                         small
% 3.75/1.01  --sat_out_clauses                       false
% 3.75/1.01  
% 3.75/1.01  ------ QBF Options
% 3.75/1.01  
% 3.75/1.01  --qbf_mode                              false
% 3.75/1.01  --qbf_elim_univ                         false
% 3.75/1.01  --qbf_dom_inst                          none
% 3.75/1.01  --qbf_dom_pre_inst                      false
% 3.75/1.01  --qbf_sk_in                             false
% 3.75/1.01  --qbf_pred_elim                         true
% 3.75/1.01  --qbf_split                             512
% 3.75/1.01  
% 3.75/1.01  ------ BMC1 Options
% 3.75/1.01  
% 3.75/1.01  --bmc1_incremental                      false
% 3.75/1.01  --bmc1_axioms                           reachable_all
% 3.75/1.01  --bmc1_min_bound                        0
% 3.75/1.01  --bmc1_max_bound                        -1
% 3.75/1.01  --bmc1_max_bound_default                -1
% 3.75/1.01  --bmc1_symbol_reachability              true
% 3.75/1.01  --bmc1_property_lemmas                  false
% 3.75/1.01  --bmc1_k_induction                      false
% 3.75/1.01  --bmc1_non_equiv_states                 false
% 3.75/1.01  --bmc1_deadlock                         false
% 3.75/1.01  --bmc1_ucm                              false
% 3.75/1.01  --bmc1_add_unsat_core                   none
% 3.75/1.01  --bmc1_unsat_core_children              false
% 3.75/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.75/1.01  --bmc1_out_stat                         full
% 3.75/1.01  --bmc1_ground_init                      false
% 3.75/1.01  --bmc1_pre_inst_next_state              false
% 3.75/1.01  --bmc1_pre_inst_state                   false
% 3.75/1.01  --bmc1_pre_inst_reach_state             false
% 3.75/1.01  --bmc1_out_unsat_core                   false
% 3.75/1.01  --bmc1_aig_witness_out                  false
% 3.75/1.01  --bmc1_verbose                          false
% 3.75/1.01  --bmc1_dump_clauses_tptp                false
% 3.75/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.75/1.01  --bmc1_dump_file                        -
% 3.75/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.75/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.75/1.01  --bmc1_ucm_extend_mode                  1
% 3.75/1.01  --bmc1_ucm_init_mode                    2
% 3.75/1.01  --bmc1_ucm_cone_mode                    none
% 3.75/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.75/1.01  --bmc1_ucm_relax_model                  4
% 3.75/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.75/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.75/1.01  --bmc1_ucm_layered_model                none
% 3.75/1.01  --bmc1_ucm_max_lemma_size               10
% 3.75/1.01  
% 3.75/1.01  ------ AIG Options
% 3.75/1.01  
% 3.75/1.01  --aig_mode                              false
% 3.75/1.01  
% 3.75/1.01  ------ Instantiation Options
% 3.75/1.01  
% 3.75/1.01  --instantiation_flag                    true
% 3.75/1.01  --inst_sos_flag                         false
% 3.75/1.01  --inst_sos_phase                        true
% 3.75/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.75/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.75/1.01  --inst_lit_sel_side                     none
% 3.75/1.01  --inst_solver_per_active                1400
% 3.75/1.01  --inst_solver_calls_frac                1.
% 3.75/1.01  --inst_passive_queue_type               priority_queues
% 3.75/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.75/1.01  --inst_passive_queues_freq              [25;2]
% 3.75/1.01  --inst_dismatching                      true
% 3.75/1.01  --inst_eager_unprocessed_to_passive     true
% 3.75/1.01  --inst_prop_sim_given                   true
% 3.75/1.01  --inst_prop_sim_new                     false
% 3.75/1.01  --inst_subs_new                         false
% 3.75/1.01  --inst_eq_res_simp                      false
% 3.75/1.01  --inst_subs_given                       false
% 3.75/1.01  --inst_orphan_elimination               true
% 3.75/1.01  --inst_learning_loop_flag               true
% 3.75/1.01  --inst_learning_start                   3000
% 3.75/1.01  --inst_learning_factor                  2
% 3.75/1.01  --inst_start_prop_sim_after_learn       3
% 3.75/1.01  --inst_sel_renew                        solver
% 3.75/1.01  --inst_lit_activity_flag                true
% 3.75/1.01  --inst_restr_to_given                   false
% 3.75/1.01  --inst_activity_threshold               500
% 3.75/1.01  --inst_out_proof                        true
% 3.75/1.01  
% 3.75/1.01  ------ Resolution Options
% 3.75/1.01  
% 3.75/1.01  --resolution_flag                       false
% 3.75/1.01  --res_lit_sel                           adaptive
% 3.75/1.01  --res_lit_sel_side                      none
% 3.75/1.01  --res_ordering                          kbo
% 3.75/1.01  --res_to_prop_solver                    active
% 3.75/1.01  --res_prop_simpl_new                    false
% 3.75/1.01  --res_prop_simpl_given                  true
% 3.75/1.01  --res_passive_queue_type                priority_queues
% 3.75/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.75/1.01  --res_passive_queues_freq               [15;5]
% 3.75/1.01  --res_forward_subs                      full
% 3.75/1.01  --res_backward_subs                     full
% 3.75/1.01  --res_forward_subs_resolution           true
% 3.75/1.01  --res_backward_subs_resolution          true
% 3.75/1.01  --res_orphan_elimination                true
% 3.75/1.01  --res_time_limit                        2.
% 3.75/1.01  --res_out_proof                         true
% 3.75/1.01  
% 3.75/1.01  ------ Superposition Options
% 3.75/1.01  
% 3.75/1.01  --superposition_flag                    true
% 3.75/1.01  --sup_passive_queue_type                priority_queues
% 3.75/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.75/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.75/1.01  --demod_completeness_check              fast
% 3.75/1.01  --demod_use_ground                      true
% 3.75/1.01  --sup_to_prop_solver                    passive
% 3.75/1.01  --sup_prop_simpl_new                    true
% 3.75/1.01  --sup_prop_simpl_given                  true
% 3.75/1.01  --sup_fun_splitting                     false
% 3.75/1.01  --sup_smt_interval                      50000
% 3.75/1.01  
% 3.75/1.01  ------ Superposition Simplification Setup
% 3.75/1.01  
% 3.75/1.01  --sup_indices_passive                   []
% 3.75/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.75/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.75/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.75/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.75/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.75/1.01  --sup_full_bw                           [BwDemod]
% 3.75/1.01  --sup_immed_triv                        [TrivRules]
% 3.75/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.75/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.75/1.01  --sup_immed_bw_main                     []
% 3.75/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.75/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.75/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.75/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.75/1.01  
% 3.75/1.01  ------ Combination Options
% 3.75/1.01  
% 3.75/1.01  --comb_res_mult                         3
% 3.75/1.01  --comb_sup_mult                         2
% 3.75/1.01  --comb_inst_mult                        10
% 3.75/1.01  
% 3.75/1.01  ------ Debug Options
% 3.75/1.01  
% 3.75/1.01  --dbg_backtrace                         false
% 3.75/1.01  --dbg_dump_prop_clauses                 false
% 3.75/1.01  --dbg_dump_prop_clauses_file            -
% 3.75/1.01  --dbg_out_stat                          false
% 3.75/1.01  
% 3.75/1.01  
% 3.75/1.01  
% 3.75/1.01  
% 3.75/1.01  ------ Proving...
% 3.75/1.01  
% 3.75/1.01  
% 3.75/1.01  % SZS status Theorem for theBenchmark.p
% 3.75/1.01  
% 3.75/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.75/1.01  
% 3.75/1.01  fof(f3,axiom,(
% 3.75/1.01    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0),
% 3.75/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/1.01  
% 3.75/1.01  fof(f38,plain,(
% 3.75/1.01    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0) )),
% 3.75/1.01    inference(cnf_transformation,[],[f3])).
% 3.75/1.01  
% 3.75/1.01  fof(f4,axiom,(
% 3.75/1.01    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 3.75/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/1.01  
% 3.75/1.01  fof(f28,plain,(
% 3.75/1.01    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 3.75/1.01    inference(nnf_transformation,[],[f4])).
% 3.75/1.01  
% 3.75/1.01  fof(f40,plain,(
% 3.75/1.01    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 3.75/1.01    inference(cnf_transformation,[],[f28])).
% 3.75/1.01  
% 3.75/1.01  fof(f1,axiom,(
% 3.75/1.01    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.75/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/1.01  
% 3.75/1.01  fof(f14,plain,(
% 3.75/1.01    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.75/1.01    inference(rectify,[],[f1])).
% 3.75/1.01  
% 3.75/1.01  fof(f15,plain,(
% 3.75/1.01    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 3.75/1.01    inference(ennf_transformation,[],[f14])).
% 3.75/1.01  
% 3.75/1.01  fof(f25,plain,(
% 3.75/1.01    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.75/1.01    introduced(choice_axiom,[])).
% 3.75/1.01  
% 3.75/1.01  fof(f26,plain,(
% 3.75/1.01    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 3.75/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f25])).
% 3.75/1.01  
% 3.75/1.01  fof(f34,plain,(
% 3.75/1.01    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 3.75/1.01    inference(cnf_transformation,[],[f26])).
% 3.75/1.01  
% 3.75/1.01  fof(f35,plain,(
% 3.75/1.01    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 3.75/1.01    inference(cnf_transformation,[],[f26])).
% 3.75/1.01  
% 3.75/1.01  fof(f39,plain,(
% 3.75/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 3.75/1.01    inference(cnf_transformation,[],[f28])).
% 3.75/1.01  
% 3.75/1.01  fof(f12,conjecture,(
% 3.75/1.01    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 3.75/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/1.01  
% 3.75/1.01  fof(f13,negated_conjecture,(
% 3.75/1.01    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 3.75/1.01    inference(negated_conjecture,[],[f12])).
% 3.75/1.01  
% 3.75/1.01  fof(f23,plain,(
% 3.75/1.01    ? [X0,X1] : (? [X2] : ((~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.75/1.01    inference(ennf_transformation,[],[f13])).
% 3.75/1.01  
% 3.75/1.01  fof(f24,plain,(
% 3.75/1.01    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.75/1.01    inference(flattening,[],[f23])).
% 3.75/1.01  
% 3.75/1.01  fof(f31,plain,(
% 3.75/1.01    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (~r1_tarski(k8_setfam_1(X0,sK3),k8_setfam_1(X0,X1)) & r1_tarski(X1,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(X0))))) )),
% 3.75/1.01    introduced(choice_axiom,[])).
% 3.75/1.01  
% 3.75/1.01  fof(f30,plain,(
% 3.75/1.01    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (? [X2] : (~r1_tarski(k8_setfam_1(sK1,X2),k8_setfam_1(sK1,sK2)) & r1_tarski(sK2,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK1)))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))))),
% 3.75/1.01    introduced(choice_axiom,[])).
% 3.75/1.01  
% 3.75/1.01  fof(f32,plain,(
% 3.75/1.01    (~r1_tarski(k8_setfam_1(sK1,sK3),k8_setfam_1(sK1,sK2)) & r1_tarski(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1)))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1)))),
% 3.75/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f24,f31,f30])).
% 3.75/1.01  
% 3.75/1.01  fof(f52,plain,(
% 3.75/1.01    r1_tarski(sK2,sK3)),
% 3.75/1.01    inference(cnf_transformation,[],[f32])).
% 3.75/1.01  
% 3.75/1.01  fof(f11,axiom,(
% 3.75/1.01    ! [X0,X1] : (r1_tarski(X0,X1) => (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 3.75/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/1.01  
% 3.75/1.01  fof(f21,plain,(
% 3.75/1.01    ! [X0,X1] : ((r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0) | ~r1_tarski(X0,X1))),
% 3.75/1.01    inference(ennf_transformation,[],[f11])).
% 3.75/1.01  
% 3.75/1.01  fof(f22,plain,(
% 3.75/1.01    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1))),
% 3.75/1.01    inference(flattening,[],[f21])).
% 3.75/1.01  
% 3.75/1.01  fof(f49,plain,(
% 3.75/1.01    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1)) )),
% 3.75/1.01    inference(cnf_transformation,[],[f22])).
% 3.75/1.01  
% 3.75/1.01  fof(f2,axiom,(
% 3.75/1.01    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 3.75/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/1.01  
% 3.75/1.01  fof(f27,plain,(
% 3.75/1.01    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 3.75/1.01    inference(nnf_transformation,[],[f2])).
% 3.75/1.01  
% 3.75/1.01  fof(f37,plain,(
% 3.75/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 3.75/1.01    inference(cnf_transformation,[],[f27])).
% 3.75/1.01  
% 3.75/1.01  fof(f36,plain,(
% 3.75/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 3.75/1.01    inference(cnf_transformation,[],[f27])).
% 3.75/1.01  
% 3.75/1.01  fof(f51,plain,(
% 3.75/1.01    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1)))),
% 3.75/1.01    inference(cnf_transformation,[],[f32])).
% 3.75/1.01  
% 3.75/1.01  fof(f6,axiom,(
% 3.75/1.01    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((k1_xboole_0 = X1 => k8_setfam_1(X0,X1) = X0) & (k1_xboole_0 != X1 => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1))))),
% 3.75/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/1.01  
% 3.75/1.01  fof(f16,plain,(
% 3.75/1.01    ! [X0,X1] : (((k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1) & (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.75/1.01    inference(ennf_transformation,[],[f6])).
% 3.75/1.01  
% 3.75/1.01  fof(f42,plain,(
% 3.75/1.01    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 3.75/1.01    inference(cnf_transformation,[],[f16])).
% 3.75/1.01  
% 3.75/1.01  fof(f8,axiom,(
% 3.75/1.01    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k6_setfam_1(X0,X1) = k1_setfam_1(X1))),
% 3.75/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/1.01  
% 3.75/1.01  fof(f18,plain,(
% 3.75/1.01    ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.75/1.01    inference(ennf_transformation,[],[f8])).
% 3.75/1.01  
% 3.75/1.01  fof(f45,plain,(
% 3.75/1.01    ( ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 3.75/1.01    inference(cnf_transformation,[],[f18])).
% 3.75/1.01  
% 3.75/1.01  fof(f50,plain,(
% 3.75/1.01    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1)))),
% 3.75/1.01    inference(cnf_transformation,[],[f32])).
% 3.75/1.01  
% 3.75/1.01  fof(f53,plain,(
% 3.75/1.01    ~r1_tarski(k8_setfam_1(sK1,sK3),k8_setfam_1(sK1,sK2))),
% 3.75/1.01    inference(cnf_transformation,[],[f32])).
% 3.75/1.01  
% 3.75/1.01  fof(f43,plain,(
% 3.75/1.01    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 3.75/1.01    inference(cnf_transformation,[],[f16])).
% 3.75/1.01  
% 3.75/1.01  fof(f54,plain,(
% 3.75/1.01    ( ! [X0] : (k8_setfam_1(X0,k1_xboole_0) = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 3.75/1.01    inference(equality_resolution,[],[f43])).
% 3.75/1.01  
% 3.75/1.01  fof(f5,axiom,(
% 3.75/1.01    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.75/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/1.01  
% 3.75/1.01  fof(f41,plain,(
% 3.75/1.01    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.75/1.01    inference(cnf_transformation,[],[f5])).
% 3.75/1.01  
% 3.75/1.01  fof(f7,axiom,(
% 3.75/1.01    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 3.75/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/1.01  
% 3.75/1.01  fof(f17,plain,(
% 3.75/1.01    ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.75/1.01    inference(ennf_transformation,[],[f7])).
% 3.75/1.01  
% 3.75/1.01  fof(f44,plain,(
% 3.75/1.01    ( ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 3.75/1.01    inference(cnf_transformation,[],[f17])).
% 3.75/1.01  
% 3.75/1.01  fof(f9,axiom,(
% 3.75/1.01    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.75/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/1.01  
% 3.75/1.01  fof(f29,plain,(
% 3.75/1.01    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.75/1.01    inference(nnf_transformation,[],[f9])).
% 3.75/1.01  
% 3.75/1.01  fof(f46,plain,(
% 3.75/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.75/1.01    inference(cnf_transformation,[],[f29])).
% 3.75/1.01  
% 3.75/1.01  cnf(c_5,plain,
% 3.75/1.01      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.75/1.01      inference(cnf_transformation,[],[f38]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_6,plain,
% 3.75/1.01      ( r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0 ),
% 3.75/1.01      inference(cnf_transformation,[],[f40]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_853,plain,
% 3.75/1.01      ( k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1) = iProver_top ),
% 3.75/1.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_1170,plain,
% 3.75/1.01      ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
% 3.75/1.01      inference(superposition,[status(thm)],[c_5,c_853]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_1,plain,
% 3.75/1.01      ( r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1) ),
% 3.75/1.01      inference(cnf_transformation,[],[f34]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_857,plain,
% 3.75/1.01      ( r2_hidden(sK0(X0,X1),X1) = iProver_top
% 3.75/1.01      | r1_xboole_0(X0,X1) = iProver_top ),
% 3.75/1.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_0,plain,
% 3.75/1.01      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 3.75/1.01      inference(cnf_transformation,[],[f35]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_858,plain,
% 3.75/1.01      ( r2_hidden(X0,X1) != iProver_top
% 3.75/1.01      | r2_hidden(X0,X2) != iProver_top
% 3.75/1.01      | r1_xboole_0(X1,X2) != iProver_top ),
% 3.75/1.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_2746,plain,
% 3.75/1.01      ( r2_hidden(sK0(X0,X1),X2) != iProver_top
% 3.75/1.01      | r1_xboole_0(X2,X1) != iProver_top
% 3.75/1.01      | r1_xboole_0(X0,X1) = iProver_top ),
% 3.75/1.01      inference(superposition,[status(thm)],[c_857,c_858]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_13584,plain,
% 3.75/1.01      ( r1_xboole_0(X0,X0) != iProver_top
% 3.75/1.01      | r1_xboole_0(X1,X0) = iProver_top ),
% 3.75/1.01      inference(superposition,[status(thm)],[c_857,c_2746]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_13594,plain,
% 3.75/1.01      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 3.75/1.01      inference(superposition,[status(thm)],[c_1170,c_13584]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_7,plain,
% 3.75/1.01      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 3.75/1.01      inference(cnf_transformation,[],[f39]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_852,plain,
% 3.75/1.01      ( k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1) != iProver_top ),
% 3.75/1.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_13840,plain,
% 3.75/1.01      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.75/1.01      inference(superposition,[status(thm)],[c_13594,c_852]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_18,negated_conjecture,
% 3.75/1.01      ( r1_tarski(sK2,sK3) ),
% 3.75/1.01      inference(cnf_transformation,[],[f52]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_841,plain,
% 3.75/1.01      ( r1_tarski(sK2,sK3) = iProver_top ),
% 3.75/1.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_16,plain,
% 3.75/1.01      ( ~ r1_tarski(X0,X1)
% 3.75/1.01      | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
% 3.75/1.01      | k1_xboole_0 = X0 ),
% 3.75/1.01      inference(cnf_transformation,[],[f49]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_843,plain,
% 3.75/1.01      ( k1_xboole_0 = X0
% 3.75/1.01      | r1_tarski(X0,X1) != iProver_top
% 3.75/1.01      | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) = iProver_top ),
% 3.75/1.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_3,plain,
% 3.75/1.01      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 3.75/1.01      inference(cnf_transformation,[],[f37]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_855,plain,
% 3.75/1.01      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 3.75/1.01      | r1_tarski(X0,X1) != iProver_top ),
% 3.75/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_1354,plain,
% 3.75/1.01      ( k4_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) = k1_xboole_0
% 3.75/1.01      | k1_xboole_0 = X1
% 3.75/1.01      | r1_tarski(X1,X0) != iProver_top ),
% 3.75/1.01      inference(superposition,[status(thm)],[c_843,c_855]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_3282,plain,
% 3.75/1.01      ( k4_xboole_0(k1_setfam_1(sK3),k1_setfam_1(sK2)) = k1_xboole_0
% 3.75/1.01      | sK2 = k1_xboole_0 ),
% 3.75/1.01      inference(superposition,[status(thm)],[c_841,c_1354]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_4,plain,
% 3.75/1.01      ( r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0 ),
% 3.75/1.01      inference(cnf_transformation,[],[f36]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_854,plain,
% 3.75/1.01      ( k4_xboole_0(X0,X1) != k1_xboole_0
% 3.75/1.01      | r1_tarski(X0,X1) = iProver_top ),
% 3.75/1.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_3440,plain,
% 3.75/1.01      ( sK2 = k1_xboole_0
% 3.75/1.01      | r1_tarski(k1_setfam_1(sK3),k1_setfam_1(sK2)) = iProver_top ),
% 3.75/1.01      inference(superposition,[status(thm)],[c_3282,c_854]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_19,negated_conjecture,
% 3.75/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
% 3.75/1.01      inference(cnf_transformation,[],[f51]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_840,plain,
% 3.75/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
% 3.75/1.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_10,plain,
% 3.75/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 3.75/1.01      | k6_setfam_1(X1,X0) = k8_setfam_1(X1,X0)
% 3.75/1.01      | k1_xboole_0 = X0 ),
% 3.75/1.01      inference(cnf_transformation,[],[f42]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_849,plain,
% 3.75/1.01      ( k6_setfam_1(X0,X1) = k8_setfam_1(X0,X1)
% 3.75/1.01      | k1_xboole_0 = X1
% 3.75/1.01      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 3.75/1.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_2647,plain,
% 3.75/1.01      ( k6_setfam_1(sK1,sK3) = k8_setfam_1(sK1,sK3) | sK3 = k1_xboole_0 ),
% 3.75/1.01      inference(superposition,[status(thm)],[c_840,c_849]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_12,plain,
% 3.75/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 3.75/1.01      | k6_setfam_1(X1,X0) = k1_setfam_1(X0) ),
% 3.75/1.01      inference(cnf_transformation,[],[f45]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_847,plain,
% 3.75/1.01      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
% 3.75/1.01      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 3.75/1.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_1974,plain,
% 3.75/1.01      ( k6_setfam_1(sK1,sK3) = k1_setfam_1(sK3) ),
% 3.75/1.01      inference(superposition,[status(thm)],[c_840,c_847]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_2656,plain,
% 3.75/1.01      ( k8_setfam_1(sK1,sK3) = k1_setfam_1(sK3) | sK3 = k1_xboole_0 ),
% 3.75/1.01      inference(light_normalisation,[status(thm)],[c_2647,c_1974]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_20,negated_conjecture,
% 3.75/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
% 3.75/1.01      inference(cnf_transformation,[],[f50]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_839,plain,
% 3.75/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
% 3.75/1.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_2648,plain,
% 3.75/1.01      ( k6_setfam_1(sK1,sK2) = k8_setfam_1(sK1,sK2) | sK2 = k1_xboole_0 ),
% 3.75/1.01      inference(superposition,[status(thm)],[c_839,c_849]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_1975,plain,
% 3.75/1.01      ( k6_setfam_1(sK1,sK2) = k1_setfam_1(sK2) ),
% 3.75/1.01      inference(superposition,[status(thm)],[c_839,c_847]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_2651,plain,
% 3.75/1.01      ( k8_setfam_1(sK1,sK2) = k1_setfam_1(sK2) | sK2 = k1_xboole_0 ),
% 3.75/1.01      inference(light_normalisation,[status(thm)],[c_2648,c_1975]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_17,negated_conjecture,
% 3.75/1.01      ( ~ r1_tarski(k8_setfam_1(sK1,sK3),k8_setfam_1(sK1,sK2)) ),
% 3.75/1.01      inference(cnf_transformation,[],[f53]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_842,plain,
% 3.75/1.01      ( r1_tarski(k8_setfam_1(sK1,sK3),k8_setfam_1(sK1,sK2)) != iProver_top ),
% 3.75/1.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_2807,plain,
% 3.75/1.01      ( sK2 = k1_xboole_0
% 3.75/1.01      | r1_tarski(k8_setfam_1(sK1,sK3),k1_setfam_1(sK2)) != iProver_top ),
% 3.75/1.01      inference(superposition,[status(thm)],[c_2651,c_842]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_2902,plain,
% 3.75/1.01      ( sK2 = k1_xboole_0
% 3.75/1.01      | sK3 = k1_xboole_0
% 3.75/1.01      | r1_tarski(k1_setfam_1(sK3),k1_setfam_1(sK2)) != iProver_top ),
% 3.75/1.01      inference(superposition,[status(thm)],[c_2656,c_2807]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_3459,plain,
% 3.75/1.01      ( sK2 = k1_xboole_0 | sK3 = k1_xboole_0 ),
% 3.75/1.01      inference(superposition,[status(thm)],[c_3440,c_2902]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_3884,plain,
% 3.75/1.01      ( sK3 = k1_xboole_0
% 3.75/1.01      | r1_tarski(k8_setfam_1(sK1,sK3),k8_setfam_1(sK1,k1_xboole_0)) != iProver_top ),
% 3.75/1.01      inference(superposition,[status(thm)],[c_3459,c_842]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_9,plain,
% 3.75/1.01      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
% 3.75/1.01      | k8_setfam_1(X0,k1_xboole_0) = X0 ),
% 3.75/1.01      inference(cnf_transformation,[],[f54]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_850,plain,
% 3.75/1.01      ( k8_setfam_1(X0,k1_xboole_0) = X0
% 3.75/1.01      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 3.75/1.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_8,plain,
% 3.75/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.75/1.01      inference(cnf_transformation,[],[f41]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_851,plain,
% 3.75/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.75/1.01      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_905,plain,
% 3.75/1.01      ( k8_setfam_1(X0,k1_xboole_0) = X0 ),
% 3.75/1.01      inference(forward_subsumption_resolution,
% 3.75/1.01                [status(thm)],
% 3.75/1.01                [c_850,c_851]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_3893,plain,
% 3.75/1.01      ( sK3 = k1_xboole_0
% 3.75/1.01      | r1_tarski(k8_setfam_1(sK1,sK3),sK1) != iProver_top ),
% 3.75/1.01      inference(demodulation,[status(thm)],[c_3884,c_905]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_22,plain,
% 3.75/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
% 3.75/1.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_11,plain,
% 3.75/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 3.75/1.01      | m1_subset_1(k8_setfam_1(X1,X0),k1_zfmisc_1(X1)) ),
% 3.75/1.01      inference(cnf_transformation,[],[f44]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_1003,plain,
% 3.75/1.01      ( m1_subset_1(k8_setfam_1(sK1,sK3),k1_zfmisc_1(sK1))
% 3.75/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
% 3.75/1.01      inference(instantiation,[status(thm)],[c_11]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_1004,plain,
% 3.75/1.01      ( m1_subset_1(k8_setfam_1(sK1,sK3),k1_zfmisc_1(sK1)) = iProver_top
% 3.75/1.01      | m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top ),
% 3.75/1.01      inference(predicate_to_equality,[status(thm)],[c_1003]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_14,plain,
% 3.75/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.75/1.01      inference(cnf_transformation,[],[f46]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_1624,plain,
% 3.75/1.01      ( ~ m1_subset_1(k8_setfam_1(sK1,sK3),k1_zfmisc_1(X0))
% 3.75/1.01      | r1_tarski(k8_setfam_1(sK1,sK3),X0) ),
% 3.75/1.01      inference(instantiation,[status(thm)],[c_14]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_2852,plain,
% 3.75/1.01      ( ~ m1_subset_1(k8_setfam_1(sK1,sK3),k1_zfmisc_1(sK1))
% 3.75/1.01      | r1_tarski(k8_setfam_1(sK1,sK3),sK1) ),
% 3.75/1.01      inference(instantiation,[status(thm)],[c_1624]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_2853,plain,
% 3.75/1.01      ( m1_subset_1(k8_setfam_1(sK1,sK3),k1_zfmisc_1(sK1)) != iProver_top
% 3.75/1.01      | r1_tarski(k8_setfam_1(sK1,sK3),sK1) = iProver_top ),
% 3.75/1.01      inference(predicate_to_equality,[status(thm)],[c_2852]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_4096,plain,
% 3.75/1.01      ( sK3 = k1_xboole_0 ),
% 3.75/1.01      inference(global_propositional_subsumption,
% 3.75/1.01                [status(thm)],
% 3.75/1.01                [c_3893,c_22,c_1004,c_2853]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_1355,plain,
% 3.75/1.01      ( k4_xboole_0(sK2,sK3) = k1_xboole_0 ),
% 3.75/1.01      inference(superposition,[status(thm)],[c_841,c_855]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_4115,plain,
% 3.75/1.01      ( k4_xboole_0(sK2,k1_xboole_0) = k1_xboole_0 ),
% 3.75/1.01      inference(demodulation,[status(thm)],[c_4096,c_1355]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_13850,plain,
% 3.75/1.01      ( sK2 = k1_xboole_0 ),
% 3.75/1.01      inference(superposition,[status(thm)],[c_13840,c_4115]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_361,plain,
% 3.75/1.01      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.75/1.01      theory(equality) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_1028,plain,
% 3.75/1.01      ( m1_subset_1(X0,X1)
% 3.75/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
% 3.75/1.01      | X0 != X2
% 3.75/1.01      | X1 != k1_zfmisc_1(X3) ),
% 3.75/1.01      inference(instantiation,[status(thm)],[c_361]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_1120,plain,
% 3.75/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.75/1.01      | m1_subset_1(X2,k1_zfmisc_1(X3))
% 3.75/1.01      | X2 != X0
% 3.75/1.01      | k1_zfmisc_1(X3) != k1_zfmisc_1(X1) ),
% 3.75/1.01      inference(instantiation,[status(thm)],[c_1028]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_1407,plain,
% 3.75/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.75/1.01      | m1_subset_1(X2,k1_zfmisc_1(k8_setfam_1(sK1,sK2)))
% 3.75/1.01      | X2 != X0
% 3.75/1.01      | k1_zfmisc_1(k8_setfam_1(sK1,sK2)) != k1_zfmisc_1(X1) ),
% 3.75/1.01      inference(instantiation,[status(thm)],[c_1120]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_2235,plain,
% 3.75/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.75/1.01      | m1_subset_1(k8_setfam_1(sK1,sK2),k1_zfmisc_1(k8_setfam_1(sK1,sK2)))
% 3.75/1.01      | k8_setfam_1(sK1,sK2) != X0
% 3.75/1.01      | k1_zfmisc_1(k8_setfam_1(sK1,sK2)) != k1_zfmisc_1(X1) ),
% 3.75/1.01      inference(instantiation,[status(thm)],[c_1407]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_3529,plain,
% 3.75/1.01      ( ~ m1_subset_1(k8_setfam_1(k8_setfam_1(sK1,sK2),k1_xboole_0),k1_zfmisc_1(X0))
% 3.75/1.01      | m1_subset_1(k8_setfam_1(sK1,sK2),k1_zfmisc_1(k8_setfam_1(sK1,sK2)))
% 3.75/1.01      | k8_setfam_1(sK1,sK2) != k8_setfam_1(k8_setfam_1(sK1,sK2),k1_xboole_0)
% 3.75/1.01      | k1_zfmisc_1(k8_setfam_1(sK1,sK2)) != k1_zfmisc_1(X0) ),
% 3.75/1.01      inference(instantiation,[status(thm)],[c_2235]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_11956,plain,
% 3.75/1.01      ( ~ m1_subset_1(k8_setfam_1(k8_setfam_1(sK1,sK2),k1_xboole_0),k1_zfmisc_1(k8_setfam_1(sK1,sK2)))
% 3.75/1.01      | m1_subset_1(k8_setfam_1(sK1,sK2),k1_zfmisc_1(k8_setfam_1(sK1,sK2)))
% 3.75/1.01      | k8_setfam_1(sK1,sK2) != k8_setfam_1(k8_setfam_1(sK1,sK2),k1_xboole_0)
% 3.75/1.01      | k1_zfmisc_1(k8_setfam_1(sK1,sK2)) != k1_zfmisc_1(k8_setfam_1(sK1,sK2)) ),
% 3.75/1.01      inference(instantiation,[status(thm)],[c_3529]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_362,plain,
% 3.75/1.01      ( X0 != X1 | X2 != X3 | k8_setfam_1(X0,X2) = k8_setfam_1(X1,X3) ),
% 3.75/1.01      theory(equality) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_1182,plain,
% 3.75/1.01      ( k8_setfam_1(sK1,sK3) = k8_setfam_1(X0,X1)
% 3.75/1.01      | sK3 != X1
% 3.75/1.01      | sK1 != X0 ),
% 3.75/1.01      inference(instantiation,[status(thm)],[c_362]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_4959,plain,
% 3.75/1.01      ( k8_setfam_1(sK1,sK3) = k8_setfam_1(sK1,X0)
% 3.75/1.01      | sK3 != X0
% 3.75/1.01      | sK1 != sK1 ),
% 3.75/1.01      inference(instantiation,[status(thm)],[c_1182]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_10831,plain,
% 3.75/1.01      ( k8_setfam_1(sK1,sK3) = k8_setfam_1(sK1,sK2)
% 3.75/1.01      | sK3 != sK2
% 3.75/1.01      | sK1 != sK1 ),
% 3.75/1.01      inference(instantiation,[status(thm)],[c_4959]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_356,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_1545,plain,
% 3.75/1.01      ( X0 != X1 | sK3 != X1 | sK3 = X0 ),
% 3.75/1.01      inference(instantiation,[status(thm)],[c_356]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_10148,plain,
% 3.75/1.01      ( sK2 != X0 | sK3 != X0 | sK3 = sK2 ),
% 3.75/1.01      inference(instantiation,[status(thm)],[c_1545]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_10149,plain,
% 3.75/1.01      ( sK2 != k1_xboole_0 | sK3 = sK2 | sK3 != k1_xboole_0 ),
% 3.75/1.01      inference(instantiation,[status(thm)],[c_10148]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_359,plain,
% 3.75/1.01      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.75/1.01      theory(equality) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_1018,plain,
% 3.75/1.01      ( ~ r1_tarski(X0,X1)
% 3.75/1.01      | r1_tarski(k8_setfam_1(sK1,sK3),k8_setfam_1(sK1,sK2))
% 3.75/1.01      | k8_setfam_1(sK1,sK2) != X1
% 3.75/1.01      | k8_setfam_1(sK1,sK3) != X0 ),
% 3.75/1.01      inference(instantiation,[status(thm)],[c_359]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_1044,plain,
% 3.75/1.01      ( ~ r1_tarski(X0,k8_setfam_1(sK1,sK2))
% 3.75/1.01      | r1_tarski(k8_setfam_1(sK1,sK3),k8_setfam_1(sK1,sK2))
% 3.75/1.01      | k8_setfam_1(sK1,sK2) != k8_setfam_1(sK1,sK2)
% 3.75/1.01      | k8_setfam_1(sK1,sK3) != X0 ),
% 3.75/1.01      inference(instantiation,[status(thm)],[c_1018]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_4873,plain,
% 3.75/1.01      ( ~ r1_tarski(k8_setfam_1(sK1,sK2),k8_setfam_1(sK1,sK2))
% 3.75/1.01      | r1_tarski(k8_setfam_1(sK1,sK3),k8_setfam_1(sK1,sK2))
% 3.75/1.01      | k8_setfam_1(sK1,sK2) != k8_setfam_1(sK1,sK2)
% 3.75/1.01      | k8_setfam_1(sK1,sK3) != k8_setfam_1(sK1,sK2) ),
% 3.75/1.01      inference(instantiation,[status(thm)],[c_1044]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_360,plain,
% 3.75/1.01      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 3.75/1.01      theory(equality) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_3243,plain,
% 3.75/1.01      ( k8_setfam_1(sK1,sK2) != k8_setfam_1(sK1,sK2)
% 3.75/1.01      | k1_zfmisc_1(k8_setfam_1(sK1,sK2)) = k1_zfmisc_1(k8_setfam_1(sK1,sK2)) ),
% 3.75/1.01      inference(instantiation,[status(thm)],[c_360]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_355,plain,( X0 = X0 ),theory(equality) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_1963,plain,
% 3.75/1.01      ( sK1 = sK1 ),
% 3.75/1.01      inference(instantiation,[status(thm)],[c_355]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_1137,plain,
% 3.75/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k8_setfam_1(sK1,sK2)))
% 3.75/1.01      | r1_tarski(X0,k8_setfam_1(sK1,sK2)) ),
% 3.75/1.01      inference(instantiation,[status(thm)],[c_14]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_1831,plain,
% 3.75/1.01      ( ~ m1_subset_1(k8_setfam_1(sK1,sK2),k1_zfmisc_1(k8_setfam_1(sK1,sK2)))
% 3.75/1.01      | r1_tarski(k8_setfam_1(sK1,sK2),k8_setfam_1(sK1,sK2)) ),
% 3.75/1.01      inference(instantiation,[status(thm)],[c_1137]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_993,plain,
% 3.75/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ),
% 3.75/1.01      inference(instantiation,[status(thm)],[c_8]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_1613,plain,
% 3.75/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k8_setfam_1(sK1,sK2)))) ),
% 3.75/1.01      inference(instantiation,[status(thm)],[c_993]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_1429,plain,
% 3.75/1.01      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k8_setfam_1(sK1,sK2))))
% 3.75/1.01      | k8_setfam_1(k8_setfam_1(sK1,sK2),k1_xboole_0) = k8_setfam_1(sK1,sK2) ),
% 3.75/1.01      inference(instantiation,[status(thm)],[c_9]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_1050,plain,
% 3.75/1.01      ( X0 != X1
% 3.75/1.01      | k8_setfam_1(sK1,sK2) != X1
% 3.75/1.01      | k8_setfam_1(sK1,sK2) = X0 ),
% 3.75/1.01      inference(instantiation,[status(thm)],[c_356]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_1157,plain,
% 3.75/1.01      ( X0 != k8_setfam_1(sK1,sK2)
% 3.75/1.01      | k8_setfam_1(sK1,sK2) = X0
% 3.75/1.01      | k8_setfam_1(sK1,sK2) != k8_setfam_1(sK1,sK2) ),
% 3.75/1.01      inference(instantiation,[status(thm)],[c_1050]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_1428,plain,
% 3.75/1.01      ( k8_setfam_1(k8_setfam_1(sK1,sK2),k1_xboole_0) != k8_setfam_1(sK1,sK2)
% 3.75/1.01      | k8_setfam_1(sK1,sK2) = k8_setfam_1(k8_setfam_1(sK1,sK2),k1_xboole_0)
% 3.75/1.01      | k8_setfam_1(sK1,sK2) != k8_setfam_1(sK1,sK2) ),
% 3.75/1.01      inference(instantiation,[status(thm)],[c_1157]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_1388,plain,
% 3.75/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(k8_setfam_1(sK1,sK2))))
% 3.75/1.01      | m1_subset_1(k8_setfam_1(k8_setfam_1(sK1,sK2),X0),k1_zfmisc_1(k8_setfam_1(sK1,sK2))) ),
% 3.75/1.01      inference(instantiation,[status(thm)],[c_11]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_1394,plain,
% 3.75/1.01      ( m1_subset_1(k8_setfam_1(k8_setfam_1(sK1,sK2),k1_xboole_0),k1_zfmisc_1(k8_setfam_1(sK1,sK2)))
% 3.75/1.01      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k8_setfam_1(sK1,sK2)))) ),
% 3.75/1.01      inference(instantiation,[status(thm)],[c_1388]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(c_1045,plain,
% 3.75/1.01      ( k8_setfam_1(sK1,sK2) = k8_setfam_1(sK1,sK2) ),
% 3.75/1.01      inference(instantiation,[status(thm)],[c_355]) ).
% 3.75/1.01  
% 3.75/1.01  cnf(contradiction,plain,
% 3.75/1.01      ( $false ),
% 3.75/1.01      inference(minisat,
% 3.75/1.01                [status(thm)],
% 3.75/1.01                [c_13850,c_11956,c_10831,c_10149,c_4873,c_3893,c_3243,
% 3.75/1.01                 c_2853,c_1963,c_1831,c_1613,c_1429,c_1428,c_1394,c_1045,
% 3.75/1.01                 c_1004,c_17,c_22]) ).
% 3.75/1.01  
% 3.75/1.01  
% 3.75/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.75/1.01  
% 3.75/1.01  ------                               Statistics
% 3.75/1.01  
% 3.75/1.01  ------ General
% 3.75/1.01  
% 3.75/1.01  abstr_ref_over_cycles:                  0
% 3.75/1.01  abstr_ref_under_cycles:                 0
% 3.75/1.01  gc_basic_clause_elim:                   0
% 3.75/1.01  forced_gc_time:                         0
% 3.75/1.01  parsing_time:                           0.008
% 3.75/1.01  unif_index_cands_time:                  0.
% 3.75/1.01  unif_index_add_time:                    0.
% 3.75/1.01  orderings_time:                         0.
% 3.75/1.01  out_proof_time:                         0.008
% 3.75/1.01  total_time:                             0.366
% 3.75/1.01  num_of_symbols:                         45
% 3.75/1.01  num_of_terms:                           9760
% 3.75/1.01  
% 3.75/1.01  ------ Preprocessing
% 3.75/1.01  
% 3.75/1.01  num_of_splits:                          0
% 3.75/1.01  num_of_split_atoms:                     0
% 3.75/1.01  num_of_reused_defs:                     0
% 3.75/1.01  num_eq_ax_congr_red:                    18
% 3.75/1.01  num_of_sem_filtered_clauses:            1
% 3.75/1.01  num_of_subtypes:                        0
% 3.75/1.01  monotx_restored_types:                  0
% 3.75/1.01  sat_num_of_epr_types:                   0
% 3.75/1.01  sat_num_of_non_cyclic_types:            0
% 3.75/1.01  sat_guarded_non_collapsed_types:        0
% 3.75/1.01  num_pure_diseq_elim:                    0
% 3.75/1.01  simp_replaced_by:                       0
% 3.75/1.01  res_preprocessed:                       80
% 3.75/1.01  prep_upred:                             0
% 3.75/1.01  prep_unflattend:                        6
% 3.75/1.01  smt_new_axioms:                         0
% 3.75/1.01  pred_elim_cands:                        4
% 3.75/1.01  pred_elim:                              0
% 3.75/1.01  pred_elim_cl:                           0
% 3.75/1.01  pred_elim_cycles:                       1
% 3.75/1.01  merged_defs:                            18
% 3.75/1.01  merged_defs_ncl:                        0
% 3.75/1.01  bin_hyper_res:                          18
% 3.75/1.01  prep_cycles:                            3
% 3.75/1.01  pred_elim_time:                         0.001
% 3.75/1.01  splitting_time:                         0.
% 3.75/1.01  sem_filter_time:                        0.
% 3.75/1.01  monotx_time:                            0.
% 3.75/1.01  subtype_inf_time:                       0.
% 3.75/1.01  
% 3.75/1.01  ------ Problem properties
% 3.75/1.01  
% 3.75/1.01  clauses:                                21
% 3.75/1.01  conjectures:                            4
% 3.75/1.01  epr:                                    2
% 3.75/1.01  horn:                                   17
% 3.75/1.01  ground:                                 4
% 3.75/1.01  unary:                                  6
% 3.75/1.01  binary:                                 11
% 3.75/1.01  lits:                                   40
% 3.75/1.01  lits_eq:                                10
% 3.75/1.01  fd_pure:                                0
% 3.75/1.01  fd_pseudo:                              0
% 3.75/1.01  fd_cond:                                2
% 3.75/1.01  fd_pseudo_cond:                         0
% 3.75/1.01  ac_symbols:                             0
% 3.75/1.01  
% 3.75/1.01  ------ Propositional Solver
% 3.75/1.01  
% 3.75/1.01  prop_solver_calls:                      27
% 3.75/1.01  prop_fast_solver_calls:                 868
% 3.75/1.01  smt_solver_calls:                       0
% 3.75/1.01  smt_fast_solver_calls:                  0
% 3.75/1.01  prop_num_of_clauses:                    4642
% 3.75/1.01  prop_preprocess_simplified:             9394
% 3.75/1.01  prop_fo_subsumed:                       11
% 3.75/1.01  prop_solver_time:                       0.
% 3.75/1.01  smt_solver_time:                        0.
% 3.75/1.01  smt_fast_solver_time:                   0.
% 3.75/1.01  prop_fast_solver_time:                  0.
% 3.75/1.01  prop_unsat_core_time:                   0.
% 3.75/1.01  
% 3.75/1.01  ------ QBF
% 3.75/1.01  
% 3.75/1.01  qbf_q_res:                              0
% 3.75/1.01  qbf_num_tautologies:                    0
% 3.75/1.01  qbf_prep_cycles:                        0
% 3.75/1.01  
% 3.75/1.01  ------ BMC1
% 3.75/1.01  
% 3.75/1.01  bmc1_current_bound:                     -1
% 3.75/1.01  bmc1_last_solved_bound:                 -1
% 3.75/1.01  bmc1_unsat_core_size:                   -1
% 3.75/1.01  bmc1_unsat_core_parents_size:           -1
% 3.75/1.01  bmc1_merge_next_fun:                    0
% 3.75/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.75/1.01  
% 3.75/1.01  ------ Instantiation
% 3.75/1.01  
% 3.75/1.01  inst_num_of_clauses:                    1502
% 3.75/1.01  inst_num_in_passive:                    359
% 3.75/1.01  inst_num_in_active:                     785
% 3.75/1.01  inst_num_in_unprocessed:                358
% 3.75/1.01  inst_num_of_loops:                      960
% 3.75/1.01  inst_num_of_learning_restarts:          0
% 3.75/1.01  inst_num_moves_active_passive:          170
% 3.75/1.01  inst_lit_activity:                      0
% 3.75/1.01  inst_lit_activity_moves:                0
% 3.75/1.01  inst_num_tautologies:                   0
% 3.75/1.01  inst_num_prop_implied:                  0
% 3.75/1.01  inst_num_existing_simplified:           0
% 3.75/1.01  inst_num_eq_res_simplified:             0
% 3.75/1.01  inst_num_child_elim:                    0
% 3.75/1.01  inst_num_of_dismatching_blockings:      912
% 3.75/1.01  inst_num_of_non_proper_insts:           1947
% 3.75/1.01  inst_num_of_duplicates:                 0
% 3.75/1.01  inst_inst_num_from_inst_to_res:         0
% 3.75/1.01  inst_dismatching_checking_time:         0.
% 3.75/1.01  
% 3.75/1.01  ------ Resolution
% 3.75/1.01  
% 3.75/1.01  res_num_of_clauses:                     0
% 3.75/1.01  res_num_in_passive:                     0
% 3.75/1.01  res_num_in_active:                      0
% 3.75/1.01  res_num_of_loops:                       83
% 3.75/1.01  res_forward_subset_subsumed:            215
% 3.75/1.01  res_backward_subset_subsumed:           0
% 3.75/1.01  res_forward_subsumed:                   0
% 3.75/1.01  res_backward_subsumed:                  0
% 3.75/1.01  res_forward_subsumption_resolution:     0
% 3.75/1.01  res_backward_subsumption_resolution:    0
% 3.75/1.01  res_clause_to_clause_subsumption:       1221
% 3.75/1.01  res_orphan_elimination:                 0
% 3.75/1.01  res_tautology_del:                      190
% 3.75/1.01  res_num_eq_res_simplified:              0
% 3.75/1.01  res_num_sel_changes:                    0
% 3.75/1.01  res_moves_from_active_to_pass:          0
% 3.75/1.01  
% 3.75/1.01  ------ Superposition
% 3.75/1.01  
% 3.75/1.01  sup_time_total:                         0.
% 3.75/1.01  sup_time_generating:                    0.
% 3.75/1.01  sup_time_sim_full:                      0.
% 3.75/1.01  sup_time_sim_immed:                     0.
% 3.75/1.01  
% 3.75/1.01  sup_num_of_clauses:                     272
% 3.75/1.01  sup_num_in_active:                      152
% 3.75/1.01  sup_num_in_passive:                     120
% 3.75/1.01  sup_num_of_loops:                       191
% 3.75/1.01  sup_fw_superposition:                   243
% 3.75/1.01  sup_bw_superposition:                   252
% 3.75/1.01  sup_immediate_simplified:               116
% 3.75/1.01  sup_given_eliminated:                   0
% 3.75/1.01  comparisons_done:                       0
% 3.75/1.01  comparisons_avoided:                    49
% 3.75/1.01  
% 3.75/1.01  ------ Simplifications
% 3.75/1.01  
% 3.75/1.01  
% 3.75/1.01  sim_fw_subset_subsumed:                 81
% 3.75/1.01  sim_bw_subset_subsumed:                 33
% 3.75/1.01  sim_fw_subsumed:                        14
% 3.75/1.01  sim_bw_subsumed:                        6
% 3.75/1.01  sim_fw_subsumption_res:                 1
% 3.75/1.01  sim_bw_subsumption_res:                 0
% 3.75/1.01  sim_tautology_del:                      2
% 3.75/1.01  sim_eq_tautology_del:                   11
% 3.75/1.01  sim_eq_res_simp:                        1
% 3.75/1.01  sim_fw_demodulated:                     12
% 3.75/1.01  sim_bw_demodulated:                     20
% 3.75/1.01  sim_light_normalised:                   12
% 3.75/1.01  sim_joinable_taut:                      0
% 3.75/1.01  sim_joinable_simp:                      0
% 3.75/1.01  sim_ac_normalised:                      0
% 3.75/1.01  sim_smt_subsumption:                    0
% 3.75/1.01  
%------------------------------------------------------------------------------
