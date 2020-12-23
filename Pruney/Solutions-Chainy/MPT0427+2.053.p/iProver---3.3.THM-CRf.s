%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:42:37 EST 2020

% Result     : Theorem 7.32s
% Output     : CNFRefutation 7.32s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 493 expanded)
%              Number of clauses        :   96 ( 225 expanded)
%              Number of leaves         :   21 ( 112 expanded)
%              Depth                    :   19
%              Number of atoms          :  358 (1425 expanded)
%              Number of equality atoms :  163 ( 391 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f16,plain,(
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

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f31])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( r1_tarski(X1,X2)
           => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( r1_tarski(X1,X2)
             => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f29,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f30,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f29])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
     => ( ~ r1_tarski(k8_setfam_1(X0,sK4),k8_setfam_1(X0,X1))
        & r1_tarski(X1,sK4)
        & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
            & r1_tarski(X1,X2)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(sK2,X2),k8_setfam_1(sK2,sK3))
          & r1_tarski(sK3,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK2))) )
      & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ~ r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3))
    & r1_tarski(sK3,sK4)
    & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2)))
    & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f30,f38,f37])).

fof(f60,plain,(
    r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f39])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f59,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(cnf_transformation,[],[f39])).

fof(f61,plain,(
    ~ r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f39])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ( k1_xboole_0 = X1
         => k8_setfam_1(X0,X1) = X0 )
        & ( k1_xboole_0 != X1
         => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ( k8_setfam_1(X0,X1) = X0
          | k1_xboole_0 != X1 )
        & ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
          | k1_xboole_0 = X1 ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f62,plain,(
    ! [X0] :
      ( k8_setfam_1(X0,k1_xboole_0) = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f51])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f58,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(cnf_transformation,[],[f39])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f18,f33])).

fof(f43,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_15123,plain,
    ( ~ r2_hidden(sK1(sK3),X0)
    | ~ r2_hidden(sK1(sK3),sK3)
    | ~ r1_xboole_0(X0,sK3) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_41250,plain,
    ( ~ r2_hidden(sK1(sK3),sK3)
    | ~ r1_xboole_0(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_15123])).

cnf(c_9,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_934,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_928,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1385,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_934,c_928])).

cnf(c_19,negated_conjecture,
    ( r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_924,plain,
    ( r1_tarski(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_17,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_926,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_xboole_0(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_935,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_xboole_0(X0,k4_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_7,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_936,plain,
    ( k4_xboole_0(X0,X1) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1653,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X2)) = X0
    | r1_tarski(X0,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_935,c_936])).

cnf(c_1659,plain,
    ( k4_xboole_0(k1_setfam_1(X0),k4_xboole_0(X1,k1_setfam_1(X2))) = k1_setfam_1(X0)
    | k1_xboole_0 = X2
    | r1_tarski(X2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_926,c_1653])).

cnf(c_3536,plain,
    ( k4_xboole_0(k1_setfam_1(sK4),k4_xboole_0(X0,k1_setfam_1(sK3))) = k1_setfam_1(sK4)
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_924,c_1659])).

cnf(c_3780,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(X0,k4_xboole_0(X1,k1_setfam_1(sK3))) != iProver_top
    | r1_xboole_0(X0,k1_setfam_1(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3536,c_935])).

cnf(c_5272,plain,
    ( sK3 = k1_xboole_0
    | r1_xboole_0(k1_xboole_0,k1_setfam_1(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1385,c_3780])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_18,negated_conjecture,
    ( ~ r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | m1_subset_1(k8_setfam_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1096,plain,
    ( m1_subset_1(k8_setfam_1(sK2,sK4),k1_zfmisc_1(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_405,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1352,plain,
    ( k8_setfam_1(sK2,sK4) = k8_setfam_1(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_405])).

cnf(c_1531,plain,
    ( ~ m1_subset_1(k8_setfam_1(sK2,sK4),k1_zfmisc_1(X0))
    | r1_tarski(k8_setfam_1(sK2,sK4),X0) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1741,plain,
    ( ~ m1_subset_1(k8_setfam_1(sK2,sK4),k1_zfmisc_1(sK2))
    | r1_tarski(k8_setfam_1(sK2,sK4),sK2) ),
    inference(instantiation,[status(thm)],[c_1531])).

cnf(c_1984,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_405])).

cnf(c_409,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1539,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k8_setfam_1(sK2,sK4),X2)
    | X2 != X1
    | k8_setfam_1(sK2,sK4) != X0 ),
    inference(instantiation,[status(thm)],[c_409])).

cnf(c_1756,plain,
    ( ~ r1_tarski(k8_setfam_1(sK2,sK4),X0)
    | r1_tarski(k8_setfam_1(sK2,sK4),X1)
    | X1 != X0
    | k8_setfam_1(sK2,sK4) != k8_setfam_1(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_1539])).

cnf(c_2523,plain,
    ( r1_tarski(k8_setfam_1(sK2,sK4),X0)
    | ~ r1_tarski(k8_setfam_1(sK2,sK4),sK2)
    | X0 != sK2
    | k8_setfam_1(sK2,sK4) != k8_setfam_1(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_1756])).

cnf(c_3076,plain,
    ( r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,k1_xboole_0))
    | ~ r1_tarski(k8_setfam_1(sK2,sK4),sK2)
    | k8_setfam_1(sK2,sK4) != k8_setfam_1(sK2,sK4)
    | k8_setfam_1(sK2,k1_xboole_0) != sK2 ),
    inference(instantiation,[status(thm)],[c_2523])).

cnf(c_10,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
    | k8_setfam_1(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_3077,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK2)))
    | k8_setfam_1(sK2,k1_xboole_0) = sK2 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_412,plain,
    ( X0 != X1
    | X2 != X3
    | k8_setfam_1(X0,X2) = k8_setfam_1(X1,X3) ),
    theory(equality)).

cnf(c_1172,plain,
    ( k8_setfam_1(sK2,sK3) = k8_setfam_1(X0,X1)
    | sK3 != X1
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_412])).

cnf(c_3498,plain,
    ( k8_setfam_1(sK2,sK3) = k8_setfam_1(sK2,X0)
    | sK3 != X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1172])).

cnf(c_3499,plain,
    ( k8_setfam_1(sK2,sK3) = k8_setfam_1(sK2,k1_xboole_0)
    | sK3 != k1_xboole_0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_3498])).

cnf(c_1086,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_5100,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(instantiation,[status(thm)],[c_1086])).

cnf(c_1116,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3))
    | k8_setfam_1(sK2,sK3) != X1
    | k8_setfam_1(sK2,sK4) != X0 ),
    inference(instantiation,[status(thm)],[c_409])).

cnf(c_1171,plain,
    ( ~ r1_tarski(X0,k8_setfam_1(X1,X2))
    | r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3))
    | k8_setfam_1(sK2,sK3) != k8_setfam_1(X1,X2)
    | k8_setfam_1(sK2,sK4) != X0 ),
    inference(instantiation,[status(thm)],[c_1116])).

cnf(c_1358,plain,
    ( ~ r1_tarski(k8_setfam_1(X0,X1),k8_setfam_1(X2,X3))
    | r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3))
    | k8_setfam_1(sK2,sK3) != k8_setfam_1(X2,X3)
    | k8_setfam_1(sK2,sK4) != k8_setfam_1(X0,X1) ),
    inference(instantiation,[status(thm)],[c_1171])).

cnf(c_4929,plain,
    ( ~ r1_tarski(k8_setfam_1(X0,X1),k8_setfam_1(sK2,X2))
    | r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3))
    | k8_setfam_1(sK2,sK3) != k8_setfam_1(sK2,X2)
    | k8_setfam_1(sK2,sK4) != k8_setfam_1(X0,X1) ),
    inference(instantiation,[status(thm)],[c_1358])).

cnf(c_7335,plain,
    ( ~ r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,X0))
    | r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3))
    | k8_setfam_1(sK2,sK3) != k8_setfam_1(sK2,X0)
    | k8_setfam_1(sK2,sK4) != k8_setfam_1(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_4929])).

cnf(c_7337,plain,
    ( r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3))
    | ~ r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,k1_xboole_0))
    | k8_setfam_1(sK2,sK3) != k8_setfam_1(sK2,k1_xboole_0)
    | k8_setfam_1(sK2,sK4) != k8_setfam_1(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_7335])).

cnf(c_9068,plain,
    ( r1_xboole_0(k1_xboole_0,k1_setfam_1(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5272,c_20,c_18,c_1096,c_1352,c_1741,c_1984,c_3076,c_3077,c_3499,c_5100,c_7337])).

cnf(c_9073,plain,
    ( k4_xboole_0(k1_xboole_0,k1_setfam_1(sK4)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_9068,c_936])).

cnf(c_923,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1386,plain,
    ( r1_tarski(sK4,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_923,c_928])).

cnf(c_3538,plain,
    ( k4_xboole_0(k1_setfam_1(k1_zfmisc_1(sK2)),k4_xboole_0(X0,k1_setfam_1(sK4))) = k1_setfam_1(k1_zfmisc_1(sK2))
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1386,c_1659])).

cnf(c_9397,plain,
    ( k4_xboole_0(k1_setfam_1(k1_zfmisc_1(sK2)),k1_xboole_0) = k1_setfam_1(k1_zfmisc_1(sK2))
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_9073,c_3538])).

cnf(c_24,plain,
    ( r1_tarski(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k6_setfam_1(X1,X0) = k8_setfam_1(X1,X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_932,plain,
    ( k6_setfam_1(X0,X1) = k8_setfam_1(X0,X1)
    | k1_xboole_0 = X1
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2722,plain,
    ( k6_setfam_1(sK2,sK4) = k8_setfam_1(sK2,sK4)
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_923,c_932])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k6_setfam_1(X1,X0) = k1_setfam_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_930,plain,
    ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2028,plain,
    ( k6_setfam_1(sK2,sK4) = k1_setfam_1(sK4) ),
    inference(superposition,[status(thm)],[c_923,c_930])).

cnf(c_2731,plain,
    ( k8_setfam_1(sK2,sK4) = k1_setfam_1(sK4)
    | sK4 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2722,c_2028])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_922,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2723,plain,
    ( k6_setfam_1(sK2,sK3) = k8_setfam_1(sK2,sK3)
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_922,c_932])).

cnf(c_2029,plain,
    ( k6_setfam_1(sK2,sK3) = k1_setfam_1(sK3) ),
    inference(superposition,[status(thm)],[c_922,c_930])).

cnf(c_2726,plain,
    ( k8_setfam_1(sK2,sK3) = k1_setfam_1(sK3)
    | sK3 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2723,c_2029])).

cnf(c_925,plain,
    ( r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3838,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(k8_setfam_1(sK2,sK4),k1_setfam_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2726,c_925])).

cnf(c_3935,plain,
    ( sK3 = k1_xboole_0
    | sK4 = k1_xboole_0
    | r1_tarski(k1_setfam_1(sK4),k1_setfam_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2731,c_3838])).

cnf(c_5033,plain,
    ( sK3 = k1_xboole_0
    | sK4 = k1_xboole_0
    | r1_tarski(sK3,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_926,c_3935])).

cnf(c_10825,plain,
    ( sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9397,c_20,c_24,c_18,c_1096,c_1352,c_1741,c_1984,c_3076,c_3077,c_3499,c_5033,c_5100,c_7337])).

cnf(c_10881,plain,
    ( r1_tarski(sK3,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_10825,c_924])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_939,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2635,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1385,c_939])).

cnf(c_11090,plain,
    ( r1_tarski(sK3,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_10881,c_2635])).

cnf(c_1662,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(X0,k1_zfmisc_1(sK2))) = sK4 ),
    inference(superposition,[status(thm)],[c_1386,c_1653])).

cnf(c_5,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_938,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1658,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X0)) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_938,c_1653])).

cnf(c_4638,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k1_zfmisc_1(sK2)),X1),sK4) = k4_xboole_0(k4_xboole_0(X0,k1_zfmisc_1(sK2)),X1) ),
    inference(superposition,[status(thm)],[c_1662,c_1658])).

cnf(c_1660,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(X0,sK4)) = sK3 ),
    inference(superposition,[status(thm)],[c_924,c_1653])).

cnf(c_1852,plain,
    ( r1_tarski(X0,k4_xboole_0(X1,sK4)) != iProver_top
    | r1_xboole_0(X0,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1660,c_935])).

cnf(c_7131,plain,
    ( r1_tarski(X0,k4_xboole_0(k4_xboole_0(X1,k1_zfmisc_1(sK2)),X2)) != iProver_top
    | r1_xboole_0(X0,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4638,c_1852])).

cnf(c_11208,plain,
    ( r1_xboole_0(sK3,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_11090,c_7131])).

cnf(c_11225,plain,
    ( r1_xboole_0(sK3,sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_11208])).

cnf(c_3,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_2814,plain,
    ( r2_hidden(sK1(sK3),sK3)
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_406,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1326,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_406])).

cnf(c_1883,plain,
    ( X0 != sK3
    | sK3 = X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1326])).

cnf(c_1884,plain,
    ( sK3 != sK3
    | sK3 = k1_xboole_0
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_1883])).

cnf(c_1324,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_405])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_41250,c_11225,c_7337,c_5100,c_3499,c_3077,c_3076,c_2814,c_1984,c_1884,c_1741,c_1352,c_1324,c_1096,c_18,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.20/0.34  % WCLimit    : 600
% 0.20/0.34  % DateTime   : Tue Dec  1 16:03:05 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.35  % Running in FOF mode
% 7.32/1.51  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.32/1.51  
% 7.32/1.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.32/1.51  
% 7.32/1.51  ------  iProver source info
% 7.32/1.51  
% 7.32/1.51  git: date: 2020-06-30 10:37:57 +0100
% 7.32/1.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.32/1.51  git: non_committed_changes: false
% 7.32/1.51  git: last_make_outside_of_git: false
% 7.32/1.51  
% 7.32/1.51  ------ 
% 7.32/1.51  
% 7.32/1.51  ------ Input Options
% 7.32/1.51  
% 7.32/1.51  --out_options                           all
% 7.32/1.51  --tptp_safe_out                         true
% 7.32/1.51  --problem_path                          ""
% 7.32/1.51  --include_path                          ""
% 7.32/1.51  --clausifier                            res/vclausify_rel
% 7.32/1.51  --clausifier_options                    --mode clausify
% 7.32/1.51  --stdin                                 false
% 7.32/1.51  --stats_out                             all
% 7.32/1.51  
% 7.32/1.51  ------ General Options
% 7.32/1.51  
% 7.32/1.51  --fof                                   false
% 7.32/1.51  --time_out_real                         305.
% 7.32/1.51  --time_out_virtual                      -1.
% 7.32/1.51  --symbol_type_check                     false
% 7.32/1.51  --clausify_out                          false
% 7.32/1.51  --sig_cnt_out                           false
% 7.32/1.51  --trig_cnt_out                          false
% 7.32/1.51  --trig_cnt_out_tolerance                1.
% 7.32/1.51  --trig_cnt_out_sk_spl                   false
% 7.32/1.51  --abstr_cl_out                          false
% 7.32/1.51  
% 7.32/1.51  ------ Global Options
% 7.32/1.51  
% 7.32/1.51  --schedule                              default
% 7.32/1.51  --add_important_lit                     false
% 7.32/1.51  --prop_solver_per_cl                    1000
% 7.32/1.51  --min_unsat_core                        false
% 7.32/1.51  --soft_assumptions                      false
% 7.32/1.51  --soft_lemma_size                       3
% 7.32/1.51  --prop_impl_unit_size                   0
% 7.32/1.51  --prop_impl_unit                        []
% 7.32/1.51  --share_sel_clauses                     true
% 7.32/1.51  --reset_solvers                         false
% 7.32/1.51  --bc_imp_inh                            [conj_cone]
% 7.32/1.51  --conj_cone_tolerance                   3.
% 7.32/1.51  --extra_neg_conj                        none
% 7.32/1.51  --large_theory_mode                     true
% 7.32/1.51  --prolific_symb_bound                   200
% 7.32/1.51  --lt_threshold                          2000
% 7.32/1.51  --clause_weak_htbl                      true
% 7.32/1.51  --gc_record_bc_elim                     false
% 7.32/1.51  
% 7.32/1.51  ------ Preprocessing Options
% 7.32/1.51  
% 7.32/1.51  --preprocessing_flag                    true
% 7.32/1.51  --time_out_prep_mult                    0.1
% 7.32/1.51  --splitting_mode                        input
% 7.32/1.51  --splitting_grd                         true
% 7.32/1.51  --splitting_cvd                         false
% 7.32/1.51  --splitting_cvd_svl                     false
% 7.32/1.51  --splitting_nvd                         32
% 7.32/1.51  --sub_typing                            true
% 7.32/1.51  --prep_gs_sim                           true
% 7.32/1.51  --prep_unflatten                        true
% 7.32/1.51  --prep_res_sim                          true
% 7.32/1.51  --prep_upred                            true
% 7.32/1.51  --prep_sem_filter                       exhaustive
% 7.32/1.51  --prep_sem_filter_out                   false
% 7.32/1.51  --pred_elim                             true
% 7.32/1.51  --res_sim_input                         true
% 7.32/1.51  --eq_ax_congr_red                       true
% 7.32/1.51  --pure_diseq_elim                       true
% 7.32/1.51  --brand_transform                       false
% 7.32/1.51  --non_eq_to_eq                          false
% 7.32/1.51  --prep_def_merge                        true
% 7.32/1.51  --prep_def_merge_prop_impl              false
% 7.32/1.51  --prep_def_merge_mbd                    true
% 7.32/1.51  --prep_def_merge_tr_red                 false
% 7.32/1.51  --prep_def_merge_tr_cl                  false
% 7.32/1.51  --smt_preprocessing                     true
% 7.32/1.51  --smt_ac_axioms                         fast
% 7.32/1.51  --preprocessed_out                      false
% 7.32/1.51  --preprocessed_stats                    false
% 7.32/1.51  
% 7.32/1.51  ------ Abstraction refinement Options
% 7.32/1.51  
% 7.32/1.51  --abstr_ref                             []
% 7.32/1.51  --abstr_ref_prep                        false
% 7.32/1.51  --abstr_ref_until_sat                   false
% 7.32/1.51  --abstr_ref_sig_restrict                funpre
% 7.32/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.32/1.51  --abstr_ref_under                       []
% 7.32/1.51  
% 7.32/1.51  ------ SAT Options
% 7.32/1.51  
% 7.32/1.51  --sat_mode                              false
% 7.32/1.51  --sat_fm_restart_options                ""
% 7.32/1.51  --sat_gr_def                            false
% 7.32/1.51  --sat_epr_types                         true
% 7.32/1.51  --sat_non_cyclic_types                  false
% 7.32/1.51  --sat_finite_models                     false
% 7.32/1.51  --sat_fm_lemmas                         false
% 7.32/1.51  --sat_fm_prep                           false
% 7.32/1.51  --sat_fm_uc_incr                        true
% 7.32/1.51  --sat_out_model                         small
% 7.32/1.51  --sat_out_clauses                       false
% 7.32/1.51  
% 7.32/1.51  ------ QBF Options
% 7.32/1.51  
% 7.32/1.51  --qbf_mode                              false
% 7.32/1.51  --qbf_elim_univ                         false
% 7.32/1.51  --qbf_dom_inst                          none
% 7.32/1.51  --qbf_dom_pre_inst                      false
% 7.32/1.51  --qbf_sk_in                             false
% 7.32/1.51  --qbf_pred_elim                         true
% 7.32/1.51  --qbf_split                             512
% 7.32/1.51  
% 7.32/1.51  ------ BMC1 Options
% 7.32/1.51  
% 7.32/1.51  --bmc1_incremental                      false
% 7.32/1.51  --bmc1_axioms                           reachable_all
% 7.32/1.51  --bmc1_min_bound                        0
% 7.32/1.51  --bmc1_max_bound                        -1
% 7.32/1.51  --bmc1_max_bound_default                -1
% 7.32/1.51  --bmc1_symbol_reachability              true
% 7.32/1.51  --bmc1_property_lemmas                  false
% 7.32/1.51  --bmc1_k_induction                      false
% 7.32/1.51  --bmc1_non_equiv_states                 false
% 7.32/1.51  --bmc1_deadlock                         false
% 7.32/1.51  --bmc1_ucm                              false
% 7.32/1.51  --bmc1_add_unsat_core                   none
% 7.32/1.51  --bmc1_unsat_core_children              false
% 7.32/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.32/1.51  --bmc1_out_stat                         full
% 7.32/1.51  --bmc1_ground_init                      false
% 7.32/1.51  --bmc1_pre_inst_next_state              false
% 7.32/1.51  --bmc1_pre_inst_state                   false
% 7.32/1.51  --bmc1_pre_inst_reach_state             false
% 7.32/1.51  --bmc1_out_unsat_core                   false
% 7.32/1.51  --bmc1_aig_witness_out                  false
% 7.32/1.51  --bmc1_verbose                          false
% 7.32/1.51  --bmc1_dump_clauses_tptp                false
% 7.32/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.32/1.51  --bmc1_dump_file                        -
% 7.32/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.32/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.32/1.51  --bmc1_ucm_extend_mode                  1
% 7.32/1.51  --bmc1_ucm_init_mode                    2
% 7.32/1.51  --bmc1_ucm_cone_mode                    none
% 7.32/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.32/1.51  --bmc1_ucm_relax_model                  4
% 7.32/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.32/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.32/1.51  --bmc1_ucm_layered_model                none
% 7.32/1.51  --bmc1_ucm_max_lemma_size               10
% 7.32/1.51  
% 7.32/1.51  ------ AIG Options
% 7.32/1.51  
% 7.32/1.51  --aig_mode                              false
% 7.32/1.51  
% 7.32/1.51  ------ Instantiation Options
% 7.32/1.51  
% 7.32/1.51  --instantiation_flag                    true
% 7.32/1.51  --inst_sos_flag                         false
% 7.32/1.51  --inst_sos_phase                        true
% 7.32/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.32/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.32/1.51  --inst_lit_sel_side                     num_symb
% 7.32/1.51  --inst_solver_per_active                1400
% 7.32/1.51  --inst_solver_calls_frac                1.
% 7.32/1.51  --inst_passive_queue_type               priority_queues
% 7.32/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.32/1.51  --inst_passive_queues_freq              [25;2]
% 7.32/1.51  --inst_dismatching                      true
% 7.32/1.51  --inst_eager_unprocessed_to_passive     true
% 7.32/1.51  --inst_prop_sim_given                   true
% 7.32/1.51  --inst_prop_sim_new                     false
% 7.32/1.51  --inst_subs_new                         false
% 7.32/1.51  --inst_eq_res_simp                      false
% 7.32/1.51  --inst_subs_given                       false
% 7.32/1.51  --inst_orphan_elimination               true
% 7.32/1.51  --inst_learning_loop_flag               true
% 7.32/1.51  --inst_learning_start                   3000
% 7.32/1.51  --inst_learning_factor                  2
% 7.32/1.51  --inst_start_prop_sim_after_learn       3
% 7.32/1.51  --inst_sel_renew                        solver
% 7.32/1.51  --inst_lit_activity_flag                true
% 7.32/1.51  --inst_restr_to_given                   false
% 7.32/1.51  --inst_activity_threshold               500
% 7.32/1.51  --inst_out_proof                        true
% 7.32/1.51  
% 7.32/1.51  ------ Resolution Options
% 7.32/1.51  
% 7.32/1.51  --resolution_flag                       true
% 7.32/1.51  --res_lit_sel                           adaptive
% 7.32/1.51  --res_lit_sel_side                      none
% 7.32/1.51  --res_ordering                          kbo
% 7.32/1.51  --res_to_prop_solver                    active
% 7.32/1.51  --res_prop_simpl_new                    false
% 7.32/1.51  --res_prop_simpl_given                  true
% 7.32/1.51  --res_passive_queue_type                priority_queues
% 7.32/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.32/1.51  --res_passive_queues_freq               [15;5]
% 7.32/1.51  --res_forward_subs                      full
% 7.32/1.51  --res_backward_subs                     full
% 7.32/1.51  --res_forward_subs_resolution           true
% 7.32/1.51  --res_backward_subs_resolution          true
% 7.32/1.51  --res_orphan_elimination                true
% 7.32/1.51  --res_time_limit                        2.
% 7.32/1.51  --res_out_proof                         true
% 7.32/1.51  
% 7.32/1.51  ------ Superposition Options
% 7.32/1.51  
% 7.32/1.51  --superposition_flag                    true
% 7.32/1.51  --sup_passive_queue_type                priority_queues
% 7.32/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.32/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.32/1.51  --demod_completeness_check              fast
% 7.32/1.51  --demod_use_ground                      true
% 7.32/1.51  --sup_to_prop_solver                    passive
% 7.32/1.51  --sup_prop_simpl_new                    true
% 7.32/1.51  --sup_prop_simpl_given                  true
% 7.32/1.51  --sup_fun_splitting                     false
% 7.32/1.51  --sup_smt_interval                      50000
% 7.32/1.51  
% 7.32/1.51  ------ Superposition Simplification Setup
% 7.32/1.51  
% 7.32/1.51  --sup_indices_passive                   []
% 7.32/1.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.32/1.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.32/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.32/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.32/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.32/1.51  --sup_full_bw                           [BwDemod]
% 7.32/1.51  --sup_immed_triv                        [TrivRules]
% 7.32/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.32/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.32/1.51  --sup_immed_bw_main                     []
% 7.32/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.32/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.32/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.32/1.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.32/1.51  
% 7.32/1.51  ------ Combination Options
% 7.32/1.51  
% 7.32/1.51  --comb_res_mult                         3
% 7.32/1.51  --comb_sup_mult                         2
% 7.32/1.51  --comb_inst_mult                        10
% 7.32/1.51  
% 7.32/1.51  ------ Debug Options
% 7.32/1.51  
% 7.32/1.51  --dbg_backtrace                         false
% 7.32/1.51  --dbg_dump_prop_clauses                 false
% 7.32/1.51  --dbg_dump_prop_clauses_file            -
% 7.32/1.51  --dbg_out_stat                          false
% 7.32/1.51  ------ Parsing...
% 7.32/1.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.32/1.51  
% 7.32/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.32/1.51  
% 7.32/1.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.32/1.51  
% 7.32/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.32/1.51  ------ Proving...
% 7.32/1.51  ------ Problem Properties 
% 7.32/1.51  
% 7.32/1.51  
% 7.32/1.51  clauses                                 22
% 7.32/1.51  conjectures                             4
% 7.32/1.51  EPR                                     3
% 7.32/1.51  Horn                                    17
% 7.32/1.51  unary                                   6
% 7.32/1.51  binary                                  11
% 7.32/1.51  lits                                    43
% 7.32/1.51  lits eq                                 8
% 7.32/1.51  fd_pure                                 0
% 7.32/1.51  fd_pseudo                               0
% 7.32/1.51  fd_cond                                 3
% 7.32/1.51  fd_pseudo_cond                          0
% 7.32/1.51  AC symbols                              0
% 7.32/1.51  
% 7.32/1.51  ------ Schedule dynamic 5 is on 
% 7.32/1.51  
% 7.32/1.51  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.32/1.51  
% 7.32/1.51  
% 7.32/1.51  ------ 
% 7.32/1.51  Current options:
% 7.32/1.51  ------ 
% 7.32/1.51  
% 7.32/1.51  ------ Input Options
% 7.32/1.51  
% 7.32/1.51  --out_options                           all
% 7.32/1.51  --tptp_safe_out                         true
% 7.32/1.51  --problem_path                          ""
% 7.32/1.51  --include_path                          ""
% 7.32/1.51  --clausifier                            res/vclausify_rel
% 7.32/1.51  --clausifier_options                    --mode clausify
% 7.32/1.51  --stdin                                 false
% 7.32/1.51  --stats_out                             all
% 7.32/1.51  
% 7.32/1.51  ------ General Options
% 7.32/1.51  
% 7.32/1.51  --fof                                   false
% 7.32/1.51  --time_out_real                         305.
% 7.32/1.51  --time_out_virtual                      -1.
% 7.32/1.51  --symbol_type_check                     false
% 7.32/1.51  --clausify_out                          false
% 7.32/1.51  --sig_cnt_out                           false
% 7.32/1.51  --trig_cnt_out                          false
% 7.32/1.51  --trig_cnt_out_tolerance                1.
% 7.32/1.51  --trig_cnt_out_sk_spl                   false
% 7.32/1.51  --abstr_cl_out                          false
% 7.32/1.51  
% 7.32/1.51  ------ Global Options
% 7.32/1.51  
% 7.32/1.51  --schedule                              default
% 7.32/1.51  --add_important_lit                     false
% 7.32/1.51  --prop_solver_per_cl                    1000
% 7.32/1.51  --min_unsat_core                        false
% 7.32/1.51  --soft_assumptions                      false
% 7.32/1.51  --soft_lemma_size                       3
% 7.32/1.51  --prop_impl_unit_size                   0
% 7.32/1.51  --prop_impl_unit                        []
% 7.32/1.51  --share_sel_clauses                     true
% 7.32/1.51  --reset_solvers                         false
% 7.32/1.51  --bc_imp_inh                            [conj_cone]
% 7.32/1.51  --conj_cone_tolerance                   3.
% 7.32/1.51  --extra_neg_conj                        none
% 7.32/1.51  --large_theory_mode                     true
% 7.32/1.51  --prolific_symb_bound                   200
% 7.32/1.51  --lt_threshold                          2000
% 7.32/1.51  --clause_weak_htbl                      true
% 7.32/1.51  --gc_record_bc_elim                     false
% 7.32/1.51  
% 7.32/1.51  ------ Preprocessing Options
% 7.32/1.51  
% 7.32/1.51  --preprocessing_flag                    true
% 7.32/1.51  --time_out_prep_mult                    0.1
% 7.32/1.51  --splitting_mode                        input
% 7.32/1.51  --splitting_grd                         true
% 7.32/1.51  --splitting_cvd                         false
% 7.32/1.51  --splitting_cvd_svl                     false
% 7.32/1.51  --splitting_nvd                         32
% 7.32/1.51  --sub_typing                            true
% 7.32/1.51  --prep_gs_sim                           true
% 7.32/1.51  --prep_unflatten                        true
% 7.32/1.51  --prep_res_sim                          true
% 7.32/1.51  --prep_upred                            true
% 7.32/1.51  --prep_sem_filter                       exhaustive
% 7.32/1.51  --prep_sem_filter_out                   false
% 7.32/1.51  --pred_elim                             true
% 7.32/1.51  --res_sim_input                         true
% 7.32/1.51  --eq_ax_congr_red                       true
% 7.32/1.51  --pure_diseq_elim                       true
% 7.32/1.51  --brand_transform                       false
% 7.32/1.51  --non_eq_to_eq                          false
% 7.32/1.51  --prep_def_merge                        true
% 7.32/1.51  --prep_def_merge_prop_impl              false
% 7.32/1.51  --prep_def_merge_mbd                    true
% 7.32/1.51  --prep_def_merge_tr_red                 false
% 7.32/1.51  --prep_def_merge_tr_cl                  false
% 7.32/1.51  --smt_preprocessing                     true
% 7.32/1.51  --smt_ac_axioms                         fast
% 7.32/1.51  --preprocessed_out                      false
% 7.32/1.51  --preprocessed_stats                    false
% 7.32/1.51  
% 7.32/1.51  ------ Abstraction refinement Options
% 7.32/1.51  
% 7.32/1.51  --abstr_ref                             []
% 7.32/1.51  --abstr_ref_prep                        false
% 7.32/1.51  --abstr_ref_until_sat                   false
% 7.32/1.51  --abstr_ref_sig_restrict                funpre
% 7.32/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.32/1.51  --abstr_ref_under                       []
% 7.32/1.51  
% 7.32/1.51  ------ SAT Options
% 7.32/1.51  
% 7.32/1.51  --sat_mode                              false
% 7.32/1.51  --sat_fm_restart_options                ""
% 7.32/1.51  --sat_gr_def                            false
% 7.32/1.51  --sat_epr_types                         true
% 7.32/1.51  --sat_non_cyclic_types                  false
% 7.32/1.51  --sat_finite_models                     false
% 7.32/1.51  --sat_fm_lemmas                         false
% 7.32/1.51  --sat_fm_prep                           false
% 7.32/1.51  --sat_fm_uc_incr                        true
% 7.32/1.51  --sat_out_model                         small
% 7.32/1.51  --sat_out_clauses                       false
% 7.32/1.51  
% 7.32/1.51  ------ QBF Options
% 7.32/1.51  
% 7.32/1.51  --qbf_mode                              false
% 7.32/1.51  --qbf_elim_univ                         false
% 7.32/1.51  --qbf_dom_inst                          none
% 7.32/1.51  --qbf_dom_pre_inst                      false
% 7.32/1.51  --qbf_sk_in                             false
% 7.32/1.51  --qbf_pred_elim                         true
% 7.32/1.51  --qbf_split                             512
% 7.32/1.51  
% 7.32/1.51  ------ BMC1 Options
% 7.32/1.51  
% 7.32/1.51  --bmc1_incremental                      false
% 7.32/1.51  --bmc1_axioms                           reachable_all
% 7.32/1.51  --bmc1_min_bound                        0
% 7.32/1.51  --bmc1_max_bound                        -1
% 7.32/1.51  --bmc1_max_bound_default                -1
% 7.32/1.51  --bmc1_symbol_reachability              true
% 7.32/1.51  --bmc1_property_lemmas                  false
% 7.32/1.51  --bmc1_k_induction                      false
% 7.32/1.51  --bmc1_non_equiv_states                 false
% 7.32/1.51  --bmc1_deadlock                         false
% 7.32/1.51  --bmc1_ucm                              false
% 7.32/1.51  --bmc1_add_unsat_core                   none
% 7.32/1.51  --bmc1_unsat_core_children              false
% 7.32/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.32/1.51  --bmc1_out_stat                         full
% 7.32/1.51  --bmc1_ground_init                      false
% 7.32/1.51  --bmc1_pre_inst_next_state              false
% 7.32/1.51  --bmc1_pre_inst_state                   false
% 7.32/1.51  --bmc1_pre_inst_reach_state             false
% 7.32/1.51  --bmc1_out_unsat_core                   false
% 7.32/1.51  --bmc1_aig_witness_out                  false
% 7.32/1.51  --bmc1_verbose                          false
% 7.32/1.51  --bmc1_dump_clauses_tptp                false
% 7.32/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.32/1.51  --bmc1_dump_file                        -
% 7.32/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.32/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.32/1.51  --bmc1_ucm_extend_mode                  1
% 7.32/1.51  --bmc1_ucm_init_mode                    2
% 7.32/1.51  --bmc1_ucm_cone_mode                    none
% 7.32/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.32/1.51  --bmc1_ucm_relax_model                  4
% 7.32/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.32/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.32/1.51  --bmc1_ucm_layered_model                none
% 7.32/1.51  --bmc1_ucm_max_lemma_size               10
% 7.32/1.51  
% 7.32/1.51  ------ AIG Options
% 7.32/1.51  
% 7.32/1.51  --aig_mode                              false
% 7.32/1.51  
% 7.32/1.51  ------ Instantiation Options
% 7.32/1.51  
% 7.32/1.51  --instantiation_flag                    true
% 7.32/1.51  --inst_sos_flag                         false
% 7.32/1.51  --inst_sos_phase                        true
% 7.32/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.32/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.32/1.51  --inst_lit_sel_side                     none
% 7.32/1.51  --inst_solver_per_active                1400
% 7.32/1.51  --inst_solver_calls_frac                1.
% 7.32/1.51  --inst_passive_queue_type               priority_queues
% 7.32/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.32/1.51  --inst_passive_queues_freq              [25;2]
% 7.32/1.51  --inst_dismatching                      true
% 7.32/1.51  --inst_eager_unprocessed_to_passive     true
% 7.32/1.51  --inst_prop_sim_given                   true
% 7.32/1.51  --inst_prop_sim_new                     false
% 7.32/1.51  --inst_subs_new                         false
% 7.32/1.51  --inst_eq_res_simp                      false
% 7.32/1.51  --inst_subs_given                       false
% 7.32/1.51  --inst_orphan_elimination               true
% 7.32/1.51  --inst_learning_loop_flag               true
% 7.32/1.51  --inst_learning_start                   3000
% 7.32/1.51  --inst_learning_factor                  2
% 7.32/1.51  --inst_start_prop_sim_after_learn       3
% 7.32/1.51  --inst_sel_renew                        solver
% 7.32/1.51  --inst_lit_activity_flag                true
% 7.32/1.51  --inst_restr_to_given                   false
% 7.32/1.51  --inst_activity_threshold               500
% 7.32/1.51  --inst_out_proof                        true
% 7.32/1.51  
% 7.32/1.51  ------ Resolution Options
% 7.32/1.51  
% 7.32/1.51  --resolution_flag                       false
% 7.32/1.51  --res_lit_sel                           adaptive
% 7.32/1.51  --res_lit_sel_side                      none
% 7.32/1.51  --res_ordering                          kbo
% 7.32/1.51  --res_to_prop_solver                    active
% 7.32/1.51  --res_prop_simpl_new                    false
% 7.32/1.51  --res_prop_simpl_given                  true
% 7.32/1.51  --res_passive_queue_type                priority_queues
% 7.32/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.32/1.51  --res_passive_queues_freq               [15;5]
% 7.32/1.51  --res_forward_subs                      full
% 7.32/1.51  --res_backward_subs                     full
% 7.32/1.51  --res_forward_subs_resolution           true
% 7.32/1.51  --res_backward_subs_resolution          true
% 7.32/1.51  --res_orphan_elimination                true
% 7.32/1.51  --res_time_limit                        2.
% 7.32/1.51  --res_out_proof                         true
% 7.32/1.51  
% 7.32/1.51  ------ Superposition Options
% 7.32/1.51  
% 7.32/1.51  --superposition_flag                    true
% 7.32/1.51  --sup_passive_queue_type                priority_queues
% 7.32/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.32/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.32/1.51  --demod_completeness_check              fast
% 7.32/1.51  --demod_use_ground                      true
% 7.32/1.51  --sup_to_prop_solver                    passive
% 7.32/1.51  --sup_prop_simpl_new                    true
% 7.32/1.51  --sup_prop_simpl_given                  true
% 7.32/1.51  --sup_fun_splitting                     false
% 7.32/1.51  --sup_smt_interval                      50000
% 7.32/1.51  
% 7.32/1.51  ------ Superposition Simplification Setup
% 7.32/1.51  
% 7.32/1.51  --sup_indices_passive                   []
% 7.32/1.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.32/1.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.32/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.32/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.32/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.32/1.51  --sup_full_bw                           [BwDemod]
% 7.32/1.51  --sup_immed_triv                        [TrivRules]
% 7.32/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.32/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.32/1.51  --sup_immed_bw_main                     []
% 7.32/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.32/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.32/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.32/1.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.32/1.51  
% 7.32/1.51  ------ Combination Options
% 7.32/1.51  
% 7.32/1.51  --comb_res_mult                         3
% 7.32/1.51  --comb_sup_mult                         2
% 7.32/1.51  --comb_inst_mult                        10
% 7.32/1.51  
% 7.32/1.51  ------ Debug Options
% 7.32/1.51  
% 7.32/1.51  --dbg_backtrace                         false
% 7.32/1.51  --dbg_dump_prop_clauses                 false
% 7.32/1.51  --dbg_dump_prop_clauses_file            -
% 7.32/1.51  --dbg_out_stat                          false
% 7.32/1.51  
% 7.32/1.51  
% 7.32/1.51  
% 7.32/1.51  
% 7.32/1.51  ------ Proving...
% 7.32/1.51  
% 7.32/1.51  
% 7.32/1.51  % SZS status Theorem for theBenchmark.p
% 7.32/1.51  
% 7.32/1.51  % SZS output start CNFRefutation for theBenchmark.p
% 7.32/1.51  
% 7.32/1.51  fof(f1,axiom,(
% 7.32/1.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 7.32/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.32/1.51  
% 7.32/1.51  fof(f16,plain,(
% 7.32/1.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 7.32/1.51    inference(rectify,[],[f1])).
% 7.32/1.51  
% 7.32/1.51  fof(f17,plain,(
% 7.32/1.51    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 7.32/1.51    inference(ennf_transformation,[],[f16])).
% 7.32/1.51  
% 7.32/1.51  fof(f31,plain,(
% 7.32/1.51    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.32/1.51    introduced(choice_axiom,[])).
% 7.32/1.51  
% 7.32/1.51  fof(f32,plain,(
% 7.32/1.51    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 7.32/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f31])).
% 7.32/1.51  
% 7.32/1.51  fof(f42,plain,(
% 7.32/1.51    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 7.32/1.51    inference(cnf_transformation,[],[f32])).
% 7.32/1.51  
% 7.32/1.51  fof(f7,axiom,(
% 7.32/1.51    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 7.32/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.32/1.51  
% 7.32/1.51  fof(f49,plain,(
% 7.32/1.51    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 7.32/1.51    inference(cnf_transformation,[],[f7])).
% 7.32/1.51  
% 7.32/1.51  fof(f11,axiom,(
% 7.32/1.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.32/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.32/1.51  
% 7.32/1.51  fof(f36,plain,(
% 7.32/1.51    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.32/1.51    inference(nnf_transformation,[],[f11])).
% 7.32/1.51  
% 7.32/1.51  fof(f54,plain,(
% 7.32/1.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.32/1.51    inference(cnf_transformation,[],[f36])).
% 7.32/1.51  
% 7.32/1.51  fof(f14,conjecture,(
% 7.32/1.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 7.32/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.32/1.51  
% 7.32/1.51  fof(f15,negated_conjecture,(
% 7.32/1.51    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 7.32/1.51    inference(negated_conjecture,[],[f14])).
% 7.32/1.51  
% 7.32/1.51  fof(f29,plain,(
% 7.32/1.51    ? [X0,X1] : (? [X2] : ((~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 7.32/1.51    inference(ennf_transformation,[],[f15])).
% 7.32/1.51  
% 7.32/1.51  fof(f30,plain,(
% 7.32/1.51    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 7.32/1.51    inference(flattening,[],[f29])).
% 7.32/1.51  
% 7.32/1.51  fof(f38,plain,(
% 7.32/1.51    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (~r1_tarski(k8_setfam_1(X0,sK4),k8_setfam_1(X0,X1)) & r1_tarski(X1,sK4) & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(X0))))) )),
% 7.32/1.51    introduced(choice_axiom,[])).
% 7.32/1.51  
% 7.32/1.51  fof(f37,plain,(
% 7.32/1.51    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (? [X2] : (~r1_tarski(k8_setfam_1(sK2,X2),k8_setfam_1(sK2,sK3)) & r1_tarski(sK3,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK2)))) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))))),
% 7.32/1.51    introduced(choice_axiom,[])).
% 7.32/1.51  
% 7.32/1.51  fof(f39,plain,(
% 7.32/1.51    (~r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)) & r1_tarski(sK3,sK4) & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2)))) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2)))),
% 7.32/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f30,f38,f37])).
% 7.32/1.51  
% 7.32/1.51  fof(f60,plain,(
% 7.32/1.51    r1_tarski(sK3,sK4)),
% 7.32/1.51    inference(cnf_transformation,[],[f39])).
% 7.32/1.51  
% 7.32/1.51  fof(f13,axiom,(
% 7.32/1.51    ! [X0,X1] : (r1_tarski(X0,X1) => (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 7.32/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.32/1.51  
% 7.32/1.51  fof(f27,plain,(
% 7.32/1.51    ! [X0,X1] : ((r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0) | ~r1_tarski(X0,X1))),
% 7.32/1.51    inference(ennf_transformation,[],[f13])).
% 7.32/1.51  
% 7.32/1.51  fof(f28,plain,(
% 7.32/1.51    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1))),
% 7.32/1.51    inference(flattening,[],[f27])).
% 7.32/1.51  
% 7.32/1.51  fof(f57,plain,(
% 7.32/1.51    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1)) )),
% 7.32/1.51    inference(cnf_transformation,[],[f28])).
% 7.32/1.51  
% 7.32/1.51  fof(f6,axiom,(
% 7.32/1.51    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 7.32/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.32/1.51  
% 7.32/1.51  fof(f21,plain,(
% 7.32/1.51    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 7.32/1.51    inference(ennf_transformation,[],[f6])).
% 7.32/1.51  
% 7.32/1.51  fof(f48,plain,(
% 7.32/1.51    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 7.32/1.51    inference(cnf_transformation,[],[f21])).
% 7.32/1.51  
% 7.32/1.51  fof(f5,axiom,(
% 7.32/1.51    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 7.32/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.32/1.51  
% 7.32/1.51  fof(f35,plain,(
% 7.32/1.51    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 7.32/1.51    inference(nnf_transformation,[],[f5])).
% 7.32/1.51  
% 7.32/1.51  fof(f46,plain,(
% 7.32/1.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 7.32/1.51    inference(cnf_transformation,[],[f35])).
% 7.32/1.51  
% 7.32/1.51  fof(f59,plain,(
% 7.32/1.51    m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2)))),
% 7.32/1.51    inference(cnf_transformation,[],[f39])).
% 7.32/1.51  
% 7.32/1.51  fof(f61,plain,(
% 7.32/1.51    ~r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3))),
% 7.32/1.51    inference(cnf_transformation,[],[f39])).
% 7.32/1.51  
% 7.32/1.51  fof(f9,axiom,(
% 7.32/1.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 7.32/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.32/1.51  
% 7.32/1.51  fof(f23,plain,(
% 7.32/1.51    ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 7.32/1.51    inference(ennf_transformation,[],[f9])).
% 7.32/1.51  
% 7.32/1.51  fof(f52,plain,(
% 7.32/1.51    ( ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 7.32/1.51    inference(cnf_transformation,[],[f23])).
% 7.32/1.51  
% 7.32/1.51  fof(f8,axiom,(
% 7.32/1.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((k1_xboole_0 = X1 => k8_setfam_1(X0,X1) = X0) & (k1_xboole_0 != X1 => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1))))),
% 7.32/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.32/1.51  
% 7.32/1.51  fof(f22,plain,(
% 7.32/1.51    ! [X0,X1] : (((k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1) & (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 7.32/1.51    inference(ennf_transformation,[],[f8])).
% 7.32/1.51  
% 7.32/1.51  fof(f51,plain,(
% 7.32/1.51    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 7.32/1.51    inference(cnf_transformation,[],[f22])).
% 7.32/1.51  
% 7.32/1.51  fof(f62,plain,(
% 7.32/1.51    ( ! [X0] : (k8_setfam_1(X0,k1_xboole_0) = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 7.32/1.51    inference(equality_resolution,[],[f51])).
% 7.32/1.51  
% 7.32/1.51  fof(f50,plain,(
% 7.32/1.51    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 7.32/1.51    inference(cnf_transformation,[],[f22])).
% 7.32/1.51  
% 7.32/1.51  fof(f10,axiom,(
% 7.32/1.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k6_setfam_1(X0,X1) = k1_setfam_1(X1))),
% 7.32/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.32/1.51  
% 7.32/1.51  fof(f24,plain,(
% 7.32/1.51    ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 7.32/1.51    inference(ennf_transformation,[],[f10])).
% 7.32/1.51  
% 7.32/1.51  fof(f53,plain,(
% 7.32/1.51    ( ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 7.32/1.51    inference(cnf_transformation,[],[f24])).
% 7.32/1.51  
% 7.32/1.51  fof(f58,plain,(
% 7.32/1.51    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2)))),
% 7.32/1.51    inference(cnf_transformation,[],[f39])).
% 7.32/1.51  
% 7.32/1.51  fof(f3,axiom,(
% 7.32/1.51    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 7.32/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.32/1.51  
% 7.32/1.51  fof(f19,plain,(
% 7.32/1.51    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 7.32/1.51    inference(ennf_transformation,[],[f3])).
% 7.32/1.51  
% 7.32/1.51  fof(f20,plain,(
% 7.32/1.51    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 7.32/1.51    inference(flattening,[],[f19])).
% 7.32/1.51  
% 7.32/1.51  fof(f44,plain,(
% 7.32/1.51    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 7.32/1.51    inference(cnf_transformation,[],[f20])).
% 7.32/1.51  
% 7.32/1.51  fof(f4,axiom,(
% 7.32/1.51    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 7.32/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.32/1.51  
% 7.32/1.51  fof(f45,plain,(
% 7.32/1.51    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 7.32/1.51    inference(cnf_transformation,[],[f4])).
% 7.32/1.51  
% 7.32/1.51  fof(f2,axiom,(
% 7.32/1.51    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 7.32/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.32/1.51  
% 7.32/1.51  fof(f18,plain,(
% 7.32/1.51    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 7.32/1.51    inference(ennf_transformation,[],[f2])).
% 7.32/1.51  
% 7.32/1.51  fof(f33,plain,(
% 7.32/1.51    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 7.32/1.51    introduced(choice_axiom,[])).
% 7.32/1.51  
% 7.32/1.51  fof(f34,plain,(
% 7.32/1.51    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 7.32/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f18,f33])).
% 7.32/1.51  
% 7.32/1.51  fof(f43,plain,(
% 7.32/1.51    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 7.32/1.51    inference(cnf_transformation,[],[f34])).
% 7.32/1.51  
% 7.32/1.51  cnf(c_0,plain,
% 7.32/1.51      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 7.32/1.51      inference(cnf_transformation,[],[f42]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_15123,plain,
% 7.32/1.51      ( ~ r2_hidden(sK1(sK3),X0)
% 7.32/1.51      | ~ r2_hidden(sK1(sK3),sK3)
% 7.32/1.51      | ~ r1_xboole_0(X0,sK3) ),
% 7.32/1.51      inference(instantiation,[status(thm)],[c_0]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_41250,plain,
% 7.32/1.51      ( ~ r2_hidden(sK1(sK3),sK3) | ~ r1_xboole_0(sK3,sK3) ),
% 7.32/1.51      inference(instantiation,[status(thm)],[c_15123]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_9,plain,
% 7.32/1.51      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 7.32/1.51      inference(cnf_transformation,[],[f49]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_934,plain,
% 7.32/1.51      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 7.32/1.51      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_15,plain,
% 7.32/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.32/1.51      inference(cnf_transformation,[],[f54]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_928,plain,
% 7.32/1.51      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.32/1.51      | r1_tarski(X0,X1) = iProver_top ),
% 7.32/1.51      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_1385,plain,
% 7.32/1.51      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 7.32/1.51      inference(superposition,[status(thm)],[c_934,c_928]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_19,negated_conjecture,
% 7.32/1.51      ( r1_tarski(sK3,sK4) ),
% 7.32/1.51      inference(cnf_transformation,[],[f60]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_924,plain,
% 7.32/1.51      ( r1_tarski(sK3,sK4) = iProver_top ),
% 7.32/1.51      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_17,plain,
% 7.32/1.51      ( ~ r1_tarski(X0,X1)
% 7.32/1.51      | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
% 7.32/1.51      | k1_xboole_0 = X0 ),
% 7.32/1.51      inference(cnf_transformation,[],[f57]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_926,plain,
% 7.32/1.51      ( k1_xboole_0 = X0
% 7.32/1.51      | r1_tarski(X0,X1) != iProver_top
% 7.32/1.51      | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) = iProver_top ),
% 7.32/1.51      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_8,plain,
% 7.32/1.51      ( ~ r1_tarski(X0,X1) | r1_xboole_0(X0,k4_xboole_0(X2,X1)) ),
% 7.32/1.51      inference(cnf_transformation,[],[f48]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_935,plain,
% 7.32/1.51      ( r1_tarski(X0,X1) != iProver_top
% 7.32/1.51      | r1_xboole_0(X0,k4_xboole_0(X2,X1)) = iProver_top ),
% 7.32/1.51      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_7,plain,
% 7.32/1.51      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 7.32/1.51      inference(cnf_transformation,[],[f46]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_936,plain,
% 7.32/1.51      ( k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1) != iProver_top ),
% 7.32/1.51      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_1653,plain,
% 7.32/1.51      ( k4_xboole_0(X0,k4_xboole_0(X1,X2)) = X0
% 7.32/1.51      | r1_tarski(X0,X2) != iProver_top ),
% 7.32/1.51      inference(superposition,[status(thm)],[c_935,c_936]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_1659,plain,
% 7.32/1.51      ( k4_xboole_0(k1_setfam_1(X0),k4_xboole_0(X1,k1_setfam_1(X2))) = k1_setfam_1(X0)
% 7.32/1.51      | k1_xboole_0 = X2
% 7.32/1.51      | r1_tarski(X2,X0) != iProver_top ),
% 7.32/1.51      inference(superposition,[status(thm)],[c_926,c_1653]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_3536,plain,
% 7.32/1.51      ( k4_xboole_0(k1_setfam_1(sK4),k4_xboole_0(X0,k1_setfam_1(sK3))) = k1_setfam_1(sK4)
% 7.32/1.51      | sK3 = k1_xboole_0 ),
% 7.32/1.51      inference(superposition,[status(thm)],[c_924,c_1659]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_3780,plain,
% 7.32/1.51      ( sK3 = k1_xboole_0
% 7.32/1.51      | r1_tarski(X0,k4_xboole_0(X1,k1_setfam_1(sK3))) != iProver_top
% 7.32/1.51      | r1_xboole_0(X0,k1_setfam_1(sK4)) = iProver_top ),
% 7.32/1.51      inference(superposition,[status(thm)],[c_3536,c_935]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_5272,plain,
% 7.32/1.51      ( sK3 = k1_xboole_0
% 7.32/1.51      | r1_xboole_0(k1_xboole_0,k1_setfam_1(sK4)) = iProver_top ),
% 7.32/1.51      inference(superposition,[status(thm)],[c_1385,c_3780]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_20,negated_conjecture,
% 7.32/1.51      ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
% 7.32/1.51      inference(cnf_transformation,[],[f59]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_18,negated_conjecture,
% 7.32/1.51      ( ~ r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)) ),
% 7.32/1.51      inference(cnf_transformation,[],[f61]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_12,plain,
% 7.32/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 7.32/1.51      | m1_subset_1(k8_setfam_1(X1,X0),k1_zfmisc_1(X1)) ),
% 7.32/1.51      inference(cnf_transformation,[],[f52]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_1096,plain,
% 7.32/1.51      ( m1_subset_1(k8_setfam_1(sK2,sK4),k1_zfmisc_1(sK2))
% 7.32/1.51      | ~ m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
% 7.32/1.51      inference(instantiation,[status(thm)],[c_12]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_405,plain,( X0 = X0 ),theory(equality) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_1352,plain,
% 7.32/1.51      ( k8_setfam_1(sK2,sK4) = k8_setfam_1(sK2,sK4) ),
% 7.32/1.51      inference(instantiation,[status(thm)],[c_405]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_1531,plain,
% 7.32/1.51      ( ~ m1_subset_1(k8_setfam_1(sK2,sK4),k1_zfmisc_1(X0))
% 7.32/1.51      | r1_tarski(k8_setfam_1(sK2,sK4),X0) ),
% 7.32/1.51      inference(instantiation,[status(thm)],[c_15]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_1741,plain,
% 7.32/1.51      ( ~ m1_subset_1(k8_setfam_1(sK2,sK4),k1_zfmisc_1(sK2))
% 7.32/1.51      | r1_tarski(k8_setfam_1(sK2,sK4),sK2) ),
% 7.32/1.51      inference(instantiation,[status(thm)],[c_1531]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_1984,plain,
% 7.32/1.51      ( sK2 = sK2 ),
% 7.32/1.51      inference(instantiation,[status(thm)],[c_405]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_409,plain,
% 7.32/1.51      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.32/1.51      theory(equality) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_1539,plain,
% 7.32/1.51      ( ~ r1_tarski(X0,X1)
% 7.32/1.51      | r1_tarski(k8_setfam_1(sK2,sK4),X2)
% 7.32/1.51      | X2 != X1
% 7.32/1.51      | k8_setfam_1(sK2,sK4) != X0 ),
% 7.32/1.51      inference(instantiation,[status(thm)],[c_409]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_1756,plain,
% 7.32/1.51      ( ~ r1_tarski(k8_setfam_1(sK2,sK4),X0)
% 7.32/1.51      | r1_tarski(k8_setfam_1(sK2,sK4),X1)
% 7.32/1.51      | X1 != X0
% 7.32/1.51      | k8_setfam_1(sK2,sK4) != k8_setfam_1(sK2,sK4) ),
% 7.32/1.51      inference(instantiation,[status(thm)],[c_1539]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_2523,plain,
% 7.32/1.51      ( r1_tarski(k8_setfam_1(sK2,sK4),X0)
% 7.32/1.51      | ~ r1_tarski(k8_setfam_1(sK2,sK4),sK2)
% 7.32/1.51      | X0 != sK2
% 7.32/1.51      | k8_setfam_1(sK2,sK4) != k8_setfam_1(sK2,sK4) ),
% 7.32/1.51      inference(instantiation,[status(thm)],[c_1756]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_3076,plain,
% 7.32/1.51      ( r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,k1_xboole_0))
% 7.32/1.51      | ~ r1_tarski(k8_setfam_1(sK2,sK4),sK2)
% 7.32/1.51      | k8_setfam_1(sK2,sK4) != k8_setfam_1(sK2,sK4)
% 7.32/1.51      | k8_setfam_1(sK2,k1_xboole_0) != sK2 ),
% 7.32/1.51      inference(instantiation,[status(thm)],[c_2523]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_10,plain,
% 7.32/1.51      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
% 7.32/1.51      | k8_setfam_1(X0,k1_xboole_0) = X0 ),
% 7.32/1.51      inference(cnf_transformation,[],[f62]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_3077,plain,
% 7.32/1.51      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK2)))
% 7.32/1.51      | k8_setfam_1(sK2,k1_xboole_0) = sK2 ),
% 7.32/1.51      inference(instantiation,[status(thm)],[c_10]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_412,plain,
% 7.32/1.51      ( X0 != X1 | X2 != X3 | k8_setfam_1(X0,X2) = k8_setfam_1(X1,X3) ),
% 7.32/1.51      theory(equality) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_1172,plain,
% 7.32/1.51      ( k8_setfam_1(sK2,sK3) = k8_setfam_1(X0,X1)
% 7.32/1.51      | sK3 != X1
% 7.32/1.51      | sK2 != X0 ),
% 7.32/1.51      inference(instantiation,[status(thm)],[c_412]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_3498,plain,
% 7.32/1.51      ( k8_setfam_1(sK2,sK3) = k8_setfam_1(sK2,X0)
% 7.32/1.51      | sK3 != X0
% 7.32/1.51      | sK2 != sK2 ),
% 7.32/1.51      inference(instantiation,[status(thm)],[c_1172]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_3499,plain,
% 7.32/1.51      ( k8_setfam_1(sK2,sK3) = k8_setfam_1(sK2,k1_xboole_0)
% 7.32/1.51      | sK3 != k1_xboole_0
% 7.32/1.51      | sK2 != sK2 ),
% 7.32/1.51      inference(instantiation,[status(thm)],[c_3498]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_1086,plain,
% 7.32/1.51      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ),
% 7.32/1.51      inference(instantiation,[status(thm)],[c_9]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_5100,plain,
% 7.32/1.51      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
% 7.32/1.51      inference(instantiation,[status(thm)],[c_1086]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_1116,plain,
% 7.32/1.51      ( ~ r1_tarski(X0,X1)
% 7.32/1.51      | r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3))
% 7.32/1.51      | k8_setfam_1(sK2,sK3) != X1
% 7.32/1.51      | k8_setfam_1(sK2,sK4) != X0 ),
% 7.32/1.51      inference(instantiation,[status(thm)],[c_409]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_1171,plain,
% 7.32/1.51      ( ~ r1_tarski(X0,k8_setfam_1(X1,X2))
% 7.32/1.51      | r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3))
% 7.32/1.51      | k8_setfam_1(sK2,sK3) != k8_setfam_1(X1,X2)
% 7.32/1.51      | k8_setfam_1(sK2,sK4) != X0 ),
% 7.32/1.51      inference(instantiation,[status(thm)],[c_1116]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_1358,plain,
% 7.32/1.51      ( ~ r1_tarski(k8_setfam_1(X0,X1),k8_setfam_1(X2,X3))
% 7.32/1.51      | r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3))
% 7.32/1.51      | k8_setfam_1(sK2,sK3) != k8_setfam_1(X2,X3)
% 7.32/1.51      | k8_setfam_1(sK2,sK4) != k8_setfam_1(X0,X1) ),
% 7.32/1.51      inference(instantiation,[status(thm)],[c_1171]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_4929,plain,
% 7.32/1.51      ( ~ r1_tarski(k8_setfam_1(X0,X1),k8_setfam_1(sK2,X2))
% 7.32/1.51      | r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3))
% 7.32/1.51      | k8_setfam_1(sK2,sK3) != k8_setfam_1(sK2,X2)
% 7.32/1.51      | k8_setfam_1(sK2,sK4) != k8_setfam_1(X0,X1) ),
% 7.32/1.51      inference(instantiation,[status(thm)],[c_1358]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_7335,plain,
% 7.32/1.51      ( ~ r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,X0))
% 7.32/1.51      | r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3))
% 7.32/1.51      | k8_setfam_1(sK2,sK3) != k8_setfam_1(sK2,X0)
% 7.32/1.51      | k8_setfam_1(sK2,sK4) != k8_setfam_1(sK2,sK4) ),
% 7.32/1.51      inference(instantiation,[status(thm)],[c_4929]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_7337,plain,
% 7.32/1.51      ( r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3))
% 7.32/1.51      | ~ r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,k1_xboole_0))
% 7.32/1.51      | k8_setfam_1(sK2,sK3) != k8_setfam_1(sK2,k1_xboole_0)
% 7.32/1.51      | k8_setfam_1(sK2,sK4) != k8_setfam_1(sK2,sK4) ),
% 7.32/1.51      inference(instantiation,[status(thm)],[c_7335]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_9068,plain,
% 7.32/1.51      ( r1_xboole_0(k1_xboole_0,k1_setfam_1(sK4)) = iProver_top ),
% 7.32/1.51      inference(global_propositional_subsumption,
% 7.32/1.51                [status(thm)],
% 7.32/1.51                [c_5272,c_20,c_18,c_1096,c_1352,c_1741,c_1984,c_3076,
% 7.32/1.51                 c_3077,c_3499,c_5100,c_7337]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_9073,plain,
% 7.32/1.51      ( k4_xboole_0(k1_xboole_0,k1_setfam_1(sK4)) = k1_xboole_0 ),
% 7.32/1.51      inference(superposition,[status(thm)],[c_9068,c_936]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_923,plain,
% 7.32/1.51      ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))) = iProver_top ),
% 7.32/1.51      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_1386,plain,
% 7.32/1.51      ( r1_tarski(sK4,k1_zfmisc_1(sK2)) = iProver_top ),
% 7.32/1.51      inference(superposition,[status(thm)],[c_923,c_928]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_3538,plain,
% 7.32/1.51      ( k4_xboole_0(k1_setfam_1(k1_zfmisc_1(sK2)),k4_xboole_0(X0,k1_setfam_1(sK4))) = k1_setfam_1(k1_zfmisc_1(sK2))
% 7.32/1.51      | sK4 = k1_xboole_0 ),
% 7.32/1.51      inference(superposition,[status(thm)],[c_1386,c_1659]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_9397,plain,
% 7.32/1.51      ( k4_xboole_0(k1_setfam_1(k1_zfmisc_1(sK2)),k1_xboole_0) = k1_setfam_1(k1_zfmisc_1(sK2))
% 7.32/1.51      | sK4 = k1_xboole_0 ),
% 7.32/1.51      inference(superposition,[status(thm)],[c_9073,c_3538]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_24,plain,
% 7.32/1.51      ( r1_tarski(sK3,sK4) = iProver_top ),
% 7.32/1.51      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_11,plain,
% 7.32/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 7.32/1.51      | k6_setfam_1(X1,X0) = k8_setfam_1(X1,X0)
% 7.32/1.51      | k1_xboole_0 = X0 ),
% 7.32/1.51      inference(cnf_transformation,[],[f50]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_932,plain,
% 7.32/1.51      ( k6_setfam_1(X0,X1) = k8_setfam_1(X0,X1)
% 7.32/1.51      | k1_xboole_0 = X1
% 7.32/1.51      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 7.32/1.51      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_2722,plain,
% 7.32/1.51      ( k6_setfam_1(sK2,sK4) = k8_setfam_1(sK2,sK4) | sK4 = k1_xboole_0 ),
% 7.32/1.51      inference(superposition,[status(thm)],[c_923,c_932]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_13,plain,
% 7.32/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 7.32/1.51      | k6_setfam_1(X1,X0) = k1_setfam_1(X0) ),
% 7.32/1.51      inference(cnf_transformation,[],[f53]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_930,plain,
% 7.32/1.51      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
% 7.32/1.51      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 7.32/1.51      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_2028,plain,
% 7.32/1.51      ( k6_setfam_1(sK2,sK4) = k1_setfam_1(sK4) ),
% 7.32/1.51      inference(superposition,[status(thm)],[c_923,c_930]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_2731,plain,
% 7.32/1.51      ( k8_setfam_1(sK2,sK4) = k1_setfam_1(sK4) | sK4 = k1_xboole_0 ),
% 7.32/1.51      inference(light_normalisation,[status(thm)],[c_2722,c_2028]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_21,negated_conjecture,
% 7.32/1.51      ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
% 7.32/1.51      inference(cnf_transformation,[],[f58]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_922,plain,
% 7.32/1.51      ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) = iProver_top ),
% 7.32/1.51      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_2723,plain,
% 7.32/1.51      ( k6_setfam_1(sK2,sK3) = k8_setfam_1(sK2,sK3) | sK3 = k1_xboole_0 ),
% 7.32/1.51      inference(superposition,[status(thm)],[c_922,c_932]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_2029,plain,
% 7.32/1.51      ( k6_setfam_1(sK2,sK3) = k1_setfam_1(sK3) ),
% 7.32/1.51      inference(superposition,[status(thm)],[c_922,c_930]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_2726,plain,
% 7.32/1.51      ( k8_setfam_1(sK2,sK3) = k1_setfam_1(sK3) | sK3 = k1_xboole_0 ),
% 7.32/1.51      inference(light_normalisation,[status(thm)],[c_2723,c_2029]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_925,plain,
% 7.32/1.51      ( r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)) != iProver_top ),
% 7.32/1.51      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_3838,plain,
% 7.32/1.51      ( sK3 = k1_xboole_0
% 7.32/1.51      | r1_tarski(k8_setfam_1(sK2,sK4),k1_setfam_1(sK3)) != iProver_top ),
% 7.32/1.51      inference(superposition,[status(thm)],[c_2726,c_925]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_3935,plain,
% 7.32/1.51      ( sK3 = k1_xboole_0
% 7.32/1.51      | sK4 = k1_xboole_0
% 7.32/1.51      | r1_tarski(k1_setfam_1(sK4),k1_setfam_1(sK3)) != iProver_top ),
% 7.32/1.51      inference(superposition,[status(thm)],[c_2731,c_3838]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_5033,plain,
% 7.32/1.51      ( sK3 = k1_xboole_0
% 7.32/1.51      | sK4 = k1_xboole_0
% 7.32/1.51      | r1_tarski(sK3,sK4) != iProver_top ),
% 7.32/1.51      inference(superposition,[status(thm)],[c_926,c_3935]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_10825,plain,
% 7.32/1.51      ( sK4 = k1_xboole_0 ),
% 7.32/1.51      inference(global_propositional_subsumption,
% 7.32/1.51                [status(thm)],
% 7.32/1.51                [c_9397,c_20,c_24,c_18,c_1096,c_1352,c_1741,c_1984,
% 7.32/1.51                 c_3076,c_3077,c_3499,c_5033,c_5100,c_7337]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_10881,plain,
% 7.32/1.51      ( r1_tarski(sK3,k1_xboole_0) = iProver_top ),
% 7.32/1.51      inference(demodulation,[status(thm)],[c_10825,c_924]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_4,plain,
% 7.32/1.51      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 7.32/1.51      inference(cnf_transformation,[],[f44]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_939,plain,
% 7.32/1.51      ( r1_tarski(X0,X1) != iProver_top
% 7.32/1.51      | r1_tarski(X2,X0) != iProver_top
% 7.32/1.51      | r1_tarski(X2,X1) = iProver_top ),
% 7.32/1.51      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_2635,plain,
% 7.32/1.51      ( r1_tarski(X0,X1) = iProver_top
% 7.32/1.51      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 7.32/1.51      inference(superposition,[status(thm)],[c_1385,c_939]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_11090,plain,
% 7.32/1.51      ( r1_tarski(sK3,X0) = iProver_top ),
% 7.32/1.51      inference(superposition,[status(thm)],[c_10881,c_2635]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_1662,plain,
% 7.32/1.51      ( k4_xboole_0(sK4,k4_xboole_0(X0,k1_zfmisc_1(sK2))) = sK4 ),
% 7.32/1.51      inference(superposition,[status(thm)],[c_1386,c_1653]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_5,plain,
% 7.32/1.51      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 7.32/1.51      inference(cnf_transformation,[],[f45]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_938,plain,
% 7.32/1.51      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 7.32/1.51      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_1658,plain,
% 7.32/1.51      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X0)) = k4_xboole_0(X0,X1) ),
% 7.32/1.51      inference(superposition,[status(thm)],[c_938,c_1653]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_4638,plain,
% 7.32/1.51      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k1_zfmisc_1(sK2)),X1),sK4) = k4_xboole_0(k4_xboole_0(X0,k1_zfmisc_1(sK2)),X1) ),
% 7.32/1.51      inference(superposition,[status(thm)],[c_1662,c_1658]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_1660,plain,
% 7.32/1.51      ( k4_xboole_0(sK3,k4_xboole_0(X0,sK4)) = sK3 ),
% 7.32/1.51      inference(superposition,[status(thm)],[c_924,c_1653]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_1852,plain,
% 7.32/1.51      ( r1_tarski(X0,k4_xboole_0(X1,sK4)) != iProver_top
% 7.32/1.51      | r1_xboole_0(X0,sK3) = iProver_top ),
% 7.32/1.51      inference(superposition,[status(thm)],[c_1660,c_935]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_7131,plain,
% 7.32/1.51      ( r1_tarski(X0,k4_xboole_0(k4_xboole_0(X1,k1_zfmisc_1(sK2)),X2)) != iProver_top
% 7.32/1.51      | r1_xboole_0(X0,sK3) = iProver_top ),
% 7.32/1.51      inference(superposition,[status(thm)],[c_4638,c_1852]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_11208,plain,
% 7.32/1.51      ( r1_xboole_0(sK3,sK3) = iProver_top ),
% 7.32/1.51      inference(superposition,[status(thm)],[c_11090,c_7131]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_11225,plain,
% 7.32/1.51      ( r1_xboole_0(sK3,sK3) ),
% 7.32/1.51      inference(predicate_to_equality_rev,[status(thm)],[c_11208]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_3,plain,
% 7.32/1.51      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 7.32/1.51      inference(cnf_transformation,[],[f43]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_2814,plain,
% 7.32/1.51      ( r2_hidden(sK1(sK3),sK3) | k1_xboole_0 = sK3 ),
% 7.32/1.51      inference(instantiation,[status(thm)],[c_3]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_406,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_1326,plain,
% 7.32/1.51      ( X0 != X1 | sK3 != X1 | sK3 = X0 ),
% 7.32/1.51      inference(instantiation,[status(thm)],[c_406]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_1883,plain,
% 7.32/1.51      ( X0 != sK3 | sK3 = X0 | sK3 != sK3 ),
% 7.32/1.51      inference(instantiation,[status(thm)],[c_1326]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_1884,plain,
% 7.32/1.51      ( sK3 != sK3 | sK3 = k1_xboole_0 | k1_xboole_0 != sK3 ),
% 7.32/1.51      inference(instantiation,[status(thm)],[c_1883]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_1324,plain,
% 7.32/1.51      ( sK3 = sK3 ),
% 7.32/1.51      inference(instantiation,[status(thm)],[c_405]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(contradiction,plain,
% 7.32/1.51      ( $false ),
% 7.32/1.51      inference(minisat,
% 7.32/1.51                [status(thm)],
% 7.32/1.51                [c_41250,c_11225,c_7337,c_5100,c_3499,c_3077,c_3076,
% 7.32/1.51                 c_2814,c_1984,c_1884,c_1741,c_1352,c_1324,c_1096,c_18,
% 7.32/1.51                 c_20]) ).
% 7.32/1.51  
% 7.32/1.51  
% 7.32/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 7.32/1.51  
% 7.32/1.51  ------                               Statistics
% 7.32/1.51  
% 7.32/1.51  ------ General
% 7.32/1.51  
% 7.32/1.51  abstr_ref_over_cycles:                  0
% 7.32/1.51  abstr_ref_under_cycles:                 0
% 7.32/1.51  gc_basic_clause_elim:                   0
% 7.32/1.51  forced_gc_time:                         0
% 7.32/1.51  parsing_time:                           0.013
% 7.32/1.51  unif_index_cands_time:                  0.
% 7.32/1.51  unif_index_add_time:                    0.
% 7.32/1.51  orderings_time:                         0.
% 7.32/1.51  out_proof_time:                         0.011
% 7.32/1.51  total_time:                             0.975
% 7.32/1.51  num_of_symbols:                         46
% 7.32/1.51  num_of_terms:                           29475
% 7.32/1.51  
% 7.32/1.51  ------ Preprocessing
% 7.32/1.51  
% 7.32/1.51  num_of_splits:                          0
% 7.32/1.51  num_of_split_atoms:                     0
% 7.32/1.51  num_of_reused_defs:                     0
% 7.32/1.51  num_eq_ax_congr_red:                    20
% 7.32/1.51  num_of_sem_filtered_clauses:            1
% 7.32/1.51  num_of_subtypes:                        0
% 7.32/1.51  monotx_restored_types:                  0
% 7.32/1.51  sat_num_of_epr_types:                   0
% 7.32/1.51  sat_num_of_non_cyclic_types:            0
% 7.32/1.51  sat_guarded_non_collapsed_types:        0
% 7.32/1.51  num_pure_diseq_elim:                    0
% 7.32/1.51  simp_replaced_by:                       0
% 7.32/1.51  res_preprocessed:                       83
% 7.32/1.51  prep_upred:                             0
% 7.32/1.51  prep_unflattend:                        10
% 7.32/1.51  smt_new_axioms:                         0
% 7.32/1.51  pred_elim_cands:                        4
% 7.32/1.51  pred_elim:                              0
% 7.32/1.51  pred_elim_cl:                           0
% 7.32/1.51  pred_elim_cycles:                       1
% 7.32/1.51  merged_defs:                            12
% 7.32/1.51  merged_defs_ncl:                        0
% 7.32/1.51  bin_hyper_res:                          12
% 7.32/1.51  prep_cycles:                            3
% 7.32/1.51  pred_elim_time:                         0.002
% 7.32/1.51  splitting_time:                         0.
% 7.32/1.51  sem_filter_time:                        0.
% 7.32/1.51  monotx_time:                            0.001
% 7.32/1.51  subtype_inf_time:                       0.
% 7.32/1.51  
% 7.32/1.51  ------ Problem properties
% 7.32/1.51  
% 7.32/1.51  clauses:                                22
% 7.32/1.51  conjectures:                            4
% 7.32/1.51  epr:                                    3
% 7.32/1.51  horn:                                   17
% 7.32/1.51  ground:                                 4
% 7.32/1.51  unary:                                  6
% 7.32/1.51  binary:                                 11
% 7.32/1.51  lits:                                   43
% 7.32/1.51  lits_eq:                                8
% 7.32/1.51  fd_pure:                                0
% 7.32/1.51  fd_pseudo:                              0
% 7.32/1.51  fd_cond:                                3
% 7.32/1.51  fd_pseudo_cond:                         0
% 7.32/1.51  ac_symbols:                             0
% 7.32/1.51  
% 7.32/1.51  ------ Propositional Solver
% 7.32/1.51  
% 7.32/1.51  prop_solver_calls:                      29
% 7.32/1.51  prop_fast_solver_calls:                 1310
% 7.32/1.51  smt_solver_calls:                       0
% 7.32/1.51  smt_fast_solver_calls:                  0
% 7.32/1.51  prop_num_of_clauses:                    14835
% 7.32/1.51  prop_preprocess_simplified:             21076
% 7.32/1.51  prop_fo_subsumed:                       83
% 7.32/1.51  prop_solver_time:                       0.
% 7.32/1.51  smt_solver_time:                        0.
% 7.32/1.51  smt_fast_solver_time:                   0.
% 7.32/1.51  prop_fast_solver_time:                  0.
% 7.32/1.51  prop_unsat_core_time:                   0.001
% 7.32/1.51  
% 7.32/1.51  ------ QBF
% 7.32/1.51  
% 7.32/1.51  qbf_q_res:                              0
% 7.32/1.51  qbf_num_tautologies:                    0
% 7.32/1.51  qbf_prep_cycles:                        0
% 7.32/1.51  
% 7.32/1.51  ------ BMC1
% 7.32/1.51  
% 7.32/1.51  bmc1_current_bound:                     -1
% 7.32/1.51  bmc1_last_solved_bound:                 -1
% 7.32/1.51  bmc1_unsat_core_size:                   -1
% 7.32/1.51  bmc1_unsat_core_parents_size:           -1
% 7.32/1.51  bmc1_merge_next_fun:                    0
% 7.32/1.51  bmc1_unsat_core_clauses_time:           0.
% 7.32/1.51  
% 7.32/1.51  ------ Instantiation
% 7.32/1.51  
% 7.32/1.51  inst_num_of_clauses:                    3813
% 7.32/1.51  inst_num_in_passive:                    542
% 7.32/1.51  inst_num_in_active:                     1625
% 7.32/1.51  inst_num_in_unprocessed:                1645
% 7.32/1.51  inst_num_of_loops:                      1895
% 7.32/1.51  inst_num_of_learning_restarts:          0
% 7.32/1.51  inst_num_moves_active_passive:          263
% 7.32/1.51  inst_lit_activity:                      0
% 7.32/1.51  inst_lit_activity_moves:                0
% 7.32/1.51  inst_num_tautologies:                   0
% 7.32/1.51  inst_num_prop_implied:                  0
% 7.32/1.51  inst_num_existing_simplified:           0
% 7.32/1.51  inst_num_eq_res_simplified:             0
% 7.32/1.51  inst_num_child_elim:                    0
% 7.32/1.51  inst_num_of_dismatching_blockings:      2591
% 7.32/1.51  inst_num_of_non_proper_insts:           4570
% 7.32/1.51  inst_num_of_duplicates:                 0
% 7.32/1.51  inst_inst_num_from_inst_to_res:         0
% 7.32/1.51  inst_dismatching_checking_time:         0.
% 7.32/1.51  
% 7.32/1.51  ------ Resolution
% 7.32/1.51  
% 7.32/1.51  res_num_of_clauses:                     0
% 7.32/1.51  res_num_in_passive:                     0
% 7.32/1.51  res_num_in_active:                      0
% 7.32/1.51  res_num_of_loops:                       86
% 7.32/1.51  res_forward_subset_subsumed:            337
% 7.32/1.51  res_backward_subset_subsumed:           2
% 7.32/1.51  res_forward_subsumed:                   0
% 7.32/1.51  res_backward_subsumed:                  0
% 7.32/1.51  res_forward_subsumption_resolution:     0
% 7.32/1.51  res_backward_subsumption_resolution:    0
% 7.32/1.51  res_clause_to_clause_subsumption:       5196
% 7.32/1.51  res_orphan_elimination:                 0
% 7.32/1.51  res_tautology_del:                      408
% 7.32/1.51  res_num_eq_res_simplified:              0
% 7.32/1.51  res_num_sel_changes:                    0
% 7.32/1.51  res_moves_from_active_to_pass:          0
% 7.32/1.51  
% 7.32/1.51  ------ Superposition
% 7.32/1.51  
% 7.32/1.51  sup_time_total:                         0.
% 7.32/1.51  sup_time_generating:                    0.
% 7.32/1.51  sup_time_sim_full:                      0.
% 7.32/1.51  sup_time_sim_immed:                     0.
% 7.32/1.51  
% 7.32/1.51  sup_num_of_clauses:                     1278
% 7.32/1.51  sup_num_in_active:                      289
% 7.32/1.51  sup_num_in_passive:                     989
% 7.32/1.51  sup_num_of_loops:                       378
% 7.32/1.51  sup_fw_superposition:                   2239
% 7.32/1.51  sup_bw_superposition:                   2316
% 7.32/1.51  sup_immediate_simplified:               1040
% 7.32/1.51  sup_given_eliminated:                   1
% 7.32/1.51  comparisons_done:                       0
% 7.32/1.51  comparisons_avoided:                    60
% 7.32/1.51  
% 7.32/1.51  ------ Simplifications
% 7.32/1.51  
% 7.32/1.51  
% 7.32/1.51  sim_fw_subset_subsumed:                 63
% 7.32/1.51  sim_bw_subset_subsumed:                 20
% 7.32/1.51  sim_fw_subsumed:                        552
% 7.32/1.51  sim_bw_subsumed:                        57
% 7.32/1.51  sim_fw_subsumption_res:                 1
% 7.32/1.51  sim_bw_subsumption_res:                 0
% 7.32/1.51  sim_tautology_del:                      71
% 7.32/1.51  sim_eq_tautology_del:                   105
% 7.32/1.51  sim_eq_res_simp:                        0
% 7.32/1.51  sim_fw_demodulated:                     194
% 7.32/1.51  sim_bw_demodulated:                     87
% 7.32/1.51  sim_light_normalised:                   302
% 7.32/1.51  sim_joinable_taut:                      0
% 7.32/1.51  sim_joinable_simp:                      0
% 7.32/1.51  sim_ac_normalised:                      0
% 7.32/1.51  sim_smt_subsumption:                    0
% 7.32/1.51  
%------------------------------------------------------------------------------
