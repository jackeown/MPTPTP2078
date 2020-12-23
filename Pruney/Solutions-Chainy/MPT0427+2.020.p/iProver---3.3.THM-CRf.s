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
% DateTime   : Thu Dec  3 11:42:30 EST 2020

% Result     : Theorem 14.62s
% Output     : CNFRefutation 14.62s
% Verified   : 
% Statistics : Number of formulae       :  178 ( 474 expanded)
%              Number of clauses        :  120 ( 206 expanded)
%              Number of leaves         :   22 ( 115 expanded)
%              Depth                    :   20
%              Number of atoms          :  464 (1459 expanded)
%              Number of equality atoms :  200 ( 354 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( r1_tarski(X1,X2)
           => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( r1_tarski(X1,X2)
             => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f28,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f29,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f28])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
     => ( ~ r1_tarski(k8_setfam_1(X0,sK4),k8_setfam_1(X0,X1))
        & r1_tarski(X1,sK4)
        & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
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

fof(f42,plain,
    ( ~ r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3))
    & r1_tarski(sK3,sK4)
    & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2)))
    & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f29,f41,f40])).

fof(f69,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(cnf_transformation,[],[f42])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ( k1_xboole_0 = X1
         => k8_setfam_1(X0,X1) = X0 )
        & ( k1_xboole_0 != X1
         => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ( k8_setfam_1(X0,X1) = X0
          | k1_xboole_0 != X1 )
        & ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
          | k1_xboole_0 = X1 ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X1,X2) )
     => ( r1_tarski(X1,k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(flattening,[],[f24])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) )
     => ( ~ r1_tarski(X1,sK1(X0,X1))
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ( ~ r1_tarski(X1,sK1(X0,X1))
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f25,f38])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f71,plain,(
    ~ r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f42])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f76,plain,(
    ! [X0] :
      ( k8_setfam_1(X0,k1_xboole_0) = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f59])).

fof(f68,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(cnf_transformation,[],[f42])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r2_hidden(X0,X1) )
     => r1_tarski(k1_setfam_1(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k1_setfam_1(X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k1_setfam_1(X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f30])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f73,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f43])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X1,sK1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f70,plain,(
    r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f42])).

fof(f45,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1272,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k6_setfam_1(X1,X0) = k8_setfam_1(X1,X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1283,plain,
    ( k6_setfam_1(X0,X1) = k8_setfam_1(X0,X1)
    | k1_xboole_0 = X1
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_5220,plain,
    ( k6_setfam_1(sK2,sK4) = k8_setfam_1(sK2,sK4)
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1272,c_1283])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k6_setfam_1(X1,X0) = k1_setfam_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1281,plain,
    ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2281,plain,
    ( k6_setfam_1(sK2,sK4) = k1_setfam_1(sK4) ),
    inference(superposition,[status(thm)],[c_1272,c_1281])).

cnf(c_5229,plain,
    ( k8_setfam_1(sK2,sK4) = k1_setfam_1(sK4)
    | sK4 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_5220,c_2281])).

cnf(c_23,plain,
    ( r2_hidden(sK1(X0,X1),X0)
    | r1_tarski(X1,k1_setfam_1(X0))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1276,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0,X1),X0) = iProver_top
    | r1_tarski(X1,k1_setfam_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | m1_subset_1(k8_setfam_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1282,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | m1_subset_1(k8_setfam_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_21,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1278,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_4151,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | r2_hidden(X0,k8_setfam_1(X1,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1282,c_1278])).

cnf(c_32055,plain,
    ( m1_subset_1(X0,sK2) = iProver_top
    | r2_hidden(X0,k8_setfam_1(sK2,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1272,c_4151])).

cnf(c_32407,plain,
    ( k8_setfam_1(sK2,sK4) = k1_xboole_0
    | m1_subset_1(sK1(k8_setfam_1(sK2,sK4),X0),sK2) = iProver_top
    | r1_tarski(X0,k1_setfam_1(k8_setfam_1(sK2,sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1276,c_32055])).

cnf(c_19,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2574,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(resolution,[status(thm)],[c_21,c_19])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2552,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | r1_tarski(k8_setfam_1(X1,X0),X1) ),
    inference(resolution,[status(thm)],[c_17,c_20])).

cnf(c_7510,plain,
    ( r1_tarski(k8_setfam_1(sK2,sK4),sK2) ),
    inference(resolution,[status(thm)],[c_2552,c_27])).

cnf(c_8301,plain,
    ( m1_subset_1(X0,sK2)
    | ~ r2_hidden(X0,k8_setfam_1(sK2,sK4)) ),
    inference(resolution,[status(thm)],[c_2574,c_7510])).

cnf(c_8857,plain,
    ( m1_subset_1(sK1(k8_setfam_1(sK2,sK4),X0),sK2)
    | r1_tarski(X0,k1_setfam_1(k8_setfam_1(sK2,sK4)))
    | k1_xboole_0 = k8_setfam_1(sK2,sK4) ),
    inference(resolution,[status(thm)],[c_8301,c_23])).

cnf(c_25,negated_conjecture,
    ( ~ r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1510,plain,
    ( ~ m1_subset_1(k8_setfam_1(sK2,sK4),k1_zfmisc_1(k8_setfam_1(sK2,sK3)))
    | r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_619,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1658,plain,
    ( k8_setfam_1(sK2,sK4) = k8_setfam_1(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_619])).

cnf(c_620,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1663,plain,
    ( X0 != X1
    | k8_setfam_1(sK2,sK4) != X1
    | k8_setfam_1(sK2,sK4) = X0 ),
    inference(instantiation,[status(thm)],[c_620])).

cnf(c_1903,plain,
    ( X0 != k8_setfam_1(sK2,sK4)
    | k8_setfam_1(sK2,sK4) = X0
    | k8_setfam_1(sK2,sK4) != k8_setfam_1(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_1663])).

cnf(c_1904,plain,
    ( k8_setfam_1(sK2,sK4) != k8_setfam_1(sK2,sK4)
    | k8_setfam_1(sK2,sK4) = k1_xboole_0
    | k1_xboole_0 != k8_setfam_1(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_1903])).

cnf(c_2200,plain,
    ( k8_setfam_1(sK2,sK3) = k8_setfam_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_619])).

cnf(c_622,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_2366,plain,
    ( k8_setfam_1(sK2,sK3) != X0
    | k1_zfmisc_1(k8_setfam_1(sK2,sK3)) = k1_zfmisc_1(X0) ),
    inference(instantiation,[status(thm)],[c_622])).

cnf(c_4457,plain,
    ( k8_setfam_1(sK2,sK3) != k8_setfam_1(sK2,sK3)
    | k1_zfmisc_1(k8_setfam_1(sK2,sK3)) = k1_zfmisc_1(k8_setfam_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_2366])).

cnf(c_624,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1608,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | X0 != X2
    | X1 != k1_zfmisc_1(X3) ),
    inference(instantiation,[status(thm)],[c_624])).

cnf(c_1739,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(X2,k1_zfmisc_1(X3))
    | X2 != X0
    | k1_zfmisc_1(X3) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_1608])).

cnf(c_2108,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k8_setfam_1(sK2,sK4),k1_zfmisc_1(k8_setfam_1(sK2,sK3)))
    | k8_setfam_1(sK2,sK4) != X0
    | k1_zfmisc_1(k8_setfam_1(sK2,sK3)) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_1739])).

cnf(c_7809,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k8_setfam_1(sK2,sK3)))
    | m1_subset_1(k8_setfam_1(sK2,sK4),k1_zfmisc_1(k8_setfam_1(sK2,sK3)))
    | k8_setfam_1(sK2,sK4) != X0
    | k1_zfmisc_1(k8_setfam_1(sK2,sK3)) != k1_zfmisc_1(k8_setfam_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_2108])).

cnf(c_7812,plain,
    ( m1_subset_1(k8_setfam_1(sK2,sK4),k1_zfmisc_1(k8_setfam_1(sK2,sK3)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k8_setfam_1(sK2,sK3)))
    | k8_setfam_1(sK2,sK4) != k1_xboole_0
    | k1_zfmisc_1(k8_setfam_1(sK2,sK3)) != k1_zfmisc_1(k8_setfam_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_7809])).

cnf(c_14,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_7965,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k8_setfam_1(sK2,sK3))) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_10772,plain,
    ( r1_tarski(X0,k1_setfam_1(k8_setfam_1(sK2,sK4)))
    | m1_subset_1(sK1(k8_setfam_1(sK2,sK4),X0),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8857,c_25,c_1510,c_1658,c_1904,c_2200,c_4457,c_7812,c_7965])).

cnf(c_10773,plain,
    ( m1_subset_1(sK1(k8_setfam_1(sK2,sK4),X0),sK2)
    | r1_tarski(X0,k1_setfam_1(k8_setfam_1(sK2,sK4))) ),
    inference(renaming,[status(thm)],[c_10772])).

cnf(c_10774,plain,
    ( m1_subset_1(sK1(k8_setfam_1(sK2,sK4),X0),sK2) = iProver_top
    | r1_tarski(X0,k1_setfam_1(k8_setfam_1(sK2,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10773])).

cnf(c_33310,plain,
    ( m1_subset_1(sK1(k8_setfam_1(sK2,sK4),X0),sK2) = iProver_top
    | r1_tarski(X0,k1_setfam_1(k8_setfam_1(sK2,sK4))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_32407,c_10774])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1287,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_33318,plain,
    ( r2_hidden(sK1(k8_setfam_1(sK2,sK4),X0),sK2) = iProver_top
    | r1_tarski(X0,k1_setfam_1(k8_setfam_1(sK2,sK4))) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_33310,c_1287])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_228,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_19])).

cnf(c_229,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_228])).

cnf(c_279,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_13,c_229])).

cnf(c_7522,plain,
    ( ~ r2_hidden(X0,k8_setfam_1(sK2,sK4))
    | r2_hidden(X0,sK2) ),
    inference(resolution,[status(thm)],[c_7510,c_279])).

cnf(c_7717,plain,
    ( r2_hidden(sK1(k8_setfam_1(sK2,sK4),X0),sK2)
    | r1_tarski(X0,k1_setfam_1(k8_setfam_1(sK2,sK4)))
    | k1_xboole_0 = k8_setfam_1(sK2,sK4) ),
    inference(resolution,[status(thm)],[c_7522,c_23])).

cnf(c_7718,plain,
    ( k1_xboole_0 = k8_setfam_1(sK2,sK4)
    | r2_hidden(sK1(k8_setfam_1(sK2,sK4),X0),sK2) = iProver_top
    | r1_tarski(X0,k1_setfam_1(k8_setfam_1(sK2,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7717])).

cnf(c_39742,plain,
    ( r1_tarski(X0,k1_setfam_1(k8_setfam_1(sK2,sK4))) = iProver_top
    | r2_hidden(sK1(k8_setfam_1(sK2,sK4),X0),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_33318,c_25,c_1510,c_1658,c_1904,c_2200,c_4457,c_7718,c_7812,c_7965])).

cnf(c_39743,plain,
    ( r2_hidden(sK1(k8_setfam_1(sK2,sK4),X0),sK2) = iProver_top
    | r1_tarski(X0,k1_setfam_1(k8_setfam_1(sK2,sK4))) = iProver_top ),
    inference(renaming,[status(thm)],[c_39742])).

cnf(c_39748,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(sK1(k1_setfam_1(sK4),X0),sK2) = iProver_top
    | r1_tarski(X0,k1_setfam_1(k8_setfam_1(sK2,sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5229,c_39743])).

cnf(c_1537,plain,
    ( m1_subset_1(k8_setfam_1(sK2,sK4),k1_zfmisc_1(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1911,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_619])).

cnf(c_1824,plain,
    ( ~ m1_subset_1(k8_setfam_1(sK2,sK4),k1_zfmisc_1(X0))
    | r1_tarski(k8_setfam_1(sK2,sK4),X0) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_2234,plain,
    ( ~ m1_subset_1(k8_setfam_1(sK2,sK4),k1_zfmisc_1(sK2))
    | r1_tarski(k8_setfam_1(sK2,sK4),sK2) ),
    inference(instantiation,[status(thm)],[c_1824])).

cnf(c_621,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1603,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3))
    | k8_setfam_1(sK2,sK3) != X1
    | k8_setfam_1(sK2,sK4) != X0 ),
    inference(instantiation,[status(thm)],[c_621])).

cnf(c_1657,plain,
    ( ~ r1_tarski(k8_setfam_1(sK2,sK4),X0)
    | r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3))
    | k8_setfam_1(sK2,sK3) != X0
    | k8_setfam_1(sK2,sK4) != k8_setfam_1(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_1603])).

cnf(c_2349,plain,
    ( r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3))
    | ~ r1_tarski(k8_setfam_1(sK2,sK4),sK2)
    | k8_setfam_1(sK2,sK3) != sK2
    | k8_setfam_1(sK2,sK4) != k8_setfam_1(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_1657])).

cnf(c_2446,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_619])).

cnf(c_1913,plain,
    ( X0 != X1
    | sK2 != X1
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_620])).

cnf(c_2396,plain,
    ( X0 != sK2
    | sK2 = X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1913])).

cnf(c_4524,plain,
    ( k8_setfam_1(sK2,k1_xboole_0) != sK2
    | sK2 = k8_setfam_1(sK2,k1_xboole_0)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_2396])).

cnf(c_15,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
    | k8_setfam_1(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_4525,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK2)))
    | k8_setfam_1(sK2,k1_xboole_0) = sK2 ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_2448,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_620])).

cnf(c_4821,plain,
    ( X0 != sK3
    | sK3 = X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2448])).

cnf(c_4822,plain,
    ( sK3 != sK3
    | sK3 = k1_xboole_0
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_4821])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1271,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_5221,plain,
    ( k6_setfam_1(sK2,sK3) = k8_setfam_1(sK2,sK3)
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1271,c_1283])).

cnf(c_2282,plain,
    ( k6_setfam_1(sK2,sK3) = k1_setfam_1(sK3) ),
    inference(superposition,[status(thm)],[c_1271,c_1281])).

cnf(c_5224,plain,
    ( k8_setfam_1(sK2,sK3) = k1_setfam_1(sK3)
    | sK3 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_5221,c_2282])).

cnf(c_1274,plain,
    ( r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_6527,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(k8_setfam_1(sK2,sK4),k1_setfam_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5224,c_1274])).

cnf(c_7682,plain,
    ( sK3 = k1_xboole_0
    | sK4 = k1_xboole_0
    | r1_tarski(k1_setfam_1(sK4),k1_setfam_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5229,c_6527])).

cnf(c_7701,plain,
    ( ~ r1_tarski(k1_setfam_1(sK4),k1_setfam_1(sK3))
    | sK3 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7682])).

cnf(c_1530,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_10807,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(instantiation,[status(thm)],[c_1530])).

cnf(c_626,plain,
    ( X0 != X1
    | X2 != X3
    | k8_setfam_1(X0,X2) = k8_setfam_1(X1,X3) ),
    theory(equality)).

cnf(c_2207,plain,
    ( k8_setfam_1(sK2,sK3) = k8_setfam_1(X0,X1)
    | sK3 != X1
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_626])).

cnf(c_18032,plain,
    ( k8_setfam_1(sK2,sK3) = k8_setfam_1(sK2,X0)
    | sK3 != X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_2207])).

cnf(c_18033,plain,
    ( k8_setfam_1(sK2,sK3) = k8_setfam_1(sK2,k1_xboole_0)
    | sK3 != k1_xboole_0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_18032])).

cnf(c_4536,plain,
    ( X0 != X1
    | X0 = sK2
    | sK2 != X1 ),
    inference(instantiation,[status(thm)],[c_620])).

cnf(c_13167,plain,
    ( k8_setfam_1(sK2,sK3) != X0
    | k8_setfam_1(sK2,sK3) = sK2
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_4536])).

cnf(c_44791,plain,
    ( k8_setfam_1(sK2,sK3) != k8_setfam_1(sK2,k1_xboole_0)
    | k8_setfam_1(sK2,sK3) = sK2
    | sK2 != k8_setfam_1(sK2,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_13167])).

cnf(c_24,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_setfam_1(X1),X2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2720,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k1_setfam_1(X1),X0) ),
    inference(resolution,[status(thm)],[c_24,c_2])).

cnf(c_22,plain,
    ( ~ r1_tarski(X0,sK1(X1,X0))
    | r1_tarski(X0,k1_setfam_1(X1))
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_6766,plain,
    ( ~ r2_hidden(sK1(X0,k1_setfam_1(X1)),X1)
    | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
    | k1_xboole_0 = X0 ),
    inference(resolution,[status(thm)],[c_2720,c_22])).

cnf(c_26,negated_conjecture,
    ( r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2309,plain,
    ( ~ r2_hidden(X0,sK3)
    | r2_hidden(X0,sK4) ),
    inference(resolution,[status(thm)],[c_279,c_26])).

cnf(c_2904,plain,
    ( r2_hidden(sK1(sK3,X0),sK4)
    | r1_tarski(X0,k1_setfam_1(sK3))
    | k1_xboole_0 = sK3 ),
    inference(resolution,[status(thm)],[c_2309,c_23])).

cnf(c_53553,plain,
    ( r1_tarski(k1_setfam_1(sK4),k1_setfam_1(sK3))
    | k1_xboole_0 = sK3 ),
    inference(resolution,[status(thm)],[c_6766,c_2904])).

cnf(c_54195,plain,
    ( sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_39748,c_27,c_25,c_1537,c_1658,c_1911,c_2234,c_2349,c_2446,c_4524,c_4525,c_4822,c_7701,c_10807,c_18033,c_44791,c_53553])).

cnf(c_1273,plain,
    ( r1_tarski(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1297,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3944,plain,
    ( sK3 = sK4
    | r1_tarski(sK4,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1273,c_1297])).

cnf(c_1834,plain,
    ( r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3))
    | ~ r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK4))
    | k8_setfam_1(sK2,sK3) != k8_setfam_1(sK2,sK4)
    | k8_setfam_1(sK2,sK4) != k8_setfam_1(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_1657])).

cnf(c_1835,plain,
    ( r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK4)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2191,plain,
    ( k8_setfam_1(sK2,sK3) = k8_setfam_1(sK2,sK4)
    | sK3 != sK4
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_626])).

cnf(c_4348,plain,
    ( r1_tarski(sK4,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3944,c_25,c_1658,c_1834,c_1835,c_1911,c_2191])).

cnf(c_54315,plain,
    ( r1_tarski(k1_xboole_0,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_54195,c_4348])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_41403,plain,
    ( r1_tarski(k1_xboole_0,sK3) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_41406,plain,
    ( r1_tarski(k1_xboole_0,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41403])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_54315,c_41406])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:14:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 14.62/2.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.62/2.49  
% 14.62/2.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 14.62/2.49  
% 14.62/2.49  ------  iProver source info
% 14.62/2.49  
% 14.62/2.49  git: date: 2020-06-30 10:37:57 +0100
% 14.62/2.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 14.62/2.49  git: non_committed_changes: false
% 14.62/2.49  git: last_make_outside_of_git: false
% 14.62/2.49  
% 14.62/2.49  ------ 
% 14.62/2.49  ------ Parsing...
% 14.62/2.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 14.62/2.49  
% 14.62/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 14.62/2.49  
% 14.62/2.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 14.62/2.49  
% 14.62/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 14.62/2.49  ------ Proving...
% 14.62/2.49  ------ Problem Properties 
% 14.62/2.49  
% 14.62/2.49  
% 14.62/2.49  clauses                                 28
% 14.62/2.49  conjectures                             4
% 14.62/2.49  EPR                                     9
% 14.62/2.49  Horn                                    22
% 14.62/2.49  unary                                   8
% 14.62/2.49  binary                                  7
% 14.62/2.49  lits                                    61
% 14.62/2.49  lits eq                                 9
% 14.62/2.49  fd_pure                                 0
% 14.62/2.49  fd_pseudo                               0
% 14.62/2.49  fd_cond                                 3
% 14.62/2.49  fd_pseudo_cond                          3
% 14.62/2.49  AC symbols                              0
% 14.62/2.49  
% 14.62/2.49  ------ Input Options Time Limit: Unbounded
% 14.62/2.49  
% 14.62/2.49  
% 14.62/2.49  ------ 
% 14.62/2.49  Current options:
% 14.62/2.49  ------ 
% 14.62/2.49  
% 14.62/2.49  
% 14.62/2.49  
% 14.62/2.49  
% 14.62/2.49  ------ Proving...
% 14.62/2.49  
% 14.62/2.49  
% 14.62/2.49  % SZS status Theorem for theBenchmark.p
% 14.62/2.49  
% 14.62/2.49  % SZS output start CNFRefutation for theBenchmark.p
% 14.62/2.49  
% 14.62/2.49  fof(f15,conjecture,(
% 14.62/2.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 14.62/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 14.62/2.49  
% 14.62/2.49  fof(f16,negated_conjecture,(
% 14.62/2.49    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 14.62/2.49    inference(negated_conjecture,[],[f15])).
% 14.62/2.49  
% 14.62/2.49  fof(f28,plain,(
% 14.62/2.49    ? [X0,X1] : (? [X2] : ((~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 14.62/2.49    inference(ennf_transformation,[],[f16])).
% 14.62/2.49  
% 14.62/2.49  fof(f29,plain,(
% 14.62/2.49    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 14.62/2.49    inference(flattening,[],[f28])).
% 14.62/2.49  
% 14.62/2.49  fof(f41,plain,(
% 14.62/2.49    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (~r1_tarski(k8_setfam_1(X0,sK4),k8_setfam_1(X0,X1)) & r1_tarski(X1,sK4) & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(X0))))) )),
% 14.62/2.49    introduced(choice_axiom,[])).
% 14.62/2.49  
% 14.62/2.49  fof(f40,plain,(
% 14.62/2.49    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (? [X2] : (~r1_tarski(k8_setfam_1(sK2,X2),k8_setfam_1(sK2,sK3)) & r1_tarski(sK3,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK2)))) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))))),
% 14.62/2.49    introduced(choice_axiom,[])).
% 14.62/2.49  
% 14.62/2.49  fof(f42,plain,(
% 14.62/2.49    (~r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)) & r1_tarski(sK3,sK4) & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2)))) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2)))),
% 14.62/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f29,f41,f40])).
% 14.62/2.49  
% 14.62/2.49  fof(f69,plain,(
% 14.62/2.49    m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2)))),
% 14.62/2.49    inference(cnf_transformation,[],[f42])).
% 14.62/2.49  
% 14.62/2.49  fof(f8,axiom,(
% 14.62/2.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((k1_xboole_0 = X1 => k8_setfam_1(X0,X1) = X0) & (k1_xboole_0 != X1 => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1))))),
% 14.62/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 14.62/2.49  
% 14.62/2.49  fof(f19,plain,(
% 14.62/2.49    ! [X0,X1] : (((k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1) & (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 14.62/2.49    inference(ennf_transformation,[],[f8])).
% 14.62/2.49  
% 14.62/2.49  fof(f58,plain,(
% 14.62/2.49    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 14.62/2.49    inference(cnf_transformation,[],[f19])).
% 14.62/2.49  
% 14.62/2.49  fof(f10,axiom,(
% 14.62/2.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k6_setfam_1(X0,X1) = k1_setfam_1(X1))),
% 14.62/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 14.62/2.49  
% 14.62/2.49  fof(f21,plain,(
% 14.62/2.49    ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 14.62/2.49    inference(ennf_transformation,[],[f10])).
% 14.62/2.49  
% 14.62/2.49  fof(f61,plain,(
% 14.62/2.49    ( ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 14.62/2.49    inference(cnf_transformation,[],[f21])).
% 14.62/2.49  
% 14.62/2.49  fof(f13,axiom,(
% 14.62/2.49    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X1,X2)) => (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 14.62/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 14.62/2.49  
% 14.62/2.49  fof(f24,plain,(
% 14.62/2.49    ! [X0,X1] : ((r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0) | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 14.62/2.49    inference(ennf_transformation,[],[f13])).
% 14.62/2.49  
% 14.62/2.49  fof(f25,plain,(
% 14.62/2.49    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 14.62/2.49    inference(flattening,[],[f24])).
% 14.62/2.49  
% 14.62/2.49  fof(f38,plain,(
% 14.62/2.49    ! [X1,X0] : (? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)) => (~r1_tarski(X1,sK1(X0,X1)) & r2_hidden(sK1(X0,X1),X0)))),
% 14.62/2.49    introduced(choice_axiom,[])).
% 14.62/2.49  
% 14.62/2.49  fof(f39,plain,(
% 14.62/2.49    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | (~r1_tarski(X1,sK1(X0,X1)) & r2_hidden(sK1(X0,X1),X0)))),
% 14.62/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f25,f38])).
% 14.62/2.49  
% 14.62/2.49  fof(f65,plain,(
% 14.62/2.49    ( ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | r2_hidden(sK1(X0,X1),X0)) )),
% 14.62/2.49    inference(cnf_transformation,[],[f39])).
% 14.62/2.49  
% 14.62/2.49  fof(f9,axiom,(
% 14.62/2.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 14.62/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 14.62/2.49  
% 14.62/2.49  fof(f20,plain,(
% 14.62/2.49    ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 14.62/2.49    inference(ennf_transformation,[],[f9])).
% 14.62/2.49  
% 14.62/2.49  fof(f60,plain,(
% 14.62/2.49    ( ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 14.62/2.49    inference(cnf_transformation,[],[f20])).
% 14.62/2.49  
% 14.62/2.49  fof(f12,axiom,(
% 14.62/2.49    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 14.62/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 14.62/2.49  
% 14.62/2.49  fof(f22,plain,(
% 14.62/2.49    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 14.62/2.49    inference(ennf_transformation,[],[f12])).
% 14.62/2.49  
% 14.62/2.49  fof(f23,plain,(
% 14.62/2.49    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 14.62/2.49    inference(flattening,[],[f22])).
% 14.62/2.49  
% 14.62/2.49  fof(f64,plain,(
% 14.62/2.49    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 14.62/2.49    inference(cnf_transformation,[],[f23])).
% 14.62/2.49  
% 14.62/2.49  fof(f11,axiom,(
% 14.62/2.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 14.62/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 14.62/2.49  
% 14.62/2.49  fof(f37,plain,(
% 14.62/2.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 14.62/2.49    inference(nnf_transformation,[],[f11])).
% 14.62/2.49  
% 14.62/2.49  fof(f63,plain,(
% 14.62/2.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 14.62/2.49    inference(cnf_transformation,[],[f37])).
% 14.62/2.49  
% 14.62/2.49  fof(f62,plain,(
% 14.62/2.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 14.62/2.49    inference(cnf_transformation,[],[f37])).
% 14.62/2.49  
% 14.62/2.49  fof(f71,plain,(
% 14.62/2.49    ~r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3))),
% 14.62/2.49    inference(cnf_transformation,[],[f42])).
% 14.62/2.49  
% 14.62/2.49  fof(f7,axiom,(
% 14.62/2.49    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 14.62/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 14.62/2.49  
% 14.62/2.49  fof(f57,plain,(
% 14.62/2.49    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 14.62/2.49    inference(cnf_transformation,[],[f7])).
% 14.62/2.49  
% 14.62/2.49  fof(f4,axiom,(
% 14.62/2.49    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 14.62/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 14.62/2.49  
% 14.62/2.49  fof(f17,plain,(
% 14.62/2.49    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 14.62/2.49    inference(ennf_transformation,[],[f4])).
% 14.62/2.49  
% 14.62/2.49  fof(f36,plain,(
% 14.62/2.49    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 14.62/2.49    inference(nnf_transformation,[],[f17])).
% 14.62/2.49  
% 14.62/2.49  fof(f51,plain,(
% 14.62/2.49    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 14.62/2.49    inference(cnf_transformation,[],[f36])).
% 14.62/2.49  
% 14.62/2.49  fof(f6,axiom,(
% 14.62/2.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 14.62/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 14.62/2.49  
% 14.62/2.49  fof(f18,plain,(
% 14.62/2.49    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 14.62/2.49    inference(ennf_transformation,[],[f6])).
% 14.62/2.49  
% 14.62/2.49  fof(f56,plain,(
% 14.62/2.49    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 14.62/2.49    inference(cnf_transformation,[],[f18])).
% 14.62/2.49  
% 14.62/2.49  fof(f59,plain,(
% 14.62/2.49    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 14.62/2.49    inference(cnf_transformation,[],[f19])).
% 14.62/2.49  
% 14.62/2.49  fof(f76,plain,(
% 14.62/2.49    ( ! [X0] : (k8_setfam_1(X0,k1_xboole_0) = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 14.62/2.49    inference(equality_resolution,[],[f59])).
% 14.62/2.49  
% 14.62/2.49  fof(f68,plain,(
% 14.62/2.49    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2)))),
% 14.62/2.49    inference(cnf_transformation,[],[f42])).
% 14.62/2.49  
% 14.62/2.49  fof(f14,axiom,(
% 14.62/2.49    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r2_hidden(X0,X1)) => r1_tarski(k1_setfam_1(X1),X2))),
% 14.62/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 14.62/2.49  
% 14.62/2.49  fof(f26,plain,(
% 14.62/2.49    ! [X0,X1,X2] : (r1_tarski(k1_setfam_1(X1),X2) | (~r1_tarski(X0,X2) | ~r2_hidden(X0,X1)))),
% 14.62/2.49    inference(ennf_transformation,[],[f14])).
% 14.62/2.49  
% 14.62/2.49  fof(f27,plain,(
% 14.62/2.49    ! [X0,X1,X2] : (r1_tarski(k1_setfam_1(X1),X2) | ~r1_tarski(X0,X2) | ~r2_hidden(X0,X1))),
% 14.62/2.49    inference(flattening,[],[f26])).
% 14.62/2.49  
% 14.62/2.49  fof(f67,plain,(
% 14.62/2.49    ( ! [X2,X0,X1] : (r1_tarski(k1_setfam_1(X1),X2) | ~r1_tarski(X0,X2) | ~r2_hidden(X0,X1)) )),
% 14.62/2.49    inference(cnf_transformation,[],[f27])).
% 14.62/2.49  
% 14.62/2.49  fof(f1,axiom,(
% 14.62/2.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 14.62/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 14.62/2.49  
% 14.62/2.49  fof(f30,plain,(
% 14.62/2.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 14.62/2.49    inference(nnf_transformation,[],[f1])).
% 14.62/2.49  
% 14.62/2.49  fof(f31,plain,(
% 14.62/2.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 14.62/2.49    inference(flattening,[],[f30])).
% 14.62/2.49  
% 14.62/2.49  fof(f43,plain,(
% 14.62/2.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 14.62/2.49    inference(cnf_transformation,[],[f31])).
% 14.62/2.49  
% 14.62/2.49  fof(f73,plain,(
% 14.62/2.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 14.62/2.49    inference(equality_resolution,[],[f43])).
% 14.62/2.49  
% 14.62/2.49  fof(f66,plain,(
% 14.62/2.49    ( ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X1,sK1(X0,X1))) )),
% 14.62/2.49    inference(cnf_transformation,[],[f39])).
% 14.62/2.49  
% 14.62/2.49  fof(f70,plain,(
% 14.62/2.49    r1_tarski(sK3,sK4)),
% 14.62/2.49    inference(cnf_transformation,[],[f42])).
% 14.62/2.49  
% 14.62/2.49  fof(f45,plain,(
% 14.62/2.49    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 14.62/2.49    inference(cnf_transformation,[],[f31])).
% 14.62/2.49  
% 14.62/2.49  fof(f2,axiom,(
% 14.62/2.49    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 14.62/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 14.62/2.49  
% 14.62/2.49  fof(f46,plain,(
% 14.62/2.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 14.62/2.49    inference(cnf_transformation,[],[f2])).
% 14.62/2.49  
% 14.62/2.49  cnf(c_27,negated_conjecture,
% 14.62/2.49      ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
% 14.62/2.49      inference(cnf_transformation,[],[f69]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_1272,plain,
% 14.62/2.49      ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))) = iProver_top ),
% 14.62/2.49      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_16,plain,
% 14.62/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 14.62/2.49      | k6_setfam_1(X1,X0) = k8_setfam_1(X1,X0)
% 14.62/2.49      | k1_xboole_0 = X0 ),
% 14.62/2.49      inference(cnf_transformation,[],[f58]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_1283,plain,
% 14.62/2.49      ( k6_setfam_1(X0,X1) = k8_setfam_1(X0,X1)
% 14.62/2.49      | k1_xboole_0 = X1
% 14.62/2.49      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 14.62/2.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_5220,plain,
% 14.62/2.49      ( k6_setfam_1(sK2,sK4) = k8_setfam_1(sK2,sK4) | sK4 = k1_xboole_0 ),
% 14.62/2.49      inference(superposition,[status(thm)],[c_1272,c_1283]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_18,plain,
% 14.62/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 14.62/2.49      | k6_setfam_1(X1,X0) = k1_setfam_1(X0) ),
% 14.62/2.49      inference(cnf_transformation,[],[f61]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_1281,plain,
% 14.62/2.49      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
% 14.62/2.49      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 14.62/2.49      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_2281,plain,
% 14.62/2.49      ( k6_setfam_1(sK2,sK4) = k1_setfam_1(sK4) ),
% 14.62/2.49      inference(superposition,[status(thm)],[c_1272,c_1281]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_5229,plain,
% 14.62/2.49      ( k8_setfam_1(sK2,sK4) = k1_setfam_1(sK4) | sK4 = k1_xboole_0 ),
% 14.62/2.49      inference(light_normalisation,[status(thm)],[c_5220,c_2281]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_23,plain,
% 14.62/2.49      ( r2_hidden(sK1(X0,X1),X0)
% 14.62/2.49      | r1_tarski(X1,k1_setfam_1(X0))
% 14.62/2.49      | k1_xboole_0 = X0 ),
% 14.62/2.49      inference(cnf_transformation,[],[f65]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_1276,plain,
% 14.62/2.49      ( k1_xboole_0 = X0
% 14.62/2.49      | r2_hidden(sK1(X0,X1),X0) = iProver_top
% 14.62/2.49      | r1_tarski(X1,k1_setfam_1(X0)) = iProver_top ),
% 14.62/2.49      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_17,plain,
% 14.62/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 14.62/2.49      | m1_subset_1(k8_setfam_1(X1,X0),k1_zfmisc_1(X1)) ),
% 14.62/2.49      inference(cnf_transformation,[],[f60]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_1282,plain,
% 14.62/2.49      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 14.62/2.49      | m1_subset_1(k8_setfam_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 14.62/2.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_21,plain,
% 14.62/2.49      ( m1_subset_1(X0,X1)
% 14.62/2.49      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 14.62/2.49      | ~ r2_hidden(X0,X2) ),
% 14.62/2.49      inference(cnf_transformation,[],[f64]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_1278,plain,
% 14.62/2.49      ( m1_subset_1(X0,X1) = iProver_top
% 14.62/2.49      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 14.62/2.49      | r2_hidden(X0,X2) != iProver_top ),
% 14.62/2.49      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_4151,plain,
% 14.62/2.49      ( m1_subset_1(X0,X1) = iProver_top
% 14.62/2.49      | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 14.62/2.49      | r2_hidden(X0,k8_setfam_1(X1,X2)) != iProver_top ),
% 14.62/2.49      inference(superposition,[status(thm)],[c_1282,c_1278]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_32055,plain,
% 14.62/2.49      ( m1_subset_1(X0,sK2) = iProver_top
% 14.62/2.49      | r2_hidden(X0,k8_setfam_1(sK2,sK4)) != iProver_top ),
% 14.62/2.49      inference(superposition,[status(thm)],[c_1272,c_4151]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_32407,plain,
% 14.62/2.49      ( k8_setfam_1(sK2,sK4) = k1_xboole_0
% 14.62/2.49      | m1_subset_1(sK1(k8_setfam_1(sK2,sK4),X0),sK2) = iProver_top
% 14.62/2.49      | r1_tarski(X0,k1_setfam_1(k8_setfam_1(sK2,sK4))) = iProver_top ),
% 14.62/2.49      inference(superposition,[status(thm)],[c_1276,c_32055]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_19,plain,
% 14.62/2.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 14.62/2.49      inference(cnf_transformation,[],[f63]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_2574,plain,
% 14.62/2.49      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_tarski(X2,X1) ),
% 14.62/2.49      inference(resolution,[status(thm)],[c_21,c_19]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_20,plain,
% 14.62/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 14.62/2.49      inference(cnf_transformation,[],[f62]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_2552,plain,
% 14.62/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 14.62/2.49      | r1_tarski(k8_setfam_1(X1,X0),X1) ),
% 14.62/2.49      inference(resolution,[status(thm)],[c_17,c_20]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_7510,plain,
% 14.62/2.49      ( r1_tarski(k8_setfam_1(sK2,sK4),sK2) ),
% 14.62/2.49      inference(resolution,[status(thm)],[c_2552,c_27]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_8301,plain,
% 14.62/2.49      ( m1_subset_1(X0,sK2) | ~ r2_hidden(X0,k8_setfam_1(sK2,sK4)) ),
% 14.62/2.49      inference(resolution,[status(thm)],[c_2574,c_7510]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_8857,plain,
% 14.62/2.49      ( m1_subset_1(sK1(k8_setfam_1(sK2,sK4),X0),sK2)
% 14.62/2.49      | r1_tarski(X0,k1_setfam_1(k8_setfam_1(sK2,sK4)))
% 14.62/2.49      | k1_xboole_0 = k8_setfam_1(sK2,sK4) ),
% 14.62/2.49      inference(resolution,[status(thm)],[c_8301,c_23]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_25,negated_conjecture,
% 14.62/2.49      ( ~ r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)) ),
% 14.62/2.49      inference(cnf_transformation,[],[f71]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_1510,plain,
% 14.62/2.49      ( ~ m1_subset_1(k8_setfam_1(sK2,sK4),k1_zfmisc_1(k8_setfam_1(sK2,sK3)))
% 14.62/2.49      | r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)) ),
% 14.62/2.49      inference(instantiation,[status(thm)],[c_20]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_619,plain,( X0 = X0 ),theory(equality) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_1658,plain,
% 14.62/2.49      ( k8_setfam_1(sK2,sK4) = k8_setfam_1(sK2,sK4) ),
% 14.62/2.49      inference(instantiation,[status(thm)],[c_619]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_620,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_1663,plain,
% 14.62/2.49      ( X0 != X1
% 14.62/2.49      | k8_setfam_1(sK2,sK4) != X1
% 14.62/2.49      | k8_setfam_1(sK2,sK4) = X0 ),
% 14.62/2.49      inference(instantiation,[status(thm)],[c_620]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_1903,plain,
% 14.62/2.49      ( X0 != k8_setfam_1(sK2,sK4)
% 14.62/2.49      | k8_setfam_1(sK2,sK4) = X0
% 14.62/2.49      | k8_setfam_1(sK2,sK4) != k8_setfam_1(sK2,sK4) ),
% 14.62/2.49      inference(instantiation,[status(thm)],[c_1663]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_1904,plain,
% 14.62/2.49      ( k8_setfam_1(sK2,sK4) != k8_setfam_1(sK2,sK4)
% 14.62/2.49      | k8_setfam_1(sK2,sK4) = k1_xboole_0
% 14.62/2.49      | k1_xboole_0 != k8_setfam_1(sK2,sK4) ),
% 14.62/2.49      inference(instantiation,[status(thm)],[c_1903]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_2200,plain,
% 14.62/2.49      ( k8_setfam_1(sK2,sK3) = k8_setfam_1(sK2,sK3) ),
% 14.62/2.49      inference(instantiation,[status(thm)],[c_619]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_622,plain,
% 14.62/2.49      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 14.62/2.49      theory(equality) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_2366,plain,
% 14.62/2.49      ( k8_setfam_1(sK2,sK3) != X0
% 14.62/2.49      | k1_zfmisc_1(k8_setfam_1(sK2,sK3)) = k1_zfmisc_1(X0) ),
% 14.62/2.49      inference(instantiation,[status(thm)],[c_622]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_4457,plain,
% 14.62/2.49      ( k8_setfam_1(sK2,sK3) != k8_setfam_1(sK2,sK3)
% 14.62/2.49      | k1_zfmisc_1(k8_setfam_1(sK2,sK3)) = k1_zfmisc_1(k8_setfam_1(sK2,sK3)) ),
% 14.62/2.49      inference(instantiation,[status(thm)],[c_2366]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_624,plain,
% 14.62/2.49      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 14.62/2.49      theory(equality) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_1608,plain,
% 14.62/2.49      ( m1_subset_1(X0,X1)
% 14.62/2.49      | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
% 14.62/2.49      | X0 != X2
% 14.62/2.49      | X1 != k1_zfmisc_1(X3) ),
% 14.62/2.49      inference(instantiation,[status(thm)],[c_624]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_1739,plain,
% 14.62/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 14.62/2.49      | m1_subset_1(X2,k1_zfmisc_1(X3))
% 14.62/2.49      | X2 != X0
% 14.62/2.49      | k1_zfmisc_1(X3) != k1_zfmisc_1(X1) ),
% 14.62/2.49      inference(instantiation,[status(thm)],[c_1608]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_2108,plain,
% 14.62/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 14.62/2.49      | m1_subset_1(k8_setfam_1(sK2,sK4),k1_zfmisc_1(k8_setfam_1(sK2,sK3)))
% 14.62/2.49      | k8_setfam_1(sK2,sK4) != X0
% 14.62/2.49      | k1_zfmisc_1(k8_setfam_1(sK2,sK3)) != k1_zfmisc_1(X1) ),
% 14.62/2.49      inference(instantiation,[status(thm)],[c_1739]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_7809,plain,
% 14.62/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k8_setfam_1(sK2,sK3)))
% 14.62/2.49      | m1_subset_1(k8_setfam_1(sK2,sK4),k1_zfmisc_1(k8_setfam_1(sK2,sK3)))
% 14.62/2.49      | k8_setfam_1(sK2,sK4) != X0
% 14.62/2.49      | k1_zfmisc_1(k8_setfam_1(sK2,sK3)) != k1_zfmisc_1(k8_setfam_1(sK2,sK3)) ),
% 14.62/2.49      inference(instantiation,[status(thm)],[c_2108]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_7812,plain,
% 14.62/2.49      ( m1_subset_1(k8_setfam_1(sK2,sK4),k1_zfmisc_1(k8_setfam_1(sK2,sK3)))
% 14.62/2.49      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k8_setfam_1(sK2,sK3)))
% 14.62/2.49      | k8_setfam_1(sK2,sK4) != k1_xboole_0
% 14.62/2.49      | k1_zfmisc_1(k8_setfam_1(sK2,sK3)) != k1_zfmisc_1(k8_setfam_1(sK2,sK3)) ),
% 14.62/2.49      inference(instantiation,[status(thm)],[c_7809]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_14,plain,
% 14.62/2.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 14.62/2.49      inference(cnf_transformation,[],[f57]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_7965,plain,
% 14.62/2.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k8_setfam_1(sK2,sK3))) ),
% 14.62/2.49      inference(instantiation,[status(thm)],[c_14]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_10772,plain,
% 14.62/2.49      ( r1_tarski(X0,k1_setfam_1(k8_setfam_1(sK2,sK4)))
% 14.62/2.49      | m1_subset_1(sK1(k8_setfam_1(sK2,sK4),X0),sK2) ),
% 14.62/2.49      inference(global_propositional_subsumption,
% 14.62/2.49                [status(thm)],
% 14.62/2.49                [c_8857,c_25,c_1510,c_1658,c_1904,c_2200,c_4457,c_7812,
% 14.62/2.49                 c_7965]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_10773,plain,
% 14.62/2.49      ( m1_subset_1(sK1(k8_setfam_1(sK2,sK4),X0),sK2)
% 14.62/2.49      | r1_tarski(X0,k1_setfam_1(k8_setfam_1(sK2,sK4))) ),
% 14.62/2.49      inference(renaming,[status(thm)],[c_10772]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_10774,plain,
% 14.62/2.49      ( m1_subset_1(sK1(k8_setfam_1(sK2,sK4),X0),sK2) = iProver_top
% 14.62/2.49      | r1_tarski(X0,k1_setfam_1(k8_setfam_1(sK2,sK4))) = iProver_top ),
% 14.62/2.49      inference(predicate_to_equality,[status(thm)],[c_10773]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_33310,plain,
% 14.62/2.49      ( m1_subset_1(sK1(k8_setfam_1(sK2,sK4),X0),sK2) = iProver_top
% 14.62/2.49      | r1_tarski(X0,k1_setfam_1(k8_setfam_1(sK2,sK4))) = iProver_top ),
% 14.62/2.49      inference(global_propositional_subsumption,
% 14.62/2.49                [status(thm)],
% 14.62/2.49                [c_32407,c_10774]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_11,plain,
% 14.62/2.49      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 14.62/2.49      inference(cnf_transformation,[],[f51]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_1287,plain,
% 14.62/2.49      ( m1_subset_1(X0,X1) != iProver_top
% 14.62/2.49      | r2_hidden(X0,X1) = iProver_top
% 14.62/2.49      | v1_xboole_0(X1) = iProver_top ),
% 14.62/2.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_33318,plain,
% 14.62/2.49      ( r2_hidden(sK1(k8_setfam_1(sK2,sK4),X0),sK2) = iProver_top
% 14.62/2.49      | r1_tarski(X0,k1_setfam_1(k8_setfam_1(sK2,sK4))) = iProver_top
% 14.62/2.49      | v1_xboole_0(sK2) = iProver_top ),
% 14.62/2.49      inference(superposition,[status(thm)],[c_33310,c_1287]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_13,plain,
% 14.62/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 14.62/2.49      | ~ r2_hidden(X2,X0)
% 14.62/2.49      | r2_hidden(X2,X1) ),
% 14.62/2.49      inference(cnf_transformation,[],[f56]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_228,plain,
% 14.62/2.49      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 14.62/2.49      inference(prop_impl,[status(thm)],[c_19]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_229,plain,
% 14.62/2.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 14.62/2.49      inference(renaming,[status(thm)],[c_228]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_279,plain,
% 14.62/2.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 14.62/2.49      inference(bin_hyper_res,[status(thm)],[c_13,c_229]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_7522,plain,
% 14.62/2.49      ( ~ r2_hidden(X0,k8_setfam_1(sK2,sK4)) | r2_hidden(X0,sK2) ),
% 14.62/2.49      inference(resolution,[status(thm)],[c_7510,c_279]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_7717,plain,
% 14.62/2.49      ( r2_hidden(sK1(k8_setfam_1(sK2,sK4),X0),sK2)
% 14.62/2.49      | r1_tarski(X0,k1_setfam_1(k8_setfam_1(sK2,sK4)))
% 14.62/2.49      | k1_xboole_0 = k8_setfam_1(sK2,sK4) ),
% 14.62/2.49      inference(resolution,[status(thm)],[c_7522,c_23]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_7718,plain,
% 14.62/2.49      ( k1_xboole_0 = k8_setfam_1(sK2,sK4)
% 14.62/2.49      | r2_hidden(sK1(k8_setfam_1(sK2,sK4),X0),sK2) = iProver_top
% 14.62/2.49      | r1_tarski(X0,k1_setfam_1(k8_setfam_1(sK2,sK4))) = iProver_top ),
% 14.62/2.49      inference(predicate_to_equality,[status(thm)],[c_7717]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_39742,plain,
% 14.62/2.49      ( r1_tarski(X0,k1_setfam_1(k8_setfam_1(sK2,sK4))) = iProver_top
% 14.62/2.49      | r2_hidden(sK1(k8_setfam_1(sK2,sK4),X0),sK2) = iProver_top ),
% 14.62/2.49      inference(global_propositional_subsumption,
% 14.62/2.49                [status(thm)],
% 14.62/2.49                [c_33318,c_25,c_1510,c_1658,c_1904,c_2200,c_4457,c_7718,
% 14.62/2.49                 c_7812,c_7965]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_39743,plain,
% 14.62/2.49      ( r2_hidden(sK1(k8_setfam_1(sK2,sK4),X0),sK2) = iProver_top
% 14.62/2.49      | r1_tarski(X0,k1_setfam_1(k8_setfam_1(sK2,sK4))) = iProver_top ),
% 14.62/2.49      inference(renaming,[status(thm)],[c_39742]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_39748,plain,
% 14.62/2.49      ( sK4 = k1_xboole_0
% 14.62/2.49      | r2_hidden(sK1(k1_setfam_1(sK4),X0),sK2) = iProver_top
% 14.62/2.49      | r1_tarski(X0,k1_setfam_1(k8_setfam_1(sK2,sK4))) = iProver_top ),
% 14.62/2.49      inference(superposition,[status(thm)],[c_5229,c_39743]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_1537,plain,
% 14.62/2.49      ( m1_subset_1(k8_setfam_1(sK2,sK4),k1_zfmisc_1(sK2))
% 14.62/2.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
% 14.62/2.49      inference(instantiation,[status(thm)],[c_17]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_1911,plain,
% 14.62/2.49      ( sK2 = sK2 ),
% 14.62/2.49      inference(instantiation,[status(thm)],[c_619]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_1824,plain,
% 14.62/2.49      ( ~ m1_subset_1(k8_setfam_1(sK2,sK4),k1_zfmisc_1(X0))
% 14.62/2.49      | r1_tarski(k8_setfam_1(sK2,sK4),X0) ),
% 14.62/2.49      inference(instantiation,[status(thm)],[c_20]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_2234,plain,
% 14.62/2.49      ( ~ m1_subset_1(k8_setfam_1(sK2,sK4),k1_zfmisc_1(sK2))
% 14.62/2.49      | r1_tarski(k8_setfam_1(sK2,sK4),sK2) ),
% 14.62/2.49      inference(instantiation,[status(thm)],[c_1824]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_621,plain,
% 14.62/2.49      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 14.62/2.49      theory(equality) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_1603,plain,
% 14.62/2.49      ( ~ r1_tarski(X0,X1)
% 14.62/2.49      | r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3))
% 14.62/2.49      | k8_setfam_1(sK2,sK3) != X1
% 14.62/2.49      | k8_setfam_1(sK2,sK4) != X0 ),
% 14.62/2.49      inference(instantiation,[status(thm)],[c_621]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_1657,plain,
% 14.62/2.49      ( ~ r1_tarski(k8_setfam_1(sK2,sK4),X0)
% 14.62/2.49      | r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3))
% 14.62/2.49      | k8_setfam_1(sK2,sK3) != X0
% 14.62/2.49      | k8_setfam_1(sK2,sK4) != k8_setfam_1(sK2,sK4) ),
% 14.62/2.49      inference(instantiation,[status(thm)],[c_1603]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_2349,plain,
% 14.62/2.49      ( r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3))
% 14.62/2.49      | ~ r1_tarski(k8_setfam_1(sK2,sK4),sK2)
% 14.62/2.49      | k8_setfam_1(sK2,sK3) != sK2
% 14.62/2.49      | k8_setfam_1(sK2,sK4) != k8_setfam_1(sK2,sK4) ),
% 14.62/2.49      inference(instantiation,[status(thm)],[c_1657]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_2446,plain,
% 14.62/2.49      ( sK3 = sK3 ),
% 14.62/2.49      inference(instantiation,[status(thm)],[c_619]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_1913,plain,
% 14.62/2.49      ( X0 != X1 | sK2 != X1 | sK2 = X0 ),
% 14.62/2.49      inference(instantiation,[status(thm)],[c_620]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_2396,plain,
% 14.62/2.49      ( X0 != sK2 | sK2 = X0 | sK2 != sK2 ),
% 14.62/2.49      inference(instantiation,[status(thm)],[c_1913]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_4524,plain,
% 14.62/2.49      ( k8_setfam_1(sK2,k1_xboole_0) != sK2
% 14.62/2.49      | sK2 = k8_setfam_1(sK2,k1_xboole_0)
% 14.62/2.49      | sK2 != sK2 ),
% 14.62/2.49      inference(instantiation,[status(thm)],[c_2396]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_15,plain,
% 14.62/2.49      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
% 14.62/2.49      | k8_setfam_1(X0,k1_xboole_0) = X0 ),
% 14.62/2.49      inference(cnf_transformation,[],[f76]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_4525,plain,
% 14.62/2.49      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK2)))
% 14.62/2.49      | k8_setfam_1(sK2,k1_xboole_0) = sK2 ),
% 14.62/2.49      inference(instantiation,[status(thm)],[c_15]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_2448,plain,
% 14.62/2.49      ( X0 != X1 | sK3 != X1 | sK3 = X0 ),
% 14.62/2.49      inference(instantiation,[status(thm)],[c_620]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_4821,plain,
% 14.62/2.49      ( X0 != sK3 | sK3 = X0 | sK3 != sK3 ),
% 14.62/2.49      inference(instantiation,[status(thm)],[c_2448]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_4822,plain,
% 14.62/2.49      ( sK3 != sK3 | sK3 = k1_xboole_0 | k1_xboole_0 != sK3 ),
% 14.62/2.49      inference(instantiation,[status(thm)],[c_4821]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_28,negated_conjecture,
% 14.62/2.49      ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
% 14.62/2.49      inference(cnf_transformation,[],[f68]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_1271,plain,
% 14.62/2.49      ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) = iProver_top ),
% 14.62/2.49      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_5221,plain,
% 14.62/2.49      ( k6_setfam_1(sK2,sK3) = k8_setfam_1(sK2,sK3) | sK3 = k1_xboole_0 ),
% 14.62/2.49      inference(superposition,[status(thm)],[c_1271,c_1283]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_2282,plain,
% 14.62/2.49      ( k6_setfam_1(sK2,sK3) = k1_setfam_1(sK3) ),
% 14.62/2.49      inference(superposition,[status(thm)],[c_1271,c_1281]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_5224,plain,
% 14.62/2.49      ( k8_setfam_1(sK2,sK3) = k1_setfam_1(sK3) | sK3 = k1_xboole_0 ),
% 14.62/2.49      inference(light_normalisation,[status(thm)],[c_5221,c_2282]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_1274,plain,
% 14.62/2.49      ( r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)) != iProver_top ),
% 14.62/2.49      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_6527,plain,
% 14.62/2.49      ( sK3 = k1_xboole_0
% 14.62/2.49      | r1_tarski(k8_setfam_1(sK2,sK4),k1_setfam_1(sK3)) != iProver_top ),
% 14.62/2.49      inference(superposition,[status(thm)],[c_5224,c_1274]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_7682,plain,
% 14.62/2.49      ( sK3 = k1_xboole_0
% 14.62/2.49      | sK4 = k1_xboole_0
% 14.62/2.49      | r1_tarski(k1_setfam_1(sK4),k1_setfam_1(sK3)) != iProver_top ),
% 14.62/2.49      inference(superposition,[status(thm)],[c_5229,c_6527]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_7701,plain,
% 14.62/2.49      ( ~ r1_tarski(k1_setfam_1(sK4),k1_setfam_1(sK3))
% 14.62/2.49      | sK3 = k1_xboole_0
% 14.62/2.49      | sK4 = k1_xboole_0 ),
% 14.62/2.49      inference(predicate_to_equality_rev,[status(thm)],[c_7682]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_1530,plain,
% 14.62/2.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ),
% 14.62/2.49      inference(instantiation,[status(thm)],[c_14]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_10807,plain,
% 14.62/2.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
% 14.62/2.49      inference(instantiation,[status(thm)],[c_1530]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_626,plain,
% 14.62/2.49      ( X0 != X1 | X2 != X3 | k8_setfam_1(X0,X2) = k8_setfam_1(X1,X3) ),
% 14.62/2.49      theory(equality) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_2207,plain,
% 14.62/2.49      ( k8_setfam_1(sK2,sK3) = k8_setfam_1(X0,X1)
% 14.62/2.49      | sK3 != X1
% 14.62/2.49      | sK2 != X0 ),
% 14.62/2.49      inference(instantiation,[status(thm)],[c_626]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_18032,plain,
% 14.62/2.49      ( k8_setfam_1(sK2,sK3) = k8_setfam_1(sK2,X0)
% 14.62/2.49      | sK3 != X0
% 14.62/2.49      | sK2 != sK2 ),
% 14.62/2.49      inference(instantiation,[status(thm)],[c_2207]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_18033,plain,
% 14.62/2.49      ( k8_setfam_1(sK2,sK3) = k8_setfam_1(sK2,k1_xboole_0)
% 14.62/2.49      | sK3 != k1_xboole_0
% 14.62/2.49      | sK2 != sK2 ),
% 14.62/2.49      inference(instantiation,[status(thm)],[c_18032]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_4536,plain,
% 14.62/2.49      ( X0 != X1 | X0 = sK2 | sK2 != X1 ),
% 14.62/2.49      inference(instantiation,[status(thm)],[c_620]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_13167,plain,
% 14.62/2.49      ( k8_setfam_1(sK2,sK3) != X0
% 14.62/2.49      | k8_setfam_1(sK2,sK3) = sK2
% 14.62/2.49      | sK2 != X0 ),
% 14.62/2.49      inference(instantiation,[status(thm)],[c_4536]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_44791,plain,
% 14.62/2.49      ( k8_setfam_1(sK2,sK3) != k8_setfam_1(sK2,k1_xboole_0)
% 14.62/2.49      | k8_setfam_1(sK2,sK3) = sK2
% 14.62/2.49      | sK2 != k8_setfam_1(sK2,k1_xboole_0) ),
% 14.62/2.49      inference(instantiation,[status(thm)],[c_13167]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_24,plain,
% 14.62/2.49      ( ~ r2_hidden(X0,X1)
% 14.62/2.49      | ~ r1_tarski(X0,X2)
% 14.62/2.49      | r1_tarski(k1_setfam_1(X1),X2) ),
% 14.62/2.49      inference(cnf_transformation,[],[f67]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_2,plain,
% 14.62/2.49      ( r1_tarski(X0,X0) ),
% 14.62/2.49      inference(cnf_transformation,[],[f73]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_2720,plain,
% 14.62/2.49      ( ~ r2_hidden(X0,X1) | r1_tarski(k1_setfam_1(X1),X0) ),
% 14.62/2.49      inference(resolution,[status(thm)],[c_24,c_2]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_22,plain,
% 14.62/2.49      ( ~ r1_tarski(X0,sK1(X1,X0))
% 14.62/2.49      | r1_tarski(X0,k1_setfam_1(X1))
% 14.62/2.49      | k1_xboole_0 = X1 ),
% 14.62/2.49      inference(cnf_transformation,[],[f66]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_6766,plain,
% 14.62/2.49      ( ~ r2_hidden(sK1(X0,k1_setfam_1(X1)),X1)
% 14.62/2.49      | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
% 14.62/2.49      | k1_xboole_0 = X0 ),
% 14.62/2.49      inference(resolution,[status(thm)],[c_2720,c_22]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_26,negated_conjecture,
% 14.62/2.49      ( r1_tarski(sK3,sK4) ),
% 14.62/2.49      inference(cnf_transformation,[],[f70]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_2309,plain,
% 14.62/2.49      ( ~ r2_hidden(X0,sK3) | r2_hidden(X0,sK4) ),
% 14.62/2.49      inference(resolution,[status(thm)],[c_279,c_26]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_2904,plain,
% 14.62/2.49      ( r2_hidden(sK1(sK3,X0),sK4)
% 14.62/2.49      | r1_tarski(X0,k1_setfam_1(sK3))
% 14.62/2.49      | k1_xboole_0 = sK3 ),
% 14.62/2.49      inference(resolution,[status(thm)],[c_2309,c_23]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_53553,plain,
% 14.62/2.49      ( r1_tarski(k1_setfam_1(sK4),k1_setfam_1(sK3))
% 14.62/2.49      | k1_xboole_0 = sK3 ),
% 14.62/2.49      inference(resolution,[status(thm)],[c_6766,c_2904]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_54195,plain,
% 14.62/2.49      ( sK4 = k1_xboole_0 ),
% 14.62/2.49      inference(global_propositional_subsumption,
% 14.62/2.49                [status(thm)],
% 14.62/2.49                [c_39748,c_27,c_25,c_1537,c_1658,c_1911,c_2234,c_2349,
% 14.62/2.49                 c_2446,c_4524,c_4525,c_4822,c_7701,c_10807,c_18033,
% 14.62/2.49                 c_44791,c_53553]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_1273,plain,
% 14.62/2.49      ( r1_tarski(sK3,sK4) = iProver_top ),
% 14.62/2.49      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_0,plain,
% 14.62/2.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 14.62/2.49      inference(cnf_transformation,[],[f45]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_1297,plain,
% 14.62/2.49      ( X0 = X1
% 14.62/2.49      | r1_tarski(X0,X1) != iProver_top
% 14.62/2.49      | r1_tarski(X1,X0) != iProver_top ),
% 14.62/2.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_3944,plain,
% 14.62/2.49      ( sK3 = sK4 | r1_tarski(sK4,sK3) != iProver_top ),
% 14.62/2.49      inference(superposition,[status(thm)],[c_1273,c_1297]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_1834,plain,
% 14.62/2.49      ( r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3))
% 14.62/2.49      | ~ r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK4))
% 14.62/2.49      | k8_setfam_1(sK2,sK3) != k8_setfam_1(sK2,sK4)
% 14.62/2.49      | k8_setfam_1(sK2,sK4) != k8_setfam_1(sK2,sK4) ),
% 14.62/2.49      inference(instantiation,[status(thm)],[c_1657]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_1835,plain,
% 14.62/2.49      ( r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK4)) ),
% 14.62/2.49      inference(instantiation,[status(thm)],[c_2]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_2191,plain,
% 14.62/2.49      ( k8_setfam_1(sK2,sK3) = k8_setfam_1(sK2,sK4)
% 14.62/2.49      | sK3 != sK4
% 14.62/2.49      | sK2 != sK2 ),
% 14.62/2.49      inference(instantiation,[status(thm)],[c_626]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_4348,plain,
% 14.62/2.49      ( r1_tarski(sK4,sK3) != iProver_top ),
% 14.62/2.49      inference(global_propositional_subsumption,
% 14.62/2.49                [status(thm)],
% 14.62/2.49                [c_3944,c_25,c_1658,c_1834,c_1835,c_1911,c_2191]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_54315,plain,
% 14.62/2.49      ( r1_tarski(k1_xboole_0,sK3) != iProver_top ),
% 14.62/2.49      inference(demodulation,[status(thm)],[c_54195,c_4348]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_3,plain,
% 14.62/2.49      ( r1_tarski(k1_xboole_0,X0) ),
% 14.62/2.49      inference(cnf_transformation,[],[f46]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_41403,plain,
% 14.62/2.49      ( r1_tarski(k1_xboole_0,sK3) ),
% 14.62/2.49      inference(instantiation,[status(thm)],[c_3]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(c_41406,plain,
% 14.62/2.49      ( r1_tarski(k1_xboole_0,sK3) = iProver_top ),
% 14.62/2.49      inference(predicate_to_equality,[status(thm)],[c_41403]) ).
% 14.62/2.49  
% 14.62/2.49  cnf(contradiction,plain,
% 14.62/2.49      ( $false ),
% 14.62/2.49      inference(minisat,[status(thm)],[c_54315,c_41406]) ).
% 14.62/2.49  
% 14.62/2.49  
% 14.62/2.49  % SZS output end CNFRefutation for theBenchmark.p
% 14.62/2.49  
% 14.62/2.49  ------                               Statistics
% 14.62/2.49  
% 14.62/2.49  ------ Selected
% 14.62/2.49  
% 14.62/2.49  total_time:                             1.564
% 14.62/2.49  
%------------------------------------------------------------------------------
