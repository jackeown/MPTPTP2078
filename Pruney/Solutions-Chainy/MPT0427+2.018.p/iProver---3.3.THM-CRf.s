%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:42:30 EST 2020

% Result     : Theorem 2.39s
% Output     : CNFRefutation 2.39s
% Verified   : 
% Statistics : Number of formulae       :  152 (1923 expanded)
%              Number of clauses        :   93 ( 701 expanded)
%              Number of leaves         :   18 ( 449 expanded)
%              Depth                    :   25
%              Number of atoms          :  363 (6225 expanded)
%              Number of equality atoms :  171 (1627 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   1 average)

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

fof(f24,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f24])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
     => ( ~ r1_tarski(k8_setfam_1(X0,sK3),k8_setfam_1(X0,X1))
        & r1_tarski(X1,sK3)
        & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
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

fof(f35,plain,
    ( ~ r1_tarski(k8_setfam_1(sK1,sK3),k8_setfam_1(sK1,sK2))
    & r1_tarski(sK2,sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1)))
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f25,f34,f33])).

fof(f54,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(cnf_transformation,[],[f35])).

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

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

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

fof(f45,plain,(
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

fof(f48,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f53,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(cnf_transformation,[],[f35])).

fof(f56,plain,(
    ~ r1_tarski(k8_setfam_1(sK1,sK3),k8_setfam_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f35])).

fof(f55,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f4,axiom,(
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
    inference(ennf_transformation,[],[f4])).

fof(f42,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | r1_xboole_0(X0,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f59,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f42])).

fof(f43,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f60,plain,(
    ! [X0] :
      ( k8_setfam_1(X0,k1_xboole_0) = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f46])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f30])).

fof(f41,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f5,axiom,(
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
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f16])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f58,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f39])).

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

fof(f38,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

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

fof(f37,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f57,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f40])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_821,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | m1_subset_1(k8_setfam_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_828,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | m1_subset_1(k8_setfam_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_825,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1873,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | r1_tarski(k8_setfam_1(X1,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_828,c_825])).

cnf(c_3465,plain,
    ( r1_tarski(k8_setfam_1(sK1,sK3),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_821,c_1873])).

cnf(c_16,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_824,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k6_setfam_1(X1,X0) = k8_setfam_1(X1,X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_829,plain,
    ( k6_setfam_1(X0,X1) = k8_setfam_1(X0,X1)
    | k1_xboole_0 = X1
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2051,plain,
    ( k6_setfam_1(sK1,sK3) = k8_setfam_1(sK1,sK3)
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_821,c_829])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k6_setfam_1(X1,X0) = k1_setfam_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_827,plain,
    ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1310,plain,
    ( k6_setfam_1(sK1,sK3) = k1_setfam_1(sK3) ),
    inference(superposition,[status(thm)],[c_821,c_827])).

cnf(c_2060,plain,
    ( k8_setfam_1(sK1,sK3) = k1_setfam_1(sK3)
    | sK3 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2051,c_1310])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_820,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2052,plain,
    ( k6_setfam_1(sK1,sK2) = k8_setfam_1(sK1,sK2)
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_820,c_829])).

cnf(c_1311,plain,
    ( k6_setfam_1(sK1,sK2) = k1_setfam_1(sK2) ),
    inference(superposition,[status(thm)],[c_820,c_827])).

cnf(c_2055,plain,
    ( k8_setfam_1(sK1,sK2) = k1_setfam_1(sK2)
    | sK2 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2052,c_1311])).

cnf(c_17,negated_conjecture,
    ( ~ r1_tarski(k8_setfam_1(sK1,sK3),k8_setfam_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_823,plain,
    ( r1_tarski(k8_setfam_1(sK1,sK3),k8_setfam_1(sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2264,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(k8_setfam_1(sK1,sK3),k1_setfam_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2055,c_823])).

cnf(c_2346,plain,
    ( sK2 = k1_xboole_0
    | sK3 = k1_xboole_0
    | r1_tarski(k1_setfam_1(sK3),k1_setfam_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2060,c_2264])).

cnf(c_2434,plain,
    ( sK2 = k1_xboole_0
    | sK3 = k1_xboole_0
    | r1_tarski(sK2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_824,c_2346])).

cnf(c_18,negated_conjecture,
    ( r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2435,plain,
    ( ~ r1_tarski(sK2,sK3)
    | sK2 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2434])).

cnf(c_2437,plain,
    ( sK3 = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2434,c_18,c_2435])).

cnf(c_2438,plain,
    ( sK2 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_2437])).

cnf(c_2448,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(k8_setfam_1(sK1,sK3),k8_setfam_1(sK1,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2438,c_823])).

cnf(c_2449,plain,
    ( sK3 = k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2438,c_820])).

cnf(c_22,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_7,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_6,plain,
    ( ~ r1_xboole_0(X0,X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_54,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_448,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_962,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | X0 != X2
    | X1 != k1_zfmisc_1(X3) ),
    inference(instantiation,[status(thm)],[c_448])).

cnf(c_1050,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(X2,k1_zfmisc_1(X1))
    | X2 != X0
    | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_962])).

cnf(c_1260,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k1_zfmisc_1(k1_zfmisc_1(X1)) != k1_zfmisc_1(k1_zfmisc_1(X1))
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1050])).

cnf(c_1924,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1)))
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK1)))
    | k1_zfmisc_1(k1_zfmisc_1(sK1)) != k1_zfmisc_1(k1_zfmisc_1(sK1))
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_1260])).

cnf(c_1925,plain,
    ( k1_zfmisc_1(k1_zfmisc_1(sK1)) != k1_zfmisc_1(k1_zfmisc_1(sK1))
    | k1_xboole_0 != sK3
    | m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1924])).

cnf(c_443,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2105,plain,
    ( sK3 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_443])).

cnf(c_2106,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2105])).

cnf(c_442,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1051,plain,
    ( k1_zfmisc_1(X0) = k1_zfmisc_1(X0) ),
    inference(instantiation,[status(thm)],[c_442])).

cnf(c_2217,plain,
    ( k1_zfmisc_1(k1_zfmisc_1(sK1)) = k1_zfmisc_1(k1_zfmisc_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_1051])).

cnf(c_2689,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2449,c_22,c_7,c_54,c_1925,c_2106,c_2217])).

cnf(c_9,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
    | k8_setfam_1(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_830,plain,
    ( k8_setfam_1(X0,k1_xboole_0) = X0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2694,plain,
    ( k8_setfam_1(sK1,k1_xboole_0) = sK1 ),
    inference(superposition,[status(thm)],[c_2689,c_830])).

cnf(c_2751,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(k8_setfam_1(sK1,sK3),sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2448,c_2694])).

cnf(c_3495,plain,
    ( sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3465,c_2751])).

cnf(c_822,plain,
    ( r1_tarski(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_832,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1895,plain,
    ( sK2 = sK3
    | r1_tarski(sK3,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_822,c_832])).

cnf(c_3766,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(k1_xboole_0,sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3495,c_1895])).

cnf(c_8,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_49,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_51,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_49])).

cnf(c_52,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_56,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_58,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_56])).

cnf(c_1109,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_442])).

cnf(c_1102,plain,
    ( X0 != X1
    | sK2 != X1
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_443])).

cnf(c_1545,plain,
    ( X0 != sK2
    | sK2 = X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1102])).

cnf(c_1546,plain,
    ( sK2 != sK2
    | sK2 = k1_xboole_0
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_1545])).

cnf(c_2,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1749,plain,
    ( ~ v1_xboole_0(sK2)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1760,plain,
    ( k1_xboole_0 = sK2
    | v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1749])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_13,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_166,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_13])).

cnf(c_167,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_166])).

cnf(c_198,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(bin_hyper_res,[status(thm)],[c_15,c_167])).

cnf(c_285,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | X0 != X2
    | sK0(X2) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_198])).

cnf(c_286,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_285])).

cnf(c_818,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_286])).

cnf(c_1140,plain,
    ( v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_822,c_818])).

cnf(c_3768,plain,
    ( v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3495,c_1140])).

cnf(c_4046,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3766,c_51,c_52,c_58,c_1109,c_1546,c_1760,c_3768])).

cnf(c_3771,plain,
    ( r1_tarski(k8_setfam_1(sK1,k1_xboole_0),k8_setfam_1(sK1,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3495,c_823])).

cnf(c_3777,plain,
    ( r1_tarski(sK1,k8_setfam_1(sK1,sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3771,c_2694])).

cnf(c_4049,plain,
    ( r1_tarski(sK1,k8_setfam_1(sK1,k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4046,c_3777])).

cnf(c_4061,plain,
    ( r1_tarski(sK1,sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4049,c_2694])).

cnf(c_4,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_831,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4375,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4061,c_831])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:46:35 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 2.39/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.39/0.99  
% 2.39/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.39/0.99  
% 2.39/0.99  ------  iProver source info
% 2.39/0.99  
% 2.39/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.39/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.39/0.99  git: non_committed_changes: false
% 2.39/0.99  git: last_make_outside_of_git: false
% 2.39/0.99  
% 2.39/0.99  ------ 
% 2.39/0.99  
% 2.39/0.99  ------ Input Options
% 2.39/0.99  
% 2.39/0.99  --out_options                           all
% 2.39/0.99  --tptp_safe_out                         true
% 2.39/0.99  --problem_path                          ""
% 2.39/0.99  --include_path                          ""
% 2.39/0.99  --clausifier                            res/vclausify_rel
% 2.39/0.99  --clausifier_options                    --mode clausify
% 2.39/0.99  --stdin                                 false
% 2.39/0.99  --stats_out                             all
% 2.39/0.99  
% 2.39/0.99  ------ General Options
% 2.39/0.99  
% 2.39/0.99  --fof                                   false
% 2.39/0.99  --time_out_real                         305.
% 2.39/0.99  --time_out_virtual                      -1.
% 2.39/0.99  --symbol_type_check                     false
% 2.39/0.99  --clausify_out                          false
% 2.39/0.99  --sig_cnt_out                           false
% 2.39/0.99  --trig_cnt_out                          false
% 2.39/0.99  --trig_cnt_out_tolerance                1.
% 2.39/0.99  --trig_cnt_out_sk_spl                   false
% 2.39/0.99  --abstr_cl_out                          false
% 2.39/0.99  
% 2.39/0.99  ------ Global Options
% 2.39/0.99  
% 2.39/0.99  --schedule                              default
% 2.39/0.99  --add_important_lit                     false
% 2.39/0.99  --prop_solver_per_cl                    1000
% 2.39/0.99  --min_unsat_core                        false
% 2.39/0.99  --soft_assumptions                      false
% 2.39/0.99  --soft_lemma_size                       3
% 2.39/0.99  --prop_impl_unit_size                   0
% 2.39/0.99  --prop_impl_unit                        []
% 2.39/0.99  --share_sel_clauses                     true
% 2.39/0.99  --reset_solvers                         false
% 2.39/0.99  --bc_imp_inh                            [conj_cone]
% 2.39/0.99  --conj_cone_tolerance                   3.
% 2.39/0.99  --extra_neg_conj                        none
% 2.39/0.99  --large_theory_mode                     true
% 2.39/0.99  --prolific_symb_bound                   200
% 2.39/0.99  --lt_threshold                          2000
% 2.39/0.99  --clause_weak_htbl                      true
% 2.39/0.99  --gc_record_bc_elim                     false
% 2.39/0.99  
% 2.39/0.99  ------ Preprocessing Options
% 2.39/0.99  
% 2.39/0.99  --preprocessing_flag                    true
% 2.39/0.99  --time_out_prep_mult                    0.1
% 2.39/0.99  --splitting_mode                        input
% 2.39/0.99  --splitting_grd                         true
% 2.39/0.99  --splitting_cvd                         false
% 2.39/0.99  --splitting_cvd_svl                     false
% 2.39/0.99  --splitting_nvd                         32
% 2.39/0.99  --sub_typing                            true
% 2.39/0.99  --prep_gs_sim                           true
% 2.39/0.99  --prep_unflatten                        true
% 2.39/0.99  --prep_res_sim                          true
% 2.39/0.99  --prep_upred                            true
% 2.39/0.99  --prep_sem_filter                       exhaustive
% 2.39/0.99  --prep_sem_filter_out                   false
% 2.39/0.99  --pred_elim                             true
% 2.39/0.99  --res_sim_input                         true
% 2.39/0.99  --eq_ax_congr_red                       true
% 2.39/0.99  --pure_diseq_elim                       true
% 2.39/0.99  --brand_transform                       false
% 2.39/0.99  --non_eq_to_eq                          false
% 2.39/0.99  --prep_def_merge                        true
% 2.39/0.99  --prep_def_merge_prop_impl              false
% 2.39/0.99  --prep_def_merge_mbd                    true
% 2.39/0.99  --prep_def_merge_tr_red                 false
% 2.39/0.99  --prep_def_merge_tr_cl                  false
% 2.39/0.99  --smt_preprocessing                     true
% 2.39/0.99  --smt_ac_axioms                         fast
% 2.39/0.99  --preprocessed_out                      false
% 2.39/0.99  --preprocessed_stats                    false
% 2.39/0.99  
% 2.39/0.99  ------ Abstraction refinement Options
% 2.39/0.99  
% 2.39/0.99  --abstr_ref                             []
% 2.39/0.99  --abstr_ref_prep                        false
% 2.39/0.99  --abstr_ref_until_sat                   false
% 2.39/0.99  --abstr_ref_sig_restrict                funpre
% 2.39/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.39/0.99  --abstr_ref_under                       []
% 2.39/0.99  
% 2.39/0.99  ------ SAT Options
% 2.39/0.99  
% 2.39/0.99  --sat_mode                              false
% 2.39/0.99  --sat_fm_restart_options                ""
% 2.39/0.99  --sat_gr_def                            false
% 2.39/0.99  --sat_epr_types                         true
% 2.39/0.99  --sat_non_cyclic_types                  false
% 2.39/0.99  --sat_finite_models                     false
% 2.39/0.99  --sat_fm_lemmas                         false
% 2.39/0.99  --sat_fm_prep                           false
% 2.39/0.99  --sat_fm_uc_incr                        true
% 2.39/0.99  --sat_out_model                         small
% 2.39/0.99  --sat_out_clauses                       false
% 2.39/0.99  
% 2.39/0.99  ------ QBF Options
% 2.39/0.99  
% 2.39/0.99  --qbf_mode                              false
% 2.39/0.99  --qbf_elim_univ                         false
% 2.39/0.99  --qbf_dom_inst                          none
% 2.39/0.99  --qbf_dom_pre_inst                      false
% 2.39/0.99  --qbf_sk_in                             false
% 2.39/0.99  --qbf_pred_elim                         true
% 2.39/0.99  --qbf_split                             512
% 2.39/0.99  
% 2.39/0.99  ------ BMC1 Options
% 2.39/0.99  
% 2.39/0.99  --bmc1_incremental                      false
% 2.39/0.99  --bmc1_axioms                           reachable_all
% 2.39/0.99  --bmc1_min_bound                        0
% 2.39/0.99  --bmc1_max_bound                        -1
% 2.39/0.99  --bmc1_max_bound_default                -1
% 2.39/0.99  --bmc1_symbol_reachability              true
% 2.39/0.99  --bmc1_property_lemmas                  false
% 2.39/0.99  --bmc1_k_induction                      false
% 2.39/0.99  --bmc1_non_equiv_states                 false
% 2.39/0.99  --bmc1_deadlock                         false
% 2.39/0.99  --bmc1_ucm                              false
% 2.39/0.99  --bmc1_add_unsat_core                   none
% 2.39/0.99  --bmc1_unsat_core_children              false
% 2.39/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.39/0.99  --bmc1_out_stat                         full
% 2.39/0.99  --bmc1_ground_init                      false
% 2.39/0.99  --bmc1_pre_inst_next_state              false
% 2.39/0.99  --bmc1_pre_inst_state                   false
% 2.39/0.99  --bmc1_pre_inst_reach_state             false
% 2.39/0.99  --bmc1_out_unsat_core                   false
% 2.39/0.99  --bmc1_aig_witness_out                  false
% 2.39/0.99  --bmc1_verbose                          false
% 2.39/0.99  --bmc1_dump_clauses_tptp                false
% 2.39/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.39/0.99  --bmc1_dump_file                        -
% 2.39/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.39/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.39/0.99  --bmc1_ucm_extend_mode                  1
% 2.39/0.99  --bmc1_ucm_init_mode                    2
% 2.39/0.99  --bmc1_ucm_cone_mode                    none
% 2.39/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.39/0.99  --bmc1_ucm_relax_model                  4
% 2.39/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.39/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.39/0.99  --bmc1_ucm_layered_model                none
% 2.39/0.99  --bmc1_ucm_max_lemma_size               10
% 2.39/0.99  
% 2.39/0.99  ------ AIG Options
% 2.39/0.99  
% 2.39/0.99  --aig_mode                              false
% 2.39/0.99  
% 2.39/0.99  ------ Instantiation Options
% 2.39/0.99  
% 2.39/0.99  --instantiation_flag                    true
% 2.39/0.99  --inst_sos_flag                         false
% 2.39/0.99  --inst_sos_phase                        true
% 2.39/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.39/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.39/0.99  --inst_lit_sel_side                     num_symb
% 2.39/0.99  --inst_solver_per_active                1400
% 2.39/0.99  --inst_solver_calls_frac                1.
% 2.39/0.99  --inst_passive_queue_type               priority_queues
% 2.39/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.39/0.99  --inst_passive_queues_freq              [25;2]
% 2.39/0.99  --inst_dismatching                      true
% 2.39/0.99  --inst_eager_unprocessed_to_passive     true
% 2.39/0.99  --inst_prop_sim_given                   true
% 2.39/0.99  --inst_prop_sim_new                     false
% 2.39/0.99  --inst_subs_new                         false
% 2.39/0.99  --inst_eq_res_simp                      false
% 2.39/0.99  --inst_subs_given                       false
% 2.39/0.99  --inst_orphan_elimination               true
% 2.39/0.99  --inst_learning_loop_flag               true
% 2.39/0.99  --inst_learning_start                   3000
% 2.39/0.99  --inst_learning_factor                  2
% 2.39/0.99  --inst_start_prop_sim_after_learn       3
% 2.39/0.99  --inst_sel_renew                        solver
% 2.39/0.99  --inst_lit_activity_flag                true
% 2.39/0.99  --inst_restr_to_given                   false
% 2.39/0.99  --inst_activity_threshold               500
% 2.39/0.99  --inst_out_proof                        true
% 2.39/0.99  
% 2.39/0.99  ------ Resolution Options
% 2.39/0.99  
% 2.39/0.99  --resolution_flag                       true
% 2.39/0.99  --res_lit_sel                           adaptive
% 2.39/0.99  --res_lit_sel_side                      none
% 2.39/0.99  --res_ordering                          kbo
% 2.39/0.99  --res_to_prop_solver                    active
% 2.39/0.99  --res_prop_simpl_new                    false
% 2.39/0.99  --res_prop_simpl_given                  true
% 2.39/0.99  --res_passive_queue_type                priority_queues
% 2.39/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.39/0.99  --res_passive_queues_freq               [15;5]
% 2.39/0.99  --res_forward_subs                      full
% 2.39/0.99  --res_backward_subs                     full
% 2.39/0.99  --res_forward_subs_resolution           true
% 2.39/0.99  --res_backward_subs_resolution          true
% 2.39/0.99  --res_orphan_elimination                true
% 2.39/0.99  --res_time_limit                        2.
% 2.39/0.99  --res_out_proof                         true
% 2.39/0.99  
% 2.39/0.99  ------ Superposition Options
% 2.39/0.99  
% 2.39/0.99  --superposition_flag                    true
% 2.39/0.99  --sup_passive_queue_type                priority_queues
% 2.39/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.39/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.39/0.99  --demod_completeness_check              fast
% 2.39/0.99  --demod_use_ground                      true
% 2.39/0.99  --sup_to_prop_solver                    passive
% 2.39/0.99  --sup_prop_simpl_new                    true
% 2.39/0.99  --sup_prop_simpl_given                  true
% 2.39/0.99  --sup_fun_splitting                     false
% 2.39/0.99  --sup_smt_interval                      50000
% 2.39/0.99  
% 2.39/0.99  ------ Superposition Simplification Setup
% 2.39/0.99  
% 2.39/0.99  --sup_indices_passive                   []
% 2.39/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.39/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.39/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.39/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.39/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.39/0.99  --sup_full_bw                           [BwDemod]
% 2.39/0.99  --sup_immed_triv                        [TrivRules]
% 2.39/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.39/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.39/0.99  --sup_immed_bw_main                     []
% 2.39/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.39/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.39/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.39/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.39/0.99  
% 2.39/0.99  ------ Combination Options
% 2.39/0.99  
% 2.39/0.99  --comb_res_mult                         3
% 2.39/0.99  --comb_sup_mult                         2
% 2.39/0.99  --comb_inst_mult                        10
% 2.39/0.99  
% 2.39/0.99  ------ Debug Options
% 2.39/0.99  
% 2.39/0.99  --dbg_backtrace                         false
% 2.39/0.99  --dbg_dump_prop_clauses                 false
% 2.39/0.99  --dbg_dump_prop_clauses_file            -
% 2.39/0.99  --dbg_out_stat                          false
% 2.39/0.99  ------ Parsing...
% 2.39/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.39/0.99  
% 2.39/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.39/0.99  
% 2.39/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.39/0.99  
% 2.39/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.39/0.99  ------ Proving...
% 2.39/0.99  ------ Problem Properties 
% 2.39/0.99  
% 2.39/0.99  
% 2.39/0.99  clauses                                 16
% 2.39/0.99  conjectures                             4
% 2.39/0.99  EPR                                     6
% 2.39/0.99  Horn                                    14
% 2.39/0.99  unary                                   6
% 2.39/0.99  binary                                  6
% 2.39/0.99  lits                                    30
% 2.39/0.99  lits eq                                 7
% 2.39/0.99  fd_pure                                 0
% 2.39/0.99  fd_pseudo                               0
% 2.39/0.99  fd_cond                                 3
% 2.39/0.99  fd_pseudo_cond                          1
% 2.39/0.99  AC symbols                              0
% 2.39/0.99  
% 2.39/0.99  ------ Schedule dynamic 5 is on 
% 2.39/0.99  
% 2.39/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.39/0.99  
% 2.39/0.99  
% 2.39/0.99  ------ 
% 2.39/0.99  Current options:
% 2.39/0.99  ------ 
% 2.39/0.99  
% 2.39/0.99  ------ Input Options
% 2.39/0.99  
% 2.39/0.99  --out_options                           all
% 2.39/0.99  --tptp_safe_out                         true
% 2.39/0.99  --problem_path                          ""
% 2.39/0.99  --include_path                          ""
% 2.39/0.99  --clausifier                            res/vclausify_rel
% 2.39/0.99  --clausifier_options                    --mode clausify
% 2.39/0.99  --stdin                                 false
% 2.39/0.99  --stats_out                             all
% 2.39/0.99  
% 2.39/0.99  ------ General Options
% 2.39/0.99  
% 2.39/0.99  --fof                                   false
% 2.39/0.99  --time_out_real                         305.
% 2.39/0.99  --time_out_virtual                      -1.
% 2.39/0.99  --symbol_type_check                     false
% 2.39/0.99  --clausify_out                          false
% 2.39/0.99  --sig_cnt_out                           false
% 2.39/0.99  --trig_cnt_out                          false
% 2.39/0.99  --trig_cnt_out_tolerance                1.
% 2.39/0.99  --trig_cnt_out_sk_spl                   false
% 2.39/0.99  --abstr_cl_out                          false
% 2.39/0.99  
% 2.39/0.99  ------ Global Options
% 2.39/0.99  
% 2.39/0.99  --schedule                              default
% 2.39/0.99  --add_important_lit                     false
% 2.39/0.99  --prop_solver_per_cl                    1000
% 2.39/0.99  --min_unsat_core                        false
% 2.39/0.99  --soft_assumptions                      false
% 2.39/0.99  --soft_lemma_size                       3
% 2.39/0.99  --prop_impl_unit_size                   0
% 2.39/0.99  --prop_impl_unit                        []
% 2.39/0.99  --share_sel_clauses                     true
% 2.39/0.99  --reset_solvers                         false
% 2.39/0.99  --bc_imp_inh                            [conj_cone]
% 2.39/0.99  --conj_cone_tolerance                   3.
% 2.39/0.99  --extra_neg_conj                        none
% 2.39/0.99  --large_theory_mode                     true
% 2.39/0.99  --prolific_symb_bound                   200
% 2.39/0.99  --lt_threshold                          2000
% 2.39/0.99  --clause_weak_htbl                      true
% 2.39/0.99  --gc_record_bc_elim                     false
% 2.39/0.99  
% 2.39/0.99  ------ Preprocessing Options
% 2.39/0.99  
% 2.39/0.99  --preprocessing_flag                    true
% 2.39/0.99  --time_out_prep_mult                    0.1
% 2.39/0.99  --splitting_mode                        input
% 2.39/0.99  --splitting_grd                         true
% 2.39/0.99  --splitting_cvd                         false
% 2.39/0.99  --splitting_cvd_svl                     false
% 2.39/0.99  --splitting_nvd                         32
% 2.39/0.99  --sub_typing                            true
% 2.39/0.99  --prep_gs_sim                           true
% 2.39/0.99  --prep_unflatten                        true
% 2.39/0.99  --prep_res_sim                          true
% 2.39/0.99  --prep_upred                            true
% 2.39/0.99  --prep_sem_filter                       exhaustive
% 2.39/0.99  --prep_sem_filter_out                   false
% 2.39/0.99  --pred_elim                             true
% 2.39/0.99  --res_sim_input                         true
% 2.39/0.99  --eq_ax_congr_red                       true
% 2.39/0.99  --pure_diseq_elim                       true
% 2.39/0.99  --brand_transform                       false
% 2.39/0.99  --non_eq_to_eq                          false
% 2.39/0.99  --prep_def_merge                        true
% 2.39/0.99  --prep_def_merge_prop_impl              false
% 2.39/0.99  --prep_def_merge_mbd                    true
% 2.39/0.99  --prep_def_merge_tr_red                 false
% 2.39/0.99  --prep_def_merge_tr_cl                  false
% 2.39/0.99  --smt_preprocessing                     true
% 2.39/0.99  --smt_ac_axioms                         fast
% 2.39/0.99  --preprocessed_out                      false
% 2.39/0.99  --preprocessed_stats                    false
% 2.39/0.99  
% 2.39/0.99  ------ Abstraction refinement Options
% 2.39/0.99  
% 2.39/0.99  --abstr_ref                             []
% 2.39/0.99  --abstr_ref_prep                        false
% 2.39/0.99  --abstr_ref_until_sat                   false
% 2.39/0.99  --abstr_ref_sig_restrict                funpre
% 2.39/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.39/0.99  --abstr_ref_under                       []
% 2.39/0.99  
% 2.39/0.99  ------ SAT Options
% 2.39/0.99  
% 2.39/0.99  --sat_mode                              false
% 2.39/0.99  --sat_fm_restart_options                ""
% 2.39/0.99  --sat_gr_def                            false
% 2.39/0.99  --sat_epr_types                         true
% 2.39/0.99  --sat_non_cyclic_types                  false
% 2.39/0.99  --sat_finite_models                     false
% 2.39/0.99  --sat_fm_lemmas                         false
% 2.39/0.99  --sat_fm_prep                           false
% 2.39/0.99  --sat_fm_uc_incr                        true
% 2.39/0.99  --sat_out_model                         small
% 2.39/0.99  --sat_out_clauses                       false
% 2.39/0.99  
% 2.39/0.99  ------ QBF Options
% 2.39/0.99  
% 2.39/0.99  --qbf_mode                              false
% 2.39/0.99  --qbf_elim_univ                         false
% 2.39/0.99  --qbf_dom_inst                          none
% 2.39/0.99  --qbf_dom_pre_inst                      false
% 2.39/0.99  --qbf_sk_in                             false
% 2.39/0.99  --qbf_pred_elim                         true
% 2.39/0.99  --qbf_split                             512
% 2.39/0.99  
% 2.39/0.99  ------ BMC1 Options
% 2.39/0.99  
% 2.39/0.99  --bmc1_incremental                      false
% 2.39/0.99  --bmc1_axioms                           reachable_all
% 2.39/0.99  --bmc1_min_bound                        0
% 2.39/0.99  --bmc1_max_bound                        -1
% 2.39/0.99  --bmc1_max_bound_default                -1
% 2.39/0.99  --bmc1_symbol_reachability              true
% 2.39/0.99  --bmc1_property_lemmas                  false
% 2.39/0.99  --bmc1_k_induction                      false
% 2.39/0.99  --bmc1_non_equiv_states                 false
% 2.39/0.99  --bmc1_deadlock                         false
% 2.39/0.99  --bmc1_ucm                              false
% 2.39/0.99  --bmc1_add_unsat_core                   none
% 2.39/0.99  --bmc1_unsat_core_children              false
% 2.39/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.39/0.99  --bmc1_out_stat                         full
% 2.39/0.99  --bmc1_ground_init                      false
% 2.39/0.99  --bmc1_pre_inst_next_state              false
% 2.39/0.99  --bmc1_pre_inst_state                   false
% 2.39/0.99  --bmc1_pre_inst_reach_state             false
% 2.39/0.99  --bmc1_out_unsat_core                   false
% 2.39/0.99  --bmc1_aig_witness_out                  false
% 2.39/0.99  --bmc1_verbose                          false
% 2.39/0.99  --bmc1_dump_clauses_tptp                false
% 2.39/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.39/0.99  --bmc1_dump_file                        -
% 2.39/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.39/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.39/0.99  --bmc1_ucm_extend_mode                  1
% 2.39/0.99  --bmc1_ucm_init_mode                    2
% 2.39/0.99  --bmc1_ucm_cone_mode                    none
% 2.39/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.39/0.99  --bmc1_ucm_relax_model                  4
% 2.39/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.39/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.39/0.99  --bmc1_ucm_layered_model                none
% 2.39/0.99  --bmc1_ucm_max_lemma_size               10
% 2.39/0.99  
% 2.39/0.99  ------ AIG Options
% 2.39/0.99  
% 2.39/0.99  --aig_mode                              false
% 2.39/0.99  
% 2.39/0.99  ------ Instantiation Options
% 2.39/0.99  
% 2.39/0.99  --instantiation_flag                    true
% 2.39/0.99  --inst_sos_flag                         false
% 2.39/0.99  --inst_sos_phase                        true
% 2.39/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.39/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.39/0.99  --inst_lit_sel_side                     none
% 2.39/0.99  --inst_solver_per_active                1400
% 2.39/0.99  --inst_solver_calls_frac                1.
% 2.39/0.99  --inst_passive_queue_type               priority_queues
% 2.39/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.39/0.99  --inst_passive_queues_freq              [25;2]
% 2.39/0.99  --inst_dismatching                      true
% 2.39/0.99  --inst_eager_unprocessed_to_passive     true
% 2.39/0.99  --inst_prop_sim_given                   true
% 2.39/0.99  --inst_prop_sim_new                     false
% 2.39/0.99  --inst_subs_new                         false
% 2.39/0.99  --inst_eq_res_simp                      false
% 2.39/0.99  --inst_subs_given                       false
% 2.39/0.99  --inst_orphan_elimination               true
% 2.39/0.99  --inst_learning_loop_flag               true
% 2.39/0.99  --inst_learning_start                   3000
% 2.39/0.99  --inst_learning_factor                  2
% 2.39/0.99  --inst_start_prop_sim_after_learn       3
% 2.39/0.99  --inst_sel_renew                        solver
% 2.39/0.99  --inst_lit_activity_flag                true
% 2.39/0.99  --inst_restr_to_given                   false
% 2.39/0.99  --inst_activity_threshold               500
% 2.39/0.99  --inst_out_proof                        true
% 2.39/0.99  
% 2.39/0.99  ------ Resolution Options
% 2.39/0.99  
% 2.39/0.99  --resolution_flag                       false
% 2.39/0.99  --res_lit_sel                           adaptive
% 2.39/0.99  --res_lit_sel_side                      none
% 2.39/0.99  --res_ordering                          kbo
% 2.39/0.99  --res_to_prop_solver                    active
% 2.39/0.99  --res_prop_simpl_new                    false
% 2.39/0.99  --res_prop_simpl_given                  true
% 2.39/0.99  --res_passive_queue_type                priority_queues
% 2.39/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.39/0.99  --res_passive_queues_freq               [15;5]
% 2.39/0.99  --res_forward_subs                      full
% 2.39/0.99  --res_backward_subs                     full
% 2.39/0.99  --res_forward_subs_resolution           true
% 2.39/0.99  --res_backward_subs_resolution          true
% 2.39/0.99  --res_orphan_elimination                true
% 2.39/0.99  --res_time_limit                        2.
% 2.39/0.99  --res_out_proof                         true
% 2.39/0.99  
% 2.39/0.99  ------ Superposition Options
% 2.39/0.99  
% 2.39/0.99  --superposition_flag                    true
% 2.39/0.99  --sup_passive_queue_type                priority_queues
% 2.39/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.39/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.39/0.99  --demod_completeness_check              fast
% 2.39/0.99  --demod_use_ground                      true
% 2.39/0.99  --sup_to_prop_solver                    passive
% 2.39/0.99  --sup_prop_simpl_new                    true
% 2.39/0.99  --sup_prop_simpl_given                  true
% 2.39/0.99  --sup_fun_splitting                     false
% 2.39/0.99  --sup_smt_interval                      50000
% 2.39/0.99  
% 2.39/0.99  ------ Superposition Simplification Setup
% 2.39/0.99  
% 2.39/0.99  --sup_indices_passive                   []
% 2.39/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.39/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.39/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.39/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.39/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.39/0.99  --sup_full_bw                           [BwDemod]
% 2.39/0.99  --sup_immed_triv                        [TrivRules]
% 2.39/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.39/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.39/0.99  --sup_immed_bw_main                     []
% 2.39/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.39/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.39/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.39/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.39/0.99  
% 2.39/0.99  ------ Combination Options
% 2.39/0.99  
% 2.39/0.99  --comb_res_mult                         3
% 2.39/0.99  --comb_sup_mult                         2
% 2.39/0.99  --comb_inst_mult                        10
% 2.39/0.99  
% 2.39/0.99  ------ Debug Options
% 2.39/0.99  
% 2.39/0.99  --dbg_backtrace                         false
% 2.39/0.99  --dbg_dump_prop_clauses                 false
% 2.39/0.99  --dbg_dump_prop_clauses_file            -
% 2.39/0.99  --dbg_out_stat                          false
% 2.39/0.99  
% 2.39/0.99  
% 2.39/0.99  
% 2.39/0.99  
% 2.39/0.99  ------ Proving...
% 2.39/0.99  
% 2.39/0.99  
% 2.39/0.99  % SZS status Theorem for theBenchmark.p
% 2.39/0.99  
% 2.39/0.99   Resolution empty clause
% 2.39/0.99  
% 2.39/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.39/0.99  
% 2.39/0.99  fof(f12,conjecture,(
% 2.39/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 2.39/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.39/0.99  
% 2.39/0.99  fof(f13,negated_conjecture,(
% 2.39/0.99    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 2.39/0.99    inference(negated_conjecture,[],[f12])).
% 2.39/0.99  
% 2.39/0.99  fof(f24,plain,(
% 2.39/0.99    ? [X0,X1] : (? [X2] : ((~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.39/0.99    inference(ennf_transformation,[],[f13])).
% 2.39/0.99  
% 2.39/0.99  fof(f25,plain,(
% 2.39/0.99    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.39/0.99    inference(flattening,[],[f24])).
% 2.39/0.99  
% 2.39/0.99  fof(f34,plain,(
% 2.39/0.99    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (~r1_tarski(k8_setfam_1(X0,sK3),k8_setfam_1(X0,X1)) & r1_tarski(X1,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(X0))))) )),
% 2.39/0.99    introduced(choice_axiom,[])).
% 2.39/0.99  
% 2.39/0.99  fof(f33,plain,(
% 2.39/0.99    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (? [X2] : (~r1_tarski(k8_setfam_1(sK1,X2),k8_setfam_1(sK1,sK2)) & r1_tarski(sK2,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK1)))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))))),
% 2.39/0.99    introduced(choice_axiom,[])).
% 2.39/0.99  
% 2.39/0.99  fof(f35,plain,(
% 2.39/0.99    (~r1_tarski(k8_setfam_1(sK1,sK3),k8_setfam_1(sK1,sK2)) & r1_tarski(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1)))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1)))),
% 2.39/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f25,f34,f33])).
% 2.39/0.99  
% 2.39/0.99  fof(f54,plain,(
% 2.39/0.99    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1)))),
% 2.39/0.99    inference(cnf_transformation,[],[f35])).
% 2.39/0.99  
% 2.39/0.99  fof(f7,axiom,(
% 2.39/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.39/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.39/0.99  
% 2.39/0.99  fof(f19,plain,(
% 2.39/0.99    ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.39/0.99    inference(ennf_transformation,[],[f7])).
% 2.39/0.99  
% 2.39/0.99  fof(f47,plain,(
% 2.39/0.99    ( ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.39/0.99    inference(cnf_transformation,[],[f19])).
% 2.39/0.99  
% 2.39/0.99  fof(f9,axiom,(
% 2.39/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.39/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.39/0.99  
% 2.39/0.99  fof(f32,plain,(
% 2.39/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.39/0.99    inference(nnf_transformation,[],[f9])).
% 2.39/0.99  
% 2.39/0.99  fof(f49,plain,(
% 2.39/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.39/0.99    inference(cnf_transformation,[],[f32])).
% 2.39/0.99  
% 2.39/0.99  fof(f11,axiom,(
% 2.39/0.99    ! [X0,X1] : (r1_tarski(X0,X1) => (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 2.39/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.39/0.99  
% 2.39/0.99  fof(f22,plain,(
% 2.39/0.99    ! [X0,X1] : ((r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0) | ~r1_tarski(X0,X1))),
% 2.39/0.99    inference(ennf_transformation,[],[f11])).
% 2.39/0.99  
% 2.39/0.99  fof(f23,plain,(
% 2.39/0.99    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1))),
% 2.39/0.99    inference(flattening,[],[f22])).
% 2.39/0.99  
% 2.39/0.99  fof(f52,plain,(
% 2.39/0.99    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1)) )),
% 2.39/0.99    inference(cnf_transformation,[],[f23])).
% 2.39/0.99  
% 2.39/0.99  fof(f6,axiom,(
% 2.39/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((k1_xboole_0 = X1 => k8_setfam_1(X0,X1) = X0) & (k1_xboole_0 != X1 => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1))))),
% 2.39/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.39/0.99  
% 2.39/0.99  fof(f18,plain,(
% 2.39/0.99    ! [X0,X1] : (((k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1) & (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.39/0.99    inference(ennf_transformation,[],[f6])).
% 2.39/0.99  
% 2.39/0.99  fof(f45,plain,(
% 2.39/0.99    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.39/0.99    inference(cnf_transformation,[],[f18])).
% 2.39/0.99  
% 2.39/0.99  fof(f8,axiom,(
% 2.39/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k6_setfam_1(X0,X1) = k1_setfam_1(X1))),
% 2.39/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.39/0.99  
% 2.39/0.99  fof(f20,plain,(
% 2.39/0.99    ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.39/0.99    inference(ennf_transformation,[],[f8])).
% 2.39/0.99  
% 2.39/0.99  fof(f48,plain,(
% 2.39/0.99    ( ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.39/0.99    inference(cnf_transformation,[],[f20])).
% 2.39/0.99  
% 2.39/0.99  fof(f53,plain,(
% 2.39/0.99    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1)))),
% 2.39/0.99    inference(cnf_transformation,[],[f35])).
% 2.39/0.99  
% 2.39/0.99  fof(f56,plain,(
% 2.39/0.99    ~r1_tarski(k8_setfam_1(sK1,sK3),k8_setfam_1(sK1,sK2))),
% 2.39/0.99    inference(cnf_transformation,[],[f35])).
% 2.39/0.99  
% 2.39/0.99  fof(f55,plain,(
% 2.39/0.99    r1_tarski(sK2,sK3)),
% 2.39/0.99    inference(cnf_transformation,[],[f35])).
% 2.39/0.99  
% 2.39/0.99  fof(f4,axiom,(
% 2.39/0.99    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 2.39/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.39/0.99  
% 2.39/0.99  fof(f15,plain,(
% 2.39/0.99    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 2.39/0.99    inference(ennf_transformation,[],[f4])).
% 2.39/0.99  
% 2.39/0.99  fof(f42,plain,(
% 2.39/0.99    ( ! [X0] : (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)) )),
% 2.39/0.99    inference(cnf_transformation,[],[f15])).
% 2.39/0.99  
% 2.39/0.99  fof(f59,plain,(
% 2.39/0.99    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 2.39/0.99    inference(equality_resolution,[],[f42])).
% 2.39/0.99  
% 2.39/0.99  fof(f43,plain,(
% 2.39/0.99    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 2.39/0.99    inference(cnf_transformation,[],[f15])).
% 2.39/0.99  
% 2.39/0.99  fof(f46,plain,(
% 2.39/0.99    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.39/0.99    inference(cnf_transformation,[],[f18])).
% 2.39/0.99  
% 2.39/0.99  fof(f60,plain,(
% 2.39/0.99    ( ! [X0] : (k8_setfam_1(X0,k1_xboole_0) = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.39/0.99    inference(equality_resolution,[],[f46])).
% 2.39/0.99  
% 2.39/0.99  fof(f3,axiom,(
% 2.39/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.39/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.39/0.99  
% 2.39/0.99  fof(f30,plain,(
% 2.39/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.39/0.99    inference(nnf_transformation,[],[f3])).
% 2.39/0.99  
% 2.39/0.99  fof(f31,plain,(
% 2.39/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.39/0.99    inference(flattening,[],[f30])).
% 2.39/0.99  
% 2.39/0.99  fof(f41,plain,(
% 2.39/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.39/0.99    inference(cnf_transformation,[],[f31])).
% 2.39/0.99  
% 2.39/0.99  fof(f5,axiom,(
% 2.39/0.99    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 2.39/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.39/0.99  
% 2.39/0.99  fof(f16,plain,(
% 2.39/0.99    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 2.39/0.99    inference(ennf_transformation,[],[f5])).
% 2.39/0.99  
% 2.39/0.99  fof(f17,plain,(
% 2.39/0.99    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 2.39/0.99    inference(flattening,[],[f16])).
% 2.39/0.99  
% 2.39/0.99  fof(f44,plain,(
% 2.39/0.99    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 2.39/0.99    inference(cnf_transformation,[],[f17])).
% 2.39/0.99  
% 2.39/0.99  fof(f39,plain,(
% 2.39/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.39/0.99    inference(cnf_transformation,[],[f31])).
% 2.39/0.99  
% 2.39/0.99  fof(f58,plain,(
% 2.39/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.39/0.99    inference(equality_resolution,[],[f39])).
% 2.39/0.99  
% 2.39/0.99  fof(f2,axiom,(
% 2.39/0.99    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.39/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.39/0.99  
% 2.39/0.99  fof(f14,plain,(
% 2.39/0.99    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.39/0.99    inference(ennf_transformation,[],[f2])).
% 2.39/0.99  
% 2.39/0.99  fof(f38,plain,(
% 2.39/0.99    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 2.39/0.99    inference(cnf_transformation,[],[f14])).
% 2.39/0.99  
% 2.39/0.99  fof(f1,axiom,(
% 2.39/0.99    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.39/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.39/0.99  
% 2.39/0.99  fof(f26,plain,(
% 2.39/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.39/0.99    inference(nnf_transformation,[],[f1])).
% 2.39/0.99  
% 2.39/0.99  fof(f27,plain,(
% 2.39/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.39/0.99    inference(rectify,[],[f26])).
% 2.39/0.99  
% 2.39/0.99  fof(f28,plain,(
% 2.39/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.39/0.99    introduced(choice_axiom,[])).
% 2.39/0.99  
% 2.39/0.99  fof(f29,plain,(
% 2.39/0.99    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.39/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).
% 2.39/0.99  
% 2.39/0.99  fof(f37,plain,(
% 2.39/0.99    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 2.39/0.99    inference(cnf_transformation,[],[f29])).
% 2.39/0.99  
% 2.39/0.99  fof(f10,axiom,(
% 2.39/0.99    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 2.39/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.39/0.99  
% 2.39/0.99  fof(f21,plain,(
% 2.39/0.99    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.39/0.99    inference(ennf_transformation,[],[f10])).
% 2.39/0.99  
% 2.39/0.99  fof(f51,plain,(
% 2.39/0.99    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.39/0.99    inference(cnf_transformation,[],[f21])).
% 2.39/0.99  
% 2.39/0.99  fof(f50,plain,(
% 2.39/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.39/0.99    inference(cnf_transformation,[],[f32])).
% 2.39/0.99  
% 2.39/0.99  fof(f40,plain,(
% 2.39/0.99    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.39/0.99    inference(cnf_transformation,[],[f31])).
% 2.39/0.99  
% 2.39/0.99  fof(f57,plain,(
% 2.39/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.39/0.99    inference(equality_resolution,[],[f40])).
% 2.39/0.99  
% 2.39/0.99  cnf(c_19,negated_conjecture,
% 2.39/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
% 2.39/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_821,plain,
% 2.39/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
% 2.39/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_11,plain,
% 2.39/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.39/0.99      | m1_subset_1(k8_setfam_1(X1,X0),k1_zfmisc_1(X1)) ),
% 2.39/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_828,plain,
% 2.39/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 2.39/0.99      | m1_subset_1(k8_setfam_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 2.39/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_14,plain,
% 2.39/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.39/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_825,plain,
% 2.39/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.39/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 2.39/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_1873,plain,
% 2.39/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 2.39/0.99      | r1_tarski(k8_setfam_1(X1,X0),X1) = iProver_top ),
% 2.39/0.99      inference(superposition,[status(thm)],[c_828,c_825]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_3465,plain,
% 2.39/0.99      ( r1_tarski(k8_setfam_1(sK1,sK3),sK1) = iProver_top ),
% 2.39/0.99      inference(superposition,[status(thm)],[c_821,c_1873]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_16,plain,
% 2.39/0.99      ( ~ r1_tarski(X0,X1)
% 2.39/0.99      | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
% 2.39/0.99      | k1_xboole_0 = X0 ),
% 2.39/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_824,plain,
% 2.39/0.99      ( k1_xboole_0 = X0
% 2.39/0.99      | r1_tarski(X0,X1) != iProver_top
% 2.39/0.99      | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) = iProver_top ),
% 2.39/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_10,plain,
% 2.39/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.39/0.99      | k6_setfam_1(X1,X0) = k8_setfam_1(X1,X0)
% 2.39/0.99      | k1_xboole_0 = X0 ),
% 2.39/0.99      inference(cnf_transformation,[],[f45]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_829,plain,
% 2.39/0.99      ( k6_setfam_1(X0,X1) = k8_setfam_1(X0,X1)
% 2.39/0.99      | k1_xboole_0 = X1
% 2.39/0.99      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 2.39/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_2051,plain,
% 2.39/0.99      ( k6_setfam_1(sK1,sK3) = k8_setfam_1(sK1,sK3) | sK3 = k1_xboole_0 ),
% 2.39/0.99      inference(superposition,[status(thm)],[c_821,c_829]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_12,plain,
% 2.39/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.39/0.99      | k6_setfam_1(X1,X0) = k1_setfam_1(X0) ),
% 2.39/0.99      inference(cnf_transformation,[],[f48]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_827,plain,
% 2.39/0.99      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
% 2.39/0.99      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 2.39/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_1310,plain,
% 2.39/0.99      ( k6_setfam_1(sK1,sK3) = k1_setfam_1(sK3) ),
% 2.39/0.99      inference(superposition,[status(thm)],[c_821,c_827]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_2060,plain,
% 2.39/0.99      ( k8_setfam_1(sK1,sK3) = k1_setfam_1(sK3) | sK3 = k1_xboole_0 ),
% 2.39/0.99      inference(light_normalisation,[status(thm)],[c_2051,c_1310]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_20,negated_conjecture,
% 2.39/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
% 2.39/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_820,plain,
% 2.39/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
% 2.39/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_2052,plain,
% 2.39/0.99      ( k6_setfam_1(sK1,sK2) = k8_setfam_1(sK1,sK2) | sK2 = k1_xboole_0 ),
% 2.39/0.99      inference(superposition,[status(thm)],[c_820,c_829]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_1311,plain,
% 2.39/0.99      ( k6_setfam_1(sK1,sK2) = k1_setfam_1(sK2) ),
% 2.39/0.99      inference(superposition,[status(thm)],[c_820,c_827]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_2055,plain,
% 2.39/0.99      ( k8_setfam_1(sK1,sK2) = k1_setfam_1(sK2) | sK2 = k1_xboole_0 ),
% 2.39/0.99      inference(light_normalisation,[status(thm)],[c_2052,c_1311]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_17,negated_conjecture,
% 2.39/0.99      ( ~ r1_tarski(k8_setfam_1(sK1,sK3),k8_setfam_1(sK1,sK2)) ),
% 2.39/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_823,plain,
% 2.39/0.99      ( r1_tarski(k8_setfam_1(sK1,sK3),k8_setfam_1(sK1,sK2)) != iProver_top ),
% 2.39/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_2264,plain,
% 2.39/0.99      ( sK2 = k1_xboole_0
% 2.39/0.99      | r1_tarski(k8_setfam_1(sK1,sK3),k1_setfam_1(sK2)) != iProver_top ),
% 2.39/0.99      inference(superposition,[status(thm)],[c_2055,c_823]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_2346,plain,
% 2.39/0.99      ( sK2 = k1_xboole_0
% 2.39/0.99      | sK3 = k1_xboole_0
% 2.39/0.99      | r1_tarski(k1_setfam_1(sK3),k1_setfam_1(sK2)) != iProver_top ),
% 2.39/0.99      inference(superposition,[status(thm)],[c_2060,c_2264]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_2434,plain,
% 2.39/0.99      ( sK2 = k1_xboole_0
% 2.39/0.99      | sK3 = k1_xboole_0
% 2.39/0.99      | r1_tarski(sK2,sK3) != iProver_top ),
% 2.39/0.99      inference(superposition,[status(thm)],[c_824,c_2346]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_18,negated_conjecture,
% 2.39/0.99      ( r1_tarski(sK2,sK3) ),
% 2.39/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_2435,plain,
% 2.39/0.99      ( ~ r1_tarski(sK2,sK3) | sK2 = k1_xboole_0 | sK3 = k1_xboole_0 ),
% 2.39/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_2434]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_2437,plain,
% 2.39/0.99      ( sK3 = k1_xboole_0 | sK2 = k1_xboole_0 ),
% 2.39/0.99      inference(global_propositional_subsumption,
% 2.39/0.99                [status(thm)],
% 2.39/0.99                [c_2434,c_18,c_2435]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_2438,plain,
% 2.39/0.99      ( sK2 = k1_xboole_0 | sK3 = k1_xboole_0 ),
% 2.39/0.99      inference(renaming,[status(thm)],[c_2437]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_2448,plain,
% 2.39/0.99      ( sK3 = k1_xboole_0
% 2.39/0.99      | r1_tarski(k8_setfam_1(sK1,sK3),k8_setfam_1(sK1,k1_xboole_0)) != iProver_top ),
% 2.39/0.99      inference(superposition,[status(thm)],[c_2438,c_823]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_2449,plain,
% 2.39/0.99      ( sK3 = k1_xboole_0
% 2.39/0.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
% 2.39/0.99      inference(superposition,[status(thm)],[c_2438,c_820]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_22,plain,
% 2.39/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
% 2.39/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_7,plain,
% 2.39/0.99      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 2.39/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_6,plain,
% 2.39/0.99      ( ~ r1_xboole_0(X0,X0) | k1_xboole_0 = X0 ),
% 2.39/0.99      inference(cnf_transformation,[],[f43]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_54,plain,
% 2.39/0.99      ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k1_xboole_0 ),
% 2.39/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_448,plain,
% 2.39/0.99      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.39/0.99      theory(equality) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_962,plain,
% 2.39/0.99      ( m1_subset_1(X0,X1)
% 2.39/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
% 2.39/0.99      | X0 != X2
% 2.39/0.99      | X1 != k1_zfmisc_1(X3) ),
% 2.39/0.99      inference(instantiation,[status(thm)],[c_448]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_1050,plain,
% 2.39/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.39/0.99      | m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.39/0.99      | X2 != X0
% 2.39/0.99      | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
% 2.39/0.99      inference(instantiation,[status(thm)],[c_962]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_1260,plain,
% 2.39/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.39/0.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.39/0.99      | k1_zfmisc_1(k1_zfmisc_1(X1)) != k1_zfmisc_1(k1_zfmisc_1(X1))
% 2.39/0.99      | k1_xboole_0 != X0 ),
% 2.39/0.99      inference(instantiation,[status(thm)],[c_1050]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_1924,plain,
% 2.39/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1)))
% 2.39/0.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK1)))
% 2.39/0.99      | k1_zfmisc_1(k1_zfmisc_1(sK1)) != k1_zfmisc_1(k1_zfmisc_1(sK1))
% 2.39/0.99      | k1_xboole_0 != sK3 ),
% 2.39/0.99      inference(instantiation,[status(thm)],[c_1260]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_1925,plain,
% 2.39/0.99      ( k1_zfmisc_1(k1_zfmisc_1(sK1)) != k1_zfmisc_1(k1_zfmisc_1(sK1))
% 2.39/0.99      | k1_xboole_0 != sK3
% 2.39/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
% 2.39/0.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
% 2.39/0.99      inference(predicate_to_equality,[status(thm)],[c_1924]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_443,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_2105,plain,
% 2.39/0.99      ( sK3 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK3 ),
% 2.39/0.99      inference(instantiation,[status(thm)],[c_443]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_2106,plain,
% 2.39/0.99      ( sK3 != k1_xboole_0 | k1_xboole_0 = sK3 | k1_xboole_0 != k1_xboole_0 ),
% 2.39/0.99      inference(instantiation,[status(thm)],[c_2105]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_442,plain,( X0 = X0 ),theory(equality) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_1051,plain,
% 2.39/0.99      ( k1_zfmisc_1(X0) = k1_zfmisc_1(X0) ),
% 2.39/0.99      inference(instantiation,[status(thm)],[c_442]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_2217,plain,
% 2.39/0.99      ( k1_zfmisc_1(k1_zfmisc_1(sK1)) = k1_zfmisc_1(k1_zfmisc_1(sK1)) ),
% 2.39/0.99      inference(instantiation,[status(thm)],[c_1051]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_2689,plain,
% 2.39/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
% 2.39/0.99      inference(global_propositional_subsumption,
% 2.39/0.99                [status(thm)],
% 2.39/0.99                [c_2449,c_22,c_7,c_54,c_1925,c_2106,c_2217]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_9,plain,
% 2.39/0.99      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
% 2.39/0.99      | k8_setfam_1(X0,k1_xboole_0) = X0 ),
% 2.39/0.99      inference(cnf_transformation,[],[f60]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_830,plain,
% 2.39/0.99      ( k8_setfam_1(X0,k1_xboole_0) = X0
% 2.39/0.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 2.39/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_2694,plain,
% 2.39/0.99      ( k8_setfam_1(sK1,k1_xboole_0) = sK1 ),
% 2.39/0.99      inference(superposition,[status(thm)],[c_2689,c_830]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_2751,plain,
% 2.39/0.99      ( sK3 = k1_xboole_0
% 2.39/0.99      | r1_tarski(k8_setfam_1(sK1,sK3),sK1) != iProver_top ),
% 2.39/0.99      inference(light_normalisation,[status(thm)],[c_2448,c_2694]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_3495,plain,
% 2.39/0.99      ( sK3 = k1_xboole_0 ),
% 2.39/0.99      inference(superposition,[status(thm)],[c_3465,c_2751]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_822,plain,
% 2.39/0.99      ( r1_tarski(sK2,sK3) = iProver_top ),
% 2.39/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_3,plain,
% 2.39/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 2.39/0.99      inference(cnf_transformation,[],[f41]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_832,plain,
% 2.39/0.99      ( X0 = X1
% 2.39/0.99      | r1_tarski(X0,X1) != iProver_top
% 2.39/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 2.39/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_1895,plain,
% 2.39/0.99      ( sK2 = sK3 | r1_tarski(sK3,sK2) != iProver_top ),
% 2.39/0.99      inference(superposition,[status(thm)],[c_822,c_832]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_3766,plain,
% 2.39/0.99      ( sK2 = k1_xboole_0 | r1_tarski(k1_xboole_0,sK2) != iProver_top ),
% 2.39/0.99      inference(demodulation,[status(thm)],[c_3495,c_1895]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_8,plain,
% 2.39/0.99      ( ~ r1_xboole_0(X0,X1) | ~ r1_tarski(X0,X1) | v1_xboole_0(X0) ),
% 2.39/0.99      inference(cnf_transformation,[],[f44]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_49,plain,
% 2.39/0.99      ( r1_xboole_0(X0,X1) != iProver_top
% 2.39/0.99      | r1_tarski(X0,X1) != iProver_top
% 2.39/0.99      | v1_xboole_0(X0) = iProver_top ),
% 2.39/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_51,plain,
% 2.39/0.99      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top
% 2.39/0.99      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 2.39/0.99      | v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.39/0.99      inference(instantiation,[status(thm)],[c_49]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_52,plain,
% 2.39/0.99      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 2.39/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_5,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f58]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_56,plain,
% 2.39/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 2.39/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_58,plain,
% 2.39/0.99      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 2.39/0.99      inference(instantiation,[status(thm)],[c_56]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_1109,plain,
% 2.39/0.99      ( sK2 = sK2 ),
% 2.39/0.99      inference(instantiation,[status(thm)],[c_442]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_1102,plain,
% 2.39/0.99      ( X0 != X1 | sK2 != X1 | sK2 = X0 ),
% 2.39/0.99      inference(instantiation,[status(thm)],[c_443]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_1545,plain,
% 2.39/0.99      ( X0 != sK2 | sK2 = X0 | sK2 != sK2 ),
% 2.39/0.99      inference(instantiation,[status(thm)],[c_1102]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_1546,plain,
% 2.39/0.99      ( sK2 != sK2 | sK2 = k1_xboole_0 | k1_xboole_0 != sK2 ),
% 2.39/0.99      inference(instantiation,[status(thm)],[c_1545]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_2,plain,
% 2.39/0.99      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 2.39/0.99      inference(cnf_transformation,[],[f38]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_1749,plain,
% 2.39/0.99      ( ~ v1_xboole_0(sK2) | k1_xboole_0 = sK2 ),
% 2.39/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_1760,plain,
% 2.39/0.99      ( k1_xboole_0 = sK2 | v1_xboole_0(sK2) != iProver_top ),
% 2.39/0.99      inference(predicate_to_equality,[status(thm)],[c_1749]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_0,plain,
% 2.39/0.99      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 2.39/0.99      inference(cnf_transformation,[],[f37]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_15,plain,
% 2.39/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.39/0.99      | ~ r2_hidden(X2,X0)
% 2.39/0.99      | ~ v1_xboole_0(X1) ),
% 2.39/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_13,plain,
% 2.39/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.39/0.99      inference(cnf_transformation,[],[f50]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_166,plain,
% 2.39/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.39/0.99      inference(prop_impl,[status(thm)],[c_13]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_167,plain,
% 2.39/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.39/0.99      inference(renaming,[status(thm)],[c_166]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_198,plain,
% 2.39/0.99      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | ~ v1_xboole_0(X1) ),
% 2.39/0.99      inference(bin_hyper_res,[status(thm)],[c_15,c_167]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_285,plain,
% 2.39/0.99      ( ~ r1_tarski(X0,X1)
% 2.39/0.99      | ~ v1_xboole_0(X1)
% 2.39/0.99      | v1_xboole_0(X2)
% 2.39/0.99      | X0 != X2
% 2.39/0.99      | sK0(X2) != X3 ),
% 2.39/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_198]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_286,plain,
% 2.39/0.99      ( ~ r1_tarski(X0,X1) | ~ v1_xboole_0(X1) | v1_xboole_0(X0) ),
% 2.39/0.99      inference(unflattening,[status(thm)],[c_285]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_818,plain,
% 2.39/0.99      ( r1_tarski(X0,X1) != iProver_top
% 2.39/0.99      | v1_xboole_0(X1) != iProver_top
% 2.39/0.99      | v1_xboole_0(X0) = iProver_top ),
% 2.39/0.99      inference(predicate_to_equality,[status(thm)],[c_286]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_1140,plain,
% 2.39/0.99      ( v1_xboole_0(sK2) = iProver_top | v1_xboole_0(sK3) != iProver_top ),
% 2.39/0.99      inference(superposition,[status(thm)],[c_822,c_818]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_3768,plain,
% 2.39/0.99      ( v1_xboole_0(sK2) = iProver_top
% 2.39/0.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.39/0.99      inference(demodulation,[status(thm)],[c_3495,c_1140]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_4046,plain,
% 2.39/0.99      ( sK2 = k1_xboole_0 ),
% 2.39/0.99      inference(global_propositional_subsumption,
% 2.39/0.99                [status(thm)],
% 2.39/0.99                [c_3766,c_51,c_52,c_58,c_1109,c_1546,c_1760,c_3768]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_3771,plain,
% 2.39/0.99      ( r1_tarski(k8_setfam_1(sK1,k1_xboole_0),k8_setfam_1(sK1,sK2)) != iProver_top ),
% 2.39/0.99      inference(demodulation,[status(thm)],[c_3495,c_823]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_3777,plain,
% 2.39/0.99      ( r1_tarski(sK1,k8_setfam_1(sK1,sK2)) != iProver_top ),
% 2.39/0.99      inference(light_normalisation,[status(thm)],[c_3771,c_2694]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_4049,plain,
% 2.39/0.99      ( r1_tarski(sK1,k8_setfam_1(sK1,k1_xboole_0)) != iProver_top ),
% 2.39/0.99      inference(demodulation,[status(thm)],[c_4046,c_3777]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_4061,plain,
% 2.39/0.99      ( r1_tarski(sK1,sK1) != iProver_top ),
% 2.39/0.99      inference(light_normalisation,[status(thm)],[c_4049,c_2694]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_4,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f57]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_831,plain,
% 2.39/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 2.39/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_4375,plain,
% 2.39/0.99      ( $false ),
% 2.39/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_4061,c_831]) ).
% 2.39/0.99  
% 2.39/0.99  
% 2.39/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.39/0.99  
% 2.39/0.99  ------                               Statistics
% 2.39/0.99  
% 2.39/0.99  ------ General
% 2.39/0.99  
% 2.39/0.99  abstr_ref_over_cycles:                  0
% 2.39/0.99  abstr_ref_under_cycles:                 0
% 2.39/0.99  gc_basic_clause_elim:                   0
% 2.39/0.99  forced_gc_time:                         0
% 2.39/0.99  parsing_time:                           0.011
% 2.39/0.99  unif_index_cands_time:                  0.
% 2.39/0.99  unif_index_add_time:                    0.
% 2.39/0.99  orderings_time:                         0.
% 2.39/0.99  out_proof_time:                         0.009
% 2.39/0.99  total_time:                             0.152
% 2.39/0.99  num_of_symbols:                         45
% 2.39/0.99  num_of_terms:                           2664
% 2.39/0.99  
% 2.39/0.99  ------ Preprocessing
% 2.39/0.99  
% 2.39/0.99  num_of_splits:                          0
% 2.39/0.99  num_of_split_atoms:                     0
% 2.39/0.99  num_of_reused_defs:                     0
% 2.39/0.99  num_eq_ax_congr_red:                    12
% 2.39/0.99  num_of_sem_filtered_clauses:            1
% 2.39/0.99  num_of_subtypes:                        0
% 2.39/0.99  monotx_restored_types:                  0
% 2.39/0.99  sat_num_of_epr_types:                   0
% 2.39/0.99  sat_num_of_non_cyclic_types:            0
% 2.39/0.99  sat_guarded_non_collapsed_types:        0
% 2.39/0.99  num_pure_diseq_elim:                    0
% 2.39/0.99  simp_replaced_by:                       0
% 2.39/0.99  res_preprocessed:                       83
% 2.39/0.99  prep_upred:                             0
% 2.39/0.99  prep_unflattend:                        7
% 2.39/0.99  smt_new_axioms:                         0
% 2.39/0.99  pred_elim_cands:                        3
% 2.39/0.99  pred_elim:                              2
% 2.39/0.99  pred_elim_cl:                           4
% 2.39/0.99  pred_elim_cycles:                       4
% 2.39/0.99  merged_defs:                            8
% 2.39/0.99  merged_defs_ncl:                        0
% 2.39/0.99  bin_hyper_res:                          9
% 2.39/0.99  prep_cycles:                            4
% 2.39/0.99  pred_elim_time:                         0.001
% 2.39/0.99  splitting_time:                         0.
% 2.39/0.99  sem_filter_time:                        0.
% 2.39/0.99  monotx_time:                            0.
% 2.39/0.99  subtype_inf_time:                       0.
% 2.39/0.99  
% 2.39/0.99  ------ Problem properties
% 2.39/0.99  
% 2.39/0.99  clauses:                                16
% 2.39/0.99  conjectures:                            4
% 2.39/0.99  epr:                                    6
% 2.39/0.99  horn:                                   14
% 2.39/0.99  ground:                                 5
% 2.39/0.99  unary:                                  6
% 2.39/0.99  binary:                                 6
% 2.39/0.99  lits:                                   30
% 2.39/0.99  lits_eq:                                7
% 2.39/0.99  fd_pure:                                0
% 2.39/0.99  fd_pseudo:                              0
% 2.39/0.99  fd_cond:                                3
% 2.39/0.99  fd_pseudo_cond:                         1
% 2.39/0.99  ac_symbols:                             0
% 2.39/0.99  
% 2.39/0.99  ------ Propositional Solver
% 2.39/0.99  
% 2.39/0.99  prop_solver_calls:                      30
% 2.39/0.99  prop_fast_solver_calls:                 483
% 2.39/0.99  smt_solver_calls:                       0
% 2.39/0.99  smt_fast_solver_calls:                  0
% 2.39/0.99  prop_num_of_clauses:                    1408
% 2.39/0.99  prop_preprocess_simplified:             3974
% 2.39/0.99  prop_fo_subsumed:                       11
% 2.39/0.99  prop_solver_time:                       0.
% 2.39/0.99  smt_solver_time:                        0.
% 2.39/0.99  smt_fast_solver_time:                   0.
% 2.39/0.99  prop_fast_solver_time:                  0.
% 2.39/0.99  prop_unsat_core_time:                   0.
% 2.39/0.99  
% 2.39/0.99  ------ QBF
% 2.39/0.99  
% 2.39/0.99  qbf_q_res:                              0
% 2.39/0.99  qbf_num_tautologies:                    0
% 2.39/0.99  qbf_prep_cycles:                        0
% 2.39/0.99  
% 2.39/0.99  ------ BMC1
% 2.39/0.99  
% 2.39/0.99  bmc1_current_bound:                     -1
% 2.39/0.99  bmc1_last_solved_bound:                 -1
% 2.39/0.99  bmc1_unsat_core_size:                   -1
% 2.39/0.99  bmc1_unsat_core_parents_size:           -1
% 2.39/0.99  bmc1_merge_next_fun:                    0
% 2.39/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.39/0.99  
% 2.39/0.99  ------ Instantiation
% 2.39/0.99  
% 2.39/0.99  inst_num_of_clauses:                    460
% 2.39/0.99  inst_num_in_passive:                    220
% 2.39/0.99  inst_num_in_active:                     226
% 2.39/0.99  inst_num_in_unprocessed:                14
% 2.39/0.99  inst_num_of_loops:                      290
% 2.39/0.99  inst_num_of_learning_restarts:          0
% 2.39/0.99  inst_num_moves_active_passive:          60
% 2.39/0.99  inst_lit_activity:                      0
% 2.39/0.99  inst_lit_activity_moves:                0
% 2.39/0.99  inst_num_tautologies:                   0
% 2.39/0.99  inst_num_prop_implied:                  0
% 2.39/0.99  inst_num_existing_simplified:           0
% 2.39/0.99  inst_num_eq_res_simplified:             0
% 2.39/0.99  inst_num_child_elim:                    0
% 2.39/0.99  inst_num_of_dismatching_blockings:      270
% 2.39/0.99  inst_num_of_non_proper_insts:           665
% 2.39/0.99  inst_num_of_duplicates:                 0
% 2.39/0.99  inst_inst_num_from_inst_to_res:         0
% 2.39/0.99  inst_dismatching_checking_time:         0.
% 2.39/0.99  
% 2.39/0.99  ------ Resolution
% 2.39/0.99  
% 2.39/0.99  res_num_of_clauses:                     0
% 2.39/0.99  res_num_in_passive:                     0
% 2.39/0.99  res_num_in_active:                      0
% 2.39/0.99  res_num_of_loops:                       87
% 2.39/0.99  res_forward_subset_subsumed:            80
% 2.39/0.99  res_backward_subset_subsumed:           0
% 2.39/0.99  res_forward_subsumed:                   0
% 2.39/0.99  res_backward_subsumed:                  0
% 2.39/0.99  res_forward_subsumption_resolution:     0
% 2.39/0.99  res_backward_subsumption_resolution:    0
% 2.39/0.99  res_clause_to_clause_subsumption:       212
% 2.39/0.99  res_orphan_elimination:                 0
% 2.39/0.99  res_tautology_del:                      67
% 2.39/0.99  res_num_eq_res_simplified:              0
% 2.39/0.99  res_num_sel_changes:                    0
% 2.39/0.99  res_moves_from_active_to_pass:          0
% 2.39/0.99  
% 2.39/0.99  ------ Superposition
% 2.39/0.99  
% 2.39/0.99  sup_time_total:                         0.
% 2.39/0.99  sup_time_generating:                    0.
% 2.39/0.99  sup_time_sim_full:                      0.
% 2.39/0.99  sup_time_sim_immed:                     0.
% 2.39/0.99  
% 2.39/0.99  sup_num_of_clauses:                     44
% 2.39/0.99  sup_num_in_active:                      28
% 2.39/0.99  sup_num_in_passive:                     16
% 2.39/0.99  sup_num_of_loops:                       57
% 2.39/0.99  sup_fw_superposition:                   43
% 2.39/0.99  sup_bw_superposition:                   46
% 2.39/0.99  sup_immediate_simplified:               19
% 2.39/0.99  sup_given_eliminated:                   1
% 2.39/0.99  comparisons_done:                       0
% 2.39/0.99  comparisons_avoided:                    13
% 2.39/0.99  
% 2.39/0.99  ------ Simplifications
% 2.39/0.99  
% 2.39/0.99  
% 2.39/0.99  sim_fw_subset_subsumed:                 9
% 2.39/0.99  sim_bw_subset_subsumed:                 13
% 2.39/0.99  sim_fw_subsumed:                        3
% 2.39/0.99  sim_bw_subsumed:                        0
% 2.39/0.99  sim_fw_subsumption_res:                 1
% 2.39/0.99  sim_bw_subsumption_res:                 0
% 2.39/0.99  sim_tautology_del:                      3
% 2.39/0.99  sim_eq_tautology_del:                   9
% 2.39/0.99  sim_eq_res_simp:                        0
% 2.39/0.99  sim_fw_demodulated:                     0
% 2.39/0.99  sim_bw_demodulated:                     22
% 2.39/0.99  sim_light_normalised:                   12
% 2.39/0.99  sim_joinable_taut:                      0
% 2.39/0.99  sim_joinable_simp:                      0
% 2.39/0.99  sim_ac_normalised:                      0
% 2.39/0.99  sim_smt_subsumption:                    0
% 2.39/0.99  
%------------------------------------------------------------------------------
