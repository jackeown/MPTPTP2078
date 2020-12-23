%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:42:27 EST 2020

% Result     : Theorem 2.41s
% Output     : CNFRefutation 2.41s
% Verified   : 
% Statistics : Number of formulae       :  140 (1914 expanded)
%              Number of clauses        :   89 ( 698 expanded)
%              Number of leaves         :   16 ( 447 expanded)
%              Depth                    :   25
%              Number of atoms          :  331 (6197 expanded)
%              Number of equality atoms :  168 (1625 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( r1_tarski(X1,X2)
           => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( r1_tarski(X1,X2)
             => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f24,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f23])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
     => ( ~ r1_tarski(k8_setfam_1(X0,sK2),k8_setfam_1(X0,X1))
        & r1_tarski(X1,sK2)
        & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
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

fof(f30,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f29,f28])).

fof(f47,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f30])).

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

fof(f27,plain,(
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
    inference(cnf_transformation,[],[f27])).

fof(f10,axiom,(
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
    inference(ennf_transformation,[],[f10])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

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

fof(f46,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f30])).

fof(f49,plain,(
    ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f30])).

fof(f48,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f3,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f35,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | r1_xboole_0(X0,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f52,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f35])).

fof(f36,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f53,plain,(
    ! [X0] :
      ( k8_setfam_1(X0,k1_xboole_0) = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f40])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f25])).

fof(f34,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f15])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f51,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f32])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f31,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_772,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | m1_subset_1(k8_setfam_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_779,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | m1_subset_1(k8_setfam_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_776,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1827,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | r1_tarski(k8_setfam_1(X1,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_779,c_776])).

cnf(c_3431,plain,
    ( r1_tarski(k8_setfam_1(sK0,sK2),sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_772,c_1827])).

cnf(c_14,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_775,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k6_setfam_1(X1,X0) = k8_setfam_1(X1,X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_780,plain,
    ( k6_setfam_1(X0,X1) = k8_setfam_1(X0,X1)
    | k1_xboole_0 = X1
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2005,plain,
    ( k6_setfam_1(sK0,sK2) = k8_setfam_1(sK0,sK2)
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_772,c_780])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k6_setfam_1(X1,X0) = k1_setfam_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_778,plain,
    ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1261,plain,
    ( k6_setfam_1(sK0,sK2) = k1_setfam_1(sK2) ),
    inference(superposition,[status(thm)],[c_772,c_778])).

cnf(c_2014,plain,
    ( k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | sK2 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2005,c_1261])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_771,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2006,plain,
    ( k6_setfam_1(sK0,sK1) = k8_setfam_1(sK0,sK1)
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_771,c_780])).

cnf(c_1262,plain,
    ( k6_setfam_1(sK0,sK1) = k1_setfam_1(sK1) ),
    inference(superposition,[status(thm)],[c_771,c_778])).

cnf(c_2009,plain,
    ( k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1)
    | sK1 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2006,c_1262])).

cnf(c_15,negated_conjecture,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_774,plain,
    ( r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2216,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k8_setfam_1(sK0,sK2),k1_setfam_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2009,c_774])).

cnf(c_2298,plain,
    ( sK1 = k1_xboole_0
    | sK2 = k1_xboole_0
    | r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2014,c_2216])).

cnf(c_2386,plain,
    ( sK1 = k1_xboole_0
    | sK2 = k1_xboole_0
    | r1_tarski(sK1,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_775,c_2298])).

cnf(c_16,negated_conjecture,
    ( r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2387,plain,
    ( ~ r1_tarski(sK1,sK2)
    | sK1 = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2386])).

cnf(c_2389,plain,
    ( sK2 = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2386,c_16,c_2387])).

cnf(c_2390,plain,
    ( sK1 = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_2389])).

cnf(c_2400,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2390,c_774])).

cnf(c_2401,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2390,c_771])).

cnf(c_20,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_5,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_4,plain,
    ( ~ r1_xboole_0(X0,X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_50,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_398,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_913,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | X0 != X2
    | X1 != k1_zfmisc_1(X3) ),
    inference(instantiation,[status(thm)],[c_398])).

cnf(c_999,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(X2,k1_zfmisc_1(X1))
    | X2 != X0
    | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_913])).

cnf(c_1210,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k1_zfmisc_1(k1_zfmisc_1(X1)) != k1_zfmisc_1(k1_zfmisc_1(X1))
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_999])).

cnf(c_1877,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | k1_zfmisc_1(k1_zfmisc_1(sK0)) != k1_zfmisc_1(k1_zfmisc_1(sK0))
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_1210])).

cnf(c_1878,plain,
    ( k1_zfmisc_1(k1_zfmisc_1(sK0)) != k1_zfmisc_1(k1_zfmisc_1(sK0))
    | k1_xboole_0 != sK2
    | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1877])).

cnf(c_394,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2062,plain,
    ( sK2 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_394])).

cnf(c_2063,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2062])).

cnf(c_393,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1000,plain,
    ( k1_zfmisc_1(X0) = k1_zfmisc_1(X0) ),
    inference(instantiation,[status(thm)],[c_393])).

cnf(c_2171,plain,
    ( k1_zfmisc_1(k1_zfmisc_1(sK0)) = k1_zfmisc_1(k1_zfmisc_1(sK0)) ),
    inference(instantiation,[status(thm)],[c_1000])).

cnf(c_2641,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2401,c_20,c_5,c_50,c_1878,c_2063,c_2171])).

cnf(c_8,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
    | k8_setfam_1(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_781,plain,
    ( k8_setfam_1(X0,k1_xboole_0) = X0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2647,plain,
    ( k8_setfam_1(sK0,k1_xboole_0) = sK0 ),
    inference(superposition,[status(thm)],[c_2641,c_781])).

cnf(c_2703,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(k8_setfam_1(sK0,sK2),sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2400,c_2647])).

cnf(c_3461,plain,
    ( sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3431,c_2703])).

cnf(c_773,plain,
    ( r1_tarski(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_783,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1849,plain,
    ( sK1 = sK2
    | r1_tarski(sK2,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_773,c_783])).

cnf(c_3730,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k1_xboole_0,sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3461,c_1849])).

cnf(c_6,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_45,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_47,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_45])).

cnf(c_48,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_52,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_54,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_52])).

cnf(c_1059,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_393])).

cnf(c_1061,plain,
    ( X0 != X1
    | sK1 != X1
    | sK1 = X0 ),
    inference(instantiation,[status(thm)],[c_394])).

cnf(c_1499,plain,
    ( X0 != sK1
    | sK1 = X0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1061])).

cnf(c_1500,plain,
    ( sK1 != sK1
    | sK1 = k1_xboole_0
    | k1_xboole_0 != sK1 ),
    inference(instantiation,[status(thm)],[c_1499])).

cnf(c_0,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_1703,plain,
    ( ~ v1_xboole_0(sK1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1714,plain,
    ( k1_xboole_0 = sK1
    | v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1703])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_12,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_146,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_12])).

cnf(c_147,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_146])).

cnf(c_173,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_7,c_147])).

cnf(c_770,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_173])).

cnf(c_1091,plain,
    ( v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_773,c_770])).

cnf(c_3732,plain,
    ( v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3461,c_1091])).

cnf(c_3984,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3730,c_47,c_48,c_54,c_1059,c_1500,c_1714,c_3732])).

cnf(c_3735,plain,
    ( r1_tarski(k8_setfam_1(sK0,k1_xboole_0),k8_setfam_1(sK0,sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3461,c_774])).

cnf(c_3741,plain,
    ( r1_tarski(sK0,k8_setfam_1(sK0,sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3735,c_2647])).

cnf(c_3987,plain,
    ( r1_tarski(sK0,k8_setfam_1(sK0,k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3984,c_3741])).

cnf(c_3999,plain,
    ( r1_tarski(sK0,sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3987,c_2647])).

cnf(c_782,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_4321,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3999,c_782])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : iproveropt_run.sh %d %s
% 0.11/0.32  % Computer   : n020.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 10:18:52 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  % Running in FOF mode
% 2.41/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.41/0.97  
% 2.41/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.41/0.97  
% 2.41/0.97  ------  iProver source info
% 2.41/0.97  
% 2.41/0.97  git: date: 2020-06-30 10:37:57 +0100
% 2.41/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.41/0.97  git: non_committed_changes: false
% 2.41/0.97  git: last_make_outside_of_git: false
% 2.41/0.97  
% 2.41/0.97  ------ 
% 2.41/0.97  
% 2.41/0.97  ------ Input Options
% 2.41/0.97  
% 2.41/0.97  --out_options                           all
% 2.41/0.97  --tptp_safe_out                         true
% 2.41/0.97  --problem_path                          ""
% 2.41/0.97  --include_path                          ""
% 2.41/0.97  --clausifier                            res/vclausify_rel
% 2.41/0.97  --clausifier_options                    --mode clausify
% 2.41/0.97  --stdin                                 false
% 2.41/0.97  --stats_out                             all
% 2.41/0.97  
% 2.41/0.97  ------ General Options
% 2.41/0.97  
% 2.41/0.97  --fof                                   false
% 2.41/0.97  --time_out_real                         305.
% 2.41/0.97  --time_out_virtual                      -1.
% 2.41/0.97  --symbol_type_check                     false
% 2.41/0.97  --clausify_out                          false
% 2.41/0.97  --sig_cnt_out                           false
% 2.41/0.97  --trig_cnt_out                          false
% 2.41/0.97  --trig_cnt_out_tolerance                1.
% 2.41/0.97  --trig_cnt_out_sk_spl                   false
% 2.41/0.97  --abstr_cl_out                          false
% 2.41/0.97  
% 2.41/0.97  ------ Global Options
% 2.41/0.97  
% 2.41/0.97  --schedule                              default
% 2.41/0.97  --add_important_lit                     false
% 2.41/0.97  --prop_solver_per_cl                    1000
% 2.41/0.97  --min_unsat_core                        false
% 2.41/0.97  --soft_assumptions                      false
% 2.41/0.97  --soft_lemma_size                       3
% 2.41/0.97  --prop_impl_unit_size                   0
% 2.41/0.97  --prop_impl_unit                        []
% 2.41/0.97  --share_sel_clauses                     true
% 2.41/0.97  --reset_solvers                         false
% 2.41/0.97  --bc_imp_inh                            [conj_cone]
% 2.41/0.97  --conj_cone_tolerance                   3.
% 2.41/0.97  --extra_neg_conj                        none
% 2.41/0.97  --large_theory_mode                     true
% 2.41/0.97  --prolific_symb_bound                   200
% 2.41/0.97  --lt_threshold                          2000
% 2.41/0.97  --clause_weak_htbl                      true
% 2.41/0.97  --gc_record_bc_elim                     false
% 2.41/0.97  
% 2.41/0.97  ------ Preprocessing Options
% 2.41/0.97  
% 2.41/0.97  --preprocessing_flag                    true
% 2.41/0.97  --time_out_prep_mult                    0.1
% 2.41/0.97  --splitting_mode                        input
% 2.41/0.97  --splitting_grd                         true
% 2.41/0.97  --splitting_cvd                         false
% 2.41/0.97  --splitting_cvd_svl                     false
% 2.41/0.97  --splitting_nvd                         32
% 2.41/0.97  --sub_typing                            true
% 2.41/0.97  --prep_gs_sim                           true
% 2.41/0.97  --prep_unflatten                        true
% 2.41/0.97  --prep_res_sim                          true
% 2.41/0.97  --prep_upred                            true
% 2.41/0.97  --prep_sem_filter                       exhaustive
% 2.41/0.97  --prep_sem_filter_out                   false
% 2.41/0.97  --pred_elim                             true
% 2.41/0.97  --res_sim_input                         true
% 2.41/0.97  --eq_ax_congr_red                       true
% 2.41/0.97  --pure_diseq_elim                       true
% 2.41/0.97  --brand_transform                       false
% 2.41/0.97  --non_eq_to_eq                          false
% 2.41/0.97  --prep_def_merge                        true
% 2.41/0.97  --prep_def_merge_prop_impl              false
% 2.41/0.97  --prep_def_merge_mbd                    true
% 2.41/0.97  --prep_def_merge_tr_red                 false
% 2.41/0.97  --prep_def_merge_tr_cl                  false
% 2.41/0.97  --smt_preprocessing                     true
% 2.41/0.97  --smt_ac_axioms                         fast
% 2.41/0.97  --preprocessed_out                      false
% 2.41/0.97  --preprocessed_stats                    false
% 2.41/0.97  
% 2.41/0.97  ------ Abstraction refinement Options
% 2.41/0.97  
% 2.41/0.97  --abstr_ref                             []
% 2.41/0.97  --abstr_ref_prep                        false
% 2.41/0.97  --abstr_ref_until_sat                   false
% 2.41/0.97  --abstr_ref_sig_restrict                funpre
% 2.41/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.41/0.97  --abstr_ref_under                       []
% 2.41/0.97  
% 2.41/0.97  ------ SAT Options
% 2.41/0.97  
% 2.41/0.97  --sat_mode                              false
% 2.41/0.97  --sat_fm_restart_options                ""
% 2.41/0.97  --sat_gr_def                            false
% 2.41/0.97  --sat_epr_types                         true
% 2.41/0.97  --sat_non_cyclic_types                  false
% 2.41/0.97  --sat_finite_models                     false
% 2.41/0.97  --sat_fm_lemmas                         false
% 2.41/0.97  --sat_fm_prep                           false
% 2.41/0.97  --sat_fm_uc_incr                        true
% 2.41/0.97  --sat_out_model                         small
% 2.41/0.97  --sat_out_clauses                       false
% 2.41/0.97  
% 2.41/0.97  ------ QBF Options
% 2.41/0.97  
% 2.41/0.97  --qbf_mode                              false
% 2.41/0.97  --qbf_elim_univ                         false
% 2.41/0.97  --qbf_dom_inst                          none
% 2.41/0.97  --qbf_dom_pre_inst                      false
% 2.41/0.97  --qbf_sk_in                             false
% 2.41/0.97  --qbf_pred_elim                         true
% 2.41/0.97  --qbf_split                             512
% 2.41/0.97  
% 2.41/0.97  ------ BMC1 Options
% 2.41/0.97  
% 2.41/0.97  --bmc1_incremental                      false
% 2.41/0.97  --bmc1_axioms                           reachable_all
% 2.41/0.97  --bmc1_min_bound                        0
% 2.41/0.97  --bmc1_max_bound                        -1
% 2.41/0.97  --bmc1_max_bound_default                -1
% 2.41/0.97  --bmc1_symbol_reachability              true
% 2.41/0.97  --bmc1_property_lemmas                  false
% 2.41/0.97  --bmc1_k_induction                      false
% 2.41/0.97  --bmc1_non_equiv_states                 false
% 2.41/0.97  --bmc1_deadlock                         false
% 2.41/0.97  --bmc1_ucm                              false
% 2.41/0.97  --bmc1_add_unsat_core                   none
% 2.41/0.97  --bmc1_unsat_core_children              false
% 2.41/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.41/0.97  --bmc1_out_stat                         full
% 2.41/0.97  --bmc1_ground_init                      false
% 2.41/0.97  --bmc1_pre_inst_next_state              false
% 2.41/0.97  --bmc1_pre_inst_state                   false
% 2.41/0.97  --bmc1_pre_inst_reach_state             false
% 2.41/0.97  --bmc1_out_unsat_core                   false
% 2.41/0.97  --bmc1_aig_witness_out                  false
% 2.41/0.97  --bmc1_verbose                          false
% 2.41/0.97  --bmc1_dump_clauses_tptp                false
% 2.41/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.41/0.97  --bmc1_dump_file                        -
% 2.41/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.41/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.41/0.97  --bmc1_ucm_extend_mode                  1
% 2.41/0.97  --bmc1_ucm_init_mode                    2
% 2.41/0.97  --bmc1_ucm_cone_mode                    none
% 2.41/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.41/0.97  --bmc1_ucm_relax_model                  4
% 2.41/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.41/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.41/0.97  --bmc1_ucm_layered_model                none
% 2.41/0.97  --bmc1_ucm_max_lemma_size               10
% 2.41/0.97  
% 2.41/0.97  ------ AIG Options
% 2.41/0.97  
% 2.41/0.97  --aig_mode                              false
% 2.41/0.97  
% 2.41/0.97  ------ Instantiation Options
% 2.41/0.97  
% 2.41/0.97  --instantiation_flag                    true
% 2.41/0.97  --inst_sos_flag                         false
% 2.41/0.97  --inst_sos_phase                        true
% 2.41/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.41/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.41/0.97  --inst_lit_sel_side                     num_symb
% 2.41/0.97  --inst_solver_per_active                1400
% 2.41/0.97  --inst_solver_calls_frac                1.
% 2.41/0.97  --inst_passive_queue_type               priority_queues
% 2.41/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.41/0.97  --inst_passive_queues_freq              [25;2]
% 2.41/0.97  --inst_dismatching                      true
% 2.41/0.97  --inst_eager_unprocessed_to_passive     true
% 2.41/0.97  --inst_prop_sim_given                   true
% 2.41/0.97  --inst_prop_sim_new                     false
% 2.41/0.97  --inst_subs_new                         false
% 2.41/0.97  --inst_eq_res_simp                      false
% 2.41/0.97  --inst_subs_given                       false
% 2.41/0.97  --inst_orphan_elimination               true
% 2.41/0.97  --inst_learning_loop_flag               true
% 2.41/0.97  --inst_learning_start                   3000
% 2.41/0.97  --inst_learning_factor                  2
% 2.41/0.97  --inst_start_prop_sim_after_learn       3
% 2.41/0.97  --inst_sel_renew                        solver
% 2.41/0.97  --inst_lit_activity_flag                true
% 2.41/0.97  --inst_restr_to_given                   false
% 2.41/0.97  --inst_activity_threshold               500
% 2.41/0.97  --inst_out_proof                        true
% 2.41/0.97  
% 2.41/0.97  ------ Resolution Options
% 2.41/0.97  
% 2.41/0.97  --resolution_flag                       true
% 2.41/0.97  --res_lit_sel                           adaptive
% 2.41/0.97  --res_lit_sel_side                      none
% 2.41/0.97  --res_ordering                          kbo
% 2.41/0.97  --res_to_prop_solver                    active
% 2.41/0.97  --res_prop_simpl_new                    false
% 2.41/0.97  --res_prop_simpl_given                  true
% 2.41/0.97  --res_passive_queue_type                priority_queues
% 2.41/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.41/0.97  --res_passive_queues_freq               [15;5]
% 2.41/0.97  --res_forward_subs                      full
% 2.41/0.97  --res_backward_subs                     full
% 2.41/0.97  --res_forward_subs_resolution           true
% 2.41/0.97  --res_backward_subs_resolution          true
% 2.41/0.97  --res_orphan_elimination                true
% 2.41/0.97  --res_time_limit                        2.
% 2.41/0.97  --res_out_proof                         true
% 2.41/0.97  
% 2.41/0.97  ------ Superposition Options
% 2.41/0.97  
% 2.41/0.97  --superposition_flag                    true
% 2.41/0.97  --sup_passive_queue_type                priority_queues
% 2.41/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.41/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.41/0.97  --demod_completeness_check              fast
% 2.41/0.97  --demod_use_ground                      true
% 2.41/0.97  --sup_to_prop_solver                    passive
% 2.41/0.97  --sup_prop_simpl_new                    true
% 2.41/0.97  --sup_prop_simpl_given                  true
% 2.41/0.97  --sup_fun_splitting                     false
% 2.41/0.97  --sup_smt_interval                      50000
% 2.41/0.97  
% 2.41/0.97  ------ Superposition Simplification Setup
% 2.41/0.97  
% 2.41/0.97  --sup_indices_passive                   []
% 2.41/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.41/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.41/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.41/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.41/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.41/0.97  --sup_full_bw                           [BwDemod]
% 2.41/0.97  --sup_immed_triv                        [TrivRules]
% 2.41/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.41/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.41/0.97  --sup_immed_bw_main                     []
% 2.41/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.41/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.41/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.41/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.41/0.97  
% 2.41/0.97  ------ Combination Options
% 2.41/0.97  
% 2.41/0.97  --comb_res_mult                         3
% 2.41/0.97  --comb_sup_mult                         2
% 2.41/0.97  --comb_inst_mult                        10
% 2.41/0.97  
% 2.41/0.97  ------ Debug Options
% 2.41/0.97  
% 2.41/0.97  --dbg_backtrace                         false
% 2.41/0.97  --dbg_dump_prop_clauses                 false
% 2.41/0.97  --dbg_dump_prop_clauses_file            -
% 2.41/0.97  --dbg_out_stat                          false
% 2.41/0.97  ------ Parsing...
% 2.41/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.41/0.97  
% 2.41/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.41/0.97  
% 2.41/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.41/0.97  
% 2.41/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.41/0.97  ------ Proving...
% 2.41/0.97  ------ Problem Properties 
% 2.41/0.97  
% 2.41/0.97  
% 2.41/0.97  clauses                                 16
% 2.41/0.97  conjectures                             4
% 2.41/0.97  EPR                                     6
% 2.41/0.97  Horn                                    14
% 2.41/0.97  unary                                   6
% 2.41/0.97  binary                                  6
% 2.41/0.97  lits                                    30
% 2.41/0.97  lits eq                                 7
% 2.41/0.97  fd_pure                                 0
% 2.41/0.97  fd_pseudo                               0
% 2.41/0.97  fd_cond                                 3
% 2.41/0.97  fd_pseudo_cond                          1
% 2.41/0.97  AC symbols                              0
% 2.41/0.97  
% 2.41/0.97  ------ Schedule dynamic 5 is on 
% 2.41/0.97  
% 2.41/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.41/0.97  
% 2.41/0.97  
% 2.41/0.97  ------ 
% 2.41/0.97  Current options:
% 2.41/0.97  ------ 
% 2.41/0.97  
% 2.41/0.97  ------ Input Options
% 2.41/0.97  
% 2.41/0.97  --out_options                           all
% 2.41/0.97  --tptp_safe_out                         true
% 2.41/0.97  --problem_path                          ""
% 2.41/0.97  --include_path                          ""
% 2.41/0.97  --clausifier                            res/vclausify_rel
% 2.41/0.97  --clausifier_options                    --mode clausify
% 2.41/0.97  --stdin                                 false
% 2.41/0.97  --stats_out                             all
% 2.41/0.97  
% 2.41/0.97  ------ General Options
% 2.41/0.97  
% 2.41/0.97  --fof                                   false
% 2.41/0.97  --time_out_real                         305.
% 2.41/0.97  --time_out_virtual                      -1.
% 2.41/0.97  --symbol_type_check                     false
% 2.41/0.97  --clausify_out                          false
% 2.41/0.97  --sig_cnt_out                           false
% 2.41/0.97  --trig_cnt_out                          false
% 2.41/0.97  --trig_cnt_out_tolerance                1.
% 2.41/0.97  --trig_cnt_out_sk_spl                   false
% 2.41/0.97  --abstr_cl_out                          false
% 2.41/0.97  
% 2.41/0.97  ------ Global Options
% 2.41/0.97  
% 2.41/0.97  --schedule                              default
% 2.41/0.97  --add_important_lit                     false
% 2.41/0.97  --prop_solver_per_cl                    1000
% 2.41/0.97  --min_unsat_core                        false
% 2.41/0.97  --soft_assumptions                      false
% 2.41/0.97  --soft_lemma_size                       3
% 2.41/0.97  --prop_impl_unit_size                   0
% 2.41/0.97  --prop_impl_unit                        []
% 2.41/0.97  --share_sel_clauses                     true
% 2.41/0.97  --reset_solvers                         false
% 2.41/0.97  --bc_imp_inh                            [conj_cone]
% 2.41/0.97  --conj_cone_tolerance                   3.
% 2.41/0.97  --extra_neg_conj                        none
% 2.41/0.97  --large_theory_mode                     true
% 2.41/0.97  --prolific_symb_bound                   200
% 2.41/0.97  --lt_threshold                          2000
% 2.41/0.97  --clause_weak_htbl                      true
% 2.41/0.97  --gc_record_bc_elim                     false
% 2.41/0.97  
% 2.41/0.97  ------ Preprocessing Options
% 2.41/0.97  
% 2.41/0.97  --preprocessing_flag                    true
% 2.41/0.97  --time_out_prep_mult                    0.1
% 2.41/0.97  --splitting_mode                        input
% 2.41/0.97  --splitting_grd                         true
% 2.41/0.97  --splitting_cvd                         false
% 2.41/0.97  --splitting_cvd_svl                     false
% 2.41/0.97  --splitting_nvd                         32
% 2.41/0.97  --sub_typing                            true
% 2.41/0.97  --prep_gs_sim                           true
% 2.41/0.97  --prep_unflatten                        true
% 2.41/0.97  --prep_res_sim                          true
% 2.41/0.97  --prep_upred                            true
% 2.41/0.97  --prep_sem_filter                       exhaustive
% 2.41/0.97  --prep_sem_filter_out                   false
% 2.41/0.97  --pred_elim                             true
% 2.41/0.97  --res_sim_input                         true
% 2.41/0.97  --eq_ax_congr_red                       true
% 2.41/0.97  --pure_diseq_elim                       true
% 2.41/0.97  --brand_transform                       false
% 2.41/0.97  --non_eq_to_eq                          false
% 2.41/0.97  --prep_def_merge                        true
% 2.41/0.97  --prep_def_merge_prop_impl              false
% 2.41/0.97  --prep_def_merge_mbd                    true
% 2.41/0.97  --prep_def_merge_tr_red                 false
% 2.41/0.97  --prep_def_merge_tr_cl                  false
% 2.41/0.97  --smt_preprocessing                     true
% 2.41/0.97  --smt_ac_axioms                         fast
% 2.41/0.97  --preprocessed_out                      false
% 2.41/0.97  --preprocessed_stats                    false
% 2.41/0.97  
% 2.41/0.97  ------ Abstraction refinement Options
% 2.41/0.97  
% 2.41/0.97  --abstr_ref                             []
% 2.41/0.97  --abstr_ref_prep                        false
% 2.41/0.97  --abstr_ref_until_sat                   false
% 2.41/0.97  --abstr_ref_sig_restrict                funpre
% 2.41/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.41/0.97  --abstr_ref_under                       []
% 2.41/0.97  
% 2.41/0.97  ------ SAT Options
% 2.41/0.97  
% 2.41/0.97  --sat_mode                              false
% 2.41/0.97  --sat_fm_restart_options                ""
% 2.41/0.97  --sat_gr_def                            false
% 2.41/0.97  --sat_epr_types                         true
% 2.41/0.97  --sat_non_cyclic_types                  false
% 2.41/0.97  --sat_finite_models                     false
% 2.41/0.97  --sat_fm_lemmas                         false
% 2.41/0.97  --sat_fm_prep                           false
% 2.41/0.97  --sat_fm_uc_incr                        true
% 2.41/0.97  --sat_out_model                         small
% 2.41/0.97  --sat_out_clauses                       false
% 2.41/0.97  
% 2.41/0.97  ------ QBF Options
% 2.41/0.97  
% 2.41/0.97  --qbf_mode                              false
% 2.41/0.97  --qbf_elim_univ                         false
% 2.41/0.97  --qbf_dom_inst                          none
% 2.41/0.97  --qbf_dom_pre_inst                      false
% 2.41/0.97  --qbf_sk_in                             false
% 2.41/0.97  --qbf_pred_elim                         true
% 2.41/0.97  --qbf_split                             512
% 2.41/0.97  
% 2.41/0.97  ------ BMC1 Options
% 2.41/0.97  
% 2.41/0.97  --bmc1_incremental                      false
% 2.41/0.97  --bmc1_axioms                           reachable_all
% 2.41/0.97  --bmc1_min_bound                        0
% 2.41/0.97  --bmc1_max_bound                        -1
% 2.41/0.97  --bmc1_max_bound_default                -1
% 2.41/0.97  --bmc1_symbol_reachability              true
% 2.41/0.97  --bmc1_property_lemmas                  false
% 2.41/0.97  --bmc1_k_induction                      false
% 2.41/0.97  --bmc1_non_equiv_states                 false
% 2.41/0.97  --bmc1_deadlock                         false
% 2.41/0.97  --bmc1_ucm                              false
% 2.41/0.97  --bmc1_add_unsat_core                   none
% 2.41/0.97  --bmc1_unsat_core_children              false
% 2.41/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.41/0.97  --bmc1_out_stat                         full
% 2.41/0.97  --bmc1_ground_init                      false
% 2.41/0.97  --bmc1_pre_inst_next_state              false
% 2.41/0.97  --bmc1_pre_inst_state                   false
% 2.41/0.97  --bmc1_pre_inst_reach_state             false
% 2.41/0.97  --bmc1_out_unsat_core                   false
% 2.41/0.97  --bmc1_aig_witness_out                  false
% 2.41/0.97  --bmc1_verbose                          false
% 2.41/0.97  --bmc1_dump_clauses_tptp                false
% 2.41/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.41/0.97  --bmc1_dump_file                        -
% 2.41/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.41/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.41/0.97  --bmc1_ucm_extend_mode                  1
% 2.41/0.97  --bmc1_ucm_init_mode                    2
% 2.41/0.97  --bmc1_ucm_cone_mode                    none
% 2.41/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.41/0.97  --bmc1_ucm_relax_model                  4
% 2.41/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.41/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.41/0.97  --bmc1_ucm_layered_model                none
% 2.41/0.97  --bmc1_ucm_max_lemma_size               10
% 2.41/0.97  
% 2.41/0.97  ------ AIG Options
% 2.41/0.97  
% 2.41/0.97  --aig_mode                              false
% 2.41/0.97  
% 2.41/0.97  ------ Instantiation Options
% 2.41/0.97  
% 2.41/0.97  --instantiation_flag                    true
% 2.41/0.97  --inst_sos_flag                         false
% 2.41/0.97  --inst_sos_phase                        true
% 2.41/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.41/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.41/0.97  --inst_lit_sel_side                     none
% 2.41/0.97  --inst_solver_per_active                1400
% 2.41/0.97  --inst_solver_calls_frac                1.
% 2.41/0.97  --inst_passive_queue_type               priority_queues
% 2.41/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.41/0.97  --inst_passive_queues_freq              [25;2]
% 2.41/0.97  --inst_dismatching                      true
% 2.41/0.97  --inst_eager_unprocessed_to_passive     true
% 2.41/0.97  --inst_prop_sim_given                   true
% 2.41/0.97  --inst_prop_sim_new                     false
% 2.41/0.97  --inst_subs_new                         false
% 2.41/0.97  --inst_eq_res_simp                      false
% 2.41/0.97  --inst_subs_given                       false
% 2.41/0.97  --inst_orphan_elimination               true
% 2.41/0.97  --inst_learning_loop_flag               true
% 2.41/0.97  --inst_learning_start                   3000
% 2.41/0.97  --inst_learning_factor                  2
% 2.41/0.97  --inst_start_prop_sim_after_learn       3
% 2.41/0.97  --inst_sel_renew                        solver
% 2.41/0.97  --inst_lit_activity_flag                true
% 2.41/0.97  --inst_restr_to_given                   false
% 2.41/0.97  --inst_activity_threshold               500
% 2.41/0.97  --inst_out_proof                        true
% 2.41/0.97  
% 2.41/0.97  ------ Resolution Options
% 2.41/0.97  
% 2.41/0.97  --resolution_flag                       false
% 2.41/0.97  --res_lit_sel                           adaptive
% 2.41/0.97  --res_lit_sel_side                      none
% 2.41/0.97  --res_ordering                          kbo
% 2.41/0.97  --res_to_prop_solver                    active
% 2.41/0.97  --res_prop_simpl_new                    false
% 2.41/0.97  --res_prop_simpl_given                  true
% 2.41/0.97  --res_passive_queue_type                priority_queues
% 2.41/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.41/0.97  --res_passive_queues_freq               [15;5]
% 2.41/0.97  --res_forward_subs                      full
% 2.41/0.97  --res_backward_subs                     full
% 2.41/0.97  --res_forward_subs_resolution           true
% 2.41/0.97  --res_backward_subs_resolution          true
% 2.41/0.97  --res_orphan_elimination                true
% 2.41/0.97  --res_time_limit                        2.
% 2.41/0.97  --res_out_proof                         true
% 2.41/0.97  
% 2.41/0.97  ------ Superposition Options
% 2.41/0.97  
% 2.41/0.97  --superposition_flag                    true
% 2.41/0.97  --sup_passive_queue_type                priority_queues
% 2.41/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.41/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.41/0.97  --demod_completeness_check              fast
% 2.41/0.97  --demod_use_ground                      true
% 2.41/0.97  --sup_to_prop_solver                    passive
% 2.41/0.97  --sup_prop_simpl_new                    true
% 2.41/0.97  --sup_prop_simpl_given                  true
% 2.41/0.97  --sup_fun_splitting                     false
% 2.41/0.97  --sup_smt_interval                      50000
% 2.41/0.97  
% 2.41/0.97  ------ Superposition Simplification Setup
% 2.41/0.97  
% 2.41/0.97  --sup_indices_passive                   []
% 2.41/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.41/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.41/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.41/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.41/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.41/0.97  --sup_full_bw                           [BwDemod]
% 2.41/0.97  --sup_immed_triv                        [TrivRules]
% 2.41/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.41/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.41/0.97  --sup_immed_bw_main                     []
% 2.41/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.41/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.41/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.41/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.41/0.97  
% 2.41/0.97  ------ Combination Options
% 2.41/0.97  
% 2.41/0.97  --comb_res_mult                         3
% 2.41/0.97  --comb_sup_mult                         2
% 2.41/0.97  --comb_inst_mult                        10
% 2.41/0.97  
% 2.41/0.97  ------ Debug Options
% 2.41/0.97  
% 2.41/0.97  --dbg_backtrace                         false
% 2.41/0.97  --dbg_dump_prop_clauses                 false
% 2.41/0.97  --dbg_dump_prop_clauses_file            -
% 2.41/0.97  --dbg_out_stat                          false
% 2.41/0.97  
% 2.41/0.97  
% 2.41/0.97  
% 2.41/0.97  
% 2.41/0.97  ------ Proving...
% 2.41/0.97  
% 2.41/0.97  
% 2.41/0.97  % SZS status Theorem for theBenchmark.p
% 2.41/0.97  
% 2.41/0.97   Resolution empty clause
% 2.41/0.97  
% 2.41/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 2.41/0.97  
% 2.41/0.97  fof(f11,conjecture,(
% 2.41/0.97    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 2.41/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/0.97  
% 2.41/0.97  fof(f12,negated_conjecture,(
% 2.41/0.97    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 2.41/0.97    inference(negated_conjecture,[],[f11])).
% 2.41/0.97  
% 2.41/0.97  fof(f23,plain,(
% 2.41/0.97    ? [X0,X1] : (? [X2] : ((~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.41/0.97    inference(ennf_transformation,[],[f12])).
% 2.41/0.97  
% 2.41/0.97  fof(f24,plain,(
% 2.41/0.97    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.41/0.97    inference(flattening,[],[f23])).
% 2.41/0.97  
% 2.41/0.97  fof(f29,plain,(
% 2.41/0.97    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (~r1_tarski(k8_setfam_1(X0,sK2),k8_setfam_1(X0,X1)) & r1_tarski(X1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(X0))))) )),
% 2.41/0.97    introduced(choice_axiom,[])).
% 2.41/0.97  
% 2.41/0.97  fof(f28,plain,(
% 2.41/0.97    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (? [X2] : (~r1_tarski(k8_setfam_1(sK0,X2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 2.41/0.97    introduced(choice_axiom,[])).
% 2.41/0.97  
% 2.41/0.97  fof(f30,plain,(
% 2.41/0.97    (~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 2.41/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f29,f28])).
% 2.41/0.97  
% 2.41/0.97  fof(f47,plain,(
% 2.41/0.97    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 2.41/0.97    inference(cnf_transformation,[],[f30])).
% 2.41/0.97  
% 2.41/0.97  fof(f7,axiom,(
% 2.41/0.97    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.41/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/0.97  
% 2.41/0.97  fof(f19,plain,(
% 2.41/0.97    ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.41/0.97    inference(ennf_transformation,[],[f7])).
% 2.41/0.97  
% 2.41/0.97  fof(f41,plain,(
% 2.41/0.97    ( ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.41/0.97    inference(cnf_transformation,[],[f19])).
% 2.41/0.97  
% 2.41/0.97  fof(f9,axiom,(
% 2.41/0.97    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.41/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/0.97  
% 2.41/0.97  fof(f27,plain,(
% 2.41/0.97    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.41/0.97    inference(nnf_transformation,[],[f9])).
% 2.41/0.97  
% 2.41/0.97  fof(f43,plain,(
% 2.41/0.97    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.41/0.97    inference(cnf_transformation,[],[f27])).
% 2.41/0.97  
% 2.41/0.97  fof(f10,axiom,(
% 2.41/0.97    ! [X0,X1] : (r1_tarski(X0,X1) => (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 2.41/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/0.97  
% 2.41/0.97  fof(f21,plain,(
% 2.41/0.97    ! [X0,X1] : ((r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0) | ~r1_tarski(X0,X1))),
% 2.41/0.97    inference(ennf_transformation,[],[f10])).
% 2.41/0.97  
% 2.41/0.97  fof(f22,plain,(
% 2.41/0.97    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1))),
% 2.41/0.97    inference(flattening,[],[f21])).
% 2.41/0.97  
% 2.41/0.97  fof(f45,plain,(
% 2.41/0.97    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1)) )),
% 2.41/0.97    inference(cnf_transformation,[],[f22])).
% 2.41/0.97  
% 2.41/0.97  fof(f6,axiom,(
% 2.41/0.97    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((k1_xboole_0 = X1 => k8_setfam_1(X0,X1) = X0) & (k1_xboole_0 != X1 => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1))))),
% 2.41/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/0.97  
% 2.41/0.97  fof(f18,plain,(
% 2.41/0.97    ! [X0,X1] : (((k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1) & (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.41/0.97    inference(ennf_transformation,[],[f6])).
% 2.41/0.97  
% 2.41/0.97  fof(f39,plain,(
% 2.41/0.97    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.41/0.97    inference(cnf_transformation,[],[f18])).
% 2.41/0.97  
% 2.41/0.97  fof(f8,axiom,(
% 2.41/0.97    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k6_setfam_1(X0,X1) = k1_setfam_1(X1))),
% 2.41/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/0.97  
% 2.41/0.97  fof(f20,plain,(
% 2.41/0.97    ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.41/0.97    inference(ennf_transformation,[],[f8])).
% 2.41/0.97  
% 2.41/0.97  fof(f42,plain,(
% 2.41/0.97    ( ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.41/0.97    inference(cnf_transformation,[],[f20])).
% 2.41/0.97  
% 2.41/0.97  fof(f46,plain,(
% 2.41/0.97    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 2.41/0.97    inference(cnf_transformation,[],[f30])).
% 2.41/0.97  
% 2.41/0.97  fof(f49,plain,(
% 2.41/0.97    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))),
% 2.41/0.97    inference(cnf_transformation,[],[f30])).
% 2.41/0.97  
% 2.41/0.97  fof(f48,plain,(
% 2.41/0.97    r1_tarski(sK1,sK2)),
% 2.41/0.97    inference(cnf_transformation,[],[f30])).
% 2.41/0.97  
% 2.41/0.97  fof(f3,axiom,(
% 2.41/0.97    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 2.41/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/0.97  
% 2.41/0.97  fof(f14,plain,(
% 2.41/0.97    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 2.41/0.97    inference(ennf_transformation,[],[f3])).
% 2.41/0.97  
% 2.41/0.97  fof(f35,plain,(
% 2.41/0.97    ( ! [X0] : (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)) )),
% 2.41/0.97    inference(cnf_transformation,[],[f14])).
% 2.41/0.97  
% 2.41/0.97  fof(f52,plain,(
% 2.41/0.97    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 2.41/0.97    inference(equality_resolution,[],[f35])).
% 2.41/0.97  
% 2.41/0.97  fof(f36,plain,(
% 2.41/0.97    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 2.41/0.97    inference(cnf_transformation,[],[f14])).
% 2.41/0.97  
% 2.41/0.97  fof(f40,plain,(
% 2.41/0.97    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.41/0.97    inference(cnf_transformation,[],[f18])).
% 2.41/0.97  
% 2.41/0.97  fof(f53,plain,(
% 2.41/0.97    ( ! [X0] : (k8_setfam_1(X0,k1_xboole_0) = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.41/0.97    inference(equality_resolution,[],[f40])).
% 2.41/0.97  
% 2.41/0.97  fof(f2,axiom,(
% 2.41/0.97    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.41/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/0.97  
% 2.41/0.97  fof(f25,plain,(
% 2.41/0.97    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.41/0.97    inference(nnf_transformation,[],[f2])).
% 2.41/0.97  
% 2.41/0.97  fof(f26,plain,(
% 2.41/0.97    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.41/0.97    inference(flattening,[],[f25])).
% 2.41/0.97  
% 2.41/0.97  fof(f34,plain,(
% 2.41/0.97    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.41/0.97    inference(cnf_transformation,[],[f26])).
% 2.41/0.97  
% 2.41/0.97  fof(f4,axiom,(
% 2.41/0.97    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 2.41/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/0.97  
% 2.41/0.97  fof(f15,plain,(
% 2.41/0.97    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 2.41/0.97    inference(ennf_transformation,[],[f4])).
% 2.41/0.97  
% 2.41/0.97  fof(f16,plain,(
% 2.41/0.97    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 2.41/0.97    inference(flattening,[],[f15])).
% 2.41/0.97  
% 2.41/0.97  fof(f37,plain,(
% 2.41/0.97    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 2.41/0.97    inference(cnf_transformation,[],[f16])).
% 2.41/0.97  
% 2.41/0.97  fof(f32,plain,(
% 2.41/0.97    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.41/0.97    inference(cnf_transformation,[],[f26])).
% 2.41/0.97  
% 2.41/0.97  fof(f51,plain,(
% 2.41/0.97    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.41/0.97    inference(equality_resolution,[],[f32])).
% 2.41/0.97  
% 2.41/0.97  fof(f1,axiom,(
% 2.41/0.97    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.41/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/0.97  
% 2.41/0.97  fof(f13,plain,(
% 2.41/0.97    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.41/0.97    inference(ennf_transformation,[],[f1])).
% 2.41/0.97  
% 2.41/0.97  fof(f31,plain,(
% 2.41/0.97    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 2.41/0.97    inference(cnf_transformation,[],[f13])).
% 2.41/0.97  
% 2.41/0.97  fof(f5,axiom,(
% 2.41/0.97    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 2.41/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/0.97  
% 2.41/0.97  fof(f17,plain,(
% 2.41/0.97    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 2.41/0.97    inference(ennf_transformation,[],[f5])).
% 2.41/0.97  
% 2.41/0.97  fof(f38,plain,(
% 2.41/0.97    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 2.41/0.97    inference(cnf_transformation,[],[f17])).
% 2.41/0.97  
% 2.41/0.97  fof(f44,plain,(
% 2.41/0.97    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.41/0.97    inference(cnf_transformation,[],[f27])).
% 2.41/0.97  
% 2.41/0.97  cnf(c_17,negated_conjecture,
% 2.41/0.97      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
% 2.41/0.97      inference(cnf_transformation,[],[f47]) ).
% 2.41/0.97  
% 2.41/0.97  cnf(c_772,plain,
% 2.41/0.97      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) = iProver_top ),
% 2.41/0.97      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.41/0.97  
% 2.41/0.97  cnf(c_10,plain,
% 2.41/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.41/0.97      | m1_subset_1(k8_setfam_1(X1,X0),k1_zfmisc_1(X1)) ),
% 2.41/0.97      inference(cnf_transformation,[],[f41]) ).
% 2.41/0.97  
% 2.41/0.97  cnf(c_779,plain,
% 2.41/0.97      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 2.41/0.97      | m1_subset_1(k8_setfam_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 2.41/0.97      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.41/0.97  
% 2.41/0.97  cnf(c_13,plain,
% 2.41/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.41/0.97      inference(cnf_transformation,[],[f43]) ).
% 2.41/0.97  
% 2.41/0.97  cnf(c_776,plain,
% 2.41/0.97      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.41/0.97      | r1_tarski(X0,X1) = iProver_top ),
% 2.41/0.97      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.41/0.97  
% 2.41/0.97  cnf(c_1827,plain,
% 2.41/0.97      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 2.41/0.97      | r1_tarski(k8_setfam_1(X1,X0),X1) = iProver_top ),
% 2.41/0.97      inference(superposition,[status(thm)],[c_779,c_776]) ).
% 2.41/0.97  
% 2.41/0.97  cnf(c_3431,plain,
% 2.41/0.97      ( r1_tarski(k8_setfam_1(sK0,sK2),sK0) = iProver_top ),
% 2.41/0.97      inference(superposition,[status(thm)],[c_772,c_1827]) ).
% 2.41/0.97  
% 2.41/0.97  cnf(c_14,plain,
% 2.41/0.97      ( ~ r1_tarski(X0,X1)
% 2.41/0.97      | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
% 2.41/0.97      | k1_xboole_0 = X0 ),
% 2.41/0.97      inference(cnf_transformation,[],[f45]) ).
% 2.41/0.97  
% 2.41/0.97  cnf(c_775,plain,
% 2.41/0.97      ( k1_xboole_0 = X0
% 2.41/0.97      | r1_tarski(X0,X1) != iProver_top
% 2.41/0.97      | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) = iProver_top ),
% 2.41/0.97      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.41/0.97  
% 2.41/0.97  cnf(c_9,plain,
% 2.41/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.41/0.97      | k6_setfam_1(X1,X0) = k8_setfam_1(X1,X0)
% 2.41/0.97      | k1_xboole_0 = X0 ),
% 2.41/0.97      inference(cnf_transformation,[],[f39]) ).
% 2.41/0.97  
% 2.41/0.97  cnf(c_780,plain,
% 2.41/0.97      ( k6_setfam_1(X0,X1) = k8_setfam_1(X0,X1)
% 2.41/0.97      | k1_xboole_0 = X1
% 2.41/0.97      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 2.41/0.97      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.41/0.97  
% 2.41/0.97  cnf(c_2005,plain,
% 2.41/0.97      ( k6_setfam_1(sK0,sK2) = k8_setfam_1(sK0,sK2) | sK2 = k1_xboole_0 ),
% 2.41/0.97      inference(superposition,[status(thm)],[c_772,c_780]) ).
% 2.41/0.97  
% 2.41/0.97  cnf(c_11,plain,
% 2.41/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.41/0.97      | k6_setfam_1(X1,X0) = k1_setfam_1(X0) ),
% 2.41/0.97      inference(cnf_transformation,[],[f42]) ).
% 2.41/0.97  
% 2.41/0.97  cnf(c_778,plain,
% 2.41/0.97      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
% 2.41/0.97      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 2.41/0.97      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.41/0.97  
% 2.41/0.97  cnf(c_1261,plain,
% 2.41/0.97      ( k6_setfam_1(sK0,sK2) = k1_setfam_1(sK2) ),
% 2.41/0.97      inference(superposition,[status(thm)],[c_772,c_778]) ).
% 2.41/0.97  
% 2.41/0.97  cnf(c_2014,plain,
% 2.41/0.97      ( k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) | sK2 = k1_xboole_0 ),
% 2.41/0.97      inference(light_normalisation,[status(thm)],[c_2005,c_1261]) ).
% 2.41/0.97  
% 2.41/0.97  cnf(c_18,negated_conjecture,
% 2.41/0.97      ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
% 2.41/0.97      inference(cnf_transformation,[],[f46]) ).
% 2.41/0.97  
% 2.41/0.97  cnf(c_771,plain,
% 2.41/0.97      ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) = iProver_top ),
% 2.41/0.97      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.41/0.97  
% 2.41/0.97  cnf(c_2006,plain,
% 2.41/0.97      ( k6_setfam_1(sK0,sK1) = k8_setfam_1(sK0,sK1) | sK1 = k1_xboole_0 ),
% 2.41/0.97      inference(superposition,[status(thm)],[c_771,c_780]) ).
% 2.41/0.97  
% 2.41/0.97  cnf(c_1262,plain,
% 2.41/0.97      ( k6_setfam_1(sK0,sK1) = k1_setfam_1(sK1) ),
% 2.41/0.97      inference(superposition,[status(thm)],[c_771,c_778]) ).
% 2.41/0.97  
% 2.41/0.97  cnf(c_2009,plain,
% 2.41/0.97      ( k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1) | sK1 = k1_xboole_0 ),
% 2.41/0.97      inference(light_normalisation,[status(thm)],[c_2006,c_1262]) ).
% 2.41/0.97  
% 2.41/0.97  cnf(c_15,negated_conjecture,
% 2.41/0.97      ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) ),
% 2.41/0.97      inference(cnf_transformation,[],[f49]) ).
% 2.41/0.97  
% 2.41/0.97  cnf(c_774,plain,
% 2.41/0.97      ( r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) != iProver_top ),
% 2.41/0.97      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.41/0.97  
% 2.41/0.97  cnf(c_2216,plain,
% 2.41/0.97      ( sK1 = k1_xboole_0
% 2.41/0.97      | r1_tarski(k8_setfam_1(sK0,sK2),k1_setfam_1(sK1)) != iProver_top ),
% 2.41/0.97      inference(superposition,[status(thm)],[c_2009,c_774]) ).
% 2.41/0.97  
% 2.41/0.97  cnf(c_2298,plain,
% 2.41/0.97      ( sK1 = k1_xboole_0
% 2.41/0.97      | sK2 = k1_xboole_0
% 2.41/0.97      | r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) != iProver_top ),
% 2.41/0.97      inference(superposition,[status(thm)],[c_2014,c_2216]) ).
% 2.41/0.97  
% 2.41/0.97  cnf(c_2386,plain,
% 2.41/0.97      ( sK1 = k1_xboole_0
% 2.41/0.97      | sK2 = k1_xboole_0
% 2.41/0.97      | r1_tarski(sK1,sK2) != iProver_top ),
% 2.41/0.97      inference(superposition,[status(thm)],[c_775,c_2298]) ).
% 2.41/0.97  
% 2.41/0.97  cnf(c_16,negated_conjecture,
% 2.41/0.97      ( r1_tarski(sK1,sK2) ),
% 2.41/0.97      inference(cnf_transformation,[],[f48]) ).
% 2.41/0.97  
% 2.41/0.97  cnf(c_2387,plain,
% 2.41/0.97      ( ~ r1_tarski(sK1,sK2) | sK1 = k1_xboole_0 | sK2 = k1_xboole_0 ),
% 2.41/0.97      inference(predicate_to_equality_rev,[status(thm)],[c_2386]) ).
% 2.41/0.97  
% 2.41/0.97  cnf(c_2389,plain,
% 2.41/0.97      ( sK2 = k1_xboole_0 | sK1 = k1_xboole_0 ),
% 2.41/0.97      inference(global_propositional_subsumption,
% 2.41/0.97                [status(thm)],
% 2.41/0.97                [c_2386,c_16,c_2387]) ).
% 2.41/0.97  
% 2.41/0.97  cnf(c_2390,plain,
% 2.41/0.97      ( sK1 = k1_xboole_0 | sK2 = k1_xboole_0 ),
% 2.41/0.97      inference(renaming,[status(thm)],[c_2389]) ).
% 2.41/0.97  
% 2.41/0.97  cnf(c_2400,plain,
% 2.41/0.97      ( sK2 = k1_xboole_0
% 2.41/0.97      | r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,k1_xboole_0)) != iProver_top ),
% 2.41/0.97      inference(superposition,[status(thm)],[c_2390,c_774]) ).
% 2.41/0.97  
% 2.41/0.97  cnf(c_2401,plain,
% 2.41/0.97      ( sK2 = k1_xboole_0
% 2.41/0.97      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) = iProver_top ),
% 2.41/0.97      inference(superposition,[status(thm)],[c_2390,c_771]) ).
% 2.41/0.97  
% 2.41/0.97  cnf(c_20,plain,
% 2.41/0.97      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) = iProver_top ),
% 2.41/0.97      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.41/0.97  
% 2.41/0.97  cnf(c_5,plain,
% 2.41/0.97      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 2.41/0.97      inference(cnf_transformation,[],[f52]) ).
% 2.41/0.97  
% 2.41/0.97  cnf(c_4,plain,
% 2.41/0.97      ( ~ r1_xboole_0(X0,X0) | k1_xboole_0 = X0 ),
% 2.41/0.97      inference(cnf_transformation,[],[f36]) ).
% 2.41/0.97  
% 2.41/0.97  cnf(c_50,plain,
% 2.41/0.97      ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k1_xboole_0 ),
% 2.41/0.97      inference(instantiation,[status(thm)],[c_4]) ).
% 2.41/0.97  
% 2.41/0.97  cnf(c_398,plain,
% 2.41/0.97      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.41/0.97      theory(equality) ).
% 2.41/0.97  
% 2.41/0.97  cnf(c_913,plain,
% 2.41/0.97      ( m1_subset_1(X0,X1)
% 2.41/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
% 2.41/0.97      | X0 != X2
% 2.41/0.97      | X1 != k1_zfmisc_1(X3) ),
% 2.41/0.97      inference(instantiation,[status(thm)],[c_398]) ).
% 2.41/0.97  
% 2.41/0.97  cnf(c_999,plain,
% 2.41/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.41/0.97      | m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.41/0.97      | X2 != X0
% 2.41/0.97      | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
% 2.41/0.97      inference(instantiation,[status(thm)],[c_913]) ).
% 2.41/0.97  
% 2.41/0.97  cnf(c_1210,plain,
% 2.41/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.41/0.97      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.41/0.97      | k1_zfmisc_1(k1_zfmisc_1(X1)) != k1_zfmisc_1(k1_zfmisc_1(X1))
% 2.41/0.97      | k1_xboole_0 != X0 ),
% 2.41/0.97      inference(instantiation,[status(thm)],[c_999]) ).
% 2.41/0.97  
% 2.41/0.97  cnf(c_1877,plain,
% 2.41/0.97      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
% 2.41/0.97      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
% 2.41/0.97      | k1_zfmisc_1(k1_zfmisc_1(sK0)) != k1_zfmisc_1(k1_zfmisc_1(sK0))
% 2.41/0.97      | k1_xboole_0 != sK2 ),
% 2.41/0.97      inference(instantiation,[status(thm)],[c_1210]) ).
% 2.41/0.97  
% 2.41/0.97  cnf(c_1878,plain,
% 2.41/0.97      ( k1_zfmisc_1(k1_zfmisc_1(sK0)) != k1_zfmisc_1(k1_zfmisc_1(sK0))
% 2.41/0.97      | k1_xboole_0 != sK2
% 2.41/0.97      | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) != iProver_top
% 2.41/0.97      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) = iProver_top ),
% 2.41/0.97      inference(predicate_to_equality,[status(thm)],[c_1877]) ).
% 2.41/0.97  
% 2.41/0.97  cnf(c_394,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.41/0.97  
% 2.41/0.97  cnf(c_2062,plain,
% 2.41/0.97      ( sK2 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK2 ),
% 2.41/0.97      inference(instantiation,[status(thm)],[c_394]) ).
% 2.41/0.97  
% 2.41/0.97  cnf(c_2063,plain,
% 2.41/0.97      ( sK2 != k1_xboole_0 | k1_xboole_0 = sK2 | k1_xboole_0 != k1_xboole_0 ),
% 2.41/0.97      inference(instantiation,[status(thm)],[c_2062]) ).
% 2.41/0.97  
% 2.41/0.97  cnf(c_393,plain,( X0 = X0 ),theory(equality) ).
% 2.41/0.97  
% 2.41/0.97  cnf(c_1000,plain,
% 2.41/0.97      ( k1_zfmisc_1(X0) = k1_zfmisc_1(X0) ),
% 2.41/0.97      inference(instantiation,[status(thm)],[c_393]) ).
% 2.41/0.97  
% 2.41/0.97  cnf(c_2171,plain,
% 2.41/0.97      ( k1_zfmisc_1(k1_zfmisc_1(sK0)) = k1_zfmisc_1(k1_zfmisc_1(sK0)) ),
% 2.41/0.97      inference(instantiation,[status(thm)],[c_1000]) ).
% 2.41/0.97  
% 2.41/0.97  cnf(c_2641,plain,
% 2.41/0.97      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) = iProver_top ),
% 2.41/0.97      inference(global_propositional_subsumption,
% 2.41/0.97                [status(thm)],
% 2.41/0.97                [c_2401,c_20,c_5,c_50,c_1878,c_2063,c_2171]) ).
% 2.41/0.97  
% 2.41/0.97  cnf(c_8,plain,
% 2.41/0.97      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
% 2.41/0.97      | k8_setfam_1(X0,k1_xboole_0) = X0 ),
% 2.41/0.97      inference(cnf_transformation,[],[f53]) ).
% 2.41/0.97  
% 2.41/0.97  cnf(c_781,plain,
% 2.41/0.97      ( k8_setfam_1(X0,k1_xboole_0) = X0
% 2.41/0.97      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 2.41/0.97      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.41/0.97  
% 2.41/0.97  cnf(c_2647,plain,
% 2.41/0.97      ( k8_setfam_1(sK0,k1_xboole_0) = sK0 ),
% 2.41/0.97      inference(superposition,[status(thm)],[c_2641,c_781]) ).
% 2.41/0.97  
% 2.41/0.97  cnf(c_2703,plain,
% 2.41/0.97      ( sK2 = k1_xboole_0
% 2.41/0.97      | r1_tarski(k8_setfam_1(sK0,sK2),sK0) != iProver_top ),
% 2.41/0.97      inference(light_normalisation,[status(thm)],[c_2400,c_2647]) ).
% 2.41/0.97  
% 2.41/0.97  cnf(c_3461,plain,
% 2.41/0.97      ( sK2 = k1_xboole_0 ),
% 2.41/0.97      inference(superposition,[status(thm)],[c_3431,c_2703]) ).
% 2.41/0.97  
% 2.41/0.97  cnf(c_773,plain,
% 2.41/0.97      ( r1_tarski(sK1,sK2) = iProver_top ),
% 2.41/0.97      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.41/0.97  
% 2.41/0.97  cnf(c_1,plain,
% 2.41/0.97      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 2.41/0.97      inference(cnf_transformation,[],[f34]) ).
% 2.41/0.97  
% 2.41/0.97  cnf(c_783,plain,
% 2.41/0.97      ( X0 = X1
% 2.41/0.97      | r1_tarski(X0,X1) != iProver_top
% 2.41/0.97      | r1_tarski(X1,X0) != iProver_top ),
% 2.41/0.97      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.41/0.97  
% 2.41/0.97  cnf(c_1849,plain,
% 2.41/0.97      ( sK1 = sK2 | r1_tarski(sK2,sK1) != iProver_top ),
% 2.41/0.97      inference(superposition,[status(thm)],[c_773,c_783]) ).
% 2.41/0.97  
% 2.41/0.97  cnf(c_3730,plain,
% 2.41/0.97      ( sK1 = k1_xboole_0 | r1_tarski(k1_xboole_0,sK1) != iProver_top ),
% 2.41/0.97      inference(demodulation,[status(thm)],[c_3461,c_1849]) ).
% 2.41/0.97  
% 2.41/0.97  cnf(c_6,plain,
% 2.41/0.97      ( ~ r1_xboole_0(X0,X1) | ~ r1_tarski(X0,X1) | v1_xboole_0(X0) ),
% 2.41/0.97      inference(cnf_transformation,[],[f37]) ).
% 2.41/0.97  
% 2.41/0.97  cnf(c_45,plain,
% 2.41/0.97      ( r1_xboole_0(X0,X1) != iProver_top
% 2.41/0.97      | r1_tarski(X0,X1) != iProver_top
% 2.41/0.97      | v1_xboole_0(X0) = iProver_top ),
% 2.41/0.97      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.41/0.97  
% 2.41/0.97  cnf(c_47,plain,
% 2.41/0.97      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top
% 2.41/0.97      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 2.41/0.97      | v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.41/0.97      inference(instantiation,[status(thm)],[c_45]) ).
% 2.41/0.97  
% 2.41/0.97  cnf(c_48,plain,
% 2.41/0.97      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 2.41/0.97      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.41/0.97  
% 2.41/0.97  cnf(c_3,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f51]) ).
% 2.41/0.97  
% 2.41/0.97  cnf(c_52,plain,
% 2.41/0.97      ( r1_tarski(X0,X0) = iProver_top ),
% 2.41/0.97      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.41/0.97  
% 2.41/0.97  cnf(c_54,plain,
% 2.41/0.97      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 2.41/0.97      inference(instantiation,[status(thm)],[c_52]) ).
% 2.41/0.97  
% 2.41/0.97  cnf(c_1059,plain,
% 2.41/0.97      ( sK1 = sK1 ),
% 2.41/0.97      inference(instantiation,[status(thm)],[c_393]) ).
% 2.41/0.97  
% 2.41/0.97  cnf(c_1061,plain,
% 2.41/0.97      ( X0 != X1 | sK1 != X1 | sK1 = X0 ),
% 2.41/0.97      inference(instantiation,[status(thm)],[c_394]) ).
% 2.41/0.97  
% 2.41/0.97  cnf(c_1499,plain,
% 2.41/0.97      ( X0 != sK1 | sK1 = X0 | sK1 != sK1 ),
% 2.41/0.97      inference(instantiation,[status(thm)],[c_1061]) ).
% 2.41/0.97  
% 2.41/0.97  cnf(c_1500,plain,
% 2.41/0.97      ( sK1 != sK1 | sK1 = k1_xboole_0 | k1_xboole_0 != sK1 ),
% 2.41/0.97      inference(instantiation,[status(thm)],[c_1499]) ).
% 2.41/0.97  
% 2.41/0.97  cnf(c_0,plain,
% 2.41/0.97      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 2.41/0.97      inference(cnf_transformation,[],[f31]) ).
% 2.41/0.97  
% 2.41/0.97  cnf(c_1703,plain,
% 2.41/0.97      ( ~ v1_xboole_0(sK1) | k1_xboole_0 = sK1 ),
% 2.41/0.97      inference(instantiation,[status(thm)],[c_0]) ).
% 2.41/0.97  
% 2.41/0.97  cnf(c_1714,plain,
% 2.41/0.97      ( k1_xboole_0 = sK1 | v1_xboole_0(sK1) != iProver_top ),
% 2.41/0.97      inference(predicate_to_equality,[status(thm)],[c_1703]) ).
% 2.41/0.97  
% 2.41/0.97  cnf(c_7,plain,
% 2.41/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.41/0.97      | ~ v1_xboole_0(X1)
% 2.41/0.97      | v1_xboole_0(X0) ),
% 2.41/0.97      inference(cnf_transformation,[],[f38]) ).
% 2.41/0.97  
% 2.41/0.97  cnf(c_12,plain,
% 2.41/0.97      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.41/0.97      inference(cnf_transformation,[],[f44]) ).
% 2.41/0.97  
% 2.41/0.97  cnf(c_146,plain,
% 2.41/0.97      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.41/0.97      inference(prop_impl,[status(thm)],[c_12]) ).
% 2.41/0.97  
% 2.41/0.97  cnf(c_147,plain,
% 2.41/0.97      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.41/0.97      inference(renaming,[status(thm)],[c_146]) ).
% 2.41/0.97  
% 2.41/0.97  cnf(c_173,plain,
% 2.41/0.97      ( ~ r1_tarski(X0,X1) | ~ v1_xboole_0(X1) | v1_xboole_0(X0) ),
% 2.41/0.97      inference(bin_hyper_res,[status(thm)],[c_7,c_147]) ).
% 2.41/0.97  
% 2.41/0.97  cnf(c_770,plain,
% 2.41/0.97      ( r1_tarski(X0,X1) != iProver_top
% 2.41/0.97      | v1_xboole_0(X1) != iProver_top
% 2.41/0.97      | v1_xboole_0(X0) = iProver_top ),
% 2.41/0.97      inference(predicate_to_equality,[status(thm)],[c_173]) ).
% 2.41/0.97  
% 2.41/0.97  cnf(c_1091,plain,
% 2.41/0.97      ( v1_xboole_0(sK1) = iProver_top | v1_xboole_0(sK2) != iProver_top ),
% 2.41/0.97      inference(superposition,[status(thm)],[c_773,c_770]) ).
% 2.41/0.97  
% 2.41/0.97  cnf(c_3732,plain,
% 2.41/0.97      ( v1_xboole_0(sK1) = iProver_top
% 2.41/0.97      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.41/0.97      inference(demodulation,[status(thm)],[c_3461,c_1091]) ).
% 2.41/0.97  
% 2.41/0.97  cnf(c_3984,plain,
% 2.41/0.97      ( sK1 = k1_xboole_0 ),
% 2.41/0.97      inference(global_propositional_subsumption,
% 2.41/0.97                [status(thm)],
% 2.41/0.97                [c_3730,c_47,c_48,c_54,c_1059,c_1500,c_1714,c_3732]) ).
% 2.41/0.97  
% 2.41/0.97  cnf(c_3735,plain,
% 2.41/0.97      ( r1_tarski(k8_setfam_1(sK0,k1_xboole_0),k8_setfam_1(sK0,sK1)) != iProver_top ),
% 2.41/0.97      inference(demodulation,[status(thm)],[c_3461,c_774]) ).
% 2.41/0.97  
% 2.41/0.97  cnf(c_3741,plain,
% 2.41/0.97      ( r1_tarski(sK0,k8_setfam_1(sK0,sK1)) != iProver_top ),
% 2.41/0.97      inference(light_normalisation,[status(thm)],[c_3735,c_2647]) ).
% 2.41/0.97  
% 2.41/0.97  cnf(c_3987,plain,
% 2.41/0.97      ( r1_tarski(sK0,k8_setfam_1(sK0,k1_xboole_0)) != iProver_top ),
% 2.41/0.97      inference(demodulation,[status(thm)],[c_3984,c_3741]) ).
% 2.41/0.97  
% 2.41/0.97  cnf(c_3999,plain,
% 2.41/0.97      ( r1_tarski(sK0,sK0) != iProver_top ),
% 2.41/0.97      inference(light_normalisation,[status(thm)],[c_3987,c_2647]) ).
% 2.41/0.97  
% 2.41/0.97  cnf(c_782,plain,
% 2.41/0.97      ( r1_tarski(X0,X0) = iProver_top ),
% 2.41/0.97      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.41/0.97  
% 2.41/0.97  cnf(c_4321,plain,
% 2.41/0.97      ( $false ),
% 2.41/0.97      inference(forward_subsumption_resolution,[status(thm)],[c_3999,c_782]) ).
% 2.41/0.97  
% 2.41/0.97  
% 2.41/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 2.41/0.97  
% 2.41/0.97  ------                               Statistics
% 2.41/0.97  
% 2.41/0.97  ------ General
% 2.41/0.97  
% 2.41/0.97  abstr_ref_over_cycles:                  0
% 2.41/0.97  abstr_ref_under_cycles:                 0
% 2.41/0.97  gc_basic_clause_elim:                   0
% 2.41/0.97  forced_gc_time:                         0
% 2.41/0.97  parsing_time:                           0.008
% 2.41/0.97  unif_index_cands_time:                  0.
% 2.41/0.97  unif_index_add_time:                    0.
% 2.41/0.97  orderings_time:                         0.
% 2.41/0.97  out_proof_time:                         0.008
% 2.41/0.97  total_time:                             0.143
% 2.41/0.97  num_of_symbols:                         43
% 2.41/0.97  num_of_terms:                           2619
% 2.41/0.97  
% 2.41/0.97  ------ Preprocessing
% 2.41/0.97  
% 2.41/0.97  num_of_splits:                          0
% 2.41/0.97  num_of_split_atoms:                     0
% 2.41/0.97  num_of_reused_defs:                     0
% 2.41/0.97  num_eq_ax_congr_red:                    10
% 2.41/0.97  num_of_sem_filtered_clauses:            1
% 2.41/0.97  num_of_subtypes:                        0
% 2.41/0.97  monotx_restored_types:                  0
% 2.41/0.97  sat_num_of_epr_types:                   0
% 2.41/0.97  sat_num_of_non_cyclic_types:            0
% 2.41/0.97  sat_guarded_non_collapsed_types:        0
% 2.41/0.97  num_pure_diseq_elim:                    0
% 2.41/0.97  simp_replaced_by:                       0
% 2.41/0.97  res_preprocessed:                       81
% 2.41/0.97  prep_upred:                             0
% 2.41/0.97  prep_unflattend:                        3
% 2.41/0.97  smt_new_axioms:                         0
% 2.41/0.97  pred_elim_cands:                        3
% 2.41/0.97  pred_elim:                              1
% 2.41/0.97  pred_elim_cl:                           2
% 2.41/0.97  pred_elim_cycles:                       3
% 2.41/0.97  merged_defs:                            8
% 2.41/0.97  merged_defs_ncl:                        0
% 2.41/0.97  bin_hyper_res:                          9
% 2.41/0.97  prep_cycles:                            4
% 2.41/0.97  pred_elim_time:                         0.
% 2.41/0.97  splitting_time:                         0.
% 2.41/0.97  sem_filter_time:                        0.
% 2.41/0.97  monotx_time:                            0.001
% 2.41/0.97  subtype_inf_time:                       0.
% 2.41/0.97  
% 2.41/0.97  ------ Problem properties
% 2.41/0.97  
% 2.41/0.97  clauses:                                16
% 2.41/0.97  conjectures:                            4
% 2.41/0.97  epr:                                    6
% 2.41/0.97  horn:                                   14
% 2.41/0.97  ground:                                 5
% 2.41/0.97  unary:                                  6
% 2.41/0.97  binary:                                 6
% 2.41/0.97  lits:                                   30
% 2.41/0.97  lits_eq:                                7
% 2.41/0.97  fd_pure:                                0
% 2.41/0.97  fd_pseudo:                              0
% 2.41/0.97  fd_cond:                                3
% 2.41/0.97  fd_pseudo_cond:                         1
% 2.41/0.97  ac_symbols:                             0
% 2.41/0.97  
% 2.41/0.97  ------ Propositional Solver
% 2.41/0.97  
% 2.41/0.97  prop_solver_calls:                      30
% 2.41/0.97  prop_fast_solver_calls:                 472
% 2.41/0.97  smt_solver_calls:                       0
% 2.41/0.97  smt_fast_solver_calls:                  0
% 2.41/0.97  prop_num_of_clauses:                    1398
% 2.41/0.97  prop_preprocess_simplified:             3900
% 2.41/0.97  prop_fo_subsumed:                       11
% 2.41/0.97  prop_solver_time:                       0.
% 2.41/0.97  smt_solver_time:                        0.
% 2.41/0.97  smt_fast_solver_time:                   0.
% 2.41/0.97  prop_fast_solver_time:                  0.
% 2.41/0.97  prop_unsat_core_time:                   0.
% 2.41/0.97  
% 2.41/0.97  ------ QBF
% 2.41/0.97  
% 2.41/0.97  qbf_q_res:                              0
% 2.41/0.97  qbf_num_tautologies:                    0
% 2.41/0.97  qbf_prep_cycles:                        0
% 2.41/0.97  
% 2.41/0.97  ------ BMC1
% 2.41/0.97  
% 2.41/0.97  bmc1_current_bound:                     -1
% 2.41/0.97  bmc1_last_solved_bound:                 -1
% 2.41/0.97  bmc1_unsat_core_size:                   -1
% 2.41/0.97  bmc1_unsat_core_parents_size:           -1
% 2.41/0.97  bmc1_merge_next_fun:                    0
% 2.41/0.97  bmc1_unsat_core_clauses_time:           0.
% 2.41/0.97  
% 2.41/0.97  ------ Instantiation
% 2.41/0.97  
% 2.41/0.97  inst_num_of_clauses:                    458
% 2.41/0.97  inst_num_in_passive:                    220
% 2.41/0.97  inst_num_in_active:                     224
% 2.41/0.97  inst_num_in_unprocessed:                14
% 2.41/0.97  inst_num_of_loops:                      290
% 2.41/0.97  inst_num_of_learning_restarts:          0
% 2.41/0.97  inst_num_moves_active_passive:          62
% 2.41/0.97  inst_lit_activity:                      0
% 2.41/0.97  inst_lit_activity_moves:                0
% 2.41/0.97  inst_num_tautologies:                   0
% 2.41/0.97  inst_num_prop_implied:                  0
% 2.41/0.97  inst_num_existing_simplified:           0
% 2.41/0.97  inst_num_eq_res_simplified:             0
% 2.41/0.97  inst_num_child_elim:                    0
% 2.41/0.97  inst_num_of_dismatching_blockings:      265
% 2.41/0.97  inst_num_of_non_proper_insts:           660
% 2.41/0.97  inst_num_of_duplicates:                 0
% 2.41/0.97  inst_inst_num_from_inst_to_res:         0
% 2.41/0.97  inst_dismatching_checking_time:         0.
% 2.41/0.97  
% 2.41/0.97  ------ Resolution
% 2.41/0.97  
% 2.41/0.97  res_num_of_clauses:                     0
% 2.41/0.97  res_num_in_passive:                     0
% 2.41/0.97  res_num_in_active:                      0
% 2.41/0.97  res_num_of_loops:                       85
% 2.41/0.97  res_forward_subset_subsumed:            88
% 2.41/0.97  res_backward_subset_subsumed:           0
% 2.41/0.97  res_forward_subsumed:                   0
% 2.41/0.97  res_backward_subsumed:                  0
% 2.41/0.97  res_forward_subsumption_resolution:     0
% 2.41/0.97  res_backward_subsumption_resolution:    0
% 2.41/0.97  res_clause_to_clause_subsumption:       211
% 2.41/0.97  res_orphan_elimination:                 0
% 2.41/0.97  res_tautology_del:                      61
% 2.41/0.97  res_num_eq_res_simplified:              0
% 2.41/0.97  res_num_sel_changes:                    0
% 2.41/0.97  res_moves_from_active_to_pass:          0
% 2.41/0.97  
% 2.41/0.97  ------ Superposition
% 2.41/0.97  
% 2.41/0.97  sup_time_total:                         0.
% 2.41/0.97  sup_time_generating:                    0.
% 2.41/0.97  sup_time_sim_full:                      0.
% 2.41/0.97  sup_time_sim_immed:                     0.
% 2.41/0.97  
% 2.41/0.97  sup_num_of_clauses:                     44
% 2.41/0.97  sup_num_in_active:                      28
% 2.41/0.97  sup_num_in_passive:                     16
% 2.41/0.97  sup_num_of_loops:                       57
% 2.41/0.97  sup_fw_superposition:                   43
% 2.41/0.97  sup_bw_superposition:                   46
% 2.41/0.97  sup_immediate_simplified:               19
% 2.41/0.97  sup_given_eliminated:                   1
% 2.41/0.97  comparisons_done:                       0
% 2.41/0.97  comparisons_avoided:                    13
% 2.41/0.97  
% 2.41/0.97  ------ Simplifications
% 2.41/0.97  
% 2.41/0.97  
% 2.41/0.97  sim_fw_subset_subsumed:                 9
% 2.41/0.97  sim_bw_subset_subsumed:                 13
% 2.41/0.97  sim_fw_subsumed:                        3
% 2.41/0.97  sim_bw_subsumed:                        0
% 2.41/0.97  sim_fw_subsumption_res:                 1
% 2.41/0.97  sim_bw_subsumption_res:                 0
% 2.41/0.97  sim_tautology_del:                      3
% 2.41/0.97  sim_eq_tautology_del:                   9
% 2.41/0.97  sim_eq_res_simp:                        0
% 2.41/0.97  sim_fw_demodulated:                     0
% 2.41/0.97  sim_bw_demodulated:                     22
% 2.41/0.97  sim_light_normalised:                   12
% 2.41/0.97  sim_joinable_taut:                      0
% 2.41/0.97  sim_joinable_simp:                      0
% 2.41/0.97  sim_ac_normalised:                      0
% 2.41/0.97  sim_smt_subsumption:                    0
% 2.41/0.97  
%------------------------------------------------------------------------------
