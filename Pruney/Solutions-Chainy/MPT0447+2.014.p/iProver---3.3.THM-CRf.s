%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:43:11 EST 2020

% Result     : Theorem 11.88s
% Output     : CNFRefutation 11.88s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 248 expanded)
%              Number of clauses        :   58 (  91 expanded)
%              Number of leaves         :   15 (  55 expanded)
%              Depth                    :   16
%              Number of atoms          :  245 ( 694 expanded)
%              Number of equality atoms :   80 ( 130 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f23,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_tarski(X0,X1)
             => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f37])).

fof(f58,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
     => ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(sK6))
        & r1_tarski(X0,sK6)
        & v1_relat_1(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
            & r1_tarski(X0,X1)
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(sK5),k3_relat_1(X1))
          & r1_tarski(sK5,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,
    ( ~ r1_tarski(k3_relat_1(sK5),k3_relat_1(sK6))
    & r1_tarski(sK5,sK6)
    & v1_relat_1(sK6)
    & v1_relat_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f38,f58,f57])).

fof(f96,plain,(
    v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f59])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f92,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f48])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f116,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f71])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f15,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f83,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k6_subset_1(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(definition_unfolding,[],[f80,f83])).

fof(f98,plain,(
    r1_tarski(sK5,sK6) ),
    inference(cnf_transformation,[],[f59])).

fof(f22,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f95,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f87,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f86,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f97,plain,(
    v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f59])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k6_subset_1(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f81,f83])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f94,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f99,plain,(
    ~ r1_tarski(k3_relat_1(sK5),k3_relat_1(sK6)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_37,negated_conjecture,
    ( v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1439,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_30,plain,
    ( ~ v1_relat_1(X0)
    | k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1444,plain,
    ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_3328,plain,
    ( k2_xboole_0(k1_relat_1(sK5),k2_relat_1(sK5)) = k3_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_1439,c_1444])).

cnf(c_11,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_1457,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_20,plain,
    ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
    | r1_tarski(k6_subset_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_1450,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
    | r1_tarski(k6_subset_1(X0,X1),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_9370,plain,
    ( r1_tarski(k6_subset_1(k2_xboole_0(X0,X1),X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1457,c_1450])).

cnf(c_59343,plain,
    ( r1_tarski(k6_subset_1(k3_relat_1(sK5),k1_relat_1(sK5)),k2_relat_1(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3328,c_9370])).

cnf(c_35,negated_conjecture,
    ( r1_tarski(sK5,sK6) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1441,plain,
    ( r1_tarski(sK5,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_32,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_23,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_202,plain,
    ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_32,c_25,c_23])).

cnf(c_203,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(renaming,[status(thm)],[c_202])).

cnf(c_1437,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_203])).

cnf(c_15,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1454,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2782,plain,
    ( k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(X1)
    | r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1437,c_1454])).

cnf(c_19109,plain,
    ( k2_xboole_0(k2_relat_1(sK5),k2_relat_1(sK6)) = k2_relat_1(sK6)
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1441,c_2782])).

cnf(c_36,negated_conjecture,
    ( v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_39,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_19932,plain,
    ( k2_xboole_0(k2_relat_1(sK5),k2_relat_1(sK6)) = k2_relat_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_19109,c_39])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_13,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1456,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k2_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_4370,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k2_xboole_0(X1,X2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_1456])).

cnf(c_19942,plain,
    ( r1_tarski(X0,k2_relat_1(sK6)) = iProver_top
    | r1_tarski(X0,k2_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_19932,c_4370])).

cnf(c_59645,plain,
    ( r1_tarski(k6_subset_1(k3_relat_1(sK5),k1_relat_1(sK5)),k2_relat_1(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_59343,c_19942])).

cnf(c_1440,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_3327,plain,
    ( k2_xboole_0(k1_relat_1(sK6),k2_relat_1(sK6)) = k3_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_1440,c_1444])).

cnf(c_4378,plain,
    ( r1_tarski(X0,k3_relat_1(sK6)) = iProver_top
    | r1_tarski(X0,k2_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3327,c_1456])).

cnf(c_60578,plain,
    ( r1_tarski(k6_subset_1(k3_relat_1(sK5),k1_relat_1(sK5)),k3_relat_1(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_59645,c_4378])).

cnf(c_21,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2))
    | ~ r1_tarski(k6_subset_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_1449,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2)) = iProver_top
    | r1_tarski(k6_subset_1(X0,X1),X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_60656,plain,
    ( r1_tarski(k3_relat_1(sK5),k2_xboole_0(k1_relat_1(sK5),k3_relat_1(sK6))) = iProver_top ),
    inference(superposition,[status(thm)],[c_60578,c_1449])).

cnf(c_14,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1455,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_4322,plain,
    ( r1_tarski(k3_relat_1(sK5),X0) != iProver_top
    | r1_tarski(k1_relat_1(sK5),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3328,c_1455])).

cnf(c_4653,plain,
    ( r1_tarski(k3_relat_1(sK5),X0) != iProver_top
    | r1_tarski(k1_relat_1(sK5),k2_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1456,c_4322])).

cnf(c_17520,plain,
    ( r1_tarski(k3_relat_1(sK5),k2_relat_1(sK6)) != iProver_top
    | r1_tarski(k1_relat_1(sK5),k3_relat_1(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3327,c_4653])).

cnf(c_40,plain,
    ( r1_tarski(sK5,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_33,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_197,plain,
    ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_33,c_25,c_23])).

cnf(c_198,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(renaming,[status(thm)],[c_197])).

cnf(c_1438,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_198])).

cnf(c_7075,plain,
    ( r1_tarski(X0,k3_relat_1(sK6)) = iProver_top
    | r1_tarski(X0,k1_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3327,c_4370])).

cnf(c_8436,plain,
    ( r1_tarski(X0,sK6) != iProver_top
    | r1_tarski(k1_relat_1(X0),k3_relat_1(sK6)) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1438,c_7075])).

cnf(c_8452,plain,
    ( r1_tarski(k1_relat_1(sK5),k3_relat_1(sK6)) = iProver_top
    | r1_tarski(sK5,sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_8436])).

cnf(c_17697,plain,
    ( r1_tarski(k1_relat_1(sK5),k3_relat_1(sK6)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_17520,c_39,c_40,c_8452])).

cnf(c_17704,plain,
    ( k2_xboole_0(k1_relat_1(sK5),k3_relat_1(sK6)) = k3_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_17697,c_1454])).

cnf(c_60664,plain,
    ( r1_tarski(k3_relat_1(sK5),k3_relat_1(sK6)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_60656,c_17704])).

cnf(c_34,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(sK5),k3_relat_1(sK6)) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_41,plain,
    ( r1_tarski(k3_relat_1(sK5),k3_relat_1(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_60664,c_41])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:31:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 11.88/1.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.88/1.99  
% 11.88/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.88/1.99  
% 11.88/1.99  ------  iProver source info
% 11.88/1.99  
% 11.88/1.99  git: date: 2020-06-30 10:37:57 +0100
% 11.88/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.88/1.99  git: non_committed_changes: false
% 11.88/1.99  git: last_make_outside_of_git: false
% 11.88/1.99  
% 11.88/1.99  ------ 
% 11.88/1.99  
% 11.88/1.99  ------ Input Options
% 11.88/1.99  
% 11.88/1.99  --out_options                           all
% 11.88/1.99  --tptp_safe_out                         true
% 11.88/1.99  --problem_path                          ""
% 11.88/1.99  --include_path                          ""
% 11.88/1.99  --clausifier                            res/vclausify_rel
% 11.88/1.99  --clausifier_options                    --mode clausify
% 11.88/1.99  --stdin                                 false
% 11.88/1.99  --stats_out                             all
% 11.88/1.99  
% 11.88/1.99  ------ General Options
% 11.88/1.99  
% 11.88/1.99  --fof                                   false
% 11.88/1.99  --time_out_real                         305.
% 11.88/1.99  --time_out_virtual                      -1.
% 11.88/1.99  --symbol_type_check                     false
% 11.88/1.99  --clausify_out                          false
% 11.88/1.99  --sig_cnt_out                           false
% 11.88/1.99  --trig_cnt_out                          false
% 11.88/1.99  --trig_cnt_out_tolerance                1.
% 11.88/1.99  --trig_cnt_out_sk_spl                   false
% 11.88/1.99  --abstr_cl_out                          false
% 11.88/1.99  
% 11.88/1.99  ------ Global Options
% 11.88/1.99  
% 11.88/1.99  --schedule                              default
% 11.88/1.99  --add_important_lit                     false
% 11.88/1.99  --prop_solver_per_cl                    1000
% 11.88/1.99  --min_unsat_core                        false
% 11.88/1.99  --soft_assumptions                      false
% 11.88/1.99  --soft_lemma_size                       3
% 11.88/1.99  --prop_impl_unit_size                   0
% 11.88/1.99  --prop_impl_unit                        []
% 11.88/1.99  --share_sel_clauses                     true
% 11.88/1.99  --reset_solvers                         false
% 11.88/1.99  --bc_imp_inh                            [conj_cone]
% 11.88/1.99  --conj_cone_tolerance                   3.
% 11.88/1.99  --extra_neg_conj                        none
% 11.88/1.99  --large_theory_mode                     true
% 11.88/1.99  --prolific_symb_bound                   200
% 11.88/1.99  --lt_threshold                          2000
% 11.88/1.99  --clause_weak_htbl                      true
% 11.88/1.99  --gc_record_bc_elim                     false
% 11.88/1.99  
% 11.88/1.99  ------ Preprocessing Options
% 11.88/1.99  
% 11.88/1.99  --preprocessing_flag                    true
% 11.88/1.99  --time_out_prep_mult                    0.1
% 11.88/1.99  --splitting_mode                        input
% 11.88/1.99  --splitting_grd                         true
% 11.88/1.99  --splitting_cvd                         false
% 11.88/1.99  --splitting_cvd_svl                     false
% 11.88/1.99  --splitting_nvd                         32
% 11.88/1.99  --sub_typing                            true
% 11.88/1.99  --prep_gs_sim                           true
% 11.88/1.99  --prep_unflatten                        true
% 11.88/1.99  --prep_res_sim                          true
% 11.88/1.99  --prep_upred                            true
% 11.88/1.99  --prep_sem_filter                       exhaustive
% 11.88/1.99  --prep_sem_filter_out                   false
% 11.88/1.99  --pred_elim                             true
% 11.88/1.99  --res_sim_input                         true
% 11.88/1.99  --eq_ax_congr_red                       true
% 11.88/1.99  --pure_diseq_elim                       true
% 11.88/1.99  --brand_transform                       false
% 11.88/1.99  --non_eq_to_eq                          false
% 11.88/1.99  --prep_def_merge                        true
% 11.88/1.99  --prep_def_merge_prop_impl              false
% 11.88/1.99  --prep_def_merge_mbd                    true
% 11.88/1.99  --prep_def_merge_tr_red                 false
% 11.88/1.99  --prep_def_merge_tr_cl                  false
% 11.88/1.99  --smt_preprocessing                     true
% 11.88/1.99  --smt_ac_axioms                         fast
% 11.88/1.99  --preprocessed_out                      false
% 11.88/1.99  --preprocessed_stats                    false
% 11.88/1.99  
% 11.88/1.99  ------ Abstraction refinement Options
% 11.88/1.99  
% 11.88/1.99  --abstr_ref                             []
% 11.88/1.99  --abstr_ref_prep                        false
% 11.88/1.99  --abstr_ref_until_sat                   false
% 11.88/1.99  --abstr_ref_sig_restrict                funpre
% 11.88/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.88/1.99  --abstr_ref_under                       []
% 11.88/1.99  
% 11.88/1.99  ------ SAT Options
% 11.88/1.99  
% 11.88/1.99  --sat_mode                              false
% 11.88/1.99  --sat_fm_restart_options                ""
% 11.88/1.99  --sat_gr_def                            false
% 11.88/1.99  --sat_epr_types                         true
% 11.88/1.99  --sat_non_cyclic_types                  false
% 11.88/1.99  --sat_finite_models                     false
% 11.88/1.99  --sat_fm_lemmas                         false
% 11.88/1.99  --sat_fm_prep                           false
% 11.88/1.99  --sat_fm_uc_incr                        true
% 11.88/1.99  --sat_out_model                         small
% 11.88/1.99  --sat_out_clauses                       false
% 11.88/1.99  
% 11.88/1.99  ------ QBF Options
% 11.88/1.99  
% 11.88/1.99  --qbf_mode                              false
% 11.88/1.99  --qbf_elim_univ                         false
% 11.88/1.99  --qbf_dom_inst                          none
% 11.88/1.99  --qbf_dom_pre_inst                      false
% 11.88/1.99  --qbf_sk_in                             false
% 11.88/1.99  --qbf_pred_elim                         true
% 11.88/1.99  --qbf_split                             512
% 11.88/1.99  
% 11.88/1.99  ------ BMC1 Options
% 11.88/1.99  
% 11.88/1.99  --bmc1_incremental                      false
% 11.88/1.99  --bmc1_axioms                           reachable_all
% 11.88/1.99  --bmc1_min_bound                        0
% 11.88/1.99  --bmc1_max_bound                        -1
% 11.88/1.99  --bmc1_max_bound_default                -1
% 11.88/1.99  --bmc1_symbol_reachability              true
% 11.88/1.99  --bmc1_property_lemmas                  false
% 11.88/1.99  --bmc1_k_induction                      false
% 11.88/1.99  --bmc1_non_equiv_states                 false
% 11.88/1.99  --bmc1_deadlock                         false
% 11.88/1.99  --bmc1_ucm                              false
% 11.88/1.99  --bmc1_add_unsat_core                   none
% 11.88/1.99  --bmc1_unsat_core_children              false
% 11.88/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.88/1.99  --bmc1_out_stat                         full
% 11.88/1.99  --bmc1_ground_init                      false
% 11.88/1.99  --bmc1_pre_inst_next_state              false
% 11.88/1.99  --bmc1_pre_inst_state                   false
% 11.88/1.99  --bmc1_pre_inst_reach_state             false
% 11.88/1.99  --bmc1_out_unsat_core                   false
% 11.88/1.99  --bmc1_aig_witness_out                  false
% 11.88/1.99  --bmc1_verbose                          false
% 11.88/1.99  --bmc1_dump_clauses_tptp                false
% 11.88/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.88/1.99  --bmc1_dump_file                        -
% 11.88/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.88/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.88/1.99  --bmc1_ucm_extend_mode                  1
% 11.88/1.99  --bmc1_ucm_init_mode                    2
% 11.88/1.99  --bmc1_ucm_cone_mode                    none
% 11.88/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.88/1.99  --bmc1_ucm_relax_model                  4
% 11.88/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.88/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.88/1.99  --bmc1_ucm_layered_model                none
% 11.88/1.99  --bmc1_ucm_max_lemma_size               10
% 11.88/1.99  
% 11.88/1.99  ------ AIG Options
% 11.88/1.99  
% 11.88/1.99  --aig_mode                              false
% 11.88/1.99  
% 11.88/1.99  ------ Instantiation Options
% 11.88/1.99  
% 11.88/1.99  --instantiation_flag                    true
% 11.88/1.99  --inst_sos_flag                         false
% 11.88/1.99  --inst_sos_phase                        true
% 11.88/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.88/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.88/1.99  --inst_lit_sel_side                     num_symb
% 11.88/1.99  --inst_solver_per_active                1400
% 11.88/1.99  --inst_solver_calls_frac                1.
% 11.88/1.99  --inst_passive_queue_type               priority_queues
% 11.88/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.88/1.99  --inst_passive_queues_freq              [25;2]
% 11.88/1.99  --inst_dismatching                      true
% 11.88/1.99  --inst_eager_unprocessed_to_passive     true
% 11.88/1.99  --inst_prop_sim_given                   true
% 11.88/1.99  --inst_prop_sim_new                     false
% 11.88/1.99  --inst_subs_new                         false
% 11.88/1.99  --inst_eq_res_simp                      false
% 11.88/1.99  --inst_subs_given                       false
% 11.88/1.99  --inst_orphan_elimination               true
% 11.88/1.99  --inst_learning_loop_flag               true
% 11.88/1.99  --inst_learning_start                   3000
% 11.88/1.99  --inst_learning_factor                  2
% 11.88/1.99  --inst_start_prop_sim_after_learn       3
% 11.88/1.99  --inst_sel_renew                        solver
% 11.88/1.99  --inst_lit_activity_flag                true
% 11.88/1.99  --inst_restr_to_given                   false
% 11.88/1.99  --inst_activity_threshold               500
% 11.88/1.99  --inst_out_proof                        true
% 11.88/1.99  
% 11.88/1.99  ------ Resolution Options
% 11.88/1.99  
% 11.88/1.99  --resolution_flag                       true
% 11.88/1.99  --res_lit_sel                           adaptive
% 11.88/1.99  --res_lit_sel_side                      none
% 11.88/1.99  --res_ordering                          kbo
% 11.88/1.99  --res_to_prop_solver                    active
% 11.88/1.99  --res_prop_simpl_new                    false
% 11.88/1.99  --res_prop_simpl_given                  true
% 11.88/1.99  --res_passive_queue_type                priority_queues
% 11.88/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.88/1.99  --res_passive_queues_freq               [15;5]
% 11.88/1.99  --res_forward_subs                      full
% 11.88/1.99  --res_backward_subs                     full
% 11.88/1.99  --res_forward_subs_resolution           true
% 11.88/1.99  --res_backward_subs_resolution          true
% 11.88/1.99  --res_orphan_elimination                true
% 11.88/1.99  --res_time_limit                        2.
% 11.88/1.99  --res_out_proof                         true
% 11.88/1.99  
% 11.88/1.99  ------ Superposition Options
% 11.88/1.99  
% 11.88/1.99  --superposition_flag                    true
% 11.88/1.99  --sup_passive_queue_type                priority_queues
% 11.88/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.88/1.99  --sup_passive_queues_freq               [8;1;4]
% 11.88/1.99  --demod_completeness_check              fast
% 11.88/1.99  --demod_use_ground                      true
% 11.88/1.99  --sup_to_prop_solver                    passive
% 11.88/1.99  --sup_prop_simpl_new                    true
% 11.88/1.99  --sup_prop_simpl_given                  true
% 11.88/1.99  --sup_fun_splitting                     false
% 11.88/1.99  --sup_smt_interval                      50000
% 11.88/1.99  
% 11.88/1.99  ------ Superposition Simplification Setup
% 11.88/1.99  
% 11.88/1.99  --sup_indices_passive                   []
% 11.88/1.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.88/1.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.88/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.88/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.88/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.88/1.99  --sup_full_bw                           [BwDemod]
% 11.88/1.99  --sup_immed_triv                        [TrivRules]
% 11.88/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.88/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.88/1.99  --sup_immed_bw_main                     []
% 11.88/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.88/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.88/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.88/1.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.88/1.99  
% 11.88/1.99  ------ Combination Options
% 11.88/1.99  
% 11.88/1.99  --comb_res_mult                         3
% 11.88/1.99  --comb_sup_mult                         2
% 11.88/1.99  --comb_inst_mult                        10
% 11.88/1.99  
% 11.88/1.99  ------ Debug Options
% 11.88/1.99  
% 11.88/1.99  --dbg_backtrace                         false
% 11.88/1.99  --dbg_dump_prop_clauses                 false
% 11.88/1.99  --dbg_dump_prop_clauses_file            -
% 11.88/1.99  --dbg_out_stat                          false
% 11.88/1.99  ------ Parsing...
% 11.88/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.88/1.99  
% 11.88/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 11.88/1.99  
% 11.88/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.88/1.99  
% 11.88/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.88/1.99  ------ Proving...
% 11.88/1.99  ------ Problem Properties 
% 11.88/1.99  
% 11.88/1.99  
% 11.88/1.99  clauses                                 35
% 11.88/1.99  conjectures                             4
% 11.88/1.99  EPR                                     8
% 11.88/1.99  Horn                                    29
% 11.88/1.99  unary                                   10
% 11.88/1.99  binary                                  13
% 11.88/1.99  lits                                    73
% 11.88/1.99  lits eq                                 12
% 11.88/1.99  fd_pure                                 0
% 11.88/1.99  fd_pseudo                               0
% 11.88/1.99  fd_cond                                 0
% 11.88/1.99  fd_pseudo_cond                          6
% 11.88/1.99  AC symbols                              0
% 11.88/1.99  
% 11.88/1.99  ------ Schedule dynamic 5 is on 
% 11.88/1.99  
% 11.88/1.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.88/1.99  
% 11.88/1.99  
% 11.88/1.99  ------ 
% 11.88/1.99  Current options:
% 11.88/1.99  ------ 
% 11.88/1.99  
% 11.88/1.99  ------ Input Options
% 11.88/1.99  
% 11.88/1.99  --out_options                           all
% 11.88/1.99  --tptp_safe_out                         true
% 11.88/1.99  --problem_path                          ""
% 11.88/1.99  --include_path                          ""
% 11.88/1.99  --clausifier                            res/vclausify_rel
% 11.88/1.99  --clausifier_options                    --mode clausify
% 11.88/1.99  --stdin                                 false
% 11.88/1.99  --stats_out                             all
% 11.88/1.99  
% 11.88/1.99  ------ General Options
% 11.88/1.99  
% 11.88/1.99  --fof                                   false
% 11.88/1.99  --time_out_real                         305.
% 11.88/1.99  --time_out_virtual                      -1.
% 11.88/1.99  --symbol_type_check                     false
% 11.88/1.99  --clausify_out                          false
% 11.88/1.99  --sig_cnt_out                           false
% 11.88/1.99  --trig_cnt_out                          false
% 11.88/1.99  --trig_cnt_out_tolerance                1.
% 11.88/1.99  --trig_cnt_out_sk_spl                   false
% 11.88/1.99  --abstr_cl_out                          false
% 11.88/1.99  
% 11.88/1.99  ------ Global Options
% 11.88/1.99  
% 11.88/1.99  --schedule                              default
% 11.88/1.99  --add_important_lit                     false
% 11.88/1.99  --prop_solver_per_cl                    1000
% 11.88/1.99  --min_unsat_core                        false
% 11.88/1.99  --soft_assumptions                      false
% 11.88/1.99  --soft_lemma_size                       3
% 11.88/1.99  --prop_impl_unit_size                   0
% 11.88/1.99  --prop_impl_unit                        []
% 11.88/1.99  --share_sel_clauses                     true
% 11.88/1.99  --reset_solvers                         false
% 11.88/1.99  --bc_imp_inh                            [conj_cone]
% 11.88/1.99  --conj_cone_tolerance                   3.
% 11.88/1.99  --extra_neg_conj                        none
% 11.88/1.99  --large_theory_mode                     true
% 11.88/1.99  --prolific_symb_bound                   200
% 11.88/1.99  --lt_threshold                          2000
% 11.88/1.99  --clause_weak_htbl                      true
% 11.88/1.99  --gc_record_bc_elim                     false
% 11.88/1.99  
% 11.88/1.99  ------ Preprocessing Options
% 11.88/1.99  
% 11.88/1.99  --preprocessing_flag                    true
% 11.88/1.99  --time_out_prep_mult                    0.1
% 11.88/1.99  --splitting_mode                        input
% 11.88/1.99  --splitting_grd                         true
% 11.88/1.99  --splitting_cvd                         false
% 11.88/1.99  --splitting_cvd_svl                     false
% 11.88/1.99  --splitting_nvd                         32
% 11.88/1.99  --sub_typing                            true
% 11.88/1.99  --prep_gs_sim                           true
% 11.88/1.99  --prep_unflatten                        true
% 11.88/1.99  --prep_res_sim                          true
% 11.88/1.99  --prep_upred                            true
% 11.88/1.99  --prep_sem_filter                       exhaustive
% 11.88/1.99  --prep_sem_filter_out                   false
% 11.88/1.99  --pred_elim                             true
% 11.88/1.99  --res_sim_input                         true
% 11.88/1.99  --eq_ax_congr_red                       true
% 11.88/1.99  --pure_diseq_elim                       true
% 11.88/1.99  --brand_transform                       false
% 11.88/1.99  --non_eq_to_eq                          false
% 11.88/1.99  --prep_def_merge                        true
% 11.88/1.99  --prep_def_merge_prop_impl              false
% 11.88/1.99  --prep_def_merge_mbd                    true
% 11.88/1.99  --prep_def_merge_tr_red                 false
% 11.88/1.99  --prep_def_merge_tr_cl                  false
% 11.88/1.99  --smt_preprocessing                     true
% 11.88/1.99  --smt_ac_axioms                         fast
% 11.88/1.99  --preprocessed_out                      false
% 11.88/1.99  --preprocessed_stats                    false
% 11.88/1.99  
% 11.88/1.99  ------ Abstraction refinement Options
% 11.88/1.99  
% 11.88/1.99  --abstr_ref                             []
% 11.88/1.99  --abstr_ref_prep                        false
% 11.88/1.99  --abstr_ref_until_sat                   false
% 11.88/1.99  --abstr_ref_sig_restrict                funpre
% 11.88/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.88/1.99  --abstr_ref_under                       []
% 11.88/1.99  
% 11.88/1.99  ------ SAT Options
% 11.88/1.99  
% 11.88/1.99  --sat_mode                              false
% 11.88/1.99  --sat_fm_restart_options                ""
% 11.88/1.99  --sat_gr_def                            false
% 11.88/1.99  --sat_epr_types                         true
% 11.88/1.99  --sat_non_cyclic_types                  false
% 11.88/1.99  --sat_finite_models                     false
% 11.88/1.99  --sat_fm_lemmas                         false
% 11.88/1.99  --sat_fm_prep                           false
% 11.88/1.99  --sat_fm_uc_incr                        true
% 11.88/1.99  --sat_out_model                         small
% 11.88/1.99  --sat_out_clauses                       false
% 11.88/1.99  
% 11.88/1.99  ------ QBF Options
% 11.88/1.99  
% 11.88/1.99  --qbf_mode                              false
% 11.88/1.99  --qbf_elim_univ                         false
% 11.88/1.99  --qbf_dom_inst                          none
% 11.88/1.99  --qbf_dom_pre_inst                      false
% 11.88/1.99  --qbf_sk_in                             false
% 11.88/1.99  --qbf_pred_elim                         true
% 11.88/1.99  --qbf_split                             512
% 11.88/1.99  
% 11.88/1.99  ------ BMC1 Options
% 11.88/1.99  
% 11.88/1.99  --bmc1_incremental                      false
% 11.88/1.99  --bmc1_axioms                           reachable_all
% 11.88/1.99  --bmc1_min_bound                        0
% 11.88/1.99  --bmc1_max_bound                        -1
% 11.88/1.99  --bmc1_max_bound_default                -1
% 11.88/1.99  --bmc1_symbol_reachability              true
% 11.88/1.99  --bmc1_property_lemmas                  false
% 11.88/1.99  --bmc1_k_induction                      false
% 11.88/1.99  --bmc1_non_equiv_states                 false
% 11.88/1.99  --bmc1_deadlock                         false
% 11.88/1.99  --bmc1_ucm                              false
% 11.88/1.99  --bmc1_add_unsat_core                   none
% 11.88/1.99  --bmc1_unsat_core_children              false
% 11.88/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.88/1.99  --bmc1_out_stat                         full
% 11.88/1.99  --bmc1_ground_init                      false
% 11.88/1.99  --bmc1_pre_inst_next_state              false
% 11.88/1.99  --bmc1_pre_inst_state                   false
% 11.88/1.99  --bmc1_pre_inst_reach_state             false
% 11.88/1.99  --bmc1_out_unsat_core                   false
% 11.88/1.99  --bmc1_aig_witness_out                  false
% 11.88/1.99  --bmc1_verbose                          false
% 11.88/1.99  --bmc1_dump_clauses_tptp                false
% 11.88/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.88/1.99  --bmc1_dump_file                        -
% 11.88/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.88/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.88/1.99  --bmc1_ucm_extend_mode                  1
% 11.88/1.99  --bmc1_ucm_init_mode                    2
% 11.88/1.99  --bmc1_ucm_cone_mode                    none
% 11.88/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.88/1.99  --bmc1_ucm_relax_model                  4
% 11.88/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.88/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.88/1.99  --bmc1_ucm_layered_model                none
% 11.88/1.99  --bmc1_ucm_max_lemma_size               10
% 11.88/1.99  
% 11.88/1.99  ------ AIG Options
% 11.88/1.99  
% 11.88/1.99  --aig_mode                              false
% 11.88/1.99  
% 11.88/1.99  ------ Instantiation Options
% 11.88/1.99  
% 11.88/1.99  --instantiation_flag                    true
% 11.88/1.99  --inst_sos_flag                         false
% 11.88/1.99  --inst_sos_phase                        true
% 11.88/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.88/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.88/1.99  --inst_lit_sel_side                     none
% 11.88/1.99  --inst_solver_per_active                1400
% 11.88/1.99  --inst_solver_calls_frac                1.
% 11.88/1.99  --inst_passive_queue_type               priority_queues
% 11.88/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.88/1.99  --inst_passive_queues_freq              [25;2]
% 11.88/1.99  --inst_dismatching                      true
% 11.88/1.99  --inst_eager_unprocessed_to_passive     true
% 11.88/1.99  --inst_prop_sim_given                   true
% 11.88/1.99  --inst_prop_sim_new                     false
% 11.88/1.99  --inst_subs_new                         false
% 11.88/1.99  --inst_eq_res_simp                      false
% 11.88/1.99  --inst_subs_given                       false
% 11.88/1.99  --inst_orphan_elimination               true
% 11.88/1.99  --inst_learning_loop_flag               true
% 11.88/1.99  --inst_learning_start                   3000
% 11.88/1.99  --inst_learning_factor                  2
% 11.88/1.99  --inst_start_prop_sim_after_learn       3
% 11.88/1.99  --inst_sel_renew                        solver
% 11.88/1.99  --inst_lit_activity_flag                true
% 11.88/1.99  --inst_restr_to_given                   false
% 11.88/1.99  --inst_activity_threshold               500
% 11.88/1.99  --inst_out_proof                        true
% 11.88/1.99  
% 11.88/1.99  ------ Resolution Options
% 11.88/1.99  
% 11.88/1.99  --resolution_flag                       false
% 11.88/1.99  --res_lit_sel                           adaptive
% 11.88/1.99  --res_lit_sel_side                      none
% 11.88/1.99  --res_ordering                          kbo
% 11.88/1.99  --res_to_prop_solver                    active
% 11.88/1.99  --res_prop_simpl_new                    false
% 11.88/1.99  --res_prop_simpl_given                  true
% 11.88/1.99  --res_passive_queue_type                priority_queues
% 11.88/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.88/1.99  --res_passive_queues_freq               [15;5]
% 11.88/1.99  --res_forward_subs                      full
% 11.88/1.99  --res_backward_subs                     full
% 11.88/1.99  --res_forward_subs_resolution           true
% 11.88/1.99  --res_backward_subs_resolution          true
% 11.88/1.99  --res_orphan_elimination                true
% 11.88/1.99  --res_time_limit                        2.
% 11.88/1.99  --res_out_proof                         true
% 11.88/1.99  
% 11.88/1.99  ------ Superposition Options
% 11.88/1.99  
% 11.88/1.99  --superposition_flag                    true
% 11.88/1.99  --sup_passive_queue_type                priority_queues
% 11.88/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.88/1.99  --sup_passive_queues_freq               [8;1;4]
% 11.88/1.99  --demod_completeness_check              fast
% 11.88/1.99  --demod_use_ground                      true
% 11.88/1.99  --sup_to_prop_solver                    passive
% 11.88/1.99  --sup_prop_simpl_new                    true
% 11.88/1.99  --sup_prop_simpl_given                  true
% 11.88/1.99  --sup_fun_splitting                     false
% 11.88/1.99  --sup_smt_interval                      50000
% 11.88/1.99  
% 11.88/1.99  ------ Superposition Simplification Setup
% 11.88/1.99  
% 11.88/1.99  --sup_indices_passive                   []
% 11.88/1.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.88/1.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.88/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.88/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.88/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.88/1.99  --sup_full_bw                           [BwDemod]
% 11.88/1.99  --sup_immed_triv                        [TrivRules]
% 11.88/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.88/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.88/1.99  --sup_immed_bw_main                     []
% 11.88/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.88/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.88/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.88/1.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.88/1.99  
% 11.88/1.99  ------ Combination Options
% 11.88/1.99  
% 11.88/1.99  --comb_res_mult                         3
% 11.88/1.99  --comb_sup_mult                         2
% 11.88/1.99  --comb_inst_mult                        10
% 11.88/1.99  
% 11.88/1.99  ------ Debug Options
% 11.88/1.99  
% 11.88/1.99  --dbg_backtrace                         false
% 11.88/1.99  --dbg_dump_prop_clauses                 false
% 11.88/1.99  --dbg_dump_prop_clauses_file            -
% 11.88/1.99  --dbg_out_stat                          false
% 11.88/1.99  
% 11.88/1.99  
% 11.88/1.99  
% 11.88/1.99  
% 11.88/1.99  ------ Proving...
% 11.88/1.99  
% 11.88/1.99  
% 11.88/1.99  % SZS status Theorem for theBenchmark.p
% 11.88/1.99  
% 11.88/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 11.88/1.99  
% 11.88/1.99  fof(f23,conjecture,(
% 11.88/1.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 11.88/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.88/1.99  
% 11.88/1.99  fof(f24,negated_conjecture,(
% 11.88/1.99    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 11.88/1.99    inference(negated_conjecture,[],[f23])).
% 11.88/1.99  
% 11.88/1.99  fof(f37,plain,(
% 11.88/1.99    ? [X0] : (? [X1] : ((~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 11.88/1.99    inference(ennf_transformation,[],[f24])).
% 11.88/1.99  
% 11.88/1.99  fof(f38,plain,(
% 11.88/1.99    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 11.88/1.99    inference(flattening,[],[f37])).
% 11.88/1.99  
% 11.88/1.99  fof(f58,plain,(
% 11.88/1.99    ( ! [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) => (~r1_tarski(k3_relat_1(X0),k3_relat_1(sK6)) & r1_tarski(X0,sK6) & v1_relat_1(sK6))) )),
% 11.88/1.99    introduced(choice_axiom,[])).
% 11.88/1.99  
% 11.88/1.99  fof(f57,plain,(
% 11.88/1.99    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k3_relat_1(sK5),k3_relat_1(X1)) & r1_tarski(sK5,X1) & v1_relat_1(X1)) & v1_relat_1(sK5))),
% 11.88/1.99    introduced(choice_axiom,[])).
% 11.88/1.99  
% 11.88/1.99  fof(f59,plain,(
% 11.88/1.99    (~r1_tarski(k3_relat_1(sK5),k3_relat_1(sK6)) & r1_tarski(sK5,sK6) & v1_relat_1(sK6)) & v1_relat_1(sK5)),
% 11.88/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f38,f58,f57])).
% 11.88/1.99  
% 11.88/1.99  fof(f96,plain,(
% 11.88/1.99    v1_relat_1(sK5)),
% 11.88/1.99    inference(cnf_transformation,[],[f59])).
% 11.88/1.99  
% 11.88/1.99  fof(f20,axiom,(
% 11.88/1.99    ! [X0] : (v1_relat_1(X0) => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0))),
% 11.88/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.88/1.99  
% 11.88/1.99  fof(f33,plain,(
% 11.88/1.99    ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0))),
% 11.88/1.99    inference(ennf_transformation,[],[f20])).
% 11.88/1.99  
% 11.88/1.99  fof(f92,plain,(
% 11.88/1.99    ( ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 11.88/1.99    inference(cnf_transformation,[],[f33])).
% 11.88/1.99  
% 11.88/1.99  fof(f4,axiom,(
% 11.88/1.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.88/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.88/1.99  
% 11.88/1.99  fof(f48,plain,(
% 11.88/1.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.88/1.99    inference(nnf_transformation,[],[f4])).
% 11.88/1.99  
% 11.88/1.99  fof(f49,plain,(
% 11.88/1.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.88/1.99    inference(flattening,[],[f48])).
% 11.88/1.99  
% 11.88/1.99  fof(f71,plain,(
% 11.88/1.99    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 11.88/1.99    inference(cnf_transformation,[],[f49])).
% 11.88/1.99  
% 11.88/1.99  fof(f116,plain,(
% 11.88/1.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 11.88/1.99    inference(equality_resolution,[],[f71])).
% 11.88/1.99  
% 11.88/1.99  fof(f12,axiom,(
% 11.88/1.99    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 11.88/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.88/1.99  
% 11.88/1.99  fof(f30,plain,(
% 11.88/1.99    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 11.88/1.99    inference(ennf_transformation,[],[f12])).
% 11.88/1.99  
% 11.88/1.99  fof(f80,plain,(
% 11.88/1.99    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 11.88/1.99    inference(cnf_transformation,[],[f30])).
% 11.88/1.99  
% 11.88/1.99  fof(f15,axiom,(
% 11.88/1.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 11.88/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.88/1.99  
% 11.88/1.99  fof(f83,plain,(
% 11.88/1.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 11.88/1.99    inference(cnf_transformation,[],[f15])).
% 11.88/1.99  
% 11.88/1.99  fof(f110,plain,(
% 11.88/1.99    ( ! [X2,X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 11.88/1.99    inference(definition_unfolding,[],[f80,f83])).
% 11.88/1.99  
% 11.88/1.99  fof(f98,plain,(
% 11.88/1.99    r1_tarski(sK5,sK6)),
% 11.88/1.99    inference(cnf_transformation,[],[f59])).
% 11.88/1.99  
% 11.88/1.99  fof(f22,axiom,(
% 11.88/1.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 11.88/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.88/1.99  
% 11.88/1.99  fof(f35,plain,(
% 11.88/1.99    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 11.88/1.99    inference(ennf_transformation,[],[f22])).
% 11.88/1.99  
% 11.88/1.99  fof(f36,plain,(
% 11.88/1.99    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 11.88/1.99    inference(flattening,[],[f35])).
% 11.88/1.99  
% 11.88/1.99  fof(f95,plain,(
% 11.88/1.99    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 11.88/1.99    inference(cnf_transformation,[],[f36])).
% 11.88/1.99  
% 11.88/1.99  fof(f18,axiom,(
% 11.88/1.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 11.88/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.88/1.99  
% 11.88/1.99  fof(f32,plain,(
% 11.88/1.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 11.88/1.99    inference(ennf_transformation,[],[f18])).
% 11.88/1.99  
% 11.88/1.99  fof(f87,plain,(
% 11.88/1.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 11.88/1.99    inference(cnf_transformation,[],[f32])).
% 11.88/1.99  
% 11.88/1.99  fof(f17,axiom,(
% 11.88/1.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 11.88/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.88/1.99  
% 11.88/1.99  fof(f50,plain,(
% 11.88/1.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 11.88/1.99    inference(nnf_transformation,[],[f17])).
% 11.88/1.99  
% 11.88/1.99  fof(f86,plain,(
% 11.88/1.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 11.88/1.99    inference(cnf_transformation,[],[f50])).
% 11.88/1.99  
% 11.88/1.99  fof(f7,axiom,(
% 11.88/1.99    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 11.88/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.88/1.99  
% 11.88/1.99  fof(f28,plain,(
% 11.88/1.99    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 11.88/1.99    inference(ennf_transformation,[],[f7])).
% 11.88/1.99  
% 11.88/1.99  fof(f75,plain,(
% 11.88/1.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 11.88/1.99    inference(cnf_transformation,[],[f28])).
% 11.88/1.99  
% 11.88/1.99  fof(f97,plain,(
% 11.88/1.99    v1_relat_1(sK6)),
% 11.88/1.99    inference(cnf_transformation,[],[f59])).
% 11.88/1.99  
% 11.88/1.99  fof(f1,axiom,(
% 11.88/1.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 11.88/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.88/1.99  
% 11.88/1.99  fof(f60,plain,(
% 11.88/1.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 11.88/1.99    inference(cnf_transformation,[],[f1])).
% 11.88/1.99  
% 11.88/1.99  fof(f5,axiom,(
% 11.88/1.99    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 11.88/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.88/1.99  
% 11.88/1.99  fof(f26,plain,(
% 11.88/1.99    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 11.88/1.99    inference(ennf_transformation,[],[f5])).
% 11.88/1.99  
% 11.88/1.99  fof(f73,plain,(
% 11.88/1.99    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 11.88/1.99    inference(cnf_transformation,[],[f26])).
% 11.88/1.99  
% 11.88/1.99  fof(f13,axiom,(
% 11.88/1.99    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 11.88/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.88/1.99  
% 11.88/1.99  fof(f31,plain,(
% 11.88/1.99    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 11.88/1.99    inference(ennf_transformation,[],[f13])).
% 11.88/1.99  
% 11.88/1.99  fof(f81,plain,(
% 11.88/1.99    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 11.88/1.99    inference(cnf_transformation,[],[f31])).
% 11.88/1.99  
% 11.88/1.99  fof(f111,plain,(
% 11.88/1.99    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k6_subset_1(X0,X1),X2)) )),
% 11.88/1.99    inference(definition_unfolding,[],[f81,f83])).
% 11.88/1.99  
% 11.88/1.99  fof(f6,axiom,(
% 11.88/1.99    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 11.88/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.88/1.99  
% 11.88/1.99  fof(f27,plain,(
% 11.88/1.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 11.88/1.99    inference(ennf_transformation,[],[f6])).
% 11.88/1.99  
% 11.88/1.99  fof(f74,plain,(
% 11.88/1.99    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 11.88/1.99    inference(cnf_transformation,[],[f27])).
% 11.88/1.99  
% 11.88/1.99  fof(f94,plain,(
% 11.88/1.99    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 11.88/1.99    inference(cnf_transformation,[],[f36])).
% 11.88/1.99  
% 11.88/1.99  fof(f99,plain,(
% 11.88/1.99    ~r1_tarski(k3_relat_1(sK5),k3_relat_1(sK6))),
% 11.88/1.99    inference(cnf_transformation,[],[f59])).
% 11.88/1.99  
% 11.88/1.99  cnf(c_37,negated_conjecture,
% 11.88/1.99      ( v1_relat_1(sK5) ),
% 11.88/1.99      inference(cnf_transformation,[],[f96]) ).
% 11.88/2.00  
% 11.88/2.00  cnf(c_1439,plain,
% 11.88/2.00      ( v1_relat_1(sK5) = iProver_top ),
% 11.88/2.00      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 11.88/2.00  
% 11.88/2.00  cnf(c_30,plain,
% 11.88/2.00      ( ~ v1_relat_1(X0)
% 11.88/2.00      | k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ),
% 11.88/2.00      inference(cnf_transformation,[],[f92]) ).
% 11.88/2.00  
% 11.88/2.00  cnf(c_1444,plain,
% 11.88/2.00      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
% 11.88/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.88/2.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 11.88/2.00  
% 11.88/2.00  cnf(c_3328,plain,
% 11.88/2.00      ( k2_xboole_0(k1_relat_1(sK5),k2_relat_1(sK5)) = k3_relat_1(sK5) ),
% 11.88/2.00      inference(superposition,[status(thm)],[c_1439,c_1444]) ).
% 11.88/2.00  
% 11.88/2.00  cnf(c_11,plain,
% 11.88/2.00      ( r1_tarski(X0,X0) ),
% 11.88/2.00      inference(cnf_transformation,[],[f116]) ).
% 11.88/2.00  
% 11.88/2.00  cnf(c_1457,plain,
% 11.88/2.00      ( r1_tarski(X0,X0) = iProver_top ),
% 11.88/2.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 11.88/2.00  
% 11.88/2.00  cnf(c_20,plain,
% 11.88/2.00      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
% 11.88/2.00      | r1_tarski(k6_subset_1(X0,X1),X2) ),
% 11.88/2.00      inference(cnf_transformation,[],[f110]) ).
% 11.88/2.00  
% 11.88/2.00  cnf(c_1450,plain,
% 11.88/2.00      ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
% 11.88/2.00      | r1_tarski(k6_subset_1(X0,X1),X2) = iProver_top ),
% 11.88/2.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 11.88/2.00  
% 11.88/2.00  cnf(c_9370,plain,
% 11.88/2.00      ( r1_tarski(k6_subset_1(k2_xboole_0(X0,X1),X0),X1) = iProver_top ),
% 11.88/2.00      inference(superposition,[status(thm)],[c_1457,c_1450]) ).
% 11.88/2.00  
% 11.88/2.00  cnf(c_59343,plain,
% 11.88/2.00      ( r1_tarski(k6_subset_1(k3_relat_1(sK5),k1_relat_1(sK5)),k2_relat_1(sK5)) = iProver_top ),
% 11.88/2.00      inference(superposition,[status(thm)],[c_3328,c_9370]) ).
% 11.88/2.00  
% 11.88/2.00  cnf(c_35,negated_conjecture,
% 11.88/2.00      ( r1_tarski(sK5,sK6) ),
% 11.88/2.00      inference(cnf_transformation,[],[f98]) ).
% 11.88/2.00  
% 11.88/2.00  cnf(c_1441,plain,
% 11.88/2.00      ( r1_tarski(sK5,sK6) = iProver_top ),
% 11.88/2.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 11.88/2.00  
% 11.88/2.00  cnf(c_32,plain,
% 11.88/2.00      ( ~ r1_tarski(X0,X1)
% 11.88/2.00      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 11.88/2.00      | ~ v1_relat_1(X0)
% 11.88/2.00      | ~ v1_relat_1(X1) ),
% 11.88/2.00      inference(cnf_transformation,[],[f95]) ).
% 11.88/2.00  
% 11.88/2.00  cnf(c_25,plain,
% 11.88/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.88/2.00      | ~ v1_relat_1(X1)
% 11.88/2.00      | v1_relat_1(X0) ),
% 11.88/2.00      inference(cnf_transformation,[],[f87]) ).
% 11.88/2.00  
% 11.88/2.00  cnf(c_23,plain,
% 11.88/2.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 11.88/2.00      inference(cnf_transformation,[],[f86]) ).
% 11.88/2.00  
% 11.88/2.00  cnf(c_202,plain,
% 11.88/2.00      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 11.88/2.00      | ~ r1_tarski(X0,X1)
% 11.88/2.00      | ~ v1_relat_1(X1) ),
% 11.88/2.00      inference(global_propositional_subsumption,
% 11.88/2.00                [status(thm)],
% 11.88/2.00                [c_32,c_25,c_23]) ).
% 11.88/2.00  
% 11.88/2.00  cnf(c_203,plain,
% 11.88/2.00      ( ~ r1_tarski(X0,X1)
% 11.88/2.00      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 11.88/2.00      | ~ v1_relat_1(X1) ),
% 11.88/2.00      inference(renaming,[status(thm)],[c_202]) ).
% 11.88/2.00  
% 11.88/2.00  cnf(c_1437,plain,
% 11.88/2.00      ( r1_tarski(X0,X1) != iProver_top
% 11.88/2.00      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) = iProver_top
% 11.88/2.00      | v1_relat_1(X1) != iProver_top ),
% 11.88/2.00      inference(predicate_to_equality,[status(thm)],[c_203]) ).
% 11.88/2.00  
% 11.88/2.00  cnf(c_15,plain,
% 11.88/2.00      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 11.88/2.00      inference(cnf_transformation,[],[f75]) ).
% 11.88/2.00  
% 11.88/2.00  cnf(c_1454,plain,
% 11.88/2.00      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 11.88/2.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 11.88/2.00  
% 11.88/2.00  cnf(c_2782,plain,
% 11.88/2.00      ( k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(X1)
% 11.88/2.00      | r1_tarski(X0,X1) != iProver_top
% 11.88/2.00      | v1_relat_1(X1) != iProver_top ),
% 11.88/2.00      inference(superposition,[status(thm)],[c_1437,c_1454]) ).
% 11.88/2.00  
% 11.88/2.00  cnf(c_19109,plain,
% 11.88/2.00      ( k2_xboole_0(k2_relat_1(sK5),k2_relat_1(sK6)) = k2_relat_1(sK6)
% 11.88/2.00      | v1_relat_1(sK6) != iProver_top ),
% 11.88/2.00      inference(superposition,[status(thm)],[c_1441,c_2782]) ).
% 11.88/2.00  
% 11.88/2.00  cnf(c_36,negated_conjecture,
% 11.88/2.00      ( v1_relat_1(sK6) ),
% 11.88/2.00      inference(cnf_transformation,[],[f97]) ).
% 11.88/2.00  
% 11.88/2.00  cnf(c_39,plain,
% 11.88/2.00      ( v1_relat_1(sK6) = iProver_top ),
% 11.88/2.00      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 11.88/2.00  
% 11.88/2.00  cnf(c_19932,plain,
% 11.88/2.00      ( k2_xboole_0(k2_relat_1(sK5),k2_relat_1(sK6)) = k2_relat_1(sK6) ),
% 11.88/2.00      inference(global_propositional_subsumption,
% 11.88/2.00                [status(thm)],
% 11.88/2.00                [c_19109,c_39]) ).
% 11.88/2.00  
% 11.88/2.00  cnf(c_0,plain,
% 11.88/2.00      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 11.88/2.00      inference(cnf_transformation,[],[f60]) ).
% 11.88/2.00  
% 11.88/2.00  cnf(c_13,plain,
% 11.88/2.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X0,k2_xboole_0(X2,X1)) ),
% 11.88/2.00      inference(cnf_transformation,[],[f73]) ).
% 11.88/2.00  
% 11.88/2.00  cnf(c_1456,plain,
% 11.88/2.00      ( r1_tarski(X0,X1) != iProver_top
% 11.88/2.00      | r1_tarski(X0,k2_xboole_0(X2,X1)) = iProver_top ),
% 11.88/2.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 11.88/2.00  
% 11.88/2.00  cnf(c_4370,plain,
% 11.88/2.00      ( r1_tarski(X0,X1) != iProver_top
% 11.88/2.00      | r1_tarski(X0,k2_xboole_0(X1,X2)) = iProver_top ),
% 11.88/2.00      inference(superposition,[status(thm)],[c_0,c_1456]) ).
% 11.88/2.00  
% 11.88/2.00  cnf(c_19942,plain,
% 11.88/2.00      ( r1_tarski(X0,k2_relat_1(sK6)) = iProver_top
% 11.88/2.00      | r1_tarski(X0,k2_relat_1(sK5)) != iProver_top ),
% 11.88/2.00      inference(superposition,[status(thm)],[c_19932,c_4370]) ).
% 11.88/2.00  
% 11.88/2.00  cnf(c_59645,plain,
% 11.88/2.00      ( r1_tarski(k6_subset_1(k3_relat_1(sK5),k1_relat_1(sK5)),k2_relat_1(sK6)) = iProver_top ),
% 11.88/2.00      inference(superposition,[status(thm)],[c_59343,c_19942]) ).
% 11.88/2.00  
% 11.88/2.00  cnf(c_1440,plain,
% 11.88/2.00      ( v1_relat_1(sK6) = iProver_top ),
% 11.88/2.00      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 11.88/2.00  
% 11.88/2.00  cnf(c_3327,plain,
% 11.88/2.00      ( k2_xboole_0(k1_relat_1(sK6),k2_relat_1(sK6)) = k3_relat_1(sK6) ),
% 11.88/2.00      inference(superposition,[status(thm)],[c_1440,c_1444]) ).
% 11.88/2.00  
% 11.88/2.00  cnf(c_4378,plain,
% 11.88/2.00      ( r1_tarski(X0,k3_relat_1(sK6)) = iProver_top
% 11.88/2.00      | r1_tarski(X0,k2_relat_1(sK6)) != iProver_top ),
% 11.88/2.00      inference(superposition,[status(thm)],[c_3327,c_1456]) ).
% 11.88/2.00  
% 11.88/2.00  cnf(c_60578,plain,
% 11.88/2.00      ( r1_tarski(k6_subset_1(k3_relat_1(sK5),k1_relat_1(sK5)),k3_relat_1(sK6)) = iProver_top ),
% 11.88/2.00      inference(superposition,[status(thm)],[c_59645,c_4378]) ).
% 11.88/2.00  
% 11.88/2.00  cnf(c_21,plain,
% 11.88/2.00      ( r1_tarski(X0,k2_xboole_0(X1,X2))
% 11.88/2.00      | ~ r1_tarski(k6_subset_1(X0,X1),X2) ),
% 11.88/2.00      inference(cnf_transformation,[],[f111]) ).
% 11.88/2.00  
% 11.88/2.00  cnf(c_1449,plain,
% 11.88/2.00      ( r1_tarski(X0,k2_xboole_0(X1,X2)) = iProver_top
% 11.88/2.00      | r1_tarski(k6_subset_1(X0,X1),X2) != iProver_top ),
% 11.88/2.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 11.88/2.00  
% 11.88/2.00  cnf(c_60656,plain,
% 11.88/2.00      ( r1_tarski(k3_relat_1(sK5),k2_xboole_0(k1_relat_1(sK5),k3_relat_1(sK6))) = iProver_top ),
% 11.88/2.00      inference(superposition,[status(thm)],[c_60578,c_1449]) ).
% 11.88/2.00  
% 11.88/2.00  cnf(c_14,plain,
% 11.88/2.00      ( r1_tarski(X0,X1) | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 11.88/2.00      inference(cnf_transformation,[],[f74]) ).
% 11.88/2.00  
% 11.88/2.00  cnf(c_1455,plain,
% 11.88/2.00      ( r1_tarski(X0,X1) = iProver_top
% 11.88/2.00      | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
% 11.88/2.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 11.88/2.00  
% 11.88/2.00  cnf(c_4322,plain,
% 11.88/2.00      ( r1_tarski(k3_relat_1(sK5),X0) != iProver_top
% 11.88/2.00      | r1_tarski(k1_relat_1(sK5),X0) = iProver_top ),
% 11.88/2.00      inference(superposition,[status(thm)],[c_3328,c_1455]) ).
% 11.88/2.00  
% 11.88/2.00  cnf(c_4653,plain,
% 11.88/2.00      ( r1_tarski(k3_relat_1(sK5),X0) != iProver_top
% 11.88/2.00      | r1_tarski(k1_relat_1(sK5),k2_xboole_0(X1,X0)) = iProver_top ),
% 11.88/2.00      inference(superposition,[status(thm)],[c_1456,c_4322]) ).
% 11.88/2.00  
% 11.88/2.00  cnf(c_17520,plain,
% 11.88/2.00      ( r1_tarski(k3_relat_1(sK5),k2_relat_1(sK6)) != iProver_top
% 11.88/2.00      | r1_tarski(k1_relat_1(sK5),k3_relat_1(sK6)) = iProver_top ),
% 11.88/2.00      inference(superposition,[status(thm)],[c_3327,c_4653]) ).
% 11.88/2.00  
% 11.88/2.00  cnf(c_40,plain,
% 11.88/2.00      ( r1_tarski(sK5,sK6) = iProver_top ),
% 11.88/2.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 11.88/2.00  
% 11.88/2.00  cnf(c_33,plain,
% 11.88/2.00      ( ~ r1_tarski(X0,X1)
% 11.88/2.00      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 11.88/2.00      | ~ v1_relat_1(X0)
% 11.88/2.00      | ~ v1_relat_1(X1) ),
% 11.88/2.00      inference(cnf_transformation,[],[f94]) ).
% 11.88/2.00  
% 11.88/2.00  cnf(c_197,plain,
% 11.88/2.00      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 11.88/2.00      | ~ r1_tarski(X0,X1)
% 11.88/2.00      | ~ v1_relat_1(X1) ),
% 11.88/2.00      inference(global_propositional_subsumption,
% 11.88/2.00                [status(thm)],
% 11.88/2.00                [c_33,c_25,c_23]) ).
% 11.88/2.00  
% 11.88/2.00  cnf(c_198,plain,
% 11.88/2.00      ( ~ r1_tarski(X0,X1)
% 11.88/2.00      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 11.88/2.00      | ~ v1_relat_1(X1) ),
% 11.88/2.00      inference(renaming,[status(thm)],[c_197]) ).
% 11.88/2.00  
% 11.88/2.00  cnf(c_1438,plain,
% 11.88/2.00      ( r1_tarski(X0,X1) != iProver_top
% 11.88/2.00      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) = iProver_top
% 11.88/2.00      | v1_relat_1(X1) != iProver_top ),
% 11.88/2.00      inference(predicate_to_equality,[status(thm)],[c_198]) ).
% 11.88/2.00  
% 11.88/2.00  cnf(c_7075,plain,
% 11.88/2.00      ( r1_tarski(X0,k3_relat_1(sK6)) = iProver_top
% 11.88/2.00      | r1_tarski(X0,k1_relat_1(sK6)) != iProver_top ),
% 11.88/2.00      inference(superposition,[status(thm)],[c_3327,c_4370]) ).
% 11.88/2.00  
% 11.88/2.00  cnf(c_8436,plain,
% 11.88/2.00      ( r1_tarski(X0,sK6) != iProver_top
% 11.88/2.00      | r1_tarski(k1_relat_1(X0),k3_relat_1(sK6)) = iProver_top
% 11.88/2.00      | v1_relat_1(sK6) != iProver_top ),
% 11.88/2.00      inference(superposition,[status(thm)],[c_1438,c_7075]) ).
% 11.88/2.00  
% 11.88/2.00  cnf(c_8452,plain,
% 11.88/2.00      ( r1_tarski(k1_relat_1(sK5),k3_relat_1(sK6)) = iProver_top
% 11.88/2.00      | r1_tarski(sK5,sK6) != iProver_top
% 11.88/2.00      | v1_relat_1(sK6) != iProver_top ),
% 11.88/2.00      inference(instantiation,[status(thm)],[c_8436]) ).
% 11.88/2.00  
% 11.88/2.00  cnf(c_17697,plain,
% 11.88/2.00      ( r1_tarski(k1_relat_1(sK5),k3_relat_1(sK6)) = iProver_top ),
% 11.88/2.00      inference(global_propositional_subsumption,
% 11.88/2.00                [status(thm)],
% 11.88/2.00                [c_17520,c_39,c_40,c_8452]) ).
% 11.88/2.00  
% 11.88/2.00  cnf(c_17704,plain,
% 11.88/2.00      ( k2_xboole_0(k1_relat_1(sK5),k3_relat_1(sK6)) = k3_relat_1(sK6) ),
% 11.88/2.00      inference(superposition,[status(thm)],[c_17697,c_1454]) ).
% 11.88/2.00  
% 11.88/2.00  cnf(c_60664,plain,
% 11.88/2.00      ( r1_tarski(k3_relat_1(sK5),k3_relat_1(sK6)) = iProver_top ),
% 11.88/2.00      inference(light_normalisation,[status(thm)],[c_60656,c_17704]) ).
% 11.88/2.00  
% 11.88/2.00  cnf(c_34,negated_conjecture,
% 11.88/2.00      ( ~ r1_tarski(k3_relat_1(sK5),k3_relat_1(sK6)) ),
% 11.88/2.00      inference(cnf_transformation,[],[f99]) ).
% 11.88/2.00  
% 11.88/2.00  cnf(c_41,plain,
% 11.88/2.00      ( r1_tarski(k3_relat_1(sK5),k3_relat_1(sK6)) != iProver_top ),
% 11.88/2.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 11.88/2.00  
% 11.88/2.00  cnf(contradiction,plain,
% 11.88/2.00      ( $false ),
% 11.88/2.00      inference(minisat,[status(thm)],[c_60664,c_41]) ).
% 11.88/2.00  
% 11.88/2.00  
% 11.88/2.00  % SZS output end CNFRefutation for theBenchmark.p
% 11.88/2.00  
% 11.88/2.00  ------                               Statistics
% 11.88/2.00  
% 11.88/2.00  ------ General
% 11.88/2.00  
% 11.88/2.00  abstr_ref_over_cycles:                  0
% 11.88/2.00  abstr_ref_under_cycles:                 0
% 11.88/2.00  gc_basic_clause_elim:                   0
% 11.88/2.00  forced_gc_time:                         0
% 11.88/2.00  parsing_time:                           0.011
% 11.88/2.00  unif_index_cands_time:                  0.
% 11.88/2.00  unif_index_add_time:                    0.
% 11.88/2.00  orderings_time:                         0.
% 11.88/2.00  out_proof_time:                         0.012
% 11.88/2.00  total_time:                             1.341
% 11.88/2.00  num_of_symbols:                         52
% 11.88/2.00  num_of_terms:                           51982
% 11.88/2.00  
% 11.88/2.00  ------ Preprocessing
% 11.88/2.00  
% 11.88/2.00  num_of_splits:                          0
% 11.88/2.00  num_of_split_atoms:                     0
% 11.88/2.00  num_of_reused_defs:                     0
% 11.88/2.00  num_eq_ax_congr_red:                    44
% 11.88/2.00  num_of_sem_filtered_clauses:            1
% 11.88/2.00  num_of_subtypes:                        0
% 11.88/2.00  monotx_restored_types:                  0
% 11.88/2.00  sat_num_of_epr_types:                   0
% 11.88/2.00  sat_num_of_non_cyclic_types:            0
% 11.88/2.00  sat_guarded_non_collapsed_types:        0
% 11.88/2.00  num_pure_diseq_elim:                    0
% 11.88/2.00  simp_replaced_by:                       0
% 11.88/2.00  res_preprocessed:                       165
% 11.88/2.00  prep_upred:                             0
% 11.88/2.00  prep_unflattend:                        0
% 11.88/2.00  smt_new_axioms:                         0
% 11.88/2.00  pred_elim_cands:                        3
% 11.88/2.00  pred_elim:                              1
% 11.88/2.00  pred_elim_cl:                           2
% 11.88/2.00  pred_elim_cycles:                       3
% 11.88/2.00  merged_defs:                            10
% 11.88/2.00  merged_defs_ncl:                        0
% 11.88/2.00  bin_hyper_res:                          11
% 11.88/2.00  prep_cycles:                            4
% 11.88/2.00  pred_elim_time:                         0.001
% 11.88/2.00  splitting_time:                         0.
% 11.88/2.00  sem_filter_time:                        0.
% 11.88/2.00  monotx_time:                            0.001
% 11.88/2.00  subtype_inf_time:                       0.
% 11.88/2.00  
% 11.88/2.00  ------ Problem properties
% 11.88/2.00  
% 11.88/2.00  clauses:                                35
% 11.88/2.00  conjectures:                            4
% 11.88/2.00  epr:                                    8
% 11.88/2.00  horn:                                   29
% 11.88/2.00  ground:                                 4
% 11.88/2.00  unary:                                  10
% 11.88/2.00  binary:                                 13
% 11.88/2.00  lits:                                   73
% 11.88/2.00  lits_eq:                                12
% 11.88/2.00  fd_pure:                                0
% 11.88/2.00  fd_pseudo:                              0
% 11.88/2.00  fd_cond:                                0
% 11.88/2.00  fd_pseudo_cond:                         6
% 11.88/2.00  ac_symbols:                             0
% 11.88/2.00  
% 11.88/2.00  ------ Propositional Solver
% 11.88/2.00  
% 11.88/2.00  prop_solver_calls:                      30
% 11.88/2.00  prop_fast_solver_calls:                 1308
% 11.88/2.00  smt_solver_calls:                       0
% 11.88/2.00  smt_fast_solver_calls:                  0
% 11.88/2.00  prop_num_of_clauses:                    23274
% 11.88/2.00  prop_preprocess_simplified:             36328
% 11.88/2.00  prop_fo_subsumed:                       11
% 11.88/2.00  prop_solver_time:                       0.
% 11.88/2.00  smt_solver_time:                        0.
% 11.88/2.00  smt_fast_solver_time:                   0.
% 11.88/2.00  prop_fast_solver_time:                  0.
% 11.88/2.00  prop_unsat_core_time:                   0.002
% 11.88/2.00  
% 11.88/2.00  ------ QBF
% 11.88/2.00  
% 11.88/2.00  qbf_q_res:                              0
% 11.88/2.00  qbf_num_tautologies:                    0
% 11.88/2.00  qbf_prep_cycles:                        0
% 11.88/2.00  
% 11.88/2.00  ------ BMC1
% 11.88/2.00  
% 11.88/2.00  bmc1_current_bound:                     -1
% 11.88/2.00  bmc1_last_solved_bound:                 -1
% 11.88/2.00  bmc1_unsat_core_size:                   -1
% 11.88/2.00  bmc1_unsat_core_parents_size:           -1
% 11.88/2.00  bmc1_merge_next_fun:                    0
% 11.88/2.00  bmc1_unsat_core_clauses_time:           0.
% 11.88/2.00  
% 11.88/2.00  ------ Instantiation
% 11.88/2.00  
% 11.88/2.00  inst_num_of_clauses:                    4437
% 11.88/2.00  inst_num_in_passive:                    2178
% 11.88/2.00  inst_num_in_active:                     1455
% 11.88/2.00  inst_num_in_unprocessed:                804
% 11.88/2.00  inst_num_of_loops:                      1660
% 11.88/2.00  inst_num_of_learning_restarts:          0
% 11.88/2.00  inst_num_moves_active_passive:          203
% 11.88/2.00  inst_lit_activity:                      0
% 11.88/2.00  inst_lit_activity_moves:                0
% 11.88/2.00  inst_num_tautologies:                   0
% 11.88/2.00  inst_num_prop_implied:                  0
% 11.88/2.00  inst_num_existing_simplified:           0
% 11.88/2.00  inst_num_eq_res_simplified:             0
% 11.88/2.00  inst_num_child_elim:                    0
% 11.88/2.00  inst_num_of_dismatching_blockings:      4062
% 11.88/2.00  inst_num_of_non_proper_insts:           4939
% 11.88/2.00  inst_num_of_duplicates:                 0
% 11.88/2.00  inst_inst_num_from_inst_to_res:         0
% 11.88/2.00  inst_dismatching_checking_time:         0.
% 11.88/2.00  
% 11.88/2.00  ------ Resolution
% 11.88/2.00  
% 11.88/2.00  res_num_of_clauses:                     0
% 11.88/2.00  res_num_in_passive:                     0
% 11.88/2.00  res_num_in_active:                      0
% 11.88/2.00  res_num_of_loops:                       169
% 11.88/2.00  res_forward_subset_subsumed:            476
% 11.88/2.00  res_backward_subset_subsumed:           0
% 11.88/2.00  res_forward_subsumed:                   0
% 11.88/2.00  res_backward_subsumed:                  0
% 11.88/2.00  res_forward_subsumption_resolution:     0
% 11.88/2.00  res_backward_subsumption_resolution:    0
% 11.88/2.00  res_clause_to_clause_subsumption:       13547
% 11.88/2.00  res_orphan_elimination:                 0
% 11.88/2.00  res_tautology_del:                      295
% 11.88/2.00  res_num_eq_res_simplified:              0
% 11.88/2.00  res_num_sel_changes:                    0
% 11.88/2.00  res_moves_from_active_to_pass:          0
% 11.88/2.00  
% 11.88/2.00  ------ Superposition
% 11.88/2.00  
% 11.88/2.00  sup_time_total:                         0.
% 11.88/2.00  sup_time_generating:                    0.
% 11.88/2.00  sup_time_sim_full:                      0.
% 11.88/2.00  sup_time_sim_immed:                     0.
% 11.88/2.00  
% 11.88/2.00  sup_num_of_clauses:                     2736
% 11.88/2.00  sup_num_in_active:                      304
% 11.88/2.00  sup_num_in_passive:                     2432
% 11.88/2.00  sup_num_of_loops:                       331
% 11.88/2.00  sup_fw_superposition:                   2493
% 11.88/2.00  sup_bw_superposition:                   2829
% 11.88/2.00  sup_immediate_simplified:               849
% 11.88/2.00  sup_given_eliminated:                   2
% 11.88/2.00  comparisons_done:                       0
% 11.88/2.00  comparisons_avoided:                    0
% 11.88/2.00  
% 11.88/2.00  ------ Simplifications
% 11.88/2.00  
% 11.88/2.00  
% 11.88/2.00  sim_fw_subset_subsumed:                 135
% 11.88/2.00  sim_bw_subset_subsumed:                 6
% 11.88/2.00  sim_fw_subsumed:                        362
% 11.88/2.00  sim_bw_subsumed:                        62
% 11.88/2.00  sim_fw_subsumption_res:                 2
% 11.88/2.00  sim_bw_subsumption_res:                 0
% 11.88/2.00  sim_tautology_del:                      194
% 11.88/2.00  sim_eq_tautology_del:                   57
% 11.88/2.00  sim_eq_res_simp:                        1
% 11.88/2.00  sim_fw_demodulated:                     250
% 11.88/2.00  sim_bw_demodulated:                     33
% 11.88/2.00  sim_light_normalised:                   181
% 11.88/2.00  sim_joinable_taut:                      0
% 11.88/2.00  sim_joinable_simp:                      0
% 11.88/2.00  sim_ac_normalised:                      0
% 11.88/2.00  sim_smt_subsumption:                    0
% 11.88/2.00  
%------------------------------------------------------------------------------
