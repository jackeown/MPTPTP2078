%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:39:48 EST 2020

% Result     : Theorem 1.22s
% Output     : CNFRefutation 1.22s
% Verified   : 
% Statistics : Number of formulae       :  150 (4138 expanded)
%              Number of clauses        :   92 (1574 expanded)
%              Number of leaves         :   19 ( 847 expanded)
%              Depth                    :   26
%              Number of atoms          :  312 (9550 expanded)
%              Number of equality atoms :  179 (4307 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(X1,k3_subset_1(X0,X1))
        <=> k1_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f27,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(X1,k3_subset_1(X0,X1))
      <~> k1_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f32,plain,(
    ? [X0,X1] :
      ( ( k1_subset_1(X0) != X1
        | ~ r1_tarski(X1,k3_subset_1(X0,X1)) )
      & ( k1_subset_1(X0) = X1
        | r1_tarski(X1,k3_subset_1(X0,X1)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f33,plain,(
    ? [X0,X1] :
      ( ( k1_subset_1(X0) != X1
        | ~ r1_tarski(X1,k3_subset_1(X0,X1)) )
      & ( k1_subset_1(X0) = X1
        | r1_tarski(X1,k3_subset_1(X0,X1)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f32])).

fof(f34,plain,
    ( ? [X0,X1] :
        ( ( k1_subset_1(X0) != X1
          | ~ r1_tarski(X1,k3_subset_1(X0,X1)) )
        & ( k1_subset_1(X0) = X1
          | r1_tarski(X1,k3_subset_1(X0,X1)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ( k1_subset_1(sK1) != sK2
        | ~ r1_tarski(sK2,k3_subset_1(sK1,sK2)) )
      & ( k1_subset_1(sK1) = sK2
        | r1_tarski(sK2,k3_subset_1(sK1,sK2)) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ( k1_subset_1(sK1) != sK2
      | ~ r1_tarski(sK2,k3_subset_1(sK1,sK2)) )
    & ( k1_subset_1(sK1) = sK2
      | r1_tarski(sK2,k3_subset_1(sK1,sK2)) )
    & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f33,f34])).

fof(f53,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f35])).

fof(f8,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,k3_subset_1(X0,X2))
           => r1_tarski(X2,k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k3_subset_1(X0,X1))
          | ~ r1_tarski(X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k3_subset_1(X0,X1))
          | ~ r1_tarski(X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f25])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,k3_subset_1(X0,X1))
      | ~ r1_tarski(X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f11,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f13,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f10,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f56,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f50,f47])).

fof(f57,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f48,f56])).

fof(f15,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f6,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f49,f43])).

fof(f54,plain,
    ( k1_subset_1(sK1) = sK2
    | r1_tarski(sK2,k3_subset_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f35])).

fof(f60,plain,
    ( k1_xboole_0 = sK2
    | r1_tarski(sK2,k3_subset_1(sK1,sK2)) ),
    inference(definition_unfolding,[],[f54,f47])).

fof(f5,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f22])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f55,plain,
    ( k1_subset_1(sK1) != sK2
    | ~ r1_tarski(sK2,k3_subset_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f35])).

fof(f59,plain,
    ( k1_xboole_0 != sK2
    | ~ r1_tarski(sK2,k3_subset_1(sK1,sK2)) ),
    inference(definition_unfolding,[],[f55,f47])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_735,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_8,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_741,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,k3_subset_1(X1,X2))
    | r1_tarski(X2,k3_subset_1(X1,X0)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_739,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,k3_subset_1(X1,X2)) != iProver_top
    | r1_tarski(X2,k3_subset_1(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1610,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,k3_subset_1(X1,k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_741,c_739])).

cnf(c_10,plain,
    ( k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1633,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1610,c_10])).

cnf(c_13,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_738,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2935,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1633,c_738])).

cnf(c_2938,plain,
    ( r1_tarski(sK2,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_735,c_2935])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_742,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3002,plain,
    ( k3_xboole_0(sK2,sK1) = sK2 ),
    inference(superposition,[status(thm)],[c_2938,c_742])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_740,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1744,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) = k3_subset_1(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_735,c_740])).

cnf(c_2005,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)) = k3_subset_1(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_0,c_1744])).

cnf(c_3091,plain,
    ( k3_subset_1(sK1,sK2) = k5_xboole_0(sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_3002,c_2005])).

cnf(c_15,negated_conjecture,
    ( r1_tarski(sK2,k3_subset_1(sK1,sK2))
    | k1_xboole_0 = sK2 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_736,plain,
    ( k1_xboole_0 = sK2
    | r1_tarski(sK2,k3_subset_1(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3311,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(sK2,k5_xboole_0(sK1,sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3091,c_736])).

cnf(c_6,plain,
    ( r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_9,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_200,plain,
    ( ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0)
    | k5_xboole_0(X2,X3) != X1
    | k3_xboole_0(X2,X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_9])).

cnf(c_201,plain,
    ( ~ r1_tarski(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))
    | v1_xboole_0(k3_xboole_0(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_200])).

cnf(c_734,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) != iProver_top
    | v1_xboole_0(k3_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_201])).

cnf(c_1044,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),k5_xboole_0(X1,X0)) != iProver_top
    | v1_xboole_0(k3_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_734])).

cnf(c_2206,plain,
    ( r1_tarski(k3_xboole_0(k3_xboole_0(sK2,sK1),sK1),k3_subset_1(sK1,sK2)) != iProver_top
    | v1_xboole_0(k3_xboole_0(sK1,k3_xboole_0(sK2,sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2005,c_1044])).

cnf(c_3087,plain,
    ( r1_tarski(k3_xboole_0(sK2,sK1),k3_subset_1(sK1,sK2)) != iProver_top
    | v1_xboole_0(k3_xboole_0(sK1,sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3002,c_2206])).

cnf(c_3106,plain,
    ( r1_tarski(k3_xboole_0(sK2,sK1),k5_xboole_0(sK1,sK2)) != iProver_top
    | v1_xboole_0(k3_xboole_0(sK1,sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3087,c_3091])).

cnf(c_3109,plain,
    ( r1_tarski(sK2,k5_xboole_0(sK1,sK2)) != iProver_top
    | v1_xboole_0(k3_xboole_0(sK1,sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3106,c_3002])).

cnf(c_3985,plain,
    ( sK2 = k1_xboole_0
    | v1_xboole_0(k3_xboole_0(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3311,c_3109])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1046,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),k5_xboole_0(X1,X0)) != iProver_top
    | v1_xboole_0(k3_xboole_0(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_734])).

cnf(c_2401,plain,
    ( r1_tarski(k3_xboole_0(k3_xboole_0(sK1,sK2),sK1),k3_subset_1(sK1,sK2)) != iProver_top
    | v1_xboole_0(k3_xboole_0(k3_xboole_0(sK1,sK2),sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1744,c_1046])).

cnf(c_2599,plain,
    ( r1_tarski(k3_xboole_0(k3_xboole_0(sK2,sK1),sK1),k3_subset_1(sK1,sK2)) != iProver_top
    | v1_xboole_0(k3_xboole_0(k3_xboole_0(sK1,sK2),sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_2401])).

cnf(c_31,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1743,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = k3_subset_1(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_738,c_740])).

cnf(c_1061,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_741,c_742])).

cnf(c_1264,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1061,c_0])).

cnf(c_1748,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1743,c_10,c_1264])).

cnf(c_1754,plain,
    ( r1_tarski(k3_xboole_0(X0,k1_xboole_0),X0) != iProver_top
    | v1_xboole_0(k3_xboole_0(X0,k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1748,c_734])).

cnf(c_1761,plain,
    ( r1_tarski(k1_xboole_0,X0) != iProver_top
    | v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1754,c_1264])).

cnf(c_4,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_744,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_746,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1161,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_744,c_746])).

cnf(c_1895,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) != iProver_top
    | v1_xboole_0(k3_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_1044])).

cnf(c_2440,plain,
    ( r1_tarski(k3_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k3_subset_1(sK1,sK2)) != iProver_top
    | v1_xboole_0(k3_xboole_0(k3_xboole_0(sK1,sK2),sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1744,c_1895])).

cnf(c_2609,plain,
    ( v1_xboole_0(k3_xboole_0(k3_xboole_0(sK1,sK2),sK1)) = iProver_top
    | v1_xboole_0(k3_xboole_0(sK1,k3_xboole_0(sK1,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1161,c_2440])).

cnf(c_374,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2675,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(k1_xboole_0)
    | X0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_374])).

cnf(c_2676,plain,
    ( X0 != k1_xboole_0
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2675])).

cnf(c_2678,plain,
    ( sK2 != k1_xboole_0
    | v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2676])).

cnf(c_2008,plain,
    ( r1_tarski(k3_xboole_0(k3_xboole_0(sK1,sK2),sK1),k3_subset_1(sK1,sK2)) != iProver_top
    | v1_xboole_0(k3_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1744,c_1044])).

cnf(c_2255,plain,
    ( v1_xboole_0(k3_xboole_0(k3_xboole_0(sK1,sK2),sK1)) != iProver_top
    | v1_xboole_0(k3_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1161,c_2008])).

cnf(c_2315,plain,
    ( v1_xboole_0(k3_xboole_0(k3_xboole_0(sK2,sK1),sK1)) != iProver_top
    | v1_xboole_0(k3_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_2255])).

cnf(c_3090,plain,
    ( v1_xboole_0(k3_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = iProver_top
    | v1_xboole_0(k3_xboole_0(sK2,sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3002,c_2315])).

cnf(c_3096,plain,
    ( v1_xboole_0(k3_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = iProver_top
    | v1_xboole_0(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3090,c_3002])).

cnf(c_2258,plain,
    ( r1_tarski(k3_xboole_0(k3_xboole_0(sK2,sK1),sK1),k3_subset_1(sK1,sK2)) != iProver_top
    | v1_xboole_0(k3_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_2008])).

cnf(c_3084,plain,
    ( r1_tarski(k3_xboole_0(sK2,sK1),k3_subset_1(sK1,sK2)) != iProver_top
    | v1_xboole_0(k3_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3002,c_2258])).

cnf(c_3121,plain,
    ( r1_tarski(k3_xboole_0(sK2,sK1),k5_xboole_0(sK1,sK2)) != iProver_top
    | v1_xboole_0(k3_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3084,c_3091])).

cnf(c_3124,plain,
    ( r1_tarski(sK2,k5_xboole_0(sK1,sK2)) != iProver_top
    | v1_xboole_0(k3_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3121,c_3002])).

cnf(c_3900,plain,
    ( v1_xboole_0(k3_xboole_0(k3_xboole_0(sK1,sK2),sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2599,c_31,c_1761,c_2609,c_2678,c_3096,c_3124,c_3311])).

cnf(c_3907,plain,
    ( v1_xboole_0(k3_xboole_0(k3_xboole_0(sK2,sK1),sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_3900])).

cnf(c_3913,plain,
    ( v1_xboole_0(sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3907,c_3002])).

cnf(c_3984,plain,
    ( v1_xboole_0(k3_xboole_0(sK1,sK2)) = iProver_top
    | v1_xboole_0(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1161,c_3109])).

cnf(c_4051,plain,
    ( v1_xboole_0(k3_xboole_0(sK1,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3985,c_3913,c_3984])).

cnf(c_1457,plain,
    ( k3_xboole_0(X0,X1) = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1161,c_742])).

cnf(c_4470,plain,
    ( k3_xboole_0(k3_xboole_0(sK1,sK2),X0) = k3_xboole_0(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_4051,c_1457])).

cnf(c_4612,plain,
    ( k3_xboole_0(k3_xboole_0(sK2,sK1),X0) = k3_xboole_0(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_0,c_4470])).

cnf(c_4746,plain,
    ( k3_xboole_0(sK2,X0) = k3_xboole_0(sK1,sK2) ),
    inference(light_normalisation,[status(thm)],[c_4612,c_3002])).

cnf(c_4771,plain,
    ( k3_xboole_0(X0,sK2) = k3_xboole_0(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_4746,c_0])).

cnf(c_1062,plain,
    ( k3_xboole_0(sK2,k3_subset_1(sK1,sK2)) = sK2
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_736,c_742])).

cnf(c_3310,plain,
    ( k3_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = sK2
    | sK2 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3091,c_1062])).

cnf(c_4773,plain,
    ( k3_xboole_0(sK1,sK2) = sK2
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4746,c_3310])).

cnf(c_17,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_14,negated_conjecture,
    ( ~ r1_tarski(sK2,k3_subset_1(sK1,sK2))
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_737,plain,
    ( k1_xboole_0 != sK2
    | r1_tarski(sK2,k3_subset_1(sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3312,plain,
    ( sK2 != k1_xboole_0
    | r1_tarski(sK2,k5_xboole_0(sK1,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3091,c_737])).

cnf(c_1609,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X2,k3_subset_1(X1,X0)) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1161,c_739])).

cnf(c_4414,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK1)) != iProver_top
    | r1_tarski(X0,k5_xboole_0(sK1,sK2)) = iProver_top
    | v1_xboole_0(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3091,c_1609])).

cnf(c_4453,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) != iProver_top
    | r1_tarski(sK2,k5_xboole_0(sK1,sK2)) = iProver_top
    | v1_xboole_0(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4414])).

cnf(c_5038,plain,
    ( k3_xboole_0(sK1,sK2) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4773,c_17,c_3312,c_3913,c_4453])).

cnf(c_5422,plain,
    ( k3_xboole_0(X0,sK2) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_4771,c_5038])).

cnf(c_5437,plain,
    ( sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5422,c_1061])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5437,c_4453,c_3913,c_3312,c_17])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:27:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 1.22/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.22/1.02  
% 1.22/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.22/1.02  
% 1.22/1.02  ------  iProver source info
% 1.22/1.02  
% 1.22/1.02  git: date: 2020-06-30 10:37:57 +0100
% 1.22/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.22/1.02  git: non_committed_changes: false
% 1.22/1.02  git: last_make_outside_of_git: false
% 1.22/1.02  
% 1.22/1.02  ------ 
% 1.22/1.02  
% 1.22/1.02  ------ Input Options
% 1.22/1.02  
% 1.22/1.02  --out_options                           all
% 1.22/1.02  --tptp_safe_out                         true
% 1.22/1.02  --problem_path                          ""
% 1.22/1.02  --include_path                          ""
% 1.22/1.02  --clausifier                            res/vclausify_rel
% 1.22/1.02  --clausifier_options                    --mode clausify
% 1.22/1.02  --stdin                                 false
% 1.22/1.02  --stats_out                             all
% 1.22/1.02  
% 1.22/1.02  ------ General Options
% 1.22/1.02  
% 1.22/1.02  --fof                                   false
% 1.22/1.02  --time_out_real                         305.
% 1.22/1.02  --time_out_virtual                      -1.
% 1.22/1.02  --symbol_type_check                     false
% 1.22/1.02  --clausify_out                          false
% 1.22/1.02  --sig_cnt_out                           false
% 1.22/1.02  --trig_cnt_out                          false
% 1.22/1.02  --trig_cnt_out_tolerance                1.
% 1.22/1.02  --trig_cnt_out_sk_spl                   false
% 1.22/1.02  --abstr_cl_out                          false
% 1.22/1.02  
% 1.22/1.02  ------ Global Options
% 1.22/1.02  
% 1.22/1.02  --schedule                              default
% 1.22/1.02  --add_important_lit                     false
% 1.22/1.02  --prop_solver_per_cl                    1000
% 1.22/1.02  --min_unsat_core                        false
% 1.22/1.02  --soft_assumptions                      false
% 1.22/1.02  --soft_lemma_size                       3
% 1.22/1.02  --prop_impl_unit_size                   0
% 1.22/1.02  --prop_impl_unit                        []
% 1.22/1.02  --share_sel_clauses                     true
% 1.22/1.02  --reset_solvers                         false
% 1.22/1.02  --bc_imp_inh                            [conj_cone]
% 1.22/1.02  --conj_cone_tolerance                   3.
% 1.22/1.02  --extra_neg_conj                        none
% 1.22/1.02  --large_theory_mode                     true
% 1.22/1.02  --prolific_symb_bound                   200
% 1.22/1.02  --lt_threshold                          2000
% 1.22/1.02  --clause_weak_htbl                      true
% 1.22/1.02  --gc_record_bc_elim                     false
% 1.22/1.02  
% 1.22/1.02  ------ Preprocessing Options
% 1.22/1.02  
% 1.22/1.02  --preprocessing_flag                    true
% 1.22/1.02  --time_out_prep_mult                    0.1
% 1.22/1.02  --splitting_mode                        input
% 1.22/1.02  --splitting_grd                         true
% 1.22/1.02  --splitting_cvd                         false
% 1.22/1.02  --splitting_cvd_svl                     false
% 1.22/1.02  --splitting_nvd                         32
% 1.22/1.02  --sub_typing                            true
% 1.22/1.02  --prep_gs_sim                           true
% 1.22/1.02  --prep_unflatten                        true
% 1.22/1.02  --prep_res_sim                          true
% 1.22/1.02  --prep_upred                            true
% 1.22/1.02  --prep_sem_filter                       exhaustive
% 1.22/1.02  --prep_sem_filter_out                   false
% 1.22/1.02  --pred_elim                             true
% 1.22/1.02  --res_sim_input                         true
% 1.22/1.02  --eq_ax_congr_red                       true
% 1.22/1.02  --pure_diseq_elim                       true
% 1.22/1.02  --brand_transform                       false
% 1.22/1.02  --non_eq_to_eq                          false
% 1.22/1.02  --prep_def_merge                        true
% 1.22/1.02  --prep_def_merge_prop_impl              false
% 1.22/1.02  --prep_def_merge_mbd                    true
% 1.22/1.02  --prep_def_merge_tr_red                 false
% 1.22/1.02  --prep_def_merge_tr_cl                  false
% 1.22/1.02  --smt_preprocessing                     true
% 1.22/1.02  --smt_ac_axioms                         fast
% 1.22/1.02  --preprocessed_out                      false
% 1.22/1.02  --preprocessed_stats                    false
% 1.22/1.02  
% 1.22/1.02  ------ Abstraction refinement Options
% 1.22/1.02  
% 1.22/1.02  --abstr_ref                             []
% 1.22/1.02  --abstr_ref_prep                        false
% 1.22/1.02  --abstr_ref_until_sat                   false
% 1.22/1.02  --abstr_ref_sig_restrict                funpre
% 1.22/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 1.22/1.02  --abstr_ref_under                       []
% 1.22/1.02  
% 1.22/1.02  ------ SAT Options
% 1.22/1.02  
% 1.22/1.02  --sat_mode                              false
% 1.22/1.02  --sat_fm_restart_options                ""
% 1.22/1.02  --sat_gr_def                            false
% 1.22/1.02  --sat_epr_types                         true
% 1.22/1.02  --sat_non_cyclic_types                  false
% 1.22/1.02  --sat_finite_models                     false
% 1.22/1.02  --sat_fm_lemmas                         false
% 1.22/1.02  --sat_fm_prep                           false
% 1.22/1.02  --sat_fm_uc_incr                        true
% 1.22/1.02  --sat_out_model                         small
% 1.22/1.02  --sat_out_clauses                       false
% 1.22/1.02  
% 1.22/1.02  ------ QBF Options
% 1.22/1.02  
% 1.22/1.02  --qbf_mode                              false
% 1.22/1.02  --qbf_elim_univ                         false
% 1.22/1.02  --qbf_dom_inst                          none
% 1.22/1.02  --qbf_dom_pre_inst                      false
% 1.22/1.02  --qbf_sk_in                             false
% 1.22/1.02  --qbf_pred_elim                         true
% 1.22/1.02  --qbf_split                             512
% 1.22/1.02  
% 1.22/1.02  ------ BMC1 Options
% 1.22/1.02  
% 1.22/1.02  --bmc1_incremental                      false
% 1.22/1.02  --bmc1_axioms                           reachable_all
% 1.22/1.02  --bmc1_min_bound                        0
% 1.22/1.02  --bmc1_max_bound                        -1
% 1.22/1.02  --bmc1_max_bound_default                -1
% 1.22/1.02  --bmc1_symbol_reachability              true
% 1.22/1.02  --bmc1_property_lemmas                  false
% 1.22/1.02  --bmc1_k_induction                      false
% 1.22/1.02  --bmc1_non_equiv_states                 false
% 1.22/1.02  --bmc1_deadlock                         false
% 1.22/1.02  --bmc1_ucm                              false
% 1.22/1.02  --bmc1_add_unsat_core                   none
% 1.22/1.02  --bmc1_unsat_core_children              false
% 1.22/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 1.22/1.02  --bmc1_out_stat                         full
% 1.22/1.02  --bmc1_ground_init                      false
% 1.22/1.02  --bmc1_pre_inst_next_state              false
% 1.22/1.02  --bmc1_pre_inst_state                   false
% 1.22/1.02  --bmc1_pre_inst_reach_state             false
% 1.22/1.02  --bmc1_out_unsat_core                   false
% 1.22/1.02  --bmc1_aig_witness_out                  false
% 1.22/1.02  --bmc1_verbose                          false
% 1.22/1.02  --bmc1_dump_clauses_tptp                false
% 1.22/1.02  --bmc1_dump_unsat_core_tptp             false
% 1.22/1.02  --bmc1_dump_file                        -
% 1.22/1.02  --bmc1_ucm_expand_uc_limit              128
% 1.22/1.02  --bmc1_ucm_n_expand_iterations          6
% 1.22/1.02  --bmc1_ucm_extend_mode                  1
% 1.22/1.02  --bmc1_ucm_init_mode                    2
% 1.22/1.02  --bmc1_ucm_cone_mode                    none
% 1.22/1.02  --bmc1_ucm_reduced_relation_type        0
% 1.22/1.02  --bmc1_ucm_relax_model                  4
% 1.22/1.02  --bmc1_ucm_full_tr_after_sat            true
% 1.22/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 1.22/1.02  --bmc1_ucm_layered_model                none
% 1.22/1.02  --bmc1_ucm_max_lemma_size               10
% 1.22/1.02  
% 1.22/1.02  ------ AIG Options
% 1.22/1.02  
% 1.22/1.02  --aig_mode                              false
% 1.22/1.02  
% 1.22/1.02  ------ Instantiation Options
% 1.22/1.02  
% 1.22/1.02  --instantiation_flag                    true
% 1.22/1.02  --inst_sos_flag                         false
% 1.22/1.02  --inst_sos_phase                        true
% 1.22/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.22/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.22/1.02  --inst_lit_sel_side                     num_symb
% 1.22/1.02  --inst_solver_per_active                1400
% 1.22/1.02  --inst_solver_calls_frac                1.
% 1.22/1.02  --inst_passive_queue_type               priority_queues
% 1.22/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.22/1.02  --inst_passive_queues_freq              [25;2]
% 1.22/1.02  --inst_dismatching                      true
% 1.22/1.02  --inst_eager_unprocessed_to_passive     true
% 1.22/1.02  --inst_prop_sim_given                   true
% 1.22/1.02  --inst_prop_sim_new                     false
% 1.22/1.02  --inst_subs_new                         false
% 1.22/1.02  --inst_eq_res_simp                      false
% 1.22/1.02  --inst_subs_given                       false
% 1.22/1.02  --inst_orphan_elimination               true
% 1.22/1.02  --inst_learning_loop_flag               true
% 1.22/1.02  --inst_learning_start                   3000
% 1.22/1.02  --inst_learning_factor                  2
% 1.22/1.02  --inst_start_prop_sim_after_learn       3
% 1.22/1.02  --inst_sel_renew                        solver
% 1.22/1.02  --inst_lit_activity_flag                true
% 1.22/1.02  --inst_restr_to_given                   false
% 1.22/1.02  --inst_activity_threshold               500
% 1.22/1.02  --inst_out_proof                        true
% 1.22/1.02  
% 1.22/1.02  ------ Resolution Options
% 1.22/1.02  
% 1.22/1.02  --resolution_flag                       true
% 1.22/1.02  --res_lit_sel                           adaptive
% 1.22/1.02  --res_lit_sel_side                      none
% 1.22/1.02  --res_ordering                          kbo
% 1.22/1.02  --res_to_prop_solver                    active
% 1.22/1.02  --res_prop_simpl_new                    false
% 1.22/1.02  --res_prop_simpl_given                  true
% 1.22/1.02  --res_passive_queue_type                priority_queues
% 1.22/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.22/1.02  --res_passive_queues_freq               [15;5]
% 1.22/1.02  --res_forward_subs                      full
% 1.22/1.02  --res_backward_subs                     full
% 1.22/1.02  --res_forward_subs_resolution           true
% 1.22/1.02  --res_backward_subs_resolution          true
% 1.22/1.02  --res_orphan_elimination                true
% 1.22/1.02  --res_time_limit                        2.
% 1.22/1.02  --res_out_proof                         true
% 1.22/1.02  
% 1.22/1.02  ------ Superposition Options
% 1.22/1.02  
% 1.22/1.02  --superposition_flag                    true
% 1.22/1.02  --sup_passive_queue_type                priority_queues
% 1.22/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.22/1.02  --sup_passive_queues_freq               [8;1;4]
% 1.22/1.02  --demod_completeness_check              fast
% 1.22/1.02  --demod_use_ground                      true
% 1.22/1.02  --sup_to_prop_solver                    passive
% 1.22/1.02  --sup_prop_simpl_new                    true
% 1.22/1.02  --sup_prop_simpl_given                  true
% 1.22/1.02  --sup_fun_splitting                     false
% 1.22/1.02  --sup_smt_interval                      50000
% 1.22/1.02  
% 1.22/1.02  ------ Superposition Simplification Setup
% 1.22/1.02  
% 1.22/1.02  --sup_indices_passive                   []
% 1.22/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.22/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.22/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.22/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 1.22/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.22/1.02  --sup_full_bw                           [BwDemod]
% 1.22/1.02  --sup_immed_triv                        [TrivRules]
% 1.22/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.22/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.22/1.02  --sup_immed_bw_main                     []
% 1.22/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.22/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 1.22/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.22/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.22/1.02  
% 1.22/1.02  ------ Combination Options
% 1.22/1.02  
% 1.22/1.02  --comb_res_mult                         3
% 1.22/1.02  --comb_sup_mult                         2
% 1.22/1.02  --comb_inst_mult                        10
% 1.22/1.02  
% 1.22/1.02  ------ Debug Options
% 1.22/1.02  
% 1.22/1.02  --dbg_backtrace                         false
% 1.22/1.02  --dbg_dump_prop_clauses                 false
% 1.22/1.02  --dbg_dump_prop_clauses_file            -
% 1.22/1.02  --dbg_out_stat                          false
% 1.22/1.02  ------ Parsing...
% 1.22/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.22/1.02  
% 1.22/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 1.22/1.02  
% 1.22/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.22/1.02  
% 1.22/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.22/1.02  ------ Proving...
% 1.22/1.02  ------ Problem Properties 
% 1.22/1.02  
% 1.22/1.02  
% 1.22/1.02  clauses                                 16
% 1.22/1.02  conjectures                             3
% 1.22/1.02  EPR                                     3
% 1.22/1.02  Horn                                    14
% 1.22/1.02  unary                                   6
% 1.22/1.02  binary                                  8
% 1.22/1.02  lits                                    29
% 1.22/1.02  lits eq                                 7
% 1.22/1.02  fd_pure                                 0
% 1.22/1.02  fd_pseudo                               0
% 1.22/1.02  fd_cond                                 0
% 1.22/1.02  fd_pseudo_cond                          0
% 1.22/1.02  AC symbols                              0
% 1.22/1.02  
% 1.22/1.02  ------ Schedule dynamic 5 is on 
% 1.22/1.02  
% 1.22/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.22/1.02  
% 1.22/1.02  
% 1.22/1.02  ------ 
% 1.22/1.02  Current options:
% 1.22/1.02  ------ 
% 1.22/1.02  
% 1.22/1.02  ------ Input Options
% 1.22/1.02  
% 1.22/1.02  --out_options                           all
% 1.22/1.02  --tptp_safe_out                         true
% 1.22/1.02  --problem_path                          ""
% 1.22/1.02  --include_path                          ""
% 1.22/1.02  --clausifier                            res/vclausify_rel
% 1.22/1.02  --clausifier_options                    --mode clausify
% 1.22/1.02  --stdin                                 false
% 1.22/1.02  --stats_out                             all
% 1.22/1.02  
% 1.22/1.02  ------ General Options
% 1.22/1.02  
% 1.22/1.02  --fof                                   false
% 1.22/1.02  --time_out_real                         305.
% 1.22/1.02  --time_out_virtual                      -1.
% 1.22/1.02  --symbol_type_check                     false
% 1.22/1.02  --clausify_out                          false
% 1.22/1.02  --sig_cnt_out                           false
% 1.22/1.02  --trig_cnt_out                          false
% 1.22/1.02  --trig_cnt_out_tolerance                1.
% 1.22/1.02  --trig_cnt_out_sk_spl                   false
% 1.22/1.02  --abstr_cl_out                          false
% 1.22/1.02  
% 1.22/1.02  ------ Global Options
% 1.22/1.02  
% 1.22/1.02  --schedule                              default
% 1.22/1.02  --add_important_lit                     false
% 1.22/1.02  --prop_solver_per_cl                    1000
% 1.22/1.02  --min_unsat_core                        false
% 1.22/1.02  --soft_assumptions                      false
% 1.22/1.02  --soft_lemma_size                       3
% 1.22/1.02  --prop_impl_unit_size                   0
% 1.22/1.02  --prop_impl_unit                        []
% 1.22/1.02  --share_sel_clauses                     true
% 1.22/1.02  --reset_solvers                         false
% 1.22/1.02  --bc_imp_inh                            [conj_cone]
% 1.22/1.02  --conj_cone_tolerance                   3.
% 1.22/1.02  --extra_neg_conj                        none
% 1.22/1.02  --large_theory_mode                     true
% 1.22/1.02  --prolific_symb_bound                   200
% 1.22/1.02  --lt_threshold                          2000
% 1.22/1.02  --clause_weak_htbl                      true
% 1.22/1.02  --gc_record_bc_elim                     false
% 1.22/1.02  
% 1.22/1.02  ------ Preprocessing Options
% 1.22/1.02  
% 1.22/1.02  --preprocessing_flag                    true
% 1.22/1.02  --time_out_prep_mult                    0.1
% 1.22/1.02  --splitting_mode                        input
% 1.22/1.02  --splitting_grd                         true
% 1.22/1.02  --splitting_cvd                         false
% 1.22/1.02  --splitting_cvd_svl                     false
% 1.22/1.02  --splitting_nvd                         32
% 1.22/1.02  --sub_typing                            true
% 1.22/1.02  --prep_gs_sim                           true
% 1.22/1.02  --prep_unflatten                        true
% 1.22/1.02  --prep_res_sim                          true
% 1.22/1.02  --prep_upred                            true
% 1.22/1.02  --prep_sem_filter                       exhaustive
% 1.22/1.02  --prep_sem_filter_out                   false
% 1.22/1.02  --pred_elim                             true
% 1.22/1.02  --res_sim_input                         true
% 1.22/1.02  --eq_ax_congr_red                       true
% 1.22/1.02  --pure_diseq_elim                       true
% 1.22/1.02  --brand_transform                       false
% 1.22/1.02  --non_eq_to_eq                          false
% 1.22/1.02  --prep_def_merge                        true
% 1.22/1.02  --prep_def_merge_prop_impl              false
% 1.22/1.02  --prep_def_merge_mbd                    true
% 1.22/1.02  --prep_def_merge_tr_red                 false
% 1.22/1.02  --prep_def_merge_tr_cl                  false
% 1.22/1.02  --smt_preprocessing                     true
% 1.22/1.02  --smt_ac_axioms                         fast
% 1.22/1.02  --preprocessed_out                      false
% 1.22/1.02  --preprocessed_stats                    false
% 1.22/1.02  
% 1.22/1.02  ------ Abstraction refinement Options
% 1.22/1.02  
% 1.22/1.02  --abstr_ref                             []
% 1.22/1.02  --abstr_ref_prep                        false
% 1.22/1.02  --abstr_ref_until_sat                   false
% 1.22/1.02  --abstr_ref_sig_restrict                funpre
% 1.22/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 1.22/1.02  --abstr_ref_under                       []
% 1.22/1.02  
% 1.22/1.02  ------ SAT Options
% 1.22/1.02  
% 1.22/1.02  --sat_mode                              false
% 1.22/1.02  --sat_fm_restart_options                ""
% 1.22/1.02  --sat_gr_def                            false
% 1.22/1.02  --sat_epr_types                         true
% 1.22/1.02  --sat_non_cyclic_types                  false
% 1.22/1.02  --sat_finite_models                     false
% 1.22/1.02  --sat_fm_lemmas                         false
% 1.22/1.02  --sat_fm_prep                           false
% 1.22/1.02  --sat_fm_uc_incr                        true
% 1.22/1.02  --sat_out_model                         small
% 1.22/1.02  --sat_out_clauses                       false
% 1.22/1.02  
% 1.22/1.02  ------ QBF Options
% 1.22/1.02  
% 1.22/1.02  --qbf_mode                              false
% 1.22/1.02  --qbf_elim_univ                         false
% 1.22/1.02  --qbf_dom_inst                          none
% 1.22/1.02  --qbf_dom_pre_inst                      false
% 1.22/1.02  --qbf_sk_in                             false
% 1.22/1.02  --qbf_pred_elim                         true
% 1.22/1.02  --qbf_split                             512
% 1.22/1.02  
% 1.22/1.02  ------ BMC1 Options
% 1.22/1.02  
% 1.22/1.02  --bmc1_incremental                      false
% 1.22/1.02  --bmc1_axioms                           reachable_all
% 1.22/1.02  --bmc1_min_bound                        0
% 1.22/1.02  --bmc1_max_bound                        -1
% 1.22/1.02  --bmc1_max_bound_default                -1
% 1.22/1.02  --bmc1_symbol_reachability              true
% 1.22/1.02  --bmc1_property_lemmas                  false
% 1.22/1.02  --bmc1_k_induction                      false
% 1.22/1.02  --bmc1_non_equiv_states                 false
% 1.22/1.02  --bmc1_deadlock                         false
% 1.22/1.02  --bmc1_ucm                              false
% 1.22/1.02  --bmc1_add_unsat_core                   none
% 1.22/1.02  --bmc1_unsat_core_children              false
% 1.22/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 1.22/1.02  --bmc1_out_stat                         full
% 1.22/1.02  --bmc1_ground_init                      false
% 1.22/1.02  --bmc1_pre_inst_next_state              false
% 1.22/1.02  --bmc1_pre_inst_state                   false
% 1.22/1.02  --bmc1_pre_inst_reach_state             false
% 1.22/1.02  --bmc1_out_unsat_core                   false
% 1.22/1.02  --bmc1_aig_witness_out                  false
% 1.22/1.02  --bmc1_verbose                          false
% 1.22/1.02  --bmc1_dump_clauses_tptp                false
% 1.22/1.02  --bmc1_dump_unsat_core_tptp             false
% 1.22/1.02  --bmc1_dump_file                        -
% 1.22/1.02  --bmc1_ucm_expand_uc_limit              128
% 1.22/1.02  --bmc1_ucm_n_expand_iterations          6
% 1.22/1.02  --bmc1_ucm_extend_mode                  1
% 1.22/1.02  --bmc1_ucm_init_mode                    2
% 1.22/1.02  --bmc1_ucm_cone_mode                    none
% 1.22/1.02  --bmc1_ucm_reduced_relation_type        0
% 1.22/1.02  --bmc1_ucm_relax_model                  4
% 1.22/1.02  --bmc1_ucm_full_tr_after_sat            true
% 1.22/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 1.22/1.02  --bmc1_ucm_layered_model                none
% 1.22/1.02  --bmc1_ucm_max_lemma_size               10
% 1.22/1.02  
% 1.22/1.02  ------ AIG Options
% 1.22/1.02  
% 1.22/1.02  --aig_mode                              false
% 1.22/1.02  
% 1.22/1.02  ------ Instantiation Options
% 1.22/1.02  
% 1.22/1.02  --instantiation_flag                    true
% 1.22/1.02  --inst_sos_flag                         false
% 1.22/1.02  --inst_sos_phase                        true
% 1.22/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.22/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.22/1.02  --inst_lit_sel_side                     none
% 1.22/1.02  --inst_solver_per_active                1400
% 1.22/1.02  --inst_solver_calls_frac                1.
% 1.22/1.02  --inst_passive_queue_type               priority_queues
% 1.22/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.22/1.03  --inst_passive_queues_freq              [25;2]
% 1.22/1.03  --inst_dismatching                      true
% 1.22/1.03  --inst_eager_unprocessed_to_passive     true
% 1.22/1.03  --inst_prop_sim_given                   true
% 1.22/1.03  --inst_prop_sim_new                     false
% 1.22/1.03  --inst_subs_new                         false
% 1.22/1.03  --inst_eq_res_simp                      false
% 1.22/1.03  --inst_subs_given                       false
% 1.22/1.03  --inst_orphan_elimination               true
% 1.22/1.03  --inst_learning_loop_flag               true
% 1.22/1.03  --inst_learning_start                   3000
% 1.22/1.03  --inst_learning_factor                  2
% 1.22/1.03  --inst_start_prop_sim_after_learn       3
% 1.22/1.03  --inst_sel_renew                        solver
% 1.22/1.03  --inst_lit_activity_flag                true
% 1.22/1.03  --inst_restr_to_given                   false
% 1.22/1.03  --inst_activity_threshold               500
% 1.22/1.03  --inst_out_proof                        true
% 1.22/1.03  
% 1.22/1.03  ------ Resolution Options
% 1.22/1.03  
% 1.22/1.03  --resolution_flag                       false
% 1.22/1.03  --res_lit_sel                           adaptive
% 1.22/1.03  --res_lit_sel_side                      none
% 1.22/1.03  --res_ordering                          kbo
% 1.22/1.03  --res_to_prop_solver                    active
% 1.22/1.03  --res_prop_simpl_new                    false
% 1.22/1.03  --res_prop_simpl_given                  true
% 1.22/1.03  --res_passive_queue_type                priority_queues
% 1.22/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.22/1.03  --res_passive_queues_freq               [15;5]
% 1.22/1.03  --res_forward_subs                      full
% 1.22/1.03  --res_backward_subs                     full
% 1.22/1.03  --res_forward_subs_resolution           true
% 1.22/1.03  --res_backward_subs_resolution          true
% 1.22/1.03  --res_orphan_elimination                true
% 1.22/1.03  --res_time_limit                        2.
% 1.22/1.03  --res_out_proof                         true
% 1.22/1.03  
% 1.22/1.03  ------ Superposition Options
% 1.22/1.03  
% 1.22/1.03  --superposition_flag                    true
% 1.22/1.03  --sup_passive_queue_type                priority_queues
% 1.22/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.22/1.03  --sup_passive_queues_freq               [8;1;4]
% 1.22/1.03  --demod_completeness_check              fast
% 1.22/1.03  --demod_use_ground                      true
% 1.22/1.03  --sup_to_prop_solver                    passive
% 1.22/1.03  --sup_prop_simpl_new                    true
% 1.22/1.03  --sup_prop_simpl_given                  true
% 1.22/1.03  --sup_fun_splitting                     false
% 1.22/1.03  --sup_smt_interval                      50000
% 1.22/1.03  
% 1.22/1.03  ------ Superposition Simplification Setup
% 1.22/1.03  
% 1.22/1.03  --sup_indices_passive                   []
% 1.22/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.22/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.22/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.22/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 1.22/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.22/1.03  --sup_full_bw                           [BwDemod]
% 1.22/1.03  --sup_immed_triv                        [TrivRules]
% 1.22/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.22/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.22/1.03  --sup_immed_bw_main                     []
% 1.22/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.22/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 1.22/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.22/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.22/1.03  
% 1.22/1.03  ------ Combination Options
% 1.22/1.03  
% 1.22/1.03  --comb_res_mult                         3
% 1.22/1.03  --comb_sup_mult                         2
% 1.22/1.03  --comb_inst_mult                        10
% 1.22/1.03  
% 1.22/1.03  ------ Debug Options
% 1.22/1.03  
% 1.22/1.03  --dbg_backtrace                         false
% 1.22/1.03  --dbg_dump_prop_clauses                 false
% 1.22/1.03  --dbg_dump_prop_clauses_file            -
% 1.22/1.03  --dbg_out_stat                          false
% 1.22/1.03  
% 1.22/1.03  
% 1.22/1.03  
% 1.22/1.03  
% 1.22/1.03  ------ Proving...
% 1.22/1.03  
% 1.22/1.03  
% 1.22/1.03  % SZS status Theorem for theBenchmark.p
% 1.22/1.03  
% 1.22/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 1.22/1.03  
% 1.22/1.03  fof(f1,axiom,(
% 1.22/1.03    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.22/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.22/1.03  
% 1.22/1.03  fof(f36,plain,(
% 1.22/1.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.22/1.03    inference(cnf_transformation,[],[f1])).
% 1.22/1.03  
% 1.22/1.03  fof(f16,conjecture,(
% 1.22/1.03    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 1.22/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.22/1.03  
% 1.22/1.03  fof(f17,negated_conjecture,(
% 1.22/1.03    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 1.22/1.03    inference(negated_conjecture,[],[f16])).
% 1.22/1.03  
% 1.22/1.03  fof(f27,plain,(
% 1.22/1.03    ? [X0,X1] : ((r1_tarski(X1,k3_subset_1(X0,X1)) <~> k1_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.22/1.03    inference(ennf_transformation,[],[f17])).
% 1.22/1.03  
% 1.22/1.03  fof(f32,plain,(
% 1.22/1.03    ? [X0,X1] : (((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1)))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.22/1.03    inference(nnf_transformation,[],[f27])).
% 1.22/1.03  
% 1.22/1.03  fof(f33,plain,(
% 1.22/1.03    ? [X0,X1] : ((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.22/1.03    inference(flattening,[],[f32])).
% 1.22/1.03  
% 1.22/1.03  fof(f34,plain,(
% 1.22/1.03    ? [X0,X1] : ((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => ((k1_subset_1(sK1) != sK2 | ~r1_tarski(sK2,k3_subset_1(sK1,sK2))) & (k1_subset_1(sK1) = sK2 | r1_tarski(sK2,k3_subset_1(sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(sK1)))),
% 1.22/1.03    introduced(choice_axiom,[])).
% 1.22/1.03  
% 1.22/1.03  fof(f35,plain,(
% 1.22/1.03    (k1_subset_1(sK1) != sK2 | ~r1_tarski(sK2,k3_subset_1(sK1,sK2))) & (k1_subset_1(sK1) = sK2 | r1_tarski(sK2,k3_subset_1(sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 1.22/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f33,f34])).
% 1.22/1.03  
% 1.22/1.03  fof(f53,plain,(
% 1.22/1.03    m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 1.22/1.03    inference(cnf_transformation,[],[f35])).
% 1.22/1.03  
% 1.22/1.03  fof(f8,axiom,(
% 1.22/1.03    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.22/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.22/1.03  
% 1.22/1.03  fof(f45,plain,(
% 1.22/1.03    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.22/1.03    inference(cnf_transformation,[],[f8])).
% 1.22/1.03  
% 1.22/1.03  fof(f14,axiom,(
% 1.22/1.03    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X2)) => r1_tarski(X2,k3_subset_1(X0,X1)))))),
% 1.22/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.22/1.03  
% 1.22/1.03  fof(f25,plain,(
% 1.22/1.03    ! [X0,X1] : (! [X2] : ((r1_tarski(X2,k3_subset_1(X0,X1)) | ~r1_tarski(X1,k3_subset_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.22/1.03    inference(ennf_transformation,[],[f14])).
% 1.22/1.03  
% 1.22/1.03  fof(f26,plain,(
% 1.22/1.03    ! [X0,X1] : (! [X2] : (r1_tarski(X2,k3_subset_1(X0,X1)) | ~r1_tarski(X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.22/1.03    inference(flattening,[],[f25])).
% 1.22/1.03  
% 1.22/1.03  fof(f51,plain,(
% 1.22/1.03    ( ! [X2,X0,X1] : (r1_tarski(X2,k3_subset_1(X0,X1)) | ~r1_tarski(X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.22/1.03    inference(cnf_transformation,[],[f26])).
% 1.22/1.03  
% 1.22/1.03  fof(f11,axiom,(
% 1.22/1.03    ! [X0] : k2_subset_1(X0) = X0),
% 1.22/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.22/1.03  
% 1.22/1.03  fof(f48,plain,(
% 1.22/1.03    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.22/1.03    inference(cnf_transformation,[],[f11])).
% 1.22/1.03  
% 1.22/1.03  fof(f13,axiom,(
% 1.22/1.03    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 1.22/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.22/1.03  
% 1.22/1.03  fof(f50,plain,(
% 1.22/1.03    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 1.22/1.03    inference(cnf_transformation,[],[f13])).
% 1.22/1.03  
% 1.22/1.03  fof(f10,axiom,(
% 1.22/1.03    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 1.22/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.22/1.03  
% 1.22/1.03  fof(f47,plain,(
% 1.22/1.03    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 1.22/1.03    inference(cnf_transformation,[],[f10])).
% 1.22/1.03  
% 1.22/1.03  fof(f56,plain,(
% 1.22/1.03    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 1.22/1.03    inference(definition_unfolding,[],[f50,f47])).
% 1.22/1.03  
% 1.22/1.03  fof(f57,plain,(
% 1.22/1.03    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 1.22/1.03    inference(definition_unfolding,[],[f48,f56])).
% 1.22/1.03  
% 1.22/1.03  fof(f15,axiom,(
% 1.22/1.03    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.22/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.22/1.03  
% 1.22/1.03  fof(f52,plain,(
% 1.22/1.03    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.22/1.03    inference(cnf_transformation,[],[f15])).
% 1.22/1.03  
% 1.22/1.03  fof(f7,axiom,(
% 1.22/1.03    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.22/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.22/1.03  
% 1.22/1.03  fof(f21,plain,(
% 1.22/1.03    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.22/1.03    inference(ennf_transformation,[],[f7])).
% 1.22/1.03  
% 1.22/1.03  fof(f44,plain,(
% 1.22/1.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.22/1.03    inference(cnf_transformation,[],[f21])).
% 1.22/1.03  
% 1.22/1.03  fof(f12,axiom,(
% 1.22/1.03    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.22/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.22/1.03  
% 1.22/1.03  fof(f24,plain,(
% 1.22/1.03    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.22/1.03    inference(ennf_transformation,[],[f12])).
% 1.22/1.03  
% 1.22/1.03  fof(f49,plain,(
% 1.22/1.03    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.22/1.03    inference(cnf_transformation,[],[f24])).
% 1.22/1.03  
% 1.22/1.03  fof(f6,axiom,(
% 1.22/1.03    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 1.22/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.22/1.03  
% 1.22/1.03  fof(f43,plain,(
% 1.22/1.03    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 1.22/1.03    inference(cnf_transformation,[],[f6])).
% 1.22/1.03  
% 1.22/1.03  fof(f58,plain,(
% 1.22/1.03    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.22/1.03    inference(definition_unfolding,[],[f49,f43])).
% 1.22/1.03  
% 1.22/1.03  fof(f54,plain,(
% 1.22/1.03    k1_subset_1(sK1) = sK2 | r1_tarski(sK2,k3_subset_1(sK1,sK2))),
% 1.22/1.03    inference(cnf_transformation,[],[f35])).
% 1.22/1.03  
% 1.22/1.03  fof(f60,plain,(
% 1.22/1.03    k1_xboole_0 = sK2 | r1_tarski(sK2,k3_subset_1(sK1,sK2))),
% 1.22/1.03    inference(definition_unfolding,[],[f54,f47])).
% 1.22/1.03  
% 1.22/1.03  fof(f5,axiom,(
% 1.22/1.03    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 1.22/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.22/1.03  
% 1.22/1.03  fof(f42,plain,(
% 1.22/1.03    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 1.22/1.03    inference(cnf_transformation,[],[f5])).
% 1.22/1.03  
% 1.22/1.03  fof(f9,axiom,(
% 1.22/1.03    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 1.22/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.22/1.03  
% 1.22/1.03  fof(f22,plain,(
% 1.22/1.03    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 1.22/1.03    inference(ennf_transformation,[],[f9])).
% 1.22/1.03  
% 1.22/1.03  fof(f23,plain,(
% 1.22/1.03    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 1.22/1.03    inference(flattening,[],[f22])).
% 1.22/1.03  
% 1.22/1.03  fof(f46,plain,(
% 1.22/1.03    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 1.22/1.03    inference(cnf_transformation,[],[f23])).
% 1.22/1.03  
% 1.22/1.03  fof(f2,axiom,(
% 1.22/1.03    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 1.22/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.22/1.03  
% 1.22/1.03  fof(f37,plain,(
% 1.22/1.03    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 1.22/1.03    inference(cnf_transformation,[],[f2])).
% 1.22/1.03  
% 1.22/1.03  fof(f4,axiom,(
% 1.22/1.03    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.22/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.22/1.03  
% 1.22/1.03  fof(f20,plain,(
% 1.22/1.03    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.22/1.03    inference(ennf_transformation,[],[f4])).
% 1.22/1.03  
% 1.22/1.03  fof(f28,plain,(
% 1.22/1.03    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.22/1.03    inference(nnf_transformation,[],[f20])).
% 1.22/1.03  
% 1.22/1.03  fof(f29,plain,(
% 1.22/1.03    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.22/1.03    inference(rectify,[],[f28])).
% 1.22/1.03  
% 1.22/1.03  fof(f30,plain,(
% 1.22/1.03    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 1.22/1.03    introduced(choice_axiom,[])).
% 1.22/1.03  
% 1.22/1.03  fof(f31,plain,(
% 1.22/1.03    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.22/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).
% 1.22/1.03  
% 1.22/1.03  fof(f40,plain,(
% 1.22/1.03    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 1.22/1.03    inference(cnf_transformation,[],[f31])).
% 1.22/1.03  
% 1.22/1.03  fof(f3,axiom,(
% 1.22/1.03    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.22/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.22/1.03  
% 1.22/1.03  fof(f18,plain,(
% 1.22/1.03    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 1.22/1.03    inference(unused_predicate_definition_removal,[],[f3])).
% 1.22/1.03  
% 1.22/1.03  fof(f19,plain,(
% 1.22/1.03    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 1.22/1.03    inference(ennf_transformation,[],[f18])).
% 1.22/1.03  
% 1.22/1.03  fof(f38,plain,(
% 1.22/1.03    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 1.22/1.03    inference(cnf_transformation,[],[f19])).
% 1.22/1.03  
% 1.22/1.03  fof(f55,plain,(
% 1.22/1.03    k1_subset_1(sK1) != sK2 | ~r1_tarski(sK2,k3_subset_1(sK1,sK2))),
% 1.22/1.03    inference(cnf_transformation,[],[f35])).
% 1.22/1.03  
% 1.22/1.03  fof(f59,plain,(
% 1.22/1.03    k1_xboole_0 != sK2 | ~r1_tarski(sK2,k3_subset_1(sK1,sK2))),
% 1.22/1.03    inference(definition_unfolding,[],[f55,f47])).
% 1.22/1.03  
% 1.22/1.03  cnf(c_0,plain,
% 1.22/1.03      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 1.22/1.03      inference(cnf_transformation,[],[f36]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_16,negated_conjecture,
% 1.22/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
% 1.22/1.03      inference(cnf_transformation,[],[f53]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_735,plain,
% 1.22/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
% 1.22/1.03      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_8,plain,
% 1.22/1.03      ( r1_tarski(k1_xboole_0,X0) ),
% 1.22/1.03      inference(cnf_transformation,[],[f45]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_741,plain,
% 1.22/1.03      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 1.22/1.03      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_12,plain,
% 1.22/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.22/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 1.22/1.03      | ~ r1_tarski(X0,k3_subset_1(X1,X2))
% 1.22/1.03      | r1_tarski(X2,k3_subset_1(X1,X0)) ),
% 1.22/1.03      inference(cnf_transformation,[],[f51]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_739,plain,
% 1.22/1.03      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 1.22/1.03      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 1.22/1.03      | r1_tarski(X0,k3_subset_1(X1,X2)) != iProver_top
% 1.22/1.03      | r1_tarski(X2,k3_subset_1(X1,X0)) = iProver_top ),
% 1.22/1.03      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_1610,plain,
% 1.22/1.03      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 1.22/1.03      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) != iProver_top
% 1.22/1.03      | r1_tarski(X0,k3_subset_1(X1,k1_xboole_0)) = iProver_top ),
% 1.22/1.03      inference(superposition,[status(thm)],[c_741,c_739]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_10,plain,
% 1.22/1.03      ( k3_subset_1(X0,k1_xboole_0) = X0 ),
% 1.22/1.03      inference(cnf_transformation,[],[f57]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_1633,plain,
% 1.22/1.03      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 1.22/1.03      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) != iProver_top
% 1.22/1.03      | r1_tarski(X0,X1) = iProver_top ),
% 1.22/1.03      inference(demodulation,[status(thm)],[c_1610,c_10]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_13,plain,
% 1.22/1.03      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 1.22/1.03      inference(cnf_transformation,[],[f52]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_738,plain,
% 1.22/1.03      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 1.22/1.03      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_2935,plain,
% 1.22/1.03      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 1.22/1.03      | r1_tarski(X0,X1) = iProver_top ),
% 1.22/1.03      inference(forward_subsumption_resolution,
% 1.22/1.03                [status(thm)],
% 1.22/1.03                [c_1633,c_738]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_2938,plain,
% 1.22/1.03      ( r1_tarski(sK2,sK1) = iProver_top ),
% 1.22/1.03      inference(superposition,[status(thm)],[c_735,c_2935]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_7,plain,
% 1.22/1.03      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 1.22/1.03      inference(cnf_transformation,[],[f44]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_742,plain,
% 1.22/1.03      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 1.22/1.03      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_3002,plain,
% 1.22/1.03      ( k3_xboole_0(sK2,sK1) = sK2 ),
% 1.22/1.03      inference(superposition,[status(thm)],[c_2938,c_742]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_11,plain,
% 1.22/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.22/1.03      | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
% 1.22/1.03      inference(cnf_transformation,[],[f58]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_740,plain,
% 1.22/1.03      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
% 1.22/1.03      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 1.22/1.03      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_1744,plain,
% 1.22/1.03      ( k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) = k3_subset_1(sK1,sK2) ),
% 1.22/1.03      inference(superposition,[status(thm)],[c_735,c_740]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_2005,plain,
% 1.22/1.03      ( k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)) = k3_subset_1(sK1,sK2) ),
% 1.22/1.03      inference(superposition,[status(thm)],[c_0,c_1744]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_3091,plain,
% 1.22/1.03      ( k3_subset_1(sK1,sK2) = k5_xboole_0(sK1,sK2) ),
% 1.22/1.03      inference(demodulation,[status(thm)],[c_3002,c_2005]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_15,negated_conjecture,
% 1.22/1.03      ( r1_tarski(sK2,k3_subset_1(sK1,sK2)) | k1_xboole_0 = sK2 ),
% 1.22/1.03      inference(cnf_transformation,[],[f60]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_736,plain,
% 1.22/1.03      ( k1_xboole_0 = sK2
% 1.22/1.03      | r1_tarski(sK2,k3_subset_1(sK1,sK2)) = iProver_top ),
% 1.22/1.03      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_3311,plain,
% 1.22/1.03      ( sK2 = k1_xboole_0
% 1.22/1.03      | r1_tarski(sK2,k5_xboole_0(sK1,sK2)) = iProver_top ),
% 1.22/1.03      inference(demodulation,[status(thm)],[c_3091,c_736]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_6,plain,
% 1.22/1.03      ( r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
% 1.22/1.03      inference(cnf_transformation,[],[f42]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_9,plain,
% 1.22/1.03      ( ~ r1_xboole_0(X0,X1) | ~ r1_tarski(X0,X1) | v1_xboole_0(X0) ),
% 1.22/1.03      inference(cnf_transformation,[],[f46]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_200,plain,
% 1.22/1.03      ( ~ r1_tarski(X0,X1)
% 1.22/1.03      | v1_xboole_0(X0)
% 1.22/1.03      | k5_xboole_0(X2,X3) != X1
% 1.22/1.03      | k3_xboole_0(X2,X3) != X0 ),
% 1.22/1.03      inference(resolution_lifted,[status(thm)],[c_6,c_9]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_201,plain,
% 1.22/1.03      ( ~ r1_tarski(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))
% 1.22/1.03      | v1_xboole_0(k3_xboole_0(X0,X1)) ),
% 1.22/1.03      inference(unflattening,[status(thm)],[c_200]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_734,plain,
% 1.22/1.03      ( r1_tarski(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) != iProver_top
% 1.22/1.03      | v1_xboole_0(k3_xboole_0(X0,X1)) = iProver_top ),
% 1.22/1.03      inference(predicate_to_equality,[status(thm)],[c_201]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_1044,plain,
% 1.22/1.03      ( r1_tarski(k3_xboole_0(X0,X1),k5_xboole_0(X1,X0)) != iProver_top
% 1.22/1.03      | v1_xboole_0(k3_xboole_0(X1,X0)) = iProver_top ),
% 1.22/1.03      inference(superposition,[status(thm)],[c_0,c_734]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_2206,plain,
% 1.22/1.03      ( r1_tarski(k3_xboole_0(k3_xboole_0(sK2,sK1),sK1),k3_subset_1(sK1,sK2)) != iProver_top
% 1.22/1.03      | v1_xboole_0(k3_xboole_0(sK1,k3_xboole_0(sK2,sK1))) = iProver_top ),
% 1.22/1.03      inference(superposition,[status(thm)],[c_2005,c_1044]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_3087,plain,
% 1.22/1.03      ( r1_tarski(k3_xboole_0(sK2,sK1),k3_subset_1(sK1,sK2)) != iProver_top
% 1.22/1.03      | v1_xboole_0(k3_xboole_0(sK1,sK2)) = iProver_top ),
% 1.22/1.03      inference(demodulation,[status(thm)],[c_3002,c_2206]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_3106,plain,
% 1.22/1.03      ( r1_tarski(k3_xboole_0(sK2,sK1),k5_xboole_0(sK1,sK2)) != iProver_top
% 1.22/1.03      | v1_xboole_0(k3_xboole_0(sK1,sK2)) = iProver_top ),
% 1.22/1.03      inference(light_normalisation,[status(thm)],[c_3087,c_3091]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_3109,plain,
% 1.22/1.03      ( r1_tarski(sK2,k5_xboole_0(sK1,sK2)) != iProver_top
% 1.22/1.03      | v1_xboole_0(k3_xboole_0(sK1,sK2)) = iProver_top ),
% 1.22/1.03      inference(light_normalisation,[status(thm)],[c_3106,c_3002]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_3985,plain,
% 1.22/1.03      ( sK2 = k1_xboole_0
% 1.22/1.03      | v1_xboole_0(k3_xboole_0(sK1,sK2)) = iProver_top ),
% 1.22/1.03      inference(superposition,[status(thm)],[c_3311,c_3109]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_1,plain,
% 1.22/1.03      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 1.22/1.03      inference(cnf_transformation,[],[f37]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_1046,plain,
% 1.22/1.03      ( r1_tarski(k3_xboole_0(X0,X1),k5_xboole_0(X1,X0)) != iProver_top
% 1.22/1.03      | v1_xboole_0(k3_xboole_0(X0,X1)) = iProver_top ),
% 1.22/1.03      inference(superposition,[status(thm)],[c_1,c_734]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_2401,plain,
% 1.22/1.03      ( r1_tarski(k3_xboole_0(k3_xboole_0(sK1,sK2),sK1),k3_subset_1(sK1,sK2)) != iProver_top
% 1.22/1.03      | v1_xboole_0(k3_xboole_0(k3_xboole_0(sK1,sK2),sK1)) = iProver_top ),
% 1.22/1.03      inference(superposition,[status(thm)],[c_1744,c_1046]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_2599,plain,
% 1.22/1.03      ( r1_tarski(k3_xboole_0(k3_xboole_0(sK2,sK1),sK1),k3_subset_1(sK1,sK2)) != iProver_top
% 1.22/1.03      | v1_xboole_0(k3_xboole_0(k3_xboole_0(sK1,sK2),sK1)) = iProver_top ),
% 1.22/1.03      inference(superposition,[status(thm)],[c_0,c_2401]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_31,plain,
% 1.22/1.03      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 1.22/1.03      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_1743,plain,
% 1.22/1.03      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = k3_subset_1(X0,k1_xboole_0) ),
% 1.22/1.03      inference(superposition,[status(thm)],[c_738,c_740]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_1061,plain,
% 1.22/1.03      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 1.22/1.03      inference(superposition,[status(thm)],[c_741,c_742]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_1264,plain,
% 1.22/1.03      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 1.22/1.03      inference(superposition,[status(thm)],[c_1061,c_0]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_1748,plain,
% 1.22/1.03      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 1.22/1.03      inference(light_normalisation,[status(thm)],[c_1743,c_10,c_1264]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_1754,plain,
% 1.22/1.03      ( r1_tarski(k3_xboole_0(X0,k1_xboole_0),X0) != iProver_top
% 1.22/1.03      | v1_xboole_0(k3_xboole_0(X0,k1_xboole_0)) = iProver_top ),
% 1.22/1.03      inference(superposition,[status(thm)],[c_1748,c_734]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_1761,plain,
% 1.22/1.03      ( r1_tarski(k1_xboole_0,X0) != iProver_top
% 1.22/1.03      | v1_xboole_0(k1_xboole_0) = iProver_top ),
% 1.22/1.03      inference(light_normalisation,[status(thm)],[c_1754,c_1264]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_4,plain,
% 1.22/1.03      ( r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0) ),
% 1.22/1.03      inference(cnf_transformation,[],[f40]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_744,plain,
% 1.22/1.03      ( r1_tarski(X0,X1) = iProver_top
% 1.22/1.03      | r2_hidden(sK0(X0,X1),X0) = iProver_top ),
% 1.22/1.03      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_2,plain,
% 1.22/1.03      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 1.22/1.03      inference(cnf_transformation,[],[f38]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_746,plain,
% 1.22/1.03      ( r2_hidden(X0,X1) != iProver_top
% 1.22/1.03      | v1_xboole_0(X1) != iProver_top ),
% 1.22/1.03      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_1161,plain,
% 1.22/1.03      ( r1_tarski(X0,X1) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 1.22/1.03      inference(superposition,[status(thm)],[c_744,c_746]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_1895,plain,
% 1.22/1.03      ( r1_tarski(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) != iProver_top
% 1.22/1.03      | v1_xboole_0(k3_xboole_0(X1,X0)) = iProver_top ),
% 1.22/1.03      inference(superposition,[status(thm)],[c_1,c_1044]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_2440,plain,
% 1.22/1.03      ( r1_tarski(k3_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k3_subset_1(sK1,sK2)) != iProver_top
% 1.22/1.03      | v1_xboole_0(k3_xboole_0(k3_xboole_0(sK1,sK2),sK1)) = iProver_top ),
% 1.22/1.03      inference(superposition,[status(thm)],[c_1744,c_1895]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_2609,plain,
% 1.22/1.03      ( v1_xboole_0(k3_xboole_0(k3_xboole_0(sK1,sK2),sK1)) = iProver_top
% 1.22/1.03      | v1_xboole_0(k3_xboole_0(sK1,k3_xboole_0(sK1,sK2))) != iProver_top ),
% 1.22/1.03      inference(superposition,[status(thm)],[c_1161,c_2440]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_374,plain,
% 1.22/1.03      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 1.22/1.03      theory(equality) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_2675,plain,
% 1.22/1.03      ( v1_xboole_0(X0)
% 1.22/1.03      | ~ v1_xboole_0(k1_xboole_0)
% 1.22/1.03      | X0 != k1_xboole_0 ),
% 1.22/1.03      inference(instantiation,[status(thm)],[c_374]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_2676,plain,
% 1.22/1.03      ( X0 != k1_xboole_0
% 1.22/1.03      | v1_xboole_0(X0) = iProver_top
% 1.22/1.03      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 1.22/1.03      inference(predicate_to_equality,[status(thm)],[c_2675]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_2678,plain,
% 1.22/1.03      ( sK2 != k1_xboole_0
% 1.22/1.03      | v1_xboole_0(sK2) = iProver_top
% 1.22/1.03      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 1.22/1.03      inference(instantiation,[status(thm)],[c_2676]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_2008,plain,
% 1.22/1.03      ( r1_tarski(k3_xboole_0(k3_xboole_0(sK1,sK2),sK1),k3_subset_1(sK1,sK2)) != iProver_top
% 1.22/1.03      | v1_xboole_0(k3_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = iProver_top ),
% 1.22/1.03      inference(superposition,[status(thm)],[c_1744,c_1044]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_2255,plain,
% 1.22/1.03      ( v1_xboole_0(k3_xboole_0(k3_xboole_0(sK1,sK2),sK1)) != iProver_top
% 1.22/1.03      | v1_xboole_0(k3_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = iProver_top ),
% 1.22/1.03      inference(superposition,[status(thm)],[c_1161,c_2008]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_2315,plain,
% 1.22/1.03      ( v1_xboole_0(k3_xboole_0(k3_xboole_0(sK2,sK1),sK1)) != iProver_top
% 1.22/1.03      | v1_xboole_0(k3_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = iProver_top ),
% 1.22/1.03      inference(superposition,[status(thm)],[c_0,c_2255]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_3090,plain,
% 1.22/1.03      ( v1_xboole_0(k3_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = iProver_top
% 1.22/1.03      | v1_xboole_0(k3_xboole_0(sK2,sK1)) != iProver_top ),
% 1.22/1.03      inference(demodulation,[status(thm)],[c_3002,c_2315]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_3096,plain,
% 1.22/1.03      ( v1_xboole_0(k3_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = iProver_top
% 1.22/1.03      | v1_xboole_0(sK2) != iProver_top ),
% 1.22/1.03      inference(light_normalisation,[status(thm)],[c_3090,c_3002]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_2258,plain,
% 1.22/1.03      ( r1_tarski(k3_xboole_0(k3_xboole_0(sK2,sK1),sK1),k3_subset_1(sK1,sK2)) != iProver_top
% 1.22/1.03      | v1_xboole_0(k3_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = iProver_top ),
% 1.22/1.03      inference(superposition,[status(thm)],[c_0,c_2008]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_3084,plain,
% 1.22/1.03      ( r1_tarski(k3_xboole_0(sK2,sK1),k3_subset_1(sK1,sK2)) != iProver_top
% 1.22/1.03      | v1_xboole_0(k3_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = iProver_top ),
% 1.22/1.03      inference(demodulation,[status(thm)],[c_3002,c_2258]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_3121,plain,
% 1.22/1.03      ( r1_tarski(k3_xboole_0(sK2,sK1),k5_xboole_0(sK1,sK2)) != iProver_top
% 1.22/1.03      | v1_xboole_0(k3_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = iProver_top ),
% 1.22/1.03      inference(light_normalisation,[status(thm)],[c_3084,c_3091]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_3124,plain,
% 1.22/1.03      ( r1_tarski(sK2,k5_xboole_0(sK1,sK2)) != iProver_top
% 1.22/1.03      | v1_xboole_0(k3_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = iProver_top ),
% 1.22/1.03      inference(light_normalisation,[status(thm)],[c_3121,c_3002]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_3900,plain,
% 1.22/1.03      ( v1_xboole_0(k3_xboole_0(k3_xboole_0(sK1,sK2),sK1)) = iProver_top ),
% 1.22/1.03      inference(global_propositional_subsumption,
% 1.22/1.03                [status(thm)],
% 1.22/1.03                [c_2599,c_31,c_1761,c_2609,c_2678,c_3096,c_3124,c_3311]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_3907,plain,
% 1.22/1.03      ( v1_xboole_0(k3_xboole_0(k3_xboole_0(sK2,sK1),sK1)) = iProver_top ),
% 1.22/1.03      inference(superposition,[status(thm)],[c_0,c_3900]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_3913,plain,
% 1.22/1.03      ( v1_xboole_0(sK2) = iProver_top ),
% 1.22/1.03      inference(light_normalisation,[status(thm)],[c_3907,c_3002]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_3984,plain,
% 1.22/1.03      ( v1_xboole_0(k3_xboole_0(sK1,sK2)) = iProver_top
% 1.22/1.03      | v1_xboole_0(sK2) != iProver_top ),
% 1.22/1.03      inference(superposition,[status(thm)],[c_1161,c_3109]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_4051,plain,
% 1.22/1.03      ( v1_xboole_0(k3_xboole_0(sK1,sK2)) = iProver_top ),
% 1.22/1.03      inference(global_propositional_subsumption,
% 1.22/1.03                [status(thm)],
% 1.22/1.03                [c_3985,c_3913,c_3984]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_1457,plain,
% 1.22/1.03      ( k3_xboole_0(X0,X1) = X0 | v1_xboole_0(X0) != iProver_top ),
% 1.22/1.03      inference(superposition,[status(thm)],[c_1161,c_742]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_4470,plain,
% 1.22/1.03      ( k3_xboole_0(k3_xboole_0(sK1,sK2),X0) = k3_xboole_0(sK1,sK2) ),
% 1.22/1.03      inference(superposition,[status(thm)],[c_4051,c_1457]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_4612,plain,
% 1.22/1.03      ( k3_xboole_0(k3_xboole_0(sK2,sK1),X0) = k3_xboole_0(sK1,sK2) ),
% 1.22/1.03      inference(superposition,[status(thm)],[c_0,c_4470]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_4746,plain,
% 1.22/1.03      ( k3_xboole_0(sK2,X0) = k3_xboole_0(sK1,sK2) ),
% 1.22/1.03      inference(light_normalisation,[status(thm)],[c_4612,c_3002]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_4771,plain,
% 1.22/1.03      ( k3_xboole_0(X0,sK2) = k3_xboole_0(sK1,sK2) ),
% 1.22/1.03      inference(superposition,[status(thm)],[c_4746,c_0]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_1062,plain,
% 1.22/1.03      ( k3_xboole_0(sK2,k3_subset_1(sK1,sK2)) = sK2 | sK2 = k1_xboole_0 ),
% 1.22/1.03      inference(superposition,[status(thm)],[c_736,c_742]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_3310,plain,
% 1.22/1.03      ( k3_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = sK2 | sK2 = k1_xboole_0 ),
% 1.22/1.03      inference(demodulation,[status(thm)],[c_3091,c_1062]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_4773,plain,
% 1.22/1.03      ( k3_xboole_0(sK1,sK2) = sK2 | sK2 = k1_xboole_0 ),
% 1.22/1.03      inference(superposition,[status(thm)],[c_4746,c_3310]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_17,plain,
% 1.22/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
% 1.22/1.03      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_14,negated_conjecture,
% 1.22/1.03      ( ~ r1_tarski(sK2,k3_subset_1(sK1,sK2)) | k1_xboole_0 != sK2 ),
% 1.22/1.03      inference(cnf_transformation,[],[f59]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_737,plain,
% 1.22/1.03      ( k1_xboole_0 != sK2
% 1.22/1.03      | r1_tarski(sK2,k3_subset_1(sK1,sK2)) != iProver_top ),
% 1.22/1.03      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_3312,plain,
% 1.22/1.03      ( sK2 != k1_xboole_0
% 1.22/1.03      | r1_tarski(sK2,k5_xboole_0(sK1,sK2)) != iProver_top ),
% 1.22/1.03      inference(demodulation,[status(thm)],[c_3091,c_737]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_1609,plain,
% 1.22/1.03      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 1.22/1.03      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 1.22/1.03      | r1_tarski(X2,k3_subset_1(X1,X0)) = iProver_top
% 1.22/1.03      | v1_xboole_0(X0) != iProver_top ),
% 1.22/1.03      inference(superposition,[status(thm)],[c_1161,c_739]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_4414,plain,
% 1.22/1.03      ( m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top
% 1.22/1.03      | m1_subset_1(sK2,k1_zfmisc_1(sK1)) != iProver_top
% 1.22/1.03      | r1_tarski(X0,k5_xboole_0(sK1,sK2)) = iProver_top
% 1.22/1.03      | v1_xboole_0(sK2) != iProver_top ),
% 1.22/1.03      inference(superposition,[status(thm)],[c_3091,c_1609]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_4453,plain,
% 1.22/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) != iProver_top
% 1.22/1.03      | r1_tarski(sK2,k5_xboole_0(sK1,sK2)) = iProver_top
% 1.22/1.03      | v1_xboole_0(sK2) != iProver_top ),
% 1.22/1.03      inference(instantiation,[status(thm)],[c_4414]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_5038,plain,
% 1.22/1.03      ( k3_xboole_0(sK1,sK2) = sK2 ),
% 1.22/1.03      inference(global_propositional_subsumption,
% 1.22/1.03                [status(thm)],
% 1.22/1.03                [c_4773,c_17,c_3312,c_3913,c_4453]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_5422,plain,
% 1.22/1.03      ( k3_xboole_0(X0,sK2) = sK2 ),
% 1.22/1.03      inference(light_normalisation,[status(thm)],[c_4771,c_5038]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(c_5437,plain,
% 1.22/1.03      ( sK2 = k1_xboole_0 ),
% 1.22/1.03      inference(superposition,[status(thm)],[c_5422,c_1061]) ).
% 1.22/1.03  
% 1.22/1.03  cnf(contradiction,plain,
% 1.22/1.03      ( $false ),
% 1.22/1.03      inference(minisat,[status(thm)],[c_5437,c_4453,c_3913,c_3312,c_17]) ).
% 1.22/1.03  
% 1.22/1.03  
% 1.22/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 1.22/1.03  
% 1.22/1.03  ------                               Statistics
% 1.22/1.03  
% 1.22/1.03  ------ General
% 1.22/1.03  
% 1.22/1.03  abstr_ref_over_cycles:                  0
% 1.22/1.03  abstr_ref_under_cycles:                 0
% 1.22/1.03  gc_basic_clause_elim:                   0
% 1.22/1.03  forced_gc_time:                         0
% 1.22/1.03  parsing_time:                           0.008
% 1.22/1.03  unif_index_cands_time:                  0.
% 1.22/1.03  unif_index_add_time:                    0.
% 1.22/1.03  orderings_time:                         0.
% 1.22/1.03  out_proof_time:                         0.009
% 1.22/1.03  total_time:                             0.159
% 1.22/1.03  num_of_symbols:                         44
% 1.22/1.03  num_of_terms:                           5057
% 1.22/1.03  
% 1.22/1.03  ------ Preprocessing
% 1.22/1.03  
% 1.22/1.03  num_of_splits:                          0
% 1.22/1.03  num_of_split_atoms:                     0
% 1.22/1.03  num_of_reused_defs:                     0
% 1.22/1.03  num_eq_ax_congr_red:                    19
% 1.22/1.03  num_of_sem_filtered_clauses:            1
% 1.22/1.03  num_of_subtypes:                        0
% 1.22/1.03  monotx_restored_types:                  0
% 1.22/1.03  sat_num_of_epr_types:                   0
% 1.22/1.03  sat_num_of_non_cyclic_types:            0
% 1.22/1.03  sat_guarded_non_collapsed_types:        0
% 1.22/1.03  num_pure_diseq_elim:                    0
% 1.22/1.03  simp_replaced_by:                       0
% 1.22/1.03  res_preprocessed:                       84
% 1.22/1.03  prep_upred:                             0
% 1.22/1.03  prep_unflattend:                        4
% 1.22/1.03  smt_new_axioms:                         0
% 1.22/1.03  pred_elim_cands:                        4
% 1.22/1.03  pred_elim:                              1
% 1.22/1.03  pred_elim_cl:                           1
% 1.22/1.03  pred_elim_cycles:                       3
% 1.22/1.03  merged_defs:                            8
% 1.22/1.03  merged_defs_ncl:                        0
% 1.22/1.03  bin_hyper_res:                          8
% 1.22/1.03  prep_cycles:                            4
% 1.22/1.03  pred_elim_time:                         0.
% 1.22/1.03  splitting_time:                         0.
% 1.22/1.03  sem_filter_time:                        0.
% 1.22/1.03  monotx_time:                            0.
% 1.22/1.03  subtype_inf_time:                       0.
% 1.22/1.03  
% 1.22/1.03  ------ Problem properties
% 1.22/1.03  
% 1.22/1.03  clauses:                                16
% 1.22/1.03  conjectures:                            3
% 1.22/1.03  epr:                                    3
% 1.22/1.03  horn:                                   14
% 1.22/1.03  ground:                                 3
% 1.22/1.03  unary:                                  6
% 1.22/1.03  binary:                                 8
% 1.22/1.03  lits:                                   29
% 1.22/1.03  lits_eq:                                7
% 1.22/1.03  fd_pure:                                0
% 1.22/1.03  fd_pseudo:                              0
% 1.22/1.03  fd_cond:                                0
% 1.22/1.03  fd_pseudo_cond:                         0
% 1.22/1.03  ac_symbols:                             0
% 1.22/1.03  
% 1.22/1.03  ------ Propositional Solver
% 1.22/1.03  
% 1.22/1.03  prop_solver_calls:                      29
% 1.22/1.03  prop_fast_solver_calls:                 562
% 1.22/1.03  smt_solver_calls:                       0
% 1.22/1.03  smt_fast_solver_calls:                  0
% 1.22/1.03  prop_num_of_clauses:                    2046
% 1.22/1.03  prop_preprocess_simplified:             4982
% 1.22/1.03  prop_fo_subsumed:                       23
% 1.22/1.03  prop_solver_time:                       0.
% 1.22/1.03  smt_solver_time:                        0.
% 1.22/1.03  smt_fast_solver_time:                   0.
% 1.22/1.03  prop_fast_solver_time:                  0.
% 1.22/1.03  prop_unsat_core_time:                   0.
% 1.22/1.03  
% 1.22/1.03  ------ QBF
% 1.22/1.03  
% 1.22/1.03  qbf_q_res:                              0
% 1.22/1.03  qbf_num_tautologies:                    0
% 1.22/1.03  qbf_prep_cycles:                        0
% 1.22/1.03  
% 1.22/1.03  ------ BMC1
% 1.22/1.03  
% 1.22/1.03  bmc1_current_bound:                     -1
% 1.22/1.03  bmc1_last_solved_bound:                 -1
% 1.22/1.03  bmc1_unsat_core_size:                   -1
% 1.22/1.03  bmc1_unsat_core_parents_size:           -1
% 1.22/1.03  bmc1_merge_next_fun:                    0
% 1.22/1.03  bmc1_unsat_core_clauses_time:           0.
% 1.22/1.03  
% 1.22/1.03  ------ Instantiation
% 1.22/1.03  
% 1.22/1.03  inst_num_of_clauses:                    616
% 1.22/1.03  inst_num_in_passive:                    227
% 1.22/1.03  inst_num_in_active:                     257
% 1.22/1.03  inst_num_in_unprocessed:                138
% 1.22/1.03  inst_num_of_loops:                      420
% 1.22/1.03  inst_num_of_learning_restarts:          0
% 1.22/1.03  inst_num_moves_active_passive:          160
% 1.22/1.03  inst_lit_activity:                      0
% 1.22/1.03  inst_lit_activity_moves:                0
% 1.22/1.03  inst_num_tautologies:                   0
% 1.22/1.03  inst_num_prop_implied:                  0
% 1.22/1.03  inst_num_existing_simplified:           0
% 1.22/1.03  inst_num_eq_res_simplified:             0
% 1.22/1.03  inst_num_child_elim:                    0
% 1.22/1.03  inst_num_of_dismatching_blockings:      195
% 1.22/1.03  inst_num_of_non_proper_insts:           650
% 1.22/1.03  inst_num_of_duplicates:                 0
% 1.22/1.03  inst_inst_num_from_inst_to_res:         0
% 1.22/1.03  inst_dismatching_checking_time:         0.
% 1.22/1.03  
% 1.22/1.03  ------ Resolution
% 1.22/1.03  
% 1.22/1.03  res_num_of_clauses:                     0
% 1.22/1.03  res_num_in_passive:                     0
% 1.22/1.03  res_num_in_active:                      0
% 1.22/1.03  res_num_of_loops:                       88
% 1.22/1.03  res_forward_subset_subsumed:            53
% 1.22/1.03  res_backward_subset_subsumed:           16
% 1.22/1.03  res_forward_subsumed:                   0
% 1.22/1.03  res_backward_subsumed:                  0
% 1.22/1.03  res_forward_subsumption_resolution:     0
% 1.22/1.03  res_backward_subsumption_resolution:    0
% 1.22/1.03  res_clause_to_clause_subsumption:       652
% 1.22/1.03  res_orphan_elimination:                 0
% 1.22/1.03  res_tautology_del:                      78
% 1.22/1.03  res_num_eq_res_simplified:              0
% 1.22/1.03  res_num_sel_changes:                    0
% 1.22/1.03  res_moves_from_active_to_pass:          0
% 1.22/1.03  
% 1.22/1.03  ------ Superposition
% 1.22/1.03  
% 1.22/1.03  sup_time_total:                         0.
% 1.22/1.03  sup_time_generating:                    0.
% 1.22/1.03  sup_time_sim_full:                      0.
% 1.22/1.03  sup_time_sim_immed:                     0.
% 1.22/1.03  
% 1.22/1.03  sup_num_of_clauses:                     82
% 1.22/1.03  sup_num_in_active:                      44
% 1.22/1.03  sup_num_in_passive:                     38
% 1.22/1.03  sup_num_of_loops:                       83
% 1.22/1.03  sup_fw_superposition:                   191
% 1.22/1.03  sup_bw_superposition:                   106
% 1.22/1.03  sup_immediate_simplified:               51
% 1.22/1.03  sup_given_eliminated:                   3
% 1.22/1.03  comparisons_done:                       0
% 1.22/1.03  comparisons_avoided:                    0
% 1.22/1.03  
% 1.22/1.03  ------ Simplifications
% 1.22/1.03  
% 1.22/1.03  
% 1.22/1.03  sim_fw_subset_subsumed:                 7
% 1.22/1.03  sim_bw_subset_subsumed:                 21
% 1.22/1.03  sim_fw_subsumed:                        14
% 1.22/1.03  sim_bw_subsumed:                        0
% 1.22/1.03  sim_fw_subsumption_res:                 1
% 1.22/1.03  sim_bw_subsumption_res:                 0
% 1.22/1.03  sim_tautology_del:                      8
% 1.22/1.03  sim_eq_tautology_del:                   3
% 1.22/1.03  sim_eq_res_simp:                        0
% 1.22/1.03  sim_fw_demodulated:                     4
% 1.22/1.03  sim_bw_demodulated:                     44
% 1.22/1.03  sim_light_normalised:                   32
% 1.22/1.03  sim_joinable_taut:                      0
% 1.22/1.03  sim_joinable_simp:                      0
% 1.22/1.03  sim_ac_normalised:                      0
% 1.22/1.03  sim_smt_subsumption:                    0
% 1.22/1.03  
%------------------------------------------------------------------------------
