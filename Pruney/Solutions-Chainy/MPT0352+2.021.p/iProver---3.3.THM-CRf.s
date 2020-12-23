%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:39:34 EST 2020

% Result     : Theorem 39.14s
% Output     : CNFRefutation 39.14s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 370 expanded)
%              Number of clauses        :   77 ( 148 expanded)
%              Number of leaves         :   17 (  86 expanded)
%              Depth                    :   18
%              Number of atoms          :  225 ( 955 expanded)
%              Number of equality atoms :  117 ( 277 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :   12 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f15,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f76,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f61,f58])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f14,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f14])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f17,axiom,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f17])).

fof(f6,axiom,(
    ! [X0,X1,X2] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X2,X0,X1] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f73,plain,(
    ! [X2,X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(X0,X2)) ),
    inference(definition_unfolding,[],[f48,f58])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f28])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f25,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_tarski(X1,X2)
            <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f34,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_tarski(X1,X2)
          <~> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f37,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | ~ r1_tarski(X1,X2) )
          & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f38,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | ~ r1_tarski(X1,X2) )
          & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f37])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | ~ r1_tarski(X1,X2) )
          & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
     => ( ( ~ r1_tarski(k3_subset_1(X0,sK2),k3_subset_1(X0,X1))
          | ~ r1_tarski(X1,sK2) )
        & ( r1_tarski(k3_subset_1(X0,sK2),k3_subset_1(X0,X1))
          | r1_tarski(X1,sK2) )
        & m1_subset_1(sK2,k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | r1_tarski(X1,X2) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1))
            | ~ r1_tarski(sK1,X2) )
          & ( r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1))
            | r1_tarski(sK1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ( ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
      | ~ r1_tarski(sK1,sK2) )
    & ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
      | r1_tarski(sK1,sK2) )
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f38,f40,f39])).

fof(f69,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f41])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f71,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | ~ r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f68,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f41])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f70,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f66,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_18,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_15,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1042,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_15])).

cnf(c_1584,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_18,c_1042])).

cnf(c_12,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1779,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1584,c_12])).

cnf(c_5,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1781,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1779,c_5])).

cnf(c_14,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1539,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k4_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[status(thm)],[c_1042,c_14])).

cnf(c_17,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1551,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1539,c_17])).

cnf(c_2610,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_1551])).

cnf(c_6,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_730,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(X0,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3954,plain,
    ( r1_tarski(k4_xboole_0(X0,k1_xboole_0),k2_xboole_0(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2610,c_730])).

cnf(c_990,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_5,c_0])).

cnf(c_1128,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_990,c_12])).

cnf(c_1129,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(demodulation,[status(thm)],[c_1128,c_990])).

cnf(c_3983,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3954,c_1129])).

cnf(c_4570,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1781,c_3983])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X3)
    | r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_728,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X3) != iProver_top
    | r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_721,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_726,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_109941,plain,
    ( k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) ),
    inference(superposition,[status(thm)],[c_721,c_726])).

cnf(c_25,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | ~ r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_723,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) != iProver_top
    | r1_tarski(sK1,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_111274,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK2),k3_subset_1(sK0,sK1)) != iProver_top
    | r1_tarski(sK1,sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_109941,c_723])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_720,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_109942,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_720,c_726])).

cnf(c_111275,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) != iProver_top
    | r1_tarski(sK1,sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_111274,c_109942])).

cnf(c_112457,plain,
    ( r1_tarski(sK1,sK2) != iProver_top
    | r1_tarski(sK0,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_728,c_111275])).

cnf(c_11,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_756,plain,
    ( r1_tarski(sK1,sK2)
    | k4_xboole_0(sK1,sK2) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_757,plain,
    ( k4_xboole_0(sK1,sK2) != k1_xboole_0
    | r1_tarski(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_756])).

cnf(c_26,negated_conjecture,
    ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_722,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) = iProver_top
    | r1_tarski(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_732,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_6897,plain,
    ( k4_xboole_0(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) = k1_xboole_0
    | r1_tarski(sK1,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_722,c_732])).

cnf(c_7724,plain,
    ( k4_xboole_0(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) = k1_xboole_0
    | k4_xboole_0(sK1,sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6897,c_732])).

cnf(c_7753,plain,
    ( k4_xboole_0(sK1,sK2) = k1_xboole_0
    | k2_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK2)) = k2_xboole_0(k3_subset_1(sK0,sK1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_7724,c_12])).

cnf(c_7754,plain,
    ( k4_xboole_0(sK1,sK2) = k1_xboole_0
    | k2_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK2)) = k3_subset_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_7753,c_5])).

cnf(c_111268,plain,
    ( k4_xboole_0(sK1,sK2) = k1_xboole_0
    | k2_xboole_0(k3_subset_1(sK0,sK1),k4_xboole_0(sK0,sK2)) = k3_subset_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_109941,c_7754])).

cnf(c_111283,plain,
    ( k4_xboole_0(sK1,sK2) = k1_xboole_0
    | k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_111268,c_109942])).

cnf(c_1545,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X0,X1)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_14,c_1042])).

cnf(c_1285,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1042,c_12])).

cnf(c_1286,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_1285,c_5])).

cnf(c_2025,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_1286])).

cnf(c_3101,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
    inference(superposition,[status(thm)],[c_12,c_2025])).

cnf(c_3143,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_3101,c_2025])).

cnf(c_4837,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_3143,c_0])).

cnf(c_5525,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(k4_xboole_0(X1,X2),X0) ),
    inference(superposition,[status(thm)],[c_14,c_4837])).

cnf(c_50472,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,X2))) = k2_xboole_0(k4_xboole_0(X1,X2),X0) ),
    inference(superposition,[status(thm)],[c_0,c_5525])).

cnf(c_89297,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))),X2) = k2_xboole_0(X2,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1545,c_50472])).

cnf(c_89794,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))),X2) = X2 ),
    inference(demodulation,[status(thm)],[c_89297,c_5])).

cnf(c_90417,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))),X2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_89794,c_15])).

cnf(c_113191,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2) = k1_xboole_0
    | k4_xboole_0(sK1,sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_111283,c_90417])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_725,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_112187,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_109942,c_725])).

cnf(c_29,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_112448,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_112187,c_29])).

cnf(c_112452,plain,
    ( k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_112448,c_726])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_724,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_109935,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_720,c_724])).

cnf(c_111049,plain,
    ( k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_109935,c_109935,c_109942])).

cnf(c_112455,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_112452,c_111049])).

cnf(c_113251,plain,
    ( k4_xboole_0(sK1,sK2) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_113191,c_112455])).

cnf(c_135102,plain,
    ( r1_tarski(sK0,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_112457,c_757,c_113251])).

cnf(c_135106,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_4570,c_135102])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:37:16 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 39.14/5.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 39.14/5.48  
% 39.14/5.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 39.14/5.48  
% 39.14/5.48  ------  iProver source info
% 39.14/5.48  
% 39.14/5.48  git: date: 2020-06-30 10:37:57 +0100
% 39.14/5.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 39.14/5.48  git: non_committed_changes: false
% 39.14/5.48  git: last_make_outside_of_git: false
% 39.14/5.48  
% 39.14/5.48  ------ 
% 39.14/5.48  
% 39.14/5.48  ------ Input Options
% 39.14/5.48  
% 39.14/5.48  --out_options                           all
% 39.14/5.48  --tptp_safe_out                         true
% 39.14/5.48  --problem_path                          ""
% 39.14/5.48  --include_path                          ""
% 39.14/5.48  --clausifier                            res/vclausify_rel
% 39.14/5.48  --clausifier_options                    ""
% 39.14/5.48  --stdin                                 false
% 39.14/5.48  --stats_out                             all
% 39.14/5.48  
% 39.14/5.48  ------ General Options
% 39.14/5.48  
% 39.14/5.48  --fof                                   false
% 39.14/5.48  --time_out_real                         305.
% 39.14/5.48  --time_out_virtual                      -1.
% 39.14/5.48  --symbol_type_check                     false
% 39.14/5.48  --clausify_out                          false
% 39.14/5.48  --sig_cnt_out                           false
% 39.14/5.48  --trig_cnt_out                          false
% 39.14/5.48  --trig_cnt_out_tolerance                1.
% 39.14/5.48  --trig_cnt_out_sk_spl                   false
% 39.14/5.48  --abstr_cl_out                          false
% 39.14/5.48  
% 39.14/5.48  ------ Global Options
% 39.14/5.48  
% 39.14/5.48  --schedule                              default
% 39.14/5.48  --add_important_lit                     false
% 39.14/5.48  --prop_solver_per_cl                    1000
% 39.14/5.48  --min_unsat_core                        false
% 39.14/5.48  --soft_assumptions                      false
% 39.14/5.48  --soft_lemma_size                       3
% 39.14/5.48  --prop_impl_unit_size                   0
% 39.14/5.48  --prop_impl_unit                        []
% 39.14/5.48  --share_sel_clauses                     true
% 39.14/5.48  --reset_solvers                         false
% 39.14/5.48  --bc_imp_inh                            [conj_cone]
% 39.14/5.48  --conj_cone_tolerance                   3.
% 39.14/5.48  --extra_neg_conj                        none
% 39.14/5.48  --large_theory_mode                     true
% 39.14/5.48  --prolific_symb_bound                   200
% 39.14/5.48  --lt_threshold                          2000
% 39.14/5.48  --clause_weak_htbl                      true
% 39.14/5.48  --gc_record_bc_elim                     false
% 39.14/5.48  
% 39.14/5.48  ------ Preprocessing Options
% 39.14/5.48  
% 39.14/5.48  --preprocessing_flag                    true
% 39.14/5.48  --time_out_prep_mult                    0.1
% 39.14/5.48  --splitting_mode                        input
% 39.14/5.48  --splitting_grd                         true
% 39.14/5.48  --splitting_cvd                         false
% 39.14/5.48  --splitting_cvd_svl                     false
% 39.14/5.48  --splitting_nvd                         32
% 39.14/5.48  --sub_typing                            true
% 39.14/5.48  --prep_gs_sim                           true
% 39.14/5.48  --prep_unflatten                        true
% 39.14/5.48  --prep_res_sim                          true
% 39.14/5.48  --prep_upred                            true
% 39.14/5.48  --prep_sem_filter                       exhaustive
% 39.14/5.48  --prep_sem_filter_out                   false
% 39.14/5.48  --pred_elim                             true
% 39.14/5.48  --res_sim_input                         true
% 39.14/5.48  --eq_ax_congr_red                       true
% 39.14/5.48  --pure_diseq_elim                       true
% 39.14/5.48  --brand_transform                       false
% 39.14/5.48  --non_eq_to_eq                          false
% 39.14/5.48  --prep_def_merge                        true
% 39.14/5.48  --prep_def_merge_prop_impl              false
% 39.14/5.48  --prep_def_merge_mbd                    true
% 39.14/5.48  --prep_def_merge_tr_red                 false
% 39.14/5.48  --prep_def_merge_tr_cl                  false
% 39.14/5.48  --smt_preprocessing                     true
% 39.14/5.48  --smt_ac_axioms                         fast
% 39.14/5.48  --preprocessed_out                      false
% 39.14/5.48  --preprocessed_stats                    false
% 39.14/5.48  
% 39.14/5.48  ------ Abstraction refinement Options
% 39.14/5.48  
% 39.14/5.48  --abstr_ref                             []
% 39.14/5.48  --abstr_ref_prep                        false
% 39.14/5.48  --abstr_ref_until_sat                   false
% 39.14/5.48  --abstr_ref_sig_restrict                funpre
% 39.14/5.48  --abstr_ref_af_restrict_to_split_sk     false
% 39.14/5.48  --abstr_ref_under                       []
% 39.14/5.48  
% 39.14/5.48  ------ SAT Options
% 39.14/5.48  
% 39.14/5.48  --sat_mode                              false
% 39.14/5.48  --sat_fm_restart_options                ""
% 39.14/5.48  --sat_gr_def                            false
% 39.14/5.48  --sat_epr_types                         true
% 39.14/5.48  --sat_non_cyclic_types                  false
% 39.14/5.48  --sat_finite_models                     false
% 39.14/5.48  --sat_fm_lemmas                         false
% 39.14/5.48  --sat_fm_prep                           false
% 39.14/5.48  --sat_fm_uc_incr                        true
% 39.14/5.48  --sat_out_model                         small
% 39.14/5.48  --sat_out_clauses                       false
% 39.14/5.48  
% 39.14/5.48  ------ QBF Options
% 39.14/5.48  
% 39.14/5.48  --qbf_mode                              false
% 39.14/5.48  --qbf_elim_univ                         false
% 39.14/5.48  --qbf_dom_inst                          none
% 39.14/5.48  --qbf_dom_pre_inst                      false
% 39.14/5.48  --qbf_sk_in                             false
% 39.14/5.48  --qbf_pred_elim                         true
% 39.14/5.48  --qbf_split                             512
% 39.14/5.48  
% 39.14/5.48  ------ BMC1 Options
% 39.14/5.48  
% 39.14/5.48  --bmc1_incremental                      false
% 39.14/5.48  --bmc1_axioms                           reachable_all
% 39.14/5.48  --bmc1_min_bound                        0
% 39.14/5.48  --bmc1_max_bound                        -1
% 39.14/5.48  --bmc1_max_bound_default                -1
% 39.14/5.48  --bmc1_symbol_reachability              true
% 39.14/5.48  --bmc1_property_lemmas                  false
% 39.14/5.48  --bmc1_k_induction                      false
% 39.14/5.48  --bmc1_non_equiv_states                 false
% 39.14/5.48  --bmc1_deadlock                         false
% 39.14/5.48  --bmc1_ucm                              false
% 39.14/5.48  --bmc1_add_unsat_core                   none
% 39.14/5.48  --bmc1_unsat_core_children              false
% 39.14/5.48  --bmc1_unsat_core_extrapolate_axioms    false
% 39.14/5.48  --bmc1_out_stat                         full
% 39.14/5.48  --bmc1_ground_init                      false
% 39.14/5.48  --bmc1_pre_inst_next_state              false
% 39.14/5.48  --bmc1_pre_inst_state                   false
% 39.14/5.48  --bmc1_pre_inst_reach_state             false
% 39.14/5.48  --bmc1_out_unsat_core                   false
% 39.14/5.48  --bmc1_aig_witness_out                  false
% 39.14/5.48  --bmc1_verbose                          false
% 39.14/5.48  --bmc1_dump_clauses_tptp                false
% 39.14/5.48  --bmc1_dump_unsat_core_tptp             false
% 39.14/5.48  --bmc1_dump_file                        -
% 39.14/5.48  --bmc1_ucm_expand_uc_limit              128
% 39.14/5.48  --bmc1_ucm_n_expand_iterations          6
% 39.14/5.48  --bmc1_ucm_extend_mode                  1
% 39.14/5.48  --bmc1_ucm_init_mode                    2
% 39.14/5.48  --bmc1_ucm_cone_mode                    none
% 39.14/5.48  --bmc1_ucm_reduced_relation_type        0
% 39.14/5.48  --bmc1_ucm_relax_model                  4
% 39.14/5.48  --bmc1_ucm_full_tr_after_sat            true
% 39.14/5.48  --bmc1_ucm_expand_neg_assumptions       false
% 39.14/5.48  --bmc1_ucm_layered_model                none
% 39.14/5.48  --bmc1_ucm_max_lemma_size               10
% 39.14/5.48  
% 39.14/5.48  ------ AIG Options
% 39.14/5.48  
% 39.14/5.48  --aig_mode                              false
% 39.14/5.48  
% 39.14/5.48  ------ Instantiation Options
% 39.14/5.48  
% 39.14/5.48  --instantiation_flag                    true
% 39.14/5.48  --inst_sos_flag                         true
% 39.14/5.48  --inst_sos_phase                        true
% 39.14/5.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 39.14/5.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 39.14/5.48  --inst_lit_sel_side                     num_symb
% 39.14/5.48  --inst_solver_per_active                1400
% 39.14/5.48  --inst_solver_calls_frac                1.
% 39.14/5.48  --inst_passive_queue_type               priority_queues
% 39.14/5.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 39.14/5.48  --inst_passive_queues_freq              [25;2]
% 39.14/5.48  --inst_dismatching                      true
% 39.14/5.48  --inst_eager_unprocessed_to_passive     true
% 39.14/5.48  --inst_prop_sim_given                   true
% 39.14/5.48  --inst_prop_sim_new                     false
% 39.14/5.48  --inst_subs_new                         false
% 39.14/5.48  --inst_eq_res_simp                      false
% 39.14/5.48  --inst_subs_given                       false
% 39.14/5.48  --inst_orphan_elimination               true
% 39.14/5.48  --inst_learning_loop_flag               true
% 39.14/5.48  --inst_learning_start                   3000
% 39.14/5.48  --inst_learning_factor                  2
% 39.14/5.48  --inst_start_prop_sim_after_learn       3
% 39.14/5.48  --inst_sel_renew                        solver
% 39.14/5.48  --inst_lit_activity_flag                true
% 39.14/5.48  --inst_restr_to_given                   false
% 39.14/5.48  --inst_activity_threshold               500
% 39.14/5.48  --inst_out_proof                        true
% 39.14/5.48  
% 39.14/5.48  ------ Resolution Options
% 39.14/5.48  
% 39.14/5.48  --resolution_flag                       true
% 39.14/5.48  --res_lit_sel                           adaptive
% 39.14/5.48  --res_lit_sel_side                      none
% 39.14/5.48  --res_ordering                          kbo
% 39.14/5.48  --res_to_prop_solver                    active
% 39.14/5.48  --res_prop_simpl_new                    false
% 39.14/5.48  --res_prop_simpl_given                  true
% 39.14/5.48  --res_passive_queue_type                priority_queues
% 39.14/5.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 39.14/5.48  --res_passive_queues_freq               [15;5]
% 39.14/5.48  --res_forward_subs                      full
% 39.14/5.48  --res_backward_subs                     full
% 39.14/5.48  --res_forward_subs_resolution           true
% 39.14/5.48  --res_backward_subs_resolution          true
% 39.14/5.48  --res_orphan_elimination                true
% 39.14/5.48  --res_time_limit                        2.
% 39.14/5.48  --res_out_proof                         true
% 39.14/5.48  
% 39.14/5.48  ------ Superposition Options
% 39.14/5.48  
% 39.14/5.48  --superposition_flag                    true
% 39.14/5.48  --sup_passive_queue_type                priority_queues
% 39.14/5.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 39.14/5.48  --sup_passive_queues_freq               [8;1;4]
% 39.14/5.48  --demod_completeness_check              fast
% 39.14/5.48  --demod_use_ground                      true
% 39.14/5.48  --sup_to_prop_solver                    passive
% 39.14/5.48  --sup_prop_simpl_new                    true
% 39.14/5.48  --sup_prop_simpl_given                  true
% 39.14/5.48  --sup_fun_splitting                     true
% 39.14/5.48  --sup_smt_interval                      50000
% 39.14/5.48  
% 39.14/5.48  ------ Superposition Simplification Setup
% 39.14/5.48  
% 39.14/5.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 39.14/5.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 39.14/5.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 39.14/5.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 39.14/5.48  --sup_full_triv                         [TrivRules;PropSubs]
% 39.14/5.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 39.14/5.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 39.14/5.48  --sup_immed_triv                        [TrivRules]
% 39.14/5.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 39.14/5.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 39.14/5.48  --sup_immed_bw_main                     []
% 39.14/5.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 39.14/5.48  --sup_input_triv                        [Unflattening;TrivRules]
% 39.14/5.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 39.14/5.48  --sup_input_bw                          []
% 39.14/5.48  
% 39.14/5.48  ------ Combination Options
% 39.14/5.48  
% 39.14/5.48  --comb_res_mult                         3
% 39.14/5.48  --comb_sup_mult                         2
% 39.14/5.48  --comb_inst_mult                        10
% 39.14/5.48  
% 39.14/5.48  ------ Debug Options
% 39.14/5.48  
% 39.14/5.48  --dbg_backtrace                         false
% 39.14/5.48  --dbg_dump_prop_clauses                 false
% 39.14/5.48  --dbg_dump_prop_clauses_file            -
% 39.14/5.48  --dbg_out_stat                          false
% 39.14/5.48  ------ Parsing...
% 39.14/5.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 39.14/5.48  
% 39.14/5.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 39.14/5.48  
% 39.14/5.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 39.14/5.48  
% 39.14/5.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 39.14/5.48  ------ Proving...
% 39.14/5.48  ------ Problem Properties 
% 39.14/5.48  
% 39.14/5.48  
% 39.14/5.48  clauses                                 27
% 39.14/5.48  conjectures                             4
% 39.14/5.48  EPR                                     1
% 39.14/5.48  Horn                                    26
% 39.14/5.48  unary                                   18
% 39.14/5.48  binary                                  8
% 39.14/5.48  lits                                    37
% 39.14/5.48  lits eq                                 18
% 39.14/5.48  fd_pure                                 0
% 39.14/5.48  fd_pseudo                               0
% 39.14/5.48  fd_cond                                 0
% 39.14/5.48  fd_pseudo_cond                          0
% 39.14/5.48  AC symbols                              0
% 39.14/5.48  
% 39.14/5.48  ------ Schedule dynamic 5 is on 
% 39.14/5.48  
% 39.14/5.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 39.14/5.48  
% 39.14/5.48  
% 39.14/5.48  ------ 
% 39.14/5.48  Current options:
% 39.14/5.48  ------ 
% 39.14/5.48  
% 39.14/5.48  ------ Input Options
% 39.14/5.48  
% 39.14/5.48  --out_options                           all
% 39.14/5.48  --tptp_safe_out                         true
% 39.14/5.48  --problem_path                          ""
% 39.14/5.48  --include_path                          ""
% 39.14/5.48  --clausifier                            res/vclausify_rel
% 39.14/5.48  --clausifier_options                    ""
% 39.14/5.48  --stdin                                 false
% 39.14/5.48  --stats_out                             all
% 39.14/5.48  
% 39.14/5.48  ------ General Options
% 39.14/5.48  
% 39.14/5.48  --fof                                   false
% 39.14/5.48  --time_out_real                         305.
% 39.14/5.48  --time_out_virtual                      -1.
% 39.14/5.48  --symbol_type_check                     false
% 39.14/5.48  --clausify_out                          false
% 39.14/5.48  --sig_cnt_out                           false
% 39.14/5.48  --trig_cnt_out                          false
% 39.14/5.48  --trig_cnt_out_tolerance                1.
% 39.14/5.48  --trig_cnt_out_sk_spl                   false
% 39.14/5.48  --abstr_cl_out                          false
% 39.14/5.48  
% 39.14/5.48  ------ Global Options
% 39.14/5.48  
% 39.14/5.48  --schedule                              default
% 39.14/5.48  --add_important_lit                     false
% 39.14/5.48  --prop_solver_per_cl                    1000
% 39.14/5.48  --min_unsat_core                        false
% 39.14/5.48  --soft_assumptions                      false
% 39.14/5.48  --soft_lemma_size                       3
% 39.14/5.48  --prop_impl_unit_size                   0
% 39.14/5.48  --prop_impl_unit                        []
% 39.14/5.48  --share_sel_clauses                     true
% 39.14/5.48  --reset_solvers                         false
% 39.14/5.48  --bc_imp_inh                            [conj_cone]
% 39.14/5.48  --conj_cone_tolerance                   3.
% 39.14/5.48  --extra_neg_conj                        none
% 39.14/5.48  --large_theory_mode                     true
% 39.14/5.48  --prolific_symb_bound                   200
% 39.14/5.48  --lt_threshold                          2000
% 39.14/5.48  --clause_weak_htbl                      true
% 39.14/5.48  --gc_record_bc_elim                     false
% 39.14/5.48  
% 39.14/5.48  ------ Preprocessing Options
% 39.14/5.48  
% 39.14/5.48  --preprocessing_flag                    true
% 39.14/5.48  --time_out_prep_mult                    0.1
% 39.14/5.48  --splitting_mode                        input
% 39.14/5.48  --splitting_grd                         true
% 39.14/5.48  --splitting_cvd                         false
% 39.14/5.48  --splitting_cvd_svl                     false
% 39.14/5.48  --splitting_nvd                         32
% 39.14/5.48  --sub_typing                            true
% 39.14/5.48  --prep_gs_sim                           true
% 39.14/5.48  --prep_unflatten                        true
% 39.14/5.48  --prep_res_sim                          true
% 39.14/5.48  --prep_upred                            true
% 39.14/5.48  --prep_sem_filter                       exhaustive
% 39.14/5.48  --prep_sem_filter_out                   false
% 39.14/5.48  --pred_elim                             true
% 39.14/5.48  --res_sim_input                         true
% 39.14/5.48  --eq_ax_congr_red                       true
% 39.14/5.48  --pure_diseq_elim                       true
% 39.14/5.48  --brand_transform                       false
% 39.14/5.48  --non_eq_to_eq                          false
% 39.14/5.48  --prep_def_merge                        true
% 39.14/5.48  --prep_def_merge_prop_impl              false
% 39.14/5.48  --prep_def_merge_mbd                    true
% 39.14/5.48  --prep_def_merge_tr_red                 false
% 39.14/5.48  --prep_def_merge_tr_cl                  false
% 39.14/5.48  --smt_preprocessing                     true
% 39.14/5.48  --smt_ac_axioms                         fast
% 39.14/5.48  --preprocessed_out                      false
% 39.14/5.48  --preprocessed_stats                    false
% 39.14/5.48  
% 39.14/5.48  ------ Abstraction refinement Options
% 39.14/5.48  
% 39.14/5.48  --abstr_ref                             []
% 39.14/5.48  --abstr_ref_prep                        false
% 39.14/5.48  --abstr_ref_until_sat                   false
% 39.14/5.48  --abstr_ref_sig_restrict                funpre
% 39.14/5.48  --abstr_ref_af_restrict_to_split_sk     false
% 39.14/5.48  --abstr_ref_under                       []
% 39.14/5.48  
% 39.14/5.48  ------ SAT Options
% 39.14/5.48  
% 39.14/5.48  --sat_mode                              false
% 39.14/5.48  --sat_fm_restart_options                ""
% 39.14/5.48  --sat_gr_def                            false
% 39.14/5.48  --sat_epr_types                         true
% 39.14/5.48  --sat_non_cyclic_types                  false
% 39.14/5.48  --sat_finite_models                     false
% 39.14/5.48  --sat_fm_lemmas                         false
% 39.14/5.48  --sat_fm_prep                           false
% 39.14/5.48  --sat_fm_uc_incr                        true
% 39.14/5.48  --sat_out_model                         small
% 39.14/5.48  --sat_out_clauses                       false
% 39.14/5.48  
% 39.14/5.48  ------ QBF Options
% 39.14/5.48  
% 39.14/5.48  --qbf_mode                              false
% 39.14/5.48  --qbf_elim_univ                         false
% 39.14/5.48  --qbf_dom_inst                          none
% 39.14/5.48  --qbf_dom_pre_inst                      false
% 39.14/5.48  --qbf_sk_in                             false
% 39.14/5.48  --qbf_pred_elim                         true
% 39.14/5.48  --qbf_split                             512
% 39.14/5.48  
% 39.14/5.48  ------ BMC1 Options
% 39.14/5.48  
% 39.14/5.48  --bmc1_incremental                      false
% 39.14/5.48  --bmc1_axioms                           reachable_all
% 39.14/5.48  --bmc1_min_bound                        0
% 39.14/5.48  --bmc1_max_bound                        -1
% 39.14/5.48  --bmc1_max_bound_default                -1
% 39.14/5.48  --bmc1_symbol_reachability              true
% 39.14/5.48  --bmc1_property_lemmas                  false
% 39.14/5.48  --bmc1_k_induction                      false
% 39.14/5.48  --bmc1_non_equiv_states                 false
% 39.14/5.48  --bmc1_deadlock                         false
% 39.14/5.48  --bmc1_ucm                              false
% 39.14/5.48  --bmc1_add_unsat_core                   none
% 39.14/5.48  --bmc1_unsat_core_children              false
% 39.14/5.48  --bmc1_unsat_core_extrapolate_axioms    false
% 39.14/5.48  --bmc1_out_stat                         full
% 39.14/5.48  --bmc1_ground_init                      false
% 39.14/5.48  --bmc1_pre_inst_next_state              false
% 39.14/5.48  --bmc1_pre_inst_state                   false
% 39.14/5.48  --bmc1_pre_inst_reach_state             false
% 39.14/5.48  --bmc1_out_unsat_core                   false
% 39.14/5.48  --bmc1_aig_witness_out                  false
% 39.14/5.48  --bmc1_verbose                          false
% 39.14/5.48  --bmc1_dump_clauses_tptp                false
% 39.14/5.48  --bmc1_dump_unsat_core_tptp             false
% 39.14/5.48  --bmc1_dump_file                        -
% 39.14/5.48  --bmc1_ucm_expand_uc_limit              128
% 39.14/5.48  --bmc1_ucm_n_expand_iterations          6
% 39.14/5.48  --bmc1_ucm_extend_mode                  1
% 39.14/5.48  --bmc1_ucm_init_mode                    2
% 39.14/5.48  --bmc1_ucm_cone_mode                    none
% 39.14/5.48  --bmc1_ucm_reduced_relation_type        0
% 39.14/5.48  --bmc1_ucm_relax_model                  4
% 39.14/5.48  --bmc1_ucm_full_tr_after_sat            true
% 39.14/5.48  --bmc1_ucm_expand_neg_assumptions       false
% 39.14/5.48  --bmc1_ucm_layered_model                none
% 39.14/5.48  --bmc1_ucm_max_lemma_size               10
% 39.14/5.48  
% 39.14/5.48  ------ AIG Options
% 39.14/5.48  
% 39.14/5.48  --aig_mode                              false
% 39.14/5.48  
% 39.14/5.48  ------ Instantiation Options
% 39.14/5.48  
% 39.14/5.48  --instantiation_flag                    true
% 39.14/5.48  --inst_sos_flag                         true
% 39.14/5.48  --inst_sos_phase                        true
% 39.14/5.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 39.14/5.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 39.14/5.48  --inst_lit_sel_side                     none
% 39.14/5.48  --inst_solver_per_active                1400
% 39.14/5.48  --inst_solver_calls_frac                1.
% 39.14/5.48  --inst_passive_queue_type               priority_queues
% 39.14/5.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 39.14/5.48  --inst_passive_queues_freq              [25;2]
% 39.14/5.48  --inst_dismatching                      true
% 39.14/5.48  --inst_eager_unprocessed_to_passive     true
% 39.14/5.48  --inst_prop_sim_given                   true
% 39.14/5.48  --inst_prop_sim_new                     false
% 39.14/5.48  --inst_subs_new                         false
% 39.14/5.48  --inst_eq_res_simp                      false
% 39.14/5.48  --inst_subs_given                       false
% 39.14/5.48  --inst_orphan_elimination               true
% 39.14/5.48  --inst_learning_loop_flag               true
% 39.14/5.48  --inst_learning_start                   3000
% 39.14/5.48  --inst_learning_factor                  2
% 39.14/5.48  --inst_start_prop_sim_after_learn       3
% 39.14/5.48  --inst_sel_renew                        solver
% 39.14/5.48  --inst_lit_activity_flag                true
% 39.14/5.48  --inst_restr_to_given                   false
% 39.14/5.48  --inst_activity_threshold               500
% 39.14/5.48  --inst_out_proof                        true
% 39.14/5.48  
% 39.14/5.48  ------ Resolution Options
% 39.14/5.48  
% 39.14/5.48  --resolution_flag                       false
% 39.14/5.48  --res_lit_sel                           adaptive
% 39.14/5.48  --res_lit_sel_side                      none
% 39.14/5.48  --res_ordering                          kbo
% 39.14/5.48  --res_to_prop_solver                    active
% 39.14/5.48  --res_prop_simpl_new                    false
% 39.14/5.48  --res_prop_simpl_given                  true
% 39.14/5.48  --res_passive_queue_type                priority_queues
% 39.14/5.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 39.14/5.48  --res_passive_queues_freq               [15;5]
% 39.14/5.48  --res_forward_subs                      full
% 39.14/5.48  --res_backward_subs                     full
% 39.14/5.48  --res_forward_subs_resolution           true
% 39.14/5.48  --res_backward_subs_resolution          true
% 39.14/5.48  --res_orphan_elimination                true
% 39.14/5.48  --res_time_limit                        2.
% 39.14/5.48  --res_out_proof                         true
% 39.14/5.48  
% 39.14/5.48  ------ Superposition Options
% 39.14/5.48  
% 39.14/5.48  --superposition_flag                    true
% 39.14/5.48  --sup_passive_queue_type                priority_queues
% 39.14/5.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 39.14/5.48  --sup_passive_queues_freq               [8;1;4]
% 39.14/5.48  --demod_completeness_check              fast
% 39.14/5.48  --demod_use_ground                      true
% 39.14/5.48  --sup_to_prop_solver                    passive
% 39.14/5.48  --sup_prop_simpl_new                    true
% 39.14/5.48  --sup_prop_simpl_given                  true
% 39.14/5.48  --sup_fun_splitting                     true
% 39.14/5.48  --sup_smt_interval                      50000
% 39.14/5.48  
% 39.14/5.48  ------ Superposition Simplification Setup
% 39.14/5.48  
% 39.14/5.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 39.14/5.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 39.14/5.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 39.14/5.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 39.14/5.48  --sup_full_triv                         [TrivRules;PropSubs]
% 39.14/5.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 39.14/5.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 39.14/5.48  --sup_immed_triv                        [TrivRules]
% 39.14/5.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 39.14/5.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 39.14/5.48  --sup_immed_bw_main                     []
% 39.14/5.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 39.14/5.48  --sup_input_triv                        [Unflattening;TrivRules]
% 39.14/5.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 39.14/5.48  --sup_input_bw                          []
% 39.14/5.48  
% 39.14/5.48  ------ Combination Options
% 39.14/5.48  
% 39.14/5.48  --comb_res_mult                         3
% 39.14/5.48  --comb_sup_mult                         2
% 39.14/5.48  --comb_inst_mult                        10
% 39.14/5.48  
% 39.14/5.48  ------ Debug Options
% 39.14/5.48  
% 39.14/5.48  --dbg_backtrace                         false
% 39.14/5.48  --dbg_dump_prop_clauses                 false
% 39.14/5.48  --dbg_dump_prop_clauses_file            -
% 39.14/5.48  --dbg_out_stat                          false
% 39.14/5.48  
% 39.14/5.48  
% 39.14/5.48  
% 39.14/5.48  
% 39.14/5.48  ------ Proving...
% 39.14/5.48  
% 39.14/5.48  
% 39.14/5.48  % SZS status Theorem for theBenchmark.p
% 39.14/5.48  
% 39.14/5.48   Resolution empty clause
% 39.14/5.48  
% 39.14/5.48  % SZS output start CNFRefutation for theBenchmark.p
% 39.14/5.48  
% 39.14/5.48  fof(f18,axiom,(
% 39.14/5.48    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 39.14/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.14/5.48  
% 39.14/5.48  fof(f61,plain,(
% 39.14/5.48    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 39.14/5.48    inference(cnf_transformation,[],[f18])).
% 39.14/5.48  
% 39.14/5.48  fof(f15,axiom,(
% 39.14/5.48    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 39.14/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.14/5.48  
% 39.14/5.48  fof(f58,plain,(
% 39.14/5.48    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 39.14/5.48    inference(cnf_transformation,[],[f15])).
% 39.14/5.48  
% 39.14/5.48  fof(f76,plain,(
% 39.14/5.48    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 39.14/5.48    inference(definition_unfolding,[],[f61,f58])).
% 39.14/5.48  
% 39.14/5.48  fof(f1,axiom,(
% 39.14/5.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 39.14/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.14/5.48  
% 39.14/5.48  fof(f42,plain,(
% 39.14/5.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 39.14/5.48    inference(cnf_transformation,[],[f1])).
% 39.14/5.48  
% 39.14/5.48  fof(f14,axiom,(
% 39.14/5.48    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 39.14/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.14/5.48  
% 39.14/5.48  fof(f57,plain,(
% 39.14/5.48    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 39.14/5.48    inference(cnf_transformation,[],[f14])).
% 39.14/5.48  
% 39.14/5.48  fof(f11,axiom,(
% 39.14/5.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 39.14/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.14/5.48  
% 39.14/5.48  fof(f54,plain,(
% 39.14/5.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 39.14/5.48    inference(cnf_transformation,[],[f11])).
% 39.14/5.48  
% 39.14/5.48  fof(f5,axiom,(
% 39.14/5.48    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 39.14/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.14/5.48  
% 39.14/5.48  fof(f47,plain,(
% 39.14/5.48    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 39.14/5.48    inference(cnf_transformation,[],[f5])).
% 39.14/5.48  
% 39.14/5.48  fof(f13,axiom,(
% 39.14/5.48    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 39.14/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.14/5.48  
% 39.14/5.48  fof(f56,plain,(
% 39.14/5.48    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 39.14/5.48    inference(cnf_transformation,[],[f13])).
% 39.14/5.48  
% 39.14/5.48  fof(f17,axiom,(
% 39.14/5.48    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0),
% 39.14/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.14/5.48  
% 39.14/5.48  fof(f60,plain,(
% 39.14/5.48    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0) )),
% 39.14/5.48    inference(cnf_transformation,[],[f17])).
% 39.14/5.48  
% 39.14/5.48  fof(f6,axiom,(
% 39.14/5.48    ! [X0,X1,X2] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2))),
% 39.14/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.14/5.48  
% 39.14/5.48  fof(f48,plain,(
% 39.14/5.48    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2))) )),
% 39.14/5.48    inference(cnf_transformation,[],[f6])).
% 39.14/5.48  
% 39.14/5.48  fof(f73,plain,(
% 39.14/5.48    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(X0,X2))) )),
% 39.14/5.48    inference(definition_unfolding,[],[f48,f58])).
% 39.14/5.48  
% 39.14/5.48  fof(f9,axiom,(
% 39.14/5.48    ! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2)))),
% 39.14/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.14/5.48  
% 39.14/5.48  fof(f28,plain,(
% 39.14/5.48    ! [X0,X1,X2,X3] : (r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2)) | (~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)))),
% 39.14/5.48    inference(ennf_transformation,[],[f9])).
% 39.14/5.48  
% 39.14/5.48  fof(f29,plain,(
% 39.14/5.48    ! [X0,X1,X2,X3] : (r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))),
% 39.14/5.48    inference(flattening,[],[f28])).
% 39.14/5.48  
% 39.14/5.48  fof(f51,plain,(
% 39.14/5.48    ( ! [X2,X0,X3,X1] : (r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) )),
% 39.14/5.48    inference(cnf_transformation,[],[f29])).
% 39.14/5.48  
% 39.14/5.48  fof(f25,conjecture,(
% 39.14/5.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 39.14/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.14/5.48  
% 39.14/5.48  fof(f26,negated_conjecture,(
% 39.14/5.48    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 39.14/5.48    inference(negated_conjecture,[],[f25])).
% 39.14/5.48  
% 39.14/5.48  fof(f34,plain,(
% 39.14/5.48    ? [X0,X1] : (? [X2] : ((r1_tarski(X1,X2) <~> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 39.14/5.48    inference(ennf_transformation,[],[f26])).
% 39.14/5.48  
% 39.14/5.48  fof(f37,plain,(
% 39.14/5.48    ? [X0,X1] : (? [X2] : (((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 39.14/5.48    inference(nnf_transformation,[],[f34])).
% 39.14/5.48  
% 39.14/5.48  fof(f38,plain,(
% 39.14/5.48    ? [X0,X1] : (? [X2] : ((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 39.14/5.48    inference(flattening,[],[f37])).
% 39.14/5.48  
% 39.14/5.48  fof(f40,plain,(
% 39.14/5.48    ( ! [X0,X1] : (? [X2] : ((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) => ((~r1_tarski(k3_subset_1(X0,sK2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,sK2)) & (r1_tarski(k3_subset_1(X0,sK2),k3_subset_1(X0,X1)) | r1_tarski(X1,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(X0)))) )),
% 39.14/5.48    introduced(choice_axiom,[])).
% 39.14/5.48  
% 39.14/5.48  fof(f39,plain,(
% 39.14/5.48    ? [X0,X1] : (? [X2] : ((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : ((~r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1)) | ~r1_tarski(sK1,X2)) & (r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1)) | r1_tarski(sK1,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 39.14/5.48    introduced(choice_axiom,[])).
% 39.14/5.48  
% 39.14/5.48  fof(f41,plain,(
% 39.14/5.48    ((~r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | ~r1_tarski(sK1,sK2)) & (r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | r1_tarski(sK1,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 39.14/5.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f38,f40,f39])).
% 39.14/5.48  
% 39.14/5.48  fof(f69,plain,(
% 39.14/5.48    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 39.14/5.48    inference(cnf_transformation,[],[f41])).
% 39.14/5.48  
% 39.14/5.48  fof(f22,axiom,(
% 39.14/5.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 39.14/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.14/5.48  
% 39.14/5.48  fof(f31,plain,(
% 39.14/5.48    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 39.14/5.48    inference(ennf_transformation,[],[f22])).
% 39.14/5.48  
% 39.14/5.48  fof(f65,plain,(
% 39.14/5.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 39.14/5.48    inference(cnf_transformation,[],[f31])).
% 39.14/5.48  
% 39.14/5.48  fof(f71,plain,(
% 39.14/5.48    ~r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | ~r1_tarski(sK1,sK2)),
% 39.14/5.48    inference(cnf_transformation,[],[f41])).
% 39.14/5.48  
% 39.14/5.48  fof(f68,plain,(
% 39.14/5.48    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 39.14/5.48    inference(cnf_transformation,[],[f41])).
% 39.14/5.48  
% 39.14/5.48  fof(f10,axiom,(
% 39.14/5.48    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 39.14/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.14/5.48  
% 39.14/5.48  fof(f36,plain,(
% 39.14/5.48    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 39.14/5.48    inference(nnf_transformation,[],[f10])).
% 39.14/5.48  
% 39.14/5.48  fof(f52,plain,(
% 39.14/5.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 39.14/5.48    inference(cnf_transformation,[],[f36])).
% 39.14/5.48  
% 39.14/5.48  fof(f70,plain,(
% 39.14/5.48    r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | r1_tarski(sK1,sK2)),
% 39.14/5.48    inference(cnf_transformation,[],[f41])).
% 39.14/5.48  
% 39.14/5.48  fof(f53,plain,(
% 39.14/5.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 39.14/5.48    inference(cnf_transformation,[],[f36])).
% 39.14/5.48  
% 39.14/5.48  fof(f23,axiom,(
% 39.14/5.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 39.14/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.14/5.48  
% 39.14/5.48  fof(f32,plain,(
% 39.14/5.48    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 39.14/5.48    inference(ennf_transformation,[],[f23])).
% 39.14/5.48  
% 39.14/5.48  fof(f66,plain,(
% 39.14/5.48    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 39.14/5.48    inference(cnf_transformation,[],[f32])).
% 39.14/5.48  
% 39.14/5.48  fof(f24,axiom,(
% 39.14/5.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 39.14/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.14/5.48  
% 39.14/5.48  fof(f33,plain,(
% 39.14/5.48    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 39.14/5.48    inference(ennf_transformation,[],[f24])).
% 39.14/5.48  
% 39.14/5.48  fof(f67,plain,(
% 39.14/5.48    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 39.14/5.48    inference(cnf_transformation,[],[f33])).
% 39.14/5.48  
% 39.14/5.48  cnf(c_18,plain,
% 39.14/5.48      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
% 39.14/5.48      inference(cnf_transformation,[],[f76]) ).
% 39.14/5.48  
% 39.14/5.48  cnf(c_0,plain,
% 39.14/5.48      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 39.14/5.48      inference(cnf_transformation,[],[f42]) ).
% 39.14/5.48  
% 39.14/5.48  cnf(c_15,plain,
% 39.14/5.48      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 39.14/5.48      inference(cnf_transformation,[],[f57]) ).
% 39.14/5.48  
% 39.14/5.48  cnf(c_1042,plain,
% 39.14/5.48      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 39.14/5.48      inference(superposition,[status(thm)],[c_0,c_15]) ).
% 39.14/5.48  
% 39.14/5.48  cnf(c_1584,plain,
% 39.14/5.48      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
% 39.14/5.48      inference(superposition,[status(thm)],[c_18,c_1042]) ).
% 39.14/5.48  
% 39.14/5.48  cnf(c_12,plain,
% 39.14/5.48      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 39.14/5.48      inference(cnf_transformation,[],[f54]) ).
% 39.14/5.48  
% 39.14/5.48  cnf(c_1779,plain,
% 39.14/5.48      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = k2_xboole_0(X0,k1_xboole_0) ),
% 39.14/5.48      inference(superposition,[status(thm)],[c_1584,c_12]) ).
% 39.14/5.48  
% 39.14/5.48  cnf(c_5,plain,
% 39.14/5.48      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 39.14/5.48      inference(cnf_transformation,[],[f47]) ).
% 39.14/5.48  
% 39.14/5.48  cnf(c_1781,plain,
% 39.14/5.48      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 39.14/5.48      inference(light_normalisation,[status(thm)],[c_1779,c_5]) ).
% 39.14/5.48  
% 39.14/5.48  cnf(c_14,plain,
% 39.14/5.48      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 39.14/5.48      inference(cnf_transformation,[],[f56]) ).
% 39.14/5.48  
% 39.14/5.48  cnf(c_1539,plain,
% 39.14/5.48      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k4_xboole_0(k1_xboole_0,X2) ),
% 39.14/5.48      inference(superposition,[status(thm)],[c_1042,c_14]) ).
% 39.14/5.48  
% 39.14/5.48  cnf(c_17,plain,
% 39.14/5.48      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 39.14/5.48      inference(cnf_transformation,[],[f60]) ).
% 39.14/5.48  
% 39.14/5.48  cnf(c_1551,plain,
% 39.14/5.48      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k1_xboole_0 ),
% 39.14/5.48      inference(demodulation,[status(thm)],[c_1539,c_17]) ).
% 39.14/5.48  
% 39.14/5.48  cnf(c_2610,plain,
% 39.14/5.48      ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X0))) = k1_xboole_0 ),
% 39.14/5.48      inference(superposition,[status(thm)],[c_0,c_1551]) ).
% 39.14/5.48  
% 39.14/5.48  cnf(c_6,plain,
% 39.14/5.48      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(X0,X2)) ),
% 39.14/5.48      inference(cnf_transformation,[],[f73]) ).
% 39.14/5.48  
% 39.14/5.48  cnf(c_730,plain,
% 39.14/5.48      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(X0,X2)) = iProver_top ),
% 39.14/5.48      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 39.14/5.48  
% 39.14/5.48  cnf(c_3954,plain,
% 39.14/5.48      ( r1_tarski(k4_xboole_0(X0,k1_xboole_0),k2_xboole_0(X0,X1)) = iProver_top ),
% 39.14/5.48      inference(superposition,[status(thm)],[c_2610,c_730]) ).
% 39.14/5.48  
% 39.14/5.48  cnf(c_990,plain,
% 39.14/5.48      ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
% 39.14/5.48      inference(superposition,[status(thm)],[c_5,c_0]) ).
% 39.14/5.48  
% 39.14/5.48  cnf(c_1128,plain,
% 39.14/5.48      ( k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(k1_xboole_0,X0) ),
% 39.14/5.48      inference(superposition,[status(thm)],[c_990,c_12]) ).
% 39.14/5.48  
% 39.14/5.48  cnf(c_1129,plain,
% 39.14/5.48      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 39.14/5.48      inference(demodulation,[status(thm)],[c_1128,c_990]) ).
% 39.14/5.48  
% 39.14/5.48  cnf(c_3983,plain,
% 39.14/5.48      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 39.14/5.48      inference(light_normalisation,[status(thm)],[c_3954,c_1129]) ).
% 39.14/5.48  
% 39.14/5.48  cnf(c_4570,plain,
% 39.14/5.48      ( r1_tarski(X0,X0) = iProver_top ),
% 39.14/5.48      inference(superposition,[status(thm)],[c_1781,c_3983]) ).
% 39.14/5.48  
% 39.14/5.48  cnf(c_9,plain,
% 39.14/5.48      ( ~ r1_tarski(X0,X1)
% 39.14/5.48      | ~ r1_tarski(X2,X3)
% 39.14/5.48      | r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2)) ),
% 39.14/5.48      inference(cnf_transformation,[],[f51]) ).
% 39.14/5.48  
% 39.14/5.48  cnf(c_728,plain,
% 39.14/5.48      ( r1_tarski(X0,X1) != iProver_top
% 39.14/5.48      | r1_tarski(X2,X3) != iProver_top
% 39.14/5.48      | r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2)) = iProver_top ),
% 39.14/5.48      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 39.14/5.48  
% 39.14/5.48  cnf(c_27,negated_conjecture,
% 39.14/5.48      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
% 39.14/5.48      inference(cnf_transformation,[],[f69]) ).
% 39.14/5.48  
% 39.14/5.48  cnf(c_721,plain,
% 39.14/5.48      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
% 39.14/5.48      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 39.14/5.48  
% 39.14/5.48  cnf(c_22,plain,
% 39.14/5.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 39.14/5.48      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 39.14/5.48      inference(cnf_transformation,[],[f65]) ).
% 39.14/5.48  
% 39.14/5.48  cnf(c_726,plain,
% 39.14/5.48      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 39.14/5.48      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 39.14/5.48      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 39.14/5.48  
% 39.14/5.48  cnf(c_109941,plain,
% 39.14/5.48      ( k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) ),
% 39.14/5.48      inference(superposition,[status(thm)],[c_721,c_726]) ).
% 39.14/5.48  
% 39.14/5.48  cnf(c_25,negated_conjecture,
% 39.14/5.48      ( ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
% 39.14/5.48      | ~ r1_tarski(sK1,sK2) ),
% 39.14/5.48      inference(cnf_transformation,[],[f71]) ).
% 39.14/5.48  
% 39.14/5.48  cnf(c_723,plain,
% 39.14/5.48      ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) != iProver_top
% 39.14/5.48      | r1_tarski(sK1,sK2) != iProver_top ),
% 39.14/5.48      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 39.14/5.48  
% 39.14/5.48  cnf(c_111274,plain,
% 39.14/5.48      ( r1_tarski(k4_xboole_0(sK0,sK2),k3_subset_1(sK0,sK1)) != iProver_top
% 39.14/5.48      | r1_tarski(sK1,sK2) != iProver_top ),
% 39.14/5.48      inference(demodulation,[status(thm)],[c_109941,c_723]) ).
% 39.14/5.48  
% 39.14/5.48  cnf(c_28,negated_conjecture,
% 39.14/5.48      ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
% 39.14/5.48      inference(cnf_transformation,[],[f68]) ).
% 39.14/5.48  
% 39.14/5.48  cnf(c_720,plain,
% 39.14/5.48      ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) = iProver_top ),
% 39.14/5.48      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 39.14/5.48  
% 39.14/5.48  cnf(c_109942,plain,
% 39.14/5.48      ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
% 39.14/5.48      inference(superposition,[status(thm)],[c_720,c_726]) ).
% 39.14/5.48  
% 39.14/5.48  cnf(c_111275,plain,
% 39.14/5.48      ( r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) != iProver_top
% 39.14/5.48      | r1_tarski(sK1,sK2) != iProver_top ),
% 39.14/5.48      inference(light_normalisation,[status(thm)],[c_111274,c_109942]) ).
% 39.14/5.48  
% 39.14/5.48  cnf(c_112457,plain,
% 39.14/5.48      ( r1_tarski(sK1,sK2) != iProver_top | r1_tarski(sK0,sK0) != iProver_top ),
% 39.14/5.48      inference(superposition,[status(thm)],[c_728,c_111275]) ).
% 39.14/5.48  
% 39.14/5.48  cnf(c_11,plain,
% 39.14/5.48      ( r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0 ),
% 39.14/5.48      inference(cnf_transformation,[],[f52]) ).
% 39.14/5.48  
% 39.14/5.48  cnf(c_756,plain,
% 39.14/5.48      ( r1_tarski(sK1,sK2) | k4_xboole_0(sK1,sK2) != k1_xboole_0 ),
% 39.14/5.48      inference(instantiation,[status(thm)],[c_11]) ).
% 39.14/5.48  
% 39.14/5.48  cnf(c_757,plain,
% 39.14/5.48      ( k4_xboole_0(sK1,sK2) != k1_xboole_0
% 39.14/5.48      | r1_tarski(sK1,sK2) = iProver_top ),
% 39.14/5.48      inference(predicate_to_equality,[status(thm)],[c_756]) ).
% 39.14/5.48  
% 39.14/5.48  cnf(c_26,negated_conjecture,
% 39.14/5.48      ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
% 39.14/5.48      | r1_tarski(sK1,sK2) ),
% 39.14/5.48      inference(cnf_transformation,[],[f70]) ).
% 39.14/5.48  
% 39.14/5.48  cnf(c_722,plain,
% 39.14/5.48      ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) = iProver_top
% 39.14/5.48      | r1_tarski(sK1,sK2) = iProver_top ),
% 39.14/5.48      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 39.14/5.48  
% 39.14/5.48  cnf(c_10,plain,
% 39.14/5.48      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 39.14/5.48      inference(cnf_transformation,[],[f53]) ).
% 39.14/5.48  
% 39.14/5.48  cnf(c_732,plain,
% 39.14/5.48      ( k4_xboole_0(X0,X1) = k1_xboole_0 | r1_tarski(X0,X1) != iProver_top ),
% 39.14/5.48      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 39.14/5.48  
% 39.14/5.48  cnf(c_6897,plain,
% 39.14/5.48      ( k4_xboole_0(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) = k1_xboole_0
% 39.14/5.48      | r1_tarski(sK1,sK2) = iProver_top ),
% 39.14/5.48      inference(superposition,[status(thm)],[c_722,c_732]) ).
% 39.14/5.48  
% 39.14/5.48  cnf(c_7724,plain,
% 39.14/5.48      ( k4_xboole_0(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) = k1_xboole_0
% 39.14/5.48      | k4_xboole_0(sK1,sK2) = k1_xboole_0 ),
% 39.14/5.48      inference(superposition,[status(thm)],[c_6897,c_732]) ).
% 39.14/5.48  
% 39.14/5.48  cnf(c_7753,plain,
% 39.14/5.48      ( k4_xboole_0(sK1,sK2) = k1_xboole_0
% 39.14/5.48      | k2_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK2)) = k2_xboole_0(k3_subset_1(sK0,sK1),k1_xboole_0) ),
% 39.14/5.48      inference(superposition,[status(thm)],[c_7724,c_12]) ).
% 39.14/5.48  
% 39.14/5.48  cnf(c_7754,plain,
% 39.14/5.48      ( k4_xboole_0(sK1,sK2) = k1_xboole_0
% 39.14/5.48      | k2_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK2)) = k3_subset_1(sK0,sK1) ),
% 39.14/5.48      inference(demodulation,[status(thm)],[c_7753,c_5]) ).
% 39.14/5.48  
% 39.14/5.48  cnf(c_111268,plain,
% 39.14/5.48      ( k4_xboole_0(sK1,sK2) = k1_xboole_0
% 39.14/5.48      | k2_xboole_0(k3_subset_1(sK0,sK1),k4_xboole_0(sK0,sK2)) = k3_subset_1(sK0,sK1) ),
% 39.14/5.48      inference(demodulation,[status(thm)],[c_109941,c_7754]) ).
% 39.14/5.48  
% 39.14/5.48  cnf(c_111283,plain,
% 39.14/5.48      ( k4_xboole_0(sK1,sK2) = k1_xboole_0
% 39.14/5.48      | k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK0,sK1) ),
% 39.14/5.48      inference(light_normalisation,[status(thm)],[c_111268,c_109942]) ).
% 39.14/5.48  
% 39.14/5.48  cnf(c_1545,plain,
% 39.14/5.48      ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X0,X1)))) = k1_xboole_0 ),
% 39.14/5.48      inference(superposition,[status(thm)],[c_14,c_1042]) ).
% 39.14/5.48  
% 39.14/5.48  cnf(c_1285,plain,
% 39.14/5.48      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
% 39.14/5.48      inference(superposition,[status(thm)],[c_1042,c_12]) ).
% 39.14/5.48  
% 39.14/5.48  cnf(c_1286,plain,
% 39.14/5.48      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
% 39.14/5.48      inference(demodulation,[status(thm)],[c_1285,c_5]) ).
% 39.14/5.48  
% 39.14/5.48  cnf(c_2025,plain,
% 39.14/5.48      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X1,X0) ),
% 39.14/5.48      inference(superposition,[status(thm)],[c_0,c_1286]) ).
% 39.14/5.48  
% 39.14/5.48  cnf(c_3101,plain,
% 39.14/5.48      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
% 39.14/5.48      inference(superposition,[status(thm)],[c_12,c_2025]) ).
% 39.14/5.48  
% 39.14/5.48  cnf(c_3143,plain,
% 39.14/5.48      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
% 39.14/5.48      inference(demodulation,[status(thm)],[c_3101,c_2025]) ).
% 39.14/5.48  
% 39.14/5.48  cnf(c_4837,plain,
% 39.14/5.48      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 39.14/5.48      inference(superposition,[status(thm)],[c_3143,c_0]) ).
% 39.14/5.48  
% 39.14/5.48  cnf(c_5525,plain,
% 39.14/5.48      ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(k4_xboole_0(X1,X2),X0) ),
% 39.14/5.48      inference(superposition,[status(thm)],[c_14,c_4837]) ).
% 39.14/5.48  
% 39.14/5.48  cnf(c_50472,plain,
% 39.14/5.48      ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,X2))) = k2_xboole_0(k4_xboole_0(X1,X2),X0) ),
% 39.14/5.48      inference(superposition,[status(thm)],[c_0,c_5525]) ).
% 39.14/5.48  
% 39.14/5.48  cnf(c_89297,plain,
% 39.14/5.48      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))),X2) = k2_xboole_0(X2,k1_xboole_0) ),
% 39.14/5.48      inference(superposition,[status(thm)],[c_1545,c_50472]) ).
% 39.14/5.48  
% 39.14/5.48  cnf(c_89794,plain,
% 39.14/5.48      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))),X2) = X2 ),
% 39.14/5.48      inference(demodulation,[status(thm)],[c_89297,c_5]) ).
% 39.14/5.48  
% 39.14/5.48  cnf(c_90417,plain,
% 39.14/5.48      ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))),X2) = k1_xboole_0 ),
% 39.14/5.48      inference(superposition,[status(thm)],[c_89794,c_15]) ).
% 39.14/5.48  
% 39.14/5.48  cnf(c_113191,plain,
% 39.14/5.48      ( k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2) = k1_xboole_0
% 39.14/5.48      | k4_xboole_0(sK1,sK2) = k1_xboole_0 ),
% 39.14/5.48      inference(superposition,[status(thm)],[c_111283,c_90417]) ).
% 39.14/5.48  
% 39.14/5.48  cnf(c_23,plain,
% 39.14/5.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 39.14/5.48      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 39.14/5.48      inference(cnf_transformation,[],[f66]) ).
% 39.14/5.48  
% 39.14/5.48  cnf(c_725,plain,
% 39.14/5.48      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 39.14/5.48      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 39.14/5.48      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 39.14/5.48  
% 39.14/5.48  cnf(c_112187,plain,
% 39.14/5.48      ( m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) = iProver_top
% 39.14/5.48      | m1_subset_1(sK1,k1_zfmisc_1(sK0)) != iProver_top ),
% 39.14/5.48      inference(superposition,[status(thm)],[c_109942,c_725]) ).
% 39.14/5.48  
% 39.14/5.48  cnf(c_29,plain,
% 39.14/5.48      ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) = iProver_top ),
% 39.14/5.48      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 39.14/5.48  
% 39.14/5.48  cnf(c_112448,plain,
% 39.14/5.48      ( m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) = iProver_top ),
% 39.14/5.48      inference(global_propositional_subsumption,[status(thm)],[c_112187,c_29]) ).
% 39.14/5.48  
% 39.14/5.48  cnf(c_112452,plain,
% 39.14/5.48      ( k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 39.14/5.48      inference(superposition,[status(thm)],[c_112448,c_726]) ).
% 39.14/5.48  
% 39.14/5.48  cnf(c_24,plain,
% 39.14/5.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 39.14/5.48      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 39.14/5.48      inference(cnf_transformation,[],[f67]) ).
% 39.14/5.48  
% 39.14/5.48  cnf(c_724,plain,
% 39.14/5.48      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 39.14/5.48      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 39.14/5.48      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 39.14/5.48  
% 39.14/5.48  cnf(c_109935,plain,
% 39.14/5.48      ( k3_subset_1(sK0,k3_subset_1(sK0,sK1)) = sK1 ),
% 39.14/5.48      inference(superposition,[status(thm)],[c_720,c_724]) ).
% 39.14/5.48  
% 39.14/5.48  cnf(c_111049,plain,
% 39.14/5.48      ( k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) = sK1 ),
% 39.14/5.48      inference(light_normalisation,[status(thm)],[c_109935,c_109935,c_109942]) ).
% 39.14/5.48  
% 39.14/5.48  cnf(c_112455,plain,
% 39.14/5.48      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = sK1 ),
% 39.14/5.48      inference(light_normalisation,[status(thm)],[c_112452,c_111049]) ).
% 39.14/5.48  
% 39.14/5.48  cnf(c_113251,plain,
% 39.14/5.48      ( k4_xboole_0(sK1,sK2) = k1_xboole_0 ),
% 39.14/5.48      inference(light_normalisation,[status(thm)],[c_113191,c_112455]) ).
% 39.14/5.48  
% 39.14/5.48  cnf(c_135102,plain,
% 39.14/5.48      ( r1_tarski(sK0,sK0) != iProver_top ),
% 39.14/5.48      inference(global_propositional_subsumption,
% 39.14/5.48                [status(thm)],
% 39.14/5.48                [c_112457,c_757,c_113251]) ).
% 39.14/5.48  
% 39.14/5.48  cnf(c_135106,plain,
% 39.14/5.48      ( $false ),
% 39.14/5.48      inference(superposition,[status(thm)],[c_4570,c_135102]) ).
% 39.14/5.48  
% 39.14/5.48  
% 39.14/5.48  % SZS output end CNFRefutation for theBenchmark.p
% 39.14/5.48  
% 39.14/5.48  ------                               Statistics
% 39.14/5.48  
% 39.14/5.48  ------ General
% 39.14/5.48  
% 39.14/5.48  abstr_ref_over_cycles:                  0
% 39.14/5.48  abstr_ref_under_cycles:                 0
% 39.14/5.48  gc_basic_clause_elim:                   0
% 39.14/5.48  forced_gc_time:                         0
% 39.14/5.48  parsing_time:                           0.007
% 39.14/5.48  unif_index_cands_time:                  0.
% 39.14/5.48  unif_index_add_time:                    0.
% 39.14/5.48  orderings_time:                         0.
% 39.14/5.48  out_proof_time:                         0.021
% 39.14/5.48  total_time:                             4.702
% 39.14/5.48  num_of_symbols:                         41
% 39.14/5.48  num_of_terms:                           209941
% 39.14/5.48  
% 39.14/5.48  ------ Preprocessing
% 39.14/5.48  
% 39.14/5.48  num_of_splits:                          0
% 39.14/5.48  num_of_split_atoms:                     0
% 39.14/5.48  num_of_reused_defs:                     0
% 39.14/5.48  num_eq_ax_congr_red:                    0
% 39.14/5.48  num_of_sem_filtered_clauses:            1
% 39.14/5.48  num_of_subtypes:                        0
% 39.14/5.48  monotx_restored_types:                  0
% 39.14/5.48  sat_num_of_epr_types:                   0
% 39.14/5.48  sat_num_of_non_cyclic_types:            0
% 39.14/5.48  sat_guarded_non_collapsed_types:        0
% 39.14/5.48  num_pure_diseq_elim:                    0
% 39.14/5.48  simp_replaced_by:                       0
% 39.14/5.48  res_preprocessed:                       125
% 39.14/5.48  prep_upred:                             0
% 39.14/5.48  prep_unflattend:                        0
% 39.14/5.48  smt_new_axioms:                         0
% 39.14/5.48  pred_elim_cands:                        2
% 39.14/5.48  pred_elim:                              0
% 39.14/5.48  pred_elim_cl:                           0
% 39.14/5.48  pred_elim_cycles:                       2
% 39.14/5.48  merged_defs:                            16
% 39.14/5.48  merged_defs_ncl:                        0
% 39.14/5.48  bin_hyper_res:                          16
% 39.14/5.48  prep_cycles:                            4
% 39.14/5.48  pred_elim_time:                         0.
% 39.14/5.48  splitting_time:                         0.
% 39.14/5.48  sem_filter_time:                        0.
% 39.14/5.48  monotx_time:                            0.
% 39.14/5.48  subtype_inf_time:                       0.
% 39.14/5.48  
% 39.14/5.48  ------ Problem properties
% 39.14/5.48  
% 39.14/5.48  clauses:                                27
% 39.14/5.48  conjectures:                            4
% 39.14/5.48  epr:                                    1
% 39.14/5.48  horn:                                   26
% 39.14/5.48  ground:                                 4
% 39.14/5.48  unary:                                  18
% 39.14/5.48  binary:                                 8
% 39.14/5.48  lits:                                   37
% 39.14/5.48  lits_eq:                                18
% 39.14/5.48  fd_pure:                                0
% 39.14/5.48  fd_pseudo:                              0
% 39.14/5.48  fd_cond:                                0
% 39.14/5.48  fd_pseudo_cond:                         0
% 39.14/5.48  ac_symbols:                             1
% 39.14/5.48  
% 39.14/5.48  ------ Propositional Solver
% 39.14/5.48  
% 39.14/5.48  prop_solver_calls:                      48
% 39.14/5.48  prop_fast_solver_calls:                 1624
% 39.14/5.48  smt_solver_calls:                       0
% 39.14/5.48  smt_fast_solver_calls:                  0
% 39.14/5.48  prop_num_of_clauses:                    47431
% 39.14/5.48  prop_preprocess_simplified:             41712
% 39.14/5.48  prop_fo_subsumed:                       23
% 39.14/5.49  prop_solver_time:                       0.
% 39.14/5.49  smt_solver_time:                        0.
% 39.14/5.49  smt_fast_solver_time:                   0.
% 39.14/5.49  prop_fast_solver_time:                  0.
% 39.14/5.49  prop_unsat_core_time:                   0.
% 39.14/5.49  
% 39.14/5.49  ------ QBF
% 39.14/5.49  
% 39.14/5.49  qbf_q_res:                              0
% 39.14/5.49  qbf_num_tautologies:                    0
% 39.14/5.49  qbf_prep_cycles:                        0
% 39.14/5.49  
% 39.14/5.49  ------ BMC1
% 39.14/5.49  
% 39.14/5.49  bmc1_current_bound:                     -1
% 39.14/5.49  bmc1_last_solved_bound:                 -1
% 39.14/5.49  bmc1_unsat_core_size:                   -1
% 39.14/5.49  bmc1_unsat_core_parents_size:           -1
% 39.14/5.49  bmc1_merge_next_fun:                    0
% 39.14/5.49  bmc1_unsat_core_clauses_time:           0.
% 39.14/5.49  
% 39.14/5.49  ------ Instantiation
% 39.14/5.49  
% 39.14/5.49  inst_num_of_clauses:                    7533
% 39.14/5.49  inst_num_in_passive:                    4972
% 39.14/5.49  inst_num_in_active:                     1591
% 39.14/5.49  inst_num_in_unprocessed:                970
% 39.14/5.49  inst_num_of_loops:                      2460
% 39.14/5.49  inst_num_of_learning_restarts:          0
% 39.14/5.49  inst_num_moves_active_passive:          865
% 39.14/5.49  inst_lit_activity:                      0
% 39.14/5.49  inst_lit_activity_moves:                3
% 39.14/5.49  inst_num_tautologies:                   0
% 39.14/5.49  inst_num_prop_implied:                  0
% 39.14/5.49  inst_num_existing_simplified:           0
% 39.14/5.49  inst_num_eq_res_simplified:             0
% 39.14/5.49  inst_num_child_elim:                    0
% 39.14/5.49  inst_num_of_dismatching_blockings:      4503
% 39.14/5.49  inst_num_of_non_proper_insts:           6369
% 39.14/5.49  inst_num_of_duplicates:                 0
% 39.14/5.49  inst_inst_num_from_inst_to_res:         0
% 39.14/5.49  inst_dismatching_checking_time:         0.
% 39.14/5.49  
% 39.14/5.49  ------ Resolution
% 39.14/5.49  
% 39.14/5.49  res_num_of_clauses:                     0
% 39.14/5.49  res_num_in_passive:                     0
% 39.14/5.49  res_num_in_active:                      0
% 39.14/5.49  res_num_of_loops:                       129
% 39.14/5.49  res_forward_subset_subsumed:            1345
% 39.14/5.49  res_backward_subset_subsumed:           6
% 39.14/5.49  res_forward_subsumed:                   0
% 39.14/5.49  res_backward_subsumed:                  0
% 39.14/5.49  res_forward_subsumption_resolution:     0
% 39.14/5.49  res_backward_subsumption_resolution:    0
% 39.14/5.49  res_clause_to_clause_subsumption:       289265
% 39.14/5.49  res_orphan_elimination:                 0
% 39.14/5.49  res_tautology_del:                      499
% 39.14/5.49  res_num_eq_res_simplified:              0
% 39.14/5.49  res_num_sel_changes:                    0
% 39.14/5.49  res_moves_from_active_to_pass:          0
% 39.14/5.49  
% 39.14/5.49  ------ Superposition
% 39.14/5.49  
% 39.14/5.49  sup_time_total:                         0.
% 39.14/5.49  sup_time_generating:                    0.
% 39.14/5.49  sup_time_sim_full:                      0.
% 39.14/5.49  sup_time_sim_immed:                     0.
% 39.14/5.49  
% 39.14/5.49  sup_num_of_clauses:                     6611
% 39.14/5.49  sup_num_in_active:                      206
% 39.14/5.49  sup_num_in_passive:                     6405
% 39.14/5.49  sup_num_of_loops:                       491
% 39.14/5.49  sup_fw_superposition:                   29477
% 39.14/5.49  sup_bw_superposition:                   16673
% 39.14/5.49  sup_immediate_simplified:               26939
% 39.14/5.49  sup_given_eliminated:                   9
% 39.14/5.49  comparisons_done:                       0
% 39.14/5.49  comparisons_avoided:                    105
% 39.14/5.49  
% 39.14/5.49  ------ Simplifications
% 39.14/5.49  
% 39.14/5.49  
% 39.14/5.49  sim_fw_subset_subsumed:                 452
% 39.14/5.49  sim_bw_subset_subsumed:                 4714
% 39.14/5.49  sim_fw_subsumed:                        4980
% 39.14/5.49  sim_bw_subsumed:                        239
% 39.14/5.49  sim_fw_subsumption_res:                 0
% 39.14/5.49  sim_bw_subsumption_res:                 0
% 39.14/5.49  sim_tautology_del:                      920
% 39.14/5.49  sim_eq_tautology_del:                   4679
% 39.14/5.49  sim_eq_res_simp:                        0
% 39.14/5.49  sim_fw_demodulated:                     23047
% 39.14/5.49  sim_bw_demodulated:                     449
% 39.14/5.49  sim_light_normalised:                   7058
% 39.14/5.49  sim_joinable_taut:                      342
% 39.14/5.49  sim_joinable_simp:                      0
% 39.14/5.49  sim_ac_normalised:                      0
% 39.14/5.49  sim_smt_subsumption:                    0
% 39.14/5.49  
%------------------------------------------------------------------------------
