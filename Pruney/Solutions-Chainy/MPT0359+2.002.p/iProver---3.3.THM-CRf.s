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
% DateTime   : Thu Dec  3 11:40:01 EST 2020

% Result     : Theorem 31.47s
% Output     : CNFRefutation 31.47s
% Verified   : 
% Statistics : Number of formulae       :  192 (2121 expanded)
%              Number of clauses        :  115 ( 736 expanded)
%              Number of leaves         :   24 ( 475 expanded)
%              Depth                    :   22
%              Number of atoms          :  397 (4614 expanded)
%              Number of equality atoms :  258 (2459 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f27,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(k3_subset_1(X0,X1),X1)
      <=> k2_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(k3_subset_1(X0,X1),X1)
        <=> k2_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f27])).

fof(f35,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(k3_subset_1(X0,X1),X1)
      <~> k2_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f40,plain,(
    ? [X0,X1] :
      ( ( k2_subset_1(X0) != X1
        | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
      & ( k2_subset_1(X0) = X1
        | r1_tarski(k3_subset_1(X0,X1),X1) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f41,plain,(
    ? [X0,X1] :
      ( ( k2_subset_1(X0) != X1
        | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
      & ( k2_subset_1(X0) = X1
        | r1_tarski(k3_subset_1(X0,X1),X1) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f40])).

fof(f42,plain,
    ( ? [X0,X1] :
        ( ( k2_subset_1(X0) != X1
          | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
        & ( k2_subset_1(X0) = X1
          | r1_tarski(k3_subset_1(X0,X1),X1) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ( k2_subset_1(sK0) != sK1
        | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) )
      & ( k2_subset_1(sK0) = sK1
        | r1_tarski(k3_subset_1(sK0,sK1),sK1) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ( k2_subset_1(sK0) != sK1
      | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) )
    & ( k2_subset_1(sK0) = sK1
      | r1_tarski(k3_subset_1(sK0,sK1),sK1) )
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f41,f42])).

fof(f74,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f43])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f18,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f24,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f17,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f17])).

fof(f79,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f70,f63])).

fof(f86,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f64,f79])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_tarski(X1,X2)
              | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f8,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f26,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f26])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f87,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f65,f51])).

fof(f23,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f23])).

fof(f89,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k6_subset_1(X0,X1) ),
    inference(definition_unfolding,[],[f69,f51])).

fof(f21,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f78,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f58,f59])).

fof(f84,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f57,f78,f78])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f10,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f77,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f56,f51])).

fof(f85,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f60,f77,f78])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f9])).

fof(f83,plain,(
    ! [X0,X1] : k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) ),
    inference(definition_unfolding,[],[f55,f51,f77])).

fof(f75,plain,
    ( k2_subset_1(sK0) = sK1
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f91,plain,
    ( k3_subset_1(sK0,k1_xboole_0) = sK1
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(definition_unfolding,[],[f75,f79])).

fof(f76,plain,
    ( k2_subset_1(sK0) != sK1
    | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f90,plain,
    ( k3_subset_1(sK0,k1_xboole_0) != sK1
    | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(definition_unfolding,[],[f76,f79])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f36])).

fof(f48,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f93,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f46])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f49,f51])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f50,f51])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_839,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_845,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_5483,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_839,c_845])).

cnf(c_15,plain,
    ( k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X0)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_843,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1341,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(k3_subset_1(X1,X0),X1) = iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_15,c_843])).

cnf(c_9,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_60,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_5281,plain,
    ( r1_tarski(k3_subset_1(X1,X0),X1) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1341,c_60])).

cnf(c_5282,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(k3_subset_1(X1,X0),X1) = iProver_top ),
    inference(renaming,[status(thm)],[c_5281])).

cnf(c_5674,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) != iProver_top
    | r1_tarski(sK1,sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5483,c_5282])).

cnf(c_23,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1797,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_1798,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1797])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_848,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_20,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_864,plain,
    ( k6_subset_1(X0,X1) = k3_subset_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_848,c_20])).

cnf(c_5604,plain,
    ( k6_subset_1(sK0,sK1) = k3_subset_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_839,c_864])).

cnf(c_18,plain,
    ( m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_846,plain,
    ( m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_5887,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5604,c_846])).

cnf(c_6109,plain,
    ( r1_tarski(sK1,sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5674,c_1798,c_5887])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_851,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_6115,plain,
    ( k3_xboole_0(sK1,sK0) = sK1 ),
    inference(superposition,[status(thm)],[c_6109,c_851])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1394,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k6_subset_1(X0,X1) ),
    inference(superposition,[status(thm)],[c_0,c_20])).

cnf(c_7929,plain,
    ( k6_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_6115,c_1394])).

cnf(c_11,plain,
    ( k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_12,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_860,plain,
    ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k5_xboole_0(X0,k6_subset_1(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_12,c_20])).

cnf(c_2394,plain,
    ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k5_xboole_0(X1,k6_subset_1(X0,X1)) ),
    inference(superposition,[status(thm)],[c_11,c_860])).

cnf(c_10,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_858,plain,
    ( k6_subset_1(X0,k5_xboole_0(X0,k6_subset_1(X1,X0))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_10,c_20])).

cnf(c_2499,plain,
    ( k6_subset_1(X0,k3_tarski(k2_enumset1(X1,X1,X1,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2394,c_858])).

cnf(c_2500,plain,
    ( k6_subset_1(X0,k5_xboole_0(X1,k6_subset_1(X0,X1))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2499,c_860])).

cnf(c_79180,plain,
    ( k6_subset_1(sK0,k5_xboole_0(sK1,k5_xboole_0(sK0,sK1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7929,c_2500])).

cnf(c_11178,plain,
    ( k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_7929,c_5604])).

cnf(c_25,negated_conjecture,
    ( r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | k3_subset_1(sK0,k1_xboole_0) = sK1 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_840,plain,
    ( k3_subset_1(sK0,k1_xboole_0) = sK1
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_857,plain,
    ( sK1 = sK0
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_840,c_15])).

cnf(c_2133,plain,
    ( k3_xboole_0(k3_subset_1(sK0,sK1),sK1) = k3_subset_1(sK0,sK1)
    | sK1 = sK0 ),
    inference(superposition,[status(thm)],[c_857,c_851])).

cnf(c_2201,plain,
    ( k6_subset_1(sK1,k3_subset_1(sK0,sK1)) = k5_xboole_0(sK1,k3_subset_1(sK0,sK1))
    | sK1 = sK0 ),
    inference(superposition,[status(thm)],[c_2133,c_1394])).

cnf(c_2586,plain,
    ( sK1 = sK0
    | m1_subset_1(k5_xboole_0(sK1,k3_subset_1(sK0,sK1)),k1_zfmisc_1(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2201,c_846])).

cnf(c_11306,plain,
    ( sK1 = sK0
    | m1_subset_1(k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)),k1_zfmisc_1(sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11178,c_2586])).

cnf(c_24,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | k3_subset_1(sK0,k1_xboole_0) != sK1 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_841,plain,
    ( k3_subset_1(sK0,k1_xboole_0) != sK1
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_863,plain,
    ( sK1 != sK0
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_841,c_15])).

cnf(c_873,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | sK1 != sK0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_863])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_913,plain,
    ( ~ r1_tarski(X0,sK1)
    | ~ r1_tarski(sK1,X0)
    | sK1 = X0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_956,plain,
    ( ~ r1_tarski(sK1,sK1)
    | sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_913])).

cnf(c_4,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1029,plain,
    ( r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1030,plain,
    ( r1_tarski(sK1,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1029])).

cnf(c_436,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_905,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k3_subset_1(sK0,k1_xboole_0),sK1)
    | k3_subset_1(sK0,k1_xboole_0) != X0
    | sK1 != X1 ),
    inference(instantiation,[status(thm)],[c_436])).

cnf(c_936,plain,
    ( ~ r1_tarski(X0,sK1)
    | r1_tarski(k3_subset_1(sK0,k1_xboole_0),sK1)
    | k3_subset_1(sK0,k1_xboole_0) != X0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_905])).

cnf(c_1198,plain,
    ( r1_tarski(k3_subset_1(sK0,k1_xboole_0),sK1)
    | ~ r1_tarski(sK1,sK1)
    | k3_subset_1(sK0,k1_xboole_0) != sK1
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_936])).

cnf(c_1199,plain,
    ( k3_subset_1(sK0,k1_xboole_0) != sK1
    | sK1 != sK1
    | r1_tarski(k3_subset_1(sK0,k1_xboole_0),sK1) = iProver_top
    | r1_tarski(sK1,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1198])).

cnf(c_6,plain,
    ( r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_852,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_861,plain,
    ( k6_subset_1(X0,X1) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_852,c_20])).

cnf(c_5886,plain,
    ( k3_subset_1(sK0,sK1) != k1_xboole_0
    | r1_tarski(sK0,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_5604,c_861])).

cnf(c_61,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_62,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_60])).

cnf(c_74,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_892,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,k1_xboole_0),sK1)
    | ~ r1_tarski(sK1,k3_subset_1(sK0,k1_xboole_0))
    | k3_subset_1(sK0,k1_xboole_0) = sK1 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_893,plain,
    ( k3_subset_1(sK0,k1_xboole_0) = sK1
    | r1_tarski(k3_subset_1(sK0,k1_xboole_0),sK1) != iProver_top
    | r1_tarski(sK1,k3_subset_1(sK0,k1_xboole_0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_892])).

cnf(c_1357,plain,
    ( r1_tarski(k1_xboole_0,sK1) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1473,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,k3_subset_1(sK0,sK1))
    | X2 != X0
    | k3_subset_1(sK0,sK1) != X1 ),
    inference(instantiation,[status(thm)],[c_436])).

cnf(c_1474,plain,
    ( X0 != X1
    | k3_subset_1(sK0,sK1) != X2
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,k3_subset_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1473])).

cnf(c_1476,plain,
    ( k3_subset_1(sK0,sK1) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | r1_tarski(k1_xboole_0,k3_subset_1(sK0,sK1)) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1474])).

cnf(c_2091,plain,
    ( r1_tarski(k3_subset_1(sK0,k1_xboole_0),sK1)
    | ~ r1_tarski(sK0,sK1)
    | k3_subset_1(sK0,k1_xboole_0) != sK0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_936])).

cnf(c_2092,plain,
    ( k3_subset_1(sK0,k1_xboole_0) != sK0
    | sK1 != sK1
    | r1_tarski(k3_subset_1(sK0,k1_xboole_0),sK1) = iProver_top
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2091])).

cnf(c_967,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,sK1)
    | X2 != X0
    | sK1 != X1 ),
    inference(instantiation,[status(thm)],[c_436])).

cnf(c_1170,plain,
    ( ~ r1_tarski(X0,sK1)
    | r1_tarski(X1,sK1)
    | X1 != X0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_967])).

cnf(c_1370,plain,
    ( r1_tarski(X0,sK1)
    | ~ r1_tarski(k1_xboole_0,sK1)
    | X0 != k1_xboole_0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1170])).

cnf(c_3444,plain,
    ( r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | ~ r1_tarski(k1_xboole_0,sK1)
    | k3_subset_1(sK0,sK1) != k1_xboole_0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1370])).

cnf(c_3561,plain,
    ( k3_subset_1(sK0,k1_xboole_0) = sK0 ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_5679,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) != iProver_top
    | r1_tarski(X0,k3_subset_1(sK0,sK1)) != iProver_top
    | r1_tarski(sK1,k3_subset_1(sK0,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5483,c_843])).

cnf(c_5692,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) != iProver_top
    | r1_tarski(sK1,k3_subset_1(sK0,k1_xboole_0)) = iProver_top
    | r1_tarski(k1_xboole_0,k3_subset_1(sK0,sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5679])).

cnf(c_6106,plain,
    ( k3_subset_1(sK0,sK1) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5886,c_24,c_61,c_62,c_74,c_893,c_956,c_1029,c_1357,c_1476,c_1798,c_2092,c_3444,c_3561,c_5692,c_5887])).

cnf(c_1340,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X1,k3_subset_1(X1,X0)) = iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_15,c_843])).

cnf(c_5675,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) != iProver_top
    | r1_tarski(k3_subset_1(sK0,sK1),k1_xboole_0) != iProver_top
    | r1_tarski(sK0,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_5483,c_1340])).

cnf(c_6291,plain,
    ( r1_tarski(k3_subset_1(sK0,sK1),k1_xboole_0) != iProver_top
    | r1_tarski(sK0,sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5675,c_1798,c_5887])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | r1_tarski(X0,X2)
    | ~ r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X0)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_844,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X2) = iProver_top
    | r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_5676,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) != iProver_top
    | r1_tarski(k3_subset_1(sK0,X0),sK1) != iProver_top
    | r1_tarski(k3_subset_1(sK0,sK1),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5483,c_844])).

cnf(c_7257,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK0)) != iProver_top
    | r1_tarski(k3_subset_1(sK0,X0),sK1) != iProver_top
    | r1_tarski(k3_subset_1(sK0,sK1),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5676,c_5887])).

cnf(c_7260,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) != iProver_top
    | r1_tarski(k3_subset_1(sK0,sK1),k1_xboole_0) = iProver_top
    | r1_tarski(k3_subset_1(sK0,k1_xboole_0),sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_7257])).

cnf(c_7264,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) != iProver_top
    | r1_tarski(k3_subset_1(sK0,sK1),k1_xboole_0) = iProver_top
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_15,c_7257])).

cnf(c_8800,plain,
    ( r1_tarski(k3_subset_1(sK0,sK1),k1_xboole_0) = iProver_top
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7264,c_1798])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_853,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_862,plain,
    ( k6_subset_1(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_853,c_20])).

cnf(c_8805,plain,
    ( k6_subset_1(k3_subset_1(sK0,sK1),k1_xboole_0) = k1_xboole_0
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_8800,c_862])).

cnf(c_842,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_5603,plain,
    ( k6_subset_1(X0,k1_xboole_0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_842,c_864])).

cnf(c_5633,plain,
    ( k6_subset_1(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_5603,c_15])).

cnf(c_8810,plain,
    ( k3_subset_1(sK0,sK1) = k1_xboole_0
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8805,c_5633])).

cnf(c_21496,plain,
    ( m1_subset_1(k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)),k1_zfmisc_1(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11306,c_25,c_24,c_61,c_62,c_74,c_873,c_893,c_956,c_1029,c_1030,c_1199,c_1357,c_1476,c_1798,c_2092,c_3444,c_3561,c_5692,c_5886,c_5887,c_6291,c_7260,c_8810])).

cnf(c_21500,plain,
    ( k6_subset_1(sK1,k5_xboole_0(sK1,k5_xboole_0(sK0,sK1))) = k3_subset_1(sK1,k5_xboole_0(sK1,k5_xboole_0(sK0,sK1))) ),
    inference(superposition,[status(thm)],[c_21496,c_864])).

cnf(c_11181,plain,
    ( k6_subset_1(sK1,k5_xboole_0(sK1,k5_xboole_0(sK0,sK1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7929,c_858])).

cnf(c_21502,plain,
    ( k3_subset_1(sK1,k5_xboole_0(sK1,k5_xboole_0(sK0,sK1))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_21500,c_11181])).

cnf(c_21501,plain,
    ( k3_subset_1(sK1,k3_subset_1(sK1,k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)))) = k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_21496,c_845])).

cnf(c_21503,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k3_subset_1(sK1,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_21502,c_21501])).

cnf(c_21504,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = sK1 ),
    inference(demodulation,[status(thm)],[c_21503,c_15])).

cnf(c_79218,plain,
    ( k5_xboole_0(sK0,sK1) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_79180,c_7929,c_21504])).

cnf(c_11179,plain,
    ( k5_xboole_0(sK0,sK1) != k1_xboole_0
    | r1_tarski(sK0,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_7929,c_861])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_79218,c_11179,c_8810,c_6106])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:27:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 31.47/4.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 31.47/4.50  
% 31.47/4.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 31.47/4.50  
% 31.47/4.50  ------  iProver source info
% 31.47/4.50  
% 31.47/4.50  git: date: 2020-06-30 10:37:57 +0100
% 31.47/4.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 31.47/4.50  git: non_committed_changes: false
% 31.47/4.50  git: last_make_outside_of_git: false
% 31.47/4.50  
% 31.47/4.50  ------ 
% 31.47/4.50  
% 31.47/4.50  ------ Input Options
% 31.47/4.50  
% 31.47/4.50  --out_options                           all
% 31.47/4.50  --tptp_safe_out                         true
% 31.47/4.50  --problem_path                          ""
% 31.47/4.50  --include_path                          ""
% 31.47/4.50  --clausifier                            res/vclausify_rel
% 31.47/4.50  --clausifier_options                    ""
% 31.47/4.50  --stdin                                 false
% 31.47/4.50  --stats_out                             all
% 31.47/4.50  
% 31.47/4.50  ------ General Options
% 31.47/4.50  
% 31.47/4.50  --fof                                   false
% 31.47/4.50  --time_out_real                         305.
% 31.47/4.50  --time_out_virtual                      -1.
% 31.47/4.50  --symbol_type_check                     false
% 31.47/4.50  --clausify_out                          false
% 31.47/4.50  --sig_cnt_out                           false
% 31.47/4.50  --trig_cnt_out                          false
% 31.47/4.50  --trig_cnt_out_tolerance                1.
% 31.47/4.50  --trig_cnt_out_sk_spl                   false
% 31.47/4.50  --abstr_cl_out                          false
% 31.47/4.50  
% 31.47/4.50  ------ Global Options
% 31.47/4.50  
% 31.47/4.50  --schedule                              default
% 31.47/4.50  --add_important_lit                     false
% 31.47/4.50  --prop_solver_per_cl                    1000
% 31.47/4.50  --min_unsat_core                        false
% 31.47/4.50  --soft_assumptions                      false
% 31.47/4.50  --soft_lemma_size                       3
% 31.47/4.50  --prop_impl_unit_size                   0
% 31.47/4.50  --prop_impl_unit                        []
% 31.47/4.50  --share_sel_clauses                     true
% 31.47/4.50  --reset_solvers                         false
% 31.47/4.50  --bc_imp_inh                            [conj_cone]
% 31.47/4.50  --conj_cone_tolerance                   3.
% 31.47/4.50  --extra_neg_conj                        none
% 31.47/4.50  --large_theory_mode                     true
% 31.47/4.50  --prolific_symb_bound                   200
% 31.47/4.50  --lt_threshold                          2000
% 31.47/4.50  --clause_weak_htbl                      true
% 31.47/4.50  --gc_record_bc_elim                     false
% 31.47/4.50  
% 31.47/4.50  ------ Preprocessing Options
% 31.47/4.50  
% 31.47/4.50  --preprocessing_flag                    true
% 31.47/4.50  --time_out_prep_mult                    0.1
% 31.47/4.50  --splitting_mode                        input
% 31.47/4.50  --splitting_grd                         true
% 31.47/4.50  --splitting_cvd                         false
% 31.47/4.50  --splitting_cvd_svl                     false
% 31.47/4.50  --splitting_nvd                         32
% 31.47/4.50  --sub_typing                            true
% 31.47/4.50  --prep_gs_sim                           true
% 31.47/4.50  --prep_unflatten                        true
% 31.47/4.50  --prep_res_sim                          true
% 31.47/4.50  --prep_upred                            true
% 31.47/4.50  --prep_sem_filter                       exhaustive
% 31.47/4.50  --prep_sem_filter_out                   false
% 31.47/4.50  --pred_elim                             true
% 31.47/4.50  --res_sim_input                         true
% 31.47/4.50  --eq_ax_congr_red                       true
% 31.47/4.50  --pure_diseq_elim                       true
% 31.47/4.50  --brand_transform                       false
% 31.47/4.50  --non_eq_to_eq                          false
% 31.47/4.50  --prep_def_merge                        true
% 31.47/4.50  --prep_def_merge_prop_impl              false
% 31.47/4.50  --prep_def_merge_mbd                    true
% 31.47/4.50  --prep_def_merge_tr_red                 false
% 31.47/4.50  --prep_def_merge_tr_cl                  false
% 31.47/4.50  --smt_preprocessing                     true
% 31.47/4.50  --smt_ac_axioms                         fast
% 31.47/4.50  --preprocessed_out                      false
% 31.47/4.50  --preprocessed_stats                    false
% 31.47/4.50  
% 31.47/4.50  ------ Abstraction refinement Options
% 31.47/4.50  
% 31.47/4.50  --abstr_ref                             []
% 31.47/4.50  --abstr_ref_prep                        false
% 31.47/4.50  --abstr_ref_until_sat                   false
% 31.47/4.50  --abstr_ref_sig_restrict                funpre
% 31.47/4.50  --abstr_ref_af_restrict_to_split_sk     false
% 31.47/4.50  --abstr_ref_under                       []
% 31.47/4.50  
% 31.47/4.50  ------ SAT Options
% 31.47/4.50  
% 31.47/4.50  --sat_mode                              false
% 31.47/4.50  --sat_fm_restart_options                ""
% 31.47/4.50  --sat_gr_def                            false
% 31.47/4.50  --sat_epr_types                         true
% 31.47/4.50  --sat_non_cyclic_types                  false
% 31.47/4.50  --sat_finite_models                     false
% 31.47/4.50  --sat_fm_lemmas                         false
% 31.47/4.50  --sat_fm_prep                           false
% 31.47/4.50  --sat_fm_uc_incr                        true
% 31.47/4.50  --sat_out_model                         small
% 31.47/4.50  --sat_out_clauses                       false
% 31.47/4.50  
% 31.47/4.50  ------ QBF Options
% 31.47/4.50  
% 31.47/4.50  --qbf_mode                              false
% 31.47/4.50  --qbf_elim_univ                         false
% 31.47/4.50  --qbf_dom_inst                          none
% 31.47/4.50  --qbf_dom_pre_inst                      false
% 31.47/4.50  --qbf_sk_in                             false
% 31.47/4.50  --qbf_pred_elim                         true
% 31.47/4.50  --qbf_split                             512
% 31.47/4.50  
% 31.47/4.50  ------ BMC1 Options
% 31.47/4.50  
% 31.47/4.50  --bmc1_incremental                      false
% 31.47/4.50  --bmc1_axioms                           reachable_all
% 31.47/4.50  --bmc1_min_bound                        0
% 31.47/4.50  --bmc1_max_bound                        -1
% 31.47/4.50  --bmc1_max_bound_default                -1
% 31.47/4.50  --bmc1_symbol_reachability              true
% 31.47/4.50  --bmc1_property_lemmas                  false
% 31.47/4.50  --bmc1_k_induction                      false
% 31.47/4.50  --bmc1_non_equiv_states                 false
% 31.47/4.50  --bmc1_deadlock                         false
% 31.47/4.50  --bmc1_ucm                              false
% 31.47/4.50  --bmc1_add_unsat_core                   none
% 31.47/4.50  --bmc1_unsat_core_children              false
% 31.47/4.50  --bmc1_unsat_core_extrapolate_axioms    false
% 31.47/4.50  --bmc1_out_stat                         full
% 31.47/4.50  --bmc1_ground_init                      false
% 31.47/4.50  --bmc1_pre_inst_next_state              false
% 31.47/4.50  --bmc1_pre_inst_state                   false
% 31.47/4.50  --bmc1_pre_inst_reach_state             false
% 31.47/4.50  --bmc1_out_unsat_core                   false
% 31.47/4.50  --bmc1_aig_witness_out                  false
% 31.47/4.50  --bmc1_verbose                          false
% 31.47/4.50  --bmc1_dump_clauses_tptp                false
% 31.47/4.50  --bmc1_dump_unsat_core_tptp             false
% 31.47/4.50  --bmc1_dump_file                        -
% 31.47/4.50  --bmc1_ucm_expand_uc_limit              128
% 31.47/4.50  --bmc1_ucm_n_expand_iterations          6
% 31.47/4.50  --bmc1_ucm_extend_mode                  1
% 31.47/4.50  --bmc1_ucm_init_mode                    2
% 31.47/4.50  --bmc1_ucm_cone_mode                    none
% 31.47/4.50  --bmc1_ucm_reduced_relation_type        0
% 31.47/4.50  --bmc1_ucm_relax_model                  4
% 31.47/4.50  --bmc1_ucm_full_tr_after_sat            true
% 31.47/4.50  --bmc1_ucm_expand_neg_assumptions       false
% 31.47/4.50  --bmc1_ucm_layered_model                none
% 31.47/4.50  --bmc1_ucm_max_lemma_size               10
% 31.47/4.50  
% 31.47/4.50  ------ AIG Options
% 31.47/4.50  
% 31.47/4.50  --aig_mode                              false
% 31.47/4.50  
% 31.47/4.50  ------ Instantiation Options
% 31.47/4.50  
% 31.47/4.50  --instantiation_flag                    true
% 31.47/4.50  --inst_sos_flag                         true
% 31.47/4.50  --inst_sos_phase                        true
% 31.47/4.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 31.47/4.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 31.47/4.50  --inst_lit_sel_side                     num_symb
% 31.47/4.50  --inst_solver_per_active                1400
% 31.47/4.50  --inst_solver_calls_frac                1.
% 31.47/4.50  --inst_passive_queue_type               priority_queues
% 31.47/4.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 31.47/4.50  --inst_passive_queues_freq              [25;2]
% 31.47/4.50  --inst_dismatching                      true
% 31.47/4.50  --inst_eager_unprocessed_to_passive     true
% 31.47/4.50  --inst_prop_sim_given                   true
% 31.47/4.50  --inst_prop_sim_new                     false
% 31.47/4.50  --inst_subs_new                         false
% 31.47/4.50  --inst_eq_res_simp                      false
% 31.47/4.50  --inst_subs_given                       false
% 31.47/4.50  --inst_orphan_elimination               true
% 31.47/4.50  --inst_learning_loop_flag               true
% 31.47/4.50  --inst_learning_start                   3000
% 31.47/4.50  --inst_learning_factor                  2
% 31.47/4.50  --inst_start_prop_sim_after_learn       3
% 31.47/4.50  --inst_sel_renew                        solver
% 31.47/4.50  --inst_lit_activity_flag                true
% 31.47/4.50  --inst_restr_to_given                   false
% 31.47/4.50  --inst_activity_threshold               500
% 31.47/4.50  --inst_out_proof                        true
% 31.47/4.50  
% 31.47/4.50  ------ Resolution Options
% 31.47/4.50  
% 31.47/4.50  --resolution_flag                       true
% 31.47/4.50  --res_lit_sel                           adaptive
% 31.47/4.50  --res_lit_sel_side                      none
% 31.47/4.50  --res_ordering                          kbo
% 31.47/4.50  --res_to_prop_solver                    active
% 31.47/4.50  --res_prop_simpl_new                    false
% 31.47/4.50  --res_prop_simpl_given                  true
% 31.47/4.50  --res_passive_queue_type                priority_queues
% 31.47/4.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 31.47/4.50  --res_passive_queues_freq               [15;5]
% 31.47/4.50  --res_forward_subs                      full
% 31.47/4.50  --res_backward_subs                     full
% 31.47/4.50  --res_forward_subs_resolution           true
% 31.47/4.50  --res_backward_subs_resolution          true
% 31.47/4.50  --res_orphan_elimination                true
% 31.47/4.50  --res_time_limit                        2.
% 31.47/4.50  --res_out_proof                         true
% 31.47/4.50  
% 31.47/4.50  ------ Superposition Options
% 31.47/4.50  
% 31.47/4.50  --superposition_flag                    true
% 31.47/4.50  --sup_passive_queue_type                priority_queues
% 31.47/4.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 31.47/4.50  --sup_passive_queues_freq               [8;1;4]
% 31.47/4.50  --demod_completeness_check              fast
% 31.47/4.50  --demod_use_ground                      true
% 31.47/4.50  --sup_to_prop_solver                    passive
% 31.47/4.50  --sup_prop_simpl_new                    true
% 31.47/4.50  --sup_prop_simpl_given                  true
% 31.47/4.50  --sup_fun_splitting                     true
% 31.47/4.50  --sup_smt_interval                      50000
% 31.47/4.50  
% 31.47/4.50  ------ Superposition Simplification Setup
% 31.47/4.50  
% 31.47/4.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 31.47/4.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 31.47/4.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 31.47/4.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 31.47/4.50  --sup_full_triv                         [TrivRules;PropSubs]
% 31.47/4.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 31.47/4.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 31.47/4.50  --sup_immed_triv                        [TrivRules]
% 31.47/4.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 31.47/4.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.47/4.50  --sup_immed_bw_main                     []
% 31.47/4.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 31.47/4.50  --sup_input_triv                        [Unflattening;TrivRules]
% 31.47/4.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.47/4.50  --sup_input_bw                          []
% 31.47/4.50  
% 31.47/4.50  ------ Combination Options
% 31.47/4.50  
% 31.47/4.50  --comb_res_mult                         3
% 31.47/4.50  --comb_sup_mult                         2
% 31.47/4.50  --comb_inst_mult                        10
% 31.47/4.50  
% 31.47/4.50  ------ Debug Options
% 31.47/4.50  
% 31.47/4.50  --dbg_backtrace                         false
% 31.47/4.50  --dbg_dump_prop_clauses                 false
% 31.47/4.50  --dbg_dump_prop_clauses_file            -
% 31.47/4.50  --dbg_out_stat                          false
% 31.47/4.50  ------ Parsing...
% 31.47/4.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 31.47/4.50  
% 31.47/4.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 31.47/4.50  
% 31.47/4.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 31.47/4.50  
% 31.47/4.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.47/4.50  ------ Proving...
% 31.47/4.50  ------ Problem Properties 
% 31.47/4.50  
% 31.47/4.50  
% 31.47/4.50  clauses                                 26
% 31.47/4.50  conjectures                             3
% 31.47/4.50  EPR                                     3
% 31.47/4.50  Horn                                    25
% 31.47/4.50  unary                                   15
% 31.47/4.50  binary                                  8
% 31.47/4.50  lits                                    42
% 31.47/4.50  lits eq                                 17
% 31.47/4.50  fd_pure                                 0
% 31.47/4.50  fd_pseudo                               0
% 31.47/4.50  fd_cond                                 0
% 31.47/4.50  fd_pseudo_cond                          1
% 31.47/4.50  AC symbols                              0
% 31.47/4.50  
% 31.47/4.50  ------ Schedule dynamic 5 is on 
% 31.47/4.50  
% 31.47/4.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 31.47/4.50  
% 31.47/4.50  
% 31.47/4.50  ------ 
% 31.47/4.50  Current options:
% 31.47/4.50  ------ 
% 31.47/4.50  
% 31.47/4.50  ------ Input Options
% 31.47/4.50  
% 31.47/4.50  --out_options                           all
% 31.47/4.50  --tptp_safe_out                         true
% 31.47/4.50  --problem_path                          ""
% 31.47/4.50  --include_path                          ""
% 31.47/4.50  --clausifier                            res/vclausify_rel
% 31.47/4.50  --clausifier_options                    ""
% 31.47/4.50  --stdin                                 false
% 31.47/4.50  --stats_out                             all
% 31.47/4.50  
% 31.47/4.50  ------ General Options
% 31.47/4.50  
% 31.47/4.50  --fof                                   false
% 31.47/4.50  --time_out_real                         305.
% 31.47/4.50  --time_out_virtual                      -1.
% 31.47/4.50  --symbol_type_check                     false
% 31.47/4.50  --clausify_out                          false
% 31.47/4.50  --sig_cnt_out                           false
% 31.47/4.50  --trig_cnt_out                          false
% 31.47/4.50  --trig_cnt_out_tolerance                1.
% 31.47/4.50  --trig_cnt_out_sk_spl                   false
% 31.47/4.50  --abstr_cl_out                          false
% 31.47/4.50  
% 31.47/4.50  ------ Global Options
% 31.47/4.50  
% 31.47/4.50  --schedule                              default
% 31.47/4.50  --add_important_lit                     false
% 31.47/4.50  --prop_solver_per_cl                    1000
% 31.47/4.50  --min_unsat_core                        false
% 31.47/4.50  --soft_assumptions                      false
% 31.47/4.50  --soft_lemma_size                       3
% 31.47/4.50  --prop_impl_unit_size                   0
% 31.47/4.50  --prop_impl_unit                        []
% 31.47/4.50  --share_sel_clauses                     true
% 31.47/4.50  --reset_solvers                         false
% 31.47/4.50  --bc_imp_inh                            [conj_cone]
% 31.47/4.50  --conj_cone_tolerance                   3.
% 31.47/4.50  --extra_neg_conj                        none
% 31.47/4.50  --large_theory_mode                     true
% 31.47/4.50  --prolific_symb_bound                   200
% 31.47/4.50  --lt_threshold                          2000
% 31.47/4.50  --clause_weak_htbl                      true
% 31.47/4.50  --gc_record_bc_elim                     false
% 31.47/4.50  
% 31.47/4.50  ------ Preprocessing Options
% 31.47/4.50  
% 31.47/4.50  --preprocessing_flag                    true
% 31.47/4.50  --time_out_prep_mult                    0.1
% 31.47/4.50  --splitting_mode                        input
% 31.47/4.50  --splitting_grd                         true
% 31.47/4.50  --splitting_cvd                         false
% 31.47/4.50  --splitting_cvd_svl                     false
% 31.47/4.50  --splitting_nvd                         32
% 31.47/4.50  --sub_typing                            true
% 31.47/4.50  --prep_gs_sim                           true
% 31.47/4.50  --prep_unflatten                        true
% 31.47/4.50  --prep_res_sim                          true
% 31.47/4.50  --prep_upred                            true
% 31.47/4.50  --prep_sem_filter                       exhaustive
% 31.47/4.50  --prep_sem_filter_out                   false
% 31.47/4.50  --pred_elim                             true
% 31.47/4.50  --res_sim_input                         true
% 31.47/4.50  --eq_ax_congr_red                       true
% 31.47/4.50  --pure_diseq_elim                       true
% 31.47/4.50  --brand_transform                       false
% 31.47/4.50  --non_eq_to_eq                          false
% 31.47/4.50  --prep_def_merge                        true
% 31.47/4.50  --prep_def_merge_prop_impl              false
% 31.47/4.50  --prep_def_merge_mbd                    true
% 31.47/4.50  --prep_def_merge_tr_red                 false
% 31.47/4.50  --prep_def_merge_tr_cl                  false
% 31.47/4.50  --smt_preprocessing                     true
% 31.47/4.50  --smt_ac_axioms                         fast
% 31.47/4.50  --preprocessed_out                      false
% 31.47/4.50  --preprocessed_stats                    false
% 31.47/4.50  
% 31.47/4.50  ------ Abstraction refinement Options
% 31.47/4.50  
% 31.47/4.50  --abstr_ref                             []
% 31.47/4.50  --abstr_ref_prep                        false
% 31.47/4.50  --abstr_ref_until_sat                   false
% 31.47/4.50  --abstr_ref_sig_restrict                funpre
% 31.47/4.50  --abstr_ref_af_restrict_to_split_sk     false
% 31.47/4.50  --abstr_ref_under                       []
% 31.47/4.50  
% 31.47/4.50  ------ SAT Options
% 31.47/4.50  
% 31.47/4.50  --sat_mode                              false
% 31.47/4.50  --sat_fm_restart_options                ""
% 31.47/4.50  --sat_gr_def                            false
% 31.47/4.50  --sat_epr_types                         true
% 31.47/4.50  --sat_non_cyclic_types                  false
% 31.47/4.50  --sat_finite_models                     false
% 31.47/4.50  --sat_fm_lemmas                         false
% 31.47/4.50  --sat_fm_prep                           false
% 31.47/4.50  --sat_fm_uc_incr                        true
% 31.47/4.50  --sat_out_model                         small
% 31.47/4.50  --sat_out_clauses                       false
% 31.47/4.50  
% 31.47/4.50  ------ QBF Options
% 31.47/4.50  
% 31.47/4.50  --qbf_mode                              false
% 31.47/4.50  --qbf_elim_univ                         false
% 31.47/4.50  --qbf_dom_inst                          none
% 31.47/4.50  --qbf_dom_pre_inst                      false
% 31.47/4.50  --qbf_sk_in                             false
% 31.47/4.50  --qbf_pred_elim                         true
% 31.47/4.50  --qbf_split                             512
% 31.47/4.50  
% 31.47/4.50  ------ BMC1 Options
% 31.47/4.50  
% 31.47/4.50  --bmc1_incremental                      false
% 31.47/4.50  --bmc1_axioms                           reachable_all
% 31.47/4.50  --bmc1_min_bound                        0
% 31.47/4.50  --bmc1_max_bound                        -1
% 31.47/4.50  --bmc1_max_bound_default                -1
% 31.47/4.50  --bmc1_symbol_reachability              true
% 31.47/4.50  --bmc1_property_lemmas                  false
% 31.47/4.50  --bmc1_k_induction                      false
% 31.47/4.50  --bmc1_non_equiv_states                 false
% 31.47/4.50  --bmc1_deadlock                         false
% 31.47/4.50  --bmc1_ucm                              false
% 31.47/4.50  --bmc1_add_unsat_core                   none
% 31.47/4.50  --bmc1_unsat_core_children              false
% 31.47/4.50  --bmc1_unsat_core_extrapolate_axioms    false
% 31.47/4.50  --bmc1_out_stat                         full
% 31.47/4.50  --bmc1_ground_init                      false
% 31.47/4.50  --bmc1_pre_inst_next_state              false
% 31.47/4.50  --bmc1_pre_inst_state                   false
% 31.47/4.50  --bmc1_pre_inst_reach_state             false
% 31.47/4.50  --bmc1_out_unsat_core                   false
% 31.47/4.50  --bmc1_aig_witness_out                  false
% 31.47/4.50  --bmc1_verbose                          false
% 31.47/4.50  --bmc1_dump_clauses_tptp                false
% 31.47/4.50  --bmc1_dump_unsat_core_tptp             false
% 31.47/4.50  --bmc1_dump_file                        -
% 31.47/4.50  --bmc1_ucm_expand_uc_limit              128
% 31.47/4.50  --bmc1_ucm_n_expand_iterations          6
% 31.47/4.50  --bmc1_ucm_extend_mode                  1
% 31.47/4.50  --bmc1_ucm_init_mode                    2
% 31.47/4.50  --bmc1_ucm_cone_mode                    none
% 31.47/4.50  --bmc1_ucm_reduced_relation_type        0
% 31.47/4.50  --bmc1_ucm_relax_model                  4
% 31.47/4.50  --bmc1_ucm_full_tr_after_sat            true
% 31.47/4.50  --bmc1_ucm_expand_neg_assumptions       false
% 31.47/4.50  --bmc1_ucm_layered_model                none
% 31.47/4.50  --bmc1_ucm_max_lemma_size               10
% 31.47/4.50  
% 31.47/4.50  ------ AIG Options
% 31.47/4.50  
% 31.47/4.50  --aig_mode                              false
% 31.47/4.50  
% 31.47/4.50  ------ Instantiation Options
% 31.47/4.50  
% 31.47/4.50  --instantiation_flag                    true
% 31.47/4.50  --inst_sos_flag                         true
% 31.47/4.50  --inst_sos_phase                        true
% 31.47/4.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 31.47/4.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 31.47/4.50  --inst_lit_sel_side                     none
% 31.47/4.50  --inst_solver_per_active                1400
% 31.47/4.50  --inst_solver_calls_frac                1.
% 31.47/4.50  --inst_passive_queue_type               priority_queues
% 31.47/4.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 31.47/4.50  --inst_passive_queues_freq              [25;2]
% 31.47/4.50  --inst_dismatching                      true
% 31.47/4.50  --inst_eager_unprocessed_to_passive     true
% 31.47/4.50  --inst_prop_sim_given                   true
% 31.47/4.50  --inst_prop_sim_new                     false
% 31.47/4.50  --inst_subs_new                         false
% 31.47/4.50  --inst_eq_res_simp                      false
% 31.47/4.50  --inst_subs_given                       false
% 31.47/4.50  --inst_orphan_elimination               true
% 31.47/4.50  --inst_learning_loop_flag               true
% 31.47/4.50  --inst_learning_start                   3000
% 31.47/4.50  --inst_learning_factor                  2
% 31.47/4.50  --inst_start_prop_sim_after_learn       3
% 31.47/4.50  --inst_sel_renew                        solver
% 31.47/4.50  --inst_lit_activity_flag                true
% 31.47/4.50  --inst_restr_to_given                   false
% 31.47/4.50  --inst_activity_threshold               500
% 31.47/4.50  --inst_out_proof                        true
% 31.47/4.50  
% 31.47/4.50  ------ Resolution Options
% 31.47/4.50  
% 31.47/4.50  --resolution_flag                       false
% 31.47/4.50  --res_lit_sel                           adaptive
% 31.47/4.50  --res_lit_sel_side                      none
% 31.47/4.50  --res_ordering                          kbo
% 31.47/4.50  --res_to_prop_solver                    active
% 31.47/4.50  --res_prop_simpl_new                    false
% 31.47/4.50  --res_prop_simpl_given                  true
% 31.47/4.50  --res_passive_queue_type                priority_queues
% 31.47/4.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 31.47/4.50  --res_passive_queues_freq               [15;5]
% 31.47/4.50  --res_forward_subs                      full
% 31.47/4.50  --res_backward_subs                     full
% 31.47/4.50  --res_forward_subs_resolution           true
% 31.47/4.50  --res_backward_subs_resolution          true
% 31.47/4.50  --res_orphan_elimination                true
% 31.47/4.50  --res_time_limit                        2.
% 31.47/4.50  --res_out_proof                         true
% 31.47/4.50  
% 31.47/4.50  ------ Superposition Options
% 31.47/4.50  
% 31.47/4.50  --superposition_flag                    true
% 31.47/4.50  --sup_passive_queue_type                priority_queues
% 31.47/4.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 31.47/4.50  --sup_passive_queues_freq               [8;1;4]
% 31.47/4.50  --demod_completeness_check              fast
% 31.47/4.50  --demod_use_ground                      true
% 31.47/4.50  --sup_to_prop_solver                    passive
% 31.47/4.50  --sup_prop_simpl_new                    true
% 31.47/4.50  --sup_prop_simpl_given                  true
% 31.47/4.50  --sup_fun_splitting                     true
% 31.47/4.50  --sup_smt_interval                      50000
% 31.47/4.50  
% 31.47/4.50  ------ Superposition Simplification Setup
% 31.47/4.50  
% 31.47/4.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 31.47/4.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 31.47/4.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 31.47/4.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 31.47/4.50  --sup_full_triv                         [TrivRules;PropSubs]
% 31.47/4.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 31.47/4.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 31.47/4.50  --sup_immed_triv                        [TrivRules]
% 31.47/4.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 31.47/4.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.47/4.50  --sup_immed_bw_main                     []
% 31.47/4.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 31.47/4.50  --sup_input_triv                        [Unflattening;TrivRules]
% 31.47/4.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.47/4.50  --sup_input_bw                          []
% 31.47/4.50  
% 31.47/4.50  ------ Combination Options
% 31.47/4.50  
% 31.47/4.50  --comb_res_mult                         3
% 31.47/4.50  --comb_sup_mult                         2
% 31.47/4.50  --comb_inst_mult                        10
% 31.47/4.50  
% 31.47/4.50  ------ Debug Options
% 31.47/4.50  
% 31.47/4.50  --dbg_backtrace                         false
% 31.47/4.50  --dbg_dump_prop_clauses                 false
% 31.47/4.50  --dbg_dump_prop_clauses_file            -
% 31.47/4.50  --dbg_out_stat                          false
% 31.47/4.50  
% 31.47/4.50  
% 31.47/4.50  
% 31.47/4.50  
% 31.47/4.50  ------ Proving...
% 31.47/4.50  
% 31.47/4.50  
% 31.47/4.50  % SZS status Theorem for theBenchmark.p
% 31.47/4.50  
% 31.47/4.50  % SZS output start CNFRefutation for theBenchmark.p
% 31.47/4.50  
% 31.47/4.50  fof(f27,conjecture,(
% 31.47/4.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 31.47/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.47/4.50  
% 31.47/4.50  fof(f28,negated_conjecture,(
% 31.47/4.50    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 31.47/4.50    inference(negated_conjecture,[],[f27])).
% 31.47/4.50  
% 31.47/4.50  fof(f35,plain,(
% 31.47/4.50    ? [X0,X1] : ((r1_tarski(k3_subset_1(X0,X1),X1) <~> k2_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 31.47/4.50    inference(ennf_transformation,[],[f28])).
% 31.47/4.50  
% 31.47/4.50  fof(f40,plain,(
% 31.47/4.50    ? [X0,X1] : (((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 31.47/4.50    inference(nnf_transformation,[],[f35])).
% 31.47/4.50  
% 31.47/4.50  fof(f41,plain,(
% 31.47/4.50    ? [X0,X1] : ((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 31.47/4.50    inference(flattening,[],[f40])).
% 31.47/4.50  
% 31.47/4.50  fof(f42,plain,(
% 31.47/4.50    ? [X0,X1] : ((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => ((k2_subset_1(sK0) != sK1 | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)) & (k2_subset_1(sK0) = sK1 | r1_tarski(k3_subset_1(sK0,sK1),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 31.47/4.50    introduced(choice_axiom,[])).
% 31.47/4.50  
% 31.47/4.50  fof(f43,plain,(
% 31.47/4.50    (k2_subset_1(sK0) != sK1 | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)) & (k2_subset_1(sK0) = sK1 | r1_tarski(k3_subset_1(sK0,sK1),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 31.47/4.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f41,f42])).
% 31.47/4.50  
% 31.47/4.50  fof(f74,plain,(
% 31.47/4.50    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 31.47/4.50    inference(cnf_transformation,[],[f43])).
% 31.47/4.50  
% 31.47/4.50  fof(f22,axiom,(
% 31.47/4.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 31.47/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.47/4.50  
% 31.47/4.50  fof(f33,plain,(
% 31.47/4.50    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 31.47/4.50    inference(ennf_transformation,[],[f22])).
% 31.47/4.50  
% 31.47/4.50  fof(f68,plain,(
% 31.47/4.50    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 31.47/4.50    inference(cnf_transformation,[],[f33])).
% 31.47/4.50  
% 31.47/4.50  fof(f18,axiom,(
% 31.47/4.50    ! [X0] : k2_subset_1(X0) = X0),
% 31.47/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.47/4.50  
% 31.47/4.50  fof(f64,plain,(
% 31.47/4.50    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 31.47/4.50    inference(cnf_transformation,[],[f18])).
% 31.47/4.50  
% 31.47/4.50  fof(f24,axiom,(
% 31.47/4.50    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 31.47/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.47/4.50  
% 31.47/4.50  fof(f70,plain,(
% 31.47/4.50    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 31.47/4.50    inference(cnf_transformation,[],[f24])).
% 31.47/4.50  
% 31.47/4.50  fof(f17,axiom,(
% 31.47/4.50    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 31.47/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.47/4.50  
% 31.47/4.50  fof(f63,plain,(
% 31.47/4.50    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 31.47/4.50    inference(cnf_transformation,[],[f17])).
% 31.47/4.50  
% 31.47/4.50  fof(f79,plain,(
% 31.47/4.50    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 31.47/4.50    inference(definition_unfolding,[],[f70,f63])).
% 31.47/4.50  
% 31.47/4.50  fof(f86,plain,(
% 31.47/4.50    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 31.47/4.50    inference(definition_unfolding,[],[f64,f79])).
% 31.47/4.50  
% 31.47/4.50  fof(f25,axiom,(
% 31.47/4.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 31.47/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.47/4.50  
% 31.47/4.50  fof(f34,plain,(
% 31.47/4.50    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 31.47/4.50    inference(ennf_transformation,[],[f25])).
% 31.47/4.50  
% 31.47/4.50  fof(f39,plain,(
% 31.47/4.50    ! [X0,X1] : (! [X2] : (((r1_tarski(X1,X2) | ~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 31.47/4.50    inference(nnf_transformation,[],[f34])).
% 31.47/4.50  
% 31.47/4.50  fof(f71,plain,(
% 31.47/4.50    ( ! [X2,X0,X1] : (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 31.47/4.50    inference(cnf_transformation,[],[f39])).
% 31.47/4.50  
% 31.47/4.50  fof(f8,axiom,(
% 31.47/4.50    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 31.47/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.47/4.50  
% 31.47/4.50  fof(f54,plain,(
% 31.47/4.50    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 31.47/4.50    inference(cnf_transformation,[],[f8])).
% 31.47/4.50  
% 31.47/4.50  fof(f26,axiom,(
% 31.47/4.50    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 31.47/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.47/4.50  
% 31.47/4.50  fof(f73,plain,(
% 31.47/4.50    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 31.47/4.50    inference(cnf_transformation,[],[f26])).
% 31.47/4.50  
% 31.47/4.50  fof(f19,axiom,(
% 31.47/4.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 31.47/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.47/4.50  
% 31.47/4.50  fof(f32,plain,(
% 31.47/4.50    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 31.47/4.50    inference(ennf_transformation,[],[f19])).
% 31.47/4.50  
% 31.47/4.50  fof(f65,plain,(
% 31.47/4.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 31.47/4.50    inference(cnf_transformation,[],[f32])).
% 31.47/4.50  
% 31.47/4.50  fof(f5,axiom,(
% 31.47/4.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 31.47/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.47/4.50  
% 31.47/4.50  fof(f51,plain,(
% 31.47/4.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 31.47/4.50    inference(cnf_transformation,[],[f5])).
% 31.47/4.50  
% 31.47/4.50  fof(f87,plain,(
% 31.47/4.50    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 31.47/4.50    inference(definition_unfolding,[],[f65,f51])).
% 31.47/4.50  
% 31.47/4.50  fof(f23,axiom,(
% 31.47/4.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 31.47/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.47/4.50  
% 31.47/4.50  fof(f69,plain,(
% 31.47/4.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 31.47/4.50    inference(cnf_transformation,[],[f23])).
% 31.47/4.50  
% 31.47/4.50  fof(f89,plain,(
% 31.47/4.50    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k6_subset_1(X0,X1)) )),
% 31.47/4.50    inference(definition_unfolding,[],[f69,f51])).
% 31.47/4.50  
% 31.47/4.50  fof(f21,axiom,(
% 31.47/4.50    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))),
% 31.47/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.47/4.50  
% 31.47/4.50  fof(f67,plain,(
% 31.47/4.50    ( ! [X0,X1] : (m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 31.47/4.50    inference(cnf_transformation,[],[f21])).
% 31.47/4.50  
% 31.47/4.50  fof(f7,axiom,(
% 31.47/4.50    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 31.47/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.47/4.50  
% 31.47/4.50  fof(f30,plain,(
% 31.47/4.50    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 31.47/4.50    inference(ennf_transformation,[],[f7])).
% 31.47/4.50  
% 31.47/4.50  fof(f53,plain,(
% 31.47/4.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 31.47/4.50    inference(cnf_transformation,[],[f30])).
% 31.47/4.50  
% 31.47/4.50  fof(f1,axiom,(
% 31.47/4.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 31.47/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.47/4.50  
% 31.47/4.50  fof(f44,plain,(
% 31.47/4.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 31.47/4.50    inference(cnf_transformation,[],[f1])).
% 31.47/4.50  
% 31.47/4.50  fof(f11,axiom,(
% 31.47/4.50    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 31.47/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.47/4.50  
% 31.47/4.50  fof(f57,plain,(
% 31.47/4.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 31.47/4.50    inference(cnf_transformation,[],[f11])).
% 31.47/4.50  
% 31.47/4.50  fof(f12,axiom,(
% 31.47/4.50    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 31.47/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.47/4.50  
% 31.47/4.50  fof(f58,plain,(
% 31.47/4.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 31.47/4.50    inference(cnf_transformation,[],[f12])).
% 31.47/4.50  
% 31.47/4.50  fof(f13,axiom,(
% 31.47/4.50    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 31.47/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.47/4.50  
% 31.47/4.50  fof(f59,plain,(
% 31.47/4.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 31.47/4.50    inference(cnf_transformation,[],[f13])).
% 31.47/4.50  
% 31.47/4.50  fof(f78,plain,(
% 31.47/4.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 31.47/4.50    inference(definition_unfolding,[],[f58,f59])).
% 31.47/4.50  
% 31.47/4.50  fof(f84,plain,(
% 31.47/4.50    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 31.47/4.50    inference(definition_unfolding,[],[f57,f78,f78])).
% 31.47/4.50  
% 31.47/4.50  fof(f14,axiom,(
% 31.47/4.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 31.47/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.47/4.50  
% 31.47/4.50  fof(f60,plain,(
% 31.47/4.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 31.47/4.50    inference(cnf_transformation,[],[f14])).
% 31.47/4.50  
% 31.47/4.50  fof(f10,axiom,(
% 31.47/4.50    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 31.47/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.47/4.50  
% 31.47/4.50  fof(f56,plain,(
% 31.47/4.50    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 31.47/4.50    inference(cnf_transformation,[],[f10])).
% 31.47/4.50  
% 31.47/4.50  fof(f77,plain,(
% 31.47/4.50    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 31.47/4.50    inference(definition_unfolding,[],[f56,f51])).
% 31.47/4.50  
% 31.47/4.50  fof(f85,plain,(
% 31.47/4.50    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 31.47/4.50    inference(definition_unfolding,[],[f60,f77,f78])).
% 31.47/4.50  
% 31.47/4.50  fof(f9,axiom,(
% 31.47/4.50    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 31.47/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.47/4.50  
% 31.47/4.50  fof(f55,plain,(
% 31.47/4.50    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 31.47/4.50    inference(cnf_transformation,[],[f9])).
% 31.47/4.50  
% 31.47/4.50  fof(f83,plain,(
% 31.47/4.50    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))))) )),
% 31.47/4.50    inference(definition_unfolding,[],[f55,f51,f77])).
% 31.47/4.50  
% 31.47/4.50  fof(f75,plain,(
% 31.47/4.50    k2_subset_1(sK0) = sK1 | r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 31.47/4.50    inference(cnf_transformation,[],[f43])).
% 31.47/4.50  
% 31.47/4.50  fof(f91,plain,(
% 31.47/4.50    k3_subset_1(sK0,k1_xboole_0) = sK1 | r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 31.47/4.50    inference(definition_unfolding,[],[f75,f79])).
% 31.47/4.50  
% 31.47/4.50  fof(f76,plain,(
% 31.47/4.50    k2_subset_1(sK0) != sK1 | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 31.47/4.50    inference(cnf_transformation,[],[f43])).
% 31.47/4.50  
% 31.47/4.50  fof(f90,plain,(
% 31.47/4.50    k3_subset_1(sK0,k1_xboole_0) != sK1 | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 31.47/4.50    inference(definition_unfolding,[],[f76,f79])).
% 31.47/4.50  
% 31.47/4.50  fof(f3,axiom,(
% 31.47/4.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 31.47/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.47/4.50  
% 31.47/4.50  fof(f36,plain,(
% 31.47/4.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 31.47/4.50    inference(nnf_transformation,[],[f3])).
% 31.47/4.50  
% 31.47/4.50  fof(f37,plain,(
% 31.47/4.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 31.47/4.50    inference(flattening,[],[f36])).
% 31.47/4.50  
% 31.47/4.50  fof(f48,plain,(
% 31.47/4.50    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 31.47/4.50    inference(cnf_transformation,[],[f37])).
% 31.47/4.50  
% 31.47/4.50  fof(f46,plain,(
% 31.47/4.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 31.47/4.50    inference(cnf_transformation,[],[f37])).
% 31.47/4.50  
% 31.47/4.50  fof(f93,plain,(
% 31.47/4.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 31.47/4.50    inference(equality_resolution,[],[f46])).
% 31.47/4.50  
% 31.47/4.50  fof(f4,axiom,(
% 31.47/4.50    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 31.47/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.47/4.50  
% 31.47/4.50  fof(f38,plain,(
% 31.47/4.50    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 31.47/4.50    inference(nnf_transformation,[],[f4])).
% 31.47/4.50  
% 31.47/4.50  fof(f49,plain,(
% 31.47/4.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 31.47/4.50    inference(cnf_transformation,[],[f38])).
% 31.47/4.50  
% 31.47/4.50  fof(f81,plain,(
% 31.47/4.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 31.47/4.50    inference(definition_unfolding,[],[f49,f51])).
% 31.47/4.50  
% 31.47/4.50  fof(f72,plain,(
% 31.47/4.50    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 31.47/4.50    inference(cnf_transformation,[],[f39])).
% 31.47/4.50  
% 31.47/4.50  fof(f50,plain,(
% 31.47/4.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 31.47/4.50    inference(cnf_transformation,[],[f38])).
% 31.47/4.50  
% 31.47/4.50  fof(f80,plain,(
% 31.47/4.50    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) | ~r1_tarski(X0,X1)) )),
% 31.47/4.50    inference(definition_unfolding,[],[f50,f51])).
% 31.47/4.50  
% 31.47/4.50  cnf(c_26,negated_conjecture,
% 31.47/4.50      ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
% 31.47/4.50      inference(cnf_transformation,[],[f74]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_839,plain,
% 31.47/4.50      ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) = iProver_top ),
% 31.47/4.50      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_19,plain,
% 31.47/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 31.47/4.50      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 31.47/4.50      inference(cnf_transformation,[],[f68]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_845,plain,
% 31.47/4.50      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 31.47/4.50      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 31.47/4.50      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_5483,plain,
% 31.47/4.50      ( k3_subset_1(sK0,k3_subset_1(sK0,sK1)) = sK1 ),
% 31.47/4.50      inference(superposition,[status(thm)],[c_839,c_845]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_15,plain,
% 31.47/4.50      ( k3_subset_1(X0,k1_xboole_0) = X0 ),
% 31.47/4.50      inference(cnf_transformation,[],[f86]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_22,plain,
% 31.47/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 31.47/4.50      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 31.47/4.50      | ~ r1_tarski(X0,X2)
% 31.47/4.50      | r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X0)) ),
% 31.47/4.50      inference(cnf_transformation,[],[f71]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_843,plain,
% 31.47/4.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 31.47/4.50      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 31.47/4.50      | r1_tarski(X0,X2) != iProver_top
% 31.47/4.50      | r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X0)) = iProver_top ),
% 31.47/4.50      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_1341,plain,
% 31.47/4.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 31.47/4.50      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) != iProver_top
% 31.47/4.50      | r1_tarski(k3_subset_1(X1,X0),X1) = iProver_top
% 31.47/4.50      | r1_tarski(k1_xboole_0,X0) != iProver_top ),
% 31.47/4.50      inference(superposition,[status(thm)],[c_15,c_843]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_9,plain,
% 31.47/4.50      ( r1_tarski(k1_xboole_0,X0) ),
% 31.47/4.50      inference(cnf_transformation,[],[f54]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_60,plain,
% 31.47/4.50      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 31.47/4.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_5281,plain,
% 31.47/4.50      ( r1_tarski(k3_subset_1(X1,X0),X1) = iProver_top
% 31.47/4.50      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) != iProver_top
% 31.47/4.50      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 31.47/4.50      inference(global_propositional_subsumption,
% 31.47/4.50                [status(thm)],
% 31.47/4.50                [c_1341,c_60]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_5282,plain,
% 31.47/4.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 31.47/4.50      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) != iProver_top
% 31.47/4.50      | r1_tarski(k3_subset_1(X1,X0),X1) = iProver_top ),
% 31.47/4.50      inference(renaming,[status(thm)],[c_5281]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_5674,plain,
% 31.47/4.50      ( m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) != iProver_top
% 31.47/4.50      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) != iProver_top
% 31.47/4.50      | r1_tarski(sK1,sK0) = iProver_top ),
% 31.47/4.50      inference(superposition,[status(thm)],[c_5483,c_5282]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_23,plain,
% 31.47/4.50      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 31.47/4.50      inference(cnf_transformation,[],[f73]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_1797,plain,
% 31.47/4.50      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) ),
% 31.47/4.50      inference(instantiation,[status(thm)],[c_23]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_1798,plain,
% 31.47/4.50      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) = iProver_top ),
% 31.47/4.50      inference(predicate_to_equality,[status(thm)],[c_1797]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_16,plain,
% 31.47/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 31.47/4.50      | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
% 31.47/4.50      inference(cnf_transformation,[],[f87]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_848,plain,
% 31.47/4.50      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
% 31.47/4.50      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 31.47/4.50      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_20,plain,
% 31.47/4.50      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k6_subset_1(X0,X1) ),
% 31.47/4.50      inference(cnf_transformation,[],[f89]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_864,plain,
% 31.47/4.50      ( k6_subset_1(X0,X1) = k3_subset_1(X0,X1)
% 31.47/4.50      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 31.47/4.50      inference(demodulation,[status(thm)],[c_848,c_20]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_5604,plain,
% 31.47/4.50      ( k6_subset_1(sK0,sK1) = k3_subset_1(sK0,sK1) ),
% 31.47/4.50      inference(superposition,[status(thm)],[c_839,c_864]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_18,plain,
% 31.47/4.50      ( m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
% 31.47/4.50      inference(cnf_transformation,[],[f67]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_846,plain,
% 31.47/4.50      ( m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) = iProver_top ),
% 31.47/4.50      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_5887,plain,
% 31.47/4.50      ( m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) = iProver_top ),
% 31.47/4.50      inference(superposition,[status(thm)],[c_5604,c_846]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_6109,plain,
% 31.47/4.50      ( r1_tarski(sK1,sK0) = iProver_top ),
% 31.47/4.50      inference(global_propositional_subsumption,
% 31.47/4.50                [status(thm)],
% 31.47/4.50                [c_5674,c_1798,c_5887]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_8,plain,
% 31.47/4.50      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 31.47/4.50      inference(cnf_transformation,[],[f53]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_851,plain,
% 31.47/4.50      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 31.47/4.50      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_6115,plain,
% 31.47/4.50      ( k3_xboole_0(sK1,sK0) = sK1 ),
% 31.47/4.50      inference(superposition,[status(thm)],[c_6109,c_851]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_0,plain,
% 31.47/4.50      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 31.47/4.50      inference(cnf_transformation,[],[f44]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_1394,plain,
% 31.47/4.50      ( k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k6_subset_1(X0,X1) ),
% 31.47/4.50      inference(superposition,[status(thm)],[c_0,c_20]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_7929,plain,
% 31.47/4.50      ( k6_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1) ),
% 31.47/4.50      inference(superposition,[status(thm)],[c_6115,c_1394]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_11,plain,
% 31.47/4.50      ( k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
% 31.47/4.50      inference(cnf_transformation,[],[f84]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_12,plain,
% 31.47/4.50      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
% 31.47/4.50      inference(cnf_transformation,[],[f85]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_860,plain,
% 31.47/4.50      ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k5_xboole_0(X0,k6_subset_1(X1,X0)) ),
% 31.47/4.50      inference(demodulation,[status(thm)],[c_12,c_20]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_2394,plain,
% 31.47/4.50      ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k5_xboole_0(X1,k6_subset_1(X0,X1)) ),
% 31.47/4.50      inference(superposition,[status(thm)],[c_11,c_860]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_10,plain,
% 31.47/4.50      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) = k1_xboole_0 ),
% 31.47/4.50      inference(cnf_transformation,[],[f83]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_858,plain,
% 31.47/4.50      ( k6_subset_1(X0,k5_xboole_0(X0,k6_subset_1(X1,X0))) = k1_xboole_0 ),
% 31.47/4.50      inference(demodulation,[status(thm)],[c_10,c_20]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_2499,plain,
% 31.47/4.50      ( k6_subset_1(X0,k3_tarski(k2_enumset1(X1,X1,X1,X0))) = k1_xboole_0 ),
% 31.47/4.50      inference(superposition,[status(thm)],[c_2394,c_858]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_2500,plain,
% 31.47/4.50      ( k6_subset_1(X0,k5_xboole_0(X1,k6_subset_1(X0,X1))) = k1_xboole_0 ),
% 31.47/4.50      inference(demodulation,[status(thm)],[c_2499,c_860]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_79180,plain,
% 31.47/4.50      ( k6_subset_1(sK0,k5_xboole_0(sK1,k5_xboole_0(sK0,sK1))) = k1_xboole_0 ),
% 31.47/4.50      inference(superposition,[status(thm)],[c_7929,c_2500]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_11178,plain,
% 31.47/4.51      ( k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1) ),
% 31.47/4.51      inference(demodulation,[status(thm)],[c_7929,c_5604]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_25,negated_conjecture,
% 31.47/4.51      ( r1_tarski(k3_subset_1(sK0,sK1),sK1)
% 31.47/4.51      | k3_subset_1(sK0,k1_xboole_0) = sK1 ),
% 31.47/4.51      inference(cnf_transformation,[],[f91]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_840,plain,
% 31.47/4.51      ( k3_subset_1(sK0,k1_xboole_0) = sK1
% 31.47/4.51      | r1_tarski(k3_subset_1(sK0,sK1),sK1) = iProver_top ),
% 31.47/4.51      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_857,plain,
% 31.47/4.51      ( sK1 = sK0 | r1_tarski(k3_subset_1(sK0,sK1),sK1) = iProver_top ),
% 31.47/4.51      inference(demodulation,[status(thm)],[c_840,c_15]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_2133,plain,
% 31.47/4.51      ( k3_xboole_0(k3_subset_1(sK0,sK1),sK1) = k3_subset_1(sK0,sK1)
% 31.47/4.51      | sK1 = sK0 ),
% 31.47/4.51      inference(superposition,[status(thm)],[c_857,c_851]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_2201,plain,
% 31.47/4.51      ( k6_subset_1(sK1,k3_subset_1(sK0,sK1)) = k5_xboole_0(sK1,k3_subset_1(sK0,sK1))
% 31.47/4.51      | sK1 = sK0 ),
% 31.47/4.51      inference(superposition,[status(thm)],[c_2133,c_1394]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_2586,plain,
% 31.47/4.51      ( sK1 = sK0
% 31.47/4.51      | m1_subset_1(k5_xboole_0(sK1,k3_subset_1(sK0,sK1)),k1_zfmisc_1(sK1)) = iProver_top ),
% 31.47/4.51      inference(superposition,[status(thm)],[c_2201,c_846]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_11306,plain,
% 31.47/4.51      ( sK1 = sK0
% 31.47/4.51      | m1_subset_1(k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)),k1_zfmisc_1(sK1)) = iProver_top ),
% 31.47/4.51      inference(demodulation,[status(thm)],[c_11178,c_2586]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_24,negated_conjecture,
% 31.47/4.51      ( ~ r1_tarski(k3_subset_1(sK0,sK1),sK1)
% 31.47/4.51      | k3_subset_1(sK0,k1_xboole_0) != sK1 ),
% 31.47/4.51      inference(cnf_transformation,[],[f90]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_841,plain,
% 31.47/4.51      ( k3_subset_1(sK0,k1_xboole_0) != sK1
% 31.47/4.51      | r1_tarski(k3_subset_1(sK0,sK1),sK1) != iProver_top ),
% 31.47/4.51      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_863,plain,
% 31.47/4.51      ( sK1 != sK0 | r1_tarski(k3_subset_1(sK0,sK1),sK1) != iProver_top ),
% 31.47/4.51      inference(demodulation,[status(thm)],[c_841,c_15]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_873,plain,
% 31.47/4.51      ( ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) | sK1 != sK0 ),
% 31.47/4.51      inference(predicate_to_equality_rev,[status(thm)],[c_863]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_2,plain,
% 31.47/4.51      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 31.47/4.51      inference(cnf_transformation,[],[f48]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_913,plain,
% 31.47/4.51      ( ~ r1_tarski(X0,sK1) | ~ r1_tarski(sK1,X0) | sK1 = X0 ),
% 31.47/4.51      inference(instantiation,[status(thm)],[c_2]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_956,plain,
% 31.47/4.51      ( ~ r1_tarski(sK1,sK1) | sK1 = sK1 ),
% 31.47/4.51      inference(instantiation,[status(thm)],[c_913]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_4,plain,
% 31.47/4.51      ( r1_tarski(X0,X0) ),
% 31.47/4.51      inference(cnf_transformation,[],[f93]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_1029,plain,
% 31.47/4.51      ( r1_tarski(sK1,sK1) ),
% 31.47/4.51      inference(instantiation,[status(thm)],[c_4]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_1030,plain,
% 31.47/4.51      ( r1_tarski(sK1,sK1) = iProver_top ),
% 31.47/4.51      inference(predicate_to_equality,[status(thm)],[c_1029]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_436,plain,
% 31.47/4.51      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 31.47/4.51      theory(equality) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_905,plain,
% 31.47/4.51      ( ~ r1_tarski(X0,X1)
% 31.47/4.51      | r1_tarski(k3_subset_1(sK0,k1_xboole_0),sK1)
% 31.47/4.51      | k3_subset_1(sK0,k1_xboole_0) != X0
% 31.47/4.51      | sK1 != X1 ),
% 31.47/4.51      inference(instantiation,[status(thm)],[c_436]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_936,plain,
% 31.47/4.51      ( ~ r1_tarski(X0,sK1)
% 31.47/4.51      | r1_tarski(k3_subset_1(sK0,k1_xboole_0),sK1)
% 31.47/4.51      | k3_subset_1(sK0,k1_xboole_0) != X0
% 31.47/4.51      | sK1 != sK1 ),
% 31.47/4.51      inference(instantiation,[status(thm)],[c_905]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_1198,plain,
% 31.47/4.51      ( r1_tarski(k3_subset_1(sK0,k1_xboole_0),sK1)
% 31.47/4.51      | ~ r1_tarski(sK1,sK1)
% 31.47/4.51      | k3_subset_1(sK0,k1_xboole_0) != sK1
% 31.47/4.51      | sK1 != sK1 ),
% 31.47/4.51      inference(instantiation,[status(thm)],[c_936]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_1199,plain,
% 31.47/4.51      ( k3_subset_1(sK0,k1_xboole_0) != sK1
% 31.47/4.51      | sK1 != sK1
% 31.47/4.51      | r1_tarski(k3_subset_1(sK0,k1_xboole_0),sK1) = iProver_top
% 31.47/4.51      | r1_tarski(sK1,sK1) != iProver_top ),
% 31.47/4.51      inference(predicate_to_equality,[status(thm)],[c_1198]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_6,plain,
% 31.47/4.51      ( r1_tarski(X0,X1)
% 31.47/4.51      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
% 31.47/4.51      inference(cnf_transformation,[],[f81]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_852,plain,
% 31.47/4.51      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0
% 31.47/4.51      | r1_tarski(X0,X1) = iProver_top ),
% 31.47/4.51      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_861,plain,
% 31.47/4.51      ( k6_subset_1(X0,X1) != k1_xboole_0
% 31.47/4.51      | r1_tarski(X0,X1) = iProver_top ),
% 31.47/4.51      inference(light_normalisation,[status(thm)],[c_852,c_20]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_5886,plain,
% 31.47/4.51      ( k3_subset_1(sK0,sK1) != k1_xboole_0
% 31.47/4.51      | r1_tarski(sK0,sK1) = iProver_top ),
% 31.47/4.51      inference(superposition,[status(thm)],[c_5604,c_861]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_61,plain,
% 31.47/4.51      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 31.47/4.51      inference(instantiation,[status(thm)],[c_9]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_62,plain,
% 31.47/4.51      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 31.47/4.51      inference(instantiation,[status(thm)],[c_60]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_74,plain,
% 31.47/4.51      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 31.47/4.51      | k1_xboole_0 = k1_xboole_0 ),
% 31.47/4.51      inference(instantiation,[status(thm)],[c_2]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_892,plain,
% 31.47/4.51      ( ~ r1_tarski(k3_subset_1(sK0,k1_xboole_0),sK1)
% 31.47/4.51      | ~ r1_tarski(sK1,k3_subset_1(sK0,k1_xboole_0))
% 31.47/4.51      | k3_subset_1(sK0,k1_xboole_0) = sK1 ),
% 31.47/4.51      inference(instantiation,[status(thm)],[c_2]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_893,plain,
% 31.47/4.51      ( k3_subset_1(sK0,k1_xboole_0) = sK1
% 31.47/4.51      | r1_tarski(k3_subset_1(sK0,k1_xboole_0),sK1) != iProver_top
% 31.47/4.51      | r1_tarski(sK1,k3_subset_1(sK0,k1_xboole_0)) != iProver_top ),
% 31.47/4.51      inference(predicate_to_equality,[status(thm)],[c_892]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_1357,plain,
% 31.47/4.51      ( r1_tarski(k1_xboole_0,sK1) ),
% 31.47/4.51      inference(instantiation,[status(thm)],[c_9]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_1473,plain,
% 31.47/4.51      ( ~ r1_tarski(X0,X1)
% 31.47/4.51      | r1_tarski(X2,k3_subset_1(sK0,sK1))
% 31.47/4.51      | X2 != X0
% 31.47/4.51      | k3_subset_1(sK0,sK1) != X1 ),
% 31.47/4.51      inference(instantiation,[status(thm)],[c_436]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_1474,plain,
% 31.47/4.51      ( X0 != X1
% 31.47/4.51      | k3_subset_1(sK0,sK1) != X2
% 31.47/4.51      | r1_tarski(X1,X2) != iProver_top
% 31.47/4.51      | r1_tarski(X0,k3_subset_1(sK0,sK1)) = iProver_top ),
% 31.47/4.51      inference(predicate_to_equality,[status(thm)],[c_1473]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_1476,plain,
% 31.47/4.51      ( k3_subset_1(sK0,sK1) != k1_xboole_0
% 31.47/4.51      | k1_xboole_0 != k1_xboole_0
% 31.47/4.51      | r1_tarski(k1_xboole_0,k3_subset_1(sK0,sK1)) = iProver_top
% 31.47/4.51      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 31.47/4.51      inference(instantiation,[status(thm)],[c_1474]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_2091,plain,
% 31.47/4.51      ( r1_tarski(k3_subset_1(sK0,k1_xboole_0),sK1)
% 31.47/4.51      | ~ r1_tarski(sK0,sK1)
% 31.47/4.51      | k3_subset_1(sK0,k1_xboole_0) != sK0
% 31.47/4.51      | sK1 != sK1 ),
% 31.47/4.51      inference(instantiation,[status(thm)],[c_936]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_2092,plain,
% 31.47/4.51      ( k3_subset_1(sK0,k1_xboole_0) != sK0
% 31.47/4.51      | sK1 != sK1
% 31.47/4.51      | r1_tarski(k3_subset_1(sK0,k1_xboole_0),sK1) = iProver_top
% 31.47/4.51      | r1_tarski(sK0,sK1) != iProver_top ),
% 31.47/4.51      inference(predicate_to_equality,[status(thm)],[c_2091]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_967,plain,
% 31.47/4.51      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,sK1) | X2 != X0 | sK1 != X1 ),
% 31.47/4.51      inference(instantiation,[status(thm)],[c_436]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_1170,plain,
% 31.47/4.51      ( ~ r1_tarski(X0,sK1) | r1_tarski(X1,sK1) | X1 != X0 | sK1 != sK1 ),
% 31.47/4.51      inference(instantiation,[status(thm)],[c_967]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_1370,plain,
% 31.47/4.51      ( r1_tarski(X0,sK1)
% 31.47/4.51      | ~ r1_tarski(k1_xboole_0,sK1)
% 31.47/4.51      | X0 != k1_xboole_0
% 31.47/4.51      | sK1 != sK1 ),
% 31.47/4.51      inference(instantiation,[status(thm)],[c_1170]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_3444,plain,
% 31.47/4.51      ( r1_tarski(k3_subset_1(sK0,sK1),sK1)
% 31.47/4.51      | ~ r1_tarski(k1_xboole_0,sK1)
% 31.47/4.51      | k3_subset_1(sK0,sK1) != k1_xboole_0
% 31.47/4.51      | sK1 != sK1 ),
% 31.47/4.51      inference(instantiation,[status(thm)],[c_1370]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_3561,plain,
% 31.47/4.51      ( k3_subset_1(sK0,k1_xboole_0) = sK0 ),
% 31.47/4.51      inference(instantiation,[status(thm)],[c_15]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_5679,plain,
% 31.47/4.51      ( m1_subset_1(X0,k1_zfmisc_1(sK0)) != iProver_top
% 31.47/4.51      | m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) != iProver_top
% 31.47/4.51      | r1_tarski(X0,k3_subset_1(sK0,sK1)) != iProver_top
% 31.47/4.51      | r1_tarski(sK1,k3_subset_1(sK0,X0)) = iProver_top ),
% 31.47/4.51      inference(superposition,[status(thm)],[c_5483,c_843]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_5692,plain,
% 31.47/4.51      ( m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) != iProver_top
% 31.47/4.51      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) != iProver_top
% 31.47/4.51      | r1_tarski(sK1,k3_subset_1(sK0,k1_xboole_0)) = iProver_top
% 31.47/4.51      | r1_tarski(k1_xboole_0,k3_subset_1(sK0,sK1)) != iProver_top ),
% 31.47/4.51      inference(instantiation,[status(thm)],[c_5679]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_6106,plain,
% 31.47/4.51      ( k3_subset_1(sK0,sK1) != k1_xboole_0 ),
% 31.47/4.51      inference(global_propositional_subsumption,
% 31.47/4.51                [status(thm)],
% 31.47/4.51                [c_5886,c_24,c_61,c_62,c_74,c_893,c_956,c_1029,c_1357,
% 31.47/4.51                 c_1476,c_1798,c_2092,c_3444,c_3561,c_5692,c_5887]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_1340,plain,
% 31.47/4.51      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 31.47/4.51      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) != iProver_top
% 31.47/4.51      | r1_tarski(X1,k3_subset_1(X1,X0)) = iProver_top
% 31.47/4.51      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 31.47/4.51      inference(superposition,[status(thm)],[c_15,c_843]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_5675,plain,
% 31.47/4.51      ( m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) != iProver_top
% 31.47/4.51      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) != iProver_top
% 31.47/4.51      | r1_tarski(k3_subset_1(sK0,sK1),k1_xboole_0) != iProver_top
% 31.47/4.51      | r1_tarski(sK0,sK1) = iProver_top ),
% 31.47/4.51      inference(superposition,[status(thm)],[c_5483,c_1340]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_6291,plain,
% 31.47/4.51      ( r1_tarski(k3_subset_1(sK0,sK1),k1_xboole_0) != iProver_top
% 31.47/4.51      | r1_tarski(sK0,sK1) = iProver_top ),
% 31.47/4.51      inference(global_propositional_subsumption,
% 31.47/4.51                [status(thm)],
% 31.47/4.51                [c_5675,c_1798,c_5887]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_21,plain,
% 31.47/4.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 31.47/4.51      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 31.47/4.51      | r1_tarski(X0,X2)
% 31.47/4.51      | ~ r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X0)) ),
% 31.47/4.51      inference(cnf_transformation,[],[f72]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_844,plain,
% 31.47/4.51      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 31.47/4.51      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 31.47/4.51      | r1_tarski(X0,X2) = iProver_top
% 31.47/4.51      | r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X0)) != iProver_top ),
% 31.47/4.51      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_5676,plain,
% 31.47/4.51      ( m1_subset_1(X0,k1_zfmisc_1(sK0)) != iProver_top
% 31.47/4.51      | m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) != iProver_top
% 31.47/4.51      | r1_tarski(k3_subset_1(sK0,X0),sK1) != iProver_top
% 31.47/4.51      | r1_tarski(k3_subset_1(sK0,sK1),X0) = iProver_top ),
% 31.47/4.51      inference(superposition,[status(thm)],[c_5483,c_844]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_7257,plain,
% 31.47/4.51      ( m1_subset_1(X0,k1_zfmisc_1(sK0)) != iProver_top
% 31.47/4.51      | r1_tarski(k3_subset_1(sK0,X0),sK1) != iProver_top
% 31.47/4.51      | r1_tarski(k3_subset_1(sK0,sK1),X0) = iProver_top ),
% 31.47/4.51      inference(global_propositional_subsumption,
% 31.47/4.51                [status(thm)],
% 31.47/4.51                [c_5676,c_5887]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_7260,plain,
% 31.47/4.51      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) != iProver_top
% 31.47/4.51      | r1_tarski(k3_subset_1(sK0,sK1),k1_xboole_0) = iProver_top
% 31.47/4.51      | r1_tarski(k3_subset_1(sK0,k1_xboole_0),sK1) != iProver_top ),
% 31.47/4.51      inference(instantiation,[status(thm)],[c_7257]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_7264,plain,
% 31.47/4.51      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) != iProver_top
% 31.47/4.51      | r1_tarski(k3_subset_1(sK0,sK1),k1_xboole_0) = iProver_top
% 31.47/4.51      | r1_tarski(sK0,sK1) != iProver_top ),
% 31.47/4.51      inference(superposition,[status(thm)],[c_15,c_7257]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_8800,plain,
% 31.47/4.51      ( r1_tarski(k3_subset_1(sK0,sK1),k1_xboole_0) = iProver_top
% 31.47/4.51      | r1_tarski(sK0,sK1) != iProver_top ),
% 31.47/4.51      inference(global_propositional_subsumption,
% 31.47/4.51                [status(thm)],
% 31.47/4.51                [c_7264,c_1798]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_5,plain,
% 31.47/4.51      ( ~ r1_tarski(X0,X1)
% 31.47/4.51      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
% 31.47/4.51      inference(cnf_transformation,[],[f80]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_853,plain,
% 31.47/4.51      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
% 31.47/4.51      | r1_tarski(X0,X1) != iProver_top ),
% 31.47/4.51      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_862,plain,
% 31.47/4.51      ( k6_subset_1(X0,X1) = k1_xboole_0
% 31.47/4.51      | r1_tarski(X0,X1) != iProver_top ),
% 31.47/4.51      inference(demodulation,[status(thm)],[c_853,c_20]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_8805,plain,
% 31.47/4.51      ( k6_subset_1(k3_subset_1(sK0,sK1),k1_xboole_0) = k1_xboole_0
% 31.47/4.51      | r1_tarski(sK0,sK1) != iProver_top ),
% 31.47/4.51      inference(superposition,[status(thm)],[c_8800,c_862]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_842,plain,
% 31.47/4.51      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 31.47/4.51      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_5603,plain,
% 31.47/4.51      ( k6_subset_1(X0,k1_xboole_0) = k3_subset_1(X0,k1_xboole_0) ),
% 31.47/4.51      inference(superposition,[status(thm)],[c_842,c_864]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_5633,plain,
% 31.47/4.51      ( k6_subset_1(X0,k1_xboole_0) = X0 ),
% 31.47/4.51      inference(light_normalisation,[status(thm)],[c_5603,c_15]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_8810,plain,
% 31.47/4.51      ( k3_subset_1(sK0,sK1) = k1_xboole_0
% 31.47/4.51      | r1_tarski(sK0,sK1) != iProver_top ),
% 31.47/4.51      inference(demodulation,[status(thm)],[c_8805,c_5633]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_21496,plain,
% 31.47/4.51      ( m1_subset_1(k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)),k1_zfmisc_1(sK1)) = iProver_top ),
% 31.47/4.51      inference(global_propositional_subsumption,
% 31.47/4.51                [status(thm)],
% 31.47/4.51                [c_11306,c_25,c_24,c_61,c_62,c_74,c_873,c_893,c_956,
% 31.47/4.51                 c_1029,c_1030,c_1199,c_1357,c_1476,c_1798,c_2092,c_3444,
% 31.47/4.51                 c_3561,c_5692,c_5886,c_5887,c_6291,c_7260,c_8810]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_21500,plain,
% 31.47/4.51      ( k6_subset_1(sK1,k5_xboole_0(sK1,k5_xboole_0(sK0,sK1))) = k3_subset_1(sK1,k5_xboole_0(sK1,k5_xboole_0(sK0,sK1))) ),
% 31.47/4.51      inference(superposition,[status(thm)],[c_21496,c_864]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_11181,plain,
% 31.47/4.51      ( k6_subset_1(sK1,k5_xboole_0(sK1,k5_xboole_0(sK0,sK1))) = k1_xboole_0 ),
% 31.47/4.51      inference(superposition,[status(thm)],[c_7929,c_858]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_21502,plain,
% 31.47/4.51      ( k3_subset_1(sK1,k5_xboole_0(sK1,k5_xboole_0(sK0,sK1))) = k1_xboole_0 ),
% 31.47/4.51      inference(light_normalisation,[status(thm)],[c_21500,c_11181]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_21501,plain,
% 31.47/4.51      ( k3_subset_1(sK1,k3_subset_1(sK1,k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)))) = k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) ),
% 31.47/4.51      inference(superposition,[status(thm)],[c_21496,c_845]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_21503,plain,
% 31.47/4.51      ( k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k3_subset_1(sK1,k1_xboole_0) ),
% 31.47/4.51      inference(demodulation,[status(thm)],[c_21502,c_21501]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_21504,plain,
% 31.47/4.51      ( k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = sK1 ),
% 31.47/4.51      inference(demodulation,[status(thm)],[c_21503,c_15]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_79218,plain,
% 31.47/4.51      ( k5_xboole_0(sK0,sK1) = k1_xboole_0 ),
% 31.47/4.51      inference(light_normalisation,
% 31.47/4.51                [status(thm)],
% 31.47/4.51                [c_79180,c_7929,c_21504]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(c_11179,plain,
% 31.47/4.51      ( k5_xboole_0(sK0,sK1) != k1_xboole_0
% 31.47/4.51      | r1_tarski(sK0,sK1) = iProver_top ),
% 31.47/4.51      inference(superposition,[status(thm)],[c_7929,c_861]) ).
% 31.47/4.51  
% 31.47/4.51  cnf(contradiction,plain,
% 31.47/4.51      ( $false ),
% 31.47/4.51      inference(minisat,[status(thm)],[c_79218,c_11179,c_8810,c_6106]) ).
% 31.47/4.51  
% 31.47/4.51  
% 31.47/4.51  % SZS output end CNFRefutation for theBenchmark.p
% 31.47/4.51  
% 31.47/4.51  ------                               Statistics
% 31.47/4.51  
% 31.47/4.51  ------ General
% 31.47/4.51  
% 31.47/4.51  abstr_ref_over_cycles:                  0
% 31.47/4.51  abstr_ref_under_cycles:                 0
% 31.47/4.51  gc_basic_clause_elim:                   0
% 31.47/4.51  forced_gc_time:                         0
% 31.47/4.51  parsing_time:                           0.009
% 31.47/4.51  unif_index_cands_time:                  0.
% 31.47/4.51  unif_index_add_time:                    0.
% 31.47/4.51  orderings_time:                         0.
% 31.47/4.51  out_proof_time:                         0.017
% 31.47/4.51  total_time:                             3.582
% 31.47/4.51  num_of_symbols:                         43
% 31.47/4.51  num_of_terms:                           181409
% 31.47/4.51  
% 31.47/4.51  ------ Preprocessing
% 31.47/4.51  
% 31.47/4.51  num_of_splits:                          0
% 31.47/4.51  num_of_split_atoms:                     0
% 31.47/4.51  num_of_reused_defs:                     0
% 31.47/4.51  num_eq_ax_congr_red:                    18
% 31.47/4.51  num_of_sem_filtered_clauses:            1
% 31.47/4.51  num_of_subtypes:                        0
% 31.47/4.51  monotx_restored_types:                  0
% 31.47/4.51  sat_num_of_epr_types:                   0
% 31.47/4.51  sat_num_of_non_cyclic_types:            0
% 31.47/4.51  sat_guarded_non_collapsed_types:        0
% 31.47/4.51  num_pure_diseq_elim:                    0
% 31.47/4.51  simp_replaced_by:                       0
% 31.47/4.51  res_preprocessed:                       123
% 31.47/4.51  prep_upred:                             0
% 31.47/4.51  prep_unflattend:                        0
% 31.47/4.51  smt_new_axioms:                         0
% 31.47/4.51  pred_elim_cands:                        2
% 31.47/4.51  pred_elim:                              0
% 31.47/4.51  pred_elim_cl:                           0
% 31.47/4.51  pred_elim_cycles:                       2
% 31.47/4.51  merged_defs:                            16
% 31.47/4.51  merged_defs_ncl:                        0
% 31.47/4.51  bin_hyper_res:                          16
% 31.47/4.51  prep_cycles:                            4
% 31.47/4.51  pred_elim_time:                         0.
% 31.47/4.51  splitting_time:                         0.
% 31.47/4.51  sem_filter_time:                        0.
% 31.47/4.51  monotx_time:                            0.
% 31.47/4.51  subtype_inf_time:                       0.
% 31.47/4.51  
% 31.47/4.51  ------ Problem properties
% 31.47/4.51  
% 31.47/4.51  clauses:                                26
% 31.47/4.51  conjectures:                            3
% 31.47/4.51  epr:                                    3
% 31.47/4.51  horn:                                   25
% 31.47/4.51  ground:                                 3
% 31.47/4.51  unary:                                  15
% 31.47/4.51  binary:                                 8
% 31.47/4.51  lits:                                   42
% 31.47/4.51  lits_eq:                                17
% 31.47/4.51  fd_pure:                                0
% 31.47/4.51  fd_pseudo:                              0
% 31.47/4.51  fd_cond:                                0
% 31.47/4.51  fd_pseudo_cond:                         1
% 31.47/4.51  ac_symbols:                             0
% 31.47/4.51  
% 31.47/4.51  ------ Propositional Solver
% 31.47/4.51  
% 31.47/4.51  prop_solver_calls:                      38
% 31.47/4.51  prop_fast_solver_calls:                 1116
% 31.47/4.51  smt_solver_calls:                       0
% 31.47/4.51  smt_fast_solver_calls:                  0
% 31.47/4.51  prop_num_of_clauses:                    37559
% 31.47/4.51  prop_preprocess_simplified:             18262
% 31.47/4.51  prop_fo_subsumed:                       64
% 31.47/4.51  prop_solver_time:                       0.
% 31.47/4.51  smt_solver_time:                        0.
% 31.47/4.51  smt_fast_solver_time:                   0.
% 31.47/4.51  prop_fast_solver_time:                  0.
% 31.47/4.51  prop_unsat_core_time:                   0.003
% 31.47/4.51  
% 31.47/4.51  ------ QBF
% 31.47/4.51  
% 31.47/4.51  qbf_q_res:                              0
% 31.47/4.51  qbf_num_tautologies:                    0
% 31.47/4.51  qbf_prep_cycles:                        0
% 31.47/4.51  
% 31.47/4.51  ------ BMC1
% 31.47/4.51  
% 31.47/4.51  bmc1_current_bound:                     -1
% 31.47/4.51  bmc1_last_solved_bound:                 -1
% 31.47/4.51  bmc1_unsat_core_size:                   -1
% 31.47/4.51  bmc1_unsat_core_parents_size:           -1
% 31.47/4.51  bmc1_merge_next_fun:                    0
% 31.47/4.51  bmc1_unsat_core_clauses_time:           0.
% 31.47/4.51  
% 31.47/4.51  ------ Instantiation
% 31.47/4.51  
% 31.47/4.51  inst_num_of_clauses:                    2927
% 31.47/4.51  inst_num_in_passive:                    442
% 31.47/4.51  inst_num_in_active:                     1190
% 31.47/4.51  inst_num_in_unprocessed:                1296
% 31.47/4.51  inst_num_of_loops:                      1440
% 31.47/4.51  inst_num_of_learning_restarts:          0
% 31.47/4.51  inst_num_moves_active_passive:          247
% 31.47/4.51  inst_lit_activity:                      0
% 31.47/4.51  inst_lit_activity_moves:                0
% 31.47/4.51  inst_num_tautologies:                   0
% 31.47/4.51  inst_num_prop_implied:                  0
% 31.47/4.51  inst_num_existing_simplified:           0
% 31.47/4.51  inst_num_eq_res_simplified:             0
% 31.47/4.51  inst_num_child_elim:                    0
% 31.47/4.51  inst_num_of_dismatching_blockings:      1303
% 31.47/4.51  inst_num_of_non_proper_insts:           3911
% 31.47/4.51  inst_num_of_duplicates:                 0
% 31.47/4.51  inst_inst_num_from_inst_to_res:         0
% 31.47/4.51  inst_dismatching_checking_time:         0.
% 31.47/4.51  
% 31.47/4.51  ------ Resolution
% 31.47/4.51  
% 31.47/4.51  res_num_of_clauses:                     0
% 31.47/4.51  res_num_in_passive:                     0
% 31.47/4.51  res_num_in_active:                      0
% 31.47/4.51  res_num_of_loops:                       127
% 31.47/4.51  res_forward_subset_subsumed:            387
% 31.47/4.51  res_backward_subset_subsumed:           6
% 31.47/4.51  res_forward_subsumed:                   0
% 31.47/4.51  res_backward_subsumed:                  0
% 31.47/4.51  res_forward_subsumption_resolution:     0
% 31.47/4.51  res_backward_subsumption_resolution:    0
% 31.47/4.51  res_clause_to_clause_subsumption:       248501
% 31.47/4.51  res_orphan_elimination:                 0
% 31.47/4.51  res_tautology_del:                      201
% 31.47/4.51  res_num_eq_res_simplified:              0
% 31.47/4.51  res_num_sel_changes:                    0
% 31.47/4.51  res_moves_from_active_to_pass:          0
% 31.47/4.51  
% 31.47/4.51  ------ Superposition
% 31.47/4.51  
% 31.47/4.51  sup_time_total:                         0.
% 31.47/4.51  sup_time_generating:                    0.
% 31.47/4.51  sup_time_sim_full:                      0.
% 31.47/4.51  sup_time_sim_immed:                     0.
% 31.47/4.51  
% 31.47/4.51  sup_num_of_clauses:                     12064
% 31.47/4.51  sup_num_in_active:                      226
% 31.47/4.51  sup_num_in_passive:                     11838
% 31.47/4.51  sup_num_of_loops:                       286
% 31.47/4.51  sup_fw_superposition:                   16026
% 31.47/4.51  sup_bw_superposition:                   16859
% 31.47/4.51  sup_immediate_simplified:               10872
% 31.47/4.51  sup_given_eliminated:                   1
% 31.47/4.51  comparisons_done:                       0
% 31.47/4.51  comparisons_avoided:                    48
% 31.47/4.51  
% 31.47/4.51  ------ Simplifications
% 31.47/4.51  
% 31.47/4.51  
% 31.47/4.51  sim_fw_subset_subsumed:                 31
% 31.47/4.51  sim_bw_subset_subsumed:                 10
% 31.47/4.51  sim_fw_subsumed:                        2238
% 31.47/4.51  sim_bw_subsumed:                        1126
% 31.47/4.51  sim_fw_subsumption_res:                 0
% 31.47/4.51  sim_bw_subsumption_res:                 0
% 31.47/4.51  sim_tautology_del:                      32
% 31.47/4.51  sim_eq_tautology_del:                   1438
% 31.47/4.51  sim_eq_res_simp:                        0
% 31.47/4.51  sim_fw_demodulated:                     6351
% 31.47/4.51  sim_bw_demodulated:                     142
% 31.47/4.51  sim_light_normalised:                   3118
% 31.47/4.51  sim_joinable_taut:                      0
% 31.47/4.51  sim_joinable_simp:                      0
% 31.47/4.51  sim_ac_normalised:                      0
% 31.47/4.51  sim_smt_subsumption:                    0
% 31.47/4.51  
%------------------------------------------------------------------------------
