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
% DateTime   : Thu Dec  3 11:40:01 EST 2020

% Result     : Theorem 7.26s
% Output     : CNFRefutation 7.26s
% Verified   : 
% Statistics : Number of formulae       :  169 (1802 expanded)
%              Number of clauses        :   97 ( 608 expanded)
%              Number of leaves         :   25 ( 419 expanded)
%              Depth                    :   20
%              Number of atoms          :  313 (3139 expanded)
%              Number of equality atoms :  192 (1825 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(k3_subset_1(X0,X1),X1)
      <=> k2_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(k3_subset_1(X0,X1),X1)
        <=> k2_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f27,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(k3_subset_1(X0,X1),X1)
      <~> k2_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f31,plain,(
    ? [X0,X1] :
      ( ( k2_subset_1(X0) != X1
        | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
      & ( k2_subset_1(X0) = X1
        | r1_tarski(k3_subset_1(X0,X1),X1) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f32,plain,(
    ? [X0,X1] :
      ( ( k2_subset_1(X0) != X1
        | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
      & ( k2_subset_1(X0) = X1
        | r1_tarski(k3_subset_1(X0,X1),X1) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f31])).

fof(f33,plain,
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

fof(f34,plain,
    ( ( k2_subset_1(sK0) != sK1
      | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) )
    & ( k2_subset_1(sK0) = sK1
      | r1_tarski(k3_subset_1(sK0,sK1),sK1) )
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f33])).

fof(f58,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f34])).

fof(f20,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f14,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f18,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f13,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f63,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f54,f49])).

fof(f68,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f50,f63])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_tarski(X1,X2)
              | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f16,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f70,plain,(
    ! [X0] : m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f52,f63])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f51,f39])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f65,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f43,f39])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f8,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f61,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f44,f39])).

fof(f64,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X0))) = X0 ),
    inference(definition_unfolding,[],[f40,f61])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f28])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f74,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f36])).

fof(f59,plain,
    ( k2_subset_1(sK0) = sK1
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f72,plain,
    ( k3_subset_1(sK0,k1_xboole_0) = sK1
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(definition_unfolding,[],[f59,f63])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f62,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f46,f47])).

fof(f66,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f45,f62,f62])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f67,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f48,f61,f62])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f60,plain,
    ( k2_subset_1(sK0) != sK1
    | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f71,plain,
    ( k3_subset_1(sK0,k1_xboole_0) != sK1
    | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(definition_unfolding,[],[f60,f63])).

fof(f38,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_347,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2524,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | k3_subset_1(sK0,sK1) != X0
    | sK1 != X1 ),
    inference(instantiation,[status(thm)],[c_347])).

cnf(c_33361,plain,
    ( r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | ~ r1_tarski(k1_xboole_0,X0)
    | k3_subset_1(sK0,sK1) != k1_xboole_0
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_2524])).

cnf(c_33365,plain,
    ( r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | ~ r1_tarski(k1_xboole_0,sK1)
    | k3_subset_1(sK0,sK1) != k1_xboole_0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_33361])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_690,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_16,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_693,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_696,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3226,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_693,c_696])).

cnf(c_10,plain,
    ( k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_3234,plain,
    ( k3_subset_1(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3226,c_10])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | r1_tarski(X0,X2)
    | ~ r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_695,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X2) = iProver_top
    | r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3793,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k1_xboole_0,k3_subset_1(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3234,c_695])).

cnf(c_6,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_700,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_12,plain,
    ( m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_697,plain,
    ( m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_716,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_697,c_10])).

cnf(c_18677,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3793,c_700,c_716])).

cnf(c_18680,plain,
    ( r1_tarski(sK1,sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_690,c_18677])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_701,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_19198,plain,
    ( k3_xboole_0(sK1,sK0) = sK1 ),
    inference(superposition,[status(thm)],[c_18680,c_701])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_698,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4030,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) = k3_subset_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_690,c_698])).

cnf(c_7,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_699,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1568,plain,
    ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_699,c_701])).

cnf(c_12329,plain,
    ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X0) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_0,c_1568])).

cnf(c_4,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X0))) = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_12693,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X0,k3_xboole_0(X1,X0))))) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_12329,c_4])).

cnf(c_17331,plain,
    ( k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK1,sK0)),k5_xboole_0(k3_subset_1(sK0,sK1),k3_xboole_0(k3_subset_1(sK0,sK1),k5_xboole_0(sK0,k3_xboole_0(sK1,sK0))))) = k5_xboole_0(sK0,k3_xboole_0(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_4030,c_12693])).

cnf(c_17933,plain,
    ( k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k5_xboole_0(k3_subset_1(sK0,sK1),k3_xboole_0(k3_subset_1(sK0,sK1),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))))) = k5_xboole_0(sK0,k3_xboole_0(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_0,c_17331])).

cnf(c_17945,plain,
    ( k5_xboole_0(k3_subset_1(sK0,sK1),k5_xboole_0(k3_subset_1(sK0,sK1),k3_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1)))) = k5_xboole_0(sK0,k3_xboole_0(sK1,sK0)) ),
    inference(light_normalisation,[status(thm)],[c_17933,c_4030])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_702,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1566,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_702,c_701])).

cnf(c_1567,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_700,c_701])).

cnf(c_4029,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = k3_subset_1(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_693,c_698])).

cnf(c_4038,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_4029,c_10])).

cnf(c_5209,plain,
    ( k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_0,c_4038])).

cnf(c_6028,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(demodulation,[status(thm)],[c_1567,c_5209])).

cnf(c_4031,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k3_subset_1(X0,X0) ),
    inference(superposition,[status(thm)],[c_716,c_698])).

cnf(c_4033,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4031,c_3234])).

cnf(c_7870,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4033,c_1566])).

cnf(c_17946,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK1,sK0)) = k3_subset_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_17945,c_1566,c_6028,c_7870])).

cnf(c_19410,plain,
    ( k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_19198,c_17946])).

cnf(c_18,negated_conjecture,
    ( r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | k3_subset_1(sK0,k1_xboole_0) = sK1 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_691,plain,
    ( k3_subset_1(sK0,k1_xboole_0) = sK1
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_727,plain,
    ( sK1 = sK0
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_691,c_10])).

cnf(c_1570,plain,
    ( k3_xboole_0(k3_subset_1(sK0,sK1),sK1) = k3_subset_1(sK0,sK1)
    | sK1 = sK0 ),
    inference(superposition,[status(thm)],[c_727,c_701])).

cnf(c_19773,plain,
    ( k3_xboole_0(k5_xboole_0(sK0,sK1),sK1) = k5_xboole_0(sK0,sK1)
    | sK1 = sK0 ),
    inference(demodulation,[status(thm)],[c_19410,c_1570])).

cnf(c_1412,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_699])).

cnf(c_1571,plain,
    ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X0) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_1412,c_701])).

cnf(c_26072,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK0,sK1),sK1)) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)),sK1)
    | sK1 = sK0 ),
    inference(superposition,[status(thm)],[c_19773,c_1571])).

cnf(c_8,plain,
    ( k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_9,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1400,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k3_tarski(k2_enumset1(X1,X1,X1,X0)) ),
    inference(superposition,[status(thm)],[c_8,c_9])).

cnf(c_3077,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_1400,c_9])).

cnf(c_4215,plain,
    ( k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))) = k5_xboole_0(sK1,k3_subset_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_4030,c_3077])).

cnf(c_19411,plain,
    ( k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)) = k5_xboole_0(sK1,k3_subset_1(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_19198,c_4215])).

cnf(c_19413,plain,
    ( k5_xboole_0(sK1,k3_subset_1(sK0,sK1)) = sK0 ),
    inference(demodulation,[status(thm)],[c_19411,c_6028,c_7870])).

cnf(c_19416,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = sK0 ),
    inference(demodulation,[status(thm)],[c_19410,c_19413])).

cnf(c_19453,plain,
    ( k3_xboole_0(sK0,sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_19198,c_0])).

cnf(c_26165,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK0,sK1),sK1)) = sK1
    | sK1 = sK0 ),
    inference(light_normalisation,[status(thm)],[c_26072,c_19416,c_19453])).

cnf(c_31837,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = sK1
    | sK1 = sK0 ),
    inference(superposition,[status(thm)],[c_19773,c_26165])).

cnf(c_31893,plain,
    ( sK1 = sK0 ),
    inference(light_normalisation,[status(thm)],[c_31837,c_19416])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X0)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_694,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1569,plain,
    ( k3_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2)) = k3_subset_1(X0,X1)
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(X2,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_694,c_701])).

cnf(c_6870,plain,
    ( k3_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,X0)) = k3_subset_1(sK0,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(sK0)) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_690,c_1569])).

cnf(c_7230,plain,
    ( k3_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK0)) = k3_subset_1(sK0,sK1)
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_716,c_6870])).

cnf(c_6055,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1567,c_0])).

cnf(c_7233,plain,
    ( k3_subset_1(sK0,sK1) = k1_xboole_0
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7230,c_3234,c_6055])).

cnf(c_7242,plain,
    ( ~ r1_tarski(sK0,sK1)
    | k3_subset_1(sK0,sK1) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7233])).

cnf(c_345,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1189,plain,
    ( X0 != X1
    | sK0 != X1
    | sK0 = X0 ),
    inference(instantiation,[status(thm)],[c_345])).

cnf(c_1746,plain,
    ( X0 != sK0
    | sK0 = X0
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_1189])).

cnf(c_1747,plain,
    ( sK1 != sK0
    | sK0 = sK1
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_1746])).

cnf(c_1481,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK0,X2)
    | X2 != X1
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_347])).

cnf(c_1483,plain,
    ( ~ r1_tarski(sK1,sK1)
    | r1_tarski(sK0,sK1)
    | sK1 != sK1
    | sK0 != sK1 ),
    inference(instantiation,[status(thm)],[c_1481])).

cnf(c_344,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1187,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_344])).

cnf(c_17,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | k3_subset_1(sK0,k1_xboole_0) != sK1 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_692,plain,
    ( k3_subset_1(sK0,k1_xboole_0) != sK1
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_736,plain,
    ( sK1 != sK0
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_692,c_10])).

cnf(c_772,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | sK1 != sK0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_736])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_59,plain,
    ( ~ r1_tarski(sK1,sK1)
    | sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_55,plain,
    ( r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_48,plain,
    ( r1_tarski(k1_xboole_0,sK1) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_33365,c_31893,c_7242,c_1747,c_1483,c_1187,c_772,c_59,c_55,c_48])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:51:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.26/1.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.26/1.50  
% 7.26/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.26/1.50  
% 7.26/1.50  ------  iProver source info
% 7.26/1.50  
% 7.26/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.26/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.26/1.50  git: non_committed_changes: false
% 7.26/1.50  git: last_make_outside_of_git: false
% 7.26/1.50  
% 7.26/1.50  ------ 
% 7.26/1.50  
% 7.26/1.50  ------ Input Options
% 7.26/1.50  
% 7.26/1.50  --out_options                           all
% 7.26/1.50  --tptp_safe_out                         true
% 7.26/1.50  --problem_path                          ""
% 7.26/1.50  --include_path                          ""
% 7.26/1.50  --clausifier                            res/vclausify_rel
% 7.26/1.50  --clausifier_options                    --mode clausify
% 7.26/1.50  --stdin                                 false
% 7.26/1.50  --stats_out                             all
% 7.26/1.50  
% 7.26/1.50  ------ General Options
% 7.26/1.50  
% 7.26/1.50  --fof                                   false
% 7.26/1.50  --time_out_real                         305.
% 7.26/1.50  --time_out_virtual                      -1.
% 7.26/1.50  --symbol_type_check                     false
% 7.26/1.50  --clausify_out                          false
% 7.26/1.50  --sig_cnt_out                           false
% 7.26/1.50  --trig_cnt_out                          false
% 7.26/1.50  --trig_cnt_out_tolerance                1.
% 7.26/1.50  --trig_cnt_out_sk_spl                   false
% 7.26/1.50  --abstr_cl_out                          false
% 7.26/1.50  
% 7.26/1.50  ------ Global Options
% 7.26/1.50  
% 7.26/1.50  --schedule                              default
% 7.26/1.50  --add_important_lit                     false
% 7.26/1.50  --prop_solver_per_cl                    1000
% 7.26/1.50  --min_unsat_core                        false
% 7.26/1.50  --soft_assumptions                      false
% 7.26/1.50  --soft_lemma_size                       3
% 7.26/1.50  --prop_impl_unit_size                   0
% 7.26/1.50  --prop_impl_unit                        []
% 7.26/1.50  --share_sel_clauses                     true
% 7.26/1.50  --reset_solvers                         false
% 7.26/1.50  --bc_imp_inh                            [conj_cone]
% 7.26/1.50  --conj_cone_tolerance                   3.
% 7.26/1.50  --extra_neg_conj                        none
% 7.26/1.50  --large_theory_mode                     true
% 7.26/1.50  --prolific_symb_bound                   200
% 7.26/1.50  --lt_threshold                          2000
% 7.26/1.50  --clause_weak_htbl                      true
% 7.26/1.50  --gc_record_bc_elim                     false
% 7.26/1.50  
% 7.26/1.50  ------ Preprocessing Options
% 7.26/1.50  
% 7.26/1.50  --preprocessing_flag                    true
% 7.26/1.50  --time_out_prep_mult                    0.1
% 7.26/1.50  --splitting_mode                        input
% 7.26/1.50  --splitting_grd                         true
% 7.26/1.50  --splitting_cvd                         false
% 7.26/1.50  --splitting_cvd_svl                     false
% 7.26/1.50  --splitting_nvd                         32
% 7.26/1.50  --sub_typing                            true
% 7.26/1.50  --prep_gs_sim                           true
% 7.26/1.50  --prep_unflatten                        true
% 7.26/1.50  --prep_res_sim                          true
% 7.26/1.50  --prep_upred                            true
% 7.26/1.50  --prep_sem_filter                       exhaustive
% 7.26/1.50  --prep_sem_filter_out                   false
% 7.26/1.50  --pred_elim                             true
% 7.26/1.50  --res_sim_input                         true
% 7.26/1.50  --eq_ax_congr_red                       true
% 7.26/1.50  --pure_diseq_elim                       true
% 7.26/1.50  --brand_transform                       false
% 7.26/1.50  --non_eq_to_eq                          false
% 7.26/1.50  --prep_def_merge                        true
% 7.26/1.50  --prep_def_merge_prop_impl              false
% 7.26/1.50  --prep_def_merge_mbd                    true
% 7.26/1.50  --prep_def_merge_tr_red                 false
% 7.26/1.50  --prep_def_merge_tr_cl                  false
% 7.26/1.50  --smt_preprocessing                     true
% 7.26/1.50  --smt_ac_axioms                         fast
% 7.26/1.50  --preprocessed_out                      false
% 7.26/1.50  --preprocessed_stats                    false
% 7.26/1.50  
% 7.26/1.50  ------ Abstraction refinement Options
% 7.26/1.50  
% 7.26/1.50  --abstr_ref                             []
% 7.26/1.50  --abstr_ref_prep                        false
% 7.26/1.50  --abstr_ref_until_sat                   false
% 7.26/1.50  --abstr_ref_sig_restrict                funpre
% 7.26/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.26/1.50  --abstr_ref_under                       []
% 7.26/1.50  
% 7.26/1.50  ------ SAT Options
% 7.26/1.50  
% 7.26/1.50  --sat_mode                              false
% 7.26/1.50  --sat_fm_restart_options                ""
% 7.26/1.50  --sat_gr_def                            false
% 7.26/1.50  --sat_epr_types                         true
% 7.26/1.50  --sat_non_cyclic_types                  false
% 7.26/1.50  --sat_finite_models                     false
% 7.26/1.50  --sat_fm_lemmas                         false
% 7.26/1.50  --sat_fm_prep                           false
% 7.26/1.50  --sat_fm_uc_incr                        true
% 7.26/1.50  --sat_out_model                         small
% 7.26/1.50  --sat_out_clauses                       false
% 7.26/1.50  
% 7.26/1.50  ------ QBF Options
% 7.26/1.50  
% 7.26/1.50  --qbf_mode                              false
% 7.26/1.50  --qbf_elim_univ                         false
% 7.26/1.50  --qbf_dom_inst                          none
% 7.26/1.50  --qbf_dom_pre_inst                      false
% 7.26/1.50  --qbf_sk_in                             false
% 7.26/1.50  --qbf_pred_elim                         true
% 7.26/1.50  --qbf_split                             512
% 7.26/1.50  
% 7.26/1.50  ------ BMC1 Options
% 7.26/1.50  
% 7.26/1.50  --bmc1_incremental                      false
% 7.26/1.50  --bmc1_axioms                           reachable_all
% 7.26/1.50  --bmc1_min_bound                        0
% 7.26/1.50  --bmc1_max_bound                        -1
% 7.26/1.50  --bmc1_max_bound_default                -1
% 7.26/1.50  --bmc1_symbol_reachability              true
% 7.26/1.50  --bmc1_property_lemmas                  false
% 7.26/1.50  --bmc1_k_induction                      false
% 7.26/1.50  --bmc1_non_equiv_states                 false
% 7.26/1.50  --bmc1_deadlock                         false
% 7.26/1.50  --bmc1_ucm                              false
% 7.26/1.50  --bmc1_add_unsat_core                   none
% 7.26/1.50  --bmc1_unsat_core_children              false
% 7.26/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.26/1.50  --bmc1_out_stat                         full
% 7.26/1.50  --bmc1_ground_init                      false
% 7.26/1.50  --bmc1_pre_inst_next_state              false
% 7.26/1.50  --bmc1_pre_inst_state                   false
% 7.26/1.50  --bmc1_pre_inst_reach_state             false
% 7.26/1.50  --bmc1_out_unsat_core                   false
% 7.26/1.50  --bmc1_aig_witness_out                  false
% 7.26/1.50  --bmc1_verbose                          false
% 7.26/1.50  --bmc1_dump_clauses_tptp                false
% 7.26/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.26/1.50  --bmc1_dump_file                        -
% 7.26/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.26/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.26/1.50  --bmc1_ucm_extend_mode                  1
% 7.26/1.50  --bmc1_ucm_init_mode                    2
% 7.26/1.50  --bmc1_ucm_cone_mode                    none
% 7.26/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.26/1.50  --bmc1_ucm_relax_model                  4
% 7.26/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.26/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.26/1.50  --bmc1_ucm_layered_model                none
% 7.26/1.50  --bmc1_ucm_max_lemma_size               10
% 7.26/1.50  
% 7.26/1.50  ------ AIG Options
% 7.26/1.50  
% 7.26/1.50  --aig_mode                              false
% 7.26/1.50  
% 7.26/1.50  ------ Instantiation Options
% 7.26/1.50  
% 7.26/1.50  --instantiation_flag                    true
% 7.26/1.50  --inst_sos_flag                         false
% 7.26/1.50  --inst_sos_phase                        true
% 7.26/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.26/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.26/1.50  --inst_lit_sel_side                     num_symb
% 7.26/1.50  --inst_solver_per_active                1400
% 7.26/1.50  --inst_solver_calls_frac                1.
% 7.26/1.50  --inst_passive_queue_type               priority_queues
% 7.26/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.26/1.50  --inst_passive_queues_freq              [25;2]
% 7.26/1.50  --inst_dismatching                      true
% 7.26/1.50  --inst_eager_unprocessed_to_passive     true
% 7.26/1.50  --inst_prop_sim_given                   true
% 7.26/1.50  --inst_prop_sim_new                     false
% 7.26/1.50  --inst_subs_new                         false
% 7.26/1.50  --inst_eq_res_simp                      false
% 7.26/1.50  --inst_subs_given                       false
% 7.26/1.50  --inst_orphan_elimination               true
% 7.26/1.50  --inst_learning_loop_flag               true
% 7.26/1.50  --inst_learning_start                   3000
% 7.26/1.50  --inst_learning_factor                  2
% 7.26/1.50  --inst_start_prop_sim_after_learn       3
% 7.26/1.50  --inst_sel_renew                        solver
% 7.26/1.50  --inst_lit_activity_flag                true
% 7.26/1.50  --inst_restr_to_given                   false
% 7.26/1.50  --inst_activity_threshold               500
% 7.26/1.50  --inst_out_proof                        true
% 7.26/1.50  
% 7.26/1.50  ------ Resolution Options
% 7.26/1.50  
% 7.26/1.50  --resolution_flag                       true
% 7.26/1.50  --res_lit_sel                           adaptive
% 7.26/1.50  --res_lit_sel_side                      none
% 7.26/1.50  --res_ordering                          kbo
% 7.26/1.50  --res_to_prop_solver                    active
% 7.26/1.50  --res_prop_simpl_new                    false
% 7.26/1.50  --res_prop_simpl_given                  true
% 7.26/1.50  --res_passive_queue_type                priority_queues
% 7.26/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.26/1.50  --res_passive_queues_freq               [15;5]
% 7.26/1.50  --res_forward_subs                      full
% 7.26/1.50  --res_backward_subs                     full
% 7.26/1.50  --res_forward_subs_resolution           true
% 7.26/1.50  --res_backward_subs_resolution          true
% 7.26/1.50  --res_orphan_elimination                true
% 7.26/1.50  --res_time_limit                        2.
% 7.26/1.50  --res_out_proof                         true
% 7.26/1.50  
% 7.26/1.50  ------ Superposition Options
% 7.26/1.50  
% 7.26/1.50  --superposition_flag                    true
% 7.26/1.50  --sup_passive_queue_type                priority_queues
% 7.26/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.26/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.26/1.50  --demod_completeness_check              fast
% 7.26/1.50  --demod_use_ground                      true
% 7.26/1.50  --sup_to_prop_solver                    passive
% 7.26/1.50  --sup_prop_simpl_new                    true
% 7.26/1.50  --sup_prop_simpl_given                  true
% 7.26/1.50  --sup_fun_splitting                     false
% 7.26/1.50  --sup_smt_interval                      50000
% 7.26/1.50  
% 7.26/1.50  ------ Superposition Simplification Setup
% 7.26/1.50  
% 7.26/1.50  --sup_indices_passive                   []
% 7.26/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.26/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.26/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.26/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.26/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.26/1.50  --sup_full_bw                           [BwDemod]
% 7.26/1.50  --sup_immed_triv                        [TrivRules]
% 7.26/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.26/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.26/1.50  --sup_immed_bw_main                     []
% 7.26/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.26/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.26/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.26/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.26/1.50  
% 7.26/1.50  ------ Combination Options
% 7.26/1.50  
% 7.26/1.50  --comb_res_mult                         3
% 7.26/1.50  --comb_sup_mult                         2
% 7.26/1.50  --comb_inst_mult                        10
% 7.26/1.50  
% 7.26/1.50  ------ Debug Options
% 7.26/1.50  
% 7.26/1.50  --dbg_backtrace                         false
% 7.26/1.50  --dbg_dump_prop_clauses                 false
% 7.26/1.50  --dbg_dump_prop_clauses_file            -
% 7.26/1.50  --dbg_out_stat                          false
% 7.26/1.50  ------ Parsing...
% 7.26/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.26/1.50  
% 7.26/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.26/1.50  
% 7.26/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.26/1.50  
% 7.26/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.26/1.50  ------ Proving...
% 7.26/1.50  ------ Problem Properties 
% 7.26/1.50  
% 7.26/1.50  
% 7.26/1.50  clauses                                 19
% 7.26/1.50  conjectures                             3
% 7.26/1.50  EPR                                     3
% 7.26/1.50  Horn                                    18
% 7.26/1.50  unary                                   11
% 7.26/1.50  binary                                  5
% 7.26/1.50  lits                                    32
% 7.26/1.50  lits eq                                 11
% 7.26/1.50  fd_pure                                 0
% 7.26/1.50  fd_pseudo                               0
% 7.26/1.50  fd_cond                                 0
% 7.26/1.50  fd_pseudo_cond                          1
% 7.26/1.50  AC symbols                              0
% 7.26/1.50  
% 7.26/1.50  ------ Schedule dynamic 5 is on 
% 7.26/1.50  
% 7.26/1.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.26/1.50  
% 7.26/1.50  
% 7.26/1.50  ------ 
% 7.26/1.50  Current options:
% 7.26/1.50  ------ 
% 7.26/1.50  
% 7.26/1.50  ------ Input Options
% 7.26/1.50  
% 7.26/1.50  --out_options                           all
% 7.26/1.50  --tptp_safe_out                         true
% 7.26/1.50  --problem_path                          ""
% 7.26/1.50  --include_path                          ""
% 7.26/1.50  --clausifier                            res/vclausify_rel
% 7.26/1.50  --clausifier_options                    --mode clausify
% 7.26/1.50  --stdin                                 false
% 7.26/1.50  --stats_out                             all
% 7.26/1.50  
% 7.26/1.50  ------ General Options
% 7.26/1.50  
% 7.26/1.50  --fof                                   false
% 7.26/1.50  --time_out_real                         305.
% 7.26/1.50  --time_out_virtual                      -1.
% 7.26/1.50  --symbol_type_check                     false
% 7.26/1.50  --clausify_out                          false
% 7.26/1.50  --sig_cnt_out                           false
% 7.26/1.50  --trig_cnt_out                          false
% 7.26/1.50  --trig_cnt_out_tolerance                1.
% 7.26/1.50  --trig_cnt_out_sk_spl                   false
% 7.26/1.50  --abstr_cl_out                          false
% 7.26/1.50  
% 7.26/1.50  ------ Global Options
% 7.26/1.50  
% 7.26/1.50  --schedule                              default
% 7.26/1.50  --add_important_lit                     false
% 7.26/1.50  --prop_solver_per_cl                    1000
% 7.26/1.50  --min_unsat_core                        false
% 7.26/1.50  --soft_assumptions                      false
% 7.26/1.50  --soft_lemma_size                       3
% 7.26/1.50  --prop_impl_unit_size                   0
% 7.26/1.50  --prop_impl_unit                        []
% 7.26/1.50  --share_sel_clauses                     true
% 7.26/1.50  --reset_solvers                         false
% 7.26/1.50  --bc_imp_inh                            [conj_cone]
% 7.26/1.50  --conj_cone_tolerance                   3.
% 7.26/1.50  --extra_neg_conj                        none
% 7.26/1.50  --large_theory_mode                     true
% 7.26/1.50  --prolific_symb_bound                   200
% 7.26/1.50  --lt_threshold                          2000
% 7.26/1.50  --clause_weak_htbl                      true
% 7.26/1.50  --gc_record_bc_elim                     false
% 7.26/1.50  
% 7.26/1.50  ------ Preprocessing Options
% 7.26/1.50  
% 7.26/1.50  --preprocessing_flag                    true
% 7.26/1.50  --time_out_prep_mult                    0.1
% 7.26/1.50  --splitting_mode                        input
% 7.26/1.50  --splitting_grd                         true
% 7.26/1.50  --splitting_cvd                         false
% 7.26/1.50  --splitting_cvd_svl                     false
% 7.26/1.50  --splitting_nvd                         32
% 7.26/1.50  --sub_typing                            true
% 7.26/1.50  --prep_gs_sim                           true
% 7.26/1.50  --prep_unflatten                        true
% 7.26/1.50  --prep_res_sim                          true
% 7.26/1.50  --prep_upred                            true
% 7.26/1.50  --prep_sem_filter                       exhaustive
% 7.26/1.50  --prep_sem_filter_out                   false
% 7.26/1.50  --pred_elim                             true
% 7.26/1.50  --res_sim_input                         true
% 7.26/1.50  --eq_ax_congr_red                       true
% 7.26/1.50  --pure_diseq_elim                       true
% 7.26/1.50  --brand_transform                       false
% 7.26/1.50  --non_eq_to_eq                          false
% 7.26/1.50  --prep_def_merge                        true
% 7.26/1.50  --prep_def_merge_prop_impl              false
% 7.26/1.50  --prep_def_merge_mbd                    true
% 7.26/1.50  --prep_def_merge_tr_red                 false
% 7.26/1.50  --prep_def_merge_tr_cl                  false
% 7.26/1.50  --smt_preprocessing                     true
% 7.26/1.50  --smt_ac_axioms                         fast
% 7.26/1.50  --preprocessed_out                      false
% 7.26/1.50  --preprocessed_stats                    false
% 7.26/1.50  
% 7.26/1.50  ------ Abstraction refinement Options
% 7.26/1.50  
% 7.26/1.50  --abstr_ref                             []
% 7.26/1.50  --abstr_ref_prep                        false
% 7.26/1.50  --abstr_ref_until_sat                   false
% 7.26/1.50  --abstr_ref_sig_restrict                funpre
% 7.26/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.26/1.50  --abstr_ref_under                       []
% 7.26/1.50  
% 7.26/1.50  ------ SAT Options
% 7.26/1.50  
% 7.26/1.50  --sat_mode                              false
% 7.26/1.50  --sat_fm_restart_options                ""
% 7.26/1.50  --sat_gr_def                            false
% 7.26/1.50  --sat_epr_types                         true
% 7.26/1.50  --sat_non_cyclic_types                  false
% 7.26/1.50  --sat_finite_models                     false
% 7.26/1.50  --sat_fm_lemmas                         false
% 7.26/1.50  --sat_fm_prep                           false
% 7.26/1.50  --sat_fm_uc_incr                        true
% 7.26/1.50  --sat_out_model                         small
% 7.26/1.50  --sat_out_clauses                       false
% 7.26/1.50  
% 7.26/1.50  ------ QBF Options
% 7.26/1.50  
% 7.26/1.50  --qbf_mode                              false
% 7.26/1.50  --qbf_elim_univ                         false
% 7.26/1.50  --qbf_dom_inst                          none
% 7.26/1.50  --qbf_dom_pre_inst                      false
% 7.26/1.50  --qbf_sk_in                             false
% 7.26/1.50  --qbf_pred_elim                         true
% 7.26/1.50  --qbf_split                             512
% 7.26/1.50  
% 7.26/1.50  ------ BMC1 Options
% 7.26/1.50  
% 7.26/1.50  --bmc1_incremental                      false
% 7.26/1.50  --bmc1_axioms                           reachable_all
% 7.26/1.50  --bmc1_min_bound                        0
% 7.26/1.50  --bmc1_max_bound                        -1
% 7.26/1.50  --bmc1_max_bound_default                -1
% 7.26/1.50  --bmc1_symbol_reachability              true
% 7.26/1.50  --bmc1_property_lemmas                  false
% 7.26/1.50  --bmc1_k_induction                      false
% 7.26/1.50  --bmc1_non_equiv_states                 false
% 7.26/1.50  --bmc1_deadlock                         false
% 7.26/1.50  --bmc1_ucm                              false
% 7.26/1.50  --bmc1_add_unsat_core                   none
% 7.26/1.50  --bmc1_unsat_core_children              false
% 7.26/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.26/1.50  --bmc1_out_stat                         full
% 7.26/1.50  --bmc1_ground_init                      false
% 7.26/1.50  --bmc1_pre_inst_next_state              false
% 7.26/1.50  --bmc1_pre_inst_state                   false
% 7.26/1.50  --bmc1_pre_inst_reach_state             false
% 7.26/1.50  --bmc1_out_unsat_core                   false
% 7.26/1.50  --bmc1_aig_witness_out                  false
% 7.26/1.50  --bmc1_verbose                          false
% 7.26/1.50  --bmc1_dump_clauses_tptp                false
% 7.26/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.26/1.50  --bmc1_dump_file                        -
% 7.26/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.26/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.26/1.50  --bmc1_ucm_extend_mode                  1
% 7.26/1.50  --bmc1_ucm_init_mode                    2
% 7.26/1.50  --bmc1_ucm_cone_mode                    none
% 7.26/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.26/1.50  --bmc1_ucm_relax_model                  4
% 7.26/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.26/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.26/1.50  --bmc1_ucm_layered_model                none
% 7.26/1.50  --bmc1_ucm_max_lemma_size               10
% 7.26/1.50  
% 7.26/1.50  ------ AIG Options
% 7.26/1.50  
% 7.26/1.50  --aig_mode                              false
% 7.26/1.50  
% 7.26/1.50  ------ Instantiation Options
% 7.26/1.50  
% 7.26/1.50  --instantiation_flag                    true
% 7.26/1.50  --inst_sos_flag                         false
% 7.26/1.50  --inst_sos_phase                        true
% 7.26/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.26/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.26/1.50  --inst_lit_sel_side                     none
% 7.26/1.50  --inst_solver_per_active                1400
% 7.26/1.50  --inst_solver_calls_frac                1.
% 7.26/1.50  --inst_passive_queue_type               priority_queues
% 7.26/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.26/1.50  --inst_passive_queues_freq              [25;2]
% 7.26/1.50  --inst_dismatching                      true
% 7.26/1.50  --inst_eager_unprocessed_to_passive     true
% 7.26/1.50  --inst_prop_sim_given                   true
% 7.26/1.50  --inst_prop_sim_new                     false
% 7.26/1.50  --inst_subs_new                         false
% 7.26/1.50  --inst_eq_res_simp                      false
% 7.26/1.50  --inst_subs_given                       false
% 7.26/1.50  --inst_orphan_elimination               true
% 7.26/1.50  --inst_learning_loop_flag               true
% 7.26/1.50  --inst_learning_start                   3000
% 7.26/1.50  --inst_learning_factor                  2
% 7.26/1.50  --inst_start_prop_sim_after_learn       3
% 7.26/1.50  --inst_sel_renew                        solver
% 7.26/1.50  --inst_lit_activity_flag                true
% 7.26/1.50  --inst_restr_to_given                   false
% 7.26/1.50  --inst_activity_threshold               500
% 7.26/1.50  --inst_out_proof                        true
% 7.26/1.50  
% 7.26/1.50  ------ Resolution Options
% 7.26/1.50  
% 7.26/1.50  --resolution_flag                       false
% 7.26/1.50  --res_lit_sel                           adaptive
% 7.26/1.50  --res_lit_sel_side                      none
% 7.26/1.50  --res_ordering                          kbo
% 7.26/1.50  --res_to_prop_solver                    active
% 7.26/1.50  --res_prop_simpl_new                    false
% 7.26/1.50  --res_prop_simpl_given                  true
% 7.26/1.50  --res_passive_queue_type                priority_queues
% 7.26/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.26/1.50  --res_passive_queues_freq               [15;5]
% 7.26/1.50  --res_forward_subs                      full
% 7.26/1.50  --res_backward_subs                     full
% 7.26/1.50  --res_forward_subs_resolution           true
% 7.26/1.50  --res_backward_subs_resolution          true
% 7.26/1.50  --res_orphan_elimination                true
% 7.26/1.50  --res_time_limit                        2.
% 7.26/1.50  --res_out_proof                         true
% 7.26/1.50  
% 7.26/1.50  ------ Superposition Options
% 7.26/1.50  
% 7.26/1.50  --superposition_flag                    true
% 7.26/1.50  --sup_passive_queue_type                priority_queues
% 7.26/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.26/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.26/1.50  --demod_completeness_check              fast
% 7.26/1.50  --demod_use_ground                      true
% 7.26/1.50  --sup_to_prop_solver                    passive
% 7.26/1.50  --sup_prop_simpl_new                    true
% 7.26/1.50  --sup_prop_simpl_given                  true
% 7.26/1.50  --sup_fun_splitting                     false
% 7.26/1.50  --sup_smt_interval                      50000
% 7.26/1.50  
% 7.26/1.50  ------ Superposition Simplification Setup
% 7.26/1.50  
% 7.26/1.50  --sup_indices_passive                   []
% 7.26/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.26/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.26/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.26/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.26/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.26/1.50  --sup_full_bw                           [BwDemod]
% 7.26/1.50  --sup_immed_triv                        [TrivRules]
% 7.26/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.26/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.26/1.50  --sup_immed_bw_main                     []
% 7.26/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.26/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.26/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.26/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.26/1.50  
% 7.26/1.50  ------ Combination Options
% 7.26/1.50  
% 7.26/1.50  --comb_res_mult                         3
% 7.26/1.50  --comb_sup_mult                         2
% 7.26/1.50  --comb_inst_mult                        10
% 7.26/1.50  
% 7.26/1.50  ------ Debug Options
% 7.26/1.50  
% 7.26/1.50  --dbg_backtrace                         false
% 7.26/1.50  --dbg_dump_prop_clauses                 false
% 7.26/1.50  --dbg_dump_prop_clauses_file            -
% 7.26/1.50  --dbg_out_stat                          false
% 7.26/1.50  
% 7.26/1.50  
% 7.26/1.50  
% 7.26/1.50  
% 7.26/1.50  ------ Proving...
% 7.26/1.50  
% 7.26/1.50  
% 7.26/1.50  % SZS status Theorem for theBenchmark.p
% 7.26/1.50  
% 7.26/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.26/1.50  
% 7.26/1.50  fof(f21,conjecture,(
% 7.26/1.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 7.26/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.50  
% 7.26/1.50  fof(f22,negated_conjecture,(
% 7.26/1.50    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 7.26/1.50    inference(negated_conjecture,[],[f21])).
% 7.26/1.50  
% 7.26/1.50  fof(f27,plain,(
% 7.26/1.50    ? [X0,X1] : ((r1_tarski(k3_subset_1(X0,X1),X1) <~> k2_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.26/1.50    inference(ennf_transformation,[],[f22])).
% 7.26/1.50  
% 7.26/1.50  fof(f31,plain,(
% 7.26/1.50    ? [X0,X1] : (((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.26/1.50    inference(nnf_transformation,[],[f27])).
% 7.26/1.50  
% 7.26/1.50  fof(f32,plain,(
% 7.26/1.50    ? [X0,X1] : ((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.26/1.50    inference(flattening,[],[f31])).
% 7.26/1.50  
% 7.26/1.50  fof(f33,plain,(
% 7.26/1.50    ? [X0,X1] : ((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => ((k2_subset_1(sK0) != sK1 | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)) & (k2_subset_1(sK0) = sK1 | r1_tarski(k3_subset_1(sK0,sK1),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 7.26/1.50    introduced(choice_axiom,[])).
% 7.26/1.50  
% 7.26/1.50  fof(f34,plain,(
% 7.26/1.50    (k2_subset_1(sK0) != sK1 | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)) & (k2_subset_1(sK0) = sK1 | r1_tarski(k3_subset_1(sK0,sK1),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 7.26/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f33])).
% 7.26/1.50  
% 7.26/1.50  fof(f58,plain,(
% 7.26/1.50    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 7.26/1.50    inference(cnf_transformation,[],[f34])).
% 7.26/1.50  
% 7.26/1.50  fof(f20,axiom,(
% 7.26/1.50    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 7.26/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.50  
% 7.26/1.50  fof(f57,plain,(
% 7.26/1.50    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 7.26/1.50    inference(cnf_transformation,[],[f20])).
% 7.26/1.50  
% 7.26/1.50  fof(f17,axiom,(
% 7.26/1.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 7.26/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.50  
% 7.26/1.50  fof(f25,plain,(
% 7.26/1.50    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.26/1.50    inference(ennf_transformation,[],[f17])).
% 7.26/1.50  
% 7.26/1.50  fof(f53,plain,(
% 7.26/1.50    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.26/1.50    inference(cnf_transformation,[],[f25])).
% 7.26/1.50  
% 7.26/1.50  fof(f14,axiom,(
% 7.26/1.50    ! [X0] : k2_subset_1(X0) = X0),
% 7.26/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.50  
% 7.26/1.50  fof(f50,plain,(
% 7.26/1.50    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 7.26/1.50    inference(cnf_transformation,[],[f14])).
% 7.26/1.50  
% 7.26/1.50  fof(f18,axiom,(
% 7.26/1.50    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 7.26/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.50  
% 7.26/1.50  fof(f54,plain,(
% 7.26/1.50    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 7.26/1.50    inference(cnf_transformation,[],[f18])).
% 7.26/1.50  
% 7.26/1.50  fof(f13,axiom,(
% 7.26/1.50    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 7.26/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.50  
% 7.26/1.50  fof(f49,plain,(
% 7.26/1.50    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 7.26/1.50    inference(cnf_transformation,[],[f13])).
% 7.26/1.50  
% 7.26/1.50  fof(f63,plain,(
% 7.26/1.50    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 7.26/1.50    inference(definition_unfolding,[],[f54,f49])).
% 7.26/1.50  
% 7.26/1.50  fof(f68,plain,(
% 7.26/1.50    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 7.26/1.50    inference(definition_unfolding,[],[f50,f63])).
% 7.26/1.50  
% 7.26/1.50  fof(f19,axiom,(
% 7.26/1.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 7.26/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.50  
% 7.26/1.50  fof(f26,plain,(
% 7.26/1.50    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.26/1.50    inference(ennf_transformation,[],[f19])).
% 7.26/1.50  
% 7.26/1.50  fof(f30,plain,(
% 7.26/1.50    ! [X0,X1] : (! [X2] : (((r1_tarski(X1,X2) | ~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.26/1.50    inference(nnf_transformation,[],[f26])).
% 7.26/1.50  
% 7.26/1.50  fof(f56,plain,(
% 7.26/1.50    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.26/1.50    inference(cnf_transformation,[],[f30])).
% 7.26/1.50  
% 7.26/1.50  fof(f6,axiom,(
% 7.26/1.50    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 7.26/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.50  
% 7.26/1.50  fof(f42,plain,(
% 7.26/1.50    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 7.26/1.50    inference(cnf_transformation,[],[f6])).
% 7.26/1.50  
% 7.26/1.50  fof(f16,axiom,(
% 7.26/1.50    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 7.26/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.50  
% 7.26/1.50  fof(f52,plain,(
% 7.26/1.50    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 7.26/1.50    inference(cnf_transformation,[],[f16])).
% 7.26/1.50  
% 7.26/1.50  fof(f70,plain,(
% 7.26/1.50    ( ! [X0] : (m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0))) )),
% 7.26/1.50    inference(definition_unfolding,[],[f52,f63])).
% 7.26/1.50  
% 7.26/1.50  fof(f5,axiom,(
% 7.26/1.50    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 7.26/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.50  
% 7.26/1.50  fof(f23,plain,(
% 7.26/1.50    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 7.26/1.50    inference(ennf_transformation,[],[f5])).
% 7.26/1.50  
% 7.26/1.50  fof(f41,plain,(
% 7.26/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 7.26/1.50    inference(cnf_transformation,[],[f23])).
% 7.26/1.50  
% 7.26/1.50  fof(f1,axiom,(
% 7.26/1.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.26/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.50  
% 7.26/1.50  fof(f35,plain,(
% 7.26/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.26/1.50    inference(cnf_transformation,[],[f1])).
% 7.26/1.50  
% 7.26/1.50  fof(f15,axiom,(
% 7.26/1.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 7.26/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.50  
% 7.26/1.50  fof(f24,plain,(
% 7.26/1.50    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.26/1.50    inference(ennf_transformation,[],[f15])).
% 7.26/1.50  
% 7.26/1.50  fof(f51,plain,(
% 7.26/1.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.26/1.51    inference(cnf_transformation,[],[f24])).
% 7.26/1.51  
% 7.26/1.51  fof(f3,axiom,(
% 7.26/1.51    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.26/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.51  
% 7.26/1.51  fof(f39,plain,(
% 7.26/1.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.26/1.51    inference(cnf_transformation,[],[f3])).
% 7.26/1.51  
% 7.26/1.51  fof(f69,plain,(
% 7.26/1.51    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.26/1.51    inference(definition_unfolding,[],[f51,f39])).
% 7.26/1.51  
% 7.26/1.51  fof(f7,axiom,(
% 7.26/1.51    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 7.26/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.51  
% 7.26/1.51  fof(f43,plain,(
% 7.26/1.51    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 7.26/1.51    inference(cnf_transformation,[],[f7])).
% 7.26/1.51  
% 7.26/1.51  fof(f65,plain,(
% 7.26/1.51    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 7.26/1.51    inference(definition_unfolding,[],[f43,f39])).
% 7.26/1.51  
% 7.26/1.51  fof(f4,axiom,(
% 7.26/1.51    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 7.26/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.51  
% 7.26/1.51  fof(f40,plain,(
% 7.26/1.51    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 7.26/1.51    inference(cnf_transformation,[],[f4])).
% 7.26/1.51  
% 7.26/1.51  fof(f8,axiom,(
% 7.26/1.51    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 7.26/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.51  
% 7.26/1.51  fof(f44,plain,(
% 7.26/1.51    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 7.26/1.51    inference(cnf_transformation,[],[f8])).
% 7.26/1.51  
% 7.26/1.51  fof(f61,plain,(
% 7.26/1.51    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 7.26/1.51    inference(definition_unfolding,[],[f44,f39])).
% 7.26/1.51  
% 7.26/1.51  fof(f64,plain,(
% 7.26/1.51    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X0))) = X0) )),
% 7.26/1.51    inference(definition_unfolding,[],[f40,f61])).
% 7.26/1.51  
% 7.26/1.51  fof(f2,axiom,(
% 7.26/1.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.26/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.51  
% 7.26/1.51  fof(f28,plain,(
% 7.26/1.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.26/1.51    inference(nnf_transformation,[],[f2])).
% 7.26/1.51  
% 7.26/1.51  fof(f29,plain,(
% 7.26/1.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.26/1.51    inference(flattening,[],[f28])).
% 7.26/1.51  
% 7.26/1.51  fof(f36,plain,(
% 7.26/1.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.26/1.51    inference(cnf_transformation,[],[f29])).
% 7.26/1.51  
% 7.26/1.51  fof(f74,plain,(
% 7.26/1.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.26/1.51    inference(equality_resolution,[],[f36])).
% 7.26/1.51  
% 7.26/1.51  fof(f59,plain,(
% 7.26/1.51    k2_subset_1(sK0) = sK1 | r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 7.26/1.51    inference(cnf_transformation,[],[f34])).
% 7.26/1.51  
% 7.26/1.51  fof(f72,plain,(
% 7.26/1.51    k3_subset_1(sK0,k1_xboole_0) = sK1 | r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 7.26/1.51    inference(definition_unfolding,[],[f59,f63])).
% 7.26/1.51  
% 7.26/1.51  fof(f9,axiom,(
% 7.26/1.51    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 7.26/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.51  
% 7.26/1.51  fof(f45,plain,(
% 7.26/1.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 7.26/1.51    inference(cnf_transformation,[],[f9])).
% 7.26/1.51  
% 7.26/1.51  fof(f10,axiom,(
% 7.26/1.51    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.26/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.51  
% 7.26/1.51  fof(f46,plain,(
% 7.26/1.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.26/1.51    inference(cnf_transformation,[],[f10])).
% 7.26/1.51  
% 7.26/1.51  fof(f11,axiom,(
% 7.26/1.51    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.26/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.51  
% 7.26/1.51  fof(f47,plain,(
% 7.26/1.51    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.26/1.51    inference(cnf_transformation,[],[f11])).
% 7.26/1.51  
% 7.26/1.51  fof(f62,plain,(
% 7.26/1.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 7.26/1.51    inference(definition_unfolding,[],[f46,f47])).
% 7.26/1.51  
% 7.26/1.51  fof(f66,plain,(
% 7.26/1.51    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 7.26/1.51    inference(definition_unfolding,[],[f45,f62,f62])).
% 7.26/1.51  
% 7.26/1.51  fof(f12,axiom,(
% 7.26/1.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 7.26/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.51  
% 7.26/1.51  fof(f48,plain,(
% 7.26/1.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 7.26/1.51    inference(cnf_transformation,[],[f12])).
% 7.26/1.51  
% 7.26/1.51  fof(f67,plain,(
% 7.26/1.51    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 7.26/1.51    inference(definition_unfolding,[],[f48,f61,f62])).
% 7.26/1.51  
% 7.26/1.51  fof(f55,plain,(
% 7.26/1.51    ( ! [X2,X0,X1] : (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.26/1.51    inference(cnf_transformation,[],[f30])).
% 7.26/1.51  
% 7.26/1.51  fof(f60,plain,(
% 7.26/1.51    k2_subset_1(sK0) != sK1 | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 7.26/1.51    inference(cnf_transformation,[],[f34])).
% 7.26/1.51  
% 7.26/1.51  fof(f71,plain,(
% 7.26/1.51    k3_subset_1(sK0,k1_xboole_0) != sK1 | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 7.26/1.51    inference(definition_unfolding,[],[f60,f63])).
% 7.26/1.51  
% 7.26/1.51  fof(f38,plain,(
% 7.26/1.51    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.26/1.51    inference(cnf_transformation,[],[f29])).
% 7.26/1.51  
% 7.26/1.51  cnf(c_347,plain,
% 7.26/1.51      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.26/1.51      theory(equality) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_2524,plain,
% 7.26/1.51      ( ~ r1_tarski(X0,X1)
% 7.26/1.51      | r1_tarski(k3_subset_1(sK0,sK1),sK1)
% 7.26/1.51      | k3_subset_1(sK0,sK1) != X0
% 7.26/1.51      | sK1 != X1 ),
% 7.26/1.51      inference(instantiation,[status(thm)],[c_347]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_33361,plain,
% 7.26/1.51      ( r1_tarski(k3_subset_1(sK0,sK1),sK1)
% 7.26/1.51      | ~ r1_tarski(k1_xboole_0,X0)
% 7.26/1.51      | k3_subset_1(sK0,sK1) != k1_xboole_0
% 7.26/1.51      | sK1 != X0 ),
% 7.26/1.51      inference(instantiation,[status(thm)],[c_2524]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_33365,plain,
% 7.26/1.51      ( r1_tarski(k3_subset_1(sK0,sK1),sK1)
% 7.26/1.51      | ~ r1_tarski(k1_xboole_0,sK1)
% 7.26/1.51      | k3_subset_1(sK0,sK1) != k1_xboole_0
% 7.26/1.51      | sK1 != sK1 ),
% 7.26/1.51      inference(instantiation,[status(thm)],[c_33361]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_19,negated_conjecture,
% 7.26/1.51      ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
% 7.26/1.51      inference(cnf_transformation,[],[f58]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_690,plain,
% 7.26/1.51      ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) = iProver_top ),
% 7.26/1.51      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_16,plain,
% 7.26/1.51      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 7.26/1.51      inference(cnf_transformation,[],[f57]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_693,plain,
% 7.26/1.51      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 7.26/1.51      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_13,plain,
% 7.26/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.26/1.51      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 7.26/1.51      inference(cnf_transformation,[],[f53]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_696,plain,
% 7.26/1.51      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 7.26/1.51      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 7.26/1.51      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_3226,plain,
% 7.26/1.51      ( k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) = k1_xboole_0 ),
% 7.26/1.51      inference(superposition,[status(thm)],[c_693,c_696]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_10,plain,
% 7.26/1.51      ( k3_subset_1(X0,k1_xboole_0) = X0 ),
% 7.26/1.51      inference(cnf_transformation,[],[f68]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_3234,plain,
% 7.26/1.51      ( k3_subset_1(X0,X0) = k1_xboole_0 ),
% 7.26/1.51      inference(light_normalisation,[status(thm)],[c_3226,c_10]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_14,plain,
% 7.26/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.26/1.51      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 7.26/1.51      | r1_tarski(X0,X2)
% 7.26/1.51      | ~ r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X0)) ),
% 7.26/1.51      inference(cnf_transformation,[],[f56]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_695,plain,
% 7.26/1.51      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.26/1.51      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 7.26/1.51      | r1_tarski(X0,X2) = iProver_top
% 7.26/1.51      | r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X0)) != iProver_top ),
% 7.26/1.51      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_3793,plain,
% 7.26/1.51      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.26/1.51      | m1_subset_1(X1,k1_zfmisc_1(X1)) != iProver_top
% 7.26/1.51      | r1_tarski(X0,X1) = iProver_top
% 7.26/1.51      | r1_tarski(k1_xboole_0,k3_subset_1(X1,X0)) != iProver_top ),
% 7.26/1.51      inference(superposition,[status(thm)],[c_3234,c_695]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_6,plain,
% 7.26/1.51      ( r1_tarski(k1_xboole_0,X0) ),
% 7.26/1.51      inference(cnf_transformation,[],[f42]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_700,plain,
% 7.26/1.51      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 7.26/1.51      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_12,plain,
% 7.26/1.51      ( m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) ),
% 7.26/1.51      inference(cnf_transformation,[],[f70]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_697,plain,
% 7.26/1.51      ( m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) = iProver_top ),
% 7.26/1.51      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_716,plain,
% 7.26/1.51      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 7.26/1.51      inference(light_normalisation,[status(thm)],[c_697,c_10]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_18677,plain,
% 7.26/1.51      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.26/1.51      | r1_tarski(X0,X1) = iProver_top ),
% 7.26/1.51      inference(forward_subsumption_resolution,
% 7.26/1.51                [status(thm)],
% 7.26/1.51                [c_3793,c_700,c_716]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_18680,plain,
% 7.26/1.51      ( r1_tarski(sK1,sK0) = iProver_top ),
% 7.26/1.51      inference(superposition,[status(thm)],[c_690,c_18677]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_5,plain,
% 7.26/1.51      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 7.26/1.51      inference(cnf_transformation,[],[f41]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_701,plain,
% 7.26/1.51      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 7.26/1.51      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_19198,plain,
% 7.26/1.51      ( k3_xboole_0(sK1,sK0) = sK1 ),
% 7.26/1.51      inference(superposition,[status(thm)],[c_18680,c_701]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_0,plain,
% 7.26/1.51      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 7.26/1.51      inference(cnf_transformation,[],[f35]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_11,plain,
% 7.26/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.26/1.51      | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
% 7.26/1.51      inference(cnf_transformation,[],[f69]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_698,plain,
% 7.26/1.51      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
% 7.26/1.51      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 7.26/1.51      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_4030,plain,
% 7.26/1.51      ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) = k3_subset_1(sK0,sK1) ),
% 7.26/1.51      inference(superposition,[status(thm)],[c_690,c_698]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_7,plain,
% 7.26/1.51      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
% 7.26/1.51      inference(cnf_transformation,[],[f65]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_699,plain,
% 7.26/1.51      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
% 7.26/1.51      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_1568,plain,
% 7.26/1.51      ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 7.26/1.51      inference(superposition,[status(thm)],[c_699,c_701]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_12329,plain,
% 7.26/1.51      ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X0) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 7.26/1.51      inference(superposition,[status(thm)],[c_0,c_1568]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_4,plain,
% 7.26/1.51      ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X0))) = X0 ),
% 7.26/1.51      inference(cnf_transformation,[],[f64]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_12693,plain,
% 7.26/1.51      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X0,k3_xboole_0(X1,X0))))) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
% 7.26/1.51      inference(superposition,[status(thm)],[c_12329,c_4]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_17331,plain,
% 7.26/1.51      ( k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK1,sK0)),k5_xboole_0(k3_subset_1(sK0,sK1),k3_xboole_0(k3_subset_1(sK0,sK1),k5_xboole_0(sK0,k3_xboole_0(sK1,sK0))))) = k5_xboole_0(sK0,k3_xboole_0(sK1,sK0)) ),
% 7.26/1.51      inference(superposition,[status(thm)],[c_4030,c_12693]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_17933,plain,
% 7.26/1.51      ( k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k5_xboole_0(k3_subset_1(sK0,sK1),k3_xboole_0(k3_subset_1(sK0,sK1),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))))) = k5_xboole_0(sK0,k3_xboole_0(sK1,sK0)) ),
% 7.26/1.51      inference(superposition,[status(thm)],[c_0,c_17331]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_17945,plain,
% 7.26/1.51      ( k5_xboole_0(k3_subset_1(sK0,sK1),k5_xboole_0(k3_subset_1(sK0,sK1),k3_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1)))) = k5_xboole_0(sK0,k3_xboole_0(sK1,sK0)) ),
% 7.26/1.51      inference(light_normalisation,[status(thm)],[c_17933,c_4030]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_3,plain,
% 7.26/1.51      ( r1_tarski(X0,X0) ),
% 7.26/1.51      inference(cnf_transformation,[],[f74]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_702,plain,
% 7.26/1.51      ( r1_tarski(X0,X0) = iProver_top ),
% 7.26/1.51      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_1566,plain,
% 7.26/1.51      ( k3_xboole_0(X0,X0) = X0 ),
% 7.26/1.51      inference(superposition,[status(thm)],[c_702,c_701]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_1567,plain,
% 7.26/1.51      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.26/1.51      inference(superposition,[status(thm)],[c_700,c_701]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_4029,plain,
% 7.26/1.51      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = k3_subset_1(X0,k1_xboole_0) ),
% 7.26/1.51      inference(superposition,[status(thm)],[c_693,c_698]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_4038,plain,
% 7.26/1.51      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
% 7.26/1.51      inference(light_normalisation,[status(thm)],[c_4029,c_10]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_5209,plain,
% 7.26/1.51      ( k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)) = X0 ),
% 7.26/1.51      inference(superposition,[status(thm)],[c_0,c_4038]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_6028,plain,
% 7.26/1.51      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.26/1.51      inference(demodulation,[status(thm)],[c_1567,c_5209]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_4031,plain,
% 7.26/1.51      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k3_subset_1(X0,X0) ),
% 7.26/1.51      inference(superposition,[status(thm)],[c_716,c_698]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_4033,plain,
% 7.26/1.51      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k1_xboole_0 ),
% 7.26/1.51      inference(light_normalisation,[status(thm)],[c_4031,c_3234]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_7870,plain,
% 7.26/1.51      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 7.26/1.51      inference(light_normalisation,[status(thm)],[c_4033,c_1566]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_17946,plain,
% 7.26/1.51      ( k5_xboole_0(sK0,k3_xboole_0(sK1,sK0)) = k3_subset_1(sK0,sK1) ),
% 7.26/1.51      inference(demodulation,
% 7.26/1.51                [status(thm)],
% 7.26/1.51                [c_17945,c_1566,c_6028,c_7870]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_19410,plain,
% 7.26/1.51      ( k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1) ),
% 7.26/1.51      inference(demodulation,[status(thm)],[c_19198,c_17946]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_18,negated_conjecture,
% 7.26/1.51      ( r1_tarski(k3_subset_1(sK0,sK1),sK1)
% 7.26/1.51      | k3_subset_1(sK0,k1_xboole_0) = sK1 ),
% 7.26/1.51      inference(cnf_transformation,[],[f72]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_691,plain,
% 7.26/1.51      ( k3_subset_1(sK0,k1_xboole_0) = sK1
% 7.26/1.51      | r1_tarski(k3_subset_1(sK0,sK1),sK1) = iProver_top ),
% 7.26/1.51      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_727,plain,
% 7.26/1.51      ( sK1 = sK0 | r1_tarski(k3_subset_1(sK0,sK1),sK1) = iProver_top ),
% 7.26/1.51      inference(demodulation,[status(thm)],[c_691,c_10]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_1570,plain,
% 7.26/1.51      ( k3_xboole_0(k3_subset_1(sK0,sK1),sK1) = k3_subset_1(sK0,sK1)
% 7.26/1.51      | sK1 = sK0 ),
% 7.26/1.51      inference(superposition,[status(thm)],[c_727,c_701]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_19773,plain,
% 7.26/1.51      ( k3_xboole_0(k5_xboole_0(sK0,sK1),sK1) = k5_xboole_0(sK0,sK1)
% 7.26/1.51      | sK1 = sK0 ),
% 7.26/1.51      inference(demodulation,[status(thm)],[c_19410,c_1570]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_1412,plain,
% 7.26/1.51      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X0) = iProver_top ),
% 7.26/1.51      inference(superposition,[status(thm)],[c_0,c_699]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_1571,plain,
% 7.26/1.51      ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X0) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
% 7.26/1.51      inference(superposition,[status(thm)],[c_1412,c_701]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_26072,plain,
% 7.26/1.51      ( k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK0,sK1),sK1)) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)),sK1)
% 7.26/1.51      | sK1 = sK0 ),
% 7.26/1.51      inference(superposition,[status(thm)],[c_19773,c_1571]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_8,plain,
% 7.26/1.51      ( k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
% 7.26/1.51      inference(cnf_transformation,[],[f66]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_9,plain,
% 7.26/1.51      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
% 7.26/1.51      inference(cnf_transformation,[],[f67]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_1400,plain,
% 7.26/1.51      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k3_tarski(k2_enumset1(X1,X1,X1,X0)) ),
% 7.26/1.51      inference(superposition,[status(thm)],[c_8,c_9]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_3077,plain,
% 7.26/1.51      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
% 7.26/1.51      inference(superposition,[status(thm)],[c_1400,c_9]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_4215,plain,
% 7.26/1.51      ( k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))) = k5_xboole_0(sK1,k3_subset_1(sK0,sK1)) ),
% 7.26/1.51      inference(superposition,[status(thm)],[c_4030,c_3077]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_19411,plain,
% 7.26/1.51      ( k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)) = k5_xboole_0(sK1,k3_subset_1(sK0,sK1)) ),
% 7.26/1.51      inference(demodulation,[status(thm)],[c_19198,c_4215]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_19413,plain,
% 7.26/1.51      ( k5_xboole_0(sK1,k3_subset_1(sK0,sK1)) = sK0 ),
% 7.26/1.51      inference(demodulation,[status(thm)],[c_19411,c_6028,c_7870]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_19416,plain,
% 7.26/1.51      ( k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = sK0 ),
% 7.26/1.51      inference(demodulation,[status(thm)],[c_19410,c_19413]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_19453,plain,
% 7.26/1.51      ( k3_xboole_0(sK0,sK1) = sK1 ),
% 7.26/1.51      inference(superposition,[status(thm)],[c_19198,c_0]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_26165,plain,
% 7.26/1.51      ( k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK0,sK1),sK1)) = sK1
% 7.26/1.51      | sK1 = sK0 ),
% 7.26/1.51      inference(light_normalisation,
% 7.26/1.51                [status(thm)],
% 7.26/1.51                [c_26072,c_19416,c_19453]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_31837,plain,
% 7.26/1.51      ( k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = sK1 | sK1 = sK0 ),
% 7.26/1.51      inference(superposition,[status(thm)],[c_19773,c_26165]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_31893,plain,
% 7.26/1.51      ( sK1 = sK0 ),
% 7.26/1.51      inference(light_normalisation,[status(thm)],[c_31837,c_19416]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_15,plain,
% 7.26/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.26/1.51      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 7.26/1.51      | ~ r1_tarski(X0,X2)
% 7.26/1.51      | r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X0)) ),
% 7.26/1.51      inference(cnf_transformation,[],[f55]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_694,plain,
% 7.26/1.51      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.26/1.51      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 7.26/1.51      | r1_tarski(X0,X2) != iProver_top
% 7.26/1.51      | r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X0)) = iProver_top ),
% 7.26/1.51      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_1569,plain,
% 7.26/1.51      ( k3_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2)) = k3_subset_1(X0,X1)
% 7.26/1.51      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 7.26/1.51      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 7.26/1.51      | r1_tarski(X2,X1) != iProver_top ),
% 7.26/1.51      inference(superposition,[status(thm)],[c_694,c_701]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_6870,plain,
% 7.26/1.51      ( k3_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,X0)) = k3_subset_1(sK0,sK1)
% 7.26/1.51      | m1_subset_1(X0,k1_zfmisc_1(sK0)) != iProver_top
% 7.26/1.51      | r1_tarski(X0,sK1) != iProver_top ),
% 7.26/1.51      inference(superposition,[status(thm)],[c_690,c_1569]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_7230,plain,
% 7.26/1.51      ( k3_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK0)) = k3_subset_1(sK0,sK1)
% 7.26/1.51      | r1_tarski(sK0,sK1) != iProver_top ),
% 7.26/1.51      inference(superposition,[status(thm)],[c_716,c_6870]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_6055,plain,
% 7.26/1.51      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 7.26/1.51      inference(superposition,[status(thm)],[c_1567,c_0]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_7233,plain,
% 7.26/1.51      ( k3_subset_1(sK0,sK1) = k1_xboole_0
% 7.26/1.51      | r1_tarski(sK0,sK1) != iProver_top ),
% 7.26/1.51      inference(demodulation,[status(thm)],[c_7230,c_3234,c_6055]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_7242,plain,
% 7.26/1.51      ( ~ r1_tarski(sK0,sK1) | k3_subset_1(sK0,sK1) = k1_xboole_0 ),
% 7.26/1.51      inference(predicate_to_equality_rev,[status(thm)],[c_7233]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_345,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_1189,plain,
% 7.26/1.51      ( X0 != X1 | sK0 != X1 | sK0 = X0 ),
% 7.26/1.51      inference(instantiation,[status(thm)],[c_345]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_1746,plain,
% 7.26/1.51      ( X0 != sK0 | sK0 = X0 | sK0 != sK0 ),
% 7.26/1.51      inference(instantiation,[status(thm)],[c_1189]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_1747,plain,
% 7.26/1.51      ( sK1 != sK0 | sK0 = sK1 | sK0 != sK0 ),
% 7.26/1.51      inference(instantiation,[status(thm)],[c_1746]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_1481,plain,
% 7.26/1.51      ( ~ r1_tarski(X0,X1) | r1_tarski(sK0,X2) | X2 != X1 | sK0 != X0 ),
% 7.26/1.51      inference(instantiation,[status(thm)],[c_347]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_1483,plain,
% 7.26/1.51      ( ~ r1_tarski(sK1,sK1)
% 7.26/1.51      | r1_tarski(sK0,sK1)
% 7.26/1.51      | sK1 != sK1
% 7.26/1.51      | sK0 != sK1 ),
% 7.26/1.51      inference(instantiation,[status(thm)],[c_1481]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_344,plain,( X0 = X0 ),theory(equality) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_1187,plain,
% 7.26/1.51      ( sK0 = sK0 ),
% 7.26/1.51      inference(instantiation,[status(thm)],[c_344]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_17,negated_conjecture,
% 7.26/1.51      ( ~ r1_tarski(k3_subset_1(sK0,sK1),sK1)
% 7.26/1.51      | k3_subset_1(sK0,k1_xboole_0) != sK1 ),
% 7.26/1.51      inference(cnf_transformation,[],[f71]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_692,plain,
% 7.26/1.51      ( k3_subset_1(sK0,k1_xboole_0) != sK1
% 7.26/1.51      | r1_tarski(k3_subset_1(sK0,sK1),sK1) != iProver_top ),
% 7.26/1.51      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_736,plain,
% 7.26/1.51      ( sK1 != sK0 | r1_tarski(k3_subset_1(sK0,sK1),sK1) != iProver_top ),
% 7.26/1.51      inference(demodulation,[status(thm)],[c_692,c_10]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_772,plain,
% 7.26/1.51      ( ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) | sK1 != sK0 ),
% 7.26/1.51      inference(predicate_to_equality_rev,[status(thm)],[c_736]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_1,plain,
% 7.26/1.51      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.26/1.51      inference(cnf_transformation,[],[f38]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_59,plain,
% 7.26/1.51      ( ~ r1_tarski(sK1,sK1) | sK1 = sK1 ),
% 7.26/1.51      inference(instantiation,[status(thm)],[c_1]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_55,plain,
% 7.26/1.51      ( r1_tarski(sK1,sK1) ),
% 7.26/1.51      inference(instantiation,[status(thm)],[c_3]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(c_48,plain,
% 7.26/1.51      ( r1_tarski(k1_xboole_0,sK1) ),
% 7.26/1.51      inference(instantiation,[status(thm)],[c_6]) ).
% 7.26/1.51  
% 7.26/1.51  cnf(contradiction,plain,
% 7.26/1.51      ( $false ),
% 7.26/1.51      inference(minisat,
% 7.26/1.51                [status(thm)],
% 7.26/1.51                [c_33365,c_31893,c_7242,c_1747,c_1483,c_1187,c_772,c_59,
% 7.26/1.51                 c_55,c_48]) ).
% 7.26/1.51  
% 7.26/1.51  
% 7.26/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 7.26/1.51  
% 7.26/1.51  ------                               Statistics
% 7.26/1.51  
% 7.26/1.51  ------ General
% 7.26/1.51  
% 7.26/1.51  abstr_ref_over_cycles:                  0
% 7.26/1.51  abstr_ref_under_cycles:                 0
% 7.26/1.51  gc_basic_clause_elim:                   0
% 7.26/1.51  forced_gc_time:                         0
% 7.26/1.51  parsing_time:                           0.011
% 7.26/1.51  unif_index_cands_time:                  0.
% 7.26/1.51  unif_index_add_time:                    0.
% 7.26/1.51  orderings_time:                         0.
% 7.26/1.51  out_proof_time:                         0.012
% 7.26/1.51  total_time:                             0.939
% 7.26/1.51  num_of_symbols:                         42
% 7.26/1.51  num_of_terms:                           24691
% 7.26/1.51  
% 7.26/1.51  ------ Preprocessing
% 7.26/1.51  
% 7.26/1.51  num_of_splits:                          0
% 7.26/1.51  num_of_split_atoms:                     0
% 7.26/1.51  num_of_reused_defs:                     0
% 7.26/1.51  num_eq_ax_congr_red:                    15
% 7.26/1.51  num_of_sem_filtered_clauses:            1
% 7.26/1.51  num_of_subtypes:                        0
% 7.26/1.51  monotx_restored_types:                  0
% 7.26/1.51  sat_num_of_epr_types:                   0
% 7.26/1.51  sat_num_of_non_cyclic_types:            0
% 7.26/1.51  sat_guarded_non_collapsed_types:        0
% 7.26/1.51  num_pure_diseq_elim:                    0
% 7.26/1.51  simp_replaced_by:                       0
% 7.26/1.51  res_preprocessed:                       95
% 7.26/1.51  prep_upred:                             0
% 7.26/1.51  prep_unflattend:                        0
% 7.26/1.51  smt_new_axioms:                         0
% 7.26/1.51  pred_elim_cands:                        2
% 7.26/1.51  pred_elim:                              0
% 7.26/1.51  pred_elim_cl:                           0
% 7.26/1.51  pred_elim_cycles:                       2
% 7.26/1.51  merged_defs:                            8
% 7.26/1.51  merged_defs_ncl:                        0
% 7.26/1.51  bin_hyper_res:                          8
% 7.26/1.51  prep_cycles:                            4
% 7.26/1.51  pred_elim_time:                         0.
% 7.26/1.51  splitting_time:                         0.
% 7.26/1.51  sem_filter_time:                        0.
% 7.26/1.51  monotx_time:                            0.
% 7.26/1.51  subtype_inf_time:                       0.
% 7.26/1.51  
% 7.26/1.51  ------ Problem properties
% 7.26/1.51  
% 7.26/1.51  clauses:                                19
% 7.26/1.51  conjectures:                            3
% 7.26/1.51  epr:                                    3
% 7.26/1.51  horn:                                   18
% 7.26/1.51  ground:                                 3
% 7.26/1.51  unary:                                  11
% 7.26/1.51  binary:                                 5
% 7.26/1.51  lits:                                   32
% 7.26/1.51  lits_eq:                                11
% 7.26/1.51  fd_pure:                                0
% 7.26/1.51  fd_pseudo:                              0
% 7.26/1.51  fd_cond:                                0
% 7.26/1.51  fd_pseudo_cond:                         1
% 7.26/1.51  ac_symbols:                             0
% 7.26/1.51  
% 7.26/1.51  ------ Propositional Solver
% 7.26/1.51  
% 7.26/1.51  prop_solver_calls:                      29
% 7.26/1.51  prop_fast_solver_calls:                 1025
% 7.26/1.51  smt_solver_calls:                       0
% 7.26/1.51  smt_fast_solver_calls:                  0
% 7.26/1.51  prop_num_of_clauses:                    11932
% 7.26/1.51  prop_preprocess_simplified:             21915
% 7.26/1.51  prop_fo_subsumed:                       23
% 7.26/1.51  prop_solver_time:                       0.
% 7.26/1.51  smt_solver_time:                        0.
% 7.26/1.51  smt_fast_solver_time:                   0.
% 7.26/1.51  prop_fast_solver_time:                  0.
% 7.26/1.51  prop_unsat_core_time:                   0.001
% 7.26/1.51  
% 7.26/1.51  ------ QBF
% 7.26/1.51  
% 7.26/1.51  qbf_q_res:                              0
% 7.26/1.51  qbf_num_tautologies:                    0
% 7.26/1.51  qbf_prep_cycles:                        0
% 7.26/1.51  
% 7.26/1.51  ------ BMC1
% 7.26/1.51  
% 7.26/1.51  bmc1_current_bound:                     -1
% 7.26/1.51  bmc1_last_solved_bound:                 -1
% 7.26/1.51  bmc1_unsat_core_size:                   -1
% 7.26/1.51  bmc1_unsat_core_parents_size:           -1
% 7.26/1.51  bmc1_merge_next_fun:                    0
% 7.26/1.51  bmc1_unsat_core_clauses_time:           0.
% 7.26/1.51  
% 7.26/1.51  ------ Instantiation
% 7.26/1.51  
% 7.26/1.51  inst_num_of_clauses:                    3961
% 7.26/1.51  inst_num_in_passive:                    1280
% 7.26/1.51  inst_num_in_active:                     1067
% 7.26/1.51  inst_num_in_unprocessed:                1614
% 7.26/1.51  inst_num_of_loops:                      1352
% 7.26/1.51  inst_num_of_learning_restarts:          0
% 7.26/1.51  inst_num_moves_active_passive:          283
% 7.26/1.51  inst_lit_activity:                      0
% 7.26/1.51  inst_lit_activity_moves:                0
% 7.26/1.51  inst_num_tautologies:                   0
% 7.26/1.51  inst_num_prop_implied:                  0
% 7.26/1.51  inst_num_existing_simplified:           0
% 7.26/1.51  inst_num_eq_res_simplified:             0
% 7.26/1.51  inst_num_child_elim:                    0
% 7.26/1.51  inst_num_of_dismatching_blockings:      2743
% 7.26/1.51  inst_num_of_non_proper_insts:           4963
% 7.26/1.51  inst_num_of_duplicates:                 0
% 7.26/1.51  inst_inst_num_from_inst_to_res:         0
% 7.26/1.51  inst_dismatching_checking_time:         0.
% 7.26/1.51  
% 7.26/1.51  ------ Resolution
% 7.26/1.51  
% 7.26/1.51  res_num_of_clauses:                     0
% 7.26/1.51  res_num_in_passive:                     0
% 7.26/1.51  res_num_in_active:                      0
% 7.26/1.51  res_num_of_loops:                       99
% 7.26/1.51  res_forward_subset_subsumed:            642
% 7.26/1.51  res_backward_subset_subsumed:           2
% 7.26/1.51  res_forward_subsumed:                   0
% 7.26/1.51  res_backward_subsumed:                  0
% 7.26/1.51  res_forward_subsumption_resolution:     0
% 7.26/1.51  res_backward_subsumption_resolution:    0
% 7.26/1.51  res_clause_to_clause_subsumption:       3423
% 7.26/1.51  res_orphan_elimination:                 0
% 7.26/1.51  res_tautology_del:                      244
% 7.26/1.51  res_num_eq_res_simplified:              0
% 7.26/1.51  res_num_sel_changes:                    0
% 7.26/1.51  res_moves_from_active_to_pass:          0
% 7.26/1.51  
% 7.26/1.51  ------ Superposition
% 7.26/1.51  
% 7.26/1.51  sup_time_total:                         0.
% 7.26/1.51  sup_time_generating:                    0.
% 7.26/1.51  sup_time_sim_full:                      0.
% 7.26/1.51  sup_time_sim_immed:                     0.
% 7.26/1.51  
% 7.26/1.51  sup_num_of_clauses:                     414
% 7.26/1.51  sup_num_in_active:                      121
% 7.26/1.51  sup_num_in_passive:                     293
% 7.26/1.51  sup_num_of_loops:                       270
% 7.26/1.51  sup_fw_superposition:                   1191
% 7.26/1.51  sup_bw_superposition:                   1353
% 7.26/1.51  sup_immediate_simplified:               688
% 7.26/1.51  sup_given_eliminated:                   3
% 7.26/1.51  comparisons_done:                       0
% 7.26/1.51  comparisons_avoided:                    174
% 7.26/1.51  
% 7.26/1.51  ------ Simplifications
% 7.26/1.51  
% 7.26/1.51  
% 7.26/1.51  sim_fw_subset_subsumed:                 38
% 7.26/1.51  sim_bw_subset_subsumed:                 18
% 7.26/1.51  sim_fw_subsumed:                        76
% 7.26/1.51  sim_bw_subsumed:                        9
% 7.26/1.51  sim_fw_subsumption_res:                 8
% 7.26/1.51  sim_bw_subsumption_res:                 0
% 7.26/1.51  sim_tautology_del:                      15
% 7.26/1.51  sim_eq_tautology_del:                   230
% 7.26/1.51  sim_eq_res_simp:                        0
% 7.26/1.51  sim_fw_demodulated:                     320
% 7.26/1.51  sim_bw_demodulated:                     182
% 7.26/1.51  sim_light_normalised:                   434
% 7.26/1.51  sim_joinable_taut:                      0
% 7.26/1.51  sim_joinable_simp:                      0
% 7.26/1.51  sim_ac_normalised:                      0
% 7.26/1.51  sim_smt_subsumption:                    0
% 7.26/1.51  
%------------------------------------------------------------------------------
