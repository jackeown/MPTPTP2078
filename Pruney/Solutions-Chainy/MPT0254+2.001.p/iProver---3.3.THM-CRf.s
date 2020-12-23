%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:33:46 EST 2020

% Result     : Theorem 7.38s
% Output     : CNFRefutation 7.38s
% Verified   : 
% Statistics : Number of formulae       :  156 (4877 expanded)
%              Number of clauses        :   82 (1339 expanded)
%              Number of leaves         :   27 (1413 expanded)
%              Depth                    :   34
%              Number of atoms          :  237 (5056 expanded)
%              Number of equality atoms :  149 (4943 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :   10 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f25,conjecture,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    inference(negated_conjecture,[],[f25])).

fof(f30,plain,(
    ? [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 ),
    inference(ennf_transformation,[],[f26])).

fof(f37,plain,
    ( ? [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
   => k2_xboole_0(k1_tarski(sK1),sK2) = k1_xboole_0 ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    k2_xboole_0(k1_tarski(sK1),sK2) = k1_xboole_0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f30,f37])).

fof(f68,plain,(
    k2_xboole_0(k1_tarski(sK1),sK2) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f38])).

fof(f13,axiom,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f18])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f19])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f20])).

fof(f69,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f59,f60])).

fof(f70,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f58,f69])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f57,f70])).

fof(f72,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f56,f71])).

fof(f73,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f55,f72])).

fof(f74,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f54,f73])).

fof(f79,plain,(
    k5_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f68,f53,f74])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f10,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f12,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f12])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f6,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f76,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f49,f46])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f22,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f77,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f65,f53,f73])).

fof(f24,axiom,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f24])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f42,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f27])).

fof(f75,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),k3_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f42,f53])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f31])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f81,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f43])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f33])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK0(X0,X1),X0)
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( r1_tarski(sK0(X0,X1),X0)
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK0(X0,X1),X0)
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( r1_tarski(sK0(X0,X1),X0)
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f82,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f62])).

fof(f23,axiom,(
    k1_tarski(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    k1_tarski(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f23])).

fof(f78,plain,(
    k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_zfmisc_1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f66,f74])).

cnf(c_11,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_20,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_286,negated_conjecture,
    ( k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2))) = k1_xboole_0 ),
    inference(theory_normalisation,[status(thm)],[c_20,c_11,c_2])).

cnf(c_1000,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1,c_286])).

cnf(c_1278,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),X0)) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_1000,c_11])).

cnf(c_10,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1107,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_10,c_2])).

cnf(c_1284,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1278,c_1107])).

cnf(c_1549,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k3_xboole_0(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),X0))) = X0 ),
    inference(superposition,[status(thm)],[c_11,c_1284])).

cnf(c_12,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1547,plain,
    ( k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k5_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_12,c_1284])).

cnf(c_1553,plain,
    ( k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = sK2 ),
    inference(demodulation,[status(thm)],[c_1547,c_10])).

cnf(c_1557,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK2,X0)) = X0 ),
    inference(demodulation,[status(thm)],[c_1553,c_1284])).

cnf(c_1718,plain,
    ( k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k3_xboole_0(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),X0)) = k5_xboole_0(sK2,X0) ),
    inference(superposition,[status(thm)],[c_1549,c_1557])).

cnf(c_1559,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(X0,sK2)) = X0 ),
    inference(superposition,[status(thm)],[c_2,c_1557])).

cnf(c_1565,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK2,X0),X1)) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1557,c_11])).

cnf(c_1855,plain,
    ( k5_xboole_0(X0,k5_xboole_0(sK2,X0)) = k5_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_12,c_1565])).

cnf(c_1878,plain,
    ( k5_xboole_0(X0,k5_xboole_0(sK2,X0)) = sK2 ),
    inference(demodulation,[status(thm)],[c_1855,c_10])).

cnf(c_2293,plain,
    ( k5_xboole_0(k5_xboole_0(X0,sK2),X0) = sK2 ),
    inference(superposition,[status(thm)],[c_1559,c_1878])).

cnf(c_4291,plain,
    ( k5_xboole_0(k5_xboole_0(X0,sK2),k5_xboole_0(X0,X1)) = k5_xboole_0(sK2,X1) ),
    inference(superposition,[status(thm)],[c_2293,c_11])).

cnf(c_11539,plain,
    ( k5_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2),k5_xboole_0(sK2,X0)) = k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),X0)) ),
    inference(superposition,[status(thm)],[c_1718,c_4291])).

cnf(c_2284,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_2,c_1878])).

cnf(c_3479,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),sK2)) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2) ),
    inference(superposition,[status(thm)],[c_2284,c_1718])).

cnf(c_3485,plain,
    ( k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2) = k3_xboole_0(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(demodulation,[status(thm)],[c_3479,c_1559])).

cnf(c_1712,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(X0,k3_xboole_0(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))) = X0 ),
    inference(superposition,[status(thm)],[c_2,c_1549])).

cnf(c_3338,plain,
    ( k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(X0,k3_xboole_0(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) = k5_xboole_0(sK2,X0) ),
    inference(superposition,[status(thm)],[c_1712,c_1557])).

cnf(c_2292,plain,
    ( k5_xboole_0(k5_xboole_0(sK2,X0),X0) = sK2 ),
    inference(superposition,[status(thm)],[c_1557,c_1878])).

cnf(c_2807,plain,
    ( k5_xboole_0(k5_xboole_0(sK2,X0),k5_xboole_0(X0,X1)) = k5_xboole_0(sK2,X1) ),
    inference(superposition,[status(thm)],[c_2292,c_11])).

cnf(c_5986,plain,
    ( k5_xboole_0(k5_xboole_0(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_xboole_0(sK2,X0)) = k5_xboole_0(sK2,k5_xboole_0(X0,k3_xboole_0(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) ),
    inference(superposition,[status(thm)],[c_3338,c_2807])).

cnf(c_1714,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_xboole_0)) = k3_xboole_0(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(superposition,[status(thm)],[c_12,c_1549])).

cnf(c_1729,plain,
    ( k5_xboole_0(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k3_xboole_0(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(demodulation,[status(thm)],[c_1714,c_10])).

cnf(c_2325,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(sK2,X0),sK2)) = k5_xboole_0(sK2,sK2) ),
    inference(superposition,[status(thm)],[c_2284,c_1565])).

cnf(c_2295,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(sK2,X0),X1)) = k5_xboole_0(sK2,X1) ),
    inference(superposition,[status(thm)],[c_1878,c_11])).

cnf(c_2326,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(sK2,X0),sK2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2325,c_12,c_2295])).

cnf(c_597,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_11,c_2])).

cnf(c_5420,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(sK2,X0),sK2))) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2326,c_597])).

cnf(c_1853,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(X0,k5_xboole_0(sK2,X1))) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_2,c_1565])).

cnf(c_5484,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(sK2,X2)))) = k5_xboole_0(k5_xboole_0(X1,X2),X0) ),
    inference(superposition,[status(thm)],[c_597,c_1853])).

cnf(c_4858,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(sK2,X2)))) = k5_xboole_0(X2,k5_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_11,c_1853])).

cnf(c_5495,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
    inference(light_normalisation,[status(thm)],[c_5484,c_4858])).

cnf(c_5581,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(sK2,sK2)))) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_5420,c_5495])).

cnf(c_5582,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(demodulation,[status(thm)],[c_5581,c_10,c_12])).

cnf(c_5757,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(X0,k3_xboole_0(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0) ),
    inference(superposition,[status(thm)],[c_5582,c_1718])).

cnf(c_6045,plain,
    ( k5_xboole_0(k3_xboole_0(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_xboole_0(sK2,X0)) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0) ),
    inference(light_normalisation,[status(thm)],[c_5986,c_1729,c_5757])).

cnf(c_9,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_581,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2595,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_581])).

cnf(c_4061,plain,
    ( r1_tarski(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1553,c_2595])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_583,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_10573,plain,
    ( k3_xboole_0(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = sK2 ),
    inference(superposition,[status(thm)],[c_4061,c_583])).

cnf(c_11673,plain,
    ( k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_11539,c_1557,c_3485,c_6045,c_10573])).

cnf(c_11815,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_11673,c_10])).

cnf(c_17,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_287,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) ),
    inference(theory_normalisation,[status(thm)],[c_17,c_11,c_2])).

cnf(c_1104,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_1,c_287])).

cnf(c_14070,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK1,sK1))) = k3_tarski(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_11815,c_1104])).

cnf(c_19,plain,
    ( k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_14072,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK1,sK1))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_14070,c_19])).

cnf(c_3,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X0),k3_xboole_0(X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_288,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))) = X0 ),
    inference(theory_normalisation,[status(thm)],[c_3,c_11,c_2])).

cnf(c_6,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_584,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3665,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_584,c_583])).

cnf(c_14073,plain,
    ( sK1 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_14072,c_10,c_12,c_288,c_3665])).

cnf(c_14074,plain,
    ( k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_14073,c_11815])).

cnf(c_292,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_611,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k1_zfmisc_1(X3))
    | X0 != X2
    | X1 != k1_zfmisc_1(X3) ),
    inference(instantiation,[status(thm)],[c_292])).

cnf(c_641,plain,
    ( r2_hidden(X0,k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | ~ r2_hidden(X1,k1_zfmisc_1(k1_xboole_0))
    | X0 != X1
    | k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_zfmisc_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_611])).

cnf(c_2772,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(k1_xboole_0))
    | r2_hidden(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != X0
    | k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_zfmisc_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_641])).

cnf(c_6331,plain,
    ( r2_hidden(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_zfmisc_1(k1_xboole_0)
    | k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2772])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1505,plain,
    ( ~ r2_hidden(X0,k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | ~ r2_hidden(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),X0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2771,plain,
    ( ~ r2_hidden(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_1505])).

cnf(c_922,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_15,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_667,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | r2_hidden(X0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_753,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_667])).

cnf(c_18,plain,
    ( k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_zfmisc_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f78])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_14074,c_6331,c_2771,c_922,c_753,c_18])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 12:13:37 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.38/1.53  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.38/1.53  
% 7.38/1.53  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.38/1.53  
% 7.38/1.53  ------  iProver source info
% 7.38/1.53  
% 7.38/1.53  git: date: 2020-06-30 10:37:57 +0100
% 7.38/1.53  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.38/1.53  git: non_committed_changes: false
% 7.38/1.53  git: last_make_outside_of_git: false
% 7.38/1.53  
% 7.38/1.53  ------ 
% 7.38/1.53  
% 7.38/1.53  ------ Input Options
% 7.38/1.53  
% 7.38/1.53  --out_options                           all
% 7.38/1.53  --tptp_safe_out                         true
% 7.38/1.53  --problem_path                          ""
% 7.38/1.53  --include_path                          ""
% 7.38/1.53  --clausifier                            res/vclausify_rel
% 7.38/1.53  --clausifier_options                    ""
% 7.38/1.53  --stdin                                 false
% 7.38/1.53  --stats_out                             all
% 7.38/1.53  
% 7.38/1.53  ------ General Options
% 7.38/1.53  
% 7.38/1.53  --fof                                   false
% 7.38/1.53  --time_out_real                         305.
% 7.38/1.53  --time_out_virtual                      -1.
% 7.38/1.53  --symbol_type_check                     false
% 7.38/1.53  --clausify_out                          false
% 7.38/1.53  --sig_cnt_out                           false
% 7.38/1.53  --trig_cnt_out                          false
% 7.38/1.53  --trig_cnt_out_tolerance                1.
% 7.38/1.53  --trig_cnt_out_sk_spl                   false
% 7.38/1.53  --abstr_cl_out                          false
% 7.38/1.53  
% 7.38/1.53  ------ Global Options
% 7.38/1.53  
% 7.38/1.53  --schedule                              default
% 7.38/1.53  --add_important_lit                     false
% 7.38/1.53  --prop_solver_per_cl                    1000
% 7.38/1.53  --min_unsat_core                        false
% 7.38/1.53  --soft_assumptions                      false
% 7.38/1.53  --soft_lemma_size                       3
% 7.38/1.53  --prop_impl_unit_size                   0
% 7.38/1.53  --prop_impl_unit                        []
% 7.38/1.53  --share_sel_clauses                     true
% 7.38/1.53  --reset_solvers                         false
% 7.38/1.53  --bc_imp_inh                            [conj_cone]
% 7.38/1.53  --conj_cone_tolerance                   3.
% 7.38/1.53  --extra_neg_conj                        none
% 7.38/1.53  --large_theory_mode                     true
% 7.38/1.53  --prolific_symb_bound                   200
% 7.38/1.53  --lt_threshold                          2000
% 7.38/1.53  --clause_weak_htbl                      true
% 7.38/1.53  --gc_record_bc_elim                     false
% 7.38/1.53  
% 7.38/1.53  ------ Preprocessing Options
% 7.38/1.53  
% 7.38/1.53  --preprocessing_flag                    true
% 7.38/1.53  --time_out_prep_mult                    0.1
% 7.38/1.53  --splitting_mode                        input
% 7.38/1.53  --splitting_grd                         true
% 7.38/1.53  --splitting_cvd                         false
% 7.38/1.53  --splitting_cvd_svl                     false
% 7.38/1.53  --splitting_nvd                         32
% 7.38/1.53  --sub_typing                            true
% 7.38/1.53  --prep_gs_sim                           true
% 7.38/1.53  --prep_unflatten                        true
% 7.38/1.53  --prep_res_sim                          true
% 7.38/1.53  --prep_upred                            true
% 7.38/1.53  --prep_sem_filter                       exhaustive
% 7.38/1.53  --prep_sem_filter_out                   false
% 7.38/1.53  --pred_elim                             true
% 7.38/1.53  --res_sim_input                         true
% 7.38/1.53  --eq_ax_congr_red                       true
% 7.38/1.53  --pure_diseq_elim                       true
% 7.38/1.53  --brand_transform                       false
% 7.38/1.53  --non_eq_to_eq                          false
% 7.38/1.53  --prep_def_merge                        true
% 7.38/1.53  --prep_def_merge_prop_impl              false
% 7.38/1.53  --prep_def_merge_mbd                    true
% 7.38/1.53  --prep_def_merge_tr_red                 false
% 7.38/1.53  --prep_def_merge_tr_cl                  false
% 7.38/1.53  --smt_preprocessing                     true
% 7.38/1.53  --smt_ac_axioms                         fast
% 7.38/1.53  --preprocessed_out                      false
% 7.38/1.53  --preprocessed_stats                    false
% 7.38/1.53  
% 7.38/1.53  ------ Abstraction refinement Options
% 7.38/1.53  
% 7.38/1.53  --abstr_ref                             []
% 7.38/1.53  --abstr_ref_prep                        false
% 7.38/1.53  --abstr_ref_until_sat                   false
% 7.38/1.53  --abstr_ref_sig_restrict                funpre
% 7.38/1.53  --abstr_ref_af_restrict_to_split_sk     false
% 7.38/1.53  --abstr_ref_under                       []
% 7.38/1.53  
% 7.38/1.53  ------ SAT Options
% 7.38/1.53  
% 7.38/1.53  --sat_mode                              false
% 7.38/1.53  --sat_fm_restart_options                ""
% 7.38/1.53  --sat_gr_def                            false
% 7.38/1.53  --sat_epr_types                         true
% 7.38/1.53  --sat_non_cyclic_types                  false
% 7.38/1.53  --sat_finite_models                     false
% 7.38/1.53  --sat_fm_lemmas                         false
% 7.38/1.53  --sat_fm_prep                           false
% 7.38/1.53  --sat_fm_uc_incr                        true
% 7.38/1.53  --sat_out_model                         small
% 7.38/1.53  --sat_out_clauses                       false
% 7.38/1.53  
% 7.38/1.53  ------ QBF Options
% 7.38/1.53  
% 7.38/1.53  --qbf_mode                              false
% 7.38/1.53  --qbf_elim_univ                         false
% 7.38/1.53  --qbf_dom_inst                          none
% 7.38/1.53  --qbf_dom_pre_inst                      false
% 7.38/1.53  --qbf_sk_in                             false
% 7.38/1.53  --qbf_pred_elim                         true
% 7.38/1.53  --qbf_split                             512
% 7.38/1.53  
% 7.38/1.53  ------ BMC1 Options
% 7.38/1.53  
% 7.38/1.53  --bmc1_incremental                      false
% 7.38/1.53  --bmc1_axioms                           reachable_all
% 7.38/1.53  --bmc1_min_bound                        0
% 7.38/1.53  --bmc1_max_bound                        -1
% 7.38/1.53  --bmc1_max_bound_default                -1
% 7.38/1.53  --bmc1_symbol_reachability              true
% 7.38/1.53  --bmc1_property_lemmas                  false
% 7.38/1.53  --bmc1_k_induction                      false
% 7.38/1.53  --bmc1_non_equiv_states                 false
% 7.38/1.53  --bmc1_deadlock                         false
% 7.38/1.53  --bmc1_ucm                              false
% 7.38/1.53  --bmc1_add_unsat_core                   none
% 7.38/1.53  --bmc1_unsat_core_children              false
% 7.38/1.53  --bmc1_unsat_core_extrapolate_axioms    false
% 7.38/1.53  --bmc1_out_stat                         full
% 7.38/1.53  --bmc1_ground_init                      false
% 7.38/1.53  --bmc1_pre_inst_next_state              false
% 7.38/1.53  --bmc1_pre_inst_state                   false
% 7.38/1.53  --bmc1_pre_inst_reach_state             false
% 7.38/1.53  --bmc1_out_unsat_core                   false
% 7.38/1.53  --bmc1_aig_witness_out                  false
% 7.38/1.53  --bmc1_verbose                          false
% 7.38/1.53  --bmc1_dump_clauses_tptp                false
% 7.38/1.53  --bmc1_dump_unsat_core_tptp             false
% 7.38/1.53  --bmc1_dump_file                        -
% 7.38/1.53  --bmc1_ucm_expand_uc_limit              128
% 7.38/1.53  --bmc1_ucm_n_expand_iterations          6
% 7.38/1.53  --bmc1_ucm_extend_mode                  1
% 7.38/1.53  --bmc1_ucm_init_mode                    2
% 7.38/1.53  --bmc1_ucm_cone_mode                    none
% 7.38/1.53  --bmc1_ucm_reduced_relation_type        0
% 7.38/1.53  --bmc1_ucm_relax_model                  4
% 7.38/1.53  --bmc1_ucm_full_tr_after_sat            true
% 7.38/1.53  --bmc1_ucm_expand_neg_assumptions       false
% 7.38/1.53  --bmc1_ucm_layered_model                none
% 7.38/1.53  --bmc1_ucm_max_lemma_size               10
% 7.38/1.53  
% 7.38/1.53  ------ AIG Options
% 7.38/1.53  
% 7.38/1.53  --aig_mode                              false
% 7.38/1.53  
% 7.38/1.53  ------ Instantiation Options
% 7.38/1.53  
% 7.38/1.53  --instantiation_flag                    true
% 7.38/1.53  --inst_sos_flag                         true
% 7.38/1.53  --inst_sos_phase                        true
% 7.38/1.53  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.38/1.53  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.38/1.53  --inst_lit_sel_side                     num_symb
% 7.38/1.53  --inst_solver_per_active                1400
% 7.38/1.53  --inst_solver_calls_frac                1.
% 7.38/1.53  --inst_passive_queue_type               priority_queues
% 7.38/1.53  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.38/1.53  --inst_passive_queues_freq              [25;2]
% 7.38/1.53  --inst_dismatching                      true
% 7.38/1.53  --inst_eager_unprocessed_to_passive     true
% 7.38/1.53  --inst_prop_sim_given                   true
% 7.38/1.53  --inst_prop_sim_new                     false
% 7.38/1.53  --inst_subs_new                         false
% 7.38/1.53  --inst_eq_res_simp                      false
% 7.38/1.53  --inst_subs_given                       false
% 7.38/1.53  --inst_orphan_elimination               true
% 7.38/1.53  --inst_learning_loop_flag               true
% 7.38/1.53  --inst_learning_start                   3000
% 7.38/1.53  --inst_learning_factor                  2
% 7.38/1.53  --inst_start_prop_sim_after_learn       3
% 7.38/1.53  --inst_sel_renew                        solver
% 7.38/1.53  --inst_lit_activity_flag                true
% 7.38/1.53  --inst_restr_to_given                   false
% 7.38/1.53  --inst_activity_threshold               500
% 7.38/1.53  --inst_out_proof                        true
% 7.38/1.53  
% 7.38/1.53  ------ Resolution Options
% 7.38/1.53  
% 7.38/1.53  --resolution_flag                       true
% 7.38/1.53  --res_lit_sel                           adaptive
% 7.38/1.53  --res_lit_sel_side                      none
% 7.38/1.53  --res_ordering                          kbo
% 7.38/1.53  --res_to_prop_solver                    active
% 7.38/1.53  --res_prop_simpl_new                    false
% 7.38/1.53  --res_prop_simpl_given                  true
% 7.38/1.53  --res_passive_queue_type                priority_queues
% 7.38/1.53  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.38/1.53  --res_passive_queues_freq               [15;5]
% 7.38/1.53  --res_forward_subs                      full
% 7.38/1.53  --res_backward_subs                     full
% 7.38/1.53  --res_forward_subs_resolution           true
% 7.38/1.53  --res_backward_subs_resolution          true
% 7.38/1.53  --res_orphan_elimination                true
% 7.38/1.53  --res_time_limit                        2.
% 7.38/1.53  --res_out_proof                         true
% 7.38/1.53  
% 7.38/1.53  ------ Superposition Options
% 7.38/1.53  
% 7.38/1.53  --superposition_flag                    true
% 7.38/1.53  --sup_passive_queue_type                priority_queues
% 7.38/1.53  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.38/1.53  --sup_passive_queues_freq               [8;1;4]
% 7.38/1.53  --demod_completeness_check              fast
% 7.38/1.53  --demod_use_ground                      true
% 7.38/1.53  --sup_to_prop_solver                    passive
% 7.38/1.53  --sup_prop_simpl_new                    true
% 7.38/1.53  --sup_prop_simpl_given                  true
% 7.38/1.53  --sup_fun_splitting                     true
% 7.38/1.53  --sup_smt_interval                      50000
% 7.38/1.53  
% 7.38/1.53  ------ Superposition Simplification Setup
% 7.38/1.53  
% 7.38/1.53  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.38/1.53  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.38/1.53  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.38/1.53  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.38/1.53  --sup_full_triv                         [TrivRules;PropSubs]
% 7.38/1.53  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.38/1.53  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.38/1.53  --sup_immed_triv                        [TrivRules]
% 7.38/1.53  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.38/1.53  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.38/1.53  --sup_immed_bw_main                     []
% 7.38/1.53  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.38/1.53  --sup_input_triv                        [Unflattening;TrivRules]
% 7.38/1.53  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.38/1.53  --sup_input_bw                          []
% 7.38/1.53  
% 7.38/1.53  ------ Combination Options
% 7.38/1.53  
% 7.38/1.53  --comb_res_mult                         3
% 7.38/1.53  --comb_sup_mult                         2
% 7.38/1.53  --comb_inst_mult                        10
% 7.38/1.53  
% 7.38/1.53  ------ Debug Options
% 7.38/1.53  
% 7.38/1.53  --dbg_backtrace                         false
% 7.38/1.53  --dbg_dump_prop_clauses                 false
% 7.38/1.53  --dbg_dump_prop_clauses_file            -
% 7.38/1.53  --dbg_out_stat                          false
% 7.38/1.53  ------ Parsing...
% 7.38/1.53  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.38/1.53  
% 7.38/1.53  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.38/1.53  
% 7.38/1.53  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.38/1.53  
% 7.38/1.53  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.38/1.53  ------ Proving...
% 7.38/1.53  ------ Problem Properties 
% 7.38/1.53  
% 7.38/1.53  
% 7.38/1.53  clauses                                 20
% 7.38/1.53  conjectures                             1
% 7.38/1.53  EPR                                     4
% 7.38/1.53  Horn                                    19
% 7.38/1.53  unary                                   13
% 7.38/1.53  binary                                  4
% 7.38/1.53  lits                                    30
% 7.38/1.53  lits eq                                 14
% 7.38/1.53  fd_pure                                 0
% 7.38/1.53  fd_pseudo                               0
% 7.38/1.53  fd_cond                                 0
% 7.38/1.53  fd_pseudo_cond                          3
% 7.38/1.53  AC symbols                              1
% 7.38/1.53  
% 7.38/1.53  ------ Schedule dynamic 5 is on 
% 7.38/1.53  
% 7.38/1.53  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.38/1.53  
% 7.38/1.53  
% 7.38/1.53  ------ 
% 7.38/1.53  Current options:
% 7.38/1.53  ------ 
% 7.38/1.53  
% 7.38/1.53  ------ Input Options
% 7.38/1.53  
% 7.38/1.53  --out_options                           all
% 7.38/1.53  --tptp_safe_out                         true
% 7.38/1.53  --problem_path                          ""
% 7.38/1.53  --include_path                          ""
% 7.38/1.53  --clausifier                            res/vclausify_rel
% 7.38/1.53  --clausifier_options                    ""
% 7.38/1.53  --stdin                                 false
% 7.38/1.53  --stats_out                             all
% 7.38/1.53  
% 7.38/1.53  ------ General Options
% 7.38/1.53  
% 7.38/1.53  --fof                                   false
% 7.38/1.53  --time_out_real                         305.
% 7.38/1.53  --time_out_virtual                      -1.
% 7.38/1.53  --symbol_type_check                     false
% 7.38/1.53  --clausify_out                          false
% 7.38/1.53  --sig_cnt_out                           false
% 7.38/1.53  --trig_cnt_out                          false
% 7.38/1.53  --trig_cnt_out_tolerance                1.
% 7.38/1.53  --trig_cnt_out_sk_spl                   false
% 7.38/1.53  --abstr_cl_out                          false
% 7.38/1.53  
% 7.38/1.53  ------ Global Options
% 7.38/1.53  
% 7.38/1.53  --schedule                              default
% 7.38/1.53  --add_important_lit                     false
% 7.38/1.53  --prop_solver_per_cl                    1000
% 7.38/1.53  --min_unsat_core                        false
% 7.38/1.53  --soft_assumptions                      false
% 7.38/1.53  --soft_lemma_size                       3
% 7.38/1.53  --prop_impl_unit_size                   0
% 7.38/1.53  --prop_impl_unit                        []
% 7.38/1.53  --share_sel_clauses                     true
% 7.38/1.53  --reset_solvers                         false
% 7.38/1.53  --bc_imp_inh                            [conj_cone]
% 7.38/1.53  --conj_cone_tolerance                   3.
% 7.38/1.53  --extra_neg_conj                        none
% 7.38/1.53  --large_theory_mode                     true
% 7.38/1.53  --prolific_symb_bound                   200
% 7.38/1.53  --lt_threshold                          2000
% 7.38/1.53  --clause_weak_htbl                      true
% 7.38/1.53  --gc_record_bc_elim                     false
% 7.38/1.53  
% 7.38/1.53  ------ Preprocessing Options
% 7.38/1.53  
% 7.38/1.53  --preprocessing_flag                    true
% 7.38/1.53  --time_out_prep_mult                    0.1
% 7.38/1.53  --splitting_mode                        input
% 7.38/1.53  --splitting_grd                         true
% 7.38/1.53  --splitting_cvd                         false
% 7.38/1.53  --splitting_cvd_svl                     false
% 7.38/1.53  --splitting_nvd                         32
% 7.38/1.53  --sub_typing                            true
% 7.38/1.53  --prep_gs_sim                           true
% 7.38/1.53  --prep_unflatten                        true
% 7.38/1.53  --prep_res_sim                          true
% 7.38/1.53  --prep_upred                            true
% 7.38/1.53  --prep_sem_filter                       exhaustive
% 7.38/1.53  --prep_sem_filter_out                   false
% 7.38/1.53  --pred_elim                             true
% 7.38/1.53  --res_sim_input                         true
% 7.38/1.53  --eq_ax_congr_red                       true
% 7.38/1.53  --pure_diseq_elim                       true
% 7.38/1.53  --brand_transform                       false
% 7.38/1.53  --non_eq_to_eq                          false
% 7.38/1.53  --prep_def_merge                        true
% 7.38/1.53  --prep_def_merge_prop_impl              false
% 7.38/1.53  --prep_def_merge_mbd                    true
% 7.38/1.53  --prep_def_merge_tr_red                 false
% 7.38/1.53  --prep_def_merge_tr_cl                  false
% 7.38/1.53  --smt_preprocessing                     true
% 7.38/1.53  --smt_ac_axioms                         fast
% 7.38/1.53  --preprocessed_out                      false
% 7.38/1.53  --preprocessed_stats                    false
% 7.38/1.53  
% 7.38/1.53  ------ Abstraction refinement Options
% 7.38/1.53  
% 7.38/1.53  --abstr_ref                             []
% 7.38/1.53  --abstr_ref_prep                        false
% 7.38/1.53  --abstr_ref_until_sat                   false
% 7.38/1.53  --abstr_ref_sig_restrict                funpre
% 7.38/1.53  --abstr_ref_af_restrict_to_split_sk     false
% 7.38/1.53  --abstr_ref_under                       []
% 7.38/1.53  
% 7.38/1.53  ------ SAT Options
% 7.38/1.53  
% 7.38/1.53  --sat_mode                              false
% 7.38/1.53  --sat_fm_restart_options                ""
% 7.38/1.53  --sat_gr_def                            false
% 7.38/1.53  --sat_epr_types                         true
% 7.38/1.53  --sat_non_cyclic_types                  false
% 7.38/1.53  --sat_finite_models                     false
% 7.38/1.53  --sat_fm_lemmas                         false
% 7.38/1.53  --sat_fm_prep                           false
% 7.38/1.53  --sat_fm_uc_incr                        true
% 7.38/1.53  --sat_out_model                         small
% 7.38/1.53  --sat_out_clauses                       false
% 7.38/1.53  
% 7.38/1.53  ------ QBF Options
% 7.38/1.53  
% 7.38/1.53  --qbf_mode                              false
% 7.38/1.53  --qbf_elim_univ                         false
% 7.38/1.53  --qbf_dom_inst                          none
% 7.38/1.53  --qbf_dom_pre_inst                      false
% 7.38/1.53  --qbf_sk_in                             false
% 7.38/1.53  --qbf_pred_elim                         true
% 7.38/1.53  --qbf_split                             512
% 7.38/1.53  
% 7.38/1.53  ------ BMC1 Options
% 7.38/1.53  
% 7.38/1.53  --bmc1_incremental                      false
% 7.38/1.53  --bmc1_axioms                           reachable_all
% 7.38/1.53  --bmc1_min_bound                        0
% 7.38/1.53  --bmc1_max_bound                        -1
% 7.38/1.53  --bmc1_max_bound_default                -1
% 7.38/1.53  --bmc1_symbol_reachability              true
% 7.38/1.53  --bmc1_property_lemmas                  false
% 7.38/1.53  --bmc1_k_induction                      false
% 7.38/1.53  --bmc1_non_equiv_states                 false
% 7.38/1.53  --bmc1_deadlock                         false
% 7.38/1.53  --bmc1_ucm                              false
% 7.38/1.53  --bmc1_add_unsat_core                   none
% 7.38/1.53  --bmc1_unsat_core_children              false
% 7.38/1.53  --bmc1_unsat_core_extrapolate_axioms    false
% 7.38/1.53  --bmc1_out_stat                         full
% 7.38/1.53  --bmc1_ground_init                      false
% 7.38/1.53  --bmc1_pre_inst_next_state              false
% 7.38/1.53  --bmc1_pre_inst_state                   false
% 7.38/1.53  --bmc1_pre_inst_reach_state             false
% 7.38/1.53  --bmc1_out_unsat_core                   false
% 7.38/1.53  --bmc1_aig_witness_out                  false
% 7.38/1.53  --bmc1_verbose                          false
% 7.38/1.53  --bmc1_dump_clauses_tptp                false
% 7.38/1.53  --bmc1_dump_unsat_core_tptp             false
% 7.38/1.53  --bmc1_dump_file                        -
% 7.38/1.53  --bmc1_ucm_expand_uc_limit              128
% 7.38/1.53  --bmc1_ucm_n_expand_iterations          6
% 7.38/1.53  --bmc1_ucm_extend_mode                  1
% 7.38/1.53  --bmc1_ucm_init_mode                    2
% 7.38/1.53  --bmc1_ucm_cone_mode                    none
% 7.38/1.53  --bmc1_ucm_reduced_relation_type        0
% 7.38/1.53  --bmc1_ucm_relax_model                  4
% 7.38/1.53  --bmc1_ucm_full_tr_after_sat            true
% 7.38/1.53  --bmc1_ucm_expand_neg_assumptions       false
% 7.38/1.53  --bmc1_ucm_layered_model                none
% 7.38/1.53  --bmc1_ucm_max_lemma_size               10
% 7.38/1.53  
% 7.38/1.53  ------ AIG Options
% 7.38/1.53  
% 7.38/1.53  --aig_mode                              false
% 7.38/1.53  
% 7.38/1.53  ------ Instantiation Options
% 7.38/1.53  
% 7.38/1.53  --instantiation_flag                    true
% 7.38/1.53  --inst_sos_flag                         true
% 7.38/1.53  --inst_sos_phase                        true
% 7.38/1.53  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.38/1.53  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.38/1.53  --inst_lit_sel_side                     none
% 7.38/1.53  --inst_solver_per_active                1400
% 7.38/1.53  --inst_solver_calls_frac                1.
% 7.38/1.53  --inst_passive_queue_type               priority_queues
% 7.38/1.53  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.38/1.53  --inst_passive_queues_freq              [25;2]
% 7.38/1.53  --inst_dismatching                      true
% 7.38/1.53  --inst_eager_unprocessed_to_passive     true
% 7.38/1.53  --inst_prop_sim_given                   true
% 7.38/1.53  --inst_prop_sim_new                     false
% 7.38/1.53  --inst_subs_new                         false
% 7.38/1.53  --inst_eq_res_simp                      false
% 7.38/1.53  --inst_subs_given                       false
% 7.38/1.53  --inst_orphan_elimination               true
% 7.38/1.53  --inst_learning_loop_flag               true
% 7.38/1.53  --inst_learning_start                   3000
% 7.38/1.53  --inst_learning_factor                  2
% 7.38/1.53  --inst_start_prop_sim_after_learn       3
% 7.38/1.53  --inst_sel_renew                        solver
% 7.38/1.53  --inst_lit_activity_flag                true
% 7.38/1.53  --inst_restr_to_given                   false
% 7.38/1.53  --inst_activity_threshold               500
% 7.38/1.53  --inst_out_proof                        true
% 7.38/1.53  
% 7.38/1.53  ------ Resolution Options
% 7.38/1.53  
% 7.38/1.53  --resolution_flag                       false
% 7.38/1.53  --res_lit_sel                           adaptive
% 7.38/1.53  --res_lit_sel_side                      none
% 7.38/1.53  --res_ordering                          kbo
% 7.38/1.53  --res_to_prop_solver                    active
% 7.38/1.53  --res_prop_simpl_new                    false
% 7.38/1.53  --res_prop_simpl_given                  true
% 7.38/1.53  --res_passive_queue_type                priority_queues
% 7.38/1.53  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.38/1.53  --res_passive_queues_freq               [15;5]
% 7.38/1.53  --res_forward_subs                      full
% 7.38/1.53  --res_backward_subs                     full
% 7.38/1.53  --res_forward_subs_resolution           true
% 7.38/1.53  --res_backward_subs_resolution          true
% 7.38/1.53  --res_orphan_elimination                true
% 7.38/1.53  --res_time_limit                        2.
% 7.38/1.53  --res_out_proof                         true
% 7.38/1.53  
% 7.38/1.53  ------ Superposition Options
% 7.38/1.53  
% 7.38/1.53  --superposition_flag                    true
% 7.38/1.53  --sup_passive_queue_type                priority_queues
% 7.38/1.53  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.38/1.53  --sup_passive_queues_freq               [8;1;4]
% 7.38/1.53  --demod_completeness_check              fast
% 7.38/1.53  --demod_use_ground                      true
% 7.38/1.53  --sup_to_prop_solver                    passive
% 7.38/1.53  --sup_prop_simpl_new                    true
% 7.38/1.53  --sup_prop_simpl_given                  true
% 7.38/1.53  --sup_fun_splitting                     true
% 7.38/1.53  --sup_smt_interval                      50000
% 7.38/1.53  
% 7.38/1.53  ------ Superposition Simplification Setup
% 7.38/1.53  
% 7.38/1.53  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.38/1.53  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.38/1.53  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.38/1.53  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.38/1.53  --sup_full_triv                         [TrivRules;PropSubs]
% 7.38/1.53  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.38/1.53  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.38/1.53  --sup_immed_triv                        [TrivRules]
% 7.38/1.53  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.38/1.53  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.38/1.53  --sup_immed_bw_main                     []
% 7.38/1.53  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.38/1.53  --sup_input_triv                        [Unflattening;TrivRules]
% 7.38/1.53  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.38/1.53  --sup_input_bw                          []
% 7.38/1.53  
% 7.38/1.53  ------ Combination Options
% 7.38/1.53  
% 7.38/1.53  --comb_res_mult                         3
% 7.38/1.53  --comb_sup_mult                         2
% 7.38/1.53  --comb_inst_mult                        10
% 7.38/1.53  
% 7.38/1.53  ------ Debug Options
% 7.38/1.53  
% 7.38/1.53  --dbg_backtrace                         false
% 7.38/1.53  --dbg_dump_prop_clauses                 false
% 7.38/1.53  --dbg_dump_prop_clauses_file            -
% 7.38/1.53  --dbg_out_stat                          false
% 7.38/1.53  
% 7.38/1.53  
% 7.38/1.53  
% 7.38/1.53  
% 7.38/1.53  ------ Proving...
% 7.38/1.53  
% 7.38/1.53  
% 7.38/1.53  % SZS status Theorem for theBenchmark.p
% 7.38/1.53  
% 7.38/1.53  % SZS output start CNFRefutation for theBenchmark.p
% 7.38/1.53  
% 7.38/1.53  fof(f11,axiom,(
% 7.38/1.53    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 7.38/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.38/1.53  
% 7.38/1.53  fof(f51,plain,(
% 7.38/1.53    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 7.38/1.53    inference(cnf_transformation,[],[f11])).
% 7.38/1.53  
% 7.38/1.53  fof(f2,axiom,(
% 7.38/1.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.38/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.38/1.53  
% 7.38/1.53  fof(f40,plain,(
% 7.38/1.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.38/1.53    inference(cnf_transformation,[],[f2])).
% 7.38/1.53  
% 7.38/1.53  fof(f25,conjecture,(
% 7.38/1.53    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0),
% 7.38/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.38/1.53  
% 7.38/1.53  fof(f26,negated_conjecture,(
% 7.38/1.53    ~! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0),
% 7.38/1.53    inference(negated_conjecture,[],[f25])).
% 7.38/1.53  
% 7.38/1.53  fof(f30,plain,(
% 7.38/1.53    ? [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) = k1_xboole_0),
% 7.38/1.53    inference(ennf_transformation,[],[f26])).
% 7.38/1.53  
% 7.38/1.53  fof(f37,plain,(
% 7.38/1.53    ? [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 => k2_xboole_0(k1_tarski(sK1),sK2) = k1_xboole_0),
% 7.38/1.53    introduced(choice_axiom,[])).
% 7.38/1.53  
% 7.38/1.53  fof(f38,plain,(
% 7.38/1.53    k2_xboole_0(k1_tarski(sK1),sK2) = k1_xboole_0),
% 7.38/1.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f30,f37])).
% 7.38/1.53  
% 7.38/1.53  fof(f68,plain,(
% 7.38/1.53    k2_xboole_0(k1_tarski(sK1),sK2) = k1_xboole_0),
% 7.38/1.53    inference(cnf_transformation,[],[f38])).
% 7.38/1.53  
% 7.38/1.53  fof(f13,axiom,(
% 7.38/1.53    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)),
% 7.38/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.38/1.53  
% 7.38/1.53  fof(f53,plain,(
% 7.38/1.53    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 7.38/1.53    inference(cnf_transformation,[],[f13])).
% 7.38/1.53  
% 7.38/1.53  fof(f14,axiom,(
% 7.38/1.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 7.38/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.38/1.53  
% 7.38/1.53  fof(f54,plain,(
% 7.38/1.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 7.38/1.53    inference(cnf_transformation,[],[f14])).
% 7.38/1.53  
% 7.38/1.53  fof(f15,axiom,(
% 7.38/1.53    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.38/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.38/1.53  
% 7.38/1.53  fof(f55,plain,(
% 7.38/1.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.38/1.53    inference(cnf_transformation,[],[f15])).
% 7.38/1.53  
% 7.38/1.53  fof(f16,axiom,(
% 7.38/1.53    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.38/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.38/1.53  
% 7.38/1.53  fof(f56,plain,(
% 7.38/1.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.38/1.53    inference(cnf_transformation,[],[f16])).
% 7.38/1.53  
% 7.38/1.53  fof(f17,axiom,(
% 7.38/1.53    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 7.38/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.38/1.53  
% 7.38/1.53  fof(f57,plain,(
% 7.38/1.53    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 7.38/1.53    inference(cnf_transformation,[],[f17])).
% 7.38/1.53  
% 7.38/1.53  fof(f18,axiom,(
% 7.38/1.53    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 7.38/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.38/1.53  
% 7.38/1.53  fof(f58,plain,(
% 7.38/1.53    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 7.38/1.53    inference(cnf_transformation,[],[f18])).
% 7.38/1.53  
% 7.38/1.53  fof(f19,axiom,(
% 7.38/1.53    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 7.38/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.38/1.53  
% 7.38/1.53  fof(f59,plain,(
% 7.38/1.53    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 7.38/1.53    inference(cnf_transformation,[],[f19])).
% 7.38/1.53  
% 7.38/1.53  fof(f20,axiom,(
% 7.38/1.53    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 7.38/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.38/1.53  
% 7.38/1.53  fof(f60,plain,(
% 7.38/1.53    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 7.38/1.53    inference(cnf_transformation,[],[f20])).
% 7.38/1.53  
% 7.38/1.53  fof(f69,plain,(
% 7.38/1.53    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 7.38/1.53    inference(definition_unfolding,[],[f59,f60])).
% 7.38/1.53  
% 7.38/1.53  fof(f70,plain,(
% 7.38/1.53    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 7.38/1.53    inference(definition_unfolding,[],[f58,f69])).
% 7.38/1.53  
% 7.38/1.53  fof(f71,plain,(
% 7.38/1.53    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 7.38/1.53    inference(definition_unfolding,[],[f57,f70])).
% 7.38/1.53  
% 7.38/1.53  fof(f72,plain,(
% 7.38/1.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 7.38/1.53    inference(definition_unfolding,[],[f56,f71])).
% 7.38/1.53  
% 7.38/1.53  fof(f73,plain,(
% 7.38/1.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 7.38/1.53    inference(definition_unfolding,[],[f55,f72])).
% 7.38/1.53  
% 7.38/1.53  fof(f74,plain,(
% 7.38/1.53    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 7.38/1.53    inference(definition_unfolding,[],[f54,f73])).
% 7.38/1.53  
% 7.38/1.53  fof(f79,plain,(
% 7.38/1.53    k5_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)) = k1_xboole_0),
% 7.38/1.53    inference(definition_unfolding,[],[f68,f53,f74])).
% 7.38/1.53  
% 7.38/1.53  fof(f3,axiom,(
% 7.38/1.53    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 7.38/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.38/1.53  
% 7.38/1.53  fof(f41,plain,(
% 7.38/1.53    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 7.38/1.53    inference(cnf_transformation,[],[f3])).
% 7.38/1.53  
% 7.38/1.53  fof(f10,axiom,(
% 7.38/1.53    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 7.38/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.38/1.53  
% 7.38/1.53  fof(f50,plain,(
% 7.38/1.53    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.38/1.53    inference(cnf_transformation,[],[f10])).
% 7.38/1.53  
% 7.38/1.53  fof(f12,axiom,(
% 7.38/1.53    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 7.38/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.38/1.53  
% 7.38/1.53  fof(f52,plain,(
% 7.38/1.53    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 7.38/1.53    inference(cnf_transformation,[],[f12])).
% 7.38/1.53  
% 7.38/1.53  fof(f9,axiom,(
% 7.38/1.53    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 7.38/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.38/1.53  
% 7.38/1.53  fof(f49,plain,(
% 7.38/1.53    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 7.38/1.53    inference(cnf_transformation,[],[f9])).
% 7.38/1.53  
% 7.38/1.53  fof(f6,axiom,(
% 7.38/1.53    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 7.38/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.38/1.53  
% 7.38/1.53  fof(f46,plain,(
% 7.38/1.53    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 7.38/1.53    inference(cnf_transformation,[],[f6])).
% 7.38/1.53  
% 7.38/1.53  fof(f76,plain,(
% 7.38/1.53    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 7.38/1.53    inference(definition_unfolding,[],[f49,f46])).
% 7.38/1.53  
% 7.38/1.53  fof(f7,axiom,(
% 7.38/1.53    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 7.38/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.38/1.53  
% 7.38/1.53  fof(f29,plain,(
% 7.38/1.53    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 7.38/1.53    inference(ennf_transformation,[],[f7])).
% 7.38/1.53  
% 7.38/1.53  fof(f47,plain,(
% 7.38/1.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 7.38/1.53    inference(cnf_transformation,[],[f29])).
% 7.38/1.53  
% 7.38/1.53  fof(f22,axiom,(
% 7.38/1.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 7.38/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.38/1.53  
% 7.38/1.53  fof(f65,plain,(
% 7.38/1.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 7.38/1.53    inference(cnf_transformation,[],[f22])).
% 7.38/1.53  
% 7.38/1.53  fof(f77,plain,(
% 7.38/1.53    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 7.38/1.53    inference(definition_unfolding,[],[f65,f53,f73])).
% 7.38/1.53  
% 7.38/1.53  fof(f24,axiom,(
% 7.38/1.53    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 7.38/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.38/1.53  
% 7.38/1.53  fof(f67,plain,(
% 7.38/1.53    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 7.38/1.53    inference(cnf_transformation,[],[f24])).
% 7.38/1.53  
% 7.38/1.53  fof(f4,axiom,(
% 7.38/1.53    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 7.38/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.38/1.53  
% 7.38/1.53  fof(f27,plain,(
% 7.38/1.53    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 7.38/1.53    inference(rectify,[],[f4])).
% 7.38/1.53  
% 7.38/1.53  fof(f42,plain,(
% 7.38/1.53    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 7.38/1.53    inference(cnf_transformation,[],[f27])).
% 7.38/1.53  
% 7.38/1.53  fof(f75,plain,(
% 7.38/1.53    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),k3_xboole_0(X0,X0)) = X0) )),
% 7.38/1.53    inference(definition_unfolding,[],[f42,f53])).
% 7.38/1.53  
% 7.38/1.53  fof(f5,axiom,(
% 7.38/1.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.38/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.38/1.53  
% 7.38/1.53  fof(f31,plain,(
% 7.38/1.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.38/1.53    inference(nnf_transformation,[],[f5])).
% 7.38/1.53  
% 7.38/1.53  fof(f32,plain,(
% 7.38/1.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.38/1.53    inference(flattening,[],[f31])).
% 7.38/1.53  
% 7.38/1.53  fof(f43,plain,(
% 7.38/1.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.38/1.53    inference(cnf_transformation,[],[f32])).
% 7.38/1.53  
% 7.38/1.53  fof(f81,plain,(
% 7.38/1.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.38/1.53    inference(equality_resolution,[],[f43])).
% 7.38/1.53  
% 7.38/1.53  fof(f1,axiom,(
% 7.38/1.53    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 7.38/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.38/1.53  
% 7.38/1.53  fof(f28,plain,(
% 7.38/1.53    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 7.38/1.53    inference(ennf_transformation,[],[f1])).
% 7.38/1.53  
% 7.38/1.53  fof(f39,plain,(
% 7.38/1.53    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1)) )),
% 7.38/1.53    inference(cnf_transformation,[],[f28])).
% 7.38/1.53  
% 7.38/1.53  fof(f21,axiom,(
% 7.38/1.53    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 7.38/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.38/1.53  
% 7.38/1.53  fof(f33,plain,(
% 7.38/1.53    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 7.38/1.53    inference(nnf_transformation,[],[f21])).
% 7.38/1.53  
% 7.38/1.53  fof(f34,plain,(
% 7.38/1.53    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 7.38/1.53    inference(rectify,[],[f33])).
% 7.38/1.53  
% 7.38/1.53  fof(f35,plain,(
% 7.38/1.53    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 7.38/1.53    introduced(choice_axiom,[])).
% 7.38/1.53  
% 7.38/1.53  fof(f36,plain,(
% 7.38/1.53    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 7.38/1.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).
% 7.38/1.53  
% 7.38/1.53  fof(f62,plain,(
% 7.38/1.53    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 7.38/1.53    inference(cnf_transformation,[],[f36])).
% 7.38/1.53  
% 7.38/1.53  fof(f82,plain,(
% 7.38/1.53    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 7.38/1.53    inference(equality_resolution,[],[f62])).
% 7.38/1.53  
% 7.38/1.53  fof(f23,axiom,(
% 7.38/1.53    k1_tarski(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0)),
% 7.38/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.38/1.53  
% 7.38/1.53  fof(f66,plain,(
% 7.38/1.53    k1_tarski(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0)),
% 7.38/1.53    inference(cnf_transformation,[],[f23])).
% 7.38/1.53  
% 7.38/1.53  fof(f78,plain,(
% 7.38/1.53    k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_zfmisc_1(k1_xboole_0)),
% 7.38/1.53    inference(definition_unfolding,[],[f66,f74])).
% 7.38/1.53  
% 7.38/1.53  cnf(c_11,plain,
% 7.38/1.53      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 7.38/1.53      inference(cnf_transformation,[],[f51]) ).
% 7.38/1.53  
% 7.38/1.53  cnf(c_1,plain,
% 7.38/1.53      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 7.38/1.53      inference(cnf_transformation,[],[f40]) ).
% 7.38/1.53  
% 7.38/1.53  cnf(c_20,negated_conjecture,
% 7.38/1.53      ( k5_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)) = k1_xboole_0 ),
% 7.38/1.53      inference(cnf_transformation,[],[f79]) ).
% 7.38/1.53  
% 7.38/1.53  cnf(c_2,plain,
% 7.38/1.53      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 7.38/1.53      inference(cnf_transformation,[],[f41]) ).
% 7.38/1.53  
% 7.38/1.53  cnf(c_286,negated_conjecture,
% 7.38/1.53      ( k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2))) = k1_xboole_0 ),
% 7.38/1.53      inference(theory_normalisation,[status(thm)],[c_20,c_11,c_2]) ).
% 7.38/1.53  
% 7.38/1.53  cnf(c_1000,plain,
% 7.38/1.53      ( k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) = k1_xboole_0 ),
% 7.38/1.53      inference(demodulation,[status(thm)],[c_1,c_286]) ).
% 7.38/1.53  
% 7.38/1.53  cnf(c_1278,plain,
% 7.38/1.53      ( k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),X0)) = k5_xboole_0(k1_xboole_0,X0) ),
% 7.38/1.53      inference(superposition,[status(thm)],[c_1000,c_11]) ).
% 7.38/1.53  
% 7.38/1.53  cnf(c_10,plain,
% 7.38/1.53      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.38/1.53      inference(cnf_transformation,[],[f50]) ).
% 7.38/1.53  
% 7.38/1.53  cnf(c_1107,plain,
% 7.38/1.53      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 7.38/1.53      inference(superposition,[status(thm)],[c_10,c_2]) ).
% 7.38/1.53  
% 7.38/1.53  cnf(c_1284,plain,
% 7.38/1.53      ( k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),X0)) = X0 ),
% 7.38/1.53      inference(light_normalisation,[status(thm)],[c_1278,c_1107]) ).
% 7.38/1.53  
% 7.38/1.53  cnf(c_1549,plain,
% 7.38/1.53      ( k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k3_xboole_0(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),X0))) = X0 ),
% 7.38/1.53      inference(superposition,[status(thm)],[c_11,c_1284]) ).
% 7.38/1.53  
% 7.38/1.53  cnf(c_12,plain,
% 7.38/1.53      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 7.38/1.53      inference(cnf_transformation,[],[f52]) ).
% 7.38/1.53  
% 7.38/1.53  cnf(c_1547,plain,
% 7.38/1.53      ( k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k5_xboole_0(sK2,k1_xboole_0) ),
% 7.38/1.53      inference(superposition,[status(thm)],[c_12,c_1284]) ).
% 7.38/1.53  
% 7.38/1.53  cnf(c_1553,plain,
% 7.38/1.53      ( k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = sK2 ),
% 7.38/1.53      inference(demodulation,[status(thm)],[c_1547,c_10]) ).
% 7.38/1.53  
% 7.38/1.53  cnf(c_1557,plain,
% 7.38/1.53      ( k5_xboole_0(sK2,k5_xboole_0(sK2,X0)) = X0 ),
% 7.38/1.53      inference(demodulation,[status(thm)],[c_1553,c_1284]) ).
% 7.38/1.53  
% 7.38/1.53  cnf(c_1718,plain,
% 7.38/1.53      ( k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k3_xboole_0(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),X0)) = k5_xboole_0(sK2,X0) ),
% 7.38/1.53      inference(superposition,[status(thm)],[c_1549,c_1557]) ).
% 7.38/1.53  
% 7.38/1.53  cnf(c_1559,plain,
% 7.38/1.53      ( k5_xboole_0(sK2,k5_xboole_0(X0,sK2)) = X0 ),
% 7.38/1.53      inference(superposition,[status(thm)],[c_2,c_1557]) ).
% 7.38/1.53  
% 7.38/1.53  cnf(c_1565,plain,
% 7.38/1.53      ( k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK2,X0),X1)) = k5_xboole_0(X0,X1) ),
% 7.38/1.53      inference(superposition,[status(thm)],[c_1557,c_11]) ).
% 7.38/1.53  
% 7.38/1.53  cnf(c_1855,plain,
% 7.38/1.53      ( k5_xboole_0(X0,k5_xboole_0(sK2,X0)) = k5_xboole_0(sK2,k1_xboole_0) ),
% 7.38/1.53      inference(superposition,[status(thm)],[c_12,c_1565]) ).
% 7.38/1.53  
% 7.38/1.53  cnf(c_1878,plain,
% 7.38/1.53      ( k5_xboole_0(X0,k5_xboole_0(sK2,X0)) = sK2 ),
% 7.38/1.53      inference(demodulation,[status(thm)],[c_1855,c_10]) ).
% 7.38/1.53  
% 7.38/1.53  cnf(c_2293,plain,
% 7.38/1.53      ( k5_xboole_0(k5_xboole_0(X0,sK2),X0) = sK2 ),
% 7.38/1.53      inference(superposition,[status(thm)],[c_1559,c_1878]) ).
% 7.38/1.53  
% 7.38/1.53  cnf(c_4291,plain,
% 7.38/1.53      ( k5_xboole_0(k5_xboole_0(X0,sK2),k5_xboole_0(X0,X1)) = k5_xboole_0(sK2,X1) ),
% 7.38/1.53      inference(superposition,[status(thm)],[c_2293,c_11]) ).
% 7.38/1.53  
% 7.38/1.53  cnf(c_11539,plain,
% 7.38/1.53      ( k5_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2),k5_xboole_0(sK2,X0)) = k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),X0)) ),
% 7.38/1.53      inference(superposition,[status(thm)],[c_1718,c_4291]) ).
% 7.38/1.53  
% 7.38/1.53  cnf(c_2284,plain,
% 7.38/1.53      ( k5_xboole_0(X0,k5_xboole_0(X0,sK2)) = sK2 ),
% 7.38/1.53      inference(superposition,[status(thm)],[c_2,c_1878]) ).
% 7.38/1.53  
% 7.38/1.53  cnf(c_3479,plain,
% 7.38/1.53      ( k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),sK2)) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2) ),
% 7.38/1.53      inference(superposition,[status(thm)],[c_2284,c_1718]) ).
% 7.38/1.53  
% 7.38/1.53  cnf(c_3485,plain,
% 7.38/1.53      ( k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2) = k3_xboole_0(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
% 7.38/1.53      inference(demodulation,[status(thm)],[c_3479,c_1559]) ).
% 7.38/1.53  
% 7.38/1.53  cnf(c_1712,plain,
% 7.38/1.53      ( k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(X0,k3_xboole_0(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))) = X0 ),
% 7.38/1.53      inference(superposition,[status(thm)],[c_2,c_1549]) ).
% 7.38/1.53  
% 7.38/1.53  cnf(c_3338,plain,
% 7.38/1.53      ( k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(X0,k3_xboole_0(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) = k5_xboole_0(sK2,X0) ),
% 7.38/1.53      inference(superposition,[status(thm)],[c_1712,c_1557]) ).
% 7.38/1.53  
% 7.38/1.53  cnf(c_2292,plain,
% 7.38/1.53      ( k5_xboole_0(k5_xboole_0(sK2,X0),X0) = sK2 ),
% 7.38/1.53      inference(superposition,[status(thm)],[c_1557,c_1878]) ).
% 7.38/1.53  
% 7.38/1.53  cnf(c_2807,plain,
% 7.38/1.53      ( k5_xboole_0(k5_xboole_0(sK2,X0),k5_xboole_0(X0,X1)) = k5_xboole_0(sK2,X1) ),
% 7.38/1.53      inference(superposition,[status(thm)],[c_2292,c_11]) ).
% 7.38/1.53  
% 7.38/1.53  cnf(c_5986,plain,
% 7.38/1.53      ( k5_xboole_0(k5_xboole_0(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_xboole_0(sK2,X0)) = k5_xboole_0(sK2,k5_xboole_0(X0,k3_xboole_0(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) ),
% 7.38/1.53      inference(superposition,[status(thm)],[c_3338,c_2807]) ).
% 7.38/1.53  
% 7.38/1.53  cnf(c_1714,plain,
% 7.38/1.53      ( k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_xboole_0)) = k3_xboole_0(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
% 7.38/1.53      inference(superposition,[status(thm)],[c_12,c_1549]) ).
% 7.38/1.53  
% 7.38/1.53  cnf(c_1729,plain,
% 7.38/1.53      ( k5_xboole_0(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k3_xboole_0(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
% 7.38/1.53      inference(demodulation,[status(thm)],[c_1714,c_10]) ).
% 7.38/1.53  
% 7.38/1.53  cnf(c_2325,plain,
% 7.38/1.53      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(sK2,X0),sK2)) = k5_xboole_0(sK2,sK2) ),
% 7.38/1.53      inference(superposition,[status(thm)],[c_2284,c_1565]) ).
% 7.38/1.53  
% 7.38/1.53  cnf(c_2295,plain,
% 7.38/1.53      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(sK2,X0),X1)) = k5_xboole_0(sK2,X1) ),
% 7.38/1.53      inference(superposition,[status(thm)],[c_1878,c_11]) ).
% 7.38/1.53  
% 7.38/1.53  cnf(c_2326,plain,
% 7.38/1.53      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(sK2,X0),sK2)) = k1_xboole_0 ),
% 7.38/1.53      inference(demodulation,[status(thm)],[c_2325,c_12,c_2295]) ).
% 7.38/1.53  
% 7.38/1.53  cnf(c_597,plain,
% 7.38/1.53      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
% 7.38/1.53      inference(superposition,[status(thm)],[c_11,c_2]) ).
% 7.38/1.53  
% 7.38/1.53  cnf(c_5420,plain,
% 7.38/1.53      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(sK2,X0),sK2))) = k5_xboole_0(X1,k1_xboole_0) ),
% 7.38/1.53      inference(superposition,[status(thm)],[c_2326,c_597]) ).
% 7.38/1.53  
% 7.38/1.53  cnf(c_1853,plain,
% 7.38/1.53      ( k5_xboole_0(sK2,k5_xboole_0(X0,k5_xboole_0(sK2,X1))) = k5_xboole_0(X1,X0) ),
% 7.38/1.53      inference(superposition,[status(thm)],[c_2,c_1565]) ).
% 7.38/1.53  
% 7.38/1.53  cnf(c_5484,plain,
% 7.38/1.53      ( k5_xboole_0(sK2,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(sK2,X2)))) = k5_xboole_0(k5_xboole_0(X1,X2),X0) ),
% 7.38/1.53      inference(superposition,[status(thm)],[c_597,c_1853]) ).
% 7.38/1.53  
% 7.38/1.53  cnf(c_4858,plain,
% 7.38/1.53      ( k5_xboole_0(sK2,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(sK2,X2)))) = k5_xboole_0(X2,k5_xboole_0(X0,X1)) ),
% 7.38/1.53      inference(superposition,[status(thm)],[c_11,c_1853]) ).
% 7.38/1.53  
% 7.38/1.53  cnf(c_5495,plain,
% 7.38/1.53      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
% 7.38/1.53      inference(light_normalisation,[status(thm)],[c_5484,c_4858]) ).
% 7.38/1.53  
% 7.38/1.53  cnf(c_5581,plain,
% 7.38/1.53      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(sK2,sK2)))) = k5_xboole_0(X1,k1_xboole_0) ),
% 7.38/1.53      inference(demodulation,[status(thm)],[c_5420,c_5495]) ).
% 7.38/1.53  
% 7.38/1.53  cnf(c_5582,plain,
% 7.38/1.53      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
% 7.38/1.53      inference(demodulation,[status(thm)],[c_5581,c_10,c_12]) ).
% 7.38/1.53  
% 7.38/1.53  cnf(c_5757,plain,
% 7.38/1.53      ( k5_xboole_0(sK2,k5_xboole_0(X0,k3_xboole_0(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0) ),
% 7.38/1.53      inference(superposition,[status(thm)],[c_5582,c_1718]) ).
% 7.38/1.53  
% 7.38/1.53  cnf(c_6045,plain,
% 7.38/1.53      ( k5_xboole_0(k3_xboole_0(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_xboole_0(sK2,X0)) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0) ),
% 7.38/1.53      inference(light_normalisation,[status(thm)],[c_5986,c_1729,c_5757]) ).
% 7.38/1.53  
% 7.38/1.53  cnf(c_9,plain,
% 7.38/1.53      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
% 7.38/1.53      inference(cnf_transformation,[],[f76]) ).
% 7.38/1.53  
% 7.38/1.53  cnf(c_581,plain,
% 7.38/1.53      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
% 7.38/1.53      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.38/1.53  
% 7.38/1.53  cnf(c_2595,plain,
% 7.38/1.53      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X0) = iProver_top ),
% 7.38/1.53      inference(superposition,[status(thm)],[c_1,c_581]) ).
% 7.38/1.53  
% 7.38/1.53  cnf(c_4061,plain,
% 7.38/1.53      ( r1_tarski(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = iProver_top ),
% 7.38/1.53      inference(superposition,[status(thm)],[c_1553,c_2595]) ).
% 7.38/1.53  
% 7.38/1.53  cnf(c_7,plain,
% 7.38/1.53      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 7.38/1.53      inference(cnf_transformation,[],[f47]) ).
% 7.38/1.53  
% 7.38/1.53  cnf(c_583,plain,
% 7.38/1.53      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 7.38/1.53      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.38/1.53  
% 7.38/1.53  cnf(c_10573,plain,
% 7.38/1.53      ( k3_xboole_0(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = sK2 ),
% 7.38/1.53      inference(superposition,[status(thm)],[c_4061,c_583]) ).
% 7.38/1.53  
% 7.38/1.53  cnf(c_11673,plain,
% 7.38/1.53      ( k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0) = X0 ),
% 7.38/1.53      inference(light_normalisation,
% 7.38/1.53                [status(thm)],
% 7.38/1.53                [c_11539,c_1557,c_3485,c_6045,c_10573]) ).
% 7.38/1.53  
% 7.38/1.53  cnf(c_11815,plain,
% 7.38/1.53      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k1_xboole_0 ),
% 7.38/1.53      inference(superposition,[status(thm)],[c_11673,c_10]) ).
% 7.38/1.53  
% 7.38/1.53  cnf(c_17,plain,
% 7.38/1.53      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
% 7.38/1.53      inference(cnf_transformation,[],[f77]) ).
% 7.38/1.53  
% 7.38/1.53  cnf(c_287,plain,
% 7.38/1.53      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) ),
% 7.38/1.53      inference(theory_normalisation,[status(thm)],[c_17,c_11,c_2]) ).
% 7.38/1.53  
% 7.38/1.53  cnf(c_1104,plain,
% 7.38/1.53      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
% 7.38/1.53      inference(superposition,[status(thm)],[c_1,c_287]) ).
% 7.38/1.53  
% 7.38/1.53  cnf(c_14070,plain,
% 7.38/1.53      ( k5_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK1,sK1))) = k3_tarski(k1_xboole_0) ),
% 7.38/1.53      inference(superposition,[status(thm)],[c_11815,c_1104]) ).
% 7.38/1.53  
% 7.38/1.53  cnf(c_19,plain,
% 7.38/1.53      ( k3_tarski(k1_xboole_0) = k1_xboole_0 ),
% 7.38/1.53      inference(cnf_transformation,[],[f67]) ).
% 7.38/1.53  
% 7.38/1.53  cnf(c_14072,plain,
% 7.38/1.53      ( k5_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK1,sK1))) = k1_xboole_0 ),
% 7.38/1.53      inference(light_normalisation,[status(thm)],[c_14070,c_19]) ).
% 7.38/1.53  
% 7.38/1.53  cnf(c_3,plain,
% 7.38/1.53      ( k5_xboole_0(k5_xboole_0(X0,X0),k3_xboole_0(X0,X0)) = X0 ),
% 7.38/1.53      inference(cnf_transformation,[],[f75]) ).
% 7.38/1.53  
% 7.38/1.53  cnf(c_288,plain,
% 7.38/1.53      ( k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))) = X0 ),
% 7.38/1.53      inference(theory_normalisation,[status(thm)],[c_3,c_11,c_2]) ).
% 7.38/1.53  
% 7.38/1.53  cnf(c_6,plain,
% 7.38/1.53      ( r1_tarski(X0,X0) ),
% 7.38/1.53      inference(cnf_transformation,[],[f81]) ).
% 7.38/1.53  
% 7.38/1.53  cnf(c_584,plain,
% 7.38/1.53      ( r1_tarski(X0,X0) = iProver_top ),
% 7.38/1.53      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.38/1.53  
% 7.38/1.53  cnf(c_3665,plain,
% 7.38/1.53      ( k3_xboole_0(X0,X0) = X0 ),
% 7.38/1.53      inference(superposition,[status(thm)],[c_584,c_583]) ).
% 7.38/1.53  
% 7.38/1.53  cnf(c_14073,plain,
% 7.38/1.53      ( sK1 = k1_xboole_0 ),
% 7.38/1.53      inference(demodulation,
% 7.38/1.53                [status(thm)],
% 7.38/1.53                [c_14072,c_10,c_12,c_288,c_3665]) ).
% 7.38/1.53  
% 7.38/1.53  cnf(c_14074,plain,
% 7.38/1.53      ( k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 7.38/1.53      inference(demodulation,[status(thm)],[c_14073,c_11815]) ).
% 7.38/1.53  
% 7.38/1.53  cnf(c_292,plain,
% 7.38/1.53      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.38/1.53      theory(equality) ).
% 7.38/1.53  
% 7.38/1.53  cnf(c_611,plain,
% 7.38/1.53      ( r2_hidden(X0,X1)
% 7.38/1.53      | ~ r2_hidden(X2,k1_zfmisc_1(X3))
% 7.38/1.53      | X0 != X2
% 7.38/1.53      | X1 != k1_zfmisc_1(X3) ),
% 7.38/1.53      inference(instantiation,[status(thm)],[c_292]) ).
% 7.38/1.53  
% 7.38/1.53  cnf(c_641,plain,
% 7.38/1.53      ( r2_hidden(X0,k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
% 7.38/1.53      | ~ r2_hidden(X1,k1_zfmisc_1(k1_xboole_0))
% 7.38/1.53      | X0 != X1
% 7.38/1.53      | k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_zfmisc_1(k1_xboole_0) ),
% 7.38/1.53      inference(instantiation,[status(thm)],[c_611]) ).
% 7.38/1.53  
% 7.38/1.53  cnf(c_2772,plain,
% 7.38/1.53      ( ~ r2_hidden(X0,k1_zfmisc_1(k1_xboole_0))
% 7.38/1.53      | r2_hidden(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
% 7.38/1.53      | k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != X0
% 7.38/1.53      | k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_zfmisc_1(k1_xboole_0) ),
% 7.38/1.53      inference(instantiation,[status(thm)],[c_641]) ).
% 7.38/1.53  
% 7.38/1.53  cnf(c_6331,plain,
% 7.38/1.53      ( r2_hidden(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
% 7.38/1.54      | ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
% 7.38/1.54      | k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_zfmisc_1(k1_xboole_0)
% 7.38/1.54      | k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
% 7.38/1.54      inference(instantiation,[status(thm)],[c_2772]) ).
% 7.38/1.54  
% 7.38/1.54  cnf(c_0,plain,
% 7.38/1.54      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X1,X0) ),
% 7.38/1.54      inference(cnf_transformation,[],[f39]) ).
% 7.38/1.54  
% 7.38/1.54  cnf(c_1505,plain,
% 7.38/1.54      ( ~ r2_hidden(X0,k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
% 7.38/1.54      | ~ r2_hidden(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),X0) ),
% 7.38/1.54      inference(instantiation,[status(thm)],[c_0]) ).
% 7.38/1.54  
% 7.38/1.54  cnf(c_2771,plain,
% 7.38/1.54      ( ~ r2_hidden(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
% 7.38/1.54      inference(instantiation,[status(thm)],[c_1505]) ).
% 7.38/1.54  
% 7.38/1.54  cnf(c_922,plain,
% 7.38/1.54      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 7.38/1.54      inference(instantiation,[status(thm)],[c_6]) ).
% 7.38/1.54  
% 7.38/1.54  cnf(c_15,plain,
% 7.38/1.54      ( ~ r1_tarski(X0,X1) | r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 7.38/1.54      inference(cnf_transformation,[],[f82]) ).
% 7.38/1.54  
% 7.38/1.54  cnf(c_667,plain,
% 7.38/1.54      ( ~ r1_tarski(X0,k1_xboole_0)
% 7.38/1.54      | r2_hidden(X0,k1_zfmisc_1(k1_xboole_0)) ),
% 7.38/1.54      inference(instantiation,[status(thm)],[c_15]) ).
% 7.38/1.54  
% 7.38/1.54  cnf(c_753,plain,
% 7.38/1.54      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 7.38/1.54      | r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
% 7.38/1.54      inference(instantiation,[status(thm)],[c_667]) ).
% 7.38/1.54  
% 7.38/1.54  cnf(c_18,plain,
% 7.38/1.54      ( k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_zfmisc_1(k1_xboole_0) ),
% 7.38/1.54      inference(cnf_transformation,[],[f78]) ).
% 7.38/1.54  
% 7.38/1.54  cnf(contradiction,plain,
% 7.38/1.54      ( $false ),
% 7.38/1.54      inference(minisat,
% 7.38/1.54                [status(thm)],
% 7.38/1.54                [c_14074,c_6331,c_2771,c_922,c_753,c_18]) ).
% 7.38/1.54  
% 7.38/1.54  
% 7.38/1.54  % SZS output end CNFRefutation for theBenchmark.p
% 7.38/1.54  
% 7.38/1.54  ------                               Statistics
% 7.38/1.54  
% 7.38/1.54  ------ General
% 7.38/1.54  
% 7.38/1.54  abstr_ref_over_cycles:                  0
% 7.38/1.54  abstr_ref_under_cycles:                 0
% 7.38/1.54  gc_basic_clause_elim:                   0
% 7.38/1.54  forced_gc_time:                         0
% 7.38/1.54  parsing_time:                           0.009
% 7.38/1.54  unif_index_cands_time:                  0.
% 7.38/1.54  unif_index_add_time:                    0.
% 7.38/1.54  orderings_time:                         0.
% 7.38/1.54  out_proof_time:                         0.007
% 7.38/1.54  total_time:                             0.573
% 7.38/1.54  num_of_symbols:                         42
% 7.38/1.54  num_of_terms:                           26586
% 7.38/1.54  
% 7.38/1.54  ------ Preprocessing
% 7.38/1.54  
% 7.38/1.54  num_of_splits:                          0
% 7.38/1.54  num_of_split_atoms:                     0
% 7.38/1.54  num_of_reused_defs:                     0
% 7.38/1.54  num_eq_ax_congr_red:                    9
% 7.38/1.54  num_of_sem_filtered_clauses:            1
% 7.38/1.54  num_of_subtypes:                        0
% 7.38/1.54  monotx_restored_types:                  0
% 7.38/1.54  sat_num_of_epr_types:                   0
% 7.38/1.54  sat_num_of_non_cyclic_types:            0
% 7.38/1.54  sat_guarded_non_collapsed_types:        0
% 7.38/1.54  num_pure_diseq_elim:                    0
% 7.38/1.54  simp_replaced_by:                       0
% 7.38/1.54  res_preprocessed:                       99
% 7.38/1.54  prep_upred:                             0
% 7.38/1.54  prep_unflattend:                        0
% 7.38/1.54  smt_new_axioms:                         0
% 7.38/1.54  pred_elim_cands:                        2
% 7.38/1.54  pred_elim:                              0
% 7.38/1.54  pred_elim_cl:                           0
% 7.38/1.54  pred_elim_cycles:                       2
% 7.38/1.54  merged_defs:                            8
% 7.38/1.54  merged_defs_ncl:                        0
% 7.38/1.54  bin_hyper_res:                          8
% 7.38/1.54  prep_cycles:                            4
% 7.38/1.54  pred_elim_time:                         0.001
% 7.38/1.54  splitting_time:                         0.
% 7.38/1.54  sem_filter_time:                        0.
% 7.38/1.54  monotx_time:                            0.
% 7.38/1.54  subtype_inf_time:                       0.
% 7.38/1.54  
% 7.38/1.54  ------ Problem properties
% 7.38/1.54  
% 7.38/1.54  clauses:                                20
% 7.38/1.54  conjectures:                            1
% 7.38/1.54  epr:                                    4
% 7.38/1.54  horn:                                   19
% 7.38/1.54  ground:                                 3
% 7.38/1.54  unary:                                  13
% 7.38/1.54  binary:                                 4
% 7.38/1.54  lits:                                   30
% 7.38/1.54  lits_eq:                                14
% 7.38/1.54  fd_pure:                                0
% 7.38/1.54  fd_pseudo:                              0
% 7.38/1.54  fd_cond:                                0
% 7.38/1.54  fd_pseudo_cond:                         3
% 7.38/1.54  ac_symbols:                             1
% 7.38/1.54  
% 7.38/1.54  ------ Propositional Solver
% 7.38/1.54  
% 7.38/1.54  prop_solver_calls:                      30
% 7.38/1.54  prop_fast_solver_calls:                 463
% 7.38/1.54  smt_solver_calls:                       0
% 7.38/1.54  smt_fast_solver_calls:                  0
% 7.38/1.54  prop_num_of_clauses:                    4069
% 7.38/1.54  prop_preprocess_simplified:             6269
% 7.38/1.54  prop_fo_subsumed:                       0
% 7.38/1.54  prop_solver_time:                       0.
% 7.38/1.54  smt_solver_time:                        0.
% 7.38/1.54  smt_fast_solver_time:                   0.
% 7.38/1.54  prop_fast_solver_time:                  0.
% 7.38/1.54  prop_unsat_core_time:                   0.
% 7.38/1.54  
% 7.38/1.54  ------ QBF
% 7.38/1.54  
% 7.38/1.54  qbf_q_res:                              0
% 7.38/1.54  qbf_num_tautologies:                    0
% 7.38/1.54  qbf_prep_cycles:                        0
% 7.38/1.54  
% 7.38/1.54  ------ BMC1
% 7.38/1.54  
% 7.38/1.54  bmc1_current_bound:                     -1
% 7.38/1.54  bmc1_last_solved_bound:                 -1
% 7.38/1.54  bmc1_unsat_core_size:                   -1
% 7.38/1.54  bmc1_unsat_core_parents_size:           -1
% 7.38/1.54  bmc1_merge_next_fun:                    0
% 7.38/1.54  bmc1_unsat_core_clauses_time:           0.
% 7.38/1.54  
% 7.38/1.54  ------ Instantiation
% 7.38/1.54  
% 7.38/1.54  inst_num_of_clauses:                    747
% 7.38/1.54  inst_num_in_passive:                    178
% 7.38/1.54  inst_num_in_active:                     352
% 7.38/1.54  inst_num_in_unprocessed:                217
% 7.38/1.54  inst_num_of_loops:                      420
% 7.38/1.54  inst_num_of_learning_restarts:          0
% 7.38/1.54  inst_num_moves_active_passive:          65
% 7.38/1.54  inst_lit_activity:                      0
% 7.38/1.54  inst_lit_activity_moves:                0
% 7.38/1.54  inst_num_tautologies:                   0
% 7.38/1.54  inst_num_prop_implied:                  0
% 7.38/1.54  inst_num_existing_simplified:           0
% 7.38/1.54  inst_num_eq_res_simplified:             0
% 7.38/1.54  inst_num_child_elim:                    0
% 7.38/1.54  inst_num_of_dismatching_blockings:      735
% 7.38/1.54  inst_num_of_non_proper_insts:           1510
% 7.38/1.54  inst_num_of_duplicates:                 0
% 7.38/1.54  inst_inst_num_from_inst_to_res:         0
% 7.38/1.54  inst_dismatching_checking_time:         0.
% 7.38/1.54  
% 7.38/1.54  ------ Resolution
% 7.38/1.54  
% 7.38/1.54  res_num_of_clauses:                     0
% 7.38/1.54  res_num_in_passive:                     0
% 7.38/1.54  res_num_in_active:                      0
% 7.38/1.54  res_num_of_loops:                       103
% 7.38/1.54  res_forward_subset_subsumed:            171
% 7.38/1.54  res_backward_subset_subsumed:           2
% 7.38/1.54  res_forward_subsumed:                   0
% 7.38/1.54  res_backward_subsumed:                  0
% 7.38/1.54  res_forward_subsumption_resolution:     0
% 7.38/1.54  res_backward_subsumption_resolution:    0
% 7.38/1.54  res_clause_to_clause_subsumption:       12970
% 7.38/1.54  res_orphan_elimination:                 0
% 7.38/1.54  res_tautology_del:                      143
% 7.38/1.54  res_num_eq_res_simplified:              0
% 7.38/1.54  res_num_sel_changes:                    0
% 7.38/1.54  res_moves_from_active_to_pass:          0
% 7.38/1.54  
% 7.38/1.54  ------ Superposition
% 7.38/1.54  
% 7.38/1.54  sup_time_total:                         0.
% 7.38/1.54  sup_time_generating:                    0.
% 7.38/1.54  sup_time_sim_full:                      0.
% 7.38/1.54  sup_time_sim_immed:                     0.
% 7.38/1.54  
% 7.38/1.54  sup_num_of_clauses:                     1083
% 7.38/1.54  sup_num_in_active:                      60
% 7.38/1.54  sup_num_in_passive:                     1023
% 7.38/1.54  sup_num_of_loops:                       82
% 7.38/1.54  sup_fw_superposition:                   2582
% 7.38/1.54  sup_bw_superposition:                   1811
% 7.38/1.54  sup_immediate_simplified:               1833
% 7.38/1.54  sup_given_eliminated:                   6
% 7.38/1.54  comparisons_done:                       0
% 7.38/1.54  comparisons_avoided:                    0
% 7.38/1.54  
% 7.38/1.54  ------ Simplifications
% 7.38/1.54  
% 7.38/1.54  
% 7.38/1.54  sim_fw_subset_subsumed:                 0
% 7.38/1.54  sim_bw_subset_subsumed:                 0
% 7.38/1.54  sim_fw_subsumed:                        147
% 7.38/1.54  sim_bw_subsumed:                        12
% 7.38/1.54  sim_fw_subsumption_res:                 0
% 7.38/1.54  sim_bw_subsumption_res:                 0
% 7.38/1.54  sim_tautology_del:                      0
% 7.38/1.54  sim_eq_tautology_del:                   531
% 7.38/1.54  sim_eq_res_simp:                        0
% 7.38/1.54  sim_fw_demodulated:                     1740
% 7.38/1.54  sim_bw_demodulated:                     116
% 7.38/1.54  sim_light_normalised:                   681
% 7.38/1.54  sim_joinable_taut:                      116
% 7.38/1.54  sim_joinable_simp:                      0
% 7.38/1.54  sim_ac_normalised:                      0
% 7.38/1.54  sim_smt_subsumption:                    0
% 7.38/1.54  
%------------------------------------------------------------------------------
