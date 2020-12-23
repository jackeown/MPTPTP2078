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
% DateTime   : Thu Dec  3 11:34:03 EST 2020

% Result     : Theorem 7.68s
% Output     : CNFRefutation 7.68s
% Verified   : 
% Statistics : Number of formulae       :  185 (8321 expanded)
%              Number of clauses        :  108 (2288 expanded)
%              Number of leaves         :   33 (2415 expanded)
%              Depth                    :   39
%              Number of atoms          :  288 (8568 expanded)
%              Number of equality atoms :  182 (8441 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :   10 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f26,conjecture,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,negated_conjecture,(
    ~ ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(negated_conjecture,[],[f26])).

fof(f32,plain,(
    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1) ),
    inference(ennf_transformation,[],[f27])).

fof(f39,plain,
    ( ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1)
   => k1_xboole_0 = k2_xboole_0(k1_tarski(sK2),sK3) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    k1_xboole_0 = k2_xboole_0(k1_tarski(sK2),sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f32,f39])).

fof(f70,plain,(
    k1_xboole_0 = k2_xboole_0(k1_tarski(sK2),sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f14,axiom,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f18])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f19])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f20])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f21])).

fof(f71,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f61,f62])).

fof(f72,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f60,f71])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f59,f72])).

fof(f74,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f58,f73])).

fof(f75,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f57,f74])).

fof(f76,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f56,f75])).

fof(f80,plain,(
    k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f70,f55,f76])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f10,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f13,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f13])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f4,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f77,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f49,f45])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f23,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f78,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f67,f55,f75])).

fof(f25,axiom,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f25])).

fof(f7,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f33])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f11,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f9,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f50,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f36,plain,(
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
    inference(rectify,[],[f35])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK1(X0,X1),X0)
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( r1_tarski(sK1(X0,X1),X0)
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK1(X0,X1),X0)
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( r1_tarski(sK1(X0,X1),X0)
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f36,f37])).

fof(f64,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f81,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f64])).

fof(f24,axiom,(
    k1_tarski(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    k1_tarski(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f24])).

fof(f79,plain,(
    k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_zfmisc_1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f68,f76])).

cnf(c_11,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_20,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_663,negated_conjecture,
    ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))) = k1_xboole_0 ),
    inference(theory_normalisation,[status(thm)],[c_20,c_11,c_1])).

cnf(c_1211,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_0,c_663])).

cnf(c_1370,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),X0)) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_1211,c_11])).

cnf(c_9,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1257,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_9,c_1])).

cnf(c_1376,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1370,c_1257])).

cnf(c_1508,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X0))) = X0 ),
    inference(superposition,[status(thm)],[c_11,c_1376])).

cnf(c_12,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1509,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = k5_xboole_0(sK3,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_12,c_1376])).

cnf(c_1513,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = sK3 ),
    inference(demodulation,[status(thm)],[c_1509,c_9])).

cnf(c_1517,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(sK3,X0)) = X0 ),
    inference(demodulation,[status(thm)],[c_1513,c_1376])).

cnf(c_1610,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X0)) = k5_xboole_0(sK3,X0) ),
    inference(superposition,[status(thm)],[c_1508,c_1517])).

cnf(c_1525,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(sK3,X0),X1)) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1517,c_11])).

cnf(c_1720,plain,
    ( k5_xboole_0(X0,k5_xboole_0(sK3,X0)) = k5_xboole_0(sK3,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_12,c_1525])).

cnf(c_1740,plain,
    ( k5_xboole_0(X0,k5_xboole_0(sK3,X0)) = sK3 ),
    inference(demodulation,[status(thm)],[c_1720,c_9])).

cnf(c_2047,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(sK3,X0),X1)) = k5_xboole_0(sK3,X1) ),
    inference(superposition,[status(thm)],[c_1740,c_11])).

cnf(c_2044,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,X0),X0) = sK3 ),
    inference(superposition,[status(thm)],[c_1517,c_1740])).

cnf(c_2149,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,X0),k5_xboole_0(X0,X1)) = k5_xboole_0(sK3,X1) ),
    inference(superposition,[status(thm)],[c_2044,c_11])).

cnf(c_1716,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(X0,k5_xboole_0(sK3,X1))) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1,c_1525])).

cnf(c_2901,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,k5_xboole_0(sK3,X0))) = sK3 ),
    inference(superposition,[status(thm)],[c_1716,c_2044])).

cnf(c_4245,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,X0),k5_xboole_0(k5_xboole_0(X1,X0),k5_xboole_0(sK3,k5_xboole_0(sK3,X1)))) = sK3 ),
    inference(superposition,[status(thm)],[c_2149,c_2901])).

cnf(c_4317,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,X0),k5_xboole_0(k5_xboole_0(X1,X0),X1)) = sK3 ),
    inference(demodulation,[status(thm)],[c_4245,c_1517])).

cnf(c_4464,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,X1),X0)) = k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(sK3,X1)),sK3) ),
    inference(superposition,[status(thm)],[c_4317,c_2149])).

cnf(c_4487,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,X1),X0)) = k5_xboole_0(X1,sK3) ),
    inference(demodulation,[status(thm)],[c_4464,c_1517])).

cnf(c_4841,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(sK3,X0),X1)) = k5_xboole_0(X1,sK3) ),
    inference(superposition,[status(thm)],[c_4487,c_1716])).

cnf(c_979,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_11,c_1])).

cnf(c_5299,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,X0),k5_xboole_0(X1,X0)) = k5_xboole_0(X1,sK3) ),
    inference(superposition,[status(thm)],[c_2044,c_979])).

cnf(c_980,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_11,c_1])).

cnf(c_6834,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(sK3,X1),X2)) = k5_xboole_0(X2,k5_xboole_0(X0,sK3)) ),
    inference(superposition,[status(thm)],[c_5299,c_980])).

cnf(c_4835,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X0) = k5_xboole_0(sK3,k5_xboole_0(X1,sK3)) ),
    inference(superposition,[status(thm)],[c_4487,c_1517])).

cnf(c_1519,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(X0,sK3)) = X0 ),
    inference(superposition,[status(thm)],[c_1,c_1517])).

cnf(c_4845,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X0) = X1 ),
    inference(demodulation,[status(thm)],[c_4835,c_1519])).

cnf(c_4959,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(superposition,[status(thm)],[c_4845,c_11])).

cnf(c_6123,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X2)) = k5_xboole_0(X2,X0) ),
    inference(superposition,[status(thm)],[c_4959,c_980])).

cnf(c_6187,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,sK3)),X2)) = k5_xboole_0(k5_xboole_0(X1,X0),X2) ),
    inference(superposition,[status(thm)],[c_980,c_1525])).

cnf(c_1615,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(X0,k5_xboole_0(X1,sK3))) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_11,c_1519])).

cnf(c_2740,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,sK3)),X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_1615,c_11])).

cnf(c_2747,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,sK3)),X2)) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_2740,c_11])).

cnf(c_6223,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
    inference(light_normalisation,[status(thm)],[c_6187,c_2747])).

cnf(c_6865,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,X0),X1) = k5_xboole_0(X0,k5_xboole_0(X1,sK3)) ),
    inference(demodulation,[status(thm)],[c_6834,c_6123,c_6223])).

cnf(c_7696,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,sK3))) = k5_xboole_0(sK3,X1) ),
    inference(light_normalisation,[status(thm)],[c_2047,c_4841,c_6865])).

cnf(c_7718,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(sK3,sK3)) = k5_xboole_0(sK3,k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) ),
    inference(superposition,[status(thm)],[c_1610,c_7696])).

cnf(c_2230,plain,
    ( k5_xboole_0(sK3,k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_12,c_1610])).

cnf(c_2236,plain,
    ( k5_xboole_0(sK3,k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(demodulation,[status(thm)],[c_2230,c_9])).

cnf(c_7834,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(sK3,sK3)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(light_normalisation,[status(thm)],[c_7718,c_2236])).

cnf(c_2233,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(sK3,k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) ),
    inference(superposition,[status(thm)],[c_1740,c_1610])).

cnf(c_2235,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) = k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    inference(demodulation,[status(thm)],[c_2233,c_1517])).

cnf(c_981,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_11,c_1])).

cnf(c_7264,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(sK3,X0)) = k5_xboole_0(X0,k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) ),
    inference(superposition,[status(thm)],[c_2235,c_981])).

cnf(c_7,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_963,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2610,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_963])).

cnf(c_4017,plain,
    ( r1_tarski(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1513,c_2610])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_964,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_7234,plain,
    ( k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = sK3 ),
    inference(superposition,[status(thm)],[c_4017,c_964])).

cnf(c_7552,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(sK3,X0)) = k5_xboole_0(X0,sK3) ),
    inference(light_normalisation,[status(thm)],[c_7264,c_7234])).

cnf(c_7835,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7834,c_12,c_7552])).

cnf(c_17,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_664,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) ),
    inference(theory_normalisation,[status(thm)],[c_17,c_11,c_1])).

cnf(c_1254,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_0,c_664])).

cnf(c_14949,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK2,k3_xboole_0(sK2,sK2))) = k3_tarski(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_7835,c_1254])).

cnf(c_19,plain,
    ( k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_14951,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK2,k3_xboole_0(sK2,sK2))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_14949,c_19])).

cnf(c_1368,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_12,c_11])).

cnf(c_1377,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_1368,c_1257])).

cnf(c_6,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2612,plain,
    ( r1_tarski(k5_xboole_0(X0,k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_963])).

cnf(c_2617,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2612,c_9])).

cnf(c_3704,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_2617,c_964])).

cnf(c_14952,plain,
    ( sK2 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_14951,c_9,c_12,c_1377,c_3704])).

cnf(c_14953,plain,
    ( k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_14952,c_7835])).

cnf(c_667,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1412,plain,
    ( X0 != X1
    | X0 = k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != X1 ),
    inference(instantiation,[status(thm)],[c_667])).

cnf(c_1413,plain,
    ( k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1412])).

cnf(c_670,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1216,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | X0 != X2
    | X1 != k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_670])).

cnf(c_1223,plain,
    ( ~ r2_hidden(k1_xboole_0,k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | r2_hidden(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1216])).

cnf(c_1009,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k1_zfmisc_1(X3))
    | X0 != X2
    | X1 != k1_zfmisc_1(X3) ),
    inference(instantiation,[status(thm)],[c_670])).

cnf(c_1143,plain,
    ( r2_hidden(X0,k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | ~ r2_hidden(X1,k1_zfmisc_1(k1_xboole_0))
    | X0 != X1
    | k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_zfmisc_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1009])).

cnf(c_1145,plain,
    ( r2_hidden(k1_xboole_0,k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_zfmisc_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1143])).

cnf(c_671,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1103,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k3_xboole_0(X2,X3),X2)
    | X1 != X2
    | X0 != k3_xboole_0(X2,X3) ),
    inference(instantiation,[status(thm)],[c_671])).

cnf(c_1105,plain,
    ( ~ r1_tarski(k3_xboole_0(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != k3_xboole_0(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1103])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_10,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_197,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | X3 != X1
    | k1_xboole_0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_10])).

cnf(c_198,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) ),
    inference(unflattening,[status(thm)],[c_197])).

cnf(c_956,plain,
    ( r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_198])).

cnf(c_966,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_956,c_6])).

cnf(c_972,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_966])).

cnf(c_974,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_972])).

cnf(c_666,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_681,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_666])).

cnf(c_4,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_237,plain,
    ( k3_xboole_0(X0,X1) != X2
    | k1_xboole_0 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_8])).

cnf(c_238,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(unflattening,[status(thm)],[c_237])).

cnf(c_239,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_238])).

cnf(c_48,plain,
    ( r1_tarski(k3_xboole_0(k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_15,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_26,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_18,plain,
    ( k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_zfmisc_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f79])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_14953,c_1413,c_1223,c_1145,c_1105,c_974,c_681,c_239,c_48,c_26,c_18])).

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
% 0.13/0.34  % DateTime   : Tue Dec  1 19:43:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 7.68/1.51  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.68/1.51  
% 7.68/1.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.68/1.51  
% 7.68/1.51  ------  iProver source info
% 7.68/1.51  
% 7.68/1.51  git: date: 2020-06-30 10:37:57 +0100
% 7.68/1.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.68/1.51  git: non_committed_changes: false
% 7.68/1.51  git: last_make_outside_of_git: false
% 7.68/1.51  
% 7.68/1.51  ------ 
% 7.68/1.51  
% 7.68/1.51  ------ Input Options
% 7.68/1.51  
% 7.68/1.51  --out_options                           all
% 7.68/1.51  --tptp_safe_out                         true
% 7.68/1.51  --problem_path                          ""
% 7.68/1.51  --include_path                          ""
% 7.68/1.51  --clausifier                            res/vclausify_rel
% 7.68/1.51  --clausifier_options                    ""
% 7.68/1.51  --stdin                                 false
% 7.68/1.51  --stats_out                             all
% 7.68/1.51  
% 7.68/1.51  ------ General Options
% 7.68/1.51  
% 7.68/1.51  --fof                                   false
% 7.68/1.51  --time_out_real                         305.
% 7.68/1.51  --time_out_virtual                      -1.
% 7.68/1.51  --symbol_type_check                     false
% 7.68/1.51  --clausify_out                          false
% 7.68/1.51  --sig_cnt_out                           false
% 7.68/1.51  --trig_cnt_out                          false
% 7.68/1.51  --trig_cnt_out_tolerance                1.
% 7.68/1.51  --trig_cnt_out_sk_spl                   false
% 7.68/1.51  --abstr_cl_out                          false
% 7.68/1.51  
% 7.68/1.51  ------ Global Options
% 7.68/1.51  
% 7.68/1.51  --schedule                              default
% 7.68/1.51  --add_important_lit                     false
% 7.68/1.51  --prop_solver_per_cl                    1000
% 7.68/1.51  --min_unsat_core                        false
% 7.68/1.51  --soft_assumptions                      false
% 7.68/1.51  --soft_lemma_size                       3
% 7.68/1.51  --prop_impl_unit_size                   0
% 7.68/1.51  --prop_impl_unit                        []
% 7.68/1.51  --share_sel_clauses                     true
% 7.68/1.51  --reset_solvers                         false
% 7.68/1.51  --bc_imp_inh                            [conj_cone]
% 7.68/1.51  --conj_cone_tolerance                   3.
% 7.68/1.51  --extra_neg_conj                        none
% 7.68/1.51  --large_theory_mode                     true
% 7.68/1.51  --prolific_symb_bound                   200
% 7.68/1.51  --lt_threshold                          2000
% 7.68/1.51  --clause_weak_htbl                      true
% 7.68/1.51  --gc_record_bc_elim                     false
% 7.68/1.51  
% 7.68/1.51  ------ Preprocessing Options
% 7.68/1.51  
% 7.68/1.51  --preprocessing_flag                    true
% 7.68/1.51  --time_out_prep_mult                    0.1
% 7.68/1.51  --splitting_mode                        input
% 7.68/1.51  --splitting_grd                         true
% 7.68/1.51  --splitting_cvd                         false
% 7.68/1.51  --splitting_cvd_svl                     false
% 7.68/1.51  --splitting_nvd                         32
% 7.68/1.51  --sub_typing                            true
% 7.68/1.51  --prep_gs_sim                           true
% 7.68/1.51  --prep_unflatten                        true
% 7.68/1.51  --prep_res_sim                          true
% 7.68/1.51  --prep_upred                            true
% 7.68/1.51  --prep_sem_filter                       exhaustive
% 7.68/1.51  --prep_sem_filter_out                   false
% 7.68/1.51  --pred_elim                             true
% 7.68/1.51  --res_sim_input                         true
% 7.68/1.51  --eq_ax_congr_red                       true
% 7.68/1.51  --pure_diseq_elim                       true
% 7.68/1.51  --brand_transform                       false
% 7.68/1.51  --non_eq_to_eq                          false
% 7.68/1.51  --prep_def_merge                        true
% 7.68/1.51  --prep_def_merge_prop_impl              false
% 7.68/1.51  --prep_def_merge_mbd                    true
% 7.68/1.51  --prep_def_merge_tr_red                 false
% 7.68/1.51  --prep_def_merge_tr_cl                  false
% 7.68/1.51  --smt_preprocessing                     true
% 7.68/1.51  --smt_ac_axioms                         fast
% 7.68/1.51  --preprocessed_out                      false
% 7.68/1.51  --preprocessed_stats                    false
% 7.68/1.51  
% 7.68/1.51  ------ Abstraction refinement Options
% 7.68/1.51  
% 7.68/1.51  --abstr_ref                             []
% 7.68/1.51  --abstr_ref_prep                        false
% 7.68/1.51  --abstr_ref_until_sat                   false
% 7.68/1.51  --abstr_ref_sig_restrict                funpre
% 7.68/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.68/1.51  --abstr_ref_under                       []
% 7.68/1.51  
% 7.68/1.51  ------ SAT Options
% 7.68/1.51  
% 7.68/1.51  --sat_mode                              false
% 7.68/1.51  --sat_fm_restart_options                ""
% 7.68/1.51  --sat_gr_def                            false
% 7.68/1.51  --sat_epr_types                         true
% 7.68/1.51  --sat_non_cyclic_types                  false
% 7.68/1.51  --sat_finite_models                     false
% 7.68/1.51  --sat_fm_lemmas                         false
% 7.68/1.51  --sat_fm_prep                           false
% 7.68/1.51  --sat_fm_uc_incr                        true
% 7.68/1.51  --sat_out_model                         small
% 7.68/1.51  --sat_out_clauses                       false
% 7.68/1.51  
% 7.68/1.51  ------ QBF Options
% 7.68/1.51  
% 7.68/1.51  --qbf_mode                              false
% 7.68/1.51  --qbf_elim_univ                         false
% 7.68/1.51  --qbf_dom_inst                          none
% 7.68/1.51  --qbf_dom_pre_inst                      false
% 7.68/1.51  --qbf_sk_in                             false
% 7.68/1.51  --qbf_pred_elim                         true
% 7.68/1.51  --qbf_split                             512
% 7.68/1.51  
% 7.68/1.51  ------ BMC1 Options
% 7.68/1.51  
% 7.68/1.51  --bmc1_incremental                      false
% 7.68/1.51  --bmc1_axioms                           reachable_all
% 7.68/1.51  --bmc1_min_bound                        0
% 7.68/1.51  --bmc1_max_bound                        -1
% 7.68/1.51  --bmc1_max_bound_default                -1
% 7.68/1.51  --bmc1_symbol_reachability              true
% 7.68/1.51  --bmc1_property_lemmas                  false
% 7.68/1.51  --bmc1_k_induction                      false
% 7.68/1.51  --bmc1_non_equiv_states                 false
% 7.68/1.51  --bmc1_deadlock                         false
% 7.68/1.51  --bmc1_ucm                              false
% 7.68/1.51  --bmc1_add_unsat_core                   none
% 7.68/1.51  --bmc1_unsat_core_children              false
% 7.68/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.68/1.51  --bmc1_out_stat                         full
% 7.68/1.51  --bmc1_ground_init                      false
% 7.68/1.51  --bmc1_pre_inst_next_state              false
% 7.68/1.51  --bmc1_pre_inst_state                   false
% 7.68/1.51  --bmc1_pre_inst_reach_state             false
% 7.68/1.51  --bmc1_out_unsat_core                   false
% 7.68/1.51  --bmc1_aig_witness_out                  false
% 7.68/1.51  --bmc1_verbose                          false
% 7.68/1.51  --bmc1_dump_clauses_tptp                false
% 7.68/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.68/1.51  --bmc1_dump_file                        -
% 7.68/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.68/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.68/1.51  --bmc1_ucm_extend_mode                  1
% 7.68/1.51  --bmc1_ucm_init_mode                    2
% 7.68/1.51  --bmc1_ucm_cone_mode                    none
% 7.68/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.68/1.51  --bmc1_ucm_relax_model                  4
% 7.68/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.68/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.68/1.51  --bmc1_ucm_layered_model                none
% 7.68/1.51  --bmc1_ucm_max_lemma_size               10
% 7.68/1.51  
% 7.68/1.51  ------ AIG Options
% 7.68/1.51  
% 7.68/1.51  --aig_mode                              false
% 7.68/1.51  
% 7.68/1.51  ------ Instantiation Options
% 7.68/1.51  
% 7.68/1.51  --instantiation_flag                    true
% 7.68/1.51  --inst_sos_flag                         true
% 7.68/1.51  --inst_sos_phase                        true
% 7.68/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.68/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.68/1.51  --inst_lit_sel_side                     num_symb
% 7.68/1.51  --inst_solver_per_active                1400
% 7.68/1.51  --inst_solver_calls_frac                1.
% 7.68/1.51  --inst_passive_queue_type               priority_queues
% 7.68/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.68/1.51  --inst_passive_queues_freq              [25;2]
% 7.68/1.51  --inst_dismatching                      true
% 7.68/1.51  --inst_eager_unprocessed_to_passive     true
% 7.68/1.51  --inst_prop_sim_given                   true
% 7.68/1.51  --inst_prop_sim_new                     false
% 7.68/1.51  --inst_subs_new                         false
% 7.68/1.51  --inst_eq_res_simp                      false
% 7.68/1.51  --inst_subs_given                       false
% 7.68/1.51  --inst_orphan_elimination               true
% 7.68/1.51  --inst_learning_loop_flag               true
% 7.68/1.51  --inst_learning_start                   3000
% 7.68/1.51  --inst_learning_factor                  2
% 7.68/1.51  --inst_start_prop_sim_after_learn       3
% 7.68/1.51  --inst_sel_renew                        solver
% 7.68/1.51  --inst_lit_activity_flag                true
% 7.68/1.51  --inst_restr_to_given                   false
% 7.68/1.51  --inst_activity_threshold               500
% 7.68/1.51  --inst_out_proof                        true
% 7.68/1.51  
% 7.68/1.51  ------ Resolution Options
% 7.68/1.51  
% 7.68/1.51  --resolution_flag                       true
% 7.68/1.51  --res_lit_sel                           adaptive
% 7.68/1.51  --res_lit_sel_side                      none
% 7.68/1.51  --res_ordering                          kbo
% 7.68/1.51  --res_to_prop_solver                    active
% 7.68/1.51  --res_prop_simpl_new                    false
% 7.68/1.51  --res_prop_simpl_given                  true
% 7.68/1.51  --res_passive_queue_type                priority_queues
% 7.68/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.68/1.51  --res_passive_queues_freq               [15;5]
% 7.68/1.51  --res_forward_subs                      full
% 7.68/1.51  --res_backward_subs                     full
% 7.68/1.51  --res_forward_subs_resolution           true
% 7.68/1.51  --res_backward_subs_resolution          true
% 7.68/1.51  --res_orphan_elimination                true
% 7.68/1.51  --res_time_limit                        2.
% 7.68/1.51  --res_out_proof                         true
% 7.68/1.51  
% 7.68/1.51  ------ Superposition Options
% 7.68/1.51  
% 7.68/1.51  --superposition_flag                    true
% 7.68/1.51  --sup_passive_queue_type                priority_queues
% 7.68/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.68/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.68/1.51  --demod_completeness_check              fast
% 7.68/1.51  --demod_use_ground                      true
% 7.68/1.51  --sup_to_prop_solver                    passive
% 7.68/1.51  --sup_prop_simpl_new                    true
% 7.68/1.51  --sup_prop_simpl_given                  true
% 7.68/1.51  --sup_fun_splitting                     true
% 7.68/1.51  --sup_smt_interval                      50000
% 7.68/1.51  
% 7.68/1.51  ------ Superposition Simplification Setup
% 7.68/1.51  
% 7.68/1.51  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.68/1.51  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.68/1.51  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.68/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.68/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.68/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.68/1.51  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.68/1.51  --sup_immed_triv                        [TrivRules]
% 7.68/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.68/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.68/1.51  --sup_immed_bw_main                     []
% 7.68/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.68/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.68/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.68/1.51  --sup_input_bw                          []
% 7.68/1.51  
% 7.68/1.51  ------ Combination Options
% 7.68/1.51  
% 7.68/1.51  --comb_res_mult                         3
% 7.68/1.51  --comb_sup_mult                         2
% 7.68/1.51  --comb_inst_mult                        10
% 7.68/1.51  
% 7.68/1.51  ------ Debug Options
% 7.68/1.51  
% 7.68/1.51  --dbg_backtrace                         false
% 7.68/1.51  --dbg_dump_prop_clauses                 false
% 7.68/1.51  --dbg_dump_prop_clauses_file            -
% 7.68/1.51  --dbg_out_stat                          false
% 7.68/1.51  ------ Parsing...
% 7.68/1.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.68/1.51  
% 7.68/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.68/1.51  
% 7.68/1.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.68/1.51  
% 7.68/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.68/1.51  ------ Proving...
% 7.68/1.51  ------ Problem Properties 
% 7.68/1.51  
% 7.68/1.51  
% 7.68/1.51  clauses                                 20
% 7.68/1.51  conjectures                             1
% 7.68/1.51  EPR                                     1
% 7.68/1.51  Horn                                    19
% 7.68/1.51  unary                                   13
% 7.68/1.51  binary                                  5
% 7.68/1.51  lits                                    29
% 7.68/1.51  lits eq                                 14
% 7.68/1.51  fd_pure                                 0
% 7.68/1.51  fd_pseudo                               0
% 7.68/1.51  fd_cond                                 1
% 7.68/1.51  fd_pseudo_cond                          2
% 7.68/1.51  AC symbols                              1
% 7.68/1.51  
% 7.68/1.51  ------ Schedule dynamic 5 is on 
% 7.68/1.51  
% 7.68/1.51  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.68/1.51  
% 7.68/1.51  
% 7.68/1.51  ------ 
% 7.68/1.51  Current options:
% 7.68/1.51  ------ 
% 7.68/1.51  
% 7.68/1.51  ------ Input Options
% 7.68/1.51  
% 7.68/1.51  --out_options                           all
% 7.68/1.51  --tptp_safe_out                         true
% 7.68/1.51  --problem_path                          ""
% 7.68/1.51  --include_path                          ""
% 7.68/1.51  --clausifier                            res/vclausify_rel
% 7.68/1.51  --clausifier_options                    ""
% 7.68/1.51  --stdin                                 false
% 7.68/1.51  --stats_out                             all
% 7.68/1.51  
% 7.68/1.51  ------ General Options
% 7.68/1.51  
% 7.68/1.51  --fof                                   false
% 7.68/1.51  --time_out_real                         305.
% 7.68/1.51  --time_out_virtual                      -1.
% 7.68/1.51  --symbol_type_check                     false
% 7.68/1.51  --clausify_out                          false
% 7.68/1.51  --sig_cnt_out                           false
% 7.68/1.51  --trig_cnt_out                          false
% 7.68/1.51  --trig_cnt_out_tolerance                1.
% 7.68/1.51  --trig_cnt_out_sk_spl                   false
% 7.68/1.51  --abstr_cl_out                          false
% 7.68/1.51  
% 7.68/1.51  ------ Global Options
% 7.68/1.51  
% 7.68/1.51  --schedule                              default
% 7.68/1.51  --add_important_lit                     false
% 7.68/1.51  --prop_solver_per_cl                    1000
% 7.68/1.51  --min_unsat_core                        false
% 7.68/1.51  --soft_assumptions                      false
% 7.68/1.51  --soft_lemma_size                       3
% 7.68/1.51  --prop_impl_unit_size                   0
% 7.68/1.51  --prop_impl_unit                        []
% 7.68/1.51  --share_sel_clauses                     true
% 7.68/1.51  --reset_solvers                         false
% 7.68/1.51  --bc_imp_inh                            [conj_cone]
% 7.68/1.51  --conj_cone_tolerance                   3.
% 7.68/1.51  --extra_neg_conj                        none
% 7.68/1.51  --large_theory_mode                     true
% 7.68/1.51  --prolific_symb_bound                   200
% 7.68/1.51  --lt_threshold                          2000
% 7.68/1.51  --clause_weak_htbl                      true
% 7.68/1.51  --gc_record_bc_elim                     false
% 7.68/1.51  
% 7.68/1.51  ------ Preprocessing Options
% 7.68/1.51  
% 7.68/1.51  --preprocessing_flag                    true
% 7.68/1.51  --time_out_prep_mult                    0.1
% 7.68/1.51  --splitting_mode                        input
% 7.68/1.51  --splitting_grd                         true
% 7.68/1.51  --splitting_cvd                         false
% 7.68/1.51  --splitting_cvd_svl                     false
% 7.68/1.51  --splitting_nvd                         32
% 7.68/1.51  --sub_typing                            true
% 7.68/1.51  --prep_gs_sim                           true
% 7.68/1.51  --prep_unflatten                        true
% 7.68/1.51  --prep_res_sim                          true
% 7.68/1.51  --prep_upred                            true
% 7.68/1.51  --prep_sem_filter                       exhaustive
% 7.68/1.51  --prep_sem_filter_out                   false
% 7.68/1.51  --pred_elim                             true
% 7.68/1.51  --res_sim_input                         true
% 7.68/1.51  --eq_ax_congr_red                       true
% 7.68/1.51  --pure_diseq_elim                       true
% 7.68/1.51  --brand_transform                       false
% 7.68/1.51  --non_eq_to_eq                          false
% 7.68/1.51  --prep_def_merge                        true
% 7.68/1.51  --prep_def_merge_prop_impl              false
% 7.68/1.51  --prep_def_merge_mbd                    true
% 7.68/1.51  --prep_def_merge_tr_red                 false
% 7.68/1.51  --prep_def_merge_tr_cl                  false
% 7.68/1.51  --smt_preprocessing                     true
% 7.68/1.51  --smt_ac_axioms                         fast
% 7.68/1.51  --preprocessed_out                      false
% 7.68/1.51  --preprocessed_stats                    false
% 7.68/1.51  
% 7.68/1.51  ------ Abstraction refinement Options
% 7.68/1.51  
% 7.68/1.51  --abstr_ref                             []
% 7.68/1.51  --abstr_ref_prep                        false
% 7.68/1.51  --abstr_ref_until_sat                   false
% 7.68/1.51  --abstr_ref_sig_restrict                funpre
% 7.68/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.68/1.51  --abstr_ref_under                       []
% 7.68/1.51  
% 7.68/1.51  ------ SAT Options
% 7.68/1.51  
% 7.68/1.51  --sat_mode                              false
% 7.68/1.51  --sat_fm_restart_options                ""
% 7.68/1.51  --sat_gr_def                            false
% 7.68/1.51  --sat_epr_types                         true
% 7.68/1.51  --sat_non_cyclic_types                  false
% 7.68/1.51  --sat_finite_models                     false
% 7.68/1.51  --sat_fm_lemmas                         false
% 7.68/1.51  --sat_fm_prep                           false
% 7.68/1.51  --sat_fm_uc_incr                        true
% 7.68/1.51  --sat_out_model                         small
% 7.68/1.51  --sat_out_clauses                       false
% 7.68/1.51  
% 7.68/1.51  ------ QBF Options
% 7.68/1.51  
% 7.68/1.51  --qbf_mode                              false
% 7.68/1.51  --qbf_elim_univ                         false
% 7.68/1.51  --qbf_dom_inst                          none
% 7.68/1.51  --qbf_dom_pre_inst                      false
% 7.68/1.51  --qbf_sk_in                             false
% 7.68/1.51  --qbf_pred_elim                         true
% 7.68/1.51  --qbf_split                             512
% 7.68/1.51  
% 7.68/1.51  ------ BMC1 Options
% 7.68/1.51  
% 7.68/1.51  --bmc1_incremental                      false
% 7.68/1.51  --bmc1_axioms                           reachable_all
% 7.68/1.51  --bmc1_min_bound                        0
% 7.68/1.51  --bmc1_max_bound                        -1
% 7.68/1.51  --bmc1_max_bound_default                -1
% 7.68/1.51  --bmc1_symbol_reachability              true
% 7.68/1.51  --bmc1_property_lemmas                  false
% 7.68/1.51  --bmc1_k_induction                      false
% 7.68/1.51  --bmc1_non_equiv_states                 false
% 7.68/1.51  --bmc1_deadlock                         false
% 7.68/1.51  --bmc1_ucm                              false
% 7.68/1.51  --bmc1_add_unsat_core                   none
% 7.68/1.51  --bmc1_unsat_core_children              false
% 7.68/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.68/1.51  --bmc1_out_stat                         full
% 7.68/1.51  --bmc1_ground_init                      false
% 7.68/1.51  --bmc1_pre_inst_next_state              false
% 7.68/1.51  --bmc1_pre_inst_state                   false
% 7.68/1.51  --bmc1_pre_inst_reach_state             false
% 7.68/1.51  --bmc1_out_unsat_core                   false
% 7.68/1.51  --bmc1_aig_witness_out                  false
% 7.68/1.51  --bmc1_verbose                          false
% 7.68/1.51  --bmc1_dump_clauses_tptp                false
% 7.68/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.68/1.51  --bmc1_dump_file                        -
% 7.68/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.68/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.68/1.51  --bmc1_ucm_extend_mode                  1
% 7.68/1.51  --bmc1_ucm_init_mode                    2
% 7.68/1.51  --bmc1_ucm_cone_mode                    none
% 7.68/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.68/1.51  --bmc1_ucm_relax_model                  4
% 7.68/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.68/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.68/1.51  --bmc1_ucm_layered_model                none
% 7.68/1.51  --bmc1_ucm_max_lemma_size               10
% 7.68/1.51  
% 7.68/1.51  ------ AIG Options
% 7.68/1.51  
% 7.68/1.51  --aig_mode                              false
% 7.68/1.51  
% 7.68/1.51  ------ Instantiation Options
% 7.68/1.51  
% 7.68/1.51  --instantiation_flag                    true
% 7.68/1.51  --inst_sos_flag                         true
% 7.68/1.51  --inst_sos_phase                        true
% 7.68/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.68/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.68/1.51  --inst_lit_sel_side                     none
% 7.68/1.51  --inst_solver_per_active                1400
% 7.68/1.51  --inst_solver_calls_frac                1.
% 7.68/1.51  --inst_passive_queue_type               priority_queues
% 7.68/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.68/1.51  --inst_passive_queues_freq              [25;2]
% 7.68/1.51  --inst_dismatching                      true
% 7.68/1.51  --inst_eager_unprocessed_to_passive     true
% 7.68/1.51  --inst_prop_sim_given                   true
% 7.68/1.51  --inst_prop_sim_new                     false
% 7.68/1.51  --inst_subs_new                         false
% 7.68/1.51  --inst_eq_res_simp                      false
% 7.68/1.51  --inst_subs_given                       false
% 7.68/1.51  --inst_orphan_elimination               true
% 7.68/1.51  --inst_learning_loop_flag               true
% 7.68/1.51  --inst_learning_start                   3000
% 7.68/1.51  --inst_learning_factor                  2
% 7.68/1.51  --inst_start_prop_sim_after_learn       3
% 7.68/1.51  --inst_sel_renew                        solver
% 7.68/1.51  --inst_lit_activity_flag                true
% 7.68/1.51  --inst_restr_to_given                   false
% 7.68/1.51  --inst_activity_threshold               500
% 7.68/1.51  --inst_out_proof                        true
% 7.68/1.51  
% 7.68/1.51  ------ Resolution Options
% 7.68/1.51  
% 7.68/1.51  --resolution_flag                       false
% 7.68/1.51  --res_lit_sel                           adaptive
% 7.68/1.51  --res_lit_sel_side                      none
% 7.68/1.51  --res_ordering                          kbo
% 7.68/1.51  --res_to_prop_solver                    active
% 7.68/1.51  --res_prop_simpl_new                    false
% 7.68/1.51  --res_prop_simpl_given                  true
% 7.68/1.51  --res_passive_queue_type                priority_queues
% 7.68/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.68/1.51  --res_passive_queues_freq               [15;5]
% 7.68/1.51  --res_forward_subs                      full
% 7.68/1.51  --res_backward_subs                     full
% 7.68/1.51  --res_forward_subs_resolution           true
% 7.68/1.51  --res_backward_subs_resolution          true
% 7.68/1.51  --res_orphan_elimination                true
% 7.68/1.51  --res_time_limit                        2.
% 7.68/1.51  --res_out_proof                         true
% 7.68/1.51  
% 7.68/1.51  ------ Superposition Options
% 7.68/1.51  
% 7.68/1.51  --superposition_flag                    true
% 7.68/1.51  --sup_passive_queue_type                priority_queues
% 7.68/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.68/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.68/1.51  --demod_completeness_check              fast
% 7.68/1.51  --demod_use_ground                      true
% 7.68/1.51  --sup_to_prop_solver                    passive
% 7.68/1.51  --sup_prop_simpl_new                    true
% 7.68/1.51  --sup_prop_simpl_given                  true
% 7.68/1.51  --sup_fun_splitting                     true
% 7.68/1.51  --sup_smt_interval                      50000
% 7.68/1.51  
% 7.68/1.51  ------ Superposition Simplification Setup
% 7.68/1.51  
% 7.68/1.51  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.68/1.51  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.68/1.51  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.68/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.68/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.68/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.68/1.51  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.68/1.51  --sup_immed_triv                        [TrivRules]
% 7.68/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.68/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.68/1.51  --sup_immed_bw_main                     []
% 7.68/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.68/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.68/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.68/1.51  --sup_input_bw                          []
% 7.68/1.51  
% 7.68/1.51  ------ Combination Options
% 7.68/1.51  
% 7.68/1.51  --comb_res_mult                         3
% 7.68/1.51  --comb_sup_mult                         2
% 7.68/1.51  --comb_inst_mult                        10
% 7.68/1.51  
% 7.68/1.51  ------ Debug Options
% 7.68/1.51  
% 7.68/1.51  --dbg_backtrace                         false
% 7.68/1.51  --dbg_dump_prop_clauses                 false
% 7.68/1.51  --dbg_dump_prop_clauses_file            -
% 7.68/1.51  --dbg_out_stat                          false
% 7.68/1.51  
% 7.68/1.51  
% 7.68/1.51  
% 7.68/1.51  
% 7.68/1.51  ------ Proving...
% 7.68/1.51  
% 7.68/1.51  
% 7.68/1.51  % SZS status Theorem for theBenchmark.p
% 7.68/1.51  
% 7.68/1.51  % SZS output start CNFRefutation for theBenchmark.p
% 7.68/1.51  
% 7.68/1.51  fof(f12,axiom,(
% 7.68/1.51    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 7.68/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.51  
% 7.68/1.51  fof(f53,plain,(
% 7.68/1.51    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 7.68/1.51    inference(cnf_transformation,[],[f12])).
% 7.68/1.51  
% 7.68/1.51  fof(f1,axiom,(
% 7.68/1.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.68/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.51  
% 7.68/1.51  fof(f41,plain,(
% 7.68/1.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.68/1.51    inference(cnf_transformation,[],[f1])).
% 7.68/1.51  
% 7.68/1.51  fof(f26,conjecture,(
% 7.68/1.51    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 7.68/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.51  
% 7.68/1.51  fof(f27,negated_conjecture,(
% 7.68/1.51    ~! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 7.68/1.51    inference(negated_conjecture,[],[f26])).
% 7.68/1.51  
% 7.68/1.51  fof(f32,plain,(
% 7.68/1.51    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1)),
% 7.68/1.51    inference(ennf_transformation,[],[f27])).
% 7.68/1.51  
% 7.68/1.51  fof(f39,plain,(
% 7.68/1.51    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1) => k1_xboole_0 = k2_xboole_0(k1_tarski(sK2),sK3)),
% 7.68/1.51    introduced(choice_axiom,[])).
% 7.68/1.51  
% 7.68/1.51  fof(f40,plain,(
% 7.68/1.51    k1_xboole_0 = k2_xboole_0(k1_tarski(sK2),sK3)),
% 7.68/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f32,f39])).
% 7.68/1.51  
% 7.68/1.51  fof(f70,plain,(
% 7.68/1.51    k1_xboole_0 = k2_xboole_0(k1_tarski(sK2),sK3)),
% 7.68/1.51    inference(cnf_transformation,[],[f40])).
% 7.68/1.51  
% 7.68/1.51  fof(f14,axiom,(
% 7.68/1.51    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)),
% 7.68/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.51  
% 7.68/1.51  fof(f55,plain,(
% 7.68/1.51    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 7.68/1.51    inference(cnf_transformation,[],[f14])).
% 7.68/1.51  
% 7.68/1.51  fof(f15,axiom,(
% 7.68/1.51    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 7.68/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.51  
% 7.68/1.51  fof(f56,plain,(
% 7.68/1.51    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 7.68/1.51    inference(cnf_transformation,[],[f15])).
% 7.68/1.51  
% 7.68/1.51  fof(f16,axiom,(
% 7.68/1.51    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.68/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.51  
% 7.68/1.51  fof(f57,plain,(
% 7.68/1.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.68/1.51    inference(cnf_transformation,[],[f16])).
% 7.68/1.51  
% 7.68/1.51  fof(f17,axiom,(
% 7.68/1.51    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.68/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.51  
% 7.68/1.51  fof(f58,plain,(
% 7.68/1.51    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.68/1.51    inference(cnf_transformation,[],[f17])).
% 7.68/1.51  
% 7.68/1.51  fof(f18,axiom,(
% 7.68/1.51    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 7.68/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.51  
% 7.68/1.51  fof(f59,plain,(
% 7.68/1.51    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 7.68/1.51    inference(cnf_transformation,[],[f18])).
% 7.68/1.51  
% 7.68/1.51  fof(f19,axiom,(
% 7.68/1.51    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 7.68/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.51  
% 7.68/1.51  fof(f60,plain,(
% 7.68/1.51    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 7.68/1.51    inference(cnf_transformation,[],[f19])).
% 7.68/1.51  
% 7.68/1.51  fof(f20,axiom,(
% 7.68/1.51    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 7.68/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.51  
% 7.68/1.51  fof(f61,plain,(
% 7.68/1.51    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 7.68/1.51    inference(cnf_transformation,[],[f20])).
% 7.68/1.51  
% 7.68/1.51  fof(f21,axiom,(
% 7.68/1.51    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 7.68/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.51  
% 7.68/1.51  fof(f62,plain,(
% 7.68/1.51    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 7.68/1.51    inference(cnf_transformation,[],[f21])).
% 7.68/1.51  
% 7.68/1.51  fof(f71,plain,(
% 7.68/1.51    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 7.68/1.51    inference(definition_unfolding,[],[f61,f62])).
% 7.68/1.51  
% 7.68/1.51  fof(f72,plain,(
% 7.68/1.51    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 7.68/1.51    inference(definition_unfolding,[],[f60,f71])).
% 7.68/1.51  
% 7.68/1.51  fof(f73,plain,(
% 7.68/1.51    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 7.68/1.51    inference(definition_unfolding,[],[f59,f72])).
% 7.68/1.51  
% 7.68/1.51  fof(f74,plain,(
% 7.68/1.51    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 7.68/1.51    inference(definition_unfolding,[],[f58,f73])).
% 7.68/1.51  
% 7.68/1.51  fof(f75,plain,(
% 7.68/1.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 7.68/1.51    inference(definition_unfolding,[],[f57,f74])).
% 7.68/1.51  
% 7.68/1.51  fof(f76,plain,(
% 7.68/1.51    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 7.68/1.51    inference(definition_unfolding,[],[f56,f75])).
% 7.68/1.51  
% 7.68/1.51  fof(f80,plain,(
% 7.68/1.51    k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) = k1_xboole_0),
% 7.68/1.51    inference(definition_unfolding,[],[f70,f55,f76])).
% 7.68/1.51  
% 7.68/1.51  fof(f2,axiom,(
% 7.68/1.51    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 7.68/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.51  
% 7.68/1.51  fof(f42,plain,(
% 7.68/1.51    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 7.68/1.51    inference(cnf_transformation,[],[f2])).
% 7.68/1.51  
% 7.68/1.51  fof(f10,axiom,(
% 7.68/1.51    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 7.68/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.51  
% 7.68/1.51  fof(f51,plain,(
% 7.68/1.51    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.68/1.51    inference(cnf_transformation,[],[f10])).
% 7.68/1.51  
% 7.68/1.51  fof(f13,axiom,(
% 7.68/1.51    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 7.68/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.51  
% 7.68/1.51  fof(f54,plain,(
% 7.68/1.51    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 7.68/1.51    inference(cnf_transformation,[],[f13])).
% 7.68/1.51  
% 7.68/1.51  fof(f8,axiom,(
% 7.68/1.51    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 7.68/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.51  
% 7.68/1.51  fof(f49,plain,(
% 7.68/1.51    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 7.68/1.51    inference(cnf_transformation,[],[f8])).
% 7.68/1.51  
% 7.68/1.51  fof(f4,axiom,(
% 7.68/1.51    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 7.68/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.51  
% 7.68/1.51  fof(f45,plain,(
% 7.68/1.51    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 7.68/1.51    inference(cnf_transformation,[],[f4])).
% 7.68/1.51  
% 7.68/1.51  fof(f77,plain,(
% 7.68/1.51    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 7.68/1.51    inference(definition_unfolding,[],[f49,f45])).
% 7.68/1.51  
% 7.68/1.51  fof(f6,axiom,(
% 7.68/1.51    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 7.68/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.51  
% 7.68/1.51  fof(f30,plain,(
% 7.68/1.51    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 7.68/1.51    inference(ennf_transformation,[],[f6])).
% 7.68/1.51  
% 7.68/1.51  fof(f47,plain,(
% 7.68/1.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 7.68/1.51    inference(cnf_transformation,[],[f30])).
% 7.68/1.51  
% 7.68/1.51  fof(f23,axiom,(
% 7.68/1.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 7.68/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.51  
% 7.68/1.51  fof(f67,plain,(
% 7.68/1.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 7.68/1.51    inference(cnf_transformation,[],[f23])).
% 7.68/1.51  
% 7.68/1.51  fof(f78,plain,(
% 7.68/1.51    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 7.68/1.51    inference(definition_unfolding,[],[f67,f55,f75])).
% 7.68/1.51  
% 7.68/1.51  fof(f25,axiom,(
% 7.68/1.51    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 7.68/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.51  
% 7.68/1.51  fof(f69,plain,(
% 7.68/1.51    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 7.68/1.51    inference(cnf_transformation,[],[f25])).
% 7.68/1.51  
% 7.68/1.51  fof(f7,axiom,(
% 7.68/1.51    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 7.68/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.51  
% 7.68/1.51  fof(f48,plain,(
% 7.68/1.51    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 7.68/1.51    inference(cnf_transformation,[],[f7])).
% 7.68/1.51  
% 7.68/1.51  fof(f3,axiom,(
% 7.68/1.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 7.68/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.51  
% 7.68/1.51  fof(f28,plain,(
% 7.68/1.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 7.68/1.51    inference(rectify,[],[f3])).
% 7.68/1.51  
% 7.68/1.51  fof(f29,plain,(
% 7.68/1.51    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 7.68/1.51    inference(ennf_transformation,[],[f28])).
% 7.68/1.51  
% 7.68/1.51  fof(f33,plain,(
% 7.68/1.51    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 7.68/1.51    introduced(choice_axiom,[])).
% 7.68/1.51  
% 7.68/1.51  fof(f34,plain,(
% 7.68/1.51    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 7.68/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f33])).
% 7.68/1.51  
% 7.68/1.51  fof(f44,plain,(
% 7.68/1.51    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 7.68/1.51    inference(cnf_transformation,[],[f34])).
% 7.68/1.51  
% 7.68/1.51  fof(f11,axiom,(
% 7.68/1.51    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 7.68/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.51  
% 7.68/1.51  fof(f52,plain,(
% 7.68/1.51    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 7.68/1.51    inference(cnf_transformation,[],[f11])).
% 7.68/1.51  
% 7.68/1.51  fof(f5,axiom,(
% 7.68/1.51    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 7.68/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.51  
% 7.68/1.51  fof(f46,plain,(
% 7.68/1.51    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 7.68/1.51    inference(cnf_transformation,[],[f5])).
% 7.68/1.51  
% 7.68/1.51  fof(f9,axiom,(
% 7.68/1.51    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 7.68/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.51  
% 7.68/1.51  fof(f31,plain,(
% 7.68/1.51    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 7.68/1.51    inference(ennf_transformation,[],[f9])).
% 7.68/1.51  
% 7.68/1.51  fof(f50,plain,(
% 7.68/1.51    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 7.68/1.51    inference(cnf_transformation,[],[f31])).
% 7.68/1.51  
% 7.68/1.51  fof(f22,axiom,(
% 7.68/1.51    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 7.68/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.51  
% 7.68/1.51  fof(f35,plain,(
% 7.68/1.51    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 7.68/1.51    inference(nnf_transformation,[],[f22])).
% 7.68/1.51  
% 7.68/1.51  fof(f36,plain,(
% 7.68/1.51    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 7.68/1.51    inference(rectify,[],[f35])).
% 7.68/1.51  
% 7.68/1.51  fof(f37,plain,(
% 7.68/1.51    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK1(X0,X1),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r1_tarski(sK1(X0,X1),X0) | r2_hidden(sK1(X0,X1),X1))))),
% 7.68/1.51    introduced(choice_axiom,[])).
% 7.68/1.51  
% 7.68/1.51  fof(f38,plain,(
% 7.68/1.51    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK1(X0,X1),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r1_tarski(sK1(X0,X1),X0) | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 7.68/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f36,f37])).
% 7.68/1.51  
% 7.68/1.51  fof(f64,plain,(
% 7.68/1.51    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 7.68/1.51    inference(cnf_transformation,[],[f38])).
% 7.68/1.51  
% 7.68/1.51  fof(f81,plain,(
% 7.68/1.51    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 7.68/1.51    inference(equality_resolution,[],[f64])).
% 7.68/1.51  
% 7.68/1.51  fof(f24,axiom,(
% 7.68/1.51    k1_tarski(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0)),
% 7.68/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.51  
% 7.68/1.51  fof(f68,plain,(
% 7.68/1.51    k1_tarski(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0)),
% 7.68/1.51    inference(cnf_transformation,[],[f24])).
% 7.68/1.51  
% 7.68/1.51  fof(f79,plain,(
% 7.68/1.51    k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_zfmisc_1(k1_xboole_0)),
% 7.68/1.51    inference(definition_unfolding,[],[f68,f76])).
% 7.68/1.51  
% 7.68/1.51  cnf(c_11,plain,
% 7.68/1.51      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 7.68/1.51      inference(cnf_transformation,[],[f53]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_0,plain,
% 7.68/1.51      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 7.68/1.51      inference(cnf_transformation,[],[f41]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_20,negated_conjecture,
% 7.68/1.51      ( k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) = k1_xboole_0 ),
% 7.68/1.51      inference(cnf_transformation,[],[f80]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_1,plain,
% 7.68/1.51      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 7.68/1.51      inference(cnf_transformation,[],[f42]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_663,negated_conjecture,
% 7.68/1.51      ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))) = k1_xboole_0 ),
% 7.68/1.51      inference(theory_normalisation,[status(thm)],[c_20,c_11,c_1]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_1211,plain,
% 7.68/1.51      ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) = k1_xboole_0 ),
% 7.68/1.51      inference(demodulation,[status(thm)],[c_0,c_663]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_1370,plain,
% 7.68/1.51      ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),X0)) = k5_xboole_0(k1_xboole_0,X0) ),
% 7.68/1.51      inference(superposition,[status(thm)],[c_1211,c_11]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_9,plain,
% 7.68/1.51      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.68/1.51      inference(cnf_transformation,[],[f51]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_1257,plain,
% 7.68/1.51      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 7.68/1.51      inference(superposition,[status(thm)],[c_9,c_1]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_1376,plain,
% 7.68/1.51      ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),X0)) = X0 ),
% 7.68/1.51      inference(light_normalisation,[status(thm)],[c_1370,c_1257]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_1508,plain,
% 7.68/1.51      ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X0))) = X0 ),
% 7.68/1.51      inference(superposition,[status(thm)],[c_11,c_1376]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_12,plain,
% 7.68/1.51      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 7.68/1.51      inference(cnf_transformation,[],[f54]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_1509,plain,
% 7.68/1.51      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = k5_xboole_0(sK3,k1_xboole_0) ),
% 7.68/1.51      inference(superposition,[status(thm)],[c_12,c_1376]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_1513,plain,
% 7.68/1.51      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = sK3 ),
% 7.68/1.51      inference(demodulation,[status(thm)],[c_1509,c_9]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_1517,plain,
% 7.68/1.51      ( k5_xboole_0(sK3,k5_xboole_0(sK3,X0)) = X0 ),
% 7.68/1.51      inference(demodulation,[status(thm)],[c_1513,c_1376]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_1610,plain,
% 7.68/1.51      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X0)) = k5_xboole_0(sK3,X0) ),
% 7.68/1.51      inference(superposition,[status(thm)],[c_1508,c_1517]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_1525,plain,
% 7.68/1.51      ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(sK3,X0),X1)) = k5_xboole_0(X0,X1) ),
% 7.68/1.51      inference(superposition,[status(thm)],[c_1517,c_11]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_1720,plain,
% 7.68/1.51      ( k5_xboole_0(X0,k5_xboole_0(sK3,X0)) = k5_xboole_0(sK3,k1_xboole_0) ),
% 7.68/1.51      inference(superposition,[status(thm)],[c_12,c_1525]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_1740,plain,
% 7.68/1.51      ( k5_xboole_0(X0,k5_xboole_0(sK3,X0)) = sK3 ),
% 7.68/1.51      inference(demodulation,[status(thm)],[c_1720,c_9]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_2047,plain,
% 7.68/1.51      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(sK3,X0),X1)) = k5_xboole_0(sK3,X1) ),
% 7.68/1.51      inference(superposition,[status(thm)],[c_1740,c_11]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_2044,plain,
% 7.68/1.51      ( k5_xboole_0(k5_xboole_0(sK3,X0),X0) = sK3 ),
% 7.68/1.51      inference(superposition,[status(thm)],[c_1517,c_1740]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_2149,plain,
% 7.68/1.51      ( k5_xboole_0(k5_xboole_0(sK3,X0),k5_xboole_0(X0,X1)) = k5_xboole_0(sK3,X1) ),
% 7.68/1.51      inference(superposition,[status(thm)],[c_2044,c_11]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_1716,plain,
% 7.68/1.51      ( k5_xboole_0(sK3,k5_xboole_0(X0,k5_xboole_0(sK3,X1))) = k5_xboole_0(X1,X0) ),
% 7.68/1.51      inference(superposition,[status(thm)],[c_1,c_1525]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_2901,plain,
% 7.68/1.51      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,k5_xboole_0(sK3,X0))) = sK3 ),
% 7.68/1.51      inference(superposition,[status(thm)],[c_1716,c_2044]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_4245,plain,
% 7.68/1.51      ( k5_xboole_0(k5_xboole_0(sK3,X0),k5_xboole_0(k5_xboole_0(X1,X0),k5_xboole_0(sK3,k5_xboole_0(sK3,X1)))) = sK3 ),
% 7.68/1.51      inference(superposition,[status(thm)],[c_2149,c_2901]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_4317,plain,
% 7.68/1.51      ( k5_xboole_0(k5_xboole_0(sK3,X0),k5_xboole_0(k5_xboole_0(X1,X0),X1)) = sK3 ),
% 7.68/1.51      inference(demodulation,[status(thm)],[c_4245,c_1517]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_4464,plain,
% 7.68/1.51      ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,X1),X0)) = k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(sK3,X1)),sK3) ),
% 7.68/1.51      inference(superposition,[status(thm)],[c_4317,c_2149]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_4487,plain,
% 7.68/1.51      ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,X1),X0)) = k5_xboole_0(X1,sK3) ),
% 7.68/1.51      inference(demodulation,[status(thm)],[c_4464,c_1517]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_4841,plain,
% 7.68/1.51      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(sK3,X0),X1)) = k5_xboole_0(X1,sK3) ),
% 7.68/1.51      inference(superposition,[status(thm)],[c_4487,c_1716]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_979,plain,
% 7.68/1.51      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
% 7.68/1.51      inference(superposition,[status(thm)],[c_11,c_1]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_5299,plain,
% 7.68/1.51      ( k5_xboole_0(k5_xboole_0(sK3,X0),k5_xboole_0(X1,X0)) = k5_xboole_0(X1,sK3) ),
% 7.68/1.51      inference(superposition,[status(thm)],[c_2044,c_979]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_980,plain,
% 7.68/1.51      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
% 7.68/1.51      inference(superposition,[status(thm)],[c_11,c_1]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_6834,plain,
% 7.68/1.51      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(sK3,X1),X2)) = k5_xboole_0(X2,k5_xboole_0(X0,sK3)) ),
% 7.68/1.51      inference(superposition,[status(thm)],[c_5299,c_980]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_4835,plain,
% 7.68/1.51      ( k5_xboole_0(k5_xboole_0(X0,X1),X0) = k5_xboole_0(sK3,k5_xboole_0(X1,sK3)) ),
% 7.68/1.51      inference(superposition,[status(thm)],[c_4487,c_1517]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_1519,plain,
% 7.68/1.51      ( k5_xboole_0(sK3,k5_xboole_0(X0,sK3)) = X0 ),
% 7.68/1.51      inference(superposition,[status(thm)],[c_1,c_1517]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_4845,plain,
% 7.68/1.51      ( k5_xboole_0(k5_xboole_0(X0,X1),X0) = X1 ),
% 7.68/1.51      inference(demodulation,[status(thm)],[c_4835,c_1519]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_4959,plain,
% 7.68/1.51      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
% 7.68/1.51      inference(superposition,[status(thm)],[c_4845,c_11]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_6123,plain,
% 7.68/1.51      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X2)) = k5_xboole_0(X2,X0) ),
% 7.68/1.51      inference(superposition,[status(thm)],[c_4959,c_980]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_6187,plain,
% 7.68/1.51      ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,sK3)),X2)) = k5_xboole_0(k5_xboole_0(X1,X0),X2) ),
% 7.68/1.51      inference(superposition,[status(thm)],[c_980,c_1525]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_1615,plain,
% 7.68/1.51      ( k5_xboole_0(sK3,k5_xboole_0(X0,k5_xboole_0(X1,sK3))) = k5_xboole_0(X0,X1) ),
% 7.68/1.51      inference(superposition,[status(thm)],[c_11,c_1519]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_2740,plain,
% 7.68/1.51      ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,sK3)),X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
% 7.68/1.51      inference(superposition,[status(thm)],[c_1615,c_11]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_2747,plain,
% 7.68/1.51      ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,sK3)),X2)) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 7.68/1.51      inference(light_normalisation,[status(thm)],[c_2740,c_11]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_6223,plain,
% 7.68/1.51      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
% 7.68/1.51      inference(light_normalisation,[status(thm)],[c_6187,c_2747]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_6865,plain,
% 7.68/1.51      ( k5_xboole_0(k5_xboole_0(sK3,X0),X1) = k5_xboole_0(X0,k5_xboole_0(X1,sK3)) ),
% 7.68/1.51      inference(demodulation,[status(thm)],[c_6834,c_6123,c_6223]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_7696,plain,
% 7.68/1.51      ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,sK3))) = k5_xboole_0(sK3,X1) ),
% 7.68/1.51      inference(light_normalisation,[status(thm)],[c_2047,c_4841,c_6865]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_7718,plain,
% 7.68/1.51      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(sK3,sK3)) = k5_xboole_0(sK3,k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) ),
% 7.68/1.51      inference(superposition,[status(thm)],[c_1610,c_7696]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_2230,plain,
% 7.68/1.51      ( k5_xboole_0(sK3,k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k1_xboole_0) ),
% 7.68/1.51      inference(superposition,[status(thm)],[c_12,c_1610]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_2236,plain,
% 7.68/1.51      ( k5_xboole_0(sK3,k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
% 7.68/1.51      inference(demodulation,[status(thm)],[c_2230,c_9]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_7834,plain,
% 7.68/1.51      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(sK3,sK3)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
% 7.68/1.51      inference(light_normalisation,[status(thm)],[c_7718,c_2236]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_2233,plain,
% 7.68/1.51      ( k5_xboole_0(sK3,k5_xboole_0(sK3,k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) ),
% 7.68/1.51      inference(superposition,[status(thm)],[c_1740,c_1610]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_2235,plain,
% 7.68/1.51      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) = k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
% 7.68/1.51      inference(demodulation,[status(thm)],[c_2233,c_1517]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_981,plain,
% 7.68/1.51      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
% 7.68/1.51      inference(superposition,[status(thm)],[c_11,c_1]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_7264,plain,
% 7.68/1.51      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(sK3,X0)) = k5_xboole_0(X0,k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) ),
% 7.68/1.51      inference(superposition,[status(thm)],[c_2235,c_981]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_7,plain,
% 7.68/1.51      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
% 7.68/1.51      inference(cnf_transformation,[],[f77]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_963,plain,
% 7.68/1.51      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
% 7.68/1.51      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_2610,plain,
% 7.68/1.51      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X0) = iProver_top ),
% 7.68/1.51      inference(superposition,[status(thm)],[c_0,c_963]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_4017,plain,
% 7.68/1.51      ( r1_tarski(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
% 7.68/1.51      inference(superposition,[status(thm)],[c_1513,c_2610]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_5,plain,
% 7.68/1.51      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 7.68/1.51      inference(cnf_transformation,[],[f47]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_964,plain,
% 7.68/1.51      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 7.68/1.51      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_7234,plain,
% 7.68/1.51      ( k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = sK3 ),
% 7.68/1.51      inference(superposition,[status(thm)],[c_4017,c_964]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_7552,plain,
% 7.68/1.51      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(sK3,X0)) = k5_xboole_0(X0,sK3) ),
% 7.68/1.51      inference(light_normalisation,[status(thm)],[c_7264,c_7234]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_7835,plain,
% 7.68/1.51      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k1_xboole_0 ),
% 7.68/1.51      inference(demodulation,[status(thm)],[c_7834,c_12,c_7552]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_17,plain,
% 7.68/1.51      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
% 7.68/1.51      inference(cnf_transformation,[],[f78]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_664,plain,
% 7.68/1.51      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) ),
% 7.68/1.51      inference(theory_normalisation,[status(thm)],[c_17,c_11,c_1]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_1254,plain,
% 7.68/1.51      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
% 7.68/1.51      inference(superposition,[status(thm)],[c_0,c_664]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_14949,plain,
% 7.68/1.51      ( k5_xboole_0(sK2,k5_xboole_0(sK2,k3_xboole_0(sK2,sK2))) = k3_tarski(k1_xboole_0) ),
% 7.68/1.51      inference(superposition,[status(thm)],[c_7835,c_1254]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_19,plain,
% 7.68/1.51      ( k3_tarski(k1_xboole_0) = k1_xboole_0 ),
% 7.68/1.51      inference(cnf_transformation,[],[f69]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_14951,plain,
% 7.68/1.51      ( k5_xboole_0(sK2,k5_xboole_0(sK2,k3_xboole_0(sK2,sK2))) = k1_xboole_0 ),
% 7.68/1.51      inference(light_normalisation,[status(thm)],[c_14949,c_19]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_1368,plain,
% 7.68/1.51      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 7.68/1.51      inference(superposition,[status(thm)],[c_12,c_11]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_1377,plain,
% 7.68/1.51      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
% 7.68/1.51      inference(demodulation,[status(thm)],[c_1368,c_1257]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_6,plain,
% 7.68/1.51      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 7.68/1.51      inference(cnf_transformation,[],[f48]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_2612,plain,
% 7.68/1.51      ( r1_tarski(k5_xboole_0(X0,k1_xboole_0),X0) = iProver_top ),
% 7.68/1.51      inference(superposition,[status(thm)],[c_6,c_963]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_2617,plain,
% 7.68/1.51      ( r1_tarski(X0,X0) = iProver_top ),
% 7.68/1.51      inference(light_normalisation,[status(thm)],[c_2612,c_9]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_3704,plain,
% 7.68/1.51      ( k3_xboole_0(X0,X0) = X0 ),
% 7.68/1.51      inference(superposition,[status(thm)],[c_2617,c_964]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_14952,plain,
% 7.68/1.51      ( sK2 = k1_xboole_0 ),
% 7.68/1.51      inference(demodulation,
% 7.68/1.51                [status(thm)],
% 7.68/1.51                [c_14951,c_9,c_12,c_1377,c_3704]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_14953,plain,
% 7.68/1.51      ( k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 7.68/1.51      inference(demodulation,[status(thm)],[c_14952,c_7835]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_667,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_1412,plain,
% 7.68/1.51      ( X0 != X1
% 7.68/1.51      | X0 = k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
% 7.68/1.51      | k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != X1 ),
% 7.68/1.51      inference(instantiation,[status(thm)],[c_667]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_1413,plain,
% 7.68/1.51      ( k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 7.68/1.51      | k1_xboole_0 = k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
% 7.68/1.51      | k1_xboole_0 != k1_xboole_0 ),
% 7.68/1.51      inference(instantiation,[status(thm)],[c_1412]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_670,plain,
% 7.68/1.51      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.68/1.51      theory(equality) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_1216,plain,
% 7.68/1.51      ( r2_hidden(X0,X1)
% 7.68/1.51      | ~ r2_hidden(X2,k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
% 7.68/1.51      | X0 != X2
% 7.68/1.51      | X1 != k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
% 7.68/1.51      inference(instantiation,[status(thm)],[c_670]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_1223,plain,
% 7.68/1.51      ( ~ r2_hidden(k1_xboole_0,k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
% 7.68/1.51      | r2_hidden(k1_xboole_0,k1_xboole_0)
% 7.68/1.51      | k1_xboole_0 != k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
% 7.68/1.51      | k1_xboole_0 != k1_xboole_0 ),
% 7.68/1.51      inference(instantiation,[status(thm)],[c_1216]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_1009,plain,
% 7.68/1.51      ( r2_hidden(X0,X1)
% 7.68/1.51      | ~ r2_hidden(X2,k1_zfmisc_1(X3))
% 7.68/1.51      | X0 != X2
% 7.68/1.51      | X1 != k1_zfmisc_1(X3) ),
% 7.68/1.51      inference(instantiation,[status(thm)],[c_670]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_1143,plain,
% 7.68/1.51      ( r2_hidden(X0,k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
% 7.68/1.51      | ~ r2_hidden(X1,k1_zfmisc_1(k1_xboole_0))
% 7.68/1.51      | X0 != X1
% 7.68/1.51      | k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_zfmisc_1(k1_xboole_0) ),
% 7.68/1.51      inference(instantiation,[status(thm)],[c_1009]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_1145,plain,
% 7.68/1.51      ( r2_hidden(k1_xboole_0,k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
% 7.68/1.51      | ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
% 7.68/1.51      | k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_zfmisc_1(k1_xboole_0)
% 7.68/1.51      | k1_xboole_0 != k1_xboole_0 ),
% 7.68/1.51      inference(instantiation,[status(thm)],[c_1143]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_671,plain,
% 7.68/1.51      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.68/1.51      theory(equality) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_1103,plain,
% 7.68/1.51      ( r1_tarski(X0,X1)
% 7.68/1.51      | ~ r1_tarski(k3_xboole_0(X2,X3),X2)
% 7.68/1.51      | X1 != X2
% 7.68/1.51      | X0 != k3_xboole_0(X2,X3) ),
% 7.68/1.51      inference(instantiation,[status(thm)],[c_671]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_1105,plain,
% 7.68/1.51      ( ~ r1_tarski(k3_xboole_0(k1_xboole_0,k1_xboole_0),k1_xboole_0)
% 7.68/1.51      | r1_tarski(k1_xboole_0,k1_xboole_0)
% 7.68/1.51      | k1_xboole_0 != k3_xboole_0(k1_xboole_0,k1_xboole_0)
% 7.68/1.51      | k1_xboole_0 != k1_xboole_0 ),
% 7.68/1.51      inference(instantiation,[status(thm)],[c_1103]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_2,plain,
% 7.68/1.51      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2)) | ~ r1_xboole_0(X1,X2) ),
% 7.68/1.51      inference(cnf_transformation,[],[f44]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_10,plain,
% 7.68/1.51      ( r1_xboole_0(X0,k1_xboole_0) ),
% 7.68/1.51      inference(cnf_transformation,[],[f52]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_197,plain,
% 7.68/1.51      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
% 7.68/1.51      | X3 != X1
% 7.68/1.51      | k1_xboole_0 != X2 ),
% 7.68/1.51      inference(resolution_lifted,[status(thm)],[c_2,c_10]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_198,plain,
% 7.68/1.51      ( ~ r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) ),
% 7.68/1.51      inference(unflattening,[status(thm)],[c_197]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_956,plain,
% 7.68/1.51      ( r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) != iProver_top ),
% 7.68/1.51      inference(predicate_to_equality,[status(thm)],[c_198]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_966,plain,
% 7.68/1.51      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.68/1.51      inference(demodulation,[status(thm)],[c_956,c_6]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_972,plain,
% 7.68/1.51      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 7.68/1.51      inference(predicate_to_equality_rev,[status(thm)],[c_966]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_974,plain,
% 7.68/1.51      ( ~ r2_hidden(k1_xboole_0,k1_xboole_0) ),
% 7.68/1.51      inference(instantiation,[status(thm)],[c_972]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_666,plain,( X0 = X0 ),theory(equality) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_681,plain,
% 7.68/1.51      ( k1_xboole_0 = k1_xboole_0 ),
% 7.68/1.51      inference(instantiation,[status(thm)],[c_666]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_4,plain,
% 7.68/1.51      ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
% 7.68/1.51      inference(cnf_transformation,[],[f46]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_8,plain,
% 7.68/1.51      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 7.68/1.51      inference(cnf_transformation,[],[f50]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_237,plain,
% 7.68/1.51      ( k3_xboole_0(X0,X1) != X2 | k1_xboole_0 != X0 | k1_xboole_0 = X2 ),
% 7.68/1.51      inference(resolution_lifted,[status(thm)],[c_4,c_8]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_238,plain,
% 7.68/1.51      ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
% 7.68/1.51      inference(unflattening,[status(thm)],[c_237]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_239,plain,
% 7.68/1.51      ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 7.68/1.51      inference(instantiation,[status(thm)],[c_238]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_48,plain,
% 7.68/1.51      ( r1_tarski(k3_xboole_0(k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
% 7.68/1.51      inference(instantiation,[status(thm)],[c_4]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_15,plain,
% 7.68/1.51      ( ~ r1_tarski(X0,X1) | r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 7.68/1.51      inference(cnf_transformation,[],[f81]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_26,plain,
% 7.68/1.51      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 7.68/1.51      | r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
% 7.68/1.51      inference(instantiation,[status(thm)],[c_15]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(c_18,plain,
% 7.68/1.51      ( k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_zfmisc_1(k1_xboole_0) ),
% 7.68/1.51      inference(cnf_transformation,[],[f79]) ).
% 7.68/1.51  
% 7.68/1.51  cnf(contradiction,plain,
% 7.68/1.51      ( $false ),
% 7.68/1.51      inference(minisat,
% 7.68/1.51                [status(thm)],
% 7.68/1.51                [c_14953,c_1413,c_1223,c_1145,c_1105,c_974,c_681,c_239,
% 7.68/1.51                 c_48,c_26,c_18]) ).
% 7.68/1.51  
% 7.68/1.51  
% 7.68/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 7.68/1.51  
% 7.68/1.51  ------                               Statistics
% 7.68/1.51  
% 7.68/1.51  ------ General
% 7.68/1.51  
% 7.68/1.51  abstr_ref_over_cycles:                  0
% 7.68/1.51  abstr_ref_under_cycles:                 0
% 7.68/1.51  gc_basic_clause_elim:                   0
% 7.68/1.51  forced_gc_time:                         0
% 7.68/1.51  parsing_time:                           0.008
% 7.68/1.51  unif_index_cands_time:                  0.
% 7.68/1.51  unif_index_add_time:                    0.
% 7.68/1.51  orderings_time:                         0.
% 7.68/1.51  out_proof_time:                         0.009
% 7.68/1.51  total_time:                             0.543
% 7.68/1.51  num_of_symbols:                         44
% 7.68/1.51  num_of_terms:                           29543
% 7.68/1.51  
% 7.68/1.51  ------ Preprocessing
% 7.68/1.51  
% 7.68/1.51  num_of_splits:                          0
% 7.68/1.51  num_of_split_atoms:                     0
% 7.68/1.51  num_of_reused_defs:                     0
% 7.68/1.51  num_eq_ax_congr_red:                    13
% 7.68/1.51  num_of_sem_filtered_clauses:            1
% 7.68/1.51  num_of_subtypes:                        0
% 7.68/1.51  monotx_restored_types:                  0
% 7.68/1.51  sat_num_of_epr_types:                   0
% 7.68/1.51  sat_num_of_non_cyclic_types:            0
% 7.68/1.51  sat_guarded_non_collapsed_types:        0
% 7.68/1.51  num_pure_diseq_elim:                    0
% 7.68/1.51  simp_replaced_by:                       0
% 7.68/1.51  res_preprocessed:                       100
% 7.68/1.51  prep_upred:                             0
% 7.68/1.51  prep_unflattend:                        52
% 7.68/1.51  smt_new_axioms:                         0
% 7.68/1.51  pred_elim_cands:                        2
% 7.68/1.51  pred_elim:                              1
% 7.68/1.51  pred_elim_cl:                           1
% 7.68/1.51  pred_elim_cycles:                       3
% 7.68/1.51  merged_defs:                            8
% 7.68/1.51  merged_defs_ncl:                        0
% 7.68/1.51  bin_hyper_res:                          8
% 7.68/1.51  prep_cycles:                            4
% 7.68/1.51  pred_elim_time:                         0.004
% 7.68/1.51  splitting_time:                         0.
% 7.68/1.51  sem_filter_time:                        0.
% 7.68/1.51  monotx_time:                            0.
% 7.68/1.51  subtype_inf_time:                       0.
% 7.68/1.51  
% 7.68/1.51  ------ Problem properties
% 7.68/1.51  
% 7.68/1.51  clauses:                                20
% 7.68/1.51  conjectures:                            1
% 7.68/1.51  epr:                                    1
% 7.68/1.51  horn:                                   19
% 7.68/1.51  ground:                                 3
% 7.68/1.51  unary:                                  13
% 7.68/1.51  binary:                                 5
% 7.68/1.51  lits:                                   29
% 7.68/1.51  lits_eq:                                14
% 7.68/1.51  fd_pure:                                0
% 7.68/1.51  fd_pseudo:                              0
% 7.68/1.51  fd_cond:                                1
% 7.68/1.51  fd_pseudo_cond:                         2
% 7.68/1.51  ac_symbols:                             1
% 7.68/1.51  
% 7.68/1.51  ------ Propositional Solver
% 7.68/1.51  
% 7.68/1.51  prop_solver_calls:                      34
% 7.68/1.51  prop_fast_solver_calls:                 633
% 7.68/1.51  smt_solver_calls:                       0
% 7.68/1.51  smt_fast_solver_calls:                  0
% 7.68/1.51  prop_num_of_clauses:                    4427
% 7.68/1.51  prop_preprocess_simplified:             7129
% 7.68/1.51  prop_fo_subsumed:                       0
% 7.68/1.51  prop_solver_time:                       0.
% 7.68/1.51  smt_solver_time:                        0.
% 7.68/1.51  smt_fast_solver_time:                   0.
% 7.68/1.51  prop_fast_solver_time:                  0.
% 7.68/1.51  prop_unsat_core_time:                   0.
% 7.68/1.51  
% 7.68/1.51  ------ QBF
% 7.68/1.51  
% 7.68/1.51  qbf_q_res:                              0
% 7.68/1.51  qbf_num_tautologies:                    0
% 7.68/1.51  qbf_prep_cycles:                        0
% 7.68/1.51  
% 7.68/1.51  ------ BMC1
% 7.68/1.51  
% 7.68/1.51  bmc1_current_bound:                     -1
% 7.68/1.51  bmc1_last_solved_bound:                 -1
% 7.68/1.51  bmc1_unsat_core_size:                   -1
% 7.68/1.51  bmc1_unsat_core_parents_size:           -1
% 7.68/1.51  bmc1_merge_next_fun:                    0
% 7.68/1.51  bmc1_unsat_core_clauses_time:           0.
% 7.68/1.51  
% 7.68/1.51  ------ Instantiation
% 7.68/1.51  
% 7.68/1.51  inst_num_of_clauses:                    948
% 7.68/1.51  inst_num_in_passive:                    172
% 7.68/1.51  inst_num_in_active:                     435
% 7.68/1.51  inst_num_in_unprocessed:                341
% 7.68/1.51  inst_num_of_loops:                      480
% 7.68/1.51  inst_num_of_learning_restarts:          0
% 7.68/1.51  inst_num_moves_active_passive:          37
% 7.68/1.51  inst_lit_activity:                      0
% 7.68/1.51  inst_lit_activity_moves:                0
% 7.68/1.51  inst_num_tautologies:                   0
% 7.68/1.51  inst_num_prop_implied:                  0
% 7.68/1.51  inst_num_existing_simplified:           0
% 7.68/1.51  inst_num_eq_res_simplified:             0
% 7.68/1.51  inst_num_child_elim:                    0
% 7.68/1.51  inst_num_of_dismatching_blockings:      363
% 7.68/1.51  inst_num_of_non_proper_insts:           1208
% 7.68/1.51  inst_num_of_duplicates:                 0
% 7.68/1.51  inst_inst_num_from_inst_to_res:         0
% 7.68/1.51  inst_dismatching_checking_time:         0.
% 7.68/1.51  
% 7.68/1.51  ------ Resolution
% 7.68/1.51  
% 7.68/1.51  res_num_of_clauses:                     0
% 7.68/1.51  res_num_in_passive:                     0
% 7.68/1.51  res_num_in_active:                      0
% 7.68/1.51  res_num_of_loops:                       104
% 7.68/1.51  res_forward_subset_subsumed:            42
% 7.68/1.51  res_backward_subset_subsumed:           0
% 7.68/1.51  res_forward_subsumed:                   0
% 7.68/1.51  res_backward_subsumed:                  0
% 7.68/1.51  res_forward_subsumption_resolution:     0
% 7.68/1.51  res_backward_subsumption_resolution:    0
% 7.68/1.51  res_clause_to_clause_subsumption:       15388
% 7.68/1.51  res_orphan_elimination:                 0
% 7.68/1.51  res_tautology_del:                      115
% 7.68/1.51  res_num_eq_res_simplified:              0
% 7.68/1.51  res_num_sel_changes:                    0
% 7.68/1.51  res_moves_from_active_to_pass:          0
% 7.68/1.51  
% 7.68/1.51  ------ Superposition
% 7.68/1.51  
% 7.68/1.51  sup_time_total:                         0.
% 7.68/1.51  sup_time_generating:                    0.
% 7.68/1.51  sup_time_sim_full:                      0.
% 7.68/1.51  sup_time_sim_immed:                     0.
% 7.68/1.51  
% 7.68/1.51  sup_num_of_clauses:                     1241
% 7.68/1.51  sup_num_in_active:                      43
% 7.68/1.51  sup_num_in_passive:                     1198
% 7.68/1.51  sup_num_of_loops:                       94
% 7.68/1.51  sup_fw_superposition:                   3170
% 7.68/1.51  sup_bw_superposition:                   2135
% 7.68/1.51  sup_immediate_simplified:               2106
% 7.68/1.51  sup_given_eliminated:                   7
% 7.68/1.51  comparisons_done:                       0
% 7.68/1.51  comparisons_avoided:                    0
% 7.68/1.51  
% 7.68/1.51  ------ Simplifications
% 7.68/1.51  
% 7.68/1.51  
% 7.68/1.51  sim_fw_subset_subsumed:                 2
% 7.68/1.51  sim_bw_subset_subsumed:                 0
% 7.68/1.51  sim_fw_subsumed:                        168
% 7.68/1.51  sim_bw_subsumed:                        9
% 7.68/1.51  sim_fw_subsumption_res:                 0
% 7.68/1.51  sim_bw_subsumption_res:                 0
% 7.68/1.51  sim_tautology_del:                      0
% 7.68/1.51  sim_eq_tautology_del:                   589
% 7.68/1.51  sim_eq_res_simp:                        0
% 7.68/1.51  sim_fw_demodulated:                     1929
% 7.68/1.51  sim_bw_demodulated:                     88
% 7.68/1.51  sim_light_normalised:                   906
% 7.68/1.51  sim_joinable_taut:                      152
% 7.68/1.51  sim_joinable_simp:                      0
% 7.68/1.51  sim_ac_normalised:                      0
% 7.68/1.51  sim_smt_subsumption:                    0
% 7.68/1.51  
%------------------------------------------------------------------------------
