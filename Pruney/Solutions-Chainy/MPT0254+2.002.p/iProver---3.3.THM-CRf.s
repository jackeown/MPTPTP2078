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
% DateTime   : Thu Dec  3 11:33:46 EST 2020

% Result     : Theorem 3.75s
% Output     : CNFRefutation 3.75s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 522 expanded)
%              Number of clauses        :   56 ( 150 expanded)
%              Number of leaves         :   27 ( 148 expanded)
%              Depth                    :   24
%              Number of atoms          :  212 ( 611 expanded)
%              Number of equality atoms :  124 ( 515 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :   10 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f12])).

fof(f25,conjecture,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,negated_conjecture,(
    ~ ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(negated_conjecture,[],[f25])).

fof(f29,plain,(
    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1) ),
    inference(ennf_transformation,[],[f26])).

fof(f36,plain,
    ( ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1)
   => k1_xboole_0 = k2_xboole_0(k1_tarski(sK1),sK2) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    k1_xboole_0 = k2_xboole_0(k1_tarski(sK1),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f29,f36])).

fof(f67,plain,(
    k1_xboole_0 = k2_xboole_0(k1_tarski(sK1),sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f13,axiom,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f68,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f52,f48])).

fof(f14,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f18])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f19])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f20])).

fof(f69,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f58,f59])).

fof(f70,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f57,f69])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f56,f70])).

fof(f72,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f55,f71])).

fof(f73,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f54,f72])).

fof(f74,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f53,f73])).

fof(f80,plain,(
    k5_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2))) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f67,f68,f74])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f75,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f44,f48])).

fof(f10,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f76,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f39,f48,f48])).

fof(f22,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f78,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f64,f68,f73])).

fof(f24,axiom,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f24])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f77,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f45,f48])).

fof(f8,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f47,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
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
    inference(nnf_transformation,[],[f4])).

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
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f82,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f41])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
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

fof(f33,plain,(
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
    inference(rectify,[],[f32])).

fof(f34,plain,(
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

fof(f35,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).

fof(f61,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f83,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f61])).

fof(f23,axiom,(
    k1_tarski(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    k1_tarski(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f23])).

fof(f79,plain,(
    k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_zfmisc_1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f65,f74])).

cnf(c_12,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_20,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_11,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_3,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_288,negated_conjecture,
    ( k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)))) = k1_xboole_0 ),
    inference(theory_normalisation,[status(thm)],[c_20,c_11,c_3])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_590,plain,
    ( k5_xboole_0(sK2,k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_288,c_0])).

cnf(c_1210,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2),X0)) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_590,c_11])).

cnf(c_10,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1013,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_10,c_3])).

cnf(c_1220,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2),X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1210,c_1013])).

cnf(c_1417,plain,
    ( k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2) = k5_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_12,c_1220])).

cnf(c_1422,plain,
    ( k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2) = sK2 ),
    inference(demodulation,[status(thm)],[c_1417,c_10])).

cnf(c_1870,plain,
    ( k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)) = k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2) ),
    inference(superposition,[status(thm)],[c_1422,c_0])).

cnf(c_1873,plain,
    ( k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2) = sK2 ),
    inference(demodulation,[status(thm)],[c_1870,c_1422])).

cnf(c_601,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_11,c_3])).

cnf(c_3745,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_12,c_601])).

cnf(c_3920,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(demodulation,[status(thm)],[c_3745,c_10])).

cnf(c_8012,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k5_xboole_0(sK2,sK2) ),
    inference(superposition,[status(thm)],[c_1873,c_3920])).

cnf(c_8207,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_8012,c_12])).

cnf(c_2,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_17,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_289,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(theory_normalisation,[status(thm)],[c_17,c_11,c_3])).

cnf(c_1196,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
    inference(superposition,[status(thm)],[c_2,c_289])).

cnf(c_1197,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_1196,c_0])).

cnf(c_11194,plain,
    ( k5_xboole_0(sK1,k4_xboole_0(sK1,sK1)) = k3_tarski(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_8207,c_1197])).

cnf(c_19,plain,
    ( k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_11195,plain,
    ( k5_xboole_0(sK1,k4_xboole_0(sK1,sK1)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_11194,c_19])).

cnf(c_1105,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_1013,c_0])).

cnf(c_7,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_586,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_584,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2450,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_586,c_584])).

cnf(c_4083,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1105,c_2450])).

cnf(c_4096,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4083,c_2])).

cnf(c_4114,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_4096,c_0])).

cnf(c_4124,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_4114,c_10])).

cnf(c_4125,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4124,c_4096])).

cnf(c_11196,plain,
    ( sK1 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_11195,c_10,c_4125])).

cnf(c_11197,plain,
    ( k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_11196,c_8207])).

cnf(c_295,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_615,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k1_zfmisc_1(X3))
    | X0 != X2
    | X1 != k1_zfmisc_1(X3) ),
    inference(instantiation,[status(thm)],[c_295])).

cnf(c_645,plain,
    ( r2_hidden(X0,k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | ~ r2_hidden(X1,k1_zfmisc_1(k1_xboole_0))
    | X0 != X1
    | k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_zfmisc_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_615])).

cnf(c_1906,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(k1_xboole_0))
    | r2_hidden(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != X0
    | k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_zfmisc_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_645])).

cnf(c_4026,plain,
    ( r2_hidden(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_zfmisc_1(k1_xboole_0)
    | k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1906])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_660,plain,
    ( ~ r2_hidden(X0,k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | ~ r2_hidden(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),X0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1905,plain,
    ( ~ r2_hidden(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_660])).

cnf(c_6,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1003,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_15,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_688,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | r2_hidden(X0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_810,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_688])).

cnf(c_18,plain,
    ( k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_zfmisc_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f79])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11197,c_4026,c_1905,c_1003,c_810,c_18])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n018.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 10:33:11 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.75/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.75/0.98  
% 3.75/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.75/0.98  
% 3.75/0.98  ------  iProver source info
% 3.75/0.98  
% 3.75/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.75/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.75/0.98  git: non_committed_changes: false
% 3.75/0.98  git: last_make_outside_of_git: false
% 3.75/0.98  
% 3.75/0.98  ------ 
% 3.75/0.98  
% 3.75/0.98  ------ Input Options
% 3.75/0.98  
% 3.75/0.98  --out_options                           all
% 3.75/0.98  --tptp_safe_out                         true
% 3.75/0.98  --problem_path                          ""
% 3.75/0.98  --include_path                          ""
% 3.75/0.98  --clausifier                            res/vclausify_rel
% 3.75/0.98  --clausifier_options                    ""
% 3.75/0.98  --stdin                                 false
% 3.75/0.98  --stats_out                             all
% 3.75/0.98  
% 3.75/0.98  ------ General Options
% 3.75/0.98  
% 3.75/0.98  --fof                                   false
% 3.75/0.98  --time_out_real                         305.
% 3.75/0.98  --time_out_virtual                      -1.
% 3.75/0.98  --symbol_type_check                     false
% 3.75/0.98  --clausify_out                          false
% 3.75/0.98  --sig_cnt_out                           false
% 3.75/0.98  --trig_cnt_out                          false
% 3.75/0.98  --trig_cnt_out_tolerance                1.
% 3.75/0.98  --trig_cnt_out_sk_spl                   false
% 3.75/0.98  --abstr_cl_out                          false
% 3.75/0.98  
% 3.75/0.98  ------ Global Options
% 3.75/0.98  
% 3.75/0.98  --schedule                              default
% 3.75/0.98  --add_important_lit                     false
% 3.75/0.98  --prop_solver_per_cl                    1000
% 3.75/0.98  --min_unsat_core                        false
% 3.75/0.98  --soft_assumptions                      false
% 3.75/0.98  --soft_lemma_size                       3
% 3.75/0.98  --prop_impl_unit_size                   0
% 3.75/0.98  --prop_impl_unit                        []
% 3.75/0.98  --share_sel_clauses                     true
% 3.75/0.98  --reset_solvers                         false
% 3.75/0.98  --bc_imp_inh                            [conj_cone]
% 3.75/0.98  --conj_cone_tolerance                   3.
% 3.75/0.98  --extra_neg_conj                        none
% 3.75/0.98  --large_theory_mode                     true
% 3.75/0.98  --prolific_symb_bound                   200
% 3.75/0.98  --lt_threshold                          2000
% 3.75/0.98  --clause_weak_htbl                      true
% 3.75/0.98  --gc_record_bc_elim                     false
% 3.75/0.98  
% 3.75/0.98  ------ Preprocessing Options
% 3.75/0.98  
% 3.75/0.98  --preprocessing_flag                    true
% 3.75/0.98  --time_out_prep_mult                    0.1
% 3.75/0.98  --splitting_mode                        input
% 3.75/0.98  --splitting_grd                         true
% 3.75/0.98  --splitting_cvd                         false
% 3.75/0.98  --splitting_cvd_svl                     false
% 3.75/0.98  --splitting_nvd                         32
% 3.75/0.98  --sub_typing                            true
% 3.75/0.98  --prep_gs_sim                           true
% 3.75/0.98  --prep_unflatten                        true
% 3.75/0.98  --prep_res_sim                          true
% 3.75/0.98  --prep_upred                            true
% 3.75/0.98  --prep_sem_filter                       exhaustive
% 3.75/0.98  --prep_sem_filter_out                   false
% 3.75/0.98  --pred_elim                             true
% 3.75/0.98  --res_sim_input                         true
% 3.75/0.98  --eq_ax_congr_red                       true
% 3.75/0.98  --pure_diseq_elim                       true
% 3.75/0.98  --brand_transform                       false
% 3.75/0.98  --non_eq_to_eq                          false
% 3.75/0.98  --prep_def_merge                        true
% 3.75/0.98  --prep_def_merge_prop_impl              false
% 3.75/0.98  --prep_def_merge_mbd                    true
% 3.75/0.98  --prep_def_merge_tr_red                 false
% 3.75/0.98  --prep_def_merge_tr_cl                  false
% 3.75/0.98  --smt_preprocessing                     true
% 3.75/0.98  --smt_ac_axioms                         fast
% 3.75/0.98  --preprocessed_out                      false
% 3.75/0.98  --preprocessed_stats                    false
% 3.75/0.98  
% 3.75/0.98  ------ Abstraction refinement Options
% 3.75/0.98  
% 3.75/0.98  --abstr_ref                             []
% 3.75/0.98  --abstr_ref_prep                        false
% 3.75/0.98  --abstr_ref_until_sat                   false
% 3.75/0.98  --abstr_ref_sig_restrict                funpre
% 3.75/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.75/0.98  --abstr_ref_under                       []
% 3.75/0.98  
% 3.75/0.98  ------ SAT Options
% 3.75/0.98  
% 3.75/0.98  --sat_mode                              false
% 3.75/0.98  --sat_fm_restart_options                ""
% 3.75/0.98  --sat_gr_def                            false
% 3.75/0.98  --sat_epr_types                         true
% 3.75/0.98  --sat_non_cyclic_types                  false
% 3.75/0.98  --sat_finite_models                     false
% 3.75/0.98  --sat_fm_lemmas                         false
% 3.75/0.98  --sat_fm_prep                           false
% 3.75/0.98  --sat_fm_uc_incr                        true
% 3.75/0.98  --sat_out_model                         small
% 3.75/0.98  --sat_out_clauses                       false
% 3.75/0.98  
% 3.75/0.98  ------ QBF Options
% 3.75/0.98  
% 3.75/0.98  --qbf_mode                              false
% 3.75/0.98  --qbf_elim_univ                         false
% 3.75/0.98  --qbf_dom_inst                          none
% 3.75/0.98  --qbf_dom_pre_inst                      false
% 3.75/0.98  --qbf_sk_in                             false
% 3.75/0.98  --qbf_pred_elim                         true
% 3.75/0.98  --qbf_split                             512
% 3.75/0.98  
% 3.75/0.98  ------ BMC1 Options
% 3.75/0.98  
% 3.75/0.98  --bmc1_incremental                      false
% 3.75/0.98  --bmc1_axioms                           reachable_all
% 3.75/0.98  --bmc1_min_bound                        0
% 3.75/0.98  --bmc1_max_bound                        -1
% 3.75/0.98  --bmc1_max_bound_default                -1
% 3.75/0.98  --bmc1_symbol_reachability              true
% 3.75/0.98  --bmc1_property_lemmas                  false
% 3.75/0.98  --bmc1_k_induction                      false
% 3.75/0.98  --bmc1_non_equiv_states                 false
% 3.75/0.98  --bmc1_deadlock                         false
% 3.75/0.98  --bmc1_ucm                              false
% 3.75/0.98  --bmc1_add_unsat_core                   none
% 3.75/0.98  --bmc1_unsat_core_children              false
% 3.75/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.75/0.98  --bmc1_out_stat                         full
% 3.75/0.98  --bmc1_ground_init                      false
% 3.75/0.98  --bmc1_pre_inst_next_state              false
% 3.75/0.98  --bmc1_pre_inst_state                   false
% 3.75/0.98  --bmc1_pre_inst_reach_state             false
% 3.75/0.98  --bmc1_out_unsat_core                   false
% 3.75/0.98  --bmc1_aig_witness_out                  false
% 3.75/0.98  --bmc1_verbose                          false
% 3.75/0.98  --bmc1_dump_clauses_tptp                false
% 3.75/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.75/0.98  --bmc1_dump_file                        -
% 3.75/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.75/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.75/0.98  --bmc1_ucm_extend_mode                  1
% 3.75/0.98  --bmc1_ucm_init_mode                    2
% 3.75/0.98  --bmc1_ucm_cone_mode                    none
% 3.75/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.75/0.98  --bmc1_ucm_relax_model                  4
% 3.75/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.75/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.75/0.98  --bmc1_ucm_layered_model                none
% 3.75/0.98  --bmc1_ucm_max_lemma_size               10
% 3.75/0.98  
% 3.75/0.98  ------ AIG Options
% 3.75/0.98  
% 3.75/0.98  --aig_mode                              false
% 3.75/0.98  
% 3.75/0.98  ------ Instantiation Options
% 3.75/0.98  
% 3.75/0.98  --instantiation_flag                    true
% 3.75/0.98  --inst_sos_flag                         true
% 3.75/0.98  --inst_sos_phase                        true
% 3.75/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.75/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.75/0.98  --inst_lit_sel_side                     num_symb
% 3.75/0.98  --inst_solver_per_active                1400
% 3.75/0.98  --inst_solver_calls_frac                1.
% 3.75/0.98  --inst_passive_queue_type               priority_queues
% 3.75/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.75/0.98  --inst_passive_queues_freq              [25;2]
% 3.75/0.98  --inst_dismatching                      true
% 3.75/0.98  --inst_eager_unprocessed_to_passive     true
% 3.75/0.98  --inst_prop_sim_given                   true
% 3.75/0.98  --inst_prop_sim_new                     false
% 3.75/0.98  --inst_subs_new                         false
% 3.75/0.98  --inst_eq_res_simp                      false
% 3.75/0.98  --inst_subs_given                       false
% 3.75/0.98  --inst_orphan_elimination               true
% 3.75/0.98  --inst_learning_loop_flag               true
% 3.75/0.98  --inst_learning_start                   3000
% 3.75/0.98  --inst_learning_factor                  2
% 3.75/0.98  --inst_start_prop_sim_after_learn       3
% 3.75/0.98  --inst_sel_renew                        solver
% 3.75/0.98  --inst_lit_activity_flag                true
% 3.75/0.98  --inst_restr_to_given                   false
% 3.75/0.98  --inst_activity_threshold               500
% 3.75/0.98  --inst_out_proof                        true
% 3.75/0.98  
% 3.75/0.98  ------ Resolution Options
% 3.75/0.98  
% 3.75/0.98  --resolution_flag                       true
% 3.75/0.98  --res_lit_sel                           adaptive
% 3.75/0.98  --res_lit_sel_side                      none
% 3.75/0.98  --res_ordering                          kbo
% 3.75/0.98  --res_to_prop_solver                    active
% 3.75/0.98  --res_prop_simpl_new                    false
% 3.75/0.98  --res_prop_simpl_given                  true
% 3.75/0.98  --res_passive_queue_type                priority_queues
% 3.75/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.75/0.98  --res_passive_queues_freq               [15;5]
% 3.75/0.98  --res_forward_subs                      full
% 3.75/0.98  --res_backward_subs                     full
% 3.75/0.98  --res_forward_subs_resolution           true
% 3.75/0.98  --res_backward_subs_resolution          true
% 3.75/0.98  --res_orphan_elimination                true
% 3.75/0.98  --res_time_limit                        2.
% 3.75/0.98  --res_out_proof                         true
% 3.75/0.98  
% 3.75/0.98  ------ Superposition Options
% 3.75/0.98  
% 3.75/0.98  --superposition_flag                    true
% 3.75/0.98  --sup_passive_queue_type                priority_queues
% 3.75/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.75/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.75/0.98  --demod_completeness_check              fast
% 3.75/0.98  --demod_use_ground                      true
% 3.75/0.98  --sup_to_prop_solver                    passive
% 3.75/0.98  --sup_prop_simpl_new                    true
% 3.75/0.98  --sup_prop_simpl_given                  true
% 3.75/0.98  --sup_fun_splitting                     true
% 3.75/0.98  --sup_smt_interval                      50000
% 3.75/0.98  
% 3.75/0.98  ------ Superposition Simplification Setup
% 3.75/0.98  
% 3.75/0.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.75/0.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.75/0.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.75/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.75/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.75/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.75/0.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.75/0.98  --sup_immed_triv                        [TrivRules]
% 3.75/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.75/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.75/0.98  --sup_immed_bw_main                     []
% 3.75/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.75/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.75/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.75/0.98  --sup_input_bw                          []
% 3.75/0.98  
% 3.75/0.98  ------ Combination Options
% 3.75/0.98  
% 3.75/0.98  --comb_res_mult                         3
% 3.75/0.98  --comb_sup_mult                         2
% 3.75/0.98  --comb_inst_mult                        10
% 3.75/0.98  
% 3.75/0.98  ------ Debug Options
% 3.75/0.98  
% 3.75/0.98  --dbg_backtrace                         false
% 3.75/0.98  --dbg_dump_prop_clauses                 false
% 3.75/0.98  --dbg_dump_prop_clauses_file            -
% 3.75/0.98  --dbg_out_stat                          false
% 3.75/0.98  ------ Parsing...
% 3.75/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.75/0.98  
% 3.75/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.75/0.98  
% 3.75/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.75/0.98  
% 3.75/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.75/0.98  ------ Proving...
% 3.75/0.98  ------ Problem Properties 
% 3.75/0.98  
% 3.75/0.98  
% 3.75/0.98  clauses                                 20
% 3.75/0.98  conjectures                             1
% 3.75/0.98  EPR                                     5
% 3.75/0.98  Horn                                    19
% 3.75/0.98  unary                                   13
% 3.75/0.98  binary                                  4
% 3.75/0.98  lits                                    30
% 3.75/0.98  lits eq                                 14
% 3.75/0.98  fd_pure                                 0
% 3.75/0.98  fd_pseudo                               0
% 3.75/0.98  fd_cond                                 1
% 3.75/0.98  fd_pseudo_cond                          3
% 3.75/0.98  AC symbols                              1
% 3.75/0.98  
% 3.75/0.98  ------ Schedule dynamic 5 is on 
% 3.75/0.98  
% 3.75/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.75/0.98  
% 3.75/0.98  
% 3.75/0.98  ------ 
% 3.75/0.98  Current options:
% 3.75/0.98  ------ 
% 3.75/0.98  
% 3.75/0.98  ------ Input Options
% 3.75/0.98  
% 3.75/0.98  --out_options                           all
% 3.75/0.98  --tptp_safe_out                         true
% 3.75/0.98  --problem_path                          ""
% 3.75/0.98  --include_path                          ""
% 3.75/0.98  --clausifier                            res/vclausify_rel
% 3.75/0.98  --clausifier_options                    ""
% 3.75/0.98  --stdin                                 false
% 3.75/0.98  --stats_out                             all
% 3.75/0.98  
% 3.75/0.98  ------ General Options
% 3.75/0.98  
% 3.75/0.98  --fof                                   false
% 3.75/0.98  --time_out_real                         305.
% 3.75/0.98  --time_out_virtual                      -1.
% 3.75/0.98  --symbol_type_check                     false
% 3.75/0.98  --clausify_out                          false
% 3.75/0.98  --sig_cnt_out                           false
% 3.75/0.98  --trig_cnt_out                          false
% 3.75/0.98  --trig_cnt_out_tolerance                1.
% 3.75/0.98  --trig_cnt_out_sk_spl                   false
% 3.75/0.98  --abstr_cl_out                          false
% 3.75/0.98  
% 3.75/0.98  ------ Global Options
% 3.75/0.98  
% 3.75/0.98  --schedule                              default
% 3.75/0.98  --add_important_lit                     false
% 3.75/0.98  --prop_solver_per_cl                    1000
% 3.75/0.98  --min_unsat_core                        false
% 3.75/0.98  --soft_assumptions                      false
% 3.75/0.98  --soft_lemma_size                       3
% 3.75/0.98  --prop_impl_unit_size                   0
% 3.75/0.98  --prop_impl_unit                        []
% 3.75/0.98  --share_sel_clauses                     true
% 3.75/0.98  --reset_solvers                         false
% 3.75/0.98  --bc_imp_inh                            [conj_cone]
% 3.75/0.98  --conj_cone_tolerance                   3.
% 3.75/0.98  --extra_neg_conj                        none
% 3.75/0.98  --large_theory_mode                     true
% 3.75/0.98  --prolific_symb_bound                   200
% 3.75/0.98  --lt_threshold                          2000
% 3.75/0.98  --clause_weak_htbl                      true
% 3.75/0.98  --gc_record_bc_elim                     false
% 3.75/0.98  
% 3.75/0.98  ------ Preprocessing Options
% 3.75/0.98  
% 3.75/0.98  --preprocessing_flag                    true
% 3.75/0.98  --time_out_prep_mult                    0.1
% 3.75/0.98  --splitting_mode                        input
% 3.75/0.98  --splitting_grd                         true
% 3.75/0.98  --splitting_cvd                         false
% 3.75/0.98  --splitting_cvd_svl                     false
% 3.75/0.98  --splitting_nvd                         32
% 3.75/0.98  --sub_typing                            true
% 3.75/0.98  --prep_gs_sim                           true
% 3.75/0.98  --prep_unflatten                        true
% 3.75/0.98  --prep_res_sim                          true
% 3.75/0.98  --prep_upred                            true
% 3.75/0.98  --prep_sem_filter                       exhaustive
% 3.75/0.98  --prep_sem_filter_out                   false
% 3.75/0.98  --pred_elim                             true
% 3.75/0.98  --res_sim_input                         true
% 3.75/0.98  --eq_ax_congr_red                       true
% 3.75/0.98  --pure_diseq_elim                       true
% 3.75/0.98  --brand_transform                       false
% 3.75/0.98  --non_eq_to_eq                          false
% 3.75/0.98  --prep_def_merge                        true
% 3.75/0.98  --prep_def_merge_prop_impl              false
% 3.75/0.98  --prep_def_merge_mbd                    true
% 3.75/0.98  --prep_def_merge_tr_red                 false
% 3.75/0.98  --prep_def_merge_tr_cl                  false
% 3.75/0.98  --smt_preprocessing                     true
% 3.75/0.98  --smt_ac_axioms                         fast
% 3.75/0.98  --preprocessed_out                      false
% 3.75/0.98  --preprocessed_stats                    false
% 3.75/0.98  
% 3.75/0.98  ------ Abstraction refinement Options
% 3.75/0.98  
% 3.75/0.98  --abstr_ref                             []
% 3.75/0.98  --abstr_ref_prep                        false
% 3.75/0.98  --abstr_ref_until_sat                   false
% 3.75/0.98  --abstr_ref_sig_restrict                funpre
% 3.75/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.75/0.98  --abstr_ref_under                       []
% 3.75/0.98  
% 3.75/0.98  ------ SAT Options
% 3.75/0.98  
% 3.75/0.98  --sat_mode                              false
% 3.75/0.98  --sat_fm_restart_options                ""
% 3.75/0.98  --sat_gr_def                            false
% 3.75/0.98  --sat_epr_types                         true
% 3.75/0.98  --sat_non_cyclic_types                  false
% 3.75/0.98  --sat_finite_models                     false
% 3.75/0.98  --sat_fm_lemmas                         false
% 3.75/0.98  --sat_fm_prep                           false
% 3.75/0.98  --sat_fm_uc_incr                        true
% 3.75/0.98  --sat_out_model                         small
% 3.75/0.98  --sat_out_clauses                       false
% 3.75/0.98  
% 3.75/0.98  ------ QBF Options
% 3.75/0.98  
% 3.75/0.98  --qbf_mode                              false
% 3.75/0.98  --qbf_elim_univ                         false
% 3.75/0.98  --qbf_dom_inst                          none
% 3.75/0.98  --qbf_dom_pre_inst                      false
% 3.75/0.98  --qbf_sk_in                             false
% 3.75/0.98  --qbf_pred_elim                         true
% 3.75/0.98  --qbf_split                             512
% 3.75/0.98  
% 3.75/0.98  ------ BMC1 Options
% 3.75/0.98  
% 3.75/0.98  --bmc1_incremental                      false
% 3.75/0.98  --bmc1_axioms                           reachable_all
% 3.75/0.98  --bmc1_min_bound                        0
% 3.75/0.98  --bmc1_max_bound                        -1
% 3.75/0.98  --bmc1_max_bound_default                -1
% 3.75/0.98  --bmc1_symbol_reachability              true
% 3.75/0.98  --bmc1_property_lemmas                  false
% 3.75/0.98  --bmc1_k_induction                      false
% 3.75/0.98  --bmc1_non_equiv_states                 false
% 3.75/0.99  --bmc1_deadlock                         false
% 3.75/0.99  --bmc1_ucm                              false
% 3.75/0.99  --bmc1_add_unsat_core                   none
% 3.75/0.99  --bmc1_unsat_core_children              false
% 3.75/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.75/0.99  --bmc1_out_stat                         full
% 3.75/0.99  --bmc1_ground_init                      false
% 3.75/0.99  --bmc1_pre_inst_next_state              false
% 3.75/0.99  --bmc1_pre_inst_state                   false
% 3.75/0.99  --bmc1_pre_inst_reach_state             false
% 3.75/0.99  --bmc1_out_unsat_core                   false
% 3.75/0.99  --bmc1_aig_witness_out                  false
% 3.75/0.99  --bmc1_verbose                          false
% 3.75/0.99  --bmc1_dump_clauses_tptp                false
% 3.75/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.75/0.99  --bmc1_dump_file                        -
% 3.75/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.75/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.75/0.99  --bmc1_ucm_extend_mode                  1
% 3.75/0.99  --bmc1_ucm_init_mode                    2
% 3.75/0.99  --bmc1_ucm_cone_mode                    none
% 3.75/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.75/0.99  --bmc1_ucm_relax_model                  4
% 3.75/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.75/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.75/0.99  --bmc1_ucm_layered_model                none
% 3.75/0.99  --bmc1_ucm_max_lemma_size               10
% 3.75/0.99  
% 3.75/0.99  ------ AIG Options
% 3.75/0.99  
% 3.75/0.99  --aig_mode                              false
% 3.75/0.99  
% 3.75/0.99  ------ Instantiation Options
% 3.75/0.99  
% 3.75/0.99  --instantiation_flag                    true
% 3.75/0.99  --inst_sos_flag                         true
% 3.75/0.99  --inst_sos_phase                        true
% 3.75/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.75/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.75/0.99  --inst_lit_sel_side                     none
% 3.75/0.99  --inst_solver_per_active                1400
% 3.75/0.99  --inst_solver_calls_frac                1.
% 3.75/0.99  --inst_passive_queue_type               priority_queues
% 3.75/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.75/0.99  --inst_passive_queues_freq              [25;2]
% 3.75/0.99  --inst_dismatching                      true
% 3.75/0.99  --inst_eager_unprocessed_to_passive     true
% 3.75/0.99  --inst_prop_sim_given                   true
% 3.75/0.99  --inst_prop_sim_new                     false
% 3.75/0.99  --inst_subs_new                         false
% 3.75/0.99  --inst_eq_res_simp                      false
% 3.75/0.99  --inst_subs_given                       false
% 3.75/0.99  --inst_orphan_elimination               true
% 3.75/0.99  --inst_learning_loop_flag               true
% 3.75/0.99  --inst_learning_start                   3000
% 3.75/0.99  --inst_learning_factor                  2
% 3.75/0.99  --inst_start_prop_sim_after_learn       3
% 3.75/0.99  --inst_sel_renew                        solver
% 3.75/0.99  --inst_lit_activity_flag                true
% 3.75/0.99  --inst_restr_to_given                   false
% 3.75/0.99  --inst_activity_threshold               500
% 3.75/0.99  --inst_out_proof                        true
% 3.75/0.99  
% 3.75/0.99  ------ Resolution Options
% 3.75/0.99  
% 3.75/0.99  --resolution_flag                       false
% 3.75/0.99  --res_lit_sel                           adaptive
% 3.75/0.99  --res_lit_sel_side                      none
% 3.75/0.99  --res_ordering                          kbo
% 3.75/0.99  --res_to_prop_solver                    active
% 3.75/0.99  --res_prop_simpl_new                    false
% 3.75/0.99  --res_prop_simpl_given                  true
% 3.75/0.99  --res_passive_queue_type                priority_queues
% 3.75/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.75/0.99  --res_passive_queues_freq               [15;5]
% 3.75/0.99  --res_forward_subs                      full
% 3.75/0.99  --res_backward_subs                     full
% 3.75/0.99  --res_forward_subs_resolution           true
% 3.75/0.99  --res_backward_subs_resolution          true
% 3.75/0.99  --res_orphan_elimination                true
% 3.75/0.99  --res_time_limit                        2.
% 3.75/0.99  --res_out_proof                         true
% 3.75/0.99  
% 3.75/0.99  ------ Superposition Options
% 3.75/0.99  
% 3.75/0.99  --superposition_flag                    true
% 3.75/0.99  --sup_passive_queue_type                priority_queues
% 3.75/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.75/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.75/0.99  --demod_completeness_check              fast
% 3.75/0.99  --demod_use_ground                      true
% 3.75/0.99  --sup_to_prop_solver                    passive
% 3.75/0.99  --sup_prop_simpl_new                    true
% 3.75/0.99  --sup_prop_simpl_given                  true
% 3.75/0.99  --sup_fun_splitting                     true
% 3.75/0.99  --sup_smt_interval                      50000
% 3.75/0.99  
% 3.75/0.99  ------ Superposition Simplification Setup
% 3.75/0.99  
% 3.75/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.75/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.75/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.75/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.75/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.75/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.75/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.75/0.99  --sup_immed_triv                        [TrivRules]
% 3.75/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.75/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.75/0.99  --sup_immed_bw_main                     []
% 3.75/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.75/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.75/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.75/0.99  --sup_input_bw                          []
% 3.75/0.99  
% 3.75/0.99  ------ Combination Options
% 3.75/0.99  
% 3.75/0.99  --comb_res_mult                         3
% 3.75/0.99  --comb_sup_mult                         2
% 3.75/0.99  --comb_inst_mult                        10
% 3.75/0.99  
% 3.75/0.99  ------ Debug Options
% 3.75/0.99  
% 3.75/0.99  --dbg_backtrace                         false
% 3.75/0.99  --dbg_dump_prop_clauses                 false
% 3.75/0.99  --dbg_dump_prop_clauses_file            -
% 3.75/0.99  --dbg_out_stat                          false
% 3.75/0.99  
% 3.75/0.99  
% 3.75/0.99  
% 3.75/0.99  
% 3.75/0.99  ------ Proving...
% 3.75/0.99  
% 3.75/0.99  
% 3.75/0.99  % SZS status Theorem for theBenchmark.p
% 3.75/0.99  
% 3.75/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.75/0.99  
% 3.75/0.99  fof(f12,axiom,(
% 3.75/0.99    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 3.75/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.75/0.99  
% 3.75/0.99  fof(f51,plain,(
% 3.75/0.99    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 3.75/0.99    inference(cnf_transformation,[],[f12])).
% 3.75/0.99  
% 3.75/0.99  fof(f25,conjecture,(
% 3.75/0.99    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 3.75/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.75/0.99  
% 3.75/0.99  fof(f26,negated_conjecture,(
% 3.75/0.99    ~! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 3.75/0.99    inference(negated_conjecture,[],[f25])).
% 3.75/0.99  
% 3.75/0.99  fof(f29,plain,(
% 3.75/0.99    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1)),
% 3.75/0.99    inference(ennf_transformation,[],[f26])).
% 3.75/0.99  
% 3.75/0.99  fof(f36,plain,(
% 3.75/0.99    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1) => k1_xboole_0 = k2_xboole_0(k1_tarski(sK1),sK2)),
% 3.75/0.99    introduced(choice_axiom,[])).
% 3.75/0.99  
% 3.75/0.99  fof(f37,plain,(
% 3.75/0.99    k1_xboole_0 = k2_xboole_0(k1_tarski(sK1),sK2)),
% 3.75/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f29,f36])).
% 3.75/0.99  
% 3.75/0.99  fof(f67,plain,(
% 3.75/0.99    k1_xboole_0 = k2_xboole_0(k1_tarski(sK1),sK2)),
% 3.75/0.99    inference(cnf_transformation,[],[f37])).
% 3.75/0.99  
% 3.75/0.99  fof(f13,axiom,(
% 3.75/0.99    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)),
% 3.75/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.75/0.99  
% 3.75/0.99  fof(f52,plain,(
% 3.75/0.99    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 3.75/0.99    inference(cnf_transformation,[],[f13])).
% 3.75/0.99  
% 3.75/0.99  fof(f9,axiom,(
% 3.75/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.75/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.75/0.99  
% 3.75/0.99  fof(f48,plain,(
% 3.75/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.75/0.99    inference(cnf_transformation,[],[f9])).
% 3.75/0.99  
% 3.75/0.99  fof(f68,plain,(
% 3.75/0.99    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(X0,X1)) )),
% 3.75/0.99    inference(definition_unfolding,[],[f52,f48])).
% 3.75/0.99  
% 3.75/0.99  fof(f14,axiom,(
% 3.75/0.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.75/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.75/0.99  
% 3.75/0.99  fof(f53,plain,(
% 3.75/0.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.75/0.99    inference(cnf_transformation,[],[f14])).
% 3.75/0.99  
% 3.75/0.99  fof(f15,axiom,(
% 3.75/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.75/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.75/0.99  
% 3.75/0.99  fof(f54,plain,(
% 3.75/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.75/0.99    inference(cnf_transformation,[],[f15])).
% 3.75/0.99  
% 3.75/0.99  fof(f16,axiom,(
% 3.75/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.75/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.75/0.99  
% 3.75/0.99  fof(f55,plain,(
% 3.75/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.75/0.99    inference(cnf_transformation,[],[f16])).
% 3.75/0.99  
% 3.75/0.99  fof(f17,axiom,(
% 3.75/0.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.75/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.75/0.99  
% 3.75/0.99  fof(f56,plain,(
% 3.75/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.75/0.99    inference(cnf_transformation,[],[f17])).
% 3.75/0.99  
% 3.75/0.99  fof(f18,axiom,(
% 3.75/0.99    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.75/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.75/0.99  
% 3.75/0.99  fof(f57,plain,(
% 3.75/0.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.75/0.99    inference(cnf_transformation,[],[f18])).
% 3.75/0.99  
% 3.75/0.99  fof(f19,axiom,(
% 3.75/0.99    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.75/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.75/0.99  
% 3.75/0.99  fof(f58,plain,(
% 3.75/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.75/0.99    inference(cnf_transformation,[],[f19])).
% 3.75/0.99  
% 3.75/0.99  fof(f20,axiom,(
% 3.75/0.99    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.75/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.75/0.99  
% 3.75/0.99  fof(f59,plain,(
% 3.75/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.75/0.99    inference(cnf_transformation,[],[f20])).
% 3.75/0.99  
% 3.75/0.99  fof(f69,plain,(
% 3.75/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.75/0.99    inference(definition_unfolding,[],[f58,f59])).
% 3.75/0.99  
% 3.75/0.99  fof(f70,plain,(
% 3.75/0.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.75/0.99    inference(definition_unfolding,[],[f57,f69])).
% 3.75/0.99  
% 3.75/0.99  fof(f71,plain,(
% 3.75/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.75/0.99    inference(definition_unfolding,[],[f56,f70])).
% 3.75/0.99  
% 3.75/0.99  fof(f72,plain,(
% 3.75/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.75/0.99    inference(definition_unfolding,[],[f55,f71])).
% 3.75/0.99  
% 3.75/0.99  fof(f73,plain,(
% 3.75/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.75/0.99    inference(definition_unfolding,[],[f54,f72])).
% 3.75/0.99  
% 3.75/0.99  fof(f74,plain,(
% 3.75/0.99    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.75/0.99    inference(definition_unfolding,[],[f53,f73])).
% 3.75/0.99  
% 3.75/0.99  fof(f80,plain,(
% 3.75/0.99    k5_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2))) = k1_xboole_0),
% 3.75/0.99    inference(definition_unfolding,[],[f67,f68,f74])).
% 3.75/0.99  
% 3.75/0.99  fof(f11,axiom,(
% 3.75/0.99    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 3.75/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.75/0.99  
% 3.75/0.99  fof(f50,plain,(
% 3.75/0.99    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 3.75/0.99    inference(cnf_transformation,[],[f11])).
% 3.75/0.99  
% 3.75/0.99  fof(f3,axiom,(
% 3.75/0.99    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 3.75/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.75/0.99  
% 3.75/0.99  fof(f40,plain,(
% 3.75/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 3.75/0.99    inference(cnf_transformation,[],[f3])).
% 3.75/0.99  
% 3.75/0.99  fof(f5,axiom,(
% 3.75/0.99    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 3.75/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.75/0.99  
% 3.75/0.99  fof(f44,plain,(
% 3.75/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 3.75/0.99    inference(cnf_transformation,[],[f5])).
% 3.75/0.99  
% 3.75/0.99  fof(f75,plain,(
% 3.75/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1)) )),
% 3.75/0.99    inference(definition_unfolding,[],[f44,f48])).
% 3.75/0.99  
% 3.75/0.99  fof(f10,axiom,(
% 3.75/0.99    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 3.75/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.75/0.99  
% 3.75/0.99  fof(f49,plain,(
% 3.75/0.99    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.75/0.99    inference(cnf_transformation,[],[f10])).
% 3.75/0.99  
% 3.75/0.99  fof(f2,axiom,(
% 3.75/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.75/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.75/0.99  
% 3.75/0.99  fof(f39,plain,(
% 3.75/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.75/0.99    inference(cnf_transformation,[],[f2])).
% 3.75/0.99  
% 3.75/0.99  fof(f76,plain,(
% 3.75/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 3.75/0.99    inference(definition_unfolding,[],[f39,f48,f48])).
% 3.75/0.99  
% 3.75/0.99  fof(f22,axiom,(
% 3.75/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.75/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.75/0.99  
% 3.75/0.99  fof(f64,plain,(
% 3.75/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.75/0.99    inference(cnf_transformation,[],[f22])).
% 3.75/0.99  
% 3.75/0.99  fof(f78,plain,(
% 3.75/0.99    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 3.75/0.99    inference(definition_unfolding,[],[f64,f68,f73])).
% 3.75/0.99  
% 3.75/0.99  fof(f24,axiom,(
% 3.75/0.99    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 3.75/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.75/0.99  
% 3.75/0.99  fof(f66,plain,(
% 3.75/0.99    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 3.75/0.99    inference(cnf_transformation,[],[f24])).
% 3.75/0.99  
% 3.75/0.99  fof(f6,axiom,(
% 3.75/0.99    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 3.75/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.75/0.99  
% 3.75/0.99  fof(f45,plain,(
% 3.75/0.99    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 3.75/0.99    inference(cnf_transformation,[],[f6])).
% 3.75/0.99  
% 3.75/0.99  fof(f77,plain,(
% 3.75/0.99    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) )),
% 3.75/0.99    inference(definition_unfolding,[],[f45,f48])).
% 3.75/0.99  
% 3.75/0.99  fof(f8,axiom,(
% 3.75/0.99    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 3.75/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.75/0.99  
% 3.75/0.99  fof(f28,plain,(
% 3.75/0.99    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 3.75/0.99    inference(ennf_transformation,[],[f8])).
% 3.75/0.99  
% 3.75/0.99  fof(f47,plain,(
% 3.75/0.99    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 3.75/0.99    inference(cnf_transformation,[],[f28])).
% 3.75/0.99  
% 3.75/0.99  fof(f1,axiom,(
% 3.75/0.99    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 3.75/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.75/0.99  
% 3.75/0.99  fof(f27,plain,(
% 3.75/0.99    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 3.75/0.99    inference(ennf_transformation,[],[f1])).
% 3.75/0.99  
% 3.75/0.99  fof(f38,plain,(
% 3.75/0.99    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.75/0.99    inference(cnf_transformation,[],[f27])).
% 3.75/0.99  
% 3.75/0.99  fof(f4,axiom,(
% 3.75/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.75/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.75/0.99  
% 3.75/0.99  fof(f30,plain,(
% 3.75/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.75/0.99    inference(nnf_transformation,[],[f4])).
% 3.75/0.99  
% 3.75/0.99  fof(f31,plain,(
% 3.75/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.75/0.99    inference(flattening,[],[f30])).
% 3.75/0.99  
% 3.75/0.99  fof(f41,plain,(
% 3.75/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.75/0.99    inference(cnf_transformation,[],[f31])).
% 3.75/0.99  
% 3.75/0.99  fof(f82,plain,(
% 3.75/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.75/0.99    inference(equality_resolution,[],[f41])).
% 3.75/0.99  
% 3.75/0.99  fof(f21,axiom,(
% 3.75/0.99    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 3.75/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.75/0.99  
% 3.75/0.99  fof(f32,plain,(
% 3.75/0.99    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.75/0.99    inference(nnf_transformation,[],[f21])).
% 3.75/0.99  
% 3.75/0.99  fof(f33,plain,(
% 3.75/0.99    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.75/0.99    inference(rectify,[],[f32])).
% 3.75/0.99  
% 3.75/0.99  fof(f34,plain,(
% 3.75/0.99    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 3.75/0.99    introduced(choice_axiom,[])).
% 3.75/0.99  
% 3.75/0.99  fof(f35,plain,(
% 3.75/0.99    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.75/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).
% 3.75/0.99  
% 3.75/0.99  fof(f61,plain,(
% 3.75/0.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 3.75/0.99    inference(cnf_transformation,[],[f35])).
% 3.75/0.99  
% 3.75/0.99  fof(f83,plain,(
% 3.75/0.99    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 3.75/0.99    inference(equality_resolution,[],[f61])).
% 3.75/0.99  
% 3.75/0.99  fof(f23,axiom,(
% 3.75/0.99    k1_tarski(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0)),
% 3.75/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.75/0.99  
% 3.75/0.99  fof(f65,plain,(
% 3.75/0.99    k1_tarski(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0)),
% 3.75/0.99    inference(cnf_transformation,[],[f23])).
% 3.75/0.99  
% 3.75/0.99  fof(f79,plain,(
% 3.75/0.99    k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_zfmisc_1(k1_xboole_0)),
% 3.75/0.99    inference(definition_unfolding,[],[f65,f74])).
% 3.75/0.99  
% 3.75/0.99  cnf(c_12,plain,
% 3.75/0.99      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.75/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_20,negated_conjecture,
% 3.75/0.99      ( k5_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2))) = k1_xboole_0 ),
% 3.75/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_11,plain,
% 3.75/0.99      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 3.75/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_3,plain,
% 3.75/0.99      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 3.75/0.99      inference(cnf_transformation,[],[f40]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_288,negated_conjecture,
% 3.75/0.99      ( k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)))) = k1_xboole_0 ),
% 3.75/0.99      inference(theory_normalisation,[status(thm)],[c_20,c_11,c_3]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_0,plain,
% 3.75/0.99      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 3.75/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_590,plain,
% 3.75/0.99      ( k5_xboole_0(sK2,k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)) = k1_xboole_0 ),
% 3.75/0.99      inference(demodulation,[status(thm)],[c_288,c_0]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_1210,plain,
% 3.75/0.99      ( k5_xboole_0(sK2,k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2),X0)) = k5_xboole_0(k1_xboole_0,X0) ),
% 3.75/0.99      inference(superposition,[status(thm)],[c_590,c_11]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_10,plain,
% 3.75/0.99      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.75/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_1013,plain,
% 3.75/0.99      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 3.75/0.99      inference(superposition,[status(thm)],[c_10,c_3]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_1220,plain,
% 3.75/0.99      ( k5_xboole_0(sK2,k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2),X0)) = X0 ),
% 3.75/0.99      inference(light_normalisation,[status(thm)],[c_1210,c_1013]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_1417,plain,
% 3.75/0.99      ( k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2) = k5_xboole_0(sK2,k1_xboole_0) ),
% 3.75/0.99      inference(superposition,[status(thm)],[c_12,c_1220]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_1422,plain,
% 3.75/0.99      ( k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2) = sK2 ),
% 3.75/0.99      inference(demodulation,[status(thm)],[c_1417,c_10]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_1870,plain,
% 3.75/0.99      ( k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)) = k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2) ),
% 3.75/0.99      inference(superposition,[status(thm)],[c_1422,c_0]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_1873,plain,
% 3.75/0.99      ( k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2) = sK2 ),
% 3.75/0.99      inference(demodulation,[status(thm)],[c_1870,c_1422]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_601,plain,
% 3.75/0.99      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
% 3.75/0.99      inference(superposition,[status(thm)],[c_11,c_3]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_3745,plain,
% 3.75/0.99      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
% 3.75/0.99      inference(superposition,[status(thm)],[c_12,c_601]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_3920,plain,
% 3.75/0.99      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
% 3.75/0.99      inference(demodulation,[status(thm)],[c_3745,c_10]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_8012,plain,
% 3.75/0.99      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k5_xboole_0(sK2,sK2) ),
% 3.75/0.99      inference(superposition,[status(thm)],[c_1873,c_3920]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_8207,plain,
% 3.75/0.99      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k1_xboole_0 ),
% 3.75/0.99      inference(demodulation,[status(thm)],[c_8012,c_12]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_2,plain,
% 3.75/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 3.75/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_17,plain,
% 3.75/0.99      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 3.75/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_289,plain,
% 3.75/0.99      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
% 3.75/0.99      inference(theory_normalisation,[status(thm)],[c_17,c_11,c_3]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_1196,plain,
% 3.75/0.99      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
% 3.75/0.99      inference(superposition,[status(thm)],[c_2,c_289]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_1197,plain,
% 3.75/0.99      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 3.75/0.99      inference(demodulation,[status(thm)],[c_1196,c_0]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_11194,plain,
% 3.75/0.99      ( k5_xboole_0(sK1,k4_xboole_0(sK1,sK1)) = k3_tarski(k1_xboole_0) ),
% 3.75/0.99      inference(superposition,[status(thm)],[c_8207,c_1197]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_19,plain,
% 3.75/0.99      ( k3_tarski(k1_xboole_0) = k1_xboole_0 ),
% 3.75/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_11195,plain,
% 3.75/0.99      ( k5_xboole_0(sK1,k4_xboole_0(sK1,sK1)) = k1_xboole_0 ),
% 3.75/0.99      inference(light_normalisation,[status(thm)],[c_11194,c_19]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_1105,plain,
% 3.75/0.99      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
% 3.75/0.99      inference(superposition,[status(thm)],[c_1013,c_0]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_7,plain,
% 3.75/0.99      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
% 3.75/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_586,plain,
% 3.75/0.99      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = iProver_top ),
% 3.75/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_9,plain,
% 3.75/0.99      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 3.75/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_584,plain,
% 3.75/0.99      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.75/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_2450,plain,
% 3.75/0.99      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
% 3.75/0.99      inference(superposition,[status(thm)],[c_586,c_584]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_4083,plain,
% 3.75/0.99      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.75/0.99      inference(light_normalisation,[status(thm)],[c_1105,c_2450]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_4096,plain,
% 3.75/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 3.75/0.99      inference(superposition,[status(thm)],[c_4083,c_2]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_4114,plain,
% 3.75/0.99      ( k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
% 3.75/0.99      inference(superposition,[status(thm)],[c_4096,c_0]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_4124,plain,
% 3.75/0.99      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.75/0.99      inference(light_normalisation,[status(thm)],[c_4114,c_10]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_4125,plain,
% 3.75/0.99      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.75/0.99      inference(demodulation,[status(thm)],[c_4124,c_4096]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_11196,plain,
% 3.75/0.99      ( sK1 = k1_xboole_0 ),
% 3.75/0.99      inference(demodulation,[status(thm)],[c_11195,c_10,c_4125]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_11197,plain,
% 3.75/0.99      ( k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.75/0.99      inference(demodulation,[status(thm)],[c_11196,c_8207]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_295,plain,
% 3.75/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.75/0.99      theory(equality) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_615,plain,
% 3.75/0.99      ( r2_hidden(X0,X1)
% 3.75/0.99      | ~ r2_hidden(X2,k1_zfmisc_1(X3))
% 3.75/0.99      | X0 != X2
% 3.75/0.99      | X1 != k1_zfmisc_1(X3) ),
% 3.75/0.99      inference(instantiation,[status(thm)],[c_295]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_645,plain,
% 3.75/0.99      ( r2_hidden(X0,k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
% 3.75/0.99      | ~ r2_hidden(X1,k1_zfmisc_1(k1_xboole_0))
% 3.75/0.99      | X0 != X1
% 3.75/0.99      | k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_zfmisc_1(k1_xboole_0) ),
% 3.75/0.99      inference(instantiation,[status(thm)],[c_615]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_1906,plain,
% 3.75/0.99      ( ~ r2_hidden(X0,k1_zfmisc_1(k1_xboole_0))
% 3.75/0.99      | r2_hidden(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
% 3.75/0.99      | k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != X0
% 3.75/0.99      | k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_zfmisc_1(k1_xboole_0) ),
% 3.75/0.99      inference(instantiation,[status(thm)],[c_645]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_4026,plain,
% 3.75/0.99      ( r2_hidden(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
% 3.75/0.99      | ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
% 3.75/0.99      | k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_zfmisc_1(k1_xboole_0)
% 3.75/0.99      | k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
% 3.75/0.99      inference(instantiation,[status(thm)],[c_1906]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_1,plain,
% 3.75/0.99      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X1,X0) ),
% 3.75/0.99      inference(cnf_transformation,[],[f38]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_660,plain,
% 3.75/0.99      ( ~ r2_hidden(X0,k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
% 3.75/0.99      | ~ r2_hidden(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),X0) ),
% 3.75/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_1905,plain,
% 3.75/0.99      ( ~ r2_hidden(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
% 3.75/0.99      inference(instantiation,[status(thm)],[c_660]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_6,plain,
% 3.75/0.99      ( r1_tarski(X0,X0) ),
% 3.75/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_1003,plain,
% 3.75/0.99      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 3.75/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_15,plain,
% 3.75/0.99      ( ~ r1_tarski(X0,X1) | r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 3.75/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_688,plain,
% 3.75/0.99      ( ~ r1_tarski(X0,k1_xboole_0)
% 3.75/0.99      | r2_hidden(X0,k1_zfmisc_1(k1_xboole_0)) ),
% 3.75/0.99      inference(instantiation,[status(thm)],[c_15]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_810,plain,
% 3.75/0.99      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 3.75/0.99      | r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
% 3.75/0.99      inference(instantiation,[status(thm)],[c_688]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(c_18,plain,
% 3.75/0.99      ( k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_zfmisc_1(k1_xboole_0) ),
% 3.75/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.75/0.99  
% 3.75/0.99  cnf(contradiction,plain,
% 3.75/0.99      ( $false ),
% 3.75/0.99      inference(minisat,
% 3.75/0.99                [status(thm)],
% 3.75/0.99                [c_11197,c_4026,c_1905,c_1003,c_810,c_18]) ).
% 3.75/0.99  
% 3.75/0.99  
% 3.75/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.75/0.99  
% 3.75/0.99  ------                               Statistics
% 3.75/0.99  
% 3.75/0.99  ------ General
% 3.75/0.99  
% 3.75/0.99  abstr_ref_over_cycles:                  0
% 3.75/0.99  abstr_ref_under_cycles:                 0
% 3.75/0.99  gc_basic_clause_elim:                   0
% 3.75/0.99  forced_gc_time:                         0
% 3.75/0.99  parsing_time:                           0.008
% 3.75/0.99  unif_index_cands_time:                  0.
% 3.75/0.99  unif_index_add_time:                    0.
% 3.75/0.99  orderings_time:                         0.
% 3.75/0.99  out_proof_time:                         0.009
% 3.75/0.99  total_time:                             0.314
% 3.75/0.99  num_of_symbols:                         42
% 3.75/0.99  num_of_terms:                           12568
% 3.75/0.99  
% 3.75/0.99  ------ Preprocessing
% 3.75/0.99  
% 3.75/0.99  num_of_splits:                          0
% 3.75/0.99  num_of_split_atoms:                     0
% 3.75/0.99  num_of_reused_defs:                     0
% 3.75/0.99  num_eq_ax_congr_red:                    6
% 3.75/0.99  num_of_sem_filtered_clauses:            1
% 3.75/0.99  num_of_subtypes:                        0
% 3.75/0.99  monotx_restored_types:                  0
% 3.75/0.99  sat_num_of_epr_types:                   0
% 3.75/0.99  sat_num_of_non_cyclic_types:            0
% 3.75/0.99  sat_guarded_non_collapsed_types:        0
% 3.75/0.99  num_pure_diseq_elim:                    0
% 3.75/0.99  simp_replaced_by:                       0
% 3.75/0.99  res_preprocessed:                       99
% 3.75/0.99  prep_upred:                             0
% 3.75/0.99  prep_unflattend:                        0
% 3.75/0.99  smt_new_axioms:                         0
% 3.75/0.99  pred_elim_cands:                        2
% 3.75/0.99  pred_elim:                              0
% 3.75/0.99  pred_elim_cl:                           0
% 3.75/0.99  pred_elim_cycles:                       2
% 3.75/0.99  merged_defs:                            8
% 3.75/0.99  merged_defs_ncl:                        0
% 3.75/0.99  bin_hyper_res:                          8
% 3.75/0.99  prep_cycles:                            4
% 3.75/0.99  pred_elim_time:                         0.
% 3.75/0.99  splitting_time:                         0.
% 3.75/0.99  sem_filter_time:                        0.
% 3.75/0.99  monotx_time:                            0.
% 3.75/0.99  subtype_inf_time:                       0.
% 3.75/0.99  
% 3.75/0.99  ------ Problem properties
% 3.75/0.99  
% 3.75/0.99  clauses:                                20
% 3.75/0.99  conjectures:                            1
% 3.75/0.99  epr:                                    5
% 3.75/0.99  horn:                                   19
% 3.75/0.99  ground:                                 3
% 3.75/0.99  unary:                                  13
% 3.75/0.99  binary:                                 4
% 3.75/0.99  lits:                                   30
% 3.75/0.99  lits_eq:                                14
% 3.75/0.99  fd_pure:                                0
% 3.75/0.99  fd_pseudo:                              0
% 3.75/0.99  fd_cond:                                1
% 3.75/0.99  fd_pseudo_cond:                         3
% 3.75/0.99  ac_symbols:                             1
% 3.75/0.99  
% 3.75/0.99  ------ Propositional Solver
% 3.75/0.99  
% 3.75/0.99  prop_solver_calls:                      30
% 3.75/0.99  prop_fast_solver_calls:                 537
% 3.75/0.99  smt_solver_calls:                       0
% 3.75/0.99  smt_fast_solver_calls:                  0
% 3.75/0.99  prop_num_of_clauses:                    3030
% 3.75/0.99  prop_preprocess_simplified:             6917
% 3.75/0.99  prop_fo_subsumed:                       0
% 3.75/0.99  prop_solver_time:                       0.
% 3.75/0.99  smt_solver_time:                        0.
% 3.75/0.99  smt_fast_solver_time:                   0.
% 3.75/0.99  prop_fast_solver_time:                  0.
% 3.75/0.99  prop_unsat_core_time:                   0.
% 3.75/0.99  
% 3.75/0.99  ------ QBF
% 3.75/0.99  
% 3.75/0.99  qbf_q_res:                              0
% 3.75/0.99  qbf_num_tautologies:                    0
% 3.75/0.99  qbf_prep_cycles:                        0
% 3.75/0.99  
% 3.75/0.99  ------ BMC1
% 3.75/0.99  
% 3.75/0.99  bmc1_current_bound:                     -1
% 3.75/0.99  bmc1_last_solved_bound:                 -1
% 3.75/0.99  bmc1_unsat_core_size:                   -1
% 3.75/0.99  bmc1_unsat_core_parents_size:           -1
% 3.75/0.99  bmc1_merge_next_fun:                    0
% 3.75/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.75/0.99  
% 3.75/0.99  ------ Instantiation
% 3.75/0.99  
% 3.75/0.99  inst_num_of_clauses:                    748
% 3.75/0.99  inst_num_in_passive:                    311
% 3.75/0.99  inst_num_in_active:                     326
% 3.75/0.99  inst_num_in_unprocessed:                113
% 3.75/0.99  inst_num_of_loops:                      400
% 3.75/0.99  inst_num_of_learning_restarts:          0
% 3.75/0.99  inst_num_moves_active_passive:          70
% 3.75/0.99  inst_lit_activity:                      0
% 3.75/0.99  inst_lit_activity_moves:                0
% 3.75/0.99  inst_num_tautologies:                   0
% 3.75/0.99  inst_num_prop_implied:                  0
% 3.75/0.99  inst_num_existing_simplified:           0
% 3.75/0.99  inst_num_eq_res_simplified:             0
% 3.75/0.99  inst_num_child_elim:                    0
% 3.75/0.99  inst_num_of_dismatching_blockings:      663
% 3.75/0.99  inst_num_of_non_proper_insts:           1302
% 3.75/0.99  inst_num_of_duplicates:                 0
% 3.75/0.99  inst_inst_num_from_inst_to_res:         0
% 3.75/0.99  inst_dismatching_checking_time:         0.
% 3.75/0.99  
% 3.75/0.99  ------ Resolution
% 3.75/0.99  
% 3.75/0.99  res_num_of_clauses:                     0
% 3.75/0.99  res_num_in_passive:                     0
% 3.75/0.99  res_num_in_active:                      0
% 3.75/0.99  res_num_of_loops:                       103
% 3.75/0.99  res_forward_subset_subsumed:            114
% 3.75/0.99  res_backward_subset_subsumed:           6
% 3.75/0.99  res_forward_subsumed:                   0
% 3.75/0.99  res_backward_subsumed:                  0
% 3.75/0.99  res_forward_subsumption_resolution:     0
% 3.75/0.99  res_backward_subsumption_resolution:    0
% 3.75/0.99  res_clause_to_clause_subsumption:       4378
% 3.75/0.99  res_orphan_elimination:                 0
% 3.75/0.99  res_tautology_del:                      79
% 3.75/0.99  res_num_eq_res_simplified:              0
% 3.75/0.99  res_num_sel_changes:                    0
% 3.75/0.99  res_moves_from_active_to_pass:          0
% 3.75/0.99  
% 3.75/0.99  ------ Superposition
% 3.75/0.99  
% 3.75/0.99  sup_time_total:                         0.
% 3.75/0.99  sup_time_generating:                    0.
% 3.75/0.99  sup_time_sim_full:                      0.
% 3.75/0.99  sup_time_sim_immed:                     0.
% 3.75/0.99  
% 3.75/0.99  sup_num_of_clauses:                     445
% 3.75/0.99  sup_num_in_active:                      32
% 3.75/0.99  sup_num_in_passive:                     413
% 3.75/0.99  sup_num_of_loops:                       79
% 3.75/0.99  sup_fw_superposition:                   1723
% 3.75/0.99  sup_bw_superposition:                   1234
% 3.75/0.99  sup_immediate_simplified:               1228
% 3.75/0.99  sup_given_eliminated:                   7
% 3.75/0.99  comparisons_done:                       0
% 3.75/0.99  comparisons_avoided:                    0
% 3.75/0.99  
% 3.75/0.99  ------ Simplifications
% 3.75/0.99  
% 3.75/0.99  
% 3.75/0.99  sim_fw_subset_subsumed:                 0
% 3.75/0.99  sim_bw_subset_subsumed:                 0
% 3.75/0.99  sim_fw_subsumed:                        138
% 3.75/0.99  sim_bw_subsumed:                        8
% 3.75/0.99  sim_fw_subsumption_res:                 0
% 3.75/0.99  sim_bw_subsumption_res:                 0
% 3.75/0.99  sim_tautology_del:                      0
% 3.75/0.99  sim_eq_tautology_del:                   406
% 3.75/0.99  sim_eq_res_simp:                        0
% 3.75/0.99  sim_fw_demodulated:                     940
% 3.75/0.99  sim_bw_demodulated:                     56
% 3.75/0.99  sim_light_normalised:                   533
% 3.75/0.99  sim_joinable_taut:                      116
% 3.75/0.99  sim_joinable_simp:                      0
% 3.75/0.99  sim_ac_normalised:                      0
% 3.75/0.99  sim_smt_subsumption:                    0
% 3.75/0.99  
%------------------------------------------------------------------------------
