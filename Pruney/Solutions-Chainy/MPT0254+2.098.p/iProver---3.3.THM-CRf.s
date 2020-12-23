%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:34:03 EST 2020

% Result     : Theorem 7.82s
% Output     : CNFRefutation 7.82s
% Verified   : 
% Statistics : Number of formulae       :  196 (33213 expanded)
%              Number of clauses        :  119 (8934 expanded)
%              Number of leaves         :   32 (9683 expanded)
%              Depth                    :   46
%              Number of atoms          :  301 (33858 expanded)
%              Number of equality atoms :  204 (33740 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :   10 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f13])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f26,conjecture,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f18])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f19])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f20])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f12,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f11,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f23,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f78,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f67,f55,f75])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f77,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f50,f46])).

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

fof(f48,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f8,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f8])).

fof(f25,axiom,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f4,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f10,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f51,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    k1_tarski(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f24])).

fof(f79,plain,(
    k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_zfmisc_1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f68,f76])).

cnf(c_12,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_20,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_11,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_665,negated_conjecture,
    ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))) = k1_xboole_0 ),
    inference(theory_normalisation,[status(thm)],[c_20,c_11,c_1])).

cnf(c_1175,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_0,c_665])).

cnf(c_1384,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),X0)) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_1175,c_11])).

cnf(c_10,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1268,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_10,c_1])).

cnf(c_1390,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1384,c_1268])).

cnf(c_1558,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = k5_xboole_0(sK3,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_12,c_1390])).

cnf(c_1562,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = sK3 ),
    inference(demodulation,[status(thm)],[c_1558,c_10])).

cnf(c_17,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_666,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) ),
    inference(theory_normalisation,[status(thm)],[c_17,c_11,c_1])).

cnf(c_1383,plain,
    ( k5_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X2) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X0,X1)),X2)) ),
    inference(superposition,[status(thm)],[c_666,c_11])).

cnf(c_979,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_11,c_1])).

cnf(c_1566,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(sK3,X0)) = X0 ),
    inference(demodulation,[status(thm)],[c_1562,c_1390])).

cnf(c_1574,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(sK3,X0),X1)) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1566,c_11])).

cnf(c_6566,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,sK3)),X2)) = k5_xboole_0(k5_xboole_0(X1,X0),X2) ),
    inference(superposition,[status(thm)],[c_979,c_1574])).

cnf(c_1568,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(X0,sK3)) = X0 ),
    inference(superposition,[status(thm)],[c_1,c_1566])).

cnf(c_1615,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(X0,k5_xboole_0(X1,sK3))) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_11,c_1568])).

cnf(c_3368,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,sK3)),X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_1615,c_11])).

cnf(c_3379,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,sK3)),X2)) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_3368,c_11])).

cnf(c_6605,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
    inference(light_normalisation,[status(thm)],[c_6566,c_3379])).

cnf(c_13460,plain,
    ( k5_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X2) = k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X1,X2))) ),
    inference(demodulation,[status(thm)],[c_1383,c_6605])).

cnf(c_13703,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,X0)),X1)) = k5_xboole_0(k3_xboole_0(sK3,X0),k5_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_13460,c_1566])).

cnf(c_14681,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) = k5_xboole_0(k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),sK3) ),
    inference(superposition,[status(thm)],[c_1562,c_13703])).

cnf(c_1668,plain,
    ( k5_xboole_0(X0,k5_xboole_0(sK3,X0)) = k5_xboole_0(sK3,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_12,c_1574])).

cnf(c_1688,plain,
    ( k5_xboole_0(X0,k5_xboole_0(sK3,X0)) = sK3 ),
    inference(demodulation,[status(thm)],[c_1668,c_10])).

cnf(c_2016,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,sK3)) = sK3 ),
    inference(superposition,[status(thm)],[c_1,c_1688])).

cnf(c_14688,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,X0)),k5_xboole_0(X0,sK3))) = k5_xboole_0(k3_xboole_0(sK3,X0),sK3) ),
    inference(superposition,[status(thm)],[c_2016,c_13703])).

cnf(c_1262,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_0,c_666])).

cnf(c_980,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_11,c_1])).

cnf(c_6949,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,X0),k5_xboole_0(X1,sK3)) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1566,c_980])).

cnf(c_2023,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,X0),X0) = sK3 ),
    inference(superposition,[status(thm)],[c_1566,c_1688])).

cnf(c_2150,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,X0),k5_xboole_0(X0,X1)) = k5_xboole_0(sK3,X1) ),
    inference(superposition,[status(thm)],[c_2023,c_11])).

cnf(c_1664,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(X0,k5_xboole_0(sK3,X1))) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1,c_1574])).

cnf(c_3642,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,k5_xboole_0(sK3,X0))) = sK3 ),
    inference(superposition,[status(thm)],[c_1664,c_2023])).

cnf(c_4726,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,X0),k5_xboole_0(k5_xboole_0(X1,X0),k5_xboole_0(sK3,k5_xboole_0(sK3,X1)))) = sK3 ),
    inference(superposition,[status(thm)],[c_2150,c_3642])).

cnf(c_4805,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,X0),k5_xboole_0(k5_xboole_0(X1,X0),X1)) = sK3 ),
    inference(demodulation,[status(thm)],[c_4726,c_1566])).

cnf(c_4977,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,X1),X0)) = k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(sK3,X1)),sK3) ),
    inference(superposition,[status(thm)],[c_4805,c_2150])).

cnf(c_5002,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,X1),X0)) = k5_xboole_0(X1,sK3) ),
    inference(demodulation,[status(thm)],[c_4977,c_1566])).

cnf(c_5342,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X0) = k5_xboole_0(sK3,k5_xboole_0(X1,sK3)) ),
    inference(superposition,[status(thm)],[c_5002,c_1566])).

cnf(c_5353,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X0) = X1 ),
    inference(demodulation,[status(thm)],[c_5342,c_1568])).

cnf(c_7284,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(sK3,X1)) = k5_xboole_0(X0,sK3) ),
    inference(superposition,[status(thm)],[c_6949,c_5353])).

cnf(c_7805,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(X0,X1)),k5_xboole_0(X0,sK3)) = k5_xboole_0(sK3,k5_xboole_0(sK3,X1)) ),
    inference(superposition,[status(thm)],[c_7284,c_2150])).

cnf(c_7864,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(X0,X1)),k5_xboole_0(X0,sK3)) = X1 ),
    inference(demodulation,[status(thm)],[c_7805,c_1566,c_6949])).

cnf(c_8748,plain,
    ( k5_xboole_0(k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,X0)),k5_xboole_0(X0,sK3)) = k3_xboole_0(X0,sK3) ),
    inference(superposition,[status(thm)],[c_1262,c_7864])).

cnf(c_14917,plain,
    ( k5_xboole_0(k3_xboole_0(sK3,X0),sK3) = k5_xboole_0(sK3,k3_xboole_0(X0,sK3)) ),
    inference(light_normalisation,[status(thm)],[c_14688,c_8748])).

cnf(c_14926,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) = k5_xboole_0(sK3,k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) ),
    inference(demodulation,[status(thm)],[c_14681,c_14917])).

cnf(c_1265,plain,
    ( k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_666,c_1175])).

cnf(c_14927,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k1_xboole_0,k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) = k5_xboole_0(sK3,k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) ),
    inference(light_normalisation,[status(thm)],[c_14926,c_1265])).

cnf(c_5434,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X1) = X0 ),
    inference(superposition,[status(thm)],[c_1,c_5353])).

cnf(c_1557,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X0))) = X0 ),
    inference(superposition,[status(thm)],[c_11,c_1390])).

cnf(c_1604,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(X0,k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))) = X0 ),
    inference(superposition,[status(thm)],[c_1,c_1557])).

cnf(c_2340,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(X0,k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) = k5_xboole_0(sK3,X0) ),
    inference(superposition,[status(thm)],[c_1604,c_1566])).

cnf(c_5633,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(X0,k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),X0) ),
    inference(superposition,[status(thm)],[c_5434,c_2340])).

cnf(c_14928,plain,
    ( k5_xboole_0(sK3,k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(demodulation,[status(thm)],[c_14927,c_10,c_5633])).

cnf(c_5478,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(superposition,[status(thm)],[c_5353,c_11])).

cnf(c_15063,plain,
    ( k5_xboole_0(k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = sK3 ),
    inference(superposition,[status(thm)],[c_14928,c_5478])).

cnf(c_8,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_965,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2956,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_965])).

cnf(c_15070,plain,
    ( r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_14928,c_2956])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_966,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_15306,plain,
    ( k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(superposition,[status(thm)],[c_15070,c_966])).

cnf(c_15307,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_15063,c_15063,c_15306])).

cnf(c_15308,plain,
    ( sK3 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_15307,c_12])).

cnf(c_15353,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_15308,c_1562])).

cnf(c_7,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1176,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7,c_0])).

cnf(c_15365,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_15353,c_10,c_1176])).

cnf(c_18328,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK2,k3_xboole_0(sK2,sK2))) = k3_tarski(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_15365,c_1262])).

cnf(c_19,plain,
    ( k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_18330,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK2,k3_xboole_0(sK2,sK2))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_18328,c_19])).

cnf(c_1382,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_12,c_11])).

cnf(c_1391,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_1382,c_1268])).

cnf(c_2958,plain,
    ( r1_tarski(k5_xboole_0(X0,k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_965])).

cnf(c_2961,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2958,c_10])).

cnf(c_5573,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_2961,c_966])).

cnf(c_18331,plain,
    ( sK2 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_18330,c_10,c_12,c_1391,c_5573])).

cnf(c_18332,plain,
    ( k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_18331,c_15365])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_4,plain,
    ( r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_199,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | k5_xboole_0(X3,X4) != X2
    | k3_xboole_0(X3,X4) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_4])).

cnf(c_200,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2))) ),
    inference(unflattening,[status(thm)],[c_199])).

cnf(c_958,plain,
    ( r2_hidden(X0,k3_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_200])).

cnf(c_1789,plain,
    ( r2_hidden(X0,k3_xboole_0(k3_xboole_0(k1_xboole_0,X1),X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1268,c_958])).

cnf(c_1795,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1789,c_1176])).

cnf(c_1823,plain,
    ( r2_hidden(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1795])).

cnf(c_669,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1373,plain,
    ( X0 != X1
    | X0 = k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != X1 ),
    inference(instantiation,[status(thm)],[c_669])).

cnf(c_1374,plain,
    ( k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1373])).

cnf(c_672,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1218,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | X0 != X2
    | X1 != k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_672])).

cnf(c_1224,plain,
    ( X0 != X1
    | X2 != k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X1,k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1218])).

cnf(c_1226,plain,
    ( k1_xboole_0 != k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0
    | r2_hidden(k1_xboole_0,k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) != iProver_top
    | r2_hidden(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1224])).

cnf(c_1012,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k1_zfmisc_1(X3))
    | X0 != X2
    | X1 != k1_zfmisc_1(X3) ),
    inference(instantiation,[status(thm)],[c_672])).

cnf(c_1134,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k3_xboole_0(X2,X3),k1_zfmisc_1(X2))
    | X0 != k3_xboole_0(X2,X3)
    | X1 != k1_zfmisc_1(X2) ),
    inference(instantiation,[status(thm)],[c_1012])).

cnf(c_1200,plain,
    ( r2_hidden(X0,k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | ~ r2_hidden(k3_xboole_0(k1_xboole_0,X1),k1_zfmisc_1(k1_xboole_0))
    | X0 != k3_xboole_0(k1_xboole_0,X1)
    | k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_zfmisc_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1134])).

cnf(c_1201,plain,
    ( X0 != k3_xboole_0(k1_xboole_0,X1)
    | k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_zfmisc_1(k1_xboole_0)
    | r2_hidden(X0,k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) = iProver_top
    | r2_hidden(k3_xboole_0(k1_xboole_0,X1),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1200])).

cnf(c_1203,plain,
    ( k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_zfmisc_1(k1_xboole_0)
    | k1_xboole_0 != k3_xboole_0(k1_xboole_0,k1_xboole_0)
    | r2_hidden(k3_xboole_0(k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r2_hidden(k1_xboole_0,k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1201])).

cnf(c_668,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_683,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_668])).

cnf(c_5,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_239,plain,
    ( k3_xboole_0(X0,X1) != X2
    | k1_xboole_0 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_9])).

cnf(c_240,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(unflattening,[status(thm)],[c_239])).

cnf(c_241,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_240])).

cnf(c_15,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_110,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_15])).

cnf(c_224,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1))
    | X1 != X2
    | k3_xboole_0(X2,X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_110])).

cnf(c_225,plain,
    ( r2_hidden(k3_xboole_0(X0,X1),k1_zfmisc_1(X0)) ),
    inference(unflattening,[status(thm)],[c_224])).

cnf(c_226,plain,
    ( r2_hidden(k3_xboole_0(X0,X1),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_225])).

cnf(c_228,plain,
    ( r2_hidden(k3_xboole_0(k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_226])).

cnf(c_18,plain,
    ( k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_zfmisc_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f79])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_18332,c_1823,c_1374,c_1226,c_1203,c_683,c_241,c_228,c_18])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:26:29 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 7.82/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.82/1.49  
% 7.82/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.82/1.49  
% 7.82/1.49  ------  iProver source info
% 7.82/1.49  
% 7.82/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.82/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.82/1.49  git: non_committed_changes: false
% 7.82/1.49  git: last_make_outside_of_git: false
% 7.82/1.49  
% 7.82/1.49  ------ 
% 7.82/1.49  
% 7.82/1.49  ------ Input Options
% 7.82/1.49  
% 7.82/1.49  --out_options                           all
% 7.82/1.49  --tptp_safe_out                         true
% 7.82/1.49  --problem_path                          ""
% 7.82/1.49  --include_path                          ""
% 7.82/1.49  --clausifier                            res/vclausify_rel
% 7.82/1.49  --clausifier_options                    ""
% 7.82/1.49  --stdin                                 false
% 7.82/1.49  --stats_out                             all
% 7.82/1.49  
% 7.82/1.49  ------ General Options
% 7.82/1.49  
% 7.82/1.49  --fof                                   false
% 7.82/1.49  --time_out_real                         305.
% 7.82/1.49  --time_out_virtual                      -1.
% 7.82/1.49  --symbol_type_check                     false
% 7.82/1.49  --clausify_out                          false
% 7.82/1.49  --sig_cnt_out                           false
% 7.82/1.49  --trig_cnt_out                          false
% 7.82/1.49  --trig_cnt_out_tolerance                1.
% 7.82/1.49  --trig_cnt_out_sk_spl                   false
% 7.82/1.49  --abstr_cl_out                          false
% 7.82/1.49  
% 7.82/1.49  ------ Global Options
% 7.82/1.49  
% 7.82/1.49  --schedule                              default
% 7.82/1.49  --add_important_lit                     false
% 7.82/1.49  --prop_solver_per_cl                    1000
% 7.82/1.49  --min_unsat_core                        false
% 7.82/1.49  --soft_assumptions                      false
% 7.82/1.49  --soft_lemma_size                       3
% 7.82/1.49  --prop_impl_unit_size                   0
% 7.82/1.49  --prop_impl_unit                        []
% 7.82/1.49  --share_sel_clauses                     true
% 7.82/1.49  --reset_solvers                         false
% 7.82/1.49  --bc_imp_inh                            [conj_cone]
% 7.82/1.49  --conj_cone_tolerance                   3.
% 7.82/1.49  --extra_neg_conj                        none
% 7.82/1.49  --large_theory_mode                     true
% 7.82/1.49  --prolific_symb_bound                   200
% 7.82/1.49  --lt_threshold                          2000
% 7.82/1.49  --clause_weak_htbl                      true
% 7.82/1.49  --gc_record_bc_elim                     false
% 7.82/1.49  
% 7.82/1.49  ------ Preprocessing Options
% 7.82/1.49  
% 7.82/1.49  --preprocessing_flag                    true
% 7.82/1.49  --time_out_prep_mult                    0.1
% 7.82/1.49  --splitting_mode                        input
% 7.82/1.49  --splitting_grd                         true
% 7.82/1.49  --splitting_cvd                         false
% 7.82/1.49  --splitting_cvd_svl                     false
% 7.82/1.49  --splitting_nvd                         32
% 7.82/1.49  --sub_typing                            true
% 7.82/1.49  --prep_gs_sim                           true
% 7.82/1.49  --prep_unflatten                        true
% 7.82/1.49  --prep_res_sim                          true
% 7.82/1.49  --prep_upred                            true
% 7.82/1.49  --prep_sem_filter                       exhaustive
% 7.82/1.49  --prep_sem_filter_out                   false
% 7.82/1.49  --pred_elim                             true
% 7.82/1.49  --res_sim_input                         true
% 7.82/1.49  --eq_ax_congr_red                       true
% 7.82/1.49  --pure_diseq_elim                       true
% 7.82/1.49  --brand_transform                       false
% 7.82/1.49  --non_eq_to_eq                          false
% 7.82/1.49  --prep_def_merge                        true
% 7.82/1.49  --prep_def_merge_prop_impl              false
% 7.82/1.49  --prep_def_merge_mbd                    true
% 7.82/1.49  --prep_def_merge_tr_red                 false
% 7.82/1.49  --prep_def_merge_tr_cl                  false
% 7.82/1.49  --smt_preprocessing                     true
% 7.82/1.49  --smt_ac_axioms                         fast
% 7.82/1.49  --preprocessed_out                      false
% 7.82/1.49  --preprocessed_stats                    false
% 7.82/1.49  
% 7.82/1.49  ------ Abstraction refinement Options
% 7.82/1.49  
% 7.82/1.49  --abstr_ref                             []
% 7.82/1.49  --abstr_ref_prep                        false
% 7.82/1.49  --abstr_ref_until_sat                   false
% 7.82/1.49  --abstr_ref_sig_restrict                funpre
% 7.82/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.82/1.49  --abstr_ref_under                       []
% 7.82/1.49  
% 7.82/1.49  ------ SAT Options
% 7.82/1.49  
% 7.82/1.49  --sat_mode                              false
% 7.82/1.49  --sat_fm_restart_options                ""
% 7.82/1.49  --sat_gr_def                            false
% 7.82/1.49  --sat_epr_types                         true
% 7.82/1.49  --sat_non_cyclic_types                  false
% 7.82/1.49  --sat_finite_models                     false
% 7.82/1.49  --sat_fm_lemmas                         false
% 7.82/1.49  --sat_fm_prep                           false
% 7.82/1.49  --sat_fm_uc_incr                        true
% 7.82/1.49  --sat_out_model                         small
% 7.82/1.49  --sat_out_clauses                       false
% 7.82/1.49  
% 7.82/1.49  ------ QBF Options
% 7.82/1.49  
% 7.82/1.49  --qbf_mode                              false
% 7.82/1.49  --qbf_elim_univ                         false
% 7.82/1.49  --qbf_dom_inst                          none
% 7.82/1.49  --qbf_dom_pre_inst                      false
% 7.82/1.49  --qbf_sk_in                             false
% 7.82/1.49  --qbf_pred_elim                         true
% 7.82/1.49  --qbf_split                             512
% 7.82/1.49  
% 7.82/1.49  ------ BMC1 Options
% 7.82/1.49  
% 7.82/1.49  --bmc1_incremental                      false
% 7.82/1.49  --bmc1_axioms                           reachable_all
% 7.82/1.49  --bmc1_min_bound                        0
% 7.82/1.49  --bmc1_max_bound                        -1
% 7.82/1.49  --bmc1_max_bound_default                -1
% 7.82/1.49  --bmc1_symbol_reachability              true
% 7.82/1.49  --bmc1_property_lemmas                  false
% 7.82/1.49  --bmc1_k_induction                      false
% 7.82/1.49  --bmc1_non_equiv_states                 false
% 7.82/1.49  --bmc1_deadlock                         false
% 7.82/1.49  --bmc1_ucm                              false
% 7.82/1.49  --bmc1_add_unsat_core                   none
% 7.82/1.49  --bmc1_unsat_core_children              false
% 7.82/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.82/1.49  --bmc1_out_stat                         full
% 7.82/1.49  --bmc1_ground_init                      false
% 7.82/1.49  --bmc1_pre_inst_next_state              false
% 7.82/1.49  --bmc1_pre_inst_state                   false
% 7.82/1.49  --bmc1_pre_inst_reach_state             false
% 7.82/1.49  --bmc1_out_unsat_core                   false
% 7.82/1.49  --bmc1_aig_witness_out                  false
% 7.82/1.49  --bmc1_verbose                          false
% 7.82/1.49  --bmc1_dump_clauses_tptp                false
% 7.82/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.82/1.49  --bmc1_dump_file                        -
% 7.82/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.82/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.82/1.49  --bmc1_ucm_extend_mode                  1
% 7.82/1.49  --bmc1_ucm_init_mode                    2
% 7.82/1.49  --bmc1_ucm_cone_mode                    none
% 7.82/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.82/1.49  --bmc1_ucm_relax_model                  4
% 7.82/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.82/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.82/1.49  --bmc1_ucm_layered_model                none
% 7.82/1.49  --bmc1_ucm_max_lemma_size               10
% 7.82/1.49  
% 7.82/1.49  ------ AIG Options
% 7.82/1.49  
% 7.82/1.49  --aig_mode                              false
% 7.82/1.49  
% 7.82/1.49  ------ Instantiation Options
% 7.82/1.49  
% 7.82/1.49  --instantiation_flag                    true
% 7.82/1.49  --inst_sos_flag                         true
% 7.82/1.49  --inst_sos_phase                        true
% 7.82/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.82/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.82/1.49  --inst_lit_sel_side                     num_symb
% 7.82/1.49  --inst_solver_per_active                1400
% 7.82/1.49  --inst_solver_calls_frac                1.
% 7.82/1.49  --inst_passive_queue_type               priority_queues
% 7.82/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.82/1.49  --inst_passive_queues_freq              [25;2]
% 7.82/1.49  --inst_dismatching                      true
% 7.82/1.49  --inst_eager_unprocessed_to_passive     true
% 7.82/1.49  --inst_prop_sim_given                   true
% 7.82/1.49  --inst_prop_sim_new                     false
% 7.82/1.49  --inst_subs_new                         false
% 7.82/1.49  --inst_eq_res_simp                      false
% 7.82/1.49  --inst_subs_given                       false
% 7.82/1.49  --inst_orphan_elimination               true
% 7.82/1.49  --inst_learning_loop_flag               true
% 7.82/1.49  --inst_learning_start                   3000
% 7.82/1.49  --inst_learning_factor                  2
% 7.82/1.49  --inst_start_prop_sim_after_learn       3
% 7.82/1.49  --inst_sel_renew                        solver
% 7.82/1.49  --inst_lit_activity_flag                true
% 7.82/1.49  --inst_restr_to_given                   false
% 7.82/1.49  --inst_activity_threshold               500
% 7.82/1.49  --inst_out_proof                        true
% 7.82/1.49  
% 7.82/1.49  ------ Resolution Options
% 7.82/1.49  
% 7.82/1.49  --resolution_flag                       true
% 7.82/1.49  --res_lit_sel                           adaptive
% 7.82/1.49  --res_lit_sel_side                      none
% 7.82/1.49  --res_ordering                          kbo
% 7.82/1.49  --res_to_prop_solver                    active
% 7.82/1.49  --res_prop_simpl_new                    false
% 7.82/1.49  --res_prop_simpl_given                  true
% 7.82/1.49  --res_passive_queue_type                priority_queues
% 7.82/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.82/1.49  --res_passive_queues_freq               [15;5]
% 7.82/1.49  --res_forward_subs                      full
% 7.82/1.49  --res_backward_subs                     full
% 7.82/1.49  --res_forward_subs_resolution           true
% 7.82/1.49  --res_backward_subs_resolution          true
% 7.82/1.49  --res_orphan_elimination                true
% 7.82/1.49  --res_time_limit                        2.
% 7.82/1.49  --res_out_proof                         true
% 7.82/1.49  
% 7.82/1.49  ------ Superposition Options
% 7.82/1.49  
% 7.82/1.49  --superposition_flag                    true
% 7.82/1.49  --sup_passive_queue_type                priority_queues
% 7.82/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.82/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.82/1.49  --demod_completeness_check              fast
% 7.82/1.49  --demod_use_ground                      true
% 7.82/1.49  --sup_to_prop_solver                    passive
% 7.82/1.49  --sup_prop_simpl_new                    true
% 7.82/1.49  --sup_prop_simpl_given                  true
% 7.82/1.49  --sup_fun_splitting                     true
% 7.82/1.49  --sup_smt_interval                      50000
% 7.82/1.49  
% 7.82/1.49  ------ Superposition Simplification Setup
% 7.82/1.49  
% 7.82/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.82/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.82/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.82/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.82/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.82/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.82/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.82/1.49  --sup_immed_triv                        [TrivRules]
% 7.82/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.82/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.82/1.49  --sup_immed_bw_main                     []
% 7.82/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.82/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.82/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.82/1.49  --sup_input_bw                          []
% 7.82/1.49  
% 7.82/1.49  ------ Combination Options
% 7.82/1.49  
% 7.82/1.49  --comb_res_mult                         3
% 7.82/1.49  --comb_sup_mult                         2
% 7.82/1.49  --comb_inst_mult                        10
% 7.82/1.49  
% 7.82/1.49  ------ Debug Options
% 7.82/1.49  
% 7.82/1.49  --dbg_backtrace                         false
% 7.82/1.49  --dbg_dump_prop_clauses                 false
% 7.82/1.49  --dbg_dump_prop_clauses_file            -
% 7.82/1.49  --dbg_out_stat                          false
% 7.82/1.49  ------ Parsing...
% 7.82/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.82/1.49  
% 7.82/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.82/1.49  
% 7.82/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.82/1.49  
% 7.82/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.82/1.49  ------ Proving...
% 7.82/1.49  ------ Problem Properties 
% 7.82/1.49  
% 7.82/1.49  
% 7.82/1.49  clauses                                 20
% 7.82/1.49  conjectures                             1
% 7.82/1.49  EPR                                     1
% 7.82/1.49  Horn                                    19
% 7.82/1.49  unary                                   13
% 7.82/1.49  binary                                  5
% 7.82/1.49  lits                                    29
% 7.82/1.49  lits eq                                 14
% 7.82/1.49  fd_pure                                 0
% 7.82/1.49  fd_pseudo                               0
% 7.82/1.49  fd_cond                                 1
% 7.82/1.49  fd_pseudo_cond                          2
% 7.82/1.49  AC symbols                              1
% 7.82/1.49  
% 7.82/1.49  ------ Schedule dynamic 5 is on 
% 7.82/1.49  
% 7.82/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.82/1.49  
% 7.82/1.49  
% 7.82/1.49  ------ 
% 7.82/1.49  Current options:
% 7.82/1.49  ------ 
% 7.82/1.49  
% 7.82/1.49  ------ Input Options
% 7.82/1.49  
% 7.82/1.49  --out_options                           all
% 7.82/1.49  --tptp_safe_out                         true
% 7.82/1.49  --problem_path                          ""
% 7.82/1.49  --include_path                          ""
% 7.82/1.49  --clausifier                            res/vclausify_rel
% 7.82/1.49  --clausifier_options                    ""
% 7.82/1.49  --stdin                                 false
% 7.82/1.49  --stats_out                             all
% 7.82/1.49  
% 7.82/1.49  ------ General Options
% 7.82/1.49  
% 7.82/1.49  --fof                                   false
% 7.82/1.49  --time_out_real                         305.
% 7.82/1.49  --time_out_virtual                      -1.
% 7.82/1.49  --symbol_type_check                     false
% 7.82/1.49  --clausify_out                          false
% 7.82/1.49  --sig_cnt_out                           false
% 7.82/1.49  --trig_cnt_out                          false
% 7.82/1.49  --trig_cnt_out_tolerance                1.
% 7.82/1.49  --trig_cnt_out_sk_spl                   false
% 7.82/1.49  --abstr_cl_out                          false
% 7.82/1.49  
% 7.82/1.49  ------ Global Options
% 7.82/1.49  
% 7.82/1.49  --schedule                              default
% 7.82/1.49  --add_important_lit                     false
% 7.82/1.49  --prop_solver_per_cl                    1000
% 7.82/1.49  --min_unsat_core                        false
% 7.82/1.49  --soft_assumptions                      false
% 7.82/1.49  --soft_lemma_size                       3
% 7.82/1.49  --prop_impl_unit_size                   0
% 7.82/1.49  --prop_impl_unit                        []
% 7.82/1.49  --share_sel_clauses                     true
% 7.82/1.49  --reset_solvers                         false
% 7.82/1.49  --bc_imp_inh                            [conj_cone]
% 7.82/1.49  --conj_cone_tolerance                   3.
% 7.82/1.49  --extra_neg_conj                        none
% 7.82/1.49  --large_theory_mode                     true
% 7.82/1.49  --prolific_symb_bound                   200
% 7.82/1.49  --lt_threshold                          2000
% 7.82/1.49  --clause_weak_htbl                      true
% 7.82/1.49  --gc_record_bc_elim                     false
% 7.82/1.49  
% 7.82/1.49  ------ Preprocessing Options
% 7.82/1.49  
% 7.82/1.49  --preprocessing_flag                    true
% 7.82/1.49  --time_out_prep_mult                    0.1
% 7.82/1.49  --splitting_mode                        input
% 7.82/1.49  --splitting_grd                         true
% 7.82/1.49  --splitting_cvd                         false
% 7.82/1.49  --splitting_cvd_svl                     false
% 7.82/1.49  --splitting_nvd                         32
% 7.82/1.49  --sub_typing                            true
% 7.82/1.49  --prep_gs_sim                           true
% 7.82/1.49  --prep_unflatten                        true
% 7.82/1.49  --prep_res_sim                          true
% 7.82/1.49  --prep_upred                            true
% 7.82/1.49  --prep_sem_filter                       exhaustive
% 7.82/1.49  --prep_sem_filter_out                   false
% 7.82/1.49  --pred_elim                             true
% 7.82/1.49  --res_sim_input                         true
% 7.82/1.49  --eq_ax_congr_red                       true
% 7.82/1.49  --pure_diseq_elim                       true
% 7.82/1.49  --brand_transform                       false
% 7.82/1.49  --non_eq_to_eq                          false
% 7.82/1.49  --prep_def_merge                        true
% 7.82/1.49  --prep_def_merge_prop_impl              false
% 7.82/1.49  --prep_def_merge_mbd                    true
% 7.82/1.49  --prep_def_merge_tr_red                 false
% 7.82/1.49  --prep_def_merge_tr_cl                  false
% 7.82/1.49  --smt_preprocessing                     true
% 7.82/1.49  --smt_ac_axioms                         fast
% 7.82/1.49  --preprocessed_out                      false
% 7.82/1.49  --preprocessed_stats                    false
% 7.82/1.49  
% 7.82/1.49  ------ Abstraction refinement Options
% 7.82/1.49  
% 7.82/1.49  --abstr_ref                             []
% 7.82/1.49  --abstr_ref_prep                        false
% 7.82/1.49  --abstr_ref_until_sat                   false
% 7.82/1.49  --abstr_ref_sig_restrict                funpre
% 7.82/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.82/1.49  --abstr_ref_under                       []
% 7.82/1.49  
% 7.82/1.49  ------ SAT Options
% 7.82/1.49  
% 7.82/1.49  --sat_mode                              false
% 7.82/1.49  --sat_fm_restart_options                ""
% 7.82/1.49  --sat_gr_def                            false
% 7.82/1.49  --sat_epr_types                         true
% 7.82/1.49  --sat_non_cyclic_types                  false
% 7.82/1.49  --sat_finite_models                     false
% 7.82/1.49  --sat_fm_lemmas                         false
% 7.82/1.49  --sat_fm_prep                           false
% 7.82/1.49  --sat_fm_uc_incr                        true
% 7.82/1.49  --sat_out_model                         small
% 7.82/1.49  --sat_out_clauses                       false
% 7.82/1.49  
% 7.82/1.49  ------ QBF Options
% 7.82/1.49  
% 7.82/1.49  --qbf_mode                              false
% 7.82/1.49  --qbf_elim_univ                         false
% 7.82/1.49  --qbf_dom_inst                          none
% 7.82/1.49  --qbf_dom_pre_inst                      false
% 7.82/1.49  --qbf_sk_in                             false
% 7.82/1.49  --qbf_pred_elim                         true
% 7.82/1.49  --qbf_split                             512
% 7.82/1.49  
% 7.82/1.49  ------ BMC1 Options
% 7.82/1.49  
% 7.82/1.49  --bmc1_incremental                      false
% 7.82/1.49  --bmc1_axioms                           reachable_all
% 7.82/1.49  --bmc1_min_bound                        0
% 7.82/1.49  --bmc1_max_bound                        -1
% 7.82/1.49  --bmc1_max_bound_default                -1
% 7.82/1.49  --bmc1_symbol_reachability              true
% 7.82/1.49  --bmc1_property_lemmas                  false
% 7.82/1.49  --bmc1_k_induction                      false
% 7.82/1.49  --bmc1_non_equiv_states                 false
% 7.82/1.49  --bmc1_deadlock                         false
% 7.82/1.49  --bmc1_ucm                              false
% 7.82/1.49  --bmc1_add_unsat_core                   none
% 7.82/1.49  --bmc1_unsat_core_children              false
% 7.82/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.82/1.49  --bmc1_out_stat                         full
% 7.82/1.49  --bmc1_ground_init                      false
% 7.82/1.49  --bmc1_pre_inst_next_state              false
% 7.82/1.49  --bmc1_pre_inst_state                   false
% 7.82/1.49  --bmc1_pre_inst_reach_state             false
% 7.82/1.49  --bmc1_out_unsat_core                   false
% 7.82/1.49  --bmc1_aig_witness_out                  false
% 7.82/1.49  --bmc1_verbose                          false
% 7.82/1.49  --bmc1_dump_clauses_tptp                false
% 7.82/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.82/1.49  --bmc1_dump_file                        -
% 7.82/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.82/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.82/1.49  --bmc1_ucm_extend_mode                  1
% 7.82/1.49  --bmc1_ucm_init_mode                    2
% 7.82/1.49  --bmc1_ucm_cone_mode                    none
% 7.82/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.82/1.49  --bmc1_ucm_relax_model                  4
% 7.82/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.82/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.82/1.49  --bmc1_ucm_layered_model                none
% 7.82/1.49  --bmc1_ucm_max_lemma_size               10
% 7.82/1.49  
% 7.82/1.49  ------ AIG Options
% 7.82/1.49  
% 7.82/1.49  --aig_mode                              false
% 7.82/1.49  
% 7.82/1.49  ------ Instantiation Options
% 7.82/1.49  
% 7.82/1.49  --instantiation_flag                    true
% 7.82/1.49  --inst_sos_flag                         true
% 7.82/1.49  --inst_sos_phase                        true
% 7.82/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.82/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.82/1.49  --inst_lit_sel_side                     none
% 7.82/1.49  --inst_solver_per_active                1400
% 7.82/1.49  --inst_solver_calls_frac                1.
% 7.82/1.49  --inst_passive_queue_type               priority_queues
% 7.82/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.82/1.49  --inst_passive_queues_freq              [25;2]
% 7.82/1.49  --inst_dismatching                      true
% 7.82/1.49  --inst_eager_unprocessed_to_passive     true
% 7.82/1.49  --inst_prop_sim_given                   true
% 7.82/1.49  --inst_prop_sim_new                     false
% 7.82/1.49  --inst_subs_new                         false
% 7.82/1.49  --inst_eq_res_simp                      false
% 7.82/1.49  --inst_subs_given                       false
% 7.82/1.49  --inst_orphan_elimination               true
% 7.82/1.49  --inst_learning_loop_flag               true
% 7.82/1.49  --inst_learning_start                   3000
% 7.82/1.49  --inst_learning_factor                  2
% 7.82/1.49  --inst_start_prop_sim_after_learn       3
% 7.82/1.49  --inst_sel_renew                        solver
% 7.82/1.49  --inst_lit_activity_flag                true
% 7.82/1.49  --inst_restr_to_given                   false
% 7.82/1.49  --inst_activity_threshold               500
% 7.82/1.49  --inst_out_proof                        true
% 7.82/1.49  
% 7.82/1.49  ------ Resolution Options
% 7.82/1.49  
% 7.82/1.49  --resolution_flag                       false
% 7.82/1.49  --res_lit_sel                           adaptive
% 7.82/1.49  --res_lit_sel_side                      none
% 7.82/1.49  --res_ordering                          kbo
% 7.82/1.49  --res_to_prop_solver                    active
% 7.82/1.49  --res_prop_simpl_new                    false
% 7.82/1.49  --res_prop_simpl_given                  true
% 7.82/1.49  --res_passive_queue_type                priority_queues
% 7.82/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.82/1.49  --res_passive_queues_freq               [15;5]
% 7.82/1.49  --res_forward_subs                      full
% 7.82/1.49  --res_backward_subs                     full
% 7.82/1.49  --res_forward_subs_resolution           true
% 7.82/1.49  --res_backward_subs_resolution          true
% 7.82/1.49  --res_orphan_elimination                true
% 7.82/1.49  --res_time_limit                        2.
% 7.82/1.49  --res_out_proof                         true
% 7.82/1.49  
% 7.82/1.49  ------ Superposition Options
% 7.82/1.49  
% 7.82/1.49  --superposition_flag                    true
% 7.82/1.49  --sup_passive_queue_type                priority_queues
% 7.82/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.82/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.82/1.49  --demod_completeness_check              fast
% 7.82/1.49  --demod_use_ground                      true
% 7.82/1.49  --sup_to_prop_solver                    passive
% 7.82/1.49  --sup_prop_simpl_new                    true
% 7.82/1.49  --sup_prop_simpl_given                  true
% 7.82/1.49  --sup_fun_splitting                     true
% 7.82/1.49  --sup_smt_interval                      50000
% 7.82/1.49  
% 7.82/1.49  ------ Superposition Simplification Setup
% 7.82/1.49  
% 7.82/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.82/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.82/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.82/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.82/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.82/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.82/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.82/1.49  --sup_immed_triv                        [TrivRules]
% 7.82/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.82/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.82/1.49  --sup_immed_bw_main                     []
% 7.82/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.82/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.82/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.82/1.49  --sup_input_bw                          []
% 7.82/1.49  
% 7.82/1.49  ------ Combination Options
% 7.82/1.49  
% 7.82/1.49  --comb_res_mult                         3
% 7.82/1.49  --comb_sup_mult                         2
% 7.82/1.49  --comb_inst_mult                        10
% 7.82/1.49  
% 7.82/1.49  ------ Debug Options
% 7.82/1.49  
% 7.82/1.49  --dbg_backtrace                         false
% 7.82/1.49  --dbg_dump_prop_clauses                 false
% 7.82/1.49  --dbg_dump_prop_clauses_file            -
% 7.82/1.49  --dbg_out_stat                          false
% 7.82/1.49  
% 7.82/1.49  
% 7.82/1.49  
% 7.82/1.49  
% 7.82/1.49  ------ Proving...
% 7.82/1.49  
% 7.82/1.49  
% 7.82/1.49  % SZS status Theorem for theBenchmark.p
% 7.82/1.49  
% 7.82/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.82/1.49  
% 7.82/1.49  fof(f13,axiom,(
% 7.82/1.49    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 7.82/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.49  
% 7.82/1.49  fof(f54,plain,(
% 7.82/1.49    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 7.82/1.49    inference(cnf_transformation,[],[f13])).
% 7.82/1.49  
% 7.82/1.49  fof(f1,axiom,(
% 7.82/1.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.82/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.49  
% 7.82/1.49  fof(f41,plain,(
% 7.82/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.82/1.49    inference(cnf_transformation,[],[f1])).
% 7.82/1.49  
% 7.82/1.49  fof(f26,conjecture,(
% 7.82/1.49    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 7.82/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.49  
% 7.82/1.49  fof(f27,negated_conjecture,(
% 7.82/1.49    ~! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 7.82/1.49    inference(negated_conjecture,[],[f26])).
% 7.82/1.49  
% 7.82/1.49  fof(f32,plain,(
% 7.82/1.49    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1)),
% 7.82/1.49    inference(ennf_transformation,[],[f27])).
% 7.82/1.49  
% 7.82/1.49  fof(f39,plain,(
% 7.82/1.49    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1) => k1_xboole_0 = k2_xboole_0(k1_tarski(sK2),sK3)),
% 7.82/1.49    introduced(choice_axiom,[])).
% 7.82/1.49  
% 7.82/1.49  fof(f40,plain,(
% 7.82/1.49    k1_xboole_0 = k2_xboole_0(k1_tarski(sK2),sK3)),
% 7.82/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f32,f39])).
% 7.82/1.49  
% 7.82/1.49  fof(f70,plain,(
% 7.82/1.49    k1_xboole_0 = k2_xboole_0(k1_tarski(sK2),sK3)),
% 7.82/1.49    inference(cnf_transformation,[],[f40])).
% 7.82/1.49  
% 7.82/1.49  fof(f14,axiom,(
% 7.82/1.49    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)),
% 7.82/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.49  
% 7.82/1.49  fof(f55,plain,(
% 7.82/1.49    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 7.82/1.49    inference(cnf_transformation,[],[f14])).
% 7.82/1.49  
% 7.82/1.49  fof(f15,axiom,(
% 7.82/1.49    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 7.82/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.49  
% 7.82/1.49  fof(f56,plain,(
% 7.82/1.49    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 7.82/1.49    inference(cnf_transformation,[],[f15])).
% 7.82/1.49  
% 7.82/1.49  fof(f16,axiom,(
% 7.82/1.49    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.82/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.49  
% 7.82/1.49  fof(f57,plain,(
% 7.82/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.82/1.49    inference(cnf_transformation,[],[f16])).
% 7.82/1.49  
% 7.82/1.49  fof(f17,axiom,(
% 7.82/1.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.82/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.49  
% 7.82/1.49  fof(f58,plain,(
% 7.82/1.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.82/1.49    inference(cnf_transformation,[],[f17])).
% 7.82/1.49  
% 7.82/1.49  fof(f18,axiom,(
% 7.82/1.49    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 7.82/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.49  
% 7.82/1.49  fof(f59,plain,(
% 7.82/1.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 7.82/1.49    inference(cnf_transformation,[],[f18])).
% 7.82/1.49  
% 7.82/1.49  fof(f19,axiom,(
% 7.82/1.49    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 7.82/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.49  
% 7.82/1.49  fof(f60,plain,(
% 7.82/1.49    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 7.82/1.49    inference(cnf_transformation,[],[f19])).
% 7.82/1.49  
% 7.82/1.49  fof(f20,axiom,(
% 7.82/1.49    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 7.82/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.49  
% 7.82/1.49  fof(f61,plain,(
% 7.82/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 7.82/1.49    inference(cnf_transformation,[],[f20])).
% 7.82/1.49  
% 7.82/1.49  fof(f21,axiom,(
% 7.82/1.49    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 7.82/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.49  
% 7.82/1.49  fof(f62,plain,(
% 7.82/1.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 7.82/1.49    inference(cnf_transformation,[],[f21])).
% 7.82/1.49  
% 7.82/1.49  fof(f71,plain,(
% 7.82/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 7.82/1.49    inference(definition_unfolding,[],[f61,f62])).
% 7.82/1.49  
% 7.82/1.49  fof(f72,plain,(
% 7.82/1.49    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 7.82/1.49    inference(definition_unfolding,[],[f60,f71])).
% 7.82/1.49  
% 7.82/1.49  fof(f73,plain,(
% 7.82/1.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 7.82/1.49    inference(definition_unfolding,[],[f59,f72])).
% 7.82/1.49  
% 7.82/1.49  fof(f74,plain,(
% 7.82/1.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 7.82/1.49    inference(definition_unfolding,[],[f58,f73])).
% 7.82/1.49  
% 7.82/1.49  fof(f75,plain,(
% 7.82/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 7.82/1.49    inference(definition_unfolding,[],[f57,f74])).
% 7.82/1.49  
% 7.82/1.49  fof(f76,plain,(
% 7.82/1.49    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 7.82/1.49    inference(definition_unfolding,[],[f56,f75])).
% 7.82/1.49  
% 7.82/1.49  fof(f80,plain,(
% 7.82/1.49    k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) = k1_xboole_0),
% 7.82/1.49    inference(definition_unfolding,[],[f70,f55,f76])).
% 7.82/1.49  
% 7.82/1.49  fof(f12,axiom,(
% 7.82/1.49    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 7.82/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.49  
% 7.82/1.49  fof(f53,plain,(
% 7.82/1.49    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 7.82/1.49    inference(cnf_transformation,[],[f12])).
% 7.82/1.49  
% 7.82/1.49  fof(f2,axiom,(
% 7.82/1.49    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 7.82/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.49  
% 7.82/1.49  fof(f42,plain,(
% 7.82/1.49    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 7.82/1.49    inference(cnf_transformation,[],[f2])).
% 7.82/1.49  
% 7.82/1.49  fof(f11,axiom,(
% 7.82/1.49    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 7.82/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.49  
% 7.82/1.49  fof(f52,plain,(
% 7.82/1.49    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.82/1.49    inference(cnf_transformation,[],[f11])).
% 7.82/1.49  
% 7.82/1.49  fof(f23,axiom,(
% 7.82/1.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 7.82/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.49  
% 7.82/1.49  fof(f67,plain,(
% 7.82/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 7.82/1.49    inference(cnf_transformation,[],[f23])).
% 7.82/1.49  
% 7.82/1.49  fof(f78,plain,(
% 7.82/1.49    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 7.82/1.49    inference(definition_unfolding,[],[f67,f55,f75])).
% 7.82/1.49  
% 7.82/1.49  fof(f9,axiom,(
% 7.82/1.49    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 7.82/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.49  
% 7.82/1.49  fof(f50,plain,(
% 7.82/1.49    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 7.82/1.49    inference(cnf_transformation,[],[f9])).
% 7.82/1.49  
% 7.82/1.49  fof(f5,axiom,(
% 7.82/1.49    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 7.82/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.49  
% 7.82/1.49  fof(f46,plain,(
% 7.82/1.49    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 7.82/1.49    inference(cnf_transformation,[],[f5])).
% 7.82/1.49  
% 7.82/1.49  fof(f77,plain,(
% 7.82/1.49    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 7.82/1.49    inference(definition_unfolding,[],[f50,f46])).
% 7.82/1.49  
% 7.82/1.49  fof(f7,axiom,(
% 7.82/1.49    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 7.82/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.49  
% 7.82/1.49  fof(f30,plain,(
% 7.82/1.49    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 7.82/1.49    inference(ennf_transformation,[],[f7])).
% 7.82/1.49  
% 7.82/1.49  fof(f48,plain,(
% 7.82/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 7.82/1.49    inference(cnf_transformation,[],[f30])).
% 7.82/1.49  
% 7.82/1.49  fof(f8,axiom,(
% 7.82/1.49    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 7.82/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.49  
% 7.82/1.49  fof(f49,plain,(
% 7.82/1.49    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 7.82/1.49    inference(cnf_transformation,[],[f8])).
% 7.82/1.49  
% 7.82/1.49  fof(f25,axiom,(
% 7.82/1.49    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 7.82/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.49  
% 7.82/1.49  fof(f69,plain,(
% 7.82/1.49    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 7.82/1.49    inference(cnf_transformation,[],[f25])).
% 7.82/1.49  
% 7.82/1.49  fof(f3,axiom,(
% 7.82/1.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 7.82/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.49  
% 7.82/1.49  fof(f28,plain,(
% 7.82/1.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 7.82/1.49    inference(rectify,[],[f3])).
% 7.82/1.49  
% 7.82/1.49  fof(f29,plain,(
% 7.82/1.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 7.82/1.49    inference(ennf_transformation,[],[f28])).
% 7.82/1.49  
% 7.82/1.49  fof(f33,plain,(
% 7.82/1.49    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 7.82/1.49    introduced(choice_axiom,[])).
% 7.82/1.49  
% 7.82/1.49  fof(f34,plain,(
% 7.82/1.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 7.82/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f33])).
% 7.82/1.49  
% 7.82/1.49  fof(f44,plain,(
% 7.82/1.49    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 7.82/1.49    inference(cnf_transformation,[],[f34])).
% 7.82/1.49  
% 7.82/1.49  fof(f4,axiom,(
% 7.82/1.49    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 7.82/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.49  
% 7.82/1.49  fof(f45,plain,(
% 7.82/1.49    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 7.82/1.49    inference(cnf_transformation,[],[f4])).
% 7.82/1.49  
% 7.82/1.49  fof(f6,axiom,(
% 7.82/1.49    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 7.82/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.49  
% 7.82/1.49  fof(f47,plain,(
% 7.82/1.49    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 7.82/1.49    inference(cnf_transformation,[],[f6])).
% 7.82/1.49  
% 7.82/1.49  fof(f10,axiom,(
% 7.82/1.49    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 7.82/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.49  
% 7.82/1.49  fof(f31,plain,(
% 7.82/1.49    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 7.82/1.49    inference(ennf_transformation,[],[f10])).
% 7.82/1.49  
% 7.82/1.49  fof(f51,plain,(
% 7.82/1.49    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 7.82/1.49    inference(cnf_transformation,[],[f31])).
% 7.82/1.49  
% 7.82/1.49  fof(f22,axiom,(
% 7.82/1.49    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 7.82/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.49  
% 7.82/1.49  fof(f35,plain,(
% 7.82/1.49    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 7.82/1.49    inference(nnf_transformation,[],[f22])).
% 7.82/1.49  
% 7.82/1.49  fof(f36,plain,(
% 7.82/1.49    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 7.82/1.49    inference(rectify,[],[f35])).
% 7.82/1.49  
% 7.82/1.49  fof(f37,plain,(
% 7.82/1.49    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK1(X0,X1),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r1_tarski(sK1(X0,X1),X0) | r2_hidden(sK1(X0,X1),X1))))),
% 7.82/1.49    introduced(choice_axiom,[])).
% 7.82/1.49  
% 7.82/1.49  fof(f38,plain,(
% 7.82/1.49    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK1(X0,X1),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r1_tarski(sK1(X0,X1),X0) | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 7.82/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f36,f37])).
% 7.82/1.49  
% 7.82/1.49  fof(f64,plain,(
% 7.82/1.49    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 7.82/1.49    inference(cnf_transformation,[],[f38])).
% 7.82/1.49  
% 7.82/1.49  fof(f81,plain,(
% 7.82/1.49    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 7.82/1.49    inference(equality_resolution,[],[f64])).
% 7.82/1.49  
% 7.82/1.49  fof(f24,axiom,(
% 7.82/1.49    k1_tarski(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0)),
% 7.82/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.49  
% 7.82/1.49  fof(f68,plain,(
% 7.82/1.49    k1_tarski(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0)),
% 7.82/1.49    inference(cnf_transformation,[],[f24])).
% 7.82/1.49  
% 7.82/1.49  fof(f79,plain,(
% 7.82/1.49    k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_zfmisc_1(k1_xboole_0)),
% 7.82/1.49    inference(definition_unfolding,[],[f68,f76])).
% 7.82/1.49  
% 7.82/1.49  cnf(c_12,plain,
% 7.82/1.49      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 7.82/1.49      inference(cnf_transformation,[],[f54]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_0,plain,
% 7.82/1.49      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 7.82/1.49      inference(cnf_transformation,[],[f41]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_20,negated_conjecture,
% 7.82/1.49      ( k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) = k1_xboole_0 ),
% 7.82/1.49      inference(cnf_transformation,[],[f80]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_11,plain,
% 7.82/1.49      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 7.82/1.49      inference(cnf_transformation,[],[f53]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_1,plain,
% 7.82/1.49      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 7.82/1.49      inference(cnf_transformation,[],[f42]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_665,negated_conjecture,
% 7.82/1.49      ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))) = k1_xboole_0 ),
% 7.82/1.49      inference(theory_normalisation,[status(thm)],[c_20,c_11,c_1]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_1175,plain,
% 7.82/1.49      ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) = k1_xboole_0 ),
% 7.82/1.49      inference(demodulation,[status(thm)],[c_0,c_665]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_1384,plain,
% 7.82/1.49      ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),X0)) = k5_xboole_0(k1_xboole_0,X0) ),
% 7.82/1.49      inference(superposition,[status(thm)],[c_1175,c_11]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_10,plain,
% 7.82/1.49      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.82/1.49      inference(cnf_transformation,[],[f52]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_1268,plain,
% 7.82/1.49      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 7.82/1.49      inference(superposition,[status(thm)],[c_10,c_1]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_1390,plain,
% 7.82/1.49      ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),X0)) = X0 ),
% 7.82/1.49      inference(light_normalisation,[status(thm)],[c_1384,c_1268]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_1558,plain,
% 7.82/1.49      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = k5_xboole_0(sK3,k1_xboole_0) ),
% 7.82/1.49      inference(superposition,[status(thm)],[c_12,c_1390]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_1562,plain,
% 7.82/1.49      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = sK3 ),
% 7.82/1.49      inference(demodulation,[status(thm)],[c_1558,c_10]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_17,plain,
% 7.82/1.49      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
% 7.82/1.49      inference(cnf_transformation,[],[f78]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_666,plain,
% 7.82/1.49      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) ),
% 7.82/1.49      inference(theory_normalisation,[status(thm)],[c_17,c_11,c_1]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_1383,plain,
% 7.82/1.49      ( k5_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X2) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X0,X1)),X2)) ),
% 7.82/1.49      inference(superposition,[status(thm)],[c_666,c_11]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_979,plain,
% 7.82/1.49      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
% 7.82/1.49      inference(superposition,[status(thm)],[c_11,c_1]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_1566,plain,
% 7.82/1.49      ( k5_xboole_0(sK3,k5_xboole_0(sK3,X0)) = X0 ),
% 7.82/1.49      inference(demodulation,[status(thm)],[c_1562,c_1390]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_1574,plain,
% 7.82/1.49      ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(sK3,X0),X1)) = k5_xboole_0(X0,X1) ),
% 7.82/1.49      inference(superposition,[status(thm)],[c_1566,c_11]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_6566,plain,
% 7.82/1.49      ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,sK3)),X2)) = k5_xboole_0(k5_xboole_0(X1,X0),X2) ),
% 7.82/1.49      inference(superposition,[status(thm)],[c_979,c_1574]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_1568,plain,
% 7.82/1.49      ( k5_xboole_0(sK3,k5_xboole_0(X0,sK3)) = X0 ),
% 7.82/1.49      inference(superposition,[status(thm)],[c_1,c_1566]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_1615,plain,
% 7.82/1.49      ( k5_xboole_0(sK3,k5_xboole_0(X0,k5_xboole_0(X1,sK3))) = k5_xboole_0(X0,X1) ),
% 7.82/1.49      inference(superposition,[status(thm)],[c_11,c_1568]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_3368,plain,
% 7.82/1.49      ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,sK3)),X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
% 7.82/1.49      inference(superposition,[status(thm)],[c_1615,c_11]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_3379,plain,
% 7.82/1.49      ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,sK3)),X2)) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 7.82/1.49      inference(light_normalisation,[status(thm)],[c_3368,c_11]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_6605,plain,
% 7.82/1.49      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
% 7.82/1.49      inference(light_normalisation,[status(thm)],[c_6566,c_3379]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_13460,plain,
% 7.82/1.49      ( k5_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X2) = k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X1,X2))) ),
% 7.82/1.49      inference(demodulation,[status(thm)],[c_1383,c_6605]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_13703,plain,
% 7.82/1.49      ( k5_xboole_0(sK3,k5_xboole_0(k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,X0)),X1)) = k5_xboole_0(k3_xboole_0(sK3,X0),k5_xboole_0(X0,X1)) ),
% 7.82/1.49      inference(superposition,[status(thm)],[c_13460,c_1566]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_14681,plain,
% 7.82/1.49      ( k5_xboole_0(sK3,k5_xboole_0(k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) = k5_xboole_0(k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),sK3) ),
% 7.82/1.49      inference(superposition,[status(thm)],[c_1562,c_13703]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_1668,plain,
% 7.82/1.49      ( k5_xboole_0(X0,k5_xboole_0(sK3,X0)) = k5_xboole_0(sK3,k1_xboole_0) ),
% 7.82/1.49      inference(superposition,[status(thm)],[c_12,c_1574]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_1688,plain,
% 7.82/1.49      ( k5_xboole_0(X0,k5_xboole_0(sK3,X0)) = sK3 ),
% 7.82/1.49      inference(demodulation,[status(thm)],[c_1668,c_10]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_2016,plain,
% 7.82/1.49      ( k5_xboole_0(X0,k5_xboole_0(X0,sK3)) = sK3 ),
% 7.82/1.49      inference(superposition,[status(thm)],[c_1,c_1688]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_14688,plain,
% 7.82/1.49      ( k5_xboole_0(sK3,k5_xboole_0(k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,X0)),k5_xboole_0(X0,sK3))) = k5_xboole_0(k3_xboole_0(sK3,X0),sK3) ),
% 7.82/1.49      inference(superposition,[status(thm)],[c_2016,c_13703]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_1262,plain,
% 7.82/1.49      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
% 7.82/1.49      inference(superposition,[status(thm)],[c_0,c_666]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_980,plain,
% 7.82/1.49      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
% 7.82/1.49      inference(superposition,[status(thm)],[c_11,c_1]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_6949,plain,
% 7.82/1.49      ( k5_xboole_0(k5_xboole_0(sK3,X0),k5_xboole_0(X1,sK3)) = k5_xboole_0(X1,X0) ),
% 7.82/1.49      inference(superposition,[status(thm)],[c_1566,c_980]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_2023,plain,
% 7.82/1.49      ( k5_xboole_0(k5_xboole_0(sK3,X0),X0) = sK3 ),
% 7.82/1.49      inference(superposition,[status(thm)],[c_1566,c_1688]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_2150,plain,
% 7.82/1.49      ( k5_xboole_0(k5_xboole_0(sK3,X0),k5_xboole_0(X0,X1)) = k5_xboole_0(sK3,X1) ),
% 7.82/1.49      inference(superposition,[status(thm)],[c_2023,c_11]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_1664,plain,
% 7.82/1.49      ( k5_xboole_0(sK3,k5_xboole_0(X0,k5_xboole_0(sK3,X1))) = k5_xboole_0(X1,X0) ),
% 7.82/1.49      inference(superposition,[status(thm)],[c_1,c_1574]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_3642,plain,
% 7.82/1.49      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,k5_xboole_0(sK3,X0))) = sK3 ),
% 7.82/1.49      inference(superposition,[status(thm)],[c_1664,c_2023]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_4726,plain,
% 7.82/1.49      ( k5_xboole_0(k5_xboole_0(sK3,X0),k5_xboole_0(k5_xboole_0(X1,X0),k5_xboole_0(sK3,k5_xboole_0(sK3,X1)))) = sK3 ),
% 7.82/1.49      inference(superposition,[status(thm)],[c_2150,c_3642]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_4805,plain,
% 7.82/1.49      ( k5_xboole_0(k5_xboole_0(sK3,X0),k5_xboole_0(k5_xboole_0(X1,X0),X1)) = sK3 ),
% 7.82/1.49      inference(demodulation,[status(thm)],[c_4726,c_1566]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_4977,plain,
% 7.82/1.49      ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,X1),X0)) = k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(sK3,X1)),sK3) ),
% 7.82/1.49      inference(superposition,[status(thm)],[c_4805,c_2150]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_5002,plain,
% 7.82/1.49      ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,X1),X0)) = k5_xboole_0(X1,sK3) ),
% 7.82/1.49      inference(demodulation,[status(thm)],[c_4977,c_1566]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_5342,plain,
% 7.82/1.49      ( k5_xboole_0(k5_xboole_0(X0,X1),X0) = k5_xboole_0(sK3,k5_xboole_0(X1,sK3)) ),
% 7.82/1.49      inference(superposition,[status(thm)],[c_5002,c_1566]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_5353,plain,
% 7.82/1.49      ( k5_xboole_0(k5_xboole_0(X0,X1),X0) = X1 ),
% 7.82/1.49      inference(demodulation,[status(thm)],[c_5342,c_1568]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_7284,plain,
% 7.82/1.49      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(sK3,X1)) = k5_xboole_0(X0,sK3) ),
% 7.82/1.49      inference(superposition,[status(thm)],[c_6949,c_5353]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_7805,plain,
% 7.82/1.49      ( k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(X0,X1)),k5_xboole_0(X0,sK3)) = k5_xboole_0(sK3,k5_xboole_0(sK3,X1)) ),
% 7.82/1.49      inference(superposition,[status(thm)],[c_7284,c_2150]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_7864,plain,
% 7.82/1.49      ( k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(X0,X1)),k5_xboole_0(X0,sK3)) = X1 ),
% 7.82/1.49      inference(demodulation,[status(thm)],[c_7805,c_1566,c_6949]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_8748,plain,
% 7.82/1.49      ( k5_xboole_0(k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,X0)),k5_xboole_0(X0,sK3)) = k3_xboole_0(X0,sK3) ),
% 7.82/1.49      inference(superposition,[status(thm)],[c_1262,c_7864]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_14917,plain,
% 7.82/1.49      ( k5_xboole_0(k3_xboole_0(sK3,X0),sK3) = k5_xboole_0(sK3,k3_xboole_0(X0,sK3)) ),
% 7.82/1.49      inference(light_normalisation,[status(thm)],[c_14688,c_8748]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_14926,plain,
% 7.82/1.49      ( k5_xboole_0(sK3,k5_xboole_0(k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) = k5_xboole_0(sK3,k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) ),
% 7.82/1.49      inference(demodulation,[status(thm)],[c_14681,c_14917]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_1265,plain,
% 7.82/1.49      ( k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = k1_xboole_0 ),
% 7.82/1.49      inference(superposition,[status(thm)],[c_666,c_1175]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_14927,plain,
% 7.82/1.49      ( k5_xboole_0(sK3,k5_xboole_0(k1_xboole_0,k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) = k5_xboole_0(sK3,k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) ),
% 7.82/1.49      inference(light_normalisation,[status(thm)],[c_14926,c_1265]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_5434,plain,
% 7.82/1.49      ( k5_xboole_0(k5_xboole_0(X0,X1),X1) = X0 ),
% 7.82/1.49      inference(superposition,[status(thm)],[c_1,c_5353]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_1557,plain,
% 7.82/1.49      ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X0))) = X0 ),
% 7.82/1.49      inference(superposition,[status(thm)],[c_11,c_1390]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_1604,plain,
% 7.82/1.49      ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(X0,k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))) = X0 ),
% 7.82/1.49      inference(superposition,[status(thm)],[c_1,c_1557]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_2340,plain,
% 7.82/1.49      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(X0,k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) = k5_xboole_0(sK3,X0) ),
% 7.82/1.49      inference(superposition,[status(thm)],[c_1604,c_1566]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_5633,plain,
% 7.82/1.49      ( k5_xboole_0(sK3,k5_xboole_0(X0,k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),X0) ),
% 7.82/1.49      inference(superposition,[status(thm)],[c_5434,c_2340]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_14928,plain,
% 7.82/1.49      ( k5_xboole_0(sK3,k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
% 7.82/1.49      inference(demodulation,[status(thm)],[c_14927,c_10,c_5633]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_5478,plain,
% 7.82/1.49      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
% 7.82/1.49      inference(superposition,[status(thm)],[c_5353,c_11]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_15063,plain,
% 7.82/1.49      ( k5_xboole_0(k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = sK3 ),
% 7.82/1.49      inference(superposition,[status(thm)],[c_14928,c_5478]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_8,plain,
% 7.82/1.49      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
% 7.82/1.49      inference(cnf_transformation,[],[f77]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_965,plain,
% 7.82/1.49      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
% 7.82/1.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_2956,plain,
% 7.82/1.49      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X0) = iProver_top ),
% 7.82/1.49      inference(superposition,[status(thm)],[c_0,c_965]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_15070,plain,
% 7.82/1.49      ( r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) = iProver_top ),
% 7.82/1.49      inference(superposition,[status(thm)],[c_14928,c_2956]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_6,plain,
% 7.82/1.49      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 7.82/1.49      inference(cnf_transformation,[],[f48]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_966,plain,
% 7.82/1.49      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 7.82/1.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_15306,plain,
% 7.82/1.49      ( k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
% 7.82/1.49      inference(superposition,[status(thm)],[c_15070,c_966]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_15307,plain,
% 7.82/1.49      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = sK3 ),
% 7.82/1.49      inference(light_normalisation,
% 7.82/1.49                [status(thm)],
% 7.82/1.49                [c_15063,c_15063,c_15306]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_15308,plain,
% 7.82/1.49      ( sK3 = k1_xboole_0 ),
% 7.82/1.49      inference(demodulation,[status(thm)],[c_15307,c_12]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_15353,plain,
% 7.82/1.49      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = k1_xboole_0 ),
% 7.82/1.49      inference(demodulation,[status(thm)],[c_15308,c_1562]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_7,plain,
% 7.82/1.49      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 7.82/1.49      inference(cnf_transformation,[],[f49]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_1176,plain,
% 7.82/1.49      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.82/1.49      inference(superposition,[status(thm)],[c_7,c_0]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_15365,plain,
% 7.82/1.49      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k1_xboole_0 ),
% 7.82/1.49      inference(demodulation,[status(thm)],[c_15353,c_10,c_1176]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_18328,plain,
% 7.82/1.49      ( k5_xboole_0(sK2,k5_xboole_0(sK2,k3_xboole_0(sK2,sK2))) = k3_tarski(k1_xboole_0) ),
% 7.82/1.49      inference(superposition,[status(thm)],[c_15365,c_1262]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_19,plain,
% 7.82/1.49      ( k3_tarski(k1_xboole_0) = k1_xboole_0 ),
% 7.82/1.49      inference(cnf_transformation,[],[f69]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_18330,plain,
% 7.82/1.49      ( k5_xboole_0(sK2,k5_xboole_0(sK2,k3_xboole_0(sK2,sK2))) = k1_xboole_0 ),
% 7.82/1.49      inference(light_normalisation,[status(thm)],[c_18328,c_19]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_1382,plain,
% 7.82/1.49      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 7.82/1.49      inference(superposition,[status(thm)],[c_12,c_11]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_1391,plain,
% 7.82/1.49      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
% 7.82/1.49      inference(demodulation,[status(thm)],[c_1382,c_1268]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_2958,plain,
% 7.82/1.49      ( r1_tarski(k5_xboole_0(X0,k1_xboole_0),X0) = iProver_top ),
% 7.82/1.49      inference(superposition,[status(thm)],[c_7,c_965]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_2961,plain,
% 7.82/1.49      ( r1_tarski(X0,X0) = iProver_top ),
% 7.82/1.49      inference(light_normalisation,[status(thm)],[c_2958,c_10]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_5573,plain,
% 7.82/1.49      ( k3_xboole_0(X0,X0) = X0 ),
% 7.82/1.49      inference(superposition,[status(thm)],[c_2961,c_966]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_18331,plain,
% 7.82/1.49      ( sK2 = k1_xboole_0 ),
% 7.82/1.49      inference(demodulation,
% 7.82/1.49                [status(thm)],
% 7.82/1.49                [c_18330,c_10,c_12,c_1391,c_5573]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_18332,plain,
% 7.82/1.49      ( k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 7.82/1.49      inference(demodulation,[status(thm)],[c_18331,c_15365]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_2,plain,
% 7.82/1.49      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2)) | ~ r1_xboole_0(X1,X2) ),
% 7.82/1.49      inference(cnf_transformation,[],[f44]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_4,plain,
% 7.82/1.49      ( r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
% 7.82/1.49      inference(cnf_transformation,[],[f45]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_199,plain,
% 7.82/1.49      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
% 7.82/1.49      | k5_xboole_0(X3,X4) != X2
% 7.82/1.49      | k3_xboole_0(X3,X4) != X1 ),
% 7.82/1.49      inference(resolution_lifted,[status(thm)],[c_2,c_4]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_200,plain,
% 7.82/1.49      ( ~ r2_hidden(X0,k3_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2))) ),
% 7.82/1.49      inference(unflattening,[status(thm)],[c_199]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_958,plain,
% 7.82/1.49      ( r2_hidden(X0,k3_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2))) != iProver_top ),
% 7.82/1.49      inference(predicate_to_equality,[status(thm)],[c_200]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_1789,plain,
% 7.82/1.49      ( r2_hidden(X0,k3_xboole_0(k3_xboole_0(k1_xboole_0,X1),X1)) != iProver_top ),
% 7.82/1.49      inference(superposition,[status(thm)],[c_1268,c_958]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_1795,plain,
% 7.82/1.49      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.82/1.49      inference(demodulation,[status(thm)],[c_1789,c_1176]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_1823,plain,
% 7.82/1.49      ( r2_hidden(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 7.82/1.49      inference(instantiation,[status(thm)],[c_1795]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_669,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_1373,plain,
% 7.82/1.49      ( X0 != X1
% 7.82/1.49      | X0 = k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
% 7.82/1.49      | k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != X1 ),
% 7.82/1.49      inference(instantiation,[status(thm)],[c_669]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_1374,plain,
% 7.82/1.49      ( k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 7.82/1.49      | k1_xboole_0 = k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
% 7.82/1.49      | k1_xboole_0 != k1_xboole_0 ),
% 7.82/1.49      inference(instantiation,[status(thm)],[c_1373]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_672,plain,
% 7.82/1.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.82/1.49      theory(equality) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_1218,plain,
% 7.82/1.49      ( r2_hidden(X0,X1)
% 7.82/1.49      | ~ r2_hidden(X2,k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
% 7.82/1.49      | X0 != X2
% 7.82/1.49      | X1 != k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
% 7.82/1.49      inference(instantiation,[status(thm)],[c_672]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_1224,plain,
% 7.82/1.49      ( X0 != X1
% 7.82/1.49      | X2 != k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
% 7.82/1.49      | r2_hidden(X0,X2) = iProver_top
% 7.82/1.49      | r2_hidden(X1,k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) != iProver_top ),
% 7.82/1.49      inference(predicate_to_equality,[status(thm)],[c_1218]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_1226,plain,
% 7.82/1.49      ( k1_xboole_0 != k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
% 7.82/1.49      | k1_xboole_0 != k1_xboole_0
% 7.82/1.49      | r2_hidden(k1_xboole_0,k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) != iProver_top
% 7.82/1.49      | r2_hidden(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 7.82/1.49      inference(instantiation,[status(thm)],[c_1224]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_1012,plain,
% 7.82/1.49      ( r2_hidden(X0,X1)
% 7.82/1.49      | ~ r2_hidden(X2,k1_zfmisc_1(X3))
% 7.82/1.49      | X0 != X2
% 7.82/1.49      | X1 != k1_zfmisc_1(X3) ),
% 7.82/1.49      inference(instantiation,[status(thm)],[c_672]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_1134,plain,
% 7.82/1.49      ( r2_hidden(X0,X1)
% 7.82/1.49      | ~ r2_hidden(k3_xboole_0(X2,X3),k1_zfmisc_1(X2))
% 7.82/1.49      | X0 != k3_xboole_0(X2,X3)
% 7.82/1.49      | X1 != k1_zfmisc_1(X2) ),
% 7.82/1.49      inference(instantiation,[status(thm)],[c_1012]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_1200,plain,
% 7.82/1.49      ( r2_hidden(X0,k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
% 7.82/1.49      | ~ r2_hidden(k3_xboole_0(k1_xboole_0,X1),k1_zfmisc_1(k1_xboole_0))
% 7.82/1.49      | X0 != k3_xboole_0(k1_xboole_0,X1)
% 7.82/1.49      | k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_zfmisc_1(k1_xboole_0) ),
% 7.82/1.49      inference(instantiation,[status(thm)],[c_1134]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_1201,plain,
% 7.82/1.49      ( X0 != k3_xboole_0(k1_xboole_0,X1)
% 7.82/1.49      | k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_zfmisc_1(k1_xboole_0)
% 7.82/1.49      | r2_hidden(X0,k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) = iProver_top
% 7.82/1.49      | r2_hidden(k3_xboole_0(k1_xboole_0,X1),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.82/1.49      inference(predicate_to_equality,[status(thm)],[c_1200]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_1203,plain,
% 7.82/1.49      ( k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_zfmisc_1(k1_xboole_0)
% 7.82/1.49      | k1_xboole_0 != k3_xboole_0(k1_xboole_0,k1_xboole_0)
% 7.82/1.49      | r2_hidden(k3_xboole_0(k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 7.82/1.49      | r2_hidden(k1_xboole_0,k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 7.82/1.49      inference(instantiation,[status(thm)],[c_1201]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_668,plain,( X0 = X0 ),theory(equality) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_683,plain,
% 7.82/1.49      ( k1_xboole_0 = k1_xboole_0 ),
% 7.82/1.49      inference(instantiation,[status(thm)],[c_668]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_5,plain,
% 7.82/1.49      ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
% 7.82/1.49      inference(cnf_transformation,[],[f47]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_9,plain,
% 7.82/1.49      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 7.82/1.49      inference(cnf_transformation,[],[f51]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_239,plain,
% 7.82/1.49      ( k3_xboole_0(X0,X1) != X2 | k1_xboole_0 != X0 | k1_xboole_0 = X2 ),
% 7.82/1.49      inference(resolution_lifted,[status(thm)],[c_5,c_9]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_240,plain,
% 7.82/1.49      ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
% 7.82/1.49      inference(unflattening,[status(thm)],[c_239]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_241,plain,
% 7.82/1.49      ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 7.82/1.49      inference(instantiation,[status(thm)],[c_240]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_15,plain,
% 7.82/1.49      ( ~ r1_tarski(X0,X1) | r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 7.82/1.49      inference(cnf_transformation,[],[f81]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_110,plain,
% 7.82/1.49      ( ~ r1_tarski(X0,X1) | r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 7.82/1.49      inference(prop_impl,[status(thm)],[c_15]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_224,plain,
% 7.82/1.49      ( r2_hidden(X0,k1_zfmisc_1(X1))
% 7.82/1.49      | X1 != X2
% 7.82/1.49      | k3_xboole_0(X2,X3) != X0 ),
% 7.82/1.49      inference(resolution_lifted,[status(thm)],[c_5,c_110]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_225,plain,
% 7.82/1.49      ( r2_hidden(k3_xboole_0(X0,X1),k1_zfmisc_1(X0)) ),
% 7.82/1.49      inference(unflattening,[status(thm)],[c_224]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_226,plain,
% 7.82/1.49      ( r2_hidden(k3_xboole_0(X0,X1),k1_zfmisc_1(X0)) = iProver_top ),
% 7.82/1.49      inference(predicate_to_equality,[status(thm)],[c_225]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_228,plain,
% 7.82/1.49      ( r2_hidden(k3_xboole_0(k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 7.82/1.49      inference(instantiation,[status(thm)],[c_226]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_18,plain,
% 7.82/1.49      ( k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_zfmisc_1(k1_xboole_0) ),
% 7.82/1.49      inference(cnf_transformation,[],[f79]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(contradiction,plain,
% 7.82/1.49      ( $false ),
% 7.82/1.49      inference(minisat,
% 7.82/1.49                [status(thm)],
% 7.82/1.49                [c_18332,c_1823,c_1374,c_1226,c_1203,c_683,c_241,c_228,
% 7.82/1.49                 c_18]) ).
% 7.82/1.49  
% 7.82/1.49  
% 7.82/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.82/1.49  
% 7.82/1.49  ------                               Statistics
% 7.82/1.49  
% 7.82/1.49  ------ General
% 7.82/1.49  
% 7.82/1.49  abstr_ref_over_cycles:                  0
% 7.82/1.49  abstr_ref_under_cycles:                 0
% 7.82/1.49  gc_basic_clause_elim:                   0
% 7.82/1.49  forced_gc_time:                         0
% 7.82/1.49  parsing_time:                           0.008
% 7.82/1.49  unif_index_cands_time:                  0.
% 7.82/1.49  unif_index_add_time:                    0.
% 7.82/1.49  orderings_time:                         0.
% 7.82/1.49  out_proof_time:                         0.009
% 7.82/1.49  total_time:                             0.734
% 7.82/1.49  num_of_symbols:                         44
% 7.82/1.49  num_of_terms:                           32496
% 7.82/1.49  
% 7.82/1.49  ------ Preprocessing
% 7.82/1.49  
% 7.82/1.49  num_of_splits:                          0
% 7.82/1.49  num_of_split_atoms:                     0
% 7.82/1.49  num_of_reused_defs:                     0
% 7.82/1.49  num_eq_ax_congr_red:                    12
% 7.82/1.49  num_of_sem_filtered_clauses:            1
% 7.82/1.49  num_of_subtypes:                        0
% 7.82/1.49  monotx_restored_types:                  0
% 7.82/1.49  sat_num_of_epr_types:                   0
% 7.82/1.49  sat_num_of_non_cyclic_types:            0
% 7.82/1.49  sat_guarded_non_collapsed_types:        0
% 7.82/1.49  num_pure_diseq_elim:                    0
% 7.82/1.49  simp_replaced_by:                       0
% 7.82/1.49  res_preprocessed:                       100
% 7.82/1.49  prep_upred:                             0
% 7.82/1.49  prep_unflattend:                        52
% 7.82/1.49  smt_new_axioms:                         0
% 7.82/1.49  pred_elim_cands:                        2
% 7.82/1.49  pred_elim:                              1
% 7.82/1.49  pred_elim_cl:                           1
% 7.82/1.49  pred_elim_cycles:                       3
% 7.82/1.49  merged_defs:                            8
% 7.82/1.49  merged_defs_ncl:                        0
% 7.82/1.49  bin_hyper_res:                          8
% 7.82/1.49  prep_cycles:                            4
% 7.82/1.49  pred_elim_time:                         0.005
% 7.82/1.49  splitting_time:                         0.
% 7.82/1.49  sem_filter_time:                        0.
% 7.82/1.49  monotx_time:                            0.
% 7.82/1.49  subtype_inf_time:                       0.
% 7.82/1.49  
% 7.82/1.49  ------ Problem properties
% 7.82/1.49  
% 7.82/1.49  clauses:                                20
% 7.82/1.49  conjectures:                            1
% 7.82/1.49  epr:                                    1
% 7.82/1.49  horn:                                   19
% 7.82/1.49  ground:                                 3
% 7.82/1.49  unary:                                  13
% 7.82/1.49  binary:                                 5
% 7.82/1.49  lits:                                   29
% 7.82/1.49  lits_eq:                                14
% 7.82/1.49  fd_pure:                                0
% 7.82/1.49  fd_pseudo:                              0
% 7.82/1.49  fd_cond:                                1
% 7.82/1.49  fd_pseudo_cond:                         2
% 7.82/1.49  ac_symbols:                             1
% 7.82/1.49  
% 7.82/1.49  ------ Propositional Solver
% 7.82/1.49  
% 7.82/1.49  prop_solver_calls:                      34
% 7.82/1.49  prop_fast_solver_calls:                 646
% 7.82/1.49  smt_solver_calls:                       0
% 7.82/1.49  smt_fast_solver_calls:                  0
% 7.82/1.49  prop_num_of_clauses:                    5912
% 7.82/1.49  prop_preprocess_simplified:             8316
% 7.82/1.49  prop_fo_subsumed:                       0
% 7.82/1.49  prop_solver_time:                       0.
% 7.82/1.49  smt_solver_time:                        0.
% 7.82/1.49  smt_fast_solver_time:                   0.
% 7.82/1.49  prop_fast_solver_time:                  0.
% 7.82/1.49  prop_unsat_core_time:                   0.
% 7.82/1.49  
% 7.82/1.49  ------ QBF
% 7.82/1.49  
% 7.82/1.49  qbf_q_res:                              0
% 7.82/1.49  qbf_num_tautologies:                    0
% 7.82/1.49  qbf_prep_cycles:                        0
% 7.82/1.49  
% 7.82/1.49  ------ BMC1
% 7.82/1.49  
% 7.82/1.49  bmc1_current_bound:                     -1
% 7.82/1.49  bmc1_last_solved_bound:                 -1
% 7.82/1.49  bmc1_unsat_core_size:                   -1
% 7.82/1.49  bmc1_unsat_core_parents_size:           -1
% 7.82/1.49  bmc1_merge_next_fun:                    0
% 7.82/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.82/1.49  
% 7.82/1.49  ------ Instantiation
% 7.82/1.49  
% 7.82/1.49  inst_num_of_clauses:                    1122
% 7.82/1.49  inst_num_in_passive:                    142
% 7.82/1.49  inst_num_in_active:                     461
% 7.82/1.49  inst_num_in_unprocessed:                519
% 7.82/1.49  inst_num_of_loops:                      550
% 7.82/1.49  inst_num_of_learning_restarts:          0
% 7.82/1.49  inst_num_moves_active_passive:          82
% 7.82/1.49  inst_lit_activity:                      0
% 7.82/1.49  inst_lit_activity_moves:                0
% 7.82/1.49  inst_num_tautologies:                   0
% 7.82/1.49  inst_num_prop_implied:                  0
% 7.82/1.49  inst_num_existing_simplified:           0
% 7.82/1.49  inst_num_eq_res_simplified:             0
% 7.82/1.49  inst_num_child_elim:                    0
% 7.82/1.49  inst_num_of_dismatching_blockings:      365
% 7.82/1.49  inst_num_of_non_proper_insts:           1272
% 7.82/1.49  inst_num_of_duplicates:                 0
% 7.82/1.49  inst_inst_num_from_inst_to_res:         0
% 7.82/1.49  inst_dismatching_checking_time:         0.
% 7.82/1.49  
% 7.82/1.49  ------ Resolution
% 7.82/1.49  
% 7.82/1.49  res_num_of_clauses:                     0
% 7.82/1.49  res_num_in_passive:                     0
% 7.82/1.49  res_num_in_active:                      0
% 7.82/1.49  res_num_of_loops:                       104
% 7.82/1.49  res_forward_subset_subsumed:            42
% 7.82/1.49  res_backward_subset_subsumed:           0
% 7.82/1.49  res_forward_subsumed:                   0
% 7.82/1.49  res_backward_subsumed:                  0
% 7.82/1.49  res_forward_subsumption_resolution:     0
% 7.82/1.49  res_backward_subsumption_resolution:    0
% 7.82/1.49  res_clause_to_clause_subsumption:       18382
% 7.82/1.49  res_orphan_elimination:                 0
% 7.82/1.49  res_tautology_del:                      108
% 7.82/1.49  res_num_eq_res_simplified:              0
% 7.82/1.49  res_num_sel_changes:                    0
% 7.82/1.49  res_moves_from_active_to_pass:          0
% 7.82/1.49  
% 7.82/1.49  ------ Superposition
% 7.82/1.49  
% 7.82/1.49  sup_time_total:                         0.
% 7.82/1.49  sup_time_generating:                    0.
% 7.82/1.49  sup_time_sim_full:                      0.
% 7.82/1.49  sup_time_sim_immed:                     0.
% 7.82/1.49  
% 7.82/1.49  sup_num_of_clauses:                     1527
% 7.82/1.49  sup_num_in_active:                      43
% 7.82/1.49  sup_num_in_passive:                     1484
% 7.82/1.49  sup_num_of_loops:                       108
% 7.82/1.49  sup_fw_superposition:                   4007
% 7.82/1.49  sup_bw_superposition:                   2903
% 7.82/1.49  sup_immediate_simplified:               2694
% 7.82/1.49  sup_given_eliminated:                   5
% 7.82/1.49  comparisons_done:                       0
% 7.82/1.49  comparisons_avoided:                    0
% 7.82/1.49  
% 7.82/1.49  ------ Simplifications
% 7.82/1.49  
% 7.82/1.49  
% 7.82/1.49  sim_fw_subset_subsumed:                 2
% 7.82/1.49  sim_bw_subset_subsumed:                 0
% 7.82/1.49  sim_fw_subsumed:                        208
% 7.82/1.49  sim_bw_subsumed:                        8
% 7.82/1.49  sim_fw_subsumption_res:                 0
% 7.82/1.49  sim_bw_subsumption_res:                 0
% 7.82/1.49  sim_tautology_del:                      0
% 7.82/1.49  sim_eq_tautology_del:                   849
% 7.82/1.49  sim_eq_res_simp:                        0
% 7.82/1.49  sim_fw_demodulated:                     1949
% 7.82/1.49  sim_bw_demodulated:                     88
% 7.82/1.49  sim_light_normalised:                   1090
% 7.82/1.49  sim_joinable_taut:                      209
% 7.82/1.49  sim_joinable_simp:                      0
% 7.82/1.49  sim_ac_normalised:                      0
% 7.82/1.49  sim_smt_subsumption:                    0
% 7.82/1.49  
%------------------------------------------------------------------------------
