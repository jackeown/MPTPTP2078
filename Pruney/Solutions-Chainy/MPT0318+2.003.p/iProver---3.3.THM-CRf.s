%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:37:24 EST 2020

% Result     : Theorem 1.80s
% Output     : CNFRefutation 1.80s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 331 expanded)
%              Number of clauses        :   43 (  84 expanded)
%              Number of leaves         :   22 (  86 expanded)
%              Depth                    :   19
%              Number of atoms          :  239 ( 759 expanded)
%              Number of equality atoms :  150 ( 668 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
     => ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
        & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 != X0
       => ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
          & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,k1_tarski(X1))
        | k1_xboole_0 = k2_zfmisc_1(k1_tarski(X1),X0) )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f20])).

fof(f33,plain,
    ( ? [X0,X1] :
        ( ( k1_xboole_0 = k2_zfmisc_1(X0,k1_tarski(X1))
          | k1_xboole_0 = k2_zfmisc_1(k1_tarski(X1),X0) )
        & k1_xboole_0 != X0 )
   => ( ( k1_xboole_0 = k2_zfmisc_1(sK2,k1_tarski(sK3))
        | k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK3),sK2) )
      & k1_xboole_0 != sK2 ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ( k1_xboole_0 = k2_zfmisc_1(sK2,k1_tarski(sK3))
      | k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK3),sK2) )
    & k1_xboole_0 != sK2 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f23,f33])).

fof(f61,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK2,k1_tarski(sK3))
    | k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK3),sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f12])).

fof(f62,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f47,f48])).

fof(f63,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f46,f62])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f45,f63])).

fof(f65,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f44,f64])).

fof(f66,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f43,f65])).

fof(f67,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f42,f66])).

fof(f70,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK2,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))
    | k1_xboole_0 = k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK2) ),
    inference(definition_unfolding,[],[f61,f67,f67])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f31])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f60,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f34])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f74,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f54])).

fof(f17,axiom,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f69,plain,(
    ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f58,f67])).

fof(f16,axiom,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f16])).

fof(f15,axiom,(
    k1_tarski(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    k1_tarski(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f15])).

fof(f68,plain,(
    k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_zfmisc_1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f56,f67])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f29,plain,(
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

fof(f30,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f28,f29])).

fof(f50,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f71,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f50])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f25])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

cnf(c_413,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1421,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k3_xboole_0(X3,X4))
    | X2 != X0
    | k3_xboole_0(X3,X4) != X1 ),
    inference(instantiation,[status(thm)],[c_413])).

cnf(c_1423,plain,
    ( r2_hidden(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0))
    | ~ r2_hidden(k1_xboole_0,k1_xboole_0)
    | k3_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1421])).

cnf(c_18,negated_conjecture,
    ( k1_xboole_0 = k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK2)
    | k1_xboole_0 = k2_zfmisc_1(sK2,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_13,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1108,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k1_xboole_0
    | k2_zfmisc_1(sK2,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_18,c_13])).

cnf(c_19,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_22,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_12,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_23,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_411,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_819,plain,
    ( sK2 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_411])).

cnf(c_820,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_819])).

cnf(c_1115,plain,
    ( k2_zfmisc_1(sK2,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = k1_xboole_0
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1108,c_19,c_22,c_23,c_820])).

cnf(c_1116,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k1_xboole_0
    | k2_zfmisc_1(sK2,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_1115])).

cnf(c_1119,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1116,c_13])).

cnf(c_1162,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1119,c_19,c_22,c_23,c_820])).

cnf(c_16,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1167,plain,
    ( k3_tarski(k1_xboole_0) = sK3 ),
    inference(superposition,[status(thm)],[c_1162,c_16])).

cnf(c_15,plain,
    ( k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1168,plain,
    ( sK3 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1167,c_15])).

cnf(c_1170,plain,
    ( k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1168,c_1162])).

cnf(c_14,plain,
    ( k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_zfmisc_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1237,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1170,c_14])).

cnf(c_951,plain,
    ( X0 != X1
    | X0 = k1_zfmisc_1(X2)
    | k1_zfmisc_1(X2) != X1 ),
    inference(instantiation,[status(thm)],[c_411])).

cnf(c_952,plain,
    ( k1_zfmisc_1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_zfmisc_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_951])).

cnf(c_873,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k3_xboole_0(X2,X3),k1_zfmisc_1(X2))
    | X0 != k3_xboole_0(X2,X3)
    | X1 != k1_zfmisc_1(X2) ),
    inference(instantiation,[status(thm)],[c_413])).

cnf(c_875,plain,
    ( ~ r2_hidden(k3_xboole_0(k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | r2_hidden(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != k3_xboole_0(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != k1_zfmisc_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_873])).

cnf(c_867,plain,
    ( X0 != X1
    | X0 = k3_xboole_0(X2,X3)
    | k3_xboole_0(X2,X3) != X1 ),
    inference(instantiation,[status(thm)],[c_411])).

cnf(c_868,plain,
    ( k3_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_867])).

cnf(c_5,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_99,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_9])).

cnf(c_230,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1))
    | X1 != X2
    | k3_xboole_0(X2,X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_99])).

cnf(c_231,plain,
    ( r2_hidden(k3_xboole_0(X0,X1),k1_zfmisc_1(X0)) ),
    inference(unflattening,[status(thm)],[c_230])).

cnf(c_233,plain,
    ( r2_hidden(k3_xboole_0(k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_231])).

cnf(c_1,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_48,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | k3_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_44,plain,
    ( ~ r2_hidden(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0))
    | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_6,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_36,plain,
    ( k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1423,c_1237,c_952,c_875,c_868,c_233,c_48,c_44,c_36,c_23,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.08  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.09  % Command    : iproveropt_run.sh %d %s
% 0.08/0.28  % Computer   : n003.cluster.edu
% 0.08/0.28  % Model      : x86_64 x86_64
% 0.08/0.28  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.08/0.28  % Memory     : 8042.1875MB
% 0.08/0.28  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.08/0.28  % CPULimit   : 60
% 0.08/0.28  % WCLimit    : 600
% 0.08/0.28  % DateTime   : Tue Dec  1 17:23:57 EST 2020
% 0.08/0.28  % CPUTime    : 
% 0.08/0.28  % Running in FOF mode
% 1.80/0.87  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.80/0.87  
% 1.80/0.87  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.80/0.87  
% 1.80/0.87  ------  iProver source info
% 1.80/0.87  
% 1.80/0.87  git: date: 2020-06-30 10:37:57 +0100
% 1.80/0.87  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.80/0.87  git: non_committed_changes: false
% 1.80/0.87  git: last_make_outside_of_git: false
% 1.80/0.87  
% 1.80/0.87  ------ 
% 1.80/0.87  
% 1.80/0.87  ------ Input Options
% 1.80/0.87  
% 1.80/0.87  --out_options                           all
% 1.80/0.87  --tptp_safe_out                         true
% 1.80/0.87  --problem_path                          ""
% 1.80/0.87  --include_path                          ""
% 1.80/0.87  --clausifier                            res/vclausify_rel
% 1.80/0.87  --clausifier_options                    --mode clausify
% 1.80/0.87  --stdin                                 false
% 1.80/0.87  --stats_out                             all
% 1.80/0.87  
% 1.80/0.87  ------ General Options
% 1.80/0.87  
% 1.80/0.87  --fof                                   false
% 1.80/0.87  --time_out_real                         305.
% 1.80/0.87  --time_out_virtual                      -1.
% 1.80/0.87  --symbol_type_check                     false
% 1.80/0.87  --clausify_out                          false
% 1.80/0.87  --sig_cnt_out                           false
% 1.80/0.87  --trig_cnt_out                          false
% 1.80/0.87  --trig_cnt_out_tolerance                1.
% 1.80/0.87  --trig_cnt_out_sk_spl                   false
% 1.80/0.87  --abstr_cl_out                          false
% 1.80/0.87  
% 1.80/0.87  ------ Global Options
% 1.80/0.87  
% 1.80/0.87  --schedule                              default
% 1.80/0.87  --add_important_lit                     false
% 1.80/0.87  --prop_solver_per_cl                    1000
% 1.80/0.87  --min_unsat_core                        false
% 1.80/0.87  --soft_assumptions                      false
% 1.80/0.87  --soft_lemma_size                       3
% 1.80/0.87  --prop_impl_unit_size                   0
% 1.80/0.87  --prop_impl_unit                        []
% 1.80/0.87  --share_sel_clauses                     true
% 1.80/0.87  --reset_solvers                         false
% 1.80/0.87  --bc_imp_inh                            [conj_cone]
% 1.80/0.87  --conj_cone_tolerance                   3.
% 1.80/0.87  --extra_neg_conj                        none
% 1.80/0.87  --large_theory_mode                     true
% 1.80/0.87  --prolific_symb_bound                   200
% 1.80/0.87  --lt_threshold                          2000
% 1.80/0.87  --clause_weak_htbl                      true
% 1.80/0.87  --gc_record_bc_elim                     false
% 1.80/0.87  
% 1.80/0.87  ------ Preprocessing Options
% 1.80/0.87  
% 1.80/0.87  --preprocessing_flag                    true
% 1.80/0.87  --time_out_prep_mult                    0.1
% 1.80/0.87  --splitting_mode                        input
% 1.80/0.87  --splitting_grd                         true
% 1.80/0.87  --splitting_cvd                         false
% 1.80/0.87  --splitting_cvd_svl                     false
% 1.80/0.87  --splitting_nvd                         32
% 1.80/0.87  --sub_typing                            true
% 1.80/0.87  --prep_gs_sim                           true
% 1.80/0.87  --prep_unflatten                        true
% 1.80/0.87  --prep_res_sim                          true
% 1.80/0.87  --prep_upred                            true
% 1.80/0.87  --prep_sem_filter                       exhaustive
% 1.80/0.87  --prep_sem_filter_out                   false
% 1.80/0.87  --pred_elim                             true
% 1.80/0.87  --res_sim_input                         true
% 1.80/0.87  --eq_ax_congr_red                       true
% 1.80/0.87  --pure_diseq_elim                       true
% 1.80/0.87  --brand_transform                       false
% 1.80/0.87  --non_eq_to_eq                          false
% 1.80/0.87  --prep_def_merge                        true
% 1.80/0.87  --prep_def_merge_prop_impl              false
% 1.80/0.87  --prep_def_merge_mbd                    true
% 1.80/0.87  --prep_def_merge_tr_red                 false
% 1.80/0.87  --prep_def_merge_tr_cl                  false
% 1.80/0.87  --smt_preprocessing                     true
% 1.80/0.87  --smt_ac_axioms                         fast
% 1.80/0.87  --preprocessed_out                      false
% 1.80/0.87  --preprocessed_stats                    false
% 1.80/0.87  
% 1.80/0.87  ------ Abstraction refinement Options
% 1.80/0.87  
% 1.80/0.87  --abstr_ref                             []
% 1.80/0.87  --abstr_ref_prep                        false
% 1.80/0.87  --abstr_ref_until_sat                   false
% 1.80/0.87  --abstr_ref_sig_restrict                funpre
% 1.80/0.87  --abstr_ref_af_restrict_to_split_sk     false
% 1.80/0.87  --abstr_ref_under                       []
% 1.80/0.87  
% 1.80/0.87  ------ SAT Options
% 1.80/0.87  
% 1.80/0.87  --sat_mode                              false
% 1.80/0.87  --sat_fm_restart_options                ""
% 1.80/0.87  --sat_gr_def                            false
% 1.80/0.87  --sat_epr_types                         true
% 1.80/0.87  --sat_non_cyclic_types                  false
% 1.80/0.87  --sat_finite_models                     false
% 1.80/0.87  --sat_fm_lemmas                         false
% 1.80/0.87  --sat_fm_prep                           false
% 1.80/0.87  --sat_fm_uc_incr                        true
% 1.80/0.87  --sat_out_model                         small
% 1.80/0.87  --sat_out_clauses                       false
% 1.80/0.87  
% 1.80/0.87  ------ QBF Options
% 1.80/0.87  
% 1.80/0.87  --qbf_mode                              false
% 1.80/0.87  --qbf_elim_univ                         false
% 1.80/0.87  --qbf_dom_inst                          none
% 1.80/0.87  --qbf_dom_pre_inst                      false
% 1.80/0.87  --qbf_sk_in                             false
% 1.80/0.87  --qbf_pred_elim                         true
% 1.80/0.87  --qbf_split                             512
% 1.80/0.87  
% 1.80/0.87  ------ BMC1 Options
% 1.80/0.87  
% 1.80/0.87  --bmc1_incremental                      false
% 1.80/0.87  --bmc1_axioms                           reachable_all
% 1.80/0.87  --bmc1_min_bound                        0
% 1.80/0.87  --bmc1_max_bound                        -1
% 1.80/0.87  --bmc1_max_bound_default                -1
% 1.80/0.87  --bmc1_symbol_reachability              true
% 1.80/0.87  --bmc1_property_lemmas                  false
% 1.80/0.87  --bmc1_k_induction                      false
% 1.80/0.87  --bmc1_non_equiv_states                 false
% 1.80/0.87  --bmc1_deadlock                         false
% 1.80/0.87  --bmc1_ucm                              false
% 1.80/0.87  --bmc1_add_unsat_core                   none
% 1.80/0.87  --bmc1_unsat_core_children              false
% 1.80/0.87  --bmc1_unsat_core_extrapolate_axioms    false
% 1.80/0.87  --bmc1_out_stat                         full
% 1.80/0.87  --bmc1_ground_init                      false
% 1.80/0.87  --bmc1_pre_inst_next_state              false
% 1.80/0.87  --bmc1_pre_inst_state                   false
% 1.80/0.87  --bmc1_pre_inst_reach_state             false
% 1.80/0.87  --bmc1_out_unsat_core                   false
% 1.80/0.87  --bmc1_aig_witness_out                  false
% 1.80/0.87  --bmc1_verbose                          false
% 1.80/0.87  --bmc1_dump_clauses_tptp                false
% 1.80/0.87  --bmc1_dump_unsat_core_tptp             false
% 1.80/0.87  --bmc1_dump_file                        -
% 1.80/0.87  --bmc1_ucm_expand_uc_limit              128
% 1.80/0.87  --bmc1_ucm_n_expand_iterations          6
% 1.80/0.87  --bmc1_ucm_extend_mode                  1
% 1.80/0.87  --bmc1_ucm_init_mode                    2
% 1.80/0.87  --bmc1_ucm_cone_mode                    none
% 1.80/0.87  --bmc1_ucm_reduced_relation_type        0
% 1.80/0.87  --bmc1_ucm_relax_model                  4
% 1.80/0.87  --bmc1_ucm_full_tr_after_sat            true
% 1.80/0.87  --bmc1_ucm_expand_neg_assumptions       false
% 1.80/0.87  --bmc1_ucm_layered_model                none
% 1.80/0.88  --bmc1_ucm_max_lemma_size               10
% 1.80/0.88  
% 1.80/0.88  ------ AIG Options
% 1.80/0.88  
% 1.80/0.88  --aig_mode                              false
% 1.80/0.88  
% 1.80/0.88  ------ Instantiation Options
% 1.80/0.88  
% 1.80/0.88  --instantiation_flag                    true
% 1.80/0.88  --inst_sos_flag                         false
% 1.80/0.88  --inst_sos_phase                        true
% 1.80/0.88  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.80/0.88  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.80/0.88  --inst_lit_sel_side                     num_symb
% 1.80/0.88  --inst_solver_per_active                1400
% 1.80/0.88  --inst_solver_calls_frac                1.
% 1.80/0.88  --inst_passive_queue_type               priority_queues
% 1.80/0.88  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.80/0.88  --inst_passive_queues_freq              [25;2]
% 1.80/0.88  --inst_dismatching                      true
% 1.80/0.88  --inst_eager_unprocessed_to_passive     true
% 1.80/0.88  --inst_prop_sim_given                   true
% 1.80/0.88  --inst_prop_sim_new                     false
% 1.80/0.88  --inst_subs_new                         false
% 1.80/0.88  --inst_eq_res_simp                      false
% 1.80/0.88  --inst_subs_given                       false
% 1.80/0.88  --inst_orphan_elimination               true
% 1.80/0.88  --inst_learning_loop_flag               true
% 1.80/0.88  --inst_learning_start                   3000
% 1.80/0.88  --inst_learning_factor                  2
% 1.80/0.88  --inst_start_prop_sim_after_learn       3
% 1.80/0.88  --inst_sel_renew                        solver
% 1.80/0.88  --inst_lit_activity_flag                true
% 1.80/0.88  --inst_restr_to_given                   false
% 1.80/0.88  --inst_activity_threshold               500
% 1.80/0.88  --inst_out_proof                        true
% 1.80/0.88  
% 1.80/0.88  ------ Resolution Options
% 1.80/0.88  
% 1.80/0.88  --resolution_flag                       true
% 1.80/0.88  --res_lit_sel                           adaptive
% 1.80/0.88  --res_lit_sel_side                      none
% 1.80/0.88  --res_ordering                          kbo
% 1.80/0.88  --res_to_prop_solver                    active
% 1.80/0.88  --res_prop_simpl_new                    false
% 1.80/0.88  --res_prop_simpl_given                  true
% 1.80/0.88  --res_passive_queue_type                priority_queues
% 1.80/0.88  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.80/0.88  --res_passive_queues_freq               [15;5]
% 1.80/0.88  --res_forward_subs                      full
% 1.80/0.88  --res_backward_subs                     full
% 1.80/0.88  --res_forward_subs_resolution           true
% 1.80/0.88  --res_backward_subs_resolution          true
% 1.80/0.88  --res_orphan_elimination                true
% 1.80/0.88  --res_time_limit                        2.
% 1.80/0.88  --res_out_proof                         true
% 1.80/0.88  
% 1.80/0.88  ------ Superposition Options
% 1.80/0.88  
% 1.80/0.88  --superposition_flag                    true
% 1.80/0.88  --sup_passive_queue_type                priority_queues
% 1.80/0.88  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.80/0.88  --sup_passive_queues_freq               [8;1;4]
% 1.80/0.88  --demod_completeness_check              fast
% 1.80/0.88  --demod_use_ground                      true
% 1.80/0.88  --sup_to_prop_solver                    passive
% 1.80/0.88  --sup_prop_simpl_new                    true
% 1.80/0.88  --sup_prop_simpl_given                  true
% 1.80/0.88  --sup_fun_splitting                     false
% 1.80/0.88  --sup_smt_interval                      50000
% 1.80/0.88  
% 1.80/0.88  ------ Superposition Simplification Setup
% 1.80/0.88  
% 1.80/0.88  --sup_indices_passive                   []
% 1.80/0.88  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.80/0.88  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.80/0.88  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.80/0.88  --sup_full_triv                         [TrivRules;PropSubs]
% 1.80/0.88  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.80/0.88  --sup_full_bw                           [BwDemod]
% 1.80/0.88  --sup_immed_triv                        [TrivRules]
% 1.80/0.88  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.80/0.88  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.80/0.88  --sup_immed_bw_main                     []
% 1.80/0.88  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.80/0.88  --sup_input_triv                        [Unflattening;TrivRules]
% 1.80/0.88  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.80/0.88  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.80/0.88  
% 1.80/0.88  ------ Combination Options
% 1.80/0.88  
% 1.80/0.88  --comb_res_mult                         3
% 1.80/0.88  --comb_sup_mult                         2
% 1.80/0.88  --comb_inst_mult                        10
% 1.80/0.88  
% 1.80/0.88  ------ Debug Options
% 1.80/0.88  
% 1.80/0.88  --dbg_backtrace                         false
% 1.80/0.88  --dbg_dump_prop_clauses                 false
% 1.80/0.88  --dbg_dump_prop_clauses_file            -
% 1.80/0.88  --dbg_out_stat                          false
% 1.80/0.88  ------ Parsing...
% 1.80/0.88  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.80/0.88  
% 1.80/0.88  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 1.80/0.88  
% 1.80/0.88  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.80/0.88  
% 1.80/0.88  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.80/0.88  ------ Proving...
% 1.80/0.88  ------ Problem Properties 
% 1.80/0.88  
% 1.80/0.88  
% 1.80/0.88  clauses                                 20
% 1.80/0.88  conjectures                             2
% 1.80/0.88  EPR                                     1
% 1.80/0.88  Horn                                    16
% 1.80/0.88  unary                                   10
% 1.80/0.88  binary                                  7
% 1.80/0.88  lits                                    33
% 1.80/0.88  lits eq                                 18
% 1.80/0.88  fd_pure                                 0
% 1.80/0.88  fd_pseudo                               0
% 1.80/0.88  fd_cond                                 1
% 1.80/0.88  fd_pseudo_cond                          2
% 1.80/0.88  AC symbols                              0
% 1.80/0.88  
% 1.80/0.88  ------ Schedule dynamic 5 is on 
% 1.80/0.88  
% 1.80/0.88  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.80/0.88  
% 1.80/0.88  
% 1.80/0.88  ------ 
% 1.80/0.88  Current options:
% 1.80/0.88  ------ 
% 1.80/0.88  
% 1.80/0.88  ------ Input Options
% 1.80/0.88  
% 1.80/0.88  --out_options                           all
% 1.80/0.88  --tptp_safe_out                         true
% 1.80/0.88  --problem_path                          ""
% 1.80/0.88  --include_path                          ""
% 1.80/0.88  --clausifier                            res/vclausify_rel
% 1.80/0.88  --clausifier_options                    --mode clausify
% 1.80/0.88  --stdin                                 false
% 1.80/0.88  --stats_out                             all
% 1.80/0.88  
% 1.80/0.88  ------ General Options
% 1.80/0.88  
% 1.80/0.88  --fof                                   false
% 1.80/0.88  --time_out_real                         305.
% 1.80/0.88  --time_out_virtual                      -1.
% 1.80/0.88  --symbol_type_check                     false
% 1.80/0.88  --clausify_out                          false
% 1.80/0.88  --sig_cnt_out                           false
% 1.80/0.88  --trig_cnt_out                          false
% 1.80/0.88  --trig_cnt_out_tolerance                1.
% 1.80/0.88  --trig_cnt_out_sk_spl                   false
% 1.80/0.88  --abstr_cl_out                          false
% 1.80/0.88  
% 1.80/0.88  ------ Global Options
% 1.80/0.88  
% 1.80/0.88  --schedule                              default
% 1.80/0.88  --add_important_lit                     false
% 1.80/0.88  --prop_solver_per_cl                    1000
% 1.80/0.88  --min_unsat_core                        false
% 1.80/0.88  --soft_assumptions                      false
% 1.80/0.88  --soft_lemma_size                       3
% 1.80/0.88  --prop_impl_unit_size                   0
% 1.80/0.88  --prop_impl_unit                        []
% 1.80/0.88  --share_sel_clauses                     true
% 1.80/0.88  --reset_solvers                         false
% 1.80/0.88  --bc_imp_inh                            [conj_cone]
% 1.80/0.88  --conj_cone_tolerance                   3.
% 1.80/0.88  --extra_neg_conj                        none
% 1.80/0.88  --large_theory_mode                     true
% 1.80/0.88  --prolific_symb_bound                   200
% 1.80/0.88  --lt_threshold                          2000
% 1.80/0.88  --clause_weak_htbl                      true
% 1.80/0.88  --gc_record_bc_elim                     false
% 1.80/0.88  
% 1.80/0.88  ------ Preprocessing Options
% 1.80/0.88  
% 1.80/0.88  --preprocessing_flag                    true
% 1.80/0.88  --time_out_prep_mult                    0.1
% 1.80/0.88  --splitting_mode                        input
% 1.80/0.88  --splitting_grd                         true
% 1.80/0.88  --splitting_cvd                         false
% 1.80/0.88  --splitting_cvd_svl                     false
% 1.80/0.88  --splitting_nvd                         32
% 1.80/0.88  --sub_typing                            true
% 1.80/0.88  --prep_gs_sim                           true
% 1.80/0.88  --prep_unflatten                        true
% 1.80/0.88  --prep_res_sim                          true
% 1.80/0.88  --prep_upred                            true
% 1.80/0.88  --prep_sem_filter                       exhaustive
% 1.80/0.88  --prep_sem_filter_out                   false
% 1.80/0.88  --pred_elim                             true
% 1.80/0.88  --res_sim_input                         true
% 1.80/0.88  --eq_ax_congr_red                       true
% 1.80/0.88  --pure_diseq_elim                       true
% 1.80/0.88  --brand_transform                       false
% 1.80/0.88  --non_eq_to_eq                          false
% 1.80/0.88  --prep_def_merge                        true
% 1.80/0.88  --prep_def_merge_prop_impl              false
% 1.80/0.88  --prep_def_merge_mbd                    true
% 1.80/0.88  --prep_def_merge_tr_red                 false
% 1.80/0.88  --prep_def_merge_tr_cl                  false
% 1.80/0.88  --smt_preprocessing                     true
% 1.80/0.88  --smt_ac_axioms                         fast
% 1.80/0.88  --preprocessed_out                      false
% 1.80/0.88  --preprocessed_stats                    false
% 1.80/0.88  
% 1.80/0.88  ------ Abstraction refinement Options
% 1.80/0.88  
% 1.80/0.88  --abstr_ref                             []
% 1.80/0.88  --abstr_ref_prep                        false
% 1.80/0.88  --abstr_ref_until_sat                   false
% 1.80/0.88  --abstr_ref_sig_restrict                funpre
% 1.80/0.88  --abstr_ref_af_restrict_to_split_sk     false
% 1.80/0.88  --abstr_ref_under                       []
% 1.80/0.88  
% 1.80/0.88  ------ SAT Options
% 1.80/0.88  
% 1.80/0.88  --sat_mode                              false
% 1.80/0.88  --sat_fm_restart_options                ""
% 1.80/0.88  --sat_gr_def                            false
% 1.80/0.88  --sat_epr_types                         true
% 1.80/0.88  --sat_non_cyclic_types                  false
% 1.80/0.88  --sat_finite_models                     false
% 1.80/0.88  --sat_fm_lemmas                         false
% 1.80/0.88  --sat_fm_prep                           false
% 1.80/0.88  --sat_fm_uc_incr                        true
% 1.80/0.88  --sat_out_model                         small
% 1.80/0.88  --sat_out_clauses                       false
% 1.80/0.88  
% 1.80/0.88  ------ QBF Options
% 1.80/0.88  
% 1.80/0.88  --qbf_mode                              false
% 1.80/0.88  --qbf_elim_univ                         false
% 1.80/0.88  --qbf_dom_inst                          none
% 1.80/0.88  --qbf_dom_pre_inst                      false
% 1.80/0.88  --qbf_sk_in                             false
% 1.80/0.88  --qbf_pred_elim                         true
% 1.80/0.88  --qbf_split                             512
% 1.80/0.88  
% 1.80/0.88  ------ BMC1 Options
% 1.80/0.88  
% 1.80/0.88  --bmc1_incremental                      false
% 1.80/0.88  --bmc1_axioms                           reachable_all
% 1.80/0.88  --bmc1_min_bound                        0
% 1.80/0.88  --bmc1_max_bound                        -1
% 1.80/0.88  --bmc1_max_bound_default                -1
% 1.80/0.88  --bmc1_symbol_reachability              true
% 1.80/0.88  --bmc1_property_lemmas                  false
% 1.80/0.88  --bmc1_k_induction                      false
% 1.80/0.88  --bmc1_non_equiv_states                 false
% 1.80/0.88  --bmc1_deadlock                         false
% 1.80/0.88  --bmc1_ucm                              false
% 1.80/0.88  --bmc1_add_unsat_core                   none
% 1.80/0.88  --bmc1_unsat_core_children              false
% 1.80/0.88  --bmc1_unsat_core_extrapolate_axioms    false
% 1.80/0.88  --bmc1_out_stat                         full
% 1.80/0.88  --bmc1_ground_init                      false
% 1.80/0.88  --bmc1_pre_inst_next_state              false
% 1.80/0.88  --bmc1_pre_inst_state                   false
% 1.80/0.88  --bmc1_pre_inst_reach_state             false
% 1.80/0.88  --bmc1_out_unsat_core                   false
% 1.80/0.88  --bmc1_aig_witness_out                  false
% 1.80/0.88  --bmc1_verbose                          false
% 1.80/0.88  --bmc1_dump_clauses_tptp                false
% 1.80/0.88  --bmc1_dump_unsat_core_tptp             false
% 1.80/0.88  --bmc1_dump_file                        -
% 1.80/0.88  --bmc1_ucm_expand_uc_limit              128
% 1.80/0.88  --bmc1_ucm_n_expand_iterations          6
% 1.80/0.88  --bmc1_ucm_extend_mode                  1
% 1.80/0.88  --bmc1_ucm_init_mode                    2
% 1.80/0.88  --bmc1_ucm_cone_mode                    none
% 1.80/0.88  --bmc1_ucm_reduced_relation_type        0
% 1.80/0.88  --bmc1_ucm_relax_model                  4
% 1.80/0.88  --bmc1_ucm_full_tr_after_sat            true
% 1.80/0.88  --bmc1_ucm_expand_neg_assumptions       false
% 1.80/0.88  --bmc1_ucm_layered_model                none
% 1.80/0.88  --bmc1_ucm_max_lemma_size               10
% 1.80/0.88  
% 1.80/0.88  ------ AIG Options
% 1.80/0.88  
% 1.80/0.88  --aig_mode                              false
% 1.80/0.88  
% 1.80/0.88  ------ Instantiation Options
% 1.80/0.88  
% 1.80/0.88  --instantiation_flag                    true
% 1.80/0.88  --inst_sos_flag                         false
% 1.80/0.88  --inst_sos_phase                        true
% 1.80/0.88  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.80/0.88  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.80/0.88  --inst_lit_sel_side                     none
% 1.80/0.88  --inst_solver_per_active                1400
% 1.80/0.88  --inst_solver_calls_frac                1.
% 1.80/0.88  --inst_passive_queue_type               priority_queues
% 1.80/0.88  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.80/0.88  --inst_passive_queues_freq              [25;2]
% 1.80/0.88  --inst_dismatching                      true
% 1.80/0.88  --inst_eager_unprocessed_to_passive     true
% 1.80/0.88  --inst_prop_sim_given                   true
% 1.80/0.88  --inst_prop_sim_new                     false
% 1.80/0.88  --inst_subs_new                         false
% 1.80/0.88  --inst_eq_res_simp                      false
% 1.80/0.88  --inst_subs_given                       false
% 1.80/0.88  --inst_orphan_elimination               true
% 1.80/0.88  --inst_learning_loop_flag               true
% 1.80/0.88  --inst_learning_start                   3000
% 1.80/0.88  --inst_learning_factor                  2
% 1.80/0.88  --inst_start_prop_sim_after_learn       3
% 1.80/0.88  --inst_sel_renew                        solver
% 1.80/0.88  --inst_lit_activity_flag                true
% 1.80/0.88  --inst_restr_to_given                   false
% 1.80/0.88  --inst_activity_threshold               500
% 1.80/0.88  --inst_out_proof                        true
% 1.80/0.88  
% 1.80/0.88  ------ Resolution Options
% 1.80/0.88  
% 1.80/0.88  --resolution_flag                       false
% 1.80/0.88  --res_lit_sel                           adaptive
% 1.80/0.88  --res_lit_sel_side                      none
% 1.80/0.88  --res_ordering                          kbo
% 1.80/0.88  --res_to_prop_solver                    active
% 1.80/0.88  --res_prop_simpl_new                    false
% 1.80/0.88  --res_prop_simpl_given                  true
% 1.80/0.88  --res_passive_queue_type                priority_queues
% 1.80/0.88  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.80/0.88  --res_passive_queues_freq               [15;5]
% 1.80/0.88  --res_forward_subs                      full
% 1.80/0.88  --res_backward_subs                     full
% 1.80/0.88  --res_forward_subs_resolution           true
% 1.80/0.88  --res_backward_subs_resolution          true
% 1.80/0.88  --res_orphan_elimination                true
% 1.80/0.88  --res_time_limit                        2.
% 1.80/0.88  --res_out_proof                         true
% 1.80/0.88  
% 1.80/0.88  ------ Superposition Options
% 1.80/0.88  
% 1.80/0.88  --superposition_flag                    true
% 1.80/0.88  --sup_passive_queue_type                priority_queues
% 1.80/0.88  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.80/0.88  --sup_passive_queues_freq               [8;1;4]
% 1.80/0.88  --demod_completeness_check              fast
% 1.80/0.88  --demod_use_ground                      true
% 1.80/0.88  --sup_to_prop_solver                    passive
% 1.80/0.88  --sup_prop_simpl_new                    true
% 1.80/0.88  --sup_prop_simpl_given                  true
% 1.80/0.88  --sup_fun_splitting                     false
% 1.80/0.88  --sup_smt_interval                      50000
% 1.80/0.88  
% 1.80/0.88  ------ Superposition Simplification Setup
% 1.80/0.88  
% 1.80/0.88  --sup_indices_passive                   []
% 1.80/0.88  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.80/0.88  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.80/0.88  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.80/0.88  --sup_full_triv                         [TrivRules;PropSubs]
% 1.80/0.88  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.80/0.88  --sup_full_bw                           [BwDemod]
% 1.80/0.88  --sup_immed_triv                        [TrivRules]
% 1.80/0.88  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.80/0.88  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.80/0.88  --sup_immed_bw_main                     []
% 1.80/0.88  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.80/0.88  --sup_input_triv                        [Unflattening;TrivRules]
% 1.80/0.88  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.80/0.88  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.80/0.88  
% 1.80/0.88  ------ Combination Options
% 1.80/0.88  
% 1.80/0.88  --comb_res_mult                         3
% 1.80/0.88  --comb_sup_mult                         2
% 1.80/0.88  --comb_inst_mult                        10
% 1.80/0.88  
% 1.80/0.88  ------ Debug Options
% 1.80/0.88  
% 1.80/0.88  --dbg_backtrace                         false
% 1.80/0.88  --dbg_dump_prop_clauses                 false
% 1.80/0.88  --dbg_dump_prop_clauses_file            -
% 1.80/0.88  --dbg_out_stat                          false
% 1.80/0.88  
% 1.80/0.88  
% 1.80/0.88  
% 1.80/0.88  
% 1.80/0.88  ------ Proving...
% 1.80/0.88  
% 1.80/0.88  
% 1.80/0.88  % SZS status Theorem for theBenchmark.p
% 1.80/0.88  
% 1.80/0.88  % SZS output start CNFRefutation for theBenchmark.p
% 1.80/0.88  
% 1.80/0.88  fof(f19,conjecture,(
% 1.80/0.88    ! [X0,X1] : (k1_xboole_0 != X0 => (k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1)) & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)))),
% 1.80/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.80/0.88  
% 1.80/0.88  fof(f20,negated_conjecture,(
% 1.80/0.88    ~! [X0,X1] : (k1_xboole_0 != X0 => (k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1)) & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)))),
% 1.80/0.88    inference(negated_conjecture,[],[f19])).
% 1.80/0.88  
% 1.80/0.88  fof(f23,plain,(
% 1.80/0.88    ? [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,k1_tarski(X1)) | k1_xboole_0 = k2_zfmisc_1(k1_tarski(X1),X0)) & k1_xboole_0 != X0)),
% 1.80/0.88    inference(ennf_transformation,[],[f20])).
% 1.80/0.88  
% 1.80/0.88  fof(f33,plain,(
% 1.80/0.88    ? [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,k1_tarski(X1)) | k1_xboole_0 = k2_zfmisc_1(k1_tarski(X1),X0)) & k1_xboole_0 != X0) => ((k1_xboole_0 = k2_zfmisc_1(sK2,k1_tarski(sK3)) | k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK3),sK2)) & k1_xboole_0 != sK2)),
% 1.80/0.88    introduced(choice_axiom,[])).
% 1.80/0.88  
% 1.80/0.88  fof(f34,plain,(
% 1.80/0.88    (k1_xboole_0 = k2_zfmisc_1(sK2,k1_tarski(sK3)) | k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK3),sK2)) & k1_xboole_0 != sK2),
% 1.80/0.88    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f23,f33])).
% 1.80/0.88  
% 1.80/0.88  fof(f61,plain,(
% 1.80/0.88    k1_xboole_0 = k2_zfmisc_1(sK2,k1_tarski(sK3)) | k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK3),sK2)),
% 1.80/0.88    inference(cnf_transformation,[],[f34])).
% 1.80/0.88  
% 1.80/0.88  fof(f6,axiom,(
% 1.80/0.88    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.80/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.80/0.88  
% 1.80/0.88  fof(f42,plain,(
% 1.80/0.88    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.80/0.88    inference(cnf_transformation,[],[f6])).
% 1.80/0.88  
% 1.80/0.88  fof(f7,axiom,(
% 1.80/0.88    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.80/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.80/0.88  
% 1.80/0.88  fof(f43,plain,(
% 1.80/0.88    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.80/0.88    inference(cnf_transformation,[],[f7])).
% 1.80/0.88  
% 1.80/0.88  fof(f8,axiom,(
% 1.80/0.88    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.80/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.80/0.88  
% 1.80/0.88  fof(f44,plain,(
% 1.80/0.88    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.80/0.88    inference(cnf_transformation,[],[f8])).
% 1.80/0.88  
% 1.80/0.88  fof(f9,axiom,(
% 1.80/0.88    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 1.80/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.80/0.88  
% 1.80/0.88  fof(f45,plain,(
% 1.80/0.88    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 1.80/0.88    inference(cnf_transformation,[],[f9])).
% 1.80/0.88  
% 1.80/0.88  fof(f10,axiom,(
% 1.80/0.88    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 1.80/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.80/0.88  
% 1.80/0.88  fof(f46,plain,(
% 1.80/0.88    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 1.80/0.88    inference(cnf_transformation,[],[f10])).
% 1.80/0.88  
% 1.80/0.88  fof(f11,axiom,(
% 1.80/0.88    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 1.80/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.80/0.88  
% 1.80/0.88  fof(f47,plain,(
% 1.80/0.88    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 1.80/0.88    inference(cnf_transformation,[],[f11])).
% 1.80/0.88  
% 1.80/0.88  fof(f12,axiom,(
% 1.80/0.88    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 1.80/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.80/0.88  
% 1.80/0.88  fof(f48,plain,(
% 1.80/0.88    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 1.80/0.88    inference(cnf_transformation,[],[f12])).
% 1.80/0.88  
% 1.80/0.88  fof(f62,plain,(
% 1.80/0.88    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.80/0.88    inference(definition_unfolding,[],[f47,f48])).
% 1.80/0.88  
% 1.80/0.88  fof(f63,plain,(
% 1.80/0.88    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.80/0.88    inference(definition_unfolding,[],[f46,f62])).
% 1.80/0.88  
% 1.80/0.88  fof(f64,plain,(
% 1.80/0.88    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.80/0.88    inference(definition_unfolding,[],[f45,f63])).
% 1.80/0.88  
% 1.80/0.88  fof(f65,plain,(
% 1.80/0.88    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.80/0.88    inference(definition_unfolding,[],[f44,f64])).
% 1.80/0.88  
% 1.80/0.88  fof(f66,plain,(
% 1.80/0.88    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.80/0.88    inference(definition_unfolding,[],[f43,f65])).
% 1.80/0.88  
% 1.80/0.88  fof(f67,plain,(
% 1.80/0.88    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.80/0.88    inference(definition_unfolding,[],[f42,f66])).
% 1.80/0.88  
% 1.80/0.88  fof(f70,plain,(
% 1.80/0.88    k1_xboole_0 = k2_zfmisc_1(sK2,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) | k1_xboole_0 = k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK2)),
% 1.80/0.88    inference(definition_unfolding,[],[f61,f67,f67])).
% 1.80/0.88  
% 1.80/0.88  fof(f14,axiom,(
% 1.80/0.88    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.80/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.80/0.88  
% 1.80/0.88  fof(f31,plain,(
% 1.80/0.88    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.80/0.88    inference(nnf_transformation,[],[f14])).
% 1.80/0.88  
% 1.80/0.88  fof(f32,plain,(
% 1.80/0.88    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.80/0.88    inference(flattening,[],[f31])).
% 1.80/0.88  
% 1.80/0.88  fof(f53,plain,(
% 1.80/0.88    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 1.80/0.88    inference(cnf_transformation,[],[f32])).
% 1.80/0.88  
% 1.80/0.88  fof(f60,plain,(
% 1.80/0.88    k1_xboole_0 != sK2),
% 1.80/0.88    inference(cnf_transformation,[],[f34])).
% 1.80/0.88  
% 1.80/0.88  fof(f54,plain,(
% 1.80/0.88    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 1.80/0.88    inference(cnf_transformation,[],[f32])).
% 1.80/0.88  
% 1.80/0.88  fof(f74,plain,(
% 1.80/0.88    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.80/0.88    inference(equality_resolution,[],[f54])).
% 1.80/0.88  
% 1.80/0.88  fof(f17,axiom,(
% 1.80/0.88    ! [X0] : k3_tarski(k1_tarski(X0)) = X0),
% 1.80/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.80/0.88  
% 1.80/0.88  fof(f58,plain,(
% 1.80/0.88    ( ! [X0] : (k3_tarski(k1_tarski(X0)) = X0) )),
% 1.80/0.88    inference(cnf_transformation,[],[f17])).
% 1.80/0.88  
% 1.80/0.88  fof(f69,plain,(
% 1.80/0.88    ( ! [X0] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 1.80/0.88    inference(definition_unfolding,[],[f58,f67])).
% 1.80/0.88  
% 1.80/0.88  fof(f16,axiom,(
% 1.80/0.88    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 1.80/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.80/0.88  
% 1.80/0.88  fof(f57,plain,(
% 1.80/0.88    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 1.80/0.88    inference(cnf_transformation,[],[f16])).
% 1.80/0.88  
% 1.80/0.88  fof(f15,axiom,(
% 1.80/0.88    k1_tarski(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0)),
% 1.80/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.80/0.88  
% 1.80/0.88  fof(f56,plain,(
% 1.80/0.88    k1_tarski(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0)),
% 1.80/0.88    inference(cnf_transformation,[],[f15])).
% 1.80/0.88  
% 1.80/0.88  fof(f68,plain,(
% 1.80/0.88    k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_zfmisc_1(k1_xboole_0)),
% 1.80/0.88    inference(definition_unfolding,[],[f56,f67])).
% 1.80/0.88  
% 1.80/0.88  fof(f4,axiom,(
% 1.80/0.88    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.80/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.80/0.88  
% 1.80/0.88  fof(f40,plain,(
% 1.80/0.88    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.80/0.88    inference(cnf_transformation,[],[f4])).
% 1.80/0.88  
% 1.80/0.88  fof(f13,axiom,(
% 1.80/0.88    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.80/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.80/0.88  
% 1.80/0.88  fof(f27,plain,(
% 1.80/0.88    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.80/0.88    inference(nnf_transformation,[],[f13])).
% 1.80/0.88  
% 1.80/0.88  fof(f28,plain,(
% 1.80/0.88    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.80/0.88    inference(rectify,[],[f27])).
% 1.80/0.88  
% 1.80/0.88  fof(f29,plain,(
% 1.80/0.88    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK1(X0,X1),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r1_tarski(sK1(X0,X1),X0) | r2_hidden(sK1(X0,X1),X1))))),
% 1.80/0.88    introduced(choice_axiom,[])).
% 1.80/0.88  
% 1.80/0.88  fof(f30,plain,(
% 1.80/0.88    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK1(X0,X1),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r1_tarski(sK1(X0,X1),X0) | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.80/0.88    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f28,f29])).
% 1.80/0.88  
% 1.80/0.88  fof(f50,plain,(
% 1.80/0.88    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 1.80/0.88    inference(cnf_transformation,[],[f30])).
% 1.80/0.88  
% 1.80/0.88  fof(f71,plain,(
% 1.80/0.88    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 1.80/0.88    inference(equality_resolution,[],[f50])).
% 1.80/0.88  
% 1.80/0.88  fof(f2,axiom,(
% 1.80/0.88    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.80/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.80/0.88  
% 1.80/0.88  fof(f24,plain,(
% 1.80/0.88    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.80/0.88    inference(nnf_transformation,[],[f2])).
% 1.80/0.88  
% 1.80/0.88  fof(f37,plain,(
% 1.80/0.88    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.80/0.88    inference(cnf_transformation,[],[f24])).
% 1.80/0.88  
% 1.80/0.88  fof(f3,axiom,(
% 1.80/0.88    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.80/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.80/0.88  
% 1.80/0.88  fof(f21,plain,(
% 1.80/0.88    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.80/0.88    inference(rectify,[],[f3])).
% 1.80/0.88  
% 1.80/0.88  fof(f22,plain,(
% 1.80/0.88    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.80/0.88    inference(ennf_transformation,[],[f21])).
% 1.80/0.88  
% 1.80/0.88  fof(f25,plain,(
% 1.80/0.88    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 1.80/0.88    introduced(choice_axiom,[])).
% 1.80/0.88  
% 1.80/0.88  fof(f26,plain,(
% 1.80/0.88    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.80/0.88    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f25])).
% 1.80/0.88  
% 1.80/0.88  fof(f39,plain,(
% 1.80/0.88    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 1.80/0.88    inference(cnf_transformation,[],[f26])).
% 1.80/0.88  
% 1.80/0.88  fof(f5,axiom,(
% 1.80/0.88    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 1.80/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.80/0.88  
% 1.80/0.88  fof(f41,plain,(
% 1.80/0.88    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 1.80/0.88    inference(cnf_transformation,[],[f5])).
% 1.80/0.88  
% 1.80/0.88  cnf(c_413,plain,
% 1.80/0.88      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 1.80/0.88      theory(equality) ).
% 1.80/0.88  
% 1.80/0.88  cnf(c_1421,plain,
% 1.80/0.88      ( ~ r2_hidden(X0,X1)
% 1.80/0.88      | r2_hidden(X2,k3_xboole_0(X3,X4))
% 1.80/0.88      | X2 != X0
% 1.80/0.88      | k3_xboole_0(X3,X4) != X1 ),
% 1.80/0.88      inference(instantiation,[status(thm)],[c_413]) ).
% 1.80/0.88  
% 1.80/0.88  cnf(c_1423,plain,
% 1.80/0.88      ( r2_hidden(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0))
% 1.80/0.88      | ~ r2_hidden(k1_xboole_0,k1_xboole_0)
% 1.80/0.88      | k3_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 1.80/0.88      | k1_xboole_0 != k1_xboole_0 ),
% 1.80/0.88      inference(instantiation,[status(thm)],[c_1421]) ).
% 1.80/0.88  
% 1.80/0.88  cnf(c_18,negated_conjecture,
% 1.80/0.88      ( k1_xboole_0 = k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK2)
% 1.80/0.88      | k1_xboole_0 = k2_zfmisc_1(sK2,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) ),
% 1.80/0.88      inference(cnf_transformation,[],[f70]) ).
% 1.80/0.88  
% 1.80/0.88  cnf(c_13,plain,
% 1.80/0.88      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 1.80/0.88      | k1_xboole_0 = X1
% 1.80/0.88      | k1_xboole_0 = X0 ),
% 1.80/0.88      inference(cnf_transformation,[],[f53]) ).
% 1.80/0.88  
% 1.80/0.88  cnf(c_1108,plain,
% 1.80/0.88      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k1_xboole_0
% 1.80/0.88      | k2_zfmisc_1(sK2,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = k1_xboole_0
% 1.80/0.88      | sK2 = k1_xboole_0 ),
% 1.80/0.88      inference(superposition,[status(thm)],[c_18,c_13]) ).
% 1.80/0.88  
% 1.80/0.88  cnf(c_19,negated_conjecture,
% 1.80/0.88      ( k1_xboole_0 != sK2 ),
% 1.80/0.88      inference(cnf_transformation,[],[f60]) ).
% 1.80/0.88  
% 1.80/0.88  cnf(c_22,plain,
% 1.80/0.88      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 1.80/0.88      | k1_xboole_0 = k1_xboole_0 ),
% 1.80/0.88      inference(instantiation,[status(thm)],[c_13]) ).
% 1.80/0.88  
% 1.80/0.88  cnf(c_12,plain,
% 1.80/0.88      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 1.80/0.88      inference(cnf_transformation,[],[f74]) ).
% 1.80/0.88  
% 1.80/0.88  cnf(c_23,plain,
% 1.80/0.88      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 1.80/0.88      inference(instantiation,[status(thm)],[c_12]) ).
% 1.80/0.88  
% 1.80/0.88  cnf(c_411,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 1.80/0.88  
% 1.80/0.88  cnf(c_819,plain,
% 1.80/0.88      ( sK2 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK2 ),
% 1.80/0.88      inference(instantiation,[status(thm)],[c_411]) ).
% 1.80/0.88  
% 1.80/0.88  cnf(c_820,plain,
% 1.80/0.88      ( sK2 != k1_xboole_0
% 1.80/0.88      | k1_xboole_0 = sK2
% 1.80/0.88      | k1_xboole_0 != k1_xboole_0 ),
% 1.80/0.88      inference(instantiation,[status(thm)],[c_819]) ).
% 1.80/0.88  
% 1.80/0.88  cnf(c_1115,plain,
% 1.80/0.88      ( k2_zfmisc_1(sK2,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = k1_xboole_0
% 1.80/0.88      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k1_xboole_0 ),
% 1.80/0.88      inference(global_propositional_subsumption,
% 1.80/0.88                [status(thm)],
% 1.80/0.88                [c_1108,c_19,c_22,c_23,c_820]) ).
% 1.80/0.88  
% 1.80/0.88  cnf(c_1116,plain,
% 1.80/0.88      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k1_xboole_0
% 1.80/0.88      | k2_zfmisc_1(sK2,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = k1_xboole_0 ),
% 1.80/0.88      inference(renaming,[status(thm)],[c_1115]) ).
% 1.80/0.88  
% 1.80/0.88  cnf(c_1119,plain,
% 1.80/0.88      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k1_xboole_0
% 1.80/0.88      | sK2 = k1_xboole_0 ),
% 1.80/0.88      inference(superposition,[status(thm)],[c_1116,c_13]) ).
% 1.80/0.88  
% 1.80/0.88  cnf(c_1162,plain,
% 1.80/0.88      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k1_xboole_0 ),
% 1.80/0.88      inference(global_propositional_subsumption,
% 1.80/0.88                [status(thm)],
% 1.80/0.88                [c_1119,c_19,c_22,c_23,c_820]) ).
% 1.80/0.88  
% 1.80/0.88  cnf(c_16,plain,
% 1.80/0.88      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
% 1.80/0.88      inference(cnf_transformation,[],[f69]) ).
% 1.80/0.88  
% 1.80/0.88  cnf(c_1167,plain,
% 1.80/0.88      ( k3_tarski(k1_xboole_0) = sK3 ),
% 1.80/0.88      inference(superposition,[status(thm)],[c_1162,c_16]) ).
% 1.80/0.88  
% 1.80/0.88  cnf(c_15,plain,
% 1.80/0.88      ( k3_tarski(k1_xboole_0) = k1_xboole_0 ),
% 1.80/0.88      inference(cnf_transformation,[],[f57]) ).
% 1.80/0.88  
% 1.80/0.88  cnf(c_1168,plain,
% 1.80/0.88      ( sK3 = k1_xboole_0 ),
% 1.80/0.88      inference(light_normalisation,[status(thm)],[c_1167,c_15]) ).
% 1.80/0.88  
% 1.80/0.88  cnf(c_1170,plain,
% 1.80/0.88      ( k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 1.80/0.88      inference(demodulation,[status(thm)],[c_1168,c_1162]) ).
% 1.80/0.88  
% 1.80/0.88  cnf(c_14,plain,
% 1.80/0.88      ( k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_zfmisc_1(k1_xboole_0) ),
% 1.80/0.88      inference(cnf_transformation,[],[f68]) ).
% 1.80/0.88  
% 1.80/0.88  cnf(c_1237,plain,
% 1.80/0.88      ( k1_zfmisc_1(k1_xboole_0) = k1_xboole_0 ),
% 1.80/0.88      inference(demodulation,[status(thm)],[c_1170,c_14]) ).
% 1.80/0.88  
% 1.80/0.88  cnf(c_951,plain,
% 1.80/0.88      ( X0 != X1 | X0 = k1_zfmisc_1(X2) | k1_zfmisc_1(X2) != X1 ),
% 1.80/0.88      inference(instantiation,[status(thm)],[c_411]) ).
% 1.80/0.88  
% 1.80/0.88  cnf(c_952,plain,
% 1.80/0.88      ( k1_zfmisc_1(k1_xboole_0) != k1_xboole_0
% 1.80/0.88      | k1_xboole_0 = k1_zfmisc_1(k1_xboole_0)
% 1.80/0.88      | k1_xboole_0 != k1_xboole_0 ),
% 1.80/0.88      inference(instantiation,[status(thm)],[c_951]) ).
% 1.80/0.88  
% 1.80/0.88  cnf(c_873,plain,
% 1.80/0.88      ( r2_hidden(X0,X1)
% 1.80/0.88      | ~ r2_hidden(k3_xboole_0(X2,X3),k1_zfmisc_1(X2))
% 1.80/0.88      | X0 != k3_xboole_0(X2,X3)
% 1.80/0.88      | X1 != k1_zfmisc_1(X2) ),
% 1.80/0.88      inference(instantiation,[status(thm)],[c_413]) ).
% 1.80/0.88  
% 1.80/0.88  cnf(c_875,plain,
% 1.80/0.88      ( ~ r2_hidden(k3_xboole_0(k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
% 1.80/0.88      | r2_hidden(k1_xboole_0,k1_xboole_0)
% 1.80/0.88      | k1_xboole_0 != k3_xboole_0(k1_xboole_0,k1_xboole_0)
% 1.80/0.88      | k1_xboole_0 != k1_zfmisc_1(k1_xboole_0) ),
% 1.80/0.88      inference(instantiation,[status(thm)],[c_873]) ).
% 1.80/0.88  
% 1.80/0.88  cnf(c_867,plain,
% 1.80/0.88      ( X0 != X1 | X0 = k3_xboole_0(X2,X3) | k3_xboole_0(X2,X3) != X1 ),
% 1.80/0.88      inference(instantiation,[status(thm)],[c_411]) ).
% 1.80/0.88  
% 1.80/0.88  cnf(c_868,plain,
% 1.80/0.88      ( k3_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 1.80/0.88      | k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_xboole_0)
% 1.80/0.88      | k1_xboole_0 != k1_xboole_0 ),
% 1.80/0.88      inference(instantiation,[status(thm)],[c_867]) ).
% 1.80/0.88  
% 1.80/0.88  cnf(c_5,plain,
% 1.80/0.88      ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
% 1.80/0.88      inference(cnf_transformation,[],[f40]) ).
% 1.80/0.88  
% 1.80/0.88  cnf(c_9,plain,
% 1.80/0.88      ( ~ r1_tarski(X0,X1) | r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 1.80/0.88      inference(cnf_transformation,[],[f71]) ).
% 1.80/0.88  
% 1.80/0.88  cnf(c_99,plain,
% 1.80/0.88      ( ~ r1_tarski(X0,X1) | r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 1.80/0.88      inference(prop_impl,[status(thm)],[c_9]) ).
% 1.80/0.88  
% 1.80/0.88  cnf(c_230,plain,
% 1.80/0.88      ( r2_hidden(X0,k1_zfmisc_1(X1))
% 1.80/0.88      | X1 != X2
% 1.80/0.88      | k3_xboole_0(X2,X3) != X0 ),
% 1.80/0.88      inference(resolution_lifted,[status(thm)],[c_5,c_99]) ).
% 1.80/0.88  
% 1.80/0.88  cnf(c_231,plain,
% 1.80/0.88      ( r2_hidden(k3_xboole_0(X0,X1),k1_zfmisc_1(X0)) ),
% 1.80/0.88      inference(unflattening,[status(thm)],[c_230]) ).
% 1.80/0.88  
% 1.80/0.88  cnf(c_233,plain,
% 1.80/0.88      ( r2_hidden(k3_xboole_0(k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
% 1.80/0.88      inference(instantiation,[status(thm)],[c_231]) ).
% 1.80/0.88  
% 1.80/0.88  cnf(c_1,plain,
% 1.80/0.88      ( r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0 ),
% 1.80/0.88      inference(cnf_transformation,[],[f37]) ).
% 1.80/0.88  
% 1.80/0.88  cnf(c_48,plain,
% 1.80/0.88      ( r1_xboole_0(k1_xboole_0,k1_xboole_0)
% 1.80/0.88      | k3_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
% 1.80/0.88      inference(instantiation,[status(thm)],[c_1]) ).
% 1.80/0.88  
% 1.80/0.88  cnf(c_3,plain,
% 1.80/0.88      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2)) | ~ r1_xboole_0(X1,X2) ),
% 1.80/0.88      inference(cnf_transformation,[],[f39]) ).
% 1.80/0.88  
% 1.80/0.88  cnf(c_44,plain,
% 1.80/0.88      ( ~ r2_hidden(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0))
% 1.80/0.88      | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 1.80/0.88      inference(instantiation,[status(thm)],[c_3]) ).
% 1.80/0.88  
% 1.80/0.88  cnf(c_6,plain,
% 1.80/0.88      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 1.80/0.88      inference(cnf_transformation,[],[f41]) ).
% 1.80/0.88  
% 1.80/0.88  cnf(c_36,plain,
% 1.80/0.88      ( k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 1.80/0.88      inference(instantiation,[status(thm)],[c_6]) ).
% 1.80/0.88  
% 1.80/0.88  cnf(contradiction,plain,
% 1.80/0.88      ( $false ),
% 1.80/0.88      inference(minisat,
% 1.80/0.88                [status(thm)],
% 1.80/0.88                [c_1423,c_1237,c_952,c_875,c_868,c_233,c_48,c_44,c_36,
% 1.80/0.88                 c_23,c_22]) ).
% 1.80/0.88  
% 1.80/0.88  
% 1.80/0.88  % SZS output end CNFRefutation for theBenchmark.p
% 1.80/0.88  
% 1.80/0.88  ------                               Statistics
% 1.80/0.88  
% 1.80/0.88  ------ General
% 1.80/0.88  
% 1.80/0.88  abstr_ref_over_cycles:                  0
% 1.80/0.88  abstr_ref_under_cycles:                 0
% 1.80/0.88  gc_basic_clause_elim:                   0
% 1.80/0.88  forced_gc_time:                         0
% 1.80/0.88  parsing_time:                           0.006
% 1.80/0.88  unif_index_cands_time:                  0.
% 1.80/0.88  unif_index_add_time:                    0.
% 1.80/0.88  orderings_time:                         0.
% 1.80/0.88  out_proof_time:                         0.011
% 1.80/0.88  total_time:                             0.064
% 1.80/0.88  num_of_symbols:                         44
% 1.80/0.88  num_of_terms:                           1473
% 1.80/0.88  
% 1.80/0.88  ------ Preprocessing
% 1.80/0.88  
% 1.80/0.88  num_of_splits:                          0
% 1.80/0.88  num_of_split_atoms:                     0
% 1.80/0.88  num_of_reused_defs:                     0
% 1.80/0.88  num_eq_ax_congr_red:                    14
% 1.80/0.88  num_of_sem_filtered_clauses:            1
% 1.80/0.88  num_of_subtypes:                        0
% 1.80/0.88  monotx_restored_types:                  0
% 1.80/0.88  sat_num_of_epr_types:                   0
% 1.80/0.88  sat_num_of_non_cyclic_types:            0
% 1.80/0.88  sat_guarded_non_collapsed_types:        0
% 1.80/0.88  num_pure_diseq_elim:                    0
% 1.80/0.88  simp_replaced_by:                       0
% 1.80/0.88  res_preprocessed:                       79
% 1.80/0.88  prep_upred:                             0
% 1.80/0.88  prep_unflattend:                        21
% 1.80/0.88  smt_new_axioms:                         0
% 1.80/0.88  pred_elim_cands:                        3
% 1.80/0.88  pred_elim:                              0
% 1.80/0.88  pred_elim_cl:                           0
% 1.80/0.88  pred_elim_cycles:                       3
% 1.80/0.88  merged_defs:                            12
% 1.80/0.88  merged_defs_ncl:                        0
% 1.80/0.88  bin_hyper_res:                          12
% 1.80/0.88  prep_cycles:                            3
% 1.80/0.88  pred_elim_time:                         0.002
% 1.80/0.88  splitting_time:                         0.
% 1.80/0.88  sem_filter_time:                        0.
% 1.80/0.88  monotx_time:                            0.
% 1.80/0.88  subtype_inf_time:                       0.
% 1.80/0.88  
% 1.80/0.88  ------ Problem properties
% 1.80/0.88  
% 1.80/0.88  clauses:                                20
% 1.80/0.88  conjectures:                            2
% 1.80/0.88  epr:                                    1
% 1.80/0.88  horn:                                   16
% 1.80/0.88  ground:                                 4
% 1.80/0.88  unary:                                  10
% 1.80/0.88  binary:                                 7
% 1.80/0.88  lits:                                   33
% 1.80/0.88  lits_eq:                                18
% 1.80/0.88  fd_pure:                                0
% 1.80/0.88  fd_pseudo:                              0
% 1.80/0.88  fd_cond:                                1
% 1.80/0.88  fd_pseudo_cond:                         2
% 1.80/0.88  ac_symbols:                             0
% 1.80/0.88  
% 1.80/0.88  ------ Propositional Solver
% 1.80/0.88  
% 1.80/0.88  prop_solver_calls:                      23
% 1.80/0.88  prop_fast_solver_calls:                 392
% 1.80/0.88  smt_solver_calls:                       0
% 1.80/0.88  smt_fast_solver_calls:                  0
% 1.80/0.88  prop_num_of_clauses:                    461
% 1.80/0.88  prop_preprocess_simplified:             2285
% 1.80/0.88  prop_fo_subsumed:                       2
% 1.80/0.88  prop_solver_time:                       0.
% 1.80/0.88  smt_solver_time:                        0.
% 1.80/0.88  smt_fast_solver_time:                   0.
% 1.80/0.88  prop_fast_solver_time:                  0.
% 1.80/0.88  prop_unsat_core_time:                   0.
% 1.80/0.88  
% 1.80/0.88  ------ QBF
% 1.80/0.88  
% 1.80/0.88  qbf_q_res:                              0
% 1.80/0.88  qbf_num_tautologies:                    0
% 1.80/0.88  qbf_prep_cycles:                        0
% 1.80/0.88  
% 1.80/0.88  ------ BMC1
% 1.80/0.88  
% 1.80/0.88  bmc1_current_bound:                     -1
% 1.80/0.88  bmc1_last_solved_bound:                 -1
% 1.80/0.88  bmc1_unsat_core_size:                   -1
% 1.80/0.88  bmc1_unsat_core_parents_size:           -1
% 1.80/0.88  bmc1_merge_next_fun:                    0
% 1.80/0.88  bmc1_unsat_core_clauses_time:           0.
% 1.80/0.88  
% 1.80/0.88  ------ Instantiation
% 1.80/0.88  
% 1.80/0.88  inst_num_of_clauses:                    175
% 1.80/0.88  inst_num_in_passive:                    39
% 1.80/0.88  inst_num_in_active:                     95
% 1.80/0.88  inst_num_in_unprocessed:                40
% 1.80/0.88  inst_num_of_loops:                      111
% 1.80/0.88  inst_num_of_learning_restarts:          0
% 1.80/0.88  inst_num_moves_active_passive:          12
% 1.80/0.88  inst_lit_activity:                      0
% 1.80/0.88  inst_lit_activity_moves:                0
% 1.80/0.88  inst_num_tautologies:                   0
% 1.80/0.88  inst_num_prop_implied:                  0
% 1.80/0.88  inst_num_existing_simplified:           0
% 1.80/0.88  inst_num_eq_res_simplified:             0
% 1.80/0.88  inst_num_child_elim:                    0
% 1.80/0.88  inst_num_of_dismatching_blockings:      20
% 1.80/0.88  inst_num_of_non_proper_insts:           112
% 1.80/0.88  inst_num_of_duplicates:                 0
% 1.80/0.88  inst_inst_num_from_inst_to_res:         0
% 1.80/0.88  inst_dismatching_checking_time:         0.
% 1.80/0.88  
% 1.80/0.88  ------ Resolution
% 1.80/0.88  
% 1.80/0.88  res_num_of_clauses:                     0
% 1.80/0.88  res_num_in_passive:                     0
% 1.80/0.88  res_num_in_active:                      0
% 1.80/0.88  res_num_of_loops:                       82
% 1.80/0.88  res_forward_subset_subsumed:            13
% 1.80/0.88  res_backward_subset_subsumed:           0
% 1.80/0.88  res_forward_subsumed:                   0
% 1.80/0.88  res_backward_subsumed:                  0
% 1.80/0.88  res_forward_subsumption_resolution:     0
% 1.80/0.88  res_backward_subsumption_resolution:    0
% 1.80/0.88  res_clause_to_clause_subsumption:       57
% 1.80/0.88  res_orphan_elimination:                 0
% 1.80/0.88  res_tautology_del:                      34
% 1.80/0.88  res_num_eq_res_simplified:              0
% 1.80/0.88  res_num_sel_changes:                    0
% 1.80/0.88  res_moves_from_active_to_pass:          0
% 1.80/0.88  
% 1.80/0.88  ------ Superposition
% 1.80/0.88  
% 1.80/0.88  sup_time_total:                         0.
% 1.80/0.88  sup_time_generating:                    0.
% 1.80/0.88  sup_time_sim_full:                      0.
% 1.80/0.88  sup_time_sim_immed:                     0.
% 1.80/0.88  
% 1.80/0.88  sup_num_of_clauses:                     31
% 1.80/0.88  sup_num_in_active:                      18
% 1.80/0.88  sup_num_in_passive:                     13
% 1.80/0.88  sup_num_of_loops:                       22
% 1.80/0.88  sup_fw_superposition:                   20
% 1.80/0.88  sup_bw_superposition:                   12
% 1.80/0.88  sup_immediate_simplified:               5
% 1.80/0.88  sup_given_eliminated:                   0
% 1.80/0.88  comparisons_done:                       0
% 1.80/0.88  comparisons_avoided:                    0
% 1.80/0.88  
% 1.80/0.88  ------ Simplifications
% 1.80/0.88  
% 1.80/0.88  
% 1.80/0.88  sim_fw_subset_subsumed:                 0
% 1.80/0.88  sim_bw_subset_subsumed:                 1
% 1.80/0.88  sim_fw_subsumed:                        2
% 1.80/0.88  sim_bw_subsumed:                        1
% 1.80/0.88  sim_fw_subsumption_res:                 0
% 1.80/0.88  sim_bw_subsumption_res:                 0
% 1.80/0.88  sim_tautology_del:                      0
% 1.80/0.88  sim_eq_tautology_del:                   3
% 1.80/0.88  sim_eq_res_simp:                        0
% 1.80/0.88  sim_fw_demodulated:                     1
% 1.80/0.88  sim_bw_demodulated:                     3
% 1.80/0.88  sim_light_normalised:                   4
% 1.80/0.88  sim_joinable_taut:                      0
% 1.80/0.88  sim_joinable_simp:                      0
% 1.80/0.88  sim_ac_normalised:                      0
% 1.80/0.88  sim_smt_subsumption:                    0
% 1.80/0.88  
%------------------------------------------------------------------------------
