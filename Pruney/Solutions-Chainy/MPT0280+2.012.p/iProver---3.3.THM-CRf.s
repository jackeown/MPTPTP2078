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
% DateTime   : Thu Dec  3 11:36:36 EST 2020

% Result     : Theorem 11.88s
% Output     : CNFRefutation 11.88s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 127 expanded)
%              Number of clauses        :   29 (  36 expanded)
%              Number of leaves         :   18 (  31 expanded)
%              Depth                    :   16
%              Number of atoms          :  218 ( 275 expanded)
%              Number of equality atoms :  138 ( 172 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f25])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f26])).

fof(f28,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK0(X0,X1,X2,X3) != X2
            & sK0(X0,X1,X2,X3) != X1
            & sK0(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) )
        & ( sK0(X0,X1,X2,X3) = X2
          | sK0(X0,X1,X2,X3) = X1
          | sK0(X0,X1,X2,X3) = X0
          | r2_hidden(sK0(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK0(X0,X1,X2,X3) != X2
              & sK0(X0,X1,X2,X3) != X1
              & sK0(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) )
          & ( sK0(X0,X1,X2,X3) = X2
            | sK0(X0,X1,X2,X3) = X1
            | sK0(X0,X1,X2,X3) = X0
            | r2_hidden(sK0(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).

fof(f40,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f12])).

fof(f55,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f49,f50])).

fof(f56,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f48,f55])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f47,f56])).

fof(f58,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f46,f57])).

fof(f65,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f40,f58])).

fof(f71,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f65])).

fof(f72,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f71])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f59,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f45,f58])).

fof(f69,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f52,f36,f59])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f60,plain,(
    ! [X0,X1] : r1_tarski(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f34,f36])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k5_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k5_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k5_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f16,conjecture,(
    ! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_xboole_0(X0,X1))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_xboole_0(X0,X1))) ),
    inference(negated_conjecture,[],[f16])).

fof(f24,plain,(
    ? [X0,X1] : ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_xboole_0(X0,X1))) ),
    inference(ennf_transformation,[],[f17])).

fof(f30,plain,
    ( ? [X0,X1] : ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_xboole_0(X0,X1)))
   => ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(sK1),k1_zfmisc_1(sK2)),k1_zfmisc_1(k2_xboole_0(sK1,sK2))) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(sK1),k1_zfmisc_1(sK2)),k1_zfmisc_1(k2_xboole_0(sK1,sK2))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f24,f30])).

fof(f54,plain,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(sK1),k1_zfmisc_1(sK2)),k1_zfmisc_1(k2_xboole_0(sK1,sK2))) ),
    inference(cnf_transformation,[],[f31])).

fof(f70,plain,(
    ~ r1_tarski(k5_xboole_0(k5_xboole_0(k1_zfmisc_1(sK1),k1_zfmisc_1(sK2)),k3_xboole_0(k1_zfmisc_1(sK1),k1_zfmisc_1(sK2))),k1_zfmisc_1(k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)))) ),
    inference(definition_unfolding,[],[f54,f36,f36])).

cnf(c_8,plain,
    ( r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_664,plain,
    ( r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_13,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_3,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1253,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_13,c_3])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(X0,k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_660,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X0,k3_tarski(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2114,plain,
    ( r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) != iProver_top
    | r1_tarski(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1253,c_660])).

cnf(c_29742,plain,
    ( r1_tarski(X0,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X1,X0)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_664,c_2114])).

cnf(c_2,plain,
    ( r1_tarski(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_669,plain,
    ( r1_tarski(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_975,plain,
    ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_669])).

cnf(c_14,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_659,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k3_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_671,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k3_xboole_0(X0,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k5_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_670,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(k5_xboole_0(X0,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_15,negated_conjecture,
    ( ~ r1_tarski(k5_xboole_0(k5_xboole_0(k1_zfmisc_1(sK1),k1_zfmisc_1(sK2)),k3_xboole_0(k1_zfmisc_1(sK1),k1_zfmisc_1(sK2))),k1_zfmisc_1(k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_658,plain,
    ( r1_tarski(k5_xboole_0(k5_xboole_0(k1_zfmisc_1(sK1),k1_zfmisc_1(sK2)),k3_xboole_0(k1_zfmisc_1(sK1),k1_zfmisc_1(sK2))),k1_zfmisc_1(k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_773,plain,
    ( r1_tarski(k5_xboole_0(k1_zfmisc_1(sK1),k5_xboole_0(k1_zfmisc_1(sK2),k3_xboole_0(k1_zfmisc_1(sK1),k1_zfmisc_1(sK2)))),k1_zfmisc_1(k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3,c_658])).

cnf(c_875,plain,
    ( r1_tarski(k5_xboole_0(k1_zfmisc_1(sK1),k5_xboole_0(k1_zfmisc_1(sK2),k3_xboole_0(k1_zfmisc_1(sK1),k1_zfmisc_1(sK2)))),k1_zfmisc_1(k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK1,sK2))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_773])).

cnf(c_2310,plain,
    ( r1_tarski(k5_xboole_0(k1_zfmisc_1(sK2),k3_xboole_0(k1_zfmisc_1(sK1),k1_zfmisc_1(sK2))),k1_zfmisc_1(k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK1,sK2))))) != iProver_top
    | r1_tarski(k1_zfmisc_1(sK1),k1_zfmisc_1(k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK1,sK2))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_670,c_875])).

cnf(c_2826,plain,
    ( r1_tarski(k3_xboole_0(k1_zfmisc_1(sK1),k1_zfmisc_1(sK2)),k1_zfmisc_1(k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK1,sK2))))) != iProver_top
    | r1_tarski(k1_zfmisc_1(sK2),k1_zfmisc_1(k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK1,sK2))))) != iProver_top
    | r1_tarski(k1_zfmisc_1(sK1),k1_zfmisc_1(k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK1,sK2))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_670,c_2310])).

cnf(c_3061,plain,
    ( r1_tarski(k1_zfmisc_1(sK2),k1_zfmisc_1(k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK1,sK2))))) != iProver_top
    | r1_tarski(k1_zfmisc_1(sK1),k1_zfmisc_1(k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK1,sK2))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_671,c_2826])).

cnf(c_3490,plain,
    ( r1_tarski(k1_zfmisc_1(sK2),k1_zfmisc_1(k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK1,sK2))))) != iProver_top
    | r1_tarski(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK1,sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_659,c_3061])).

cnf(c_3493,plain,
    ( r1_tarski(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK1,sK2)))) != iProver_top
    | r1_tarski(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK1,sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_659,c_3490])).

cnf(c_3633,plain,
    ( r1_tarski(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK1,sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_975,c_3493])).

cnf(c_29774,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_29742,c_3633])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:55:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 11.88/2.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.88/2.00  
% 11.88/2.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.88/2.00  
% 11.88/2.00  ------  iProver source info
% 11.88/2.00  
% 11.88/2.00  git: date: 2020-06-30 10:37:57 +0100
% 11.88/2.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.88/2.00  git: non_committed_changes: false
% 11.88/2.00  git: last_make_outside_of_git: false
% 11.88/2.00  
% 11.88/2.00  ------ 
% 11.88/2.00  
% 11.88/2.00  ------ Input Options
% 11.88/2.00  
% 11.88/2.00  --out_options                           all
% 11.88/2.00  --tptp_safe_out                         true
% 11.88/2.00  --problem_path                          ""
% 11.88/2.00  --include_path                          ""
% 11.88/2.00  --clausifier                            res/vclausify_rel
% 11.88/2.00  --clausifier_options                    ""
% 11.88/2.00  --stdin                                 false
% 11.88/2.00  --stats_out                             all
% 11.88/2.00  
% 11.88/2.00  ------ General Options
% 11.88/2.00  
% 11.88/2.00  --fof                                   false
% 11.88/2.00  --time_out_real                         305.
% 11.88/2.00  --time_out_virtual                      -1.
% 11.88/2.00  --symbol_type_check                     false
% 11.88/2.00  --clausify_out                          false
% 11.88/2.00  --sig_cnt_out                           false
% 11.88/2.00  --trig_cnt_out                          false
% 11.88/2.00  --trig_cnt_out_tolerance                1.
% 11.88/2.00  --trig_cnt_out_sk_spl                   false
% 11.88/2.00  --abstr_cl_out                          false
% 11.88/2.00  
% 11.88/2.00  ------ Global Options
% 11.88/2.00  
% 11.88/2.00  --schedule                              default
% 11.88/2.00  --add_important_lit                     false
% 11.88/2.00  --prop_solver_per_cl                    1000
% 11.88/2.00  --min_unsat_core                        false
% 11.88/2.00  --soft_assumptions                      false
% 11.88/2.00  --soft_lemma_size                       3
% 11.88/2.00  --prop_impl_unit_size                   0
% 11.88/2.00  --prop_impl_unit                        []
% 11.88/2.00  --share_sel_clauses                     true
% 11.88/2.00  --reset_solvers                         false
% 11.88/2.00  --bc_imp_inh                            [conj_cone]
% 11.88/2.00  --conj_cone_tolerance                   3.
% 11.88/2.00  --extra_neg_conj                        none
% 11.88/2.00  --large_theory_mode                     true
% 11.88/2.00  --prolific_symb_bound                   200
% 11.88/2.00  --lt_threshold                          2000
% 11.88/2.00  --clause_weak_htbl                      true
% 11.88/2.00  --gc_record_bc_elim                     false
% 11.88/2.00  
% 11.88/2.00  ------ Preprocessing Options
% 11.88/2.00  
% 11.88/2.00  --preprocessing_flag                    true
% 11.88/2.00  --time_out_prep_mult                    0.1
% 11.88/2.00  --splitting_mode                        input
% 11.88/2.00  --splitting_grd                         true
% 11.88/2.00  --splitting_cvd                         false
% 11.88/2.00  --splitting_cvd_svl                     false
% 11.88/2.00  --splitting_nvd                         32
% 11.88/2.00  --sub_typing                            true
% 11.88/2.00  --prep_gs_sim                           true
% 11.88/2.00  --prep_unflatten                        true
% 11.88/2.00  --prep_res_sim                          true
% 11.88/2.00  --prep_upred                            true
% 11.88/2.00  --prep_sem_filter                       exhaustive
% 11.88/2.00  --prep_sem_filter_out                   false
% 11.88/2.00  --pred_elim                             true
% 11.88/2.00  --res_sim_input                         true
% 11.88/2.00  --eq_ax_congr_red                       true
% 11.88/2.00  --pure_diseq_elim                       true
% 11.88/2.00  --brand_transform                       false
% 11.88/2.00  --non_eq_to_eq                          false
% 11.88/2.00  --prep_def_merge                        true
% 11.88/2.00  --prep_def_merge_prop_impl              false
% 11.88/2.00  --prep_def_merge_mbd                    true
% 11.88/2.00  --prep_def_merge_tr_red                 false
% 11.88/2.00  --prep_def_merge_tr_cl                  false
% 11.88/2.00  --smt_preprocessing                     true
% 11.88/2.00  --smt_ac_axioms                         fast
% 11.88/2.00  --preprocessed_out                      false
% 11.88/2.00  --preprocessed_stats                    false
% 11.88/2.00  
% 11.88/2.00  ------ Abstraction refinement Options
% 11.88/2.00  
% 11.88/2.00  --abstr_ref                             []
% 11.88/2.00  --abstr_ref_prep                        false
% 11.88/2.00  --abstr_ref_until_sat                   false
% 11.88/2.00  --abstr_ref_sig_restrict                funpre
% 11.88/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.88/2.00  --abstr_ref_under                       []
% 11.88/2.00  
% 11.88/2.00  ------ SAT Options
% 11.88/2.00  
% 11.88/2.00  --sat_mode                              false
% 11.88/2.00  --sat_fm_restart_options                ""
% 11.88/2.00  --sat_gr_def                            false
% 11.88/2.00  --sat_epr_types                         true
% 11.88/2.00  --sat_non_cyclic_types                  false
% 11.88/2.00  --sat_finite_models                     false
% 11.88/2.00  --sat_fm_lemmas                         false
% 11.88/2.00  --sat_fm_prep                           false
% 11.88/2.00  --sat_fm_uc_incr                        true
% 11.88/2.00  --sat_out_model                         small
% 11.88/2.00  --sat_out_clauses                       false
% 11.88/2.00  
% 11.88/2.00  ------ QBF Options
% 11.88/2.00  
% 11.88/2.00  --qbf_mode                              false
% 11.88/2.00  --qbf_elim_univ                         false
% 11.88/2.00  --qbf_dom_inst                          none
% 11.88/2.00  --qbf_dom_pre_inst                      false
% 11.88/2.00  --qbf_sk_in                             false
% 11.88/2.00  --qbf_pred_elim                         true
% 11.88/2.00  --qbf_split                             512
% 11.88/2.00  
% 11.88/2.00  ------ BMC1 Options
% 11.88/2.00  
% 11.88/2.00  --bmc1_incremental                      false
% 11.88/2.00  --bmc1_axioms                           reachable_all
% 11.88/2.00  --bmc1_min_bound                        0
% 11.88/2.00  --bmc1_max_bound                        -1
% 11.88/2.00  --bmc1_max_bound_default                -1
% 11.88/2.00  --bmc1_symbol_reachability              true
% 11.88/2.00  --bmc1_property_lemmas                  false
% 11.88/2.00  --bmc1_k_induction                      false
% 11.88/2.00  --bmc1_non_equiv_states                 false
% 11.88/2.00  --bmc1_deadlock                         false
% 11.88/2.00  --bmc1_ucm                              false
% 11.88/2.00  --bmc1_add_unsat_core                   none
% 11.88/2.00  --bmc1_unsat_core_children              false
% 11.88/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.88/2.00  --bmc1_out_stat                         full
% 11.88/2.00  --bmc1_ground_init                      false
% 11.88/2.00  --bmc1_pre_inst_next_state              false
% 11.88/2.00  --bmc1_pre_inst_state                   false
% 11.88/2.00  --bmc1_pre_inst_reach_state             false
% 11.88/2.00  --bmc1_out_unsat_core                   false
% 11.88/2.00  --bmc1_aig_witness_out                  false
% 11.88/2.00  --bmc1_verbose                          false
% 11.88/2.00  --bmc1_dump_clauses_tptp                false
% 11.88/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.88/2.00  --bmc1_dump_file                        -
% 11.88/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.88/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.88/2.00  --bmc1_ucm_extend_mode                  1
% 11.88/2.00  --bmc1_ucm_init_mode                    2
% 11.88/2.00  --bmc1_ucm_cone_mode                    none
% 11.88/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.88/2.00  --bmc1_ucm_relax_model                  4
% 11.88/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.88/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.88/2.00  --bmc1_ucm_layered_model                none
% 11.88/2.00  --bmc1_ucm_max_lemma_size               10
% 11.88/2.00  
% 11.88/2.00  ------ AIG Options
% 11.88/2.00  
% 11.88/2.00  --aig_mode                              false
% 11.88/2.00  
% 11.88/2.00  ------ Instantiation Options
% 11.88/2.00  
% 11.88/2.00  --instantiation_flag                    true
% 11.88/2.00  --inst_sos_flag                         true
% 11.88/2.00  --inst_sos_phase                        true
% 11.88/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.88/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.88/2.00  --inst_lit_sel_side                     num_symb
% 11.88/2.00  --inst_solver_per_active                1400
% 11.88/2.00  --inst_solver_calls_frac                1.
% 11.88/2.00  --inst_passive_queue_type               priority_queues
% 11.88/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.88/2.00  --inst_passive_queues_freq              [25;2]
% 11.88/2.00  --inst_dismatching                      true
% 11.88/2.00  --inst_eager_unprocessed_to_passive     true
% 11.88/2.00  --inst_prop_sim_given                   true
% 11.88/2.00  --inst_prop_sim_new                     false
% 11.88/2.00  --inst_subs_new                         false
% 11.88/2.00  --inst_eq_res_simp                      false
% 11.88/2.00  --inst_subs_given                       false
% 11.88/2.00  --inst_orphan_elimination               true
% 11.88/2.00  --inst_learning_loop_flag               true
% 11.88/2.00  --inst_learning_start                   3000
% 11.88/2.00  --inst_learning_factor                  2
% 11.88/2.00  --inst_start_prop_sim_after_learn       3
% 11.88/2.00  --inst_sel_renew                        solver
% 11.88/2.00  --inst_lit_activity_flag                true
% 11.88/2.00  --inst_restr_to_given                   false
% 11.88/2.00  --inst_activity_threshold               500
% 11.88/2.00  --inst_out_proof                        true
% 11.88/2.00  
% 11.88/2.00  ------ Resolution Options
% 11.88/2.00  
% 11.88/2.00  --resolution_flag                       true
% 11.88/2.00  --res_lit_sel                           adaptive
% 11.88/2.00  --res_lit_sel_side                      none
% 11.88/2.00  --res_ordering                          kbo
% 11.88/2.00  --res_to_prop_solver                    active
% 11.88/2.00  --res_prop_simpl_new                    false
% 11.88/2.00  --res_prop_simpl_given                  true
% 11.88/2.00  --res_passive_queue_type                priority_queues
% 11.88/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.88/2.00  --res_passive_queues_freq               [15;5]
% 11.88/2.00  --res_forward_subs                      full
% 11.88/2.00  --res_backward_subs                     full
% 11.88/2.00  --res_forward_subs_resolution           true
% 11.88/2.00  --res_backward_subs_resolution          true
% 11.88/2.00  --res_orphan_elimination                true
% 11.88/2.00  --res_time_limit                        2.
% 11.88/2.00  --res_out_proof                         true
% 11.88/2.00  
% 11.88/2.00  ------ Superposition Options
% 11.88/2.00  
% 11.88/2.00  --superposition_flag                    true
% 11.88/2.00  --sup_passive_queue_type                priority_queues
% 11.88/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.88/2.00  --sup_passive_queues_freq               [8;1;4]
% 11.88/2.00  --demod_completeness_check              fast
% 11.88/2.00  --demod_use_ground                      true
% 11.88/2.00  --sup_to_prop_solver                    passive
% 11.88/2.00  --sup_prop_simpl_new                    true
% 11.88/2.00  --sup_prop_simpl_given                  true
% 11.88/2.00  --sup_fun_splitting                     true
% 11.88/2.00  --sup_smt_interval                      50000
% 11.88/2.00  
% 11.88/2.00  ------ Superposition Simplification Setup
% 11.88/2.00  
% 11.88/2.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.88/2.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.88/2.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.88/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.88/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.88/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.88/2.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.88/2.00  --sup_immed_triv                        [TrivRules]
% 11.88/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.88/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.88/2.00  --sup_immed_bw_main                     []
% 11.88/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.88/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.88/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.88/2.00  --sup_input_bw                          []
% 11.88/2.00  
% 11.88/2.00  ------ Combination Options
% 11.88/2.00  
% 11.88/2.00  --comb_res_mult                         3
% 11.88/2.00  --comb_sup_mult                         2
% 11.88/2.00  --comb_inst_mult                        10
% 11.88/2.00  
% 11.88/2.00  ------ Debug Options
% 11.88/2.00  
% 11.88/2.00  --dbg_backtrace                         false
% 11.88/2.00  --dbg_dump_prop_clauses                 false
% 11.88/2.00  --dbg_dump_prop_clauses_file            -
% 11.88/2.00  --dbg_out_stat                          false
% 11.88/2.00  ------ Parsing...
% 11.88/2.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.88/2.00  
% 11.88/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 11.88/2.00  
% 11.88/2.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.88/2.00  
% 11.88/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.88/2.00  ------ Proving...
% 11.88/2.00  ------ Problem Properties 
% 11.88/2.00  
% 11.88/2.00  
% 11.88/2.00  clauses                                 16
% 11.88/2.00  conjectures                             1
% 11.88/2.00  EPR                                     0
% 11.88/2.00  Horn                                    14
% 11.88/2.00  unary                                   7
% 11.88/2.00  binary                                  3
% 11.88/2.00  lits                                    34
% 11.88/2.00  lits eq                                 15
% 11.88/2.00  fd_pure                                 0
% 11.88/2.00  fd_pseudo                               0
% 11.88/2.00  fd_cond                                 0
% 11.88/2.00  fd_pseudo_cond                          4
% 11.88/2.00  AC symbols                              0
% 11.88/2.00  
% 11.88/2.00  ------ Schedule dynamic 5 is on 
% 11.88/2.00  
% 11.88/2.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.88/2.00  
% 11.88/2.00  
% 11.88/2.00  ------ 
% 11.88/2.00  Current options:
% 11.88/2.00  ------ 
% 11.88/2.00  
% 11.88/2.00  ------ Input Options
% 11.88/2.00  
% 11.88/2.00  --out_options                           all
% 11.88/2.00  --tptp_safe_out                         true
% 11.88/2.00  --problem_path                          ""
% 11.88/2.00  --include_path                          ""
% 11.88/2.00  --clausifier                            res/vclausify_rel
% 11.88/2.00  --clausifier_options                    ""
% 11.88/2.00  --stdin                                 false
% 11.88/2.00  --stats_out                             all
% 11.88/2.00  
% 11.88/2.00  ------ General Options
% 11.88/2.00  
% 11.88/2.00  --fof                                   false
% 11.88/2.00  --time_out_real                         305.
% 11.88/2.00  --time_out_virtual                      -1.
% 11.88/2.00  --symbol_type_check                     false
% 11.88/2.00  --clausify_out                          false
% 11.88/2.00  --sig_cnt_out                           false
% 11.88/2.00  --trig_cnt_out                          false
% 11.88/2.00  --trig_cnt_out_tolerance                1.
% 11.88/2.00  --trig_cnt_out_sk_spl                   false
% 11.88/2.00  --abstr_cl_out                          false
% 11.88/2.00  
% 11.88/2.00  ------ Global Options
% 11.88/2.00  
% 11.88/2.00  --schedule                              default
% 11.88/2.00  --add_important_lit                     false
% 11.88/2.00  --prop_solver_per_cl                    1000
% 11.88/2.00  --min_unsat_core                        false
% 11.88/2.00  --soft_assumptions                      false
% 11.88/2.00  --soft_lemma_size                       3
% 11.88/2.00  --prop_impl_unit_size                   0
% 11.88/2.00  --prop_impl_unit                        []
% 11.88/2.00  --share_sel_clauses                     true
% 11.88/2.00  --reset_solvers                         false
% 11.88/2.00  --bc_imp_inh                            [conj_cone]
% 11.88/2.00  --conj_cone_tolerance                   3.
% 11.88/2.00  --extra_neg_conj                        none
% 11.88/2.00  --large_theory_mode                     true
% 11.88/2.00  --prolific_symb_bound                   200
% 11.88/2.00  --lt_threshold                          2000
% 11.88/2.00  --clause_weak_htbl                      true
% 11.88/2.00  --gc_record_bc_elim                     false
% 11.88/2.00  
% 11.88/2.00  ------ Preprocessing Options
% 11.88/2.00  
% 11.88/2.00  --preprocessing_flag                    true
% 11.88/2.00  --time_out_prep_mult                    0.1
% 11.88/2.00  --splitting_mode                        input
% 11.88/2.00  --splitting_grd                         true
% 11.88/2.00  --splitting_cvd                         false
% 11.88/2.00  --splitting_cvd_svl                     false
% 11.88/2.00  --splitting_nvd                         32
% 11.88/2.00  --sub_typing                            true
% 11.88/2.00  --prep_gs_sim                           true
% 11.88/2.00  --prep_unflatten                        true
% 11.88/2.00  --prep_res_sim                          true
% 11.88/2.00  --prep_upred                            true
% 11.88/2.00  --prep_sem_filter                       exhaustive
% 11.88/2.00  --prep_sem_filter_out                   false
% 11.88/2.00  --pred_elim                             true
% 11.88/2.00  --res_sim_input                         true
% 11.88/2.00  --eq_ax_congr_red                       true
% 11.88/2.00  --pure_diseq_elim                       true
% 11.88/2.00  --brand_transform                       false
% 11.88/2.00  --non_eq_to_eq                          false
% 11.88/2.00  --prep_def_merge                        true
% 11.88/2.00  --prep_def_merge_prop_impl              false
% 11.88/2.00  --prep_def_merge_mbd                    true
% 11.88/2.00  --prep_def_merge_tr_red                 false
% 11.88/2.00  --prep_def_merge_tr_cl                  false
% 11.88/2.00  --smt_preprocessing                     true
% 11.88/2.00  --smt_ac_axioms                         fast
% 11.88/2.00  --preprocessed_out                      false
% 11.88/2.00  --preprocessed_stats                    false
% 11.88/2.00  
% 11.88/2.00  ------ Abstraction refinement Options
% 11.88/2.00  
% 11.88/2.00  --abstr_ref                             []
% 11.88/2.00  --abstr_ref_prep                        false
% 11.88/2.00  --abstr_ref_until_sat                   false
% 11.88/2.00  --abstr_ref_sig_restrict                funpre
% 11.88/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.88/2.00  --abstr_ref_under                       []
% 11.88/2.00  
% 11.88/2.00  ------ SAT Options
% 11.88/2.00  
% 11.88/2.00  --sat_mode                              false
% 11.88/2.00  --sat_fm_restart_options                ""
% 11.88/2.00  --sat_gr_def                            false
% 11.88/2.00  --sat_epr_types                         true
% 11.88/2.00  --sat_non_cyclic_types                  false
% 11.88/2.00  --sat_finite_models                     false
% 11.88/2.00  --sat_fm_lemmas                         false
% 11.88/2.00  --sat_fm_prep                           false
% 11.88/2.00  --sat_fm_uc_incr                        true
% 11.88/2.00  --sat_out_model                         small
% 11.88/2.00  --sat_out_clauses                       false
% 11.88/2.00  
% 11.88/2.00  ------ QBF Options
% 11.88/2.00  
% 11.88/2.00  --qbf_mode                              false
% 11.88/2.00  --qbf_elim_univ                         false
% 11.88/2.00  --qbf_dom_inst                          none
% 11.88/2.00  --qbf_dom_pre_inst                      false
% 11.88/2.00  --qbf_sk_in                             false
% 11.88/2.00  --qbf_pred_elim                         true
% 11.88/2.00  --qbf_split                             512
% 11.88/2.00  
% 11.88/2.00  ------ BMC1 Options
% 11.88/2.00  
% 11.88/2.00  --bmc1_incremental                      false
% 11.88/2.00  --bmc1_axioms                           reachable_all
% 11.88/2.00  --bmc1_min_bound                        0
% 11.88/2.00  --bmc1_max_bound                        -1
% 11.88/2.00  --bmc1_max_bound_default                -1
% 11.88/2.00  --bmc1_symbol_reachability              true
% 11.88/2.00  --bmc1_property_lemmas                  false
% 11.88/2.00  --bmc1_k_induction                      false
% 11.88/2.00  --bmc1_non_equiv_states                 false
% 11.88/2.00  --bmc1_deadlock                         false
% 11.88/2.00  --bmc1_ucm                              false
% 11.88/2.00  --bmc1_add_unsat_core                   none
% 11.88/2.00  --bmc1_unsat_core_children              false
% 11.88/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.88/2.00  --bmc1_out_stat                         full
% 11.88/2.00  --bmc1_ground_init                      false
% 11.88/2.00  --bmc1_pre_inst_next_state              false
% 11.88/2.00  --bmc1_pre_inst_state                   false
% 11.88/2.00  --bmc1_pre_inst_reach_state             false
% 11.88/2.00  --bmc1_out_unsat_core                   false
% 11.88/2.00  --bmc1_aig_witness_out                  false
% 11.88/2.00  --bmc1_verbose                          false
% 11.88/2.00  --bmc1_dump_clauses_tptp                false
% 11.88/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.88/2.00  --bmc1_dump_file                        -
% 11.88/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.88/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.88/2.00  --bmc1_ucm_extend_mode                  1
% 11.88/2.00  --bmc1_ucm_init_mode                    2
% 11.88/2.00  --bmc1_ucm_cone_mode                    none
% 11.88/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.88/2.00  --bmc1_ucm_relax_model                  4
% 11.88/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.88/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.88/2.00  --bmc1_ucm_layered_model                none
% 11.88/2.00  --bmc1_ucm_max_lemma_size               10
% 11.88/2.00  
% 11.88/2.00  ------ AIG Options
% 11.88/2.00  
% 11.88/2.00  --aig_mode                              false
% 11.88/2.00  
% 11.88/2.00  ------ Instantiation Options
% 11.88/2.00  
% 11.88/2.00  --instantiation_flag                    true
% 11.88/2.00  --inst_sos_flag                         true
% 11.88/2.00  --inst_sos_phase                        true
% 11.88/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.88/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.88/2.00  --inst_lit_sel_side                     none
% 11.88/2.00  --inst_solver_per_active                1400
% 11.88/2.00  --inst_solver_calls_frac                1.
% 11.88/2.00  --inst_passive_queue_type               priority_queues
% 11.88/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.88/2.00  --inst_passive_queues_freq              [25;2]
% 11.88/2.00  --inst_dismatching                      true
% 11.88/2.00  --inst_eager_unprocessed_to_passive     true
% 11.88/2.00  --inst_prop_sim_given                   true
% 11.88/2.00  --inst_prop_sim_new                     false
% 11.88/2.00  --inst_subs_new                         false
% 11.88/2.00  --inst_eq_res_simp                      false
% 11.88/2.00  --inst_subs_given                       false
% 11.88/2.00  --inst_orphan_elimination               true
% 11.88/2.00  --inst_learning_loop_flag               true
% 11.88/2.00  --inst_learning_start                   3000
% 11.88/2.00  --inst_learning_factor                  2
% 11.88/2.00  --inst_start_prop_sim_after_learn       3
% 11.88/2.00  --inst_sel_renew                        solver
% 11.88/2.00  --inst_lit_activity_flag                true
% 11.88/2.00  --inst_restr_to_given                   false
% 11.88/2.00  --inst_activity_threshold               500
% 11.88/2.00  --inst_out_proof                        true
% 11.88/2.00  
% 11.88/2.00  ------ Resolution Options
% 11.88/2.00  
% 11.88/2.00  --resolution_flag                       false
% 11.88/2.00  --res_lit_sel                           adaptive
% 11.88/2.00  --res_lit_sel_side                      none
% 11.88/2.00  --res_ordering                          kbo
% 11.88/2.00  --res_to_prop_solver                    active
% 11.88/2.00  --res_prop_simpl_new                    false
% 11.88/2.00  --res_prop_simpl_given                  true
% 11.88/2.00  --res_passive_queue_type                priority_queues
% 11.88/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.88/2.00  --res_passive_queues_freq               [15;5]
% 11.88/2.00  --res_forward_subs                      full
% 11.88/2.00  --res_backward_subs                     full
% 11.88/2.00  --res_forward_subs_resolution           true
% 11.88/2.00  --res_backward_subs_resolution          true
% 11.88/2.00  --res_orphan_elimination                true
% 11.88/2.00  --res_time_limit                        2.
% 11.88/2.00  --res_out_proof                         true
% 11.88/2.00  
% 11.88/2.00  ------ Superposition Options
% 11.88/2.00  
% 11.88/2.00  --superposition_flag                    true
% 11.88/2.00  --sup_passive_queue_type                priority_queues
% 11.88/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.88/2.00  --sup_passive_queues_freq               [8;1;4]
% 11.88/2.00  --demod_completeness_check              fast
% 11.88/2.00  --demod_use_ground                      true
% 11.88/2.00  --sup_to_prop_solver                    passive
% 11.88/2.00  --sup_prop_simpl_new                    true
% 11.88/2.00  --sup_prop_simpl_given                  true
% 11.88/2.00  --sup_fun_splitting                     true
% 11.88/2.00  --sup_smt_interval                      50000
% 11.88/2.00  
% 11.88/2.00  ------ Superposition Simplification Setup
% 11.88/2.00  
% 11.88/2.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.88/2.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.88/2.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.88/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.88/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.88/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.88/2.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.88/2.00  --sup_immed_triv                        [TrivRules]
% 11.88/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.88/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.88/2.00  --sup_immed_bw_main                     []
% 11.88/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.88/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.88/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.88/2.00  --sup_input_bw                          []
% 11.88/2.00  
% 11.88/2.00  ------ Combination Options
% 11.88/2.00  
% 11.88/2.00  --comb_res_mult                         3
% 11.88/2.00  --comb_sup_mult                         2
% 11.88/2.00  --comb_inst_mult                        10
% 11.88/2.00  
% 11.88/2.00  ------ Debug Options
% 11.88/2.00  
% 11.88/2.00  --dbg_backtrace                         false
% 11.88/2.00  --dbg_dump_prop_clauses                 false
% 11.88/2.00  --dbg_dump_prop_clauses_file            -
% 11.88/2.00  --dbg_out_stat                          false
% 11.88/2.00  
% 11.88/2.00  
% 11.88/2.00  
% 11.88/2.00  
% 11.88/2.00  ------ Proving...
% 11.88/2.00  
% 11.88/2.00  
% 11.88/2.00  % SZS status Theorem for theBenchmark.p
% 11.88/2.00  
% 11.88/2.00   Resolution empty clause
% 11.88/2.00  
% 11.88/2.00  % SZS output start CNFRefutation for theBenchmark.p
% 11.88/2.00  
% 11.88/2.00  fof(f6,axiom,(
% 11.88/2.00    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 11.88/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.88/2.00  
% 11.88/2.00  fof(f21,plain,(
% 11.88/2.00    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 11.88/2.00    inference(ennf_transformation,[],[f6])).
% 11.88/2.00  
% 11.88/2.00  fof(f25,plain,(
% 11.88/2.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 11.88/2.00    inference(nnf_transformation,[],[f21])).
% 11.88/2.00  
% 11.88/2.00  fof(f26,plain,(
% 11.88/2.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 11.88/2.00    inference(flattening,[],[f25])).
% 11.88/2.00  
% 11.88/2.00  fof(f27,plain,(
% 11.88/2.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 11.88/2.00    inference(rectify,[],[f26])).
% 11.88/2.00  
% 11.88/2.00  fof(f28,plain,(
% 11.88/2.00    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3))))),
% 11.88/2.00    introduced(choice_axiom,[])).
% 11.88/2.00  
% 11.88/2.00  fof(f29,plain,(
% 11.88/2.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 11.88/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).
% 11.88/2.00  
% 11.88/2.00  fof(f40,plain,(
% 11.88/2.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 11.88/2.00    inference(cnf_transformation,[],[f29])).
% 11.88/2.00  
% 11.88/2.00  fof(f8,axiom,(
% 11.88/2.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 11.88/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.88/2.00  
% 11.88/2.00  fof(f46,plain,(
% 11.88/2.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 11.88/2.00    inference(cnf_transformation,[],[f8])).
% 11.88/2.00  
% 11.88/2.00  fof(f9,axiom,(
% 11.88/2.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 11.88/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.88/2.00  
% 11.88/2.00  fof(f47,plain,(
% 11.88/2.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 11.88/2.00    inference(cnf_transformation,[],[f9])).
% 11.88/2.00  
% 11.88/2.00  fof(f10,axiom,(
% 11.88/2.00    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 11.88/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.88/2.00  
% 11.88/2.00  fof(f48,plain,(
% 11.88/2.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 11.88/2.00    inference(cnf_transformation,[],[f10])).
% 11.88/2.00  
% 11.88/2.00  fof(f11,axiom,(
% 11.88/2.00    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 11.88/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.88/2.00  
% 11.88/2.00  fof(f49,plain,(
% 11.88/2.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 11.88/2.00    inference(cnf_transformation,[],[f11])).
% 11.88/2.00  
% 11.88/2.00  fof(f12,axiom,(
% 11.88/2.00    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 11.88/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.88/2.00  
% 11.88/2.00  fof(f50,plain,(
% 11.88/2.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 11.88/2.00    inference(cnf_transformation,[],[f12])).
% 11.88/2.00  
% 11.88/2.00  fof(f55,plain,(
% 11.88/2.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 11.88/2.00    inference(definition_unfolding,[],[f49,f50])).
% 11.88/2.00  
% 11.88/2.00  fof(f56,plain,(
% 11.88/2.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 11.88/2.00    inference(definition_unfolding,[],[f48,f55])).
% 11.88/2.00  
% 11.88/2.00  fof(f57,plain,(
% 11.88/2.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 11.88/2.00    inference(definition_unfolding,[],[f47,f56])).
% 11.88/2.00  
% 11.88/2.00  fof(f58,plain,(
% 11.88/2.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 11.88/2.00    inference(definition_unfolding,[],[f46,f57])).
% 11.88/2.00  
% 11.88/2.00  fof(f65,plain,(
% 11.88/2.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 11.88/2.00    inference(definition_unfolding,[],[f40,f58])).
% 11.88/2.00  
% 11.88/2.00  fof(f71,plain,(
% 11.88/2.00    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X5) != X3) )),
% 11.88/2.00    inference(equality_resolution,[],[f65])).
% 11.88/2.00  
% 11.88/2.00  fof(f72,plain,(
% 11.88/2.00    ( ! [X0,X5,X1] : (r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X5))) )),
% 11.88/2.00    inference(equality_resolution,[],[f71])).
% 11.88/2.00  
% 11.88/2.00  fof(f14,axiom,(
% 11.88/2.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 11.88/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.88/2.00  
% 11.88/2.00  fof(f52,plain,(
% 11.88/2.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 11.88/2.00    inference(cnf_transformation,[],[f14])).
% 11.88/2.00  
% 11.88/2.00  fof(f5,axiom,(
% 11.88/2.00    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)),
% 11.88/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.88/2.00  
% 11.88/2.00  fof(f36,plain,(
% 11.88/2.00    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 11.88/2.00    inference(cnf_transformation,[],[f5])).
% 11.88/2.00  
% 11.88/2.00  fof(f7,axiom,(
% 11.88/2.00    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 11.88/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.88/2.00  
% 11.88/2.00  fof(f45,plain,(
% 11.88/2.00    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 11.88/2.00    inference(cnf_transformation,[],[f7])).
% 11.88/2.00  
% 11.88/2.00  fof(f59,plain,(
% 11.88/2.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 11.88/2.00    inference(definition_unfolding,[],[f45,f58])).
% 11.88/2.00  
% 11.88/2.00  fof(f69,plain,(
% 11.88/2.00    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 11.88/2.00    inference(definition_unfolding,[],[f52,f36,f59])).
% 11.88/2.00  
% 11.88/2.00  fof(f4,axiom,(
% 11.88/2.00    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 11.88/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.88/2.00  
% 11.88/2.00  fof(f35,plain,(
% 11.88/2.00    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 11.88/2.00    inference(cnf_transformation,[],[f4])).
% 11.88/2.00  
% 11.88/2.00  fof(f13,axiom,(
% 11.88/2.00    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 11.88/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.88/2.00  
% 11.88/2.00  fof(f22,plain,(
% 11.88/2.00    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 11.88/2.00    inference(ennf_transformation,[],[f13])).
% 11.88/2.00  
% 11.88/2.00  fof(f51,plain,(
% 11.88/2.00    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 11.88/2.00    inference(cnf_transformation,[],[f22])).
% 11.88/2.00  
% 11.88/2.00  fof(f3,axiom,(
% 11.88/2.00    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 11.88/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.88/2.00  
% 11.88/2.00  fof(f34,plain,(
% 11.88/2.00    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 11.88/2.00    inference(cnf_transformation,[],[f3])).
% 11.88/2.00  
% 11.88/2.00  fof(f60,plain,(
% 11.88/2.00    ( ! [X0,X1] : (r1_tarski(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)))) )),
% 11.88/2.00    inference(definition_unfolding,[],[f34,f36])).
% 11.88/2.00  
% 11.88/2.00  fof(f15,axiom,(
% 11.88/2.00    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)))),
% 11.88/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.88/2.00  
% 11.88/2.00  fof(f23,plain,(
% 11.88/2.00    ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 11.88/2.00    inference(ennf_transformation,[],[f15])).
% 11.88/2.00  
% 11.88/2.00  fof(f53,plain,(
% 11.88/2.00    ( ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 11.88/2.00    inference(cnf_transformation,[],[f23])).
% 11.88/2.00  
% 11.88/2.00  fof(f1,axiom,(
% 11.88/2.00    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),X1))),
% 11.88/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.88/2.00  
% 11.88/2.00  fof(f18,plain,(
% 11.88/2.00    ! [X0,X1,X2] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 11.88/2.00    inference(ennf_transformation,[],[f1])).
% 11.88/2.00  
% 11.88/2.00  fof(f32,plain,(
% 11.88/2.00    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 11.88/2.00    inference(cnf_transformation,[],[f18])).
% 11.88/2.00  
% 11.88/2.00  fof(f2,axiom,(
% 11.88/2.00    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k5_xboole_0(X0,X2),X1))),
% 11.88/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.88/2.00  
% 11.88/2.00  fof(f19,plain,(
% 11.88/2.00    ! [X0,X1,X2] : (r1_tarski(k5_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 11.88/2.00    inference(ennf_transformation,[],[f2])).
% 11.88/2.00  
% 11.88/2.00  fof(f20,plain,(
% 11.88/2.00    ! [X0,X1,X2] : (r1_tarski(k5_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 11.88/2.00    inference(flattening,[],[f19])).
% 11.88/2.00  
% 11.88/2.00  fof(f33,plain,(
% 11.88/2.00    ( ! [X2,X0,X1] : (r1_tarski(k5_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 11.88/2.00    inference(cnf_transformation,[],[f20])).
% 11.88/2.00  
% 11.88/2.00  fof(f16,conjecture,(
% 11.88/2.00    ! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_xboole_0(X0,X1)))),
% 11.88/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.88/2.00  
% 11.88/2.00  fof(f17,negated_conjecture,(
% 11.88/2.00    ~! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_xboole_0(X0,X1)))),
% 11.88/2.00    inference(negated_conjecture,[],[f16])).
% 11.88/2.00  
% 11.88/2.00  fof(f24,plain,(
% 11.88/2.00    ? [X0,X1] : ~r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_xboole_0(X0,X1)))),
% 11.88/2.00    inference(ennf_transformation,[],[f17])).
% 11.88/2.00  
% 11.88/2.00  fof(f30,plain,(
% 11.88/2.00    ? [X0,X1] : ~r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_xboole_0(X0,X1))) => ~r1_tarski(k2_xboole_0(k1_zfmisc_1(sK1),k1_zfmisc_1(sK2)),k1_zfmisc_1(k2_xboole_0(sK1,sK2)))),
% 11.88/2.00    introduced(choice_axiom,[])).
% 11.88/2.00  
% 11.88/2.00  fof(f31,plain,(
% 11.88/2.00    ~r1_tarski(k2_xboole_0(k1_zfmisc_1(sK1),k1_zfmisc_1(sK2)),k1_zfmisc_1(k2_xboole_0(sK1,sK2)))),
% 11.88/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f24,f30])).
% 11.88/2.00  
% 11.88/2.00  fof(f54,plain,(
% 11.88/2.00    ~r1_tarski(k2_xboole_0(k1_zfmisc_1(sK1),k1_zfmisc_1(sK2)),k1_zfmisc_1(k2_xboole_0(sK1,sK2)))),
% 11.88/2.00    inference(cnf_transformation,[],[f31])).
% 11.88/2.00  
% 11.88/2.00  fof(f70,plain,(
% 11.88/2.00    ~r1_tarski(k5_xboole_0(k5_xboole_0(k1_zfmisc_1(sK1),k1_zfmisc_1(sK2)),k3_xboole_0(k1_zfmisc_1(sK1),k1_zfmisc_1(sK2))),k1_zfmisc_1(k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2))))),
% 11.88/2.00    inference(definition_unfolding,[],[f54,f36,f36])).
% 11.88/2.00  
% 11.88/2.00  cnf(c_8,plain,
% 11.88/2.00      ( r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0)) ),
% 11.88/2.00      inference(cnf_transformation,[],[f72]) ).
% 11.88/2.00  
% 11.88/2.00  cnf(c_664,plain,
% 11.88/2.00      ( r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0)) = iProver_top ),
% 11.88/2.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 11.88/2.00  
% 11.88/2.00  cnf(c_13,plain,
% 11.88/2.00      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
% 11.88/2.00      inference(cnf_transformation,[],[f69]) ).
% 11.88/2.00  
% 11.88/2.00  cnf(c_3,plain,
% 11.88/2.00      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 11.88/2.00      inference(cnf_transformation,[],[f35]) ).
% 11.88/2.00  
% 11.88/2.00  cnf(c_1253,plain,
% 11.88/2.00      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) ),
% 11.88/2.00      inference(superposition,[status(thm)],[c_13,c_3]) ).
% 11.88/2.00  
% 11.88/2.00  cnf(c_12,plain,
% 11.88/2.00      ( ~ r2_hidden(X0,X1) | r1_tarski(X0,k3_tarski(X1)) ),
% 11.88/2.00      inference(cnf_transformation,[],[f51]) ).
% 11.88/2.00  
% 11.88/2.00  cnf(c_660,plain,
% 11.88/2.00      ( r2_hidden(X0,X1) != iProver_top
% 11.88/2.00      | r1_tarski(X0,k3_tarski(X1)) = iProver_top ),
% 11.88/2.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 11.88/2.00  
% 11.88/2.00  cnf(c_2114,plain,
% 11.88/2.00      ( r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) != iProver_top
% 11.88/2.00      | r1_tarski(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2)))) = iProver_top ),
% 11.88/2.00      inference(superposition,[status(thm)],[c_1253,c_660]) ).
% 11.88/2.00  
% 11.88/2.00  cnf(c_29742,plain,
% 11.88/2.00      ( r1_tarski(X0,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X1,X0)))) = iProver_top ),
% 11.88/2.00      inference(superposition,[status(thm)],[c_664,c_2114]) ).
% 11.88/2.00  
% 11.88/2.00  cnf(c_2,plain,
% 11.88/2.00      ( r1_tarski(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) ),
% 11.88/2.00      inference(cnf_transformation,[],[f60]) ).
% 11.88/2.00  
% 11.88/2.00  cnf(c_669,plain,
% 11.88/2.00      ( r1_tarski(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) = iProver_top ),
% 11.88/2.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 11.88/2.00  
% 11.88/2.00  cnf(c_975,plain,
% 11.88/2.00      ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) = iProver_top ),
% 11.88/2.00      inference(superposition,[status(thm)],[c_3,c_669]) ).
% 11.88/2.00  
% 11.88/2.00  cnf(c_14,plain,
% 11.88/2.00      ( ~ r1_tarski(X0,X1) | r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ),
% 11.88/2.00      inference(cnf_transformation,[],[f53]) ).
% 11.88/2.00  
% 11.88/2.00  cnf(c_659,plain,
% 11.88/2.00      ( r1_tarski(X0,X1) != iProver_top
% 11.88/2.00      | r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = iProver_top ),
% 11.88/2.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 11.88/2.00  
% 11.88/2.00  cnf(c_0,plain,
% 11.88/2.00      ( ~ r1_tarski(X0,X1) | r1_tarski(k3_xboole_0(X0,X2),X1) ),
% 11.88/2.00      inference(cnf_transformation,[],[f32]) ).
% 11.88/2.00  
% 11.88/2.00  cnf(c_671,plain,
% 11.88/2.00      ( r1_tarski(X0,X1) != iProver_top
% 11.88/2.00      | r1_tarski(k3_xboole_0(X0,X2),X1) = iProver_top ),
% 11.88/2.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 11.88/2.00  
% 11.88/2.00  cnf(c_1,plain,
% 11.88/2.00      ( ~ r1_tarski(X0,X1)
% 11.88/2.00      | ~ r1_tarski(X2,X1)
% 11.88/2.00      | r1_tarski(k5_xboole_0(X0,X2),X1) ),
% 11.88/2.00      inference(cnf_transformation,[],[f33]) ).
% 11.88/2.00  
% 11.88/2.00  cnf(c_670,plain,
% 11.88/2.00      ( r1_tarski(X0,X1) != iProver_top
% 11.88/2.00      | r1_tarski(X2,X1) != iProver_top
% 11.88/2.00      | r1_tarski(k5_xboole_0(X0,X2),X1) = iProver_top ),
% 11.88/2.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 11.88/2.00  
% 11.88/2.00  cnf(c_15,negated_conjecture,
% 11.88/2.00      ( ~ r1_tarski(k5_xboole_0(k5_xboole_0(k1_zfmisc_1(sK1),k1_zfmisc_1(sK2)),k3_xboole_0(k1_zfmisc_1(sK1),k1_zfmisc_1(sK2))),k1_zfmisc_1(k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)))) ),
% 11.88/2.00      inference(cnf_transformation,[],[f70]) ).
% 11.88/2.00  
% 11.88/2.00  cnf(c_658,plain,
% 11.88/2.00      ( r1_tarski(k5_xboole_0(k5_xboole_0(k1_zfmisc_1(sK1),k1_zfmisc_1(sK2)),k3_xboole_0(k1_zfmisc_1(sK1),k1_zfmisc_1(sK2))),k1_zfmisc_1(k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)))) != iProver_top ),
% 11.88/2.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 11.88/2.00  
% 11.88/2.00  cnf(c_773,plain,
% 11.88/2.00      ( r1_tarski(k5_xboole_0(k1_zfmisc_1(sK1),k5_xboole_0(k1_zfmisc_1(sK2),k3_xboole_0(k1_zfmisc_1(sK1),k1_zfmisc_1(sK2)))),k1_zfmisc_1(k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)))) != iProver_top ),
% 11.88/2.00      inference(demodulation,[status(thm)],[c_3,c_658]) ).
% 11.88/2.00  
% 11.88/2.00  cnf(c_875,plain,
% 11.88/2.00      ( r1_tarski(k5_xboole_0(k1_zfmisc_1(sK1),k5_xboole_0(k1_zfmisc_1(sK2),k3_xboole_0(k1_zfmisc_1(sK1),k1_zfmisc_1(sK2)))),k1_zfmisc_1(k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK1,sK2))))) != iProver_top ),
% 11.88/2.00      inference(superposition,[status(thm)],[c_3,c_773]) ).
% 11.88/2.00  
% 11.88/2.00  cnf(c_2310,plain,
% 11.88/2.00      ( r1_tarski(k5_xboole_0(k1_zfmisc_1(sK2),k3_xboole_0(k1_zfmisc_1(sK1),k1_zfmisc_1(sK2))),k1_zfmisc_1(k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK1,sK2))))) != iProver_top
% 11.88/2.00      | r1_tarski(k1_zfmisc_1(sK1),k1_zfmisc_1(k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK1,sK2))))) != iProver_top ),
% 11.88/2.00      inference(superposition,[status(thm)],[c_670,c_875]) ).
% 11.88/2.00  
% 11.88/2.00  cnf(c_2826,plain,
% 11.88/2.00      ( r1_tarski(k3_xboole_0(k1_zfmisc_1(sK1),k1_zfmisc_1(sK2)),k1_zfmisc_1(k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK1,sK2))))) != iProver_top
% 11.88/2.00      | r1_tarski(k1_zfmisc_1(sK2),k1_zfmisc_1(k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK1,sK2))))) != iProver_top
% 11.88/2.00      | r1_tarski(k1_zfmisc_1(sK1),k1_zfmisc_1(k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK1,sK2))))) != iProver_top ),
% 11.88/2.00      inference(superposition,[status(thm)],[c_670,c_2310]) ).
% 11.88/2.00  
% 11.88/2.00  cnf(c_3061,plain,
% 11.88/2.00      ( r1_tarski(k1_zfmisc_1(sK2),k1_zfmisc_1(k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK1,sK2))))) != iProver_top
% 11.88/2.00      | r1_tarski(k1_zfmisc_1(sK1),k1_zfmisc_1(k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK1,sK2))))) != iProver_top ),
% 11.88/2.00      inference(superposition,[status(thm)],[c_671,c_2826]) ).
% 11.88/2.00  
% 11.88/2.00  cnf(c_3490,plain,
% 11.88/2.00      ( r1_tarski(k1_zfmisc_1(sK2),k1_zfmisc_1(k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK1,sK2))))) != iProver_top
% 11.88/2.00      | r1_tarski(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK1,sK2)))) != iProver_top ),
% 11.88/2.00      inference(superposition,[status(thm)],[c_659,c_3061]) ).
% 11.88/2.00  
% 11.88/2.00  cnf(c_3493,plain,
% 11.88/2.00      ( r1_tarski(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK1,sK2)))) != iProver_top
% 11.88/2.00      | r1_tarski(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK1,sK2)))) != iProver_top ),
% 11.88/2.00      inference(superposition,[status(thm)],[c_659,c_3490]) ).
% 11.88/2.00  
% 11.88/2.00  cnf(c_3633,plain,
% 11.88/2.00      ( r1_tarski(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK1,sK2)))) != iProver_top ),
% 11.88/2.00      inference(superposition,[status(thm)],[c_975,c_3493]) ).
% 11.88/2.00  
% 11.88/2.00  cnf(c_29774,plain,
% 11.88/2.00      ( $false ),
% 11.88/2.00      inference(superposition,[status(thm)],[c_29742,c_3633]) ).
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
% 11.88/2.00  parsing_time:                           0.013
% 11.88/2.00  unif_index_cands_time:                  0.
% 11.88/2.00  unif_index_add_time:                    0.
% 11.88/2.00  orderings_time:                         0.
% 11.88/2.00  out_proof_time:                         0.007
% 11.88/2.00  total_time:                             1.433
% 11.88/2.00  num_of_symbols:                         41
% 11.88/2.00  num_of_terms:                           80427
% 11.88/2.00  
% 11.88/2.00  ------ Preprocessing
% 11.88/2.00  
% 11.88/2.00  num_of_splits:                          0
% 11.88/2.00  num_of_split_atoms:                     0
% 11.88/2.00  num_of_reused_defs:                     0
% 11.88/2.00  num_eq_ax_congr_red:                    24
% 11.88/2.00  num_of_sem_filtered_clauses:            1
% 11.88/2.00  num_of_subtypes:                        0
% 11.88/2.00  monotx_restored_types:                  0
% 11.88/2.00  sat_num_of_epr_types:                   0
% 11.88/2.00  sat_num_of_non_cyclic_types:            0
% 11.88/2.00  sat_guarded_non_collapsed_types:        0
% 11.88/2.00  num_pure_diseq_elim:                    0
% 11.88/2.00  simp_replaced_by:                       0
% 11.88/2.00  res_preprocessed:                       65
% 11.88/2.00  prep_upred:                             0
% 11.88/2.00  prep_unflattend:                        22
% 11.88/2.00  smt_new_axioms:                         0
% 11.88/2.00  pred_elim_cands:                        2
% 11.88/2.00  pred_elim:                              0
% 11.88/2.00  pred_elim_cl:                           0
% 11.88/2.00  pred_elim_cycles:                       1
% 11.88/2.00  merged_defs:                            0
% 11.88/2.00  merged_defs_ncl:                        0
% 11.88/2.00  bin_hyper_res:                          0
% 11.88/2.00  prep_cycles:                            3
% 11.88/2.00  pred_elim_time:                         0.009
% 11.88/2.00  splitting_time:                         0.
% 11.88/2.00  sem_filter_time:                        0.
% 11.88/2.00  monotx_time:                            0.001
% 11.88/2.00  subtype_inf_time:                       0.
% 11.88/2.00  
% 11.88/2.00  ------ Problem properties
% 11.88/2.00  
% 11.88/2.00  clauses:                                16
% 11.88/2.00  conjectures:                            1
% 11.88/2.00  epr:                                    0
% 11.88/2.00  horn:                                   14
% 11.88/2.00  ground:                                 1
% 11.88/2.00  unary:                                  7
% 11.88/2.00  binary:                                 3
% 11.88/2.00  lits:                                   34
% 11.88/2.00  lits_eq:                                15
% 11.88/2.00  fd_pure:                                0
% 11.88/2.00  fd_pseudo:                              0
% 11.88/2.00  fd_cond:                                0
% 11.88/2.00  fd_pseudo_cond:                         4
% 11.88/2.00  ac_symbols:                             0
% 11.88/2.00  
% 11.88/2.00  ------ Propositional Solver
% 11.88/2.00  
% 11.88/2.00  prop_solver_calls:                      25
% 11.88/2.00  prop_fast_solver_calls:                 468
% 11.88/2.00  smt_solver_calls:                       0
% 11.88/2.00  smt_fast_solver_calls:                  0
% 11.88/2.00  prop_num_of_clauses:                    13968
% 11.88/2.00  prop_preprocess_simplified:             8763
% 11.88/2.00  prop_fo_subsumed:                       0
% 11.88/2.00  prop_solver_time:                       0.
% 11.88/2.00  smt_solver_time:                        0.
% 11.88/2.00  smt_fast_solver_time:                   0.
% 11.88/2.00  prop_fast_solver_time:                  0.
% 11.88/2.00  prop_unsat_core_time:                   0.
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
% 11.88/2.00  inst_num_of_clauses:                    1072
% 11.88/2.00  inst_num_in_passive:                    344
% 11.88/2.00  inst_num_in_active:                     414
% 11.88/2.00  inst_num_in_unprocessed:                314
% 11.88/2.00  inst_num_of_loops:                      440
% 11.88/2.00  inst_num_of_learning_restarts:          0
% 11.88/2.00  inst_num_moves_active_passive:          25
% 11.88/2.00  inst_lit_activity:                      0
% 11.88/2.00  inst_lit_activity_moves:                0
% 11.88/2.00  inst_num_tautologies:                   0
% 11.88/2.00  inst_num_prop_implied:                  0
% 11.88/2.00  inst_num_existing_simplified:           0
% 11.88/2.00  inst_num_eq_res_simplified:             0
% 11.88/2.00  inst_num_child_elim:                    0
% 11.88/2.00  inst_num_of_dismatching_blockings:      1314
% 11.88/2.00  inst_num_of_non_proper_insts:           1288
% 11.88/2.00  inst_num_of_duplicates:                 0
% 11.88/2.00  inst_inst_num_from_inst_to_res:         0
% 11.88/2.00  inst_dismatching_checking_time:         0.
% 11.88/2.00  
% 11.88/2.00  ------ Resolution
% 11.88/2.00  
% 11.88/2.00  res_num_of_clauses:                     0
% 11.88/2.00  res_num_in_passive:                     0
% 11.88/2.00  res_num_in_active:                      0
% 11.88/2.00  res_num_of_loops:                       68
% 11.88/2.00  res_forward_subset_subsumed:            687
% 11.88/2.00  res_backward_subset_subsumed:           2
% 11.88/2.00  res_forward_subsumed:                   0
% 11.88/2.00  res_backward_subsumed:                  0
% 11.88/2.00  res_forward_subsumption_resolution:     0
% 11.88/2.00  res_backward_subsumption_resolution:    0
% 11.88/2.00  res_clause_to_clause_subsumption:       22925
% 11.88/2.00  res_orphan_elimination:                 0
% 11.88/2.00  res_tautology_del:                      23
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
% 11.88/2.00  sup_num_of_clauses:                     3006
% 11.88/2.00  sup_num_in_active:                      75
% 11.88/2.00  sup_num_in_passive:                     2931
% 11.88/2.00  sup_num_of_loops:                       87
% 11.88/2.00  sup_fw_superposition:                   3612
% 11.88/2.00  sup_bw_superposition:                   4328
% 11.88/2.00  sup_immediate_simplified:               3752
% 11.88/2.00  sup_given_eliminated:                   6
% 11.88/2.00  comparisons_done:                       0
% 11.88/2.00  comparisons_avoided:                    0
% 11.88/2.00  
% 11.88/2.00  ------ Simplifications
% 11.88/2.00  
% 11.88/2.00  
% 11.88/2.00  sim_fw_subset_subsumed:                 0
% 11.88/2.00  sim_bw_subset_subsumed:                 2
% 11.88/2.00  sim_fw_subsumed:                        313
% 11.88/2.00  sim_bw_subsumed:                        67
% 11.88/2.00  sim_fw_subsumption_res:                 0
% 11.88/2.00  sim_bw_subsumption_res:                 0
% 11.88/2.00  sim_tautology_del:                      0
% 11.88/2.00  sim_eq_tautology_del:                   179
% 11.88/2.00  sim_eq_res_simp:                        0
% 11.88/2.00  sim_fw_demodulated:                     4787
% 11.88/2.00  sim_bw_demodulated:                     460
% 11.88/2.00  sim_light_normalised:                   530
% 11.88/2.00  sim_joinable_taut:                      0
% 11.88/2.00  sim_joinable_simp:                      0
% 11.88/2.00  sim_ac_normalised:                      0
% 11.88/2.00  sim_smt_subsumption:                    0
% 11.88/2.00  
%------------------------------------------------------------------------------
