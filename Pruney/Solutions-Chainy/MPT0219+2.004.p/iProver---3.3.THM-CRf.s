%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:29:09 EST 2020

% Result     : Theorem 3.30s
% Output     : CNFRefutation 3.30s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 190 expanded)
%              Number of clauses        :   26 (  29 expanded)
%              Number of leaves         :   16 (  55 expanded)
%              Depth                    :   10
%              Number of atoms          :  172 ( 411 expanded)
%              Number of equality atoms :   92 ( 271 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f44])).

fof(f46,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK3(X0,X1) != X0
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( sK3(X0,X1) = X0
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK3(X0,X1) != X0
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( sK3(X0,X1) = X0
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f45,f46])).

fof(f83,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f15,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f86,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f87,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f88,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f89,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f18])).

fof(f93,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f88,f89])).

fof(f94,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f87,f93])).

fof(f95,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f86,f94])).

fof(f116,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k3_enumset1(X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f83,f95])).

fof(f131,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k3_enumset1(X3,X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f116])).

fof(f132,plain,(
    ! [X3] : r2_hidden(X3,k3_enumset1(X3,X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f131])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f27])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f19,conjecture,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f19])).

fof(f26,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f48,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) )
   => ( sK4 != sK5
      & k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)) = k1_tarski(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( sK4 != sK5
    & k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)) = k1_tarski(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f26,f48])).

fof(f90,plain,(
    k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)) = k1_tarski(sK4) ),
    inference(cnf_transformation,[],[f49])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f92,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f73,f69])).

fof(f118,plain,(
    k5_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_enumset1(sK5,sK5,sK5,sK5,sK5),k3_xboole_0(k3_enumset1(sK5,sK5,sK5,sK5,sK5),k3_enumset1(sK4,sK4,sK4,sK4,sK4)))) = k3_enumset1(sK4,sK4,sK4,sK4,sK4) ),
    inference(definition_unfolding,[],[f90,f92,f95,f95,f95])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f96,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f50,f92,f92])).

fof(f11,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f105,plain,(
    ! [X0,X1] : r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f72,f92])).

fof(f82,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f117,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k3_enumset1(X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f82,f95])).

fof(f133,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k3_enumset1(X0,X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f117])).

fof(f91,plain,(
    sK4 != sK5 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_32,plain,
    ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f132])).

cnf(c_5447,plain,
    ( r2_hidden(sK5,k3_enumset1(sK5,sK5,sK5,sK5,sK5)) ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2578,plain,
    ( ~ r2_hidden(sK5,X0)
    | r2_hidden(sK5,k3_enumset1(X1,X1,X1,X2,X3))
    | ~ r1_tarski(X0,k3_enumset1(X1,X1,X1,X2,X3)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_5446,plain,
    ( r2_hidden(sK5,k3_enumset1(X0,X0,X0,X1,X2))
    | ~ r2_hidden(sK5,k3_enumset1(sK5,sK5,sK5,sK5,sK5))
    | ~ r1_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK5),k3_enumset1(X0,X0,X0,X1,X2)) ),
    inference(instantiation,[status(thm)],[c_2578])).

cnf(c_5449,plain,
    ( ~ r2_hidden(sK5,k3_enumset1(sK5,sK5,sK5,sK5,sK5))
    | r2_hidden(sK5,k3_enumset1(sK4,sK4,sK4,sK4,sK4))
    | ~ r1_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK5),k3_enumset1(sK4,sK4,sK4,sK4,sK4)) ),
    inference(instantiation,[status(thm)],[c_5446])).

cnf(c_1,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_35,negated_conjecture,
    ( k5_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_enumset1(sK5,sK5,sK5,sK5,sK5),k3_xboole_0(k3_enumset1(sK5,sK5,sK5,sK5,sK5),k3_enumset1(sK4,sK4,sK4,sK4,sK4)))) = k3_enumset1(sK4,sK4,sK4,sK4,sK4) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_1303,plain,
    ( k5_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_enumset1(sK5,sK5,sK5,sK5,sK5),k3_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k3_enumset1(sK5,sK5,sK5,sK5,sK5)))) = k3_enumset1(sK4,sK4,sK4,sK4,sK4) ),
    inference(demodulation,[status(thm)],[c_1,c_35])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_21,plain,
    ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1009,plain,
    ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1914,plain,
    ( r1_tarski(X0,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_1009])).

cnf(c_2271,plain,
    ( r1_tarski(X0,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X1,X0)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_1914])).

cnf(c_2388,plain,
    ( r1_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK5),k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1303,c_2271])).

cnf(c_2395,plain,
    ( r1_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK5),k3_enumset1(sK4,sK4,sK4,sK4,sK4)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2388])).

cnf(c_33,plain,
    ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f133])).

cnf(c_1404,plain,
    ( ~ r2_hidden(sK5,k3_enumset1(X0,X0,X0,X0,X0))
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_1406,plain,
    ( ~ r2_hidden(sK5,k3_enumset1(sK4,sK4,sK4,sK4,sK4))
    | sK5 = sK4 ),
    inference(instantiation,[status(thm)],[c_1404])).

cnf(c_510,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1274,plain,
    ( sK5 != X0
    | sK4 != X0
    | sK4 = sK5 ),
    inference(instantiation,[status(thm)],[c_510])).

cnf(c_1275,plain,
    ( sK5 != sK4
    | sK4 = sK5
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1274])).

cnf(c_40,plain,
    ( r2_hidden(sK4,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_37,plain,
    ( ~ r2_hidden(sK4,k3_enumset1(sK4,sK4,sK4,sK4,sK4))
    | sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_34,negated_conjecture,
    ( sK4 != sK5 ),
    inference(cnf_transformation,[],[f91])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5447,c_5449,c_2395,c_1406,c_1275,c_40,c_37,c_34])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:54:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.30/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.30/1.00  
% 3.30/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.30/1.00  
% 3.30/1.00  ------  iProver source info
% 3.30/1.00  
% 3.30/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.30/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.30/1.00  git: non_committed_changes: false
% 3.30/1.00  git: last_make_outside_of_git: false
% 3.30/1.00  
% 3.30/1.00  ------ 
% 3.30/1.00  ------ Parsing...
% 3.30/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.30/1.00  
% 3.30/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.30/1.00  
% 3.30/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.30/1.00  
% 3.30/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.30/1.00  ------ Proving...
% 3.30/1.00  ------ Problem Properties 
% 3.30/1.00  
% 3.30/1.00  
% 3.30/1.00  clauses                                 35
% 3.30/1.00  conjectures                             2
% 3.30/1.00  EPR                                     4
% 3.30/1.00  Horn                                    24
% 3.30/1.00  unary                                   12
% 3.30/1.00  binary                                  6
% 3.30/1.00  lits                                    79
% 3.30/1.00  lits eq                                 29
% 3.30/1.01  fd_pure                                 0
% 3.30/1.01  fd_pseudo                               0
% 3.30/1.01  fd_cond                                 0
% 3.30/1.01  fd_pseudo_cond                          10
% 3.30/1.01  AC symbols                              0
% 3.30/1.01  
% 3.30/1.01  ------ Input Options Time Limit: Unbounded
% 3.30/1.01  
% 3.30/1.01  
% 3.30/1.01  ------ 
% 3.30/1.01  Current options:
% 3.30/1.01  ------ 
% 3.30/1.01  
% 3.30/1.01  
% 3.30/1.01  
% 3.30/1.01  
% 3.30/1.01  ------ Proving...
% 3.30/1.01  
% 3.30/1.01  
% 3.30/1.01  % SZS status Theorem for theBenchmark.p
% 3.30/1.01  
% 3.30/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.30/1.01  
% 3.30/1.01  fof(f14,axiom,(
% 3.30/1.01    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 3.30/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.30/1.01  
% 3.30/1.01  fof(f44,plain,(
% 3.30/1.01    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 3.30/1.01    inference(nnf_transformation,[],[f14])).
% 3.30/1.01  
% 3.30/1.01  fof(f45,plain,(
% 3.30/1.01    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.30/1.01    inference(rectify,[],[f44])).
% 3.30/1.01  
% 3.30/1.01  fof(f46,plain,(
% 3.30/1.01    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1))))),
% 3.30/1.01    introduced(choice_axiom,[])).
% 3.30/1.01  
% 3.30/1.01  fof(f47,plain,(
% 3.30/1.01    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.30/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f45,f46])).
% 3.30/1.01  
% 3.30/1.01  fof(f83,plain,(
% 3.30/1.01    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 3.30/1.01    inference(cnf_transformation,[],[f47])).
% 3.30/1.01  
% 3.30/1.01  fof(f15,axiom,(
% 3.30/1.01    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.30/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.30/1.01  
% 3.30/1.01  fof(f86,plain,(
% 3.30/1.01    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.30/1.01    inference(cnf_transformation,[],[f15])).
% 3.30/1.01  
% 3.30/1.01  fof(f16,axiom,(
% 3.30/1.01    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.30/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.30/1.01  
% 3.30/1.01  fof(f87,plain,(
% 3.30/1.01    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.30/1.01    inference(cnf_transformation,[],[f16])).
% 3.30/1.01  
% 3.30/1.01  fof(f17,axiom,(
% 3.30/1.01    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.30/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.30/1.01  
% 3.30/1.01  fof(f88,plain,(
% 3.30/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.30/1.01    inference(cnf_transformation,[],[f17])).
% 3.30/1.01  
% 3.30/1.01  fof(f18,axiom,(
% 3.30/1.01    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.30/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.30/1.01  
% 3.30/1.01  fof(f89,plain,(
% 3.30/1.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.30/1.01    inference(cnf_transformation,[],[f18])).
% 3.30/1.01  
% 3.30/1.01  fof(f93,plain,(
% 3.30/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 3.30/1.01    inference(definition_unfolding,[],[f88,f89])).
% 3.30/1.01  
% 3.30/1.01  fof(f94,plain,(
% 3.30/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 3.30/1.01    inference(definition_unfolding,[],[f87,f93])).
% 3.30/1.01  
% 3.30/1.01  fof(f95,plain,(
% 3.30/1.01    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 3.30/1.01    inference(definition_unfolding,[],[f86,f94])).
% 3.30/1.01  
% 3.30/1.01  fof(f116,plain,(
% 3.30/1.01    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k3_enumset1(X0,X0,X0,X0,X0) != X1) )),
% 3.30/1.01    inference(definition_unfolding,[],[f83,f95])).
% 3.30/1.01  
% 3.30/1.01  fof(f131,plain,(
% 3.30/1.01    ( ! [X3,X1] : (r2_hidden(X3,X1) | k3_enumset1(X3,X3,X3,X3,X3) != X1) )),
% 3.30/1.01    inference(equality_resolution,[],[f116])).
% 3.30/1.01  
% 3.30/1.01  fof(f132,plain,(
% 3.30/1.01    ( ! [X3] : (r2_hidden(X3,k3_enumset1(X3,X3,X3,X3,X3))) )),
% 3.30/1.01    inference(equality_resolution,[],[f131])).
% 3.30/1.01  
% 3.30/1.01  fof(f3,axiom,(
% 3.30/1.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.30/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.30/1.01  
% 3.30/1.01  fof(f22,plain,(
% 3.30/1.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.30/1.01    inference(ennf_transformation,[],[f3])).
% 3.30/1.01  
% 3.30/1.01  fof(f27,plain,(
% 3.30/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.30/1.01    inference(nnf_transformation,[],[f22])).
% 3.30/1.01  
% 3.30/1.01  fof(f28,plain,(
% 3.30/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.30/1.01    inference(rectify,[],[f27])).
% 3.30/1.01  
% 3.30/1.01  fof(f29,plain,(
% 3.30/1.01    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.30/1.01    introduced(choice_axiom,[])).
% 3.30/1.01  
% 3.30/1.01  fof(f30,plain,(
% 3.30/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.30/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).
% 3.30/1.01  
% 3.30/1.01  fof(f52,plain,(
% 3.30/1.01    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.30/1.01    inference(cnf_transformation,[],[f30])).
% 3.30/1.01  
% 3.30/1.01  fof(f2,axiom,(
% 3.30/1.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.30/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.30/1.01  
% 3.30/1.01  fof(f51,plain,(
% 3.30/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.30/1.01    inference(cnf_transformation,[],[f2])).
% 3.30/1.01  
% 3.30/1.01  fof(f19,conjecture,(
% 3.30/1.01    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) => X0 = X1)),
% 3.30/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.30/1.01  
% 3.30/1.01  fof(f20,negated_conjecture,(
% 3.30/1.01    ~! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) => X0 = X1)),
% 3.30/1.01    inference(negated_conjecture,[],[f19])).
% 3.30/1.01  
% 3.30/1.01  fof(f26,plain,(
% 3.30/1.01    ? [X0,X1] : (X0 != X1 & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0))),
% 3.30/1.01    inference(ennf_transformation,[],[f20])).
% 3.30/1.01  
% 3.30/1.01  fof(f48,plain,(
% 3.30/1.01    ? [X0,X1] : (X0 != X1 & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)) => (sK4 != sK5 & k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)) = k1_tarski(sK4))),
% 3.30/1.01    introduced(choice_axiom,[])).
% 3.30/1.01  
% 3.30/1.01  fof(f49,plain,(
% 3.30/1.01    sK4 != sK5 & k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)) = k1_tarski(sK4)),
% 3.30/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f26,f48])).
% 3.30/1.01  
% 3.30/1.01  fof(f90,plain,(
% 3.30/1.01    k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)) = k1_tarski(sK4)),
% 3.30/1.01    inference(cnf_transformation,[],[f49])).
% 3.30/1.01  
% 3.30/1.01  fof(f12,axiom,(
% 3.30/1.01    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.30/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.30/1.01  
% 3.30/1.01  fof(f73,plain,(
% 3.30/1.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.30/1.01    inference(cnf_transformation,[],[f12])).
% 3.30/1.01  
% 3.30/1.01  fof(f8,axiom,(
% 3.30/1.01    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.30/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.30/1.01  
% 3.30/1.01  fof(f69,plain,(
% 3.30/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.30/1.01    inference(cnf_transformation,[],[f8])).
% 3.30/1.01  
% 3.30/1.01  fof(f92,plain,(
% 3.30/1.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 3.30/1.01    inference(definition_unfolding,[],[f73,f69])).
% 3.30/1.01  
% 3.30/1.01  fof(f118,plain,(
% 3.30/1.01    k5_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_enumset1(sK5,sK5,sK5,sK5,sK5),k3_xboole_0(k3_enumset1(sK5,sK5,sK5,sK5,sK5),k3_enumset1(sK4,sK4,sK4,sK4,sK4)))) = k3_enumset1(sK4,sK4,sK4,sK4,sK4)),
% 3.30/1.01    inference(definition_unfolding,[],[f90,f92,f95,f95,f95])).
% 3.30/1.01  
% 3.30/1.01  fof(f1,axiom,(
% 3.30/1.01    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 3.30/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.30/1.01  
% 3.30/1.01  fof(f50,plain,(
% 3.30/1.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 3.30/1.01    inference(cnf_transformation,[],[f1])).
% 3.30/1.01  
% 3.30/1.01  fof(f96,plain,(
% 3.30/1.01    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 3.30/1.01    inference(definition_unfolding,[],[f50,f92,f92])).
% 3.30/1.01  
% 3.30/1.01  fof(f11,axiom,(
% 3.30/1.01    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 3.30/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.30/1.01  
% 3.30/1.01  fof(f72,plain,(
% 3.30/1.01    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.30/1.01    inference(cnf_transformation,[],[f11])).
% 3.30/1.01  
% 3.30/1.01  fof(f105,plain,(
% 3.30/1.01    ( ! [X0,X1] : (r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 3.30/1.01    inference(definition_unfolding,[],[f72,f92])).
% 3.30/1.01  
% 3.30/1.01  fof(f82,plain,(
% 3.30/1.01    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 3.30/1.01    inference(cnf_transformation,[],[f47])).
% 3.30/1.01  
% 3.30/1.01  fof(f117,plain,(
% 3.30/1.01    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k3_enumset1(X0,X0,X0,X0,X0) != X1) )),
% 3.30/1.01    inference(definition_unfolding,[],[f82,f95])).
% 3.30/1.01  
% 3.30/1.01  fof(f133,plain,(
% 3.30/1.01    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k3_enumset1(X0,X0,X0,X0,X0))) )),
% 3.30/1.01    inference(equality_resolution,[],[f117])).
% 3.30/1.01  
% 3.30/1.01  fof(f91,plain,(
% 3.30/1.01    sK4 != sK5),
% 3.30/1.01    inference(cnf_transformation,[],[f49])).
% 3.30/1.01  
% 3.30/1.01  cnf(c_32,plain,
% 3.30/1.01      ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0)) ),
% 3.30/1.01      inference(cnf_transformation,[],[f132]) ).
% 3.30/1.01  
% 3.30/1.01  cnf(c_5447,plain,
% 3.30/1.01      ( r2_hidden(sK5,k3_enumset1(sK5,sK5,sK5,sK5,sK5)) ),
% 3.30/1.01      inference(instantiation,[status(thm)],[c_32]) ).
% 3.30/1.01  
% 3.30/1.01  cnf(c_4,plain,
% 3.30/1.01      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 3.30/1.01      inference(cnf_transformation,[],[f52]) ).
% 3.30/1.01  
% 3.30/1.01  cnf(c_2578,plain,
% 3.30/1.01      ( ~ r2_hidden(sK5,X0)
% 3.30/1.01      | r2_hidden(sK5,k3_enumset1(X1,X1,X1,X2,X3))
% 3.30/1.01      | ~ r1_tarski(X0,k3_enumset1(X1,X1,X1,X2,X3)) ),
% 3.30/1.01      inference(instantiation,[status(thm)],[c_4]) ).
% 3.30/1.01  
% 3.30/1.01  cnf(c_5446,plain,
% 3.30/1.01      ( r2_hidden(sK5,k3_enumset1(X0,X0,X0,X1,X2))
% 3.30/1.01      | ~ r2_hidden(sK5,k3_enumset1(sK5,sK5,sK5,sK5,sK5))
% 3.30/1.01      | ~ r1_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK5),k3_enumset1(X0,X0,X0,X1,X2)) ),
% 3.30/1.01      inference(instantiation,[status(thm)],[c_2578]) ).
% 3.30/1.01  
% 3.30/1.01  cnf(c_5449,plain,
% 3.30/1.01      ( ~ r2_hidden(sK5,k3_enumset1(sK5,sK5,sK5,sK5,sK5))
% 3.30/1.01      | r2_hidden(sK5,k3_enumset1(sK4,sK4,sK4,sK4,sK4))
% 3.30/1.01      | ~ r1_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK5),k3_enumset1(sK4,sK4,sK4,sK4,sK4)) ),
% 3.30/1.01      inference(instantiation,[status(thm)],[c_5446]) ).
% 3.30/1.01  
% 3.30/1.01  cnf(c_1,plain,
% 3.30/1.01      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 3.30/1.01      inference(cnf_transformation,[],[f51]) ).
% 3.30/1.01  
% 3.30/1.01  cnf(c_35,negated_conjecture,
% 3.30/1.01      ( k5_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_enumset1(sK5,sK5,sK5,sK5,sK5),k3_xboole_0(k3_enumset1(sK5,sK5,sK5,sK5,sK5),k3_enumset1(sK4,sK4,sK4,sK4,sK4)))) = k3_enumset1(sK4,sK4,sK4,sK4,sK4) ),
% 3.30/1.01      inference(cnf_transformation,[],[f118]) ).
% 3.30/1.01  
% 3.30/1.01  cnf(c_1303,plain,
% 3.30/1.01      ( k5_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_enumset1(sK5,sK5,sK5,sK5,sK5),k3_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k3_enumset1(sK5,sK5,sK5,sK5,sK5)))) = k3_enumset1(sK4,sK4,sK4,sK4,sK4) ),
% 3.30/1.01      inference(demodulation,[status(thm)],[c_1,c_35]) ).
% 3.30/1.01  
% 3.30/1.01  cnf(c_0,plain,
% 3.30/1.01      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
% 3.30/1.01      inference(cnf_transformation,[],[f96]) ).
% 3.30/1.01  
% 3.30/1.01  cnf(c_21,plain,
% 3.30/1.01      ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
% 3.30/1.01      inference(cnf_transformation,[],[f105]) ).
% 3.30/1.01  
% 3.30/1.01  cnf(c_1009,plain,
% 3.30/1.01      ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = iProver_top ),
% 3.30/1.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.30/1.01  
% 3.30/1.01  cnf(c_1914,plain,
% 3.30/1.01      ( r1_tarski(X0,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = iProver_top ),
% 3.30/1.01      inference(superposition,[status(thm)],[c_0,c_1009]) ).
% 3.30/1.01  
% 3.30/1.01  cnf(c_2271,plain,
% 3.30/1.01      ( r1_tarski(X0,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X1,X0)))) = iProver_top ),
% 3.30/1.01      inference(superposition,[status(thm)],[c_1,c_1914]) ).
% 3.30/1.01  
% 3.30/1.01  cnf(c_2388,plain,
% 3.30/1.01      ( r1_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK5),k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
% 3.30/1.01      inference(superposition,[status(thm)],[c_1303,c_2271]) ).
% 3.30/1.01  
% 3.30/1.01  cnf(c_2395,plain,
% 3.30/1.01      ( r1_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK5),k3_enumset1(sK4,sK4,sK4,sK4,sK4)) ),
% 3.30/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_2388]) ).
% 3.30/1.01  
% 3.30/1.01  cnf(c_33,plain,
% 3.30/1.01      ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X1)) | X0 = X1 ),
% 3.30/1.01      inference(cnf_transformation,[],[f133]) ).
% 3.30/1.01  
% 3.30/1.01  cnf(c_1404,plain,
% 3.30/1.01      ( ~ r2_hidden(sK5,k3_enumset1(X0,X0,X0,X0,X0)) | sK5 = X0 ),
% 3.30/1.01      inference(instantiation,[status(thm)],[c_33]) ).
% 3.30/1.01  
% 3.30/1.01  cnf(c_1406,plain,
% 3.30/1.01      ( ~ r2_hidden(sK5,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) | sK5 = sK4 ),
% 3.30/1.01      inference(instantiation,[status(thm)],[c_1404]) ).
% 3.30/1.01  
% 3.30/1.01  cnf(c_510,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.30/1.01  
% 3.30/1.01  cnf(c_1274,plain,
% 3.30/1.01      ( sK5 != X0 | sK4 != X0 | sK4 = sK5 ),
% 3.30/1.01      inference(instantiation,[status(thm)],[c_510]) ).
% 3.30/1.01  
% 3.30/1.01  cnf(c_1275,plain,
% 3.30/1.01      ( sK5 != sK4 | sK4 = sK5 | sK4 != sK4 ),
% 3.30/1.01      inference(instantiation,[status(thm)],[c_1274]) ).
% 3.30/1.01  
% 3.30/1.01  cnf(c_40,plain,
% 3.30/1.01      ( r2_hidden(sK4,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) ),
% 3.30/1.01      inference(instantiation,[status(thm)],[c_32]) ).
% 3.30/1.01  
% 3.30/1.01  cnf(c_37,plain,
% 3.30/1.01      ( ~ r2_hidden(sK4,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) | sK4 = sK4 ),
% 3.30/1.01      inference(instantiation,[status(thm)],[c_33]) ).
% 3.30/1.01  
% 3.30/1.01  cnf(c_34,negated_conjecture,
% 3.30/1.01      ( sK4 != sK5 ),
% 3.30/1.01      inference(cnf_transformation,[],[f91]) ).
% 3.30/1.01  
% 3.30/1.01  cnf(contradiction,plain,
% 3.30/1.01      ( $false ),
% 3.30/1.01      inference(minisat,
% 3.30/1.01                [status(thm)],
% 3.30/1.01                [c_5447,c_5449,c_2395,c_1406,c_1275,c_40,c_37,c_34]) ).
% 3.30/1.01  
% 3.30/1.01  
% 3.30/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.30/1.01  
% 3.30/1.01  ------                               Statistics
% 3.30/1.01  
% 3.30/1.01  ------ Selected
% 3.30/1.01  
% 3.30/1.01  total_time:                             0.259
% 3.30/1.01  
%------------------------------------------------------------------------------
