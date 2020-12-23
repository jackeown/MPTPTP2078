%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:33:21 EST 2020

% Result     : Theorem 2.02s
% Output     : CNFRefutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 123 expanded)
%              Number of clauses        :   10 (  11 expanded)
%              Number of leaves         :   14 (  36 expanded)
%              Depth                    :   13
%              Number of atoms          :  191 ( 288 expanded)
%              Number of equality atoms :  101 ( 152 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f21,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f15,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f18])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f19])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f20])).

fof(f76,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f71,f72])).

fof(f77,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f70,f76])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f69,f77])).

fof(f79,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f68,f78])).

fof(f80,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f67,f79])).

fof(f81,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f73,f80])).

fof(f89,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f55,f81])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f22,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
     => r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
       => r2_hidden(X0,X2) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f40,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(X0,X2)
        & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) )
   => ( ~ r2_hidden(sK2,sK4)
      & r1_tarski(k2_xboole_0(k2_tarski(sK2,sK3),sK4),sK4) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ~ r2_hidden(sK2,sK4)
    & r1_tarski(k2_xboole_0(k2_tarski(sK2,sK3),sK4),sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f28,f40])).

fof(f74,plain,(
    r1_tarski(k2_xboole_0(k2_tarski(sK2,sK3),sK4),sK4) ),
    inference(cnf_transformation,[],[f41])).

fof(f99,plain,(
    r1_tarski(k3_tarski(k6_enumset1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)),sK4) ),
    inference(definition_unfolding,[],[f74,f81,f80])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f38,plain,(
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
     => ( ( ( sK1(X0,X1,X2,X3) != X2
            & sK1(X0,X1,X2,X3) != X1
            & sK1(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK1(X0,X1,X2,X3),X3) )
        & ( sK1(X0,X1,X2,X3) = X2
          | sK1(X0,X1,X2,X3) = X1
          | sK1(X0,X1,X2,X3) = X0
          | r2_hidden(sK1(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK1(X0,X1,X2,X3) != X2
              & sK1(X0,X1,X2,X3) != X1
              & sK1(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK1(X0,X1,X2,X3),X3) )
          & ( sK1(X0,X1,X2,X3) = X2
            | sK1(X0,X1,X2,X3) = X1
            | sK1(X0,X1,X2,X3) = X0
            | r2_hidden(sK1(X0,X1,X2,X3),X3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f37,f38])).

fof(f61,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f96,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f61,f79])).

fof(f104,plain,(
    ! [X2,X0,X5,X3] :
      ( r2_hidden(X5,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X5,X2) != X3 ) ),
    inference(equality_resolution,[],[f96])).

fof(f105,plain,(
    ! [X2,X0,X5] : r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X5,X2)) ),
    inference(equality_resolution,[],[f104])).

fof(f75,plain,(
    ~ r2_hidden(sK2,sK4) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_12,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1048,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
    inference(resolution,[status(thm)],[c_12,c_3])).

cnf(c_24,negated_conjecture,
    ( r1_tarski(k3_tarski(k6_enumset1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)),sK4) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_807,plain,
    ( ~ r2_hidden(X0,k3_tarski(k6_enumset1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)))
    | r2_hidden(X0,sK4) ),
    inference(resolution,[status(thm)],[c_3,c_24])).

cnf(c_1637,plain,
    ( ~ r2_hidden(X0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))
    | r2_hidden(X0,sK4) ),
    inference(resolution,[status(thm)],[c_1048,c_807])).

cnf(c_20,plain,
    ( r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X0,X2)) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1653,plain,
    ( r2_hidden(sK2,sK4) ),
    inference(resolution,[status(thm)],[c_1637,c_20])).

cnf(c_23,negated_conjecture,
    ( ~ r2_hidden(sK2,sK4) ),
    inference(cnf_transformation,[],[f75])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1653,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:49:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.02/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/0.99  
% 2.02/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.02/0.99  
% 2.02/0.99  ------  iProver source info
% 2.02/0.99  
% 2.02/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.02/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.02/0.99  git: non_committed_changes: false
% 2.02/0.99  git: last_make_outside_of_git: false
% 2.02/0.99  
% 2.02/0.99  ------ 
% 2.02/0.99  ------ Parsing...
% 2.02/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.02/0.99  
% 2.02/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.02/0.99  
% 2.02/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.02/0.99  
% 2.02/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.02/0.99  ------ Proving...
% 2.02/0.99  ------ Problem Properties 
% 2.02/0.99  
% 2.02/0.99  
% 2.02/0.99  clauses                                 24
% 2.02/0.99  conjectures                             2
% 2.02/0.99  EPR                                     4
% 2.02/0.99  Horn                                    21
% 2.02/0.99  unary                                   15
% 2.02/0.99  binary                                  2
% 2.02/0.99  lits                                    43
% 2.02/0.99  lits eq                                 21
% 2.02/0.99  fd_pure                                 0
% 2.02/0.99  fd_pseudo                               0
% 2.02/0.99  fd_cond                                 0
% 2.02/0.99  fd_pseudo_cond                          5
% 2.02/0.99  AC symbols                              1
% 2.02/0.99  
% 2.02/0.99  ------ Input Options Time Limit: Unbounded
% 2.02/0.99  
% 2.02/0.99  
% 2.02/0.99  ------ 
% 2.02/0.99  Current options:
% 2.02/0.99  ------ 
% 2.02/0.99  
% 2.02/0.99  
% 2.02/0.99  
% 2.02/0.99  
% 2.02/0.99  ------ Proving...
% 2.02/0.99  
% 2.02/0.99  
% 2.02/0.99  % SZS status Theorem for theBenchmark.p
% 2.02/0.99  
% 2.02/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.02/0.99  
% 2.02/0.99  fof(f10,axiom,(
% 2.02/0.99    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.02/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.02/0.99  
% 2.02/0.99  fof(f55,plain,(
% 2.02/0.99    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.02/0.99    inference(cnf_transformation,[],[f10])).
% 2.02/0.99  
% 2.02/0.99  fof(f21,axiom,(
% 2.02/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.02/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.02/0.99  
% 2.02/0.99  fof(f73,plain,(
% 2.02/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.02/0.99    inference(cnf_transformation,[],[f21])).
% 2.02/0.99  
% 2.02/0.99  fof(f15,axiom,(
% 2.02/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.02/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.02/0.99  
% 2.02/0.99  fof(f67,plain,(
% 2.02/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.02/0.99    inference(cnf_transformation,[],[f15])).
% 2.02/0.99  
% 2.02/0.99  fof(f16,axiom,(
% 2.02/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.02/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.02/0.99  
% 2.02/0.99  fof(f68,plain,(
% 2.02/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.02/0.99    inference(cnf_transformation,[],[f16])).
% 2.02/0.99  
% 2.02/0.99  fof(f17,axiom,(
% 2.02/0.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.02/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.02/0.99  
% 2.02/0.99  fof(f69,plain,(
% 2.02/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.02/0.99    inference(cnf_transformation,[],[f17])).
% 2.02/0.99  
% 2.02/0.99  fof(f18,axiom,(
% 2.02/0.99    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 2.02/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.02/0.99  
% 2.02/0.99  fof(f70,plain,(
% 2.02/0.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 2.02/0.99    inference(cnf_transformation,[],[f18])).
% 2.02/0.99  
% 2.02/0.99  fof(f19,axiom,(
% 2.02/0.99    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 2.02/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.02/0.99  
% 2.02/0.99  fof(f71,plain,(
% 2.02/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 2.02/0.99    inference(cnf_transformation,[],[f19])).
% 2.02/0.99  
% 2.02/0.99  fof(f20,axiom,(
% 2.02/0.99    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 2.02/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.02/0.99  
% 2.02/0.99  fof(f72,plain,(
% 2.02/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 2.02/0.99    inference(cnf_transformation,[],[f20])).
% 2.02/0.99  
% 2.02/0.99  fof(f76,plain,(
% 2.02/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.02/0.99    inference(definition_unfolding,[],[f71,f72])).
% 2.02/0.99  
% 2.02/0.99  fof(f77,plain,(
% 2.02/0.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.02/0.99    inference(definition_unfolding,[],[f70,f76])).
% 2.02/0.99  
% 2.02/0.99  fof(f78,plain,(
% 2.02/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.02/0.99    inference(definition_unfolding,[],[f69,f77])).
% 2.02/0.99  
% 2.02/0.99  fof(f79,plain,(
% 2.02/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.02/0.99    inference(definition_unfolding,[],[f68,f78])).
% 2.02/0.99  
% 2.02/0.99  fof(f80,plain,(
% 2.02/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.02/0.99    inference(definition_unfolding,[],[f67,f79])).
% 2.02/0.99  
% 2.02/0.99  fof(f81,plain,(
% 2.02/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 2.02/0.99    inference(definition_unfolding,[],[f73,f80])).
% 2.02/0.99  
% 2.02/0.99  fof(f89,plain,(
% 2.02/0.99    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 2.02/0.99    inference(definition_unfolding,[],[f55,f81])).
% 2.02/0.99  
% 2.02/0.99  fof(f2,axiom,(
% 2.02/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.02/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.02/0.99  
% 2.02/0.99  fof(f26,plain,(
% 2.02/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.02/0.99    inference(ennf_transformation,[],[f2])).
% 2.02/0.99  
% 2.02/0.99  fof(f29,plain,(
% 2.02/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.02/0.99    inference(nnf_transformation,[],[f26])).
% 2.02/0.99  
% 2.02/0.99  fof(f30,plain,(
% 2.02/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.02/0.99    inference(rectify,[],[f29])).
% 2.02/0.99  
% 2.02/0.99  fof(f31,plain,(
% 2.02/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.02/0.99    introduced(choice_axiom,[])).
% 2.02/0.99  
% 2.02/0.99  fof(f32,plain,(
% 2.02/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.02/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).
% 2.02/0.99  
% 2.02/0.99  fof(f43,plain,(
% 2.02/0.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 2.02/0.99    inference(cnf_transformation,[],[f32])).
% 2.02/0.99  
% 2.02/0.99  fof(f22,conjecture,(
% 2.02/0.99    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 2.02/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.02/0.99  
% 2.02/0.99  fof(f23,negated_conjecture,(
% 2.02/0.99    ~! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 2.02/0.99    inference(negated_conjecture,[],[f22])).
% 2.02/0.99  
% 2.02/0.99  fof(f28,plain,(
% 2.02/0.99    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2))),
% 2.02/0.99    inference(ennf_transformation,[],[f23])).
% 2.02/0.99  
% 2.02/0.99  fof(f40,plain,(
% 2.02/0.99    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)) => (~r2_hidden(sK2,sK4) & r1_tarski(k2_xboole_0(k2_tarski(sK2,sK3),sK4),sK4))),
% 2.02/0.99    introduced(choice_axiom,[])).
% 2.02/0.99  
% 2.02/0.99  fof(f41,plain,(
% 2.02/0.99    ~r2_hidden(sK2,sK4) & r1_tarski(k2_xboole_0(k2_tarski(sK2,sK3),sK4),sK4)),
% 2.02/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f28,f40])).
% 2.02/0.99  
% 2.02/0.99  fof(f74,plain,(
% 2.02/0.99    r1_tarski(k2_xboole_0(k2_tarski(sK2,sK3),sK4),sK4)),
% 2.02/0.99    inference(cnf_transformation,[],[f41])).
% 2.02/0.99  
% 2.02/0.99  fof(f99,plain,(
% 2.02/0.99    r1_tarski(k3_tarski(k6_enumset1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)),sK4)),
% 2.02/0.99    inference(definition_unfolding,[],[f74,f81,f80])).
% 2.02/0.99  
% 2.02/0.99  fof(f14,axiom,(
% 2.02/0.99    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 2.02/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.02/0.99  
% 2.02/0.99  fof(f27,plain,(
% 2.02/0.99    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 2.02/0.99    inference(ennf_transformation,[],[f14])).
% 2.02/0.99  
% 2.02/0.99  fof(f35,plain,(
% 2.02/0.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.02/0.99    inference(nnf_transformation,[],[f27])).
% 2.02/0.99  
% 2.02/0.99  fof(f36,plain,(
% 2.02/0.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.02/0.99    inference(flattening,[],[f35])).
% 2.02/0.99  
% 2.02/0.99  fof(f37,plain,(
% 2.02/0.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.02/0.99    inference(rectify,[],[f36])).
% 2.02/0.99  
% 2.02/0.99  fof(f38,plain,(
% 2.02/0.99    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3))))),
% 2.02/0.99    introduced(choice_axiom,[])).
% 2.02/0.99  
% 2.02/0.99  fof(f39,plain,(
% 2.02/0.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.02/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f37,f38])).
% 2.02/0.99  
% 2.02/0.99  fof(f61,plain,(
% 2.02/0.99    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 2.02/0.99    inference(cnf_transformation,[],[f39])).
% 2.02/0.99  
% 2.02/0.99  fof(f96,plain,(
% 2.02/0.99    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 2.02/0.99    inference(definition_unfolding,[],[f61,f79])).
% 2.02/0.99  
% 2.02/0.99  fof(f104,plain,(
% 2.02/0.99    ( ! [X2,X0,X5,X3] : (r2_hidden(X5,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X5,X2) != X3) )),
% 2.02/0.99    inference(equality_resolution,[],[f96])).
% 2.02/0.99  
% 2.02/0.99  fof(f105,plain,(
% 2.02/0.99    ( ! [X2,X0,X5] : (r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X5,X2))) )),
% 2.02/0.99    inference(equality_resolution,[],[f104])).
% 2.02/0.99  
% 2.02/0.99  fof(f75,plain,(
% 2.02/0.99    ~r2_hidden(sK2,sK4)),
% 2.02/0.99    inference(cnf_transformation,[],[f41])).
% 2.02/0.99  
% 2.02/0.99  cnf(c_12,plain,
% 2.02/0.99      ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
% 2.02/0.99      inference(cnf_transformation,[],[f89]) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_3,plain,
% 2.02/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 2.02/0.99      inference(cnf_transformation,[],[f43]) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_1048,plain,
% 2.02/0.99      ( ~ r2_hidden(X0,X1)
% 2.02/0.99      | r2_hidden(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
% 2.02/0.99      inference(resolution,[status(thm)],[c_12,c_3]) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_24,negated_conjecture,
% 2.02/0.99      ( r1_tarski(k3_tarski(k6_enumset1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)),sK4) ),
% 2.02/0.99      inference(cnf_transformation,[],[f99]) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_807,plain,
% 2.02/0.99      ( ~ r2_hidden(X0,k3_tarski(k6_enumset1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)))
% 2.02/0.99      | r2_hidden(X0,sK4) ),
% 2.02/0.99      inference(resolution,[status(thm)],[c_3,c_24]) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_1637,plain,
% 2.02/0.99      ( ~ r2_hidden(X0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))
% 2.02/0.99      | r2_hidden(X0,sK4) ),
% 2.02/0.99      inference(resolution,[status(thm)],[c_1048,c_807]) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_20,plain,
% 2.02/0.99      ( r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X0,X2)) ),
% 2.02/0.99      inference(cnf_transformation,[],[f105]) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_1653,plain,
% 2.02/0.99      ( r2_hidden(sK2,sK4) ),
% 2.02/0.99      inference(resolution,[status(thm)],[c_1637,c_20]) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_23,negated_conjecture,
% 2.02/0.99      ( ~ r2_hidden(sK2,sK4) ),
% 2.02/0.99      inference(cnf_transformation,[],[f75]) ).
% 2.02/0.99  
% 2.02/0.99  cnf(contradiction,plain,
% 2.02/0.99      ( $false ),
% 2.02/0.99      inference(minisat,[status(thm)],[c_1653,c_23]) ).
% 2.02/0.99  
% 2.02/0.99  
% 2.02/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.02/0.99  
% 2.02/0.99  ------                               Statistics
% 2.02/0.99  
% 2.02/0.99  ------ Selected
% 2.02/0.99  
% 2.02/0.99  total_time:                             0.071
% 2.02/0.99  
%------------------------------------------------------------------------------
