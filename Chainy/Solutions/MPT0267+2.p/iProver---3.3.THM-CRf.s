%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0267+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:32 EST 2020

% Result     : Theorem 47.34s
% Output     : CNFRefutation 47.34s
% Verified   : 
% Statistics : Number of formulae       :  321 (28092 expanded)
%              Number of clauses        :  207 (9088 expanded)
%              Number of leaves         :   35 (7435 expanded)
%              Depth                    :   42
%              Number of atoms          :  507 (41330 expanded)
%              Number of equality atoms :  342 (27108 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal clause size      :   12 (   1 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f302,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f649,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
        | r2_hidden(X0,X1) )
      & ( ~ r2_hidden(X0,X1)
        | k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f302])).

fof(f1077,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f649])).

fof(f363,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f364,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
      <=> ( X0 != X2
          & r2_hidden(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f363])).

fof(f532,plain,(
    ? [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <~> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f364])).

fof(f673,plain,(
    ? [X0,X1,X2] :
      ( ( X0 = X2
        | ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f532])).

fof(f674,plain,(
    ? [X0,X1,X2] :
      ( ( X0 = X2
        | ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f673])).

fof(f675,plain,
    ( ? [X0,X1,X2] :
        ( ( X0 = X2
          | ~ r2_hidden(X0,X1)
          | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) )
        & ( ( X0 != X2
            & r2_hidden(X0,X1) )
          | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) )
   => ( ( sK35 = sK37
        | ~ r2_hidden(sK35,sK36)
        | ~ r2_hidden(sK35,k4_xboole_0(sK36,k1_tarski(sK37))) )
      & ( ( sK35 != sK37
          & r2_hidden(sK35,sK36) )
        | r2_hidden(sK35,k4_xboole_0(sK36,k1_tarski(sK37))) ) ) ),
    introduced(choice_axiom,[])).

fof(f676,plain,
    ( ( sK35 = sK37
      | ~ r2_hidden(sK35,sK36)
      | ~ r2_hidden(sK35,k4_xboole_0(sK36,k1_tarski(sK37))) )
    & ( ( sK35 != sK37
        & r2_hidden(sK35,sK36) )
      | r2_hidden(sK35,k4_xboole_0(sK36,k1_tarski(sK37))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK35,sK36,sK37])],[f674,f675])).

fof(f1176,plain,
    ( sK35 = sK37
    | ~ r2_hidden(sK35,sK36)
    | ~ r2_hidden(sK35,k4_xboole_0(sK36,k1_tarski(sK37))) ),
    inference(cnf_transformation,[],[f676])).

fof(f1174,plain,
    ( r2_hidden(sK35,sK36)
    | r2_hidden(sK35,k4_xboole_0(sK36,k1_tarski(sK37))) ),
    inference(cnf_transformation,[],[f676])).

fof(f359,axiom,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
      | r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1169,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
      | r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f359])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f832,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f1504,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),X1)) = k1_tarski(X0)
      | r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(definition_unfolding,[],[f1169,f832])).

fof(f355,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f524,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f355])).

fof(f1165,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f524])).

fof(f109,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f831,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f109])).

fof(f1284,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f831,f832])).

fof(f48,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f759,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

fof(f1191,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f759,f832])).

fof(f150,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f466,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f150])).

fof(f875,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f466])).

fof(f357,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f526,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f357])).

fof(f1167,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f526])).

fof(f164,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f890,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f164])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f684,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f1321,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = o_0_0_xboole_0 ),
    inference(definition_unfolding,[],[f890,f684])).

fof(f163,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f889,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f163])).

fof(f124,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f846,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f124])).

fof(f1294,plain,(
    ! [X0] : k5_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f846,f684])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f681,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f680,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f1194,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f680,f832,f832])).

fof(f100,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f822,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f100])).

fof(f1275,plain,(
    ! [X0] : k4_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f822,f684])).

fof(f111,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f833,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f111])).

fof(f1285,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f833,f832,f832])).

fof(f88,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f809,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f88])).

fof(f1267,plain,(
    ! [X0] : o_0_0_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,o_0_0_xboole_0)) ),
    inference(definition_unfolding,[],[f809,f832,f684,f684])).

fof(f61,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k5_xboole_0(X0,X2),X1) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f778,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k5_xboole_0(X0,X2),X1) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f61])).

fof(f1237,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X1))) = k4_xboole_0(k5_xboole_0(X0,X2),k4_xboole_0(k5_xboole_0(X0,X2),X1)) ),
    inference(definition_unfolding,[],[f778,f832,f832,f832])).

fof(f167,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f893,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f167])).

fof(f166,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f892,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f166])).

fof(f1180,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f892,f832])).

fof(f1323,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(definition_unfolding,[],[f893,f832,f1180])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f706,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f1190,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f706,f1180])).

fof(f170,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f896,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f170])).

fof(f1324,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f896,f1180])).

fof(f108,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f830,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f108])).

fof(f1283,plain,(
    ! [X0,X1] : o_0_0_xboole_0 = k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f830,f684,f1180])).

fof(f103,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f825,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f103])).

fof(f1278,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(definition_unfolding,[],[f825,f1180])).

fof(f60,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k4_xboole_0(X0,X2),X1) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f777,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k4_xboole_0(X0,X2),X1) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f60])).

fof(f1236,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(k4_xboole_0(X0,X2),X1)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
    inference(definition_unfolding,[],[f777,f832,f832,f832])).

fof(f112,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f834,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f112])).

fof(f1286,plain,(
    ! [X0] : o_0_0_xboole_0 = k4_xboole_0(o_0_0_xboole_0,X0) ),
    inference(definition_unfolding,[],[f834,f684,f684])).

fof(f352,axiom,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k1_tarski(X1)) = k1_tarski(X1)
     => r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f520,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k3_xboole_0(X0,k1_tarski(X1)) != k1_tarski(X1) ) ),
    inference(ennf_transformation,[],[f352])).

fof(f1162,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k3_xboole_0(X0,k1_tarski(X1)) != k1_tarski(X1) ) ),
    inference(cnf_transformation,[],[f520])).

fof(f1499,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k4_xboole_0(X0,k4_xboole_0(X0,k1_tarski(X1))) != k1_tarski(X1) ) ),
    inference(definition_unfolding,[],[f1162,f832])).

fof(f353,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f521,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f353])).

fof(f1163,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f521])).

fof(f1500,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X1,k4_xboole_0(X1,k1_tarski(X0))) = k1_tarski(X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f1163,f832])).

fof(f303,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f650,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f303])).

fof(f1079,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f650])).

fof(f1436,plain,(
    ! [X0,X1] :
      ( o_0_0_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f1079,f684])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f379,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f572,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f379])).

fof(f723,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f572])).

fof(f321,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f500,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f321])).

fof(f1110,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f500])).

fof(f1459,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | o_0_0_xboole_0 != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(definition_unfolding,[],[f1110,f684])).

fof(f1076,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f649])).

fof(f1175,plain,
    ( sK35 != sK37
    | r2_hidden(sK35,k4_xboole_0(sK36,k1_tarski(sK37))) ),
    inference(cnf_transformation,[],[f676])).

fof(f722,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f572])).

fof(f175,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f607,plain,(
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
    inference(nnf_transformation,[],[f175])).

fof(f608,plain,(
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
    inference(rectify,[],[f607])).

fof(f609,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK20(X0,X1) != X0
          | ~ r2_hidden(sK20(X0,X1),X1) )
        & ( sK20(X0,X1) = X0
          | r2_hidden(sK20(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f610,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK20(X0,X1) != X0
            | ~ r2_hidden(sK20(X0,X1),X1) )
          & ( sK20(X0,X1) = X0
            | r2_hidden(sK20(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK20])],[f608,f609])).

fof(f909,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f610])).

fof(f1532,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f909])).

fof(f1533,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f1532])).

cnf(c_387,plain,
    ( r2_hidden(X0,X1)
    | k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1077])).

cnf(c_14194,plain,
    ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
    | r2_hidden(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_387])).

cnf(c_485,negated_conjecture,
    ( ~ r2_hidden(sK35,k4_xboole_0(sK36,k1_tarski(sK37)))
    | ~ r2_hidden(sK35,sK36)
    | sK35 = sK37 ),
    inference(cnf_transformation,[],[f1176])).

cnf(c_14150,plain,
    ( sK35 = sK37
    | r2_hidden(sK35,k4_xboole_0(sK36,k1_tarski(sK37))) != iProver_top
    | r2_hidden(sK35,sK36) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_485])).

cnf(c_130078,plain,
    ( k4_xboole_0(k1_tarski(sK35),k4_xboole_0(sK36,k1_tarski(sK37))) = k1_tarski(sK35)
    | sK37 = sK35
    | r2_hidden(sK35,sK36) != iProver_top ),
    inference(superposition,[status(thm)],[c_14194,c_14150])).

cnf(c_487,negated_conjecture,
    ( r2_hidden(sK35,k4_xboole_0(sK36,k1_tarski(sK37)))
    | r2_hidden(sK35,sK36) ),
    inference(cnf_transformation,[],[f1174])).

cnf(c_14148,plain,
    ( r2_hidden(sK35,k4_xboole_0(sK36,k1_tarski(sK37))) = iProver_top
    | r2_hidden(sK35,sK36) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_487])).

cnf(c_480,plain,
    ( r1_xboole_0(k1_tarski(X0),X1)
    | k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),X1)) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1504])).

cnf(c_476,plain,
    ( ~ r1_xboole_0(k1_tarski(X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f1165])).

cnf(c_2622,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_xboole_0(k1_tarski(X0),X1) ),
    inference(prop_impl,[status(thm)],[c_476])).

cnf(c_2623,plain,
    ( ~ r1_xboole_0(k1_tarski(X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(renaming,[status(thm)],[c_2622])).

cnf(c_3194,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),X1)) = k1_tarski(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_480,c_2623])).

cnf(c_14145,plain,
    ( k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),X1)) = k1_tarski(X0)
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3194])).

cnf(c_154,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f1284])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f1191])).

cnf(c_23083,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k5_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_154,c_1])).

cnf(c_28137,plain,
    ( k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),X1)) = k1_tarski(X0)
    | r2_hidden(X0,X1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_14145,c_23083])).

cnf(c_28140,plain,
    ( k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),k4_xboole_0(sK36,k1_tarski(sK37)))) = k1_tarski(sK35)
    | r2_hidden(sK35,sK36) = iProver_top ),
    inference(superposition,[status(thm)],[c_14148,c_28137])).

cnf(c_491,plain,
    ( r2_hidden(sK35,k4_xboole_0(sK36,k1_tarski(sK37))) = iProver_top
    | r2_hidden(sK35,sK36) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_487])).

cnf(c_15274,plain,
    ( ~ r1_xboole_0(k1_tarski(sK35),k4_xboole_0(sK36,k1_tarski(sK37)))
    | ~ r2_hidden(sK35,k4_xboole_0(sK36,k1_tarski(sK37))) ),
    inference(instantiation,[status(thm)],[c_476])).

cnf(c_15279,plain,
    ( r1_xboole_0(k1_tarski(sK35),k4_xboole_0(sK36,k1_tarski(sK37))) != iProver_top
    | r2_hidden(sK35,k4_xboole_0(sK36,k1_tarski(sK37))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15274])).

cnf(c_197,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f875])).

cnf(c_15940,plain,
    ( r1_xboole_0(k1_tarski(sK35),k4_xboole_0(sK36,k1_tarski(sK37)))
    | ~ r1_xboole_0(k1_tarski(sK35),sK36) ),
    inference(instantiation,[status(thm)],[c_197])).

cnf(c_15944,plain,
    ( r1_xboole_0(k1_tarski(sK35),k4_xboole_0(sK36,k1_tarski(sK37))) = iProver_top
    | r1_xboole_0(k1_tarski(sK35),sK36) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15940])).

cnf(c_478,plain,
    ( r1_xboole_0(k1_tarski(X0),X1)
    | r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f1167])).

cnf(c_17048,plain,
    ( r1_xboole_0(k1_tarski(sK35),sK36)
    | r2_hidden(sK35,sK36) ),
    inference(instantiation,[status(thm)],[c_478])).

cnf(c_17049,plain,
    ( r1_xboole_0(k1_tarski(sK35),sK36) = iProver_top
    | r2_hidden(sK35,sK36) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17048])).

cnf(c_30165,plain,
    ( r2_hidden(sK35,sK36) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_28140,c_491,c_15279,c_15944,c_17049])).

cnf(c_30169,plain,
    ( k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),sK36)) = k1_tarski(sK35) ),
    inference(superposition,[status(thm)],[c_30165,c_28137])).

cnf(c_212,plain,
    ( k5_xboole_0(X0,X0) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1321])).

cnf(c_211,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f889])).

cnf(c_23096,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(o_0_0_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_212,c_211])).

cnf(c_168,plain,
    ( k5_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f1294])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f681])).

cnf(c_19978,plain,
    ( k5_xboole_0(o_0_0_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_168,c_7])).

cnf(c_23121,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_23096,c_19978])).

cnf(c_30176,plain,
    ( k5_xboole_0(k1_tarski(sK35),k1_tarski(sK35)) = k4_xboole_0(k1_tarski(sK35),sK36) ),
    inference(superposition,[status(thm)],[c_30169,c_23121])).

cnf(c_30188,plain,
    ( k4_xboole_0(k1_tarski(sK35),sK36) = o_0_0_xboole_0 ),
    inference(demodulation,[status(thm)],[c_30176,c_212])).

cnf(c_6,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f1194])).

cnf(c_31003,plain,
    ( k4_xboole_0(sK36,k4_xboole_0(sK36,k1_tarski(sK35))) = k4_xboole_0(k1_tarski(sK35),o_0_0_xboole_0) ),
    inference(superposition,[status(thm)],[c_30188,c_6])).

cnf(c_145,plain,
    ( k4_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f1275])).

cnf(c_31008,plain,
    ( k4_xboole_0(sK36,k4_xboole_0(sK36,k1_tarski(sK35))) = k1_tarski(sK35) ),
    inference(demodulation,[status(thm)],[c_31003,c_145,c_23083])).

cnf(c_155,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(cnf_transformation,[],[f1285])).

cnf(c_23482,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(light_normalisation,[status(thm)],[c_155,c_155,c_23083])).

cnf(c_23483,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(demodulation,[status(thm)],[c_23482,c_23083])).

cnf(c_132,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,o_0_0_xboole_0)) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1267])).

cnf(c_14428,plain,
    ( k4_xboole_0(X0,X0) = o_0_0_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_132,c_145])).

cnf(c_23517,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k5_xboole_0(X0,k4_xboole_0(X0,X1))))) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_23483,c_14428])).

cnf(c_23071,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_6,c_154])).

cnf(c_23138,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_23071,c_23083])).

cnf(c_23523,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) = o_0_0_xboole_0 ),
    inference(demodulation,[status(thm)],[c_23517,c_23138])).

cnf(c_27694,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X0,o_0_0_xboole_0) ),
    inference(superposition,[status(thm)],[c_23523,c_23121])).

cnf(c_27712,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_27694,c_168])).

cnf(c_31828,plain,
    ( k4_xboole_0(k4_xboole_0(sK36,k1_tarski(sK35)),k1_tarski(sK35)) = k4_xboole_0(sK36,k1_tarski(sK35)) ),
    inference(superposition,[status(thm)],[c_31008,c_27712])).

cnf(c_31832,plain,
    ( k4_xboole_0(sK36,k1_tarski(sK35)) = k5_xboole_0(sK36,k1_tarski(sK35)) ),
    inference(superposition,[status(thm)],[c_31008,c_1])).

cnf(c_31895,plain,
    ( k4_xboole_0(k5_xboole_0(sK36,k1_tarski(sK35)),k1_tarski(sK35)) = k5_xboole_0(sK36,k1_tarski(sK35)) ),
    inference(light_normalisation,[status(thm)],[c_31828,c_31832])).

cnf(c_101,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X1))) = k4_xboole_0(k5_xboole_0(X0,X2),k4_xboole_0(k5_xboole_0(X0,X2),X1)) ),
    inference(cnf_transformation,[],[f1237])).

cnf(c_29034,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X1))) = k4_xboole_0(k5_xboole_0(X0,X2),k4_xboole_0(k5_xboole_0(X0,X2),X1)) ),
    inference(light_normalisation,[status(thm)],[c_101,c_101,c_23083])).

cnf(c_29035,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X1)),k5_xboole_0(X2,k4_xboole_0(X2,X1))) = k5_xboole_0(k5_xboole_0(X0,X2),k4_xboole_0(k5_xboole_0(X0,X2),X1)) ),
    inference(demodulation,[status(thm)],[c_29034,c_23083])).

cnf(c_102316,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(sK36,k1_tarski(sK35)),X0),k4_xboole_0(k5_xboole_0(k5_xboole_0(sK36,k1_tarski(sK35)),X0),k1_tarski(sK35))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(sK36,k1_tarski(sK35)),k5_xboole_0(sK36,k1_tarski(sK35))),k5_xboole_0(X0,k4_xboole_0(X0,k1_tarski(sK35)))) ),
    inference(superposition,[status(thm)],[c_31895,c_29035])).

cnf(c_31834,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK36,k1_tarski(sK35)))),k5_xboole_0(sK36,k1_tarski(sK35))) = k5_xboole_0(k5_xboole_0(X0,sK36),k4_xboole_0(k5_xboole_0(X0,sK36),k4_xboole_0(sK36,k1_tarski(sK35)))) ),
    inference(superposition,[status(thm)],[c_31008,c_29035])).

cnf(c_31886,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(sK36,k1_tarski(sK35)))),k5_xboole_0(sK36,k1_tarski(sK35))) = k5_xboole_0(k5_xboole_0(X0,sK36),k4_xboole_0(k5_xboole_0(X0,sK36),k5_xboole_0(sK36,k1_tarski(sK35)))) ),
    inference(light_normalisation,[status(thm)],[c_31834,c_31832])).

cnf(c_15134,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_211,c_7])).

cnf(c_15133,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_211,c_7])).

cnf(c_46751,plain,
    ( k5_xboole_0(o_0_0_xboole_0,k5_xboole_0(X0,X1)) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_168,c_15133])).

cnf(c_51883,plain,
    ( k5_xboole_0(o_0_0_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(k5_xboole_0(X2,X0),X1) ),
    inference(superposition,[status(thm)],[c_15134,c_46751])).

cnf(c_15132,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_211,c_7])).

cnf(c_46881,plain,
    ( k5_xboole_0(o_0_0_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X0,k5_xboole_0(X2,X1)) ),
    inference(superposition,[status(thm)],[c_46751,c_15132])).

cnf(c_51911,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X1,X0),X2) ),
    inference(light_normalisation,[status(thm)],[c_51883,c_46881])).

cnf(c_92490,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(sK36,k1_tarski(sK35)))),k5_xboole_0(sK36,k1_tarski(sK35))) = k5_xboole_0(sK36,k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X0,sK36),k5_xboole_0(sK36,k1_tarski(sK35))))) ),
    inference(demodulation,[status(thm)],[c_31886,c_51911])).

cnf(c_23214,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(superposition,[status(thm)],[c_7,c_23121])).

cnf(c_23254,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X0) = X1 ),
    inference(superposition,[status(thm)],[c_23214,c_23214])).

cnf(c_23333,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X2)) = k5_xboole_0(X1,X2) ),
    inference(superposition,[status(thm)],[c_23254,c_211])).

cnf(c_92521,plain,
    ( k5_xboole_0(k5_xboole_0(sK36,k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X0,sK36),k5_xboole_0(sK36,k1_tarski(sK35))))),k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(sK36,k1_tarski(sK35)))),X1)) = k5_xboole_0(k5_xboole_0(sK36,k1_tarski(sK35)),X1) ),
    inference(superposition,[status(thm)],[c_92490,c_23333])).

cnf(c_92570,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,k5_xboole_0(sK36,k1_tarski(sK35))),k5_xboole_0(sK36,k1_tarski(sK35)))) = k5_xboole_0(sK36,k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X0,sK36),k5_xboole_0(sK36,k1_tarski(sK35))))) ),
    inference(superposition,[status(thm)],[c_92490,c_211])).

cnf(c_214,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1323])).

cnf(c_8633,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(theory_normalisation,[status(thm)],[c_214,c_211,c_7])).

cnf(c_20780,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_6,c_1])).

cnf(c_22964,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_8633,c_20780])).

cnf(c_23221,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,X0))) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_22964,c_23121])).

cnf(c_23230,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_23221,c_1])).

cnf(c_55266,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,X1),X1)) = k4_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_23230,c_15134])).

cnf(c_92584,plain,
    ( k5_xboole_0(sK36,k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X0,sK36),k5_xboole_0(sK36,k1_tarski(sK35))))) = k4_xboole_0(k5_xboole_0(sK36,k1_tarski(sK35)),X0) ),
    inference(demodulation,[status(thm)],[c_92570,c_55266])).

cnf(c_93088,plain,
    ( k5_xboole_0(k4_xboole_0(k5_xboole_0(sK36,k1_tarski(sK35)),X0),k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(sK36,k1_tarski(sK35)))),X1)) = k5_xboole_0(k5_xboole_0(sK36,k1_tarski(sK35)),X1) ),
    inference(light_normalisation,[status(thm)],[c_92521,c_92584])).

cnf(c_23250,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X1) = X0 ),
    inference(superposition,[status(thm)],[c_23121,c_23214])).

cnf(c_23295,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X2)) = k5_xboole_0(X0,X2) ),
    inference(superposition,[status(thm)],[c_23250,c_211])).

cnf(c_57706,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X1,X0)),X2)) = k5_xboole_0(X0,X2) ),
    inference(superposition,[status(thm)],[c_23230,c_23295])).

cnf(c_57843,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(k4_xboole_0(X1,X0),k5_xboole_0(X1,X2))) = k5_xboole_0(X0,X2) ),
    inference(demodulation,[status(thm)],[c_57706,c_51911])).

cnf(c_93089,plain,
    ( k5_xboole_0(k1_tarski(sK35),k5_xboole_0(sK36,X0)) = k5_xboole_0(k5_xboole_0(sK36,k1_tarski(sK35)),X0) ),
    inference(demodulation,[status(thm)],[c_93088,c_51911,c_57843])).

cnf(c_102441,plain,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k5_xboole_0(sK36,X0)),k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k5_xboole_0(sK36,X0)),k1_tarski(sK35))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(sK36,k1_tarski(sK35)),k5_xboole_0(sK36,k1_tarski(sK35))),k5_xboole_0(X0,k4_xboole_0(X0,k1_tarski(sK35)))) ),
    inference(light_normalisation,[status(thm)],[c_102316,c_93089])).

cnf(c_29049,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X0,X1),X0)) = k5_xboole_0(k5_xboole_0(X0,o_0_0_xboole_0),k5_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_14428,c_29035])).

cnf(c_29133,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X0,X1),X0)) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_29049,c_168,c_23230])).

cnf(c_0,plain,
    ( k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)))) = k5_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f1190])).

cnf(c_8697,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))))) = k5_xboole_0(X0,X1) ),
    inference(theory_normalisation,[status(thm)],[c_0,c_211,c_7])).

cnf(c_24303,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X0,X1))) = k5_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_8697,c_20780])).

cnf(c_24315,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X0),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X0,X1),X0))) = k5_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_6,c_24303])).

cnf(c_217,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f1324])).

cnf(c_8632,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(theory_normalisation,[status(thm)],[c_217,c_211,c_7])).

cnf(c_23084,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1))) = k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X0)) ),
    inference(superposition,[status(thm)],[c_154,c_8632])).

cnf(c_23123,plain,
    ( k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X0)) = X0 ),
    inference(demodulation,[status(thm)],[c_23084,c_168,c_212])).

cnf(c_23707,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k5_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_23123,c_23121])).

cnf(c_23714,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = o_0_0_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_23707,c_212])).

cnf(c_24380,plain,
    ( k5_xboole_0(o_0_0_xboole_0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),o_0_0_xboole_0)) = k5_xboole_0(k4_xboole_0(X1,X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_24315,c_23714])).

cnf(c_24381,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k5_xboole_0(k4_xboole_0(X1,X0),X1) ),
    inference(demodulation,[status(thm)],[c_24380,c_145,c_19978])).

cnf(c_30988,plain,
    ( k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),k4_xboole_0(sK36,X0))) = k4_xboole_0(k5_xboole_0(k1_tarski(sK35),o_0_0_xboole_0),X0) ),
    inference(superposition,[status(thm)],[c_30188,c_23483])).

cnf(c_31016,plain,
    ( k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),k4_xboole_0(sK36,X0))) = k4_xboole_0(k1_tarski(sK35),X0) ),
    inference(demodulation,[status(thm)],[c_30988,c_168])).

cnf(c_33973,plain,
    ( k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k4_xboole_0(sK36,X0),X1))) = k4_xboole_0(k4_xboole_0(k1_tarski(sK35),X0),X1) ),
    inference(superposition,[status(thm)],[c_31016,c_23483])).

cnf(c_48741,plain,
    ( k4_xboole_0(k4_xboole_0(k1_tarski(sK35),X0),k4_xboole_0(sK36,X0)) = k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),o_0_0_xboole_0)) ),
    inference(superposition,[status(thm)],[c_14428,c_33973])).

cnf(c_33965,plain,
    ( k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),X0)) = k4_xboole_0(k1_tarski(sK35),k4_xboole_0(sK36,X0)) ),
    inference(superposition,[status(thm)],[c_31016,c_23121])).

cnf(c_48814,plain,
    ( k4_xboole_0(k4_xboole_0(k1_tarski(sK35),X0),k4_xboole_0(sK36,X0)) = o_0_0_xboole_0 ),
    inference(demodulation,[status(thm)],[c_48741,c_145,c_30188,c_33965])).

cnf(c_64190,plain,
    ( k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,k1_tarski(sK35)),X0),k4_xboole_0(sK36,k4_xboole_0(k1_tarski(sK35),X0))) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_24381,c_48814])).

cnf(c_153,plain,
    ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1283])).

cnf(c_8653,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = o_0_0_xboole_0 ),
    inference(theory_normalisation,[status(thm)],[c_153,c_211,c_7])).

cnf(c_23414,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) = o_0_0_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_8653,c_8632,c_8653])).

cnf(c_33958,plain,
    ( k4_xboole_0(k1_tarski(sK35),k5_xboole_0(sK36,k4_xboole_0(X0,sK36))) = k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),o_0_0_xboole_0)) ),
    inference(superposition,[status(thm)],[c_23414,c_31016])).

cnf(c_33982,plain,
    ( k4_xboole_0(k1_tarski(sK35),k5_xboole_0(sK36,k4_xboole_0(X0,sK36))) = k4_xboole_0(k1_tarski(sK35),k4_xboole_0(sK36,o_0_0_xboole_0)) ),
    inference(demodulation,[status(thm)],[c_33958,c_33965])).

cnf(c_148,plain,
    ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1278])).

cnf(c_8658,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2))))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(theory_normalisation,[status(thm)],[c_148,c_211,c_7])).

cnf(c_14441,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(demodulation,[status(thm)],[c_8658,c_8632])).

cnf(c_33983,plain,
    ( k4_xboole_0(k1_tarski(sK35),k5_xboole_0(sK36,k4_xboole_0(X0,sK36))) = o_0_0_xboole_0 ),
    inference(demodulation,[status(thm)],[c_33982,c_145,c_14441,c_30188])).

cnf(c_34314,plain,
    ( k4_xboole_0(k1_tarski(sK35),k5_xboole_0(sK36,k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,sK36))))) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_23483,c_33983])).

cnf(c_46505,plain,
    ( k4_xboole_0(k1_tarski(sK35),k5_xboole_0(X0,k5_xboole_0(sK36,k4_xboole_0(X0,k4_xboole_0(X1,sK36))))) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_15132,c_34314])).

cnf(c_47099,plain,
    ( k4_xboole_0(k1_tarski(sK35),k5_xboole_0(X0,k5_xboole_0(sK36,k4_xboole_0(sK36,k4_xboole_0(sK36,X0))))) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_6,c_46505])).

cnf(c_47172,plain,
    ( k4_xboole_0(k4_xboole_0(k1_tarski(sK35),X0),sK36) = o_0_0_xboole_0 ),
    inference(demodulation,[status(thm)],[c_47099,c_1,c_14441])).

cnf(c_49373,plain,
    ( k5_xboole_0(k4_xboole_0(k1_tarski(sK35),X0),k5_xboole_0(sK36,k4_xboole_0(k4_xboole_0(k1_tarski(sK35),X0),o_0_0_xboole_0))) = k5_xboole_0(k4_xboole_0(k1_tarski(sK35),X0),k4_xboole_0(sK36,k4_xboole_0(k1_tarski(sK35),X0))) ),
    inference(superposition,[status(thm)],[c_47172,c_8632])).

cnf(c_100,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X1))) = k4_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(k4_xboole_0(X0,X2),X1)) ),
    inference(cnf_transformation,[],[f1236])).

cnf(c_28930,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X1))) = k4_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(k4_xboole_0(X0,X2),X1)) ),
    inference(light_normalisation,[status(thm)],[c_100,c_100,c_23083])).

cnf(c_28931,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X2,X1))))) = k5_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(k4_xboole_0(X0,X2),X1)) ),
    inference(demodulation,[status(thm)],[c_28930,c_23083,c_23483])).

cnf(c_28932,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X2)) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,X1))) ),
    inference(demodulation,[status(thm)],[c_28931,c_23138])).

cnf(c_46455,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X2,k4_xboole_0(k4_xboole_0(X0,X1),X3))) = k5_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X3,X1)))) ),
    inference(superposition,[status(thm)],[c_28932,c_15132])).

cnf(c_49433,plain,
    ( k5_xboole_0(k4_xboole_0(k1_tarski(sK35),X0),k4_xboole_0(sK36,k4_xboole_0(k1_tarski(sK35),X0))) = k5_xboole_0(sK36,k4_xboole_0(k1_tarski(sK35),k4_xboole_0(sK36,k4_xboole_0(o_0_0_xboole_0,X0)))) ),
    inference(demodulation,[status(thm)],[c_49373,c_33965,c_46455])).

cnf(c_156,plain,
    ( k4_xboole_0(o_0_0_xboole_0,X0) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1286])).

cnf(c_49434,plain,
    ( k5_xboole_0(k4_xboole_0(k1_tarski(sK35),X0),k4_xboole_0(sK36,k4_xboole_0(k1_tarski(sK35),X0))) = k5_xboole_0(sK36,k4_xboole_0(k1_tarski(sK35),k4_xboole_0(sK36,o_0_0_xboole_0))) ),
    inference(light_normalisation,[status(thm)],[c_49433,c_156])).

cnf(c_49435,plain,
    ( k5_xboole_0(k4_xboole_0(k1_tarski(sK35),X0),k4_xboole_0(sK36,k4_xboole_0(k1_tarski(sK35),X0))) = sK36 ),
    inference(demodulation,[status(thm)],[c_49434,c_145,c_168,c_30188])).

cnf(c_49862,plain,
    ( k4_xboole_0(sK36,k4_xboole_0(k1_tarski(sK35),X0)) = k5_xboole_0(sK36,k4_xboole_0(k1_tarski(sK35),X0)) ),
    inference(superposition,[status(thm)],[c_49435,c_23254])).

cnf(c_64342,plain,
    ( k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,k1_tarski(sK35)),X0),k5_xboole_0(sK36,k4_xboole_0(k1_tarski(sK35),X0))) = o_0_0_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_64190,c_49862])).

cnf(c_72927,plain,
    ( k5_xboole_0(k4_xboole_0(k5_xboole_0(sK36,k4_xboole_0(k1_tarski(sK35),X0)),k5_xboole_0(k4_xboole_0(X0,k1_tarski(sK35)),X0)),k5_xboole_0(sK36,k4_xboole_0(k1_tarski(sK35),X0))) = k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,k1_tarski(sK35)),X0),o_0_0_xboole_0) ),
    inference(superposition,[status(thm)],[c_64342,c_24381])).

cnf(c_72957,plain,
    ( k4_xboole_0(k5_xboole_0(sK36,k4_xboole_0(k1_tarski(sK35),X0)),k4_xboole_0(k5_xboole_0(sK36,k4_xboole_0(k1_tarski(sK35),X0)),k5_xboole_0(k4_xboole_0(X0,k1_tarski(sK35)),X0))) = k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,k1_tarski(sK35)),X0),o_0_0_xboole_0) ),
    inference(superposition,[status(thm)],[c_64342,c_6])).

cnf(c_50726,plain,
    ( k4_xboole_0(k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),X0)),k5_xboole_0(sK36,k4_xboole_0(k1_tarski(sK35),X0))) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_49862,c_48814])).

cnf(c_30981,plain,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(sK35),X0),k4_xboole_0(k5_xboole_0(k1_tarski(sK35),X0),sK36)) = k5_xboole_0(k5_xboole_0(k1_tarski(sK35),o_0_0_xboole_0),k5_xboole_0(X0,k4_xboole_0(X0,sK36))) ),
    inference(superposition,[status(thm)],[c_30188,c_29035])).

cnf(c_31020,plain,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(sK35),X0),k4_xboole_0(k5_xboole_0(k1_tarski(sK35),X0),sK36)) = k5_xboole_0(k1_tarski(sK35),k5_xboole_0(X0,k4_xboole_0(X0,sK36))) ),
    inference(demodulation,[status(thm)],[c_30981,c_168])).

cnf(c_35009,plain,
    ( k5_xboole_0(k1_tarski(sK35),k5_xboole_0(k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),X0)),k4_xboole_0(k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),X0)),sK36))) = k5_xboole_0(k4_xboole_0(k1_tarski(sK35),X0),k4_xboole_0(k4_xboole_0(k1_tarski(sK35),X0),sK36)) ),
    inference(superposition,[status(thm)],[c_1,c_31020])).

cnf(c_37316,plain,
    ( k4_xboole_0(k1_tarski(sK35),k4_xboole_0(sK36,k4_xboole_0(k1_tarski(sK35),X0))) = k4_xboole_0(k1_tarski(sK35),X0) ),
    inference(demodulation,[status(thm)],[c_35009,c_23121,c_28932,c_31016])).

cnf(c_45245,plain,
    ( k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),X0)) = k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),X0)) ),
    inference(superposition,[status(thm)],[c_37316,c_31016])).

cnf(c_45247,plain,
    ( k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),X0)) = k4_xboole_0(k1_tarski(sK35),k4_xboole_0(sK36,X0)) ),
    inference(light_normalisation,[status(thm)],[c_45245,c_33965])).

cnf(c_50761,plain,
    ( k4_xboole_0(k4_xboole_0(k1_tarski(sK35),k4_xboole_0(sK36,X0)),k5_xboole_0(sK36,k4_xboole_0(k1_tarski(sK35),X0))) = o_0_0_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_50726,c_45247])).

cnf(c_59247,plain,
    ( k4_xboole_0(k5_xboole_0(sK36,k4_xboole_0(k1_tarski(sK35),X0)),k4_xboole_0(k5_xboole_0(sK36,k4_xboole_0(k1_tarski(sK35),X0)),k4_xboole_0(k1_tarski(sK35),k4_xboole_0(sK36,X0)))) = k4_xboole_0(k4_xboole_0(k1_tarski(sK35),k4_xboole_0(sK36,X0)),o_0_0_xboole_0) ),
    inference(superposition,[status(thm)],[c_50761,c_6])).

cnf(c_48899,plain,
    ( k5_xboole_0(k4_xboole_0(k1_tarski(sK35),X0),k5_xboole_0(k4_xboole_0(sK36,X0),k4_xboole_0(k4_xboole_0(k1_tarski(sK35),X0),o_0_0_xboole_0))) = k5_xboole_0(k4_xboole_0(k1_tarski(sK35),X0),k4_xboole_0(k4_xboole_0(sK36,X0),k4_xboole_0(k1_tarski(sK35),X0))) ),
    inference(superposition,[status(thm)],[c_48814,c_8632])).

cnf(c_48924,plain,
    ( k5_xboole_0(k4_xboole_0(k1_tarski(sK35),X0),k4_xboole_0(k4_xboole_0(sK36,X0),k4_xboole_0(k1_tarski(sK35),X0))) = k5_xboole_0(k4_xboole_0(sK36,X0),k4_xboole_0(k1_tarski(sK35),k4_xboole_0(sK36,k4_xboole_0(o_0_0_xboole_0,X0)))) ),
    inference(demodulation,[status(thm)],[c_48899,c_33965,c_46455])).

cnf(c_48925,plain,
    ( k5_xboole_0(k4_xboole_0(k1_tarski(sK35),X0),k4_xboole_0(k4_xboole_0(sK36,X0),k4_xboole_0(k1_tarski(sK35),X0))) = k5_xboole_0(k4_xboole_0(sK36,X0),k4_xboole_0(k1_tarski(sK35),k4_xboole_0(sK36,o_0_0_xboole_0))) ),
    inference(light_normalisation,[status(thm)],[c_48924,c_156])).

cnf(c_48926,plain,
    ( k5_xboole_0(k4_xboole_0(k1_tarski(sK35),X0),k4_xboole_0(k4_xboole_0(sK36,X0),k4_xboole_0(k1_tarski(sK35),X0))) = k4_xboole_0(sK36,X0) ),
    inference(demodulation,[status(thm)],[c_48925,c_145,c_168,c_30188])).

cnf(c_50184,plain,
    ( k4_xboole_0(k4_xboole_0(sK36,X0),k4_xboole_0(k1_tarski(sK35),X0)) = k5_xboole_0(k4_xboole_0(sK36,X0),k4_xboole_0(k1_tarski(sK35),X0)) ),
    inference(superposition,[status(thm)],[c_48926,c_23254])).

cnf(c_50887,plain,
    ( k4_xboole_0(k5_xboole_0(sK36,k4_xboole_0(k1_tarski(sK35),X0)),k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),X0))) = k5_xboole_0(k4_xboole_0(sK36,k4_xboole_0(k1_tarski(sK35),X0)),k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),X0))) ),
    inference(superposition,[status(thm)],[c_49862,c_50184])).

cnf(c_50984,plain,
    ( k4_xboole_0(k5_xboole_0(sK36,k4_xboole_0(k1_tarski(sK35),X0)),k4_xboole_0(k1_tarski(sK35),k4_xboole_0(sK36,X0))) = k5_xboole_0(k5_xboole_0(sK36,k4_xboole_0(k1_tarski(sK35),X0)),k4_xboole_0(k1_tarski(sK35),k4_xboole_0(sK36,X0))) ),
    inference(light_normalisation,[status(thm)],[c_50887,c_45247,c_49862])).

cnf(c_59252,plain,
    ( k4_xboole_0(k5_xboole_0(sK36,k4_xboole_0(k1_tarski(sK35),X0)),k5_xboole_0(k5_xboole_0(sK36,k4_xboole_0(k1_tarski(sK35),X0)),k4_xboole_0(k1_tarski(sK35),k4_xboole_0(sK36,X0)))) = k4_xboole_0(k4_xboole_0(k1_tarski(sK35),k4_xboole_0(sK36,X0)),o_0_0_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_59247,c_50984])).

cnf(c_43445,plain,
    ( k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(k1_tarski(sK35),k4_xboole_0(sK36,X0)),X1) ),
    inference(superposition,[status(thm)],[c_33965,c_23483])).

cnf(c_43465,plain,
    ( k4_xboole_0(k1_tarski(sK35),k4_xboole_0(sK36,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(k1_tarski(sK35),k4_xboole_0(sK36,X0)),X1) ),
    inference(demodulation,[status(thm)],[c_43445,c_33965])).

cnf(c_23287,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X2) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_211,c_23250])).

cnf(c_57350,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(k1_tarski(sK35),X1)),k4_xboole_0(k1_tarski(sK35),k4_xboole_0(sK36,X1))) = k5_xboole_0(X0,k1_tarski(sK35)) ),
    inference(superposition,[status(thm)],[c_31016,c_23287])).

cnf(c_59253,plain,
    ( k4_xboole_0(k5_xboole_0(sK36,k4_xboole_0(k1_tarski(sK35),X0)),k5_xboole_0(sK36,k1_tarski(sK35))) = k4_xboole_0(k1_tarski(sK35),k4_xboole_0(sK36,X0)) ),
    inference(demodulation,[status(thm)],[c_59252,c_145,c_43465,c_57350])).

cnf(c_55203,plain,
    ( k5_xboole_0(k4_xboole_0(sK36,X0),k4_xboole_0(k1_tarski(sK35),X0)) = k4_xboole_0(k4_xboole_0(sK36,X0),k1_tarski(sK35)) ),
    inference(superposition,[status(thm)],[c_31016,c_23230])).

cnf(c_63131,plain,
    ( k4_xboole_0(k4_xboole_0(sK36,X0),k4_xboole_0(k1_tarski(sK35),X0)) = k4_xboole_0(k4_xboole_0(sK36,X0),k1_tarski(sK35)) ),
    inference(demodulation,[status(thm)],[c_55203,c_50184])).

cnf(c_64165,plain,
    ( k4_xboole_0(k4_xboole_0(sK36,k4_xboole_0(k1_tarski(sK35),X0)),k5_xboole_0(k4_xboole_0(X0,k1_tarski(sK35)),X0)) = k4_xboole_0(k4_xboole_0(sK36,k4_xboole_0(k1_tarski(sK35),X0)),k1_tarski(sK35)) ),
    inference(superposition,[status(thm)],[c_24381,c_63131])).

cnf(c_50682,plain,
    ( k4_xboole_0(k1_tarski(sK35),k5_xboole_0(sK36,k4_xboole_0(k1_tarski(sK35),X0))) = k4_xboole_0(k1_tarski(sK35),X0) ),
    inference(demodulation,[status(thm)],[c_49862,c_37316])).

cnf(c_57913,plain,
    ( k5_xboole_0(k5_xboole_0(sK36,k4_xboole_0(k1_tarski(sK35),X0)),k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),X0))) = k4_xboole_0(k5_xboole_0(sK36,k4_xboole_0(k1_tarski(sK35),X0)),k1_tarski(sK35)) ),
    inference(superposition,[status(thm)],[c_50682,c_23230])).

cnf(c_57976,plain,
    ( k5_xboole_0(k5_xboole_0(sK36,k4_xboole_0(k1_tarski(sK35),X0)),k4_xboole_0(k1_tarski(sK35),k4_xboole_0(sK36,X0))) = k4_xboole_0(k5_xboole_0(sK36,k4_xboole_0(k1_tarski(sK35),X0)),k1_tarski(sK35)) ),
    inference(light_normalisation,[status(thm)],[c_57913,c_33965])).

cnf(c_57977,plain,
    ( k4_xboole_0(k5_xboole_0(sK36,k4_xboole_0(k1_tarski(sK35),X0)),k1_tarski(sK35)) = k5_xboole_0(sK36,k1_tarski(sK35)) ),
    inference(demodulation,[status(thm)],[c_57976,c_57350])).

cnf(c_64363,plain,
    ( k4_xboole_0(k5_xboole_0(sK36,k4_xboole_0(k1_tarski(sK35),X0)),k5_xboole_0(k4_xboole_0(X0,k1_tarski(sK35)),X0)) = k5_xboole_0(sK36,k1_tarski(sK35)) ),
    inference(light_normalisation,[status(thm)],[c_64165,c_49862,c_57977])).

cnf(c_72960,plain,
    ( k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,k1_tarski(sK35)),X0),o_0_0_xboole_0) = k4_xboole_0(k1_tarski(sK35),k4_xboole_0(sK36,X0)) ),
    inference(light_normalisation,[status(thm)],[c_72957,c_59253,c_64363])).

cnf(c_72989,plain,
    ( k5_xboole_0(k4_xboole_0(k5_xboole_0(sK36,k4_xboole_0(k1_tarski(sK35),X0)),k5_xboole_0(k4_xboole_0(X0,k1_tarski(sK35)),X0)),k5_xboole_0(sK36,k4_xboole_0(k1_tarski(sK35),X0))) = k4_xboole_0(k1_tarski(sK35),k4_xboole_0(sK36,X0)) ),
    inference(demodulation,[status(thm)],[c_72927,c_72960])).

cnf(c_72990,plain,
    ( k5_xboole_0(k5_xboole_0(sK36,k1_tarski(sK35)),k5_xboole_0(sK36,k4_xboole_0(k1_tarski(sK35),X0))) = k4_xboole_0(k1_tarski(sK35),k4_xboole_0(sK36,X0)) ),
    inference(light_normalisation,[status(thm)],[c_72989,c_64363])).

cnf(c_64166,plain,
    ( k5_xboole_0(k4_xboole_0(sK36,k4_xboole_0(k1_tarski(sK35),X0)),k5_xboole_0(k4_xboole_0(X0,k1_tarski(sK35)),X0)) = k4_xboole_0(k4_xboole_0(sK36,k4_xboole_0(k1_tarski(sK35),X0)),k1_tarski(sK35)) ),
    inference(superposition,[status(thm)],[c_24381,c_55203])).

cnf(c_64362,plain,
    ( k5_xboole_0(k5_xboole_0(sK36,k4_xboole_0(k1_tarski(sK35),X0)),k5_xboole_0(k4_xboole_0(X0,k1_tarski(sK35)),X0)) = k5_xboole_0(sK36,k1_tarski(sK35)) ),
    inference(light_normalisation,[status(thm)],[c_64166,c_49862,c_57977])).

cnf(c_57341,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X2,X1)) = k5_xboole_0(X0,o_0_0_xboole_0) ),
    inference(superposition,[status(thm)],[c_46751,c_23287])).

cnf(c_57458,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X2,X1)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_57341,c_168])).

cnf(c_101767,plain,
    ( k5_xboole_0(k5_xboole_0(sK36,k1_tarski(sK35)),k5_xboole_0(X0,k4_xboole_0(X0,k1_tarski(sK35)))) = k5_xboole_0(sK36,k4_xboole_0(k1_tarski(sK35),X0)) ),
    inference(superposition,[status(thm)],[c_64362,c_57458])).

cnf(c_102442,plain,
    ( k4_xboole_0(k1_tarski(sK35),k5_xboole_0(sK36,X0)) = k4_xboole_0(k1_tarski(sK35),k4_xboole_0(sK36,X0)) ),
    inference(demodulation,[status(thm)],[c_102441,c_29133,c_51911,c_72990,c_101767])).

cnf(c_130081,plain,
    ( k4_xboole_0(k1_tarski(sK35),k5_xboole_0(sK36,k1_tarski(sK37))) = k1_tarski(sK35)
    | sK37 = sK35
    | r2_hidden(sK35,sK36) != iProver_top ),
    inference(demodulation,[status(thm)],[c_130078,c_102442])).

cnf(c_473,plain,
    ( r2_hidden(X0,X1)
    | k4_xboole_0(X1,k4_xboole_0(X1,k1_tarski(X0))) != k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1499])).

cnf(c_15145,plain,
    ( r2_hidden(sK35,sK36)
    | k4_xboole_0(sK36,k4_xboole_0(sK36,k1_tarski(sK35))) != k1_tarski(sK35) ),
    inference(instantiation,[status(thm)],[c_473])).

cnf(c_474,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_xboole_0(X1,k4_xboole_0(X1,k1_tarski(X0))) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1500])).

cnf(c_15520,plain,
    ( ~ r2_hidden(sK35,sK36)
    | k4_xboole_0(sK36,k4_xboole_0(sK36,k1_tarski(sK35))) = k1_tarski(sK35) ),
    inference(instantiation,[status(thm)],[c_474])).

cnf(c_15521,plain,
    ( k4_xboole_0(sK36,k4_xboole_0(sK36,k1_tarski(sK35))) = k1_tarski(sK35)
    | r2_hidden(sK35,sK36) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15520])).

cnf(c_389,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_xboole_0(k1_tarski(X0),X1) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1436])).

cnf(c_22948,plain,
    ( ~ r2_hidden(sK35,k1_tarski(sK37))
    | k4_xboole_0(k1_tarski(sK35),k1_tarski(sK37)) = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_389])).

cnf(c_46,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f723])).

cnf(c_16054,plain,
    ( ~ r2_hidden(sK35,X0)
    | r2_hidden(sK35,k5_xboole_0(X0,k1_tarski(sK37)))
    | r2_hidden(sK35,k1_tarski(sK37)) ),
    inference(instantiation,[status(thm)],[c_46])).

cnf(c_44462,plain,
    ( r2_hidden(sK35,k5_xboole_0(sK36,k1_tarski(sK37)))
    | r2_hidden(sK35,k1_tarski(sK37))
    | ~ r2_hidden(sK35,sK36) ),
    inference(instantiation,[status(thm)],[c_16054])).

cnf(c_421,plain,
    ( X0 = X1
    | k4_xboole_0(k1_tarski(X1),k1_tarski(X0)) != o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1459])).

cnf(c_19466,plain,
    ( k4_xboole_0(k1_tarski(X0),k1_tarski(sK37)) != o_0_0_xboole_0
    | sK37 = X0 ),
    inference(instantiation,[status(thm)],[c_421])).

cnf(c_48163,plain,
    ( k4_xboole_0(k1_tarski(sK35),k1_tarski(sK37)) != o_0_0_xboole_0
    | sK37 = sK35 ),
    inference(instantiation,[status(thm)],[c_19466])).

cnf(c_388,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1076])).

cnf(c_77670,plain,
    ( ~ r2_hidden(sK35,k5_xboole_0(sK36,k1_tarski(sK37)))
    | k4_xboole_0(k1_tarski(sK35),k5_xboole_0(sK36,k1_tarski(sK37))) != k1_tarski(sK35) ),
    inference(instantiation,[status(thm)],[c_388])).

cnf(c_130453,plain,
    ( sK37 = sK35 ),
    inference(global_propositional_subsumption,[status(thm)],[c_130081,c_491,c_15145,c_15279,c_15521,c_15944,c_17049,c_22948,c_44462,c_48163,c_77670])).

cnf(c_486,negated_conjecture,
    ( r2_hidden(sK35,k4_xboole_0(sK36,k1_tarski(sK37)))
    | sK35 != sK37 ),
    inference(cnf_transformation,[],[f1175])).

cnf(c_14149,plain,
    ( sK35 != sK37
    | r2_hidden(sK35,k4_xboole_0(sK36,k1_tarski(sK37))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_486])).

cnf(c_130456,plain,
    ( sK35 != sK35
    | r2_hidden(sK35,k4_xboole_0(sK36,k1_tarski(sK35))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_130453,c_14149])).

cnf(c_130457,plain,
    ( r2_hidden(sK35,k4_xboole_0(sK36,k1_tarski(sK35))) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_130456])).

cnf(c_130458,plain,
    ( r2_hidden(sK35,k5_xboole_0(sK36,k1_tarski(sK35))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_130457,c_31832])).

cnf(c_47,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f722])).

cnf(c_15590,plain,
    ( ~ r2_hidden(sK35,X0)
    | ~ r2_hidden(sK35,k5_xboole_0(sK36,X0))
    | ~ r2_hidden(sK35,sK36) ),
    inference(instantiation,[status(thm)],[c_47])).

cnf(c_40326,plain,
    ( ~ r2_hidden(sK35,k5_xboole_0(sK36,k1_tarski(sK35)))
    | ~ r2_hidden(sK35,k1_tarski(sK35))
    | ~ r2_hidden(sK35,sK36) ),
    inference(instantiation,[status(thm)],[c_15590])).

cnf(c_40327,plain,
    ( r2_hidden(sK35,k5_xboole_0(sK36,k1_tarski(sK35))) != iProver_top
    | r2_hidden(sK35,k1_tarski(sK35)) != iProver_top
    | r2_hidden(sK35,sK36) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40326])).

cnf(c_231,plain,
    ( r2_hidden(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f1533])).

cnf(c_29500,plain,
    ( r2_hidden(sK35,k1_tarski(sK35)) ),
    inference(instantiation,[status(thm)],[c_231])).

cnf(c_29501,plain,
    ( r2_hidden(sK35,k1_tarski(sK35)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29500])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_130458,c_40327,c_30165,c_29501])).

%------------------------------------------------------------------------------
