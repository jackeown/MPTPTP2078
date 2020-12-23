%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0249+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:30 EST 2020

% Result     : Theorem 49.87s
% Output     : CNFRefutation 49.87s
% Verified   : 
% Statistics : Number of formulae       :  197 (15006 expanded)
%              Number of clauses        :  108 (4215 expanded)
%              Number of leaves         :   28 (4369 expanded)
%              Depth                    :   31
%              Number of atoms          :  307 (20054 expanded)
%              Number of equality atoms :  245 (19805 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    8 (   1 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f642,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f794,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f1138,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f642,f794,f794])).

fof(f48,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f721,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

fof(f1135,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f721,f794])).

fof(f109,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f793,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f109])).

fof(f1228,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f793,f794])).

fof(f108,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f792,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f108])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f646,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f166,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f854,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f166])).

fof(f1124,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f854,f794])).

fof(f1227,plain,(
    ! [X0,X1] : o_0_0_xboole_0 = k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f792,f646,f1124])).

fof(f163,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f851,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f163])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f643,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f170,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f858,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f170])).

fof(f1268,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f858,f1124])).

fof(f114,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f798,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f114])).

fof(f1232,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f798,f794,f794,f794])).

fof(f111,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f795,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f111])).

fof(f1229,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f795,f794,f794])).

fof(f345,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f346,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & X1 != X2
          & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(negated_conjecture,[],[f345])).

fof(f496,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & X1 != X2
      & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f346])).

fof(f637,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k2_xboole_0(X1,X2) = k1_tarski(X0) )
   => ( k1_xboole_0 != sK37
      & k1_xboole_0 != sK36
      & sK36 != sK37
      & k2_xboole_0(sK36,sK37) = k1_tarski(sK35) ) ),
    introduced(choice_axiom,[])).

fof(f638,plain,
    ( k1_xboole_0 != sK37
    & k1_xboole_0 != sK36
    & sK36 != sK37
    & k2_xboole_0(sK36,sK37) = k1_tarski(sK35) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK35,sK36,sK37])],[f496,f637])).

fof(f1117,plain,(
    k2_xboole_0(sK36,sK37) = k1_tarski(sK35) ),
    inference(cnf_transformation,[],[f638])).

fof(f1438,plain,(
    k5_xboole_0(k5_xboole_0(sK36,sK37),k4_xboole_0(sK36,k4_xboole_0(sK36,sK37))) = k1_tarski(sK35) ),
    inference(definition_unfolding,[],[f1117,f1124])).

fof(f100,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f784,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f100])).

fof(f1219,plain,(
    ! [X0] : k4_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f784,f646])).

fof(f117,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f801,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f117])).

fof(f1235,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f801,f794,f1124])).

fof(f103,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f787,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f103])).

fof(f1222,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(definition_unfolding,[],[f787,f1124])).

fof(f164,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f852,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f164])).

fof(f1265,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = o_0_0_xboole_0 ),
    inference(definition_unfolding,[],[f852,f646])).

fof(f124,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f808,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f124])).

fof(f1238,plain,(
    ! [X0] : k5_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f808,f646])).

fof(f92,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f404,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ) ),
    inference(ennf_transformation,[],[f92])).

fof(f775,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f404])).

fof(f1120,plain,(
    k1_xboole_0 != sK37 ),
    inference(cnf_transformation,[],[f638])).

fof(f1436,plain,(
    o_0_0_xboole_0 != sK37 ),
    inference(definition_unfolding,[],[f1120,f646])).

fof(f347,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f497,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f347])).

fof(f1121,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f497])).

fof(f340,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f631,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f340])).

fof(f632,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f631])).

fof(f1100,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
      | k1_tarski(X1) != X0 ) ),
    inference(cnf_transformation,[],[f632])).

fof(f1512,plain,(
    ! [X1] : r1_tarski(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f1100])).

fof(f97,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f564,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f97])).

fof(f780,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f564])).

fof(f1216,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | o_0_0_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f780,f646])).

fof(f1098,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f632])).

fof(f1420,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | o_0_0_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(definition_unfolding,[],[f1098,f646])).

fof(f96,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f779,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f96])).

fof(f153,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f565,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f153])).

fof(f841,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f565])).

fof(f129,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f423,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f129])).

fof(f424,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f423])).

fof(f813,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f424])).

fof(f132,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f427,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f132])).

fof(f817,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f427])).

fof(f1243,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f817,f646])).

fof(f1119,plain,(
    k1_xboole_0 != sK36 ),
    inference(cnf_transformation,[],[f638])).

fof(f1437,plain,(
    o_0_0_xboole_0 != sK36 ),
    inference(definition_unfolding,[],[f1119,f646])).

fof(f1118,plain,(
    sK36 != sK37 ),
    inference(cnf_transformation,[],[f638])).

cnf(c_6,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f1138])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f1135])).

cnf(c_24211,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_6,c_1])).

cnf(c_154,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f1228])).

cnf(c_28132,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k5_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_154,c_1])).

cnf(c_84051,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_24211,c_28132])).

cnf(c_153,plain,
    ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1227])).

cnf(c_211,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f851])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f643])).

cnf(c_8353,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = o_0_0_xboole_0 ),
    inference(theory_normalisation,[status(thm)],[c_153,c_211,c_7])).

cnf(c_217,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f1268])).

cnf(c_8332,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(theory_normalisation,[status(thm)],[c_217,c_211,c_7])).

cnf(c_23123,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) = o_0_0_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_8353,c_8332,c_8353])).

cnf(c_158,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f1232])).

cnf(c_35894,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(light_normalisation,[status(thm)],[c_158,c_158,c_28132])).

cnf(c_155,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(cnf_transformation,[],[f1229])).

cnf(c_32252,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(light_normalisation,[status(thm)],[c_155,c_155,c_28132])).

cnf(c_32253,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(demodulation,[status(thm)],[c_32252,c_28132])).

cnf(c_35895,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k5_xboole_0(X0,k4_xboole_0(X0,X2))))) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(demodulation,[status(thm)],[c_35894,c_28132,c_32253])).

cnf(c_469,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(sK36,sK37),k4_xboole_0(sK36,k4_xboole_0(sK36,sK37))) = k1_tarski(sK35) ),
    inference(cnf_transformation,[],[f1438])).

cnf(c_8205,negated_conjecture,
    ( k5_xboole_0(sK37,k5_xboole_0(sK36,k4_xboole_0(sK36,k4_xboole_0(sK36,sK37)))) = k1_tarski(sK35) ),
    inference(theory_normalisation,[status(thm)],[c_469,c_211,c_7])).

cnf(c_13898,plain,
    ( k5_xboole_0(sK37,k4_xboole_0(sK36,sK37)) = k1_tarski(sK35) ),
    inference(demodulation,[status(thm)],[c_8205,c_1])).

cnf(c_28427,plain,
    ( k5_xboole_0(sK37,k5_xboole_0(k4_xboole_0(sK36,sK37),X0)) = k5_xboole_0(k1_tarski(sK35),X0) ),
    inference(superposition,[status(thm)],[c_13898,c_211])).

cnf(c_35931,plain,
    ( k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k4_xboole_0(sK36,sK37),k4_xboole_0(X0,k5_xboole_0(k4_xboole_0(sK36,sK37),k4_xboole_0(k4_xboole_0(sK36,sK37),X1))))) = k5_xboole_0(sK37,k5_xboole_0(k4_xboole_0(sK36,sK37),k4_xboole_0(k4_xboole_0(sK36,sK37),k4_xboole_0(X0,X1)))) ),
    inference(superposition,[status(thm)],[c_35895,c_28427])).

cnf(c_35938,plain,
    ( k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k4_xboole_0(sK36,sK37),k4_xboole_0(X0,k5_xboole_0(k4_xboole_0(sK36,sK37),k4_xboole_0(k4_xboole_0(sK36,sK37),X1))))) = k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k4_xboole_0(sK36,sK37),k4_xboole_0(X0,X1))) ),
    inference(demodulation,[status(thm)],[c_35931,c_28427])).

cnf(c_36659,plain,
    ( k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k4_xboole_0(sK36,sK37),k4_xboole_0(k4_xboole_0(sK36,sK37),k4_xboole_0(sK36,sK37)))) = k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k4_xboole_0(sK36,sK37),o_0_0_xboole_0)) ),
    inference(superposition,[status(thm)],[c_23123,c_35938])).

cnf(c_145,plain,
    ( k4_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f1219])).

cnf(c_161,plain,
    ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) ),
    inference(cnf_transformation,[],[f1235])).

cnf(c_8349,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2))))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) ),
    inference(theory_normalisation,[status(thm)],[c_161,c_211,c_7])).

cnf(c_148,plain,
    ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1222])).

cnf(c_8358,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2))))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(theory_normalisation,[status(thm)],[c_148,c_211,c_7])).

cnf(c_13904,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(demodulation,[status(thm)],[c_8358,c_8332])).

cnf(c_13943,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(demodulation,[status(thm)],[c_8349,c_8332,c_13904])).

cnf(c_212,plain,
    ( k5_xboole_0(X0,X0) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1265])).

cnf(c_29083,plain,
    ( k5_xboole_0(k1_tarski(sK35),k4_xboole_0(sK36,sK37)) = k5_xboole_0(sK37,o_0_0_xboole_0) ),
    inference(superposition,[status(thm)],[c_212,c_28427])).

cnf(c_168,plain,
    ( k5_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f1238])).

cnf(c_29087,plain,
    ( k5_xboole_0(k1_tarski(sK35),k4_xboole_0(sK36,sK37)) = sK37 ),
    inference(demodulation,[status(thm)],[c_29083,c_168])).

cnf(c_36680,plain,
    ( k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k4_xboole_0(sK36,sK37),sK37)) = sK37 ),
    inference(demodulation,[status(thm)],[c_36659,c_145,c_13943,c_29087])).

cnf(c_29085,plain,
    ( k5_xboole_0(sK37,k5_xboole_0(k5_xboole_0(k4_xboole_0(sK36,sK37),X0),X1)) = k5_xboole_0(k5_xboole_0(k1_tarski(sK35),X0),X1) ),
    inference(superposition,[status(thm)],[c_28427,c_211])).

cnf(c_29082,plain,
    ( k5_xboole_0(sK37,k5_xboole_0(X0,k4_xboole_0(sK36,sK37))) = k5_xboole_0(k1_tarski(sK35),X0) ),
    inference(superposition,[status(thm)],[c_7,c_28427])).

cnf(c_29631,plain,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(sK35),X0),k4_xboole_0(sK36,sK37)) = k5_xboole_0(k1_tarski(sK35),k5_xboole_0(k4_xboole_0(sK36,sK37),X0)) ),
    inference(superposition,[status(thm)],[c_29085,c_29082])).

cnf(c_30189,plain,
    ( k5_xboole_0(k1_tarski(sK35),k5_xboole_0(k4_xboole_0(sK36,sK37),X0)) = k5_xboole_0(sK37,X0) ),
    inference(superposition,[status(thm)],[c_29087,c_211])).

cnf(c_30192,plain,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(sK35),X0),k4_xboole_0(sK36,sK37)) = k5_xboole_0(sK37,X0) ),
    inference(demodulation,[status(thm)],[c_29631,c_30189])).

cnf(c_37155,plain,
    ( k5_xboole_0(sK37,k4_xboole_0(k4_xboole_0(sK36,sK37),sK37)) = k5_xboole_0(sK37,k4_xboole_0(sK36,sK37)) ),
    inference(superposition,[status(thm)],[c_36680,c_30192])).

cnf(c_37156,plain,
    ( k5_xboole_0(sK37,k4_xboole_0(k4_xboole_0(sK36,sK37),sK37)) = k1_tarski(sK35) ),
    inference(light_normalisation,[status(thm)],[c_37155,c_13898])).

cnf(c_39625,plain,
    ( k5_xboole_0(sK37,k5_xboole_0(k4_xboole_0(k4_xboole_0(sK36,sK37),sK37),X0)) = k5_xboole_0(k1_tarski(sK35),X0) ),
    inference(superposition,[status(thm)],[c_37156,c_211])).

cnf(c_39636,plain,
    ( k5_xboole_0(sK37,k5_xboole_0(k5_xboole_0(k4_xboole_0(k4_xboole_0(sK36,sK37),sK37),X0),X1)) = k5_xboole_0(k5_xboole_0(k1_tarski(sK35),X0),X1) ),
    inference(superposition,[status(thm)],[c_39625,c_211])).

cnf(c_29612,plain,
    ( k5_xboole_0(sK37,k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(sK36,sK37)))) = k5_xboole_0(k1_tarski(sK35),k5_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_211,c_29082])).

cnf(c_40422,plain,
    ( k5_xboole_0(k1_tarski(sK35),k5_xboole_0(sK37,k5_xboole_0(k4_xboole_0(k4_xboole_0(sK36,sK37),sK37),X0))) = k5_xboole_0(sK37,k5_xboole_0(k5_xboole_0(k1_tarski(sK35),X0),k4_xboole_0(sK36,sK37))) ),
    inference(superposition,[status(thm)],[c_39636,c_29612])).

cnf(c_30222,plain,
    ( k5_xboole_0(k1_tarski(sK35),k5_xboole_0(X0,k1_tarski(sK35))) = k5_xboole_0(sK37,k5_xboole_0(X0,sK37)) ),
    inference(superposition,[status(thm)],[c_29087,c_29612])).

cnf(c_34681,plain,
    ( k5_xboole_0(k1_tarski(sK35),k5_xboole_0(k1_tarski(sK35),X0)) = k5_xboole_0(sK37,k5_xboole_0(X0,sK37)) ),
    inference(superposition,[status(thm)],[c_7,c_30222])).

cnf(c_28424,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(o_0_0_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_212,c_211])).

cnf(c_23620,plain,
    ( k5_xboole_0(o_0_0_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_168,c_7])).

cnf(c_28437,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_28424,c_23620])).

cnf(c_34693,plain,
    ( k5_xboole_0(sK37,k5_xboole_0(X0,sK37)) = X0 ),
    inference(demodulation,[status(thm)],[c_34681,c_28437])).

cnf(c_34711,plain,
    ( k5_xboole_0(k1_tarski(sK35),k5_xboole_0(k1_tarski(sK35),X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_34681,c_34693])).

cnf(c_40425,plain,
    ( k5_xboole_0(sK37,k5_xboole_0(sK37,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_40422,c_30192,c_34711,c_39625])).

cnf(c_43477,plain,
    ( k5_xboole_0(k1_tarski(sK35),k5_xboole_0(sK37,X0)) = k5_xboole_0(X0,k4_xboole_0(sK36,sK37)) ),
    inference(superposition,[status(thm)],[c_40425,c_29612])).

cnf(c_84160,plain,
    ( k5_xboole_0(k4_xboole_0(sK37,k1_tarski(sK35)),k4_xboole_0(sK36,sK37)) = k4_xboole_0(k1_tarski(sK35),sK37) ),
    inference(superposition,[status(thm)],[c_84051,c_43477])).

cnf(c_23125,plain,
    ( k4_xboole_0(sK37,k1_tarski(sK35)) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_13898,c_23123])).

cnf(c_84168,plain,
    ( k5_xboole_0(o_0_0_xboole_0,k4_xboole_0(sK36,sK37)) = k4_xboole_0(k1_tarski(sK35),sK37) ),
    inference(light_normalisation,[status(thm)],[c_84160,c_23125])).

cnf(c_84169,plain,
    ( k4_xboole_0(k1_tarski(sK35),sK37) = k4_xboole_0(sK36,sK37) ),
    inference(demodulation,[status(thm)],[c_84168,c_23620])).

cnf(c_136,plain,
    ( X0 = X1
    | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f775])).

cnf(c_88293,plain,
    ( k4_xboole_0(sK37,k1_tarski(sK35)) != k4_xboole_0(sK36,sK37)
    | k1_tarski(sK35) = sK37 ),
    inference(superposition,[status(thm)],[c_84169,c_136])).

cnf(c_88321,plain,
    ( k4_xboole_0(sK36,sK37) != o_0_0_xboole_0
    | k1_tarski(sK35) = sK37 ),
    inference(light_normalisation,[status(thm)],[c_88293,c_23125])).

cnf(c_466,negated_conjecture,
    ( o_0_0_xboole_0 != sK37 ),
    inference(cnf_transformation,[],[f1436])).

cnf(c_470,plain,
    ( ~ r1_tarski(k1_tarski(X0),k1_tarski(X1))
    | X1 = X0 ),
    inference(cnf_transformation,[],[f1121])).

cnf(c_475,plain,
    ( ~ r1_tarski(k1_tarski(o_0_0_xboole_0),k1_tarski(o_0_0_xboole_0))
    | o_0_0_xboole_0 = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_470])).

cnf(c_447,plain,
    ( r1_tarski(k1_tarski(X0),k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f1512])).

cnf(c_506,plain,
    ( r1_tarski(k1_tarski(o_0_0_xboole_0),k1_tarski(o_0_0_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_447])).

cnf(c_8400,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_14692,plain,
    ( sK37 != X0
    | o_0_0_xboole_0 != X0
    | o_0_0_xboole_0 = sK37 ),
    inference(instantiation,[status(thm)],[c_8400])).

cnf(c_14693,plain,
    ( sK37 != o_0_0_xboole_0
    | o_0_0_xboole_0 = sK37
    | o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_14692])).

cnf(c_142,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1216])).

cnf(c_13828,plain,
    ( k4_xboole_0(X0,X1) != o_0_0_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_142])).

cnf(c_71938,plain,
    ( r1_tarski(sK37,k1_tarski(sK35)) = iProver_top ),
    inference(superposition,[status(thm)],[c_23125,c_13828])).

cnf(c_449,plain,
    ( ~ r1_tarski(X0,k1_tarski(X1))
    | k1_tarski(X1) = X0
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f1420])).

cnf(c_13647,plain,
    ( k1_tarski(X0) = X1
    | o_0_0_xboole_0 = X1
    | r1_tarski(X1,k1_tarski(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_449])).

cnf(c_74221,plain,
    ( k1_tarski(sK35) = sK37
    | sK37 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_71938,c_13647])).

cnf(c_89273,plain,
    ( k1_tarski(sK35) = sK37 ),
    inference(global_propositional_subsumption,[status(thm)],[c_88321,c_466,c_475,c_506,c_14693,c_74221])).

cnf(c_84151,plain,
    ( k5_xboole_0(k1_tarski(sK35),sK36) = k4_xboole_0(sK37,sK36) ),
    inference(superposition,[status(thm)],[c_84051,c_29082])).

cnf(c_89276,plain,
    ( k4_xboole_0(sK37,sK36) = k5_xboole_0(sK37,sK36) ),
    inference(demodulation,[status(thm)],[c_89273,c_84151])).

cnf(c_140,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f779])).

cnf(c_13786,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_140])).

cnf(c_93491,plain,
    ( r1_tarski(k5_xboole_0(sK37,sK36),sK37) = iProver_top ),
    inference(superposition,[status(thm)],[c_89276,c_13786])).

cnf(c_89434,plain,
    ( k1_tarski(sK35) = X0
    | o_0_0_xboole_0 = X0
    | r1_tarski(X0,sK37) != iProver_top ),
    inference(superposition,[status(thm)],[c_89273,c_13647])).

cnf(c_89450,plain,
    ( sK37 = X0
    | o_0_0_xboole_0 = X0
    | r1_tarski(X0,sK37) != iProver_top ),
    inference(demodulation,[status(thm)],[c_89434,c_89273])).

cnf(c_146181,plain,
    ( k5_xboole_0(sK37,sK36) = sK37
    | k5_xboole_0(sK37,sK36) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_93491,c_89450])).

cnf(c_200,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) != X0 ),
    inference(cnf_transformation,[],[f841])).

cnf(c_13752,plain,
    ( k4_xboole_0(X0,X1) != X0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_200])).

cnf(c_139413,plain,
    ( k5_xboole_0(sK37,sK36) != sK37
    | r1_xboole_0(sK37,sK36) = iProver_top ),
    inference(superposition,[status(thm)],[c_89276,c_13752])).

cnf(c_173,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X1)
    | ~ r1_tarski(X2,X0) ),
    inference(cnf_transformation,[],[f813])).

cnf(c_17414,plain,
    ( ~ r1_xboole_0(X0,sK36)
    | r1_xboole_0(sK36,sK36)
    | ~ r1_tarski(sK36,X0) ),
    inference(instantiation,[status(thm)],[c_173])).

cnf(c_99415,plain,
    ( r1_xboole_0(sK36,sK36)
    | ~ r1_xboole_0(sK37,sK36)
    | ~ r1_tarski(sK36,sK37) ),
    inference(instantiation,[status(thm)],[c_17414])).

cnf(c_99426,plain,
    ( r1_xboole_0(sK36,sK36) = iProver_top
    | r1_xboole_0(sK37,sK36) != iProver_top
    | r1_tarski(sK36,sK37) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_99415])).

cnf(c_43475,plain,
    ( k5_xboole_0(k1_tarski(sK35),sK37) = k4_xboole_0(sK36,sK37) ),
    inference(superposition,[status(thm)],[c_40425,c_29082])).

cnf(c_89323,plain,
    ( k4_xboole_0(sK36,sK37) = k5_xboole_0(sK37,sK37) ),
    inference(demodulation,[status(thm)],[c_89273,c_43475])).

cnf(c_89340,plain,
    ( k4_xboole_0(sK36,sK37) = o_0_0_xboole_0 ),
    inference(demodulation,[status(thm)],[c_89323,c_212])).

cnf(c_91848,plain,
    ( k4_xboole_0(sK37,sK36) != o_0_0_xboole_0
    | sK36 = sK37 ),
    inference(superposition,[status(thm)],[c_89340,c_136])).

cnf(c_91858,plain,
    ( k5_xboole_0(sK37,sK36) != o_0_0_xboole_0
    | sK36 = sK37 ),
    inference(light_normalisation,[status(thm)],[c_91848,c_89276])).

cnf(c_18164,plain,
    ( r1_tarski(sK36,sK37)
    | k4_xboole_0(sK36,sK37) != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_142])).

cnf(c_18182,plain,
    ( k4_xboole_0(sK36,sK37) != o_0_0_xboole_0
    | r1_tarski(sK36,sK37) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18164])).

cnf(c_176,plain,
    ( ~ r1_xboole_0(X0,X0)
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f1243])).

cnf(c_14837,plain,
    ( ~ r1_xboole_0(sK36,sK36)
    | o_0_0_xboole_0 = sK36 ),
    inference(instantiation,[status(thm)],[c_176])).

cnf(c_14844,plain,
    ( o_0_0_xboole_0 = sK36
    | r1_xboole_0(sK36,sK36) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14837])).

cnf(c_467,negated_conjecture,
    ( o_0_0_xboole_0 != sK36 ),
    inference(cnf_transformation,[],[f1437])).

cnf(c_468,negated_conjecture,
    ( sK36 != sK37 ),
    inference(cnf_transformation,[],[f1118])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_146181,c_139413,c_99426,c_91858,c_89340,c_18182,c_14844,c_467,c_468])).

%------------------------------------------------------------------------------
