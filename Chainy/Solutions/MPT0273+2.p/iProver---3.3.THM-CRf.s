%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0273+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:32 EST 2020

% Result     : Theorem 42.71s
% Output     : CNFRefutation 42.71s
% Verified   : 
% Statistics : Number of formulae       :  277 (5940 expanded)
%              Number of clauses        :  142 (1727 expanded)
%              Number of leaves         :   38 (1584 expanded)
%              Depth                    :   30
%              Number of atoms          :  641 (11343 expanded)
%              Number of equality atoms :  353 (7870 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f364,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f682,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f364])).

fof(f1190,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f682])).

fof(f370,conjecture,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)
    <=> ( ( X0 = X1
          | r2_hidden(X1,X2) )
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f371,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)
      <=> ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f370])).

fof(f540,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)
    <~> ( ( X0 = X1
          | r2_hidden(X1,X2) )
        & ~ r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f371])).

fof(f685,plain,(
    ? [X0,X1,X2] :
      ( ( ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2)
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f540])).

fof(f686,plain,(
    ? [X0,X1,X2] :
      ( ( ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2)
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0) ) ) ),
    inference(flattening,[],[f685])).

fof(f687,plain,
    ( ? [X0,X1,X2] :
        ( ( ( X0 != X1
            & ~ r2_hidden(X1,X2) )
          | r2_hidden(X0,X2)
          | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0) )
        & ( ( ( X0 = X1
              | r2_hidden(X1,X2) )
            & ~ r2_hidden(X0,X2) )
          | k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0) ) )
   => ( ( ( sK35 != sK36
          & ~ r2_hidden(sK36,sK37) )
        | r2_hidden(sK35,sK37)
        | k4_xboole_0(k2_tarski(sK35,sK36),sK37) != k1_tarski(sK35) )
      & ( ( ( sK35 = sK36
            | r2_hidden(sK36,sK37) )
          & ~ r2_hidden(sK35,sK37) )
        | k4_xboole_0(k2_tarski(sK35,sK36),sK37) = k1_tarski(sK35) ) ) ),
    introduced(choice_axiom,[])).

fof(f688,plain,
    ( ( ( sK35 != sK36
        & ~ r2_hidden(sK36,sK37) )
      | r2_hidden(sK35,sK37)
      | k4_xboole_0(k2_tarski(sK35,sK36),sK37) != k1_tarski(sK35) )
    & ( ( ( sK35 = sK36
          | r2_hidden(sK36,sK37) )
        & ~ r2_hidden(sK35,sK37) )
      | k4_xboole_0(k2_tarski(sK35,sK36),sK37) = k1_tarski(sK35) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK35,sK36,sK37])],[f686,f687])).

fof(f1198,plain,
    ( ~ r2_hidden(sK35,sK37)
    | k4_xboole_0(k2_tarski(sK35,sK36),sK37) = k1_tarski(sK35) ),
    inference(cnf_transformation,[],[f688])).

fof(f226,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1000,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f226])).

fof(f166,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f904,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f166])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f844,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f1204,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f904,f844])).

fof(f1205,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f1000,f1204])).

fof(f1540,plain,
    ( ~ r2_hidden(sK35,sK37)
    | k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k1_tarski(sK36)),k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),k1_tarski(sK36)))),sK37) = k1_tarski(sK35) ),
    inference(definition_unfolding,[],[f1198,f1205])).

fof(f163,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f901,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f163])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f693,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f170,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f908,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f170])).

fof(f1348,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f908,f1204])).

fof(f1201,plain,
    ( sK35 != sK36
    | r2_hidden(sK35,sK37)
    | k4_xboole_0(k2_tarski(sK35,sK36),sK37) != k1_tarski(sK35) ),
    inference(cnf_transformation,[],[f688])).

fof(f1537,plain,
    ( sK35 != sK36
    | r2_hidden(sK35,sK37)
    | k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k1_tarski(sK36)),k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),k1_tarski(sK36)))),sK37) != k1_tarski(sK35) ),
    inference(definition_unfolding,[],[f1201,f1205])).

fof(f338,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f671,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f338])).

fof(f1143,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f671])).

fof(f304,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)
    <=> ( ( X0 = X1
          | r2_hidden(X1,X2) )
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f658,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)
        | ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f304])).

fof(f659,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)
        | ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0) ) ) ),
    inference(flattening,[],[f658])).

fof(f1092,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f659])).

fof(f1465,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),X2) != k1_tarski(X0) ) ),
    inference(definition_unfolding,[],[f1092,f1205])).

fof(f1200,plain,
    ( ~ r2_hidden(sK36,sK37)
    | r2_hidden(sK35,sK37)
    | k4_xboole_0(k2_tarski(sK35,sK36),sK37) != k1_tarski(sK35) ),
    inference(cnf_transformation,[],[f688])).

fof(f1538,plain,
    ( ~ r2_hidden(sK36,sK37)
    | r2_hidden(sK35,sK37)
    | k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k1_tarski(sK36)),k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),k1_tarski(sK36)))),sK37) != k1_tarski(sK35) ),
    inference(definition_unfolding,[],[f1200,f1205])).

fof(f1199,plain,
    ( sK35 = sK36
    | r2_hidden(sK36,sK37)
    | k4_xboole_0(k2_tarski(sK35,sK36),sK37) = k1_tarski(sK35) ),
    inference(cnf_transformation,[],[f688])).

fof(f1539,plain,
    ( sK35 = sK36
    | r2_hidden(sK36,sK37)
    | k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k1_tarski(sK36)),k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),k1_tarski(sK36)))),sK37) = k1_tarski(sK35) ),
    inference(definition_unfolding,[],[f1199,f1205])).

fof(f359,axiom,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
      | r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1181,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
      | r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f359])).

fof(f1528,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),X1)) = k1_tarski(X0)
      | r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(definition_unfolding,[],[f1181,f844])).

fof(f355,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f530,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f355])).

fof(f1177,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f530])).

fof(f109,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f843,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f109])).

fof(f1308,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f843,f844])).

fof(f48,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f771,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

fof(f1215,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f771,f844])).

fof(f96,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f829,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f96])).

fof(f320,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f668,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
        | X0 = X1 )
      & ( X0 != X1
        | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f320])).

fof(f1121,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f668])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f692,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f1218,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f692,f844,f844])).

fof(f164,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f902,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f164])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f696,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f1345,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = o_0_0_xboole_0 ),
    inference(definition_unfolding,[],[f902,f696])).

fof(f124,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f858,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f124])).

fof(f1318,plain,(
    ! [X0] : k5_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f858,f696])).

fof(f111,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f845,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f111])).

fof(f1309,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f845,f844,f844])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f594,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f595,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f594])).

fof(f757,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f595])).

fof(f175,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f614,plain,(
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

fof(f615,plain,(
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
    inference(rectify,[],[f614])).

fof(f616,plain,(
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

fof(f617,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK20])],[f615,f616])).

fof(f920,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f617])).

fof(f1566,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f920])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f385,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f579,plain,(
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
    inference(nnf_transformation,[],[f385])).

fof(f735,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f579])).

fof(f55,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k5_xboole_0(X1,X2))
    <=> ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f601,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k5_xboole_0(X1,X2))
        | ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
        | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) )
      & ( ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,k2_xboole_0(X1,X2)) )
        | ~ r1_tarski(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f55])).

fof(f602,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k5_xboole_0(X1,X2))
        | ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
        | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) )
      & ( ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,k2_xboole_0(X1,X2)) )
        | ~ r1_tarski(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(flattening,[],[f601])).

fof(f782,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f602])).

fof(f1257,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))))
      | ~ r1_tarski(X0,k5_xboole_0(X1,X2)) ) ),
    inference(definition_unfolding,[],[f782,f1204])).

fof(f105,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f435,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f105])).

fof(f839,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f435])).

fof(f1304,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ) ),
    inference(definition_unfolding,[],[f839,f1204])).

fof(f156,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f476,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f156])).

fof(f477,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f476])).

fof(f894,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f477])).

fof(f88,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f821,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f88])).

fof(f1291,plain,(
    ! [X0] : o_0_0_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,o_0_0_xboole_0)) ),
    inference(definition_unfolding,[],[f821,f844,f696,f696])).

fof(f100,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f834,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f100])).

fof(f1299,plain,(
    ! [X0] : k4_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f834,f696])).

fof(f147,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f884,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f147])).

fof(f363,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f680,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f363])).

fof(f681,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f680])).

fof(f1187,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f681])).

fof(f1621,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k4_xboole_0(X1,k1_tarski(X2))) ),
    inference(equality_resolution,[],[f1187])).

fof(f339,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f672,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f339])).

fof(f673,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f672])).

fof(f1147,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f673])).

fof(f1496,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f1147,f1205])).

fof(f343,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f518,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f343])).

fof(f678,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f518])).

fof(f679,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(flattening,[],[f678])).

fof(f1156,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X1) != X0 ) ),
    inference(cnf_transformation,[],[f679])).

fof(f1505,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k1_tarski(X2)))))
      | k1_tarski(X1) != X0 ) ),
    inference(definition_unfolding,[],[f1156,f1205])).

fof(f1618,plain,(
    ! [X2,X1] : r1_tarski(k1_tarski(X1),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k1_tarski(X2))))) ),
    inference(equality_resolution,[],[f1505])).

fof(f367,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f684,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f367])).

fof(f1194,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f684])).

fof(f1535,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | o_0_0_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(definition_unfolding,[],[f1194,f696])).

fof(f108,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f842,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f108])).

fof(f1307,plain,(
    ! [X0,X1] : o_0_0_xboole_0 = k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f842,f696,f1204])).

fof(f60,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k4_xboole_0(X0,X2),X1) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f789,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k4_xboole_0(X0,X2),X1) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f60])).

fof(f1260,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(k4_xboole_0(X0,X2),X1)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
    inference(definition_unfolding,[],[f789,f844,f844,f844])).

cnf(c_488,plain,
    ( r2_hidden(X0,X1)
    | k4_xboole_0(X1,k1_tarski(X0)) = X1 ),
    inference(cnf_transformation,[],[f1190])).

cnf(c_14426,plain,
    ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    | r2_hidden(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_488])).

cnf(c_500,negated_conjecture,
    ( ~ r2_hidden(sK35,sK37)
    | k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k1_tarski(sK36)),k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),k1_tarski(sK36)))),sK37) = k1_tarski(sK35) ),
    inference(cnf_transformation,[],[f1540])).

cnf(c_211,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f901])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f693])).

cnf(c_8652,negated_conjecture,
    ( ~ r2_hidden(sK35,sK37)
    | k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k5_xboole_0(k1_tarski(sK36),k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),k1_tarski(sK36))))),sK37) = k1_tarski(sK35) ),
    inference(theory_normalisation,[status(thm)],[c_500,c_211,c_7])).

cnf(c_14421,plain,
    ( k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k5_xboole_0(k1_tarski(sK36),k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),k1_tarski(sK36))))),sK37) = k1_tarski(sK35)
    | r2_hidden(sK35,sK37) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8652])).

cnf(c_217,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f1348])).

cnf(c_8794,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(theory_normalisation,[status(thm)],[c_217,c_211,c_7])).

cnf(c_14772,plain,
    ( k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),sK37) = k1_tarski(sK35)
    | r2_hidden(sK35,sK37) != iProver_top ),
    inference(demodulation,[status(thm)],[c_14421,c_8794])).

cnf(c_81951,plain,
    ( k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),sK37) = k1_tarski(sK35)
    | k4_xboole_0(sK37,k1_tarski(sK35)) = sK37 ),
    inference(superposition,[status(thm)],[c_14426,c_14772])).

cnf(c_8899,plain,
    ( k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k5_xboole_0(k1_tarski(sK36),k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),k1_tarski(sK36))))),sK37) = k1_tarski(sK35)
    | r2_hidden(sK35,sK37) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8652])).

cnf(c_497,negated_conjecture,
    ( r2_hidden(sK35,sK37)
    | k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k1_tarski(sK36)),k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),k1_tarski(sK36)))),sK37) != k1_tarski(sK35)
    | sK35 != sK36 ),
    inference(cnf_transformation,[],[f1537])).

cnf(c_8655,negated_conjecture,
    ( r2_hidden(sK35,sK37)
    | k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k5_xboole_0(k1_tarski(sK36),k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),k1_tarski(sK36))))),sK37) != k1_tarski(sK35)
    | sK36 != sK35 ),
    inference(theory_normalisation,[status(thm)],[c_497,c_211,c_7])).

cnf(c_14424,plain,
    ( k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k5_xboole_0(k1_tarski(sK36),k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),k1_tarski(sK36))))),sK37) != k1_tarski(sK35)
    | sK36 != sK35
    | r2_hidden(sK35,sK37) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8655])).

cnf(c_14792,plain,
    ( k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),sK37) != k1_tarski(sK35)
    | sK36 != sK35
    | r2_hidden(sK35,sK37) = iProver_top ),
    inference(demodulation,[status(thm)],[c_14424,c_8794])).

cnf(c_443,plain,
    ( ~ r1_tarski(k1_tarski(X0),X1)
    | r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f1143])).

cnf(c_16460,plain,
    ( ~ r1_tarski(k1_tarski(sK36),sK37)
    | r2_hidden(sK36,sK37) ),
    inference(instantiation,[status(thm)],[c_443])).

cnf(c_16461,plain,
    ( r1_tarski(k1_tarski(sK36),sK37) != iProver_top
    | r2_hidden(sK36,sK37) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16460])).

cnf(c_394,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X2)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X2)))),X1) != k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1465])).

cnf(c_8695,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_xboole_0(k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X2))))),X1) != k1_tarski(X0) ),
    inference(theory_normalisation,[status(thm)],[c_394,c_211,c_7])).

cnf(c_16557,plain,
    ( ~ r2_hidden(sK35,sK37)
    | k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k5_xboole_0(k1_tarski(sK36),k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),k1_tarski(sK36))))),sK37) != k1_tarski(sK35) ),
    inference(instantiation,[status(thm)],[c_8695])).

cnf(c_16558,plain,
    ( k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k5_xboole_0(k1_tarski(sK36),k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),k1_tarski(sK36))))),sK37) != k1_tarski(sK35)
    | r2_hidden(sK35,sK37) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16557])).

cnf(c_498,negated_conjecture,
    ( ~ r2_hidden(sK36,sK37)
    | r2_hidden(sK35,sK37)
    | k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k1_tarski(sK36)),k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),k1_tarski(sK36)))),sK37) != k1_tarski(sK35) ),
    inference(cnf_transformation,[],[f1538])).

cnf(c_8654,negated_conjecture,
    ( ~ r2_hidden(sK36,sK37)
    | r2_hidden(sK35,sK37)
    | k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k5_xboole_0(k1_tarski(sK36),k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),k1_tarski(sK36))))),sK37) != k1_tarski(sK35) ),
    inference(theory_normalisation,[status(thm)],[c_498,c_211,c_7])).

cnf(c_14423,plain,
    ( k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k5_xboole_0(k1_tarski(sK36),k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),k1_tarski(sK36))))),sK37) != k1_tarski(sK35)
    | r2_hidden(sK36,sK37) != iProver_top
    | r2_hidden(sK35,sK37) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8654])).

cnf(c_14799,plain,
    ( k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),sK37) != k1_tarski(sK35)
    | r2_hidden(sK36,sK37) != iProver_top
    | r2_hidden(sK35,sK37) = iProver_top ),
    inference(demodulation,[status(thm)],[c_14423,c_8794])).

cnf(c_16666,plain,
    ( r2_hidden(sK36,sK37) != iProver_top
    | k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),sK37) != k1_tarski(sK35) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14799,c_8899,c_16558])).

cnf(c_16667,plain,
    ( k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),sK37) != k1_tarski(sK35)
    | r2_hidden(sK36,sK37) != iProver_top ),
    inference(renaming,[status(thm)],[c_16666])).

cnf(c_499,negated_conjecture,
    ( r2_hidden(sK36,sK37)
    | k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k1_tarski(sK36)),k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),k1_tarski(sK36)))),sK37) = k1_tarski(sK35)
    | sK35 = sK36 ),
    inference(cnf_transformation,[],[f1539])).

cnf(c_8653,negated_conjecture,
    ( r2_hidden(sK36,sK37)
    | k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k5_xboole_0(k1_tarski(sK36),k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),k1_tarski(sK36))))),sK37) = k1_tarski(sK35)
    | sK36 = sK35 ),
    inference(theory_normalisation,[status(thm)],[c_499,c_211,c_7])).

cnf(c_14422,plain,
    ( k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k5_xboole_0(k1_tarski(sK36),k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),k1_tarski(sK36))))),sK37) = k1_tarski(sK35)
    | sK36 = sK35
    | r2_hidden(sK36,sK37) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8653])).

cnf(c_14787,plain,
    ( k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),sK37) = k1_tarski(sK35)
    | sK36 = sK35
    | r2_hidden(sK36,sK37) = iProver_top ),
    inference(demodulation,[status(thm)],[c_14422,c_8794])).

cnf(c_480,plain,
    ( r1_xboole_0(k1_tarski(X0),X1)
    | k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),X1)) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1528])).

cnf(c_476,plain,
    ( ~ r1_xboole_0(k1_tarski(X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f1177])).

cnf(c_2695,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_xboole_0(k1_tarski(X0),X1) ),
    inference(prop_impl,[status(thm)],[c_476])).

cnf(c_2696,plain,
    ( ~ r1_xboole_0(k1_tarski(X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(renaming,[status(thm)],[c_2695])).

cnf(c_3279,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),X1)) = k1_tarski(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_480,c_2696])).

cnf(c_14418,plain,
    ( k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),X1)) = k1_tarski(X0)
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3279])).

cnf(c_154,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f1308])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f1215])).

cnf(c_26019,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k5_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_154,c_1])).

cnf(c_38078,plain,
    ( k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),X1)) = k1_tarski(X0)
    | r2_hidden(X0,X1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_14418,c_26019])).

cnf(c_38081,plain,
    ( k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),sK37) = k1_tarski(sK35)
    | k5_xboole_0(k1_tarski(sK36),k4_xboole_0(k1_tarski(sK36),sK37)) = k1_tarski(sK36)
    | sK36 = sK35 ),
    inference(superposition,[status(thm)],[c_14787,c_38078])).

cnf(c_140,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f829])).

cnf(c_14602,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_140])).

cnf(c_40012,plain,
    ( k5_xboole_0(k1_tarski(sK36),k4_xboole_0(k1_tarski(sK36),sK37)) = k1_tarski(sK36)
    | sK36 = sK35
    | r1_tarski(k1_tarski(sK35),k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_38081,c_14602])).

cnf(c_419,plain,
    ( X0 = X1
    | k4_xboole_0(k1_tarski(X1),k1_tarski(X0)) = k1_tarski(X1) ),
    inference(cnf_transformation,[],[f1121])).

cnf(c_40002,plain,
    ( k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k1_tarski(sK36)),sK37) = k1_tarski(sK35)
    | k5_xboole_0(k1_tarski(sK36),k4_xboole_0(k1_tarski(sK36),sK37)) = k1_tarski(sK36)
    | sK36 = sK35 ),
    inference(superposition,[status(thm)],[c_419,c_38081])).

cnf(c_6,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f1218])).

cnf(c_27893,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_14602])).

cnf(c_27899,plain,
    ( r1_tarski(k5_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_27893,c_26019])).

cnf(c_43289,plain,
    ( k5_xboole_0(k1_tarski(sK36),k4_xboole_0(k1_tarski(sK36),sK37)) = k1_tarski(sK36)
    | sK36 = sK35
    | r1_tarski(k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k1_tarski(sK36)),k1_tarski(sK35)),sK37) = iProver_top ),
    inference(superposition,[status(thm)],[c_40002,c_27899])).

cnf(c_212,plain,
    ( k5_xboole_0(X0,X0) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1345])).

cnf(c_26420,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(o_0_0_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_212,c_211])).

cnf(c_168,plain,
    ( k5_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f1318])).

cnf(c_22164,plain,
    ( k5_xboole_0(o_0_0_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_168,c_7])).

cnf(c_26445,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_26420,c_22164])).

cnf(c_28552,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(superposition,[status(thm)],[c_7,c_26445])).

cnf(c_28592,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X0) = X1 ),
    inference(superposition,[status(thm)],[c_28552,c_28552])).

cnf(c_43315,plain,
    ( k5_xboole_0(k1_tarski(sK36),k4_xboole_0(k1_tarski(sK36),sK37)) = k1_tarski(sK36)
    | sK36 = sK35
    | r1_tarski(k1_tarski(sK36),sK37) = iProver_top ),
    inference(demodulation,[status(thm)],[c_43289,c_28592])).

cnf(c_43329,plain,
    ( sK36 = sK35
    | k5_xboole_0(k1_tarski(sK36),k4_xboole_0(k1_tarski(sK36),sK37)) = k1_tarski(sK36) ),
    inference(global_propositional_subsumption,[status(thm)],[c_40012,c_16461,c_16667,c_38081,c_43315])).

cnf(c_43330,plain,
    ( k5_xboole_0(k1_tarski(sK36),k4_xboole_0(k1_tarski(sK36),sK37)) = k1_tarski(sK36)
    | sK36 = sK35 ),
    inference(renaming,[status(thm)],[c_43329])).

cnf(c_43341,plain,
    ( sK36 = sK35
    | r1_tarski(k1_tarski(sK36),sK37) = iProver_top ),
    inference(superposition,[status(thm)],[c_43330,c_27899])).

cnf(c_82283,plain,
    ( k4_xboole_0(sK37,k1_tarski(sK35)) = sK37 ),
    inference(global_propositional_subsumption,[status(thm)],[c_81951,c_8899,c_14792,c_16461,c_16558,c_16667,c_43341])).

cnf(c_155,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(cnf_transformation,[],[f1309])).

cnf(c_32160,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(light_normalisation,[status(thm)],[c_155,c_155,c_26019])).

cnf(c_32161,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(demodulation,[status(thm)],[c_32160,c_26019])).

cnf(c_43342,plain,
    ( k5_xboole_0(k1_tarski(sK36),k4_xboole_0(k1_tarski(sK36),k4_xboole_0(sK37,X0))) = k4_xboole_0(k1_tarski(sK36),X0)
    | sK36 = sK35 ),
    inference(superposition,[status(thm)],[c_43330,c_32161])).

cnf(c_82327,plain,
    ( k5_xboole_0(k1_tarski(sK36),k4_xboole_0(k1_tarski(sK36),sK37)) = k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))
    | sK36 = sK35 ),
    inference(superposition,[status(thm)],[c_82283,c_43342])).

cnf(c_15422,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_211,c_7])).

cnf(c_43336,plain,
    ( k5_xboole_0(k1_tarski(sK36),k5_xboole_0(k4_xboole_0(k1_tarski(sK36),sK37),X0)) = k5_xboole_0(k1_tarski(sK36),X0)
    | sK36 = sK35 ),
    inference(superposition,[status(thm)],[c_43330,c_211])).

cnf(c_55351,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k1_tarski(sK36),k4_xboole_0(k1_tarski(sK36),sK37))) = k5_xboole_0(k1_tarski(sK36),X0)
    | sK36 = sK35 ),
    inference(superposition,[status(thm)],[c_15422,c_43336])).

cnf(c_95360,plain,
    ( k5_xboole_0(X0,k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))) = k5_xboole_0(k1_tarski(sK36),X0)
    | sK36 = sK35 ),
    inference(superposition,[status(thm)],[c_82327,c_55351])).

cnf(c_8901,plain,
    ( k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k5_xboole_0(k1_tarski(sK36),k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),k1_tarski(sK36))))),sK37) != k1_tarski(sK35)
    | r2_hidden(sK36,sK37) != iProver_top
    | r2_hidden(sK35,sK37) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8654])).

cnf(c_67,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f757])).

cnf(c_15652,plain,
    ( ~ r1_tarski(k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k5_xboole_0(k1_tarski(sK36),k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),k1_tarski(sK36))))),sK37),k1_tarski(sK35))
    | ~ r1_tarski(k1_tarski(sK35),k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k5_xboole_0(k1_tarski(sK36),k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),k1_tarski(sK36))))),sK37))
    | k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k5_xboole_0(k1_tarski(sK36),k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),k1_tarski(sK36))))),sK37) = k1_tarski(sK35) ),
    inference(instantiation,[status(thm)],[c_67])).

cnf(c_232,plain,
    ( ~ r2_hidden(X0,k1_tarski(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f1566])).

cnf(c_15791,plain,
    ( ~ r2_hidden(sK36,k1_tarski(sK35))
    | sK36 = sK35 ),
    inference(instantiation,[status(thm)],[c_232])).

cnf(c_46,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f735])).

cnf(c_16874,plain,
    ( ~ r2_hidden(sK36,X0)
    | r2_hidden(sK36,k5_xboole_0(X0,k1_tarski(sK35)))
    | r2_hidden(sK36,k1_tarski(sK35)) ),
    inference(instantiation,[status(thm)],[c_46])).

cnf(c_52071,plain,
    ( r2_hidden(sK36,k5_xboole_0(sK37,k1_tarski(sK35)))
    | r2_hidden(sK36,k1_tarski(sK35))
    | ~ r2_hidden(sK36,sK37) ),
    inference(instantiation,[status(thm)],[c_16874])).

cnf(c_95,plain,
    ( ~ r1_tarski(X0,k5_xboole_0(X1,X2))
    | r1_tarski(X0,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(cnf_transformation,[],[f1257])).

cnf(c_150,plain,
    ( ~ r1_tarski(X0,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))))
    | r1_tarski(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1304])).

cnf(c_2679,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X2)
    | ~ r1_tarski(X0,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(prop_impl,[status(thm)],[c_150])).

cnf(c_2680,plain,
    ( ~ r1_tarski(X0,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))))
    | r1_tarski(k4_xboole_0(X0,X1),X2) ),
    inference(renaming,[status(thm)],[c_2679])).

cnf(c_3262,plain,
    ( ~ r1_tarski(X0,k5_xboole_0(X1,X2))
    | r1_tarski(k4_xboole_0(X0,X1),X2) ),
    inference(bin_hyper_res,[status(thm)],[c_95,c_2680])).

cnf(c_53952,plain,
    ( r1_tarski(k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k5_xboole_0(k1_tarski(sK36),k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),k1_tarski(sK36))))),sK37),k1_tarski(sK35))
    | ~ r1_tarski(k5_xboole_0(k1_tarski(sK35),k5_xboole_0(k1_tarski(sK36),k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),k1_tarski(sK36))))),k5_xboole_0(sK37,k1_tarski(sK35))) ),
    inference(instantiation,[status(thm)],[c_3262])).

cnf(c_204,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f894])).

cnf(c_53966,plain,
    ( ~ r1_xboole_0(k1_tarski(sK35),sK37)
    | r1_tarski(k1_tarski(sK35),k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k5_xboole_0(k1_tarski(sK36),k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),k1_tarski(sK36))))),sK37))
    | ~ r1_tarski(k1_tarski(sK35),k5_xboole_0(k1_tarski(sK35),k5_xboole_0(k1_tarski(sK36),k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),k1_tarski(sK36)))))) ),
    inference(instantiation,[status(thm)],[c_204])).

cnf(c_132,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,o_0_0_xboole_0)) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1291])).

cnf(c_145,plain,
    ( k4_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f1299])).

cnf(c_14707,plain,
    ( k4_xboole_0(X0,X0) = o_0_0_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_132,c_145])).

cnf(c_32194,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k5_xboole_0(X0,k4_xboole_0(X0,X1))))) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_32161,c_14707])).

cnf(c_26007,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_6,c_154])).

cnf(c_26462,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_26007,c_26019])).

cnf(c_32200,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) = o_0_0_xboole_0 ),
    inference(demodulation,[status(thm)],[c_32194,c_26462])).

cnf(c_36027,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X0,o_0_0_xboole_0) ),
    inference(superposition,[status(thm)],[c_32200,c_26445])).

cnf(c_36041,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_36027,c_168])).

cnf(c_194,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f884])).

cnf(c_14573,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_194])).

cnf(c_36597,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_36041,c_14573])).

cnf(c_82311,plain,
    ( r1_xboole_0(k1_tarski(sK35),sK37) = iProver_top ),
    inference(superposition,[status(thm)],[c_82283,c_36597])).

cnf(c_82354,plain,
    ( r1_xboole_0(k1_tarski(sK35),sK37) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_82311])).

cnf(c_486,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X0))) ),
    inference(cnf_transformation,[],[f1621])).

cnf(c_14428,plain,
    ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_486])).

cnf(c_82318,plain,
    ( r2_hidden(sK35,sK37) != iProver_top ),
    inference(superposition,[status(thm)],[c_82283,c_14428])).

cnf(c_444,plain,
    ( r1_tarski(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),X2)
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(cnf_transformation,[],[f1496])).

cnf(c_8673,plain,
    ( r1_tarski(k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),X2)
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(theory_normalisation,[status(thm)],[c_444,c_211,c_7])).

cnf(c_109212,plain,
    ( r1_tarski(k5_xboole_0(k1_tarski(sK35),k5_xboole_0(k1_tarski(sK36),k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),k1_tarski(sK36))))),k5_xboole_0(sK37,k1_tarski(sK35)))
    | ~ r2_hidden(sK36,k5_xboole_0(sK37,k1_tarski(sK35)))
    | ~ r2_hidden(sK35,k5_xboole_0(sK37,k1_tarski(sK35))) ),
    inference(instantiation,[status(thm)],[c_8673])).

cnf(c_455,plain,
    ( r1_tarski(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))) ),
    inference(cnf_transformation,[],[f1618])).

cnf(c_8692,plain,
    ( r1_tarski(k1_tarski(X0),k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))))) ),
    inference(theory_normalisation,[status(thm)],[c_455,c_211,c_7])).

cnf(c_109234,plain,
    ( r1_tarski(k1_tarski(sK35),k5_xboole_0(k1_tarski(sK35),k5_xboole_0(k1_tarski(sK36),k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),k1_tarski(sK36)))))) ),
    inference(instantiation,[status(thm)],[c_8692])).

cnf(c_43335,plain,
    ( k5_xboole_0(k1_tarski(sK36),k1_tarski(sK36)) = k4_xboole_0(k1_tarski(sK36),sK37)
    | sK36 = sK35 ),
    inference(superposition,[status(thm)],[c_43330,c_26445])).

cnf(c_43346,plain,
    ( k4_xboole_0(k1_tarski(sK36),sK37) = o_0_0_xboole_0
    | sK36 = sK35 ),
    inference(demodulation,[status(thm)],[c_43335,c_212])).

cnf(c_494,plain,
    ( r2_hidden(X0,X1)
    | k4_xboole_0(k1_tarski(X0),X1) != o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1535])).

cnf(c_14470,plain,
    ( k4_xboole_0(k1_tarski(X0),X1) != o_0_0_xboole_0
    | r2_hidden(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_494])).

cnf(c_119492,plain,
    ( sK36 = sK35
    | r2_hidden(sK36,sK37) = iProver_top ),
    inference(superposition,[status(thm)],[c_43346,c_14470])).

cnf(c_119507,plain,
    ( r2_hidden(sK36,sK37)
    | sK36 = sK35 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_119492])).

cnf(c_153,plain,
    ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1307])).

cnf(c_8815,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = o_0_0_xboole_0 ),
    inference(theory_normalisation,[status(thm)],[c_153,c_211,c_7])).

cnf(c_31299,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) = o_0_0_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_8815,c_8794,c_8815])).

cnf(c_82314,plain,
    ( k4_xboole_0(k1_tarski(sK35),k5_xboole_0(k1_tarski(sK35),sK37)) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_82283,c_31299])).

cnf(c_85973,plain,
    ( k4_xboole_0(k1_tarski(sK35),k5_xboole_0(sK37,k1_tarski(sK35))) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_7,c_82314])).

cnf(c_119502,plain,
    ( r2_hidden(sK35,k5_xboole_0(sK37,k1_tarski(sK35))) = iProver_top ),
    inference(superposition,[status(thm)],[c_85973,c_14470])).

cnf(c_119519,plain,
    ( r2_hidden(sK35,k5_xboole_0(sK37,k1_tarski(sK35))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_119502])).

cnf(c_120337,plain,
    ( sK36 = sK35 ),
    inference(global_propositional_subsumption,[status(thm)],[c_95360,c_8899,c_8901,c_15652,c_15791,c_16558,c_52071,c_53952,c_53966,c_82354,c_109212,c_109234,c_119492,c_119507,c_119519])).

cnf(c_120382,plain,
    ( k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),k1_tarski(sK35))),sK37) != k1_tarski(sK35)
    | sK35 != sK35
    | r2_hidden(sK35,sK37) = iProver_top ),
    inference(demodulation,[status(thm)],[c_120337,c_14792])).

cnf(c_120383,plain,
    ( k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),k1_tarski(sK35))),sK37) != k1_tarski(sK35)
    | r2_hidden(sK35,sK37) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_120382])).

cnf(c_82312,plain,
    ( k4_xboole_0(k1_tarski(sK35),sK37) = k1_tarski(sK35) ),
    inference(superposition,[status(thm)],[c_82283,c_36041])).

cnf(c_100,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X1))) = k4_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(k4_xboole_0(X0,X2),X1)) ),
    inference(cnf_transformation,[],[f1260])).

cnf(c_38788,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X1))) = k4_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(k4_xboole_0(X0,X2),X1)) ),
    inference(light_normalisation,[status(thm)],[c_100,c_100,c_26019])).

cnf(c_38789,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X2,X1))))) = k5_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(k4_xboole_0(X0,X2),X1)) ),
    inference(demodulation,[status(thm)],[c_38788,c_26019,c_32161])).

cnf(c_38790,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X2)) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,X1))) ),
    inference(demodulation,[status(thm)],[c_38789,c_26462])).

cnf(c_82955,plain,
    ( k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),k4_xboole_0(X0,sK37))) = k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),X0)) ),
    inference(superposition,[status(thm)],[c_82312,c_38790])).

cnf(c_26023,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_26019,c_154])).

cnf(c_106790,plain,
    ( k4_xboole_0(k1_tarski(sK35),k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),X0))) = k4_xboole_0(k1_tarski(sK35),k4_xboole_0(X0,sK37)) ),
    inference(superposition,[status(thm)],[c_82955,c_26023])).

cnf(c_106801,plain,
    ( k4_xboole_0(k1_tarski(sK35),k4_xboole_0(X0,sK37)) = k4_xboole_0(k1_tarski(sK35),X0) ),
    inference(demodulation,[status(thm)],[c_106790,c_26023])).

cnf(c_120384,plain,
    ( k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),k1_tarski(sK35))) != k1_tarski(sK35)
    | r2_hidden(sK35,sK37) = iProver_top ),
    inference(demodulation,[status(thm)],[c_120383,c_32161,c_106801])).

cnf(c_120385,plain,
    ( k1_tarski(sK35) != k1_tarski(sK35)
    | r2_hidden(sK35,sK37) = iProver_top ),
    inference(demodulation,[status(thm)],[c_120384,c_168,c_14707])).

cnf(c_120386,plain,
    ( r2_hidden(sK35,sK37) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_120385])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_120386,c_82318])).

%------------------------------------------------------------------------------
