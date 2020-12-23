%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0318+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:35 EST 2020

% Result     : Theorem 11.33s
% Output     : CNFRefutation 11.33s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 257 expanded)
%              Number of clauses        :   26 (  44 expanded)
%              Number of leaves         :   14 (  76 expanded)
%              Depth                    :   13
%              Number of atoms          :  171 ( 486 expanded)
%              Number of equality atoms :  138 ( 401 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f341,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
     => ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
        & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f342,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 != X0
       => ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
          & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f341])).

fof(f574,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,k1_tarski(X1))
        | k1_xboole_0 = k2_zfmisc_1(k1_tarski(X1),X0) )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f342])).

fof(f776,plain,
    ( ? [X0,X1] :
        ( ( k1_xboole_0 = k2_zfmisc_1(X0,k1_tarski(X1))
          | k1_xboole_0 = k2_zfmisc_1(k1_tarski(X1),X0) )
        & k1_xboole_0 != X0 )
   => ( ( k1_xboole_0 = k2_zfmisc_1(sK50,k1_tarski(sK51))
        | k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK51),sK50) )
      & k1_xboole_0 != sK50 ) ),
    introduced(choice_axiom,[])).

fof(f777,plain,
    ( ( k1_xboole_0 = k2_zfmisc_1(sK50,k1_tarski(sK51))
      | k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK51),sK50) )
    & k1_xboole_0 != sK50 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK50,sK51])],[f574,f776])).

fof(f1292,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK50,k1_tarski(sK51))
    | k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK51),sK50) ),
    inference(cnf_transformation,[],[f777])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f816,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f1712,plain,
    ( o_0_0_xboole_0 = k2_zfmisc_1(sK50,k1_tarski(sK51))
    | o_0_0_xboole_0 = k2_zfmisc_1(k1_tarski(sK51),sK50) ),
    inference(definition_unfolding,[],[f1292,f816,f816])).

fof(f323,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f770,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f323])).

fof(f771,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f770])).

fof(f1261,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f771])).

fof(f1698,plain,(
    ! [X0,X1] :
      ( o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0
      | o_0_0_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f1261,f816,f816,f816])).

fof(f1291,plain,(
    k1_xboole_0 != sK50 ),
    inference(cnf_transformation,[],[f777])).

fof(f1713,plain,(
    o_0_0_xboole_0 != sK50 ),
    inference(definition_unfolding,[],[f1291,f816])).

fof(f400,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)
    <=> ( ( X0 = X1
          | r2_hidden(X1,X2) )
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f795,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)
        | ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f400])).

fof(f796,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)
        | ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0) ) ) ),
    inference(flattening,[],[f795])).

fof(f1379,plain,(
    ! [X2,X0,X1] :
      ( X0 = X1
      | r2_hidden(X1,X2)
      | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f796])).

fof(f226,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1120,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f226])).

fof(f166,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1024,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f166])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f964,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f1415,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f1024,f964])).

fof(f1416,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f1120,f1415])).

fof(f1775,plain,(
    ! [X2,X0,X1] :
      ( X0 = X1
      | r2_hidden(X1,X2)
      | k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),X2) != k1_tarski(X0) ) ),
    inference(definition_unfolding,[],[f1379,f1416])).

fof(f1381,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)
      | X0 != X1
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f796])).

fof(f1773,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),X2) = k1_tarski(X0)
      | X0 != X1
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f1381,f1416])).

fof(f1882,plain,(
    ! [X2,X1] :
      ( k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X1)),k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k1_tarski(X1)))),X2) = k1_tarski(X1)
      | r2_hidden(X1,X2) ) ),
    inference(equality_resolution,[],[f1773])).

fof(f381,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1353,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f381])).

fof(f1758,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),X2),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),X2))) != o_0_0_xboole_0 ),
    inference(definition_unfolding,[],[f1353,f1415,f1416,f816])).

fof(f379,axiom,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
     => k2_xboole_0(k2_tarski(X0,X2),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f597,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(k2_tarski(X0,X2),X1) = X1
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f379])).

fof(f598,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(k2_tarski(X0,X2),X1) = X1
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f597])).

fof(f1351,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(k2_tarski(X0,X2),X1) = X1
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f598])).

fof(f1756,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X2)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X2)))),X1),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X2)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X2)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X2)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X2)))),X1))) = X1
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f1351,f1415,f1416])).

fof(f350,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f778,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
        | X0 = X1 )
      & ( X0 != X1
        | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f350])).

fof(f1300,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f778])).

fof(f1871,plain,(
    ! [X1] : k4_xboole_0(k1_tarski(X1),k1_tarski(X1)) != k1_tarski(X1) ),
    inference(equality_resolution,[],[f1300])).

fof(f88,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f941,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f88])).

fof(f1502,plain,(
    ! [X0] : o_0_0_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,o_0_0_xboole_0)) ),
    inference(definition_unfolding,[],[f941,f964,f816,f816])).

fof(f100,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f954,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f100])).

fof(f1510,plain,(
    ! [X0] : k4_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f954,f816])).

cnf(c_470,negated_conjecture,
    ( o_0_0_xboole_0 = k2_zfmisc_1(k1_tarski(sK51),sK50)
    | o_0_0_xboole_0 = k2_zfmisc_1(sK50,k1_tarski(sK51)) ),
    inference(cnf_transformation,[],[f1712])).

cnf(c_442,plain,
    ( k2_zfmisc_1(X0,X1) != o_0_0_xboole_0
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f1698])).

cnf(c_25122,plain,
    ( k2_zfmisc_1(sK50,k1_tarski(sK51)) = o_0_0_xboole_0
    | k1_tarski(sK51) = o_0_0_xboole_0
    | sK50 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_470,c_442])).

cnf(c_471,negated_conjecture,
    ( o_0_0_xboole_0 != sK50 ),
    inference(cnf_transformation,[],[f1713])).

cnf(c_559,plain,
    ( r2_hidden(X0,X1)
    | X0 = X2
    | k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X2),k1_tarski(X0)),k4_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X2),k1_tarski(X0)))),X1) != k1_tarski(X2) ),
    inference(cnf_transformation,[],[f1775])).

cnf(c_667,plain,
    ( r2_hidden(o_0_0_xboole_0,o_0_0_xboole_0)
    | k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(o_0_0_xboole_0),k1_tarski(o_0_0_xboole_0)),k4_xboole_0(k1_tarski(o_0_0_xboole_0),k4_xboole_0(k1_tarski(o_0_0_xboole_0),k1_tarski(o_0_0_xboole_0)))),o_0_0_xboole_0) != k1_tarski(o_0_0_xboole_0)
    | o_0_0_xboole_0 = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_559])).

cnf(c_557,plain,
    ( r2_hidden(X0,X1)
    | k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X0)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X0)))),X1) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1882])).

cnf(c_671,plain,
    ( r2_hidden(o_0_0_xboole_0,o_0_0_xboole_0)
    | k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(o_0_0_xboole_0),k1_tarski(o_0_0_xboole_0)),k4_xboole_0(k1_tarski(o_0_0_xboole_0),k4_xboole_0(k1_tarski(o_0_0_xboole_0),k1_tarski(o_0_0_xboole_0)))),o_0_0_xboole_0) = k1_tarski(o_0_0_xboole_0) ),
    inference(instantiation,[status(thm)],[c_557])).

cnf(c_532,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),X2),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),X2))) != o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1758])).

cnf(c_739,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(o_0_0_xboole_0),k1_tarski(o_0_0_xboole_0)),k4_xboole_0(k1_tarski(o_0_0_xboole_0),k4_xboole_0(k1_tarski(o_0_0_xboole_0),k1_tarski(o_0_0_xboole_0)))),o_0_0_xboole_0),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(o_0_0_xboole_0),k1_tarski(o_0_0_xboole_0)),k4_xboole_0(k1_tarski(o_0_0_xboole_0),k4_xboole_0(k1_tarski(o_0_0_xboole_0),k1_tarski(o_0_0_xboole_0)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(o_0_0_xboole_0),k1_tarski(o_0_0_xboole_0)),k4_xboole_0(k1_tarski(o_0_0_xboole_0),k4_xboole_0(k1_tarski(o_0_0_xboole_0),k1_tarski(o_0_0_xboole_0)))),o_0_0_xboole_0))) != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_532])).

cnf(c_530,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X2)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X2)))),X1),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X2)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X2)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X2)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X2)))),X1))) = X1 ),
    inference(cnf_transformation,[],[f1756])).

cnf(c_742,plain,
    ( ~ r2_hidden(o_0_0_xboole_0,o_0_0_xboole_0)
    | k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(o_0_0_xboole_0),k1_tarski(o_0_0_xboole_0)),k4_xboole_0(k1_tarski(o_0_0_xboole_0),k4_xboole_0(k1_tarski(o_0_0_xboole_0),k1_tarski(o_0_0_xboole_0)))),o_0_0_xboole_0),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(o_0_0_xboole_0),k1_tarski(o_0_0_xboole_0)),k4_xboole_0(k1_tarski(o_0_0_xboole_0),k4_xboole_0(k1_tarski(o_0_0_xboole_0),k1_tarski(o_0_0_xboole_0)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(o_0_0_xboole_0),k1_tarski(o_0_0_xboole_0)),k4_xboole_0(k1_tarski(o_0_0_xboole_0),k4_xboole_0(k1_tarski(o_0_0_xboole_0),k1_tarski(o_0_0_xboole_0)))),o_0_0_xboole_0))) = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_530])).

cnf(c_10154,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_21203,plain,
    ( sK50 != X0
    | o_0_0_xboole_0 != X0
    | o_0_0_xboole_0 = sK50 ),
    inference(instantiation,[status(thm)],[c_10154])).

cnf(c_21204,plain,
    ( sK50 != o_0_0_xboole_0
    | o_0_0_xboole_0 = sK50
    | o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_21203])).

cnf(c_25446,plain,
    ( k1_tarski(sK51) = o_0_0_xboole_0
    | k2_zfmisc_1(sK50,k1_tarski(sK51)) = o_0_0_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_25122,c_471,c_667,c_671,c_739,c_742,c_21204])).

cnf(c_25447,plain,
    ( k2_zfmisc_1(sK50,k1_tarski(sK51)) = o_0_0_xboole_0
    | k1_tarski(sK51) = o_0_0_xboole_0 ),
    inference(renaming,[status(thm)],[c_25446])).

cnf(c_480,plain,
    ( k4_xboole_0(k1_tarski(X0),k1_tarski(X0)) != k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1871])).

cnf(c_132,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,o_0_0_xboole_0)) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1502])).

cnf(c_145,plain,
    ( k4_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f1510])).

cnf(c_17464,plain,
    ( k4_xboole_0(X0,X0) = o_0_0_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_132,c_145])).

cnf(c_17474,plain,
    ( k1_tarski(X0) != o_0_0_xboole_0 ),
    inference(demodulation,[status(thm)],[c_480,c_17464])).

cnf(c_25450,plain,
    ( k2_zfmisc_1(sK50,k1_tarski(sK51)) = o_0_0_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_25447,c_17474])).

cnf(c_25451,plain,
    ( k1_tarski(sK51) = o_0_0_xboole_0
    | sK50 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_25450,c_442])).

cnf(c_26290,plain,
    ( k1_tarski(sK51) = o_0_0_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_25451,c_471,c_667,c_671,c_739,c_742,c_21204])).

cnf(c_26293,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_26290,c_17474])).

%------------------------------------------------------------------------------
