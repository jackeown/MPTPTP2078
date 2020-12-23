%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0260+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:31 EST 2020

% Result     : Theorem 11.50s
% Output     : CNFRefutation 11.50s
% Verified   : 
% Statistics : Number of formulae       :   48 (  67 expanded)
%              Number of clauses        :   12 (  14 expanded)
%              Number of leaves         :   11 (  18 expanded)
%              Depth                    :   12
%              Number of atoms          :  157 ( 183 expanded)
%              Number of equality atoms :   70 (  84 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f176,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f597,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f176])).

fof(f598,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f597])).

fof(f599,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f598])).

fof(f600,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK21(X0,X1,X2) != X1
            & sK21(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK21(X0,X1,X2),X2) )
        & ( sK21(X0,X1,X2) = X1
          | sK21(X0,X1,X2) = X0
          | r2_hidden(sK21(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f601,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK21(X0,X1,X2) != X1
              & sK21(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK21(X0,X1,X2),X2) )
          & ( sK21(X0,X1,X2) = X1
            | sK21(X0,X1,X2) = X0
            | r2_hidden(sK21(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK21])],[f599,f600])).

fof(f897,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f601])).

fof(f226,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f972,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f226])).

fof(f166,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f876,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f166])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f816,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f1155,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f876,f816])).

fof(f1156,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f972,f1155])).

fof(f1315,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))) != X2 ) ),
    inference(definition_unfolding,[],[f897,f1156])).

fof(f1506,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k5_xboole_0(k5_xboole_0(k1_tarski(X4),k1_tarski(X1)),k4_xboole_0(k1_tarski(X4),k4_xboole_0(k1_tarski(X4),k1_tarski(X1)))) != X2 ) ),
    inference(equality_resolution,[],[f1315])).

fof(f1507,plain,(
    ! [X4,X1] : r2_hidden(X4,k5_xboole_0(k5_xboole_0(k1_tarski(X4),k1_tarski(X1)),k4_xboole_0(k1_tarski(X4),k4_xboole_0(k1_tarski(X4),k1_tarski(X1))))) ),
    inference(equality_resolution,[],[f1506])).

fof(f163,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f873,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f163])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f665,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f32,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f364,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f32])).

fof(f375,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f364])).

fof(f565,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK13(X0,X1),X1)
        & r2_hidden(sK13(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f566,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK13(X0,X1),X1)
          & r2_hidden(sK13(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13])],[f375,f565])).

fof(f717,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f566])).

fof(f356,conjecture,(
    ! [X0,X1,X2] :
      ~ ( r2_hidden(X0,X2)
        & r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f357,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( r2_hidden(X0,X2)
          & r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(negated_conjecture,[],[f356])).

fof(f518,plain,(
    ? [X0,X1,X2] :
      ( r2_hidden(X0,X2)
      & r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f357])).

fof(f659,plain,
    ( ? [X0,X1,X2] :
        ( r2_hidden(X0,X2)
        & r1_xboole_0(k2_tarski(X0,X1),X2) )
   => ( r2_hidden(sK35,sK37)
      & r1_xboole_0(k2_tarski(sK35,sK36),sK37) ) ),
    introduced(choice_axiom,[])).

fof(f660,plain,
    ( r2_hidden(sK35,sK37)
    & r1_xboole_0(k2_tarski(sK35,sK36),sK37) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK35,sK36,sK37])],[f518,f659])).

fof(f1150,plain,(
    r1_xboole_0(k2_tarski(sK35,sK36),sK37) ),
    inference(cnf_transformation,[],[f660])).

fof(f1477,plain,(
    r1_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k1_tarski(sK36)),k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),k1_tarski(sK36)))),sK37) ),
    inference(definition_unfolding,[],[f1150,f1156])).

fof(f1151,plain,(
    r2_hidden(sK35,sK37) ),
    inference(cnf_transformation,[],[f660])).

cnf(c_237,plain,
    ( r2_hidden(X0,k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))) ),
    inference(cnf_transformation,[],[f1507])).

cnf(c_211,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f873])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f665])).

cnf(c_8439,plain,
    ( r2_hidden(X0,k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))))) ),
    inference(theory_normalisation,[status(thm)],[c_237,c_211,c_7])).

cnf(c_16756,plain,
    ( r2_hidden(sK35,k5_xboole_0(k1_tarski(sK35),k5_xboole_0(k1_tarski(sK36),k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),k1_tarski(sK36)))))) ),
    inference(instantiation,[status(thm)],[c_8439])).

cnf(c_55,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f717])).

cnf(c_14831,plain,
    ( ~ r1_xboole_0(X0,sK37)
    | ~ r2_hidden(sK35,X0)
    | ~ r2_hidden(sK35,sK37) ),
    inference(instantiation,[status(thm)],[c_55])).

cnf(c_16012,plain,
    ( ~ r1_xboole_0(k5_xboole_0(k1_tarski(sK35),k5_xboole_0(k1_tarski(sK36),k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),k1_tarski(sK36))))),sK37)
    | ~ r2_hidden(sK35,k5_xboole_0(k1_tarski(sK35),k5_xboole_0(k1_tarski(sK36),k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),k1_tarski(sK36))))))
    | ~ r2_hidden(sK35,sK37) ),
    inference(instantiation,[status(thm)],[c_14831])).

cnf(c_478,negated_conjecture,
    ( r1_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k1_tarski(sK36)),k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),k1_tarski(sK36)))),sK37) ),
    inference(cnf_transformation,[],[f1477])).

cnf(c_8322,negated_conjecture,
    ( r1_xboole_0(k5_xboole_0(k1_tarski(sK35),k5_xboole_0(k1_tarski(sK36),k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),k1_tarski(sK36))))),sK37) ),
    inference(theory_normalisation,[status(thm)],[c_478,c_211,c_7])).

cnf(c_477,negated_conjecture,
    ( r2_hidden(sK35,sK37) ),
    inference(cnf_transformation,[],[f1151])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_16756,c_16012,c_8322,c_477])).

%------------------------------------------------------------------------------
