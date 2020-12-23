%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0274+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:21 EST 2020

% Result     : Theorem 2.13s
% Output     : Refutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 197 expanded)
%              Number of leaves         :    9 (  53 expanded)
%              Depth                    :   20
%              Number of atoms          :  158 ( 567 expanded)
%              Number of equality atoms :   58 ( 212 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2275,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2260,f1585])).

fof(f1585,plain,(
    r2_hidden(sK19,sK20) ),
    inference(subsumption_resolution,[],[f1584,f1462])).

fof(f1462,plain,(
    ~ r2_hidden(sK18,sK20) ),
    inference(subsumption_resolution,[],[f1455,f995])).

fof(f995,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(k2_enumset1(X0,X0,X0,X1),X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f653,f818])).

fof(f818,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(cnf_transformation,[],[f262])).

fof(f262,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).

fof(f653,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f381])).

fof(f381,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f356])).

fof(f356,axiom,(
    ! [X0,X1,X2] :
      ~ ( r2_hidden(X0,X2)
        & r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).

fof(f1455,plain,
    ( r1_xboole_0(k2_enumset1(sK18,sK18,sK18,sK19),sK20)
    | ~ r2_hidden(sK18,sK20) ),
    inference(trivial_inequality_removal,[],[f1391])).

fof(f1391,plain,
    ( k2_enumset1(sK18,sK18,sK18,sK19) != k2_enumset1(sK18,sK18,sK18,sK19)
    | r1_xboole_0(k2_enumset1(sK18,sK18,sK18,sK19),sK20)
    | ~ r2_hidden(sK18,sK20) ),
    inference(superposition,[],[f883,f993])).

fof(f993,plain,
    ( k2_enumset1(sK18,sK18,sK18,sK19) = k4_xboole_0(k2_enumset1(sK18,sK18,sK18,sK19),sK20)
    | ~ r2_hidden(sK18,sK20) ),
    inference(definition_unfolding,[],[f649,f818,f818])).

fof(f649,plain,
    ( ~ r2_hidden(sK18,sK20)
    | k2_tarski(sK18,sK19) = k4_xboole_0(k2_tarski(sK18,sK19),sK20) ),
    inference(cnf_transformation,[],[f538])).

fof(f538,plain,
    ( ( r2_hidden(sK19,sK20)
      | r2_hidden(sK18,sK20)
      | k2_tarski(sK18,sK19) != k4_xboole_0(k2_tarski(sK18,sK19),sK20) )
    & ( ( ~ r2_hidden(sK19,sK20)
        & ~ r2_hidden(sK18,sK20) )
      | k2_tarski(sK18,sK19) = k4_xboole_0(k2_tarski(sK18,sK19),sK20) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK18,sK19,sK20])],[f536,f537])).

fof(f537,plain,
    ( ? [X0,X1,X2] :
        ( ( r2_hidden(X1,X2)
          | r2_hidden(X0,X2)
          | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) )
        & ( ( ~ r2_hidden(X1,X2)
            & ~ r2_hidden(X0,X2) )
          | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) ) )
   => ( ( r2_hidden(sK19,sK20)
        | r2_hidden(sK18,sK20)
        | k2_tarski(sK18,sK19) != k4_xboole_0(k2_tarski(sK18,sK19),sK20) )
      & ( ( ~ r2_hidden(sK19,sK20)
          & ~ r2_hidden(sK18,sK20) )
        | k2_tarski(sK18,sK19) = k4_xboole_0(k2_tarski(sK18,sK19),sK20) ) ) ),
    introduced(choice_axiom,[])).

fof(f536,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,X2)
        | r2_hidden(X0,X2)
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f535])).

fof(f535,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,X2)
        | r2_hidden(X0,X2)
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f379])).

fof(f379,plain,(
    ? [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <~> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f372])).

fof(f372,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
      <=> ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f371])).

fof(f371,conjecture,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).

fof(f883,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f624])).

fof(f624,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f153])).

fof(f153,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f1584,plain,
    ( r2_hidden(sK19,sK20)
    | r2_hidden(sK18,sK20) ),
    inference(duplicate_literal_removal,[],[f1578])).

fof(f1578,plain,
    ( r2_hidden(sK19,sK20)
    | r2_hidden(sK19,sK20)
    | r2_hidden(sK18,sK20) ),
    inference(resolution,[],[f1570,f996])).

fof(f996,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f658,f818])).

fof(f658,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f383])).

fof(f383,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f358])).

fof(f358,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_xboole_0(k2_tarski(X0,X2),X1)
        & ~ r2_hidden(X2,X1)
        & ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_zfmisc_1)).

fof(f1570,plain,
    ( ~ r1_xboole_0(k2_enumset1(sK18,sK18,sK18,sK19),sK20)
    | r2_hidden(sK19,sK20) ),
    inference(trivial_inequality_removal,[],[f1568])).

fof(f1568,plain,
    ( k2_enumset1(sK18,sK18,sK18,sK19) != k2_enumset1(sK18,sK18,sK18,sK19)
    | r2_hidden(sK19,sK20)
    | ~ r1_xboole_0(k2_enumset1(sK18,sK18,sK18,sK19),sK20) ),
    inference(superposition,[],[f1559,f882])).

fof(f882,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f624])).

fof(f1559,plain,
    ( k2_enumset1(sK18,sK18,sK18,sK19) != k4_xboole_0(k2_enumset1(sK18,sK18,sK18,sK19),sK20)
    | r2_hidden(sK19,sK20) ),
    inference(subsumption_resolution,[],[f991,f1462])).

fof(f991,plain,
    ( r2_hidden(sK19,sK20)
    | r2_hidden(sK18,sK20)
    | k2_enumset1(sK18,sK18,sK18,sK19) != k4_xboole_0(k2_enumset1(sK18,sK18,sK18,sK19),sK20) ),
    inference(definition_unfolding,[],[f651,f818,f818])).

fof(f651,plain,
    ( r2_hidden(sK19,sK20)
    | r2_hidden(sK18,sK20)
    | k2_tarski(sK18,sK19) != k4_xboole_0(k2_tarski(sK18,sK19),sK20) ),
    inference(cnf_transformation,[],[f538])).

fof(f2260,plain,(
    ~ r2_hidden(sK19,sK20) ),
    inference(resolution,[],[f2248,f995])).

fof(f2248,plain,(
    r1_xboole_0(k2_enumset1(sK19,sK19,sK19,sK19),sK20) ),
    inference(resolution,[],[f2177,f1181])).

fof(f1181,plain,(
    ! [X2,X1] : r1_tarski(k2_enumset1(X2,X2,X2,X2),k2_enumset1(X1,X1,X1,X2)) ),
    inference(equality_resolution,[],[f1077])).

fof(f1077,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_enumset1(X1,X1,X1,X2))
      | k2_enumset1(X2,X2,X2,X2) != X0 ) ),
    inference(definition_unfolding,[],[f810,f818,f988])).

fof(f988,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f824,f818])).

fof(f824,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f254])).

fof(f254,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f810,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X2) != X0 ) ),
    inference(cnf_transformation,[],[f618])).

fof(f618,plain,(
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
    inference(flattening,[],[f617])).

fof(f617,plain,(
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
    inference(nnf_transformation,[],[f431])).

fof(f431,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f307])).

fof(f307,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

fof(f2177,plain,(
    ! [X17] :
      ( ~ r1_tarski(X17,k2_enumset1(sK18,sK18,sK18,sK19))
      | r1_xboole_0(X17,sK20) ) ),
    inference(subsumption_resolution,[],[f1230,f1585])).

fof(f1230,plain,(
    ! [X17] :
      ( ~ r1_tarski(X17,k2_enumset1(sK18,sK18,sK18,sK19))
      | r1_xboole_0(X17,sK20)
      | ~ r2_hidden(sK19,sK20) ) ),
    inference(superposition,[],[f873,f992])).

fof(f992,plain,
    ( k2_enumset1(sK18,sK18,sK18,sK19) = k4_xboole_0(k2_enumset1(sK18,sK18,sK18,sK19),sK20)
    | ~ r2_hidden(sK19,sK20) ),
    inference(definition_unfolding,[],[f650,f818,f818])).

fof(f650,plain,
    ( ~ r2_hidden(sK19,sK20)
    | k2_tarski(sK18,sK19) = k4_xboole_0(k2_tarski(sK18,sK19),sK20) ),
    inference(cnf_transformation,[],[f538])).

fof(f873,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f473])).

fof(f473,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f54])).

fof(f54,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).
%------------------------------------------------------------------------------
