%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0276+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:21 EST 2020

% Result     : Theorem 1.34s
% Output     : Refutation 1.34s
% Verified   : 
% Statistics : Number of formulae       :   23 (  44 expanded)
%              Number of leaves         :    5 (  14 expanded)
%              Depth                    :    7
%              Number of atoms          :   76 ( 154 expanded)
%              Number of equality atoms :   65 ( 143 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1854,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1739,f939])).

fof(f939,plain,(
    k4_xboole_0(k2_tarski(sK16,sK17),sK18) != k2_tarski(sK16,sK16) ),
    inference(definition_unfolding,[],[f641,f741])).

fof(f741,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f254])).

fof(f254,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f641,plain,(
    k4_xboole_0(k2_tarski(sK16,sK17),sK18) != k1_tarski(sK16) ),
    inference(cnf_transformation,[],[f533])).

fof(f533,plain,
    ( k2_tarski(sK16,sK17) != k4_xboole_0(k2_tarski(sK16,sK17),sK18)
    & k4_xboole_0(k2_tarski(sK16,sK17),sK18) != k1_tarski(sK17)
    & k4_xboole_0(k2_tarski(sK16,sK17),sK18) != k1_tarski(sK16)
    & k1_xboole_0 != k4_xboole_0(k2_tarski(sK16,sK17),sK18) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK16,sK17,sK18])],[f381,f532])).

fof(f532,plain,
    ( ? [X0,X1,X2] :
        ( k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)
        & k1_tarski(X1) != k4_xboole_0(k2_tarski(X0,X1),X2)
        & k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)
        & k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) )
   => ( k2_tarski(sK16,sK17) != k4_xboole_0(k2_tarski(sK16,sK17),sK18)
      & k4_xboole_0(k2_tarski(sK16,sK17),sK18) != k1_tarski(sK17)
      & k4_xboole_0(k2_tarski(sK16,sK17),sK18) != k1_tarski(sK16)
      & k1_xboole_0 != k4_xboole_0(k2_tarski(sK16,sK17),sK18) ) ),
    introduced(choice_axiom,[])).

fof(f381,plain,(
    ? [X0,X1,X2] :
      ( k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)
      & k1_tarski(X1) != k4_xboole_0(k2_tarski(X0,X1),X2)
      & k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)
      & k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f374])).

fof(f374,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)
          & k1_tarski(X1) != k4_xboole_0(k2_tarski(X0,X1),X2)
          & k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)
          & k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(negated_conjecture,[],[f373])).

fof(f373,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)
        & k1_tarski(X1) != k4_xboole_0(k2_tarski(X0,X1),X2)
        & k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)
        & k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_zfmisc_1)).

fof(f1739,plain,(
    k4_xboole_0(k2_tarski(sK16,sK17),sK18) = k2_tarski(sK16,sK16) ),
    inference(unit_resulting_resolution,[],[f640,f693,f643,f938,f996])).

fof(f996,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = X0
      | k2_tarski(X2,X2) = X0
      | k2_tarski(X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(definition_unfolding,[],[f757,f741,f741])).

fof(f757,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = X0
      | k1_tarski(X2) = X0
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f577])).

fof(f577,plain,(
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
    inference(flattening,[],[f576])).

fof(f576,plain,(
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
    inference(nnf_transformation,[],[f419])).

fof(f419,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f343])).

fof(f343,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_zfmisc_1)).

fof(f938,plain,(
    k4_xboole_0(k2_tarski(sK16,sK17),sK18) != k2_tarski(sK17,sK17) ),
    inference(definition_unfolding,[],[f642,f741])).

fof(f642,plain,(
    k4_xboole_0(k2_tarski(sK16,sK17),sK18) != k1_tarski(sK17) ),
    inference(cnf_transformation,[],[f533])).

fof(f643,plain,(
    k2_tarski(sK16,sK17) != k4_xboole_0(k2_tarski(sK16,sK17),sK18) ),
    inference(cnf_transformation,[],[f533])).

fof(f693,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f96])).

fof(f96,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f640,plain,(
    k1_xboole_0 != k4_xboole_0(k2_tarski(sK16,sK17),sK18) ),
    inference(cnf_transformation,[],[f533])).
%------------------------------------------------------------------------------
