%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0087+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:08 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   24 (  30 expanded)
%              Number of leaves         :    6 (   9 expanded)
%              Depth                    :    6
%              Number of atoms          :   62 (  77 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f360,plain,(
    $false ),
    inference(subsumption_resolution,[],[f354,f319])).

fof(f319,plain,(
    ~ sP5(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f301,f189,f304])).

fof(f304,plain,(
    ! [X0,X3,X1] :
      ( ~ sP5(X3,X0)
      | ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X1,X3) ) ),
    inference(general_splitting,[],[f214,f303_D])).

fof(f303,plain,(
    ! [X2,X0,X3] :
      ( sP5(X3,X0)
      | ~ r1_tarski(X2,X3)
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f303_D])).

fof(f303_D,plain,(
    ! [X0,X3] :
      ( ! [X2] :
          ( ~ r1_tarski(X2,X3)
          | r1_xboole_0(X0,X2) )
    <=> ~ sP5(X3,X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP5])])).

fof(f214,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f145])).

fof(f145,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f144])).

fof(f144,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f106])).

fof(f106,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X1,X3)
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_xboole_1)).

fof(f189,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f182])).

fof(f182,plain,
    ( ~ r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    & r1_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f133,f181])).

fof(f181,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(X0,k4_xboole_0(X1,X2))
        & r1_xboole_0(X0,X1) )
   => ( ~ r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))
      & r1_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f133,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,k4_xboole_0(X1,X2))
      & r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f127])).

fof(f127,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_xboole_0(X0,X1)
       => r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    inference(negated_conjecture,[],[f126])).

fof(f126,conjecture,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_xboole_1)).

fof(f301,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f238])).

fof(f238,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f186])).

fof(f186,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f185])).

fof(f185,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f354,plain,(
    sP5(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f212,f190,f303])).

fof(f190,plain,(
    ~ r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f182])).

fof(f212,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
%------------------------------------------------------------------------------
