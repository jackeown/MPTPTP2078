%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0029+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:04 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   29 (  55 expanded)
%              Number of leaves         :    7 (  16 expanded)
%              Depth                    :    7
%              Number of atoms          :   83 ( 167 expanded)
%              Number of equality atoms :   18 (  36 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f249,plain,(
    $false ),
    inference(subsumption_resolution,[],[f241,f243])).

fof(f243,plain,(
    ~ r1_tarski(sK6,sK13(sK6,k3_xboole_0(sK6,sK7),sK6)) ),
    inference(unit_resulting_resolution,[],[f233,f200])).

fof(f200,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,sK13(X0,X1,X2))
      | ~ sP5(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f142])).

fof(f142,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_tarski(X0,sK13(X0,X1,X2))
        & r1_tarski(X1,sK13(X0,X1,X2))
        & r1_tarski(X2,sK13(X0,X1,X2)) )
      | ~ sP5(X0,X1,X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13])],[f140,f141])).

fof(f141,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_tarski(X0,X3)
          & r1_tarski(X1,X3)
          & r1_tarski(X2,X3) )
     => ( ~ r1_tarski(X0,sK13(X0,X1,X2))
        & r1_tarski(X1,sK13(X0,X1,X2))
        & r1_tarski(X2,sK13(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f140,plain,(
    ! [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(X0,X3)
          & r1_tarski(X1,X3)
          & r1_tarski(X2,X3) )
      | ~ sP5(X0,X1,X2) ) ),
    inference(rectify,[],[f139])).

fof(f139,plain,(
    ! [X1,X2,X0] :
      ( ? [X3] :
          ( ~ r1_tarski(X1,X3)
          & r1_tarski(X2,X3)
          & r1_tarski(X0,X3) )
      | ~ sP5(X1,X2,X0) ) ),
    inference(nnf_transformation,[],[f108])).

fof(f108,plain,(
    ! [X1,X2,X0] :
      ( ? [X3] :
          ( ~ r1_tarski(X1,X3)
          & r1_tarski(X2,X3)
          & r1_tarski(X0,X3) )
      | ~ sP5(X1,X2,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).

fof(f233,plain,(
    sP5(sK6,k3_xboole_0(sK6,sK7),sK6) ),
    inference(unit_resulting_resolution,[],[f231,f179,f155,f201])).

fof(f201,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X2) = X1
      | sP5(X1,X2,X0)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f109])).

fof(f109,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X2) = X1
      | sP5(X1,X2,X0)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_folding,[],[f82,f108])).

fof(f82,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X2) = X1
      | ? [X3] :
          ( ~ r1_tarski(X1,X3)
          & r1_tarski(X2,X3)
          & r1_tarski(X0,X3) )
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f81])).

fof(f81,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X2) = X1
      | ? [X3] :
          ( ~ r1_tarski(X1,X3)
          & r1_tarski(X2,X3)
          & r1_tarski(X0,X3) )
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f44])).

fof(f44,axiom,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ( r1_tarski(X2,X3)
              & r1_tarski(X0,X3) )
           => r1_tarski(X1,X3) )
        & r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => k2_xboole_0(X0,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_xboole_1)).

fof(f155,plain,(
    sK6 != k2_xboole_0(sK6,k3_xboole_0(sK6,sK7)) ),
    inference(cnf_transformation,[],[f111])).

fof(f111,plain,(
    sK6 != k2_xboole_0(sK6,k3_xboole_0(sK6,sK7)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f70,f110])).

fof(f110,plain,
    ( ? [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) != X0
   => sK6 != k2_xboole_0(sK6,k3_xboole_0(sK6,sK7)) ),
    introduced(choice_axiom,[])).

fof(f70,plain,(
    ? [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) != X0 ),
    inference(ennf_transformation,[],[f55])).

fof(f55,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(negated_conjecture,[],[f54])).

fof(f54,conjecture,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f179,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f231,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f207])).

fof(f207,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f144])).

fof(f144,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f143])).

fof(f143,plain,(
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

fof(f241,plain,(
    r1_tarski(sK6,sK13(sK6,k3_xboole_0(sK6,sK7),sK6)) ),
    inference(unit_resulting_resolution,[],[f233,f198])).

fof(f198,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,sK13(X0,X1,X2))
      | ~ sP5(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f142])).
%------------------------------------------------------------------------------
