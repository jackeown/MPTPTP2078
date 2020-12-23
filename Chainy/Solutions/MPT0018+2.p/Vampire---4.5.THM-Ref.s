%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0018+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:03 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   23 (  30 expanded)
%              Number of leaves         :    6 (  10 expanded)
%              Depth                    :    7
%              Number of atoms          :   47 (  63 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f355,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f255,f260,f353])).

fof(f353,plain,
    ( spl16_1
    | ~ spl16_2 ),
    inference(avatar_contradiction_clause,[],[f352])).

fof(f352,plain,
    ( $false
    | spl16_1
    | ~ spl16_2 ),
    inference(subsumption_resolution,[],[f317,f153])).

fof(f153,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f317,plain,
    ( ~ r1_tarski(sK0,k2_xboole_0(sK0,sK1))
    | spl16_1
    | ~ spl16_2 ),
    inference(unit_resulting_resolution,[],[f254,f259,f188])).

fof(f188,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f84,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f83])).

fof(f83,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f44])).

fof(f44,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f259,plain,
    ( r1_tarski(k2_xboole_0(sK0,sK1),sK2)
    | ~ spl16_2 ),
    inference(avatar_component_clause,[],[f257])).

fof(f257,plain,
    ( spl16_2
  <=> r1_tarski(k2_xboole_0(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_2])])).

fof(f254,plain,
    ( ~ r1_tarski(sK0,sK2)
    | spl16_1 ),
    inference(avatar_component_clause,[],[f252])).

fof(f252,plain,
    ( spl16_1
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_1])])).

fof(f260,plain,(
    spl16_2 ),
    inference(avatar_split_clause,[],[f137,f257])).

fof(f137,plain,(
    r1_tarski(k2_xboole_0(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f91])).

fof(f91,plain,
    ( ~ r1_tarski(sK0,sK2)
    & r1_tarski(k2_xboole_0(sK0,sK1),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f62,f90])).

fof(f90,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X2)
        & r1_tarski(k2_xboole_0(X0,X1),X2) )
   => ( ~ r1_tarski(sK0,sK2)
      & r1_tarski(k2_xboole_0(sK0,sK1),sK2) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X2)
      & r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f42])).

fof(f42,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_xboole_0(X0,X1),X2)
       => r1_tarski(X0,X2) ) ),
    inference(negated_conjecture,[],[f41])).

fof(f41,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f255,plain,(
    ~ spl16_1 ),
    inference(avatar_split_clause,[],[f138,f252])).

fof(f138,plain,(
    ~ r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f91])).
%------------------------------------------------------------------------------
