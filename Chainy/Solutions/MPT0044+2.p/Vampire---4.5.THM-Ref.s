%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0044+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:05 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   21 (  47 expanded)
%              Number of leaves         :    4 (  15 expanded)
%              Depth                    :   10
%              Number of atoms          :   50 ( 125 expanded)
%              Number of equality atoms :   19 (  54 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f171,plain,(
    $false ),
    inference(subsumption_resolution,[],[f170,f160])).

fof(f160,plain,(
    ~ sQ4_eqProxy(k1_xboole_0,k4_xboole_0(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f143,f150])).

fof(f150,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ sQ4_eqProxy(k1_xboole_0,k4_xboole_0(X0,X1)) ) ),
    inference(equality_proxy_replacement,[],[f125,f142])).

fof(f142,plain,(
    ! [X1,X0] :
      ( sQ4_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ4_eqProxy])])).

fof(f125,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f143,plain,
    ( ~ r1_tarski(sK0,sK1)
    | ~ sQ4_eqProxy(k1_xboole_0,k4_xboole_0(sK0,sK1)) ),
    inference(equality_proxy_replacement,[],[f111,f142])).

fof(f111,plain,
    ( ~ r1_tarski(sK0,sK1)
    | k1_xboole_0 != k4_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f99])).

fof(f99,plain,
    ( ( ~ r1_tarski(sK0,sK1)
      | k1_xboole_0 != k4_xboole_0(sK0,sK1) )
    & ( r1_tarski(sK0,sK1)
      | k1_xboole_0 = k4_xboole_0(sK0,sK1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f97,f98])).

fof(f98,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_tarski(X0,X1)
          | k1_xboole_0 != k4_xboole_0(X0,X1) )
        & ( r1_tarski(X0,X1)
          | k1_xboole_0 = k4_xboole_0(X0,X1) ) )
   => ( ( ~ r1_tarski(sK0,sK1)
        | k1_xboole_0 != k4_xboole_0(sK0,sK1) )
      & ( r1_tarski(sK0,sK1)
        | k1_xboole_0 = k4_xboole_0(sK0,sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f97,plain,(
    ? [X0,X1] :
      ( ( ~ r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 = k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f86])).

fof(f86,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <~> r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f73])).

fof(f73,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k4_xboole_0(X0,X1)
      <=> r1_tarski(X0,X1) ) ),
    inference(negated_conjecture,[],[f72])).

fof(f72,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).

fof(f170,plain,(
    sQ4_eqProxy(k1_xboole_0,k4_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f161,f149])).

fof(f149,plain,(
    ! [X0,X1] :
      ( sQ4_eqProxy(k1_xboole_0,k4_xboole_0(X0,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(equality_proxy_replacement,[],[f126,f142])).

fof(f126,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f107])).

fof(f161,plain,(
    r1_tarski(sK0,sK1) ),
    inference(subsumption_resolution,[],[f144,f160])).

fof(f144,plain,
    ( r1_tarski(sK0,sK1)
    | sQ4_eqProxy(k1_xboole_0,k4_xboole_0(sK0,sK1)) ),
    inference(equality_proxy_replacement,[],[f110,f142])).

fof(f110,plain,
    ( r1_tarski(sK0,sK1)
    | k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f99])).
%------------------------------------------------------------------------------
