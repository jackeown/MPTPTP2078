%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0270+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:20 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   21 (  47 expanded)
%              Number of leaves         :    4 (  15 expanded)
%              Depth                    :   10
%              Number of atoms          :   50 ( 125 expanded)
%              Number of equality atoms :   19 (  54 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f571,plain,(
    $false ),
    inference(subsumption_resolution,[],[f568,f552])).

fof(f552,plain,(
    ~ sQ8_eqProxy(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f515,f528])).

fof(f528,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ sQ8_eqProxy(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),X1)) ) ),
    inference(equality_proxy_replacement,[],[f458,f514])).

fof(f514,plain,(
    ! [X1,X0] :
      ( sQ8_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ8_eqProxy])])).

fof(f458,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f417])).

fof(f417,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
        | r2_hidden(X0,X1) )
      & ( ~ r2_hidden(X0,X1)
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f302])).

fof(f302,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).

fof(f515,plain,
    ( r2_hidden(sK0,sK1)
    | ~ sQ8_eqProxy(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),sK1)) ),
    inference(equality_proxy_replacement,[],[f434,f514])).

fof(f434,plain,
    ( r2_hidden(sK0,sK1)
    | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f399])).

fof(f399,plain,
    ( ( r2_hidden(sK0,sK1)
      | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) )
    & ( ~ r2_hidden(sK0,sK1)
      | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f397,f398])).

fof(f398,plain,
    ( ? [X0,X1] :
        ( ( r2_hidden(X0,X1)
          | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) )
        & ( ~ r2_hidden(X0,X1)
          | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) ) )
   => ( ( r2_hidden(sK0,sK1)
        | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) )
      & ( ~ r2_hidden(sK0,sK1)
        | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f397,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,X1)
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) )
      & ( ~ r2_hidden(X0,X1)
        | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f371])).

fof(f371,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <~> ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f367])).

fof(f367,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
      <=> ~ r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f366])).

fof(f366,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_zfmisc_1)).

fof(f568,plain,(
    sQ8_eqProxy(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),sK1)) ),
    inference(resolution,[],[f553,f527])).

fof(f527,plain,(
    ! [X0,X1] :
      ( sQ8_eqProxy(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),X1))
      | r2_hidden(X0,X1) ) ),
    inference(equality_proxy_replacement,[],[f459,f514])).

fof(f459,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f417])).

fof(f553,plain,(
    ~ r2_hidden(sK0,sK1) ),
    inference(subsumption_resolution,[],[f516,f552])).

fof(f516,plain,
    ( ~ r2_hidden(sK0,sK1)
    | sQ8_eqProxy(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),sK1)) ),
    inference(equality_proxy_replacement,[],[f433,f514])).

fof(f433,plain,
    ( ~ r2_hidden(sK0,sK1)
    | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f399])).
%------------------------------------------------------------------------------
