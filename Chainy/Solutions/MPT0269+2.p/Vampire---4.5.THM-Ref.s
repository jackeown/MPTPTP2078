%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0269+2 : TPTP v7.4.0. Released v7.4.0.
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
% Statistics : Number of formulae       :   30 (  47 expanded)
%              Number of leaves         :    6 (  17 expanded)
%              Depth                    :   10
%              Number of atoms          :   69 ( 119 expanded)
%              Number of equality atoms :   38 (  80 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2193,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1817,f2156])).

fof(f2156,plain,(
    ~ spl39_7 ),
    inference(avatar_split_clause,[],[f2155,f1778])).

fof(f1778,plain,
    ( spl39_7
  <=> r1_tarski(sK4,k1_tarski(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_7])])).

fof(f2155,plain,(
    ~ r1_tarski(sK4,k1_tarski(sK5)) ),
    inference(subsumption_resolution,[],[f2058,f1286])).

fof(f1286,plain,(
    ~ sQ38_eqProxy(k1_xboole_0,sK4) ),
    inference(equality_proxy_replacement,[],[f681,f1269])).

fof(f1269,plain,(
    ! [X1,X0] :
      ( sQ38_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ38_eqProxy])])).

fof(f681,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f545])).

fof(f545,plain,
    ( sK4 != k1_tarski(sK5)
    & k1_xboole_0 != sK4
    & k1_xboole_0 = k4_xboole_0(sK4,k1_tarski(sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f376,f544])).

fof(f544,plain,
    ( ? [X0,X1] :
        ( k1_tarski(X1) != X0
        & k1_xboole_0 != X0
        & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) )
   => ( sK4 != k1_tarski(sK5)
      & k1_xboole_0 != sK4
      & k1_xboole_0 = k4_xboole_0(sK4,k1_tarski(sK5)) ) ),
    introduced(choice_axiom,[])).

fof(f376,plain,(
    ? [X0,X1] :
      ( k1_tarski(X1) != X0
      & k1_xboole_0 != X0
      & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f366])).

fof(f366,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0
          & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(negated_conjecture,[],[f365])).

fof(f365,conjecture,(
    ! [X0,X1] :
      ~ ( k1_tarski(X1) != X0
        & k1_xboole_0 != X0
        & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_zfmisc_1)).

fof(f2058,plain,
    ( sQ38_eqProxy(k1_xboole_0,sK4)
    | ~ r1_tarski(sK4,k1_tarski(sK5)) ),
    inference(resolution,[],[f1765,f1382])).

fof(f1382,plain,(
    ! [X0,X1] :
      ( sQ38_eqProxy(k1_tarski(X1),X0)
      | sQ38_eqProxy(k1_xboole_0,X0)
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(equality_proxy_replacement,[],[f844,f1269,f1269])).

fof(f844,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f588])).

fof(f588,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f587])).

fof(f587,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f340])).

fof(f340,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_zfmisc_1)).

fof(f1765,plain,(
    ~ sQ38_eqProxy(k1_tarski(sK5),sK4) ),
    inference(resolution,[],[f1285,f1577])).

fof(f1577,plain,(
    ! [X0,X1] :
      ( ~ sQ38_eqProxy(X0,X1)
      | sQ38_eqProxy(X1,X0) ) ),
    inference(equality_proxy_axiom,[],[f1269])).

fof(f1285,plain,(
    ~ sQ38_eqProxy(sK4,k1_tarski(sK5)) ),
    inference(equality_proxy_replacement,[],[f682,f1269])).

fof(f682,plain,(
    sK4 != k1_tarski(sK5) ),
    inference(cnf_transformation,[],[f545])).

fof(f1817,plain,(
    spl39_7 ),
    inference(avatar_split_clause,[],[f1811,f1778])).

fof(f1811,plain,(
    r1_tarski(sK4,k1_tarski(sK5)) ),
    inference(resolution,[],[f1287,f1384])).

fof(f1384,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ sQ38_eqProxy(k1_xboole_0,k4_xboole_0(X0,X1)) ) ),
    inference(equality_proxy_replacement,[],[f851,f1269])).

fof(f851,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f591])).

fof(f591,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f1287,plain,(
    sQ38_eqProxy(k1_xboole_0,k4_xboole_0(sK4,k1_tarski(sK5))) ),
    inference(equality_proxy_replacement,[],[f680,f1269])).

fof(f680,plain,(
    k1_xboole_0 = k4_xboole_0(sK4,k1_tarski(sK5)) ),
    inference(cnf_transformation,[],[f545])).
%------------------------------------------------------------------------------
