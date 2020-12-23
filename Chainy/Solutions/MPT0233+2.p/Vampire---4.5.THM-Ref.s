%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0233+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:18 EST 2020

% Result     : Theorem 1.31s
% Output     : Refutation 1.31s
% Verified   : 
% Statistics : Number of formulae       :   26 (  39 expanded)
%              Number of leaves         :    6 (  13 expanded)
%              Depth                    :    9
%              Number of atoms          :   59 ( 101 expanded)
%              Number of equality atoms :   21 (  48 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f590,plain,(
    $false ),
    inference(subsumption_resolution,[],[f589,f383])).

fof(f383,plain,(
    ~ sQ5_eqProxy(sK0,sK3) ),
    inference(equality_proxy_replacement,[],[f352,f382])).

fof(f382,plain,(
    ! [X1,X0] :
      ( sQ5_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ5_eqProxy])])).

fof(f352,plain,(
    sK0 != sK3 ),
    inference(cnf_transformation,[],[f345])).

fof(f345,plain,
    ( sK0 != sK3
    & sK0 != sK2
    & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f324,f344])).

fof(f344,plain,
    ( ? [X0,X1,X2,X3] :
        ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) )
   => ( sK0 != sK3
      & sK0 != sK2
      & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f324,plain,(
    ? [X0,X1,X2,X3] :
      ( X0 != X3
      & X0 != X2
      & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(ennf_transformation,[],[f319])).

fof(f319,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( X0 != X3
          & X0 != X2
          & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(negated_conjecture,[],[f318])).

fof(f318,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_zfmisc_1)).

fof(f589,plain,(
    sQ5_eqProxy(sK0,sK3) ),
    inference(subsumption_resolution,[],[f586,f378])).

fof(f378,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f302])).

fof(f302,axiom,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

fof(f586,plain,
    ( ~ r1_tarski(k1_tarski(sK0),k2_tarski(sK0,sK1))
    | sQ5_eqProxy(sK0,sK3) ),
    inference(resolution,[],[f424,f414])).

fof(f414,plain,(
    ! [X4] :
      ( ~ r1_tarski(k1_tarski(sK0),k2_tarski(sK2,X4))
      | sQ5_eqProxy(sK0,X4) ) ),
    inference(resolution,[],[f384,f391])).

fof(f391,plain,(
    ! [X2,X0,X1] :
      ( sQ5_eqProxy(X0,X2)
      | sQ5_eqProxy(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(equality_proxy_replacement,[],[f368,f382,f382])).

fof(f368,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f338])).

fof(f338,plain,(
    ! [X0,X1,X2] :
      ( X0 = X2
      | X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(ennf_transformation,[],[f315])).

fof(f315,axiom,(
    ! [X0,X1,X2] :
      ~ ( X0 != X2
        & X0 != X1
        & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).

fof(f384,plain,(
    ~ sQ5_eqProxy(sK0,sK2) ),
    inference(equality_proxy_replacement,[],[f351,f382])).

fof(f351,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f345])).

fof(f424,plain,(
    ! [X7] :
      ( r1_tarski(X7,k2_tarski(sK2,sK3))
      | ~ r1_tarski(X7,k2_tarski(sK0,sK1)) ) ),
    inference(resolution,[],[f350,f358])).

fof(f358,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f332])).

fof(f332,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f331])).

fof(f331,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f77])).

fof(f77,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f350,plain,(
    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ),
    inference(cnf_transformation,[],[f345])).
%------------------------------------------------------------------------------
