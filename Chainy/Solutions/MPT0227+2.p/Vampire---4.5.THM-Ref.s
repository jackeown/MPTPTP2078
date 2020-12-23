%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0227+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:18 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   15 (  16 expanded)
%              Number of leaves         :    5 (   6 expanded)
%              Depth                    :    6
%              Number of atoms          :   23 (  25 expanded)
%              Number of equality atoms :   12 (  13 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1370,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f597,f1054,f1135])).

fof(f1135,plain,(
    ! [X0,X1] :
      ( sQ28_eqProxy(k1_xboole_0,k4_xboole_0(X0,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(equality_proxy_replacement,[],[f700,f1038])).

fof(f1038,plain,(
    ! [X1,X0] :
      ( sQ28_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ28_eqProxy])])).

fof(f700,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f495])).

fof(f495,plain,(
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

fof(f1054,plain,(
    ~ sQ28_eqProxy(k1_xboole_0,k4_xboole_0(k1_tarski(sK2),k2_tarski(sK2,sK3))) ),
    inference(equality_proxy_replacement,[],[f555,f1038])).

fof(f555,plain,(
    k1_xboole_0 != k4_xboole_0(k1_tarski(sK2),k2_tarski(sK2,sK3)) ),
    inference(cnf_transformation,[],[f453])).

fof(f453,plain,(
    k1_xboole_0 != k4_xboole_0(k1_tarski(sK2),k2_tarski(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f322,f452])).

fof(f452,plain,
    ( ? [X0,X1] : k1_xboole_0 != k4_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))
   => k1_xboole_0 != k4_xboole_0(k1_tarski(sK2),k2_tarski(sK2,sK3)) ),
    introduced(choice_axiom,[])).

fof(f322,plain,(
    ? [X0,X1] : k1_xboole_0 != k4_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(ennf_transformation,[],[f311])).

fof(f311,negated_conjecture,(
    ~ ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(negated_conjecture,[],[f310])).

fof(f310,conjecture,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_zfmisc_1)).

fof(f597,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f300])).

fof(f300,axiom,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).
%------------------------------------------------------------------------------
