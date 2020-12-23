%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0256+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:19 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   18 (  31 expanded)
%              Number of leaves         :    5 (  11 expanded)
%              Depth                    :    6
%              Number of atoms          :   29 (  49 expanded)
%              Number of equality atoms :   17 (  31 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1055,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1017,f853])).

fof(f853,plain,(
    k2_tarski(sK16,sK16) = k4_xboole_0(sK15,k4_xboole_0(sK15,k2_tarski(sK16,sK16))) ),
    inference(definition_unfolding,[],[f592,f796,f715,f796])).

fof(f715,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f796,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f254])).

fof(f254,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f592,plain,(
    k1_tarski(sK16) = k3_xboole_0(sK15,k1_tarski(sK16)) ),
    inference(cnf_transformation,[],[f498])).

fof(f498,plain,
    ( ~ r2_hidden(sK16,sK15)
    & k1_tarski(sK16) = k3_xboole_0(sK15,k1_tarski(sK16)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15,sK16])],[f361,f497])).

fof(f497,plain,
    ( ? [X0,X1] :
        ( ~ r2_hidden(X1,X0)
        & k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1)) )
   => ( ~ r2_hidden(sK16,sK15)
      & k1_tarski(sK16) = k3_xboole_0(sK15,k1_tarski(sK16)) ) ),
    introduced(choice_axiom,[])).

fof(f361,plain,(
    ? [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      & k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f353])).

fof(f353,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1))
       => r2_hidden(X1,X0) ) ),
    inference(negated_conjecture,[],[f352])).

fof(f352,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1))
     => r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_zfmisc_1)).

fof(f1017,plain,(
    k2_tarski(sK16,sK16) != k4_xboole_0(sK15,k4_xboole_0(sK15,k2_tarski(sK16,sK16))) ),
    inference(unit_resulting_resolution,[],[f593,f875])).

fof(f875,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k2_tarski(X1,X1) != k4_xboole_0(X0,k4_xboole_0(X0,k2_tarski(X1,X1))) ) ),
    inference(definition_unfolding,[],[f671,f796,f715,f796])).

fof(f671,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f375])).

fof(f375,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f299])).

fof(f299,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1))
     => r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l29_zfmisc_1)).

fof(f593,plain,(
    ~ r2_hidden(sK16,sK15) ),
    inference(cnf_transformation,[],[f498])).
%------------------------------------------------------------------------------
