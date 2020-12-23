%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0095+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:09 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   15 (  20 expanded)
%              Number of leaves         :    4 (   6 expanded)
%              Depth                    :    6
%              Number of atoms          :   27 (  39 expanded)
%              Number of equality atoms :   15 (  21 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f487,plain,(
    $false ),
    inference(subsumption_resolution,[],[f486,f476])).

fof(f476,plain,(
    sK0 = k4_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f288,f338])).

fof(f338,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f255])).

fof(f255,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f129])).

fof(f129,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f288,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f233])).

fof(f233,plain,
    ( sK0 != k4_xboole_0(k2_xboole_0(sK0,sK1),sK1)
    & r1_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f143,f232])).

fof(f232,plain,
    ( ? [X0,X1] :
        ( k4_xboole_0(k2_xboole_0(X0,X1),X1) != X0
        & r1_xboole_0(X0,X1) )
   => ( sK0 != k4_xboole_0(k2_xboole_0(sK0,sK1),sK1)
      & r1_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f143,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) != X0
      & r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f135])).

fof(f135,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_xboole_0(X0,X1)
       => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 ) ),
    inference(negated_conjecture,[],[f134])).

% (10165)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_3 on theBenchmark
fof(f134,conjecture,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_xboole_1)).

fof(f486,plain,(
    sK0 != k4_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f289,f357])).

fof(f357,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f289,plain,(
    sK0 != k4_xboole_0(k2_xboole_0(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f233])).
%------------------------------------------------------------------------------
