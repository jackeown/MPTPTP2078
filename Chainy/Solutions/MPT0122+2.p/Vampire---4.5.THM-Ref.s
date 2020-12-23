%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0122+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:10 EST 2020

% Result     : Theorem 1.19s
% Output     : Refutation 1.19s
% Verified   : 
% Statistics : Number of formulae       :    9 (   9 expanded)
%              Number of leaves         :    3 (   3 expanded)
%              Depth                    :    5
%              Number of atoms          :   10 (  10 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    4 (   2 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f689,plain,(
    $false ),
    inference(subsumption_resolution,[],[f346,f350])).

fof(f350,plain,(
    ! [X0] : ~ r2_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f127])).

fof(f127,axiom,(
    ! [X0] : ~ r2_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_xboole_1)).

fof(f346,plain,(
    r2_xboole_0(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f285])).

fof(f285,plain,(
    r2_xboole_0(sK0,k1_xboole_0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f178,f284])).

fof(f284,plain,
    ( ? [X0] : r2_xboole_0(X0,k1_xboole_0)
   => r2_xboole_0(sK0,k1_xboole_0) ),
    introduced(choice_axiom,[])).

fof(f178,plain,(
    ? [X0] : r2_xboole_0(X0,k1_xboole_0) ),
    inference(ennf_transformation,[],[f65])).

fof(f65,negated_conjecture,(
    ~ ! [X0] : ~ r2_xboole_0(X0,k1_xboole_0) ),
    inference(negated_conjecture,[],[f64])).

fof(f64,conjecture,(
    ! [X0] : ~ r2_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t115_xboole_1)).
%------------------------------------------------------------------------------
