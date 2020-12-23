%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0185+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:15 EST 2020

% Result     : Theorem 1.12s
% Output     : Refutation 1.12s
% Verified   : 
% Statistics : Number of formulae       :   17 (  26 expanded)
%              Number of leaves         :    5 (   9 expanded)
%              Depth                    :    8
%              Number of atoms          :   18 (  27 expanded)
%              Number of equality atoms :   17 (  26 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f296,plain,(
    $false ),
    inference(subsumption_resolution,[],[f295,f287])).

fof(f287,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(definition_unfolding,[],[f260,f257])).

fof(f257,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f199])).

fof(f199,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

fof(f260,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f197])).

fof(f197,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

fof(f295,plain,(
    k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK3)) != k2_xboole_0(k1_tarski(sK0),k1_enumset1(sK1,sK2,sK3)) ),
    inference(forward_demodulation,[],[f294,f277])).

fof(f277,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1) ),
    inference(cnf_transformation,[],[f250])).

fof(f250,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_enumset1)).

fof(f294,plain,(
    k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK3)) != k2_xboole_0(k1_tarski(sK0),k1_enumset1(sK1,sK3,sK2)) ),
    inference(forward_demodulation,[],[f284,f287])).

fof(f284,plain,(
    k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK3)) != k2_xboole_0(k1_enumset1(sK0,sK1,sK3),k1_tarski(sK2)) ),
    inference(definition_unfolding,[],[f256,f257,f257])).

fof(f256,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK1,sK3,sK2) ),
    inference(cnf_transformation,[],[f255])).

fof(f255,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK1,sK3,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f253,f254])).

fof(f254,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X0,X1,X3,X2)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK1,sK3,sK2) ),
    introduced(choice_axiom,[])).

fof(f253,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X0,X1,X3,X2) ),
    inference(ennf_transformation,[],[f193])).

% (20549)Refutation not found, incomplete strategy% (20549)------------------------------
% (20549)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (20549)Termination reason: Refutation not found, incomplete strategy

fof(f193,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
    inference(negated_conjecture,[],[f192])).

% (20549)Memory used [KB]: 6268
% (20549)Time elapsed: 0.001 s
fof(f192,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_enumset1)).

% (20549)------------------------------
% (20549)------------------------------
%------------------------------------------------------------------------------
