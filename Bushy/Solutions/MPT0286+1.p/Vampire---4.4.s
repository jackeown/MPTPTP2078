%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : zfmisc_1__t93_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:42:13 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :    9 (   9 expanded)
%              Number of leaves         :    3 (   3 expanded)
%              Depth                    :    5
%              Number of atoms          :   10 (  10 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f36,plain,(
    $false ),
    inference(subsumption_resolution,[],[f26,f34])).

fof(f34,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t93_zfmisc_1.p',l51_zfmisc_1)).

fof(f26,plain,(
    k3_tarski(k2_tarski(sK0,sK1)) != k2_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    k3_tarski(k2_tarski(sK0,sK1)) != k2_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f24])).

fof(f24,plain,
    ( ? [X0,X1] : k3_tarski(k2_tarski(X0,X1)) != k2_xboole_0(X0,X1)
   => k3_tarski(k2_tarski(sK0,sK1)) != k2_xboole_0(sK0,sK1) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1] : k3_tarski(k2_tarski(X0,X1)) != k2_xboole_0(X0,X1) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t93_zfmisc_1.p',t93_zfmisc_1)).
%------------------------------------------------------------------------------
