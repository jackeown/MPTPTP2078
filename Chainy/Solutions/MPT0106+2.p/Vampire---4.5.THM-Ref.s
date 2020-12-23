%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0106+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:09 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   21 (  38 expanded)
%              Number of leaves         :    5 (  13 expanded)
%              Depth                    :    9
%              Number of atoms          :   21 (  38 expanded)
%              Number of equality atoms :   20 (  37 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f632,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f631])).

fof(f631,plain,(
    k4_xboole_0(k5_xboole_0(sK0,sK1),sK2) != k4_xboole_0(k5_xboole_0(sK0,sK1),sK2) ),
    inference(forward_demodulation,[],[f587,f443])).

fof(f443,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f334,f336])).

fof(f336,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f149])).

fof(f149,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f334,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f587,plain,(
    k4_xboole_0(k5_xboole_0(sK0,sK1),sK2) != k4_xboole_0(k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK0,sK1))),sK2) ),
    inference(superposition,[],[f556,f459])).

fof(f459,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X2) = k5_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f269,f336,f336])).

fof(f269,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f83])).

fof(f83,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_xboole_1)).

fof(f556,plain,(
    k4_xboole_0(k5_xboole_0(sK0,sK1),sK2) != k5_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK2),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK0),sK2),k4_xboole_0(k4_xboole_0(sK0,sK1),sK2))) ),
    inference(forward_demodulation,[],[f555,f467])).

fof(f467,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) ),
    inference(definition_unfolding,[],[f277,f336])).

fof(f277,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f82])).

fof(f82,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f555,plain,(
    k4_xboole_0(k5_xboole_0(sK0,sK1),sK2) != k5_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK2),k4_xboole_0(k4_xboole_0(sK1,k5_xboole_0(sK0,k4_xboole_0(sK2,sK0))),k4_xboole_0(k4_xboole_0(sK0,sK1),sK2))) ),
    inference(forward_demodulation,[],[f444,f467])).

fof(f444,plain,(
    k4_xboole_0(k5_xboole_0(sK0,sK1),sK2) != k5_xboole_0(k4_xboole_0(sK0,k5_xboole_0(sK1,k4_xboole_0(sK2,sK1))),k4_xboole_0(k4_xboole_0(sK1,k5_xboole_0(sK0,k4_xboole_0(sK2,sK0))),k4_xboole_0(sK0,k5_xboole_0(sK1,k4_xboole_0(sK2,sK1))))) ),
    inference(definition_unfolding,[],[f254,f336,f336,f336])).

fof(f254,plain,(
    k4_xboole_0(k5_xboole_0(sK0,sK1),sK2) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k2_xboole_0(sK0,sK2))) ),
    inference(cnf_transformation,[],[f158])).

fof(f158,plain,(
    ? [X0,X1,X2] : k4_xboole_0(k5_xboole_0(X0,X1),X2) != k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2))) ),
    inference(ennf_transformation,[],[f151])).

fof(f151,negated_conjecture,(
    ~ ! [X0,X1,X2] : k4_xboole_0(k5_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2))) ),
    inference(negated_conjecture,[],[f150])).

% (29425)lrs-2_3:2_av=off:bce=on:cond=on:gsp=input_only:gs=on:gsem=on:lcm=predicate:lma=on:newcnf=on:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:updr=off:uhcvi=on_62 on theBenchmark
fof(f150,conjecture,(
    ! [X0,X1,X2] : k4_xboole_0(k5_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_xboole_1)).
%------------------------------------------------------------------------------
