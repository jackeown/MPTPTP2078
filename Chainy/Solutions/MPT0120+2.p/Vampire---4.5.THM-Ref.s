%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0120+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:10 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   17 (  23 expanded)
%              Number of leaves         :    4 (   7 expanded)
%              Depth                    :   10
%              Number of atoms          :   21 (  27 expanded)
%              Number of equality atoms :   20 (  26 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
% (20950)lrs+1002_8:1_av=off:cond=on:gsp=input_only:gs=on:irw=on:lma=on:nm=0:nwc=1.7:stl=30:sd=2:ss=axioms:sos=on:sp=occurrence:urr=on_41 on theBenchmark
fof(f425,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f424])).

fof(f424,plain,(
    k4_xboole_0(k2_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK2,sK3))),k2_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK2,sK3)))) != k4_xboole_0(k2_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK2,sK3))),k2_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK2,sK3)))) ),
    inference(forward_demodulation,[],[f423,f265])).

fof(f265,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f110])).

fof(f110,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f423,plain,(
    k4_xboole_0(k2_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK2,sK3))),k2_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),sK3))) != k4_xboole_0(k2_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),sK3)),k2_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK2,sK3)))) ),
    inference(forward_demodulation,[],[f407,f265])).

fof(f407,plain,(
    k4_xboole_0(k2_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK2,sK3))),k2_xboole_0(k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)),sK3)) != k4_xboole_0(k2_xboole_0(k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)),sK3),k2_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK2,sK3)))) ),
    inference(unit_resulting_resolution,[],[f399,f272])).

fof(f272,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f178])).

fof(f178,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ) ),
    inference(ennf_transformation,[],[f89])).

fof(f89,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_xboole_1)).

fof(f399,plain,(
    k2_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK2,sK3))) != k2_xboole_0(k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)),sK3) ),
    inference(forward_demodulation,[],[f398,f265])).

fof(f398,plain,(
    k2_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3) != k2_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK2,sK3))) ),
    inference(forward_demodulation,[],[f246,f265])).

fof(f246,plain,(
    k2_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3) != k2_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),sK3)) ),
    inference(cnf_transformation,[],[f235])).

fof(f235,plain,(
    k2_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3) != k2_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f172,f234])).

fof(f234,plain,
    ( ? [X0,X1,X2,X3] : k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) != k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3))
   => k2_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3) != k2_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),sK3)) ),
    introduced(choice_axiom,[])).

fof(f172,plain,(
    ? [X0,X1,X2,X3] : k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) != k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) ),
    inference(ennf_transformation,[],[f63])).

fof(f63,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) = k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) ),
    inference(negated_conjecture,[],[f62])).

fof(f62,conjecture,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) = k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_xboole_1)).
%------------------------------------------------------------------------------
