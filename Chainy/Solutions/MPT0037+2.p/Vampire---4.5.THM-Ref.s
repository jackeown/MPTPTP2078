%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0037+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:05 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   19 (  26 expanded)
%              Number of leaves         :    5 (   8 expanded)
%              Depth                    :    7
%              Number of atoms          :   29 (  43 expanded)
%              Number of equality atoms :   18 (  26 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (5440)dis+4_8:1_add=large:afp=100000:afq=1.4:ep=RST:fde=unused:gsp=input_only:lcm=predicate:nwc=1:sos=all:sp=occurrence:updr=off:uhcvi=on_33 on theBenchmark
fof(f444,plain,(
    $false ),
    inference(subsumption_resolution,[],[f266,f423])).

fof(f423,plain,(
    ! [X16] : k2_xboole_0(sK2,k3_xboole_0(sK3,X16)) = k3_xboole_0(sK3,k2_xboole_0(sK2,X16)) ),
    inference(superposition,[],[f143,f182])).

fof(f182,plain,(
    sK3 = k2_xboole_0(sK2,sK3) ),
    inference(unit_resulting_resolution,[],[f116,f129])).

fof(f129,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f42])).

fof(f42,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f116,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f105])).

fof(f105,plain,
    ( k2_xboole_0(sK2,k3_xboole_0(sK4,sK3)) != k3_xboole_0(k2_xboole_0(sK2,sK4),sK3)
    & r1_tarski(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f78,f104])).

fof(f104,plain,
    ( ? [X0,X1,X2] :
        ( k2_xboole_0(X0,k3_xboole_0(X2,X1)) != k3_xboole_0(k2_xboole_0(X0,X2),X1)
        & r1_tarski(X0,X1) )
   => ( k2_xboole_0(sK2,k3_xboole_0(sK4,sK3)) != k3_xboole_0(k2_xboole_0(sK2,sK4),sK3)
      & r1_tarski(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f78,plain,(
    ? [X0,X1,X2] :
      ( k2_xboole_0(X0,k3_xboole_0(X2,X1)) != k3_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f65])).

fof(f65,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,X1)
       => k2_xboole_0(X0,k3_xboole_0(X2,X1)) = k3_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f64])).

fof(f64,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k3_xboole_0(X2,X1)) = k3_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_xboole_1)).

fof(f143,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_xboole_1)).

fof(f266,plain,(
    k3_xboole_0(sK3,k2_xboole_0(sK2,sK4)) != k2_xboole_0(sK2,k3_xboole_0(sK3,sK4)) ),
    inference(superposition,[],[f159,f150])).

fof(f150,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f159,plain,(
    k3_xboole_0(k2_xboole_0(sK2,sK4),sK3) != k2_xboole_0(sK2,k3_xboole_0(sK3,sK4)) ),
    inference(forward_demodulation,[],[f117,f150])).

fof(f117,plain,(
    k2_xboole_0(sK2,k3_xboole_0(sK4,sK3)) != k3_xboole_0(k2_xboole_0(sK2,sK4),sK3) ),
    inference(cnf_transformation,[],[f105])).
%------------------------------------------------------------------------------
